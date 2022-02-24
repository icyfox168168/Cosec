
#include <string.h>
#include <stdio.h>
#include <assert.h>

#include "Assembler.h"

typedef struct {
    Fn *fn;         // Current function we're assembling
    BB *bb;         // Current basic block we're assembling
    int stack_size; // Number of bytes allocated on the stack by 'IR_ALLOC's
    int next_gpr, next_sse; // Next virtual register slot to use
} Assembler;

// Tells us which register each function argument is in, according to the
// System V ABI. The array is indexed by function argument number, where 0 is
// the left-most argument. Floating point function arguments are indexed
// SEPARATELY (using 'FN_ARGS_SSE_REGS').
//
// 'NUM_FN_ARGS_REGS' tells us how many function arguments are passed via
// registers. After this many arguments, we need to start pulling off the stack.
// #define NUM_FN_ARGS_GPRS 6
static GPReg FN_ARGS_GPRS[] = {
    GPR_RDI,
    GPR_RSI,
    GPR_RDX,
    GPR_RCX,
    GPR_R8,
    GPR_R9,
};

// #define NUM_FN_ARGS_SSE_REGS 8
static SSEReg FN_ARGS_SSE_REGS[] = {
    SSE_XMM0,
    SSE_XMM1,
    SSE_XMM2,
    SSE_XMM3,
    SSE_XMM4,
    SSE_XMM5,
    SSE_XMM6,
    SSE_XMM7,
};

static AsmOpcode IR_OP_TO_SETXX[NUM_IR_OPS] = { // Convert IR to SETxx opcode
    [IR_EQ] = X86_SETE,
    [IR_NEQ] = X86_SETNE,
    [IR_SLT] = X86_SETL,
    [IR_SLE] = X86_SETLE,
    [IR_SGT] = X86_SETG,
    [IR_SGE] = X86_SETGE,
    [IR_ULT] = X86_SETB,
    [IR_ULE] = X86_SETBE,
    [IR_UGT] = X86_SETA,
    [IR_UGE] = X86_SETAE,
    [IR_FLT] = X86_SETB,
    [IR_FLE] = X86_SETBE,
    [IR_FGT] = X86_SETA,
    [IR_FGE] = X86_SETAE,
};

static AsmOpcode IR_OP_TO_JXX[NUM_IR_OPS] = { // Convert IR to Jxx opcode
    [IR_EQ] = X86_JE,
    [IR_NEQ] = X86_JNE,
    [IR_SLT] = X86_JL,
    [IR_SLE] = X86_JLE,
    [IR_SGT] = X86_JG,
    [IR_SGE] = X86_JGE,
    [IR_ULT] = X86_JB,
    [IR_ULE] = X86_JBE,
    [IR_UGT] = X86_JA,
    [IR_UGE] = X86_JAE,
    [IR_FLT] = X86_JB,
    [IR_FLE] = X86_JBE,
    [IR_FGT] = X86_JA,
    [IR_FGE] = X86_JAE,
};

static AsmOpcode INVERT_COND[NUM_X86_OPS] = { // Invert a conditional opcode
    [X86_JE] = X86_JNE,
    [X86_JNE] = X86_JE,
    [X86_JL] = X86_JGE,
    [X86_JLE] = X86_JG,
    [X86_JG] = X86_JLE,
    [X86_JGE] = X86_JL,
    [X86_JB] = X86_JAE,
    [X86_JBE] = X86_JA,
    [X86_JA] = X86_JBE,
    [X86_JAE] = X86_JB,
};

static AsmIns * new_asm(AsmOpcode op) {
    AsmIns *ins = malloc(sizeof(AsmIns));
    ins->next = NULL;
    ins->prev = NULL;
    ins->idx = -1;
    ins->op = op;
    ins->l.type = 0;
    ins->l.reg = 0;
    ins->l.size = GPR_Q;
    ins->r.type = 0;
    ins->r.reg = 0;
    ins->r.size = GPR_Q;
    return ins;
}

static AsmIns * emit(Assembler *a, AsmIns *ins) {
    BB *bb = a->bb;
    ins->bb = bb;
    ins->prev = bb->asm_last;
    if (bb->asm_last) {
        bb->asm_last->next = ins;
    } else { // Head of linked list
        bb->asm_head = ins;
    }
    bb->asm_last = ins;
    return ins;
}

void delete_asm(AsmIns *ins) {
    if (ins->prev) {
        ins->prev->next = ins->next;
    } else { // Head of linked list
        ins->bb->asm_head = ins->next;
    }
    if (ins->next) {
        ins->next->prev = ins->prev;
    }
    if (ins->bb->asm_last == ins) {
        ins->bb->asm_last = ins->prev;
    }
}

static GPRSize GPR_SIZE[] = {
    [1] = GPR_L,
    [2] = GPR_W,
    [4] = GPR_D,
    [8] = GPR_Q,
};

// Returns the register size to use for a specific type
static GPRSize gpr_size(Type *t) {
    if (is_arr(t)) {
        return GPR_Q; // Treat all arrays as pointers
    } else {
        return GPR_SIZE[bytes(t)];
    }
}

static AsmOperand discharge(Assembler *a, IrIns *ins); // Forward declarations
static AsmOperand to_mem_operand(Assembler *a, IrIns *ir_ptr);

static AsmOperand alloc_to_mem_operand(IrIns *ir_alloc) {
    AsmOperand result;
    result.type = OP_MEM;      // From memory
    result.base_reg = GPR_RBP; // Offset relative to rbp
    result.base_size = GPR_Q;
    result.index_reg = 0;
    result.index_size = GPR_NONE;
    result.scale = 1;
    result.disp = -ir_alloc->stack_slot;
    result.access_size = bytes(ir_alloc->type->ptr);
    return result;
}

static AsmOperand vreg_ptr_to_mem_operand(Assembler *a, IrIns *ir_ptr) {
    AsmOperand l = discharge(a, ir_ptr);
    AsmOperand result;
    result.type = OP_MEM;      // From memory
    result.base_reg = l.reg;   // Indexed by a vreg
    result.base_size = l.size; // Should be GPR_Q
    assert(l.size == GPR_Q);
    result.index_reg = 0;
    result.index_size = GPR_NONE;
    result.scale = 1;
    result.disp = 0;
    result.access_size = bytes(ir_ptr->type->ptr);
    return result;
}

// Converts a pointer instruction (i.e., IR_ALLOC, IR_ELEM, or some other
// pointer value stored in a vreg) to a memory access assembly operand,
// e.g., to [rbp - 4] or [rax]
static AsmOperand to_mem_operand(Assembler *a, IrIns *ir_ptr) {
    switch (ir_ptr->op) {
        case IR_ALLOC: return alloc_to_mem_operand(ir_ptr);
        default:       return vreg_ptr_to_mem_operand(a, ir_ptr);
        // TODO: could incorporate IR_ELEM here for efficiency
    }
}

static AsmOperand discharge_imm(Assembler *a, IrIns *ir_k) {
    ir_k->vreg = a->next_gpr++;
    AsmIns *mov = new_asm(X86_MOV);
    mov->l.type = OP_GPR;
    mov->l.reg = ir_k->vreg;
    mov->l.size = gpr_size(ir_k->type);
    mov->r.type = OP_IMM;
    mov->r.imm = ir_k->imm;
    emit(a, mov);
    return mov->l; // The vreg we 'mov'd into is the result
}

static AsmOperand discharge_fp_const(Assembler *a, IrIns *ir_k) {
    ir_k->vreg = a->next_sse++;
    AsmIns *mov = new_asm(ir_k->type->prim == T_f32 ? X86_MOVSS : X86_MOVSD);
    mov->l.type = OP_XMM;
    mov->l.reg = ir_k->vreg;
    mov->r.type = OP_CONST;
    mov->r.access_size = bytes(ir_k->type);
    mov->r.const_idx = ir_k->const_idx;
    emit(a, mov);
    return mov->l; // The vreg we 'mov'd into is the result
}

static AsmOperand discharge_str_const(Assembler *a, IrIns *ir_k) {
    ir_k->vreg = a->next_gpr++;
    AsmIns *mov = new_asm(X86_LEA);
    mov->l.type = OP_GPR;
    mov->l.reg = ir_k->vreg;
    mov->l.size = gpr_size(ir_k->type);
    mov->r.type = OP_CONST;
    mov->r.imm = ir_k->const_idx;
    emit(a, mov);
    return mov->l; // The vreg we 'mov'd into is the result
}

static AsmOperand discharge_const(Assembler *a, IrIns *ir_k) {
    if (is_fp(ir_k->type)) {
        return discharge_fp_const(a, ir_k);
    } else if (ir_k->type->kind == T_PTR && ir_k->type->ptr->kind == T_PRIM &&
               ir_k->type->ptr->prim == T_i8) {
        return discharge_str_const(a, ir_k);
    } else {
        UNREACHABLE();
    }
}

static AsmOperand discharge_fp_load(Assembler *a, IrIns *ir_load) {
    ir_load->vreg = a->next_sse++;
    AsmIns *mov = new_asm(ir_load->type->prim == T_f32 ? X86_MOVSS : X86_MOVSD);
    mov->l.type = OP_XMM; // Load into a vreg
    mov->l.reg = ir_load->vreg;
    mov->r = to_mem_operand(a, ir_load->l);
    emit(a, mov);
    return mov->l;
}

static AsmOperand discharge_load(Assembler *a, IrIns *ir_load) {
    if (is_fp(ir_load->type)) {
        return discharge_fp_load(a, ir_load);
    }
    ir_load->vreg = a->next_gpr++;
    AsmIns *mov = new_asm(X86_MOV);
    mov->l.type = OP_GPR; // Load into a vreg
    mov->l.reg = ir_load->vreg;
    mov->l.size = gpr_size(ir_load->type);
    mov->r = to_mem_operand(a, ir_load->l);
    emit(a, mov);
    return mov->l;
}

static AsmOperand discharge_alloc(Assembler *a, IrIns *ir_alloc) {
    ir_alloc->vreg = a->next_gpr++;
    AsmIns *lea = new_asm(X86_LEA);
    lea->l.type = OP_GPR;
    lea->l.reg = ir_alloc->vreg;
    lea->l.size = gpr_size(ir_alloc->type);
    lea->r = to_mem_operand(a, ir_alloc);
    lea->r.access_size = 0; // Don't care about bytes for a LEA instruction
    emit(a, lea);
    return lea->l;
}

static void asm_cmp(Assembler *a, IrIns *ir_cmp); // Forward declaration

static AsmOperand discharge_rel(Assembler *a, IrIns *ir_rel) {
    asm_cmp(a, ir_rel); // Emit a comparison instruction
    ir_rel->vreg = a->next_gpr++;
    AsmIns *set = new_asm(IR_OP_TO_SETXX[ir_rel->op]); // SETcc operation
    set->l.type = OP_GPR;
    set->l.reg = ir_rel->vreg;
    set->l.size = GPR_L; // Lowest 8 bits of the vreg
    emit(a, set);
    AsmIns *and = new_asm(X86_AND); // Clear the rest of the vreg
    and->l.type = OP_GPR;
    and->l.reg = ir_rel->vreg;
    and->l.size = GPR_L; // Lowest 8 bits (ir_rel type is always i1)
    and->r.type = OP_IMM;
    and->r.imm = 1;
    emit(a, and);
    return and->l;
}

// Emits an instruction to a virtual register
static AsmOperand discharge(Assembler *a, IrIns *ins) {
    if (ins->vreg >= 0) { // Already in a vreg
        AsmOperand result;
        if (is_fp(ins->type)) { // Result in an SSE register
            result.type = OP_XMM;
        } else { // Result in a GPR
            result.type = OP_GPR;
            result.size = gpr_size(ins->type);
        }
        result.reg = ins->vreg;
        return result;
    }
    switch (ins->op) {
    case IR_IMM:   return discharge_imm(a, ins);   // Immediate
    case IR_CONST: return discharge_const(a, ins); // Constant (float or string)
    case IR_LOAD:  return discharge_load(a, ins);  // Memory load
    case IR_ALLOC: return discharge_alloc(a, ins); // Pointer load
    case IR_EQ: case IR_NEQ:
    case IR_SLT: case IR_SLE: case IR_SGT: case IR_SGE:
    case IR_ULT: case IR_ULE: case IR_UGT: case IR_UGE:
        return discharge_rel(a, ins); // Comparisons
    default: UNREACHABLE();
    }
}

static AsmOperand inline_imm(Assembler *a, IrIns *ir_k) {
    if (ir_k->op == IR_IMM) { // Constant
        AsmOperand result;
        result.type = OP_IMM;
        result.imm = ir_k->imm;
        return result;
    } else {
        return discharge(a, ir_k);
    }
}

static AsmOperand inline_mem(Assembler *a, IrIns *ir_ins) {
    if (ir_ins->op == IR_LOAD) { // Inline a load
        // IR_LOADs are emitted as they happen by 'asm_ins' if they have more
        // than one usage; they're only inlined if they have ONE use
        if (ir_ins->vreg >= 0) { // Load has already been emitted
            return discharge(a, ir_ins); // Already in a vreg
        }
        return to_mem_operand(a, ir_ins->l); // Has only ONE use -> inline
    } else if (ir_ins->op == IR_CONST) {
        AsmOperand result;
        result.type = OP_CONST;
        result.const_idx = ir_ins->const_idx;
        result.access_size = bytes(ir_ins->type);
        return result;
    } else { // Everything else, put in a vreg
        return discharge(a, ir_ins);
    }
}

// If operand is IR_KINT, then returns OP_IMM AsmOperand; if operand is an
// IR_LOAD, then returns an OP_MEM AsmOperand; otherwise discharges the operand
// to a vreg
static AsmOperand inline_imm_mem(Assembler *a, IrIns *ir_ins) {
    if (ir_ins->op == IR_IMM) {
        return inline_imm(a, ir_ins);
    } else if (ir_ins->op == IR_LOAD || ir_ins->op == IR_CONST) {
        return inline_mem(a, ir_ins);
    } else { // Otherwise, put it in a vreg
        return discharge(a, ir_ins);
    }
}

static void asm_fp_farg(Assembler *a, IrIns *ir_farg) {
    AsmIns *mov = new_asm(ir_farg->type->prim == T_f32 ? X86_MOVSS : X86_MOVSD);
    ir_farg->vreg = a->next_sse++;
    mov->l.type = OP_XMM;
    mov->l.reg = ir_farg->vreg;
    mov->r.type = OP_XMM;
    // Pull the argument out of the register specified by the ABI
    mov->r.reg = FN_ARGS_SSE_REGS[ir_farg->arg_num];
    emit(a, mov);
}

static void asm_farg(Assembler *a, IrIns *ir_farg) {
    // TODO: read more arguments off the stack
    if (is_fp(ir_farg->type)) {
        asm_fp_farg(a, ir_farg);
        return;
    }
    AsmIns *mov = new_asm(X86_MOV);
    ir_farg->vreg = a->next_gpr++;
    mov->l.type = OP_GPR;
    mov->l.reg = ir_farg->vreg;
    mov->l.size = gpr_size(ir_farg->type);
    mov->r.type = OP_GPR;
    // Pull the argument out of the register specified by the ABI
    mov->r.reg = FN_ARGS_GPRS[ir_farg->arg_num];
    mov->r.size = mov->l.size;
    emit(a, mov);
}

static void asm_alloc(Assembler *a, IrIns *ir_alloc) {
    // Align the stack to the size of the type we're storing
    // IR_ALLOC returns a POINTER to what we want stack space for
    Type *to_alloc = ir_alloc->type->ptr;
    int align = alignment(to_alloc);
    if (a->stack_size % align != 0) { // Stack not already aligned
        a->stack_size += align - (a->stack_size % align);
    }
    a->stack_size += bytes(to_alloc); // Create space on the stack
    ir_alloc->stack_slot = a->stack_size;
}

static void asm_store(Assembler *a, IrIns *ir_store) {
    // The right operand has to be either an immediate or vreg (NOT memory)
    AsmOperand r = inline_imm(a, ir_store->r);
    Type *t = ir_store->r->type;
    AsmOpcode op;
    if (is_fp(t) && t->prim == T_f32) {
        op = X86_MOVSS;
    } else if (is_fp(t) && t->prim == T_f64) {
        op = X86_MOVSD;
    } else {
        op = X86_MOV;
    }
    AsmIns *mov = new_asm(op); // Store into memory
    mov->l = to_mem_operand(a, ir_store->l);
    mov->r = r;
    emit(a, mov);
}

static void asm_load(Assembler *a, IrIns *ir_load) {
    if (ir_load->use_chain && !ir_load->use_chain->next) { // Has a SINGLE use
        // IR_LOADs with a SINGLE use can be folded into the operation that
        // uses them; e.g., 'mov %1, [rbp]; add %2, %1' becomes 'add %2, [rbp]'
        // This is done on the fly by 'inline_mem'
        return;
    }
    // If the load has multiple uses, then it needs to happen just once at the
    // current program point, so discharge it here
    discharge_load(a, ir_load);
}

static void asm_elem(Assembler *a, IrIns *ir_elem) {
    // TODO: can merge chained IR_ELEM instructions
    AsmOperand base = discharge(a, ir_elem->l); // Base always a vreg
    AsmOperand index = inline_imm(a, ir_elem->r);
    if (index.type == OP_IMM && index.imm == 0) {
        // Doesn't modify the pointer! So point to the base pointer
        ir_elem->vreg = base.reg;
        return;
    }

    int index_reg = -1;
    if (index.type == OP_GPR) {
        index_reg = a->next_gpr++;
        AsmIns *mov = new_asm(X86_MOV);
        mov->l.type = OP_GPR;
        mov->l.reg = index_reg;
        mov->r = index;
        emit(a, mov);
        AsmIns *mul = new_asm(X86_MUL); // TODO: mul by 1,2,4,8 can be folded into OP_MEM
        mul->l = mov->l;
        mul->r.type = OP_IMM;
        mul->r.imm = bytes(ir_elem->type->ptr);
        emit(a, mul);
    }

    ir_elem->vreg = a->next_gpr++;
    AsmIns *lea = new_asm(X86_LEA);
    lea->l.type = OP_GPR;
    lea->l.reg = ir_elem->vreg;
    lea->r.type = OP_MEM;
    lea->r.base_reg = base.reg;
    assert(base.size == GPR_Q);
    lea->r.base_size = GPR_Q; // Must be i64
    if (index.type == OP_IMM) {
        lea->r.index_reg = 0;
        lea->r.index_size = GPR_NONE;
        lea->r.scale = 1;
        lea->r.disp = (int64_t) index.imm * bytes(ir_elem->type->ptr);
    } else { // OP_REG otherwise
        lea->r.index_reg = index_reg;
        assert(index.size == GPR_Q);
        lea->r.index_size = GPR_Q; // Must be i64
        lea->r.scale = 1;
        lea->r.disp = 0;
    }
    lea->r.access_size = 0; // Irrelevant for LEA
    emit(a, lea);
}

// Emits arithmetic operation for floating point values
static void asm_fp_arith(Assembler *a, IrIns *ir_arith) {
    AsmOperand l = discharge(a, ir_arith->l); // Left operand always a vreg
    AsmOperand r = inline_imm_mem(a, ir_arith->r);
    ir_arith->vreg = a->next_sse++; // Allocate a new vreg for the result

    AsmIns *mov = new_asm(ir_arith->type->prim == T_f32 ? X86_MOVSS : X86_MOVSD);
    mov->l.type = OP_XMM;
    mov->l.reg = ir_arith->vreg;
    mov->r = l;
    emit(a, mov);

    AsmOpcode op;
    switch (ir_arith->op) {
        case IR_ADD:  op = X86_ADDSS; break;
        case IR_SUB:  op = X86_SUBSS; break;
        case IR_MUL:  op = X86_MULSS; break;
        case IR_FDIV: op = X86_DIVSS; break;
        default: UNREACHABLE();
    }
    if (ir_arith->type->prim == T_f64) {
        op++; // Use SD version for doubles (right after SS opcode)
    }
    AsmIns *arith = new_asm(op);
    arith->l = mov->l;
    arith->r = r;
    emit(a, arith);
}

// Emits an arithmetic operation while lowering from 3-address code to 2-address
// code, i.e., 'a = b + c' becomes 'mov a, b; add a, c'
static void asm_arith(Assembler *a, IrIns *ir_arith) {
    if (is_fp(ir_arith->type)) {
        asm_fp_arith(a, ir_arith);
        return;
    }
    AsmOperand l = discharge(a, ir_arith->l); // Left operand always a vreg
    AsmOperand r = inline_imm_mem(a, ir_arith->r);
    ir_arith->vreg = a->next_gpr++; // Allocate a new vreg for the result

    AsmIns *mov = new_asm(X86_MOV); // Emit a mov for the new vreg
    mov->l.type = OP_GPR;
    mov->l.reg = ir_arith->vreg;
    mov->l.size = l.size;
    mov->r = l;
    emit(a, mov);

    AsmOpcode op;
    switch (ir_arith->op) {
        case IR_ADD:  op = X86_ADD; break;
        case IR_SUB:  op = X86_SUB; break;
        case IR_MUL:  op = X86_MUL; break;
        case IR_AND:  op = X86_AND; break;
        case IR_OR:   op = X86_OR;  break;
        case IR_XOR:  op = X86_XOR; break;
        default: UNREACHABLE();
    }
    AsmIns *arith = new_asm(op);
    arith->l = mov->l;
    arith->r = r;
    emit(a, arith);
}

static void asm_div_mod(Assembler *a, IrIns *ir_div) {
    AsmOperand dividend = discharge(a, ir_div->l); // Left always a vreg
    AsmOperand divisor = inline_mem(a, ir_div->r);

    // TODO: CDQ etc. define rdx; need to make register allocator aware
    AsmIns *mov1 = new_asm(X86_MOV); // Mov dividend into eax
    mov1->l.type = OP_GPR;
    mov1->l.reg = GPR_RAX;
    mov1->l.size = GPR_D;
    mov1->r = dividend;
    emit(a, mov1);

    AsmOpcode ext_op; // Sign extend ?ax into ?dx depending on the size
    switch (bytes(ir_div->type)) {
        case 4:  ext_op = X86_CDQ; break;
        case 8:  ext_op = X86_CQO; break;
        default: ext_op = X86_CWD; break;
    }
    emit(a, new_asm(ext_op));

    AsmOpcode op;
    switch (ir_div->op) {
        case IR_SDIV: case IR_SMOD: op = X86_IDIV; break;
        case IR_UDIV: case IR_UMOD: op = X86_DIV;  break;
        default: UNREACHABLE();
    }
    AsmIns *div = new_asm(op); // Performs edx:eax / <operand>
    div->l = divisor;
    emit(a, div);

    ir_div->vreg = a->next_gpr++; // Allocate a new vreg for the result
    AsmIns *mov2 = new_asm(X86_MOV); // Move the result into a new vreg
    mov2->l.type = OP_GPR;
    mov2->l.reg = ir_div->vreg;
    mov2->l.size = gpr_size(ir_div->type);
    mov2->r.type = OP_GPR;
    if (ir_div->op == IR_SDIV || ir_div->op == IR_UDIV) {
        mov2->r.reg = GPR_RAX; // Division (quotient in rax)
    } else {
        mov2->r.reg = GPR_RDX; // Modulo (remainder in rdx)
    }
    mov2->r.size = mov2->l.size;
    emit(a, mov2);
}

static void asm_shift(Assembler *a, IrIns *ir_shift) {
    AsmOperand l = discharge(a, ir_shift->l); // Left operand always a vreg
    ir_shift->vreg = a->next_gpr++; // Allocate a new vreg for the result

    AsmOperand r = inline_imm(a, ir_shift->r); // Right either immediate or vreg
    if (r.type == OP_GPR) { // If in vreg, shift count has to be in cl
        AsmIns *mov2 = new_asm(X86_MOV); // Move shift count into rcx
        mov2->l.type = OP_GPR;
        mov2->l.reg = GPR_RCX;
        mov2->l.size = r.size;
        mov2->r = r;
        emit(a, mov2);
        r.type = OP_GPR;
        r.reg = GPR_RCX; // Use cl
        r.size = GPR_L;
    }

    AsmIns *mov1 = new_asm(X86_MOV); // Emit a mov for the new vreg
    mov1->l.type = OP_GPR;
    mov1->l.reg = ir_shift->vreg;
    mov1->l.size = l.size;
    mov1->r = l;
    emit(a, mov1);

    AsmOpcode op;
    switch (ir_shift->op) {
        case IR_SHL:  op = X86_SHL; break;
        case IR_ASHR: op = X86_SAR; break;
        case IR_LSHR: op = X86_SHR; break;
        default: UNREACHABLE();
    }
    AsmIns *shift = new_asm(op);
    shift->l = mov1->l;
    shift->r = r;
    emit(a, shift);
}

static void asm_cmp(Assembler *a, IrIns *ir_cmp) {
    AsmOperand l = discharge(a, ir_cmp->l); // Left operand always a vreg
    AsmOperand r = inline_imm_mem(a, ir_cmp->r);
    AsmOpcode op;
    if (is_fp(ir_cmp->l->type)) {
        op = ir_cmp->l->type->prim == T_f32 ? X86_UCOMISS : X86_UCOMISD;
    } else {
        op = X86_CMP;
    }
    AsmIns *cmp = new_asm(op); // Comparison
    cmp->l = l;
    cmp->r = r;
    emit(a, cmp);
}

static void asm_ext(Assembler *a, IrIns *ir_ext, AsmOpcode op) {
    AsmOperand src = inline_imm_mem(a, ir_ext->l);
    ir_ext->vreg = a->next_gpr++; // New vreg for result
    AsmIns *mov = new_asm(op); // Move into a larger reg
    mov->l.type = OP_GPR;
    mov->l.reg = ir_ext->vreg;
    mov->l.size = gpr_size(ir_ext->type);
    mov->r = src;
    emit(a, mov);
}

static void asm_trunc(Assembler *a, IrIns *ir_trunc) {
    AsmOperand src = inline_imm_mem(a, ir_trunc->l);
    ir_trunc->vreg = a->next_gpr++; // New vreg for result
    AsmIns *mov = new_asm(X86_MOV); // Move into a smaller reg
    mov->l.type = OP_GPR;
    mov->l.reg = ir_trunc->vreg;
    // We can't do mov ax, qword [rbp-4]; we have to mov into a register the
    // same size as the SOURCE, then use the truncated register (i.e., ax) in
    // future instructions
    mov->l.size = gpr_size(ir_trunc->l->type);
    mov->r = src;
    emit(a, mov);
}

static void asm_fp_ext_trunc(Assembler *a, IrIns *ir_ext, AsmOpcode op) {
    // https://stackoverflow.com/questions/16597587/why-dont-gcc-and-clang-use-cvtss2sd-memory
    // See the above link for why we don't use cvtxx2xx with a memory operand
    AsmOperand src = discharge(a, ir_ext->l);
    ir_ext->vreg = a->next_sse++; // New vreg for result
    AsmIns *mov = new_asm(op); // Move into a larger reg
    mov->l.type = OP_XMM;
    mov->l.reg = ir_ext->vreg;
    mov->r = src;
    emit(a, mov);
}

static void asm_fp_to_int(Assembler *a, IrIns *ir_conv) {
    AsmOperand src = discharge(a, ir_conv->l);
    ir_conv->vreg = a->next_gpr++; // New vreg for result
    AsmOpcode op = ir_conv->l->type->prim == T_f32 ? X86_CVTTSS2SI :
            X86_CVTTSD2SI;
    AsmIns *mov = new_asm(op); // Move into a larger reg
    mov->l.type = OP_GPR;
    mov->l.reg = ir_conv->vreg;
    mov->l.size = gpr_size(ir_conv->l->type);
    mov->r = src;
    emit(a, mov);
}

static void asm_int_to_fp(Assembler *a, IrIns *ir_conv) {
    AsmOperand src = discharge(a, ir_conv->l);
    ir_conv->vreg = a->next_sse++; // New vreg for result
    AsmOpcode op = ir_conv->type->prim == T_f32 ? X86_CVTSI2SS : X86_CVTSI2SD;
    AsmIns *mov = new_asm(op); // Move into a larger reg
    mov->l.type = OP_XMM;
    mov->l.reg = ir_conv->vreg;
    mov->r = src;
    emit(a, mov);
}

// For IR_PTR2I, IR_I2PTR, IR_PTR2PTR -> we need to maintain SSA form over the
// assembly output, so just emit a mov into a new vreg and let the coalescer
// deal with it.
// We can't just allocate the result of the conversion to the same vreg as its
// source operand, because the source operand might still be used after the
// conversion operand (in which case, the new vreg's lifetime will interfere
// with the source vreg's)
static void asm_ptr_conv(Assembler *a, IrIns *ir_conv) {
    AsmOperand src = inline_imm_mem(a, ir_conv->l);
    ir_conv->vreg = a->next_gpr++; // New vreg for result
    AsmIns *mov = new_asm(X86_MOV);
    mov->l.type = OP_GPR;
    mov->l.reg = ir_conv->vreg;
    mov->l.size = gpr_size(ir_conv->type);
    mov->r = src;
    emit(a, mov);
}

static void asm_br(Assembler *a, IrIns *ir_br) {
    if (ir_br->br == a->bb->next) { // If the branch is to the next BB
        return; // Don't emit_ins a JMP to the very next instruction
    }
    AsmIns *jmp = new_asm(X86_JMP);
    jmp->l.type = OP_LABEL;
    jmp->l.bb = ir_br->br;
    emit(a, jmp);
}

static void asm_cond_br(Assembler *a, IrIns *ir_br) {
    // One of the true case or false case MUST be the next block (either the
    // true case or the false case must fall through)
    assert(ir_br->true == a->bb->next || ir_br->false == a->bb->next);
    asm_cmp(a, ir_br->cond); // Emit a CMP instruction
    AsmOpcode op = IR_OP_TO_JXX[ir_br->cond->op];
    if (a->bb->next == ir_br->true) { // If the true case falls through
        op = INVERT_COND[op]; // Invert the condition
    }
    AsmIns *jmp = new_asm(op); // Emit a conditional JMP instruction
    jmp->l.type = OP_LABEL;
    if (a->bb->next == ir_br->true) { // If true case falls through
        jmp->l.bb = ir_br->false; // Jump to the false block
    } else { // Otherwise, the false case falls through
        jmp->l.bb = ir_br->true; // Jump to the true block
    }
    emit(a, jmp);
}

static void asm_ret0(Assembler *a) {
    AsmIns *pop = new_asm(X86_POP); // pop rbp
    pop->l.type = OP_GPR;
    pop->l.reg = GPR_RBP;
    pop->l.size = GPR_Q;
    emit(a, pop);
    emit(a, new_asm(X86_RET));
}

static void asm_ret1(Assembler *a, IrIns *ir_ret) {
    AsmOperand result = inline_imm_mem(a, ir_ret->l);
    // Make sure to zero the rest of eax by using movsx if the function returns
    // something smaller than an int
    int needs_sext = bits(ir_ret->l->type) < 32;
    AsmIns *mov = new_asm(needs_sext ? X86_MOVSX : X86_MOV);
    mov->l.type = OP_GPR;
    mov->l.reg = GPR_RAX;
    mov->l.size = needs_sext ? GPR_D : gpr_size(ir_ret->l->type);
    mov->r = result;
    emit(a, mov);
    asm_ret0(a);
}

static void asm_ins(Assembler *a, IrIns *ir_ins) {
    switch (ir_ins->op) {
        // Constants - do nothing
    case IR_IMM: case IR_CONST: break;

        // Memory accesses
    case IR_FARG:  asm_farg(a, ir_ins); break;
    case IR_ALLOC: asm_alloc(a, ir_ins); break;
    case IR_STORE: asm_store(a, ir_ins); break;
    case IR_LOAD:  asm_load(a, ir_ins); break;
    case IR_ELEM:  asm_elem(a, ir_ins); break;

        // Arithmetic
    case IR_ADD: case IR_SUB: case IR_MUL: case IR_FDIV:
    case IR_AND: case IR_OR: case IR_XOR:
        asm_arith(a, ir_ins); break;
    case IR_SDIV: case IR_UDIV: case IR_SMOD: case IR_UMOD:
        asm_div_mod(a, ir_ins); break;
    case IR_SHL: case IR_ASHR: case IR_LSHR:
        asm_shift(a, ir_ins); break;

        // Comparisons
    case IR_EQ:  case IR_NEQ:
    case IR_SLT: case IR_SLE: case IR_SGT: case IR_SGE:
    case IR_ULT: case IR_ULE: case IR_UGT: case IR_UGE:
    case IR_FLT: case IR_FLE: case IR_FGT: case IR_FGE:
        break; // Don't do anything; all on CONDBR

        // Conversions
    case IR_TRUNC: asm_trunc(a, ir_ins); break;
    case IR_SEXT:  asm_ext(a, ir_ins, X86_MOVSX); break;
    case IR_ZEXT:  asm_ext(a, ir_ins, X86_MOVZX); break;
    case IR_PTR2I: case IR_I2PTR: case IR_PTR2PTR:
        asm_ptr_conv(a, ir_ins); break;

    case IR_FPEXT:   asm_fp_ext_trunc(a, ir_ins, X86_CVTSS2SD); break;
    case IR_FPTRUNC: asm_fp_ext_trunc(a, ir_ins, X86_CVTSD2SS); break;
    case IR_FP2I:    asm_fp_to_int(a, ir_ins); break;
    case IR_I2FP:    asm_int_to_fp(a, ir_ins); break;

        // Control flow
    case IR_BR:     asm_br(a, ir_ins); break;
    case IR_CONDBR: asm_cond_br(a, ir_ins); break;
    case IR_RET0:   asm_ret0(a); break;
    case IR_RET1:   asm_ret1(a, ir_ins); break;
    default: printf("unsupported IR instruction to assembler\n"); exit(1);
    }
}

static void asm_bb(Assembler *a, BB *ir_bb) {
    for (IrIns *ir_ins = ir_bb->ir_head; ir_ins; ir_ins = ir_ins->next) {
        asm_ins(a, ir_ins);
    }
}

static void asm_fn_preamble(Assembler *a) {
    AsmIns *push = new_asm(X86_PUSH); // push rbp
    push->l.type = OP_GPR;
    push->l.reg = GPR_RBP;
    push->l.size = GPR_Q;
    emit(a, push);
    AsmIns *mov = new_asm(X86_MOV); // mov rbp, rsp
    mov->l.type = OP_GPR;
    mov->l.reg = GPR_RBP;
    mov->l.size = GPR_Q;
    mov->r.type = OP_GPR;
    mov->r.reg = GPR_RSP;
    mov->r.size = GPR_Q;
    emit(a, mov);
}

static void asm_fn(Fn *fn) {
    Assembler a;
    a.fn = fn;
    a.stack_size = 0;
    a.next_gpr = LAST_GPR; // Save the first LAST_GPR for physical registers
    a.next_sse = LAST_SSE;

    a.bb = fn->entry; // Add the function preamble to the entry BB
    asm_fn_preamble(&a);

    for (BB *bb = fn->entry; bb; bb = bb->next) { // Assemble each BB
        a.bb = bb;
        asm_bb(&a, bb);
    }

    fn->num_gprs = a.next_gpr; // Tell the function how many vregs we used
    fn->num_sse_regs = a.next_sse;
}

void assemble(Module *module) {
    for (Fn *fn = module->fns; fn; fn = fn->next) {
        asm_fn(fn);
    }
}
