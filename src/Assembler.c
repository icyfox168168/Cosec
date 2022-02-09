
#include <string.h>
#include <stdio.h>
#include <assert.h>

#include "Assembler.h"

typedef struct {
    BB *bb;         // Current basic block we're assembling
    int stack_size; // Number of bytes allocated on the stack by 'IR_ALLOC's
    int next_reg;       // Next virtual register slot to use
} Assembler;

// Tells us which register each function argument is in, according to the
// System V ABI. The array is indexed by function argument number, where 1 is
// the left-most argument.
//
// 'NUM_FN_ARGS_REGS' tells us how many function arguments are passed via
// registers. After this many arguments, we need to start pulling off the stack.
// #define NUM_FN_ARGS_REGS 6 // No support for stack function arguments yet
static Reg FN_ARGS_REGS[] = {
    REG_RDI,
    REG_RSI,
    REG_RDX,
    REG_RCX,
    REG_R8,
    REG_R9,
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
};

static AsmOpcode INVERT_COND[NUM_X86_OPS] = { // Invert a conditional opcode
    [X86_JE] = X86_JNE, // Jxx
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
    ins->l.size = REG_Q;
    ins->r.type = 0;
    ins->r.reg = 0;
    ins->r.size = REG_Q;
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

static AsmOperand discharge(Assembler *a, IrIns *ins); // Forward declarations
static void asm_cmp(Assembler *a, IrIns *ir_cmp);

// Converts a pointer instruction (i.e., IR_ALLOC, IR_IDX, or some other pointer
// value) to a memory access assembly operand, e.g., to [rbp - 4] or [rax]
static AsmOperand to_mem_operand(Assembler *a, IrIns *ir_ptr) {
    AsmOperand result;
    if (ir_ptr->op == IR_ALLOC) { // Load from stack
        result.type = OP_MEM;  // From memory
        result.base_reg = REG_RBP; // Offset relative to rbp
        result.base_size = REG_Q;
        result.index_reg = 0;
        result.index_size = REG_NONE;
        result.scale = 1;
        result.disp = -ir_ptr->stack_slot;
    } else { // Load from a vreg
        AsmOperand l = discharge(a, ir_ptr);
        result.type = OP_MEM; // From memory
        result.base_reg = l.reg;  // Indexed by a vreg
        result.base_size = l.size; // Should be REG_Q
        assert(l.size == REG_Q);
        result.index_reg = 0;
        result.index_size = REG_NONE;
        result.scale = 1;
        result.disp = 0;
    }
    result.scale = 1;
    Type t = ir_ptr->type;
    t.ptrs--;
    result.access_size = bytes(t); // Number of bytes to read/write
    return result;
}

static AsmOperand discharge_imm(Assembler *a, IrIns *ir_k) {
    ir_k->vreg = a->next_reg++;
    AsmIns *mov = new_asm(X86_MOV);
    mov->l.type = OP_REG;
    mov->l.reg = ir_k->vreg;
    mov->l.size = REG_SIZE[bytes(ir_k->type)];
    mov->r.type = OP_IMM;
    mov->r.imm = ir_k->kint;
    emit(a, mov);
    return mov->l; // The vreg we 'mov'd into is the result
}

static AsmOperand discharge_load(Assembler *a, IrIns *ir_load) {
    ir_load->vreg = a->next_reg++;
    AsmIns *mov = new_asm(X86_MOV);
    mov->l.type = OP_REG; // Load into a vreg
    mov->l.reg = ir_load->vreg;
    mov->l.size = REG_SIZE[bytes(ir_load->type)];
    mov->r = to_mem_operand(a, ir_load->l);
    emit(a, mov);
    return mov->l;
}

static AsmOperand discharge_alloc(Assembler *a, IrIns *ir_alloc) {
    // TODO: pointers must be 8 byte aligned as per C standard!
    ir_alloc->vreg = a->next_reg++;
    AsmIns *lea = new_asm(X86_LEA);
    lea->l.type = OP_REG;
    lea->l.reg = ir_alloc->vreg;
    lea->l.size = REG_SIZE[bytes(ir_alloc->type)];
    lea->r = to_mem_operand(a, ir_alloc);
    lea->r.access_size = 0; // Don't care about bytes for a LEA instruction
    emit(a, lea);
    return lea->l;
}

static AsmOperand discharge_rel(Assembler *a, IrIns *ir_rel) {
    asm_cmp(a, ir_rel); // Emit a comparison instruction
    ir_rel->vreg = a->next_reg++;
    AsmIns *set = new_asm(IR_OP_TO_SETXX[ir_rel->op]); // SETcc operation
    set->l.type = OP_REG;
    set->l.reg = ir_rel->vreg;
    set->l.size = REG_L; // Lowest 8 bits of the vreg
    emit(a, set);
    AsmIns *and = new_asm(X86_AND); // Clear the rest of the vreg
    and->l.type = OP_REG;
    and->l.reg = ir_rel->vreg;
    and->l.size = REG_L; // Lowest 8 bits (ir_rel type is always i1)
    and->r.type = OP_IMM;
    and->r.imm = 1;
    emit(a, and);
    return and->l;
}

// Emits an instruction to a virtual register
static AsmOperand discharge(Assembler *a, IrIns *ins) {
    if (ins->vreg >= 0) { // Already in a vreg
        AsmOperand result;
        result.type = OP_REG;
        result.reg = ins->vreg;
        result.size = REG_SIZE[bytes(ins->type)];
        return result;
    }
    switch (ins->op) {
    case IR_KINT:   return discharge_imm(a, ins);   // Immediate
    case IR_LOAD:   return discharge_load(a, ins);  // Memory load
    case IR_ALLOC:  return discharge_alloc(a, ins); // Pointer load
    case IR_EQ: case IR_NEQ:
    case IR_SLT: case IR_SLE: case IR_SGT: case IR_SGE:
    case IR_ULT: case IR_ULE: case IR_UGT: case IR_UGE:
        return discharge_rel(a, ins); // Comparisons
    default: UNREACHABLE();
    }
}

static AsmOperand inline_mem(Assembler *a, IrIns *ir_load) {
    if (ir_load->op == IR_LOAD) { // Inline a load
        // IR_LOADs are emitted as they happen by 'asm_ins' if they have more
        // than one usage; they're only inlined if they have ONE use
        if (ir_load->vreg >= 0) { // Load has already been emitted
            return discharge(a, ir_load); // Already in a vreg
        }
        return to_mem_operand(a, ir_load->l); // Has only ONE use -> inline
    } else { // Everything else, put in a vreg
        return discharge(a, ir_load);
    }
}

static AsmOperand inline_imm(Assembler *a, IrIns *ir_kint) {
    if (ir_kint->op == IR_KINT) { // Constant
        AsmOperand result;
        result.type = OP_IMM;
        result.imm = ir_kint->kint;
        return result;
    } else {
        return discharge(a, ir_kint);
    }
}

// If operand is IR_KINT, then returns OP_IMM AsmOperand; if operand is an
// IR_LOAD, then returns an OP_MEM AsmOperand; otherwise discharges the operand
// to a vreg
static AsmOperand inline_imm_mem(Assembler *a, IrIns *ir_kint_or_load) {
    // TODO: one potentially useful IR optimisation is if we have commutative
    // arithmetic operations with one operand a LOAD and another not a LOAD,
    // then the load should go in the right hand side so that the assembly
    // can inline the memory operation (note we do the same for constants
    // i.e. put them on the RHS, because that way they get inlined)
    // An example being: long long int a = 3; int b = 4; a = a + b;
    if (ir_kint_or_load->op == IR_KINT) { // Inline a constant integer
        return inline_imm(a, ir_kint_or_load);
    } else if (ir_kint_or_load->op == IR_LOAD) { // Inline a load
        return inline_mem(a, ir_kint_or_load);
    } else { // Otherwise, put it in a vreg
        return discharge(a, ir_kint_or_load);
    }
}

static void asm_farg(Assembler *a, IrIns *ir_farg) {
    AsmIns *mov = new_asm(X86_MOV);
    ir_farg->vreg = a->next_reg++;
    mov->l.type = OP_REG;
    mov->l.reg = ir_farg->vreg;
    mov->l.size = REG_SIZE[bytes(ir_farg->type)];
    mov->r.type = OP_REG;
    // Pull the argument out of the register specified by the ABI
    mov->r.reg = FN_ARGS_REGS[ir_farg->arg_num];
    mov->r.size = mov->l.size;
    emit(a, mov);
}

static void asm_alloc(Assembler *a, IrIns *ir_alloc) {
    Type t = ir_alloc->type;
    t.ptrs -= 1; // IR_ALLOC returns a POINTER to what we want stack space for
    a->stack_size += bytes(t); // Create some space on the stack
    ir_alloc->stack_slot = a->stack_size;
}

static void asm_store(Assembler *a, IrIns *ir_store) {
    // The right operand has to be either an immediate or vreg (NOT memory)
    AsmOperand r = inline_imm(a, ir_store->r);
    AsmIns *mov = new_asm(X86_MOV); // Store into memory
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

static void asm_lea(Assembler *a, IrIns *ir_lea) {
    AsmOperand l = discharge(a, ir_lea->l); // Pointer into a vreg
    AsmOperand offset = inline_imm(a, ir_lea->r); // Right can be imm or vreg
    ir_lea->vreg = a->next_reg++; // Allocate a new vreg for the result

    AsmOperand r;
    r.type = OP_MEM;
    r.base_reg = l.reg;
    r.base_size = l.size; // Should be 8 bytes (size of a pointer)
    r.access_size = 0; // Doesn't apply for lea
    if (offset.type == OP_REG) {
        r.index_reg = offset.reg;
        r.index_size = offset.size; // Should be 8 bytes
        r.disp = 0;
    } else {
        r.index_reg = 0;
        r.index_size = REG_NONE; // No index reg
        r.disp = offset.imm;
    }

    AsmIns *mov = new_asm(X86_LEA);
    mov->l.type = OP_REG;
    mov->l.reg = ir_lea->vreg;
    mov->l.size = l.size;
    mov->r = r;
    emit(a, mov);
}

// Emits an arithmetic operation while lowering from 3-address code to 2-address
// code, i.e., 'a = b + c' becomes 'mov a, b; add a, c'
static void asm_arith(Assembler *a, IrIns *ir_arith) {
    AsmOperand l = discharge(a, ir_arith->l); // Left operand always a vreg
    AsmOperand r = inline_imm_mem(a, ir_arith->r);
    ir_arith->vreg = a->next_reg++; // Allocate a new vreg for the result

    AsmIns *mov = new_asm(X86_MOV); // Emit a mov for the new vreg
    mov->l.type = OP_REG;
    mov->l.reg = ir_arith->vreg;
    mov->l.size = l.size;
    mov->r = l;
    emit(a, mov);

    AsmOpcode op;
    switch (ir_arith->op) {
        case IR_ADD: op = X86_ADD; break;
        case IR_SUB: op = X86_SUB; break;
        case IR_MUL: op = X86_MUL; break;
        case IR_AND: op = X86_AND; break;
        case IR_OR:  op = X86_OR;  break;
        case IR_XOR: op = X86_XOR; break;
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

    // TODO: doesn't work for i64s
    AsmIns *mov1 = new_asm(X86_MOV); // Mov dividend into eax
    mov1->l.type = OP_REG;
    mov1->l.reg = REG_RAX;
    mov1->l.size = REG_D;
    mov1->r = dividend;
    emit(a, mov1);
    emit(a, new_asm(X86_CDQ)); // Sign extend eax into edx

    AsmOpcode op;
    switch (ir_div->op) {
        case IR_SDIV: case IR_SMOD: op = X86_IDIV; break;
        case IR_UDIV: case IR_UMOD: op = X86_DIV;  break;
        default: UNREACHABLE();
    }
    AsmIns *div = new_asm(op); // Performs edx:eax / <operand>
    div->l = divisor;
    emit(a, div);

    ir_div->vreg = a->next_reg++; // Allocate a new vreg for the result
    AsmIns *mov2 = new_asm( X86_MOV); // Move the result into a new vreg
    mov2->l.type = OP_REG;
    mov2->l.reg = ir_div->vreg;
    mov2->l.size = REG_SIZE[bytes(ir_div->type)];
    mov2->r.type = OP_REG;
    if (ir_div->op == IR_SDIV || ir_div->op == IR_UDIV) {
        mov2->r.reg = REG_RAX; // Division (quotient in rax)
    } else {
        mov2->r.reg = REG_RDX; // Modulo (remainder in rdx)
    }
    mov2->r.size = mov2->l.size;
    emit(a, mov2);
}

static void asm_shift(Assembler *a, IrIns *ir_shift) {
    AsmOperand l = discharge(a, ir_shift->l); // Left operand always a vreg
    ir_shift->vreg = a->next_reg++; // Allocate a new vreg for the result

    AsmOperand r = inline_imm(a, ir_shift->r); // Right operand either an immediate or cl
    if (r.type == OP_REG) { // If in vreg, shift count has to be in cl
        AsmIns *mov2 = new_asm(X86_MOV); // Move shift count into rcx
        mov2->l.type = OP_REG;
        mov2->l.reg = REG_RCX;
        mov2->l.size = r.size;
        mov2->r = r;
        emit(a, mov2);
        r.type = OP_REG;
        r.reg = REG_RCX; // Use cl
        r.size = REG_L;
    }

    AsmIns *mov1 = new_asm(X86_MOV); // Emit a mov for the new vreg
    mov1->l.type = OP_REG;
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
    AsmIns *cmp = new_asm(X86_CMP); // Comparison
    cmp->l = l;
    cmp->r = r;
    emit(a, cmp);
}

static void asm_ext(Assembler *a, IrIns *ir_ext) {
    AsmOpcode op = ir_ext->op == IR_ZEXT ? X86_MOVZX : X86_MOVSX;
    AsmOperand src = inline_imm_mem(a, ir_ext->l);
    ir_ext->vreg = a->next_reg++; // New vreg for result
    AsmIns *mov = new_asm(op); // Move into a smaller reg
    mov->l.type = OP_REG;
    mov->l.reg = ir_ext->vreg;
    mov->l.size = REG_SIZE[bytes(ir_ext->type)];
    mov->r = src;
    emit(a, mov);
}

static void asm_trunc(Assembler *a, IrIns *ir_trunc) {
    AsmOperand src = inline_imm_mem(a, ir_trunc->l);
    ir_trunc->vreg = a->next_reg++; // New vreg for result
    AsmIns *mov = new_asm(X86_MOV); // Move into a smaller reg
    mov->l.type = OP_REG;
    mov->l.reg = ir_trunc->vreg;
    // We can't do mov ax, qword [rbp-4]; we have to mov into a register the
    // same size as the SOURCE, then use the truncated register (i.e., ax) in
    // future instructions
    mov->l.size = REG_SIZE[bytes(ir_trunc->l->type)];
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
static void asm_conv(Assembler *a, IrIns *ir_conv) {
    AsmOperand src = inline_imm_mem(a, ir_conv->l);
    ir_conv->vreg = a->next_reg++; // New vreg for result
    AsmIns *mov = new_asm(X86_MOV);
    mov->l.type = OP_REG;
    mov->l.reg = ir_conv->vreg;
    mov->l.size = REG_SIZE[bytes(ir_conv->type)];
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
    pop->l.type = OP_REG;
    pop->l.reg = REG_RBP;
    pop->l.size = REG_Q;
    emit(a, pop);
    emit(a, new_asm(X86_RET));
}

static void asm_ret1(Assembler *a, IrIns *ir_ret) {
    AsmOperand result = inline_imm_mem(a, ir_ret->l);
    // Make sure to zero the rest of eax by using movsx if the function returns
    // something smaller than an int
    int needs_sext = bits(ir_ret->l->type) < 32;
    AsmIns *mov = new_asm(needs_sext ? X86_MOVSX : X86_MOV);
    mov->l.type = OP_REG;
    mov->l.reg = REG_RAX;
    mov->l.size = needs_sext ? REG_D : REG_SIZE[bytes(ir_ret->l->type)];
    mov->r = result;
    emit(a, mov);
    asm_ret0(a);
}

static void asm_ins(Assembler *a, IrIns *ir_ins) {
    switch (ir_ins->op) {
        // Constants
    case IR_KINT:  break; // Don't do anything for constants

        // Memory accesses
    case IR_FARG:  asm_farg(a, ir_ins); break;
    case IR_ALLOC: asm_alloc(a, ir_ins); break;
    case IR_STORE: asm_store(a, ir_ins); break;
    case IR_LOAD:  asm_load(a, ir_ins); break;
    case IR_LEA:   asm_lea(a, ir_ins); break;

        // Arithmetic
    case IR_ADD: case IR_SUB: case IR_MUL:
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
        break; // Don't do anything

        // Conversions
    case IR_TRUNC: asm_trunc(a, ir_ins); break;
    case IR_SEXT: case IR_ZEXT: asm_ext(a, ir_ins); break;
    case IR_PTR2I: case IR_I2PTR: case IR_PTR2PTR: asm_conv(a, ir_ins); break;

        // Control flow
    case IR_BR:      asm_br(a, ir_ins); break;
    case IR_CONDBR:  asm_cond_br(a, ir_ins); break;
    case IR_RET0:    asm_ret0(a); break;
    case IR_RET1:    asm_ret1(a, ir_ins); break;
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
    push->l.type = OP_REG;
    push->l.reg = REG_RBP;
    push->l.size = REG_Q;
    emit(a, push);
    AsmIns *mov = new_asm(X86_MOV); // mov rbp, rsp
    mov->l.type = OP_REG;
    mov->l.reg = REG_RBP;
    mov->l.size = REG_Q;
    mov->r.type = OP_REG;
    mov->r.reg = REG_RSP;
    mov->r.size = REG_Q;
    emit(a, mov);
}

static void asm_fn(Assembler *a, Fn *fn) {
    a->bb = fn->entry;
    a->stack_size = 0; // Reset for this function
    a->next_reg = LAST_PREG; // Save the first LAST_PREG for physical registers

    asm_fn_preamble(a); // Add the function preamble to the entry BB
    for (BB *bb = fn->entry; bb; bb = bb->next) { // Assemble each BB
        a->bb = bb;
        asm_bb(a, bb);
    }
    fn->num_regs = a->next_reg;
}

// The 'main' function isn't the first thing that gets executed when the kernel
// launches a user-space program, it's the 'start' function. 'start' performs
// some set-up and shut-down things before and after calling 'main':
// 1. Puts the arguments to 'main' (argc, argv, envp; given by the kernel on
//    the stack) into registers according to the ABI calling convention
// 2. Calls the 'exit' syscall after 'main' is finished
//
// The full start stub is (see https://en.wikipedia.org/wiki/Crt0):
// _start:
//     xor ebp, ebp         ; Effectively zero rbp
//     mov edi, [rsp]       ; Take argc off the stack
//     lea rsi, [rsp+8]     ; Take argv off the stack
//     lea rdx, [rsp+16]    ; Take envp off the stack
//     xor eax, eax         ; Convention per ABI
//     call main            ; Call the main function
//     mov rdi, rax         ; Exit syscall
//     mov rax, 0x2000001
//     syscall
static Fn * asm_start(Assembler *a, Fn *main) {
    Fn *start = new_fn();
    start->name = "_start";
    BB *entry = new_bb();
    start->entry = entry;

    a->bb = entry;
    AsmIns *i;
    i = new_asm(X86_XOR); // Zero rbp
    i->l.type = OP_REG; i->l.reg = REG_RBP; i->l.size = REG_D;
    i->r.type = OP_REG; i->r.reg = REG_RBP; i->r.size = REG_D;
    emit(a, i);
    i = new_asm(X86_MOV); // Take argc off the stack
    i->l.type = OP_REG; i->l.reg = REG_RDI; i->l.size = REG_D;
    i->r.type = OP_MEM; i->r.base_reg = REG_RSP; i->r.base_size = REG_Q;
    i->r.index_reg = 0; i->r.index_size = REG_NONE; i->r.scale = 1;
    i->r.disp = 0; i->r.access_size = 4;
    emit(a, i);
    i = new_asm(X86_LEA); // Take argv off the stack
    i->l.type = OP_REG; i->l.reg = REG_RSI; i->l.size = REG_Q;
    i->r.type = OP_MEM; i->r.base_reg = REG_RSP; i->r.base_size = REG_Q;
    i->r.index_reg = 0; i->r.index_size = REG_NONE; i->r.scale = 1;
    i->r.disp = 8; i->r.access_size = 8;
    emit(a, i);
    i = new_asm(X86_LEA); // Take envp off the stack
    i->l.type = OP_REG; i->l.reg = REG_RDX; i->l.size = REG_Q;
    i->r.type = OP_MEM; i->r.base_reg = REG_RSP; i->r.base_size = REG_Q;
    i->r.index_reg = 0; i->r.index_size = REG_NONE; i->r.scale = 1;
    i->r.disp = 16; i->r.access_size = 8;
    emit(a, i);
    i = new_asm(X86_XOR); // Zero eax (convention per ABI)
    i->l.type = OP_REG; i->l.reg = REG_RAX; i->l.size = REG_D;
    i->r.type = OP_REG; i->r.reg = REG_RAX; i->r.size = REG_D;
    emit(a, i);
    i = new_asm(X86_CALL); // Call main
    i->l.type = OP_FN; i->l.fn = main;
    emit(a, i);
    i = new_asm(X86_MOV); // syscall to exit
    i->l.type = OP_REG; i->l.reg = REG_RDI; i->l.size = REG_Q;
    i->r.type = OP_REG; i->r.reg = REG_RAX; i->l.size = REG_Q;
    emit(a, i);
    i = new_asm(X86_MOV);
    i->l.type = OP_REG; i->l.reg = REG_RAX; i->l.size = REG_Q;
    i->r.type = OP_IMM; i->r.imm = 0x2000001;
    emit(a, i);
    emit(a, new_asm(X86_SYSCALL));
    return start;
}

void assemble(Module *module) {
    Assembler a;
    a.bb = NULL;

    for (Fn *fn = module->fns; fn; fn = fn->next) {
        if (strcmp(fn->name, "main") == 0) {
            module->main = fn; // Set the main function
        }
        asm_fn(&a, fn);
    }
    // Insert a 'start' stub if this module has a main function
    if (module->main) {
        Fn *start = asm_start(&a, module->main);
        start->next = module->fns;
        module->fns = start;
    }
}
