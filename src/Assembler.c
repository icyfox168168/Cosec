
#include <string.h>
#include <stdio.h>
#include <assert.h>

#include "Assembler.h"

typedef struct {
    BB *bb;         // Current basic block we're assembling
    int stack_size; // Number of bytes allocated on the stack by 'IR_ALLOC's
    int vreg;       // Next virtual register slot to use
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

static Assembler new_asm() {
    Assembler a;
    a.bb = NULL;
    a.stack_size = 0;
    a.vreg = 0;
    return a;
}

static AsmIns * emit(Assembler *a, AsmOpcode op) {
    return emit_asm(a->bb, op);
}

// Converts an IR_LOAD instruction to a memory access assembly operand, e.g.,
// to [rbp - 4]
static AsmOperand load_to_mem_operand(IrIns *ir_load) {
    AsmOperand operand;
    operand.type = OP_MEM;  // From memory
    operand.base = REG_RBP; // Offset relative to rbp
    operand.size = REG_Q;
    operand.scale = 1;
    operand.bytes = bytes(ir_load->type); // Number of bytes to read
    operand.index = -ir_load->l->stack_slot;
    return operand;
}

// Converts an IR_STORE instruction to a memory access assembly operand
static AsmOperand store_to_mem_operand(IrIns *ir_store) {
    AsmOperand operand;
    operand.type = OP_MEM;  // From memory
    operand.base = REG_RBP; // Offset relative to rbp
    operand.size = REG_Q;
    operand.scale = 1;
    Type t = ir_store->l->type;
    t.ptrs--;
    operand.bytes = bytes(t); // Number of bytes to write
    operand.index = -ir_store->l->stack_slot;
    return operand;
}

static AsmOperand discharge(Assembler *a, IrIns *ins); // Forward declarations
static void asm_cmp(Assembler *a, IrIns *ir_cmp);

static AsmOperand discharge_imm(Assembler *a, IrIns *ir_k) {
    ir_k->vreg = a->vreg++;
    AsmIns *mov = emit(a, X86_MOV);
    mov->l.type = OP_VREG;
    mov->l.vreg = ir_k->vreg;
    mov->l.size = REG_SIZE[bytes(ir_k->type)];
    mov->r.type = OP_IMM;
    mov->r.imm = ir_k->kint;
    return mov->l; // The vreg we 'mov'd into is the result
}

static AsmOperand discharge_load(Assembler *a, IrIns *ir_load) {
    assert(ir_load->l->op == IR_ALLOC); // Only IR_ALLOC can create pointers
    ir_load->vreg = a->vreg++;
    AsmIns *mov = emit(a, X86_MOV);
    mov->l.type = OP_VREG; // Load into a vreg
    mov->l.vreg = ir_load->vreg;
    mov->l.size = REG_SIZE[bytes(ir_load->type)];
    mov->r = load_to_mem_operand(ir_load);
    return mov->l;
}

static AsmOperand discharge_rel(Assembler *a, IrIns *ir_rel) {
    asm_cmp(a, ir_rel); // Emit a comparison instruction
    ir_rel->vreg = a->vreg++;
    AsmIns *set = emit(a, IR_OP_TO_SETXX[ir_rel->op]); // SETcc operation
    set->l.type = OP_VREG;
    set->l.vreg = ir_rel->vreg;
    set->l.size = REG_L; // Lowest 8 bits of the vreg
    AsmIns *and = emit(a, X86_AND); // Clear the rest of the vreg
    and->l.type = OP_VREG;
    and->l.vreg = ir_rel->vreg;
    and->l.size = REG_L; // Lowest 8 bits (ir_rel type is always i1)
    and->r.type = OP_IMM;
    and->r.imm = 1;
    return and->l;
}

// Emits an instruction to a virtual register
static AsmOperand discharge(Assembler *a, IrIns *ins) {
    if (ins->vreg >= 0) { // Already in a vreg
        AsmOperand result;
        result.type = OP_VREG;
        result.vreg = ins->vreg;
        result.size = REG_SIZE[bytes(ins->type)];
        return result;
    }
    switch (ins->op) {
    case IR_KINT:
        return discharge_imm(a, ins); // Immediate
    case IR_LOAD:
        return discharge_load(a, ins); // Memory load
    case IR_EQ: case IR_NEQ:
    case IR_SLT: case IR_SLE: case IR_SGT: case IR_SGE:
    case IR_ULT: case IR_ULE: case IR_UGT: case IR_UGE:
        return discharge_rel(a, ins); // Comparisons
    default: UNREACHABLE();
    }
}

// If a load has already been emitted, then returns the vreg it was loaded
// into. Otherwise, returns a memory AsmOperand that can be used for the load
static AsmOperand fold_load(Assembler *a, IrIns *ir_load) {
    if (ir_load->vreg >= 0) {
        return discharge(a, ir_load); // Already in a vreg
    }
    // Otherwise, only has ONE use, so inline the load
    return load_to_mem_operand(ir_load);
}

static void asm_farg(Assembler *a, IrIns *ir_farg) {
    AsmIns *mov = emit(a, X86_MOV);
    ir_farg->vreg = a->vreg++;
    mov->l.type = OP_VREG;
    mov->l.vreg = ir_farg->vreg;
    mov->l.size = REG_SIZE[bytes(ir_farg->type)];
    mov->r.type = OP_REG;
    // Pull the argument out of the register specified by the ABI
    mov->r.reg = FN_ARGS_REGS[ir_farg->arg_num];
    mov->r.size = mov->l.size;
}

static void asm_alloc(Assembler *a, IrIns *ir_alloc) {
    Type t = ir_alloc->type;
    t.ptrs -= 1; // IR_ALLOC returns a POINTER to what we want stack space for
    a->stack_size += bytes(t); // Create some space on the stack
    ir_alloc->stack_slot = a->stack_size;
    // Create a vreg for the POINTER returned by the ALLOC instruction
    ir_alloc->vreg = a->vreg++;
}

static void asm_store(Assembler *a, IrIns *ir_store) {
    assert(ir_store->l->op == IR_ALLOC); // Only source of pointers is IR_ALLOC
    AsmOperand r; // Right operand either an immediate or vreg (not memory)
    if (ir_store->r->op == IR_KINT) { // Constant
        r.type = OP_IMM;
        r.imm = ir_store->r->kint;
    } else {
        r = discharge(a, ir_store->r); // vreg
    }
    AsmIns *mov = emit(a, X86_MOV); // Store into memory
    mov->l = store_to_mem_operand(ir_store);
    mov->r = r;
}

static void asm_load(Assembler *a, IrIns *ir_load) {
    if (ir_load->use_chain && !ir_load->use_chain->next) { // Has a SINGLE use
        // IR_LOADs with a SINGLE use can be folded into the operation that
        // uses them; e.g., 'mov %1, [rbp]; add %2, %1' becomes 'add %2, [rbp]'
        // This is done on the fly by 'fold_load'
        return;
    }
    // If the load has multiple uses, then it needs to happen just once, so
    // discharge it here
    discharge_load(a, ir_load);
}

// Emits an arithmetic operation while lowering from 3-address code to 2-address
// code, i.e., 'a = b + c' becomes 'mov a, b; add a, c'
static void asm_arith(Assembler *a, IrIns *ir_arith) {
    AsmOperand l = discharge(a, ir_arith->l); // Left operand always a vreg
    ir_arith->vreg = a->vreg++; // Allocate a new vreg for the result

    AsmIns *mov = emit(a, X86_MOV); // Emit a mov for the new vreg
    mov->l.type = OP_VREG;
    mov->l.vreg = ir_arith->vreg;
    mov->l.size = l.size;
    mov->r = l;

    AsmOperand r;
    if (ir_arith->r->op == IR_KINT) {
        r.type = OP_IMM;
        r.imm = ir_arith->r->kint;
    } else if (ir_arith->r->op == IR_LOAD) {
        r = fold_load(a, ir_arith->r);
    } else {
        r = discharge(a, ir_arith->r);
    }

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
    AsmIns *arith = emit(a, op);
    arith->l = mov->l;
    arith->r = r;
}

static void asm_div_mod(Assembler *a, IrIns *ir_div) {
    AsmOperand dividend = discharge(a, ir_div->l); // Left always a vreg
    AsmOperand divisor;
    if (ir_div->r->op == IR_LOAD) {
        divisor = fold_load(a, ir_div->r);
    } else { // Including immediate (can't divide by immediate)
        divisor = discharge(a, ir_div->r);
    }

    AsmIns *mov1 = emit(a, X86_MOV); // Mov dividend into eax
    mov1->l.type = OP_REG;
    mov1->l.reg = REG_RAX;
    mov1->l.size = REG_D;
    mov1->r = dividend;
    emit(a, X86_CDQ); // Sign extend eax into edx

    AsmIns *div = emit(a, X86_IDIV); // Performs edx:eax / <operand>
    div->l = divisor;

    ir_div->vreg = a->vreg++; // Allocate a new vreg for the result
    AsmIns *mov2 = emit(a, X86_MOV); // Move the result into a new vreg
    mov2->l.type = OP_VREG;
    mov2->l.vreg = ir_div->vreg;
    mov2->l.size = REG_SIZE[bytes(ir_div->type)];
    mov2->r.type = OP_REG;
    if (ir_div->op == IR_DIV) {
        mov2->r.reg = REG_RAX; // Division (quotient in rax)
    } else {
        mov2->r.reg = REG_RDX; // Modulo (remainder in rdx)
    }
    mov2->r.size = mov2->l.size;
}

static void asm_shift(Assembler *a, IrIns *ir_shift) {
    AsmOperand l = discharge(a, ir_shift->l); // Left operand always a vreg
    ir_shift->vreg = a->vreg++; // Allocate a new vreg for the result

    AsmIns *mov1 = emit(a, X86_MOV); // Emit a mov for the new vreg
    mov1->l.type = OP_VREG;
    mov1->l.vreg = ir_shift->vreg;
    mov1->l.size = l.size;
    mov1->r = l;

    AsmOperand r; // Right operand either an immediate or cl
    if (ir_shift->r->op == IR_KINT) { // Can shift by an immediate
        r.type = OP_IMM;
        r.imm = ir_shift->r->kint;
    } else { // Otherwise, shift count has to be in cl
        AsmOperand discharged = discharge(a, ir_shift->r);
        AsmIns *mov2 = emit(a, X86_MOV); // Move shift count into rcx
        mov2->l.type = OP_REG;
        mov2->l.reg = REG_RCX;
        mov2->l.size = discharged.size;
        mov2->r = discharged;
        r.type = OP_REG;
        r.reg = REG_RCX; // Use cl
        r.size = REG_L;
    }

    AsmOpcode op;
    switch (ir_shift->op) {
        case IR_SHL:  op = X86_SHL; break;
        case IR_ASHR: op = X86_SAR; break;
        case IR_LSHR: op = X86_SHR; break;
        default: UNREACHABLE();
    }
    AsmIns *shift = emit(a, op);
    shift->l = mov1->l;
    shift->r = r;
}

static void asm_cmp(Assembler *a, IrIns *ir_cmp) {
    AsmOperand l = discharge(a, ir_cmp->l); // Left operand always a vreg
    AsmOperand r;
    if (ir_cmp->r->op == IR_KINT) {
        r.type = OP_IMM;
        r.imm = ir_cmp->r->kint;
    } else if (ir_cmp->r->op == IR_LOAD) {
        r = fold_load(a, ir_cmp->r);
    } else {
        r = discharge(a, ir_cmp->r);
    }
    AsmIns *cmp = emit(a, X86_CMP); // Comparison
    cmp->l = l;
    cmp->r = r;
}

static void asm_trunc_or_ext(Assembler *a, IrIns *ir_trunc_ext, AsmOpcode op) {
    AsmOperand l = discharge(a, ir_trunc_ext->l);
    ir_trunc_ext->vreg = a->vreg++; // New vreg for result
    AsmIns *mov = emit(a, op); // Move into a smaller reg
    mov->l.type = OP_VREG;
    mov->l.vreg = ir_trunc_ext->vreg;
    mov->l.size = REG_SIZE[bytes(ir_trunc_ext->type)];
    mov->r.type = OP_VREG;
    mov->r.vreg = l.vreg;
    mov->r.size = REG_SIZE[bytes(ir_trunc_ext->l->type)];
}

static void asm_trunc(Assembler *a, IrIns *ir_trunc) {
    asm_trunc_or_ext(a, ir_trunc, X86_MOV); // Regular mov
}

static void asm_sext(Assembler *a, IrIns *ir_sext) {
    asm_trunc_or_ext(a, ir_sext, X86_MOVSX); // Sign extend
}

static void asm_zext(Assembler *a, IrIns *ir_zext) {
    asm_trunc_or_ext(a, ir_zext, X86_MOVZX); // Zero extend
}

static void asm_br(Assembler *a, IrIns *ir_br) {
    if (ir_br->br == a->bb->next) { // If the branch is to the next BB
        return; // Don't emit_ins a JMP to the very next instruction
    }
    AsmIns *jmp = emit(a, X86_JMP);
    jmp->l.type = OP_LABEL;
    jmp->l.bb = ir_br->br;
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
    AsmIns *jmp = emit(a, op); // Emit a conditional JMP instruction
    jmp->l.type = OP_LABEL;
    if (a->bb->next == ir_br->true) { // If true case falls through
        jmp->l.bb = ir_br->false; // Jump to the false block
    } else { // Otherwise, the false case falls through
        jmp->l.bb = ir_br->true; // Jump to the true block
    }
}

static void asm_ret0(Assembler *a) {
    AsmIns *pop = emit(a, X86_POP); // pop rbp
    pop->l.type = OP_REG;
    pop->l.reg = REG_RBP;
    pop->l.size = REG_Q;
    emit(a, X86_RET);
}

static void asm_ret1(Assembler *a, IrIns *ir_ret) {
    AsmOperand result = discharge(a, ir_ret->l);
    AsmIns *mov = emit(a, X86_MOV); // mov rax, <value>
    mov->l.type = OP_REG;
    mov->l.reg = REG_RAX;
    mov->l.size = REG_SIZE[bytes(ir_ret->l->type)];
    mov->r = result;
    asm_ret0(a);
}

static void asm_ins(Assembler *a, IrIns *ir_ins) {
    switch (ir_ins->op) {
    case IR_KINT:  break; // Don't do anything for constants
    case IR_FARG:  asm_farg(a, ir_ins); break;
    case IR_ALLOC: asm_alloc(a, ir_ins); break;
    case IR_LOAD:  asm_load(a, ir_ins); break;
    case IR_STORE: asm_store(a, ir_ins); break;
    case IR_ADD: case IR_SUB: case IR_MUL:
    case IR_AND: case IR_OR: case IR_XOR:
        asm_arith(a, ir_ins); break;
    case IR_DIV: case IR_MOD:
        asm_div_mod(a, ir_ins); break;
    case IR_SHL: case IR_ASHR: case IR_LSHR:
        asm_shift(a, ir_ins); break;
    case IR_EQ:  case IR_NEQ:
    case IR_SLT: case IR_SLE: case IR_SGT: case IR_SGE:
    case IR_ULT: case IR_ULE: case IR_UGT: case IR_UGE:
        break; // Don't do anything for comparisons
    case IR_TRUNC:  asm_trunc(a, ir_ins); break;
    case IR_SEXT:   asm_sext(a, ir_ins); break;
    case IR_ZEXT:   asm_zext(a, ir_ins); break;
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
    AsmIns *ins;
    ins = emit(a, X86_PUSH); // push rbp
    ins->l.type = OP_REG;
    ins->l.reg = REG_RBP;
    ins->l.size = REG_Q;
    ins = emit(a, X86_MOV); // mov rbp, rsp
    ins->l.type = OP_REG;
    ins->l.reg = REG_RBP;
    ins->l.size = REG_Q;
    ins->r.type = OP_REG;
    ins->r.reg = REG_RSP;
    ins->r.size = REG_Q;
}

static void asm_fn(Fn *fn) {
    Assembler a = new_asm();
    a.bb = fn->entry;
    asm_fn_preamble(&a); // Add the function preamble to the entry BB
    for (BB *bb = fn->entry; bb; bb = bb->next) { // Assemble each BB
        a.bb = bb;
        asm_bb(&a, bb);
    }
    fn->num_vregs = a.vreg;
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
static Fn * asm_start(Fn *main) {
    Fn *start = new_fn();
    start->name = "_start";
    BB *entry = new_bb();
    start->entry = entry;

    Assembler a = new_asm();
    a.bb = entry;

    AsmIns *i;
    i = emit(&a, X86_XOR); // Zero rbp
    i->l.type = OP_REG; i->l.reg = REG_RBP; i->l.size = REG_D;
    i->r.type = OP_REG; i->r.reg = REG_RBP; i->r.size = REG_D;
    i = emit(&a, X86_MOV); // Take argc off the stack
    i->l.type = OP_REG; i->l.reg = REG_RDI; i->l.size = REG_D;
    i->r.type = OP_MEM; i->r.base = REG_RSP; i->r.size = REG_Q; i->r.scale = 1;
    i->r.index = 0; i->r.bytes = 4;
    i = emit(&a, X86_LEA); // Take argv off the stack
    i->l.type = OP_REG; i->l.reg = REG_RSI; i->l.size = REG_Q;
    i->r.type = OP_MEM; i->r.base = REG_RSP; i->r.size = REG_Q; i->r.scale = 1;
    i->r.index = 8; i->r.bytes = 8;
    i = emit(&a, X86_LEA); // Take envp off the stack
    i->l.type = OP_REG; i->l.reg = REG_RDX; i->l.size = REG_Q;
    i->r.type = OP_MEM; i->r.base = REG_RSP; i->r.size = REG_Q; i->r.scale = 1;
    i->r.index = 16; i->r.bytes = 8;
    i = emit(&a, X86_XOR); // Zero eax (convention per ABI)
    i->l.type = OP_REG; i->l.reg = REG_RAX; i->l.size = REG_D;
    i->r.type = OP_REG; i->r.reg = REG_RAX; i->r.size = REG_D;
    i = emit(&a, X86_CALL); // Call main
    i->l.type = OP_FN; i->l.fn = main;
    i = emit(&a, X86_MOV); // syscall to exit
    i->l.type = OP_REG; i->l.reg = REG_RDI; i->l.size = REG_Q;
    i->r.type = OP_REG; i->r.reg = REG_RAX; i->l.size = REG_Q;
    i = emit(&a, X86_MOV);
    i->l.type = OP_REG; i->l.reg = REG_RAX; i->l.size = REG_Q;
    i->r.type = OP_IMM; i->r.imm = 0x2000001;
    emit(&a, X86_SYSCALL);
    return start;
}

void assemble(Module *module) {
    module->main = module->fns; // TODO: first function is 'main'
    for (Fn *fn = module->fns; fn; fn = fn->next) {
        asm_fn(fn);
    }
    Fn *start = asm_start(module->main); // Insert 'start' stub
    module->fns->next = start;
}
