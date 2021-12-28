
#include <string.h>
#include <stdio.h>
#include <assert.h>

#include "Assembler.h"

typedef struct {
    AsmFn *fn;
    AsmIns **ins;
    int stack_size; // Number of bytes allocated on the stack by 'IR_ALLOC's
    int vreg; // Next virtual register slot to use
} Assembler;

static AsmIns * emit(Assembler *a, AsmOp op) {
    AsmIns *ins = malloc(sizeof(AsmIns));
    ins->next = NULL;
    ins->op = op;
    ins->l.type = 0;
    ins->l.vreg = 0;
    ins->l.subsection = REG_ALL;
    ins->r.type = 0;
    ins->r.vreg = 0;
    ins->r.subsection = REG_ALL;
    *a->ins = ins;
    a->ins = &ins->next;
    return ins;
}

static AsmOperand discharge(Assembler *a, IrIns *ins); // Forward declaration

static AsmOperand discharge_imm(Assembler *a, IrIns *ir_k) {
    ir_k->vreg = a->vreg++;
    AsmIns *mov = emit(a, X86_MOV);
    mov->l.type = OP_VREG;
    mov->l.vreg = ir_k->vreg;
    mov->r.type = OP_IMM; // Immediate
    mov->r.imm = ir_k->ki32;
    AsmOperand result = {.type = OP_VREG, .vreg = ir_k->vreg};
    return result;
}

static AsmOperand discharge_load(Assembler *a, IrIns *ir_load) {
    assert(ir_load->l->type.ptrs >= 1); // Can only ir_load from a pointer
    assert(ir_load->l->op == IR_ALLOC); // Only source of pointers at the moment is IR_ALLOC
    ir_load->vreg = a->vreg++;
    AsmIns *mov = emit(a, X86_MOV);
    mov->l.type = OP_VREG;
    mov->l.vreg = ir_load->vreg;
    mov->r.type = OP_MEM; // Memory ir_load
    mov->r.base = REG_RBP;
    mov->r.scale = 1;
    mov->r.index = -ir_load->l->stack_slot;
    AsmOperand result = {.type = OP_VREG, .vreg = ir_load->vreg};
    return result;
}

static AsmOperand discharge_rel(Assembler *a, IrIns *ir_rel) {
    AsmOperand l = discharge(a, ir_rel->l); // Left operand to cmp always a vreg
    AsmOperand r;
    if (ir_rel->r->op == IR_KI32) {
        r.type = OP_IMM;
        r.imm = ir_rel->r->ki32;
    } else if (ir_rel->r->op == IR_LOAD) {
        IrIns *ir_load = ir_rel->r;
        r.type = OP_MEM;
        r.base = REG_RBP;
        r.scale = 1;
        r.index = -ir_load->l->stack_slot;
    } else {
        r = discharge(a, ir_rel->r);
    }
    AsmIns *cmp = emit(a, X86_CMP); // Comparison
    cmp->l = l;
    cmp->r = r;

    ir_rel->vreg = a->vreg++;
    AsmIns *set = emit(a, IROP_TO_SETXX[ir_rel->op]); // SETcc operation
    set->l.type = OP_VREG;
    set->l.vreg = ir_rel->vreg;
    set->l.subsection = REG_8L; // Lowest 8 bits of the vreg

    AsmIns *and = emit(a, X86_AND); // Clear the rest of the vreg
    and->l.type = OP_VREG;
    and->l.vreg = ir_rel->vreg;
    and->l.subsection = REG_8L; // Lowest 8 bits of the vreg
    and->r.type = OP_IMM;
    and->r.imm = 1;

    AsmIns *movzx = emit(a, X86_MOV); // Sign extend the lowest 8 bits into the whole thing
    movzx->l.type = OP_VREG;
    movzx->l.vreg = ir_rel->vreg;
    movzx->r.type = OP_VREG;
    movzx->r.vreg = ir_rel->vreg;
    movzx->r.subsection = REG_8L; // Lowest 8 bits of the vreg
    AsmOperand result = {.type = OP_VREG, .vreg = ir_rel->vreg};
    return result;
}

// Emits an instruction to a virtual register
static AsmOperand discharge(Assembler *a, IrIns *ins) {
    if (ins->op != IR_KI32 && ins->op != IR_LOAD && !(ins->op >= IR_EQ && ins->op <= IR_UGE)) {
        AsmOperand result = {.type = OP_VREG, .vreg = ins->vreg};
        return result; // Already in a virtual register, don't need to discharge again
    }

    switch (ins->op) {
    case IR_KI32: // Immediates
        return discharge_imm(a, ins);
    case IR_LOAD: // Memory
        return discharge_load(a, ins);
    case IR_EQ: case IR_NEQ: // Comparisons
    case IR_SLT: case IR_SLE: case IR_SGT: case IR_SGE:
    case IR_ULT: case IR_ULE: case IR_UGT: case IR_UGE:
        return discharge_rel(a, ins);
    default: UNREACHABLE();
    }
}

static void asm_farg(Assembler *a, IrIns *ir_farg) {
    AsmIns *mov = emit(a, X86_MOV);
    ir_farg->vreg = a->vreg++;
    mov->l.type = OP_VREG;
    mov->l.vreg = ir_farg->vreg;
    mov->r.type = OP_REG;
    mov->r.reg = FN_ARGS_REGS[ir_farg->narg]; // Pull the argument out of the reg specified by the ABI
}

static void asm_alloc(Assembler *a, IrIns *ir_alloc) {
    a->stack_size += size_of(ir_alloc->type);
    ir_alloc->stack_slot = a->stack_size;
    ir_alloc->vreg = a->vreg++; // Virtual register for the POINTER returned by the ALLOC instruction
    // Don't emit any instructions for a fixed-size allocation
}

static void asm_store(Assembler *a, IrIns *ir_store) {
    assert(ir_store->l->op == IR_ALLOC); // Only source of pointers is IR_ALLOC
    assert(ir_store->l->type.prim == ir_store->r->type.prim); // Can only store <type> into <type>*
    assert(ir_store->l->type.ptrs == ir_store->r->type.ptrs + 1);

    AsmOperand r; // Right operand either a constant or vreg (not memory)
    if (ir_store->r->op == IR_KI32) { // Constant
        r.type = OP_IMM;
        r.imm = ir_store->r->ki32;
    } else {
        r = discharge(a, ir_store->r); // Virtual register
    }

    AsmIns *mov = emit(a, X86_MOV);
    mov->l.type = OP_MEM;
    mov->l.base = REG_RBP;
    mov->l.scale = 1;
    mov->l.index = -ir_store->l->stack_slot;
    mov->r = r;
}

static void asm_arith(Assembler *a, IrIns *ir_arith) {
    AsmOp op;
    switch (ir_arith->op) {
        case IR_ADD: op = X86_ADD; break;
        case IR_SUB: op = X86_SUB; break;
        case IR_MUL: op = X86_MUL; break;
        case IR_AND: op = X86_AND; break;
        case IR_OR:  op = X86_OR; break;
        case IR_XOR: op = X86_XOR; break;
        default: UNREACHABLE();
    }

    AsmOperand l = discharge(a, ir_arith->l); // Left operand always a vreg
    AsmOperand r;
    if (ir_arith->r->op == IR_KI32) {
        r.type = OP_IMM;
        r.imm = ir_arith->r->ki32;
    } else if (ir_arith->r->op == IR_LOAD) {
        IrIns *ir_load = ir_arith->r;
        r.type = OP_MEM;
        r.base = REG_RBP;
        r.scale = 1;
        r.index = -ir_load->l->stack_slot;
    } else {
        r = discharge(a, ir_arith->r);
    }
    AsmIns *arith = emit(a, op);
    arith->l = l;
    arith->r = r;
    ir_arith->vreg = arith->l.vreg;
}

static void asm_div(Assembler *a, IrIns *ir_div) {
    AsmOperand dividend = discharge(a, ir_div->l); // Left operand always a vreg
    AsmOperand divisor;
    if (ir_div->r->op == IR_LOAD) {
        IrIns *ir_load = ir_div->r;
        divisor.type = OP_MEM;
        divisor.base = REG_RBP;
        divisor.scale = 1;
        divisor.index = -ir_load->l->stack_slot;
    } else { // Including immediate (can't divide by an immediate)
        divisor = discharge(a, ir_div->r);
        divisor.type = OP_VREG;
        divisor.vreg = ir_div->r->vreg;
    }

    AsmIns *mov1 = emit(a, X86_MOV); // Mov dividend into eax
    mov1->l.type = OP_REG;
    mov1->l.reg = REG_RAX;
    mov1->r = dividend;
    emit(a, X86_CDQ); // Sign extend eax into edx
    AsmIns *div = emit(a, X86_IDIV); // Performs edx:eax / <operand>; quotient in eax, remainder in edx
    div->l = divisor;
    ir_div->vreg = a->vreg++;
    AsmIns *mov2 = emit(a, X86_MOV); // Move the result out of eax and into a new vreg
    mov2->l.type = OP_VREG;
    mov2->l.vreg = ir_div->vreg;
    mov2->r.type = OP_REG;
    if (ir_div->op == IR_DIV) {
        mov2->r.reg = REG_RAX; // Division (quotient in rax)
    } else {
        mov2->r.reg = REG_RDX; // Modulo (remainder in rdx)
    }
}

static void asm_shift(Assembler *a, IrIns *ir_shift) {
    AsmOperand l = discharge(a, ir_shift->l); // Left operand always a vreg
    AsmOperand r; // Right operand either an immediate or cl
    if (ir_shift->r->op == IR_KI32) { // Can shift by an immediate
        r.type = OP_IMM;
        r.imm = ir_shift->r->ki32;
    } else { // Otherwise, shift count has to be in cl
        AsmOperand discharged = discharge(a, ir_shift->r);
        AsmIns *mov = emit(a, X86_MOV); // Mov shift count into rcx
        mov->l.type = OP_REG;
        mov->l.reg = REG_RCX;
        mov->r = discharged;
        r.type = OP_REG;
        r.reg = REG_CL;
    }

    AsmOp op;
    switch (ir_shift->op) {
        case IR_SHL: op = X86_SHL; break;
        case IR_ASHR: op = X86_SAR; break;
        case IR_LSHR: op = X86_SHR; break;
        default: UNREACHABLE();
    }
    AsmIns *shift = emit(a, op);
    shift->l = l;
    shift->r = r;
    ir_shift->vreg = shift->l.vreg; // Result stored into left operand
}

static void asm_ret0(Assembler *a) {
    AsmIns *pop = emit(a, X86_POP); // Post-amble
    pop->l.type = OP_REG;
    pop->l.reg = REG_RBP;
    emit(a, X86_RET);
}

static void asm_ret1(Assembler *a, IrIns *ir_ret) {
    assert(ir_ret->l->op == IR_KI32); // Can only return integers for now
    AsmIns *mov = emit(a, X86_MOV); // mov rax, <value>
    mov->l.type = OP_REG;
    mov->l.reg = REG_RAX;
    mov->r.type = OP_IMM;
    mov->r.imm = ir_ret->l->ki32;
    asm_ret0(a);
}

static void asm_ins(Assembler *a, IrIns *ir_ins) {
    switch (ir_ins->op) {
        case IR_KI32:
            break; // Don't do anything for constants
        case IR_FARG:
            asm_farg(a, ir_ins);
            break;
        case IR_ALLOC:
            asm_alloc(a, ir_ins);
            break;
        case IR_LOAD:
            break; // Loads don't always have to generate 'mov's; do it as needed with 'discharge'
        case IR_STORE:
            asm_store(a, ir_ins);
            break;
        case IR_ADD: case IR_SUB: case IR_MUL: case IR_AND: case IR_OR: case IR_XOR:
            asm_arith(a, ir_ins);
            break;
        case IR_DIV: case IR_MOD:
            asm_div(a, ir_ins);
            break;
        case IR_SHL: case IR_ASHR: case IR_LSHR:
            asm_shift(a, ir_ins);
            break;
        case IR_EQ: case IR_NEQ: case IR_SLT: case IR_SLE: case IR_SGT: case IR_SGE:
            break; // Don't do anything for comparisons; do it as needed with 'discharge'
        case IR_RET0:
            asm_ret0(a);
            break;
        case IR_RET1:
            asm_ret1(a, ir_ins);
            break;
        default: printf("unsupported IR instruction to assembler\n"); exit(1);
    }
}

static void asm_bb(Assembler *a, BB *ir_bb) {
    for (IrIns *ir_ins = ir_bb->head; ir_ins; ir_ins = ir_ins->next) {
        asm_ins(a, ir_ins);
    }
}

static char * prepend_underscore(char *str) {
    char *out = malloc(strlen(str) + 2);
    out[0] = '_';
    strcpy(&out[1], str);
    return out;
}

static AsmFn * asm_fn(Assembler *a, FnDef *ir_fn) {
    AsmFn *fn = malloc(sizeof(AsmFn));
    fn->next = NULL;
    fn->entry = malloc(sizeof(AsmBB));
    fn->entry->next = NULL;
    fn->entry->label = prepend_underscore(ir_fn->decl->name);
    fn->entry->head = NULL;
    a->fn = fn;
    a->ins = &fn->entry->head;

    // Add the function preamble
    AsmIns *ins;
    ins = emit(a, X86_PUSH);
    ins->l.type = OP_REG;
    ins->l.reg = REG_RBP;
    ins = emit(a, X86_MOV);
    ins->l.type = OP_REG;
    ins->l.reg = REG_RBP;
    ins->r.type = OP_REG;
    ins->r.reg = REG_RSP;

    asm_bb(a, ir_fn->entry);
    return fn;
}

/* The 'main' function isn't the first thing that gets executed when the kernel
 * launches a user-space program, it's the 'start' function. 'start' performs
 * some set-up and shut-down things before and after calling 'main':
 * 1. Puts the arguments to 'main' (argc, argv, envp; given by the kernel on
 *    the stack) into registers according to the System V ABI calling convention
 * 2. Calls the 'exit' syscall after 'main' is finished
 *
 * The full start stub is (see https://en.wikipedia.org/wiki/Crt0):
 * _start:
 *     xor ebp, ebp         ; Effectively zero rbp
 *     mov edi, [rsp]       ; Take argc off the stack
 *     lea rsi, [rsp+8]     ; Take argv off the stack
 *     lea rdx, [rsp+16]    ; Take envp off the stack
 *     xor eax, eax         ; Convention per ABI
 *     call main            ; Call the main function
 *     mov rdi, rax         ; Exit syscall
 *     mov rax, 0x2000001
 *     syscall
 */
static AsmFn * asm_start(AsmFn *main) {
    AsmFn *start = malloc(sizeof(AsmFn));
    AsmBB *entry = malloc(sizeof(AsmBB));
    entry->next = NULL;
    entry->label = "_start";
    entry->head = NULL;
    start->entry = entry;
    start->next = NULL;

    Assembler a;
    a.fn = start;
    a.ins = &entry->head;

    AsmIns *ins;
    ins = emit(&a, X86_XOR); // Zero rbp
    ins->l.type = OP_REG; ins->l.reg = REG_EBP;
    ins->r.type = OP_REG; ins->r.reg = REG_EBP;
    ins = emit(&a, X86_MOV); // Take argc off the stack
    ins->l.type = OP_REG; ins->l.reg = REG_EDI;
    ins->r.type = OP_MEM; ins->r.base = REG_RSP; ins->r.scale = 1; ins->r.index = 0;
    ins = emit(&a, X86_LEA); // Take argc off the stack
    ins->l.type = OP_REG; ins->l.reg = REG_RSI;
    ins->r.type = OP_MEM; ins->r.base = REG_RSP; ins->r.scale = 1; ins->r.index = 8;
    ins = emit(&a, X86_LEA); // Take envp off the stack
    ins->l.type = OP_REG; ins->l.reg = REG_RDX;
    ins->r.type = OP_MEM; ins->r.base = REG_RSP; ins->r.scale = 1; ins->r.index = 16;
    ins = emit(&a, X86_XOR); // Zero eax (convention per ABI)
    ins->l.type = OP_REG; ins->l.reg = REG_EAX;
    ins->r.type = OP_REG; ins->r.reg = REG_EAX;
    ins = emit(&a, X86_CALL); // Call main
    ins->l.type = OP_SYM; ins->l.sym = main->entry;
    ins = emit(&a, X86_MOV); // Exit syscall
    ins->l.type = OP_REG; ins->l.reg = REG_RDI;
    ins->r.type = OP_REG; ins->r.reg = REG_RAX;
    ins = emit(&a, X86_MOV);
    ins->l.type = OP_REG; ins->l.reg = REG_RAX;
    ins->r.type = OP_IMM; ins->r.imm = 0x2000001;
    emit(&a, X86_SYSCALL);
    return start;
}

AsmModule * assemble(Module *ir_mod) {
    Assembler a;
    a.fn = NULL;
    a.ins = NULL;
    a.stack_size = 0;
    a.vreg = 0;
    AsmModule *module = malloc(sizeof(AsmModule));
    module->fns = asm_fn(&a, ir_mod->fns);
    module->main = module->fns; // There's only one function, make it the main one (even if it's not called 'main')

    if (module->main) { // If this module has a 'main' function
        AsmFn *start = asm_start(module->main); // Insert a 'start' stub to call the 'main' function
        start->next = module->fns;
        module->fns = start;
    }
    return module;
}
