
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
    *a->ins = ins;
    a->ins = &ins->next;
    return ins;
}

// Emits an instruction to a virtual register
static AsmOperand discharge(Assembler *a, IrIns *ins) {
    if (!is_const(ins->op) && ins->op != IR_LOAD) {
        AsmOperand result = {.type = OP_VREG, .vreg = ins->vreg};
        return result; // Already in a virtual register, don't need to discharge again
    }

    ins->vreg = a->vreg++;
    AsmIns *mov = emit(a, X86_MOV);
    mov->l.type = OP_VREG;
    mov->l.vreg = ins->vreg;
    if (is_const(ins->op)) {
        mov->r.type = OP_IMM; // Immediate
        mov->r.imm = ins->ki32;
    } else if (ins->op == IR_LOAD) {
        assert(ins->l->type.ptrs >= 1); // Can only load from a pointer
        assert(ins->l->op == IR_ALLOC); // Only source of pointers at the moment is IR_ALLOC

        mov->r.type = OP_MEM; // Memory load
        mov->r.base = REG_RBP;
        mov->r.scale = 1;
        mov->r.index = -ins->l->stack_slot;
    }
    AsmOperand result = {.type = OP_VREG, .vreg = ins->vreg};
    return result;
}

static void asm_alloc(Assembler *a, IrIns *ir_alloc) {
    a->stack_size += size_of(ir_alloc->type);
    ir_alloc->stack_slot = a->stack_size;
    ir_alloc->vreg = a->vreg++; // Virtual register for the POINTER returned by the ALLOC instruction
    // Don't emit any instructions for a fixed-size allocation
}

static void asm_store(Assembler *a, IrIns *ir_store) {
    assert(ir_store->l->type.prim == ir_store->r->type.prim); // Can only store <type> into <type>*
    assert(ir_store->l->type.ptrs == ir_store->r->type.ptrs + 1);
    assert(ir_store->l->op == IR_ALLOC); // Only source of pointers is IR_ALLOC

    AsmOperand r; // Right operand either a constant or vreg (not memory)
    if (is_const(ir_store->r->op)) { // Constant
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
    AsmOp op = X86_NOP;
    switch (ir_arith->op) {
        case IR_ADD: op = X86_ADD; break;
        case IR_SUB: op = X86_SUB; break;
        case IR_MUL: op = X86_MUL; break;
        case IR_DIV: op = X86_IDIV; break;
        default: break; // Doesn't happen
    }

    AsmOperand l = discharge(a, ir_arith->l); // Left operand always a vreg

    AsmIns *arith = emit(a, op);
    arith->l = l;
    if (is_const(ir_arith->r->op)) {
        arith->r.type = OP_IMM;
        arith->r.imm = ir_arith->r->ki32;
    } else if (ir_arith->r->op == IR_LOAD) {
        arith->r.type = OP_MEM;
        arith->r.base = REG_RBP;
        arith->r.scale = 1;
        arith->r.index = -ir_arith->r->stack_slot;
    } else {
        arith->r.type = OP_VREG;
        arith->r.vreg = ir_arith->r->vreg;
    }
    ir_arith->vreg = arith->l.vreg;
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
    AsmIns *pop = emit(a, X86_POP); // Post-amble
    pop->l.type = OP_REG;
    pop->l.reg = REG_RBP;
    emit(a, X86_RET);
}

static void asm_ins(Assembler *a, IrIns *ir_ins) {
    switch (ir_ins->op) {
        case IR_KI32:  break; // Don't do anything for constants
        case IR_ALLOC: asm_alloc(a, ir_ins); break;
        case IR_LOAD:  break; // Loads don't always have to generate 'mov's; do as needed
        case IR_STORE: asm_store(a, ir_ins); break;
        case IR_ADD: case IR_SUB: case IR_MUL: case IR_DIV: asm_arith(a, ir_ins); break;
        case IR_RET0:  asm_ret0(a); break;
        case IR_RET1:  asm_ret1(a, ir_ins); break;
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

    // Compile the basic block
    asm_bb(a, ir_fn->entry);

    // Ensure every function ends in ret
    AsmIns *last = fn->entry->head;
    while (last->next) { last = last->next; }
    if (last->op != X86_RET) {
        ins = emit(a, X86_POP); // Post-amble
        ins->l.type = OP_REG;
        ins->l.reg = REG_RBP;
        emit(a, X86_RET);
    }
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

    Assembler a;
    a.fn = start;
    a.ins = &entry->head;

    // _start:
    //     call main
    //     mov rdi, rax
    //     mov rax, 0x2000001
    //     syscall
    AsmIns *ins;
    ins = emit(&a, X86_CALL);
    ins->l.type = OP_SYM;
    ins->l.sym = main->entry;
    ins = emit(&a, X86_MOV);
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
