
#include <string.h>
#include <stdio.h>
#include <assert.h>

#include "Assembler.h"

typedef struct {
    AsmFn *fn;
    AsmIns **ins;
} Assembler;

static AsmIns * emit(Assembler *a, AsmOp op) {
    AsmIns *ins = malloc(sizeof(AsmIns));
    ins->next = NULL;
    ins->op = op;
    *a->ins = ins;
    a->ins = &ins->next;
    return ins;
}

static void asm_ret0(Assembler *a) {
    emit(a, X86_RET);
}

static void asm_ret1(Assembler *a, IrIns *ir_ret) {
    assert(ir_ret->l->op == IR_KI32); // Can only return integers for now
    AsmIns *mov = emit(a, X86_MOV); // mov rax, <value>
    mov->l.type = OP_REG;
    mov->l.reg = REG_RAX;
    mov->r.type = OP_IMM;
    mov->r.imm = ir_ret->l->ki32;
    emit(a, X86_RET);
}

static void asm_ins(Assembler *a, IrIns *ir_ins) {
    switch (ir_ins->op) {
        case IR_KI32: break; // Don't do anything
        case IR_RET0: asm_ret0(a); break;
        case IR_RET1: asm_ret1(a, ir_ins); break;
        default: printf("unsupported IR instruction to assembler\n"); exit(1);
    }
}

static AsmBB * asm_bb(Assembler *a, BB *ir_bb) {
    AsmBB *bb = malloc(sizeof(AsmBB));
    bb->next = NULL;
    bb->label = NULL;
    bb->head = NULL;
    a->ins = &bb->head;
    for (IrIns *ir_ins = ir_bb->head; ir_ins; ir_ins = ir_ins->next) {
        asm_ins(a, ir_ins);
    }
    return bb;
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
    a->fn = fn;
    fn->entry = asm_bb(a, ir_fn->entry);
    fn->entry->label = prepend_underscore(ir_fn->decl->name);
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
static AsmFn * asm_start(Assembler *a, AsmFn *main) {
    AsmFn *start = malloc(sizeof(AsmFn));
    AsmBB *entry = malloc(sizeof(AsmBB));
    entry->next = NULL;
    entry->label = "_start";
    entry->head = NULL;
    start->entry = entry;
    a->fn = start;
    a->ins = &entry->head;

    // _start:
    //     call main
    //     mov rdi, rax
    //     mov rax, 0x2000001
    //     syscall
    AsmIns *ins;
    ins = emit(a, X86_CALL);
    ins->l.type = OP_SYM;
    ins->l.sym = main->entry;
    ins = emit(a, X86_MOV);
    ins->l.type = OP_REG; ins->l.reg = REG_RDI;
    ins->r.type = OP_REG; ins->r.reg = REG_RAX;
    ins = emit(a, X86_MOV);
    ins->l.type = OP_REG; ins->l.reg = REG_RAX;
    ins->r.type = OP_IMM; ins->r.imm = 0x2000001;
    emit(a, X86_SYSCALL);
    return start;
}

AsmModule * assemble(Module *ir_mod) {
    Assembler a;
    a.fn = NULL;
    a.ins = NULL;
    AsmModule *module = malloc(sizeof(AsmModule));
    module->fns = asm_fn(&a, ir_mod->fns);
    module->main = module->fns; // There's only one function, make it the main one (even if it's not called 'main')

    if (module->main) { // If this module has a 'main' function
        AsmFn *start = asm_start(&a, module->main); // Insert a 'start' stub to call it
        start->next = module->fns;
        module->fns = start;
    }
    return module;
}
