
#include <stdio.h>

#include "Debug.h"

static char *IR_PRIM_NAMES[] = {
#define X(name) #name,
    IR_PRIMS
#undef X
};

static char *IR_OPCODE_NAMES[] = {
#define X(opcode, nargs) #opcode,
    IR_OPCODES
#undef X
};

static void print_type(Type t) {
    printf("%s", IR_PRIM_NAMES[t.prim]); // Primitive name
    for (int i = 0; i < t.ptrs; i++) {
        printf("*"); // Star for every pointer indirection
    }
}

static void print_phi(IrIns *phi) {
    Phi *pair = phi->phi;
    while (pair) {
        printf("[ %s, %.4d ] ", pair->bb->label, pair->def->idx);
        pair = pair->next;
    }
}

static void print_ins(IrIns *ins) {
    printf("\t"); // Indent all instructions by a tab
    printf("%.4d\t", ins->idx); // Instruction's index in the function
    print_type(ins->type); // Return type (void if control flow)
    printf("\t%s\t", IR_OPCODE_NAMES[ins->op]); // Opcode name
    switch (ins->op) { // Handle special case instructions (e.g., constants)
    case IR_FARG:   printf("%d", ins->arg_num); break;
    case IR_KI32:   printf("%+d", ins->ki32); break;
    case IR_ALLOC:  printf("%s", IR_PRIM_NAMES[ins->type.prim]); break;
    case IR_BR:     printf("%s", ins->br ? ins->br->label : "NULL"); break;
    case IR_CONDBR:
        printf("%.4d\t", ins->cond->idx); // Condition
        printf("%s\t", ins->true ? ins->true->label : "NULL"); // True branch
        printf("%s", ins->false ? ins->false->label : "NULL"); // False branch
        break;
    case IR_PHI: print_phi(ins); break;
    default:
        if (IR_OPCODE_NARGS[ins->op] >= 1) { // Single argument instructions
            printf("%.4d", ins->l->idx);
        }
        if (IR_OPCODE_NARGS[ins->op] >= 2) { // Two argument instructions
            printf("\t%.4d", ins->r->idx);
        }
        break;
    }
    printf("\n");
}

static void print_bb(BB *bb) {
    printf("%s:\n", bb->label); // Print the BB label
    for (IrIns *ins = bb->ir_head; ins; ins = ins->next) {
        print_ins(ins); // Print every instruction in the BB
    }
}

static void number_ins(FnDef *fn) {
    int ins_idx = 0;
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        for (IrIns *ins = bb->ir_head; ins; ins = ins->next) {
            ins->idx = ins_idx++; // Number the IR instructions
        }
    }
}

void print_fn(FnDef *fn) {
    number_ins(fn);
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        print_bb(bb); // Print BBs in the order they appear in the source
    }
}
