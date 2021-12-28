
#include <stdio.h>
#include <string.h>

#include "Debug.h"

static void print_type(Type t) {
    printf("%s", IR_PRIM_NAMES[t.prim]);
    for (int i = 0; i < t.ptrs; i++) {
        printf("*");
    }
}

static void print_ins(IrIns *ins) {
    printf("\t%.4d\t", ins->debug_idx);
    print_type(ins->type);
    printf("\t%s\t", IR_OPCODE_NAMES[ins->op]);
    if (strlen(IR_OPCODE_NAMES[ins->op]) < 8) {
        printf("\t"); // Some opcode names are less than the length of a tab
    }
    switch (ins->op) { // Handle special case instructions (e.g., constants)
    case IR_FARG: printf("%d", ins->narg); break;
    case IR_KI32: printf("%+d", ins->ki32); break;
    case IR_ALLOC: printf("%s", IR_PRIM_NAMES[ins->type.prim]); break;
    case IR_BR: printf("%d", ins->br->label); break;
    case IR_CONDBR: printf("%.4d\t%d\t%d", ins->cond->debug_idx, ins->true->label, ins->false->label); break;
    default:
        if (IR_OPCODE_NARGS[ins->op] >= 1) { // Single argument instructions
            printf("%.4d", ins->l->debug_idx);
        }
        if (IR_OPCODE_NARGS[ins->op] >= 2) { // Two argument instructions
            printf("\t%.4d", ins->r->debug_idx);
        }
        break;
    }
    printf("\n");
}

static void print_bb(BB *bb, void *_) {
    printf("%d:\n", bb->label); // Print the BB label
    for (IrIns *ins = bb->head; ins; ins = ins->next) { // Number every instruction
        print_ins(ins);
    }
}

static void number_ins(BB *bb, void *ins_idx) {
    for (IrIns *ins = bb->head; ins; ins = ins->next) { // Number every instruction
        ins->debug_idx = (*((int *) ins_idx))++;
    }
}

static void label_bb(BB *bb, void *bb_idx) {
    bb->label = (*((int *) bb_idx))++;
}

void print_fn(FnDef *fn) {
    int label_idx = 0;
    iterate_bb(fn, label_bb, &label_idx); // Label basic blocks
    int ins_idx = 0;
    iterate_bb(fn, number_ins, &ins_idx);
    iterate_bb(fn, print_bb, NULL);
}
