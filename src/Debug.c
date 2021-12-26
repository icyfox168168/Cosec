
#include <stdio.h>
#include <string.h>

#include "Debug.h"

static void print_ins(IrIns *ins) {
    printf("%.4d\t%s\t", ins->debug_idx, IR_OPCODE_NAMES[ins->op]);
    if (strlen(IR_OPCODE_NAMES[ins->op]) < 8) {
        printf("\t"); // Some opcode names are less than the length of a tab
    }
    switch (ins->op) { // Handle special case instructions (e.g., constants)
        case IR_FARG: printf("%d", ins->narg); break;
        case IR_KI32: printf("%+d", ins->ki32); break;
        case IR_ALLOC: printf("%s", IR_PRIM_NAMES[ins->type.prim]); break;
        default:
            printf("%.4d", ins->l->debug_idx); // Single argument instructions
            if (IR_OPCODE_NARGS[ins->op] == 2) { // Two argument instructions
                printf("\t%.4d", ins->r->debug_idx);
            }
            break;
    }
    printf("\n");
}

void print_bb(BB *bb) {
    int idx = 0;
    for (IrIns *ins = bb->head; ins; ins = ins->next) { // Number the instructions
        ins->debug_idx = idx++;
    }
    for (IrIns *ins = bb->head; ins; ins = ins->next) { // Print the instructions
        print_ins(ins);
    }
}
