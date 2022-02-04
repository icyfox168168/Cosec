
#include "UseChain.h"

static void add_use(IrIns *ins, IrIns *use) {
    UseChain *link = malloc(sizeof(UseChain));
    link->next = NULL;
    link->ins = use;
    if (ins->use_chain) {
        // Add to the start of the use chain as this will place the uses in
        // order, since we iterate over all the instructions in reverse
        link->next = ins->use_chain;
        ins->use_chain = link;
    } else {
        ins->use_chain = link; // No uses yet
    }
}

static int uses_left(IrIns *ins) {
    IrOpcode op = ins->op;
    return IR_OPCODE_NARGS[op] >= 1 &&
        op != IR_KINT &&
        op != IR_FARG &&
        op != IR_ALLOC &&
        op != IR_PHI &&
        op != IR_BR &&
        op != IR_CONDBR &&
        op != IR_RET0;
}

static int uses_right(IrIns *ins) {
    return uses_left(ins) && IR_OPCODE_NARGS[ins->op] >= 2;
}

void analyse_use_chains(FnDef *fn) {
    // Allocate 'use_chain' for each instruction
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        for (IrIns *ins = bb->ir_head; ins; ins = ins->next) {
            ins->use_chain = NULL;
        }
    }

    // Iterate in reverse order to find uses
    for (BB *bb = fn->last; bb; bb = bb->prev) {
        for (IrIns *ins = bb->ir_last; ins; ins = ins->prev) {
            if (uses_left(ins)) {
                add_use(ins->l, ins);
            }
            if (uses_right(ins)) {
                add_use(ins->r, ins);
            }
        }
    }
}
