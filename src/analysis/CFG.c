
#include <stdlib.h>

#include "CFG.h"

void add_pair(BB *pred, BB *succ) {
    // Make some more room in the pred array if needed
    if (succ->cfg.num_pred >= succ->cfg.max_pred) {
        succ->cfg.max_pred *= 2;
        succ->cfg.pred = realloc(succ->cfg.pred,
                                     sizeof(BB *) * succ->cfg.max_pred);
    }
    // Add 'succ' as a successor to 'pred' and 'pred' as a predecessor to 'succ'
    pred->cfg.succ[pred->cfg.num_succ++] = succ;
    succ->cfg.pred[succ->cfg.num_pred++] = pred;
}

void analyse_cfg(BB *head) {
    // Allocate the predecessor and successor arrays
    for (BB *bb = head; bb; bb = bb->next) {
        bb->cfg.max_pred = 4; // Could be an unlimited number of pred
        bb->cfg.num_pred = 0;
        bb->cfg.pred = malloc(sizeof(BB *) * bb->cfg.max_pred);
        bb->cfg.num_succ = 0; // Can ONLY have a max of 2 successors
    }

    // Calculate predecessor and successor blocks
    for (BB *bb = head; bb; bb = bb->next) {
        IrIns *last = bb->ir_last;
        if (last->op == IR_BR) { // Unconditional jump
            add_pair(bb, last->br); // One successor
        } else if (last->op == IR_CONDBR) { // Conditional jump
            add_pair(bb, last->true); // Two successors
            add_pair(bb, last->false);
        } // Otherwise, no successors
    }
}
