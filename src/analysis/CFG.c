
#include <stdlib.h>

#include "CFG.h"

void add_pair(BB *pred, BB *succ) {
    // Make some more room in the pred array if needed
    if (succ->num_pred >= succ->max_pred) {
        succ->max_pred *= 2;
        succ->pred = realloc(succ->pred,
                                     sizeof(BB *) * succ->max_pred);
    }
    // Add 'succ' as a successor to 'pred' and 'pred' as a predecessor to 'succ'
    pred->succ[pred->num_succ++] = succ;
    succ->pred[succ->num_pred++] = pred;
}

void analysis_cfg(BB *head) {
    // Allocate the predecessor and successor arrays
    for (BB *bb = head; bb; bb = bb->next) {
        bb->max_pred = 4; // Could be an unlimited number of pred
        bb->num_pred = 0;
        bb->pred = malloc(sizeof(BB *) * bb->max_pred);
        bb->num_succ = 0; // Can ONLY have a max of 2 successors
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
