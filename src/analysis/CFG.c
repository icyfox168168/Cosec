
#include <stdlib.h>

#include "CFG.h"

void add_pair(BB *predecessor, BB *successor) {
    // Make some more room in the predecessors array if needed
    if (successor->num_pred >= successor->max_pred) {
        successor->max_pred *= 2;
        successor->predecessors = realloc(successor->predecessors,
                                          sizeof(BB *) * successor->max_pred);
    }
    // Add 'successor' as a successor to 'predecessor', and 'predecessor' as a
    // predecessor to 'successor'
    predecessor->successors[predecessor->num_succ++] = successor;
    successor->predecessors[successor->num_pred++] = predecessor;
}

void analysis_cfg(BB *head) {
    // Allocate the predecessors and successors arrays
    for (BB *bb = head; bb; bb = bb->next) {
        bb->max_pred = 4; // Could be an unlimited number of predecessors
        bb->num_pred = 0;
        bb->predecessors = malloc(sizeof(BB *) * bb->max_pred);
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
