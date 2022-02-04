
#include <stdint.h>

#include "Fold.h"

static void fold_arith(IrIns *ins) {
    if (ins->l->op != IR_KINT || ins->r->op != IR_KINT) {
        return;
    }
    int32_t v = 0;
    switch (ins->op) {
        case IR_ADD: v = ins->l->kint + ins->r->kint; break;
        case IR_SUB: v = ins->l->kint - ins->r->kint; break;
        case IR_MUL: v = ins->l->kint * ins->r->kint; break;
        case IR_DIV: v = ins->l->kint / ins->r->kint; break;
        default: break; // Doesn't happen
    }
    // Fold arithmetic instructions in place (don't need to update their uses)
    ins->op = IR_KINT;
    ins->kint = v;
    // If either KI32 arguments are now unused, DCE will eliminate them...
}

static void fold_ins(IrIns *ins) {
    switch (ins->op) {
        case IR_ADD: case IR_SUB: case IR_MUL: case IR_DIV:
            fold_arith(ins); break;
        default: break; // Can't fold anything else at the moment
    }
}

void opt_fold(FnDef *fn) {
    // Iterate over every instruction and check if it can be folded (don't need
    // to bother with conditionals and control flow yet)
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        for (IrIns *ins = bb->ir_head; ins; ins = ins->next) {
            fold_ins(ins);
        }
    }
}
