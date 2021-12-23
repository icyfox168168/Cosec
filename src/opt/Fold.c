
#include <stdint.h>

#include "Fold.h"

static void fold_binary_arith(IrIns *ins) {
    if (ins->l->op != IR_KI32 || ins->r->op != IR_KI32) {
        return;
    }
    int32_t v = 0;
    switch (ins->op) {
        case IR_ADD: v = ins->l->ki32 + ins->r->ki32; break;
        case IR_SUB: v = ins->l->ki32 - ins->r->ki32; break;
        case IR_MUL: v = ins->l->ki32 * ins->r->ki32; break;
        case IR_DIV: v = ins->l->ki32 / ins->r->ki32; break;
        default: break; // Doesn't happen
    }
    // Fold arithmetic instructions in place (don't need to update their uses)
    ins->op = IR_KI32;
    ins->ki32 = v;
    // If either of the KI32 arguments are now unused, DCE will eliminate them
}

static void fold_unary_arith(IrIns *ins) {
    if (ins->l->op != IR_KI32) {
        return;
    }
    int32_t v = 0;
    switch (ins->op) {
        case IR_NEG: v = -ins->l->ki32; break;
        default: break; // Doesn't happen
    }
    // Fold arithmetic instructions in place (don't need to update their uses)
    ins->op = IR_KI32;
    ins->ki32 = v;
    // If the KI32 argument is now unused, DCE will eliminate it
}

static void fold_ins(IrIns *ins) {
    switch (ins->op) {
        case IR_ADD: case IR_SUB: case IR_MUL: case IR_DIV: fold_binary_arith(ins); break;
        case IR_NEG: fold_unary_arith(ins); break;
        default: break; // Can't fold anything else
    }
}

static void fold_bb(BB *bb) {
    for (IrIns *ins = bb->head; ins; ins = ins->next) {
        fold_ins(ins);
    }
}

void opt_fold(FnDef *fn) {
    // Iterate over every instruction and check if it can be folded (don't need
    // to bother with conditionals and control flow yet)
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        fold_bb(bb);
    }
}
