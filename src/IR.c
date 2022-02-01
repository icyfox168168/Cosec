
#include <stdlib.h>

#include "IR.h"

int size_of(Type t) {
    if (t.ptrs > 0) {
        return 8; // Pointers are always 8 bytes
    }
    switch (t.prim) {
        case T_void: return 0;
        case T_i32:  return 4;
    }
}

BB * new_bb() {
    BB *bb = malloc(sizeof(BB));
    bb->next = NULL;
    bb->prev = NULL;
    bb->label = NULL;
    bb->ir_head = NULL;
    bb->ir_last = NULL;
    bb->asm_head = NULL;
    bb->asm_last = NULL;

    bb->pred = NULL;
    bb->num_pred = 0;
    bb->num_succ = 0;
    bb->max_pred = 0;

    bb->live_in = NULL;
    return bb;
}

static IrIns * new_ir(IrOpcode op) {
    IrIns *ins = malloc(sizeof(IrIns));
    ins->bb = NULL;
    ins->op = op;
    ins->next = NULL;
    ins->prev = NULL;
    ins->type.prim = T_void;
    ins->type.ptrs = 0;
    return ins;
}

IrIns * emit_ir(BB *bb, IrOpcode op) {
    IrIns *ins = new_ir(op);
    ins->bb = bb;
    ins->prev = bb->ir_last;
    if (bb->ir_last) {
        bb->ir_last->next = ins;
    } else {
        bb->ir_head = ins; // Head of the basic block
    }
    bb->ir_last = ins;
    return ins;
}

void delete_ir(IrIns *ins) {
    if (ins->prev) {
        ins->prev->next = ins->next;
    } else { // Head of the linked list
        ins->bb->ir_head = ins->next;
    }
    if (ins->bb->ir_last == ins) {
        ins->bb->ir_last = ins->prev;
    }
}

static AsmIns * new_asm(AsmOpcode op) {
    AsmIns *ins = malloc(sizeof(AsmIns));
    ins->next = NULL;
    ins->prev = NULL;
    ins->idx = -1;
    ins->op = op;
    ins->l.type = 0;
    ins->l.vreg = 0;
    ins->l.size = REG_Q;
    ins->r.type = 0;
    ins->r.vreg = 0;
    ins->r.size = REG_Q;
    return ins;
}

AsmIns * emit_asm(BB *bb, AsmOpcode op) {
    AsmIns *ins = new_asm(op);
    ins->bb = bb;
    ins->prev = bb->asm_last;
    if (bb->asm_last) {
        bb->asm_last->next = ins;
    } else {
        bb->asm_head = ins;
    }
    bb->asm_last = ins;
    return ins;
}

void delete_asm(AsmIns *ins) {
    if (ins->prev) {
        ins->prev->next = ins->next;
    } else { // Head of linked list
        ins->bb->asm_head = ins->next;
    }
    if (ins->bb->asm_last == ins) {
        ins->bb->asm_last = ins->prev;
    }
}