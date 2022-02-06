
#include <stdlib.h>

#include "IR.h"

Type signed_to_type(SignedType t) {
    Type r;
    r.prim = t.prim;
    r.ptrs = t.ptrs;
    return r;
}

Type type_none() {
    Type t;
    t.prim = T_NONE;
    t.ptrs = 0;
    return t;
}

SignedType signed_none() {
    SignedType t;
    t.prim = T_NONE;
    t.ptrs = 0;
    t.is_signed = 1;
    return t;
}

SignedType signed_i1() {
    SignedType t;
    t.prim = T_i1;
    t.ptrs = 0;
    t.is_signed = 0;
    return t;
}

SignedType signed_i32() {
    SignedType t;
    t.prim = T_i32;
    t.ptrs = 0;
    t.is_signed = 1;
    return t;
}

int signed_bits(SignedType t) {
    return bits(signed_to_type(t));
}

int bits(Type t) {
    if (t.ptrs > 0) {
        return 64; // Pointers are always 8 bytes
    }
    switch (t.prim) {
        case T_NONE: return -1;
        case T_void: return 0;
        case T_i1:   return 1;
        case T_i8:   return 8;
        case T_i16:  return 16;
        case T_i32:  return 32;
        case T_i64:  return 64;
        case T_f32:  return 32;
        case T_f64:  return 64;
    }
}

int bytes(Type t) {
    // Can't just divide 'bits(t)' by 8, since this wouldn't work for i1
    return (t.prim == T_i1 && t.ptrs == 0) ? 1 : bits(t) / 8;
}


// ---- Abstract Syntax Tree --------------------------------------------------

AstModule * new_ast_module() {
    AstModule *module = malloc(sizeof(AstModule));
    module->fns = NULL;
    return module;
}

FnDef * new_fn_def() {
    FnDef *def = malloc(sizeof(FnDef));
    def->next = NULL;
    def->decl = NULL;
    def->body = NULL;
    return def;
}

FnDecl * new_fn_decl() {
    FnDecl *decl = malloc(sizeof(FnDecl));
    decl->return_type = signed_none();
    decl->local = NULL;
    decl->args = NULL;
    return decl;
}

FnArg * new_fn_arg() {
    FnArg *arg = malloc(sizeof(FnArg));
    arg->next = NULL;
    arg->local = NULL;
    return arg;
}

Stmt * new_stmt(StmtType kind) {
    Stmt *stmt = malloc(sizeof(Stmt));
    stmt->next = NULL;
    stmt->kind = kind;
    stmt->expr = NULL;
    return stmt;
}

IfChain * new_if_chain() {
    IfChain *if_stmt = malloc(sizeof(IfChain));
    if_stmt->next = NULL;
    if_stmt->cond = NULL;
    if_stmt->body = NULL;
    return if_stmt;
}

Expr * new_expr(ExprType kind) {
    Expr *expr = malloc(sizeof(Expr));
    expr->kind = kind;
    expr->type = signed_none();
    expr->op = 0;
    expr->l = NULL;
    expr->r = NULL;
    return expr;
}

Local * new_local(char *name, SignedType type) {
    Local *local = malloc(sizeof(Local));
    local->next = NULL;
    local->name = name;
    local->type = type;
    local->alloc = NULL;
    return local;
}


// ---- SSA and Assembly IR ---------------------------------------------------

Module * new_module() {
    Module *module = malloc(sizeof(Module));
    module->fns = NULL;
    return module;
}

Fn * new_fn() {
    Fn *fn = malloc(sizeof(Fn));
    fn->next = NULL;
    fn->entry = NULL;
    fn->last = NULL;
    fn->num_vregs = 0;
    return fn;
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
    return bb;
}

IrIns * new_ir(IrOpcode op) {
    IrIns *ins = malloc(sizeof(IrIns));
    ins->bb = NULL;
    ins->op = op;
    ins->next = NULL;
    ins->prev = NULL;
    ins->type.prim = T_NONE;
    ins->type.ptrs = 0;
    ins->vreg = -1; // Important for the assembler
    return ins;
}

void emit_ir(BB *bb, IrIns *ins) {
    ins->bb = bb;
    ins->prev = bb->ir_last;
    if (bb->ir_last) {
        bb->ir_last->next = ins;
    } else {
        bb->ir_head = ins; // Head of the basic block
    }
    bb->ir_last = ins;
}

void delete_ir(IrIns *ins) {
    if (ins->prev) {
        ins->prev->next = ins->next;
    } else { // Head of the linked list
        ins->bb->ir_head = ins->next;
    }
    if (ins->next) {
        ins->next->prev = ins->prev;
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
    if (ins->next) {
        ins->next->prev = ins->prev;
    }
    if (ins->bb->asm_last == ins) {
        ins->bb->asm_last = ins->prev;
    }
}