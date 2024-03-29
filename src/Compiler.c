
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "Compiler.h"
#include "Lexer.h"

typedef struct loop {
    BrChain *breaks;
    BrChain *continues;
    struct loop *outer;
} Loop;

typedef struct {
    Fn *fn;     // Current IR function we're compiling TO
    Loop *loop; // Innermost loop that we're parsing (for breaks)
} Compiler;

Fn * new_fn() {
    Fn *fn = malloc(sizeof(Fn));
    fn->next = NULL;
    fn->entry = NULL;
    fn->last = NULL;
    fn->num_gprs = 0;
    fn->max_consts = 4;
    fn->num_consts = 0;
    fn->consts = malloc(sizeof(Constant) * fn->max_consts);
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

static BB * emit_bb(Compiler *c) {
    BB *bb = new_bb();
    bb->prev = c->fn->last;
    if (c->fn->last) {
        c->fn->last->next = bb;
    }
    c->fn->last = bb;
    return bb;
}

static IrIns * new_ir(IrOpcode op) {
    IrIns *ins = malloc(sizeof(IrIns));
    ins->bb = NULL;
    ins->op = op;
    ins->next = NULL;
    ins->prev = NULL;
    ins->type = NULL;
    ins->vreg = -1; // Important for the assembler
    return ins;
}

static void sanity_check(IrIns *ins) {
    if (ins->op == IR_STORE) {
        // Store <type> into <type>*
        assert(is_ptr(ins->l->type));
        assert(are_equal(ins->l->type->ptr, ins->r->type));
    } else if (ins->op == IR_LOAD) {
        // Load from <type>* into <type>
        assert(is_ptr(ins->l->type));
        assert(are_equal(ins->type, ins->l->type->ptr));
    } else if (ins->op == IR_ELEM) {
        // Add <type>* + i64
        assert(is_ptr_arr(ins->l->type));
        assert(are_equal(ins->r->type, t_prim(T_i64, 0)));
    } else if (IR_OPCODE_NARGS[ins->op] == 2) {
        // Otherwise, both types should be the SAME
        assert(are_equal(ins->l->type, ins->r->type));
    }
}

static void emit_ir(BB *bb, IrIns *ins) {
    sanity_check(ins);
    ins->bb = bb;
    ins->prev = bb->ir_last;
    if (bb->ir_last) {
        bb->ir_last->next = ins;
    } else {
        bb->ir_head = ins; // Head of the basic block
    }
    bb->ir_last = ins;
}

static void emit(Compiler *c, IrIns *ins) {
    emit_ir(c->fn->last, ins);
}

static void delete_ir(IrIns *ins) {
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

static Loop new_loop() {
    Loop loop;
    loop.breaks = NULL;
    loop.continues = NULL;
    loop.outer = NULL;
    return loop;
};

static PhiChain * new_phi(BB *bb, IrIns *def) {
    PhiChain *phi = malloc(sizeof(PhiChain));
    phi->next = NULL;
    phi->bb = bb;
    phi->def = def;
    return phi;
}

static int add_const(Compiler *c, Constant constant) {
    Fn *fn = c->fn;
    if (fn->num_consts >= fn->max_consts) {
        fn->max_consts *= 2;
        fn->consts = realloc(fn->consts, sizeof(double) * fn->max_consts);
    }
    fn->consts[fn->num_consts] = constant;
    return fn->num_consts++;
}


// ---- Expressions -----------------------------------------------------------

static IrOpcode SIGNED_BINOP[NUM_TKS] = {
    ['+'] = IR_ADD,
    ['-'] = IR_SUB,
    ['*'] = IR_MUL,
    ['/'] = IR_SDIV,
    ['%'] = IR_SMOD,
    ['&'] = IR_AND,
    ['|'] = IR_OR,
    ['^'] = IR_XOR,
    [TK_EQ]  = IR_EQ,
    [TK_NEQ] = IR_NEQ,
    ['<']    = IR_SLT,
    [TK_LE]  = IR_SLE,
    ['>']    = IR_SGT,
    [TK_GE]  = IR_SGE,
    [TK_LSHIFT] = IR_SHL,
    [TK_RSHIFT] = IR_ASHR,
    [TK_ADD_ASSIGN] = IR_ADD,
    [TK_SUB_ASSIGN] = IR_SUB,
    [TK_MUL_ASSIGN] = IR_MUL,
    [TK_DIV_ASSIGN] = IR_SDIV,
    [TK_MOD_ASSIGN] = IR_SMOD,
    [TK_AND_ASSIGN] = IR_AND,
    [TK_OR_ASSIGN]  = IR_OR,
    [TK_XOR_ASSIGN] = IR_XOR,
    [TK_LSHIFT_ASSIGN] = IR_SHL,
    [TK_RSHIFT_ASSIGN] = IR_ASHR,
};

static IrOpcode UNSIGNED_BINOP[NUM_TKS] = {
    ['+'] = IR_ADD,
    ['-'] = IR_SUB,
    ['*'] = IR_MUL,
    ['/'] = IR_UDIV, // Unsigned division/modulo
    ['%'] = IR_UMOD,
    ['&'] = IR_AND,
    ['|'] = IR_OR,
    ['^'] = IR_XOR,
    [TK_EQ]  = IR_EQ,
    [TK_NEQ] = IR_NEQ,
    ['<']    = IR_ULT, // Unsigned comparisons
    [TK_LE]  = IR_ULE,
    ['>']    = IR_UGT,
    [TK_GE]  = IR_UGE,
    [TK_LSHIFT] = IR_SHL,
    [TK_RSHIFT] = IR_LSHR, // Logical shift
    [TK_ADD_ASSIGN] = IR_ADD,
    [TK_SUB_ASSIGN] = IR_SUB,
    [TK_MUL_ASSIGN] = IR_MUL,
    [TK_DIV_ASSIGN] = IR_UDIV, // Unsigned division/modulo
    [TK_MOD_ASSIGN] = IR_UMOD,
    [TK_AND_ASSIGN] = IR_AND,
    [TK_OR_ASSIGN]  = IR_OR,
    [TK_XOR_ASSIGN] = IR_XOR,
    [TK_LSHIFT_ASSIGN] = IR_SHL,
    [TK_RSHIFT_ASSIGN] = IR_LSHR, // Logical shift
};

static IrOpcode FP_BINOP[NUM_TKS] = {
    ['+'] = IR_ADD,
    ['-'] = IR_SUB,
    ['*'] = IR_MUL,
    ['/'] = IR_FDIV,
    [TK_EQ]  = IR_EQ,
    [TK_NEQ] = IR_NEQ,
    ['<']    = IR_FLT,
    [TK_LE]  = IR_FLE,
    ['>']    = IR_FGT,
    [TK_GE]  = IR_FGE,
    [TK_ADD_ASSIGN] = IR_ADD,
    [TK_SUB_ASSIGN] = IR_SUB,
    [TK_MUL_ASSIGN] = IR_MUL,
    [TK_DIV_ASSIGN] = IR_FDIV,
};

static IrOpcode INVERT_COND[NUM_IR_OPS] = {
    [IR_EQ] = IR_NEQ,
    [IR_NEQ] = IR_EQ,
    [IR_SLT] = IR_SGE,
    [IR_SLE] = IR_SGT,
    [IR_SGT] = IR_SLE,
    [IR_SGE] = IR_SLT,
    [IR_ULT] = IR_UGE,
    [IR_ULE] = IR_UGT,
    [IR_UGT] = IR_ULE,
    [IR_UGE] = IR_ULT,
};

static BrChain * new_branch_chain(BB **jmp, IrIns *br) {
    BrChain *j = malloc(sizeof(BrChain));
    j->br = jmp;
    j->ins = br;
    j->next = NULL;
    return j;
}

static void patch_branch_chain(BrChain *head, BB *target) {
    // Patch all branches in a chain so that they all point to 'target'
    while (head) {
        *head->br = target;
        BrChain *next = head->next;
        head = next;
    }
}

// Append the given branch chain to the end of the other
static void merge_branch_chains(BrChain **head, BrChain *to_append) {
    if (!to_append) {
        return;
    }
    while (*head) { // Find the end of the jump list
        head = &(*head)->next;
    }
    *head = to_append;
}

static IrIns * discharge(Compiler *c, IrIns *ins); // Forward declarations
static IrIns * compile_expr(Compiler *c, Expr *expr);

// Emits an IR conversion instruction that converts 'operand' from its type
// 'src' to the target type 'target'
static IrIns * emit_conv(Compiler *c, IrIns *operand, Type *src, Type *target) {
    IrOpcode op;
    if (is_int(src) && is_int(target)) {
        if (bits(target) < bits(src)) {
            op = IR_TRUNC; // Target type is smaller
        } else if (bits(src) == 1 || !src->is_signed) {
            op = IR_ZEXT; // Always zext an i1, or if the value is unsigned
        } else {
            op = IR_SEXT; // Value is signed and larger than i1
        }
    } else if (is_fp(src) && is_fp(target)) {
        if (bits(target) < bits(src)) {
            op = IR_FPTRUNC; // Target type is smaller
        } else {
            op = IR_FPEXT; // Target type is larger
        }
    } else if (is_int(src) && is_fp(target)) {
        op = IR_I2FP;
    } else if (is_fp(src) && is_int(target)) {
        op = IR_FP2I;
    } else if (is_int(src) && is_ptr(target)) {
        op = IR_I2PTR;
    } else if (is_ptr(src) && is_int(target)) {
        op = IR_PTR2I;
    } else if (is_ptr(src) && is_ptr(target)) {
        op = IR_PTR2PTR;
    } else if (is_arr(src) && is_ptr(target)) {
        assert(are_equal(src->elem, target->ptr));
        return discharge(c, operand); // Turn the array into a pointer
    } else {
        assert(0); // Parser should protect against this
    }
    IrIns *conv = new_ir(op);
    conv->l = operand;
    conv->type = t_copy(target);
    emit(c, conv);
    return conv;
}

static IrIns * discharge_cond(Compiler *c, IrIns *cond) {
    assert(cond->op == IR_CONDBR);
    IrIns *k_true = new_ir(IR_IMM); // True and false constants
    k_true->imm = 1;
    k_true->type = t_prim(T_i1, 0);
    IrIns *k_false = new_ir(IR_IMM);
    k_false->imm = 0;
    k_false->type = t_prim(T_i1, 0);

    PhiChain *phi_head = NULL; // Construct the phi chain
    PhiChain **phi = &phi_head;
    for (BrChain *true = cond->true_chain; true; true = true->next) {
        if (true->ins == cond) {
            continue; // Handle the last instruction separately
        }
        *phi = new_phi(true->ins->bb, k_true);
        phi = &(*phi)->next;
    }
    for (BrChain *false = cond->false_chain; false; false = false->next) {
        if (false->ins == cond) {
            continue; // Handle the last instruction separately
        }
        *phi = new_phi(false->ins->bb, k_false);
        phi = &(*phi)->next;
    }

    // If there was only ONE CONDBR instruction in the true/false chains, then
    // we don't need to generate a PHI instruction
    if (!phi_head) {
        IrIns *result = cond->cond;
        if (cond->true_chain->br == &cond->false) { // Needs negation
            result->op = INVERT_COND[result->op];
        }
        delete_ir(cond);
        return result;
    }

    // Basic block for the result of the condition
    BB *bb = emit_bb(c);
    emit(c, k_true);
    emit(c, k_false);

    // Patch the true and false list here
    patch_branch_chain(cond->true_chain, bb);
    patch_branch_chain(cond->false_chain, bb);

    // Handle the last condition in the phi chain separately
    IrIns *last_cond = cond->cond;
    cond->op = IR_BR; // Change the last conditional branch into an
    cond->br = bb;    // unconditional one
    *phi = new_phi(bb, last_cond);

    IrIns *phi_ins = new_ir(IR_PHI); // Phi instruction for the result
    phi_ins->phi = phi_head;
    phi_ins->type = t_prim(T_i1, 0);
    emit(c, phi_ins);
    return phi_ins;
}

static IrIns * discharge_array(Compiler *c, IrIns *array) {
    assert(is_arr(array->type));
    // Convert the array into a pointer by accessing its 0th element
    IrIns *zero = new_ir(IR_IMM);
    zero->imm = 0;
    zero->type = t_prim(T_i64, 0); // Always unsigned
    emit(c, zero);
    IrIns *elem = new_ir(IR_ELEM);
    elem->l = array;
    elem->r = zero;
    elem->type = t_ptr(t_copy(array->type->elem));
    emit(c, elem);
    return elem;
}

// Performs several conversions that make values usable in expressions:
// * Converts condition expressions into values by (1) emitting a phi
//   instruction if there's more than one true or false branch chain to patch;
//   or (2) removing the CONDBR instruction and referring to the underlying
//   comparison instruction if there's only one branch (no need for a phi)
// * Converts array objects into a pointer to its 0th element
static IrIns * discharge(Compiler *c, IrIns *ins) {
    if (ins->op == IR_CONDBR) {
        return discharge_cond(c, ins);
    } else if (ins->type && is_arr(ins->type)) {
        return discharge_array(c, ins);
    }
    return ins; // Doesn't need to be discharged
}

// Convert a compiled expression into a condition (e.g., for an if or while
// statement) by emitting a branch if needed
static IrIns * to_cond(Compiler *c, IrIns *expr) {
    if (expr->op == IR_CONDBR) {
        return expr; // Already a condition, don't do anything
    }
    expr = discharge(c, expr);
    assert(expr->op >= IR_EQ && expr->op <= IR_FGE); // Should be a comparison
    IrIns *br = new_ir(IR_CONDBR); // Emit a branch on the condition
    br->cond = expr;
    // Start a new true and false branch chain
    br->true_chain = new_branch_chain(&br->true, br);
    br->false_chain = new_branch_chain(&br->false, br);
    emit(c, br);
    return br;
}

static IrIns * compile_ternary(Compiler *c, Expr *ternary) {
    IrIns *cond = compile_expr(c, ternary->cond);
    cond = to_cond(c, cond);
    BB *true_bb = emit_bb(c); // New BB for the true value
    // The condition's true case should target the true value
    patch_branch_chain(cond->true_chain, true_bb);

    IrIns *true_val = compile_expr(c, ternary->l);
    true_val = discharge(c, true_val);
    IrIns *true_br = new_ir(IR_BR);
    emit(c, true_br);
    BB *false_bb = emit_bb(c); // New BB for the false value
    patch_branch_chain(cond->false_chain, false_bb);

    IrIns *false_val = compile_expr(c, ternary->r);
    false_val = discharge(c, false_val);
    IrIns *false_br = new_ir(IR_BR);
    emit(c, false_br);

    // New BB for everything after, since PHIs can only occur at the start of
    // basic blocks
    BB *after_bb = emit_bb(c);
    true_br->br = after_bb;
    false_br->br = after_bb;

    // Emit a phi
    IrIns *phi_ins = new_ir(IR_PHI);
    phi_ins->phi = new_phi(true_bb, true_val);
    phi_ins->phi->next = new_phi(false_bb, false_val);
    phi_ins->type = t_copy(ternary->type);
    emit(c, phi_ins);
    return phi_ins;
}

static IrIns * compile_operation(Compiler *c, Expr *binary) {
    IrIns *left = compile_expr(c, binary->l);
    left = discharge(c, left);
    IrIns *right = compile_expr(c, binary->r);
    right = discharge(c, right);
    IrOpcode op;
    if (is_fp(binary->l->type)) {
        op = FP_BINOP[binary->op];
    } else if (binary->type->is_signed) {
        op = SIGNED_BINOP[binary->op];
    } else {
        op = UNSIGNED_BINOP[binary->op];
    }
    IrIns *operation = new_ir(op);
    operation->l = left;
    operation->r = right;
    operation->type = t_copy(binary->type);
    emit(c, operation);
    return operation;
}

// For '<ptr> + <integer>' or '<ptr> - <integer>'
static IrIns * compile_ptr_arith(Compiler *c, Expr *binary) {
    // Exactly one of 'binary->l' or 'binary->r' is a pointer/array -> make sure
    // we DON'T discharge an array! Saves an IR_ELEM instruction
    IrIns *left = compile_expr(c, binary->l);
    if (!is_ptr_arr(binary->l->type)) {
        left = discharge(c, left);
    }
    IrIns *right = compile_expr(c, binary->r);
    if (!is_ptr_arr(binary->r->type)) {
        right = discharge(c, right);
    }

    IrIns *ptr = is_ptr_arr(binary->l->type) ? left : right;
    IrIns *to_add = is_ptr_arr(binary->l->type) ? right : left;
    if (binary->op == '-') { // Negate the offset if needed
        IrIns *zero = new_ir(IR_IMM);
        zero->imm = 0;
        zero->type = t_copy(to_add->type);
        emit(c, zero);
        IrIns *sub = new_ir(IR_SUB);
        sub->l = zero;
        sub->r = to_add;
        sub->type = t_copy(to_add->type);
        emit(c, sub);
        to_add = sub;
    }

    IrIns *elem = new_ir(IR_ELEM);
    elem->l = ptr;
    elem->r = to_add;
    elem->type = to_ptr(ptr->type); // Results in a POINTER
    emit(c, elem);
    return elem;
}

// For '<ptr> - <ptr>'
static IrIns * compile_ptr_sub(Compiler *c, Expr *binary) {
    Type *deref_type = binary->l->type->ptr;

    IrIns *left = compile_expr(c, binary->l);
    left = discharge(c, left);
    IrIns *right = compile_expr(c, binary->r);
    right = discharge(c, right);

    // Convert 'left' and 'right' to i64s by emitting PTR2I
    left = emit_conv(c, left, binary->l->type, binary->type);
    right = emit_conv(c, right, binary->r->type, binary->type);

    IrIns *sub = new_ir(IR_SUB);
    sub->l = left;
    sub->r = right;
    sub->type = t_copy(binary->type);
    emit(c, sub);
    // Need to divide the sub by the size of the 'deref_type'; since all
    // type sizes are powers of 2, we can accomplish this with a shift.
    // Compute the shift size = log2(bytes(deref_type))
    int log2 = 0;
    int val = bytes(deref_type) - 1;
    while (val) { val >>= 1; log2++; }
    IrIns *size = new_ir(IR_IMM);
    size->imm = log2;
    size->type = t_copy(sub->type);
    emit(c, size);
    IrIns *div = new_ir(IR_ASHR);
    div->l = sub;
    div->r = size;
    div->type = t_copy(sub->type); // Results in i64
    emit(c, div);
    return div;
}

static IrIns * compile_arith_assign(Compiler *c, Expr *assign) {
    // The parser expects the output type for this assignment to be the type
    // of the lvalue (not its integer promotion type) -> this stuffs up the
    // return type of the arithmetic operation here, so fix it manually
    assign->type = t_copy(assign->l->type);
    IrIns *right = compile_operation(c, assign);

    // Find the lvalue expression, which gives us our target type for 'right'
    Expr *lvalue_expr = assign->l;
    if (lvalue_expr->kind == EXPR_CONV) {
        lvalue_expr = lvalue_expr->l;
    }

    // Find the emitted IR instruction corresponding to the lvalue.
    // 'right' is an arith (e.g., IR_ADD). 'right->l' is a conversion or IR_LOAD
    IrIns *lvalue = right->l;
    if (lvalue->op != IR_LOAD) { // 'right->l' is a type conversion
        lvalue = lvalue->l;
    }
    assert(lvalue->op == IR_LOAD);

    // We may need to insert a truncation (which the parser hasn't done for us)
    // e.g., in the case 'char a = 3; char *b = &a; *b += 1'
    if (bits(lvalue_expr->type) != bits(assign->type)) {
        right = emit_conv(c, right, assign->type, lvalue_expr->type);
    }

    // Copy the IR_LOAD, re-emit it, modify it into an IR_STORE
    IrIns *load = new_ir(IR_LOAD);
    *load = *lvalue;
    load->next = NULL;
    emit(c, load);
    load->op = IR_STORE;
    // IR_STORE destination is the same as the IR_LOAD (don't change store->l)
    load->r = right;
    load->type = NULL; // Clear the type set by the IR_LOAD
    return right; // Assignment evaluates to its right operand
}

static IrIns * compile_assign(Compiler *c, Expr *assign) {
    IrIns *right = compile_expr(c, assign->r);
    right = discharge(c, right);
    IrIns *load = compile_expr(c, assign->l);
    assert(load->op == IR_LOAD);
    load->op = IR_STORE; // Modify IR_LOAD into an IR_STORE
    // IR_STORE destination is the same as the IR_LOAD (don't change store->l)
    load->r = right;
    load->type = NULL; // Clear the type set by IR_LOAD
    return right; // Assignment evaluates to its right operand
}

static IrIns * emit_load(Compiler *c, IrIns *to_load) {
    IrIns *load;
    if (is_ptr(to_load->type) && is_arr(to_load->type->ptr)) {
        // Loading a pointer to an array
        IrIns *zero = new_ir(IR_IMM);
        zero->imm = 0;
        zero->type = t_prim(T_i64, 0);
        emit(c, zero);
        load = new_ir(IR_ELEM);
        load->l = to_load;
        load->r = zero;
        load->type = t_copy(to_load->type->ptr);
        emit(c, load);
    } else if (is_arr(to_load->type)) {
        load = to_load; // The array itself -> nothing to load
    } else if (is_ptr(to_load->type)) {
        load = new_ir(IR_LOAD); // Any other normal variable
        load->l = to_load;
        load->type = t_copy(to_load->type->ptr);
        emit(c, load);
    } else {
        assert(0); // Shouldn't happen!
    }
    return load;
}

static IrIns * compile_array_access(Compiler *c, Expr *access) {
    IrIns *ptr = compile_ptr_arith(c, access);
    return emit_load(c, ptr); // Load the array access
}

static IrIns * compile_and(Compiler *c, Expr *binary) {
    IrIns *left = compile_expr(c, binary->l);
    left = to_cond(c, left);
    BB *right_bb = emit_bb(c); // New BB for right operand
    patch_branch_chain(left->true_chain, right_bb);

    IrIns *right = compile_expr(c, binary->r);
    right = to_cond(c, right);
    // Merge left's false list onto the right operand's false list
    merge_branch_chains(&right->false_chain, left->false_chain);
    return right;
}

static IrIns * compile_or(Compiler *c, Expr *binary) {
    IrIns *left = compile_expr(c, binary->l);
    left = to_cond(c, left);
    BB *right_bb = emit_bb(c); // New BB for right operand
    patch_branch_chain(left->false_chain, right_bb);

    IrIns *right = compile_expr(c, binary->r);
    right = to_cond(c, right);
    // Merge left's true list onto the right operand's true list
    merge_branch_chains(&right->true_chain, left->true_chain);
    return right;
}

static IrIns * compile_comma(Compiler *c, Expr *comma) {
    compile_expr(c, comma->l); // Discard the result
    IrIns *right = compile_expr(c, comma->r);
    return right; // Comma results in its RHS
}

static IrIns * compile_binary(Compiler *c, Expr *binary) {
    switch (binary->op) {
    case '-':
        if (is_ptr_arr(binary->l->type) && is_ptr_arr(binary->r->type)) {
            return compile_ptr_sub(c, binary); // <ptr> - <ptr>
        } // Fall through...
    case '+':
        if (is_ptr_arr(binary->l->type) || is_ptr_arr(binary->r->type)) {
            return compile_ptr_arith(c, binary); // <ptr> + <integer>
        } // Fall through...
    case '*': case '/': case '%':
    case TK_LSHIFT: case TK_RSHIFT: case '&': case '|': case '^':
    case TK_EQ: case TK_NEQ: case '<': case TK_LE: case '>': case TK_GE:
        return compile_operation(c, binary);
    case '=':
        return compile_assign(c, binary);
    case TK_ADD_ASSIGN: case TK_SUB_ASSIGN:
    case TK_MUL_ASSIGN: case TK_DIV_ASSIGN: case TK_MOD_ASSIGN:
    case TK_AND_ASSIGN: case TK_OR_ASSIGN:  case TK_XOR_ASSIGN:
    case TK_LSHIFT_ASSIGN: case TK_RSHIFT_ASSIGN:
        return compile_arith_assign(c, binary);
    case '[':    return compile_array_access(c, binary);
    case TK_AND: return compile_and(c, binary);
    case TK_OR:  return compile_or(c, binary);
    case ',':    return compile_comma(c, binary);
    default: UNREACHABLE();
    }
}

static IrIns * compile_neg(Compiler *c, Expr *unary) {
    Expr *zero = new_expr(EXPR_KINT);
    zero->kint = 0;
    zero->type = t_copy(unary->type);
    Expr *sub = new_expr(EXPR_BINARY);
    sub->op = '-';
    sub->l = zero;
    sub->r = unary->l;
    sub->type = t_copy(unary->type);
    return compile_operation(c, sub);
}

static IrIns * compile_plus(Compiler *c, Expr *unary) {
    // The only function of the unary '+' operand is type promotion
    return compile_expr(c, unary->l); // Does the type promotion for us
}

static IrIns * compile_bit_not(Compiler *c, Expr *unary) {
    Expr *neg1 = new_expr(EXPR_KINT);
    neg1->kint = -1;
    neg1->type = t_copy(unary->type);
    Expr *xor = new_expr(EXPR_BINARY);
    xor->op = '^';
    xor->l = unary->l;
    xor->r = neg1;
    xor->type = t_copy(unary->type);
    return compile_operation(c, xor);
}

static IrIns * compile_not(Compiler *c, Expr *unary) {
    IrIns *result = compile_expr(c, unary->l);
    result = to_cond(c, result);
    assert(result->op == IR_CONDBR);
    BrChain *swap = result->true_chain; // Swap true and false lists
    result->true_chain = result->false_chain;
    result->false_chain = swap;
    return result;
}

static IrIns * compile_addr(Compiler *c, Expr *unary) {
    IrIns *result = compile_expr(c, unary->l);
    assert(result->op == IR_LOAD || result->op == IR_ELEM);
    IrIns *ptr = result->l; // Left operand contains the pointer we're after
    delete_ir(result); // Delete the IR_LOAD/IR_ELEM
    return ptr;
}

static IrIns * compile_deref(Compiler *c, Expr *unary) {
    IrIns *result = compile_expr(c, unary->l);
    result = discharge(c, result);
    return emit_load(c, result);
}

// Compiles ++ or -- as a prefix or postfix operator. We could've had the
// parser expand '++a' into 'a = a + 1', but this would've created two extra
// CONVs if 'a' is smaller than an i32. Since '++a' involves immediately
// loading, adding, and storing 'a', the extra SEXT then TRUNC is a waste. So,
// we get the compiler to handle prefix/postfix ++ and -- as special
// unary/postfix instructions.
static IrIns * compile_inc_dec(Compiler *c, Expr *unary, int is_prefix) {
    Expr *one = new_expr(EXPR_KINT);
    one->kint = 1;
    one->type = t_copy(unary->type); // Use the same type as what we're adding
    Expr *add = new_expr(EXPR_BINARY);
    add->op = unary->op == TK_INC ? '+' : '-';
    add->l = unary->l;
    add->r = one;
    add->type = t_copy(unary->type);
    IrIns *right = compile_operation(c, add);

    // Find the emitted IR instruction corresponding to the lvalue.
    // 'right' is an arith (e.g., IR_ADD). 'right->l' is IR_LOAD
    IrIns *lvalue = right->l;
    assert(lvalue->op == IR_LOAD);

    // Copy the IR_LOAD, re-emit it, modify it into an IR_STORE
    IrIns *load = new_ir(IR_LOAD);
    *load = *lvalue;
    load->next = NULL;
    emit(c, load);
    load->op = IR_STORE; // Modify IR_LOAD into an IR_STORE
    // IR_STORE destination is the same as the IR_LOAD (don't change store->l)
    load->r = right;
    load->type = NULL; // Clear the type set by IR_LOAD
    if (is_prefix) {
        return right;
    } else {
        return lvalue;
    }
}

static IrIns * compile_unary(Compiler *c, Expr *unary) {
    switch (unary->op) {
        case '-': return compile_neg(c, unary);
        case '+': return compile_plus(c, unary);
        case '~': return compile_bit_not(c, unary);
        case '!': return compile_not(c, unary);
        case '&': return compile_addr(c, unary);
        case '*': return compile_deref(c, unary);
        case TK_INC: case TK_DEC: return compile_inc_dec(c, unary, 1);
        default: UNREACHABLE();
    }
}

static IrIns * compile_postfix(Compiler *c, Expr *operand) {
    switch (operand->op) {
        case TK_INC: case TK_DEC: return compile_inc_dec(c, operand, 0);
        default: UNREACHABLE();
    }
}

static IrIns * compile_conv(Compiler *c, Expr *conv) {
    IrIns *operand = compile_expr(c, conv->l);
    operand = discharge(c, operand);
    return emit_conv(c, operand, conv->l->type, conv->type);
}

static IrIns * compile_local(Compiler *c, Expr *expr) {
    assert(expr->local->alloc); // Check the local has been allocated
    return emit_load(c, expr->local->alloc);
}

static IrIns * compile_kint(Compiler *c, Expr *expr) {
    IrIns *k = new_ir(IR_IMM);
    k->imm = expr->kint;
    k->type = t_copy(expr->type);
    emit(c, k);
    return k;
}

static IrIns * compile_kfloat(Compiler *c, Expr *expr) {
    Constant constant;
    constant.type = t_copy(expr->type);
    if (expr->type->prim == T_f32) {
        // Changing from float -> double -> float does not lose ANY precision
        constant.f32 = (float) expr->kfloat;
    } else {
        constant.f64 = expr->kfloat;
    }
    IrIns *k = new_ir(IR_CONST);
    k->const_idx = add_const(c, constant);
    k->type = t_copy(expr->type);
    emit(c, k);
    return k;
}

static IrIns * compile_kchar(Compiler *c, Expr *expr) {
    IrIns *k = new_ir(IR_IMM);
    k->imm = (int) expr->kch;
    k->type = t_copy(expr->type);
    emit(c, k);
    return k;
}

static IrIns * compile_kstr(Compiler *c, Expr *expr) {
    Constant constant = {.type = t_copy(expr->type), .str = expr->kstr};
    IrIns *k = new_ir(IR_CONST);
    k->const_idx = add_const(c, constant);
    k->type = t_copy(expr->type);
    emit(c, k);
    return k;
}

static IrIns * compile_expr(Compiler *c, Expr *expr) {
    switch (expr->kind) {
        case EXPR_KINT:    return compile_kint(c, expr);
        case EXPR_KFLOAT:  return compile_kfloat(c, expr);
        case EXPR_KCHAR:   return compile_kchar(c, expr);
        case EXPR_KSTR:    return compile_kstr(c, expr);
        case EXPR_LOCAL:   return compile_local(c, expr);
        case EXPR_CONV:    return compile_conv(c, expr);
        case EXPR_POSTFIX: return compile_postfix(c, expr);
        case EXPR_UNARY:   return compile_unary(c, expr);
        case EXPR_BINARY:  return compile_binary(c, expr);
        case EXPR_TERNARY: return compile_ternary(c, expr);
    }
}


// ---- Statements ------------------------------------------------------------

// Forward declaration
static void compile_block(Compiler *c, Stmt *stmt);

static void compile_decl(Compiler *c, Stmt *decl) {
    IrIns *alloc = new_ir(IR_ALLOC); // Create some stack space
    // The result of IR_ALLOC is a POINTER to the value
    alloc->type = t_ptr(t_copy(decl->local->decl.type));
    emit(c, alloc);
    decl->local->alloc = alloc;
}

static void compile_if(Compiler *c, Stmt *stmt) {
    BB *after;
    BrChain *head = NULL;
    BrChain **chain = &head;
    IfChain *if_chain = stmt->if_chain;
    while (if_chain && if_chain->cond) { // Parse 'if' and 'else if's
        IrIns *cond = compile_expr(c, if_chain->cond);
        cond = to_cond(c, cond);

        BB *body = emit_bb(c);
        patch_branch_chain(cond->true_chain, body);
        compile_block(c, if_chain->body);
        IrIns *end_br = new_ir(IR_BR);
        emit(c, end_br);
        // Add the body's end branch to the branch chain
        *chain = new_branch_chain(&end_br->br, end_br);
        chain = &(*chain)->next;

        after = emit_bb(c);
        patch_branch_chain(cond->false_chain, after);
        if_chain = if_chain->next;
    }
    if (if_chain) { // Parse 'else'
        assert(!if_chain->cond);
        compile_block(c, if_chain->body);
        IrIns *end_br = new_ir(IR_BR);
        emit(c, end_br);
        *chain = new_branch_chain(&end_br->br, end_br);
        after = emit_bb(c);
    }
    // Patch all the branches at the end of all the 'if'/'else if'/'else's
    patch_branch_chain(head, after);
}

static void compile_while(Compiler *c, Stmt *stmt) {
    IrIns *before_br = new_ir(IR_BR);
    emit(c, before_br);
    BB *cond_bb = emit_bb(c);
    before_br->br = cond_bb;

    IrIns *cond = compile_expr(c, stmt->cond); // Condition
    cond = to_cond(c, cond);

    Loop loop = new_loop();
    loop.outer = c->loop;
    c->loop = &loop;
    BB *body = emit_bb(c);
    patch_branch_chain(cond->true_chain, body);
    compile_block(c, stmt->body); // Body
    IrIns *end_br = new_ir(IR_BR);
    end_br->br = cond_bb;
    emit(c, end_br);
    c->loop = loop.outer;

    BB *after = emit_bb(c);
    patch_branch_chain(cond->false_chain, after);
    patch_branch_chain(loop.breaks, after);
    patch_branch_chain(loop.continues, cond_bb);
}

static void compile_do_while(Compiler *c, Stmt *do_while_stmt) {
    IrIns *before_br = new_ir(IR_BR);
    emit(c, before_br);

    Loop loop = new_loop();
    loop.outer = c->loop;
    c->loop = &loop;
    BB *body = emit_bb(c);
    before_br->br = body;
    compile_block(c, do_while_stmt->body); // Body
    c->loop = loop.outer;

    IrIns *cond = compile_expr(c, do_while_stmt->cond); // Condition
    cond = to_cond(c, cond);
    patch_branch_chain(cond->true_chain, body);

    BB *after = emit_bb(c);
    patch_branch_chain(cond->false_chain, after);
    patch_branch_chain(loop.breaks, after);
    patch_branch_chain(loop.continues, body);
}

static void compile_for(Compiler *c, Stmt *stmt) {
    IrIns *before_br = new_ir(IR_BR);
    emit(c, before_br);

    BB *start_bb = NULL;
    IrIns *cond = NULL;
    if (stmt->cond) {
        start_bb = emit_bb(c);
        before_br->br = start_bb;
        cond = compile_expr(c, stmt->cond); // Condition
        cond = to_cond(c, cond);
    }

    Loop loop = new_loop();
    loop.outer = c->loop;
    c->loop = &loop;
    BB *body = emit_bb(c);
    if (cond) {
        patch_branch_chain(cond->true_chain, body);
    } else {
        start_bb = body;
        before_br->br = body;
    }
    compile_block(c, stmt->body); // Body
    IrIns *end_br = new_ir(IR_BR);
    emit(c, end_br);

    BB *continue_bb;
    if (stmt->inc) {
        // New BB for the increment since all the 'continue's must jump to it
        BB *inc_bb = emit_bb(c); // Increment
        end_br->br = inc_bb;
        compile_expr(c, stmt->inc);
        IrIns *inc_br = new_ir(IR_BR);
        inc_br->br = start_bb; // Either the condition or the body
        emit(c, inc_br);
        continue_bb = inc_bb; // Target all 'continue's to the increment
    } else {
        end_br->br = start_bb;
        continue_bb = start_bb;
    }
    c->loop = loop.outer;

    BB *after = emit_bb(c);
    if (cond) {
        patch_branch_chain(cond->false_chain, after);
    }
    patch_branch_chain(loop.breaks, after);
    patch_branch_chain(loop.continues, continue_bb);
}

static void compile_break_or_continue(Compiler *c, Stmt *stmt) {
    IrIns *br_ins = new_ir(IR_BR);
    emit(c, br_ins);
    BrChain *chain = new_branch_chain(&br_ins->br, br_ins);
    BrChain **target = stmt->kind == STMT_BREAK ?
                       &c->loop->breaks : &c->loop->continues;
    merge_branch_chains(target, chain);
    emit_bb(c); // For everything after the break
}

static void compile_ret(Compiler *c, Stmt *ret_stmt) {
    IrIns *value = NULL;
    if (ret_stmt->expr) { // If we're returning something
        value = compile_expr(c, ret_stmt->expr);
        value = discharge(c, value);
    }
    IrIns *ret = new_ir(value ? IR_RET1 : IR_RET0);
    ret->l = value;
    emit(c, ret);
}

static void compile_stmt(Compiler *c, Stmt *stmt) {
    switch (stmt->kind) {
        case STMT_DECL:     compile_decl(c, stmt); break;
        case STMT_EXPR:     compile_expr(c, stmt->expr); break;
        case STMT_IF:       compile_if(c, stmt); break;
        case STMT_WHILE:    compile_while(c, stmt); break;
        case STMT_DO_WHILE: compile_do_while(c, stmt); break;
        case STMT_FOR:      compile_for(c, stmt); break;
        case STMT_BREAK:
        case STMT_CONTINUE: compile_break_or_continue(c, stmt); break;
        case STMT_RET:      compile_ret(c, stmt); break;
    }
}

static void compile_block(Compiler *c, Stmt *stmt) {
    while (stmt) {
        compile_stmt(c, stmt);
        stmt = stmt->next;
    }
}


// ---- Module ----------------------------------------------------------------

static void compile_fn_args(Compiler *c, Local **args, int nargs) {
    int gpr_arg_num = 0, fp_arg_num = 0;
    IrIns *fargs[nargs];
    for (int i = 0; i < nargs; i++) { // Emit IR_FARGs
        IrIns *farg = new_ir(IR_FARG);
        farg->type = t_copy(args[i]->decl.type);
        if (is_fp(farg->type)) {
            // Count floating point arguments SEPARATELY since they go into
            // SSE registers (separate from the general purpose registers)
            farg->arg_num = fp_arg_num++;
        } else {
            farg->arg_num = gpr_arg_num++;
        }
        emit(c, farg);
        fargs[i] = farg;
    }
    for (int i = 0; i < nargs; i++) { // Emit IR_ALLOCs
        IrIns *alloc = new_ir(IR_ALLOC);
        // IR_ALLOC returns a POINTER
        alloc->type = t_ptr(t_copy(args[i]->decl.type));
        emit(c, alloc);
        args[i]->alloc = alloc;
        IrIns *store = new_ir(IR_STORE);
        store->l = alloc;
        store->r = fargs[i];
        emit(c, store);
    }
}

static void ensure_ret(Fn *fn) {
    for (BB *bb = fn->entry; bb; bb = bb->next) { // Iterate over all BBs
        IrIns *end = bb->ir_head;
        if (!end) { // BB is empty, put RET0 in it
            emit_ir(bb, new_ir(IR_RET0));
            continue;
        }
        while (end->next) { // Find the last instruction
            end = end->next;
        }
        // The last instruction in a basic block must be a branch or ret
        if (end->op != IR_BR && end->op != IR_CONDBR &&
            end->op != IR_RET0 && end->op != IR_RET1) {
            emit_ir(bb, new_ir(IR_RET0));
        }
    }
}

static char * prepend_underscore(char *str, size_t len) {
    char *out = malloc(len + 2);
    out[0] = '_';
    strncpy(&out[1], str, len);
    return out;
}

static Fn * compile_fn_def(Compiler *c, FnDef *ast_fn) {
    Fn *fn = new_fn();
    c->fn = fn;
    Declarator *fn_decl = &ast_fn->local->decl;
    fn->name = prepend_underscore(fn_decl->name->start, fn_decl->name->len);
    fn->entry = emit_bb(c); // Entry block
    compile_fn_args(c, fn_decl->type->args, fn_decl->type->nargs);
    compile_block(c, ast_fn->body); // Body
    ensure_ret(fn); // Make sure every BB ends with a terminator instruction
    return fn;
}

static Module * compile_module(Compiler *c, AstModule *ast) {
    Module *module = malloc(sizeof(Module));
    module->fns = NULL;
    Fn **fn = &module->fns;
    for (FnDef *ast_fn = ast->fns; ast_fn; ast_fn = ast_fn->next) {
        *fn = compile_fn_def(c, ast_fn);
        fn = &(*fn)->next;
    }
    return module;
}

Module * compile(AstModule *ast) {
    Compiler c;
    c.fn = NULL;
    c.loop = NULL;
    Module *module = compile_module(&c, ast);
    return module;
}
