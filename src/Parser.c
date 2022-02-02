
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <math.h>

#include "Parser.h"

#define BB_PREFIX ".BB_"

typedef struct {
    Type type;
    char *name;
    IrIns *alloc; // The IR_ALLOC instruction that created this local
} Local;

// A jump list is a linked list of pointers into 'IR_BR' or 'IR_CONDBR'
// arguments (either 'ins->true' or 'ins->false' branch targets) that need to
// be back-filled when the destination for an expression is determined.
typedef struct jmp_list {
    BB **jmp;
    IrIns *br; // The IR_BR or IR_CONDBR instruction referred to by 'jmp'
    struct jmp_list *next;
} JmpList;

typedef struct loop {
    JmpList *break_list;
    struct loop *outer;
} Loop;

typedef struct {
    Lexer l;
    FnDef *fn;     // Function we're parsing
    Local *locals; // Local variables in scope
    Loop *loop;    // Innermost loop that we're parsing (for breaks)
    int num_locals, max_locals;
} Parser;

static Parser new_parser(char *source) {
    Parser p;
    p.l = new_lexer(source);
    next_tk(&p.l); // Lex the first token in the file
    p.fn = NULL;
    p.num_locals = 0;
    p.max_locals = 8;
    p.locals = malloc(sizeof(Local) * p.max_locals);
    return p;
}

static FnDef * new_fn() {
    FnDef *fn = malloc(sizeof(FnDef));
    fn->decl = NULL;
    fn->entry = NULL;
    fn->last = NULL;
    return fn;
}

static BB * emit_bb(Parser *p) {
    BB *bb = new_bb();
    bb->prev = p->fn->last;
    if (p->fn->last) {
        p->fn->last->next = bb;
    }
    p->fn->last = bb;
    return bb;
}

static void delete_bb(Parser *p, BB *bb) {
    assert(bb->prev); // CAN'T delete the entry BB!
    bb->prev->next = bb->next;
    if (p->fn->last == bb) {
        p->fn->last = bb->prev;
    }
}

static IrIns * emit(Parser *p, IrOpcode op) { // Wrapper
    return emit_ir(p->fn->last, op);
}

static void def_local(Parser *p, Local local) {
    // TODO: compare against function definitions too!
    for (int i = p->num_locals - 1; i >= 0; i--) { // Check local isn't defined
        if (strcmp(p->locals[i].name, local.name) == 0) {
            printf("local already defn\n");
            exit(1);
        }
    }
    if (p->num_locals >= p->max_locals) { // Allocate more space if needed
        p->max_locals *= 2;
        p->locals = realloc(p->locals, sizeof(Local) * p->max_locals);
    }
    p->locals[p->num_locals++] = local;
}

static Phi * new_phi(BB *bb, IrIns *def) {
    Phi *phi = malloc(sizeof(Phi));
    phi->next = NULL;
    phi->bb = bb;
    phi->def = def;
    return phi;
}


// ---- Expressions -----------------------------------------------------------

typedef enum {
    PREC_NONE,
    PREC_COMMA,   // Comma operator
    PREC_ASSIGN,  // =, +=, -=, *=, /=, %=, &=, |=, ^=, >>=, <<=
    PREC_TERNARY, // ?
    PREC_OR,      // ||
    PREC_AND,     // &&
    PREC_BIT_OR,  // |
    PREC_BIT_XOR, // ^
    PREC_BIT_AND, // &
    PREC_EQ,      // ==, !=
    PREC_GTLT,    // <, >, <=, >=
    PREC_SHIFT,   // >>, <<
    PREC_ADD,     // +, -
    PREC_MUL,     // *, /, %
    PREC_UNARY,   // ++, -- (prefix), -, + (unary), !, ~, casts, *, &, sizeof
    PREC_POSTFIX, // ++, -- (postfix), calls, array index, member access (., ->)
} Prec;

static Prec UNOP_PREC[TK_LAST] = {
    ['-'] = PREC_UNARY,  // Negation
    ['~'] = PREC_UNARY, // Bitwise not
    ['!'] = PREC_UNARY,  // Logical not
    [TK_INC] = PREC_UNARY, // Increment
    [TK_DEC] = PREC_UNARY, // Decrement
};

static Prec POSTOP_PREC[TK_LAST] = {
    [TK_INC] = PREC_POSTFIX, // Increment
    [TK_DEC] = PREC_POSTFIX, // Decrement
};

static Prec BINOP_PREC[TK_LAST] = {
    ['*'] = PREC_MUL,         // Multiplication
    ['/'] = PREC_MUL,         // Division
    ['%'] = PREC_MUL,         // Modulo
    ['+'] = PREC_ADD,         // Addition
    ['-'] = PREC_ADD,         // Subtraction
    [TK_LSHIFT] = PREC_SHIFT, // Left shift
    [TK_RSHIFT] = PREC_SHIFT, // Right shift
    ['<'] = PREC_GTLT,        // Less than
    [TK_LE] = PREC_GTLT,      // Less than or equal
    ['>'] = PREC_GTLT,        // Greater than
    [TK_GE] = PREC_GTLT,      // Greater than or equal
    [TK_EQ] = PREC_EQ,        // Equal
    [TK_NEQ] = PREC_EQ,       // Not equal
    ['&'] = PREC_BIT_AND,     // Bitwise and
    ['^'] = PREC_BIT_XOR,     // Bitwise xor
    ['|'] = PREC_BIT_OR,      // Bitwise or
    [TK_AND] = PREC_AND,      // Logical and
    [TK_OR] = PREC_OR,        // Logical or
    ['?'] = PREC_TERNARY,     // Ternary operator
    ['='] = PREC_ASSIGN,      // Assignments
    [TK_ADD_ASSIGN] = PREC_ASSIGN,
    [TK_SUB_ASSIGN] = PREC_ASSIGN,
    [TK_MUL_ASSIGN] = PREC_ASSIGN,
    [TK_DIV_ASSIGN] = PREC_ASSIGN,
    [TK_MOD_ASSIGN] = PREC_ASSIGN,
    [TK_AND_ASSIGN] = PREC_ASSIGN,
    [TK_OR_ASSIGN] = PREC_ASSIGN,
    [TK_XOR_ASSIGN] = PREC_ASSIGN,
    [TK_LSHIFT_ASSIGN] = PREC_ASSIGN,
    [TK_RSHIFT_ASSIGN] = PREC_ASSIGN,
};

static int IS_RIGHT_ASSOC[TK_LAST] = {
    ['?'] = 1, // Ternary operator is right associative
    ['='] = 1, // Assignment is right associative
    [TK_ADD_ASSIGN] = 1,
    [TK_SUB_ASSIGN] = 1,
    [TK_MUL_ASSIGN] = 1,
    [TK_DIV_ASSIGN] = 1,
    [TK_MOD_ASSIGN] = 1,
    [TK_AND_ASSIGN] = 1,
    [TK_OR_ASSIGN] = 1,
    [TK_XOR_ASSIGN] = 1,
    [TK_LSHIFT_ASSIGN] = 1,
    [TK_RSHIFT_ASSIGN] = 1,
};

static IrOpcode BINOP_OPCODES[TK_LAST] = {
    ['+'] = IR_ADD,
    ['-'] = IR_SUB,
    ['*'] = IR_MUL,
    ['/'] = IR_DIV,
    ['%'] = IR_MOD,
    ['&'] = IR_AND,
    ['|'] = IR_OR,
    ['^'] = IR_XOR,
    [TK_EQ] = IR_EQ,
    [TK_NEQ] = IR_NEQ,
    ['<'] = IR_SLT,
    [TK_LE] = IR_SLE,
    ['>'] = IR_SGT,
    [TK_GE] = IR_SGE,
    [TK_LSHIFT] = IR_SHL,
    [TK_RSHIFT] = IR_ASHR,
    [TK_ADD_ASSIGN] = IR_ADD,
    [TK_SUB_ASSIGN] = IR_SUB,
    [TK_MUL_ASSIGN] = IR_MUL,
    [TK_DIV_ASSIGN] = IR_DIV,
    [TK_MOD_ASSIGN] = IR_MOD,
    [TK_AND_ASSIGN] = IR_AND,
    [TK_OR_ASSIGN] = IR_OR,
    [TK_XOR_ASSIGN] = IR_XOR,
    [TK_LSHIFT_ASSIGN] = IR_SHL,
    [TK_RSHIFT_ASSIGN] = IR_ASHR,
};

typedef enum {
    EXPR_INS,   // Result of an operation
    EXPR_LOCAL, // Local variable that's yet to be loaded (no IR_LOAD emitted)
    EXPR_COND,  // Conditional branch (e.g., in an '&&' expression)
} ExprType;

// For an EXPR_COND, the 'true_list' refers to all the branch targets that
// need to point to the true case, and the 'false_list' refers to all the
// branch targets that need to point to the false case.
typedef struct {
    ExprType type;
    union {
        IrIns *ins;   // For EXPR_INS
        Local *local; // For EXPR_LOCAL
        struct { IrIns *_; JmpList *true_list, *false_list; }; // For EXPR_COND
    };
} Expr;

static Expr new_expr(ExprType type) {
    Expr expr;
    expr.type = type;
    expr.ins = NULL;
    expr.true_list = NULL;
    expr.false_list = NULL;
    return expr;
}

static JmpList * new_jmp_list(BB **jmp, IrIns *br) {
    JmpList *j = malloc(sizeof(JmpList));
    j->jmp = jmp;
    j->br = br;
    j->next = NULL;
    return j;
}

// Patch the branches in a jump list so that they all point to 'target'
static void patch_jmp_list(JmpList *head, BB *target) {
    while (head) {
        *head->jmp = target;
        JmpList *next = head->next;
        free(head); // Free the jump list as we go
        head = next;
    }
}

// Append the given jump list to the end of the other
static void merge_jmp_lists(JmpList **head, JmpList *to_append) {
    if (!to_append) {
        return;
    }
    while (*head) { // Find the end of the jump list
        head = &(*head)->next;
    }
    *head = to_append;
}

// Emits an IR_LOAD instruction for a local variable
static Expr discharge_local(Parser *p, Expr local) {
    IrIns *load = emit(p, IR_LOAD);
    load->l = local.local->alloc;
    load->type = local.local->type;
    Expr result = new_expr(EXPR_INS);
    result.ins = load;
    return result;
}

// Creates a new basic block and an IR_PHI instruction for the result of a
// condition that's used as a boolean variable
static Expr discharge_cond(Parser *p, Expr cond) {
    assert(cond.type == EXPR_COND); // Ensure we are discharging a conditional
    assert(cond.ins->op == IR_CONDBR);

    BB *bb = emit_bb(p); // Basic block for the result of the condition
    IrIns *k_false = emit(p, IR_KI32); // True and false constants
    k_false->ki32 = 0;
    k_false->type.prim = T_i32;
    k_false->type.ptrs = 0;
    IrIns *k_true = emit(p, IR_KI32);
    k_true->ki32 = 1;
    k_true->type.prim = T_i32;
    k_true->type.ptrs = 0;

    Phi *phi_head = NULL; // Construct the phi chain
    Phi **phi = &phi_head;
    for (JmpList *true = cond.true_list; true; true = true->next) {
        if (true->br == cond.ins) {
            continue; // Handle the last instruction separately
        }
        *phi = new_phi(true->br->bb, k_true);
        phi = &(*phi)->next;
    }
    for (JmpList *false = cond.false_list; false; false = false->next) {
        if (false->br == cond.ins) {
            continue; // Handle the last instruction separately
        }
        *phi = new_phi(false->br->bb, k_false);
        phi = &(*phi)->next;
    }

    IrIns *last_cond = cond.ins->cond;
    // If there's only one predecessor block (empty phi), then roll back the
    // conditional
    if (!phi_head) {
        delete_bb(p, bb); // Roll back the new BB we created
        int is_neg = *(cond.true_list->jmp) == cond.ins->false;
        delete_ir(cond.ins); // Delete the IR_CONDBR instruction
        IrIns *result_ins = last_cond;
        if (is_neg) { // If we need to negate the condition
            k_true = emit(p, IR_KI32);
            k_true->ki32 = 1;
            k_true->type.prim = T_i32;
            k_true->type.ptrs = 0;
            IrIns *xor = emit(p, IR_XOR);
            xor->l = result_ins;
            xor->r = k_true;
            xor->type = result_ins->type;
            result_ins = xor;
        }
        Expr result = new_expr(EXPR_INS);
        result.ins = result_ins; // Result is the condition instruction
        return result;
    }

    // Patch the true and false list here
    patch_jmp_list(cond.true_list, bb);
    patch_jmp_list(cond.false_list, bb);

    // Handle the last condition in the phi chain separately
    cond.ins->op = IR_BR; // Change the last conditional branch into an
    cond.ins->br = bb;    // unconditional one
    *phi = new_phi(cond.ins->bb, last_cond);

    IrIns *phi_ins = emit(p, IR_PHI); // Phi instruction for the result
    phi_ins->phi = phi_head;
    phi_ins->type.prim = T_i32;
    phi_ins->type.ptrs = 0;
    Expr result = new_expr(EXPR_INS);
    result.ins = phi_ins;
    return result;
}

// Convert all expressions into EXPR_INS
static Expr discharge(Parser *p, Expr expr) {
    if (expr.type == EXPR_LOCAL) {
        return discharge_local(p, expr);
    } else if (expr.type == EXPR_COND) {
        return discharge_cond(p, expr);
    } else {
        return expr; // Already discharged
    }
}

// Convert an expression into a condition (e.g., for an if or while statement)
// by emitting a comparison (if needed) and a branch
static Expr to_cond(Parser *p, Expr expr) {
    if (expr.type == EXPR_COND) {
        return expr; // Already a condition, don't need to do anything
    }
    expr = discharge(p, expr);
    if (!(expr.ins->op >= IR_EQ && expr.ins->op <= IR_UGE)) {
        // 'expr' isn't a comparison that we can branch on; emit a branch on the
        // truth value of 'expr'
        IrIns *k_false = emit(p, IR_KI32);
        k_false->ki32 = 0;
        k_false->type.prim = T_i32;
        k_false->type.ptrs = 0;
        IrIns *cmp = emit(p, IR_NEQ);
        cmp->l = expr.ins;
        cmp->r = k_false;
        cmp->type.prim = T_i32;
        cmp->type.ptrs = 0;
        expr.ins = cmp;
    }
    IrIns *br = emit(p, IR_CONDBR); // Emit a branch on the condition
    br->cond = expr.ins;
    Expr result = new_expr(EXPR_COND);
    result.ins = br;
    result.true_list = new_jmp_list(&br->true, br);
    result.false_list = new_jmp_list(&br->false, br);
    return result;
}

static Expr parse_subexpr(Parser *p, Prec min_prec); // Forward declaration

static Expr parse_ternary(Parser *p, Expr cond, Expr true_val) {
    true_val = discharge(p, true_val);
    IrIns *true_br = emit(p, IR_BR);

    expect_tk(&p->l, ':');
    next_tk(&p->l);
    BB *false_bb = emit_bb(p); // New BB for the false value
    patch_jmp_list(cond.false_list, false_bb);
    // '- 1' since '?' is right associative
    Expr false_val = parse_subexpr(p, PREC_TERNARY - 1);
    false_val = discharge(p, false_val);
    IrIns *false_br = emit(p, IR_BR);

    // Create a new BB for everything after, because phis can only occur at the
    // start of BBs
    BB *after_bb = emit_bb(p);
    true_br->br = after_bb;
    false_br->br = after_bb;

    // Emit a phi
    IrIns *phi_ins = emit(p, IR_PHI);
    BB *true_bb = cond.ins->bb->next; // The true value is right after cond
    phi_ins->phi = new_phi(cond.ins->bb->next, true_val.ins);
    phi_ins->phi->next = new_phi(false_bb, false_val.ins);
    phi_ins->type = true_val.ins->type;
    Expr result = new_expr(EXPR_INS);
    result.ins = phi_ins;
    return result;
}

static Expr parse_operation(Parser *p, Tk binop, Expr left, Expr right) {
    left = discharge(p, left);
    right = discharge(p, right);

    // 'left' and 'right' should have the same type
    assert(left.ins->type.prim == right.ins->type.prim);
    assert(left.ins->type.ptrs == right.ins->type.ptrs);

    IrIns *operation = emit(p, BINOP_OPCODES[binop]);
    operation->l = left.ins;
    operation->r = right.ins;
    operation->type = left.ins->type; // Same as 'right.ins->type'
    Expr result = new_expr(EXPR_INS);
    result.ins = operation;
    return result;
}

static Expr parse_assign(Parser *p, Tk binop, Expr left, Expr right) {
    if (binop != '=') {
        right = parse_operation(p, binop, left, right);
    }
    assert(left.type == EXPR_LOCAL); // Can only assign to lvalues
    right = discharge(p, right);
    IrIns *store = emit(p, IR_STORE);
    store->l = left.local->alloc;
    store->r = right.ins;
    store->type = left.local->type;
    return right; // Assignment evaluates to its right operand
}

static Expr parse_and(Parser *p, Expr left, Expr right) {
    right = to_cond(p, right);
    // Merge left's false list onto the right operand's false list
    merge_jmp_lists(&right.false_list, left.false_list);
    return right;
}

static Expr parse_or(Parser *p, Expr left, Expr right) {
    right = to_cond(p, right);
    // Merge left's true list onto the right operand's true list
    merge_jmp_lists(&right.true_list, left.true_list);
    return right;
}

static Expr parse_binary(Parser *p, Tk binop, Expr left, Expr right) {
    switch (binop) {
    case '=':
    case TK_ADD_ASSIGN: case TK_SUB_ASSIGN:
    case TK_MUL_ASSIGN: case TK_DIV_ASSIGN: case TK_MOD_ASSIGN:
    case TK_AND_ASSIGN: case TK_OR_ASSIGN:  case TK_XOR_ASSIGN:
    case TK_LSHIFT_ASSIGN: case TK_RSHIFT_ASSIGN:
        return parse_assign(p, binop, left, right);
    case TK_AND: return parse_and(p, left, right);
    case TK_OR:  return parse_or(p, left, right);
    case '?':    return parse_ternary(p, left, right);
    default:     return parse_operation(p, binop, left, right);
    }
}

static Expr parse_and_left(Parser *p, Expr left) {
    left = to_cond(p, left);
    BB *right_bb = emit_bb(p); // New BB for the right operand
    // Left's true case should target the right operand
    patch_jmp_list(left.true_list, right_bb);
    return left;
}

static Expr parse_or_left(Parser *p, Expr left) {
    left = to_cond(p, left);
    BB *right_bb = emit_bb(p); // New BB for the right operand
    // Left's false case should target the right operand
    patch_jmp_list(left.false_list, right_bb);
    return left;
}

static Expr parse_ternary_left(Parser *p, Expr cond) {
    cond = to_cond(p, cond);
    BB *true_bb = emit_bb(p); // New BB for the false value
    // The condition's true case should target the true value
    patch_jmp_list(cond.true_list, true_bb);
    return cond;
}

static Expr parse_binary_left(Parser *p, Tk binop, Expr left) {
    switch (binop) {
        case TK_AND: return parse_and_left(p, left);
        case TK_OR:  return parse_or_left(p, left);
        case '?':    return parse_ternary_left(p, left);
        default:     return left;
    }
}

static Expr parse_const_int(Parser *p) {
    expect_tk(&p->l, TK_NUM);
    long value = p->l.num;
    next_tk(&p->l);
    IrIns *k = emit(p, IR_KI32);
    k->ki32 = (int32_t) value;
    k->type.prim = T_i32;
    k->type.ptrs = 0;
    Expr result = new_expr(EXPR_INS);
    result.ins = k;
    return result;
}

static Expr parse_local(Parser *p) {
    expect_tk(&p->l, TK_IDENT);
    char *name = p->l.ident;
    int len = p->l.len;
    Local *local = NULL;
    for (int i = 0; i < p->num_locals; i++) {
        char *candidate = p->locals[i].name;
        if (len == strlen(candidate) && strncmp(name, candidate, len) == 0) {
            local = &p->locals[i];
            break;
        }
    }
    if (!local) { // Check the local exists
        printf("undeclared variable\n");
        exit(1);
    }
    next_tk(&p->l);
    Expr result = new_expr(EXPR_LOCAL);
    result.local = local;
    return result;
}

static Expr parse_braced_subexpr(Parser *p) {
    expect_tk(&p->l, '(');
    next_tk(&p->l);
    Expr expr = parse_subexpr(p, PREC_NONE);
    expect_tk(&p->l, ')');
    next_tk(&p->l);
    return expr;
}

static Expr parse_operand(Parser *p) {
    switch (p->l.tk) {
        case TK_NUM:   return parse_const_int(p);
        case TK_IDENT: return parse_local(p);
        case '(':      return parse_braced_subexpr(p);
        default:       printf("expected expression\n"); exit(1);
    }
}

static Expr parse_neg(Parser *p, Expr operand) {
    operand = discharge(p, operand);
    IrIns *zero = emit(p, IR_KI32); // -a is equivalent to '0 - a'
    zero->ki32 = 0;
    zero->type.prim = T_i32;
    zero->type.ptrs = 0;
    IrIns *operation = emit(p, IR_SUB);
    operation->l = zero;
    operation->r = operand.ins;
    operation->type = operand.ins->type;
    Expr result = new_expr(EXPR_INS);
    result.ins = operation;
    return result;
}

static Expr parse_bit_not(Parser *p, Expr operand) {
    operand = discharge(p, operand);
    IrIns *neg1 = emit(p, IR_KI32); // ~a is equivalent to 'a ^ -1'
    neg1->ki32 = -1;
    neg1->type.prim = T_i32;
    neg1->type.ptrs = 0;
    IrIns *operation = emit(p, IR_XOR);
    operation->l = operand.ins;
    operation->r = neg1;
    operation->type = operand.ins->type;
    Expr result = new_expr(EXPR_INS);
    result.ins = operation;
    return result;
}

static Expr parse_not(Parser *p, Expr operand) {
    operand = to_cond(p, operand);
    JmpList *true_list = operand.true_list; // Swap true and false lists
    operand.true_list = operand.false_list;
    operand.false_list = true_list;
    return operand;
}

static Expr parse_inc_dec(Parser *p, Tk op, Expr operand, int is_prefix) {
    IrIns *one = emit(p, IR_KI32); // i++ is equivalent to 'i = i + 1'
    one->ki32 = 1;
    one->type.prim = T_i32;
    one->type.ptrs = 0;
    Expr one_expr = new_expr(EXPR_INS);
    one_expr.ins = one;
    // Can't use add-assign/sub-assign here since only want to discharge ONCE
    Expr discharged = discharge(p, operand);
    Tk binop = op == TK_INC ? '+' : '-';
    Expr operation = parse_operation(p, binop, discharged, one_expr);
    Expr assign = parse_assign(p, '=', operand, operation);
    if (is_prefix) {
        return assign; // Prefix evaluates to the result of the assignment
    } else {
        return discharged; // Postfix evaluates to the operand itself
    }
}

static Expr parse_postfix(Parser *p, Expr operand) {
    Tk postop = p->l.tk;
    if (POSTOP_PREC[postop]) { // Is there a postfix operator
        next_tk(&p->l); // Skip the postfix operator
        switch (postop) {
            case TK_INC: case TK_DEC:
                return parse_inc_dec(p, postop, operand, 0);
            default: UNREACHABLE();
        }
    } else {
        return operand;
    }
}

static Expr parse_unary(Parser *p) {
    Tk unop = p->l.tk;
    if (UNOP_PREC[unop]) {
        next_tk(&p->l); // Skip the unary operator
        Expr operand = parse_subexpr(p, UNOP_PREC[unop]);
        switch (unop) {
            case '-': return parse_neg(p, operand);
            case '~': return parse_bit_not(p, operand);
            case '!': return parse_not(p, operand);
            case TK_INC: case TK_DEC:
                return parse_inc_dec(p, unop, operand, 1);
            default: UNREACHABLE();
        }
    } else { // No unary operator, try parsing a postfix operator
        Expr operand = parse_operand(p);
        return parse_postfix(p, operand);
    }
}

static Expr parse_subexpr(Parser *p, Prec min_prec) {
    Expr left = parse_unary(p);
    while (BINOP_PREC[p->l.tk] > min_prec) {
        Tk binop = p->l.tk;
        next_tk(&p->l); // Skip the operator
        left = parse_binary_left(p, binop, left);
        Prec prec = BINOP_PREC[binop] - IS_RIGHT_ASSOC[binop];
        Expr right = parse_subexpr(p, prec); // Parse the right operand
        left = parse_binary(p, binop, left, right); // Emit the operation
    }
    return left;
}

static Expr parse_expr(Parser *p) {
    return parse_subexpr(p, PREC_NONE); // Wrapper for 'parse_subexpr'
}


// ---- Statements ------------------------------------------------------------

static Type parse_decl_spec(Parser *p) {
    expect_tk(&p->l, TK_INT); // The only type available for now
    next_tk(&p->l);
    Type type;
    type.prim = T_i32;
    type.ptrs = 0;
    return type;
}

static void parse_decl(Parser *p) {
    Type type = parse_decl_spec(p); // Type
    expect_tk(&p->l, TK_IDENT); // Name
    char *name = malloc((p->l.len + 1) * sizeof(char));
    strncpy(name, p->l.ident, p->l.len);
    name[p->l.len] = '\0';
    next_tk(&p->l);

    IrIns *alloc = emit(p, IR_ALLOC); // Create some stack space
    alloc->type = type;
    alloc->type.ptrs += 1; // The result of IR_ALLOC is a POINTER to the value
    if (p->l.tk == '=') { // Check if we have a definition too
        next_tk(&p->l); // Skip the '=' token
        Expr expr = parse_expr(p); // Value
        expr = discharge(p, expr);
        IrIns *store = emit(p, IR_STORE);
        store->l = alloc;
        store->r = expr.ins;
        store->type = expr.ins->type;
    }
    Local local;
    local.name = name;
    local.type = type;
    local.alloc = alloc;
    def_local(p, local);
}

static void parse_stmt(Parser *p); // Forward declaration

// The body for an 'if', 'while', etc. statement can be either a single
// statement (with its OWN local variable scope), or a braced block of multiple
// statements.
static void parse_body(Parser *p) {
    int num_locals = p->num_locals; // Create a new scope for locals
    parse_stmt(p);
    p->num_locals = num_locals; // Get rid of any locals defined in the block
}

static void parse_if(Parser *p) {
    expect_tk(&p->l, TK_IF);
    JmpList *jmp_list_head = NULL;
    JmpList **jmp_list = &jmp_list_head;
    BB *after;
    int has_else = 0;
    while (p->l.tk == TK_IF) { // Parse 'if' and 'else if's
        next_tk(&p->l);
        expect_tk(&p->l, '(');
        next_tk(&p->l);
        Expr cond = parse_expr(p); // Condition
        cond = to_cond(p, cond);
        expect_tk(&p->l, ')');
        next_tk(&p->l);

        BB *body = emit_bb(p); // Body
        patch_jmp_list(cond.true_list, body);
        parse_body(p);
        IrIns *end_br = emit(p, IR_BR); // End body with branch
        // Add the body's end branch to the jump list
        *jmp_list = new_jmp_list(&end_br->br, end_br);
        jmp_list = &((*jmp_list)->next);

        after = emit_bb(p);
        patch_jmp_list(cond.false_list, after);

        has_else = 0;
        if (p->l.tk == TK_ELSE) { // Check for an 'else'
            has_else = 1;
            next_tk(&p->l); // Skip over 'else'
        } else {
            break;
        }
    }
    if (has_else) { // Deal with 'else'
        parse_body(p);
        IrIns *end_br = emit(p, IR_BR); // End body with branch
        // Add the body's end branch to the jump list
        *jmp_list = new_jmp_list(&end_br->br, end_br);
        jmp_list = &((*jmp_list)->next);
        after = emit_bb(p); // New BB for everything after the if statement
    }
    // Patch the branches at the end of all the bodies to here
    patch_jmp_list(jmp_list_head, after);
}

static void parse_while(Parser *p) {
    expect_tk(&p->l, TK_WHILE);
    next_tk(&p->l);
    IrIns *before_br = emit(p, IR_BR);
    BB *cond_bb = emit_bb(p);
    before_br->br = cond_bb;

    expect_tk(&p->l, '(');
    next_tk(&p->l);
    Expr cond = parse_expr(p); // Condition
    cond = to_cond(p, cond);
    expect_tk(&p->l, ')');
    next_tk(&p->l);

    Loop loop;
    loop.break_list = NULL;
    loop.outer = p->loop;
    p->loop = &loop;
    BB *body = emit_bb(p); // Body
    patch_jmp_list(cond.true_list, body);
    parse_body(p);
    IrIns *end_br = emit(p, IR_BR); // End body with branch to cond_bb
    end_br->br = cond_bb;
    p->loop = loop.outer;

    BB *after = emit_bb(p);
    patch_jmp_list(cond.false_list, after);
    patch_jmp_list(loop.break_list, after);
}

static void parse_for(Parser *p) {
    expect_tk(&p->l, TK_FOR);
    next_tk(&p->l);

    expect_tk(&p->l, '(');
    next_tk(&p->l);
    int num_locals = p->num_locals; // Create a new variable scope
    parse_decl(p); // Declaration
    expect_tk(&p->l, ';');
    next_tk(&p->l);

    IrIns *before_br = emit(p, IR_BR);
    BB *cond_bb = emit_bb(p);
    before_br->br = cond_bb;
    Expr cond = parse_expr(p); // Condition
    cond = to_cond(p, cond);
    expect_tk(&p->l, ';');
    next_tk(&p->l);

    BB *increment_bb = emit_bb(p); // Increment
    parse_expr(p);
    p->fn->last = increment_bb->prev; // Un-attach the increment BB
    p->fn->last->next = NULL;
    expect_tk(&p->l, ')');
    next_tk(&p->l);

    Loop loop;
    loop.break_list = NULL;
    loop.outer = p->loop;
    p->loop = &loop;

    BB *body = emit_bb(p); // Body
    patch_jmp_list(cond.true_list, body);
    parse_body(p);
    // Attach the increment BB to the end of the body
    IrIns *body_br = emit(p, IR_BR); // End body with branch to increment_bb
    body_br->br = increment_bb;
    p->fn->last->next = increment_bb;
    increment_bb->prev = p->fn->last;
    p->fn->last = increment_bb;
    IrIns *inc_br = emit(p, IR_BR); // Branch to cond_bb
    inc_br->br = cond_bb;

    p->loop = loop.outer;

    BB *after = emit_bb(p);
    patch_jmp_list(cond.false_list, after);
    patch_jmp_list(loop.break_list, after);
    p->num_locals = num_locals; // Get rid of locals declared
}

static void parse_do_while(Parser *p) {
    expect_tk(&p->l, TK_DO);
    next_tk(&p->l);
    IrIns *before_br = emit(p, IR_BR);

    Loop loop;
    loop.break_list = NULL;
    loop.outer = p->loop;
    p->loop = &loop;
    BB *body = emit_bb(p); // Body
    before_br->br = body;
    parse_body(p);
    p->loop = loop.outer;

    expect_tk(&p->l, TK_WHILE);
    next_tk(&p->l);
    expect_tk(&p->l, '(');
    next_tk(&p->l);
    Expr cond = parse_expr(p); // Condition
    cond = to_cond(p, cond);
    expect_tk(&p->l, ')');
    next_tk(&p->l);
    expect_tk(&p->l, ';');
    next_tk(&p->l);

    patch_jmp_list(cond.true_list, body);
    BB *after = emit_bb(p);
    patch_jmp_list(cond.false_list, after);
    patch_jmp_list(loop.break_list, after);
}

static void parse_break(Parser *p) {
    expect_tk(&p->l, TK_BREAK);
    next_tk(&p->l);
    IrIns *br = emit(p, IR_BR);
    JmpList *jmp_list = new_jmp_list(&br->br, br);
    merge_jmp_lists(&p->loop->break_list, jmp_list);
    emit_bb(p); // For everything after the break
}

static void parse_ret(Parser *p) {
    expect_tk(&p->l, TK_RETURN);
    next_tk(&p->l);
    IrIns *value = NULL;
    if (p->l.tk != ';') { // If we're returning something
        Expr expr = parse_expr(p);
        expr = discharge(p, expr);
        value = expr.ins;
    }
    IrIns *ret = emit(p, value ? IR_RET1 : IR_RET0);
    ret->l = value;
}

static void parse_braced_block(Parser *p); // Forward declaration

static void parse_stmt(Parser *p) {
    switch (p->l.tk) {
        case ';':       next_tk(&p->l); return;        // Empty statement
        case '{':       parse_braced_block(p); return; // Block
        case TK_IF:     parse_if(p); return;           // If statement
        case TK_WHILE:  parse_while(p); return;        // While loop
        case TK_FOR:    parse_for(p); return;          // For loop
        case TK_DO:     parse_do_while(p); return;     // Do-while loop
        case TK_BREAK:  parse_break(p); break;         // Break
        case TK_RETURN: parse_ret(p); break;           // Return
        case TK_INT:    parse_decl(p); break;          // Declaration
        default:        parse_expr(p); break;          // Expression statement
    }
    expect_tk(&p->l, ';');
    next_tk(&p->l);
}

static void parse_braced_block(Parser *p) {
    expect_tk(&p->l, '{');
    next_tk(&p->l);
    int num_locals = p->num_locals;
    while (p->l.tk != '\0' && p->l.tk != '}') {
        parse_stmt(p);
    }
    p->num_locals = num_locals; // Get rid of any locals allocated in the block
    expect_tk(&p->l, '}');
    next_tk(&p->l);
}


// ---- Top Level Module ------------------------------------------------------

static IrIns * parse_fn_arg(Parser *p, int narg) {
    Type arg_type = parse_decl_spec(p); // Type
    expect_tk(&p->l, TK_IDENT); // Name
    char *name = malloc((p->l.len + 1) * sizeof(char));
    strncpy(name, p->l.ident, p->l.len);
    name[p->l.len] = '\0';
    next_tk(&p->l);

    IrIns *farg = emit(p, IR_FARG); // Define the argument
    farg->arg_num = narg;
    farg->type = arg_type;
    Local local; // Create a local for the function argument
    local.name = name;
    local.type = arg_type;
    local.alloc = NULL;
    def_local(p, local);
    return farg;
}

static void parse_fn_args(Parser *p) {
    int arg_num = 0;
    IrIns *first = NULL;
    // Put all the IR_FARGs together at the start of the function
    while (p->l.tk != '\0' && p->l.tk != ')') {
        IrIns *farg = parse_fn_arg(p, arg_num++); // Parse an argument
        if (!first) { // Save the first one
            first = farg;
        }
        if (p->l.tk == ',') { // Check for another argument
            next_tk(&p->l);
            continue;
        } else {
            break;
        }
    }
    arg_num = 0;
    for (IrIns *farg = first; farg && farg->op == IR_FARG; farg = farg->next) {
        IrIns *alloc = emit(p, IR_ALLOC); // Create IR_ALLOC for each
        alloc->type = farg->type;
        alloc->type.ptrs += 1; // IR_ALLOC returns a POINTER
        IrIns *store = emit(p, IR_STORE);
        store->l = alloc;
        store->r = farg;
        store->type = farg->type;
        p->locals[arg_num++].alloc = alloc;
    }
}

static FnDecl * parse_fn_decl(Parser *p) {
    FnDecl *decl = malloc(sizeof(FnDecl));
    decl->return_type = parse_decl_spec(p); // Return type
    expect_tk(&p->l, TK_IDENT);
    decl->name = malloc((p->l.len + 1) * sizeof(char)); // Name
    strncpy(decl->name, p->l.ident, p->l.len);
    decl->name[p->l.len] = '\0';
    next_tk(&p->l);
    expect_tk(&p->l, '('); // Arguments
    next_tk(&p->l);
    parse_fn_args(p);
    expect_tk(&p->l, ')');
    next_tk(&p->l);
    return decl;
}

static void ensure_ret(FnDef *fn) {
    for (BB *bb = fn->entry; bb; bb = bb->next) { // Iterate over all BBs
        IrIns *end = bb->ir_head;
        if (!end) { // BB is empty, put RET0 in it
            emit_ir(bb, IR_RET0);
            continue;
        }
        while (end->next) { // Find the last instruction
            end = end->next;
        }
        // The last instruction in a basic block must be a branch or ret
        if (end->op != IR_BR && end->op != IR_CONDBR &&
                end->op != IR_RET0 && end->op != IR_RET1) {
            emit_ir(bb, IR_RET0);
        }
    }
}

static char * bb_label(int idx) {
    int num_digits = (idx == 0) ? 1 : (int) log10(idx) + 1;
    char *out = malloc(strlen(BB_PREFIX) + num_digits + 1);
    sprintf(out, BB_PREFIX "%d", idx);
    return out;
}

static void label_bbs(FnDef *fn) {
    int idx = 0;
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        if (!bb->label) {
            bb->label = bb_label(idx++);
        }
    }
}

static char * prepend_underscore(char *str) {
    char *out = malloc(strlen(str) + 2);
    out[0] = '_';
    strcpy(&out[1], str);
    return out;
}

static FnDef * parse_fn_def(Parser *p) {
    FnDef *fn = new_fn();
    p->fn = fn;
    fn->entry = emit_bb(p);
    int num_locals = p->num_locals; // 'parse_fn_args' creates new locals
    fn->decl = parse_fn_decl(p); // Declaration
    fn->entry->label = prepend_underscore(fn->decl->name);
    parse_braced_block(p); // Body
    p->num_locals = num_locals; // Get rid of the function's arguments
    ensure_ret(fn);
    label_bbs(fn); // Add a label to BBs without one
    return fn;
}

static Module * parse_module(Parser *p) {
    Module *module = malloc(sizeof(Module));
    module->fn = parse_fn_def(p); // Only one function for now
    return module;
}

static char * read_file(char *path) {
    FILE *f = fopen(path, "r");
    if (!f) {
        return NULL;
    }
    fseek(f, 0, SEEK_END); // Get length
    size_t length = (size_t) ftell(f);
    rewind(f);
    char *source = malloc(sizeof(char) * (length + 1)); // Read file
    fread(source, sizeof(char), length, f);
    fclose(f);
    source[length] = '\0';
    return source;
}

Module * parse(char *file) {
    char *source = read_file(file);
    if (!source) {
        printf("couldn't read file\n");
        exit(1);
    }
    Parser p = new_parser(source);
    Module *module = parse_module(&p);
    free(source);
    return module;
}
