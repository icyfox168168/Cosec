
#include <string.h>
#include <assert.h>

#include "Parser.h"
#include "Error.h"

typedef struct {
    Lexer l;
    FnDef *fn; // Current function we're parsing into
    // Linked list of locals in the current scope; head of the list is the
    // most RECENTLY defined local (not the first one)
    Local *locals;
} Parser;

static Stmt * new_stmt(StmtType kind) {
    Stmt *stmt = malloc(sizeof(Stmt));
    stmt->next = NULL;
    stmt->kind = kind;
    stmt->expr = NULL;
    return stmt;
}

Expr * new_expr(ExprType kind) {
    Expr *expr = malloc(sizeof(Expr));
    expr->kind = kind;
    expr->type = NULL;
    expr->op = 0;
    expr->l = NULL;
    expr->r = NULL;
    return expr;
}

static Local * find_local(Parser *p, char *name, int len) {
    for (Local *l = p->locals; l; l = l->next) {
        if (strlen(l->name) == len && strncmp(l->name, name, len) == 0) {
            return l;
        }
    }
    return NULL;
}

static Local * def_local(Parser *p, TkInfo name, Type *type) {
    if (find_local(p, name.start, name.len)) {
        trigger_error_at(name, "redefinition of '%.*s'", name.len, name.start);
    }
    char *name_str = malloc((name.len + 1) * sizeof(char));
    strncpy(name_str, name.start, name.len);
    name_str[name.len] = '\0';
    Local *local = malloc(sizeof(Local));
    local->next = p->locals; // Prepend to the linked list
    local->name = name_str;
    local->type = type;
    local->alloc = NULL;
    p->locals = local;
    return local;
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

static Prec UNARY_PREC[NUM_TKS] = {
    ['-'] = PREC_UNARY, // Negation
    ['+'] = PREC_UNARY, // Promotion
    ['~'] = PREC_UNARY, // Bitwise not
    ['!'] = PREC_UNARY, // Logical not
    ['&'] = PREC_UNARY, // Address-of
    ['*'] = PREC_UNARY, // Dereference
    ['('] = PREC_UNARY, // Cast
    [TK_INC] = PREC_UNARY, // Increment
    [TK_DEC] = PREC_UNARY, // Decrement
};

static Prec POSTFIX_PREC[NUM_TKS] = {
    [TK_INC] = PREC_POSTFIX, // Increment
    [TK_DEC] = PREC_POSTFIX, // Decrement
    ['['] = PREC_POSTFIX,    // Array access
};

static Prec BINARY_PREC[NUM_TKS] = {
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
    [','] = PREC_COMMA,
};

static int IS_RIGHT_ASSOC[NUM_TKS] = {
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

static Tk ASSIGNMENT_TO_ARITH_OP[NUM_TKS] = {
    [TK_ADD_ASSIGN] = '+',
    [TK_SUB_ASSIGN] = '-',
    [TK_MUL_ASSIGN] = '*',
    [TK_DIV_ASSIGN] = '/',
    [TK_MOD_ASSIGN] = '%',
    [TK_AND_ASSIGN] = '&',
    [TK_OR_ASSIGN] = '|',
    [TK_XOR_ASSIGN] = '^',
    [TK_LSHIFT_ASSIGN] = TK_LSHIFT,
    [TK_RSHIFT_ASSIGN] = TK_RSHIFT,
};

static int is_null_ptr(Expr *e) {
    return e->kind == EXPR_KINT && e->kint == 0;
}

static void ensure_lvalue(Expr *lvalue) {
    // Can only assign to a local, pointer dereference, or array index
    if (!(lvalue->kind == EXPR_LOCAL ||
            (lvalue->kind == EXPR_UNARY && lvalue->op == '*') ||
            (lvalue->kind == EXPR_BINARY && lvalue->op == '['))) {
        trigger_error_at(lvalue->tk, "expression is not assignable");
    }
    if (is_arr(lvalue->type)) {
        trigger_error_at(lvalue->tk, "array type '%s' is not assignable",
                         type_to_str(lvalue->type));
    }
}

static void ensure_can_take_addr(Expr *operand) {
    // See 6.5.3.2 in C99 standard for what's allowed (local, dereference,
    // and array access)
    if (!(operand->kind == EXPR_LOCAL ||
          (operand->kind == EXPR_UNARY && operand->op == '*') ||
          (operand->kind == EXPR_BINARY && operand->op == '['))) {
        trigger_error_at(operand->tk, "cannot take address of operand");
    }
}

static void ensure_can_deref(Expr *operand) {
    // Can only dereference a pointer or an array
    if (operand->type->kind != T_PTR && operand->type->kind != T_ARR) {
        trigger_error_at(operand->tk, "cannot dereference operand of type '%s'",
                         type_to_str(operand->type));
    }
}

__attribute__((noreturn))
static void invalid_arguments(Expr *l, Expr *r) {
    trigger_error_at(merge_tks(l->tk, r->tk),
                     "invalid arguments '%s' and '%s' to operation",
                     type_to_str(l->type), type_to_str(r->type));
}

static void check_conv(Expr *src, Type *t, int explicit_cast) {
    Type *s = src->type;
    if (!((is_arith(t) && is_arith(s)) ||
          (is_ptr(t) && is_ptr(s)) ||
          (is_ptr(t) && is_int(s)) || (is_int(t) && is_ptr(s)) ||
          (is_ptr(t) && is_arr(s)) || (is_arr(t) && is_ptr(s)))) {
        trigger_error_at(src->tk, "invalid conversion from '%s' to '%s'",
                         type_to_str(s), type_to_str(t));
    }
    if (!explicit_cast && is_int(t) && is_int(s) && bits(t) < bits(s)) {
        trigger_warning_at(src->tk, "implicit conversion from '%s' to '%s' "
                                    "loses precision",
                           type_to_str(s), type_to_str(t));
    }
    if (!explicit_cast && is_ptr(t) && is_ptr(s) && !are_equal(t, s) &&
            !(is_void_ptr(s) || is_void_ptr(t) || is_null_ptr(src))) {
        trigger_warning_at(src->tk, "implicit conversion between incompatible "
                                    "pointer types '%s' and '%s'",
                           type_to_str(s), type_to_str(t));
    }
    if (!explicit_cast && is_ptr_arr(t) && is_ptr_arr(s) &&
            !are_equal(t->ptr, s->ptr) && !is_void_ptr(s) && !is_void_ptr(t)) {
        trigger_warning_at(src->tk, "implicit conversion between incompatible "
                                    "pointer and array types '%s' and '%s'",
                           type_to_str(s), type_to_str(t));
    }
}

static Expr * conv_const(Expr *expr, Type *target) {
    if (is_fp(target) && expr->kind == EXPR_KINT) {
        expr->kind = EXPR_KFLOAT;
        expr->kfloat = (double) expr->kint;
    } else if (is_int(target) && expr->kind == EXPR_KFLOAT) {
        expr->kind = EXPR_KINT;
        expr->kint = (uint64_t) expr->kfloat;
    }
    expr->type = target;
    return expr;
}

static Expr * conv_to(Expr *src, Type *target, int explicit_cast) {
    if (are_equal(src->type, target)) {
        return src; // No conversion necessary
    }
    check_conv(src, target, explicit_cast);
    if (src->kind == EXPR_KINT || src->kind == EXPR_KFLOAT) {
        return conv_const(src, target); // Don't emit CONV on constants
    }
    Expr *conv = new_expr(EXPR_CONV);
    conv->l = src;
    conv->type = target;
    conv->tk = src->tk;
    return conv;
}

static int is_arith_op(Tk o) {
    return o == '+' || o == '-' || o == '*' || o == '/' || o == '%';
}

static int is_bit_op(Tk o) {
    return o == '&' || o == '|' || o == '^' || o == TK_LSHIFT || o == TK_RSHIFT;
}

static int is_rel_op(Tk o) {
    return o == '<' || o == TK_LE || o == '>' || o == TK_GE;
}

static int is_eq_op(Tk o) {
    return o == TK_EQ || o == TK_NEQ;
}

// Returns the type that a binary integer operation's operands should be
// converted to (if necessary)
static Type * promote_binary_int(Type *lt, Type *rt) {
    // Implicit integer promotion rule as per 6.3.1.1 in C11 standard.
    // In practice (i.e., on my system where shorts are smaller than ints),
    // all "small" integer types (char, short) are converted to
    // SIGNED ints (regardless whether the original was unsigned)
    //
    // Implicit arithmetic conversions as per 6.3.18 in C11 standard:
    // 1. If same type -> no conversion
    // 2. If both signed or both unsigned -> convert to larger signed or
    //    unsigned type
    // 3. If unsigned type is larger than OR EQUAL TO the signed type ->
    //    convert signed operand to the unsigned type
    // 4. If signed type is larger than unsigned type -> convert unsigned
    //    operand to signed type
    // Note: these don't apply to prefix/postfix ++ and --
    //
    // See this Stack Overflow for a useful explanation:
    //   https://stackoverflow.com/questions/46073295/implicit-type-promotion-rules
    if (bits(lt) < 32 && bits(rt) < 32) {
        // 0. Implicit promotion to (signed) 'int' for "small" integer types
        return t_prim(T_i32, 1);
    } else if (bits(lt) == bits(rt) && lt->is_signed == rt->is_signed) {
        // 1. Types are equal
        return lt;
    } else if (lt->is_signed == rt->is_signed) {
        // 2. Both signed or unsigned -> convert to larger type
        return bits(lt) > bits(rt) ? lt : rt;
    } else {
        // 3. and 4. pick the larger type; if they're both the same size then
        // pick the unsigned type
        Type *st = lt->is_signed ? lt : rt, *ut = lt->is_signed ? rt : lt;
        return bits(ut) >= bits(st) ? ut : st;
    }
}

// Returns the type that a binary arithmetic operation's operands should be
// converted to (if necessary)
static Type * promote_binary_arith(Type *lt, Type *rt) {
    if (is_int(lt) && is_int(rt)) { // Both ints
        return promote_binary_int(lt, rt);
    } else if (is_fp(lt) && is_fp(rt)) { // Both floats
        return bits(lt) > bits(rt) ? lt : rt; // Pick larger
    } else { // One's a float and one's an int
        return is_fp(lt) ? lt : rt; // Pick float type
    }
}

// Returns the type that a unary integer operation's operands should be
// converted to (if necessary)
static Type * promote_unary_arith(Type *t) {
    if (is_int(t) && bits(t) < 32) {
        // Implicit promotion to (signed) 'int' for "small" integer types
        return t_prim(T_i32, 1);
    } else {
        return t; // No conversion necessary
    }
}

// Forward declarations
static Expr * parse_subexpr(Parser *p, Prec min_prec);
static Expr * parse_eq(Tk op, Expr *left, Expr *right);

static Expr * to_cond(Expr *expr) {
    Tk op = expr->op;
    if ((expr->kind == EXPR_UNARY && op == '!') ||
        (expr->kind == EXPR_BINARY && (is_rel_op(op) || is_eq_op(op) ||
                                       op == TK_OR || op == TK_AND))) {
        return expr; // Already a condition
    }
    // If 'expr' isn't a comparison or condition, then emit '!= 0'; if expr is
    // a pointer, then this constant is equivalent to a null pointer
    Expr *zero = new_expr(EXPR_KINT);
    zero->kint = 0;
    zero->type = expr->type;
    zero->tk = expr->tk;
    return parse_eq(TK_NEQ, expr, zero);
}

static Expr * parse_ternary(Parser *p, Expr *cond, Expr *l) {
    expect_tk(&p->l, ':');
    next_tk(&p->l);
    Prec prec = BINARY_PREC['?'] - IS_RIGHT_ASSOC['?'];
    Expr *r = parse_subexpr(p, prec);

    Type *result;
    if (is_arith(l->type) && is_arith(r->type)) {
        result = promote_binary_arith(l->type, r->type);
        l = conv_to(l, result, 0);
        r = conv_to(r, result, 0);
    } else if (is_ptr(l->type) && is_ptr(r->type) &&
               are_equal(l->type, r->type)) {
        result = l->type; // Doesn't matter which one we pick
    } else if (is_ptr(l->type) && (is_void_ptr(r->type) || is_null_ptr(r))) {
        result = l->type; // Pick the non-void pointer
        r = conv_to(r, result, 0); // Convert to the non-void pointer
    } else if ((is_void_ptr(l->type) || is_null_ptr(l)) && is_ptr(r->type)) {
        result = r->type; // Pick the non-void pointer
        l = conv_to(l, result, 0); // Convert to the non-void pointer
    } else {
        invalid_arguments(l, r);
    }
    Expr *ternary = new_expr(EXPR_TERNARY);
    ternary->cond = to_cond(cond);
    ternary->l = l;
    ternary->r = r;
    ternary->type = result;
    ternary->tk = merge_tks(cond->tk, r->tk);
    return ternary;
}

static Expr * parse_operation(Tk op, Expr *l, Expr *r, Type *result) {
    Expr *arith = new_expr(EXPR_BINARY);
    arith->op = op;
    arith->l = l;
    arith->r = r;
    arith->type = result;
    arith->tk = merge_tks(l->tk, r->tk);
    return arith;
}

static Expr * parse_arith(Tk op, Expr *l, Expr *r) {
    Type *result;
    if (is_arith(l->type) && is_arith(r->type)) {
        result = promote_binary_arith(l->type, r->type);
        l = conv_to(l, result, 0);
        r = conv_to(r, result, 0);
    } else if ((op == '+' || op == '-') && is_ptr(l->type) && is_int(r->type)) {
        result = l->type; // Result is a pointer
        r = conv_to(r, t_prim(T_i64, 0), 0);
    } else if (op == '+' && is_int(l->type) && is_ptr(r->type)) {
        result = r->type; // Result is a pointer
        l = conv_to(l, t_prim(T_i64, 0), 0);
    } else if (op == '-' && is_ptr(l->type) && is_ptr(r->type) &&
               are_equal(l->type, r->type)) {
        // Result is an INTEGER
        result = t_prim(T_i64, 0);
    } else {
        invalid_arguments(l, r);
    }
    return parse_operation(op, l, r, result);
}

static Expr * parse_bit(Tk op, Expr *l, Expr *r) {
    if (!(is_int(l->type) && is_int(r->type))) {
        invalid_arguments(l, r);
    }
    Type *result = promote_binary_int(l->type, r->type);
    l = conv_to(l, result, 0);
    r = conv_to(r, result, 0);
    return parse_operation(op, l, r, result);
}

static Expr * parse_assign(Expr *l, Expr *r) {
    ensure_lvalue(l);
    r = conv_to(r, l->type, 0); // Lower 'r' to 'l->type'
    Expr *assign = new_expr(EXPR_BINARY);
    assign->op = '=';
    assign->l = l;
    assign->r = r;
    assign->type = l->type;
    assign->tk = merge_tks(l->tk, r->tk);
    return assign;
}

static Expr * parse_arith_assign(Tk op, Expr *l, Expr *r) {
    ensure_lvalue(l);
    Type *lvalue_type = l->type;
    Tk arith_op = ASSIGNMENT_TO_ARITH_OP[op];
    Expr *assign = parse_arith(arith_op, l, r);
    assign->op = op;
    // Assignment always results in its right operand being converted to
    // 'l->type' (although this is handled in the compiler here, not by an
    // EXPR_CONV emitted by the parser)
    assign->type = lvalue_type;
    return assign;
}

static Expr * parse_eq(Tk op, Expr *l, Expr *r) {
    Type *result;
    if (is_arith(l->type) && is_arith(r->type)) {
        Type *promotion = promote_binary_arith(l->type, r->type);
        l = conv_to(l, promotion, 0);
        r = conv_to(r, promotion, 0);
        result = t_prim(T_i1, promotion->is_signed); // Preserve signed-ness
    } else if (is_ptr(l->type) && is_ptr(r->type) &&
               are_equal(l->type, r->type)) {
        result = t_prim(T_i1, 0); // Pointer comparisons always unsigned
    } else if (is_ptr(l->type) && (is_void_ptr(r->type) || is_null_ptr(r))) {
        Type *promotion = l->type; // Pick the non-void/non-null pointer
        r = conv_to(r, promotion, 0); // Convert to the non-void pointer
        result = t_prim(T_i1, 0); // Pointer comparisons always unsigned
    } else if ((is_void_ptr(l->type) || is_null_ptr(l)) && is_ptr(r->type)) {
        Type *promotion = r->type; // Pick the non-void/non-null pointer
        l = conv_to(l, promotion, 0); // Convert to the non-void pointer
        result = t_prim(T_i1, 0); // Pointer comparisons always unsigned
    } else {
        invalid_arguments(l, r);
    }
    return parse_operation(op, l, r, result);
}

static Expr * parse_rel(Tk op, Expr *l, Expr *r) {
    Type *result;
    if (is_arith(l->type) && is_arith(r->type)) {
        Type *promotion = promote_binary_arith(l->type, r->type);
        l = conv_to(l, promotion, 0);
        r = conv_to(r, promotion, 0);
        result = t_prim(T_i1, promotion->is_signed); // Preserve signed-ness
    } else if (is_ptr(l->type) && is_ptr(r->type) &&
               are_equal(l->type, r->type)) {
        result = t_prim(T_i1, 0); // Pointer comparisons always unsigned
    } else {
        invalid_arguments(l, r);
    }
    return parse_operation(op, l, r, result);
}

static Expr * parse_cond(Tk op, Expr *l, Expr *r) {
    l = to_cond(l);
    r = to_cond(r);
    Expr *cond = new_expr(EXPR_BINARY);
    cond->op = op;
    cond->l = l;
    cond->r = r;
    cond->type = t_prim(T_i1, 0);
    cond->tk = merge_tks(l->tk, r->tk);
    return cond;
}

static Expr * parse_comma(Expr *l, Expr *r) {
    Expr *comma = new_expr(EXPR_BINARY);
    comma->op = ',';
    comma->l = l;
    comma->r = r;
    comma->type = r->type; // Comma results in its r operand
    comma->tk = merge_tks(l->tk, r->tk);
    return comma;
}

static Expr * parse_binary(Parser *p, Tk op, Expr *left, Expr *right) {
    switch (op) {
    case '+': case '-': case '*': case '/':
        return parse_arith(op, left, right);
    case '%': // Only takes integer arguments
    case TK_LSHIFT: case TK_RSHIFT: case '&': case '|': case '^':
        return parse_bit(op, left, right);
    case TK_EQ: case TK_NEQ:
        return parse_eq(op, left, right);
    case '<': case TK_LE: case '>': case TK_GE:
        return parse_rel(op, left, right);
    case '=':
        return parse_assign(left, right);
    case TK_ADD_ASSIGN: case TK_SUB_ASSIGN:
    case TK_MUL_ASSIGN: case TK_DIV_ASSIGN: case TK_MOD_ASSIGN:
    case TK_AND_ASSIGN: case TK_OR_ASSIGN:  case TK_XOR_ASSIGN:
    case TK_LSHIFT_ASSIGN: case TK_RSHIFT_ASSIGN:
        return parse_arith_assign(op, left, right);
    case TK_AND: case TK_OR:
        return parse_cond(op, left, right);
    case '?': return parse_ternary(p, left, right);
    case ',': return parse_comma(left, right);
    default: UNREACHABLE();
    }
}

static Expr * parse_kint(Parser *p) {
    expect_tk(&p->l, TK_KINT);
    Expr *k = new_expr(EXPR_KINT);
    k->kint = p->l.kint;
    if (k->kint > INT64_MAX) {
        k->type = t_prim(T_i64, 0);
    } else if (k->kint > INT32_MAX) {
        k->type = t_prim(T_i64, 1);
    } else {
        k->type = t_prim(T_i32, 1);
    }
    k->tk = p->l.info;
    next_tk(&p->l);
    return k;
}

static Expr * parse_kfloat(Parser *p) {
    expect_tk(&p->l, TK_KFLOAT);
    Expr *k = new_expr(EXPR_KFLOAT);
    k->kfloat = p->l.kfloat;
    k->type = t_prim(T_f32, 1);
    k->tk = p->l.info;
    next_tk(&p->l);
    return k;
}

static Expr * parse_kchar(Parser *p) {
    expect_tk(&p->l, TK_KCHAR);
    Expr *k = new_expr(EXPR_KCHAR);
    k->kch = p->l.kch;
    k->type = t_prim(T_i8, 1);
    k->tk = p->l.info;
    next_tk(&p->l);
    return k;
}

static Expr * parse_kstr(Parser *p) {
    expect_tk(&p->l, TK_KSTR);
    Expr *k = new_expr(EXPR_KSTR);
    k->kstr = p->l.kstr;
    k->type = t_ptr(t_prim(T_i8, 1));
    k->tk = p->l.info;
    next_tk(&p->l);
    return k;
}

static Expr * parse_local(Parser *p) {
    expect_tk(&p->l, TK_IDENT);
    char *name = p->l.ident;
    int len = p->l.len;
    Local *local = find_local(p, name, len);
    if (!local) { // Check the local exists
        trigger_error_at(p->l.info, "undeclared identifier '%.*s'", len, name);
    }
    Expr *expr = new_expr(EXPR_LOCAL);
    expr->local = local;
    expr->type = local->type;
    expr->tk = p->l.info;
    next_tk(&p->l);
    return expr;
}

static int has_decl(Parser *p); // Forward declarations
static Type * parse_type_specs(Parser *p);
static Declarator parse_declarator(Parser *p, Type *base, int is_abstract);
static Expr * parse_unary(Parser *p);

static Expr * parse_sizeof(Parser *p) {
    expect_tk(&p->l, TK_SIZEOF);
    TkInfo start = p->l.info;
    next_tk(&p->l);
    Type *result;
    TkInfo tk, end;
    if (p->l.tk == '(') {
        next_tk(&p->l);
        if (!has_decl(p)) {
            trigger_error_at(p->l.info, "expected type name");
        }
        tk = p->l.info;
        Type *base_type = parse_type_specs(p);
        Declarator decl = parse_declarator(p, base_type, 1);
        result = decl.type;
        tk = merge_tks(tk, decl.tk);
        expect_tk(&p->l, ')');
        end = p->l.info;
        next_tk(&p->l);
    } else {
        Expr *operand = parse_unary(p);
        result = operand->type; // Discard the operand itself; not evaluated
        tk = operand->tk;
        end = tk;
    }
    if (is_incomplete(result)) {
        trigger_error_at(tk, "cannot calculate size of incomplete type '%s'",
                         type_to_str(result));
    }
    // The operand to a 'sizeof' operator isn't evaluated (unless it's a VLA);
    // 'sizeof' just evaluates to a constant integer
    Expr *size = new_expr(EXPR_KINT);
    size->kint = bytes(result);
    size->type = t_prim(T_i64, 0); // Always 64 bits on a 64-bit system
    size->tk = merge_tks(start, end);
    return size;
}

static Expr * parse_operand(Parser *p) {
    switch (p->l.tk) {
        case TK_KINT:   return parse_kint(p);
        case TK_KFLOAT: return parse_kfloat(p);
        case TK_KCHAR:  return parse_kchar(p);
        case TK_KSTR:   return parse_kstr(p);
        case TK_IDENT:  return parse_local(p);
        case TK_SIZEOF: return parse_sizeof(p);
        default:        trigger_error_at(p->l.info, "expected expression");
    }
}

static Expr * parse_postfix_inc_dec(Tk op, Expr *operand) {
    // Note we can't just expand postfix a++ or a-- to a = a + 1, since the
    // result of this assignment would be the ADDITION, not the value of 'a'
    // BEFORE the addition -- we have to pass on the postfix to the compiler.
    // Standard integer promotions DON'T APPLY to ++ and --
    ensure_lvalue(operand);
    Expr *postfix = new_expr(EXPR_POSTFIX);
    postfix->op = op;
    postfix->l = operand;
    postfix->type = operand->type;
    return postfix;
}

static Expr * parse_array_access(Parser *p, Expr *array) {
    TkInfo start = p->l.info;
    expect_tk(&p->l, '[');
    next_tk(&p->l);
    Expr *index = parse_subexpr(p, PREC_NONE);
    expect_tk(&p->l, ']');
    index->tk = merge_tks(start, p->l.info);
    next_tk(&p->l);

    ensure_can_deref(array);
    if (!is_int(index->type)) {
        trigger_error_at(index->tk, "invalid argument '%s' to array access",
                         type_to_str(index->type));
    }
    index = conv_to(index, t_prim(T_i64, 0), 0); // Have to add an i64
    Expr *array_access = new_expr(EXPR_BINARY);
    array_access->op = '[';
    array_access->l = array;
    array_access->r = index;
    array_access->type = array->type->ptr;
    array_access->tk = merge_tks(array->tk, index->tk);
    return array_access;
}

static Expr * parse_postfix(Parser *p, Expr *operand) {
    Tk op = p->l.tk;
    if (!POSTFIX_PREC[op]) { // No postfix operation
        return operand;
    }
    Expr *postfix;
    switch (op) {
    case TK_INC: case TK_DEC:
        postfix = parse_postfix_inc_dec(op, operand);
        postfix->tk = merge_tks(operand->tk, p->l.info);
        next_tk(&p->l); // Skip the operator
        break;
    case '[':
        postfix = parse_array_access(p, operand);
        break;
    default: UNREACHABLE();
    }
    return postfix;
}

static Expr * parse_not(Expr *operand) {
    operand = to_cond(operand);
    Expr *unary = new_expr(EXPR_UNARY);
    unary->op = '!';
    unary->l = operand; // No conv needed -> guaranteed to be a condition
    unary->type = t_prim(T_i1, 0);
    return unary;
}

static Expr * parse_addr(Expr *operand) {
    ensure_can_take_addr(operand);
    Expr *addr = new_expr(EXPR_UNARY);
    addr->op = '&';
    addr->l = operand;
    addr->type = t_ptr(operand->type);
    return addr;
}

static Expr * parse_deref(Expr *operand) {
    ensure_can_deref(operand);
    Expr *deref = new_expr(EXPR_UNARY);
    deref->op = '*';
    deref->l = operand;
    deref->type = operand->type->ptr;
    return deref;
}

static Expr * parse_prefix_inc_dec(Tk op, Expr *operand) {
    // Standard integer promotions DON'T APPLY to ++ and --
    ensure_lvalue(operand);
    Expr *prefix = new_expr(EXPR_UNARY);
    prefix->op = op;
    prefix->l = operand;
    prefix->type = operand->type;
    return prefix;
}

static Expr * parse_unary_arith(Tk op, Expr *operand) {
    if (!((is_arith_op(op) && is_arith(operand->type)) ||
          (is_bit_op(op) && is_int(operand->type)))) {
        trigger_error_at(operand->tk, "invalid argument '%s' to operation",
                         type_to_str(operand->type));
    }
    Type *result = promote_unary_arith(operand->type);
    operand = conv_to(operand, result, 0);
    Expr *unary = new_expr(EXPR_UNARY);
    unary->op = op;
    unary->l = operand;
    unary->type = result;
    return unary;
}

static Expr * parse_cast(Parser *p, TkInfo start_tk) {
    Type *base_type = parse_type_specs(p);
    Declarator declarator = parse_declarator(p, base_type, 1);
    expect_tk(&p->l, ')');
    next_tk(&p->l);
    Expr *operand = parse_subexpr(p, UNARY_PREC['(']);
    Expr *conv = conv_to(operand, declarator.type, 1);
    conv->tk = merge_tks(start_tk, operand->tk);
    return conv;
}

static Expr * parse_braced_subexpr(Parser *p) {
    Expr *expr = parse_subexpr(p, PREC_NONE);
    expect_tk(&p->l, ')');
    next_tk(&p->l);
    return expr;
}

static Expr * parse_unary(Parser *p) {
    Tk op = p->l.tk;
    TkInfo op_tk = p->l.info;
    if (!UNARY_PREC[op]) { // If there's no unary operator
        Expr *operand = parse_operand(p); // Parse an operand
        return parse_postfix(p, operand); // And optional postfix operator
    }
    next_tk(&p->l); // Skip the unary operator
    if (op == '(') {
        if (has_decl(p)) { // Cast
            return parse_cast(p, op_tk);
        } else { // Expression in parentheses
            return parse_braced_subexpr(p);
        }
    }
    Expr *operand = parse_subexpr(p, UNARY_PREC[op]);
    Expr *unary;
    switch (op) {
    case '+': case '-': case '~':
        unary = parse_unary_arith(op, operand); break;
    case TK_INC: case TK_DEC:
        unary = parse_prefix_inc_dec(op, operand); break;
    case '!': unary = parse_not(operand); break;
    case '&': unary = parse_addr(operand); break;
    case '*': unary = parse_deref(operand); break;
    default: UNREACHABLE();
    }
    unary->tk = merge_tks(op_tk, operand->tk);
    return unary;
}

static Expr * parse_subexpr(Parser *p, Prec min_prec) {
    Expr *left = parse_unary(p);
    while (BINARY_PREC[p->l.tk] > min_prec) {
        Tk op = p->l.tk;
        next_tk(&p->l); // Skip the binary operator
        Prec prec = BINARY_PREC[op] + IS_RIGHT_ASSOC[op];
        Expr *right = parse_subexpr(p, prec); // Parse right operand
        left = parse_binary(p, op, left, right);
    }
    return left;
}

static Expr * parse_expr(Parser *p) {
    return parse_subexpr(p, PREC_NONE);
}

static uint64_t parse_const_expr(Parser *p) {
    // TODO: constant expressions only consist of an integer so far
    if (p->l.tk == TK_KINT) {
        uint64_t result = p->l.kint;
        next_tk(&p->l);
        return result;
    } else {
        trigger_error_at(p->l.info, "expected constant expression");
    }
}


// ---- Statements ------------------------------------------------------------

#define NUM_TYPE_COMBINATIONS 30
#define COMBINATION_SIZE (NUM_TKS - FIRST_KEYWORD)
#define T(tk) ((TK_ ## tk) - FIRST_KEYWORD)

// All valid type specifiers
static int TYPE_SPECS[NUM_TKS] = {
    [TK_VOID] = 1,
    [TK_CHAR] = 1,
    [TK_SHORT] = 1,
    [TK_INT] = 1,
    [TK_LONG] = 1,
    [TK_SIGNED] = 1,
    [TK_UNSIGNED] = 1,
    [TK_FLOAT] = 1,
    [TK_DOUBLE] = 1,
};

// All valid combinations of type specifiers. Must occur in the same order as
// TYPE_COMBINATION_TO_PRIM below
static int TYPE_COMBINATIONS[NUM_TYPE_COMBINATIONS][COMBINATION_SIZE] = {
    { [T(VOID)] = 1, },                                   // void
    { [T(CHAR)] = 1, },                                   // char
    { [T(CHAR)] = 1, [T(SIGNED)] = 1, },                  // signed char
    { [T(CHAR)] = 1, [T(UNSIGNED)] = 1, },                // unsigned char
    { [T(SHORT)] = 1, },                                  // short
    { [T(SHORT)] = 1, [T(SIGNED)] = 1, },                 // signed short
    { [T(SHORT)] = 1, [T(UNSIGNED)] = 1, },               // unsigned short
    { [T(SHORT)] = 1, [T(INT)] = 1 },                     // short int
    { [T(SHORT)] = 1, [T(SIGNED)] = 1, [T(INT)] = 1, },   // signed short int
    { [T(SHORT)] = 1, [T(UNSIGNED)] = 1, [T(INT)] = 1, }, // unsigned short int
    { [T(INT)] = 1, },                                    // int
    { [T(SIGNED)] = 1, },                                 // signed
    { [T(UNSIGNED)] = 1, },                               // unsigned
    { [T(INT)] = 1, [T(SIGNED)] = 1, },                   // signed int
    { [T(INT)] = 1, [T(UNSIGNED)] = 1, },                 // unsigned int
    { [T(LONG)] = 1, },                                   // long
    { [T(LONG)] = 1, [T(SIGNED)] = 1, },                  // signed long
    { [T(LONG)] = 1, [T(UNSIGNED)] = 1, },                // unsigned long
    { [T(LONG)] = 1, [T(INT)] = 1, },                     // long int
    { [T(LONG)] = 1, [T(SIGNED)] = 1, [T(INT)] = 1, },    // signed long int
    { [T(LONG)] = 1, [T(UNSIGNED)] = 1, [T(INT)] = 1, },  // unsigned long int
    { [T(LONG)] = 2, },                                   // long long
    { [T(LONG)] = 2, [T(SIGNED)] = 1, },                  // signed long long
    { [T(LONG)] = 2, [T(UNSIGNED)] = 1, },                // unsigned long long
    { [T(LONG)] = 2, [T(INT)] = 1, },                     // long long int
    { [T(LONG)] = 2, [T(SIGNED)] = 1, [T(INT)] = 1, },    // signed long long int
    { [T(LONG)] = 2, [T(UNSIGNED)] = 1, [T(INT)] = 1, },  // unsigned long long int
    { [T(FLOAT)] = 1, },                                  // float
    { [T(DOUBLE)] = 1, },                                 // double
    { [T(DOUBLE)] = 1, [T(LONG)] = 1, },                  // long double
};

// Each index in the above TYPE_COMBINATIONS corresponds to the following
// internal primitive representation
// Note this is specific to my target architecture (i.e., my computer!)
static Prim TYPE_COMBINATION_TO_PRIM[NUM_TYPE_COMBINATIONS] = {
    T_void, // void
    T_i8,   // char
    T_i8,   // signed char
    T_i8,   // unsigned char
    T_i16,  // short
    T_i16,  // signed short
    T_i16,  // unsigned short
    T_i16,  // short int
    T_i16,  // signed short int
    T_i16,  // unsigned short int
    T_i32,  // int
    T_i32,  // signed
    T_i32,  // unsigned
    T_i32,  // signed int
    T_i32,  // unsigned int
    T_i32,  // long
    T_i32,  // signed long
    T_i32,  // unsigned long
    T_i32,  // long int
    T_i32,  // signed long int
    T_i32,  // unsigned long int
    T_i64,  // long long
    T_i64,  // signed long long
    T_i64,  // unsigned long long
    T_i64,  // long long int
    T_i64,  // signed long long int
    T_i64,  // unsigned long long int
    T_f32,  // float
    T_f64,  // double
    T_f64,  // long double
};

static int has_decl(Parser *p) {
    return TYPE_SPECS[p->l.tk];
}

static Type * parse_type_specs(Parser *p) {
    // Check there's at least one type specifier
    TkInfo start = p->l.info;
    if (!has_decl(p)) {
        trigger_error_at(start, "expected declaration");
    }
    // Keep parsing type specifiers into a hash-map until there's no more
    int type_specs[COMBINATION_SIZE];
    memset(type_specs, 0, sizeof(int) * (NUM_TKS - FIRST_KEYWORD));
    TkInfo end = start;
    while (has_decl(p)) {
        type_specs[p->l.tk - FIRST_KEYWORD]++;
        end = p->l.info;
        next_tk(&p->l);
    }
    // Find the corresponding combination in TYPE_COMBINATIONS
    int combination = -1;
    for (int i = 0; i < NUM_TYPE_COMBINATIONS; i++) {
        if (memcmp(type_specs, TYPE_COMBINATIONS[i],
                   COMBINATION_SIZE * sizeof(int)) == 0) {
            combination = i;
            break;
        }
    }
    if (combination == -1) {
        TkInfo tk = merge_tks(start, end);
        trigger_error_at(tk, "invalid combination of type specifiers");
    }
    int is_signed = !type_specs[TK_UNSIGNED - FIRST_KEYWORD];
    return t_prim(TYPE_COMBINATION_TO_PRIM[combination], is_signed);
}

// Forward declaration
static void parse_declarator_internal(Parser *p, Declarator *decl);

static void parse_direct_declarator(Parser *p, Declarator *decl) {
    switch (p->l.tk) {
    case TK_IDENT:
        decl->name = p->l.info;
        decl->tk = merge_tks(decl->tk, p->l.info);
        next_tk(&p->l);
        break;
    case '(':
        next_tk(&p->l);
        parse_declarator_internal(p, decl);
        expect_tk(&p->l, ')');
        decl->tk = merge_tks(decl->tk, p->l.info);
        next_tk(&p->l);
        break;
    default: break;
    }
    while (p->l.tk == '[') { // Arrays
        next_tk(&p->l);
        uint64_t size = parse_const_expr(p);
        expect_tk(&p->l, ']');
        decl->tk = merge_tks(decl->tk, p->l.info);
        next_tk(&p->l);
        decl->type = t_arr(decl->type, size);
    }
}

static void parse_declarator_internal(Parser *p, Declarator *decl) {
    int num_ptrs = 0;
    while (p->l.tk == '*') {
        num_ptrs++;
        decl->tk = merge_tks(decl->tk, p->l.info);
        next_tk(&p->l);
    }
    parse_direct_declarator(p, decl);
    for (int i = 0; i < num_ptrs; i++) { // Pointers come at the end
        decl->type = t_ptr(decl->type);
    }
}

static Declarator parse_declarator(Parser *p, Type *base, int is_abstract) {
    Declarator d;
    d.type = base;
    d.name.start = NULL;
    d.tk = p->l.info; // Start token
    parse_declarator_internal(p, &d);
    if (is_abstract && d.name.start) {
        trigger_error_at(d.name, "variable name not permitted here");
    } else if (!is_abstract && !d.name.start) {
        trigger_error_at(d.tk, "expected variable name");
    }
    return d;
}

static Stmt * parse_declaration(Parser *p, Type *base_type, int allowed_defn) {
    Declarator declarator = parse_declarator(p, base_type, 0);
    Expr *value = NULL;
    if (allowed_defn && p->l.tk == '=') { // Optional assignment
        next_tk(&p->l); // Skip the '=' token
        value = parse_subexpr(p, PREC_COMMA); // Can't have commas
    }

    Stmt *result = new_stmt(STMT_DECL);
    result->local = def_local(p, declarator.name, declarator.type);
    if (value) {
        Expr *local_expr = new_expr(EXPR_LOCAL);
        local_expr->local = result->local;
        local_expr->type = result->local->type;
        local_expr->tk = declarator.tk;
        Stmt *assign = new_stmt(STMT_EXPR);
        assign->expr = parse_assign(local_expr, value);
        result->next = assign;
    }
    return result;
}

static Stmt * parse_declaration_list(Parser *p) {
    Type *base_type = parse_type_specs(p); // Base type specifiers
    Stmt *head;
    Stmt **decl = &head;
    while (p->l.tk != ';') {
        *decl = parse_declaration(p, base_type, 1);
        while (*decl) { // Find the end of the chain
            decl = &(*decl)->next;
        }
        if (p->l.tk == ',') {
            next_tk(&p->l); // Parse another declaration
        } else {
            break; // Stop parsing declarations
        }
    }
    expect_tk(&p->l, ';');
    next_tk(&p->l);
    return head;
}

static Stmt * parse_stmt(Parser *p); // Forward declaration

static Stmt * parse_expr_stmt(Parser *p) {
    Stmt *stmt = new_stmt(STMT_EXPR);
    stmt->expr = parse_expr(p);
    expect_tk(&p->l, ';');
    next_tk(&p->l);
    return stmt;
}

static Stmt * parse_if(Parser *p) {
    expect_tk(&p->l, TK_IF);
    Stmt *stmt = new_stmt(STMT_IF);
    IfChain **if_chain = &stmt->if_chain;
    int has_else = 0;
    while (p->l.tk == TK_IF) {
        next_tk(&p->l);
        expect_tk(&p->l, '(');
        next_tk(&p->l);
        Expr *cond = parse_expr(p); // Condition
        cond = to_cond(cond);
        expect_tk(&p->l, ')');
        next_tk(&p->l);
        Stmt *body = parse_stmt(p); // Body
        IfChain *this_if = malloc(sizeof(IfChain));
        this_if->next = NULL;
        this_if->cond = cond;
        this_if->body = body;
        *if_chain = this_if;
        if_chain = &(*if_chain)->next;
        has_else = 0;
        if (p->l.tk == TK_ELSE) {
            has_else = 1;
            next_tk(&p->l);
        } else {
            break;
        }
    }
    if (has_else) {
        IfChain *this_else = malloc(sizeof(IfChain));
        this_else->next = NULL;
        this_else->cond = NULL;
        this_else->body = parse_stmt(p);
        *if_chain = this_else;
    }
    return stmt;
}

static Stmt * parse_while(Parser *p) {
    Stmt *stmt = new_stmt(STMT_WHILE);
    expect_tk(&p->l, TK_WHILE);
    next_tk(&p->l);
    expect_tk(&p->l, '(');
    next_tk(&p->l);
    Expr *cond = parse_expr(p); // Condition
    stmt->cond = to_cond(cond);
    expect_tk(&p->l, ')');
    next_tk(&p->l);
    stmt->body = parse_stmt(p); // Body
    return stmt;
}

static Stmt * parse_for(Parser *p) {
    Stmt *head = NULL;
    Stmt **stmt = &head;
    expect_tk(&p->l, TK_FOR);
    next_tk(&p->l);
    expect_tk(&p->l, '(');
    next_tk(&p->l);
    Local *scope = p->locals;

    if (has_decl(p)) { // Initializer
        *stmt = parse_declaration_list(p); // Declaration initializer
    } else if (p->l.tk != ';') {
        *stmt = parse_expr_stmt(p); // Expression initializer
    } else {
        next_tk(&p->l); // No initializer, skip ';'
    }
    while (*stmt) { // Find the end of the initializer
        stmt = &(*stmt)->next;
    }

    Expr *cond = NULL; // Condition
    if (p->l.tk != ';') {
        cond = parse_expr(p);
        cond = to_cond(cond);
    }
    expect_tk(&p->l, ';');
    next_tk(&p->l);

    Expr *inc = NULL;
    if (p->l.tk != ')') {
        inc = parse_expr(p); // Increment
    }
    expect_tk(&p->l, ')');
    next_tk(&p->l);

    Stmt *body = parse_stmt(p); // Body
    p->locals = scope; // Remove the declarations in the loop header

    // We can't just compile for loops to while loops, since the increment
    // still needs to be executed when we 'continue' -> compiler needs to
    // generate a separate increment BB at the end of the body which all
    // 'continue's jump to
    Stmt *loop = new_stmt(STMT_FOR);
    loop->cond = cond;
    loop->inc = inc;
    loop->body = body;
    *stmt = loop;
    return head;
}

static Stmt * parse_do_while(Parser *p) {
    Stmt *stmt = new_stmt(STMT_DO_WHILE);
    expect_tk(&p->l, TK_DO);
    next_tk(&p->l);
    stmt->body = parse_stmt(p); // Body
    expect_tk(&p->l, TK_WHILE);
    next_tk(&p->l);
    expect_tk(&p->l, '(');
    next_tk(&p->l);
    Expr *cond = parse_expr(p); // Condition
    stmt->cond = to_cond(cond);
    expect_tk(&p->l, ')');
    next_tk(&p->l);
    expect_tk(&p->l, ';');
    next_tk(&p->l);
    return stmt;
}

static Stmt * parse_break(Parser *p) {
    expect_tk(&p->l, TK_BREAK);
    next_tk(&p->l);
    expect_tk(&p->l, ';');
    next_tk(&p->l);
    Stmt *stmt = new_stmt(STMT_BREAK);
    return stmt;
}

static Stmt * parse_continue(Parser *p) {
    expect_tk(&p->l, TK_CONTINUE);
    next_tk(&p->l);
    expect_tk(&p->l, ';');
    next_tk(&p->l);
    Stmt *stmt = new_stmt(STMT_CONTINUE);
    return stmt;
}

static Stmt * parse_ret(Parser *p) {
    expect_tk(&p->l, TK_RETURN);
    next_tk(&p->l);
    Stmt *ret = new_stmt(STMT_RET);
    if (p->l.tk != ';') {
        Expr *value = parse_expr(p);
        value = conv_to(value, p->fn->decl->return_type, 0);
        ret->expr = value;
    }
    expect_tk(&p->l, ';');
    next_tk(&p->l);
    return ret;
}

static Stmt * parse_block(Parser *p) {
    expect_tk(&p->l, '{');
    next_tk(&p->l);
    Stmt *block = NULL;
    Stmt **stmt = &block;
    Local *scope = p->locals; // New locals scope
    while (p->l.tk && p->l.tk != '}') {
        if (has_decl(p)) { // Declarations can only occur in BLOCKS
            *stmt = parse_declaration_list(p);
        } else {
            *stmt = parse_stmt(p);
        }
        while (*stmt) { // Find the last statement in the chain
            stmt = &(*stmt)->next;
        }
    }
    p->locals = scope;
    expect_tk(&p->l, '}');
    next_tk(&p->l);
    return block;
}

static Stmt * parse_stmt(Parser *p) {
    switch (p->l.tk) {
        case ';':         next_tk(&p->l); return NULL; // Empty
        case '{':         return parse_block(p);       // Block
        case TK_IF:       return parse_if(p);          // If/else if/else
        case TK_WHILE:    return parse_while(p);       // While loop
        case TK_FOR:      return parse_for(p);         // For loop
        case TK_DO:       return parse_do_while(p);    // Do-while loop
        case TK_BREAK:    return parse_break(p);       // Break
        case TK_CONTINUE: return parse_continue(p);    // Continue
        case TK_RETURN:   return parse_ret(p);         // Return
        default:          return parse_expr_stmt(p);   // Expression
    }
}


// ---- Module ----------------------------------------------------------------

static FnArg * parse_fn_decl_arg(Parser *p) {
    Type *base_type = parse_type_specs(p); // Type
    FnArg *arg = malloc(sizeof(FnArg));
    arg->next = NULL;
    Stmt *decl = parse_declaration(p, base_type, 0);
    arg->local = decl->local;
    assert(!decl->next); // Sanity check -> only one statement from 'parse_declaration'
    return arg;
}

static FnArg * parse_fn_decl_args(Parser *p) {
    expect_tk(&p->l, '('); // Arguments
    next_tk(&p->l);
    FnArg *head = NULL;
    FnArg **arg = &head;
    while (p->l.tk && p->l.tk != ')') {
        *arg = parse_fn_decl_arg(p); // Parse an argument
        arg = &(*arg)->next;
        if (p->l.tk == ',') { // Check for another argument
            next_tk(&p->l);
            continue;
        } else {
            break;
        }
    }
    expect_tk(&p->l, ')');
    next_tk(&p->l);
    return head;
}

static FnDef * parse_fn_def(Parser *p) {
    FnDef *def = malloc(sizeof(FnDef));
    def->next = NULL;
    p->fn = def;

    def->decl = malloc(sizeof(FnDecl));
    def->decl->return_type = parse_type_specs(p); // Return type

    expect_tk(&p->l, TK_IDENT); // Name
    def->decl->local = def_local(p, p->l.info, NULL);
    next_tk(&p->l);

    // 'parse_fn_decl_args' creates new locals for the function arguments;
    // create a new scope so that they get deleted
    Local *scope = p->locals;
    def->decl->args = parse_fn_decl_args(p); // Arguments
    def->body = parse_block(p); // Body
    p->locals = scope;
    return def;
}

static AstModule * parse_module(Parser *p) {
    AstModule *module = malloc(sizeof(AstModule));
    module->fns = NULL;
    FnDef **def = &module->fns;
    while (p->l.tk) { // Until we reach the end of the file
        *def = parse_fn_def(p);
        def = &(*def)->next;
    }
    return module;
}

AstModule * parse(char *file) {
    Parser p;
    p.l = new_lexer(file);
    next_tk(&p.l);
    p.locals = NULL;
    AstModule *module = parse_module(&p);
    return module;
}
