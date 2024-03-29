
#include <string.h>
#include <assert.h>

#include "Parser.h"
#include "Error.h"

typedef struct {
    Token *tk; // Current token we're parsing
    FnDef *fn; // Current function we're parsing into
    // Linked list of locals in the current scope; head of the list is the
    // most RECENTLY defined local (not the first one)
    Local *locals;
} Parser;

static void next_tk(Parser *p) {
    if (p->tk->t != '\0') {
        p->tk = p->tk->next;
    }
}

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

static Local * find_local(Parser *p, Token *name) {
    if (!name) {
        return NULL;
    }
    for (Local *l = p->locals; l; l = l->next) {
        if (l->decl.name && l->decl.name->len == name->len &&
                strncmp(l->decl.name->start, name->start, name->len) == 0) {
            return l;
        }
    }
    return NULL;
}

static Local * def_local(Parser *p, Declarator decl) {
    Local *existing = find_local(p, decl.name);
    if (existing) {
        print_error_at(decl.tk, "redefinition of '%.*s'", decl.name->len,
                       decl.name->start);
        print_info_at(existing->decl.tk, "initial definition here");
        trigger_error();
    }
    Local *local = malloc(sizeof(Local));
    local->decl = decl;
    local->alloc = NULL;
    local->next = p->locals; // Prepend to the linked list
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
    [TK_INC] = PREC_UNARY, // Increment
    [TK_DEC] = PREC_UNARY, // Decrement
    [TK_SIZEOF] = PREC_UNARY, // 'sizeof'
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
        print_error_at(lvalue->tk, "expression is not assignable");
        trigger_error();
    }
    if (is_arr(lvalue->type)) {
        print_error_at(lvalue->tk, "array type '%s' is not assignable",
                       type_to_str(lvalue->type));
        trigger_error();
    }
    if (is_incomplete(lvalue->type)) {
        print_error_at(lvalue->tk, "incomplete type '%s' is not assignable",
                       type_to_str(lvalue->type));
        trigger_error();
    }
}

static void ensure_can_take_addr(Expr *operand) {
    // See 6.5.3.2 in C99 standard for what's allowed (local, dereference,
    // and array access)
    if (!(operand->kind == EXPR_LOCAL ||
          (operand->kind == EXPR_UNARY && operand->op == '*') ||
          (operand->kind == EXPR_BINARY && operand->op == '['))) {
        print_error_at(operand->tk, "cannot take address of operand");
        trigger_error();
    }
}

static void ensure_can_deref(Expr *operand) {
    // Can only dereference a pointer or an array
    if (operand->type->kind != T_PTR && operand->type->kind != T_ARR) {
        print_error_at(operand->tk, "cannot dereference operand of type '%s'",
                       type_to_str(operand->type));
        trigger_error();
    }
}

static void check_conv(Expr *src, Type *t, int explicit_cast) {
    Type *s = src->type;
    if (!((is_arith(t) && is_arith(s)) ||
          (is_ptr(t) && is_ptr(s)) ||
          (is_ptr(t) && is_int(s)) || (is_int(t) && is_ptr(s)) ||
          (is_ptr(t) && is_arr(s)))) {
        print_error_at(src->tk, "invalid conversion from '%s' to '%s'",
                       type_to_str(s), type_to_str(t));
        trigger_error();
    }
    if (!explicit_cast && is_int(t) && is_int(s) && bits(t) < bits(s)) {
        print_warning_at(src->tk, "implicit conversion from '%s' to '%s' "
                                  "loses precision",
                         type_to_str(s), type_to_str(t));
    }
    if (!explicit_cast && is_ptr(t) && is_ptr(s) && !are_equal(t, s) &&
            !(is_void_ptr(s) || is_void_ptr(t) || is_null_ptr(src))) {
        print_warning_at(src->tk, "implicit conversion between incompatible "
                                  "pointer types '%s' and '%s'",
                         type_to_str(s), type_to_str(t));
    }
    if (!explicit_cast && is_ptr(t) && is_arr(s) &&
            !are_equal(t->ptr, s->ptr) && !is_void_ptr(t)) {
        print_warning_at(src->tk, "implicit conversion between incompatible "
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
    return o == '&' || o == '|' || o == '^' || o == TK_LSHIFT ||
           o == TK_RSHIFT || o == '~';
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
        return t_copy(lt);
    } else if (lt->is_signed == rt->is_signed) {
        // 2. Both signed or unsigned -> convert to larger type
        return bits(lt) > bits(rt) ? t_copy(lt) : t_copy(rt);
    } else {
        // 3. and 4. pick the larger type; if they're both the same size then
        // pick the unsigned type
        Type *st = lt->is_signed ? lt : rt, *ut = lt->is_signed ? rt : lt;
        return bits(ut) >= bits(st) ? t_copy(ut) : t_copy(st);
    }
}

// Returns the type that a binary arithmetic operation's operands should be
// converted to (if necessary)
static Type * promote_binary_arith(Type *lt, Type *rt) {
    if (is_int(lt) && is_int(rt)) { // Both ints
        return promote_binary_int(lt, rt);
    } else if (is_fp(lt) && is_fp(rt)) { // Both floats
        return bits(lt) > bits(rt) ? t_copy(lt) : t_copy(rt); // Pick larger
    } else { // One's a float and one's an int
        return is_fp(lt) ? t_copy(lt) : t_copy(rt); // Pick float type
    }
}

// Returns the type that a unary integer operation's operands should be
// converted to (if necessary)
static Type * promote_unary_arith(Type *t) {
    if (is_int(t) && bits(t) < 32) {
        // Implicit promotion to (signed) 'int' for "small" integer types
        return t_prim(T_i32, 1);
    } else {
        return t_copy(t); // No conversion necessary
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
    zero->type = t_copy(expr->type);
    zero->tk = expr->tk;
    return parse_eq(TK_NEQ, expr, zero);
}

static Expr * parse_ternary(Parser *p, Expr *cond, Expr *l) {
    expect_tk(p->tk, ':');
    next_tk(p);
    Prec prec = BINARY_PREC['?'] - IS_RIGHT_ASSOC['?'];
    Expr *r = parse_subexpr(p, prec);

    Type *result;
    if (is_arith(l->type) && is_arith(r->type)) {
        result = promote_binary_arith(l->type, r->type);
        l = conv_to(l, result, 0);
        r = conv_to(r, result, 0);
    } else if (is_ptr_arr(l->type) && is_ptr_arr(r->type) &&
               are_equal(l->type, r->type)) {
        result = to_ptr(l->type); // Doesn't matter which one we pick
    } else if (is_ptr_arr(l->type) &&
               (is_void_ptr(r->type) || is_null_ptr(r))) {
        result = to_ptr(l->type); // Pick the non-void pointer
        r = conv_to(r, result, 0); // Convert to the non-void pointer
    } else if ((is_void_ptr(l->type) || is_null_ptr(l)) &&
               is_ptr_arr(r->type)) {
        result = to_ptr(r->type); // Pick the non-void pointer
        l = conv_to(l, result, 0); // Convert to the non-void pointer
    } else {
        print_error_at(merge_tks(l->tk, r->tk),
                       "invalid arguments '%s' and '%s' to ternary operation",
                       type_to_str(l->type), type_to_str(r->type));
        trigger_error();
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
    } else if ((op == '+' || op == '-') && is_ptr_arr(l->type) &&
               is_int(r->type)) {
        result = to_ptr(l->type); // Result is a pointer
        r = conv_to(r, t_prim(T_i64, 0), 0);
    } else if (op == '+' && is_int(l->type) && is_ptr_arr(r->type)) {
        result = to_ptr(r->type); // Result is a pointer
        l = conv_to(l, t_prim(T_i64, 0), 0);
    } else if (op == '-' && is_ptr_arr(l->type) && is_ptr_arr(r->type) &&
               are_equal(l->type, r->type)) {
        // Result is an INTEGER
        result = t_prim(T_i64, 0);
    } else {
        print_error_at(merge_tks(l->tk, r->tk),
                       "invalid arguments '%s' and '%s' to arithmetic "
                       "operation",
                       type_to_str(l->type), type_to_str(r->type));
        trigger_error();
    }
    return parse_operation(op, l, r, result);
}

static Expr * parse_bit(Tk op, Expr *l, Expr *r) {
    if (!(is_int(l->type) && is_int(r->type))) {
        print_error_at(merge_tks(l->tk, r->tk),
                       "invalid arguments '%s' and '%s' to bitwise operation",
                       type_to_str(l->type), type_to_str(r->type));
        trigger_error();
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
    assign->type = t_copy(l->type);
    assign->tk = merge_tks(l->tk, r->tk);
    return assign;
}

static Expr * parse_arith_assign(Tk op, Expr *l, Expr *r) {
    ensure_lvalue(l);
    Type *lvalue_type = t_copy(l->type);
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
    } else if (is_ptr_arr(l->type) && is_ptr_arr(r->type) &&
               are_equal(l->type, r->type)) {
        result = t_prim(T_i1, 0); // Pointer comparisons always unsigned
    } else if (is_ptr_arr(l->type) &&
               (is_void_ptr(r->type) || is_null_ptr(r))) {
        Type *promotion = to_ptr(l->type); // Pick the non-void/non-null pointer
        r = conv_to(r, promotion, 0); // Convert to the non-void pointer
        result = t_prim(T_i1, 0); // Pointer comparisons always unsigned
    } else if ((is_void_ptr(l->type) || is_null_ptr(l)) &&
               is_ptr_arr(r->type)) {
        Type *promotion = to_ptr(r->type); // Pick the non-void/non-null pointer
        l = conv_to(l, promotion, 0); // Convert to the non-void pointer
        result = t_prim(T_i1, 0); // Pointer comparisons always unsigned
    } else {
        print_error_at(merge_tks(l->tk, r->tk),
                       "invalid arguments '%s' and '%s' to comparison "
                       "operation",
                       type_to_str(l->type), type_to_str(r->type));
        trigger_error();
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
    } else if (is_ptr_arr(l->type) && is_ptr_arr(r->type) &&
               are_equal(l->type, r->type)) {
        result = t_prim(T_i1, 0); // Pointer comparisons always unsigned
    } else {
        print_error_at(merge_tks(l->tk, r->tk),
                       "invalid arguments '%s' and '%s' to comparison "
                       "operation",
                       type_to_str(l->type), type_to_str(r->type));
        trigger_error();
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
    comma->type = t_copy(r->type); // Comma results in its r operand
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
    expect_tk(p->tk, TK_KINT);
    Expr *k = new_expr(EXPR_KINT);
    k->kint = p->tk->kint;
    if (k->kint > INT64_MAX) {
        k->type = t_prim(T_i64, 0);
    } else if (k->kint > INT32_MAX) {
        k->type = t_prim(T_i64, 1);
    } else {
        k->type = t_prim(T_i32, 1);
    }
    k->tk = p->tk;
    next_tk(p);
    return k;
}

static Expr * parse_kfloat(Parser *p) {
    expect_tk(p->tk, TK_KFLOAT);
    Expr *k = new_expr(EXPR_KFLOAT);
    k->kfloat = p->tk->kfloat;
    k->type = t_prim(T_f32, 1);
    k->tk = p->tk;
    next_tk(p);
    return k;
}

static Expr * parse_kchar(Parser *p) {
    expect_tk(p->tk, TK_KCHAR);
    Expr *k = new_expr(EXPR_KCHAR);
    k->kch = p->tk->kch;
    k->type = t_prim(T_i8, 1);
    k->tk = p->tk;
    next_tk(p);
    return k;
}

static Expr * parse_kstr(Parser *p) {
    expect_tk(p->tk, TK_KSTR);
    Expr *k = new_expr(EXPR_KSTR);
    k->kstr = p->tk->kstr;
    k->type = t_ptr(t_prim(T_i8, 1));
    k->tk = p->tk;
    next_tk(p);
    return k;
}

static Expr * parse_local(Parser *p) {
    expect_tk(p->tk, TK_IDENT);
    Token *name = p->tk;
    Local *local = find_local(p, name);
    if (!local) { // Check the local exists
        print_error_at(p->tk, "undeclared identifier '%.*s'", name->len,
                       name->start);
        trigger_error();
    }
    Expr *expr = new_expr(EXPR_LOCAL);
    expr->local = local;
    expr->type = t_copy(local->decl.type);
    expr->tk = p->tk;
    next_tk(p);
    return expr;
}

static Expr * parse_braced_subexpr(Parser *p) {
    expect_tk(p->tk, '(');
    Token *start = p->tk;
    next_tk(p);
    Expr *subexpr = parse_subexpr(p, PREC_NONE);
    expect_tk(p->tk, ')');
    subexpr->tk = merge_tks(start, p->tk);
    next_tk(p);
    return subexpr;
}

static Expr * parse_operand(Parser *p) {
    switch (p->tk->t) {
        case TK_KINT:   return parse_kint(p);
        case TK_KFLOAT: return parse_kfloat(p);
        case TK_KCHAR:  return parse_kchar(p);
        case TK_KSTR:   return parse_kstr(p);
        case TK_IDENT:  return parse_local(p);
        case '(':       return parse_braced_subexpr(p);
        default:
            print_error_at(p->tk, "expected expression");
            trigger_error();
    }
}

static Expr * parse_postfix_inc_dec(Parser *p, Tk op, Expr *operand) {
    // Note we can't just expand postfix a++ or a-- to a = a + 1, since the
    // result of this assignment would be the ADDITION, not the value of 'a'
    // BEFORE the addition -- we have to pass on the postfix to the compiler.
    // Standard integer promotions DON'T APPLY to ++ and --
    ensure_lvalue(operand);
    Expr *postfix = new_expr(EXPR_POSTFIX);
    postfix->op = op;
    postfix->l = operand;
    postfix->type = t_copy(operand->type);
    postfix->tk = merge_tks(operand->tk, p->tk);
    next_tk(p); // Skip the operator
    return postfix;
}

static Expr * parse_array_access(Parser *p, Expr *array) {
    Token *start = p->tk;
    expect_tk(p->tk, '[');
    next_tk(p);
    Expr *index = parse_subexpr(p, PREC_NONE);
    expect_tk(p->tk, ']');
    index->tk = merge_tks(start, p->tk);
    next_tk(p);

    ensure_can_deref(array);
    if (!is_int(index->type)) {
        print_error_at(index->tk, "invalid argument '%s' to array access",
                       type_to_str(index->type));
        trigger_error();
    }
    index = conv_to(index, t_prim(T_i64, 0), 0); // Have to add an i64
    Expr *array_access = new_expr(EXPR_BINARY);
    array_access->op = '[';
    array_access->l = array;
    array_access->r = index;
    array_access->type = t_copy(array->type->ptr);
    array_access->tk = merge_tks(array->tk, index->tk);
    return array_access;
}

static Expr * parse_postfix(Parser *p, Expr *operand) {
    Expr *postfix = operand;
    while (POSTFIX_PREC[p->tk->t]) {
        switch (p->tk->t) {
        case TK_INC: case TK_DEC:
            postfix = parse_postfix_inc_dec(p, p->tk->t, postfix);
            break;
        case '[':
            postfix = parse_array_access(p, postfix);
            break;
        default: UNREACHABLE();
        }
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
    deref->type = t_copy(operand->type->ptr);
    return deref;
}

static Expr * parse_prefix_inc_dec(Tk op, Expr *operand) {
    // Standard integer promotions DON'T APPLY to ++ and --
    ensure_lvalue(operand);
    Expr *prefix = new_expr(EXPR_UNARY);
    prefix->op = op;
    prefix->l = operand;
    prefix->type = t_copy(operand->type);
    return prefix;
}

static Expr * parse_unary_arith(Tk op, Expr *operand) {
    if (!((is_arith_op(op) && is_arith(operand->type)) ||
          (is_bit_op(op) && is_int(operand->type)))) {
        print_error_at(operand->tk, "invalid argument '%s' to operation",
                       type_to_str(operand->type));
        trigger_error();
    }
    Type *result = promote_unary_arith(operand->type);
    operand = conv_to(operand, result, 0);
    Expr *unary = new_expr(EXPR_UNARY);
    unary->op = op;
    unary->l = operand;
    unary->type = result;
    return unary;
}

static int has_decl(Token *tk); // Forward declarations
static Type * parse_type_specs(Parser *p);
static Declarator parse_abstract_declarator(Parser *p, Type *base);

static Expr * parse_cast(Parser *p) {
    expect_tk(p->tk, '(');
    Token *start = p->tk;
    next_tk(p);
    Type *base_type = parse_type_specs(p);
    Declarator declarator = parse_abstract_declarator(p, base_type);
    expect_tk(p->tk, ')');
    next_tk(p);
    Expr *operand = parse_subexpr(p, UNARY_PREC['(']);
    Expr *conv = conv_to(operand, declarator.type, 1);
    conv->tk = merge_tks(start, operand->tk);
    return conv;
}

static Expr * parse_sizeof(Parser *p) {
    expect_tk(p->tk, TK_SIZEOF);
    Token *start = p->tk;
    next_tk(p);

    Type *result;
    Token *err, *end;
    if (p->tk->t == '(') {
        next_tk(p);
        if (!has_decl(p->tk)) {
            print_error_at(p->tk, "expected type name");
            trigger_error();
        }
        err = p->tk;
        Type *base_type = parse_type_specs(p);
        Declarator decl = parse_abstract_declarator(p, base_type);
        result = decl.type;
        err = merge_tks(err, decl.tk);
        expect_tk(p->tk, ')');
        end = p->tk;
        next_tk(p);
    } else {
        Expr *operand = parse_subexpr(p, UNARY_PREC[TK_SIZEOF]);
        result = operand->type; // Discard the operand itself; not evaluated
        err = operand->tk;
        end = err;
    }
    if (is_incomplete(result)) {
        print_error_at(err, "cannot calculate size of incomplete type '%s'",
                       type_to_str(result));
        trigger_error();
    }
    // The operand to a 'sizeof' operator isn't evaluated (unless it's a VLA);
    // 'sizeof' just evaluates to a constant integer
    Expr *size = new_expr(EXPR_KINT);
    size->kint = bytes(result);
    size->type = t_prim(T_i64, 0); // Always 64 bits on a 64-bit system
    size->tk = merge_tks(start, end);
    return size;
}

static Expr * parse_unary(Parser *p) {
    Tk op = p->tk->t;
    Token *op_tk = p->tk;
    if (op == '(' && has_decl(p->tk->next)) { // Handle casts separately
        return parse_cast(p);
    }
    if (!UNARY_PREC[op]) { // Otherwise, if there's no unary operator
        Expr *operand = parse_operand(p); // Parse an operand
        return parse_postfix(p, operand); // And optional postfix operator
    }
    if (op == TK_SIZEOF) { // Handle sizeof separately
        return parse_sizeof(p);
    }
    next_tk(p); // Skip the unary operator
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
    while (BINARY_PREC[p->tk->t] > min_prec) {
        Tk op = p->tk->t;
        next_tk(p); // Skip the binary operator
        Prec prec = BINARY_PREC[op] + IS_RIGHT_ASSOC[op];
        Expr *right = parse_subexpr(p, prec); // Parse right operand
        left = parse_binary(p, op, left, right);
    }
    return left;
}

static Expr * parse_expr(Parser *p) {
    return parse_subexpr(p, PREC_NONE);
}

static int64_t calc_const_expr(Expr *expr); // Forward declaration

static int64_t resolve_conv(Expr *expr) {
    switch (expr->l->kind) {
        case EXPR_KFLOAT: return (int64_t) expr->l->kfloat;
        default: return calc_const_expr(expr->l);
    }
}

static int64_t resolve_postfix(Expr *expr) {
    switch (expr->op) {
    case '[':
        if (expr->l->kind == EXPR_KSTR) {
            return expr->l->kstr[calc_const_expr(expr->r)];
        } // Fall through otherwise...
    default:
        print_error_at(expr->tk, "expected constant expression");
        trigger_error();
    }
}

static int64_t resolve_unary(Expr *expr) {
    int64_t l = calc_const_expr(expr->l);
    switch (expr->op) {
        case '-': return -l;
        case '+': return l;
        case '~': return ~l;
        case '!': return !l;
        default:
            print_error_at(expr->tk, "expected constant expression");
            trigger_error();
    }
}

static int64_t resolve_binary(Expr *expr) {
    int64_t l = calc_const_expr(expr->l), r = calc_const_expr(expr->r);
    switch (expr->op) {
        case '+':       return l + r;
        case '-':       return l - r;
        case '*':       return l * r;
        case '/':       return l / r;
        case '%':       return l % r;
        case TK_LSHIFT: return l << r;
        case TK_RSHIFT: return l >> r;
        case '<':       return l < r;
        case TK_LE:     return l <= r;
        case '>':       return l > r;
        case TK_GE:     return l >= r;
        case TK_EQ:     return l == r;
        case TK_NEQ:    return l != r;
        case '&':       return l & r;
        case '|':       return l | r;
        case TK_AND:    return l && r;
        case TK_OR:     return l || r;
        default:
            print_error_at(expr->tk, "expected constant expression");
            trigger_error();
    }
}

static int64_t calc_const_expr(Expr *expr) {
    int64_t result;
    switch (expr->kind) {
        case EXPR_KINT:    result = (int64_t) expr->kint; break;
        case EXPR_KCHAR:   result = (int64_t) expr->kch; break;
        case EXPR_CONV:    result = resolve_conv(expr); break;
        case EXPR_POSTFIX: result = resolve_postfix(expr); break;
        case EXPR_UNARY:   result = resolve_unary(expr); break;
        case EXPR_BINARY:  result = resolve_binary(expr); break;
        case EXPR_TERNARY: result = calc_const_expr(expr->cond) ?
                                    calc_const_expr(expr->l) :
                                    calc_const_expr(expr->r); break;
        default:
            print_error_at(expr->tk, "expected constant expression");
            trigger_error();
    }
    int b = bits(expr->type);
    result &= (((int64_t) 1 << b) - 1); // Limit to the target type
    if (expr->type->is_signed && (result & ((int64_t) 1 << (b - 1)))) {
        // Sign extend if the result is signed and the sign bit is set
        result |= ~(((int64_t) 1 << b) - 1);
    }
    return result;
}

static int64_t parse_const_expr(Parser *p) {
    Expr *expr = parse_expr(p);
    return calc_const_expr(expr);
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

static int has_decl(Token *tk) {
    return TYPE_SPECS[tk->t];
}

static Type * parse_type_specs(Parser *p) {
    // Check there's at least one type specifier
    Token *start = p->tk;
    if (!has_decl(start)) {
        print_error_at(start, "expected declaration");
        trigger_error();
    }
    // Keep parsing type specifiers into a hash-map until there's no more
    int type_specs[COMBINATION_SIZE];
    memset(type_specs, 0, sizeof(int) * (NUM_TKS - FIRST_KEYWORD));
    Token *end = start;
    while (has_decl(p->tk)) {
        type_specs[p->tk->t - FIRST_KEYWORD]++;
        end = p->tk;
        next_tk(p);
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
        Token *tk = merge_tks(start, end);
        print_error_at(tk, "invalid combination of type specifiers");
        trigger_error();
    }
    int is_signed = !type_specs[TK_UNSIGNED - FIRST_KEYWORD];
    return t_prim(TYPE_COMBINATION_TO_PRIM[combination], is_signed);
}

static Type ** parse_array_declarator(Parser *p, Declarator *d, Type **t) {
    expect_tk(p->tk, '[');
    next_tk(p);
    int64_t size = parse_const_expr(p);
    expect_tk(p->tk, ']');
    d->tk = merge_tks(d->tk, p->tk);
    next_tk(p);
    if (size <= 0) {
        print_error_at(d->tk, "invalid array size '%lli', must be positive",
                       size);
        trigger_error();
    }
    *t = t_arr(NULL, size);
    t = &(*t)->elem;
    return t;
}

// Forward declaration
static Declarator parse_declarator(Parser *p, Type *base);

static Type ** parse_fn_declarator(Parser *p, Declarator *d, Type **t) {
    expect_tk(p->tk, '(');
    next_tk(p);
    int nargs = 0, max_args = 4;
    Local **args = malloc(sizeof(Local) * max_args);
    while (p->tk->t != ')') {
        Type *base = parse_type_specs(p);
        if (nargs >= max_args) {
            max_args *= 2;
            args = realloc(args, sizeof(Local) * max_args);
        }
        Declarator arg = parse_declarator(p, base); // Can be named or abstract
        args[nargs++] = def_local(p, arg);
        if (p->tk->t != ',') {
            break;
        } else {
            next_tk(p);
        }
    }
    expect_tk(p->tk, ')');
    d->tk = merge_tks(d->tk, p->tk);
    next_tk(p);
    *t = t_fn(NULL, args, nargs);
    t = &(*t)->ret;
    return t;
}

static Type ** parse_declarator_recursive(Parser *p, Declarator *d, Type **t) {
    int num_ptrs = 0;
    while (p->tk->t == '*') {
        num_ptrs++;
        d->tk = merge_tks(d->tk, p->tk);
        next_tk(p);
    }
    if (p->tk->t == TK_IDENT) {
        d->name = p->tk;
        d->tk = merge_tks(d->tk, p->tk);
        next_tk(p);
    } else if (p->tk->t == '(' && p->tk->next->t != ')') {
        // An empty "sub-declarator" is a function pointer not a NOP
        next_tk(p);
        t = parse_declarator_recursive(p, d, t);
        expect_tk(p->tk, ')');
        d->tk = merge_tks(d->tk, p->tk);
        next_tk(p);
    }
    while (p->tk->t == '[' || p->tk->t == '(') {
        if (p->tk->t == '[') {
            t = parse_array_declarator(p, d, t);
        } else if (p->tk->t == '(') {
            Local *scope = p->locals; // Function declaration scope
            t = parse_fn_declarator(p, d, t);
            p->locals = scope;
        }
    }
    while (num_ptrs--) {
        *t = t_ptr(NULL);
        t = &(*t)->ptr;
    }
    return t;
}

static void check_type(Type *t, Token *err) {
    while (t->kind != T_PRIM) {
        if (t->kind == T_FN && t->ret->kind == T_ARR) {
            print_error_at(err, "function cannot return array type '%s'",
                           type_to_str(t->ret));
            trigger_error();
        } else if (t->kind == T_FN && t->ret->kind == T_FN) {
            print_error_at(err, "function cannot return function type '%s'",
                           type_to_str(t->ret));
            trigger_error();
        }
        t = t->ptr;
    }
}

static Declarator parse_declarator(Parser *p, Type *base) {
    Declarator d;
    d.type = base;
    d.name = NULL;
    d.tk = p->tk; // Start token
    Type **inner = parse_declarator_recursive(p, &d, &d.type);
    *inner = base;
    check_type(d.type, d.tk);
    return d;
}

static Declarator parse_named_declarator(Parser *p, Type *base) {
    Declarator decl = parse_declarator(p, base);
    if (!decl.name) {
        print_error_at(decl.tk, "expected variable name");
        trigger_error();
    }
    return decl;
}

static Declarator parse_abstract_declarator(Parser *p, Type *base) {
    Declarator decl = parse_declarator(p, base);
    if (decl.name) {
        print_error_at(decl.name, "variable name not permitted here");
        trigger_error();
    }
    return decl;
}

static Stmt * parse_declaration(Parser *p, Type *base_type, int allowed_defn) {
    Declarator declarator = parse_named_declarator(p, base_type);
    Local *local = def_local(p, declarator);
    Expr *value = NULL;
    if (allowed_defn && p->tk->t == '=') { // Optional assignment
        next_tk(p); // Skip the '=' token
        value = parse_subexpr(p, PREC_COMMA); // Can't have commas
    }

    Stmt *result = new_stmt(STMT_DECL);
    result->local = local;
    if (value) {
        Expr *local_expr = new_expr(EXPR_LOCAL);
        local_expr->local = result->local;
        local_expr->type = result->local->decl.type;
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
    while (p->tk->t != ';') {
        *decl = parse_declaration(p, base_type, 1);
        while (*decl) { // Find the end of the chain
            decl = &(*decl)->next;
        }
        if (p->tk->t == ',') {
            next_tk(p); // Parse another declaration
        } else {
            break; // Stop parsing declarations
        }
    }
    expect_tk(p->tk, ';');
    next_tk(p);
    return head;
}

static Stmt * parse_stmt(Parser *p); // Forward declaration

static Stmt * parse_expr_stmt(Parser *p) {
    Stmt *stmt = new_stmt(STMT_EXPR);
    stmt->expr = parse_expr(p);
    expect_tk(p->tk, ';');
    next_tk(p);
    return stmt;
}

static Stmt * parse_if(Parser *p) {
    expect_tk(p->tk, TK_IF);
    Stmt *stmt = new_stmt(STMT_IF);
    IfChain **if_chain = &stmt->if_chain;
    int has_else = 0;
    while (p->tk->t == TK_IF) {
        next_tk(p);
        expect_tk(p->tk, '(');
        next_tk(p);
        Expr *cond = parse_expr(p); // Condition
        cond = to_cond(cond);
        expect_tk(p->tk, ')');
        next_tk(p);
        Stmt *body = parse_stmt(p); // Body
        IfChain *this_if = malloc(sizeof(IfChain));
        this_if->next = NULL;
        this_if->cond = cond;
        this_if->body = body;
        *if_chain = this_if;
        if_chain = &(*if_chain)->next;
        has_else = 0;
        if (p->tk->t == TK_ELSE) {
            has_else = 1;
            next_tk(p);
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
    expect_tk(p->tk, TK_WHILE);
    next_tk(p);
    expect_tk(p->tk, '(');
    next_tk(p);
    Expr *cond = parse_expr(p); // Condition
    stmt->cond = to_cond(cond);
    expect_tk(p->tk, ')');
    next_tk(p);
    stmt->body = parse_stmt(p); // Body
    return stmt;
}

static Stmt * parse_for(Parser *p) {
    Stmt *head = NULL;
    Stmt **stmt = &head;
    expect_tk(p->tk, TK_FOR);
    next_tk(p);
    expect_tk(p->tk, '(');
    next_tk(p);
    Local *scope = p->locals;

    if (has_decl(p->tk)) { // Initializer
        *stmt = parse_declaration_list(p); // Declaration initializer
    } else if (p->tk->t != ';') {
        *stmt = parse_expr_stmt(p); // Expression initializer
    } else {
        next_tk(p); // No initializer, skip ';'
    }
    while (*stmt) { // Find the end of the initializer
        stmt = &(*stmt)->next;
    }

    Expr *cond = NULL; // Condition
    if (p->tk->t != ';') {
        cond = parse_expr(p);
        cond = to_cond(cond);
    }
    expect_tk(p->tk, ';');
    next_tk(p);

    Expr *inc = NULL;
    if (p->tk->t != ')') {
        inc = parse_expr(p); // Increment
    }
    expect_tk(p->tk, ')');
    next_tk(p);

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
    expect_tk(p->tk, TK_DO);
    next_tk(p);
    stmt->body = parse_stmt(p); // Body
    expect_tk(p->tk, TK_WHILE);
    next_tk(p);
    expect_tk(p->tk, '(');
    next_tk(p);
    Expr *cond = parse_expr(p); // Condition
    stmt->cond = to_cond(cond);
    expect_tk(p->tk, ')');
    next_tk(p);
    expect_tk(p->tk, ';');
    next_tk(p);
    return stmt;
}

static Stmt * parse_break(Parser *p) {
    expect_tk(p->tk, TK_BREAK);
    next_tk(p);
    expect_tk(p->tk, ';');
    next_tk(p);
    Stmt *stmt = new_stmt(STMT_BREAK);
    return stmt;
}

static Stmt * parse_continue(Parser *p) {
    expect_tk(p->tk, TK_CONTINUE);
    next_tk(p);
    expect_tk(p->tk, ';');
    next_tk(p);
    Stmt *stmt = new_stmt(STMT_CONTINUE);
    return stmt;
}

static Stmt * parse_ret(Parser *p) {
    expect_tk(p->tk, TK_RETURN);
    next_tk(p);
    Stmt *ret = new_stmt(STMT_RET);
    if (p->tk->t != ';') {
        Expr *value = parse_expr(p);
        value = conv_to(value, p->fn->local->decl.type->ret, 0);
        ret->expr = value;
    }
    expect_tk(p->tk, ';');
    next_tk(p);
    return ret;
}

static Stmt * parse_block(Parser *p) {
    expect_tk(p->tk, '{');
    next_tk(p);
    Stmt *block = NULL;
    Stmt **stmt = &block;
    Local *scope = p->locals; // New locals scope
    while (p->tk->t && p->tk->t != '}') {
        if (has_decl(p->tk)) { // Declarations can only occur in BLOCKS
            *stmt = parse_declaration_list(p);
        } else {
            *stmt = parse_stmt(p);
        }
        while (*stmt) { // Find the last statement in the chain
            stmt = &(*stmt)->next;
        }
    }
    p->locals = scope;
    expect_tk(p->tk, '}');
    next_tk(p);
    return block;
}

static Stmt * parse_stmt(Parser *p) {
    switch (p->tk->t) {
        case ';':         next_tk(p); return NULL; // Empty
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

static AstModule * parse_module(Parser *p) {
    AstModule *module = malloc(sizeof(AstModule));
    module->fns = NULL;
    FnDef **def = &module->fns;
    while (p->tk->t) { // Until we reach the end of the file
        Type *base = parse_type_specs(p); // Declaration
        Declarator decl = parse_named_declarator(p, base);
        if (p->tk->t == '{') {
            if (!is_fn(decl.type)) {
                print_error_at(decl.tk, "expected function");
                trigger_error();
            }
            FnDef *fn = malloc(sizeof(FnDef));
            fn->next = NULL;
            fn->local = def_local(p, decl);
            p->fn = fn;

            Type *fn_decl_type = fn->local->decl.type;
            Local *scope = p->locals;
            p->locals->next = fn_decl_type->args[fn_decl_type->nargs - 1];
            fn->body = parse_block(p); // Body
            p->locals = scope;

            *def = fn;
            def = &(*def)->next;
        } else {
            expect_tk(p->tk, ';');
            next_tk(p);
            // TODO: top level declarations
        }
    }
    return module;
}

AstModule * parse(char *file) {
    Parser p;
    p.tk = lex_file(file);
    p.locals = NULL;
    AstModule *module = parse_module(&p);
    return module;
}
