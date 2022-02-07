
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

static Parser new_parser(char *file) {
    Parser p;
    p.l = new_lexer(file);
    next_tk(&p.l);
    p.locals = NULL;
    return p;
}

static Local * find_local(Parser *p, char *name, int len) {
    for (Local *l = p->locals; l; l = l->next) {
        if (strlen(l->name) == len && strncmp(l->name, name, len) == 0) {
            return l;
        }
    }
    return NULL;
}

static Local * def_local(Parser *p, TkInfo name, SignedType type) {
    if (find_local(p, name.start, name.len)) {
        trigger_error_at(name, "redefinition of '%.*s'", name.len, name.start);
    }
    char *name_str = malloc((name.len + 1) * sizeof(char));
    strncpy(name_str, name.start, name.len);
    name_str[name.len] = '\0';
    Local *local = new_local(name_str, type);
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
};

static Prec POSTFIX_PREC[NUM_TKS] = {
    [TK_INC] = PREC_POSTFIX, // Increment
    [TK_DEC] = PREC_POSTFIX, // Decrement
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

// Forward declarations
static Expr * parse_subexpr(Parser *p, Prec min_prec);
static Expr * parse_operation(Tk op, Expr *left, Expr *right);

static void ensure_lvalue(Expr *lvalue) {
    if (lvalue->kind == EXPR_LOCAL) {
        return; // Assigning to a local
    }
    if (lvalue->kind == EXPR_UNARY && lvalue->op == '*') {
        return; // Assigning to a pointer dereference
    }
    trigger_error_at(lvalue->tk, "expression is not assignable");
}

static void ensure_can_take_addr(Expr *operand) {
    // See 6.5.3.2 in C99 standard for what's allowed
    if (operand->kind == EXPR_LOCAL) {
        return; // Address of a local
    }
    if (operand->kind == EXPR_UNARY && operand->op == '*') {
        return; // Address of dereference
    }
    trigger_error_at(operand->tk, "cannot take address of operand");
}

static void ensure_can_deref(Expr *operand) {
    if (operand->type.ptrs < 1) {
        trigger_error_at(operand->tk, "cannot dereference operand");
    }
}

static int is_null_ptr(Expr *e) {
    return e->kind == EXPR_KINT && e->kint == 0;
}

// Returns 1 if the conversion from the source to target type is valid
static int check_conv(Expr *src, SignedType tt) {
    SignedType st = src->type;
    if (is_ptr(tt) && is_ptr(st) && !is_null_ptr(src)) {
        trigger_warning_at(src->tk, "incompatible pointer types");
    }
    return (is_arith(tt) && is_arith(st)) ||
           (is_ptr(tt) && is_ptr(st)) ||
           (is_ptr(tt) && is_int(st)) ||
           (is_int(tt) && is_ptr(st));
}

static Expr * conv_const(Expr *expr, SignedType target) {
    if (is_fp(target) && expr->kind == EXPR_KINT) {
        expr->kind = EXPR_KFLOAT;
        expr->kfloat = (double) expr->kint;
    } else if (is_int(target) && expr->kind == EXPR_KFLOAT) {
        expr->kind = EXPR_KFLOAT;
        expr->kint = (int) expr->kfloat;
    }
    expr->type = target;
    return expr;
}

static Expr * conv_to(Expr *src, SignedType target) {
    assert(target.prim != T_NONE);
    if (are_equal(src->type, target)) {
        return src; // No conversion necessary
    }
    if (src->kind == EXPR_KINT || src->kind == EXPR_KFLOAT) {
        return conv_const(src, target); // Don't emit CONV on constants
    }
    if (!check_conv(src, target)) {
        trigger_error_at(src->tk, "invalid type conversion");
        // TODO: print the types we're converting between
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
static SignedType promote_binary_int(Expr *l, Expr *r) {
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
    SignedType lt = l->type, rt = r->type;
    if (signed_bits(lt) < 32 && signed_bits(rt) < 32) {
        // 0. Implicit promotion to (signed) 'int' for "small" integer types
        return signed_i32();
    } else if (signed_bits(lt) == signed_bits(rt) &&
               lt.is_signed == rt.is_signed) {
        // 1. Types are equal
        return lt;
    } else if (lt.is_signed == rt.is_signed) {
        // 2. Both signed or unsigned -> convert to larger type
        return signed_bits(lt) > signed_bits(rt) ? lt : rt;
    } else {
        // 3. and 4. pick the larger type; if they're both the same size then
        // pick the unsigned type
        SignedType st = lt.is_signed ? lt : rt, ut = lt.is_signed ? rt : lt;
        return signed_bits(ut) >= signed_bits(st) ? ut : st;
    }
}

// Returns the type that a binary arithmetic operation's operands should be
// converted to (if necessary)
static SignedType promote_binary_arith(Expr *l, Expr *r) {
    SignedType lt = l->type, rt = r->type;
    if (is_int(lt) && is_int(rt)) { // Both ints
        return promote_binary_int(l, r);
    } else if (is_fp(lt) && is_fp(rt)) { // Both floats
        return signed_bits(lt) > signed_bits(rt) ? lt : rt; // Pick larger
    } else { // One's a float and one's an int
        return is_fp(lt) ? lt : rt; // Pick float type
    }
}

// Takes a binary operation and its two operands and computes the type that the
// result of the operation should have, and performs any necessary type
// conversions on the operands.
// Type checking is complex! The C standard is very specific about what needs
// to happen
static SignedType resolve_types(Tk o, Expr **l, Expr **r) {
    SignedType result, lt = (*l)->type, rt = (*r)->type;
    if (is_bit_op(o) && is_int(lt) && is_int(rt)) {
        result = promote_binary_int(*l, *r);
        *l = conv_to(*l, result);
        *r = conv_to(*r, result);
    } else if ((is_arith_op(o) || o == '?') && is_arith(lt) && is_arith(rt)) {
        result = promote_binary_arith(*l, *r);
        *l = conv_to(*l, result);
        *r = conv_to(*r, result);
    } else if ((is_rel_op(o) || is_eq_op(o)) && is_arith(lt) && is_arith(rt)) {
        SignedType promotion = promote_binary_arith(*l, *r);
        *l = conv_to(*l, promotion);
        *r = conv_to(*r, promotion);
        result = unsigned_i1(); // Result is an i1
        result.is_signed = promotion.is_signed; // Preserve signed-ness
    } else if ((o == '+' || o == '-') && is_ptr(lt) && is_arith(rt)) {
        result = lt; // Result is a pointer
        *r = conv_to(*r, unsigned_i64()); // Can only add i64 to pointers
    } else if (o == '+' && is_arith(rt) && is_ptr(lt)) {
        result = rt; // Result is a pointer
        *l = conv_to(*l, unsigned_i64()); // Can only add i64 to pointers
    } else if (o == '-' && is_ptr(lt) && is_ptr(rt) && are_equal(lt, rt)) {
        result = unsigned_i64(); // Result is an INTEGER
        *l = conv_to(*l, result); // Convert both operands to i64s
        *r = conv_to(*r, result);
    } else if (o == '?' && is_ptr(lt) && is_ptr(rt) && are_equal(lt, rt)) {
        result = lt; // Doesn't matter which one we pick
    } else if ((is_rel_op(o) || is_eq_op(o)) &&
               is_ptr(lt) && is_ptr(rt) && are_equal(lt, rt)) { // Both ptrs
        result = unsigned_i1(); // Pointer comparisons are always unsigned
    } else if (o == '?' && is_ptr(lt) && (is_void_ptr(rt) || is_null_ptr(*r))) {
        result = lt; // Pick the non-void/non-null pointer
        *r = conv_to(*r, result); // Convert to the non-void pointer
    } else if (o == '?' && (is_void_ptr(lt) || is_null_ptr(*l)) && is_ptr(rt)) {
        result = rt; // Pick the non-void/non-null pointer
        *l = conv_to(*l, result); // Convert to the non-void pointer
    } else if (is_eq_op(o) &&
               is_ptr(lt) && (is_void_ptr(rt) || is_null_ptr(*r))) {
        SignedType promotion = lt; // Pick the non-void/non-null pointer
        *r = conv_to(*r, promotion); // Convert to the non-void pointer
        result = unsigned_i1(); // Pointer comparisons always unsigned
    } else if (is_eq_op(o) &&
              (is_void_ptr(lt) || is_null_ptr(*l)) && is_ptr(rt)) {
        SignedType promotion = rt; // Pick the non-void/non-null pointer
        *l = conv_to(*l, promotion); // Convert to the non-void pointer
        result = unsigned_i1(); // Pointer comparisons always unsigned
    } else {
        TkInfo operation = merge_tks((*l)->tk, (*r)->tk);
        trigger_error_at(operation, "invalid argument to operation");
        // TODO: might be useful to print the C type associated
    }
    return result;
}

// Returns the type that a unary integer operation's operands should be
// converted to (if necessary)
static SignedType promote_unary_arith(Expr *operand) {
    if (is_int(operand->type) && signed_bits(operand->type) < 32) {
        // Implicit promotion to (signed) 'int' for "small" integer types
        return signed_i32();
    } else {
        return operand->type; // No conversion necessary
    }
}

// Takes a unary operation and its operand and computes the type that the
// result of the operation should have, and performs any necessary conversions
static SignedType resolve_unary_type(Tk op, Expr **e) {
    SignedType result, t = (*e)->type;
    if ((is_arith_op(op) && is_arith(t)) || (is_bit_op(op) && is_int(t))) {
        result = promote_unary_arith(*e);
        *e = conv_to(*e, result);
    } else {
        trigger_error_at((*e)->tk, "invalid argument to operation");
        // TODO: might be useful to print the C type associated
    }
    return result;
}

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
    return parse_operation(TK_NEQ, expr, zero);
}

static Expr * parse_ternary(Parser *p, Expr *cond, Expr *left) {
    expect_tk(&p->l, ':');
    next_tk(&p->l);
    Prec prec = BINARY_PREC['?'] - IS_RIGHT_ASSOC['?'];
    Expr *right = parse_subexpr(p, prec);

    SignedType result = resolve_types('?', &left, &right);
    Expr *ternary = new_expr(EXPR_TERNARY);
    ternary->cond = to_cond(cond);
    ternary->l = left;
    ternary->r = right;
    ternary->type = result;
    ternary->tk = merge_tks(cond->tk, right->tk);
    return ternary;
}

static Expr * parse_operation(Tk op, Expr *left, Expr *right) {
    SignedType result = resolve_types(op, &left, &right);
    Expr *arith = new_expr(EXPR_BINARY);
    arith->op = op;
    arith->l = left;
    arith->r = right;
    arith->type = result;
    arith->tk = merge_tks(left->tk, right->tk);
    return arith;
}

static Expr * parse_assign(Expr *left, Expr *right) {
    ensure_lvalue(left);
    right = conv_to(right, left->type); // Lower 'right' to 'left->type'
    Expr *assign = new_expr(EXPR_BINARY);
    assign->op = '=';
    assign->l = left;
    assign->r = right;
    assign->type = left->type;
    assign->tk = merge_tks(left->tk, right->tk);
    return assign;
}

static Expr * parse_arith_assign(Tk op, Expr *left, Expr *right) {
    ensure_lvalue(left);
    SignedType lvalue_type = left->type;
    Tk arith_op = ASSIGNMENT_TO_ARITH_OP[op];
    resolve_types(arith_op, &left, &right); // Emit CONVs for arguments
    Expr *assign = new_expr(EXPR_BINARY);
    assign->op = op;
    assign->l = left;
    assign->r = right;
    // Assignment always results in its right operand being converted to
    // 'left->type' (although this is handled in the compiler here, not by an
    // EXPR_CONV emitted by the parser)
    assign->type = lvalue_type;
    assign->tk = merge_tks(left->tk, right->tk);
    return assign;
}

static Expr * parse_cond(Tk op, Expr *left, Expr *right) {
    left = to_cond(left);
    right = to_cond(right);
    Expr *cond = new_expr(EXPR_BINARY);
    cond->op = op;
    cond->l = left;
    cond->r = right;
    cond->type = unsigned_i1();
    cond->tk = merge_tks(left->tk, right->tk);
    return cond;
}

static Expr * parse_comma(Expr *left, Expr *right) {
    Expr *comma = new_expr(EXPR_BINARY);
    comma->op = ',';
    comma->l = left;
    comma->r = right;
    comma->type = right->type; // Comma results in its right operand
    comma->tk = merge_tks(left->tk, right->tk);
    return comma;
}

static Expr * parse_binary(Parser *p, Tk op, Expr *left, Expr *right) {
    switch (op) {
    case '+': case '-': case '*': case '/': case '%':
    case TK_LSHIFT: case TK_RSHIFT: case '&': case '|': case '^':
    case TK_EQ: case TK_NEQ: case '<': case TK_LE: case '>': case TK_GE:
        return parse_operation(op, left, right);
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
    k->type = signed_i32();
    k->tk = p->l.info;
    next_tk(&p->l);
    return k;
}

static Expr * parse_kfloat(Parser *p) {
    expect_tk(&p->l, TK_KFLOAT);
    Expr *k = new_expr(EXPR_KFLOAT);
    k->kfloat = p->l.kfloat;
    k->type = signed_f32();
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

static Expr * parse_braced_subexpr(Parser *p) {
    TkInfo start = p->l.info;
    expect_tk(&p->l, '(');
    next_tk(&p->l);
    Expr *expr = parse_subexpr(p, PREC_NONE);
    expect_tk(&p->l, ')');
    expr->tk = merge_tks(start, p->l.info);
    next_tk(&p->l);
    return expr;
}

static Expr * parse_operand(Parser *p) {
    switch (p->l.tk) {
        case TK_KINT:   return parse_kint(p);
        case TK_KFLOAT: return parse_kfloat(p);
        case TK_IDENT:  return parse_local(p);
        case '(':       return parse_braced_subexpr(p);
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

static Expr * parse_postfix(Parser *p, Expr *operand) {
    Tk op = p->l.tk;
    if (POSTFIX_PREC[op]) { // ++ and -- are the only postfix operators for now
        Expr *operation = parse_postfix_inc_dec(op, operand);
        operation->tk = merge_tks(operand->tk, p->l.info);
        next_tk(&p->l); // Skip the operator
        return operation;
    }
    return operand; // No postfix operation
}

static Expr * parse_not(Expr *operand) {
    operand = to_cond(operand);
    Expr *unary = new_expr(EXPR_UNARY);
    unary->op = '!';
    unary->l = operand; // No conv needed -> guaranteed to be a condition
    unary->type = unsigned_i1();
    return unary;
}

static Expr * parse_addr(Expr *operand) {
    ensure_can_take_addr(operand);
    Expr *addr = new_expr(EXPR_UNARY);
    addr->op = '&';
    addr->l = operand;
    addr->type = operand->type;
    addr->type.ptrs++; // Returns a POINTER to the operand
    return addr;
}

static Expr * parse_deref(Expr *operand) {
    ensure_can_deref(operand);
    Expr *deref = new_expr(EXPR_UNARY);
    deref->op = '*';
    deref->l = operand;
    deref->type = operand->type;
    deref->type.ptrs--;
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
    SignedType result = resolve_unary_type(op, &operand);
    Expr *unary = new_expr(EXPR_UNARY);
    unary->op = op;
    unary->l = operand;
    unary->type = result;
    return unary;
}

static Expr * parse_unary(Parser *p) {
    Tk op = p->l.tk;
    if (!UNARY_PREC[op]) { // Is there a unary operator
        // Parse an operand and a potential postfix operator
        Expr *operand = parse_operand(p);
        return parse_postfix(p, operand);
    }
    TkInfo operator_tk = p->l.info;
    next_tk(&p->l); // Skip the unary operator
    Expr *operand = parse_subexpr(p, UNARY_PREC[op]);
    Expr *unary;
    switch (op) {
    case '+': case '-': case '~':
        unary = parse_unary_arith(op, operand); break;
    case '!': unary = parse_not(operand); break;
    case '&': unary = parse_addr(operand); break;
    case '*': unary = parse_deref(operand); break;
    case TK_INC: case TK_DEC:
        unary = parse_prefix_inc_dec(op, operand); break;
    default: UNREACHABLE();
    }
    unary->tk = merge_tks(operator_tk, operand->tk);
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

static SignedType parse_type_spec(Parser *p) {
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
    SignedType type;
    type.prim = TYPE_COMBINATION_TO_PRIM[combination];
    type.ptrs = 0;
    type.is_signed = !type_specs[TK_UNSIGNED - FIRST_KEYWORD];
    return type;
}

static Declarator parse_declarator(Parser *p, SignedType base_type) {
    TkInfo start = p->l.info;
    SignedType type = base_type;
    while (p->l.tk == '*') { // Pointers
        type.ptrs++;
        next_tk(&p->l);
    }

    expect_tk(&p->l, TK_IDENT); // Name
    TkInfo name = p->l.info;
    if (find_local(p, name.start, name.len)) { // Check not already defined
        trigger_error_at(name, "redefinition of '%.*s'", name.len, name.start);
    }
    next_tk(&p->l);

    Declarator d;
    d.name = name;
    d.type = type;
    d.tk = merge_tks(start, name);
    return d;
}

static Stmt * parse_decl(Parser *p, SignedType base_type, int allowed_defn) {
    Declarator declarator = parse_declarator(p, base_type);
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

static Stmt * parse_decl_list(Parser *p) {
    SignedType base_type = parse_type_spec(p); // Base type specifiers
    Stmt *head;
    Stmt **decl = &head;
    while (p->l.tk != ';') {
        *decl = parse_decl(p, base_type, 1);
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
        IfChain *this_if = new_if_chain();
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
        IfChain *this_else = new_if_chain();
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
        *stmt = parse_decl_list(p); // Declaration initializer
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
        value = conv_to(value, p->fn->decl->return_type);
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
            *stmt = parse_decl_list(p);
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
    SignedType base_type = parse_type_spec(p); // Type
    FnArg *arg = new_fn_arg();
    Stmt *decl = parse_decl(p, base_type, 0);
    arg->local = decl->local;
    assert(!decl->next); // Sanity check -> only one statement
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
    FnDef *def = new_fn_def();
    p->fn = def;

    def->decl = new_fn_decl();
    def->decl->return_type = parse_type_spec(p); // Return type

    expect_tk(&p->l, TK_IDENT); // Name
    def->decl->local = def_local(p, p->l.info, signed_none());
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
    AstModule *module = new_ast_module();
    FnDef **def = &module->fns;
    while (p->l.tk) { // Until we reach the end of the file
        *def = parse_fn_def(p);
        def = &(*def)->next;
    }
    return module;
}

AstModule * parse(char *file) {
    Parser p = new_parser(file);
    AstModule *module = parse_module(&p);
    return module;
}
