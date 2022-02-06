
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
    // TODO: compare against function names too
    for (Local *l = p->locals; l; l = l->next) {
        if (strlen(l->name) == len && strncmp(l->name, name, len) == 0) {
            return l; // Already defined
        }
    }
    return NULL;
}

static Local * def_local(Parser *p, char *name, SignedType type) {
    Local *new = new_local(name, type);
    new->next = p->locals; // Prepend to the linked list
    p->locals = new;
    return new;
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
    ['-'] = PREC_UNARY,  // Negation
    ['~'] = PREC_UNARY, // Bitwise not
    ['!'] = PREC_UNARY,  // Logical not
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

static Tk ASSIGN_OP[NUM_TKS] = {
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

static void ensure_lvalue(Expr *lvalue) {
    if (lvalue->kind != EXPR_LOCAL) {
        trigger_error_at(lvalue->tk, "expression is not assignable");
    }
}

// Returns the type that a binary arithmetic operation's operands should be
// converted to (if necessary) for a binary operation
//
// See this Stack Overflow for a useful explanation of the (rather stupid) C
// integer promotion rules:
//   https://stackoverflow.com/questions/46073295/implicit-type-promotion-rules
static SignedType binary_int_promotion(Expr *l, Expr *r) {
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
    if (signed_bits(l->type) < 32 && signed_bits(r->type) < 32) {
        // 0. Implicit promotion to (signed) 'int' for "small" integer types
        return signed_i32();
    } else if (signed_bits(l->type) == signed_bits(r->type) &&
            l->type.is_signed == r->type.is_signed) {
        // 1. Types are equal
        return l->type;
    } else if (l->type.is_signed == r->type.is_signed) {
        // 2. Both signed or unsigned -> convert to larger type
        return signed_bits(l->type) > signed_bits(r->type) ? l->type : r->type;
    } else {
        // 3. and 4. Pick the larger type; if they're both the same size then
        // pick the unsigned type
        SignedType signed_type = l->type.is_signed ? l->type : r->type;
        SignedType unsigned_type = l->type.is_signed ? r->type : l->type;
        return signed_bits(unsigned_type) >= signed_bits(signed_type) ?
            unsigned_type : signed_type;
    }
}

static SignedType unary_int_promotion(Expr *operand) {
    // Implicit integer promotion (see 'binary_int_promotion' above) for unary
    // operations
    if (signed_bits(operand->type) < 32) {
        return signed_i32();
    } else {
        return operand->type;
    }
}

static Expr * conv_to(Expr *expr, SignedType target) {
    assert(target.prim != T_NONE);
    if (signed_bits(expr->type) == signed_bits(target)) {
        return expr; // No conversion necessary
    }
    if (expr->kind == EXPR_KINT && expr->type.prim == T_NONE) {
        // Don't emit type conversions on integers if their type isn't fixed
        // by another instruction yet
        expr->type = target;
        return expr;
    }
    Expr *conv = new_expr(EXPR_CONV);
    conv->l = expr;
    conv->type = target;
    conv->tk = expr->tk;
    return conv;
}

// Forward declarations
static Expr * parse_subexpr(Parser *p, Prec min_prec);
static Expr * parse_cmp(Tk op, Expr *left, Expr *right);

static Expr * to_cond(Expr *expr) {
    Tk op = expr->op;
    if ((expr->kind == EXPR_BINARY && (op == TK_EQ || op == TK_NEQ ||
                op == '<' || op == TK_LE || op == '>' || op == TK_GE ||
                op == TK_OR || op == TK_AND)) ||
            (expr->kind == EXPR_UNARY && op == '!')) {
        return expr; // Already a condition
    }
    // If 'expr' isn't a comparison or condition, then emit a '!= 0'
    Expr *zero = new_expr(EXPR_KINT);
    zero->kint = 0;
    zero->tk = expr->tk;
    return parse_cmp(TK_NEQ, expr, zero);
}

static Expr * parse_ternary(Parser *p, Expr *cond, Expr *left) {
    expect_tk(&p->l, ':');
    next_tk(&p->l);
    Prec prec = BINARY_PREC['?'] - IS_RIGHT_ASSOC['?'];
    Expr *right = parse_subexpr(p, prec);

    SignedType target = binary_int_promotion(left, right);
    left = conv_to(left, target);
    right = conv_to(right, target);

    Expr *ternary = new_expr(EXPR_TERNARY);
    ternary->cond = to_cond(cond);
    ternary->l = left;
    ternary->r = right;
    ternary->type = target;
    ternary->tk = merge_tks(cond->tk, right->tk);
    return ternary;
}

static Expr * parse_arith(Tk op, Expr *left, Expr *right) {
    SignedType target = binary_int_promotion(left, right);
    left = conv_to(left, target);
    right = conv_to(right, target);

    Expr *arith = new_expr(EXPR_BINARY);
    arith->op = op;
    arith->l = left;
    arith->r = right;
    arith->type = target;
    arith->tk = merge_tks(left->tk, right->tk);
    return arith;
}

static Expr * parse_cmp(Tk op, Expr *left, Expr *right) {
    SignedType target = binary_int_promotion(left, right);
    left = conv_to(left, target);
    right = conv_to(right, target);

    Expr *cmp = new_expr(EXPR_BINARY);
    cmp->op = op;
    cmp->l = left;
    cmp->r = right;
    cmp->type = signed_i1(); // Comparisons always result in a boolean value
    cmp->type.is_signed = target.is_signed; // Save signed-ness
    cmp->tk = merge_tks(left->tk, right->tk);
    return cmp;
}

static Expr * parse_assign(Tk op, Expr *left, Expr *right) {
    if (op != '=') {
        // Expand arithmetic assignments to their full thing, e.g., a += 1
        // becomes a = a + 1 in the AST; makes IR generation easier
        right = parse_arith(ASSIGN_OP[op], left, right);
    }
    ensure_lvalue(left);
    right = conv_to(right, left->type);
    Expr *assign = new_expr(EXPR_BINARY);
    assign->op = '=';
    assign->l = left;
    assign->r = right;
    assign->type = right->type; // Assignment results in its right operand
    assign->tk = merge_tks(left->tk, right->tk);
    return assign;
}

static Expr * parse_cond(Tk op, Expr *left, Expr *right) {
    left = to_cond(left);
    right = to_cond(right);

    Expr *cond = new_expr(EXPR_BINARY);
    cond->op = op;
    cond->l = left; // No conv necessary -> guaranteed to be a condition
    cond->r = right;
    cond->type = signed_i1(); // Conditions always result in a boolean value
    cond->tk = merge_tks(left->tk, right->tk);
    return cond;
}

static Expr * parse_comma(Expr *left, Expr *right) {
    Expr *comma = new_expr(EXPR_BINARY);
    comma->op = ',';
    comma->l = left;
    comma->r = right;
    comma->type = right->type; // Comma results in its RHS
    comma->tk = merge_tks(left->tk, right->tk);
    return comma;
}

static Expr * parse_binary(Parser *p, Tk op, Expr *left, Expr *right) {
    switch (op) {
    case '+': case '-': case '*': case '/': case '%':
    case TK_LSHIFT: case TK_RSHIFT: case '&': case '|': case '^':
        return parse_arith(op, left, right);
    case TK_EQ: case TK_NEQ: case '<': case TK_LE: case '>': case TK_GE:
        return parse_cmp(op, left, right);
    case '=':
    case TK_ADD_ASSIGN: case TK_SUB_ASSIGN:
    case TK_MUL_ASSIGN: case TK_DIV_ASSIGN: case TK_MOD_ASSIGN:
    case TK_AND_ASSIGN: case TK_OR_ASSIGN:  case TK_XOR_ASSIGN:
    case TK_LSHIFT_ASSIGN: case TK_RSHIFT_ASSIGN:
        return parse_assign(op, left, right);
    case TK_AND: case TK_OR:
        return parse_cond(op, left, right);
    case '?': return parse_ternary(p, left, right);
    case ',': return parse_comma(left, right);
    default: UNREACHABLE();
    }
}

static Expr * parse_kint(Parser *p) {
    expect_tk(&p->l, TK_NUM);
    int value = p->l.num;
    Expr *kint = new_expr(EXPR_KINT);
    kint->kint = value;
    // kint->type gets filled in on-the-fly
    kint->tk = p->l.info;
    next_tk(&p->l);
    return kint;
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
        case TK_NUM:   return parse_kint(p);
        case TK_IDENT: return parse_local(p);
        case '(':      return parse_braced_subexpr(p);
        default:       trigger_error_at(p->l.info, "expected expression");
    }
}

static Expr * parse_postfix_inc_dec(Tk op, Expr *operand) {
    // Note we can't just expand postfix a++ or a-- to a = a + 1, since the
    // result of this assignment would be the ADDITION, not the value of 'a'
    // BEFORE the addition -- we have to pass on the postfix to the compiler.
    // Don't convert everything to i32s for prefix/postfix ++ and --, since
    // it'll just get SEXT'd then TRUNC'd anyway
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
    unary->type = signed_i1();
    return unary;
}

static Expr * parse_prefix_inc_dec(Tk op, Expr *operand) {
    // Don't convert everything to i32s for prefix/postfix ++ and --, since
    // it'll just get SEXT'd then TRUNC'd anyway
    ensure_lvalue(operand);
    Expr *prefix = new_expr(EXPR_UNARY);
    prefix->op = op;
    prefix->l = operand;
    prefix->type = operand->type;
    return prefix;
}

static Expr * parse_unary_arith(Tk op, Expr *operand) {
    // All arithmetic instructions are performed as either i32 or i64; they
    // default to i32 (the natural 'int' size on my target), but will use i64
    // if either operand is an i64
    SignedType target = unary_int_promotion(operand);
    operand = conv_to(operand, target);
    Expr *unary = new_expr(EXPR_UNARY);
    unary->op = op;
    unary->l = operand;
    unary->type = target;
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
    case '!':
        unary = parse_not(operand);
        break;
    case TK_INC: case TK_DEC:
        unary = parse_prefix_inc_dec(op, operand);
        break;
    default:
        unary = parse_unary_arith(op, operand);
        break;
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

static SignedType parse_decl_spec(Parser *p) {
    // Check there's at least one type specifier
    TkInfo start = p->l.info;
    if (!TYPE_SPECS[p->l.tk]) {
        trigger_error_at(start, "expected declaration");
    }
    // Keep parsing type specifiers into a hash-map until there's no more
    int type_specs[COMBINATION_SIZE];
    memset(type_specs, 0, sizeof(int) * (NUM_TKS - FIRST_KEYWORD));
    TkInfo end = start;
    while (TYPE_SPECS[p->l.tk]) {
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

static Stmt * parse_decl(Parser *p) {
    SignedType type = parse_decl_spec(p); // Type
    Stmt *head;
    Stmt **decl = &head;
    while (p->l.tk != ';') {
        expect_tk(&p->l, TK_IDENT);
        char *name = malloc((p->l.len + 1) * sizeof(char));
        strncpy(name, p->l.ident, p->l.len);
        name[p->l.len] = '\0';
        TkInfo local_tk = p->l.info;
        if (find_local(p, name, p->l.len)) { // Check isn't already defined
            trigger_error_at(local_tk, "redefinition of '%s'", name);
        }
        next_tk(&p->l);

        Expr *value = NULL;
        if (p->l.tk == '=') { // Assignment
            next_tk(&p->l); // Skip the '=' token
            value = parse_subexpr(p, PREC_COMMA); // Can't have commas
        }

        Stmt *result = new_stmt(STMT_DECL);
        result->local = def_local(p, name, type);
        *decl = result;
        decl = &(*decl)->next;
        if (value) {
            Expr *local_expr = new_expr(EXPR_LOCAL);
            local_expr->local = result->local;
            local_expr->type = result->local->type;
            local_expr->tk = local_tk;
            Stmt *assign = new_stmt(STMT_EXPR);
            assign->expr = parse_assign('=', local_expr, value);
            *decl = assign; // Chain the declaration and assignment
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

static Stmt * parse_expr_stmt(Parser *p) {
    Stmt *stmt = new_stmt(STMT_EXPR);
    stmt->expr = parse_expr(p);
    expect_tk(&p->l, ';');
    next_tk(&p->l);
    return stmt;
}

static Stmt * parse_block(Parser *p); // Forward declaration

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
        Stmt *body = parse_block(p); // Body
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
        this_else->body = parse_block(p);
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
    stmt->body = parse_block(p); // Body
    return stmt;
}

static Stmt * parse_for(Parser *p) {
    Stmt *head;
    Stmt **stmt = &head;
    expect_tk(&p->l, TK_FOR);
    next_tk(&p->l);
    expect_tk(&p->l, '(');
    next_tk(&p->l);
    Local *scope = p->locals;
    *stmt = parse_decl(p); // Declaration
    while (*stmt) { // Find the end of the declaration
        stmt = &(*stmt)->next;
    }
    Expr *cond = parse_expr(p); // Condition
    cond = to_cond(cond);
    expect_tk(&p->l, ';');
    next_tk(&p->l);
    Expr *inc = parse_expr(p); // Increment
    Stmt *inc_stmt = new_stmt(STMT_EXPR);
    inc_stmt->expr = inc;
    expect_tk(&p->l, ')');
    next_tk(&p->l);
    Stmt *body = parse_block(p); // Body
    Stmt **end = &body;
    while (*end) { // Find the end of the body
        end = &(*end)->next;
    }
    *end = inc_stmt; // Put the increment statement at the end of the body
    p->locals = scope; // Remove the declaration in the loop header
    Stmt *loop = new_stmt(STMT_WHILE);
    loop->cond = cond;
    loop->body = body;
    *stmt = loop;
    return head;
}

static Stmt * parse_do_while(Parser *p) {
    Stmt *stmt = new_stmt(STMT_DO_WHILE);
    expect_tk(&p->l, TK_DO);
    next_tk(&p->l);
    stmt->body = parse_block(p); // Body
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

static Stmt * parse_stmt(Parser *p) {
    switch (p->l.tk) {
    case ';':       next_tk(&p->l); return NULL; // Empty
    case '{':       return parse_block(p);       // Block
    case TK_IF:     return parse_if(p);          // If/else if/else
    case TK_WHILE:  return parse_while(p);       // While loop
    case TK_FOR:    return parse_for(p);         // For loop
    case TK_DO:     return parse_do_while(p);    // Do-while loop
    case TK_BREAK:  return parse_break(p);       // Break
    case TK_RETURN: return parse_ret(p);         // Return
    default:
        if (TYPE_SPECS[p->l.tk]) {
            return parse_decl(p);                // Declaration
        } else {
            return parse_expr_stmt(p);           // Expression
        }
    }
}

static Stmt * parse_block(Parser *p) {
    expect_tk(&p->l, '{');
    next_tk(&p->l);
    Stmt *block = NULL;
    Stmt **stmt = &block;
    Local *scope = p->locals;
    while (p->l.tk && p->l.tk != '}') {
        *stmt = parse_stmt(p);
        // Some 'stmt's returned by 'parse_stmt' contain multiple statements,
        // some contain nothing, so find the last one
        while (*stmt) {
            stmt = &(*stmt)->next;
        }
    }
    p->locals = scope;
    expect_tk(&p->l, '}');
    next_tk(&p->l);
    return block;
}


// ---- Module ----------------------------------------------------------------

static FnArg * parse_fn_decl_arg(Parser *p) {
    SignedType type = parse_decl_spec(p); // Type
    expect_tk(&p->l, TK_IDENT); // Name
    char *name = malloc((p->l.len + 1) * sizeof(char));
    strncpy(name, p->l.ident, p->l.len);
    name[p->l.len] = '\0';
    next_tk(&p->l);
    FnArg *arg = new_fn_arg();
    arg->local = def_local(p, name, type);
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

static FnDecl * parse_fn_decl(Parser *p) {
    FnDecl *decl = new_fn_decl();
    decl->return_type = parse_decl_spec(p);
    expect_tk(&p->l, TK_IDENT);
    decl->name = malloc((p->l.len + 1) * sizeof(char)); // Name
    strncpy(decl->name, p->l.ident, p->l.len);
    decl->name[p->l.len] = '\0';
    next_tk(&p->l);
    decl->args = parse_fn_decl_args(p);
    return decl;
}

static FnDef * parse_fn_def(Parser *p) {
    FnDef *def = new_fn_def();
    p->fn = def;
    // 'parse_fn_decl' creates new locals for the function arguments; create
    // a new scope so that they get deleted once we've parsed the function
    Local *scope = p->locals;
    def->decl = parse_fn_decl(p);
    def->body = parse_block(p);
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
