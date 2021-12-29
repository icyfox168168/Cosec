
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "Parser.h"

typedef struct {
    Type type;
    char *name;
    IrIns *alloc; // The IR_ALLOC instruction that created this local
} Local;

typedef struct {
    Lexer l;
    BB *bb;        // Current basic block
    IrIns **ins;   // Next instruction to emit
    Local *locals; // Local variables in scope
    int num_locals, max_locals;
} Parser;

static IrIns * new_ins(IrOpcode op) {
    IrIns *ins = malloc(sizeof(IrIns));
    ins->op = op;
    ins->next = NULL;
    ins->type.prim = T_void;
    ins->type.ptrs = 0;
    return ins;
}

static IrIns * emit(Parser *p, IrOpcode op) {
    IrIns *ins = new_ins(op);
    *p->ins = ins;
    p->ins = &ins->next;
    return ins;
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


// ---- Expressions -----------------------------------------------------------

typedef enum {
    PREC_NONE,
    PREC_COMMA,   // Comma operator
    PREC_ASSIGN,  // =, +=, -=, *=, /=, %=
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
    ['-'] = PREC_UNARY, // Negation
    ['~'] = PREC_UNARY, // Bitwise not
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
} ExprType;

typedef struct {
    ExprType type;
    union {
        IrIns *ins;   // For EXPR_INS
        Local *local; // For EXPR_LOCAL
    };
} Expr;

// Converts all expressions into EXPR_INS. Currently, this only involves
// emitting an IR_LOAD instruction for EXPR_LOCALs
static Expr discharge_expr(Parser *p,  Expr expr) {
    if (expr.type == EXPR_LOCAL) {
        IrIns *load = emit(p, IR_LOAD);
        load->l = expr.local->alloc;
        load->type = expr.local->type;
        Expr result;
        result.type = EXPR_INS;
        result.ins = load;
        return result;
    }
    return expr;
}

// Converts an expression into a condition (e.g., for if or while statements)
// by emitting a comparison operation if needed
static Expr to_cond(Parser *p, Expr expr) {
    expr = discharge_expr(p, expr);
    IrOpcode op = expr.ins->op;
    if (op >= IR_EQ && op <= IR_UGE) {
        return expr; // Already a condition
    }
    IrIns *zero = emit(p, IR_KI32);
    zero->ki32 = 0;
    zero->type.prim = T_i32;
    zero->type.ptrs = 0;

    IrIns *cmp = emit(p, IR_NEQ);
    cmp->l = expr.ins;
    cmp->r = zero;
    cmp->type.prim = T_i32;
    cmp->type.ptrs = 0;

    Expr result;
    result.type = EXPR_INS;
    result.ins = cmp;
    return result;
}

static Expr parse_const_int(Parser *p) {
    expect_tk(&p->l, TK_NUM);
    long value = p->l.num;
    next_tk(&p->l);
    IrIns *k = emit(p, IR_KI32);
    k->ki32 = (int32_t) value;
    k->type.prim = T_i32;
    k->type.ptrs = 0;
    Expr result;
    result.type = EXPR_INS;
    result.ins = k;
    return result;
}

static Expr parse_local(Parser *p) {
    expect_tk(&p->l, TK_IDENT);
    char *name = p->l.ident;
    int len = p->l.len;
    Local *local = NULL;
    for (int i = 0; i < p->num_locals; i++) {
        if (len == strlen(p->locals[i].name) && strncmp(name, p->locals[i].name, len) == 0) {
            local = &p->locals[i];
            break;
        }
    }
    if (!local) { // Check the local exists
        printf("undeclared variable\n");
        exit(1);
    }
    next_tk(&p->l);
    Expr result;
    result.type = EXPR_LOCAL;
    result.local = local;
    return result;
}

static Expr parse_subexpr(Parser *p, Prec min_prec); // Forward declaration

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
    operand = discharge_expr(p, operand);
    IrIns *zero = emit(p, IR_KI32); // -a is equivalent to '0 - a'
    zero->ki32 = 0;
    IrIns *operation = emit(p, IR_SUB);
    operation->l = zero;
    operation->r = operand.ins;
    operation->type = operand.ins->type;
    Expr result;
    result.type = EXPR_INS;
    result.ins = operation;
    return result;
}

static Expr parse_bit_not(Parser *p, Expr operand) {
    operand = discharge_expr(p, operand);
    IrIns *neg1 = emit(p, IR_KI32); // ~a is equivalent to 'a ^ -1'
    neg1->ki32 = -1;
    IrIns *operation = emit(p, IR_XOR);
    operation->l = operand.ins;
    operation->r = neg1;
    operation->type = operand.ins->type;
    Expr result;
    result.type = EXPR_INS;
    result.ins = operation;
    return result;
}

static Expr parse_unary(Parser *p) {
    Tk unop = p->l.tk;
    if (UNOP_PREC[unop]) {
        next_tk(&p->l); // Skip the unary operator
        Expr operand = parse_subexpr(p, UNOP_PREC[unop]);
        switch (unop) {
            case '-': return parse_neg(p, operand);
            case '~': return parse_bit_not(p, operand);
            default: UNREACHABLE();
        }
    } else {
        return parse_operand(p);
    }
}

static Expr parse_operation(Parser *p, Tk binop, Expr left, Expr right) {
    left = discharge_expr(p, left);
    right = discharge_expr(p, right);

    // 'left' and 'right' should have the same type
    assert(left.ins->type.prim == right.ins->type.prim);
    assert(left.ins->type.ptrs == right.ins->type.ptrs);

    IrIns *operation = emit(p, BINOP_OPCODES[binop]);
    operation->l = left.ins;
    operation->r = right.ins;
    operation->type = left.ins->type; // Same as 'right.ins->type'
    Expr result;
    result.type = EXPR_INS;
    result.ins = operation;
    return result;
}

static Expr parse_assign(Parser *p, Tk binop, Expr left, Expr right) {
    if (binop != '=') {
        right = parse_operation(p, binop, left, right);
    }
    assert(left.type == EXPR_LOCAL); // Can only assign to lvalues
    right = discharge_expr(p, right);
    IrIns *store = emit(p, IR_STORE);
    store->l = left.local->alloc;
    store->r = right.ins;
    store->type = left.local->type;
    return right; // Assignment evaluates to its right operand
}

static Expr parse_binary(Parser *p, Tk binop, Expr left, Expr right) {
    switch (binop) {
    case '=': case TK_ADD_ASSIGN: case TK_SUB_ASSIGN:
    case TK_MUL_ASSIGN: case TK_DIV_ASSIGN: case TK_MOD_ASSIGN:
    case TK_AND_ASSIGN: case TK_OR_ASSIGN: case TK_XOR_ASSIGN:
    case TK_LSHIFT_ASSIGN: case TK_RSHIFT_ASSIGN:
        return parse_assign(p, binop, left, right);
    default:
        return parse_operation(p, binop, left, right);
    }
}

static Expr parse_subexpr(Parser *p, Prec min_prec) {
    Expr left = parse_unary(p);
    while (BINOP_PREC[p->l.tk] > min_prec) {
        Tk binop = p->l.tk;
        next_tk(&p->l); // Skip the operator

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
        expr = discharge_expr(p, expr);
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
    next_tk(&p->l);
    expect_tk(&p->l, '(');
    next_tk(&p->l);
    Expr cond = parse_expr(p);
    cond = to_cond(p, cond);
    expect_tk(&p->l, ')');
    next_tk(&p->l);
    IrIns *cond_br = emit(p, IR_CONDBR);
    cond_br->cond = cond.ins;

    BB *body = new_bb();
    cond_br->true = body;
    p->bb->next = body;
    p->bb = body;
    p->ins = &body->ir_head;
    parse_body(p);
    IrIns *end_br = emit(p, IR_BR); // End the body with a branch to 'after'

    BB *after = new_bb();
    cond_br->false = after;
    end_br->br = after;
    p->bb->next = after;
    p->bb = after;
    p->ins = &after->ir_head;
}

static void parse_ret(Parser *p) {
    expect_tk(&p->l, TK_RETURN);
    next_tk(&p->l);
    IrIns *value = NULL;
    if (p->l.tk != ';') { // If we're returning something
        Expr expr = parse_expr(p);
        expr = discharge_expr(p, expr);
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
        case TK_INT:    parse_decl(p); break;          // Declaration
        case TK_RETURN: parse_ret(p); break;           // Return
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
            bb->ir_head = new_ins(IR_RET0);
            return;
        }
        while (end->next) { end = end->next; } // Find the last instruction
        // The last instruction in a basic block must be a branch or ret
        if (end->op != IR_BR && end->op != IR_CONDBR &&
                end->op != IR_RET0 && end->op != IR_RET1) {
            end->next = new_ins(IR_RET0);
        }
    }
}

static FnDef * parse_fn_def(Parser *p) {
    FnDef *fn = malloc(sizeof(FnDef));
    fn->entry = new_bb();
    p->bb = fn->entry;
    p->ins = &fn->entry->ir_head;
    int num_locals = p->num_locals; // 'parse_fn_args' creates new locals
    fn->decl = parse_fn_decl(p); // Declaration
    parse_braced_block(p); // Body
    p->num_locals = num_locals; // Get rid of the function's arguments
    ensure_ret(fn);
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
    Parser p;
    p.l = new_lexer(source);
    next_tk(&p.l); // Lex the first token in the file
    p.bb = NULL;
    p.ins = NULL;
    p.num_locals = 0;
    p.max_locals = 8;
    p.locals = malloc(sizeof(Local) * p.max_locals);
    Module *module = parse_module(&p);
    free(source);
    free(p.locals);
    return module;
}
