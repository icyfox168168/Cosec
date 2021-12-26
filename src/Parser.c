
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Parser.h"

typedef struct {
    Type type;
    char *name;
    IrIns *alloc; // Reference to IR_ALLOC instruction that created this local
} Local;

typedef struct {
    Lexer l;
    FnDef *fn; // Current function being parsed
    IrIns **ins; // Next instruction to emit
    Local *locals; // Local variables in scope
    int num_locals, max_locals;
} Parser;

static IrIns * emit(Parser *p, IrOp op) {
    IrIns *ins = malloc(sizeof(IrIns));
    ins->op = op;
    ins->next = NULL;
    ins->type.prim = T_void;
    ins->type.ptrs = 0;
    *p->ins = ins;
    p->ins = &ins->next;
    return ins;
}

static void def_local(Parser *p, Local local) {
    // TODO: compare against function definitions too!
    for (int i = p->num_locals - 1; i >= 0; i--) { // Check local isn't already defined
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


// ---- Expressions

typedef enum {
    PREC_NONE,
    PREC_COMMA,   // Comma operator
    PREC_ASSIGN,  // =, +=, -=, *=, /=, %=
    PREC_OR,      // ||
    PREC_AND,     // &&
    PREC_EQ,      // ==, !=
    PREC_REL,     // <, >, <=, >=
    PREC_ADD,     // +, -
    PREC_MUL,     // *, /, %
    PREC_UNARY,   // ++, -- (prefix), -, + (unary), !, ~, type casts, *, &, sizeof
    PREC_POSTFIX, // ++, -- (postfix), function calls, array indexes, member access (. and ->)
} Prec;

static Prec UNOP_PREC[TK_LAST] = {
    ['-'] = PREC_UNARY, // Negation
};

static Prec BINOP_PREC[TK_LAST] = {
    ['+'] = PREC_ADD, // Addition
    ['-'] = PREC_ADD, // Subtraction
    ['*'] = PREC_MUL, // Multiplication
    ['/'] = PREC_MUL, // Division
    ['%'] = PREC_MUL, // Modulo
};

static int IS_RIGHT_ASSOC[TK_LAST] = {
    ['='] = 1, // Assignment is right associative
};

static IrOp BINOP_OPCODES[TK_LAST] = {
    ['+'] = IR_ADD,
    ['-'] = IR_SUB,
    ['*'] = IR_MUL,
    ['/'] = IR_DIV,
    ['%'] = IR_MOD,
};

static IrIns * parse_const_int(Parser *p) {
    expect_tk(&p->l, TK_NUM);
    long value = p->l.num;
    next_tk(&p->l);
    IrIns *expr = emit(p, IR_KI32);
    expr->ki32 = (int32_t) value;
    expr->type.prim = T_i32;
    expr->type.ptrs = 0;
    return expr;
}

static IrIns * parse_local(Parser *p) {
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
    IrIns *load = emit(p, IR_LOAD);
    load->l = local->alloc;
    load->type = local->alloc->type;
    load->type.ptrs -= 1; // Loading DEREFERENCES a pointer
    return load;
}

static IrIns * parse_subexpr(Parser *p, Prec min_prec); // Forward declaration

static IrIns * parse_braced_subexpr(Parser *p) {
    expect_tk(&p->l, '(');
    next_tk(&p->l);
    IrIns *expr = parse_subexpr(p, PREC_NONE);
    expect_tk(&p->l, ')');
    next_tk(&p->l);
    return expr;
}

static IrIns * parse_operand(Parser *p) {
    switch (p->l.tk) {
        case TK_NUM:   return parse_const_int(p);
        case TK_IDENT: return parse_local(p);
        case '(':      return parse_braced_subexpr(p);
        default:       printf("expected expression\n"); exit(1);
    }
}

static IrIns * parse_unary(Parser *p) {
    Token unop = p->l.tk;
    if (UNOP_PREC[unop]) {
        next_tk(&p->l); // Skip the unary operator
        IrIns *operand = parse_subexpr(p, UNOP_PREC[unop]);
        switch (unop) {
        case '-': {
            IrIns *zero = emit(p, IR_KI32);
            zero->ki32 = 0;
            IrIns *operation = emit(p, IR_SUB);
            operation->l = zero;
            operation->r = operand;
            operation->type = operand->type;
            return operation;
        }
        default: return NULL; // Doesn't happen
        }
    } else {
        return parse_operand(p);
    }
}

static IrIns * parse_binary(Parser *p, Token binop, IrIns *left, IrIns *right) {
    IrIns *operation = emit(p, BINOP_OPCODES[binop]);
    operation->l = left;
    operation->r = right;
    operation->type = left->type; // Should be the same as 'right'
    return operation;
}

static IrIns * parse_subexpr(Parser *p, Prec min_prec) {
    IrIns *left = parse_unary(p);
    while (BINOP_PREC[p->l.tk] > min_prec) {
        Token binop = p->l.tk;
        next_tk(&p->l); // Skip the binary operator
        IrIns *right = parse_subexpr(p, BINOP_PREC[binop] - IS_RIGHT_ASSOC[binop]);
        left = parse_binary(p, binop, left, right);
    }
    return left;
}

static IrIns * parse_expr(Parser *p) {
    return parse_subexpr(p, PREC_NONE);
}


// ---- Statements

static int is_decl_spec(Token tk) {
    return tk == TK_INT;
}

static Type parse_decl_spec(Parser *p) {
    expect_tk(&p->l, TK_INT); // The only type available for now
    next_tk(&p->l);
    Type type = {.prim = T_i32, .ptrs = 0};
    return type;
}

static void parse_ret(Parser *p) {
    expect_tk(&p->l, TK_RETURN);
    next_tk(&p->l);
    IrIns *value = NULL;
    if (p->l.tk != ';') {
        value = parse_expr(p);
    }
    if (value) {
        IrIns *ret = emit(p, IR_RET1);
        ret->l = value;
    } else {
        emit(p, IR_RET0);
    }
}

static void parse_decl(Parser *p) {
    Type type = parse_decl_spec(p); // Type
    expect_tk(&p->l, TK_IDENT); // Name
    char *name = malloc((p->l.len + 1) * sizeof(char));
    strncpy(name, p->l.ident, p->l.len);
    name[p->l.len] = '\0';
    next_tk(&p->l);

    IrIns *alloc = emit(p, IR_ALLOC);
    alloc->type = type;
    alloc->type.ptrs += 1; // The result is a POINTER to the value
    if (p->l.tk != ';') { // Definition, not just a declaration
        expect_tk(&p->l, '=');
        next_tk(&p->l);
        IrIns *value = parse_expr(p); // Value
        IrIns *store = emit(p, IR_STORE);
        store->l = alloc;
        store->r = value;
        store->type = value->type;
    }
    Local local = {.name = name, .type = type, .alloc = alloc};
    def_local(p, local);
}

static void parse_stmt(Parser *p) {
    switch (p->l.tk) {
    case ';': next_tk(&p->l); return;
    case TK_RETURN: parse_ret(p); break;
    default:
        if (is_decl_spec(p->l.tk)) {
            parse_decl(p);
        } else {
            parse_expr(p); // Discard the result
        }
        break;
    }
    expect_tk(&p->l, ';');
    next_tk(&p->l);
}

static void parse_block(Parser *p) {
    while (p->l.tk != '\0' && p->l.tk != '}') {
        parse_stmt(p);
    }
}


// ---- Top Level Module

static void parse_fn_arg(Parser *p) {
    Type arg_type = parse_decl_spec(p); // Type
    expect_tk(&p->l, TK_IDENT); // Name
    char *name = malloc((p->l.len + 1) * sizeof(char));
    strncpy(name, p->l.ident, p->l.len);
    name[p->l.len] = '\0';
    next_tk(&p->l);

    IrIns *farg = emit(p, IR_FARG); // Define the argument
    farg->type = arg_type;
    Local local = {.name = name, .type = arg_type, .alloc = NULL}; // Create a local
    def_local(p, local);
}

static void parse_fn_args(Parser *p) {
    while (p->l.tk != '\0' && p->l.tk != ')') {
        parse_fn_arg(p);
        if (p->l.tk == ',') { // Check for another argument
            next_tk(&p->l);
            continue;
        } else {
            break;
        }
    }
    int idx = 0;
    for (IrIns *farg = p->fn->entry->head; farg && farg->op == IR_FARG; farg = farg->next) {
        IrIns *alloc = emit(p, IR_ALLOC); // Create IR_ALLOC for each argument
        alloc->type = farg->type;
        IrIns *store = emit(p, IR_STORE);
        store->l = alloc;
        store->r = farg;
        store->type = farg->type;
        p->locals[idx++].alloc = alloc;
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

static FnDef * parse_fn_def(Parser *p) {
    FnDef *fn = malloc(sizeof(FnDef));
    fn->entry = malloc(sizeof(BB));
    fn->entry->next = NULL;
    fn->entry->head = NULL;

    p->fn = fn; // Needs to happen before parsing the declaration, since function arguments emit instructions
    p->ins = &fn->entry->head;
    fn->decl = parse_fn_decl(p); // Declaration
    expect_tk(&p->l, '{'); // Body
    next_tk(&p->l);
    parse_block(p);
    expect_tk(&p->l, '}');
    next_tk(&p->l);
    return fn;
}

static Module * parse_module(Parser *p) {
    Module *module = malloc(sizeof(Module));
    module->fns = parse_fn_def(p);
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
    next_tk(&p.l);
    p.fn = NULL;
    p.ins = NULL;
    p.num_locals = 0;
    p.max_locals = 8;
    p.locals = malloc(sizeof(Local) * p.max_locals);
    Module *module = parse_module(&p);
    free(source);
    free(p.locals);
    return module;
}
