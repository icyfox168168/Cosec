
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Parser.h"

static IrIns * emit(Parser *p, IrOp op) {
    IrIns *ins = malloc(sizeof(IrIns));
    ins->op = op;
    ins->next = NULL;
//    ins->prev = *p->ins; TODO
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

static IrIns * parse_expr(Parser *p) {
    expect_tk(&p->l, TK_NUM);
    IrIns *num = emit(p, IR_KI32);
    num->ki32 = (int32_t) p->l.num;
    next_tk(&p->l);
    return num;
}


// ---- Statements

static Type parse_decl_spec(Parser *p) {
    expect_tk(&p->l, TK_INT); // The only type available for now
    next_tk(&p->l);
    return T_i32;
}

static void parse_ret(Parser *p) {
    expect_tk(&p->l, TK_RETURN);
    next_tk(&p->l);
    emit(p, IR_RET);
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
    if (p->l.tk != ';') { // Definition, not just a declaration
        expect_tk(&p->l, '=');
        next_tk(&p->l);
        IrIns *value = parse_expr(p); // Value
        IrIns *store = emit(p, IR_STORE);
        store->dest = alloc;
        store->src = value;
    }
    Local local = {.name = name, .type = type, .alloc = alloc};
    def_local(p, local);
}

static void parse_stmt(Parser *p) {
    switch (p->l.tk) {
        case ';': next_tk(&p->l); return;
        case TK_RETURN: parse_ret(p); break;
        default: parse_decl(p); break;
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

static void parse_fn_args(Parser *p) {
    while (p->l.tk != '\0' && p->l.tk != ')') {
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
        store->dest = alloc;
        store->src = farg;
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
