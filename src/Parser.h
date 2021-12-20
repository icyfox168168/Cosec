
#ifndef COSEC_PARSER_H
#define COSEC_PARSER_H

#include "IR.h"
#include "Lexer.h"

typedef struct {
    IrIns *head;
} BB; // Basic block

typedef struct {
    Type return_type;
    char *name;
} FnDecl;

typedef struct {
    FnDecl *decl;
    BB *entry;
} FnDef;

typedef struct {
    FnDef *fns;
} Module;

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

Module * parse(char *file);

#endif
