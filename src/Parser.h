
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

Module * parse(char *file);

#endif
