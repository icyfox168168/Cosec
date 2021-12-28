
#ifndef COSEC_PARSER_H
#define COSEC_PARSER_H

#include "IR.h"
#include "Lexer.h"

typedef struct bb {
    IrIns *head; // The last instruction (the terminator) MUST be a branch (BR, CONDBR) or return (RET0, RET1)
} BB;

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
