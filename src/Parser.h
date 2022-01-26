
#ifndef COSEC_PARSER_H
#define COSEC_PARSER_H

#include "IR.h"
#include "Lexer.h"

typedef struct {
    Type return_type;
    char *name;
} FnDecl;

typedef struct {
    FnDecl *decl;
    BB *entry, *last;
    int num_bbs;
} FnDef;

typedef struct {
    FnDef *fn; // Only one function for the moment
} Module;

Module * parse(char *file);

#endif
