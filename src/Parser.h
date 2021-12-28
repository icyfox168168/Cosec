
#ifndef COSEC_PARSER_H
#define COSEC_PARSER_H

#include "IR.h"
#include "Lexer.h"

typedef struct bb {
    int label;
    IrIns *head; // The last instruction (the terminator) MUST be a branch (BR, CONDBR) or return (RET0, RET1)
    int mark;
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

// Iterate over the basic blocks in a function via depth-first search (DFS).
// Passes 'data' to the 'pred' function.
void iterate_bb(FnDef *fn, void (*pred)(BB *, void *), void *data);

#endif
