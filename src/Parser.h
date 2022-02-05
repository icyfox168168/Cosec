
#ifndef COSEC_PARSER_H
#define COSEC_PARSER_H

#include "IR.h"

// PARSER -- builds an abstract syntax tree (AST, see 'IR.h') from C source
// code. Some transformations (e.g., type filling, which propagates the types
// for expressions through expression trees) and error checking (e.g.,
// incorrect syntax, undefined locals) are performed on the AST before it's
// compiled to SSA IR.

AstModule * parse(char *file);

#endif
