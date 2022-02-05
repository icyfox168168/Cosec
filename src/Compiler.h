
#ifndef COSEC_COMPILER_H
#define COSEC_COMPILER_H

#include "IR.h"
#include "Parser.h"

// COMPILER -- converts a well-formed abstract syntax tree (AST) to SSA IR.
// The SSA IR is where all the compiler optimisations take place.

Module * compile(AstModule *ast);

#endif
