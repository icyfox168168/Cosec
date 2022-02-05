
#ifndef COSEC_COMPILER_H
#define COSEC_COMPILER_H

#include "IR.h"
#include "Parser.h"

// COMPILER -- converts a well-formed abstract syntax tree (AST) to SSA IR.
// The SSA IR is where all the compiler optimisations take place.
//
// Since C is a relatively simple language, it's actually possible for us to
// get rid of the AST all together and merge its construction into SSA IR
// generation. Although possible, it's not a good idea - having the AST
// simplifies the IR generation logic sooo much and makes for cleaner code.

Module * compile(AstModule *ast);

#endif
