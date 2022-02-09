
#ifndef COSEC_DEBUG_H
#define COSEC_DEBUG_H

#include "Compiler.h"

// DEBUG -- some useful functions for printing the output of the parser and
// compiler to stdout.

void print_ast(FnDef *fn);
void print_ir(Fn *fn);

#endif
