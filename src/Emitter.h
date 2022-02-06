
#ifndef COSEC_EMITTER_H
#define COSEC_EMITTER_H

#include <stdio.h>

#include "Assembler.h"

// EMITTER -- writes the generated assembly code in NASM format to an output
// file. The output assembly code can then be assembled using NASM and linked
// (using any linker) to produce an executable.
//
// The encoder is the last step in the compiler pipeline. More complex encoders
// are planned in the future, including one that implements the x86-64
// instruction encoding.

void emit_nasm(Module *m, FILE *out);

#endif
