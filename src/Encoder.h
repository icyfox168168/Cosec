
#ifndef COSEC_ENCODER_H
#define COSEC_ENCODER_H

#include <stdio.h>

#include "Assembler.h"

// ENCODER -- writes the generated assembly code in NASM format to an output
// file. The output assembly code can then be assembled using NASM and linked
// (using any linker) to produce an executable.
//
// The encoder is the last step in the compiler pipeline. More complex encoders
// are planned in the future, including one that implements the x86-64
// instruction encoding.

void encode_nasm(AsmModule *m, FILE *out);

#endif
