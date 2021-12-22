
#ifndef COSEC_ENCODER_H
#define COSEC_ENCODER_H

#include <stdio.h>

#include "Assembler.h"

/* The ENCODER writes the generated assembly code in NASM format to an output
 * file. The output assembly code can then be assembled using NASM and linked
 * (using any other built-in linker) to produce an executable.
 *
 * The encoder is the last step in the compiler pipeline. More complex encoders
 * are planned in the future, including one that implements the x86-64
 * instruction encoding.
 */

static char *REG_NAMES[] = {
#define X(_, str, __) str,
    X86_REGS
#undef X
};

static char *X86_OPCODE_NAMES[] = {
#define X(_, str, __) str,
    X86_OPCODES
#undef X
};

static int X86_OPCODE_NARGS[] = {
#define X(_, __, nargs) nargs,
    X86_OPCODES
#undef X
};

void encode_nasm(AsmModule *m, FILE *out);

#endif
