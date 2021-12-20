
#ifndef COSEC_DEBUG_H
#define COSEC_DEBUG_H

#include "IR.h"
#include "Parser.h"

static char *IR_TYPE_NAMES[] = {
#define X(name) #name,
    IR_TYPES
#undef X
};

static char *IR_OPCODE_NAMES[] = {
#define X(opcode, nargs) #opcode,
    IR_OPCODES
#undef X
};

static int IR_OPCODE_NARGS[] = {
#define X(opcode, nargs) nargs,
    IR_OPCODES
#undef X
};

void print_bb(BB *bb);

#endif
