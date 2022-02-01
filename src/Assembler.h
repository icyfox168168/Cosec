
#ifndef COSEC_ASSEMBLER_H
#define COSEC_ASSEMBLER_H

#include "Parser.h"

// ASSEMBLER -- lowers the SSA IR into target-specific machine code
// instructions. Target-specific optimisations can then be made to the
// generated assembly code (e.g., peep-hole optimisations not possible on the
// SSA IR). Variables are still modelled by virtual registers in the assembly,
// which are later lowered to physical registers by the register allocator.

typedef struct asm_fn {
    struct asm_fn *next; // Linked list of functions
    BB *entry, *last;    // Linked list of basic blocks
    int num_vregs;
} AsmFn;

typedef struct {
    AsmFn *fns;  // Linked list of functions
    AsmFn *main; // NULL if this module has no 'main' function
} AsmModule;

AsmModule * assemble(Module *ir_mod);

#endif
