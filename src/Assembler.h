
#ifndef COSEC_ASSEMBLER_H
#define COSEC_ASSEMBLER_H

#include "Compiler.h"

// ASSEMBLER -- lowers the SSA IR into target-specific machine code
// instructions. Target-specific optimisations can then be made to the
// generated assembly code (e.g., peep-hole optimisations not possible on the
// SSA IR). Variables are still modelled by virtual registers in the assembly,
// which are later lowered to physical registers by the register allocator.
//
// REQUIRES:
// * Use chain analysis (for IR_LOAD folding)

void assemble(Module *mod);

#endif
