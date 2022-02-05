
#ifndef COSEC_USECHAIN_H
#define COSEC_USECHAIN_H

#include "../IR.h"
#include "../Compiler.h"

// USE CHAIN ANALYSIS -- runs on IR instructions. For each instruction, finds
// all other IR instructions that use it, generating a linked list of uses.
// This is really simple thanks to the property of SSA form that means every
// variable has only ONE definition; we don't need to use the more complicated
// use-def chain structures in traditional compilers.
//
// Used by simple dead code elimination (DCE) optimisation to get rid of
// instructions with no uses, and by the assembler to tell when IR_LOADs have
// only a single use and can be folded into other assembly instructions.
//
// REQUIRES:
// * No other analysis passes are required

// Results are stored per-IR instruction (see IR.h)
void analyse_use_chains(Fn *fn);

#endif
