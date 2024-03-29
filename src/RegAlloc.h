
#ifndef COSEC_REGALLOC_H
#define COSEC_REGALLOC_H

#include "Assembler.h"

// REGISTER ALLOCATOR -- lowers virtual registers used throughout the assembly
// to physical ones. Uses the standard graph-colouring algorithm found in most
// classical compiler textbooks.
//
// Note: an important distinction in the code is the difference between reg,
// preg, and vreg:
// * preg: a PHYSICAL x86-64 register (e.g., rax, rcx, xmm2, etc.)
// * vreg: a VIRTUAL register created by the assembler that's yet to be
//   assigned to a physical register by the register allocator
// * reg: refers to either a preg or vreg

void reg_alloc(Fn *fn);

#endif
