
#ifndef COSEC_REGALLOC_H
#define COSEC_REGALLOC_H

#include "IR.h"
#include "Assembler.h"
#include "analysis/Liveness.h"

// REGISTER ALLOCATOR -- lowers virtual registers used throughout the assembly
// to physical ones. Uses the standard graph-colouring algorithm found in most
// classical compiler textbooks.
//
// Note: an important distinction in the code is the difference between reg,
// preg, and vreg:
// * preg: a PHYSICAL x86-64 register (e.g., rax, rcx, r9, etc.)
// * vreg: a VIRTUAL register created by the assembler that's yet to be
//   assigned to a physical register by the register allocator
// * reg: refers to either a preg or vreg
//
// After 'reg_alloc', there will no longer be any assembly instructions with
// type 'OP_VREG'.

void reg_alloc(Fn *fn, LiveRange *ranges);

#endif
