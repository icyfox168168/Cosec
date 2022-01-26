
#ifndef COSEC_REGISTERALLOCATOR_H
#define COSEC_REGISTERALLOCATOR_H

#include "IR.h"
#include "Assembler.h"

typedef struct liveness_info {
    int *in;  // vregs live at start of BB (hash set indexed by vreg)
} LivenessInfo;

// REGISTER ALLOCATOR -- lowers virtual registers used throughout the assembly
// into physical ones. Uses the standard graph-colouring algorithm found in
// most classical compiler textbooks.
//
// After 'reg_alloc', there will no longer be any assembly instructions with
// type 'OP_VREG'.

void reg_alloc(AsmFn *fn);

#endif
