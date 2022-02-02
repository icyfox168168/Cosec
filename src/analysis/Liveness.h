
#ifndef COSEC_LIVENESS_H
#define COSEC_LIVENESS_H

#include "../Assembler.h"

// LIVENESS ANALYSIS -- runs on assembly instructions. Calculates the live
// range of each virtual register in the assembly.
//
// REQUIRES:
// * CFG analysis (for successor and predecessor blocks)

typedef struct interval {
    int start, end;
    struct interval *next;
} Interval;

// Each live range is a linked list of intervals; a 'LiveRange' refers to the
// head interval of the linked list
typedef Interval * LiveRange;

// In the returned array, the first REG_MAX are physical register live ranges,
// and the rest are vregs. E.g. vreg 3 is at live_range[REG_MAX + 3].
// Total size is REG_MAX + num_vregs
LiveRange * analyse_live_ranges(AsmFn *fn);

int ranges_intersect(LiveRange r1, LiveRange r2);
void print_live_range(LiveRange range);
void print_live_ranges(LiveRange *ranges, int num_vregs);

#endif
