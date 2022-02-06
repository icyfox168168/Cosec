
#ifndef COSEC_LIVENESS_H
#define COSEC_LIVENESS_H

#include "../Assembler.h"

// LIVENESS ANALYSIS -- runs on assembly instructions. Calculates the live
// range of each virtual register in the assembly.
//
// REQUIRES:
// * CFG analysis (for successor and predecessor blocks)

// All assembly instructions are numbered across basic blocks so that live
// ranges can be referred to by a union of intervals [start, end]
typedef struct interval {
    int start, end; // INCLUSIVE of instructions at 'start' and 'end'
    struct interval *next;
} Interval;

// Each live range is a linked list of intervals; a 'LiveRange' refers to the
// head interval of the linked list
typedef Interval * LiveRange;

// In the returned array, the first LAST_PREG are physical register live ranges,
// and the rest are vregs. E.g. vreg 3 is at live_range[LAST_PREG + 3].
// Total size is LAST_PREG + num_regs
LiveRange * analyse_live_ranges(Fn *fn);

int ranges_intersect(LiveRange r1, LiveRange r2);
LiveRange range_intersection(LiveRange r1, LiveRange r2);

void print_live_range(LiveRange range);
void print_live_ranges(LiveRange *ranges, int num_regs);

#endif
