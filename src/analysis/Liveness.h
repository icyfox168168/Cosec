
#ifndef COSEC_LIVENESS_H
#define COSEC_LIVENESS_H

#include "../Assembler.h"

// LIVENESS ANALYSIS -- runs on assembly instructions. Calculates the live
// range of each virtual register in the assembly.
//
// REQUIRES:
// * CFG analysis (for successors and predecessors)

typedef struct {
    int start, end;
} Interval;

typedef struct {
    Interval *intervals;
    int num_intervals, max_intervals;
} LiveRange;

typedef struct {
    LiveRange *vregs; // Virtual registers
    LiveRange *pregs; // Physical registers
} LiveRanges;

// Returns an array of 'LiveRange' indexed by vreg. E.g., live_ranges[3] is the
// live range for vreg 3.
LiveRanges analysis_liveness(AsmFn *fn);

int ranges_intersect(LiveRange r1, LiveRange r2);
void print_live_range(LiveRange ranges);
void print_live_ranges(AsmFn *fn, LiveRanges ranges);

#endif
