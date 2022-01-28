
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

// Returns an array of 'LiveRange' indexed by physical or virtual register,
// where the first REG_MAX values are physical register live ranges, and the
// rest are vregs (e.g., vreg 3 can be accessed by live_range[REG_MAX + 3])
LiveRange * analysis_liveness(AsmFn *fn);

int ranges_intersect(LiveRange r1, LiveRange r2);
void print_live_range(LiveRange ranges);
void print_live_ranges(AsmFn *fn, LiveRange *ranges);

#endif
