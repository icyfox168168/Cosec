
#include <stdio.h>

#include "RegisterAllocator.h"

#define IG_IDX(vreg1, vreg2) (vreg1 * fn->num_vregs + vreg2)

// Resources:
// * An overview of the graph colouring algorithm in the book:
//   Modern Compiler Implementation in C, Andrew W. Appel, Chapter 11
// * Another set of slides on the graph colouring algorithm:
//   http://web.cecs.pdx.edu/~mperkows/temp/register-allocation.pdf
// * Another article on the graph colouring algorithm:
//   https://www.lighterra.com/papers/graphcoloring/
// * A set of slides on liveness analysis:
//   https://proglang.informatik.uni-freiburg.de/teaching/compilerbau/2016ws/10-liveness.pdf
// * Useful practical information on implementing liveness analysis:
//   https://engineering.purdue.edu/~milind/ece573/2015fall/project/step7/step7.html

static int * interference_graph(AsmFn *fn, LiveRange *ranges) {
    int *graph = calloc(fn->num_vregs * fn->num_vregs, sizeof(int));

    // Build the graph by iterating over all the vregs twice
    for (int vreg1 = 0; vreg1 < fn->num_vregs; vreg1++) {
        if (ranges[vreg1].num_intervals == 0) {
            continue; // vreg1 isn't used
        }
        for (int vreg2 = 0; vreg2 < fn->num_vregs; vreg2++) {
            if (ranges[vreg2].num_intervals == 0) {
                continue; // vreg2 isn't used
            }
            if (ranges_intersect(ranges[vreg1], ranges[vreg2])) {
                graph[IG_IDX(vreg1, vreg2)] = 1;
                printf("vreg %d interferes with %d\n", vreg1, vreg2);
            }
        }
    }
    return graph;
}

void reg_alloc(AsmFn *fn, LiveRange *ranges) {
    if (fn->num_vregs <= 0 || !fn->last) {
        return; // No vregs to allocate, or the function is empty
    }
    print_live_ranges(fn, ranges);
    int *ig = interference_graph(fn, ranges);
}
