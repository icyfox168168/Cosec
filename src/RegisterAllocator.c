
#include "RegisterAllocator.h"

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

void reg_alloc(AsmFn *fn, LiveRange *ranges) {
    if (fn->num_vregs <= 0 || !fn->last) {
        return; // No vregs to allocate, or the function is empty
    }
    print_live_ranges(fn, ranges);
}
