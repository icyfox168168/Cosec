
#include <stdio.h>
#include <string.h>

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

typedef struct {
    int start, end;
} Interval;

typedef struct {
    Interval *intervals;
    int num_intervals, max_intervals;
} LiveRange;

// Adds 'suc' as a successor to the basic block 'pre', and 'pre' as a
// predecessor to 'suc'
static void add_pre_and_suc(BB *pred, BB *succ) {
    if (succ->num_pred >= succ->max_pred) {
        succ->max_pred *= 2;
        succ->predecessors = realloc(succ->predecessors,
                                 sizeof(BB *) * succ->max_pred);
    }
    pred->successors[pred->num_succ++] = succ; // Add successor
    succ->predecessors[succ->num_pred++] = pred; // Add predecessor
}

// Calculates the predecessor and successor blocks for each basic block in the
// function, populating the 'predecessors' and 'successors' arrays in each block
static void calc_pre_and_suc(AsmFn *fn) {
    // Allocate the predecessors and successors arrays
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        bb->max_pred = 4; // Could be an unlimited number of predecessors
        bb->num_pred = 0;
        bb->predecessors = malloc(sizeof(BB *) * bb->max_pred);
        bb->num_succ = 0; // Can ONLY have a max of 2 successors
    }

    for (BB *bb = fn->entry; bb; bb = bb->next) {
        AsmIns *last = bb->asm_last;
        if (last->op == X86_JMP) { // Unconditional jump
            add_pre_and_suc(bb, last->l.bb); // One successor
        } else if (last->op >= X86_JE && last->op <= X86_JAE) { // Conditional
            add_pre_and_suc(bb, last->l.bb); // Two successors
            add_pre_and_suc(bb, bb->next);
        } else if (bb->next && last->op != X86_RET) {
            // Not the last BB and doesn't end with RET
            add_pre_and_suc(bb, bb->next);
        } // Otherwise, no successors
    }
}

static void add_program_point(LiveRange *range, int point) {
    // Try to find an interval we can extend
    for (int i = 0; i < range->num_intervals; i++) {
        Interval *interval = &range->intervals[i];
        if (point >= interval->start && point < interval->end) {
            return; // Already inside an interval
        } else if (point == interval->start - 1) {
            interval->start--; // Right before an existing interval
            return;
        } else if (point == interval->end) {
            interval->end++; // Right after an existing interval
            return;
        }
    }

    // Otherwise, create a new interval
    if (range->num_intervals >= range->max_intervals) {
        range->max_intervals *= 2;
        range->intervals = realloc(range->intervals,
                                   sizeof(Interval) * range->max_intervals);
    }
    Interval new_interval = {point, point + 1};
    range->intervals[range->num_intervals++] = new_interval;
}

// Returns true if the instruction defines its left operand
static int defs_left(AsmIns *ins) {
    AsmOpcode op = ins->op;
    return (op >= X86_MOV && op <= X86_LEA) ||
          (op >= X86_ADD && op <= X86_MUL) ||
          (op >= X86_AND && op <= X86_SAR) ||
          (op >= X86_SETE && op <= X86_SETAE) ||
          (op == X86_POP);
}

// Returns true if an instruction uses its left operand
static int uses_left(AsmIns *ins) {
    // movs and setxx don't use their left argument, they only define it
    AsmOpcode op = ins->op;
    return X86_OPCODE_NARGS[op] >= 1 &&
        !(op >= X86_MOV && op <= X86_LEA) &&
        !(op >= X86_SETE && op <= X86_SETAE) &&
        op != X86_POP;
}

// Returns true if an instruction uses its right operand
static int uses_right(AsmIns *ins) {
    // If it has 2 arguments, then it uses its right operand
    return X86_OPCODE_NARGS[ins->op] >= 2;
}

// Returns 1 if the live-in list for the BB was changed
//
// Live out is the union of all the live-in lists for all successors of the
// basic block
//
// Live in is everything that's used inside this basic block, plus everything
// that's live out minus what's defined in this block
// live in = { use(bb) } union { live out(bb) \ defn(bb) }
static int live_ranges_for_bb(AsmFn *fn, LiveRange *ranges, BB *bb) {
    // Keep track of vregs that are live at each program point
    int live[fn->num_vregs];
    memset(live, 0, sizeof(int) * fn->num_vregs);

    // Find everything that's live out for the BB
    for (int i = 0; i < bb->num_succ; i++) {
        BB *succ = bb->successors[i];
        for (int vreg = 0; vreg < fn->num_vregs; vreg++) {
            if (succ->live_in[vreg]) {
                live[vreg] = 1;
            }
        }
    }

    // Iterate over all instructions in reverse order
    for (AsmIns *ins = bb->asm_last; ins; ins = ins->prev) {
        // Vregs used are now live
        if ((uses_left(ins) || defs_left(ins)) && ins->l.type == OP_VREG) {
            live[ins->l.vreg] = 1;
        }
        if (uses_right(ins) && ins->r.type == OP_VREG) {
            live[ins->r.vreg] = 1;
        }

        // Add the live vregs to the ranges
        for (int vreg = 0; vreg < fn->num_vregs; vreg++) {
            if (live[vreg]) {
                add_program_point(&ranges[vreg], ins->idx);
            }
        }

        // Vregs defined are no longer live before the current instruction
        if (defs_left(ins) && ins->l.type == OP_VREG) {
            live[ins->l.vreg] = 0;
        }
    }

    // Everything left over is now live-in
    int changed = 0;
    for (int vreg = 0; vreg < fn->num_vregs; vreg++) {
        if (live[vreg]) {
            changed |= !bb->live_in[vreg];
            bb->live_in[vreg] = 1;
        }
    }
    return changed;
}

static LiveRange * live_ranges(AsmFn *fn) {
    LiveRange *ranges = malloc(sizeof(LiveRange) * fn->num_vregs);
    for (int vreg = 0; vreg < fn->num_vregs; vreg++) {
        ranges[vreg].num_intervals = 0;
        ranges[vreg].max_intervals = 4;
        ranges[vreg].intervals = malloc(sizeof(Interval) * ranges->max_intervals);
    }

    // Allocate the live-in arrays for each basic block
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        bb->live_in = calloc(fn->num_vregs, sizeof(int));
    }

    // Create a worklist of basic blocks
    BB **worklist = malloc(sizeof(BB *) * fn->num_bbs);
    int num_worklist = 0;
    worklist[num_worklist++] = fn->last; // Start with the LAST BB in the fn

    // Iterate until the worklist is empty
    while (num_worklist > 0) {
        BB *bb = worklist[--num_worklist]; // Pull the last BB off the worklist
        int updated_live_in = live_ranges_for_bb(fn, ranges, bb);
        if (updated_live_in) { // If the live-in list was changed
            // Add all the predecessors of this block to the worklist
            for (int pred_idx = 0; pred_idx < bb->num_pred; pred_idx++) {
                worklist[num_worklist++] = bb->predecessors[pred_idx];
            }
        }
    }
    return ranges;
}

static LiveRange * liveness(AsmFn *fn) {
    calc_pre_and_suc(fn);
    return live_ranges(fn);
}

// Assigns a unique number to each of the instructions across all the basic
// blocks in a function, used for storing live ranges
static void number_ins(AsmFn *fn) {
    int idx = 0;
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        for (AsmIns *ins = bb->asm_head; ins; ins = ins->next) {
            ins->idx = idx++;
        }
    }
}

void reg_alloc(AsmFn *fn) {
    if (fn->num_vregs <= 0 || !fn->last) {
        return; // No vregs to allocate, or the function is empty
    }
    number_ins(fn);
    LiveRange *ranges = liveness(fn);
    for (int vreg = 0; vreg < fn->num_vregs; vreg++) {
        if (ranges[vreg].num_intervals == 0) {
            continue;
        }
        printf("Vreg %d live at: ", vreg);
        for (int i = 0; i < ranges[vreg].num_intervals; i++) {
            Interval *interval = &ranges[vreg].intervals[i];
            printf("[%d, %d)", interval->start, interval->end);
            if (i < ranges[vreg].num_intervals - 1) {
                printf(", ");
            }
        }
        printf("\n");
    }
}
