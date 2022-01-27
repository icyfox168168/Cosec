
#include <string.h>
#include <stdio.h>

#include "Liveness.h"

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

// Extend an existing live range interval to include the given program point
// (if a suitable interval exists), or create a new interval
static void add_program_point_to_live_range(LiveRange *range, int point) {
    // Try to find an interval we can extend
    for (int i = 0; i < range->num_intervals; i++) {
        Interval *interval = &range->intervals[i];
        if (point >= interval->start && point <= interval->end) {
            return; // Already inside an interval
        } else if (point == interval->start - 1) {
            interval->start--; // Right before an existing interval
            return;
        } else if (point == interval->end + 1) {
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
    Interval new_interval = {point, point};
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
        BB *successor = bb->successors[i];
        for (int vreg = 0; vreg < fn->num_vregs; vreg++) {
            if (successor->live_in[vreg]) {
                live[vreg] = 1;
            }
        }
    }

    // Iterate over all instructions in reverse order
    for (AsmIns *ins = bb->asm_last; ins; ins = ins->prev) {
        // Vregs used or defined are live
        if ((uses_left(ins) || defs_left(ins)) && ins->l.type == OP_VREG) {
            live[ins->l.vreg] = 1;
        }
        if (uses_right(ins) && ins->r.type == OP_VREG) {
            live[ins->r.vreg] = 1;
        }

        // Add the live vregs to the 'live ranges' structure
        for (int vreg = 0; vreg < fn->num_vregs; vreg++) {
            if (live[vreg]) {
                add_program_point_to_live_range(&ranges[vreg], ins->idx);
            }
        }

        // Vregs defined are no longer live before the current instruction
        if (defs_left(ins) && ins->l.type == OP_VREG) {
            live[ins->l.vreg] = 0;
        }
    }

    // Everything left over is now live-in for the BB
    int changed = 0;
    for (int vreg = 0; vreg < fn->num_vregs; vreg++) {
        if (live[vreg]) {
            changed |= !bb->live_in[vreg];
            bb->live_in[vreg] = 1;
        }
    }
    return changed;
}

LiveRange * analysis_liveness(AsmFn *fn) {
    number_ins(fn);

    // Allocate the live ranges array
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

int intervals_intersect(Interval i1, Interval i2) {
    return !(i1.end < i2.start || i1.start > i2.end);
}

int ranges_intersect(LiveRange r1, LiveRange r2) {
    for (int i = 0; i < r1.num_intervals; i++) {
        for (int j = 0; j < r2.num_intervals; j++) {
            if (intervals_intersect(r1.intervals[i], r2.intervals[j])) {
                return 1;
            }
        }
    }
    return 0;
}

void print_live_ranges(AsmFn *fn, LiveRange *ranges) {
    for (int vreg = 0; vreg < fn->num_vregs; vreg++) {
        if (ranges[vreg].num_intervals == 0) {
            continue;
        }
        printf("Vreg %d live at: ", vreg);
        for (int i = 0; i < ranges[vreg].num_intervals; i++) {
            Interval *interval = &ranges[vreg].intervals[i];
            printf("[%d, %d]", interval->start, interval->end);
            if (i < ranges[vreg].num_intervals - 1) {
                printf(", ");
            }
        }
        printf("\n");
    }
}
