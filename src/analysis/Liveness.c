
#include <string.h>
#include <stdio.h>

#include "Liveness.h"

// Assigns a unique number to each of the instructions across all the basic
// blocks in a function, used for storing live ranges
static void number_ins(Fn *fn) {
    int idx = 0;
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        for (AsmIns *ins = bb->asm_head; ins; ins = ins->next) {
            ins->idx = idx++;
        }
    }
}

// Extend an existing live range interval to include the given program point
// (if a suitable interval exists), or create a new interval. Returns 1 if the
// live range was updated, or 0 otherwise (i.e. the point is already contained
// in some existing interval).
//
// Points are always added in reverse order (since we only loop over
// instructions in reverse), there's no jumping around. So, this method is
// guaranteed to produce the minimum number of intervals required to represent
// the live range.
static void add_program_point(LiveRange *range, int point) {
    // Try to find an interval we can extend
    for (Interval *i = *range; i; i = i->next) {
        if (point >= i->start && point <= i->end) {
            return; // Already inside an interval
        } else if (point == i->start - 1) {
            i->start--; // Right before an existing interval
            return;
        } else if (point == i->end + 1) {
            i->end++; // Right after an existing interval
            return;
        }
    }
    // Otherwise, prepend a new interval to the linked list
    Interval *i = malloc(sizeof(Interval));
    i->start = point;
    i->end = point;
    i->next = *range;
    *range = i;
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
// live out = union over all successors { live in(successor) }
//
// Live in is everything that's used inside this basic block, plus everything
// that's live out minus what's defined in this block
// live in = { use(bb) } union { live out(bb) \ defn(bb) }
//
// This method is guaranteed to work since the live in set on one iteration of
// a basic block is a subset of the live in set on the next iteration.
static int live_ranges_for_bb(Fn *fn, LiveRange *ranges, BB *bb) {
    bb->live.mark = 1; // We've processed this BB's live ranges now

    // Keep track of vregs that are live at each program point
    int live[fn->num_vregs];
    memset(live, 0, sizeof(int) * fn->num_vregs);

    // Find everything that's live out for the BB
    for (int i = 0; i < bb->cfg.num_succ; i++) {
        BB *successor = bb->cfg.succ[i];
        for (int vreg = 0; vreg < fn->num_vregs; vreg++) {
            live[vreg] |= successor->live.in[vreg];
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
            LiveRange *range = &ranges[NUM_REGS + vreg];
            if (live[vreg]) {
                add_program_point(range, ins->idx);
            }
        }

        // Regs defined are no longer live before the current instruction
        if (defs_left(ins) && ins->l.type == OP_VREG) {
            live[ins->l.vreg] = 0;
        }
    }

    // Everything left over is now live-in for the BB
    int changed = 0;
    for (int vreg = 0; vreg < fn->num_vregs; vreg++) {
        if (live[vreg]) {
            changed |= !bb->live.in[vreg];
            bb->live.in[vreg] = 1;
        }
    }
    return changed;
}

static void live_ranges_for_vregs(Fn *fn, LiveRange *ranges) {
    // Count the basic blocks
    int num_bbs = 0;
    for (BB *bb = fn->entry; bb; bb = bb->next) { num_bbs++; }

    // Create a worklist of basic blocks
    BB *worklist[num_bbs];
    int num_worklist = 0;
    worklist[num_worklist++] = fn->last; // Start with the LAST BB in the fn

    // Iterate until the worklist is empty
    while (num_worklist > 0) {
        BB *bb = worklist[--num_worklist]; // Pull the last BB off the worklist
        int changed = live_ranges_for_bb(fn, ranges, bb);

        // Iterate over the predecessors
        for (int pred_idx = 0; pred_idx < bb->cfg.num_pred; pred_idx++) {
            BB *pred = bb->cfg.pred[pred_idx];
            // Add the predecessor to the worklist if the live in list changed
            // (add all predecessors), or if it is yet to been processed
            if (changed || !pred->live.mark) {
                worklist[num_worklist++] = pred;
            }
        }
    }
}

static void live_ranges_for_pregs(Fn *fn, LiveRange *ranges) {
    // Iterate over all instructions
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        for (AsmIns *ins = bb->asm_head; ins; ins = ins->next) {
            // Physical registers are only marked live for the single
            // instruction that uses them
            if ((uses_left(ins) || defs_left(ins)) && ins->l.type == OP_REG) {
                add_program_point(&ranges[ins->l.reg], ins->idx);
            }
            if (uses_right(ins) && ins->r.type == OP_REG) {
                add_program_point(&ranges[ins->r.reg], ins->idx);
            }
        }
    }
}

LiveRange * analyse_live_ranges(Fn *fn) {
    number_ins(fn);

    // Allocate the live ranges array, all starting with NULL
    int num_regs = NUM_REGS + fn->num_vregs;
    LiveRange *ranges = calloc(num_regs, sizeof(LiveRange));

    // Allocate the live-in array for each basic block
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        bb->live.in = calloc(fn->num_vregs, sizeof(int));
        bb->live.mark = 0;
    }

    live_ranges_for_vregs(fn, ranges);
    live_ranges_for_pregs(fn, ranges);
    return ranges;
}

static int intervals_intersect(Interval i1, Interval i2) {
    return !(i1.end < i2.start || i1.start > i2.end);
}

static Interval interval_intersection(Interval i1, Interval i2) {
    // start = max(i1.start, i2.start), end = min(i1.end, i2.end)
    Interval intersection;
    intersection.start = i1.start > i2.start ? i1.start : i2.start;
    intersection.end = i1.end < i2.end ? i1.end : i2.end;
    intersection.next = NULL;
    return intersection;
}

int ranges_intersect(LiveRange r1, LiveRange r2) {
    for (Interval *i1 = r1; i1; i1 = i1->next) {
        for (Interval *i2 = r2; i2; i2 = i2->next) {
            if (intervals_intersect(*i1, *i2)) {
                return 1;
            }
        }
    }
    return 0;
}

LiveRange range_intersection(LiveRange r1, LiveRange r2) {
    // All interval intersections should be unique, since the intervals in each
    // of r1 and r2 are unique; so don't bother trying to combine any of the
    // intersection intervals (they won't overlap)
    // The resulting intersection live range is also guaranteed to have its
    // intervals ordered, since all the intervals in r1 and r2 are ordered
    LiveRange head = NULL;
    LiveRange *next = &head;
    for (Interval *i1 = r1; i1; i1 = i1->next) {
        for (Interval *i2 = r2; i2; i2 = i2->next) {
            if (intervals_intersect(*i1, *i2)) {
                Interval *i = malloc(sizeof(Interval));
                *i = interval_intersection(*i1, *i2);
                *next = i;
                next = &i->next;
            }
        }
    }
    return head;
}

void print_live_range(LiveRange range) {
    for (Interval *i = range; i; i = i->next) {
        printf("[%d, %d]", i->start, i->end);
        if (i->next) {
            printf(", ");
        }
    }
}

void print_live_ranges(LiveRange *ranges, int num_vregs) {
    for (int reg = 0; reg < NUM_REGS + num_vregs; reg++) {
        if (!ranges[reg]) {
            continue; // Reg not used (no live range)
        }
        if (reg < NUM_REGS) { // Physical register
            printf("%s", REG_NAMES[reg][REG_Q]);
        } else { // Virtual register
            printf("%%%d", reg - NUM_REGS);
        }
        printf(" live at: ");
        print_live_range(ranges[reg]);
        printf("\n");
    }
}
