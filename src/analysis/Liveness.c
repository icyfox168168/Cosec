
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
// (if a suitable interval exists), or create a new interval. Returns 1 if the
// live range was updated, or 0 otherwise.
//
// Points are always added in reverse order (since we only loop over
// instructions in reverse), there's no jumping around. So, this method is
// guaranteed to produce the minimum number of intervals required to represent
// the live range.
static int add_program_point(LiveRange *range, int point) {
    // Try to find an interval we can extend
    for (Interval *i = *range; i; i = i->next) {
        if (point >= i->start && point <= i->end) {
            return 0; // Already inside an interval
        } else if (point == i->start - 1) {
            i->start--; // Right before an existing interval
            return 1;
        } else if (point == i->end + 1) {
            i->end++; // Right after an existing interval
            return 1;
        }
    }
    // Otherwise, prepend a new interval to the linked list
    Interval *i = malloc(sizeof(Interval));
    i->start = point;
    i->end = point;
    i->next = *range;
    *range = i;
    return 1;
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
static int live_ranges_for_bb(AsmFn *fn, LiveRange *ranges, BB *bb) {
    // Keep track of vregs that are live at each program point
    int live[fn->num_vregs];
    memset(live, 0, sizeof(int) * fn->num_vregs);

    // Find everything that's live out for the BB
    for (int i = 0; i < bb->num_succ; i++) {
        BB *successor = bb->succ[i];
        for (int vreg = 0; vreg < fn->num_vregs; vreg++) {
            live[vreg] |= successor->live_in[vreg];
        }
    }

    // Iterate over all instructions in reverse order
    int changed = 0;
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
            LiveRange *range = &ranges[REG_MAX + vreg];
            if (live[vreg]) {
                changed |= add_program_point(range, ins->idx);
            }
        }

        // Regs defined are no longer live before the current instruction
        if (defs_left(ins) && ins->l.type == OP_VREG) {
            live[ins->l.vreg] = 0;
        }
    }

    // Everything left over is now live-in for the BB
    for (int vreg = 0; vreg < fn->num_vregs; vreg++) {
        if (live[vreg]) {
            changed |= !bb->live_in[vreg];
            bb->live_in[vreg] = 1;
        }
    }
    return changed;
}

static void live_ranges_for_vregs(AsmFn *fn, LiveRange *ranges) {
    // Count the basic blocks
    int num_bbs = 0;
    for (BB *bb = fn->entry; bb; bb = bb->next) { num_bbs++; }

    // Create a worklist of basic blocks
    BB **worklist = malloc(sizeof(BB *) * num_bbs);
    int num_worklist = 0;
    worklist[num_worklist++] = fn->last; // Start with the LAST BB in the fn

    // Iterate until the worklist is empty
    while (num_worklist > 0) {
        BB *bb = worklist[--num_worklist]; // Pull the last BB off the worklist
        int changed = live_ranges_for_bb(fn, ranges, bb);
        if (changed) { // If the live-in list was changed
            // Add all the pred of this block to the worklist
            for (int pred_idx = 0; pred_idx < bb->num_pred; pred_idx++) {
                worklist[num_worklist++] = bb->pred[pred_idx];
            }
        }
    }
}

static void live_ranges_for_pregs(AsmFn *fn, LiveRange *ranges) {
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

LiveRange * analysis_liveness(AsmFn *fn) {
    number_ins(fn);

    // Allocate the live ranges array, all starting with NULL
    int num_regs = REG_MAX + fn->num_vregs;
    LiveRange *ranges = calloc(num_regs, sizeof(LiveRange));

    // Allocate the live-in array for each basic block
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        bb->live_in = calloc(fn->num_vregs, sizeof(int));
    }

    live_ranges_for_vregs(fn, ranges);
    live_ranges_for_pregs(fn, ranges);
    return ranges;
}

static int intervals_intersect(Interval i1, Interval i2) {
    return !(i1.end < i2.start || i1.start > i2.end);
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

void print_live_range(LiveRange range) {
    for (Interval *i = range; i; i = i->next) {
        printf("[%d, %d]", i->start, i->end);
        if (i->next) {
            printf(", ");
        }
    }
}

void print_live_ranges(LiveRange *ranges, int num_vregs) {
    for (int reg = 0; reg < REG_MAX + num_vregs; reg++) {
        if (!ranges[reg]) {
            continue; // Reg not used (no live range)
        }
        if (reg < REG_MAX) { // Physical register
            printf("%s", REG_NAMES[reg][REG_Q]);
        } else { // Virtual register
            printf("%%%d", reg - REG_MAX);
        }
        printf(" live at: ");
        print_live_range(ranges[reg]);
        printf("\n");
    }
}
