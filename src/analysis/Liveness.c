
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
        // Add an extra program point to mark the END of a BB (for vregs that
        // are live-out for the BB)
        idx++;
    }
}

// Extend an existing live range interval to include the given program point
// (if a suitable interval exists), or create a new interval.
//
// The algorithm is guaranteed to produce:
// * The minimum number of intervals required to represent the live range; since
//   we add program points in a linear manner always in reverse order
// * The intervals are always sorted in order of index; since we add program
//   points in reverse order, and prepend new intervals to the start of the
//   linked list
static void add_idx_to_live_range(LiveRange *range, int point) {
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
    return ins->l.type == OP_GPR &&
           ((op >= X86_MOV && op <= X86_LEA) ||
           (op >= X86_ADD && op <= X86_MUL) ||
           (op >= X86_AND && op <= X86_SAR) ||
           (op >= X86_SETE && op <= X86_SETAE) ||
           (op == X86_POP));
}

// Returns true if an instruction uses its left operand
static int uses_left(AsmIns *ins) {
    // movs and setxx don't use their left argument, they only define it
    AsmOpcode op = ins->op;
    return X86_OPCODE_NARGS[op] >= 1 && ins->l.type == OP_GPR &&
           !(op >= X86_MOV && op <= X86_LEA) &&
           !(op >= X86_SETE && op <= X86_SETAE) &&
           op != X86_POP;
}

// Returns true if an instruction uses its right operand
static int uses_right(AsmIns *ins) {
    // If it has 2 arguments, then it uses its right operand
    return X86_OPCODE_NARGS[ins->op] >= 2 && ins->r.type == OP_GPR;
}

// Marks regs that are used in a memory access operand as live in the given
// 'live' map
static void mark_mem_operand_uses_as_live(int *live, AsmOperand *mem_op) {
    if (mem_op->type != OP_MEM) {
        return;
    }
    if (mem_op->base_size > REG_NONE) {
        live[mem_op->base_reg] = 1; // Base reg is used
    }
    if (mem_op->index_size > REG_NONE) {
        live[mem_op->index_reg] = 1; // Index reg is used
    }
}

// Marks regs that are used by the instruction as live in the given 'live' map
static void mark_uses_as_live(int *live, AsmIns *ins) {
    // Regs used or defined are live
    if (uses_left(ins) || defs_left(ins)) {
        live[ins->l.reg] = 1; // Left operand is a reg and is used
    }
    if (uses_right(ins)) {
        live[ins->r.reg] = 1; // Right operand is a reg and is used
    }

    // Regs used in memory accesses are live
    mark_mem_operand_uses_as_live(live, &ins->l);
    mark_mem_operand_uses_as_live(live, &ins->r);

    // rsp and rbp shouldn't be used for register allocation -> mark them as
    // live EVERYWHERE
    live[GPR_RBP] = 1;
    live[GPR_RSP] = 1;
}

// Marks regs that are defined by the instruction as not live in the given
// 'live' map
static void mark_defs_as_dead(int *live, AsmIns *ins) {
    // Regs defined are no longer live before the current instruction
    if (defs_left(ins)) {
        live[ins->l.reg] = 0; // Left operand is a reg and is defined
    }
}

// Marks every physical register as dead in the given 'live' map
static void mark_all_pregs_as_dead(int *live) {
    for (int preg = 0; preg < LAST_GPR; preg++) {
        live[preg] = 0;
    }
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
    // Keep track of vregs that are live at each program point
    int live[fn->num_regs];
    memset(live, 0, sizeof(int) * fn->num_regs);

    // Find everything that's live out for the BB
    for (int i = 0; i < bb->cfg.num_succ; i++) {
        BB *successor = bb->cfg.succ[i];
        for (int vreg = LAST_GPR; vreg < fn->num_regs; vreg++) {
            live[vreg] |= successor->live.in[vreg - LAST_GPR];
        }
    }

    // Mark everything that's live out as live for the program point BEYOND
    // the last instruction in the BB
    for (int reg = 0; reg < fn->num_regs; reg++) {
        if (live[reg]) {
            add_idx_to_live_range(&ranges[reg], bb->asm_last->idx + 1);
        }
    }

    // Iterate over all instructions in reverse order
    for (AsmIns *ins = bb->asm_last; ins; ins = ins->prev) {
        mark_uses_as_live(live, ins);
        for (int reg = 0; reg < fn->num_regs; reg++) { // Add live regs
            if (live[reg]) {
                add_idx_to_live_range(&ranges[reg], ins->idx);
            }
        }
        mark_defs_as_dead(live, ins);
        mark_all_pregs_as_dead(live); // pregs are only live for ONE instruction
    }

    // Everything left over is now live-in for the BB
    int changed = 0;
    for (int vreg = LAST_GPR; vreg < fn->num_regs; vreg++) {
        if (live[vreg]) {
            changed |= !bb->live.in[vreg - LAST_GPR];
            bb->live.in[vreg - LAST_GPR] = 1;
        }
    }
    return changed;
}

static void live_ranges(Fn *fn, LiveRange *ranges) {
    // Count the basic blocks for the worklist size
    int num_bbs = 0;
    for (BB *bb = fn->entry; bb; bb = bb->next) { num_bbs++; }

    // Create a worklist of basic blocks; the size of the worklist is the
    // worst case scenario, where every BB is a predecessor of every other BB
    BB *worklist[num_bbs * num_bbs];
    int num_worklist = 0;

    // Add all the BB (in reverse order, so that we start with the last BB) to
    // the worklist -> ensures that they ALL get analysed at least once
    for (BB *bb = fn->last; bb; bb = bb->prev) {
        worklist[num_worklist++] = bb;
    }

    while (num_worklist > 0) { // Iterate until the worklist is empty
        BB *bb = worklist[--num_worklist]; // Pull the last BB off the worklist
        int changed = live_ranges_for_bb(fn, ranges, bb);
        if (changed) { // Add predecessors to worklist if live-in changed
            for (int pred_idx = 0; pred_idx < bb->cfg.num_pred; pred_idx++) {
                BB *pred = bb->cfg.pred[pred_idx];
                worklist[num_worklist++] = pred;
            }
        }
    }
}

LiveRange * analyse_live_ranges(Fn *fn) {
    number_ins(fn);

    // Allocate the live ranges array, all starting with NULL
    LiveRange *ranges = calloc(fn->num_regs, sizeof(LiveRange));

    // Allocate the live-in array for each basic block
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        bb->live.in = calloc(fn->num_regs - LAST_GPR, sizeof(int));
    }

    live_ranges(fn, ranges);
    return ranges;
}

static int intervals_intersect(Interval i1, Interval i2) {
    // Subtract 1 from 'end' since all intervals are EXCLUSIVE of 'end', i.e.,
    // [start, end)
    return !((i1.end - 1) < i2.start || i1.start > (i2.end - 1));
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

void print_live_ranges(LiveRange *ranges, int num_regs) {
    for (int reg = 0; reg < num_regs; reg++) {
        if (!ranges[reg]) {
            continue; // Reg not used (no live range)
        }
        if (reg < LAST_GPR) { // Physical register
            printf("%s", GPR_NAMES[reg][REG_Q]);
        } else { // Virtual register
            printf("%%%d", reg - LAST_GPR);
        }
        printf(" live at: ");
        print_live_range(ranges[reg]);
        printf("\n");
    }
}
