
#include <assert.h>
#include <string.h>
#include <stdio.h>

#include "RegAlloc.h"

// The register allocator is heavily based on the classic graph colouring
// algorithm presented in the book:
//
//   Modern Parser Implementation in C, Andrew W. Appel, Chapter 11
//
// Including the conservative coalescing algorithm. I highly recommend giving
// it a read for a great conceptual overview.
//
// Additional resources I found helpful:
// * A set of slides on the graph colouring algorithm:
//     http://web.cecs.pdx.edu/~mperkows/temp/register-allocation.pdf
// * An article on the graph colouring algorithm:
//     https://www.lighterra.com/papers/graphcoloring/
// * A set of slides on liveness analysis:
//     https://proglang.informatik.uni-freiburg.de/teaching/compilerbau/2016ws/10-liveness.pdf
// * Useful practical information on implementing liveness analysis (including
//   the worklist-based algorithm used in 'Liveness.c'):
//     https://engineering.purdue.edu/~milind/ece573/2015fall/project/step7/step7.html
// * Conceptual overview of coalescing:
//     https://www.cs.cmu.edu/afs/cs/academic/class/15745-s16/www/lectures/L23-Register-Coalescing.pdf

// Tells us some piece of information about an assembly instruction that's
// specific to a register group.
typedef int (*InsQuery)(AsmIns *ins);

// Register groups are sets of registers that can be allocated independently
// of each other. In x86-64, we define two groups, the general purpose
// registers (GPRs) which hold integer values (i.e., rax, rdx, etc.), and the
// SSE registers for floating point math (i.e., xmm0, etc.).
//
// Register allocation is generalised enough to allow allocation of each
// register group separately. The below structure describes enough information
// about a register group to enable register allocation to work.
typedef struct {
    int num_pregs; // Number of physical registers; LAST_GPR or LAST_SSE
    char **preg_names; // Names of physical registers, indexed by preg
    InsQuery uses_left;  // True if the instruction uses its left operand
    InsQuery uses_right; // True if the instruction uses its right operand
    InsQuery defs_left;  // True if the instruction defines its left operand
    AsmOperandType reg_op; // OP_GPR or OP_XMM
    InsQuery is_mov; // True if the instruction is a move that relates two regs
    InsQuery is_redundant_mov; // If a 'mov' is trivial and can be removed
    int in_mem_ops; // ONLY for GPRs; only GPRs can appear in memory references
} RegGroup;

static void print_reg(RegGroup r, int reg) {
    if (reg < r.num_pregs) { // Physical register
        printf("%s", r.preg_names[reg]);
    } else { // Virtual register
        printf(r.reg_op == OP_XMM ? "%%%df" : "%%%d", reg - r.num_pregs);
    }
}


// ---- Liveness Analysis -----------------------------------------------------

// All assembly instructions are numbered across basic blocks so that live
// ranges can be referred to by a union of intervals [start, end)
typedef struct interval {
    int start, end; // INCLUSIVE of 'start'; EXCLUSIVE of 'end'
    struct interval *next;
} Interval;

// Each live range is a linked list of intervals; a 'LiveRange' refers to the
// head interval of the linked list
typedef Interval * LiveRange;

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
static int live_ranges_for_bb(RegGroup r, LiveRange *ranges, int num_regs,
                              BB *bb) {
    // Keep track of vregs that are live at each program point
    int live[num_regs];
    memset(live, 0, sizeof(int) * num_regs);

    // Find everything that's live out for the BB
    for (int i = 0; i < bb->cfg.num_succ; i++) {
        BB *successor = bb->cfg.succ[i];
        for (int vreg = r.num_pregs; vreg < num_regs; vreg++) {
            live[vreg] |= successor->live.in[vreg - r.num_pregs];
        }
    }

    // Mark everything that's live out as live for the program point BEYOND
    // the last instruction in the BB
    for (int reg = 0; reg < num_regs; reg++) {
        if (live[reg]) {
            add_idx_to_live_range(&ranges[reg], bb->asm_last->idx + 1);
        }
    }

    // Iterate over all instructions in reverse order
    for (AsmIns *ins = bb->asm_last; ins; ins = ins->prev) {
        // Regs used or defined are live
        if (ins->l.type == r.reg_op && (r.uses_left(ins) || r.defs_left(ins))) {
            live[ins->l.reg] = 1; // Left operand is a reg and is used
        }
        if (ins->r.type == r.reg_op && r.uses_right(ins)) {
            live[ins->r.reg] = 1; // Right operand is a reg and is used
        }

        // Regs used in memory accesses are live (only if we're calculating
        // the live ranges of GPRs!)
        if (r.in_mem_ops && (ins->l.type == OP_MEM || ins->r.type == OP_MEM)) {
            AsmOperand *mem_op = ins->l.type == OP_MEM ? &ins->l : &ins->r;
            if (mem_op->base_size > REG_NONE) {
                live[mem_op->base_reg] = 1; // Base reg is used
            }
            if (mem_op->index_size > REG_NONE) {
                live[mem_op->index_reg] = 1; // Index reg is used
            }
        }

        // rsp and rbp shouldn't be used for register allocation -> mark them as
        // live EVERYWHERE (only for GPRs)
        if (r.in_mem_ops) {
            live[GPR_RBP] = 1;
            live[GPR_RSP] = 1;
        }

        // Add live regs to the 'ranges' data structure
        for (int reg = 0; reg < num_regs; reg++) {
            if (live[reg]) {
                add_idx_to_live_range(&ranges[reg], ins->idx);
            }
        }

        // Regs defined are no longer live before the current instruction
        if (ins->l.type == r.reg_op && r.defs_left(ins)) {
            live[ins->l.reg] = 0; // Left operand is a reg and is defined
        }

        // All pregs are live for only ONE instruction
        for (int preg = 0; preg < r.num_pregs; preg++) {
            live[preg] = 0;
        }
    }

    // Everything left over is now live-in for the BB
    int changed = 0;
    for (int vreg = r.num_pregs; vreg < num_regs; vreg++) {
        if (live[vreg]) {
            changed |= !bb->live.in[vreg - r.num_pregs];
            bb->live.in[vreg - r.num_pregs] = 1;
        }
    }
    return changed;
}

// Returns an array of 'LiveRange' indexed by reg number (i.e., first 'num_preg'
// live ranges are for the physical registers, and the remainder up to
// 'num_regs' are for the virtual registers)
static LiveRange * live_ranges(RegGroup r, Fn *fn, int num_regs) {
    number_ins(fn);

    // Allocate the live ranges array, all starting with NULL
    LiveRange *ranges = calloc(num_regs, sizeof(LiveRange));

    // Allocate the live-in array for each basic block
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        bb->live.in = calloc(num_regs - r.num_pregs, sizeof(int));
    }

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

    // Iterate until the worklist is empty
    while (num_worklist > 0) {
        BB *bb = worklist[--num_worklist]; // Pull the last BB off the worklist
        int changed = live_ranges_for_bb(r, ranges, num_regs, bb);
        if (changed) { // Add predecessors to worklist if live-in changed
            for (int pred_idx = 0; pred_idx < bb->cfg.num_pred; pred_idx++) {
                BB *pred = bb->cfg.pred[pred_idx];
                worklist[num_worklist++] = pred;
            }
        }
    }
    return ranges;
}

static int intervals_intersect(Interval i1, Interval i2) {
    // Subtract 1 from 'end' since all intervals are EXCLUSIVE of 'end'
    return !((i1.end - 1) < i2.start || i1.start > (i2.end - 1));
}

static int ranges_intersect(LiveRange r1, LiveRange r2) {
    for (Interval *i1 = r1; i1; i1 = i1->next) {
        for (Interval *i2 = r2; i2; i2 = i2->next) {
            if (intervals_intersect(*i1, *i2)) {
                return 1;
            }
        }
    }
    return 0;
}

static void print_live_range(LiveRange range) {
    for (Interval *i = range; i; i = i->next) {
        printf("[%d, %d]", i->start, i->end);
        if (i->next) {
            printf(", ");
        }
    }
}

static void print_live_ranges(RegGroup r, LiveRange *ranges, int num_regs) {
    for (int reg = 0; reg < num_regs; reg++) {
        if (!ranges[reg]) {
            continue; // Reg not used (no live range)
        }
        print_reg(r, reg);
        printf(" is live at: ");
        print_live_range(ranges[reg]);
        printf("\n");
    }
}


// ---- Interference and Coalescing Graphs ------------------------------------

// Accessing the interference and coalescing graph 'matrix' (a linear array
// that we turn into a doubly-indexed one)
#define G(g, reg1, reg2) ((reg1) * (g)->num_regs + (reg2))

// Use the same graph structure for the interference and the coalescing graphs.
// The first 'num_pregs' registers in 'matrix' (and in 'num_edges') are nodes
// for the physical registers; the remaining nodes are for virtual registers
// (same as for the 'LiveRange *ranges' array)
typedef struct {
    int num_regs;   // Size of matrix (number of pregs + number of vregs)
    int *matrix;    // Square bit matrix of edges
    int *num_edges; // Number of edges for each node in the graph
} RegGraph;

static RegGraph new_graph(int num_regs) {
    RegGraph g;
    g.num_regs = num_regs;
    g.matrix = calloc(num_regs * num_regs, sizeof(int));
    g.num_edges = calloc(num_regs, sizeof(int));
    return g;
}

static RegGraph copy_graph(RegGraph *g) {
    RegGraph copy = *g;
    copy.matrix = malloc(g->num_regs * g->num_regs * sizeof(int));
    memcpy(copy.matrix, g->matrix, g->num_regs * g->num_regs * sizeof(int));
    copy.num_edges = malloc(g->num_regs * sizeof(int));
    memcpy(copy.num_edges, g->num_edges, g->num_regs * sizeof(int));
    return copy;
}

static int node_exists(RegGraph *g, int reg) {
    // A node exists in the graph if its value along the diagonal (i.e. whether
    // it interferes with itself) is 1
    return g->matrix[G(g, reg, reg)];
}

static void mark_node_exists(RegGraph *g, int reg) {
    g->matrix[G(g, reg, reg)] = 1;
}

static int edge_exists(RegGraph *g, int reg1, int reg2) {
    return g->matrix[G(g, reg1, reg2)];
}

static int num_edges(RegGraph *g, int reg) {
    return g->num_edges[reg];
}

static void remove_node(RegGraph *g, int to_remove) {
    // Remove a node from the graph by setting its value along the diagonal
    // (i.e. matrix[G(vreg, vreg)]) to 0
    // Zero the row and column to remove edges with all the other nodes
    for (int reg = 0; reg < g->num_regs; reg++) {
        g->num_edges[reg] -= edge_exists(g, to_remove, reg);
        g->matrix[G(g, to_remove, reg)] = 0;
        g->matrix[G(g, reg, to_remove)] = 0;
    }
    g->num_edges[to_remove] = 0;
}

static void add_edge(RegGraph *g, int reg1, int reg2) {
    // Mirror the matrix symmetrically around the leading diagonal (this is an
    // a-directional graph)
    g->num_edges[reg1] += !edge_exists(g, reg1, reg2);
    g->matrix[G(g, reg1, reg2)] = 1;
    g->num_edges[reg2] += !edge_exists(g, reg2, reg1);
    g->matrix[G(g, reg2, reg1)] = 1;
}

// Copies all the edges from 'src' to 'dst' (maintains existing edges at 'dst')
static void copy_edges(RegGraph *g, int src, int dst) {
    // Iterate along a whole row and column
    for (int reg = 0; reg < g->num_regs; reg++) {
        if (edge_exists(g, src, reg)) {
            add_edge(g, dst, reg);
        }
    }
}

// The interference graph tells us whether two regs are live at the same time or
// not - if they do intefere, they can't be allocated the same register
static RegGraph build_interference_graph(RegGroup r, LiveRange *ranges,
                                         int num_regs) {
    // Intersect all physical and virtual registers with each other to build
    // the intersection graph (represented as a matrix). Only iterate over the
    // upper half of the leading diagonal in the matrix (for efficiency)
    RegGraph g = new_graph(num_regs);
    for (int reg1 = 0; reg1 < num_regs; reg1++) {
        LiveRange range1 = ranges[reg1];
        if (!range1) {
            continue; // reg1 isn't used
        }
        mark_node_exists(&g, reg1);
        for (int reg2 = 0; reg2 < reg1; reg2++) { // Only iterate upper half
            LiveRange range2 = ranges[reg2];
            if (!range2) {
                continue; // reg2 isn't used
            }
            if (reg1 < r.num_pregs && reg2 < r.num_pregs) {
                continue; // Don't care about physical register interference
            }
            if (ranges_intersect(range1, range2)) {
                add_edge(&g, reg1, reg2);
            }
        }
    }
    return g;
}

// The coalescing graph tells us whether two regs are candidates for coalescing;
// that is, related by a mov and their live ranges don't otherwise interfere.
// At least one of the regs in the mov should be a vreg
static RegGraph build_coalescing_graph(RegGroup r, Fn *fn, LiveRange *ranges,
                                       int num_regs) {
    // Iterate over all instructions to find move-related regs
    RegGraph g = new_graph(num_regs);
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        for (AsmIns *mov = bb->asm_head; mov; mov = mov->next) {
            // Make sure this is a coalescing candidate and at least one of the
            // registers is a vreg (not a preg)
            if (r.is_mov(mov) &&
                    (mov->l.type == r.reg_op && mov->r.type == r.reg_op) &&
                    (mov->l.reg >= r.num_pregs || mov->r.reg >= r.num_pregs)) {
                // This mov is a coalescing candidate if the live ranges of reg1
                // and reg2 DON'T intersect
                int reg1 = mov->l.reg, reg2 = mov->r.reg;
                if (!ranges_intersect(ranges[reg1], ranges[reg2])) {
                    mark_node_exists(&g, reg1);
                    mark_node_exists(&g, reg2);
                    add_edge(&g, reg1, reg2);
                }
            }
        }
    }
    return g;
}


// ---- Register Allocation ---------------------------------------------------

// Removes one non-move related node of insignificant degree (degree < num_pregs)
// from the interference graph and pushes it onto the stack. Returns 1 if we
// successfully found a node to remove, or 0 if we didn't.
static int simplify(RegGroup r, RegGraph *ig, RegGraph *cg, int *stack,
                    int *num_stack) {
    // Find a non-move related node of insignificant degree
    for (int vreg = r.num_pregs; vreg < ig->num_regs; vreg++) {
        if (!node_exists(ig, vreg)) {
            continue; // The node doesn't exist
        }
        if (num_edges(cg, vreg) > 0) {
            continue; // This node is move related
        }
        if (num_edges(ig, vreg) >= r.num_pregs) {
            continue; // This node is of significant degree (>=num_pregs edges)
        }
        stack[(*num_stack)++] = vreg; // Add to the stack
        remove_node(ig, vreg); // Remove from graphs
        remove_node(cg, vreg);
        printf("simplifying ");
        print_reg(r, vreg);
        printf("\n");
        return 1;
    }
    return 0;
}

// Calculates the Brigg's criteria for coalescing for two nodes
//   Nodes a and b can be coalesced if the resulting node ab has fewer than
//   'num_pregs' nodes of significant degree
// Basically, calculate the degree of every (unique) neighbour of a and b and
// count the number of these neighbours that have significant degree
static int briggs_criteria(RegGroup r, RegGraph *ig, int reg1, int reg2) {
    int count = 0;
    int seen[ig->num_regs];
    memset(seen, 0, sizeof(int) * ig->num_regs);
    for (int neighbour = 0; neighbour < ig->num_regs; neighbour++) {
        if ((edge_exists(ig, reg1, neighbour) || // Neighbour of reg1?
                edge_exists(ig, reg2, neighbour)) && // or of reg2?
                !seen[neighbour]) { // Unique?
            seen[neighbour] = 1;
            if (num_edges(ig, neighbour) >= r.num_pregs) { // Significant?
                count++;
            }
        }
    }
    return count;
}

// Performs conservative coalescing on one pair of move-related nodes using the
// Brigg's criteria. Returns 1 if two nodes were coalesced, or 0 otherwise
static int coalesce(RegGroup r, RegGraph *ig, RegGraph *cg, int *coalesce_map) {
    // Find two move-related nodes
    for (int reg1 = 0; reg1 < cg->num_regs; reg1++) {
        if (!node_exists(cg, reg1)) {
            continue; // Node isn't move-related to anything
        }
        for (int reg2 = 0; reg2 < reg1; reg2++) { // Only iterate upper half
            if (!node_exists(cg, reg1)) {
                continue; // Node isn't move-related to anything
            }
            if (!edge_exists(cg, reg1, reg2)) {
                continue; // Nodes aren't move-related
            }
            if (briggs_criteria(r, ig, reg1, reg2) >= r.num_pregs) {
                continue; // Can't coalesce
            }
            // Coalesce one node into the other; if one of the regs is a preg,
            // then make sure we coalesce the vreg into it
            int to_coalesce = reg1 < r.num_pregs ? reg2 : reg1;
            int target = to_coalesce == reg1 ? reg2 : reg1;
            copy_edges(ig, to_coalesce, target);
            copy_edges(cg, to_coalesce, target);
            remove_node(ig, to_coalesce);
            remove_node(cg, to_coalesce);
            coalesce_map[to_coalesce - r.num_pregs] = target;
            printf("coalescing ");
            print_reg(r, to_coalesce);
            printf(" into ");
            print_reg(r, target);
            printf("\n");
            return 1;
        }
    }
    return 0; // No nodes to coalesce
}

// Freeze looks for a move-related node of insignificant degree that we can
// freeze the moves for (give up hope of coalescing them). Returns 1 if we
// found a node to freeze, or 0 otherwise
static int freeze(RegGroup r, RegGraph *ig, RegGraph *cg) {
    // Find a move related node of insignificant degree
    for (int vreg = r.num_pregs; vreg < ig->num_regs; vreg++) {
        if (!node_exists(ig, vreg)) {
            continue; // The node doesn't exist
        }
        if (num_edges(cg, vreg) == 0) {
            continue; // This node is NOT move related
        }
        if (num_edges(ig, vreg) >= r.num_pregs) {
            continue; // This node is of significant degree (>=num_pregs edges)
        }
        remove_node(cg, vreg); // Remove from coalesce
        printf("freezing ");
        print_reg(r, vreg);
        printf("\n");
        return 1; // Found a node to freeze
    }
    return 0; // No nodes to freeze
}

// Spill looks for a significant degree node to remove from the interference
// graph and push on to the stack as a potential spill (we won't know for sure
// until we try select registers though)
static int spill(RegGroup r, RegGraph *ig, RegGraph *cg, int *stack,
                 int *num_stack) {
    // Find a node of significant degree
    for (int vreg = r.num_pregs; vreg < ig->num_regs; vreg++) {
        if (!node_exists(ig, vreg)) {
            continue; // The node doesn't exist
        }
        if (num_edges(ig, vreg) < r.num_pregs) {
            continue; // This node isn't of significant degree
        }
        stack[(*num_stack)++] = vreg; // Add to the stack
        remove_node(ig, vreg); // Remove from graphs
        remove_node(cg, vreg);
        printf("spilling ");
        print_reg(r, vreg);
        printf("\n");
        return 1;
    }
    return 0; // No nodes to spill
}

// Select keeps popping vregs off the stack and assigning physical registers
// until it hits a vreg that NEEDS to be spilled (not handled yet)
static void select(RegGroup r, RegGraph *ig, int *stack, int num_stack,
                   int *reg_map, int *coalesce_map) {
    // For each of the coalesced regs, we need to copy across their
    // interferences in the original interference graph ('coalesce' modified a
    // COPY) to the target reg they were coalesced into
    for (int vreg = r.num_pregs; vreg < ig->num_regs; vreg++) {
        int target = coalesce_map[vreg - r.num_pregs];
        if (target != -1) { // If 'vreg' was coalesced into 'target'
            copy_edges(ig, vreg, target);
        }
    }

    memset(reg_map, 0xff, (ig->num_regs - r.num_pregs) * sizeof(int));
    while (num_stack) { // Work our way down the stack allocating regs
        int vreg = stack[--num_stack]; // Pop from the stack

        // Find the first preg not interfering with 'vreg'
        int preg = 0;
        while (edge_exists(ig, vreg, preg)) {
            preg++;
        }
        if (preg >= r.num_pregs) { // All pregs interfere -> spill
            assert(0); // No spilling yet
        }
        reg_map[vreg - r.num_pregs] = preg;
        printf("allocating ");
        print_reg(r, vreg);
        printf(" to ");
        print_reg(r, preg);
        printf("\n");

        // Copy the regs that interfere with this vreg to the allocated preg
        copy_edges(ig, vreg, preg);
    }
}

static void colour_graph(RegGroup r, RegGraph *ig, RegGraph *cg, int *reg_map,
                         int *coalesce_map) {
    // Set up a stack of nodes to define an order in which to colour the vregs
    int stack[ig->num_regs - r.num_pregs];
    int num_stack = 0;

    // Keep track of which nodes we've coalesce_map into what. Maps vreg -> reg
    // (i.e. from the set of all vregs -> the set of all preg and vregs)
    memset(coalesce_map, 0xff, sizeof(int) * (ig->num_regs - r.num_pregs));

    // We're going to destroy the data in the interference graph by removing
    // nodes, so create a copy we can modify
    RegGraph ig_copy = copy_graph(ig);
    while (1) { // Keep spilling until we've removed ALL nodes from the graph
        while (1) { // Keep freezing until only significant degree nodes remain
            // Repeat simplification and coalescing until only significant-
            // degree or move-related nodes remain, ensuring each of simplify
            // and coalesce are run at least once
            int found_simplify = 1, found_coalesce;
            while (1) {
                // Keep simplifying until we can't
                while (simplify(r, &ig_copy, cg, stack, &num_stack)) {
                    found_simplify = 1;
                }
                if (!found_simplify) {
                    break;
                }
                // Keep coalescing until we can't
                found_coalesce = 0;
                while (coalesce(r, &ig_copy, cg, coalesce_map)) {
                    found_coalesce = 1;
                }
                if (!found_coalesce) {
                    break;
                }
                found_simplify = 0;
            }
            // Freeze a move-related node we can't simplify and try again
            if (!freeze(r, &ig_copy, cg)) {
                break; // Nothing to freeze
            }
        }
        // Only significant degree nodes remain, so spill one
        if (!spill(r, &ig_copy, cg, stack, &num_stack)) {
            break; // Nothing to spill
        }
    }
    // Colour the regs in the order they pop off the stack
    select(r, ig, stack, num_stack, reg_map, coalesce_map);
}

// Calculates the allocated register for a vreg by mapping it through a
// coalescing chain
static int map_vreg(RegGroup r, int vreg, int *reg_map, int *coalesce_map) {
    if (vreg < r.num_pregs) {
        return vreg; // Not a vreg
    }
    int reg = vreg;
    // Find the end of the coalescing chain (e.g., %3 -> %2 -> rax)
    while (reg >= r.num_pregs && coalesce_map[reg - r.num_pregs] != -1) {
        reg = coalesce_map[reg - r.num_pregs];
    }
    if (reg >= r.num_pregs) {
        // 'reg' might be the original vreg or a coalesced vreg
        reg = reg_map[reg - r.num_pregs];
    }
    assert(reg != -1);
    return reg;
}

// Replace any vregs in an instruction operand with their allocated register
static void replace_vreg(RegGroup r, AsmOperand *o, int *reg_map,
                         int *coalesce_map) {
    if (o->type == r.reg_op) {
        o->reg = map_vreg(r, o->reg, reg_map, coalesce_map);
    } else if (r.in_mem_ops && o->type == OP_MEM) { // Only for GPRs!
        if (o->base_size > REG_NONE) {
            o->base_reg = map_vreg(r, o->base_reg, reg_map, coalesce_map);
        }
        if (o->index_size > REG_NONE) {
            o->index_reg = map_vreg(r, o->index_reg, reg_map, coalesce_map);
        }
    }
}

// Replace any vregs in 'ins' with their allocated physical register
static void replace_ins_vregs(RegGroup r, AsmIns *ins, int *reg_map,
                              int *coalesce_map) {
    replace_vreg(r, &ins->l, reg_map, coalesce_map);
    replace_vreg(r, &ins->r, reg_map, coalesce_map);

    // Remove redundant mov instructions (according to the register group)
    if (r.is_mov(ins) &&
            ins->l.type == r.reg_op && ins->r.type == r.reg_op &&
            r.is_redundant_mov(ins)) {
        delete_asm(ins);
    }
}

// Iterate over every instruction in the function and replace any vreg with its
// allocated physical register
static void replace_vregs(RegGroup r, Fn *fn, int *reg_map, int *coalesce_map) {
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        for (AsmIns *ins = bb->asm_head; ins; ins = ins->next) {
            replace_ins_vregs(r, ins, reg_map, coalesce_map);
        }
    }
}

static void alloc_regs(RegGroup r, Fn *fn, int num_regs) {
    if (num_regs == r.num_pregs) {
        return; // No vregs to allocate
    }

    // Live ranges - calculate the instructions that each register is 'live' for
    LiveRange *ranges = live_ranges(r, fn, num_regs);
    print_live_ranges(r, ranges, num_regs);

    // Interference graph (IG) - nodes are registers (either vreg or GPR);
    // edges are drawn between nodes that are live at the same time (i.e.,
    // they interfere)
    RegGraph ig = build_interference_graph(r, ranges, num_regs);

    // Coalescing graph (CG) - nodes are registers (either vreg or GPR);
    // edges are drawn between nodes that are candidates for coalescing, i.e.,
    // two registers related by a move instruction that don't interfere
    RegGraph cg = build_coalescing_graph(r, fn, ranges, num_regs);

    // 'reg_map' tells us the PHYSICAL register that each VIRTUAL register has
    // been allocated to
    int reg_map[num_regs - r.num_pregs];

    // 'coalesce_map' tells us which register (either physical or virtual)
    // each VIRTUAL register has been coalesced into (if any)
    int coalesce_map[num_regs - r.num_pregs];

    // Performs the actual register allocation and coalescing
    colour_graph(r, &ig, &cg, reg_map, coalesce_map);

    // Runs through the code and replaces each vreg with its allocated register
    replace_vregs(r, fn, reg_map, coalesce_map);
}

static int gpr_is_mov(AsmIns *ins) {
    return ins->op >= X86_MOV && ins->op <= X86_MOVZX;
}

static int gpr_is_redundant_mov(AsmIns *ins) {
    return ins->l.reg == ins->r.reg &&
           !((ins->op == X86_MOVSX || ins->op == X86_MOVZX) &&
             ins->l.size > ins->r.size); // Don't remove, e.g., movsx rax, ax
}

static int gpr_uses_left(AsmIns *ins) {
    // movs and setxx don't use their left argument, they only define it
    AsmOpcode op = ins->op;
    return X86_OPCODE_NARGS[op] >= 1 &&
           !(op >= X86_MOV && op <= X86_LEA) &&
           !(op >= X86_SETE && op <= X86_SETAE) &&
           op != X86_POP;
}

static int gpr_uses_right(AsmIns *ins) {
    // If it has 2 arguments, then it uses its right operand
    return X86_OPCODE_NARGS[ins->op] >= 2;
}

static int gpr_defs_left(AsmIns *ins) {
    AsmOpcode op = ins->op;
    return (op >= X86_MOV && op <= X86_LEA) ||
           (op >= X86_ADD && op <= X86_MUL) ||
           (op >= X86_AND && op <= X86_SAR) ||
           (op >= X86_SETE && op <= X86_SETAE) ||
           (op == X86_POP);
}

static int sse_is_mov(AsmIns *ins) {
    return ins->op >= X86_MOVSS && ins->op <= X86_MOVSD;
}

static int sse_is_redundant_mov(AsmIns *ins) {
    return ins->l.reg == ins->r.reg;
}

static int sse_uses_left(AsmIns *ins) {
    AsmOpcode op = ins->op;
    return X86_OPCODE_NARGS[op] >= 1 && !(op >= X86_MOVSS && op <= X86_MOVSD);
}

static int sse_uses_right(AsmIns *ins) {
    // If it has 2 arguments, then it uses its right operand
    return X86_OPCODE_NARGS[ins->op] >= 2;
}

static int sse_defs_left(AsmIns *ins) {
    AsmOpcode op = ins->op;
    return (op >= X86_MOVSS && op <= X86_MOVSD) ||
           (op >= X86_ADDSS && op <= X86_DIVSD);
}

static RegGroup GPR_REG_GROUP_INFO = {
    .num_pregs = LAST_GPR,
    .preg_names = GPR_NAMES[REG_Q],
    .uses_left = gpr_uses_left,
    .uses_right = gpr_uses_right,
    .defs_left = gpr_defs_left,
    .reg_op = OP_GPR,
    .is_mov = gpr_is_mov,
    .is_redundant_mov = gpr_is_redundant_mov,
    .in_mem_ops = 1,
};

static RegGroup SSE_REG_GROUP_INFO = {
    .num_pregs = LAST_SSE,
    .preg_names = SSE_REG_NAMES,
    .uses_left = sse_uses_left,
    .uses_right = sse_uses_right,
    .defs_left = sse_defs_left,
    .reg_op = OP_XMM,
    .is_mov = sse_is_mov,
    .is_redundant_mov = sse_is_redundant_mov,
    .in_mem_ops = 0,
};

void reg_alloc(Fn *fn) {
    if (!fn->last) {
        return; // Do nothing if the function is empty
    }
    alloc_regs(GPR_REG_GROUP_INFO, fn, fn->num_gprs);
    alloc_regs(SSE_REG_GROUP_INFO, fn, fn->num_sse_regs);
}
