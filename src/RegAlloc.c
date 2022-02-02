
#include <assert.h>
#include <string.h>
#include <limits.h>
#include <stdio.h>

#include "RegAlloc.h"

// The register allocator is heavily based on the classic graph colouring
// algorithm presented in the book:
//
//   Modern Compiler Implementation in C, Andrew W. Appel, Chapter 11
//
// Including the conservative coalescing algorithm. I highly recommend giving
// it a read for a great conceptual overview.
//
// Additional resources I found helpful:
// * Another set of slides on the graph colouring algorithm:
//     http://web.cecs.pdx.edu/~mperkows/temp/register-allocation.pdf
// * Another article on the graph colouring algorithm:
//     https://www.lighterra.com/papers/graphcoloring/
// * A set of slides on liveness analysis:
//     https://proglang.informatik.uni-freiburg.de/teaching/compilerbau/2016ws/10-liveness.pdf
// * Useful practical information on implementing liveness analysis (including
//   the worklist-based algorithm used in 'Liveness.c'):
//     https://engineering.purdue.edu/~milind/ece573/2015fall/project/step7/step7.html
// * Conceptual overview of coalescing:
//     https://www.cs.cmu.edu/afs/cs/academic/class/15745-s16/www/lectures/L23-Register-Coalescing.pdf

// Accessing the interference and coalescing graph 'matrix' (a linear array
// that we turn into a doubly-indexed one)
#define G(g, reg1, reg2) ((reg1) * (REG_MAX + (g)->num_vregs) + (reg2))

// Use the same graph structure for the interference and the coalescing graphs.
// The first REG_MAX registers in 'matrix' (and in 'num_edges') are nodes for
// the physical registers; the remaining 'num_vregs' nodes are for virtual
// registers (same as for the 'LiveRange *ranges' array)
typedef struct {
    int num_vregs;  // Size of matrix is (num_vreg + REG_MAX)^2
    int *matrix;    // Square bit matrix of edges
    int *num_edges; // Number of edges for each node in the graph
} RegGraph;

static RegGraph new_reg_graph(int num_vregs) {
    int num_regs = num_vregs + REG_MAX;
    RegGraph g;
    g.num_vregs = num_vregs;
    g.matrix = calloc(num_regs * num_regs, sizeof(int));
    g.num_edges = calloc(num_regs, sizeof(int));
    return g;
}

static RegGraph copy_reg_graph(RegGraph *g) {
    RegGraph copy = *g;
    int num_regs = g->num_vregs + REG_MAX;
    copy.matrix = malloc(num_regs * num_regs * sizeof(int));
    memcpy(copy.matrix, g->matrix, num_regs * num_regs * sizeof(int));
    copy.num_edges = malloc(num_regs * sizeof(int));
    memcpy(copy.num_edges, g->num_edges, num_regs * sizeof(int));
    return copy;
}

static int node_exists(RegGraph *g, int reg) {
    // A node exists in the graph if its value along the diagonal (i.e. whether
    // it intersects with itself) is 1
    return g->matrix[G(g, reg, reg)];
}

static void mark_node_exists(RegGraph *g, int reg) {
    g->matrix[G(g, reg, reg)] = 1;
}

static void remove_node(RegGraph *g, int vreg) {
    // Remove a node from the graph by setting its value along the diagonal
    // (i.e. matrix[G(vreg, vreg)]) to 0
    // Zero the row and column to remove edges with all the other nodes
    for (int reg = 0; reg < REG_MAX + g->num_vregs; reg++) {
        if (g->matrix[G(g, REG_MAX + vreg, reg)]) {
            g->num_edges[reg]--; // Decrement edges
        }
        g->matrix[G(g, REG_MAX + vreg, reg)] = 0;
        g->matrix[G(g, reg, REG_MAX + vreg)] = 0;
    }
    g->num_edges[REG_MAX + vreg] = 0;
}

static int edge_exists(RegGraph *g, int reg1, int reg2) {
    return g->matrix[G(g, reg1, reg2)];
}

static int num_edges(RegGraph *g, int reg) {
    return g->num_edges[reg];
}

static void add_edge(RegGraph *g, int reg1, int reg2) {
    // Mirror the matrix symmetrically around the leading diagonal
    g->matrix[G(g, reg1, reg2)] = 1;
    g->matrix[G(g, reg2, reg1)] = 1;
    g->num_edges[reg1]++;
    g->num_edges[reg2]++;
}

// The interference graph tells us whether two regs interfere with each other
static RegGraph build_interference_graph(LiveRange *ranges, int num_vregs) {
    // Intersect all physical and virtual registers with each other to build
    // the intersection g (represented as a matrix). Only iterate over the
    // upper half of the leading diagonal in the matrix (for efficiency)
    RegGraph g = new_reg_graph(num_vregs);
    for (int reg1 = 0; reg1 < REG_MAX + num_vregs; reg1++) {
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
            if (reg1 < REG_MAX && reg2 < REG_MAX) {
                continue; // Don't care about physical register interference
            }
            if (ranges_intersect(range1, range2)) {
                add_edge(&g, reg1, reg2);
                printf("intersect %d %d\n", reg1 - REG_MAX, reg2 - REG_MAX);
            }
        }
    }
    return g;
}

// The coalescing graph tells us whether two regs are candidates for coalescing;
// that is, related by a mov and their live ranges don't interfere other than
// for that mov
static RegGraph build_coalescing_graph(AsmFn *fn, LiveRange *ranges) {
    // Iterate over all instructions to find move-related regs
    RegGraph g = new_reg_graph(fn->num_vregs);
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        for (AsmIns *mov = bb->asm_head; mov; mov = mov->next) {
            // Check if the instruction is a mov that relates two regs; also
            // make sure the two regs aren't both pregs - one must be a vreg
            if (mov->op == X86_MOV &&
                    (mov->l.type == OP_REG || mov->l.type == OP_VREG) &&
                    (mov->r.type == OP_REG || mov->r.type == OP_VREG) &&
                    !(mov->l.type == OP_REG && mov->r.type == OP_REG)) {
                // Convert each reg to a RegGraph index
                int reg1 = mov->l.type == OP_REG ? (int) mov->l.reg :
                           REG_MAX + mov->l.vreg;
                int reg2 = mov->r.type == OP_REG ? (int) mov->r.reg :
                           REG_MAX + mov->r.vreg;

                // This mov is a coalescing candidate if the live ranges of
                // reg1 and reg2 ONLY intersect at the mov
                LiveRange range1 = ranges[reg1];
                LiveRange range2 = ranges[reg2];
                LiveRange intersect = range_intersection(range1, range2);
                if (intersect && !intersect->next &&    // One interval
                        intersect->start == mov->idx && // Interval IS the mov
                        intersect->end == mov->idx) {
                    mark_node_exists(&g, reg1);
                    mark_node_exists(&g, reg2);
                    add_edge(&g, reg1, reg2);
                }
            }
        }
    }
    return g;
}

// Removes one non-move related node of insignificant degree (degree <REG_MAX)
// from the interference graph and pushes it onto the stack. Returns 1 if we
// successfully found a node to remove, or 0 if we didn't.
static int simplify(RegGraph *ig, RegGraph *cg, int *stack, int *num_stack) {
    // Find a non-move related node of insignificant degree
    for (int vreg = 0; vreg < ig->num_vregs; vreg++) {
        if (!node_exists(ig, REG_MAX + vreg)) {
            continue; // The node doesn't exist
        }
//        if (num_edges(cg, REG_MAX + vreg) > 0) {
//            continue; // This node is move related
//        }
        if (num_edges(ig, REG_MAX + vreg) >= REG_MAX) {
            continue; // This node is of significant degree (>=REG_MAX edges)
        }
        // Otherwise, we found one!
        stack[(*num_stack)++] = vreg; // Add to the stack
        remove_node(ig, vreg); // Remove from the graph
        return 1;
    }
    return 0;
}

static Reg * select_regs(RegGraph *ig, int *stack, int num_stack) {
    Reg *regs = malloc(ig->num_vregs * sizeof(Reg));
    memset(regs, 0xff, ig->num_vregs * sizeof(Reg)); // Set every bit
    while (num_stack) { // Work our way down the stack allocating regs
        int vreg = stack[--num_stack]; // Pop from the stack

        // Find all physical regs interfering with 'vreg' (both from actual
        // pregs and from other vregs that have already been allocated)
        int interference[REG_MAX];
        for (int p = 0; p < REG_MAX; p++) { // Physical regs
            interference[p] = edge_exists(ig, REG_MAX + vreg, p);
        }
        for (int other = 0; other < ig->num_vregs; other++) { // vregs
            if (regs[other] != ~0) {
                int reg1 = REG_MAX + vreg, reg2 = REG_MAX + other;
                interference[regs[other]] |= edge_exists(ig, reg1, reg2);
            }
        }

        // Find the first physical reg not interfering with 'vreg'
        Reg reg = 0;
        while (interference[reg]) { reg++; }
        if (reg >= REG_MAX) { // All registers interfere -> spill
            assert(0); // Spilling not yet implemented
        }
        regs[vreg] = reg;
    }
    return regs;
}

static Reg * colour_graph(RegGraph *ig, RegGraph *cg) {
    // We're going to destroy the data in the interference graph by removing
    // nodes, so create a copy we can modify
    RegGraph copy = copy_reg_graph(ig);

    // Set up a stack of nodes to define an order in which to colour the vregs
    int stack[ig->num_vregs];
    int num_stack = 0;

    // Keep simplifying the graph until we can't
    while (simplify(&copy, cg, stack, &num_stack)) {}

    // Colour the regs in the order they pop off the stack
    return select_regs(ig, stack, num_stack);
}

static void replace_vregs_for_ins(AsmIns *ins, Reg *reg_map) {
    if (ins->l.type == OP_VREG) { // Left operand
        assert(reg_map[ins->l.vreg] != ~0);
        ins->l.reg = reg_map[ins->l.vreg];
        ins->l.type = OP_REG;
    }
    if (ins->r.type == OP_VREG) { // Right operand
        assert(reg_map[ins->r.vreg] != ~0);
        ins->r.reg = reg_map[ins->r.vreg];
        ins->r.type = OP_REG;
    }
    if (ins->op == X86_MOV &&
            ins->l.type == OP_REG &&
            ins->r.type == OP_REG &&
            ins->l.reg == ins->r.reg) { // Remove redundant movs
        delete_asm(ins);
    }
}

// Change all the vreg operands in the assembly to their allocated registers
static void replace_vregs(AsmFn *fn, Reg *reg_map) {
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        for (AsmIns *ins = bb->asm_head; ins; ins = ins->next) {
            replace_vregs_for_ins(ins, reg_map);
        }
    }
}

void reg_alloc(AsmFn *fn, LiveRange *ranges) {
    if (fn->num_vregs == 0 || !fn->last) {
        return; // No vregs to allocate, or the function is empty
    }
    print_live_ranges(ranges, fn->num_vregs);
    RegGraph ig = build_interference_graph(ranges, fn->num_vregs);
    RegGraph cg = build_coalescing_graph(fn, ranges);
    Reg *reg_map = colour_graph(&ig, &cg);
    replace_vregs(fn, reg_map);
}
