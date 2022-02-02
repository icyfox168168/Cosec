
#include <assert.h>
#include <string.h>
#include <limits.h>

#include "RegAlloc.h"

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
// * Useful conceptual overview of coalescing:
//   https://www.cs.cmu.edu/afs/cs/academic/class/15745-s16/www/lectures/L23-Register-Coalescing.pdf

#define IG(graph, reg1, reg2) ((reg1) * (REG_MAX + (graph).num_vregs) + (reg2))

typedef struct {
    int num_vregs;       // Size of matrix is (num_vreg + REG_MAX)^2
    int *matrix;         // Bit matrix of edges
    int *num_neighbours; // Number of edges for each node in the graph
} InterferenceGraph;

static InterferenceGraph new_graph(int num_vregs) {
    int num_regs = num_vregs + REG_MAX;
    InterferenceGraph graph;
    graph.num_vregs = num_vregs;
    graph.matrix = calloc(num_regs * num_regs, sizeof(int));
    graph.num_neighbours = calloc(num_regs, sizeof(int));
    return graph;
}

static InterferenceGraph copy_graph(InterferenceGraph *g) {
    InterferenceGraph copy = *g;
    int num_regs = g->num_vregs + REG_MAX;
    copy.matrix = malloc(num_regs * num_regs * sizeof(int));
    memcpy(copy.matrix, g->matrix, num_regs * num_regs * sizeof(int));
    copy.num_neighbours = malloc(num_regs * sizeof(int));
    memcpy(copy.num_neighbours, g->num_neighbours, num_regs * sizeof(int));
    return copy;
}

static int node_exists(InterferenceGraph *g, int vreg) {
    // A node exists in the graph if its value along the diagonal (i.e. whether
    // it intersects with itself) is 1
    return g->matrix[IG(*g, REG_MAX + vreg, REG_MAX + vreg)];
}

static void add_node(InterferenceGraph *g, int reg) {
    g->matrix[IG(*g, reg, reg)] = 1;
}

static void remove_node(InterferenceGraph *g, int vreg) {
    // Remove a node from the graph by setting its value along the diagonal
    // (i.e. matrix[IG(vreg, vreg)]) to 0
    // Zero the row and column to remove edges with all the other nodes
    for (int reg = 0; reg < REG_MAX + g->num_vregs; reg++) {
        if (g->matrix[IG(*g, REG_MAX + vreg, reg)]) {
            g->num_neighbours[reg]--; // Decrement neighbours
        }
        g->matrix[IG(*g, REG_MAX + vreg, reg)] = 0;
        g->matrix[IG(*g, reg, REG_MAX + vreg)] = 0;
    }
    g->num_neighbours[REG_MAX + vreg] = 0;
}

static int edge_exists(InterferenceGraph *g, int reg1, int reg2) {
    return g->matrix[IG(*g, reg1, reg2)];
}

static void add_edge(InterferenceGraph *g, int reg1, int reg2) {
    // Mirror the matrix symmetrically around the diagonal
    g->matrix[IG(*g, reg1, reg2)] = 1;
    g->matrix[IG(*g, reg2, reg1)] = 1;
    g->num_neighbours[reg1]++;
    g->num_neighbours[reg2]++;
}

static InterferenceGraph build_graph(LiveRange *ranges, int num_vregs) {
    // Intersect all physical and virtual registers with each other to build
    // the intersection g (represented as a matrix). Only iterate over the
    // upper half of the leading diagonal in the matrix (for efficiency)
    InterferenceGraph g = new_graph(num_vregs);
    for (int reg1 = 0; reg1 < REG_MAX + num_vregs; reg1++) {
        LiveRange range1 = ranges[reg1];
        if (!range1) {
            continue; // reg1 isn't used
        }
        add_node(&g, reg1); // This reg is used
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
            }
        }
    }
    return g;
}

static void simplify_graph(InterferenceGraph *g, int *stack, int *num_stack) {
    while (1) { // Keep adding to the stack
        // Find the next reg with the minimum number of neighbours. This is
        // always guaranteed to put nodes with <REG_MAX neighbours onto the
        // stack first, and then spill nodes with the fewest neighbours
        int min_vreg = -1;
        int min_neighbours = INT_MAX;
        for (int vreg = 0; vreg < g->num_vregs; vreg++) {
            if (!node_exists(g, vreg)) {
                continue;
            }
            int num_neighbours = g->num_neighbours[REG_MAX + vreg];
            if (num_neighbours < min_neighbours) {
                min_vreg = vreg;
                min_neighbours = num_neighbours;
            }
        }
        if (min_vreg < 0) { // No more vregs in the graph; all on the stack
            break;
        }
        stack[(*num_stack)++] = min_vreg; // Add to the stack
        remove_node(g, min_vreg); // Remove from the graph
    }
}

static Reg * select_regs(InterferenceGraph *g, int *stack, int num_stack) {
    Reg *regs = malloc(g->num_vregs * sizeof(Reg));
    memset(regs, 0xff, g->num_vregs * sizeof(Reg)); // Set every bit
    while (num_stack) { // Work our way down the stack allocating regs
        int vreg = stack[--num_stack]; // Remove from the stack

        // Find all physical regs interfering with 'vreg'
        int interference[REG_MAX];
        memset(interference, 0, sizeof(int) * REG_MAX);
        for (int p = 0; p < REG_MAX; p++) { // Physical regs
            interference[p] |= edge_exists(g, REG_MAX + vreg, p);
        }
        for (int v = 0; v < g->num_vregs; v++) { // vregs
            if (regs[v] != ~0) {
                int in = edge_exists(g, REG_MAX + vreg, REG_MAX + v);
                interference[regs[v]] = in;
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

static Reg * colour_graph(InterferenceGraph *g) {
    // We're going to destroy the data in the interference graph by removing
    // nodes, so create a copy we can modify
    InterferenceGraph copy = copy_graph(g);
    int stack[g->num_vregs];
    int num_stack = 0;
    simplify_graph(&copy, stack, &num_stack);
    return select_regs(g, stack, num_stack);
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
    InterferenceGraph graph = build_graph(ranges, fn->num_vregs);
    Reg *reg_map = colour_graph(&graph);
    replace_vregs(fn, reg_map);
}
