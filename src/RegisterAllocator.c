
#include <assert.h>
#include <string.h>
#include <limits.h>

#include "RegisterAllocator.h"

#define IG(graph, reg1, reg2) ((reg1) * (REG_MAX + (graph).num_vregs) + (reg2))

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
    int num_vregs;       // Size of matrix is (num_vreg + REG_MAX)^2
    int *matrix;         // Bit matrix of edges
    int *num_neighbours; // Number of edges for each node in the graph
} InterferenceGraph;

static InterferenceGraph build_graph(LiveRange *ranges, int num_vregs) {
    int num_regs = num_vregs + REG_MAX;
    InterferenceGraph graph;
    graph.num_vregs = num_vregs;
    graph.matrix = calloc(num_regs * num_regs, sizeof(int));
    graph.num_neighbours = calloc(num_regs, sizeof(int));

    // Intersect all physical and virtual registers with each other to build
    // the intersection graph (represented as a matrix). Only iterate over the
    // upper half of the leading diagonal in the matrix (for efficiency)
    for (int reg1 = 0; reg1 < num_regs; reg1++) {
        LiveRange r1 = ranges[reg1];
        if (!r1) {
            continue; // reg1 isn't used
        }
        graph.matrix[IG(graph, reg1, reg1)] = 1; // This reg is used
        for (int reg2 = 0; reg2 < reg1; reg2++) { // Only iterate the upper half
            LiveRange r2 = ranges[reg2];
            if (!r2) {
                continue; // reg2 isn't used
            }
            if (ranges_intersect(r1, r2)) {
                // Mirror the matrix symmetrically around the diagonal
                graph.matrix[IG(graph, reg1, reg2)] = 1;
                graph.matrix[IG(graph, reg2, reg1)] = 1;
                graph.num_neighbours[reg1]++;
                graph.num_neighbours[reg2]++;
            }
        }
    }
    return graph;
}

// Create a new copy of the interference graph that we can modify
static InterferenceGraph copy_graph(InterferenceGraph graph) {
    int num_regs = graph.num_vregs + REG_MAX;
    InterferenceGraph copy = graph;
    copy.matrix = malloc(num_regs * num_regs * sizeof(int));
    memcpy(copy.matrix, graph.matrix, num_regs * num_regs * sizeof(int));
    copy.num_neighbours = malloc(num_regs * sizeof(int));
    memcpy(copy.num_neighbours, graph.num_neighbours, num_regs * sizeof(int));
    return copy;
}

// A node exists in the graph if its value along the diagonal (i.e. whether it
// intersects with itself) is 1
static int node_exists(InterferenceGraph graph, int vreg) {
    return graph.matrix[IG(graph, REG_MAX + vreg, REG_MAX + vreg)];
}

// Remove a node from the graph by setting its value along the diagonal (i.e.
// matrix[IG(vreg, vreg)]) to 0
static void remove_node(InterferenceGraph graph, int vreg) {
    // Zero the row and column to remove edges with all the other nodes
    for (int reg = 0; reg < REG_MAX + graph.num_vregs; reg++) {
        if (graph.matrix[IG(graph, REG_MAX + vreg, reg)]) {
            graph.num_neighbours[reg]--; // Decrement neighbours
        }
        graph.matrix[IG(graph, REG_MAX + vreg, reg)] = 0;
        graph.matrix[IG(graph, reg, REG_MAX + vreg)] = 0;
    }
    graph.num_neighbours[REG_MAX + vreg] = 0;
}

// Returns NULL (and populates 'to_spill') if the graph isn't colourable with
// REG_MAX registers. Otherwise, returns a mapping from vregs to 'Reg's
// Note: destroys the data stored in the interference graph
static Reg * colour_graph(AsmFn *fn, InterferenceGraph g) {
    // NOTE: assumes we don't need to handle spilling yet
    InterferenceGraph copy = copy_graph(g);

    // Keep a stack of vregs, which tells us the order to colour them in
    int stack[fn->num_vregs];
    int num_stack = 0;
    while (1) { // Keep adding to the stack
        // Find the next reg with the minimum number of neighbours. This is
        // always guaranteed to put nodes with <REG_MAX neighbours onto the
        // stack first, and then spill nodes with the fewest neighbours
        int min_vreg = -1;
        int min_neighbours = INT_MAX;
        for (int vreg = 0; vreg < fn->num_vregs; vreg++) {
            if (!node_exists(copy, vreg)) {
                continue;
            }
            int num_neighbours = copy.num_neighbours[REG_MAX + vreg];
            if (num_neighbours < min_neighbours) {
                min_vreg = vreg;
                min_neighbours = num_neighbours;
            }
        }
        if (min_vreg < 0) { // No more vregs in the graph; all on the stack
            break;
        }
        stack[num_stack++] = min_vreg; // Add to the stack
        remove_node(copy, min_vreg); // Remove from the graph
    }

    // Now work our way down the stack allocating registers
    int allocated[fn->num_vregs];
    memset(allocated, 0, fn->num_vregs * sizeof(int));
    Reg *regs = malloc(fn->num_vregs * sizeof(Reg));
    while (num_stack) {
        int vreg = stack[--num_stack]; // Remove from the stack

        // Find all physical regs interfering with 'vreg'
        int interference[REG_MAX];
        memset(interference, 0, sizeof(int) * REG_MAX);
        for (int preg = 0; preg < REG_MAX; preg++) { // Physical regs
            interference[preg] |= g.matrix[IG(g, REG_MAX + vreg, preg)];
        }
        for (int other = 0; other < fn->num_vregs; other++) { // Vregs
            int interferes = g.matrix[IG(g, REG_MAX + vreg, REG_MAX + other)];
            if (allocated[other] && interferes) {
                interference[regs[other]] = 1;
            }
        }

        // Find the first physical reg not interfering with 'vreg'
        int reg = 0;
        while (interference[reg]) { reg++; }
        if (reg >= REG_MAX) { // All registers interfere -> spill
            assert(0); // Spilling not yet implemented
        }
        regs[vreg] = reg;
        allocated[vreg] = 1;
    }
    return regs;
}

static void replace_vregs_for_ins(AsmIns *ins, Reg *reg_map) {
    if (ins->l.type == OP_VREG) { // Left operand
        ins->l.reg = reg_map[ins->l.vreg];
        ins->l.type = OP_REG;
    }
    if (ins->r.type == OP_VREG) { // Right operand
        ins->r.reg = reg_map[ins->r.vreg];
        ins->r.type = OP_REG;
    }

    // Remove redundant movs
    if (ins->op == X86_MOV && ins->l.type == OP_REG && ins->r.type == OP_REG &&
            ins->l.reg == ins->r.reg) {
        delete_asm(ins);
    }
}

// Change all the vreg operands in the assembly to their allocated registers
static void replace_vregs(AsmFn *fn, Reg *reg_map) {
    // Iterate over all instructions
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
    Reg *reg_map = colour_graph(fn, graph);
    replace_vregs(fn, reg_map);
}
