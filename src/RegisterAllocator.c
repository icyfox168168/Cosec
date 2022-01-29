
#include <assert.h>
#include <string.h>

#include "RegisterAllocator.h"

#define IG(graph, reg1, reg2) ((reg1) * (REG_MAX + graph.num_vregs) + (reg2))

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
    // the intersection graph (represented as a matrix)
    for (int reg1 = 0; reg1 < num_regs; reg1++) {
        if (ranges[reg1].num_intervals == 0) {
            continue; // reg1 isn't used
        }
        for (int reg2 = 0; reg2 < num_regs; reg2++) {
            if (ranges[reg2].num_intervals == 0) {
                continue; // reg2 isn't used
            }
            if (ranges_intersect(ranges[reg1], ranges[reg2])) {
                graph.matrix[IG(graph, reg1, reg2)] = 1;
                graph.num_neighbours[reg1]++;
            }
        }
    }
    return graph;
}

static InterferenceGraph copy_graph(InterferenceGraph graph) {
    int num_regs = graph.num_vregs + REG_MAX;
    InterferenceGraph copy;
    copy.num_vregs = graph.num_vregs;
    size_t matrix_size = num_regs * num_regs * sizeof(int);
    copy.matrix = malloc(matrix_size);
    size_t neighbours_size = num_regs * sizeof(int);
    copy.num_neighbours = malloc(neighbours_size);
    memcpy(copy.matrix, graph.matrix, matrix_size);
    memcpy(copy.num_neighbours, graph.num_neighbours, neighbours_size);
    return copy;
}

// A node exists in the graph if its value along the diagonal (i.e. whether it
// intersects with itself) is 1
static int node_exists(InterferenceGraph graph, int vreg) {
    return graph.matrix[IG(graph, REG_MAX + vreg, REG_MAX + vreg)];
}

static int num_neighbours(InterferenceGraph graph, int vreg) {
    return graph.num_neighbours[REG_MAX + vreg];
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

// Makes 'reg' interfere with everything that 'vreg' interferes with
static void copy_interference(InterferenceGraph graph, int vreg, int reg) {
    for (int other_vreg = 0; other_vreg < graph.num_vregs; other_vreg++) {
        if (graph.matrix[IG(graph, REG_MAX + vreg, REG_MAX + other_vreg)]) {
            graph.matrix[IG(graph, reg, REG_MAX + other_vreg)] = 1;
            graph.matrix[IG(graph, REG_MAX + other_vreg, reg)] = 1;
        }
    }
}

// Returns NULL (and populates 'to_spill') if the graph isn't colourable with
// REG_MAX registers. Otherwise, returns a mapping from vregs to 'Reg's
static Reg * colour_graph(AsmFn *fn, InterferenceGraph graph) {
    // NOTE: assumes we don't need to handle spilling yet
    InterferenceGraph copy = copy_graph(graph);

    // Stack of vregs which we'll allocate colours to in the order they appear
    int stack[fn->num_vregs];
    int num_stack = 0;

    // Keep adding to the stack
    while (1) {
        // Find the next vreg with less than REG_MAX neighbours
        int found = 0;
        for (int vreg = 0; vreg < fn->num_vregs; vreg++) {
            if (!node_exists(copy, vreg)) {
                continue;
            }
            if (num_neighbours(copy, vreg) < REG_MAX) { // Found a reg
                stack[num_stack++] = vreg; // Add to the stack
                remove_node(copy, vreg);  // Remove from the graph
                found = 1;
                break; // Start again
            }
        }
        if (!found) { // No more vregs with less than REG_MAX neighbours
            break;
        }
    }

    // Now work our way up the stack allocating registers
    Reg *regs = malloc(fn->num_vregs * sizeof(Reg)); // Init REG_NONE
    while (num_stack) {
        int vreg = stack[--num_stack]; // Remove from the stack

        // Find the first reg not interfering with 'vreg'
        int found = 0;
        for (int reg = 0; reg < REG_MAX; reg++) {
            if (!graph.matrix[IG(graph, REG_MAX + vreg, reg)]) {
                regs[vreg] = reg; // Found a reg
                copy_interference(graph, vreg, reg);
                found = 1;
                break;
            }
        }
        assert(found); // No spilling yet
    }
    return regs;
}

// Change all the vreg operands in the assembly to their allocated registers
static void replace_vregs(AsmFn *fn, Reg *reg_map) {
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        for (AsmIns *ins = bb->asm_head; ins; ins = ins->next) {
            if (ins->l.type == OP_VREG) {
                ins->l.reg = reg_map[ins->l.vreg];
                ins->l.type = OP_REG;
            }
            if (ins->r.type == OP_VREG) {
                ins->r.reg = reg_map[ins->r.vreg];
                ins->r.type = OP_REG;
            }

            // Remove redundant movs
            if (ins->op == X86_MOV && ins->l.type == OP_REG &&
                    ins->r.type == OP_REG && ins->l.reg == ins->r.reg) {
                delete_asm(ins);
            }
        }
    }
}

void reg_alloc(AsmFn *fn, LiveRange *ranges) {
    if (fn->num_vregs <= 0 || !fn->last) {
        return; // No vregs to allocate, or the function is empty
    }
    print_live_ranges(fn, ranges);
    InterferenceGraph graph = build_graph(ranges, fn->num_vregs);
    Reg *reg_map = colour_graph(fn, graph);
    replace_vregs(fn, reg_map);
}
