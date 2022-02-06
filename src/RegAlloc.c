
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
#define G(g, reg1, reg2) ((reg1) * (g)->num_regs + (reg2))

// Use the same graph structure for the interference and the coalescing graphs.
// The first LAST_PREG registers in 'matrix' (and in 'num_edges') are nodes for
// the physical registers; the remaining 'num_regs' nodes are for virtual
// registers (same as for the 'LiveRange *ranges' array)
typedef struct {
    int num_regs;   // Size of matrix (LAST_PREG + number of vregs)
    int *matrix;    // Square bit matrix of edges
    int *num_edges; // Number of edges for each node in the graph
} RegGraph;

static void print_reg(int reg) {
    if (reg < LAST_PREG) {
        printf("%s", REG_NAMES[reg][REG_Q]); // preg
    } else {
        printf("%%%d", reg - LAST_PREG); // vreg
    }
}

static RegGraph new_reg_graph(int num_regs) {
    RegGraph g;
    g.num_regs = num_regs;
    g.matrix = calloc(num_regs * num_regs, sizeof(int));
    g.num_edges = calloc(num_regs, sizeof(int));
    return g;
}

static RegGraph copy_reg_graph(RegGraph *g) {
    RegGraph copy = *g;
    copy.matrix = malloc(g->num_regs * g->num_regs * sizeof(int));
    memcpy(copy.matrix, g->matrix, g->num_regs * g->num_regs * sizeof(int));
    copy.num_edges = malloc(g->num_regs * sizeof(int));
    memcpy(copy.num_edges, g->num_edges, g->num_regs * sizeof(int));
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

static void remove_node(RegGraph *g, int to_remove) {
    // Remove a node from the graph by setting its value along the diagonal
    // (i.e. matrix[G(vreg, vreg)]) to 0
    // Zero the row and column to remove edges with all the other nodes
    for (int reg = 0; reg < g->num_regs; reg++) {
        if (g->matrix[G(g, to_remove, reg)]) {
            g->num_edges[reg]--; // Decrement edges
        }
        g->matrix[G(g, to_remove, reg)] = 0;
        g->matrix[G(g, reg, to_remove)] = 0;
    }
    g->num_edges[to_remove] = 0;
}

static int edge_exists(RegGraph *g, int reg1, int reg2) {
    return g->matrix[G(g, reg1, reg2)];
}

static int num_edges(RegGraph *g, int reg) {
    return g->num_edges[reg];
}

static void add_edge(RegGraph *g, int reg1, int reg2) {
    // Mirror the matrix symmetrically around the leading diagonal
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

// The interference graph tells us whether two regs interfere with each other
static RegGraph build_interference_graph(LiveRange *ranges, int num_regs) {
    // Intersect all physical and virtual registers with each other to build
    // the intersection g (represented as a matrix). Only iterate over the
    // upper half of the leading diagonal in the matrix (for efficiency)
    RegGraph g = new_reg_graph(num_regs);
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
            if (reg1 < LAST_PREG && reg2 < LAST_PREG) {
                continue; // Don't care about physical register interference
            }
            if (ranges_intersect(range1, range2)) {
                add_edge(&g, reg1, reg2);
                print_reg(reg1);
                printf(" intersects with ");
                print_reg(reg2);
                printf("\n");
            }
        }
    }
    return g;
}

// The coalescing graph tells us whether two regs are candidates for coalescing;
// that is, related by a mov and their live ranges don't interfere other than
// for that mov
// It's possible to coalesce across movzx and movsx too!
static RegGraph build_coalescing_graph(Fn *fn, LiveRange *ranges) {
    // Iterate over all instructions to find move-related regs
    RegGraph g = new_reg_graph(fn->num_regs);
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        for (AsmIns *mov = bb->asm_head; mov; mov = mov->next) {
            // Check if the instruction is a mov that relates two regs; also
            // make sure the two regs aren't both pregs - one must be a vreg
            if ((mov->op >= X86_MOV && mov->op <= X86_MOVZX) &&
                    mov->l.type == OP_REG && mov->r.type == OP_REG &&
                    !(mov->l.reg < LAST_PREG && mov->r.type < LAST_PREG)) {
                // This mov is a coalescing candidate if the live ranges of
                // reg1 and reg2 ONLY intersect at the mov
                LiveRange range1 = ranges[mov->l.reg];
                LiveRange range2 = ranges[mov->r.reg];
                LiveRange intersect = range_intersection(range1, range2);
                if (intersect && !intersect->next &&    // Only one interval
                        intersect->start == mov->idx && // Interval IS the mov
                        intersect->end == mov->idx) {
                    mark_node_exists(&g, mov->l.reg);
                    mark_node_exists(&g, mov->r.reg);
                    add_edge(&g, mov->l.reg, mov->r.reg);
                }
            }
        }
    }
    return g;
}

// Removes one non-move related node of insignificant degree (degree <LAST_PREG)
// from the interference graph and pushes it onto the stack. Returns 1 if we
// successfully found a node to remove, or 0 if we didn't.
static int simplify(RegGraph *ig, RegGraph *cg, int *stack, int *num_stack) {
    // Find a non-move related node of insignificant degree
    for (int vreg = LAST_PREG; vreg < ig->num_regs; vreg++) {
        if (!node_exists(ig, vreg)) {
            continue; // The node doesn't exist
        }
        if (num_edges(cg, vreg) > 0) {
            continue; // This node is move related
        }
        if (num_edges(ig, vreg) >= LAST_PREG) {
            continue; // This node is of significant degree (>=LAST_PREG edges)
        }
        stack[(*num_stack)++] = vreg; // Add to the stack
        remove_node(ig, vreg); // Remove from graphs
        remove_node(cg, vreg);
        printf("simplifying ");
        print_reg(vreg);
        printf("\n");
        return 1;
    }
    return 0;
}

// Calculates the Brigg's criteria for coalescing for two nodes
//   Nodes a and b can be coalesced if the resulting node ab has fewer than
//   LAST_PREG nodes of significant degree
// Basically, calculate the degree of every (unique) neighbour of a and b and
// count the number of these neighbours that have significant degree
static int briggs_criteria(RegGraph *ig, int reg1, int reg2) {
    int count = 0;
    int seen[ig->num_regs];
    memset(seen, 0, sizeof(int) * ig->num_regs);
    for (int neighbour = 0; neighbour < ig->num_regs; neighbour++) {
        if ((edge_exists(ig, reg1, neighbour) || // Neighbour of reg1?
                edge_exists(ig, reg2, neighbour)) && // of reg2?
                !seen[neighbour]) { // Unique?
            seen[neighbour] = 1;
            if (num_edges(ig, neighbour) >= LAST_PREG) { // Significant?
                count++;
            }
        }
    }
    return count;
}

// Performs conservative coalescing on one pair of move-related nodes using the
// Brigg's criteria. Returns 1 if two nodes were coalesced, or 0 otherwise
static int coalesce(RegGraph *ig, RegGraph *cg, int *coalesce_map) {
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
            if (briggs_criteria(ig, reg1, reg2) >= LAST_PREG) {
                continue; // Can't coalesce
            }
            // Coalesce one node into the other; if one of the regs is a preg,
            // then make sure we coalesce the vreg into it
            int to_coalesce = reg1 < LAST_PREG ? reg2 : reg1; // Pick the vreg
            int target = to_coalesce == reg1 ? reg2 : reg1; // The other one
            copy_edges(ig, to_coalesce, target);
            copy_edges(cg, to_coalesce, target);
            remove_node(ig, to_coalesce);
            remove_node(cg, to_coalesce);
            coalesce_map[to_coalesce - LAST_PREG] = target;
            printf("coalescing ");
            print_reg(to_coalesce);
            printf(" into ");
            print_reg(target);
            printf("\n");
            return 1;
        }
    }
    return 0; // No nodes to coalesce
}

// Freeze looks for a move-related node of insignificant degree that we can
// freeze the moves for (give up hope of coalescing them). Returns 1 if we
// found a node to freeze, or 0 otherwise
static int freeze(RegGraph *ig, RegGraph *cg) {
    // Find a move related node of insignificant degree
    for (int vreg = LAST_PREG; vreg < ig->num_regs; vreg++) {
        if (!node_exists(ig, vreg)) {
            continue; // The node doesn't exist
        }
        if (num_edges(cg, vreg) == 0) {
            continue; // This node is NOT move related
        }
        if (num_edges(ig, vreg) >= LAST_PREG) {
            continue; // This node is of significant degree (>=LAST_PREG edges)
        }
        remove_node(cg, vreg); // Remove from coalesce
        printf("freezing ");
        print_reg(vreg);
        printf("\n");
        return 1; // Found a node to freeze
    }
    return 0; // No nodes to freeze
}

// Spill looks for a significant degree node to remove from the interference
// graph and push on to the stack as a potential spill (we won't know for sure
// until we try select registers though)
static int spill(RegGraph *ig, RegGraph *cg, int *stack, int *num_stack) {
    // Find a node of significant degree
    for (int vreg = LAST_PREG; vreg < ig->num_regs; vreg++) {
        if (!node_exists(ig, vreg)) {
            continue; // The node doesn't exist
        }
        if (num_edges(ig, vreg) < LAST_PREG) {
            continue; // This node isn't of significant degree
        }
        stack[(*num_stack)++] = vreg; // Add to the stack
        remove_node(ig, vreg); // Remove from graphs
        remove_node(cg, vreg);
        printf("spilling ");
        print_reg(vreg);
        printf("\n");
        return 1;
    }
    return 0; // No nodes to spill
}

// Select keeps popping vregs off the stack and assigning physical registers
// until it hits a vreg that NEEDS to be spilled (not handled yet)
static void select_regs(RegGraph *ig, int *stack, int num_stack, Reg *reg_map,
                        int *coalesce_map) {
    // For each of the coalesced regs, we need to copy across their
    // interferences in the original interference graph ('coalesce' modified a
    // COPY) to the target reg they were coalesced into
    for (int vreg = LAST_PREG; vreg < ig->num_regs; vreg++) {
        int target = coalesce_map[vreg - LAST_PREG];
        if (target != -1) { // If 'vreg' was coalesced into 'target'
            copy_edges(ig, vreg, target);
        }
    }

    memset(reg_map, 0xff, (ig->num_regs - LAST_PREG) * sizeof(Reg));
    while (num_stack) { // Work our way down the stack allocating regs
        int vreg = stack[--num_stack]; // Pop from the stack

        // Find the first preg not interfering with 'vreg'
        int preg = 0;
        while (edge_exists(ig, vreg, preg)) {
            preg++;
        }
        if (preg >= LAST_PREG) { // All pregs interfere -> spill
            assert(0); // No spilling yet
        }
        reg_map[vreg - LAST_PREG] = preg;
        printf("allocating ");
        print_reg(vreg);
        printf(" to ");
        print_reg(preg);
        printf("\n");

        // Copy the regs that interfere with this vreg to the allocated preg
        copy_edges(ig, vreg, preg);
    }
}

static void colour_graph(RegGraph *ig, RegGraph *cg, Reg *reg_map,
                         int *coalesce_map) {
    // Set up a stack of nodes to define an order in which to colour the vregs
    int stack[ig->num_regs - LAST_PREG];
    int num_stack = 0;

    // Keep track of which nodes we've coalesce_map into what. Maps vreg -> reg
    // (i.e. from the set of all vregs -> the set of all preg and vregs)
    memset(coalesce_map, 0xff, sizeof(int) * (ig->num_regs - LAST_PREG));

    // We're going to destroy the data in the interference graph by removing
    // nodes, so create a copy we can modify
    RegGraph ig2 = copy_reg_graph(ig);
    while (1) { // Keep spilling until we've removed ALL nodes from the graph
        while (1) { // Keep freezing until only significant degree nodes remain
            // Repeat simplification and coalescing until only significant-
            // degree or move-related nodes remain, ensuring each of simplify
            // and coalesce are run at least once
            int found_simplify = 1, found_coalesce;
            while (1) {
                // Keep simplifying until we can't
                while (simplify(&ig2, cg, stack, &num_stack)) {
                    found_simplify = 1;
                }
                if (!found_simplify) {
                    break;
                }
                // Keep coalescing until we can't
                found_coalesce = 0;
                while (coalesce(&ig2, cg, coalesce_map)) {
                    found_coalesce = 1;
                }
                if (!found_coalesce) {
                    break;
                }
                found_simplify = 0;
            }
            // Freeze a move-related node we can't simplify and try again
            if (!freeze(&ig2, cg)) {
                break; // Nothing to freeze
            }
        }
        // Only significant degree nodes remain, so spill one
        if (!spill(&ig2, cg, stack, &num_stack)) {
            break; // Nothing to spill
        }
    }
    // Colour the regs in the order they pop off the stack
    select_regs(ig, stack, num_stack, reg_map, coalesce_map);
}

static int map_vreg(int vreg, Reg *reg_map, int *coalesce_map) {
    if (vreg < LAST_PREG) {
        return vreg; // Not a vreg
    }
    int reg = vreg;
    // Find the end of the coalescing chain (e.g., %3 -> %2 -> rax)
    while (reg >= LAST_PREG && coalesce_map[reg - LAST_PREG] != -1) {
        reg = coalesce_map[reg - LAST_PREG];
    }
    if (reg >= LAST_PREG) {
        // 'reg' might be the original vreg or a coalesced vreg
        reg = reg_map[reg - LAST_PREG];
    }
    assert(reg != -1);
    return reg;
}

static void replace_vreg(AsmOperand *o, Reg *reg_map, int *coalesce_map) {
    if (o->type == OP_REG) {
        o->reg = map_vreg(o->reg, reg_map, coalesce_map);
    } else if (o->type == OP_MEM) {
        if (o->base_size > REG_NONE) {
            o->base_reg = map_vreg(o->base_reg, reg_map, coalesce_map);
        }
        if (o->index_size > REG_NONE) {
            o->index_reg = map_vreg(o->index_reg, reg_map, coalesce_map);
        }
    }
}

static void replace_ins_vregs(AsmIns *ins, Reg *reg_map, int *coalesce_map) {
    replace_vreg(&ins->l, reg_map, coalesce_map);
    replace_vreg(&ins->r, reg_map, coalesce_map);
    if (ins->op >= X86_MOV && ins->op <= X86_MOVZX &&
            ins->l.type == OP_REG && ins->r.type == OP_REG &&
            ins->l.reg == ins->r.reg) {
        if ((ins->op == X86_MOVSX || ins->op == X86_MOVZX) &&
                ins->l.size > ins->r.size) {
            return; // Don't remove, e.g., movsx rax, ax
        }
        delete_asm(ins); // Remove a redundant mov
    }
}

// Change all OP_VREG operands in the assembly to their allocated registers
static void replace_vregs(Fn *fn, Reg *reg_map, int *coalesce_map) {
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        for (AsmIns *ins = bb->asm_head; ins; ins = ins->next) {
            replace_ins_vregs(ins, reg_map, coalesce_map);
        }
    }
}

void reg_alloc(Fn *fn, LiveRange *ranges) {
    if (fn->num_regs == 0 || !fn->last) {
        return; // No vregs to allocate, or the function is empty
    }
    print_live_ranges(ranges, fn->num_regs);
    RegGraph ig = build_interference_graph(ranges, fn->num_regs);
    RegGraph cg = build_coalescing_graph(fn, ranges);
    Reg reg_map[fn->num_regs - LAST_PREG];
    int coalesce_map[fn->num_regs - LAST_PREG];
    colour_graph(&ig, &cg, reg_map, coalesce_map);
    replace_vregs(fn, reg_map, coalesce_map);
}
