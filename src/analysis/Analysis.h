
#ifndef COSEC_ANALYSIS_H
#define COSEC_ANALYSIS_H

// ANALYSIS STRUCTURES -- this file contains per-BB and per-instruction
// analysis info, included in IR.h.


// ---- Per-BB Analysis -------------------------------------------------------

// Each basic block can have a maximum of 2 successor blocks (if it ends with a
// CONDBR instruction)
#define MAX_SUCCESSORS 2

// CFG information consists of all predecessor and successor blocks.
typedef struct {
    struct bb **pred, *succ[MAX_SUCCESSORS];
    int num_pred, max_pred, num_succ; // Don't need max_succ, always 2
} CFGInfo;

// Liveness information consists of just the live-in vregs for each BB.
typedef struct {
    int *in; // Set of all vregs that are live-in at the start of a block
} LivenessInfo;


// ---- Per-IR Instruction Analysis -------------------------------------------

// A linked list of IR instructions that use a particular instruction.
// Constructed by the 'UseChain.h' analysis pass.
typedef struct use_chain {
    struct ir_ins *ins;
    struct use_chain *next; // Next IR instruction in this use chain
} UseChain;

#endif
