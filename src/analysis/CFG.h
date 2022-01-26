
#ifndef COSEC_CFG_H
#define COSEC_CFG_H

#include "../IR.h"

// CFG ANALYSIS -- calculates the predecessor and successor basic blocks for
// every block in a function. This analysis is used by many optimisations and
// the register allocator.
//
// REQUIRES: no other analysis passes required first

void analysis_cfg(BB *head);

#endif
