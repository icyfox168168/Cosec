
#ifndef COSEC_FOLD_H
#define COSEC_FOLD_H

#include "../Parser.h"

/* FOLD pass -- eliminates instructions whose value can be computed at compile
 * time. For example, arithmetic on constant integers:
 *   0000: KI32 3
 *   0001: KI32 4
 *   0002: ADD 0000 0001
 * Becomes (after DCE):
 *   0000: KI32 7
 */

void opt_fold(FnDef *fn);

#endif
