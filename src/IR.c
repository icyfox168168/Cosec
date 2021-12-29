
#include <stdlib.h>

#include "IR.h"

BB * new_bb() {
    BB *bb = malloc(sizeof(BB));
    bb->next = NULL;
    bb->label = NULL;
    bb->ir_head = NULL;
    bb->asm_head = NULL;
    return bb;
}

int size_of(Type t) {
    if (t.ptrs > 0) {
        return 8; // Pointers are always 8 bytes
    }
    switch (t.prim) {
        case T_void: return 0;
        case T_i32:  return 4;
    }
}
