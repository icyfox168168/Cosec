
#include "IR.h"

int size_of(Type type) {
    return 32; // Only type is T_I32, which is 32 bits
}

int is_const(IrOp op) {
    return op == IR_KI32;
}
