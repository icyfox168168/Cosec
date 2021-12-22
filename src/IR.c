
#include "IR.h"

int size_of(Type type) {
    return 4; // Only type is T_I32, which is 4 bytes
}

int is_const(IrOp op) {
    return op == IR_KI32;
}
