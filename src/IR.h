
#ifndef COSEC_IR_H
#define COSEC_IR_H

#include <stdint.h>

#define IR_TYPES \
    X(i32)

typedef enum {
#define X(name) T_ ## name
    IR_TYPES
#undef X
} Type;

#define IR_OPCODES \
    X(FARG, 1)     \
    X(ALLOC, 1)    \
    X(KI32, 1)     \
    X(STORE, 2)    \
    X(LOAD, 1)     \
    X(ADD, 2)      \
    X(SUB, 2)      \
    X(MUL, 2)      \
    X(DIV, 2)      \
    X(NEG, 1)      \
    X(RET, 0)

typedef enum {
#define X(name, nargs) IR_ ## name,
    IR_OPCODES
#undef X
} IrOp;

typedef struct ir_ins {
    IrOp op;
    struct ir_ins *next, *prev;
    union { // Operands
        Type type; // For IR_FARG and IR_ALLOC
        int32_t ki32; // For IR_KI32
        struct { struct ir_ins *dest, *src; }; // For IR_STORE
        struct { struct ir_ins *l, *r; }; // For arithmetic
    };
    int debug_idx;
} IrIns;

int size_of(Type type);

#endif
