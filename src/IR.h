
#ifndef COSEC_IR_H
#define COSEC_IR_H

#include <stdint.h>

#define IR_PRIMS \
    X(void)      \
    X(i32)

typedef enum {
#define X(name) T_ ## name,
    IR_PRIMS
#undef X
} Prim;

typedef struct {
    Prim prim;
    int ptrs; // Number of levels of pointer indirection
} Type;

// LSHR = logical right shift, fills with zeros (for unsigned operations, faster)
// ASHR = arithmetic right shift, fills with sign bits (for signed operations)
#define IR_OPCODES \
    X(KI32, 1)     \
    X(FARG, 1)     \
    X(ALLOC, 1)    \
    X(STORE, 2)    \
    X(LOAD, 1)     \
    X(ADD, 2)      \
    X(SUB, 2)      \
    X(MUL, 2)      \
    X(DIV, 2)      \
    X(MOD, 2)      \
    X(AND, 2)      \
    X(OR, 2)       \
    X(XOR, 2)      \
    X(SHL, 2)      \
    X(LSHR, 2)     \
    X(ASHR, 2)     \
    X(RET1, 1)     \
    X(RET0, 0)

typedef enum {
#define X(name, nargs) IR_ ## name,
    IR_OPCODES
#undef X
} IrOp;

typedef struct ir_ins {
    struct ir_ins *next;
    IrOp op;
    Type type; // All instructions that return a value (i.e. everything but control flow) record its type here
    union {
        int narg; // Function arguments
        int32_t ki32; // Constants
        struct { struct ir_ins *l, *r; }; // Binary instructions
    };

    // Assembler per-IR instruction info
    int stack_slot; // For IR_ALLOC: location on the stack relative to rbp
    int vreg; // For instructions that generate a result: virtual register number referenced in the assembly

    // Debug info
    int debug_idx;
} IrIns;

int size_of(Type type);

#endif
