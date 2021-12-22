
#ifndef COSEC_ASSEMBLER_H
#define COSEC_ASSEMBLER_H

#include "Parser.h"

#define X86_REGS         \
    X(RAX, "rax", 0b000) \
    X(RCX, "rcx", 0b001) \
    X(RDX, "rdx", 0b010) \
    X(RBX, "rbx", 0b011) \
    X(RSP, "rsp", 0b100) \
    X(RBP, "rbp", 0b101) \
    X(RSI, "rsi", 0b110) \
    X(RDI, "rdi", 0b111)

typedef enum {
#define X(name, _, __) REG_ ## name,
    X86_REGS
#undef X
} Reg;

#define X86_OPCODES          \
    X(MOV, "mov", 2)         \
    X(ADD, "add", 2)         \
    X(SUB, "sub", 2)         \
    X(MUL, "mul", 2)         \
    X(IDIV, "idiv", 2)       \
    X(PUSH, "push", 1)       \
    X(POP, "pop", 1)         \
    X(CALL, "call", 1)       \
    X(RET, "ret", 0)         \
    X(SYSCALL, "syscall", 0) \
    X(NOP, "nop", 0)

typedef enum {
#define X(name, _, __) X86_ ## name,
    X86_OPCODES
#undef X
} AsmOp;

typedef enum {
    OP_REG,  // Physical register (e.g., rax, etc.)
    OP_VREG, // Virtual register for the register allocator
    OP_IMM,
    OP_MEM,
    OP_SYM,  // Symbol (e.g. for a call or jump)
} AsmOperandType;

typedef struct {
    AsmOperandType type;
    union {
        Reg reg;
        int vreg;
        uint64_t imm;
        struct { Reg base; int scale; int index; }; // For OP_MEM
        struct asm_bb *sym;
    };
} AsmOperand;

typedef struct asm_ins {
    struct asm_ins *next;
    AsmOp op;
    AsmOperand l, r;
} AsmIns;

typedef struct asm_bb {
    struct asm_bb *next;
    char *label; // NULL if automatically assigned
    AsmIns *head;
} AsmBB;

typedef struct asm_fn {
    struct asm_fn *next;
    AsmBB *entry; // The BBs for an AsmFn form a linear CFG (the optimiser creates the DAG to achieve this ordering)
} AsmFn;

typedef struct {
    AsmFn *fns;
    AsmFn *main; // NULL if this module has no 'main' function
} AsmModule;

AsmModule * assemble(Module *ir_mod);

#endif
