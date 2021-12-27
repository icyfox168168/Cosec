
#ifndef COSEC_ASSEMBLER_H
#define COSEC_ASSEMBLER_H

#include "Parser.h"

/* ASSEMBLER -- lowers the SSA IR into target-specific machine code
 * instructions. Target-specific optimisations can then be made to the generated
 * assembly code (e.g., peep-hole optimisations not possible on the SSA IR).
 *
 * Variables are still modelled by virtual registers, which are later lowered
 * to physical registers by the register allocator.
 */

#define X86_REGS  \
    X(RAX, "rax") \
    X(RCX, "rcx") \
    X(RDX, "rdx") \
    X(RBX, "rbx") \
    X(RSP, "rsp") \
    X(RBP, "rbp") \
    X(RSI, "rsi") \
    X(RDI, "rdi") \
    X(R8, "r8")   \
    X(R9, "r9")   \
    X(EAX, "eax") \
    X(ECX, "ecx") \
    X(EDX, "edx") \
    X(EBX, "ebx") \
    X(ESP, "esp") \
    X(EBP, "ebp") \
    X(ESI, "esi") \
    X(EDI, "edi") \
    X(CL, "cl")

typedef enum {
#define X(name, _) REG_ ## name,
    X86_REGS
#undef X
} Reg;

typedef enum {
    REG_ALL, // All 64 bits (e.g., rax)
    REG_32,  // Lowest 32 bits (e.g., eax)
    REG_16,  // Lowest 16 bits (e.g., ax)
    REG_8H,  // Highest 8 bits of the lowest 16 bits (e.g., ah)
    REG_8L,  // Lowest 8 bits (e.g., al)
} RegSubsection;

#define X86_OPCODES          \
    X(MOV, "mov", 2)         \
    X(LEA, "lea", 2)         \
    X(ADD, "add", 2)         \
    X(SUB, "sub", 2)         \
    X(MUL, "mul", 2)         \
    X(CDQ, "cdq", 0)         \
    X(IDIV, "idiv", 1)       \
    X(AND, "and", 2)         \
    X(OR, "or", 2)           \
    X(XOR, "xor", 2)         \
    X(SHL, "shl", 2)         \
    X(SHR, "shr", 2)         \
    X(SAR, "sar", 2)         \
    X(CMP, "cmp", 2)         \
    X(SETE, "sete", 1)       \
    X(SETNE, "setne", 1)     \
    X(SETL, "setl", 1)       \
    X(SETLE, "setle", 1)     \
    X(SETG, "setg", 1)       \
    X(SETGE, "setge", 1)     \
    X(SETB, "setb", 1)       \
    X(SETBE, "setbe", 1)     \
    X(SETA, "seta", 1)       \
    X(SETAE, "setae", 1)     \
    X(PUSH, "push", 1)       \
    X(POP, "pop", 1)         \
    X(CALL, "call", 1)       \
    X(RET, "ret", 0)         \
    X(SYSCALL, "syscall", 0)

typedef enum {
#define X(name, _, __) X86_ ## name,
    X86_OPCODES
#undef X
} AsmOp;

// Tells us which register each function argument is in, according to the
// System V ABI. The array is indexed by function argument number, where 1 is
// the left-most argument.
//
// 'NUM_FN_ARGS_REGS' tells us how many function arguments are passed via
// registers. After this many arguments, we need to start pulling off the stack.
#define NUM_FN_ARGS_REGS 6
static Reg FN_ARGS_REGS[] = {
    REG_RDI,
    REG_RSI,
    REG_RDX,
    REG_RCX,
    REG_R8,
    REG_R9,
};

// Converts IR instruction operands into SETxx x86 opcodes.
static AsmOp IROP_TO_SETXX[IR_LAST] = {
    [IR_EQ] = X86_SETE,
    [IR_NEQ] = X86_SETNE,
    [IR_SLT] = X86_SETL,
    [IR_SLE] = X86_SETLE,
    [IR_SGT] = X86_SETG,
    [IR_SGE] = X86_SETGE,
    [IR_ULT] = X86_SETB,
    [IR_ULE] = X86_SETBE,
    [IR_UGT] = X86_SETA,
    [IR_UGE] = X86_SETAE,
};

typedef enum {
    OP_IMM,
    OP_REG,  // Physical register (e.g., rax, etc.)
    OP_VREG, // Virtual register for the register allocator
    OP_MEM,
    OP_SYM,  // Symbol (e.g. for a call or jump)
} AsmOperandType;

typedef struct {
    AsmOperandType type;
    union {
        uint64_t imm;
        Reg reg;
        struct { int vreg, subsection; }; // For OP_VREG
        struct { Reg base; int scale, index; }; // For OP_MEM
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
