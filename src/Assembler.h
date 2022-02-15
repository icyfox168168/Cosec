
#ifndef COSEC_ASSEMBLER_H
#define COSEC_ASSEMBLER_H

#include "Compiler.h"

// ASSEMBLER -- lowers the SSA IR into target-specific machine code
// instructions. Target-specific optimisations can then be made to the
// generated assembly code (e.g., peep-hole optimisations not possible on the
// SSA IR). Variables are still modelled by virtual registers in the assembly,
// which are later lowered to physical registers by the register allocator.
//
// REQUIRES:
// * Use chain analysis (for IR_LOAD folding)

#define X86_REGS \
    X(RAX, "rax", "eax",  "ax",   "ah", "al")   \
    X(RCX, "rcx", "ecx",  "cx",   "ch", "cl")   \
    X(RDX, "rdx", "edx",  "dx",   "dh", "dl")   \
    X(RBX, "rbx", "ebx",  "bx",   "bh", "bl")   \
    X(RSP, "rsp", "esp",  "sp",   NULL, "spl")  \
    X(RBP, "rbp", "ebp",  "bp",   NULL, "bpl")  \
    X(RSI, "rsi", "esi",  "si",   NULL, "sil")  \
    X(RDI, "rdi", "edi",  "di",   NULL, "dil")  \
    X(R8,  "r8",  "r8d",  "r8w",  NULL, "r8b")  \
    X(R9,  "r9",  "r9d",  "r9w",  NULL, "r9b")  \
    X(R10, "r10", "r10d", "r10w", NULL, "r10b") \
    X(R11, "r11", "r11d", "r11w", NULL, "r11b") \
    X(R12, "r12", "r12d", "r12w", NULL, "r12b") \
    X(R13, "r13", "r13d", "r13w", NULL, "r13b") \
    X(R14, "r14", "r14d", "r14w", NULL, "r14b") \
    X(R15, "r15", "r15d", "r15w", NULL, "r15b")

typedef enum {
#define X(name, _, __, ___, ____, _____) REG_ ## name,
    X86_REGS
#undef X
    LAST_PREG,
} Reg;

typedef enum {
    REG_NONE, // Don't use the reg
    REG_L,    // Lowest 8 bits (e.g., al)
    REG_H,    // Highest 8 bits of the lowest 16 bits (e.g., ah)
    REG_W,    // Lowest 16 bits (e.g., ax)
    REG_D,    // Lowest 32 bits (e.g., eax)
    REG_Q,    // All 64 bits (e.g., rax)
} RegSize;

static char *REG_NAMES[][6] = {
#define X(name, q, d, w, h, l) \
    {[REG_Q] = (q), [REG_D] = (d), [REG_W] = (w), [REG_H] = (h), [REG_L] = (l)},
    X86_REGS
#undef X
};

// Tells us the RegSize to use for a 'Type' of a certain number of BYTES.
static RegSize REG_SIZE[] = {
    [1] = REG_L,
    [2] = REG_W,
    [4] = REG_D,
    [8] = REG_Q,
};

#define X86_OPCODES          \
    /* Memory access */      \
    X(MOV, "mov", 2)         \
    X(MOVSX, "movsx", 2) /* sign extend, for signed ints */ \
    X(MOVZX, "movzx", 2) /* zero extend, for unsigned ints */ \
    X(LEA, "lea", 2)         \
                             \
    /* Arithmetic */         \
    X(ADD, "add", 2)         \
    X(SUB, "sub", 2)         \
    X(MUL, "imul", 2)        \
    X(CDQ, "cdq", 0) /* Sign extend eax into edx, specifically for idiv */ \
    X(IDIV, "idiv", 1)       \
    X(DIV, "div", 1)         \
    X(AND, "and", 2)         \
    X(OR, "or", 2)           \
    X(XOR, "xor", 2)         \
    X(SHL, "shl", 2)         \
    X(SHR, "shr", 2)         \
    X(SAR, "sar", 2)         \
                             \
    /* Comparisons */        \
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
                             \
    /* Stack manipulation */ \
    X(PUSH, "push", 1)       \
    X(POP, "pop", 1)         \
                             \
    /* Control flow */       \
    X(JMP, "jmp", 1) /* Unconditional jump */ \
    X(JE, "je", 1)   /* Conditional jumps */ \
    X(JNE, "jne", 1)         \
    X(JL, "jl", 1)           \
    X(JLE, "jle", 1)         \
    X(JG, "jg", 1)           \
    X(JGE, "jge", 1)         \
    X(JB, "jb", 1)           \
    X(JBE, "jbe", 1)         \
    X(JA, "ja", 1)           \
    X(JAE, "jae", 1)         \
    X(CALL, "call", 1)       \
    X(RET, "ret", 0)         \
    X(SYSCALL, "syscall", 0)

typedef enum {
#define X(name, _, __) X86_ ## name,
    X86_OPCODES
#undef X
    NUM_X86_OPS, // Required for hash-maps indexed by assembly opcode
} AsmOpcode;

static int X86_OPCODE_NARGS[] = { // Number of arguments each opcode takes
#define X(_, __, nargs) nargs,
    X86_OPCODES
#undef X
};

typedef enum {
    OP_IMM,   // Immediate (constant)
    OP_REG,   // Physical or virtual register (e.g., rax, %3, etc.)
    OP_MEM,   // Memory access
    OP_LABEL, // Symbol for a branch
    OP_FN,    // Symbol for a call
} AsmOperandType;

// For OP_REG, 'operand.reg' is >= LAST_PREG if the operand represents a
// virtual register. 'operand.reg' < LAST_PREG indicates a physical register
typedef struct {
    AsmOperandType type;
    union {
        int imm; // OP_IMM
        struct { RegSize size; int reg; }; // OP_REG (physical or virtual)
        struct { // OP_MEM
            int base_reg; RegSize base_size;
            int index_reg; RegSize index_size;
            int scale, disp;
            int access_size;
        };
        struct bb *bb; // OP_LABEL
        struct fn *fn; // OP_FN
    };
} AsmOperand;

typedef struct asm_ins {
    struct asm_ins *next, *prev;
    struct bb *bb;
    int idx;
    AsmOpcode op;
    AsmOperand l, r;
} AsmIns;

void delete_asm(AsmIns *ins);

void assemble(Module *mod);

#endif
