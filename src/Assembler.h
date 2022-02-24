
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

// GPR stands for General Purpose Register; these consist of all the "integer"
// registers, as opposed to the floating point registers xmm0-15.
#define X86_GPRS \
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
#define X(name, _, __, ___, ____, _____) GPR_ ## name,
    X86_GPRS
#undef X
    LAST_GPR,
} GPReg;

typedef enum {
    GPR_NONE, // Don't use the reg
    GPR_L,    // Lowest 8 bits (e.g., al)
    REG_H,    // Highest 8 bits of the lowest 16 bits (e.g., ah)
    GPR_W,    // Lowest 16 bits (e.g., ax)
    GPR_D,    // Lowest 32 bits (e.g., eax)
    GPR_Q,    // All 64 bits (e.g., rax)
} GPRSize;

static char *GPR_NAMES[][LAST_GPR] = {
#define X(name, q, _, __, ___, ____) q,
    [GPR_Q] = {X86_GPRS },
#undef X
#define X(name, _, d, __, ___, ____) d,
    [GPR_D] = {X86_GPRS },
#undef X
#define X(name, _, __, w, ___, ____) w,
    [GPR_W] = {X86_GPRS },
#undef X
#define X(name, _, __, ___, h, ____) h,
    [REG_H] = { X86_GPRS },
#undef X
#define X(name, _, __, ___, ____, l) l,
    [GPR_L] = {X86_GPRS },
#undef X
};

#define X86_SSE \
    X(XMM0,  "xmm0")  \
    X(XMM1,  "xmm1")  \
    X(XMM2,  "xmm2")  \
    X(XMM3,  "xmm3")  \
    X(XMM4,  "xmm4")  \
    X(XMM5,  "xmm5")  \
    X(XMM6,  "xmm6")  \
    X(XMM7,  "xmm7")  \
    X(XMM8,  "xmm8")  \
    X(XMM9,  "xmm9")  \
    X(XMM10, "xmm10") \
    X(XMM11, "xmm11") \
    X(XMM12, "xmm12") \
    X(XMM13, "xmm13") \
    X(XMM14, "xmm14") \
    X(XMM15, "xmm15")

typedef enum {
#define X(name, _) SSE_ ## name,
    X86_SSE
#undef X
    LAST_SSE,
} SSEReg;

static char *SSE_REG_NAMES[] = {
#define X(name, str) [SSE_ ## name] = (str),
    X86_SSE
#undef X
};

#define X86_OPCODES            \
    /* Memory access */        \
    X(MOV, "mov", 2)           \
    X(MOVSX, "movsx", 2) /* sign extend, for signed ints */ \
    X(MOVZX, "movzx", 2) /* zero extend, for unsigned ints */ \
    X(MOVSS, "movss", 2) /* ss = for floats */ \
    X(MOVSD, "movsd", 2) /* sd = for doubles */ \
    X(LEA, "lea", 2)           \
                               \
    /* Arithmetic */           \
    X(ADD, "add", 2)           \
    X(SUB, "sub", 2)           \
    X(MUL, "imul", 2)          \
    X(CWD, "cwd", 0) /* Sign extend ax into dx, for idiv */ \
    X(CDQ, "cdq", 0) /* Sign extend eax into edx, for idiv */ \
    X(CQO, "cqo", 0) /* Sign extend rax into rdx, for idiv */ \
    X(IDIV, "idiv", 1)         \
    X(DIV, "div", 1)           \
    X(AND, "and", 2)           \
    X(OR, "or", 2)             \
    X(XOR, "xor", 2)           \
    X(SHL, "shl", 2)           \
    X(SHR, "shr", 2)           \
    X(SAR, "sar", 2)           \
                               \
    /* Floating point arithmetic */ \
    X(ADDSS, "addss", 2)       \
    X(ADDSD, "addsd", 2)       \
    X(SUBSS, "subss", 2)       \
    X(SUBSD, "subsd", 2)       \
    X(MULSS, "mulss", 2)       \
    X(MULSD, "mulsd", 2)       \
    X(DIVSS, "divss", 2)       \
    X(DIVSD, "divsd", 2)       \
                               \
    /* Comparisons */          \
    X(CMP, "cmp", 2)           \
    X(SETE, "sete", 1)         \
    X(SETNE, "setne", 1)       \
    X(SETL, "setl", 1)         \
    X(SETLE, "setle", 1)       \
    X(SETG, "setg", 1)         \
    X(SETGE, "setge", 1)       \
    X(SETB, "setb", 1)         \
    X(SETBE, "setbe", 1)       \
    X(SETA, "seta", 1)         \
    X(SETAE, "setae", 1)       \
                               \
    /* Floating point comparisons */ \
    X(UCOMISS, "ucomiss", 2)   \
    X(UCOMISD, "ucomisd", 2)   \
                               \
    /* Floating point conversions */ \
    X(CVTSS2SD, "cvtss2sd", 2) \
    X(CVTSD2SS, "cvtsd2ss", 2) \
    X(CVTSI2SS, "cvtsi2ss", 2) \
    X(CVTSI2SD, "cvtsi2sd", 2) \
    X(CVTTSS2SI, "cvttss2si", 2) \
    X(CVTTSD2SI, "cvttsd2si", 2) \
                               \
    /* Stack manipulation */   \
    X(PUSH, "push", 1)         \
    X(POP, "pop", 1)           \
                               \
    /* Control flow */         \
    X(JMP, "jmp", 1) /* Unconditional jump */ \
    X(JE, "je", 1)   /* Conditional jumps */ \
    X(JNE, "jne", 1)           \
    X(JL, "jl", 1)             \
    X(JLE, "jle", 1)           \
    X(JG, "jg", 1)             \
    X(JGE, "jge", 1)           \
    X(JB, "jb", 1)             \
    X(JBE, "jbe", 1)           \
    X(JA, "ja", 1)             \
    X(JAE, "jae", 1)           \
    X(CALL, "call", 1)         \
    X(RET, "ret", 0)           \
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
    OP_GPR,   // Physical or virtual general purpose register
    OP_XMM,   // SSE physical or virtual register
    OP_MEM,   // Memory access
    OP_CONST, // Constant in memory
    OP_LABEL, // Symbol for a branch
    OP_FN,    // Symbol for a call
} AsmOperandType;

// For OP_GPR, 'operand.reg' is >= LAST_GPR if the operand represents a
// virtual register; 'operand.reg' < LAST_GPR indicates a physical register
typedef struct {
    AsmOperandType type;
    union {
        uint64_t imm; // OP_IMM
        struct { GPRSize size; int reg; }; // OP_GPR or OP_XMM
        struct { // OP_MEM
            int access_size;
            int base_reg; GPRSize base_size;
            int index_reg; GPRSize index_size;
            int scale;
            int64_t disp;
        };
        struct { // OP_CONST
            int _access_size;
            int const_idx;
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
