
#ifndef COSEC_IR_H
#define COSEC_IR_H

#include <stdlib.h>
#include <stdint.h>

#include "analysis/Analysis.h"

#define UNREACHABLE() exit(1)

// ---- Static Single Assignment (SSA) Form IR --------------------------------

#define IR_PRIMS \
    X(NONE)      \
    X(void)      \
    X(i1) /* Boolean value */ \
    X(i8)        \
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

#define IR_OPCODES        \
    /* Constants */       \
    X(KINT, 1)            \
                          \
    /* Memory accesses */ \
    X(FARG, 1)            \
    X(ALLOC, 0)           \
    X(STORE, 2) /* Destination is FIRST argument, source is SECOND */ \
    X(LOAD, 1)            \
                          \
    /* Arithmetic */      \
    X(ADD, 2)             \
    X(SUB, 2)             \
    X(MUL, 2)             \
    X(DIV, 2)             \
    X(MOD, 2)             \
    X(AND, 2)             \
    X(OR, 2)              \
    X(XOR, 2)             \
    X(SHL, 2)             \
    X(LSHR, 2) /* Logical right shift, fill with zeros (unsigned ints) */ \
    X(ASHR, 2) /* Arithmetic right shift, fill with sign bit (signed ints) */ \
                          \
    /* Comparisons */     \
    X(EQ, 2)              \
    X(NEQ, 2)             \
    X(SLT, 2) /* Signed comparisons (for signed ints) */ \
    X(SLE, 2)             \
    X(SGT, 2)             \
    X(SGE, 2)             \
    X(ULT, 2) /* Unsigned comparisons (for unsigned ints) */ \
    X(ULE, 2)             \
    X(UGT, 2)             \
    X(UGE, 2)             \
                          \
    /* Conversions */     \
    X(TRUNC, 1) /* Truncate an int to a smaller type */ \
    X(SEXT, 1) /* Sign extend, for signed ints */ \
    X(ZEXT, 1) /* Zero extend, for unsigned ints */ \
                          \
    /* Control flow */    \
    X(PHI, 0)    /* SSA phi instruction */ \
    X(BR, 1)     /* Unconditional branch */ \
    X(CONDBR, 3) /* Conditional branch (condition, true BB, false BB) */ \
    X(RET1, 1)   /* Return a value */ \
    X(RET0, 0)   /* Return nothing */

typedef enum {
#define X(name, nargs) IR_ ## name,
    IR_OPCODES
#undef X
    NUM_IR_OPS, // Required for hash tables indexed by IR opcode
} IrOpcode;

static int IR_OPCODE_NARGS[] = {
#define X(opcode, nargs) nargs,
    IR_OPCODES
#undef X
};

// SSA phi instructions keep track of the value of a variable along different
// control flow paths. Phi instructions ONLY occur at the head of a basic block.
// They take as an argument a list of pairs <basic block, definition>, one pair
// for each predecessor basic block. The pairs are stored as a linked list.
typedef struct phi {
    struct phi *next;
    struct bb *bb;
    struct ir_ins *def;
} Phi;

typedef struct ir_ins {
    struct ir_ins *next, *prev;
    struct bb *bb;

    IrOpcode op;
    Type type; // Everything except control flow records its return type
    union {
        Phi *phi;                         // Phi instruction
        int arg_num;                      // Function argument
        int kint;                         // Integer constant
        struct { struct ir_ins *l, *r; }; // Binary operation
        struct bb *br;                    // Unconditional branch
        struct {                          // Conditional branch
            struct ir_ins *cond;
            struct bb *true, *false;
        };
    };

    // Analysis info
    UseChain *use_chain;

    // Assembler info
    int vreg; // Virtual register assigned to the instruction's result
    int stack_slot; // For IR_ALLOC; location on the stack relative to rbp

    // Debug info
    int idx;
} IrIns;


// ---- Assembly IR -----------------------------------------------------------

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
    NUM_REGS,
} Reg;

typedef enum {
    REG_Q, // All 64 bits (e.g., rax)
    REG_D, // Lowest 32 bits (e.g., eax)
    REG_W, // Lowest 16 bits (e.g., ax)
    REG_H, // Highest 8 bits of the lowest 16 bits (e.g., ah)
    REG_L, // Lowest 8 bits (e.g., al)
} RegSize;

static char *REG_NAMES[][5] = {
#define X(name, q, d, w, h, l) {q, d, w, h, l},
    X86_REGS
#undef X
};

// Tells us the RegSize to use for a 'Type' of a certain number of BYTES.
static RegSize REG_SIZE[] = {
    [8] = REG_Q,
    [4] = REG_D,
    [2] = REG_W,
    [1] = REG_L,
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
    OP_REG,   // Physical register (e.g., rax, etc.)
    OP_VREG,  // Virtual register (only prior to register allocation)
    OP_MEM,   // Memory access
    OP_LABEL, // Symbol (e.g. for a call or jump)
} AsmOperandType;

typedef struct {
    AsmOperandType type;
    union {
        int imm;                           // OP_IMM
        struct { RegSize size; Reg reg; }; // OP_REG
        struct { RegSize _s1; int vreg; }; // OP_VREG
        struct { RegSize _s2; Reg base; int scale, index, bytes; }; // OP_MEM
        struct bb *bb;                     // OP_LABEL
    };
} AsmOperand;

typedef struct asm_ins {
    struct asm_ins *next, *prev;
    struct bb *bb;
    int idx;
    AsmOpcode op;
    AsmOperand l, r;
} AsmIns;


// ---- Basic Block -----------------------------------------------------------

// Use a unified basic block structure for both the SSA and assembly IR, since
// this simplifies assembly construction. The CFG structure is the same in
// each IR (although represented more implicitly in the assembly IR).
//
// The ONLY jump allowed in a basic block is the last instruction; this
// maintains the property that basic blocks are a LINEAR sequence of
// instructions that always execute in order (useful for optimisation)
typedef struct bb {
    // Maintain an ordering over basic blocks in a function, the same as the
    // order in which they appear in the source code
    struct bb *next, *prev;
    char *label;
    IrIns *ir_head, *ir_last;    // IR instructions
    AsmIns *asm_head, *asm_last; // Assembly instructions

    // Analysis info
    CFGInfo cfg;
    LivenessInfo live;
} BB;

int size_of(Type t); // Returns the bytes of a type in bytes

BB * new_bb();
IrIns * new_ir(IrOpcode op);
void emit_ir(BB *bb, IrIns *ins);
void delete_ir(IrIns *ins);
AsmIns * emit_asm(BB *bb, AsmOpcode op);
void delete_asm(AsmIns *ins);

#endif
