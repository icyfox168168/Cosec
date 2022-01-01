
#ifndef COSEC_IR_H
#define COSEC_IR_H

#include <stdint.h>

#define UNREACHABLE() exit(1)

// ---- Static Single Assignment (SSA) Form IR --------------------------------

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

#define IR_OPCODES        \
    /* Constants */       \
    X(KI32, 1)            \
                          \
    /* Memory accesses */ \
    X(FARG, 1)            \
    X(ALLOC, 1)           \
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
    IR_LAST, // Required for hash-tables indexed by IR opcode
} IrOpcode;

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
    struct ir_ins *next;
    struct bb *bb; // The basic block this instruction is in

    IrOpcode op;
    Type type; // Everything except control flow records its return type
    union {
        Phi *phi;                         // Phi instructions
        int arg_num;                      // Function arguments
        int32_t ki32;                     // Constants
        struct { struct ir_ins *l, *r; }; // Binary operations
        struct bb *br;                    // Unconditional branches
        struct {                          // Conditional branches
            struct ir_ins *cond;
            struct bb *true, *false;
        };
    };

    // Assembler info
    int stack_slot; // For IR_ALLOC; location on the stack relative to rbp
    int vreg; // Virtual register that the instruction's result is assigned to

    // Debug info
    int debug_idx;
} IrIns;


// ---- Assembly IR -----------------------------------------------------------

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
    REG_64, // All 64 bits (e.g., rax)
    REG_32, // Lowest 32 bits (e.g., eax)
    REG_16, // Lowest 16 bits (e.g., ax)
    REG_8H, // Highest 8 bits of the lowest 16 bits (e.g., ah)
    REG_8L, // Lowest 8 bits (e.g., al)
} RegSubsection;

#define X86_OPCODES          \
    /* Memory access */      \
    X(MOV, "mov", 2)         \
    X(LEA, "lea", 2)         \
                             \
    /* Arithmetic */         \
    X(ADD, "add", 2)         \
    X(SUB, "sub", 2)         \
    X(MUL, "mul", 2)         \
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
    X86_LAST, // Required for hash-maps indexed by assembly opcode
} AsmOpcode;

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
        uint64_t imm;                           // For OP_IMM
        Reg reg;                                // For OP_REG
        struct { int vreg, subsection; };       // For OP_VREG
        struct { int scale, index; Reg base; }; // For OP_MEM (SIB)
        struct bb *bb;                          // For OP_LABEL
    };
} AsmOperand;

typedef struct asm_ins {
    struct asm_ins *next;
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
    struct bb *next;
    char *label;
    IrIns *ir_head;
    AsmIns *asm_head;
} BB;

BB * new_bb();       // Creates a new empty basic block
int size_of(Type t); // Returns the size of a type in bytes

#endif
