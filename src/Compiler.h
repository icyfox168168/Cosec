
#ifndef COSEC_COMPILER_H
#define COSEC_COMPILER_H

#include "Parser.h"
#include "analysis/Analysis.h"

// COMPILER -- converts a well-formed abstract syntax tree (AST) to SSA IR.
// The SSA IR is where all the compiler optimisations take place.
//
// Since C is a relatively simple language, it's actually possible for us to
// get rid of the AST all together and merge its construction into SSA IR
// generation. Although possible, it's not a good idea - having the AST
// simplifies the IR generation logic sooo much and makes for cleaner code.

// Information about specific IR instructions:
//
// * IR_FARG: only appears at the START of an IR function's entry basic block;
//   used to reference the 'n'th argument for the function (where argument 0
//   is the left most, argument 1 is next, etc.); floating point arguments are
//   counted SEPARATELY (since they go in SSE registers)
// * ALLOC: allocates stack space of a given size and returns a POINTER to the
//   start of this space (similar to LLVM's alloca)
// * STORE: writes its SECOND argument (with type <type>) to its FIRST (which
//   must have type <type>*)
// * LOAD: reads memory from a pointer <type>*, resulting in a value with type
//   <type>
// * ELEM: performs pointer offset calculations, similar to LLVM's
//   'getelementptr'. First argument is the base pointer, second is the index.
#define IR_OPCODES        \
    /* Immediates and constants */ \
    X(IMM, 1)             \
    X(CONST, 1)           \
                          \
    /* Memory accesses */ \
    X(FARG, 1)            \
    X(ALLOC, 0)           \
    X(STORE, 2) /* Destination is FIRST argument, source is SECOND */ \
    X(LOAD, 1)            \
    X(ELEM, 2) /* Pointer to an element in an array/pointer/struct */ \
                          \
    /* Arithmetic */      \
    X(ADD, 2)             \
    X(SUB, 2)             \
    X(MUL, 2)             \
    X(SDIV, 2) /* Signed */ \
    X(UDIV, 2) /* Unsigned */ \
    X(FDIV, 2) /* Floating point */ \
    X(SMOD, 2) /* Signed */ \
    X(UMOD, 2) /* Unsigned */ \
    X(AND, 2)             \
    X(OR, 2)              \
    X(XOR, 2)             \
    X(SHL, 2)             \
    X(ASHR, 2) /* Arithmetic right shift, fill with sign bit (signed ints) */ \
    X(LSHR, 2) /* Logical right shift, fill with zeros (unsigned ints) */ \
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
    X(FLT, 2) /* Ordered floating point comparisons */ \
    X(FLE, 2)             \
    X(FGT, 2)             \
    X(FGE, 2)             \
                          \
    /* Conversions */     \
    X(TRUNC, 1)   /* Truncate an int to a smaller type */ \
    X(SEXT, 1)    /* Sign extend, for signed ints */ \
    X(ZEXT, 1)    /* Zero extend, for unsigned ints */ \
                          \
    X(FPEXT, 1)   /* Extend a floating point */ \
    X(FPTRUNC, 1) /* Truncate a floating point */ \
    X(FP2I, 1)    /* Convert a floating point to an integer */ \
    X(I2FP, 1)    /* Convert an integer to a floating point */ \
                          \
    X(PTR2I, 1)   /* Convert a pointer to an integer */ \
    X(I2PTR, 1)   /* Convert an integer to a pointer */ \
    X(PTR2PTR, 1) /* Convert a pointer to another pointer type -> nop */ \
                          \
    /* Control flow */    \
    X(PHI, 0)    /* SSA phi instruction TODO */ \
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

// A branch chain is a linked list of pointers into 'IR_BR' or 'IR_CONDBR'
// arguments (either, 'ins->br', 'ins->true' or 'ins->false' branch targets)
// that need to/ be back-filled when the jump destination for a conditional
// expression is determined.
typedef struct br_chain {
    struct bb **br;
    struct ir_ins *ins; // The IR_BR or IR_CONDBR ins referred to by 'br'
    struct br_chain *next;
} BrChain;

// SSA phi instructions keep track of the value of a variable along different
// control flow paths. Phi instructions ONLY occur at the head of a basic block.
// They take as an argument a list of pairs <basic block, definition>, one pair
// for each predecessor basic block. The pairs are stored as a linked list.
typedef struct phi_chain {
    struct phi_chain *next;
    struct bb *bb;
    struct ir_ins *def;
} PhiChain;

typedef struct ir_ins {
    struct ir_ins *next, *prev;
    struct bb *bb;
    int idx; // For debug printing
    IrOpcode op;
    Type *type; // Type of the RESULT of the instruction
    union {
        PhiChain *phi; // IR_PHI
        int arg_num;   // IR_FARG
        uint64_t imm;  // IR_IMM
        int const_idx; // IR_CONST; index into function's 'consts' array
        struct { struct ir_ins *l, *r; }; // Unary and binary operations
        struct bb *br;                    // IR_BR
        struct {                          // IR_CONDBR
            struct ir_ins *cond;
            struct bb *true, *false;
            // Branch chains that need to be patched once the destination for
            // a conditional expression is known
            BrChain *true_chain, *false_chain;
        };
    };

    // Per-IR instruction analysis information
    UseChain *use_chain;

    // Assembler information
    int vreg;       // Virtual register that stores the instruction's result
    int stack_slot; // For IR_ALLOC: location on the stack relative to rbp
} IrIns;

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
    struct asm_ins *asm_head, *asm_last; // Assembly instructions

    // Per-BB analysis information
    CFGInfo cfg;
    LivenessInfo live;
} BB;

BB * new_bb(); // Used by the assembler

typedef struct {
    Type *type;
    union {
        float f32;
        double f64;
        char *str;
        uint32_t out32; // For the emitter when writing to the output file
        uint64_t out64;
    };
} Constant;

typedef struct fn {
    struct fn *next;  // Linked list of functions
    char *name;       // Output name for the function
    BB *entry, *last; // Linked list of basic blocks

    // For the assembler
    int num_gprs, num_sse_regs; // Number of vregs used in the function
    Constant *consts;           // Constants used in the assembly
    int num_consts, max_consts;
} Fn;

Fn * new_fn();

typedef struct {
    Fn *fns;  // Linked list of functions
} Module;

Module * compile(AstModule *ast);

#endif
