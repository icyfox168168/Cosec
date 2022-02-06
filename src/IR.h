
#ifndef COSEC_IR_H
#define COSEC_IR_H

#include <stdlib.h>
#include <stdint.h>

#include "Lexer.h"
#include "analysis/Analysis.h"

#define UNREACHABLE() exit(1)

// We steal the great idea from LLVM to merge signed and unsigned integer
// types for simplicity, the rationale being that all we really care about is
// the size of the data, not it's underlying representation. We make the
// signed/unsigned distinction in the IR instructions instead.
//
// For more information, see this LLVM enhancement request:
//   https://bugs.llvm.org/show_bug.cgi?id=950
#define IR_PRIMS \
    X(NONE)      \
    X(void)      \
    X(i1) /* Boolean value */ \
    X(i8) /* Integers */ \
    X(i16)       \
    X(i32)       \
    X(i64)       \
    X(f32) /* Float */ \
    X(f64) /* Double */

typedef enum {
#define X(name) T_ ## name,
    IR_PRIMS
#undef X
} Prim;

typedef struct {
    Prim prim;
    int ptrs; // Number of levels of pointer indirection
} Type;

Type type_none();
int bits(Type t);  // Returns the size of a type in bits
int bytes(Type t); // Returns the size of a type in bytes


// ---- Abstract Syntax Tree --------------------------------------------------

// Keep track of signed values throughout the AST, but ditch them in the IR
// in favour of signed instructions
typedef struct {
    Prim prim;
    int ptrs;
    int is_signed;
} SignedType;

Type signed_to_type(SignedType t);
SignedType signed_i1();
SignedType signed_i32();
int signed_bits(SignedType t);  // Returns the size of a type in bits

typedef struct local {
    struct local *next;
    SignedType type;
    char *name;
    struct ir_ins *alloc; // The IR_ALLOC instruction for this local
} Local;

typedef enum {
    EXPR_KINT,    // Constant integer
    EXPR_LOCAL,   // Local variable
    EXPR_CONV,    // Type conversion
    EXPR_POSTFIX, // Postfix operation
    EXPR_UNARY,   // Unary (or prefix) operation
    EXPR_BINARY,  // Binary operation
    EXPR_TERNARY, // Ternary operation ('?' only)
} ExprType;

typedef struct expr {
    ExprType kind;
    SignedType type; // Type for the result of the expression
    union {
        int kint;                                          // EXPR_KINT
        Local *local;                                      // EXPR_LOCAL
        struct { Tk op; struct expr *l; };                 // Unary, postfix
        struct { Tk _op1; struct expr *_l1, *r; };         // EXPR_BINARY
        struct { Tk _op2; struct expr *_l2, *_r, *cond; }; // EXPR_TERNARY
        // Nothing for EXPR_CONV
    };
    TkInfo tk;
} Expr;

typedef struct if_chain {
    struct if_chain *next; // For 'else if' and 'else' components
    Expr *cond;            // NULL for 'else' component
    struct stmt *body;
} IfChain;

typedef enum {
    STMT_DECL,
    STMT_EXPR,
    STMT_IF,
    STMT_WHILE,
    STMT_DO_WHILE,
    STMT_FOR,
    STMT_BREAK,
    STMT_CONTINUE,
    STMT_RET,
} StmtType;

typedef struct stmt {
    struct stmt *next; // Linked list of statements in a block
    StmtType kind;
    union {
        Expr *expr;                                       // STMT_EXPR, STMT_RET
        Local *local;                                     // STMT_DECL
        IfChain *if_chain;                                // STMT_IF
        struct { Expr *cond; struct stmt *body; };        // STMT_WHILE/DO_WHILE
        struct { Expr *_c; struct stmt *_b; Expr *inc; }; // STMT_FOR
        // Nothing for STMT_BREAK, STMT_CONTINUE
    };
} Stmt;

typedef struct fn_arg {
    struct fn_arg *next;
    Local *local;
    struct ir_ins *ir_farg; // The IR_FARG instruction emitted for this arg
} FnArg;

typedef struct {
    SignedType return_type;
    char *name;
    FnArg *args; // Linked list of function arguments
} FnDecl;

typedef struct fn_def {
    struct fn_def *next;
    FnDecl *decl;
    Stmt *body;
} FnDef;

typedef struct {
    FnDef *fns; // Linked list of top-level functions
} AstModule;

AstModule * new_ast_module();
FnDef * new_fn_def();
FnDecl * new_fn_decl();
FnArg * new_fn_arg();
Stmt * new_stmt(StmtType kind);
IfChain * new_if_chain();
Expr * new_expr(ExprType kind);
Local * new_local(char *name, SignedType type);


// ---- Static Single Assignment (SSA) Form IR --------------------------------

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
    X(SDIV, 2) /* Signed */ \
    X(UDIV, 2) /* Unsigned */ \
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

    IrOpcode op;
    Type type; // Everything except control flow records its return type
    union {
        PhiChain *phi;                         // IR_PHI
        int arg_num;                      // IR_FARG
        int kint;                         // IR_KINT
        struct { struct ir_ins *l, *r; }; // Binary operations
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
    int vreg;       // Virtual register assigned to the instruction's result
    int stack_slot; // For IR_ALLOC: location on the stack relative to rbp

    // Debug information
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
    REG_L, // Lowest 8 bits (e.g., al)
    REG_H, // Highest 8 bits of the lowest 16 bits (e.g., ah)
    REG_W, // Lowest 16 bits (e.g., ax)
    REG_D, // Lowest 32 bits (e.g., eax)
    REG_Q, // All 64 bits (e.g., rax)
} RegSize;

static char *REG_NAMES[][5] = {
#define X(name, q, d, w, h, l) {[REG_Q] = (q), [REG_D] = (d), [REG_W] = (w), \
                                [REG_H] = (h), [REG_L] = (l)},
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
    OP_REG,   // Physical register (e.g., rax, etc.)
    OP_VREG,  // Virtual register (only prior to register allocation)
    OP_MEM,   // Memory access
    OP_LABEL, // Symbol for a branch
    OP_FN,    // Symbol for a call
} AsmOperandType;

typedef struct {
    AsmOperandType type;
    union {
        int imm;                           // OP_IMM
        struct { RegSize size; Reg reg; }; // OP_REG
        struct { RegSize _s1; int vreg; }; // OP_VREG
        struct { RegSize _s2; Reg base; int scale, index, bytes; }; // OP_MEM
        struct bb *bb;                     // OP_LABEL
        struct fn *fn;                     // OP_FN
    };
} AsmOperand;

typedef struct asm_ins {
    struct asm_ins *next, *prev;
    struct bb *bb;
    int idx;
    AsmOpcode op;
    AsmOperand l, r;
} AsmIns;


// ---- Unified Blocks --------------------------------------------------------

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

    // Per-BB analysis information
    CFGInfo cfg;
    LivenessInfo live;
} BB;

typedef struct fn {
    struct fn *next;  // Linked list of functions
    char *name;       // Output name for the function
    BB *entry, *last; // Linked list of basic blocks
    int num_vregs;    // For the assembler (number of vregs used)
} Fn;

typedef struct {
    Fn *fns;  // Linked list of functions
    Fn *main; // Function called 'main', if there is one, used as program entry
} Module;

Module * new_module();
Fn * new_fn();
BB * new_bb();

IrIns * new_ir(IrOpcode op);
void emit_ir(BB *bb, IrIns *ins);
void delete_ir(IrIns *ins);

AsmIns * emit_asm(BB *bb, AsmOpcode op); // TODO: split into new_asm and emit_asm
void delete_asm(AsmIns *ins);

#endif
