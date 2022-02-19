
#ifndef COSEC_PARSER_H
#define COSEC_PARSER_H

#include "Lexer.h"
#include "Type.h"

// PARSER -- builds an abstract syntax tree (AST, see 'IR.h') from C source
// code. Some transformations (e.g., type filling, which propagates the types
// for expressions through expression trees) and error checking (e.g.,
// incorrect syntax, undefined locals) are performed on the AST before it's
// compiled to SSA IR.

typedef struct local {
    struct local *next;
    Type type;
    char *name;
    struct ir_ins *alloc; // The IR_ALLOC instruction for this local
} Local;

typedef struct {
    Type type;
    TkInfo tk;
} AbstractDeclarator;

typedef struct {
    Type type;
    TkInfo name;
    TkInfo tk;
} DirectDeclarator;

typedef enum {
    EXPR_KINT,    // Constant integer
    EXPR_KFLOAT,  // Constant floating point
    EXPR_KCHAR,   // Character literal
    EXPR_KSTR,    // String literal
    EXPR_LOCAL,   // Local variable
    EXPR_CONV,    // Type conversion
    EXPR_POSTFIX, // Postfix operation
    EXPR_UNARY,   // Unary (or prefix) operation
    EXPR_BINARY,  // Binary operation
    EXPR_TERNARY, // Ternary operation ('?' only)
} ExprType;

typedef struct expr {
    ExprType kind;
    Type type; // Type for the result of the expression
    union {
        int kint;      // EXPR_KINT
        double kfloat; // EXPR_KFLOAT
        char kch;      // EXPR_KCHAR
        char *kstr;    // EXPR_KSTR
        Local *local;  // EXPR_LOCAL
        struct { Tk op; struct expr *l; }; // EXPR_UNARY, EXPR_POSTFIX
        struct { Tk _o1; struct expr *_l1, *r; }; // EXPR_BINARY
        struct { Tk _o2; struct expr *_l2, *_r, *cond; }; // EXPR_TERNARY
        // Nothing for EXPR_CONV
    };
    TkInfo tk;
} Expr;

Expr * new_expr(ExprType kind); // Used by the compiler

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
    Type return_type;
    Local *local;
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

AstModule * parse(char *file);

#endif
