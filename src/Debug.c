
#include <stdio.h>

#include "Debug.h"

static char *PRIM_NAMES[] = {
#define X(name) #name,
        IR_PRIMS
#undef X
};

static void print_type(Type t) {
    if (t.prim == T_NONE) {
        return;
    }
    printf("%s", PRIM_NAMES[t.prim]); // Primitive name
    for (int i = 0; i < t.ptrs; i++) {
        printf("*"); // Star for every pointer indirection
    }
}

// ---- Abstract Syntax Tree --------------------------------------------------

static char *TK_NAMES[NUM_TKS] = {
#define X(name, str) [TK_ ## name] = (str),             // Value tokens
#define Y(name, _, __, str) [TK_ ## name] = (str),      // Two characters
#define Z(name, _, __, ___, str) [TK_ ## name] = (str), // Three characters
#define K(name, str) [TK_ ## name] = (str),             // Keywords
        TOKENS
#undef K
#undef Z
#undef Y
#undef X
};

static void print_local(Local *local) {
    print_type(local->type);
    printf(" %s", local->name);
}

static void print_tk(Tk op) {
    if (op < 256) { // Single character token
        printf("%c", (char) op);
    } else { // Multi-character token
        printf("%s", TK_NAMES[op]);
    }
}

static void print_expr(Expr *expr) {
    switch (expr->kind) {
    case EXPR_KINT:
        print_type(expr->type);
        printf(" %d", expr->kint);
        break;
    case EXPR_LOCAL:
        print_local(expr->local);
        break;
    case EXPR_CONV:
        print_type(expr->type);
        printf(" ( conv ");
        print_expr(expr->l);
        printf(" )");
        break;
    case EXPR_POSTFIX:
        print_type(expr->type);
        printf(" ( ");
        print_expr(expr->l);
        printf(" ");
        print_tk(expr->op);
        printf(" )");
        break;
    case EXPR_UNARY:
        print_type(expr->type);
        printf(" ( ");
        print_tk(expr->op);
        printf(" ");
        print_expr(expr->l);
        printf(" )");
        break;
    case EXPR_BINARY:
        print_type(expr->type);
        printf(" ( ");
        print_tk(expr->op);
        printf(" ");
        print_expr(expr->l);
        printf(" ");
        print_expr(expr->r);
        printf(" )");
        break;
    case EXPR_TERNARY:
        print_type(expr->type);
        printf(" ( ? ");
        print_expr(expr->cond);
        printf(" ");
        print_expr(expr->l);
        printf(" ");
        print_expr(expr->r);
        printf(" )");
        break;
    }
}

static void print_block(int indent, Stmt *block); // Forward declaration

static void print_stmt(int indent, Stmt *stmt) {
    for (int i = 0; i < indent * 2; i++) { printf(" "); }
    switch (stmt->kind) {
    case STMT_DECL:
        print_local(stmt->local);
        printf("\n");
        break;
    case STMT_EXPR:
        print_expr(stmt->expr);
        printf("\n");
        break;
    case STMT_IF:
        for (IfChain *i = stmt->if_chain; i; i = i->next) {
            printf(i == stmt->if_chain ? "if" : (i->cond ? "else if" : "else"));
            if (i->cond) {
                printf(" ");
                print_expr(i->cond);
            }
            printf(" ");
            print_block(indent + 1, i->body);
            printf(" ");
        }
        printf("\n");
        break;
    case STMT_WHILE:
        printf("while ");
        print_expr(stmt->cond);
        printf(" ");
        print_block(indent + 1, stmt->body);
        printf("\n");
        break;
    case STMT_DO_WHILE:
        printf("do ");
        print_block(indent + 1, stmt->body);
        printf(" while ");
        print_expr(stmt->cond);
        printf("\n");
        break;
    case STMT_FOR:
        printf("for ");
        print_local(stmt->ind);
        printf("; ");
        print_expr(stmt->init);
        printf("; ");
        print_expr(stmt->cond);
        printf("; ");
        print_expr(stmt->inc);
        printf(" ");
        print_block(indent + 1, stmt->body);
        printf("\n");
        break;
    case STMT_BREAK:
        printf("break\n");
        break;
    case STMT_RET:
        printf("return ");
        if (stmt->expr) {
            print_expr(stmt->expr);
        }
        printf("\n");
        break;
    }
}

static void print_block(int indent, Stmt *block) {
    printf("{\n");
    while (block) {
        print_stmt(indent, block);
        block = block->next;
    }
    for (int i = 0; i < (indent - 1) * 2; i++) { printf(" "); }
    printf("}");
}

void print_ast(FnDef *fn) {
    if (!fn) {
        return;
    }
    print_type(fn->decl->return_type);
    printf(" %s ( ", fn->decl->name);
    for (FnArg *arg = fn->decl->args; arg; arg = arg->next) {
        print_local(arg->local);
        if (arg->next) {
            printf(" ");
        }
    }
    printf(" ) ");
    print_block(1, fn->body);
    printf("\n");
}


// ---- SSA IR ----------------------------------------------------------------

static char *IR_OPCODE_NAMES[] = {
#define X(opcode, nargs) #opcode,
    IR_OPCODES
#undef X
};

static void print_phi(IrIns *phi) {
    PhiChain *pair = phi->phi;
    while (pair) {
        printf("[ %s, %.4d ] ", pair->bb->label, pair->def->idx);
        pair = pair->next;
    }
}

static void print_ins(IrIns *ins) {
    printf("\t"); // Indent all instructions by a tab
    printf("%.4d\t", ins->idx); // Instruction's index in the function
    print_type(ins->type); // Return type (void if control flow)
    printf("\t%s\t", IR_OPCODE_NAMES[ins->op]); // Opcode name
    switch (ins->op) { // Handle special case instructions (e.g., constants)
    case IR_FARG:   printf("%d", ins->arg_num); break;
    case IR_KINT:   printf("%+d", ins->kint); break;
    case IR_ALLOC:  { Type t = ins->type; t.ptrs--; print_type(t); } break;
    case IR_BR:     printf("%s", ins->br ? ins->br->label : "NULL"); break;
    case IR_CONDBR:
        printf("%.4d\t", ins->cond->idx); // Condition
        printf("%s\t", ins->true ? ins->true->label : "NULL"); // True branch
        printf("%s", ins->false ? ins->false->label : "NULL"); // False branch
        break;
    case IR_PHI: print_phi(ins); break;
    default:
        if (IR_OPCODE_NARGS[ins->op] >= 1) { // Single argument instructions
            printf("%.4d", ins->l->idx);
        }
        if (IR_OPCODE_NARGS[ins->op] >= 2) { // Two argument instructions
            printf("\t%.4d", ins->r->idx);
        }
        break;
    }
    printf("\n");
}

static void print_bb(BB *bb) {
    printf("%s:\n", bb->label); // Print the BB label
    for (IrIns *ins = bb->ir_head; ins; ins = ins->next) {
        print_ins(ins); // Print every instruction in the BB
    }
}

static void number_ins(Fn *fn) {
    int ins_idx = 0;
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        for (IrIns *ins = bb->ir_head; ins; ins = ins->next) {
            ins->idx = ins_idx++; // Number the IR instructions
        }
    }
}

void print_ir(Fn *fn) {
    number_ins(fn);
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        print_bb(bb); // Print BBs in the order they appear in the source
    }
}
