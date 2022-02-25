
#include <stdio.h>
#include <math.h>
#include <string.h>
#include <assert.h>

#include "Debug.h"

#define BB_PREFIX ".BB_"

static char *PRIM_NAMES[] = {
#define X(name, _) #name,
    IR_PRIMS
#undef X
};

static int print_type(Type *t) {
    if (!t) {
        return 0;
    }
    int len = 0;
    switch (t->kind) {
    case T_PRIM:
        len += printf("%s", PRIM_NAMES[t->prim]);
        break;
    case T_ARR:
        len += printf("[%llu x ", t->size);
        len += print_type(t->elem);
        len += printf("]");
        break;
    case T_PTR:
        len += print_type(t->ptr);
        len += printf("*");
        break;
    }
    return len;
}

// ---- Abstract Syntax Tree --------------------------------------------------

static void print_local(Local *local) {
    print_type(local->type);
    printf(" %s", local->name);
}

static void print_expr(Expr *expr) {
    switch (expr->kind) {
    case EXPR_KINT:
        print_type(expr->type);
        printf(" +%llu", expr->kint);
        break;
    case EXPR_KFLOAT:
        print_type(expr->type);
        printf(" %+g", expr->kfloat);
        break;
    case EXPR_KCHAR:
        print_type(expr->type);
        printf(" '%c'", expr->kch);
        break;
    case EXPR_KSTR:
        print_type(expr->type);
        printf(" \"%s\"", expr->kstr);
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
        print_simple_tk(expr->op);
        printf(" )");
        break;
    case EXPR_UNARY:
        print_type(expr->type);
        printf(" ( ");
        print_simple_tk(expr->op);
        printf(" ");
        print_expr(expr->l);
        printf(" )");
        break;
    case EXPR_BINARY:
        print_type(expr->type);
        printf(" ( ");
        print_simple_tk(expr->op);
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
        if (stmt->cond) {
            print_expr(stmt->cond);
            printf(" ");
        }
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
        if (stmt->cond) {
            print_expr(stmt->cond);
        }
        printf("; ");
        if (stmt->inc) {
            print_expr(stmt->inc);
        }
        printf(" ");
        print_block(indent + 1, stmt->body);
        printf("\n");
        break;
    case STMT_BREAK:    printf("break\n"); break;
    case STMT_CONTINUE: printf("continue\n"); break;
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
    printf(" %s ( ", fn->decl->local->name);
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

static void print_imm(IrIns *imm) {
    printf("+%llu", imm->imm);
    if (imm->type->kind == T_PTR && imm->type->ptr->kind == T_PRIM &&
            imm->type->ptr->prim == T_i8 && imm->type->ptr->is_signed) {
        printf(" ('%c')", (char) imm->imm);
    }
}

static void print_const(Fn *fn, IrIns *k) {
    Constant c = fn->consts[k->const_idx];
    if (k->type->kind == T_PRIM && k->type->prim == T_f32) {
        printf("%+g", c.f32);
    } else if (k->type->kind == T_PRIM && k->type->prim == T_f64) {
        printf("%+g", c.f64);
    } else if (k->type->kind == T_PTR && k->type->ptr->kind == T_PRIM &&
               k->type->ptr->prim == T_i8) {
        printf("\"%s\"", c.str);
    } else {
        UNREACHABLE();
    }
}

static void print_phi(IrIns *phi) {
    PhiChain *pair = phi->phi;
    while (pair) {
        printf("[ %s, %.4d ] ", pair->bb->label, pair->def->idx);
        pair = pair->next;
    }
}

static void print_ins(Fn *fn, IrIns *ins) {
    printf("\t"); // Indent all instructions by a tab
    printf("%.4d\t", ins->idx); // Instruction's index in the function
    int type_len = print_type(ins->type); // Return type (void if control flow)
    if (type_len < 8) { // Two tabs for short types
        printf("\t");
    }
    printf("\t%s\t", IR_OPCODE_NAMES[ins->op]); // Opcode name
    switch (ins->op) { // Handle special case instructions (e.g., constants)
    case IR_FARG:  printf("%d", ins->arg_num); break;
    case IR_IMM:   print_imm(ins); break;
    case IR_CONST: print_const(fn, ins); break;
    case IR_ALLOC: print_type(ins->type->ptr); break;
    case IR_BR:    printf("%s", ins->br ? ins->br->label : "NULL"); break;
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

static void print_bb(Fn *fn, BB *bb) {
    printf("%s:\n", bb->label); // Print the BB label
    for (IrIns *ins = bb->ir_head; ins; ins = ins->next) {
        print_ins(fn, ins); // Print every instruction in the BB
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

static char * bb_label(int idx) {
    int num_digits = (idx == 0) ? 1 : (int) log10(idx) + 1;
    char *out = malloc(strlen(BB_PREFIX) + num_digits + 1);
    sprintf(out, BB_PREFIX "%d", idx);
    return out;
}

static void label_bbs(Fn *fn) {
    int idx = 0;
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        if (!bb->label) {
            bb->label = bb_label(idx++);
        }
    }
}

void print_ir(Fn *fn) {
    label_bbs(fn);
    number_ins(fn);
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        print_bb(fn, bb); // Print BBs in the order they appear in the source
    }
}
