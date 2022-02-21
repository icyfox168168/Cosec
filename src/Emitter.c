
#include <assert.h>
#include <math.h>
#include <stdio.h>
#include <string.h>

#include "Emitter.h"

#define BB_PREFIX    ".BB_"
#define CONST_PREFIX "K_"

static char *X86_OPCODE_NAMES[] = {
#define X(_, str, __) str,
    X86_OPCODES
#undef X
};

static char *NASM_MEM_PREFIX[] = {
    [1] = "byte",
    [2] = "word",
    [4] = "dword",
    [8] = "qword",
};

static void write_gpr(int reg, RegSize size, FILE *out) {
    assert(size != REG_NONE);
    if (reg < LAST_GPR) {
        fprintf(out, "%s", GPR_NAMES[size][reg]);
    } else {
        fprintf(out, "%%%d", reg - LAST_GPR);
        switch (size) {
            case REG_Q: fprintf(out, "q"); break;
            case REG_D: fprintf(out, "d"); break;
            case REG_W: fprintf(out, "w"); break;
            case REG_H: fprintf(out, "h"); break;
            case REG_L: fprintf(out, "l"); break;
            default: UNREACHABLE();
        }
    }
}

static void write_sse_reg(int reg, FILE *out) {
    if (reg < LAST_SSE) {
        fprintf(out, "%s", SSE_REG_NAMES[reg]);
    } else {
        fprintf(out, "%%%df", reg - LAST_SSE);
    }
}

static void write_mem_op(AsmOperand op, FILE *out) {
    if (op.access_size > 0) {
        fprintf(out, "%s ", NASM_MEM_PREFIX[op.access_size]);
    }
    fprintf(out, "[");
    write_gpr(op.base_reg, op.base_size, out); // Base
    if (op.index_size > REG_NONE) { // Index
        fprintf(out, " + ");
        write_gpr(op.index_reg, op.index_size, out);
        if (op.scale > 1) { // Scale
            fprintf(out, "*%d", op.scale);
        }
    }
    if (op.disp > 0) {
        fprintf(out, " + %d", op.disp);
    } else if (op.disp < 0) {
        fprintf(out, " - %d", -op.disp);
    }
    fprintf(out, "]");
}

static void write_const_op(AsmOperand op, FILE *out) {
    if (op.access_size > 0) {
        fprintf(out, "%s ", NASM_MEM_PREFIX[op.access_size]);
    }
    fprintf(out, "[rel " CONST_PREFIX "%d]", op.const_idx);
}

static void write_operand(AsmOperand op, FILE *out) {
    switch (op.type) {
        case OP_IMM:   fprintf(out, "%llu", op.imm); break;
        case OP_GPR:   write_gpr(op.reg, op.size, out); break;
        case OP_XMM:   write_sse_reg(op.reg, out); break;
        case OP_MEM:   write_mem_op(op, out); break;
        case OP_CONST: write_const_op(op, out); break;
        case OP_LABEL: fprintf(out, "%s", op.bb->label); break;
        case OP_FN:    fprintf(out, "%s", op.fn->name); break;
    }
}

static void write_ins(AsmIns *ins, FILE *out) {
    fprintf(out, "    "); // Indent instructions by 4 spaces
    fprintf(out, "%s", X86_OPCODE_NAMES[ins->op]); // Opcode
    if (X86_OPCODE_NARGS[ins->op] >= 1) { // First argument
        fprintf(out, " ");
        write_operand(ins->l, out);
    }
    if (X86_OPCODE_NARGS[ins->op] >= 2) { // Second argument
        fprintf(out, ", ");
        write_operand(ins->r, out);
    }
    fprintf(out, "\n");
}

static void write_bb(BB *bb, FILE *out) {
    if (bb->label) {
        fprintf(out, "%s:\n", bb->label);
    }
    for (AsmIns *ins = bb->asm_head; ins; ins = ins->next) {
        write_ins(ins, out); // Print every instruction in the BB
    }
}

static void write_const(int idx, Constant c, FILE *out) {
    fprintf(out, CONST_PREFIX "%d: ", idx);
    if (c.type->kind == T_PRIM && c.type->prim == T_f32) {
        fprintf(out, "dd 0x%x ; float %g", c.out32, c.f32);
    } else if (c.type->kind == T_PRIM && c.type->prim == T_f64) {
        fprintf(out, "dq 0x%llx ; double %g", c.out64, c.f64);
    } else if (c.type->kind == T_PTR && c.type->ptr->kind == T_PRIM &&
               c.type->ptr->prim == T_i8) {
        fprintf(out, "db \"%s\", 0", c.str);
    } else {
        UNREACHABLE();
    }
    fprintf(out, "\n");
}

static void write_consts(Fn *fn, FILE *out) {
    for (int i = 0; i < fn->num_consts; i++) {
        Constant c = fn->consts[i];
        if (is_fp(c.type)) { // Only write floating point constants here
            write_const(i, c, out);
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

static void write_fn(Fn *fn, FILE *out) {
    label_bbs(fn);
    write_consts(fn, out);
    fprintf(out, "global %s\n", fn->name); // Make every function global
    fprintf(out, "%s:\n", fn->name);
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        write_bb(bb, out); // Print every basic block in the function
    }
}

void emit_nasm(Module *m, FILE *out) {
    fprintf(out, "section .text\n");
    for (Fn *fn = m->fns; fn; fn = fn->next) {
        write_fn(fn, out); // Print every function in the module
        if (fn->next) {
            fprintf(out, "\n"); // Separated by a new line
        }
    }

    // Write string constants to the data section
    int written_section_header = 0;
    for (Fn *fn = m->fns; fn; fn = fn->next) {
        for (int i = 0; i < fn->num_consts; i++) {
            Constant c = fn->consts[i];
            if (!is_fp(c.type)) {
                if (!written_section_header) {
                    fprintf(out, "\nsection .data\n");
                    written_section_header = 1;
                }
                write_const(i, c, out);
            }
        }
    }
}
