
#include <assert.h>

#include "Emitter.h"

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

static void write_operand(AsmOperand op, FILE *out) {
    switch (op.type) {
    case OP_IMM: fprintf(out, "%d", op.imm); break;
    case OP_REG: fprintf(out, "%s", REG_NAMES[op.reg][op.size]); break;
    case OP_VREG:
        fprintf(out, "%%%d", op.vreg);
        switch (op.size) {
            case REG_Q: fprintf(out, "(q)"); break;
            case REG_D: fprintf(out, "(d)"); break;
            case REG_W: fprintf(out, "(w)"); break;
            case REG_H: fprintf(out, "(h)"); break;
            case REG_L: fprintf(out, "(l)"); break;
        }
        break;
    case OP_MEM:
        assert(op.bytes >= 0);
        fprintf(out, "%s ", NASM_MEM_PREFIX[op.bytes]);
        fprintf(out, "[%s", REG_NAMES[op.base][op.size]); // Base
        if (op.scale > 1) { // Scale
            fprintf(out, "*%d", op.scale);
        }
        if (op.index > 0) { // Index
            fprintf(out, " + %d", op.index);
        } else if (op.index < 0) {
            fprintf(out, " - %d", -op.index);
        }
        fprintf(out, "]");
        break;
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

static void write_fn(Fn *fn, FILE *out) {
    fprintf(out, "global %s\n", fn->name); // Make every function global
    fprintf(out, "%s:\n", fn->name);
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        write_bb(bb, out); // Print every basic block in the function
    }
}

void emit_nasm(Module *m, FILE *out) {
    for (Fn *fn = m->fns; fn; fn = fn->next) {
        write_fn(fn, out); // Print every function in the module
        if (fn->next) {
            fprintf(out, "\n"); // Separated by a new line
        }
    }
}
