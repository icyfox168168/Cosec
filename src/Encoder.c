
#include "Encoder.h"

static char *X86_OPCODE_NAMES[] = {
#define X(_, str, __) str,
    X86_OPCODES
#undef X
};

static char * NASM_MEM_PREFIX[] = {
    [1] = "byte",
    [2] = "word",
    [4] = "dword",
    [8] = "qword",
};

static void encode_operand(AsmOperand op, FILE *out) {
    switch (op.type) {
    case OP_IMM: fprintf(out, "%llu", op.imm); break;
    case OP_REG: fprintf(out, "%s", REG_NAMES[op.reg][op.bits]); break;
    case OP_VREG:
        fprintf(out, "%%%d", op.vreg);
        switch (op.bits) {
            case REG_Q: break; // Don't print anything for REG_64
            case REG_D: fprintf(out, "(d)"); break;
            case REG_W: fprintf(out, "(w)"); break;
            case REG_H: fprintf(out, "(h)"); break;
            case REG_L: fprintf(out, "(l)"); break;
        }
        break;
    case OP_MEM:
        fprintf(out, "%s ", NASM_MEM_PREFIX[op.size]);
        fprintf(out, "[%s", REG_NAMES[op.base][op.bits]); // Base
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
    }
}

static void encode_ins(AsmIns *ins, FILE *out) {
    fprintf(out, "    "); // Indent instructions by 4 spaces
    fprintf(out, "%s", X86_OPCODE_NAMES[ins->op]); // Instruction opcode
    if (X86_OPCODE_NARGS[ins->op] >= 1) { // First argument
        fprintf(out, " ");
        encode_operand(ins->l, out);
    }
    if (X86_OPCODE_NARGS[ins->op] >= 2) { // Second argument
        fprintf(out, ", ");
        encode_operand(ins->r, out);
    }
    fprintf(out, "\n");
}

static void encode_bb(BB *bb, FILE *out) {
    fprintf(out, "%s:\n", bb->label); // BB's label
    for (AsmIns *ins = bb->asm_head; ins; ins = ins->next) {
        encode_ins(ins, out); // Print every instruction in the BB
    }
}

static void encode_fn(AsmFn *fn, FILE *out) {
    fprintf(out, "global %s\n", fn->entry->label); // Make every function global
    for (BB *bb = fn->entry; bb; bb = bb->next) {
        encode_bb(bb, out); // Print every basic block in the function
    }
}

void encode_nasm(AsmModule *m, FILE *out) {
    for (AsmFn *fn = m->fns; fn; fn = fn->next) {
        encode_fn(fn, out); // Print every function in the module
        if (fn->next) {
            fprintf(out, "\n"); // Separated by a new line
        }
    }
}
