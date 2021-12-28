
#include "Encoder.h"

static void encode_operand(AsmOperand op, FILE *out) {
    switch (op.type) {
    case OP_REG: fprintf(out, "%s", REG_NAMES[op.reg]); break;
    case OP_VREG:
        fprintf(out, "%%%d", op.vreg);
        switch (op.subsection) {
            case REG_32: fprintf(out, "(32)"); break;
            case REG_16: fprintf(out, "(16)"); break;
            case REG_8H: fprintf(out, "(8h)"); break;
            case REG_8L: fprintf(out, "(8l)"); break;
            default: break; // Don't print anything for REG_ALL
        }
        break;
    case OP_MEM:
        fprintf(out, "[%s", REG_NAMES[op.base]);
        if (op.scale > 1) {
            fprintf(out, "*%d", op.scale);
        }
        if (op.index > 0) {
            fprintf(out, " + %d", op.index);
        } else if (op.index < 0) {
            fprintf(out, " - %d", -op.index);
        }
        fprintf(out, "]");
        break;
    case OP_IMM: fprintf(out, "%llu", op.imm); break;
    case OP_LABEL: fprintf(out, "BB%d", op.bb->label); break;
    }
}

static void encode_ins(AsmIns *ins, FILE *out) {
    fprintf(out, "    %s", X86_OPCODE_NAMES[ins->op]);
    if (X86_OPCODE_NARGS[ins->op] >= 1) {
        fprintf(out, " ");
        encode_operand(ins->l, out);
    }
    if (X86_OPCODE_NARGS[ins->op] >= 2) {
        fprintf(out, ", ");
        encode_operand(ins->r, out);
    }
    fprintf(out, "\n");
}

static void encode_bb(AsmBB *bb, FILE *out) {
    for (AsmIns *ins = bb->head; ins; ins = ins->next) {
        encode_ins(ins, out);
    }
}

static void encode_fn(AsmFn *fn, FILE *out) {
    fprintf(out, "global %s\n", fn->name); // Make every function global for now
    fprintf(out, "%s:\n", fn->name); // Print the label for the basic block
    for (AsmBB *bb = fn->entry; bb; bb = bb->next) { // AsmBB are linear
        encode_bb(bb, out);
    }
}

void encode_nasm(AsmModule *m, FILE *out) {
    for (AsmFn *fn = m->fns; fn; fn = fn->next) {
        encode_fn(fn, out);
    }
}
