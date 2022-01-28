
#include <stdio.h>
#include <string.h>

#include "Parser.h"
#include "Assembler.h"
#include "RegisterAllocator.h"
#include "Encoder.h"
#include "Debug.h"
#include "analysis/CFG.h"

// Cosec compiler structure:
// 1. Lexer -- splits a module's source code up into tokens
// 2. Parser -- generates IR from the source tokens
// 3. Optimiser -- converts the IR into SSA form and optimises it
// 4. Assembler -- lowers the SSA IR to target-specific machine code IR
// 5. Register allocation -- lowers virtual registers in the IR to physical ones
// 6. Encoder -- writes the machine code to an object file ready for linking
//
// Compile the generated assembly with (on my macOS machine):
//     nasm -f macho64 out.s
//     ld -L/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib -lSystem out.o
// (Yes, the linker arguments are annoying, but necessary)
//
// For debugging, see the equivalent LLVM IR with:
//     clang -emit_ins-llvm -Xclang -disable-O0-optnone -S test.c
//     cat test.ll
// See the assembly code generated by clang with:
//     clang -S -masm=intel -O0 test.c
//     cat test.s
// See the result of optimisations (e.g., mem2reg) on the LLVM IR with:
//     clang -emit_ins-llvm -Xclang -disable-O0-optnone -S test.c
//     opt -S test.ll -mem2reg
//     cat test.ll

typedef struct {
    int help, version;
} CLIOpts;

void print_version() {
    printf("Cosec v0.1\n");
    printf("A toy optimising C compiler\n");
}

void print_help() {
    printf("Usage: cosec [options] <files>\n");
    printf("\n");
    printf("Options:\n");
    printf("  --help, -h       Print this help message\n");
    printf("  --version, -v    Print the compiler version\n");
}

int main(int argc, char *argv[]) {
    CLIOpts opts = {0};
    char *file = NULL;
    for (int i = 1; i < argc; i++) { // Skip the first arg (the executable name)
        char *arg = argv[i];
        if (strcmp(arg, "--help") == 0 || strcmp(arg, "-h") == 0) {
            opts.help = 1;
        } else if (strcmp(arg, "--version") == 0 || strcmp(arg, "-v") == 0) {
            opts.version = 1;
        } else {
            file = argv[i];
        }
    }
    if (opts.version) {
        print_version();
    } else if (opts.help || !file) {
        print_help();
    } else {
        Module *ir_module = parse(file);
        printf("---- IR\n");
        print_fn(ir_module->fn);

        AsmModule *asm_module = assemble(ir_module);
        printf("\n---- Assembly\n");
        encode_nasm(asm_module, stdout);

        printf("\n---- Register allocated assembly\n");
        analysis_cfg(asm_module->fns->entry);
        LiveRange *live_ranges = analysis_liveness(asm_module->fns);
        reg_alloc(asm_module->fns, live_ranges);
        encode_nasm(asm_module, stdout);

        FILE *output = fopen("out.s", "w");
        encode_nasm(asm_module, output);
    }
    return 0;
}
