
#include <stdio.h>
#include <string.h>

#include "Compiler.h"
#include "Assembler.h"
#include "RegAlloc.h"
#include "Emitter.h"
#include "Debug.h"

#include "analysis/CFG.h"
#include "analysis/UseChain.h"

// Compile the generated assembly with (on my macOS machine):
//     nasm -f macho64 out.s
//     ld -L/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib -lSystem out.o
// (Yes, the linker arguments are annoying but necessary on macOS Big Sur)
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
// See the assembly code generated by compiling LLVM IR (e.g., if you modify or
// optimise it) with:
//     llc --x86-asm-syntax=intel -O0 test.ll
//     cat test.s

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
        // TODO: only handles a single function for now
        AstModule *ast = parse(file);
        printf("---- AST\n");
        print_ast(ast->fns);
        printf("\n");

        Module *module = compile(ast);
        printf("---- IR\n");
        print_ir(module->fns);
        printf("\n");

        analyse_use_chains(module->fns);
        assemble(module);
        printf("---- Assembly\n");
        encode_nasm(module, stdout);
        printf("\n");

        printf("---- Register allocated assembly\n");
        analyse_cfg(module->fns->entry);
        LiveRange *live_ranges = analyse_live_ranges(module->fns);
        reg_alloc(module->fns, live_ranges);
        encode_nasm(module, stdout);

        FILE *output = fopen("out.s", "w");
        encode_nasm(module, output);
    }
    return 0;
}
