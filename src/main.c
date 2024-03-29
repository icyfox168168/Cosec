
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

static void print_version() {
    printf("cosec 0.1.0\n");
}

static void print_help() {
    printf("Usage: cosec [options] <files>\n");
    printf("\n");
    printf("Options:\n");
    printf("  --help, -h       Print this help message\n");
    printf("  --version, -v    Print the compiler version\n");
}

static void pipeline(char *file) {
    // AST
    AstModule *ast = parse(file);
    printf("---- AST\n");
    for (FnDef *fn = ast->fns; fn; fn = fn->next) {
        print_ast(fn);
        printf("\n");
    }

    // SSA IR
    printf("---- SSA IR\n");
    Module *module = compile(ast);
    for (Fn *fn = module->fns; fn; fn = fn->next) {
        printf("%s:\n", fn->name);
        print_ir(fn);
        printf("\n");
    }

    // IR analysis
    for (Fn *fn = module->fns; fn; fn = fn->next) {
        analyse_use_chains(fn);
    }

    // Assembler
    printf("---- Assembly IR\n");
    assemble(module);
    emit_nasm(module, stdout);
    printf("\n");

    // Register allocator
    printf("---- Register allocation\n");
    for (Fn *fn = module->fns; fn; fn = fn->next) {
        printf("Register allocation for function '%s':\n", fn->name);
        analyse_cfg(fn->entry);
        reg_alloc(fn);
        printf("\n");
    }

    // Emitter
    printf("---- Final\n");
    emit_nasm(module, stdout);
    FILE *output = fopen("out.s", "w");
    emit_nasm(module, output);
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
        pipeline(file);
    }
    return 0;
}
