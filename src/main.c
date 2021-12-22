
#include <stdio.h>
#include <string.h>

#include "Parser.h"
#include "opt/Fold.h"
#include "Assembler.h"
#include "Encoder.h"
#include "Debug.h"

/* Cosec compiler structure:
 * 1. Lexer     -- splits a module's source code up into tokens
 * 2. Parser    -- generates IR from the source tokens
 * 3. Optimiser -- converts the IR into SSA form and optimises it
 * 4. Assembler -- lowers the SSA IR to target-specific machine code IR
 * 5. Encoder   -- writes the machine code to an object file ready for linking
 */

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
    for (int i = 1; i < argc; i++) { // Skip the first argument (the name of the executable)
        if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            opts.help = 1;
        } else if (strcmp(argv[i], "--version") == 0 || strcmp(argv[i], "-v") == 0) {
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
        print_bb(ir_module->fns->entry);
        AsmModule *asm_module = assemble(ir_module);
        printf("\n---- Assembly\n");
        encode_nasm(asm_module, stdout);
        FILE *output = fopen("out.s", "w");
        encode_nasm(asm_module, output);
        // Compile the generated assembly with:
        //     nasm -f macho64 out.s
        //     ld -L/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib -lSystem out.o
        // (Yes, the linker arguments are annoying, but necessary)
    }
    return 0;
}
