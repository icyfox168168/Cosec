
#include <stdio.h>
#include <string.h>

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
    } else if (opts.help) {
        print_help();
    } else if (file) {
        // Compile
    } else {
        print_help();
    }
    return 0;
}
