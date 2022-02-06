
#include <stdio.h>
#include <stdarg.h>
#include <math.h>
#include <ctype.h>

// Only bother including this file if we support colors
#if !defined(_WIN32) && !defined(_WIN64)
#include <unistd.h>
#endif

#include "Error.h"

// ANSI terminal color codes
#define COLOUR_CLEAR  0
#define COLOUR_BOLD   1
#define COLOUR_RED    31
#define COLOUR_GREEN  32
#define COLOUR_YELLOW 33
#define COLOUR_BLUE   34
#define COLOUR_WHITE  37

static int supports_color() {
#if defined(_WIN32) || defined(_WIN64)
    // Don't bother with color support on Windows
    return 0;
#else
    // Base color input only on the fact if the standard output is a
	// terminal. We should probably be checking the TERM environment variable
    // for a dumb terminal, or using the terminfo database, but in practice this
	// is probably unnecessary as we don't expect to have the compiler run on
	// old hardware
    static int supported = -1;
    if (supported < 0) {
        // Lazily check if colour is supported and save it
        supported = isatty(fileno(stdout));
    }
	return supported;
#endif
}

static void print_colour(int colour) {
    if (!supports_color()) {
        return;
    }
    // Changing the text formatting attributes involves printing a special
    // terminal escape sequence (`\033[`), and then a command (`%dm`)
    printf("\033[%dm", colour);
}

static void print_error_header() {
    print_colour(COLOUR_RED);
    print_colour(COLOUR_BOLD);
    printf("error: ");
    print_colour(COLOUR_WHITE);
}

void trigger_error(char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    print_error_header();
    vprintf(fmt, args);
    print_colour(COLOUR_CLEAR);
    printf("\n");
    va_end(args);
    exit(1);
}

static void print_error_info(TkInfo at) {
    if (!at.file) {
        return; // No file
    }
    print_colour(COLOUR_BLUE);
    printf(" --> ");
    print_colour(COLOUR_CLEAR);
    printf("%s", at.file);
    if (at.line > 0) {
        printf(":%d", at.line);
    }
    if (at.col > 0) {
        printf(":%d", at.col);
    }
    printf("\n");

    if (!at.line_str) {
        return; // No line of code
    }
    print_colour(COLOUR_BLUE);
    printf(" %d | ", at.line);
    print_colour(COLOUR_CLEAR);
    char *c = at.line_str;
    while (isspace(*c)) { // Print only spaces at the start of the line
        if (*c == '\t') {
            printf("  ");
        } else {
            printf(" ");
        }
        c++;
    }
    char *text_start = c;
    while (*c && *c != '\n' && *c != '\r') { // Find the end of the line
        c++;
    }
    int line_len = (int) (c - text_start);
    printf("%.*s\n", line_len, text_start);

    if (at.len < 0 || at.col < 1) {
        return; // No arrow
    }
    int num_digits = (at.line == 0) ? 1 : (int) log10(at.line) + 1;
    for (int i = 0; i < num_digits + 4; i++) { // Spaces for line number
        printf(" ");
    }
    c = at.line_str;
    while (isspace(*c)) { // Spaces to start line
        if (*c == '\t') {
            printf("  ");
        } else {
            printf(" ");
        }
        c++;
    }
    while ((int) (c - at.line_str) < at.col - 1) { // Spaces until arrow
        printf(" ");
        c++;
    }
    print_colour(COLOUR_GREEN);
    printf("^"); // Arrow head
    for (int i = 0; i < at.len - 1; i++) {
        printf("~"); // Arrow tail
    }
    print_colour(COLOUR_CLEAR);
    printf("\n");
}

void trigger_error_at(TkInfo at, char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    print_error_header();
    vprintf(fmt, args);
    print_colour(COLOUR_CLEAR);
    printf("\n");
    print_error_info(at);
    va_end(args);
    exit(1);
}

void expect_tk(Lexer *l, Tk expected) {
    if (l->tk == expected) {
        return; // No error
    }
    print_error_header();
    printf("expected ");
    print_tk(expected);
    printf(", found ");
    print_tk(l->tk);
    print_colour(COLOUR_CLEAR);
    printf("\n");
    print_error_info(l->info);
    exit(1);
}
