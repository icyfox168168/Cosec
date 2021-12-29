
#include <ctype.h>
#include <string.h>
#include <stdio.h>

#include "Lexer.h"

// Allows us to map between the KEYWORDS array and the Tk type
#define FIRST_KEYWORD TK_INT

static char *KEYWORDS[] = {
#define X(_)
#define Y(_, __, ___)
#define Z(_, __, ___, ____)
#define K(_, keyword) keyword,
    TOKENS
#undef K
#undef Z
#undef Y
#undef X
    NULL, // Marker for the end of the KEYWORDS array
};

Lexer new_lexer(char *source) {
    Lexer l;
    l.source = source;
    l.c = source;
    l.tk = 0;
    l.ident = NULL;
    l.len = 0;
    return l;
}

static void lex_whitespace(Lexer *l) {
    while (isspace(*l->c)) {
        l->c++;
    }
}

static void lex_ident(Lexer *l) {
    char *start = l->c;
    while (isalnum(*l->c) || *l->c == '_') { // Find the end of the identifier
        l->c++;
    }
    int len = (int) (l->c - start); // Length of the identifier
    for (int i = 0; KEYWORDS[i]; i++) { // Check identifier isn't a keyword
        char *keyword = KEYWORDS[i];
        if (strlen(keyword) == len && strncmp(keyword, start, len) == 0) {
            l->tk = FIRST_KEYWORD + i;
            return;
        }
    }
    l->tk = TK_IDENT;
    l->ident = start;
    l->len = len;
}

static void lex_int(Lexer *l) {
    char *end;
    long num = strtol(l->c, &end, 0); // Read out the number
    l->c = end;
    if (isalnum(*l->c)) { // Check the character after the number is valid
        printf("invalid number\n");
        exit(1);
    }
    l->tk = TK_NUM;
    l->num = num;
}

static void lex_symbol(Lexer *l) {
#define X(_)
#define Y(name, ch1, ch2) /* 2-character tokens */     \
    else if (*l->c == (ch1) && *(l->c + 1) == (ch2)) { \
        l->tk = TK_ ## name;                           \
        l->c += 2;                                     \
    }
#define Z(name, ch1, ch2, ch3) /* 3-character tokens */                        \
    else if (*l->c == (ch1) && *(l->c + 1) == (ch2) && *(l->c + 2) == (ch3)) { \
        l->tk = TK_ ## name;                                                   \
        l->c += 2;                                                             \
    }
#define K(_, __)
    if (0) {}
    TOKENS
#undef K
#undef X
#undef Y
#undef Z
    else { // Single character token
        l->tk = (int) *l->c;
        l->c++;
    }
}

void next_tk(Lexer *l) {
    lex_whitespace(l);
    if (isalpha(*l->c) || *l->c == '_') { // Identifiers
        lex_ident(l);
    } else if (isnumber(*l->c)) { // Numbers
        lex_int(l);
    } else { // Symbols
        lex_symbol(l);
    }
}

void expect_tk(Lexer *l, Tk tk) {
    if (l->tk != tk) {
        printf("expected token '%c', found '%c'\n", tk, l->tk);
        exit(1);
    }
}
