
#include <ctype.h>
#include <string.h>
#include <stdio.h>

#include "Lexer.h"

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
    int len = (int) (l->c - start);
    for (int i = 0; KEYWORDS[i]; i++) { // Check identifier isn't a keyword
        if (strlen(KEYWORDS[i]) == len && strncmp(KEYWORDS[i], start, len) == 0) {
            l->tk = i + FIRST_KEYWORD;
            return;
        }
    }
    l->tk = TK_IDENT;
    l->ident = start;
    l->len = len;
}

static void lex_int(Lexer *l) {
    char *end;
    long num = strtol(l->c, &end, 0);
    l->c = end;
    if (isalnum(*l->c)) {
        printf("invalid number\n");
        exit(1);
    }
    l->tk = TK_NUM;
    l->num = num;
}

static void lex_symbol(Lexer *l) {
#define X(_)
#define Y(name, ch1, ch2) \
    else if (*l->c == (ch1) && *(l->c + 1) == (ch2)) { l->tk = TK_ ## name; l->c += 2; }
#define Z(name, ch1, ch2, ch3) \
    else if (*l->c == (ch1) && *(l->c + 1) == (ch2) && *(l->c + 2) == (ch3)) { l->tk = TK_ ## name; l->c += 2; }
#define K(_, __)
    if (0) {}
    TOKENS
#undef K
#undef X
#undef Y
#undef Z
    else { l->tk = (int) *l->c; l->c++; }
}

void next_tk(Lexer *l) {
    lex_whitespace(l);
    if (isalpha(*l->c) || *l->c == '_') {
        lex_ident(l);
    } else if (isnumber(*l->c)) {
        lex_int(l);
    } else {
        lex_symbol(l);
    }
}

void expect_tk(Lexer *l, Token tk) {
    if (l->tk != tk) {
        printf("expected token '%c', found '%c'\n", tk, l->tk);
        exit(1);
    }
}
