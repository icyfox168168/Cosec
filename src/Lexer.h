
#ifndef COSEC_LEXER_H
#define COSEC_LEXER_H

#include <stdlib.h>

// All the keywords must be together at the end
#define TOKENS          \
    X(IDENT)            \
    X(NUM)              \
    K(INT, "int")       \
    K(RETURN, "return")
#define FIRST_KEYWORD TK_INT

typedef int Token;
enum {
    TK_FIRST = 0xFF, // Marker
#define X(name) TK_ ## name,
#define K(name, keyword) TK_ ## name,
    TOKENS
#undef K
#undef X
    TK_LAST, // Marker
};

static char *KEYWORDS[] = {
#define X(name)
#define K(name, keyword) keyword,
    TOKENS
#undef K
#undef X
    NULL, // Marker
};

typedef struct {
    char *source; // Source code we're lexing
    char *c;
    Token tk; // Most recently lexed token
    char *ident; int len; // Start and length of an identifier in the source code
    long num; // Number converted to an integer
} Lexer;

Lexer new_lexer(char *source);
void next_tk(Lexer *l);
void expect_tk(Lexer *l, Token tk);

#endif
