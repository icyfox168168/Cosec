
#ifndef COSEC_LEXER_H
#define COSEC_LEXER_H

#include <stdlib.h>

// All the keywords must be together at the end
#define TOKENS                      \
    X(IDENT)                        \
    X(NUM)                          \
    Y(EQ, '=', '=')                 \
    Y(NEQ, '!', '=')                \
    Y(LE, '<', '=')                 \
    Y(GE, '>', '=')                 \
    Y(LSHIFT, '<', '<')             \
    Y(RSHIFT, '>', '>')             \
    Y(ADD_ASSIGN, '+', '=')         \
    Y(SUB_ASSIGN, '-', '=')         \
    Y(MUL_ASSIGN, '*', '=')         \
    Y(DIV_ASSIGN, '/', '=')         \
    Y(MOD_ASSIGN, '%', '=')         \
    Y(AND_ASSIGN, '&', '=')         \
    Y(OR_ASSIGN, '|', '=')          \
    Y(XOR_ASSIGN, '^', '=')         \
    Z(LSHIFT_ASSIGN, '<', '<', '=') \
    Z(RSHIFT_ASSIGN, '>', '>', '=') \
    K(INT, "int")                   \
    K(IF, "if")                     \
    K(RETURN, "return")
#define FIRST_KEYWORD TK_INT

typedef int Token;
enum {
    TK_FIRST = 0xFF, // Marker
#define X(name) TK_ ## name,
#define Y(name, _, __) TK_ ## name,
#define Z(name, _, __, ___) TK_ ## name,
#define K(name, _) TK_ ## name,
    TOKENS
#undef K
#undef Z
#undef Y
#undef X
    TK_LAST, // Marker
};

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
