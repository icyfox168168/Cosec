
#ifndef COSEC_LEXER_H
#define COSEC_LEXER_H

#include <stdlib.h>

#define TOKENS                      \
    /* Values */                    \
    X(IDENT)                        \
    X(NUM)                          \
                                    \
    /* Symbols */                   \
    Y(EQ, '=', '=')                 \
    Y(NEQ, '!', '=')                \
    Y(LE, '<', '=')                 \
    Y(GE, '>', '=')                 \
    Y(AND, '&', '&')                \
    Y(OR, '|', '|')                 \
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
                                    \
    /* Keywords */                  \
    /* All keyword tokens must be together! */ \
    K(INT, "int")                   \
    K(IF, "if")                     \
    K(RETURN, "return")

typedef int Tk;
enum {
    TK_FIRST = 0xFF, // The first 255 tokens are ASCII characters
#define X(name) TK_ ## name,             // Value tokens
#define Y(name, _, __) TK_ ## name,      // Two character symbols
#define Z(name, _, __, ___) TK_ ## name, // Three character symbols
#define K(name, _) TK_ ## name,          // Keywords
    TOKENS
#undef K
#undef Z
#undef Y
#undef X
    TK_LAST, // Required for hash-maps indexed by tokens
};

typedef struct {
    char *source;         // Source code we're lexing
    char *c;              // Character in 'source' that we're up to
    Tk tk;                // Most recently lexed token
    char *ident; int len; // Start and length of an identifier
    long num;             // Number that's been converted to an integer
} Lexer;

Lexer new_lexer(char *source);      // Create a new lexer object
void next_tk(Lexer *l);             // Lex the next token
void expect_tk(Lexer *l, Tk tk); // Make sure the current token is 'tk'

#endif
