
#ifndef COSEC_LEXER_H
#define COSEC_LEXER_H

#include <stdlib.h>

#define FIRST_KEYWORD TK_VOID
#define TOKENS                             \
    /* Values */                           \
    X(IDENT, "identifier")                 \
    X(KINT, "integer")                     \
    X(KFLOAT, "number")                    \
    X(KCHAR, "character literal")          \
    X(KSTR, "string literal")              \
                                           \
    /* Symbols */                          \
    Y(INC, '+', '+', "++")                 \
    Y(DEC, '-', '-', "--")                 \
    Y(EQ, '=', '=', "==")                  \
    Y(NEQ, '!', '=', "!=")                 \
    Y(LE, '<', '=', "<=")                  \
    Y(GE, '>', '=', ">=")                  \
    Y(AND, '&', '&', "&&")                 \
    Y(OR, '|', '|', "||")                  \
    Y(LSHIFT, '<', '<', "<<")              \
    Y(RSHIFT, '>', '>', ">>")              \
    Y(ADD_ASSIGN, '+', '=', "+=")          \
    Y(SUB_ASSIGN, '-', '=', "-=")          \
    Y(MUL_ASSIGN, '*', '=', "*=")          \
    Y(DIV_ASSIGN, '/', '=', "/=")          \
    Y(MOD_ASSIGN, '%', '=', "%=")          \
    Y(AND_ASSIGN, '&', '=', "&=")          \
    Y(OR_ASSIGN, '|', '=', "|=")           \
    Y(XOR_ASSIGN, '^', '=', "^=")          \
    Z(LSHIFT_ASSIGN, '<', '<', '=', "<<=") \
    Z(RSHIFT_ASSIGN, '>', '>', '=', ">>=") \
                                           \
    /* Keywords */                         \
    /* All keyword tokens must be together! */ \
    K(VOID, "void")                        \
    K(CHAR, "char")                        \
    K(SHORT, "short")                      \
    K(INT, "int")                          \
    K(LONG, "long")                        \
    K(FLOAT, "float")                      \
    K(DOUBLE, "double")                    \
    K(SIGNED, "signed")                    \
    K(UNSIGNED, "unsigned")                \
    K(IF, "if")                            \
    K(ELSE, "else")                        \
    K(WHILE, "while")                      \
    K(FOR, "for")                          \
    K(DO, "do")                            \
    K(BREAK, "break")                      \
    K(CONTINUE, "continue")                \
    K(RETURN, "return")                    \
    K(SIZEOF, "sizeof")

typedef int Tk;
enum {
    TK_FIRST = 0xFF, // The first 255 tokens are ASCII characters
#define X(name, _) TK_ ## name,                // Value tokens
#define Y(name, _, __, ___) TK_ ## name,       // Two character symbols
#define Z(name, _, __, ___, ____) TK_ ## name, // Three character symbols
#define K(name, _) TK_ ## name,                // Keywords
    TOKENS
#undef K
#undef Z
#undef Y
#undef X
    NUM_TKS, // Required for hash-maps indexed by tokens
};

typedef struct token {
    struct token *next, *prev;
    char *file;
    Tk t;
    char *start;
    size_t len;
    int line, col;
    char *line_str;
    union {
        uint64_t kint; // For TK_KINT
        double kfloat; // For TK_KFLOAT
        char kch;      // For TK_KCHAR
        char *kstr;    // For TK_KSTR
    };
} Token;

Token * lex_file(char *file);

void print_simple_tk(Tk t);
void print_tk(Token *tk);
Token * merge_tks(Token *start, Token *end);

#endif
