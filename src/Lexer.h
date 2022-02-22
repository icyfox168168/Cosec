
#ifndef COSEC_LEXER_H
#define COSEC_LEXER_H

#include <stdlib.h>

#define FIRST_KEYWORD TK_VOID
#define TOKENS                             \
    /* Values */                           \
    X(IDENT, "identifier")                 \
    X(KINT, "integer")                     \
    X(KFLOAT, "number")                    \
    X(KCHAR, "character")                  \
    X(KSTR, "string")                      \
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

typedef struct {
    char *file;
    char *start;
    int len;
    int line, col;
    char *line_str;
} TkInfo;

typedef struct {
    char *file, *source;
    char *c; // Character in 'source' that we're up to
    int line;
    char *line_str;
    TkInfo info; // Information about the most recently lexed token

    Tk tk; // Most recently lexed token
    char *ident; int len; // For TK_IDENT
    uint64_t kint;        // For TK_KINT
    double kfloat;        // For TK_KFLOAT
    char kch;             // For TK_KCHAR
    char *kstr;           // For TK_KSTR
} Lexer;

Lexer new_lexer(char *file);
void next_tk(Lexer *l);
void print_tk(Tk tk);
TkInfo merge_tks(TkInfo start, TkInfo end);

#endif
