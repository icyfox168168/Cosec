
#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <assert.h>

#include "Lexer.h"

// Allows us to map between the KEYWORDS array and the Tk type
#define FIRST_KEYWORD TK_CHAR

static char *KEYWORDS[] = {
#define X(_, __)
#define Y(_, __, ___, ____)
#define Z(_, __, ___, ____, _____)
#define K(_, keyword) keyword,
    TOKENS
#undef K
#undef Z
#undef Y
#undef X
    NULL, // Marker for the end of the KEYWORDS array
};

static char * read_file(char *path) {
    FILE *f = fopen(path, "r");
    if (!f) {
        return NULL;
    }
    fseek(f, 0, SEEK_END); // Get length
    size_t length = (size_t) ftell(f);
    rewind(f);
    char *source = malloc(sizeof(char) * (length + 1)); // Read file
    fread(source, sizeof(char), length, f);
    fclose(f);
    source[length] = '\0';
    return source;
}

Lexer new_lexer(char *file) {
    Lexer l;
    l.file = file;
    l.source = read_file(file);
    assert(l.source != NULL);
    l.c = l.source;
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

static void lex_comments(Lexer *l) {
    if (*l->c == '/' && *(l->c + 1) == '/') {
        while (*l->c != 0 && *l->c != '\n' && *l->c != '\r') {
            l->c++;
        }
    } else if (*l->c == '/' && *(l->c + 1) == '*') {
        while (*l->c != 0 && *l->c != '*' && *(l->c + 1) != '/') {
            l->c++;
        }
        if (!l->c) {
            printf("unclosed multiline comment\n");
            exit(1);
        }
        l->c += 2; // Skip final '*/'
    }
    lex_whitespace(l);
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
    int num = (int) strtol(l->c, &end, 0); // Read the number
    l->c = end;
    if (isalnum(*l->c)) { // Check the character after the number is valid
        printf("invalid number\n");
        exit(1);
    }
    l->tk = TK_NUM;
    l->num =  num;
}

static void lex_symbol(Lexer *l) {
#define X(_, __)
#define Y(name, ch1, ch2, _) /* 2-character tokens */  \
    else if (*l->c == (ch1) && *(l->c + 1) == (ch2)) { \
        l->tk = TK_ ## name;                           \
        l->c += 2;                                     \
    }
#define Z(name, ch1, ch2, ch3, _) /* 3-character tokens */                     \
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
    lex_comments(l);
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
        printf("expected token '%d', found '%d'\n", tk, l->tk);
        exit(1);
    }
}
