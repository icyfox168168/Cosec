
#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <errno.h>

#include "Lexer.h"
#include "Error.h"

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
    if (!l.source) {
        trigger_error("couldn't read file '%s'", file);
    }
    l.c = l.source;
    l.line = 1;
    l.line_str = l.source;
    l.tk = 0;
    l.ident = NULL;
    l.len = 0;
    return l;
}

static TkInfo info_at(Lexer *l) {
    TkInfo info;
    info.file = l->file;
    info.start = l->c;
    info.len = 0;
    info.line = l->line;
    info.col = (int) (l->c - l->line_str) + 1;
    info.line_str = l->line_str;
    return info;
}

static void check_newline(Lexer *l) {
    if (*l->c == '\n' || *l->c == '\r') {
        if (*l->c == '\r' && *(l->c + 1) == '\n') {
            l->c++; // Treat \r\n as a single newline (stupid Windows)
        }
        l->line++;
        l->line_str = l->c + 1; // Next character is start of new line
    }
}

static void lex_whitespace(Lexer *l) {
    while (isspace(*l->c)) {
        check_newline(l);
        l->c++;
    }
}

static void lex_comments(Lexer *l) {
    if (*l->c == '/' && *(l->c + 1) == '/') {
        while (*l->c && *l->c != '\n' && *l->c != '\r') {
            l->c++;
        }
    } else if (*l->c == '/' && *(l->c + 1) == '*') {
        TkInfo info = info_at(l);
        info.len = 2;
        l->c += 2; // Skip initial '/*'
        while (*l->c && !(*l->c == '*' && *(l->c + 1) == '/')) {
            check_newline(l);
            l->c++;
        }
        if (!*l->c) {
            trigger_error_at(info, "unterminated '/*' comment");
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

static void lex_float(Lexer *l) {
    char *end;
    errno = 0;
    double num = strtod(l->c, &end); // Try reading a float
    l->c = end;
    if (errno != 0 || end == l->info.start || isalnum(*l->c)) {
        TkInfo info = info_at(l);
        info.len = 1;
        trigger_error_at(info, "invalid digit '%c' in number", *l->c);
    }
    l->c = end;
    l->tk = TK_KFLOAT;
    l->kfloat = num;
}

static void lex_number(Lexer *l) {
    char *end;
    errno = 0;
    int num = (int) strtol(l->c, &end, 0); // Try reading an integer
    l->c = end;
    if (errno != 0 || end == l->info.start || isalnum(*l->c)) {
        TkInfo info = info_at(l);
        info.len = 1;
        trigger_error_at(info, "invalid digit '%c' in number", *l->c);
    }
    if (*end == '.') { // If the int ends in a '.', then it was a float
        l->c = l->info.start; // Re-start
        lex_float(l);
        return;
    }
    l->c = end;
    l->tk = TK_KINT;
    l->kint = num;
}

static void lex_symbol(Lexer *l) {
    if (0);
#define X(_, __)
#define Y(name, ch1, ch2, _) /* 2-character tokens */  \
    else if (*l->c == (ch1) && *(l->c + 1) == (ch2)) { \
        l->tk = TK_ ## name;                           \
        l->c += 2;                                     \
    }
#define Z(name, ch1, ch2, ch3, _) /* 3-character tokens */                     \
    else if (*l->c == (ch1) && *(l->c + 1) == (ch2) && *(l->c + 2) == (ch3)) { \
        l->tk = TK_ ## name;                                                   \
        l->c += 3;                                                             \
    }
#define K(_, __)
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
    l->info = info_at(l);
    if (isalpha(*l->c) || *l->c == '_') { // Identifier
        lex_ident(l);
    } else if (isnumber(*l->c)) { // Number
        lex_number(l);
    } else { // Symbol
        lex_symbol(l);
    }
    l->info.len = (int) (l->c - l->info.start);
}

static char *TK_NAMES[NUM_TKS] = {
#define X(name, str) [TK_ ## name] = (str),             // Value tokens
#define Y(name, _, __, str) [TK_ ## name] = (str),      // Two characters
#define Z(name, _, __, ___, str) [TK_ ## name] = (str), // Three characters
#define K(name, str) [TK_ ## name] = (str),             // Keywords
    TOKENS
#undef K
#undef Z
#undef Y
#undef X
};

void print_tk(Tk tk) {
    if (tk <= TK_FIRST) {
        printf("'%c'", (char) tk);
    } else if (tk >= TK_IDENT && tk <= TK_KFLOAT) {
        printf("%s", TK_NAMES[tk]); // Don't surround in quotes
    } else {
        printf("'%s'", TK_NAMES[tk]);
    }
}

TkInfo merge_tks(TkInfo start, TkInfo end) {
    if (end.start < start.start) {
        return merge_tks(end, start);
    }
    if (end.start + end.len < start.start + start.len) {
        return start; // 'start' is larger than 'end'
    }
    // Merge up until the end of the line
    char *c = start.start;
    while (*c && *c != '\n' && *c != '\r' && c < (end.start + end.len)) {
        c++;
    }
    start.len = (int) (c - start.start);
    if (*c == '\n' || *c == '\r') {
        start.len++; // Include the newline in the arrow
    }
    return start;
}
