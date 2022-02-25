
#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <errno.h>
#include <limits.h>

#include "Lexer.h"
#include "Error.h"

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

typedef struct {
    char *file, *source, *c; // Character in 'source' that we're up to
    int line;
    char *line_str;
} Lexer;

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
    return l;
}

static Token * cur_tk(Lexer *l, size_t len) {
    Token *tk = malloc(sizeof(Token));
    tk->next = NULL;
    tk->prev = NULL;
    tk->file = l->file;
    tk->start = l->c;
    tk->len = len;
    tk->line = l->line;
    tk->col = (int) (l->c - l->line_str) + 1;
    tk->line_str = l->line_str;
    tk->kint = 0;
    return tk;
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
        Token *err = cur_tk(l, 2);
        l->c += 2; // Skip initial '/*'
        while (*l->c && !(*l->c == '*' && *(l->c + 1) == '/')) {
            check_newline(l);
            l->c++;
        }
        if (!*l->c) {
            trigger_error_at(err, "unterminated '/*' comment");
        }
        l->c += 2; // Skip final '*/'
    }
}

static Token * lex_ident(Lexer *l) {
    Token *tk = cur_tk(l, 0);
    while (isalnum(*l->c) || *l->c == '_') { // Find the end of the identifier
        l->c++;
    }
    tk->len = l->c - tk->start; // Length of the identifier
    for (int i = 0; KEYWORDS[i]; i++) { // Check identifier isn't a keyword
        char *k = KEYWORDS[i];
        if (strlen(k) == tk->len && strncmp(k, tk->start, tk->len) == 0) {
            tk->t = FIRST_KEYWORD + i;
            return tk;
        }
    }
    tk->t = TK_IDENT;
    return tk;
}

static Token * lex_float(Lexer *l) {
    Token *tk = cur_tk(l, 0);
    char *end;
    errno = 0;
    double num = strtod(l->c, &end); // Try reading a float
    l->c = end;
    if (errno != 0 || end == tk->start || isalnum(*l->c)) {
        Token *err = cur_tk(l, 1);
        trigger_error_at(err, "invalid digit '%c' in number", *l->c);
    }
    tk->t = TK_KFLOAT;
    tk->len = l->c - tk->start;
    tk->kfloat = num;
    return tk;
}

static Token * lex_number(Lexer *l) {
    Token *tk = cur_tk(l, 0);
    char *end;
    errno = 0;
    uint64_t num = strtoull(l->c, &end, 0); // Try reading an integer
    l->c = end;
    tk->len = l->c - tk->start;
    if (errno != 0) {
        trigger_error_at(tk, "number out of range");
    }
    if (end == tk->start || isalnum(*l->c)) {
        Token *err = cur_tk(l, 1);
        trigger_error_at(err, "invalid digit '%c' in number", *l->c);
    }
    if (*end == '.') { // If the int ends in a '.', then it was a float
        l->c = tk->start; // Re-start
        return lex_float(l);
    }
    tk->t = TK_KINT;
    tk->kint = num;
    return tk;
}

static char SIMPLE_ESC_SEQS[UCHAR_MAX] = {
    ['\''] = '\'',
    ['"']  = '"',
    ['?']  = '?',
    ['\\'] = '\\',
    ['a']  = '\a',
    ['b']  = '\b',
    ['f']  = '\f',
    ['n']  = '\n',
    ['r']  = '\r',
    ['t']  = '\t',
    ['v']  = '\v',
};

static char lex_numeric_esc_seq(Lexer *l, int base) {
    char *end;
    long num = strtol(l->c, &end, base);
    Token *err = cur_tk(l, 1);
    err->len = end - l->c;
    if (err->len == 0) {
        trigger_error_at(err, "missing hex escape sequence");
    } else if (num > UCHAR_MAX) {
        trigger_error_at(err, "escape sequence out of range");
    }
    l->c = end;
    return (char) num;
}

static char lex_esc_seq(Lexer *l) {
    Token *err = cur_tk(l, 2);
    l->c++; // Skip '\'
    char c = *l->c;
    if (SIMPLE_ESC_SEQS[(int) c]) {
        l->c++;
        return SIMPLE_ESC_SEQS[(int) c];
    } else if (c >= '0' && c <= '7') {
        return lex_numeric_esc_seq(l, 8);
    } else if (c == 'x' || c == 'X') {
        l->c++; // Skip the 'x'
        return lex_numeric_esc_seq(l, 16);
    } else {
        trigger_error_at(err, "unknown escape sequence");
    }
}

static Token * lex_char(Lexer *l) {
    Token *tk = cur_tk(l, 1);
    l->c++; // Skip opening quote
    char c = *l->c;
    if (c == '\n' || c == '\r') {
        trigger_error_at(tk, "invalid character literal");
    } else if (c == '\'') {
        tk->len = 2;
        trigger_error_at(tk, "empty character literal");
    } else if (c == '\\') {
        tk->kch = lex_esc_seq(l);
    } else {
        tk->kch = c;
        l->c++;
    }
    if (*l->c++ != '\'') { // Skip terminating quote
        Token *err = cur_tk(l, 1);
        trigger_error_at(err, "expected terminating '");
    }
    tk->t = TK_KCHAR;
    tk->len = l->c - tk->start;
    return tk;
}

static Token * lex_str(Lexer *l) {
    Token *tk = cur_tk(l, 0);
    l->c++; // Skip opening quote

    // Find the end of the string, to get an upper limit on the number of
    // characters to malloc
    char *end = l->c;
    while (*end && !(*end == '"' && *(end - 1) != '\\')) { end++; }
    size_t max_len = end - l->c;

    char *str = malloc((max_len + 1) * sizeof(char));
    size_t len = 0;
    while (*l->c && !(*l->c == '"' && *(l->c - 1) != '\\')) {
        char c = *l->c;
        if (c == '\n' || c == '\r') { // Can't be a newline
            Token *err = cur_tk(l, 1);
            trigger_error_at(err, "string cannot contain newlines");
        } else if (c == '\\') { // Escape sequence
            c = lex_esc_seq(l);
        } else { // Normal character
            l->c++;
        }
        str[len++] = c;
    }
    str[len] = '\0';

    if (*l->c++ != '"') { // Skip closing quote
        Token *err = cur_tk(l, 1);
        trigger_error_at(err, "expected terminating \"");
    }
    tk->t = TK_KSTR;
    tk->len = l->c - tk->start;
    tk->kstr = str;
    return tk;
}

static Token * lex_symbol(Lexer *l) {
    Token *tk = cur_tk(l, 1);
    if (0);
#define X(_, __)
#define Y(name, ch1, ch2, _) /* 2-character tokens */  \
    else if (*l->c == (ch1) && *(l->c + 1) == (ch2)) { \
        tk->t = TK_ ## name;                           \
        l->c += 2;                                     \
    }
#define Z(name, ch1, ch2, ch3, _) /* 3-character tokens */                     \
    else if (*l->c == (ch1) && *(l->c + 1) == (ch2) && *(l->c + 2) == (ch3)) { \
        tk->t = TK_ ## name;                                                   \
        l->c += 3;                                                             \
    }
#define K(_, __)
    TOKENS
#undef K
#undef X
#undef Y
#undef Z
    else { // Single character token
        tk->t = (int) *l->c;
        l->c++;
    }
    tk->len = l->c - tk->start;
    return tk;
}

static Token * next_tk(Lexer *l) {
    lex_whitespace(l);
    lex_comments(l);
    lex_whitespace(l);
    if (*l->c == '\0') { // End of file
        Token *tk = cur_tk(l, 0);
        tk->t = '\0';
        return tk;
    } else if (isalpha(*l->c) || *l->c == '_') { // Identifier
        return lex_ident(l);
    } else if (isnumber(*l->c)) { // Number
        return lex_number(l);
    } else if (*l->c == '\'') { // Character
        return lex_char(l);
    } else if (*l->c == '"') { // String
        return lex_str(l);
    } else { // Symbol
        return lex_symbol(l);
    }
}

Token * lex_file(char *file) {
    Lexer l = new_lexer(file);
    Token *tk = next_tk(&l);
    Token *head = tk;
    Token *last = tk;
    while (tk->t != '\0') { // Create a bidirectional linked list of tokens
        tk->prev = last;
        last->next = tk;
        last = tk;
        tk = next_tk(&l);
    }
    last->next = tk; // Add the EOF token
    return head;
}

void print_simple_tk(Tk tk) {
    if (tk <= TK_FIRST) {
        printf("'%c'", (char) tk);
    } else if (tk >= TK_IDENT && tk <= TK_KFLOAT) {
        printf("%s", TK_NAMES[tk]); // Don't surround in quotes
    } else {
        printf("'%s'", TK_NAMES[tk]);
    }
}

void print_tk(Token *tk) {
    print_simple_tk(tk->t);
    switch (tk->t) {
        case TK_IDENT:  printf(" '%.*s'", (int) tk->len, tk->start); break;
        case TK_KINT:   printf(" '%lli'", tk->kint); break;
        case TK_KFLOAT: printf(" '%g'", tk->kfloat); break;
        case TK_KCHAR: case TK_KSTR:
            printf(" %.*s", (int) tk->len, tk->start); break;
        default: break; // Don't print others
    }
}

Token * merge_tks(Token *start, Token *end) {
    if (end->start < start->start) {
        return merge_tks(end, start);
    }
    Token *merged = malloc(sizeof(Token));
    *merged = *start;
    merged->next = NULL;
    merged->prev = NULL;
    if (end->start + end->len < start->start + start->len) {
        return merged; // 'start' is larger than 'end'
    }

    // Merge up until the end of the line
    char *c = start->start;
    while (*c && *c != '\n' && *c != '\r' && c < (end->start + end->len)) {
        c++;
    }
    merged->len = c - start->start;
    if (*c == '\n' || *c == '\r') {
        merged->len++; // Include the newline in the arrow
    }
    return merged;
}
