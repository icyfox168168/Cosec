
#ifndef COSEC_ERROR_H
#define COSEC_ERROR_H

#include "Lexer.h"

// ERROR -- prints colourful error and warning messages to stdout.

void trigger_error(char *fmt, ...) __attribute__((noreturn));
void trigger_error_at(Token *tk, char *fmt, ...) __attribute__((noreturn));
void trigger_warning_at(Token *tk, char *fmt, ...);
void expect_tk(Token *tk, Tk expected);

#endif
