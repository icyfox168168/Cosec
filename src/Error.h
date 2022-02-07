
#ifndef COSEC_ERROR_H
#define COSEC_ERROR_H

#include "Lexer.h"

// ERROR -- prints colourful error and warning messages to stdout.

void trigger_error(char *fmt, ...) __attribute__((noreturn));
void trigger_error_at(TkInfo at, char *fmt, ...) __attribute__((noreturn));
void trigger_warning_at(TkInfo at, char *fmt, ...);
void expect_tk(Lexer *l, Tk expected);

#endif
