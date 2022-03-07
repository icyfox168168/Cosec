
#ifndef COSEC_ERROR_H
#define COSEC_ERROR_H

#include "Lexer.h"

void print_error(char *fmt, ...);
void print_error_at(Token *tk, char *fmt, ...);
void print_warning_at(Token *tk, char *fmt, ...);
void print_info_at(Token *tk, char *fmt, ...);
void trigger_error() __attribute__((noreturn));;
void expect_tk(Token *tk, Tk expected);

#endif
