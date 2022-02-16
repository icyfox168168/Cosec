
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Type.h"

static char *PRIM_NAMES[] = {
#define X(type, name) [T_ ## type] = (name),
    IR_PRIMS
#undef X
};

Type type_i1() {
    Type t;
    t.prim = T_i1;
    t.ptrs = 0;
    t.is_signed = 0;
    return t;
}

Type type_none() {
    Type t;
    t.prim = T_NONE;
    t.ptrs = 0;
    t.is_signed = 0;
    return t;
}

Type type_signed_i32() {
    Type t;
    t.prim = T_i32;
    t.ptrs = 0;
    t.is_signed = 1;
    return t;
}

Type type_f32() {
    Type t;
    t.prim = T_f32;
    t.ptrs = 0;
    t.is_signed = 1;
    return t;
}

Type type_unsigned_i64() {
    Type t;
    t.prim = T_i64;
    t.ptrs = 0;
    t.is_signed = 0;
    return t;
}

int is_ptr(Type t) {
    return t.ptrs > 0;
}

int is_void_ptr(Type t) {
    return t.prim == T_void && t.ptrs == 1;
}

int is_arith(Type t) {
    return t.ptrs == 0 && t.prim >= T_i1 && t.prim <= T_f64;
}

int is_int(Type t) {
    return t.ptrs == 0 && t.prim >= T_i1 && t.prim <= T_i64;
}

int is_fp(Type t) {
    return t.ptrs == 0 && t.prim >= T_f32 && t.prim <= T_f64;
}

int are_equal(Type l, Type r) {
    // Right now, for two types to be compatible, they need to be the same
    return l.prim == r.prim && l.ptrs == r.ptrs && l.is_signed == r.is_signed;
}

int bits(Type t) {
    if (t.ptrs > 0) {
        return 64; // Pointers are always 8 bytes
    }
    switch (t.prim) {
        case T_NONE: return -1;
        case T_void: return 0;
        case T_i1:   return 1;
        case T_i8:   return 8;
        case T_i16:  return 16;
        case T_i32:  return 32;
        case T_i64:  return 64;
        case T_f32:  return 32;
        case T_f64:  return 64;
    }
}

int bytes(Type t) {
    // Can't just divide 'bits(t)' by 8, since this wouldn't work for i1
    return (t.prim == T_i1 && t.ptrs == 0) ? 1 : bits(t) / 8;
}

char * print_type(Type t) {
    char *prim = PRIM_NAMES[t.prim];
    size_t len = strlen(prim) + t.ptrs + 1;
    char *str = malloc(sizeof(char) * len + 1);
    strcpy(str, prim);
    size_t pos = strlen(prim);
    if (t.ptrs >= 1) {
        str[pos++] = ' ';
    }
    for (int i = 0; i < t.ptrs; i++) {
        str[pos++] = '*';
    }
    str[pos] = '\0';
    return str;
}