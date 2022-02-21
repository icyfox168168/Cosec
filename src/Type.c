
#include <stdlib.h>
#include <string.h>

#include "Type.h"

static char *PRIM_NAMES[] = {
#define X(type, name) [T_ ## type] = (name),
    IR_PRIMS
#undef X
};

Type * t_prim(Prim prim, int is_signed) {
    Type *t = malloc(sizeof(Type));
    t->kind = T_PRIM;
    t->prim = prim;
    t->is_signed = is_signed;
    return t;
}

Type * t_ptr(Type *deref) {
    Type *t = malloc(sizeof(Type));
    t->kind = T_PTR;
    t->ptr = deref;
    t->is_signed = 0; // Pointers are never signed
    return t;
}

Type * t_copy(Type *t) {
    Type *copy = malloc(sizeof(Type));
    switch (t->kind) {
    case T_PRIM:
        copy->kind = T_PRIM;
        copy->prim = t->prim;
        copy->is_signed = t->is_signed;
        break;
    case T_PTR:
        copy->kind = T_PTR;
        copy->ptr = t_copy(t->ptr);
        break;
    }
    return copy;
}

int is_ptr(Type *t) {
    return t->kind == T_PTR;
}

int is_void_ptr(Type *t) {
    return t->kind == T_PTR && t->ptr->kind == T_PRIM && t->ptr->prim == T_void;
}

int is_arith(Type *t) {
    return t->kind == T_PRIM && t->prim >= T_i1 && t->prim <= T_f64;
}

int is_int(Type *t) {
    return t->kind == T_PRIM && t->prim >= T_i1 && t->prim <= T_i64;
}

int is_fp(Type *t) {
    return t->kind == T_PRIM && (t->prim == T_f32 || t->prim == T_f64);
}

int are_equal(Type *l, Type *r) {
    if (l->kind != r->kind) {
        return 0;
    }
    switch (l->kind) {
        case T_PRIM: return l->prim == r->prim && l->is_signed == r->is_signed;
        case T_PTR:  return are_equal(l->ptr, r->ptr);
    }
}

int bits(Type *t) {
    switch (t->kind) {
    case T_PTR: return 64; // Always 8 bytes
    case T_PRIM:
        switch (t->prim) {
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
}

int bytes(Type *t) {
    // Can't just divide 'bits(t)' by 8, since this wouldn't work for i1
    return (t->kind == T_PRIM && t->prim == T_i1) ? 1 : bits(t) / 8;
}

#define MAX_TYPE_STR_LEN 100

static void write_type_to_str(Type *t, char *str, size_t *len) {
    switch (t->kind) {
    case T_PTR:
        write_type_to_str(t->ptr, str, len);
        if (t->ptr->kind == T_PRIM) {
            str[(*len)++] = ' '; // Space after primitive
        }
        str[(*len)++] = '*';
        break;
    case T_PRIM:
        if (!t->is_signed) {
            strcpy(&str[*len], "unsigned ");
            *len += strlen("unsigned ");
        }
        strcpy(&str[*len], PRIM_NAMES[t->prim]);
        *len += strlen(PRIM_NAMES[t->prim]);
        break;
    }
}

char * type_to_str(Type *t) {
    size_t len = 0;
    char *str = malloc(sizeof(char) * MAX_TYPE_STR_LEN);
    write_type_to_str(t, str, &len);
    str[len] = '\0';
    return str;
}