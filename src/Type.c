
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>

#include "Type.h"
#include "Parser.h"

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

Type * t_arr(Type *elem, uint64_t size) {
    Type *t = malloc(sizeof(Type));
    t->kind = T_ARR;
    t->elem = elem;
    t->size = size;
    t->is_signed = 0; // Pointers/arrays are never signed
    return t;
}

Type * t_fn(Type *ret, struct local **args, int nargs) {
    Type *t = malloc(sizeof(Type));
    t->kind = T_FN;
    t->ret = ret;
    t->args = args;
    t->nargs = nargs;
    return t;
}

Type * t_copy(Type *t) {
    switch (t->kind) {
    case T_PRIM: return t_prim(t->prim, t->is_signed);
    case T_PTR:  return t_ptr(t_copy(t->ptr));
    case T_ARR:  return t_arr(t_copy(t->elem), t->size);
    case T_FN: {
        Local **args = NULL;
        if (t->nargs > 0) {
            args = malloc(sizeof(Type *) * t->nargs);
            for (int i = 0; i < t->nargs; i++) {
                args[i] = t->args[i];
            }
        }
        return t_fn(t_copy(t->ret), args, t->nargs);
    }
    }
}

int is_ptr(Type *t) {
    return t->kind == T_PTR;
}

int is_void_ptr(Type *t) {
    return t->kind == T_PTR && t->ptr->kind == T_PRIM && t->ptr->prim == T_void;
}

int is_arr(Type *t) {
    return t->kind == T_ARR;
}

int is_ptr_arr(Type *t) {
    return t->kind == T_PTR || t->kind == T_ARR;
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

int is_fn(Type *t) {
    return t->kind == T_FN;
}

int are_equal(Type *l, Type *r) {
    if (l->kind != r->kind) {
        return 0;
    }
    switch (l->kind) {
    case T_PRIM: return l->prim == r->prim && l->is_signed == r->is_signed;
    case T_PTR:  return are_equal(l->ptr, r->ptr);
    case T_ARR:  return are_equal(l->elem, r->elem) && l->size == r->size;
    case T_FN: {
        if (l->nargs != r->nargs || !are_equal(l->ret, r->ret)) {
            return 0;
        }
        for (int i = 0; i < l->nargs; i++) {
            if (!are_equal(l->args[i]->decl.type, r->args[i]->decl.type)) {
                return 0;
            }
            // TODO: warning if the argument names are different
        }
        return 1;
    }
    }
}

int is_incomplete(Type *t) {
    // 'void' is the only incomplete type at the moment
    return t->kind == T_PRIM && t->prim == T_void;
}

Type * to_ptr(Type *t) {
    if (t->kind == T_PTR) {
        return t_copy(t);
    } else if (t->kind == T_ARR) {
        Type *copy = t_copy(t);
        copy->kind = T_PTR;
        return copy;
    } else {
        UNREACHABLE();
    }
}

int bits(Type *t) {
    switch (t->kind) {
    case T_PTR: case T_FN: return 64; // Always 8 bytes
    case T_ARR: return (int) t->size * bits(t->elem); // TODO: don't cast int
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

int alignment(Type *t) {
    if (bytes(t) > 16) { // All aggregate types >16 bytes are aligned 16 bytes
        return 16;
    } else {
        return bytes(t); // Otherwise, types should be aligned to their size
    }
}

#define MAX_TYPE_STR_LEN 300

static void write_prim(Type *t, char **str) {
    Type *inner = t;
    while (inner->kind != T_PRIM) {
        inner = inner->ptr;
    }
    if (!inner->is_signed) {
        *str += sprintf(*str, "unsigned ");
    }
    *str += sprintf(*str, "%s", PRIM_NAMES[inner->prim]);
    if (t->kind != T_PRIM) {
        *((*str)++) = ' ';
    }
}

static void write_ptrs_arrays_fns(Type *t, char **str) {
    switch (t->kind) {
    case T_PTR:
        *((*str)++) = '*';
        write_ptrs_arrays_fns(t->ptr, str);
        break;
    case T_ARR:
        if (t->elem->kind == T_PTR) {
            *((*str)++) = '(';
        }
        write_ptrs_arrays_fns(t->elem, str);
        if (t->elem->kind == T_PTR) {
            *((*str)++) = ')';
        }
        *str += sprintf(*str, "[%llu]", t->size);
        break;
    case T_FN:
        write_ptrs_arrays_fns(t->ret, str);
        *((*str)++) = '(';
        for (int i = 0; i < t->nargs; i++) {
            Type *arg_type = t->args[i]->decl.type;
            write_prim(arg_type, str);
            write_ptrs_arrays_fns(arg_type, str);
            if (i < t->nargs - 1) {
                *str += sprintf(*str, ", ");
            }
        }
        *((*str)++) = ')';
    case T_PRIM: break;
    }
}

char * type_to_str(Type *t) {
    // TODO: count length of string first and alloc that
    char *str = malloc(sizeof(char) * MAX_TYPE_STR_LEN);
    char *start = str;
    write_prim(t, &str);
    write_ptrs_arrays_fns(t, &str);
    *str = '\0';
    return start;
}