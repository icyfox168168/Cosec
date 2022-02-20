
#ifndef COSEC_TYPE_H
#define COSEC_TYPE_H

#define UNREACHABLE() assert(0)

// We steal the great idea from LLVM to merge signed and unsigned integer
// types for simplicity, the rationale being that all we really care about is
// the size of the data, not it's underlying representation. We make the
// signed/unsigned distinction in the IR instructions instead (e.g., SDIV vs.
// UDIV).
//
// For more information, see this LLVM enhancement request:
//   https://bugs.llvm.org/show_bug.cgi?id=950
#define IR_PRIMS                     \
    X(void, "void")                  \
    X(i1, "int") /* Boolean value */ \
    X(i8, "char")                    \
    X(i16, "short")                  \
    X(i32, "int")                    \
    X(i64, "long long")              \
    X(f32, "float")                  \
    X(f64, "double")

typedef enum {
#define X(name, _) T_ ## name,
    IR_PRIMS
#undef X
} Prim;

typedef enum {
    T_PRIM,
    T_PTR,
} Kind;

typedef struct type {
    Kind kind;
    int is_signed;
    union {
        Prim prim;
        struct type *ptr;
    };
} Type;

Type * t_prim(Prim prim, int is_signed);
Type * t_ptr(Type *deref);
Type * t_copy(Type *t);
int bits(Type *t);  // Returns the size of a type in bits
int bytes(Type *t); // Returns the size of a type in bytes

int is_ptr(Type *t);
int is_void_ptr(Type *t);
int is_arith(Type *t);
int is_int(Type *t);
int is_fp(Type *t);
int are_equal(Type *l, Type *r);

char * type_to_str(Type *t);

#endif
