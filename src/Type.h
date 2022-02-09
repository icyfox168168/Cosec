
#ifndef COSEC_TYPE_H
#define COSEC_TYPE_H

#define UNREACHABLE() exit(1)

// We steal the great idea from LLVM to merge signed and unsigned integer
// types for simplicity, the rationale being that all we really care about is
// the size of the data, not it's underlying representation. We make the
// signed/unsigned distinction in the IR instructions instead.
//
// For more information, see this LLVM enhancement request:
//   https://bugs.llvm.org/show_bug.cgi?id=950
#define IR_PRIMS \
    X(NONE)      \
    X(void)      \
    X(i1)  /* Boolean value */ \
    X(i8)  /* Integers */ \
    X(i16)       \
    X(i32)       \
    X(i64)       \
    X(f32) /* Float */ \
    X(f64) /* Double */

typedef enum {
#define X(name) T_ ## name,
    IR_PRIMS
#undef X
} Prim;

typedef struct {
    Prim prim;
    int ptrs;      // Number of levels of pointer indirection
    int is_signed; // For the AST; NOT used by the SSA IR!
} Type;

Type type_none();
Type type_i1();
Type type_signed_i32();
Type type_unsigned_i64();
Type type_f32();
int bits(Type t);  // Returns the size of a type in bits
int bytes(Type t); // Returns the size of a type in bytes

int is_ptr(Type t);
int is_void_ptr(Type t);
int is_arith(Type t);
int is_int(Type t);
int is_fp(Type t);
int are_equal(Type l, Type r);

#endif
