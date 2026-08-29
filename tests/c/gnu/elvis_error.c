//@ mode: c
//@ compile-fail

typedef struct { int x; } S;
struct A { int x; };
struct B { int x; };

int test_struct_cond(void) {
    S s = {0};
    return s ?: 1;
         //^ error: condition must be scalar-like, got S
}

int test_incompatible_struct_ptr(void) {
    struct A *pa = 0;
    struct B *pb = 0;
    return pa ?: pb;
         //^^^^^^^^ error: ternary operator branches have mismatched types: expected *mut co2(struct A), got *mut co2(struct B)
}

int test_incompatible_ptr_int_float(void) {
    int *pi = 0;
    float *pf = 0;
    return pi ?: pf;
         //^^^^^^^^ error: ternary operator branches have mismatched types: expected *mut i32, got *mut f32
}

int test_struct_vs_int(void) {
    struct A a = {0};
    int b = 0;
    return b ?: a;
         //^^^^^^ error: ternary operator branches have mismatched types: expected i32, got co2(struct A)
}
