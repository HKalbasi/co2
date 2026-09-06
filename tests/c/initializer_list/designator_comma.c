//@ mode: c
//@ compile-fail

struct S {
    int a[4];
};

void f() {
    // This is rejected by gcc, so we should reject too. But maybe with better message.
    struct S s = (struct S){[1, 2] = 7};
                           //^ error: unsupported binary op in array size
}
