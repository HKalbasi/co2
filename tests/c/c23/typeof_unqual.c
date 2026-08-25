//@ mode: c
//@ run-status: 0

#include <stddef.h>
#include <assert.h>

int sidefx_counter = 0;

int sidefx(void) {
    sidefx_counter++;
    return 1;
}

int func(double x) {
    return (int)x;
}

typedef int arr4_t[4];
typedef const int const_arr4_t[4];   // array of const int

int main(void) {
    // ------------------------------------------------------------
    // typeof_unqual(type) – removes all top‑level qualifiers
    // ------------------------------------------------------------

    typeof_unqual(int) a = 1;
    assert(_Generic(a, int: 1, default: 0));

    typeof_unqual(const int) b = 2;
    assert(_Generic(b, int: 1, default: 0));

    typeof_unqual(volatile int) c = 3;
    assert(_Generic(c, int: 1, default: 0));

    typeof_unqual(const volatile int) d = 4;
    assert(_Generic(d, int: 1, default: 0));

    // ------------------------------------------------------------
    // typeof_unqual(expr) – removes qualifiers from the expression type
    // ------------------------------------------------------------

    const int cx = 5;
    typeof_unqual(cx) e = 6;
    assert(_Generic(e, int: 1, default: 0));

    volatile int vx = 7;
    typeof_unqual(vx) f = 8;
    assert(_Generic(f, int: 1, default: 0));

    const volatile int cvx = 9;
    typeof_unqual(cvx) g = 10;
    assert(_Generic(g, int: 1, default: 0));

    // ------------------------------------------------------------
    // pointers – only top‑level const is removed
    // ------------------------------------------------------------

    int x = 0;
    int * const p = &x;          // const pointer to int

    typeof_unqual(p) q = &x;     // should be int *
    assert(_Generic(q, int *: 1, default: 0));

    const int * cp = &cx;        // pointer to const int (no top‑level qualifier)
    typeof_unqual(cp) cq = &cx;  // should still be const int *
    assert(_Generic(cq, const int *: 1, default: 0));

    const int * const cpc = &cx; // const pointer to const int
    typeof_unqual(cpc) cqc = &cx; // should be const int * (top‑level const removed)
    assert(_Generic(cqc, const int *: 1, default: 0));

    // ------------------------------------------------------------
    // arrays – qualifiers on element types are removed recursively
    // ------------------------------------------------------------

    int arr[10];
    typeof_unqual(arr) arr2 = {0};
    assert(sizeof(arr2) == sizeof(int[10]));

    const int carr[10];
    typeof_unqual(carr) uarr = {0};  // should be int[10] (const removed from element)
    assert(sizeof(uarr) == sizeof(int[10]));
    // Verify element type is int (we can't directly test array type with _Generic,
    // but we can test assignment compatibility)
    int tmp = uarr[0];  // no const warning

    const_arr4_t ca4 = {0};
    typeof_unqual(ca4) ua4 = {0};
    assert(sizeof(ua4) == sizeof(int[4]));

    // ------------------------------------------------------------
    // function types (no qualifiers possible) – unchanged
    // ------------------------------------------------------------

    typeof_unqual(func) *fp = func;
    assert(_Generic(fp, int (*)(double): 1, default: 0));

    typeof_unqual(func(1.0)) r = 0;
    assert(_Generic(r, int: 1, default: 0));

    // ------------------------------------------------------------
    // nested typeof_unqual
    // ------------------------------------------------------------

    typeof_unqual(typeof_unqual(const int)) nested = 1;
    assert(_Generic(nested, int: 1, default: 0));

    // ------------------------------------------------------------
    // anonymous struct (no qualifiers)
    // ------------------------------------------------------------

    typeof_unqual(struct { int a; long b; }) anon = {1, 2};
    assert(sizeof(anon) >= sizeof(int) + sizeof(long));

    // ------------------------------------------------------------
    // side effects must not execute
    // ------------------------------------------------------------

    sidefx_counter = 0;
    typeof_unqual(sidefx()) noeval = 0;
    assert(_Generic(noeval, int: 1, default: 0));
    if (sidefx_counter != 0)
        return 1;

    // ------------------------------------------------------------
    // comma operator
    // ------------------------------------------------------------

    typeof_unqual((x, 1.5)) d2 = 0;
    assert(_Generic(d2, double: 1, default: 0));

    // ------------------------------------------------------------
    // conditional operator
    // ------------------------------------------------------------

    typeof_unqual(1 ? x : 1L) cond = 0;
    assert(_Generic(cond, long: 1, default: 0));

    // ------------------------------------------------------------
    // compound literal – unqualified version of int (no effect)
    // ------------------------------------------------------------

    typeof_unqual((int){123}) cl = 0;
    assert(_Generic(cl, int: 1, default: 0));

    // ------------------------------------------------------------
    // compound literal with qualifier
    // ------------------------------------------------------------

    typeof_unqual((const int){42}) clq = 0;
    assert(_Generic(clq, int: 1, default: 0));

    // ------------------------------------------------------------
    // declarator interaction
    // ------------------------------------------------------------

    typeof_unqual(int) *ptr = &x;
    assert(_Generic(ptr, int *: 1, default: 0));

    // ------------------------------------------------------------
    // offsetof interaction
    // ------------------------------------------------------------

    struct foo { int a; int b; } *ptr2 = 0;
    assert(offsetof(typeof_unqual(*ptr2), b) == offsetof(struct foo, b));

    // ------------------------------------------------------------
    // struct definition inside typeof_unqual (should be okay)
    // ------------------------------------------------------------

    typeof_unqual(struct Bar { int x; }) typeof_bar = { .x = 5 };
    assert(typeof_bar.x == 5);

    return 0;
}
