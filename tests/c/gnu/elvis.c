//@ mode: c
//@ run-status: 0
// Test for GCC extension: omitted middle operand in conditional operator (?:)
// Syntax: a ?: b  is equivalent to  a ? a : b, but 'a' is evaluated only once.
// This is not standard C; it's a GNU extension (works with -std=gnu*).

#include <stddef.h>
#include <assert.h>

// side-effect counter
int counter = 0;

int inc(void) {
    counter++;
    return 1;
}

int zero(void) {
    return 0;
}

// ------------------------------------------------------------------
// 1. Basic functionality: a ?: b behaves like a ? a : b
// ------------------------------------------------------------------

void test_basic(void) {
    // Non-zero first operand -> returns first operand
    assert((5 ?: 10) == 5);
    // Zero first operand -> returns second operand
    assert((0 ?: 10) == 10);
    // With expressions
    int x = 5;
    assert((x ?: 20) == 5);
    x = 0;
    assert((x ?: 20) == 20);
}

// ------------------------------------------------------------------
// 2. Side effects: first operand evaluated only once
// ------------------------------------------------------------------

void test_side_effects(void) {
    counter = 0;
    int result = inc() ?: 42;
    assert(result == 1);
    assert(counter == 1);   // inc() called once

    // Same with zero case
    counter = 0;
    result = zero() ?: 42;
    assert(result == 42);
    assert(counter == 0);   // zero() has no side effect, but still evaluated
}

// ------------------------------------------------------------------
// 3. Type compatibility: type of expression is the common type of
//    first and second operands (with usual arithmetic conversions).
//    For omitted middle, the first operand's type is used as the
//    type for the middle (since it's not evaluated).
// ------------------------------------------------------------------

void test_types(void) {
    int i = 5;
    double d = 3.14;

    // i ?: d -> result type is double (usual arithmetic conversion)
    typeof(1 ? i : d) t1 = 0.0;
    assert(_Generic(t1, double: 1, default: 0));

    // With omitted middle: i ?: d -> first operand is int, second is double,
    // so result is double as well.
    typeof(i ?: d) t2 = 0.0;
    assert(_Generic(t2, double: 1, default: 0));

    // Pointers: first operand is pointer to int, second is pointer to void
    int x = 0;
    int *p = &x;
    void *vp = &x;
    // Conditional with both: result is void * (composite type)
    typeof(1 ? p : vp) t3 = vp;
    assert(_Generic(t3, void *: 1, default: 0));
    // Omitted middle: p ?: vp -> result type? According to GCC, the type is the
    // common type of p and vp, which is void*.
    typeof(p ?: vp) t4 = vp;
    assert(_Generic(t4, void *: 1, default: 0));

    // Qualifiers: if first operand is const int*, second is int*,
    // result is const int* (qualifiers combined).
    const int *cp = &x;
    int *p2 = &x;
    typeof(1 ? cp : p2) t5 = cp;
    assert(_Generic(t5, const int *: 1, default: 0));
    // Omitted middle: same
    typeof(cp ?: p2) t6 = cp;
    assert(_Generic(t6, const int *: 1, default: 0));
}

// ------------------------------------------------------------------
// 4. Null pointer constant and pointer types
// ------------------------------------------------------------------

void test_null_ptr(void) {
    int x = 0;
    int *p = &x;
    // 0 ?: p -> first operand is 0 (null pointer constant), second is int*.
    // The type of the conditional is int*, because null pointer constant
    // can be converted to any pointer type.
    typeof(0 ?: p) t1 = p;
    assert(_Generic(t1, int *: 1, default: 0));

    // Also with NULL
    typeof(NULL ?: p) t2 = p;
    assert(_Generic(t2, int *: 1, default: 0));
}

// ------------------------------------------------------------------
// 5. Complex expressions with side effects and type
// ------------------------------------------------------------------

int global = 10;

int get_value(void) {
    return global++;
}

void test_complex(void) {
    int a = 5;
    int b = 0;
    int result = (a > 0 ?: b);  // a>0 is true, so returns a>0 (1)
    assert(result == 1);

    // Using function returning non-zero
    global = 10;
    result = get_value() ?: 42;
    assert(result == 10);
    assert(global == 11);   // get_value() called once

    // Zero case: function returns 0
    global = 0;
    result = get_value() ?: 42;
    assert(result == 42);
    assert(global == 1);    // get_value() called once and returned 0
}

// ------------------------------------------------------------------
// 6. Nested omitted-middle operators
// ------------------------------------------------------------------

void test_nested(void) {
    int a = 0, b = 5, c = 10;
    int result = (a ?: b) ?: c;
    // a is 0, so a?:b -> b (5), then 5?:c -> 5
    assert(result == 5);

    a = 0; b = 0; c = 10;
    result = (a ?: b) ?: c;
    // a?:b -> b (0), then 0?:c -> c (10)
    assert(result == 10);
}

// ------------------------------------------------------------------
// 7. Use in assignments / as lvalue? (GNU extension also allows lvalue
//    for ?: if both operands are lvalues and compatible. For omitted middle,
//    if first operand is an lvalue, is the result an lvalue? Not well-defined.
//    We skip lvalue tests as they may vary.
// ------------------------------------------------------------------

int main(void) {
    test_basic();
    test_side_effects();
    test_types();
    test_null_ptr();
    test_complex();
    test_nested();
    return 0;
}
