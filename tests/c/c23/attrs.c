//@ mode: c
//@ run-status: 0
// Test for C23 standard attributes: [[nodiscard]], [[maybe_unused]], [[deprecated]],
// [[fallthrough]], [[likely]], [[unlikely]], [[reproducible]], [[unsequenced]].

#include <stddef.h>
#include <assert.h>

// ------------------------------------------------------------
// [[nodiscard]] – warn if return value is ignored
// ------------------------------------------------------------

[[nodiscard]] int must_use(void) {
    return 42;
}

// ------------------------------------------------------------
// [[deprecated]] – mark as obsolete (with optional message)
// ------------------------------------------------------------

[[deprecated]] int old_func(void) {
    return 0;
}

[[deprecated("use new_func instead")]] int older_func(void) {
    return 1;
}

// ------------------------------------------------------------
// [[maybe_unused]] – suppress unused warnings
// ------------------------------------------------------------

int test_unused(void) {
    [[maybe_unused]] int unused_var = 123;
    return 0;
}

// ------------------------------------------------------------
// [[fallthrough]] – indicate intentional fall‑through in switch
// ------------------------------------------------------------

int test_fallthrough(int x) {
    int result = 0;
    switch (x) {
        case 1:
            result += 1;
            [[fallthrough]];
        case 2:
            result += 2;
            break;
        default:
            result = -1;
            break;
    }
    return result;
}

// ------------------------------------------------------------
// [[likely]] and [[unlikely]] – branch prediction hints
// ------------------------------------------------------------

int test_likely(int x) {
    if (x > 0) [[likely]] {
        return x + 1;
    } else [[unlikely]] {
        return x - 1;
    }
}

int test_label_likely(int x) {
    if (x == 0) {
        goto zero;
    }
    return 1;
zero:
    [[unlikely]] return 0;
}

// ------------------------------------------------------------
// [[reproducible]] and [[unsequenced]] – function guarantees
// (C23 new attributes, require that function is pure and side‑effect‑free)
// ------------------------------------------------------------

[[reproducible]] int square(int n) {
    return n * n;
}

[[unsequenced]] int double_it(int n) {
    return n + n;
}

// ------------------------------------------------------------
// Attributes on structs, enums, and their members
// ------------------------------------------------------------

struct [[maybe_unused]] S {
    int a [[maybe_unused]];
    int b;
};

enum [[maybe_unused]] E { A [[maybe_unused]], B };

// ------------------------------------------------------------
// Attributes on function parameters ([[maybe_unused]])
// ------------------------------------------------------------

int param_unused([[maybe_unused]] int a, int b) {
    return b;
}

// ------------------------------------------------------------
// Attributes on variable declarations (with initializers)
// ------------------------------------------------------------

[[maybe_unused]] static int global_unused = 0;

// ------------------------------------------------------------
// Attributes on typedefs (maybe_unused can be applied)
// ------------------------------------------------------------

[[maybe_unused]] typedef int my_int_t;

// ------------------------------------------------------------
// Attributes on empty declarations (allowed)
// ------------------------------------------------------------

[[maybe_unused]];

// ------------------------------------------------------------
// Main test – exercise all attributes (they don't affect runtime)
// ------------------------------------------------------------

int main(void) {
    // nodiscard – ignore return to see if compile warns (we don't check warnings)
    must_use();  // ignored, should trigger warning but not error

    // deprecated – use old functions (warns)
    old_func();
    older_func();

    // maybe_unused – used in test_unused (no warning)
    test_unused();

    // fallthrough – test switch fallthrough
    assert(test_fallthrough(1) == 3);   // 1+2
    assert(test_fallthrough(2) == 2);
    assert(test_fallthrough(3) == -1);

    // likely/unlikely – branch hints
    assert(test_likely(5) == 6);
    assert(test_likely(-1) == -2);
    assert(test_label_likely(0) == 0);
    assert(test_label_likely(1) == 1);

    // reproducible and unsequenced – call functions
    assert(square(5) == 25);
    assert(double_it(5) == 10);

    // parameter unused – just call
    assert(param_unused(10, 20) == 20);

    // ensure we reference global to avoid "unused" warning
    (void)global_unused;

    // struct/enum attributes – compile only; no runtime checks
    struct S s = { .a = 1, .b = 2 };
    assert(s.a == 1);
    assert(s.b == 2);

    enum E e = B;
    assert(e == 1);  // B = 1 if A=0

    // typedef attribute – just use type
    my_int_t z = 123;
    assert(z == 123);

    // empty declaration – nothing to test

    return 0;
}
