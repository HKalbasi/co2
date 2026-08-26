//@ mode: c
//@ run-status: 0
// Test for compound literals (C99/C11/C23) – all forms

#include <stddef.h>
#include <assert.h>

// ------------------------------------------------------------
// Test structures and unions
// ------------------------------------------------------------

struct point {
    int x;
    int y;
};

struct line {
    struct point p1;
    struct point p2;
};

struct nested {
    int a;
    struct {
        int b;
        int c;
    } inner;
    struct point pt;
    int arr[2];
};

struct complex {
    struct {
        int f1;
        int f2;
    } f;
    int g;
};

union u {
    int i;
    float f;
    double d;
};

union u2 {
    struct {
        int a;
        int b;
    } s;
    long long ll;
};

// ------------------------------------------------------------
// 1. Basic compound literals without designators (positional)
// ------------------------------------------------------------

void test_positional(void) {
    // Scalar
    int *ip = &(int){ 42 };
    assert(*ip == 42);

    // Struct (positional)
    struct point *pp = &(struct point){ 3, 4 };
    assert(pp->x == 3 && pp->y == 4);

    // Union (positional) – initializes first member
    union u *up = &(union u){ 5 };
    assert(up->i == 5);

    // Array (positional) – pointer to array
    int (*arrp)[3] = &(int[3]){ 1, 2, 3 };
    assert((*arrp)[0] == 1 && (*arrp)[1] == 2 && (*arrp)[2] == 3);

    // Multidimensional array
    int (*mat)[2][2] = &(int[2][2]){ {1,2}, {3,4} };
    assert((*mat)[0][0] == 1 && (*mat)[0][1] == 2);
    assert((*mat)[1][0] == 3 && (*mat)[1][1] == 4);
}

// ------------------------------------------------------------
// 2. Compound literals with designators (nested & unions)
// ------------------------------------------------------------

void test_designators(void) {
    // Struct with designators (order irrelevant)
    struct point p = (struct point){ .y = 5, .x = 7 };
    assert(p.x == 7 && p.y == 5);

    // Nested designators
    struct line l = (struct line){ .p1.x = 1, .p2.y = 2 };
    assert(l.p1.x == 1 && l.p1.y == 0);
    assert(l.p2.x == 0 && l.p2.y == 2);

    // Deeper nesting
    struct nested n = (struct nested){
        .inner.b = 42,
        .pt.x = 99,
        .arr[1] = 77
    };
    assert(n.a == 0);
    assert(n.inner.b == 42 && n.inner.c == 0);
    assert(n.pt.x == 99 && n.pt.y == 0);
    assert(n.arr[0] == 0 && n.arr[1] == 77);

    // Union with designator for a specific member
    union u u1 = (union u){ .f = 3.14f };
    assert(u1.f == 3.14f);

    // Union with nested struct designator
    union u2 u2 = (union u2){ .s.b = 5 };
    assert(u2.s.a == 0 && u2.s.b == 5);
    assert(u2.ll != 5); // initializes s member, not ll

    // Compound literal taking address with designators
    struct complex *cp = &(struct complex){ .f.f1 = 10, .f.f2 = 20 };
    assert(cp->f.f1 == 10 && cp->f.f2 == 20 && cp->g == 0);

    // Array compound literal – pointer to element (decay)
    struct point *arrp = (struct point[2]){ [1] = { .x = 5, .y = 6 } };
    assert(arrp[0].x == 0 && arrp[0].y == 0);
    assert(arrp[1].x == 5 && arrp[1].y == 6);
}

// ------------------------------------------------------------
// 3. Mixed positional and designators (allowed: designator after positionals)
// ------------------------------------------------------------

void test_mixed_init(void) {
    // Positional then designator (last designator overrides)
    struct point p = (struct point){ 1, .y = 3 };
    assert(p.x == 1 && p.y == 3);

    // Designator then positional (positional continues from that point)
    struct point p2 = (struct point){ .x = 5, 7 };
    assert(p2.x == 5 && p2.y == 7);

    // Array mixed – pointer to array
    int (*arrp)[4] = &(int[4]){ 1, 2, [3] = 8 };
    assert((*arrp)[0] == 1 && (*arrp)[1] == 2 && (*arrp)[2] == 0 && (*arrp)[3] == 8);
}

// ------------------------------------------------------------
// 4. Compound literals as lvalues (modifiable)
// ------------------------------------------------------------

void test_lvalue(void) {
    // Modify through pointer
    struct point *pp = &(struct point){ 1, 2 };
    pp->x = 10;
    assert(pp->x == 10 && pp->y == 2);

    // Assign to struct from compound literal
    struct point p = (struct point){ .x = 5, .y = 6 };
    p = (struct point){ .x = 7, .y = 8 };
    assert(p.x == 7 && p.y == 8);

    // Array compound literal as lvalue – modify via pointer
    int (*ap)[3] = &(int[3]){ 1, 2, 3 };
    (*ap)[1] = 42;
    assert((*ap)[1] == 42);
}

// ------------------------------------------------------------
// 5. Using typeof on compound literals
// ------------------------------------------------------------

void test_typeof_compound(void) {
    // typeof on struct literal
    typeof((struct point){ .x = 1, .y = 2 }) p = { .x = 3, .y = 4 };
    assert(p.x == 3 && p.y == 4);

    // typeof on union literal
    typeof((union u){ .f = 1.0f }) u1 = { .i = 42 };
    assert(u1.i == 42); // initializes first member because no designator

    // typeof on array literal – decays to pointer? Actually typeof of array literal gives the array type.
    // We can use it to declare an array variable with brace initializer.
    typeof((int[3]){ 1, 2, 3 }) arr = { 4, 5, 6 };
    assert(arr[0] == 4 && arr[1] == 5 && arr[2] == 6);

    // typeof on nested designator
    typeof((struct complex){ .f.f1 = 1 }) c = { .f.f1 = 10, .f.f2 = 20, .g = 30 };
    assert(c.f.f1 == 10 && c.f.f2 == 20 && c.g == 30);
}

// ------------------------------------------------------------
// 6. Compound literals as function arguments
// ------------------------------------------------------------

int sum_point(struct point p) {
    return p.x + p.y;
}

int sum_array(int arr[3]) {
    return arr[0] + arr[1] + arr[2];
}

void test_function_arg(void) {
    // Direct passing of compound literal
    int s = sum_point((struct point){ .y = 10, .x = 5 });
    assert(s == 15);

    s = sum_point((struct point){ 7, 8 });
    assert(s == 15);

    // Array argument
    int total = sum_array((int[3]){ 1, 2, 3 });
    assert(total == 6);

    // With designators
    total = sum_array((int[3]){ [2] = 5, [0] = 1 });
    assert(total == 6); // 1 + 0 + 5 = 6
}

// ------------------------------------------------------------
// 7. Nested compound literals
// ------------------------------------------------------------

void test_nested_compound(void) {
    // Compound literal inside another (e.g., struct with struct literal)
    struct line l = (struct line){
        .p1 = (struct point){ .x = 1, .y = 2 },
        .p2 = (struct point){ 3, 4 }
    };
    assert(l.p1.x == 1 && l.p1.y == 2);
    assert(l.p2.x == 3 && l.p2.y == 4);

    // Array of structs with nested compound literals – pointer to element
    struct point *pts = (struct point[2]){
        (struct point){ .x = 5, .y = 6 },
        (struct point){ 7, 8 }
    };
    assert(pts[0].x == 5 && pts[0].y == 6);
    assert(pts[1].x == 7 && pts[1].y == 8);

    // Taking address of nested compound literal
    struct line *lp = &(struct line){
        .p1 = (struct point){ .x = 10, .y = 20 },
        .p2 = (struct point){ 30, 40 }
    };
    assert(lp->p1.x == 10 && lp->p1.y == 20);
    assert(lp->p2.x == 30 && lp->p2.y == 40);
}

// ------------------------------------------------------------
// 8. Arrays with designators (range designators – GNU extension)
// Not standard, so we skip range designators.
// ------------------------------------------------------------

void test_arrays_with_designators(void) {
    // Standard array designator (single index) – pointer to array
    int (*arrp)[5] = &(int[5]){ [2] = 7, [0] = 3, [4] = 9 };
    assert((*arrp)[0] == 3 && (*arrp)[1] == 0 && (*arrp)[2] == 7);
    assert((*arrp)[3] == 0 && (*arrp)[4] == 9);

    // Multidimensional array designators
    int (*matp)[2][3] = &(int[2][3]){
        [0][1] = 5,
        [1][2] = 8
    };
    assert((*matp)[0][0] == 0 && (*matp)[0][1] == 5 && (*matp)[0][2] == 0);
    assert((*matp)[1][0] == 0 && (*matp)[1][1] == 0 && (*matp)[1][2] == 8);

    // Array of structs with designators – pointer to element
    struct point *pts = (struct point[3]){
        [1] = { .x = 1, .y = 2 },
        [2] = { 3, 4 }
    };
    assert(pts[0].x == 0 && pts[0].y == 0);
    assert(pts[1].x == 1 && pts[1].y == 2);
    assert(pts[2].x == 3 && pts[2].y == 4);
}

// ------------------------------------------------------------
// 9. Union with compound literal and designator side effects (no side effects)
// ------------------------------------------------------------

int side = 0;
int inc_side(void) { side++; return 42; }

void test_union_side(void) {
    // Function call in initializer – evaluated once
    side = 0;
    union u u1 = (union u){ .i = inc_side() };
    assert(side == 1);
    assert(u1.i == 42);

    // With nested designator and function call
    side = 0;
    union u2 u2 = (union u2){ .s.a = inc_side() };
    assert(side == 1);
    assert(u2.s.a == 42 && u2.s.b == 0);
}

// ------------------------------------------------------------
// 10. Compound literal with empty initializer (zero-initialized)
// ------------------------------------------------------------

void test_empty_init(void) {
    // Empty braces -> zero initialization for struct
    struct point p = (struct point){ };
    assert(p.x == 0 && p.y == 0);

    union u u1 = (union u){ };
    assert(u1.i == 0);

    // Array – pointer to array with empty braces
    int (*arrp)[3] = &(int[3]){ };
    assert((*arrp)[0] == 0 && (*arrp)[1] == 0 && (*arrp)[2] == 0);
}

// ------------------------------------------------------------
// 11. Compound literal with designator for union with anonymous struct
// ------------------------------------------------------------

struct wrapper {
    union {
        struct {
            int a;
            int b;
        } s;
        long long ll;
    } u;
    int flag;
};

void test_anonymous_union(void) {
    // Designator for anonymous union member (unnamed)
    // Here we have a named union 'u', so we can designator .u.s.a
    struct wrapper w = (struct wrapper){
        .u.s.a = 10,
        .u.s.b = 20,
        .flag = 1
    };
    assert(w.u.s.a == 10 && w.u.s.b == 20 && w.flag == 1);
}

// ------------------------------------------------------------
// Main
// ------------------------------------------------------------

int main(void) {
    test_positional();
    test_designators();
    test_mixed_init();
    test_lvalue();
    test_typeof_compound();
    test_function_arg();
    test_nested_compound();
    test_arrays_with_designators();
    test_union_side();
    test_empty_init();
    test_anonymous_union();
    return 0;
}
