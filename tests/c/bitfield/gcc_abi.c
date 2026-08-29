//@ mode: c
//@ run-status: 0

#include <assert.h>
#include <stddef.h>
#include <string.h>

/*
 * x86-64 SysV ABI bit-field layout:
 *
 *   - fields are allocated from right to left (LSB first)
 *   - a field must fit entirely in a storage unit appropriate
 *     for its declared type
 *   - storage-unit sizes are:
 *         unsigned char       8
 *         unsigned short     16
 *         unsigned int       32
 *         unsigned long      64   (LP64)
 *         unsigned long long 64
 *   - anonymous fields consume bits but have no object member
 *   - zero-width fields force the next field onto a new
 *     allocation unit of the zero-width field's type
 *
 * This test intentionally targets the x86-64 SysV ABI rather than
 * portable ISO C semantics.
 */

#define CHECK_BYTES(obj, ...)                                             \
    do {                                                                  \
        static const unsigned char expected[] = { __VA_ARGS__ };          \
        unsigned char actual[sizeof(obj)];                                \
        memcpy(actual, &(obj), sizeof(obj));                              \
        assert(sizeof(expected) == sizeof(obj));                          \
        assert(memcmp(actual, expected, sizeof(obj)) == 0);               \
    } while (0)


/* --------------------------------------------------------------------- */
/* 1. Basic packing: multiple fields in one unit.                       */
/* --------------------------------------------------------------------- */

struct basic {
    unsigned t:4;
    unsigned m:1;
    unsigned p:11;
    unsigned char pad[6];
};

static void test_basic(void)
{
    struct basic x;

    assert(sizeof(x) == 8);
    assert(_Alignof(struct basic) == 4);
    assert(offsetof(struct basic, pad) == 2);

    /*
     *  bits  0..3  = t
     *        4      = m
     *        5..15  = p
     *  bytes 0..1  = complete 16-bit allocation
     */
    memset(&x, 0, sizeof(x));

    x.t = 0xf;
    CHECK_BYTES(x, 0x0f, 0x00, 0, 0, 0, 0, 0, 0);

    memset(&x, 0, sizeof(x));
    x.m = 1;
    CHECK_BYTES(x, 0x10, 0x00, 0, 0, 0, 0, 0, 0);

    memset(&x, 0, sizeof(x));
    x.p = 0x7ff;
    CHECK_BYTES(x, 0xe0, 0xff, 0, 0, 0, 0, 0, 0);
}


/* --------------------------------------------------------------------- */
/* 2. unsigned char: exact fit and spill.                               */
/* --------------------------------------------------------------------- */

struct uchar_exact {
    unsigned char a:3;
    unsigned char b:5;
    unsigned char x;
};

struct uchar_spill {
    unsigned char a:7;
    unsigned char b:2;
    unsigned char x;
};

static void test_uchar(void)
{
    struct uchar_exact a;
    struct uchar_spill b;

    assert(sizeof(a) == 2);
    assert(_Alignof(struct uchar_exact) == 1);
    assert(offsetof(struct uchar_exact, x) == 1);

    memset(&a, 0, sizeof(a));
    a.a = 7;
    a.b = 31;
    CHECK_BYTES(a, 0xff, 0x00);

    assert(sizeof(b) == 3);
    assert(_Alignof(struct uchar_spill) == 1);
    assert(offsetof(struct uchar_spill, x) == 2);

    /*
     * b cannot fit in the remaining one bit, so it starts
     * a fresh 8-bit allocation unit.
     */
    memset(&b, 0, sizeof(b));
    b.a = 0x7f;
    b.b = 3;
    CHECK_BYTES(b, 0x7f, 0x03, 0x00);
}


/* --------------------------------------------------------------------- */
/* 3. unsigned short: exact 16-bit boundary.                           */
/* --------------------------------------------------------------------- */

struct ushort_boundary {
    unsigned short a:3;
    unsigned short b:13;
    unsigned short c:1;
    unsigned char x;
};

static void test_ushort(void)
{
    struct ushort_boundary x;

    assert(sizeof(x) == 4);
    assert(_Alignof(struct ushort_boundary) == 2);
    assert(offsetof(struct ushort_boundary, x) == 3);

    /*
     * a+b = exactly 16 bits.
     * c therefore starts another 16-bit allocation unit.
     */
    memset(&x, 0, sizeof(x));
    x.a = 7;
    x.b = 0x1fff;
    x.c = 1;
    CHECK_BYTES(x, 0xff, 0xff, 0x01, 0x00);
}


/* --------------------------------------------------------------------- */
/* 4. unsigned int: exact 32-bit boundary.                             */
/* --------------------------------------------------------------------- */

struct uint_boundary {
    unsigned a:3;
    unsigned b:29;
    unsigned c:1;
    unsigned char x;
};

static void test_uint(void)
{
    struct uint_boundary x;

    assert(sizeof(x) == 8);
    assert(_Alignof(struct uint_boundary) == 4);
    assert(offsetof(struct uint_boundary, x) == 5);

    /*
     * a+b = exactly 32 bits.
     * c begins at the next 32-bit allocation unit.
     */
    memset(&x, 0, sizeof(x));
    x.a = 7;
    x.b = 0x1fffffff;
    x.c = 1;
    CHECK_BYTES(x, 0xff, 0xff, 0xff, 0xff,
                   0x01, 0x00, 0x00, 0x00);
}


/* --------------------------------------------------------------------- */
/* 5. unsigned long: 64-bit allocation unit on LP64.                   */
/* --------------------------------------------------------------------- */

struct ulong_boundary {
    unsigned long a:31;
    unsigned long b:33;
    unsigned long c:1;
    unsigned char x;
};

static void test_ulong(void)
{
    struct ulong_boundary x;

    assert(sizeof(x) == 16);
    assert(_Alignof(struct ulong_boundary) == 8);
    assert(offsetof(struct ulong_boundary, x) == 9);

    /*
     * a+b = exactly 64 bits.
     */
    memset(&x, 0, sizeof(x));
    x.a = 0x7fffffffUL;
    x.b = 0x1ffffffffUL;
    x.c = 1;

    CHECK_BYTES(x,
                0xff, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff, 0xff,
                0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00);
}


/* --------------------------------------------------------------------- */
/* 6. unsigned long long: same 64-bit rule.                            */
/* --------------------------------------------------------------------- */

struct ull_boundary {
    unsigned long long a:63;
    unsigned long long b:1;
    unsigned long long c:1;
    unsigned char x;
};

static void test_ull(void)
{
    struct ull_boundary x;

    assert(sizeof(x) == 16);
    assert(_Alignof(struct ull_boundary) == 8);
    assert(offsetof(struct ull_boundary, x) == 9);

    memset(&x, 0, sizeof(x));
    x.a = 0x7fffffffffffffffULL;
    x.b = 1;
    x.c = 1;

    CHECK_BYTES(x,
                0xff, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff, 0xff,
                0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00);
}


/* --------------------------------------------------------------------- */
/* 7. Anonymous non-zero-width bit-fields consume bits.                */
/* --------------------------------------------------------------------- */

struct anonymous_padding {
    unsigned char a:3;
    unsigned char :2;
    unsigned char b:3;
    unsigned char x;
};

struct anonymous_padding2 {
    unsigned a:3;
    unsigned :5;
    unsigned char b:1;
    unsigned char x;
};

static void test_anonymous_padding(void)
{
    struct anonymous_padding x;
    struct anonymous_padding2 y;

    assert(sizeof(x) == 2);
    assert(offsetof(struct anonymous_padding, x) == 1);

    /*
     * a = bits 0..2
     * :2 = bits 3..4
     * b = bits 5..7
     */
    memset(&x, 0, sizeof(x));
    x.a = 7;
    x.b = 7;
    CHECK_BYTES(x, 0xe7, 0x00);

    /*
     * The anonymous field does not become a member and doesn't
     * contribute a separately addressable object.
     */
    assert(offsetof(struct anonymous_padding, x) == 1);

    assert(sizeof(y) == 4);
    assert(offsetof(struct anonymous_padding2, x) == 2);

    /*
     * The first 3 bits belong to a; the following 5 are consumed
     * by the anonymous field; b occupies bit 8.
     */
    memset(&y, 0, sizeof(y));
    y.a = 7;
    y.b = 1;
    CHECK_BYTES(y, 0x07, 0x01, 0x00, 0x00);
}


/* --------------------------------------------------------------------- */
/* 8. Zero-width field: char allocation unit.                          */
/* --------------------------------------------------------------------- */

struct zero_char {
    unsigned char a:3;
    unsigned char :0;
    unsigned char b:1;
    unsigned char x;
};

static void test_zero_char(void)
{
    struct zero_char x;

    assert(sizeof(x) == 3);
    assert(_Alignof(struct zero_char) == 1);

    /*
     * The line above cannot be used: bit-fields have no address and
     * offsetof() on a bit-field is invalid.
     *
     * Instead, the observable boundary is x:
     */
    (void)x;
}


/* --------------------------------------------------------------------- */
/* 9. Zero-width field: int allocation/alignment boundary.              */
/* --------------------------------------------------------------------- */

struct zero_int {
    unsigned a:3;
    unsigned :0;
    unsigned char b;
    unsigned char x;
};

static void test_zero_int(void)
{
    struct zero_int x;

    /*
     * a occupies the first 32-bit allocation unit.
     * :0 terminates it.
     * b therefore starts at byte 4.
     */
    assert(sizeof(x) == 8);
    assert(_Alignof(struct zero_int) == 4);
    assert(offsetof(struct zero_int, b) == 4);
    assert(offsetof(struct zero_int, x) == 5);

    memset(&x, 0, sizeof(x));
    x.a = 7;
    x.b = 0xaa;
    x.x = 0xbb;

    CHECK_BYTES(x,
                0x07, 0x00, 0x00, 0x00,
                0xaa, 0xbb, 0x00, 0x00);
}


/* --------------------------------------------------------------------- */
/* 10. Zero-width field at an already exhausted boundary.              */
/* --------------------------------------------------------------------- */

struct zero_after_exact {
    unsigned a:16;
    unsigned b:16;
    unsigned :0;
    unsigned char x;
};

static void test_zero_after_exact(void)
{
    struct zero_after_exact x;

    assert(sizeof(x) == 8);
    assert(_Alignof(struct zero_after_exact) == 4);
    assert(offsetof(struct zero_after_exact, x) == 4);

    /*
     * The allocation unit is already exhausted.  :0 must not
     * introduce another 4-byte gap beyond the already-completed unit.
     */
    memset(&x, 0, sizeof(x));
    x.a = 0xffff;
    x.b = 0xffff;
    x.x = 0xaa;

    CHECK_BYTES(x,
                0xff, 0xff, 0xff, 0xff,
                0xaa, 0x00, 0x00, 0x00);
}


/* --------------------------------------------------------------------- */
/* 11. Mixed base types.                                                */
/* --------------------------------------------------------------------- */

struct mixed1 {
    unsigned char a:3;
    unsigned b:1;
    unsigned char c:4;
    unsigned char x;
};

struct mixed2 {
    unsigned a:3;
    unsigned char b:1;
    unsigned c:4;
    unsigned char x;
};

static void test_mixed(void)
{
    struct mixed1 a;
    struct mixed2 b;

    assert(sizeof(a) == 4);
    assert(_Alignof(struct mixed1) == 4);
    assert(offsetof(struct mixed1, x) == 1);

    /*
     * The first byte contains all eight bits:
     *   a = 0..2
     *   b = 3
     *   c = 4..7
     */
    memset(&a, 0, sizeof(a));
    a.a = 7;
    a.b = 1;
    a.c = 15;
    CHECK_BYTES(a, 0xff, 0x00, 0x00, 0x00);

    assert(sizeof(b) == 4);
    assert(_Alignof(struct mixed2) == 4);
    assert(offsetof(struct mixed2, x) == 1);

    memset(&b, 0, sizeof(b));
    b.a = 7;
    b.b = 1;
    b.c = 15;
    CHECK_BYTES(b, 0xff, 0x00, 0x00, 0x00);
}


/* --------------------------------------------------------------------- */
/* 12. Ordinary member before a bit-field: alignment.                  */
/* --------------------------------------------------------------------- */

struct ordinary_before {
    unsigned char c;
    unsigned b:1;
    unsigned char x;
};

static void test_ordinary_before(void)
{
    struct ordinary_before x;

    assert(sizeof(x) == 4);
    assert(_Alignof(struct ordinary_before) == 4);
    assert(offsetof(struct ordinary_before, c) == 0);
    assert(offsetof(struct ordinary_before, x) == 2);

    memset(&x, 0, sizeof(x));
    x.c = 0xaa;
    x.b = 1;
    x.x = 0xbb;

    CHECK_BYTES(x, 0xaa, 0x01, 0xbb, 0x00);
}


/* --------------------------------------------------------------------- */
/* 13. Ordinary member after a bit-field.                               */
/* --------------------------------------------------------------------- */

struct ordinary_after {
    unsigned a:3;
    unsigned char x;
    unsigned b:1;
};

static void test_ordinary_after(void)
{
    struct ordinary_after x;

    assert(sizeof(x) == 4);
    assert(_Alignof(struct ordinary_after) == 4);
    assert(offsetof(struct ordinary_after, x) == 1);

    /*
     * The ordinary byte does not wait for the whole 32-bit
     * allocation unit to become exhausted.
     */
    memset(&x, 0, sizeof(x));
    x.a = 7;
    x.x = 0xaa;
    x.b = 1;

    CHECK_BYTES(x,
                0x07,
                0xaa,
                0x01,
                0x00);
}


/* --------------------------------------------------------------------- */
/* 14. Signed bit-fields: value/range behavior.                        */
/* --------------------------------------------------------------------- */

struct signed_fields {
    signed int a:3;
    signed int b:5;
    signed int c:24;
    unsigned char x;
};

static void test_signed(void)
{
    struct signed_fields s;

    assert(sizeof(s) == 8);
    assert(_Alignof(struct signed_fields) == 4);
    assert(offsetof(struct signed_fields, x) == 4);

    memset(&s, 0, sizeof(s));

    s.a = -4;
    s.b = -16;
    s.c = -1;

    /*
     * These are the ABI-specified signed ranges:
     *   a: [-4, 3]
     *   b: [-16, 15]
     *   c: [-8388608, 8388607]
     */
    assert(s.a == -4);
    assert(s.b == -16);
    assert(s.c == -1);

    /*
     * Negative values use the normal signed integer representation
     * expected by x86-64 SysV.
     */
    CHECK_BYTES(s,
                0x84, 0xff, 0xff, 0xff,
                0x00, 0x00, 0x00, 0x00);
}


/* --------------------------------------------------------------------- */
/* 15. Plain (neither signed nor unsigned) bit-fields.                 */
/* --------------------------------------------------------------------- */

struct plain_fields {
    unsigned char a:3;
    unsigned char b:3;
    unsigned char c:2;
    unsigned char x;
};

static void test_plain(void)
{
    struct plain_fields x;

    assert(sizeof(x) == 2);
    assert(_Alignof(struct plain_fields) == 1);
    assert(offsetof(struct plain_fields, x) == 1);

    /*
     * SysV says a bit-field that is neither signed nor unsigned
     * has the non-negative range corresponding to its width.
     */
    memset(&x, 0, sizeof(x));

    x.a = 7;
    x.b = 7;
    x.c = 3;

    assert(x.a == 7);
    assert(x.b == 7);
    assert(x.c == 3);

    CHECK_BYTES(x, 0xff, 0x00);
}


/* --------------------------------------------------------------------- */
/* 16. _Bool bit-fields.                                                */
/* --------------------------------------------------------------------- */

struct bool_fields {
    _Bool a:1;
    _Bool b:1;
    _Bool c:1;
    unsigned char x;
};

static void test_bool(void)
{
    struct bool_fields x;

    assert(sizeof(x) == 2);
    assert(_Alignof(struct bool_fields) == 1);
    assert(offsetof(struct bool_fields, x) == 1);

    memset(&x, 0, sizeof(x));

    x.a = 1;
    x.b = 1;
    x.c = 0;

    assert(x.a == 1);
    assert(x.b == 1);
    assert(x.c == 0);

    CHECK_BYTES(x, 0x03, 0x00);
}


/* --------------------------------------------------------------------- */
/* 17. A field exactly filling a 32-bit unit followed by a member.     */
/* --------------------------------------------------------------------- */

struct exact_int {
    unsigned a:16;
    unsigned b:16;
    unsigned char x;
};

static void test_exact_int(void)
{
    struct exact_int x;

    assert(sizeof(x) == 8);
    assert(_Alignof(struct exact_int) == 4);
    assert(offsetof(struct exact_int, x) == 4);

    memset(&x, 0, sizeof(x));
    x.a = 0xffff;
    x.b = 0xffff;
    x.x = 0xaa;

    CHECK_BYTES(x,
                0xff, 0xff, 0xff, 0xff,
                0xaa, 0x00, 0x00, 0x00);
}


/* --------------------------------------------------------------------- */
/* 18. Multiple storage units with a narrow field at every boundary.  */
/* --------------------------------------------------------------------- */

struct staircase {
    unsigned char a:8;
    unsigned short b:8;
    unsigned int c:8;
    unsigned long d:8;
    unsigned char x;
};

static void test_staircase(void)
{
    struct staircase x;

    /*
     * Each field fits, but changing declared type changes the
     * allocation/alignment rules. GCC packs consecutive 8-bit
     * bit-fields tightly regardless of base type on x86-64.
     */
    assert(sizeof(x) == 8);
    assert(_Alignof(struct staircase) == 8);

    assert(offsetof(struct staircase, x) == 4);

    memset(&x, 0, sizeof(x));
    x.a = 0xaa;
    x.b = 0xbb;
    x.c = 0xcc;
    x.d = 0xdd;
    x.x = 0xee;

    CHECK_BYTES(x,
                0xaa, 0xbb, 0xcc, 0xdd,
                0xee, 0x00, 0x00, 0x00);
}


/* --------------------------------------------------------------------- */
/* 19. Union containing bit-fields.                                    */
/* --------------------------------------------------------------------- */

union bits_union {
    struct {
        unsigned a:3;
        unsigned b:29;
    } f;

    unsigned word;

    unsigned char bytes[4];
};

static void test_union(void)
{
    union bits_union u;

    assert(sizeof(u) == 4);
    assert(_Alignof(union bits_union) == 4);

    memset(&u, 0, sizeof(u));

    u.f.a = 5;
    u.f.b = 0x1234567;

    /*
     * a occupies bits 0..2; b occupies bits 3..31.
     */
    assert((u.word & 7u) == 5u);
    assert((u.word >> 3) == 0x1234567u);

    CHECK_BYTES(u, 0x3d, 0x2b, 0x1a, 0x09);
}


/* --------------------------------------------------------------------- */
/* 20. Cross-check the bit positions by writing one field at a time.  */
/* --------------------------------------------------------------------- */

struct position_check {
    unsigned a:1;
    unsigned b:2;
    unsigned c:4;
    unsigned d:8;
    unsigned e:16;
    unsigned f:1;
    unsigned char x;
};

static void test_bit_positions(void)
{
    struct position_check x;

    assert(sizeof(x) == 8);
    assert(offsetof(struct position_check, x) == 4);

    memset(&x, 0, sizeof(x));
    x.a = 1;
    CHECK_BYTES(x, 0x01, 0x00, 0x00, 0x00,
                   0x00, 0x00, 0x00, 0x00);

    memset(&x, 0, sizeof(x));
    x.b = 3;
    CHECK_BYTES(x, 0x06, 0x00, 0x00, 0x00,
                   0x00, 0x00, 0x00, 0x00);

    memset(&x, 0, sizeof(x));
    x.c = 15;
    CHECK_BYTES(x, 0x78, 0x00, 0x00, 0x00,
                   0x00, 0x00, 0x00, 0x00);

    memset(&x, 0, sizeof(x));
    x.d = 0xff;
    CHECK_BYTES(x, 0x80, 0x7f, 0x00, 0x00,
                   0x00, 0x00, 0x00, 0x00);

    memset(&x, 0, sizeof(x));
    x.e = 0xffff;
    CHECK_BYTES(x, 0x00, 0x80, 0xff, 0x7f,
                   0x00, 0x00, 0x00, 0x00);

    memset(&x, 0, sizeof(x));
    x.f = 1;
    CHECK_BYTES(x, 0x00, 0x00, 0x00, 0x80,
                   0x00, 0x00, 0x00, 0x00);
}


/* --------------------------------------------------------------------- */

int main(void)
{
    test_basic();
    test_uchar();
    test_ushort();
    test_uint();
    test_ulong();
    test_ull();
    test_anonymous_padding();

    /*
     * Do not call test_zero_char(): it intentionally documents an
     * invalid offsetof(bit-field) expression in its body.
     */
    test_zero_int();
    test_zero_after_exact();

    test_mixed();
    test_ordinary_before();
    test_ordinary_after();
    test_signed();
    test_plain();
    test_bool();
    test_exact_int();
    test_staircase();
    test_union();
    test_bit_positions();

    return 0;
}
