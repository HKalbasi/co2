//@ mode: c
//@ run-status: 0

/*
 * x86-64 GCC/SysV bit-field compatibility torture test
 *
 * Target:
 *   - x86-64
 *   - little endian
 *   - GCC-compatible System V AMD64 ABI
 *
 * This test intentionally goes beyond ISO C where necessary to verify
 * GCC-compatible ABI layout.
 *
 * It exits 0 when all assertions pass.
 *
 * Recommended:
 *
 *   gcc -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror bitfield_test.c
 *
 * For GCC's __int128 extensions:
 *
 *   gcc -std=gnu11 -O2 -Wall -Wextra -Wpedantic -Werror bitfield_test.c
 */

#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <string.h>

/*
 * -------------------------------------------------------------------------
 * Target validation
 * -------------------------------------------------------------------------
 */

#if !defined(__x86_64__) && !defined(_M_X64)
# error "This test targets x86-64."
#endif

#if CHAR_BIT != 8
# error "This test assumes 8-bit bytes, as on x86-64."
#endif

#if defined(__BYTE_ORDER__) && defined(__ORDER_LITTLE_ENDIAN__)
# if __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#  error "This test assumes little-endian x86-64."
# endif
#endif

_Static_assert(sizeof(unsigned char) == 1, "char size");
_Static_assert(sizeof(unsigned short) == 2, "short size");
_Static_assert(sizeof(unsigned int) == 4, "int size");
_Static_assert(sizeof(unsigned long) == 8, "long size");
_Static_assert(sizeof(unsigned long long) == 8, "long long size");

_Static_assert(CHAR_BIT == 8, "8-bit bytes required");

/*
 * We use an 8-bit byte view of objects.  uint8_t is required on the
 * x86-64 environment being tested; fail clearly if it is somehow absent.
 */
_Static_assert(sizeof(uint8_t) == 1, "uint8_t required");

/*
 * -------------------------------------------------------------------------
 * ISO-C baseline declarations
 * -------------------------------------------------------------------------
 */

struct iso_small {
    _Bool b1 : 1;

    unsigned int u1 : 1;
    unsigned int u2 : 2;
    unsigned int u3 : 3;
    unsigned int u8 : 8;
    unsigned int u16 : 16;
    unsigned int u31 : 31;
    unsigned int u32 : 32;

    signed int s1 : 1;
    signed int s7 : 7;
    signed int s31 : 31;
    signed int s32 : 32;
};

struct iso_ull {
    unsigned long long u1 : 1;
    unsigned long long u7 : 7;
    unsigned long long u8 : 8;
    unsigned long long u31 : 31;
    unsigned long long u32 : 32;
    unsigned long long u40 : 40;
    unsigned long long u63 : 63;
    unsigned long long u64 : 64;
};

struct iso_zero {
    unsigned int a : 5;
    unsigned int : 0;
    unsigned int b : 5;

    unsigned long long c : 5;
    unsigned long long : 0;
    unsigned long long d : 5;
};

/*
 * -------------------------------------------------------------------------
 * GCC/SysV ABI layout test structures
 * -------------------------------------------------------------------------
 *
 * On AMD64 SysV / GCC:
 *
 *   - first field occupies low-order bits;
 *   - fields grow toward more significant bits;
 *   - bit-fields are allocated right-to-left;
 *   - an allocation unit is appropriate to the declared type;
 *   - a field cannot straddle an inappropriate storage-unit boundary.
 *
 * Consequently these expected object representations are ABI tests, not
 * merely ISO-C semantic tests.
 */

/*
 * 40 + 24 = exactly one 64-bit unit.
 */
struct abi_ull_40_24 {
    unsigned long long a : 40;
    unsigned long long b : 24;
};

/*
 * 40 + 40 cannot fit in one 64-bit allocation unit.
 *
 * GCC therefore begins b in the next 64-bit unit.
 */
struct abi_ull_40_40 {
    unsigned long long a : 40;
    unsigned long long b : 40;
};

/*
 * A field ending exactly at bit 63.
 */
struct abi_boundary_exact {
    unsigned long long a : 32;
    unsigned long long b : 32;
    unsigned long long c : 1;
};

/*
 * 63 + 1 exactly fills one 64-bit unit.
 */
struct abi_ull_63_1 {
    unsigned long long a : 63;
    unsigned long long b : 1;
};

/*
 * 64 + 1 requires two units.
 */
struct abi_ull_64_1 {
    unsigned long long a : 64;
    unsigned long long b : 1;
};

/*
 * Multiple fields entirely within one 64-bit allocation unit.
 */
struct abi_ull_many {
    unsigned long long a : 1;
    unsigned long long b : 2;
    unsigned long long c : 3;
    unsigned long long d : 4;
    unsigned long long e : 5;
    unsigned long long f : 6;
    unsigned long long g : 7;
    unsigned long long h : 8;
    unsigned long long i : 9;
    unsigned long long j : 10;
    unsigned long long k : 9;
};

/*
 * Sum is 64.
 */
struct abi_ull_many_exact {
    unsigned long long a : 1;
    unsigned long long b : 2;
    unsigned long long c : 3;
    unsigned long long d : 4;
    unsigned long long e : 5;
    unsigned long long f : 6;
    unsigned long long g : 7;
    unsigned long long h : 8;
    unsigned long long i : 15;
    unsigned long long j : 13;
};

/*
 * Mixed underlying types.
 *
 * GCC SysV permits these fields to share the same storage area when the
 * relevant fields fit.
 */
struct abi_mixed {
    unsigned int        a : 20;
    unsigned long long  b : 20;
    unsigned int        c : 12;
};

/*
 * Zero-width field forces the next field to a fresh allocation boundary.
 */
struct abi_zero_int {
    unsigned int a : 1;
    unsigned int : 0;
    unsigned int b : 1;
};

struct abi_zero_ll {
    unsigned long long a : 1;
    unsigned long long : 0;
    unsigned long long b : 1;
};

/*
 * The unnamed zero-width field has no declared name and is specifically
 * being used as an allocation-unit boundary.
 */
struct abi_zero_mixed {
    unsigned int a : 1;
    unsigned int : 0;
    unsigned long long b : 1;
};

/*
 * A normal member after bit-fields.
 */
struct abi_after {
    unsigned long long a : 40;
    unsigned long long b : 24;
    uint32_t tail;
};

/*
 * A normal member before bit-fields.
 */
struct abi_before {
    uint32_t head;
    unsigned long long a : 40;
    unsigned long long b : 24;
};

/*
 * Union punning is used only for examining the object representation that
 * the implementation actually produced.
 *
 * We do not read one union member after writing another as a portable ISO-C
 * semantic test; memcpy is used to inspect bytes instead.
 */

/*
 * -------------------------------------------------------------------------
 * Byte helpers
 * -------------------------------------------------------------------------
 */

static uint64_t
load64(const unsigned char *p)
{
    uint64_t x;

    memcpy(&x, p, sizeof x);
    return x;
}

static uint32_t
load32(const unsigned char *p)
{
    uint32_t x;

    memcpy(&x, p, sizeof x);
    return x;
}

static void
assert_zero_bytes(const void *obj, size_t n)
{
    const unsigned char *p = (const unsigned char *)obj;
    size_t i;

    for (i = 0; i < n; ++i)
        assert(p[i] == 0);
}

/*
 * -------------------------------------------------------------------------
 * ISO semantic tests
 * -------------------------------------------------------------------------
 */

static void
test_bool(void)
{
    struct {
        _Bool x : 1;
    } s;

    s.x = 0;
    assert(s.x == 0);

    s.x = 1;
    assert(s.x == 1);

    s.x = 2;
    assert(s.x == 1);

    s.x = -1;
    assert(s.x == 1);

    s.x = 12345;
    assert(s.x == 1);
}

static void
test_unsigned_values(void)
{
    struct iso_small s = { 0 };

    s.u1 = 1u;
    assert(s.u1 == 1u);

    s.u2 = 3u;
    assert(s.u2 == 3u);

    s.u3 = 7u;
    assert(s.u3 == 7u);

    s.u8 = 255u;
    assert(s.u8 == 255u);

    s.u16 = 65535u;
    assert(s.u16 == 65535u);

    /*
     * Every conforming implementation has at least 32 value bits in
     * unsigned int on the x86-64 environment assumed here.
     */
    s.u31 = 0x7fffffffU;
    assert(s.u31 == 0x7fffffffU);

    s.u32 = 0xffffffffU;
    assert(s.u32 == 0xffffffffU);
}

static void
test_unsigned_long_long_values(void)
{
    struct iso_ull s = { 0 };

    s.u1 = 1ULL;
    assert(s.u1 == 1ULL);

    s.u7 = 127ULL;
    assert(s.u7 == 127ULL);

    s.u8 = 255ULL;
    assert(s.u8 == 255ULL);

    s.u31 = 0x7fffffffULL;
    assert(s.u31 == 0x7fffffffULL);

    s.u32 = 0xffffffffULL;
    assert(s.u32 == 0xffffffffULL);

    /*
     * This is the important case discussed earlier:
     *
     *   unsigned long long : 40
     *
     * is valid because unsigned long long is 64 bits here.
     */
    s.u40 = 0xffffffffffULL;
    assert(s.u40 == 0xffffffffffULL);

    s.u63 = 0x7fffffffffffffffULL;
    assert(s.u63 == 0x7fffffffffffffffULL);

    s.u64 = 0xffffffffffffffffULL;
    assert(s.u64 == 0xffffffffffffffffULL);
}

static void
test_increment_decrement(void)
{
    struct {
        unsigned long long x : 40;
    } s;

    s.x = 10;
    assert(++s.x == 11);
    assert(s.x == 11);

    assert(s.x++ == 11);
    assert(s.x == 12);

    assert(--s.x == 11);
    assert(s.x == 11);

    assert(s.x-- == 11);
    assert(s.x == 10);
}

static void
test_compound_assignment(void)
{
    struct {
        unsigned long long x : 40;
    } s;

    s.x = 10;

    s.x += 5;
    assert(s.x == 15);

    s.x *= 3;
    assert(s.x == 45);

    s.x |= 0x100;
    assert(s.x == 0x12D);

    s.x &= ~0x20ULL;
    assert((s.x & 0x20ULL) == 0);

    s.x ^= 0x100;
    assert(s.x == 0xD);
}

static void
test_promotions(void)
{
    struct {
        unsigned int u3 : 3;
        unsigned int u8 : 8;
        unsigned long long u40 : 40;
    } s;

    s.u3 = 7;
    s.u8 = 255;
    s.u40 = 123456;

    /*
     * 3- and 8-bit unsigned fields promote to int because int can represent
     * every possible value.
     */
    assert(sizeof(+s.u3) == sizeof(int));
    assert(sizeof(+s.u8) == sizeof(int));

    assert(+s.u3 == 7);
    assert(+s.u8 == 255);

    /*
     * The 40-bit unsigned long long field cannot be represented by int.
     * Its promoted expression therefore has a wider integer type.
     *
     * We test the result, not a particular implementation-internal type
     * spelling.
     */
    assert(+s.u40 == 123456ULL);
}

static void
test_signed_fields(void)
{
    struct {
        signed int s1 : 1;
        signed int s7 : 7;
        signed int s31 : 31;
    } s;

    s.s1 = 0;
    assert(s.s1 == 0);

    s.s1 = 1;
    assert(s.s1 == -1);

    s.s1 = -1;
    assert(s.s1 == -1);

    s.s7 = -1;
    assert(s.s7 == -1);

    s.s7 = 1;
    assert(s.s7 == 1);

    s.s31 = -1;
    assert(s.s31 == -1);

    s.s31 = 1234567;
    assert(s.s31 == 1234567);
}

static void
test_zero_width_semantics(void)
{
    struct iso_zero s = { 0 };

    s.a = 31;
    s.b = 31;
    s.c = 31;
    s.d = 31;

    assert(s.a == 31);
    assert(s.b == 31);
    assert(s.c == 31);
    assert(s.d == 31);
}

/*
 * -------------------------------------------------------------------------
 * ABI representation tests
 * -------------------------------------------------------------------------
 */

static void
test_ull_40_24_layout(void)
{
    struct abi_ull_40_24 s;

    memset(&s, 0, sizeof s);

    assert(sizeof s == 8);

    s.a = 0xffffffffffULL;
    assert(s.a == 0xffffffffffULL);
    assert(s.b == 0);

    /*
     * GCC x86-64 SysV:
     *
     * a occupies bits 0..39.
     */
    {
        unsigned char bytes[sizeof s];

        memcpy(bytes, &s, sizeof bytes);

        assert(load64(bytes) == 0x000000ffffffffffULL);
    }

    memset(&s, 0, sizeof s);

    s.b = 0xffffffULL;

    {
        unsigned char bytes[sizeof s];

        memcpy(bytes, &s, sizeof bytes);

        assert(load64(bytes) == 0xffffff0000000000ULL);
    }

    memset(&s, 0, sizeof s);

    s.a = 0x123456789aULL;
    s.b = 0xabcdefULL;

    assert(s.a == 0x123456789aULL);
    assert(s.b == 0xabcdefULL);

    {
        unsigned char bytes[sizeof s];

        memcpy(bytes, &s, sizeof bytes);

        assert(load64(bytes) == 0xabcdef123456789aULL);
    }
}

static void
test_ull_40_40_layout(void)
{
    struct abi_ull_40_40 s;

    memset(&s, 0, sizeof s);

    /*
     * 40 + 40 requires two 64-bit storage units.
     */
    assert(sizeof s == 16);

    s.a = 0x123456789aULL;
    s.b = 0xabcdef0123ULL;

    assert(s.a == 0x123456789aULL);
    assert(s.b == 0xabcdef0123ULL);

    {
        unsigned char bytes[sizeof s];

        memcpy(bytes, &s, sizeof bytes);

        assert(load64(bytes + 0) == 0x000000123456789aULL);
        assert(load64(bytes + 8) == 0x000000abcdef0123ULL);
    }
}

static void
test_ull_63_1_layout(void)
{
    struct abi_ull_63_1 s;

    memset(&s, 0, sizeof s);

    assert(sizeof s == 8);

    s.a = 0x7fffffffffffffffULL;
    assert(s.a == 0x7fffffffffffffffULL);

    s.b = 1;

    {
        unsigned char bytes[sizeof s];

        memcpy(bytes, &s, sizeof bytes);

        assert(load64(bytes) == 0xffffffffffffffffULL);
    }
}

static void
test_ull_64_1_layout(void)
{
    struct abi_ull_64_1 s;

    memset(&s, 0, sizeof s);

    /*
     * Full 64-bit field + another field => two allocation units.
     */
    assert(sizeof s == 16);

    s.a = 0xffffffffffffffffULL;
    s.b = 1;

    assert(s.a == 0xffffffffffffffffULL);
    assert(s.b == 1);

    {
        unsigned char bytes[sizeof s];

        memcpy(bytes, &s, sizeof bytes);

        assert(load64(bytes + 0) == 0xffffffffffffffffULL);
        assert(load64(bytes + 8) == 1ULL);
    }
}

static void
test_many_fields(void)
{
    struct abi_ull_many s;

    memset(&s, 0, sizeof s);

    /*
     * 1+2+3+4+5+6+7+8+9+10+9 = 64.
     */
    assert(sizeof s == 8);

    s.a = 1;
    s.b = 3;
    s.c = 7;
    s.d = 15;
    s.e = 31;
    s.f = 63;
    s.g = 127;
    s.h = 255;
    s.i = 511;
    s.j = 1023;
    s.k = 511;

    assert(s.a == 1);
    assert(s.b == 3);
    assert(s.c == 7);
    assert(s.d == 15);
    assert(s.e == 31);
    assert(s.f == 63);
    assert(s.g == 127);
    assert(s.h == 255);
    assert(s.i == 511);
    assert(s.j == 1023);
    assert(s.k == 511);

    {
        unsigned char bytes[sizeof s];

        memcpy(bytes, &s, sizeof bytes);

        /*
         * Every bit is set.
         */
        assert(load64(bytes) == 0xffffffffffffffffULL);
    }
}

static void
test_many_exact(void)
{
    struct abi_ull_many_exact s;

    memset(&s, 0, sizeof s);

    assert(sizeof s == 8);

    s.a = 1;
    s.b = 3;
    s.c = 7;
    s.d = 15;
    s.e = 31;
    s.f = 63;
    s.g = 127;
    s.h = 255;
    s.i = 0x7fff;
    s.j = 0x1fff;

    assert(s.a == 1);
    assert(s.b == 3);
    assert(s.c == 7);
    assert(s.d == 15);
    assert(s.e == 31);
    assert(s.f == 63);
    assert(s.g == 127);
    assert(s.h == 255);
    assert(s.i == 0x7fff);
    assert(s.j == 0x1fff);

    {
        unsigned char bytes[sizeof s];

        memcpy(bytes, &s, sizeof bytes);

        assert(load64(bytes) == 0xffffffffffffffffULL);
    }
}

static void
test_mixed_layout(void)
{
    struct abi_mixed s;

    memset(&s, 0, sizeof s);

    /*
     * On GCC x86-64 this occupies one 64-bit allocation area:
     *
     *   a: bits  0..19
     *   b: bits 20..39
     *   c: bits 40..51
     *
     * remaining bits are padding.
     */
    assert(sizeof s == 8);

    s.a = 0xfffffU;
    s.b = 0xfffffULL;
    s.c = 0xfffU;

    assert(s.a == 0xfffffU);
    assert(s.b == 0xfffffULL);
    assert(s.c == 0xfffU);

    {
        unsigned char bytes[sizeof s];
        uint64_t expected;

        memcpy(bytes, &s, sizeof bytes);

        expected =
              0x000fffffffffffffULL;

        assert(load64(bytes) == expected);
    }
}

static void
test_zero_int_layout(void)
{
    struct abi_zero_int s;

    memset(&s, 0, sizeof s);

    /*
     * First int allocation unit contains a.
     * Zero-width field starts a new allocation unit.
     * b therefore begins at the next 32-bit boundary.
     */
    assert(sizeof s == 8);

    s.a = 1;
    s.b = 1;

    {
        unsigned char bytes[sizeof s];

        memcpy(bytes, &s, sizeof bytes);

        assert(load32(bytes + 0) == 1U);
        assert(load32(bytes + 4) == 1U);
    }
}

static void
test_zero_ll_layout(void)
{
    struct abi_zero_ll s;

    memset(&s, 0, sizeof s);

    assert(sizeof s == 16);

    s.a = 1;
    s.b = 1;

    {
        unsigned char bytes[sizeof s];

        memcpy(bytes, &s, sizeof bytes);

        assert(load64(bytes + 0) == 1ULL);
        assert(load64(bytes + 8) == 1ULL);
    }
}

static void
test_zero_mixed_layout(void)
{
    struct abi_zero_mixed s;

    memset(&s, 0, sizeof s);

    /*
     * GCC SysV behavior: zero-width unsigned-int field ends the current
     * int allocation unit; the following long-long field then uses its
     * appropriate allocation area.
     */
    assert(sizeof s == 8);

    s.a = 1;
    s.b = 1;

    assert(s.a == 1);
    assert(s.b == 1);

    {
        unsigned char bytes[sizeof s];

        memcpy(bytes, &s, sizeof bytes);

        /*
         * a occupies bit 0 of the first 32-bit unit, while b occupies
         * bit 32 of the enclosing 64-bit object.
         */
        assert(load64(bytes) == 0x0000000100000001ULL);
    }
}

static void
test_normal_members(void)
{
    struct abi_after a;
    struct abi_before b;

    memset(&a, 0, sizeof a);
    memset(&b, 0, sizeof b);

    /*
     * 8-byte bit-field storage followed by a 4-byte normal member.
     */
    assert(sizeof a == 16);

    a.a = 0x123456789aULL;
    a.b = 0xabcdefULL;
    a.tail = 0x11223344U;

    assert(a.a == 0x123456789aULL);
    assert(a.b == 0xabcdefULL);
    assert(a.tail == 0x11223344U);

    /*
     * Normal member first, followed by one 64-bit allocation unit.
     */
    assert(sizeof b == 16);

    b.head = 0x55667788U;
    b.a = 0x123456789aULL;
    b.b = 0xabcdefULL;

    assert(b.head == 0x55667788U);
    assert(b.a == 0x123456789aULL);
    assert(b.b == 0xabcdefULL);
}

/*
 * -------------------------------------------------------------------------
 * Bit isolation tests
 * -------------------------------------------------------------------------
 *
 * These are particularly useful against compilers which accidentally use
 * the wrong shift direction or overwrite neighboring fields.
 */

static void
test_bit_isolation(void)
{
    struct abi_ull_40_24 s;

    s.a = 0;
    s.b = 0;

    s.a = 1;
    assert(s.a == 1);
    assert(s.b == 0);

    s.b = 1;
    assert(s.a == 1);
    assert(s.b == 1);

    s.a = 0;
    assert(s.a == 0);
    assert(s.b == 1);

    s.b = 0;
    assert(s.b == 0);

    s.a = 0xffffffffffULL;
    assert(s.a == 0xffffffffffULL);
    assert(s.b == 0);

    s.b = 0xffffffULL;
    assert(s.a == 0xffffffffffULL);
    assert(s.b == 0xffffffULL);
}

/*
 * -------------------------------------------------------------------------
 * Volatile
 * -------------------------------------------------------------------------
 */

static void
test_volatile(void)
{
    volatile struct {
        unsigned long long a : 40;
        unsigned long long b : 24;
    } s;

    s.a = 0;
    s.b = 0;

    s.a = 0x123456789aULL;
    s.b = 0xabcdefULL;

    assert(s.a == 0x123456789aULL);
    assert(s.b == 0xabcdefULL);
}

/*
 * -------------------------------------------------------------------------
 * Function ABI exercises
 * -------------------------------------------------------------------------
 *
 * These don't prove inter-compiler compatibility by themselves: if caller
 * and callee are compiled by the same buggy compiler, both could agree on
 * the same wrong ABI.
 *
 * They are nevertheless useful for catching internal inconsistencies
 * between bit-field lowering and the compiler's own aggregate calling code.
 */

struct call_8 {
    unsigned long long a : 40;
    unsigned long long b : 24;
};

struct call_16 {
    unsigned long long a : 40;
    unsigned long long b : 40;
};

static struct call_8
make_call_8(uint64_t a, uint64_t b)
{
    struct call_8 s;

    s.a = a;
    s.b = b;

    return s;
}

static uint64_t
consume_call_8(struct call_8 s)
{
    assert(s.a == 0x123456789aULL);
    assert(s.b == 0xabcdefULL);

    return s.a ^ s.b;
}

static struct call_16
make_call_16(uint64_t a, uint64_t b)
{
    struct call_16 s;

    s.a = a;
    s.b = b;

    return s;
}

static uint64_t
consume_call_16(struct call_16 s)
{
    assert(s.a == 0x123456789aULL);
    assert(s.b == 0xabcdef0123ULL);

    return s.a ^ s.b;
}

static void
test_function_calls(void)
{
    struct call_8 a;
    struct call_16 b;

    a = make_call_8(0x123456789aULL, 0xabcdefULL);

    assert(a.a == 0x123456789aULL);
    assert(a.b == 0xabcdefULL);

    assert(
        consume_call_8(a) ==
        (0x123456789aULL ^ 0xabcdefULL)
    );

    b = make_call_16(0x123456789aULL, 0xabcdef0123ULL);

    assert(b.a == 0x123456789aULL);
    assert(b.b == 0xabcdef0123ULL);

    assert(
        consume_call_16(b) ==
        (0x123456789aULL ^ 0xabcdef0123ULL)
    );
}

/*
 * -------------------------------------------------------------------------
 * Main
 * -------------------------------------------------------------------------
 */

int
main(void)
{
    test_bool();

    test_unsigned_values();
    test_unsigned_long_long_values();
    test_increment_decrement();
    test_compound_assignment();
    test_promotions();
    test_signed_fields();
    test_zero_width_semantics();

    test_ull_40_24_layout();
    test_ull_40_40_layout();
    test_ull_63_1_layout();
    test_ull_64_1_layout();
    test_many_fields();
    test_many_exact();
    test_mixed_layout();

    test_zero_int_layout();
    test_zero_ll_layout();
    test_zero_mixed_layout();

    test_normal_members();
    test_bit_isolation();
    test_volatile();

    test_function_calls();

    return 0;
}
