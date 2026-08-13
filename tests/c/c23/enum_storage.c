//@ mode: c
//@ run-status: 0

/*
 * C23 fixed-underlying-enum torture test.
 *
 * Expected result:
 *     program compiles successfully
 *     program exits with status 0
 *
 * Suggested:
 *     gcc   -std=c23 -Wall -Wextra -pedantic enum_torture.c
 *     clang -std=c23 -Wall -Wextra -pedantic enum_torture.c
 *
 * The diagnostic-only cases from a negative test suite are deliberately
 * absent because this translation unit is required to compile successfully.
 */

#include <assert.h>
#include <stdint.h>
#include <stdbool.h>
#include <limits.h>
#include <stddef.h>

/*
 * --------------------------------------------------------------------------
 * 1. Basic fixed underlying types
 * --------------------------------------------------------------------------
 */

enum E_simple {
    E_simple_foo = 5,
    E_simple_bar = 10
};

enum E_simple2 {
    E_simple2_foo = 25,
    E_simple2_bar = 210
};

enum E_u8 : uint8_t {
    E_u8_0   = 0,
    E_u8_1   = 1,
    E_u8_254 = 254,
    E_u8_255 = 255
};

enum E_i8 : int8_t {
    E_i8_min = INT8_MIN,
    E_i8_neg = -1,
    E_i8_0   = 0,
    E_i8_max = INT8_MAX
};

enum E_u16 : uint16_t {
    E_u16_0   = 0,
    E_u16_max = UINT16_MAX
};

enum E_i16 : int16_t {
    E_i16_min = INT16_MIN,
    E_i16_max = INT16_MAX
};

enum E_u32 : uint32_t {
    E_u32_0   = 0,
    E_u32_hi  = UINT32_C(0x80000000),
    E_u32_max = UINT32_MAX
};

enum E_i32 : int32_t {
    E_i32_min = INT32_MIN,
    E_i32_max = INT32_MAX
};

enum E_u64 : uint64_t {
    E_u64_0   = UINT64_C(0),
    E_u64_hi  = UINT64_C(0x8000000000000000),
    E_u64_max = UINT64_MAX
};

enum E_i64 : int64_t {
    E_i64_min = INT64_MIN,
    E_i64_max = INT64_MAX
};


/*
 * --------------------------------------------------------------------------
 * 2. Typedef underlying types
 * --------------------------------------------------------------------------
 */

typedef unsigned char  byte_t;
typedef signed char    sbyte_t;
typedef unsigned short word_t;
typedef unsigned int   dword_t;
typedef unsigned long long qword_t;

enum E_typedef_u8 : byte_t {
    E_typedef_u8_0   = 0,
    E_typedef_u8_max = 255
};

enum E_typedef_i8 : sbyte_t {
    E_typedef_i8_min = -128,
    E_typedef_i8_max = 127
};

enum E_typedef_u16 : word_t {
    E_typedef_u16_0   = 0,
    E_typedef_u16_max = UINT16_MAX
};

enum E_typedef_u32 : dword_t {
    E_typedef_u32_0   = 0,
    E_typedef_u32_max = UINT32_MAX
};

enum E_typedef_u64 : qword_t {
    E_typedef_u64_0   = 0,
    E_typedef_u64_max = UINT64_MAX
};


/*
 * --------------------------------------------------------------------------
 * 3. Fixed enum is complete at its declaration
 * --------------------------------------------------------------------------
 */

enum Complete_u8 : uint8_t;

struct CompleteStruct {
    enum Complete_u8 value;
};

enum Complete_u8 : uint8_t {
    Complete_zero = 0,
    Complete_max  = 255
};


/*
 * --------------------------------------------------------------------------
 * 4. Forward declaration followed by definition
 * --------------------------------------------------------------------------
 */

enum Forward_u16 : uint16_t;

struct ForwardStruct {
    enum Forward_u16 value;
};

enum Forward_u16 : uint16_t {
    Forward_zero = 0,
    Forward_max  = UINT16_MAX
};


/*
 * --------------------------------------------------------------------------
 * 5. Same compatible redeclaration
 * --------------------------------------------------------------------------
 *
 * C23 permits compatible redeclarations of tagged types.
 */

enum Redeclared : uint32_t {
    Redeclared_a = 1,
    Redeclared_b = 2
};

enum Redeclared : uint32_t {
    Redeclared_a = 1,
    Redeclared_b = 2
};

enum Redeclared;


/*
 * --------------------------------------------------------------------------
 * 6. Anonymous fixed-underlying enum
 * --------------------------------------------------------------------------
 */

enum : uint8_t {
    Anonymous_zero = 0,
    Anonymous_one  = 1,
    Anonymous_max  = 255
};


/*
 * --------------------------------------------------------------------------
 * 7. Automatically incremented enumerators
 * --------------------------------------------------------------------------
 *
 * In particular, exercise the top of uint8_t.
 */

enum Increment_u8 : uint8_t {
    Increment_253 = 253,
    Increment_254,
    Increment_255
};


/*
 * --------------------------------------------------------------------------
 * 8. Explicit large constants
 * --------------------------------------------------------------------------
 */

enum Large_u32 : uint32_t {
    Large_u32_zero = UINT32_C(0),
    Large_u32_31   = UINT32_C(2147483648),
    Large_u32_max  = UINT32_MAX
};

enum Large_u64 : uint64_t {
    Large_u64_zero = UINT64_C(0),
    Large_u64_63   = UINT64_C(0x8000000000000000),
    Large_u64_max  = UINT64_MAX
};

enum Large_i64 : int64_t {
    Large_i64_min = INT64_MIN,
    Large_i64_max = INT64_MAX
};


/*
 * --------------------------------------------------------------------------
 * 9. bool as underlying type
 * --------------------------------------------------------------------------
 *
 * Only 0 and 1 are representable.
 */

enum E_bool : bool {
    E_bool_false = 0,
    E_bool_true  = 1
};


/*
 * --------------------------------------------------------------------------
 * 10. _Generic helpers
 * --------------------------------------------------------------------------
 */

#define IS_TYPE(expr, type) \
    _Generic((expr), type: 1, default: 0)

#define IS_NOT_TYPE(expr, type) \
    _Generic((expr), type: 0, default: 1)


/*
 * --------------------------------------------------------------------------
 * 11. Enumeration constants have the fixed enum type
 * --------------------------------------------------------------------------
 */

static void test_enumerator_types(void)
{
    /*
     * These are deliberately enum-type checks, not underlying-type checks.
     * C23 fixed-underlying enumeration constants have the enumerated type.
     */

    assert(IS_TYPE(E_u8_0, enum E_u8));
    assert(IS_TYPE(E_u8_255, enum E_u8));

    assert(IS_TYPE(E_i8_min, enum E_i8));
    assert(IS_TYPE(E_i8_max, enum E_i8));

    assert(IS_TYPE(E_u16_max, enum E_u16));
    assert(IS_TYPE(E_i16_max, enum E_i16));

    assert(IS_TYPE(E_u32_max, enum E_u32));
    assert(IS_TYPE(E_i32_max, enum E_i32));

    assert(IS_TYPE(E_u64_max, enum E_u64));
    assert(IS_TYPE(E_i64_max, enum E_i64));

    assert(IS_TYPE(Large_u64_max, enum Large_u64));
    assert(IS_TYPE(Large_i64_max, enum Large_i64));

    assert(IS_TYPE(Anonymous_max, uint8_t) ||
           IS_TYPE(Anonymous_max, int) ||
           IS_TYPE(Anonymous_max, typeof(Anonymous_max)));
}


/*
 * --------------------------------------------------------------------------
 * 12. Size and alignment
 * --------------------------------------------------------------------------
 */

static void test_size_alignment(void)
{
    assert(sizeof(enum E_u8)  == sizeof(uint8_t));
    assert(sizeof(enum E_i8)  == sizeof(int8_t));

    assert(sizeof(enum E_u16) == sizeof(uint16_t));
    assert(sizeof(enum E_i16) == sizeof(int16_t));

    assert(sizeof(enum E_u32) == sizeof(uint32_t));
    assert(sizeof(enum E_i32) == sizeof(int32_t));

    assert(sizeof(enum E_u64) == sizeof(uint64_t));
    assert(sizeof(enum E_i64) == sizeof(int64_t));

    assert(sizeof(enum E_typedef_u8)  == sizeof(byte_t));
    assert(sizeof(enum E_typedef_i8)  == sizeof(sbyte_t));
    assert(sizeof(enum E_typedef_u16) == sizeof(word_t));
    assert(sizeof(enum E_typedef_u32) == sizeof(dword_t));
    assert(sizeof(enum E_typedef_u64) == sizeof(qword_t));

    assert(sizeof(enum E_bool) == sizeof(bool));

    assert(_Alignof(enum E_u8)  == _Alignof(uint8_t));
    assert(_Alignof(enum E_i8)  == _Alignof(int8_t));

    assert(_Alignof(enum E_u16) == _Alignof(uint16_t));
    assert(_Alignof(enum E_i16) == _Alignof(int16_t));

    assert(_Alignof(enum E_u32) == _Alignof(uint32_t));
    assert(_Alignof(enum E_i32) == _Alignof(int32_t));

    assert(_Alignof(enum E_u64) == _Alignof(uint64_t));
    assert(_Alignof(enum E_i64) == _Alignof(int64_t));
}


/*
 * --------------------------------------------------------------------------
 * 13. Values and boundaries
 * --------------------------------------------------------------------------
 */

static void test_values(void)
{
    assert(E_u8_0 == 0);
    assert(E_u8_1 == 1);
    assert(E_u8_254 == 254);
    assert(E_u8_255 == 255);

    assert(E_i8_min == -128);
    assert(E_i8_neg == -1);
    assert(E_i8_0 == 0);
    assert(E_i8_max == 127);

    assert(E_u16_0 == 0);
    assert(E_u16_max == UINT16_MAX);

    assert(E_i16_min == INT16_MIN);
    assert(E_i16_max == INT16_MAX);

    assert(E_u32_0 == 0);
    assert(E_u32_hi == UINT32_C(0x80000000));
    assert(E_u32_max == UINT32_MAX);

    assert(E_i32_min == INT32_MIN);
    assert(E_i32_max == INT32_MAX);

    assert(E_u64_0 == UINT64_C(0));
    assert(E_u64_hi == UINT64_C(0x8000000000000000));
    assert(E_u64_max == UINT64_MAX);

    assert(E_i64_min == INT64_MIN);
    assert(E_i64_max == INT64_MAX);

    assert(Increment_253 == 253);
    assert(Increment_254 == 254);
    assert(Increment_255 == 255);

    assert(Large_u32_31 == UINT32_C(0x80000000));
    assert(Large_u32_max == UINT32_MAX);

    assert(Large_u64_63 == UINT64_C(0x8000000000000000));
    assert(Large_u64_max == UINT64_MAX);

    assert(Large_i64_min == INT64_MIN);
    assert(Large_i64_max == INT64_MAX);

    assert(E_bool_false == false);
    assert(E_bool_true == true);
}


/*
 * --------------------------------------------------------------------------
 * 14. Assignment and conversion
 * --------------------------------------------------------------------------
 */

static void test_conversions(void)
{
    enum E_u8 e8 = E_u8_255;
    enum E_i8 i8 = E_i8_min;
    enum E_u16 e16 = E_u16_max;
    enum E_u32 e32 = E_u32_max;
    enum E_u64 e64 = E_u64_max;

    uint8_t  u8  = e8;
    int8_t   s8  = i8;
    uint16_t u16 = e16;
    uint32_t u32 = e32;
    uint64_t u64 = e64;

    assert(u8 == UINT8_MAX);
    assert(s8 == INT8_MIN);
    assert(u16 == UINT16_MAX);
    assert(u32 == UINT32_MAX);
    assert(u64 == UINT64_MAX);

    e8 = (enum E_u8)UINT8_MAX;
    i8 = (enum E_i8)INT8_MIN;
    e16 = (enum E_u16)UINT16_MAX;
    e32 = (enum E_u32)UINT32_MAX;
    e64 = (enum E_u64)UINT64_MAX;

    assert(e8 == E_u8_255);
    assert(i8 == E_i8_min);
    assert(e16 == E_u16_max);
    assert(e32 == E_u32_max);
    assert(e64 == E_u64_max);

    /*
     * Conversion to a fixed enum has the semantics of conversion to
     * its underlying type.
     */
    assert((enum E_u8)256 == 0);
    assert((enum E_u8)-1 == UINT8_MAX);
    assert((enum E_i8)128 == INT8_MIN);
    assert((enum E_i8)255 == -1);
}


/*
 * --------------------------------------------------------------------------
 * 15. Integer promotions
 * --------------------------------------------------------------------------
 */

static void test_promotions(void)
{
    /*
     * uint8_t/int8_t enums undergo the usual integer promotion to int
     * on ordinary implementations where int can represent their range.
     */
    assert(IS_TYPE(+((enum E_u8)1), int));
    assert(IS_TYPE(-((enum E_u8)1), int));

    assert(IS_TYPE(+((enum E_i8)1), int));
    assert(IS_TYPE(-((enum E_i8)1), int));

    assert(IS_TYPE(+((enum E_u16)1), int));
    assert(IS_TYPE(+((enum E_i16)1), int));

    /*
     * uint32_t and uint64_t cannot in general be represented by int,
     * so they retain their underlying unsigned type through the
     * usual arithmetic conversions.
     */
    assert(IS_TYPE(((enum E_u32)1 + 1), uint32_t));
    assert(IS_TYPE(((enum E_u64)1 + 1), uint64_t));

    assert(IS_TYPE(((enum E_i64)1 + 1), int64_t));
}


/*
 * --------------------------------------------------------------------------
 * 16. Unary arithmetic
 * --------------------------------------------------------------------------
 */

static void test_unary(void)
{
    assert(+((enum E_u8)7) == 7);
    assert(-((enum E_u8)7) == -7);

    assert(+((enum E_i8)-7) == -7);
    assert(-((enum E_i8)-7) == 7);

    assert(+((enum E_u32)7) == UINT32_C(7));
    assert(+((enum E_u64)7) == UINT64_C(7));

    assert(-((enum E_i64)7) == INT64_C(-7));
}


/*
 * --------------------------------------------------------------------------
 * 17. Arithmetic and usual arithmetic conversions
 * --------------------------------------------------------------------------
 */

static void test_arithmetic(void)
{
    enum E_u8 a = E_u8_254;
    enum E_u8 b = E_u8_1;

    assert(a + b == 255);
    assert(a - b == 253);
    assert(a * b == 254);

    enum E_u32 x = E_u32_hi;
    enum E_u32 y = E_u32_0;

    assert(x + y == UINT32_C(0x80000000));
    assert((x | (enum E_u32)1) == UINT32_C(0x80000001));
    assert((x & (enum E_u32)1) == UINT32_C(0));
    assert((x ^ (enum E_u32)1) == UINT32_C(0x80000001));

    enum E_u64 p = E_u64_hi;

    assert((p | (enum E_u64)1) ==
           UINT64_C(0x8000000000000001));

    assert((p & (enum E_u64)1) == UINT64_C(0));

    assert((p ^ (enum E_u64)1) ==
           UINT64_C(0x8000000000000001));
}


/*
 * --------------------------------------------------------------------------
 * 18. Shifts
 * --------------------------------------------------------------------------
 */

static void test_shifts(void)
{
    enum E_u8 e8 = E_u8_1;
    enum E_u16 e16 = (enum E_u16)1;

    assert((e8 << 7) == 128);
    assert((e8 << 8) == 256);

    assert((e16 << 8) == 256);
    assert((e16 >> 4) == 0);

    enum E_u32 e32 = (enum E_u32)1;

    assert((e32 << 31) == UINT32_C(0x80000000));
    assert((e32 >> 0) == UINT32_C(1));

    enum E_u64 e64 = (enum E_u64)1;

    assert((e64 << 63) ==
           UINT64_C(0x8000000000000000));
}


/*
 * --------------------------------------------------------------------------
 * 19. Conditional operator
 * --------------------------------------------------------------------------
 */

static void test_conditional(void)
{
    enum E_u8 a = E_u8_1;
    enum E_u8 b = E_u8_255;

    assert((true ? a : b) == E_u8_1);
    assert((false ? a : b) == E_u8_255);

    assert(IS_TYPE((true ? a : b), int));

    enum E_u32 x = E_u32_hi;
    enum E_u32 y = E_u32_max;

    assert((true ? x : y) == E_u32_hi);
    assert((false ? x : y) == E_u32_max);

    assert(IS_TYPE((true ? x : y), uint32_t));
}


/*
 * --------------------------------------------------------------------------
 * 20. Arrays
 * --------------------------------------------------------------------------
 */

static void test_arrays(void)
{
    enum E_u8 a[17];

    assert(sizeof(a) == 17 * sizeof(enum E_u8));
    assert(sizeof(a) == 17 * sizeof(uint8_t));

    enum E_u16 b[9];

    assert(sizeof(b) == 9 * sizeof(enum E_u16));
    assert(sizeof(b) == 9 * sizeof(uint16_t));
}


/*
 * --------------------------------------------------------------------------
 * 21. Struct layout
 * --------------------------------------------------------------------------
 */

struct Struct_u8 {
    unsigned char before;
    enum E_u8 value;
    unsigned char after;
};

struct Struct_u16 {
    unsigned char before;
    enum E_u16 value;
    unsigned char after;
};

static void test_structs(void)
{
    struct Struct_u8 s8 = {
        .before = 1,
        .value = E_u8_255,
        .after = 2
    };

    struct Struct_u16 s16 = {
        .before = 1,
        .value = E_u16_max,
        .after = 2
    };

    assert(s8.before == 1);
    assert(s8.value == E_u8_255);
    assert(s8.after == 2);

    assert(s16.before == 1);
    assert(s16.value == E_u16_max);
    assert(s16.after == 2);

    assert(sizeof(s8.value) == sizeof(uint8_t));
    assert(sizeof(s16.value) == sizeof(uint16_t));
}


/*
 * --------------------------------------------------------------------------
 * 22. Union layout
 * --------------------------------------------------------------------------
 */

union Union_u8 {
    enum E_u8 e;
    uint8_t u;
};

union Union_u64 {
    enum E_u64 e;
    uint64_t u;
};

static void test_unions(void)
{
    union Union_u8 u8;

    u8.e = E_u8_255;
    assert(u8.e == E_u8_255);
    assert(sizeof(u8) >= sizeof(enum E_u8));
    assert(sizeof(u8) == sizeof(uint8_t));

    u8.u = UINT8_MAX;
    assert(u8.u == UINT8_MAX);

    union Union_u64 u64;

    u64.e = E_u64_max;
    assert(u64.e == E_u64_max);
    assert(sizeof(u64) == sizeof(uint64_t));

    u64.u = UINT64_MAX;
    assert(u64.u == UINT64_MAX);
}


/*
 * --------------------------------------------------------------------------
 * 23. Complete fixed enum in a structure before its definition
 * --------------------------------------------------------------------------
 */

struct BeforeDefinition {
    enum Complete_u8 value;
};

static void test_forward_completeness(void)
{
    struct BeforeDefinition x = {
        .value = Complete_max
    };

    struct ForwardStruct y = {
        .value = Forward_max
    };

    assert(x.value == Complete_max);
    assert(y.value == Forward_max);

    assert(sizeof(enum Complete_u8) == sizeof(uint8_t));
    assert(sizeof(enum Forward_u16) == sizeof(uint16_t));
}


/*
 * --------------------------------------------------------------------------
 * 24. Redeclaration behavior
 * --------------------------------------------------------------------------
 */

static void test_redeclaration(void)
{
    enum Redeclared x = Redeclared_a;
    enum Redeclared y = Redeclared_b;

    assert(x == 1);
    assert(y == 2);

    assert(sizeof(enum Redeclared) == sizeof(uint32_t));
}


/*
 * --------------------------------------------------------------------------
 * 25. Function parameter / return ABI
 * --------------------------------------------------------------------------
 */

static enum E_u8 return_u8(enum E_u8 x)
{
    return x;
}

static enum E_i8 return_i8(enum E_i8 x)
{
    return x;
}

static enum E_u16 return_u16(enum E_u16 x)
{
    return x;
}

static enum E_u32 return_u32(enum E_u32 x)
{
    return x;
}

static enum E_u64 return_u64(enum E_u64 x)
{
    return x;
}

static enum E_i64 return_i64(enum E_i64 x)
{
    return x;
}

static void test_functions(void)
{
    assert(return_u8(E_u8_255) == E_u8_255);
    assert(return_i8(E_i8_min) == E_i8_min);
    assert(return_u16(E_u16_max) == E_u16_max);
    assert(return_u32(E_u32_max) == E_u32_max);
    assert(return_u64(E_u64_max) == E_u64_max);
    assert(return_i64(E_i64_min) == E_i64_min);
}


/*
 * --------------------------------------------------------------------------
 * 26. Pointers to enum types
 * --------------------------------------------------------------------------
 */

static void test_pointers(void)
{
    enum E_u8 e8 = E_u8_255;
    enum E_u16 e16 = E_u16_max;
    enum E_u64 e64 = E_u64_max;

    enum E_u8 *p8 = &e8;
    enum E_u16 *p16 = &e16;
    enum E_u64 *p64 = &e64;

    assert(*p8 == E_u8_255);
    assert(*p16 == E_u16_max);
    assert(*p64 == E_u64_max);

    assert(sizeof(*p8) == sizeof(uint8_t));
    assert(sizeof(*p16) == sizeof(uint16_t));
    assert(sizeof(*p64) == sizeof(uint64_t));
}


/*
 * --------------------------------------------------------------------------
 * 27. _Alignof / arrays / nested aggregates
 * --------------------------------------------------------------------------
 */

struct Aggregate {
    enum E_u8  a[3];
    enum E_u16 b[3];
    enum E_u32 c[3];
    enum E_u64 d[3];
};

static void test_aggregate(void)
{
    struct Aggregate x = {
        .a = { E_u8_0, E_u8_1, E_u8_255 },
        .b = { E_u16_0, 1, E_u16_max },
        .c = { E_u32_0, 1, E_u32_max },
        .d = { E_u64_0, 1, E_u64_max }
    };

    assert(x.a[0] == E_u8_0);
    assert(x.a[1] == E_u8_1);
    assert(x.a[2] == E_u8_255);

    assert(x.b[0] == E_u16_0);
    assert(x.b[2] == E_u16_max);

    assert(x.c[0] == E_u32_0);
    assert(x.c[2] == E_u32_max);

    assert(x.d[0] == E_u64_0);
    assert(x.d[2] == E_u64_max);
}


/*
 * --------------------------------------------------------------------------
 * 28. Different enum types with identical underlying representation
 * --------------------------------------------------------------------------
 */

enum Color : uint8_t {
    Color_red   = 1,
    Color_green = 2
};

enum Direction : uint8_t {
    Direction_up   = 1,
    Direction_down = 2
};

static void test_distinct_enum_types(void)
{
    enum Color c = Color_red;
    enum Direction d = Direction_up;

    assert(c == Color_red);
    assert(d == Direction_up);

    assert(sizeof(enum Color) == sizeof(uint8_t));
    assert(sizeof(enum Direction) == sizeof(uint8_t));

    /*
     * Same representation does not make these the same enum type.
     */
    assert(IS_TYPE(c, enum Color));
    assert(IS_TYPE(c, uint8_t));
    assert(IS_TYPE(d, enum Direction));
    assert(IS_TYPE((uint8_t)5, enum Color));
    assert(IS_TYPE((uint8_t)5, enum Direction));
    assert(IS_NOT_TYPE(c, enum Direction));
    assert(IS_NOT_TYPE(d, enum Color));
}

static void test_distinct_enum_types_for_simple(void)
{
    enum E_simple c = E_simple_foo;
    enum E_simple2 d = E_simple2_bar;

    assert(c == E_simple_foo);
    assert(d == E_simple2_bar);

    assert(sizeof(enum E_simple) == sizeof(int));
    assert(sizeof(enum E_simple2) == sizeof(int));

    /*
     * Same representation does not make these the same enum type.
     */
    assert(IS_TYPE(c, enum E_simple));
    assert(IS_NOT_TYPE(c, int));
    assert(IS_TYPE(d, enum E_simple2));
    assert(IS_NOT_TYPE(c, enum E_simple2));
    assert(IS_NOT_TYPE(d, enum E_simple));
}

/*
 * --------------------------------------------------------------------------
 * 28b. Plain enum underlying type is sized from the enumerator values
 * --------------------------------------------------------------------------
 */

enum E_int_range    { E_int_lo = -2147483647 - 1, E_int_hi = 2147483647 };
enum E_uint_range   { E_uint_lo = 0, E_uint_hi = 3000000000U };
enum E_long_range   { E_long_lo = -3000000000LL, E_long_hi = 3000000000LL };
enum E_ulong_range  { E_ulong_lo = 0, E_ulong_hi = 5000000000ULL };
enum E_u64v_range   { E_u64v_lo = 0, E_u64v_hi = 18446744073709551615ULL };

static void test_plain_enum_value_range(void)
{
    /*
     * A plain (no fixed underlying type) enum must pick an underlying type
     * able to represent all its enumerator values, mirroring GCC's choice
     * among {int, unsigned int, long, unsigned long}. Values that do not fit
     * in int must not be truncated or sign-extended as int.
     */
    assert(IS_TYPE(E_int_hi, int));
    assert(IS_TYPE(E_uint_hi, unsigned int));
    assert(IS_TYPE(E_long_lo, long));
    assert(IS_TYPE(E_long_hi, long));
    assert(IS_TYPE(E_ulong_hi, unsigned long));

    /* Values survive intact (no truncation/sign-extension via int). */
    assert((unsigned long long)E_uint_hi == 3000000000ULL);
    assert((long long)E_long_lo == -3000000000LL);
    assert((long long)E_long_hi == 3000000000LL);
    assert((unsigned long long)E_ulong_hi == 5000000000ULL);
    assert((unsigned long long)E_u64v_hi == 18446744073709551615ULL);

    /* Arithmetic on large plain-enum constants keeps the payload type. */
    assert((unsigned long long)(E_uint_hi + 1U) == 3000000001ULL);
    assert((long long)(E_long_lo - 1) == -3000000001LL);

    /* The chosen underlying type is reflected in the enum's size. */
    assert(sizeof(enum E_int_range) == sizeof(int));
    assert(sizeof(enum E_uint_range) == sizeof(unsigned int));
    assert(sizeof(enum E_long_range) == sizeof(long));
    assert(sizeof(enum E_ulong_range) == sizeof(unsigned long));
    assert(sizeof(enum E_u64v_range) == sizeof(unsigned long));
}

/*
 * --------------------------------------------------------------------------
 * 29. Signed/unsigned interaction
 * --------------------------------------------------------------------------
 */

static void test_signed_unsigned(void)
{
    enum E_i8 s = E_i8_neg;
    enum E_u8 u = E_u8_255;

    assert(s == -1);
    assert(u == 255);

    /*
     * Both narrow enums undergo integer promotion on normal C23
     * implementations with a conventional int range.
     */
    assert(IS_TYPE(s + u, int));
    assert(s + u == 254);
}


/*
 * --------------------------------------------------------------------------
 * 30. Bitwise operations
 * --------------------------------------------------------------------------
 */

static void test_bitwise(void)
{
    enum E_u8 a = (enum E_u8)0xAA;
    enum E_u8 b = (enum E_u8)0x55;

    assert((a & b) == 0);
    assert((a | b) == 0xFF);
    assert((a ^ b) == 0xFF);

    enum E_u32 x = (enum E_u32)0xAAAAAAAAU;
    enum E_u32 y = (enum E_u32)0x55555555U;

    assert((x & y) == 0);
    assert((x | y) == UINT32_MAX);
    assert((x ^ y) == UINT32_MAX);
}


/*
 * --------------------------------------------------------------------------
 * 31. Comparisons
 * --------------------------------------------------------------------------
 */

static void test_comparisons(void)
{
    enum E_u8 a = E_u8_1;
    enum E_u8 b = E_u8_255;

    assert(a < b);
    assert(b > a);
    assert(a != b);
    assert(a == 1);
    assert(b == 255);

    enum E_i8 x = E_i8_min;
    enum E_i8 y = E_i8_max;

    assert(x < y);
    assert(y > x);
    assert(x != y);
}


/*
 * --------------------------------------------------------------------------
 * 32. Switch statements
 * --------------------------------------------------------------------------
 */

static int switch_u8(enum E_u8 e)
{
    switch (e) {
        case E_u8_0:
            return 0;
        case E_u8_1:
            return 1;
        case E_u8_255:
            return 255;
        default:
            return -1;
    }
}

static int switch_u64(enum E_u64 e)
{
    switch (e) {
        case E_u64_0:
            return 0;
        case E_u64_max:
            return 1;
        default:
            return -1;
    }
}

static void test_switches(void)
{
    assert(switch_u8(E_u8_0) == 0);
    assert(switch_u8(E_u8_1) == 1);
    assert(switch_u8(E_u8_255) == 255);

    assert(switch_u64(E_u64_0) == 0);
    assert(switch_u64(E_u64_max) == 1);
}


/*
 * --------------------------------------------------------------------------
 * 33. Main
 * --------------------------------------------------------------------------
 */

int main(void)
{
    test_enumerator_types();
    test_size_alignment();
    test_values();
    test_conversions();
    test_promotions();
    test_unary();
    test_arithmetic();
    test_shifts();
    test_conditional();
    test_arrays();
    test_structs();
    test_unions();
    test_forward_completeness();
    test_redeclaration();
    test_functions();
    test_pointers();
    test_aggregate();
    test_distinct_enum_types();
    test_distinct_enum_types_for_simple();
    test_plain_enum_value_range();
    test_signed_unsigned();
    test_bitwise();
    test_comparisons();
    test_switches();

    return 0;
}
