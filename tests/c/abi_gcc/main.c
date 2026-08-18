#include <stdio.h>

#include "lib.h"

#define CHECK(idx, cond, msg) \
    do { \
        if (!(cond)) { \
            printf("FAIL %d: %s\n", (idx), (msg)); \
            return (idx); \
        } \
    } while (0)

static int add_fn(int a, int b) {
    return a + b;
}

int main(void) {
    CHECK(1, abi_add(2, 3) == 5, "abi_add");

    CHECK(2, abi_add_long(0x1122334455667788LL, 1) == 0x1122334455667789LL,
          "abi_add_long");

    CHECK(3, abi_add_double(1.5, 2.25) == 3.75, "abi_add_double");

    CHECK(4, abi_mul_float(2.0f, 3.0f) == 6.0f, "abi_mul_float");

    CHECK(5, abi_str_eq("co2", "co2"), "abi_str_eq equal");
    CHECK(6, !abi_str_eq("co2", "co3"), "abi_str_eq not equal");

    struct abi_pair q = abi_make_pair(3, 4);
    CHECK(7, q.x == 3 && q.y == 4, "abi_make_pair");

    struct abi_pair p = { 10, 32 };
    CHECK(8, abi_pair_sum(p) == 42, "abi_pair_sum");

    CHECK(9, abi_sum_many(1, 2, 3, 4, 5, 6, 7, 8) == 36, "abi_sum_many");

    CHECK(10, abi_mix(1, 1.5, 2LL, 2.5, 3) == 10.0, "abi_mix");

    CHECK(11, abi_add(abi_global, 2) == 42, "abi_global");

    struct abi_bf bf = abi_bf_make(3, 5, 10, -4);
    CHECK(12, bf.a == 3 && bf.b == 5 && bf.c == 10 && bf.s == -4, "abi_bf_make");

    CHECK(13, abi_bf_pack(bf)
                  == (3u | (5u << 3) | (10u << 8) | (((unsigned int)(-4 + 8)) << 18)),
          "abi_bf_pack");

    union abi_num n = abi_union_make(3.5);
    CHECK(14, n.f == 3.5f, "abi_union_make");
    CHECK(15, abi_union_as_double(n) == 3.5, "abi_union_as_double");

    struct abi_packed pk = abi_packed_make(0x12345678);
    CHECK(16, sizeof(struct abi_packed) == 7, "abi_packed size");
    CHECK(17, pk.c == 1 && pk.x == 0x12345678 && pk.s == 2, "abi_packed_make");
    CHECK(18, abi_packed_get(pk) == 1 + 0x12345678 + 2, "abi_packed_get");

    CHECK(19, abi_enum_next(ABI_RED) == ABI_GREEN, "abi_enum_next");
    CHECK(20, abi_enum_next(ABI_YELLOW) == ABI_RED, "abi_enum_next wrap");

    struct abi_big bg = abi_big_make(1, 2, 3, 4);
    CHECK(21, bg.a == 1 && bg.b == 2 && bg.c == 3 && bg.d == 4, "abi_big_make");
    CHECK(22, abi_big_sum(bg) == 10, "abi_big_sum");

    struct abi_big bg2 = { 10, 20, 30, 40 };
    CHECK(23, abi_big_sum(bg2) == 100, "abi_big_sum direct");

    CHECK(24, abi_apply(add_fn, 5, 7) == 12, "abi_apply");

    CHECK(25, abi_not_bool(1) == 0, "abi_not_bool true");
    CHECK(26, abi_not_bool(0) == 1, "abi_not_bool false");

    printf("all ABI checks passed\n");
    return 0;
}
