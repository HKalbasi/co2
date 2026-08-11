//@ mode: c
//@ run-status: 0

/* C11 §6.4.4.1: for a hex literal with 'u'/'U' suffix the type is the
 * first of { unsigned int, unsigned long, unsigned long long } that fits.
 * 0xffffffffffffffffu exceeds UINT_MAX so its type must be at least
 * unsigned long (64-bit on LP64), NOT unsigned int.
 *
 * Repro for the co2cc bug where IntegerSuffix::Unsigned always produced
 * UintTy::U32 regardless of the value.
 *
 * The widening must not be unconditional: a hex literal that still fits in
 * unsigned int keeps type unsigned int. 0xfffffffb (== 2^32 - 5) fits, so
 * sizeof is 4 (not 8); 0x100000000 (== 2^32) does not fit, so it widens. */

#include <stdint.h>

#define trim64(x) ((x) & 0xffffffffffffffffu)

int main(void) {
    /* 0xffffffffffffffffu must equal the 64-bit max, not the 32-bit max. */
    uint64_t lit = 0xffffffffffffffffu;
    if (lit != UINT64_C(0xffffffffffffffff))
        return 1;

    /* trim64 must leave bits above bit 31 intact. */
    uint64_t high = UINT64_C(0xffffffff00000000);
    if (trim64(high) != UINT64_C(0xffffffff00000000))
        return 2;

    /* 2^32 - 5 fits in unsigned int: type is unsigned int (sizeof 4),
     * NOT widened to 64-bit because the value happens to be large. */
    if (sizeof(0xfffffffb) != sizeof(unsigned int))
        return 3;
    if (0xfffffffb != 4294967291u)
        return 4;

    /* 2^32 does not fit in unsigned int: it must widen to unsigned long. */
    if (sizeof(0x100000000u) <= sizeof(unsigned int))
        return 5;

    return 0;
}
