//@ mode: c
//@ run-status: 0

/* C99 §6.4.4.1p5: the type of an unsuffixed integer constant is the first
 * of the candidate list in which its value fits.
 *
 * For a decimal constant the list is {int, long, long long} -- signed
 * types only -- so 2147483648 and 4294967291 (both > INT_MAX) have type
 * long, NOT unsigned int.
 *
 * Octal and hexadecimal constants may also pick unsigned types, so the same
 * values written in hex, 0x80000000 and 0xfffffffb, are unsigned int
 * (4 bytes on LP64).
 *
 * Regression for the co2 bug where the decimal-vs-hex distinction was lost
 * and an unsuffixed decimal literal like 4294967291 (2^32 - 5) was typed
 * as unsigned int (sizeof 4) instead of long (sizeof 8). */

int main(void) {
    /* values that fit in int are int regardless of radix */
    if (sizeof(2147483647) != sizeof(int))
        return 1;
    if (sizeof(0x7fffffff) != sizeof(int))
        return 2;

    /* decimal constants only consider signed types: these exceed INT_MAX,
     * so they become long (8 bytes), not unsigned int (4 bytes) */
    if (sizeof(2147483648) != sizeof(long))
        return 3;
    if (sizeof(4294967291) != sizeof(long))
        return 4;
    if (sizeof(4294967295) != sizeof(long))
        return 5;

    /* the same values written in hex fit in unsigned int and stay 32-bit */
    if (sizeof(0x80000000) != sizeof(unsigned int))
        return 6;
    if (sizeof(0xfffffffb) != sizeof(unsigned int))
        return 7;

    /* the two spellings of 2^32 - 5 must compare equal */
    if (4294967291 != 0xfffffffb)
        return 8;
    if (4294967295 != 0xffffffffu)
        return 9;

    /* _Generic sees the decimal constant as a signed 64-bit type */
    if (_Generic(4294967291, long: 0, unsigned int: 1, unsigned long: 2, default: 3) != 0)
        return 10;

    return 0;
}
