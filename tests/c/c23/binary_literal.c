//@ mode: c
//@ run-status: 0

#include <stdint.h>
#include <limits.h>

/*
 * ============================================================
 * C23 binary integer constant torture test
 *
 * Every test should compile successfully.
 * main() must return 0.
 * ============================================================
 */

/* ------------------------------------------------------------
 * 1. Basic binary literals
 * ------------------------------------------------------------ */

_Static_assert(0b0 == 0);
_Static_assert(0b1 == 1);
_Static_assert(0b10 == 2);
_Static_assert(0b11 == 3);
_Static_assert(0b100 == 4);
_Static_assert(0b101 == 5);
_Static_assert(0b110 == 6);
_Static_assert(0b111 == 7);
_Static_assert(0b1000 == 8);
_Static_assert(0b1001 == 9);
_Static_assert(0b1010 == 10);
_Static_assert(0b1011 == 11);
_Static_assert(0b1100 == 12);
_Static_assert(0b1101 == 13);
_Static_assert(0b1110 == 14);
_Static_assert(0b1111 == 15);

/* ------------------------------------------------------------
 * 2. Larger binary values
 * ------------------------------------------------------------ */

_Static_assert(0b10000 == 16);
_Static_assert(0b100000 == 32);
_Static_assert(0b1000000 == 64);
_Static_assert(0b10000000 == 128);

_Static_assert(0b100000000 == 256);
_Static_assert(0b1000000000 == 512);
_Static_assert(0b10000000000 == 1024);

_Static_assert(0b11111111 == 255);
_Static_assert(0b111111111 == 511);
_Static_assert(0b1111111111 == 1023);

/* ------------------------------------------------------------
 * 3. Leading zeroes
 * ------------------------------------------------------------ */

_Static_assert(0b0000 == 0);
_Static_assert(0b0001 == 1);
_Static_assert(0b0010 == 2);
_Static_assert(0b0011 == 3);
_Static_assert(0b0101 == 5);
_Static_assert(0b1001 == 9);
_Static_assert(0b00001001 == 9);
_Static_assert(0b000000001001 == 9);

/* ------------------------------------------------------------
 * 4. Uppercase 0B prefix
 * ------------------------------------------------------------ */

_Static_assert(0B0 == 0);
_Static_assert(0B1 == 1);
_Static_assert(0B10 == 2);
_Static_assert(0B1010 == 10);
_Static_assert(0B11111111 == 255);
_Static_assert(0B100000000 == 256);

/* ------------------------------------------------------------
 * 5. Arithmetic
 * ------------------------------------------------------------ */

_Static_assert(0b101 + 0b11 == 8);
_Static_assert(0b1000 - 0b11 == 5);
_Static_assert(0b101 * 0b11 == 15);
_Static_assert(0b10000 / 0b10 == 8);
_Static_assert(0b10000 % 0b11 == 1);

_Static_assert(0b1010 + 0b0101 == 0b1111);
_Static_assert(0b1111 - 0b0111 == 0b1000);

/* ------------------------------------------------------------
 * 6. Unary operators
 * ------------------------------------------------------------ */

_Static_assert(+0b1010 == 10);
_Static_assert(-0b1010 == -10);

_Static_assert(!0b0);
_Static_assert(!0b0000);

_Static_assert(!!0b1);
_Static_assert(!!0b1010);

/* ------------------------------------------------------------
 * 7. Comparisons
 * ------------------------------------------------------------ */

_Static_assert(0b1001 == 9);
_Static_assert(0b1001 != 10);

_Static_assert(0b1010 > 0b1001);
_Static_assert(0b1001 < 0b1010);

_Static_assert(0b1010 >= 0b1010);
_Static_assert(0b1001 <= 0b1010);

/* ------------------------------------------------------------
 * 8. Bitwise AND
 * ------------------------------------------------------------ */

_Static_assert((0b1111 & 0b1010) == 0b1010);
_Static_assert((0b1111 & 0b0101) == 0b0101);
_Static_assert((0b1010 & 0b0101) == 0);
_Static_assert((0b1100 & 0b1010) == 0b1000);

/* ------------------------------------------------------------
 * 9. Bitwise OR
 * ------------------------------------------------------------ */

_Static_assert((0b0001 | 0b0010) == 0b0011);
_Static_assert((0b1010 | 0b0101) == 0b1111);
_Static_assert((0b1100 | 0b0011) == 0b1111);

/* ------------------------------------------------------------
 * 10. Bitwise XOR
 * ------------------------------------------------------------ */

_Static_assert((0b1111 ^ 0b1010) == 0b0101);
_Static_assert((0b1010 ^ 0b0101) == 0b1111);
_Static_assert((0b1111 ^ 0b1111) == 0);

/* ------------------------------------------------------------
 * 11. Bitwise NOT
 * ------------------------------------------------------------ */

_Static_assert((~0b0) == UINT_MAX);
_Static_assert((~0b1) == UINT_MAX - 1);

/* ------------------------------------------------------------
 * 12. Left shifts
 * ------------------------------------------------------------ */

_Static_assert((0b1 << 0) == 0b1);
_Static_assert((0b1 << 1) == 0b10);
_Static_assert((0b1 << 2) == 0b100);
_Static_assert((0b1 << 3) == 0b1000);
_Static_assert((0b1 << 4) == 0b10000);
_Static_assert((0b1 << 8) == 0b100000000);

_Static_assert((0b101 << 1) == 0b1010);
_Static_assert((0b101 << 2) == 0b10100);

/* ------------------------------------------------------------
 * 13. Right shifts
 * ------------------------------------------------------------ */

_Static_assert((0b10 >> 1) == 0b1);
_Static_assert((0b100 >> 2) == 0b1);
_Static_assert((0b1000 >> 3) == 0b1);
_Static_assert((0b10000 >> 4) == 0b1);

_Static_assert((0b1010 >> 1) == 0b101);
_Static_assert((0b10100 >> 2) == 0b101);

/* ------------------------------------------------------------
 * 14. Complex bit expressions
 * ------------------------------------------------------------ */

_Static_assert(
    ((0b10101010 & 0b11110000) >> 4) == 0b1010
);

_Static_assert(
    ((0b00001111 | 0b11110000) == 0b11111111)
);

_Static_assert(
    ((0b11111111 ^ 0b10101010) == 0b01010101)
);

/* ------------------------------------------------------------
 * 15. Operator precedence
 * ------------------------------------------------------------ */

_Static_assert(0b10 + 0b11 * 0b10 == 8);
_Static_assert((0b10 + 0b11) * 0b10 == 10);

_Static_assert(0b1111 & 0b1010 == 0b1010);
_Static_assert((0b1111 & 0b1010) == 0b1010);

_Static_assert(0b1 << 4 + 1 == 0b100000);
_Static_assert(0b1 << (4 + 1) == 0b100000);

/* ------------------------------------------------------------
 * 16. Conditional operator
 * ------------------------------------------------------------ */

_Static_assert((1 ? 0b1010 : 0b0101) == 0b1010);
_Static_assert((0 ? 0b1010 : 0b0101) == 0b0101);

_Static_assert(
    (0b1010 > 0b1000 ? 0b1111 : 0b0000) == 0b1111
);

/* ------------------------------------------------------------
 * 17. Logical operators
 * ------------------------------------------------------------ */

_Static_assert(0b1 && 0b1);
_Static_assert(0b1 && 0b1010);
_Static_assert(0b0 || 0b1);
_Static_assert(0b0 || 0b1010);

_Static_assert(!(0b0));
_Static_assert(!(0b0 == 0b1));

_Static_assert(
    (0b1010 > 0b1000) &&
    (0b1111 > 0b1100)
);

/* ------------------------------------------------------------
 * 18. Binary literals with integer suffixes
 * ------------------------------------------------------------ */

_Static_assert(0b1010U == 10U);
_Static_assert(0b1010L == 10L);
_Static_assert(0b1010UL == 10UL);
_Static_assert(0b1010LL == 10LL);
_Static_assert(0b1010ULL == 10ULL);

/* ------------------------------------------------------------
 * 19. Different suffix combinations
 * ------------------------------------------------------------ */

_Static_assert(0b11111111U == 255U);
_Static_assert(0b11111111UL == 255UL);
_Static_assert(0b11111111ULL == 255ULL);

_Static_assert(0b100000000ULL == 256ULL);

/* ------------------------------------------------------------
 * 20. Integer type conversions
 * ------------------------------------------------------------ */

_Static_assert((int)0b1010 == 10);
_Static_assert((unsigned)0b1010 == 10U);
_Static_assert((long)0b1010 == 10L);
_Static_assert((long long)0b1010 == 10LL);

_Static_assert((uint8_t)0b11111111 == 255);
_Static_assert((uint16_t)0b1111111111111111 == 65535);

/* ------------------------------------------------------------
 * 21. Enum constants
 * ------------------------------------------------------------ */

enum {
    FLAG_A = 0b0001,
    FLAG_B = 0b0010,
    FLAG_C = 0b0100,
    FLAG_D = 0b1000
};

_Static_assert(FLAG_A == 1);
_Static_assert(FLAG_B == 2);
_Static_assert(FLAG_C == 4);
_Static_assert(FLAG_D == 8);

_Static_assert(
    (FLAG_A | FLAG_B | FLAG_C | FLAG_D) == 0b1111
);

/* ------------------------------------------------------------
 * 22. Macros containing binary literals
 * ------------------------------------------------------------ */

#define BIT0 0b00000001
#define BIT1 0b00000010
#define BIT2 0b00000100
#define BIT3 0b00001000

#define NIBBLE 0b1111
#define BYTE   0b11111111

_Static_assert(BIT0 == 1);
_Static_assert(BIT1 == 2);
_Static_assert(BIT2 == 4);
_Static_assert(BIT3 == 8);

_Static_assert((BIT0 | BIT1 | BIT2 | BIT3) == 0b1111);

_Static_assert(NIBBLE == 15);
_Static_assert(BYTE == 255);

/* ------------------------------------------------------------
 * 23. Array sizes
 * ------------------------------------------------------------ */

char array1[0b1001];
char array2[0b10000];
char array3[0b100000];

_Static_assert(sizeof(array1) == 9);
_Static_assert(sizeof(array2) == 16);
_Static_assert(sizeof(array3) == 32);

/* ------------------------------------------------------------
 * 24. Binary literals and sizeof
 * ------------------------------------------------------------ */

_Static_assert(sizeof(char[0b1001]) == 9);
_Static_assert(sizeof(int[0b1010]) == 10 * sizeof(int));

/* ------------------------------------------------------------
 * 25. Hexadecimal/octal/decimal equivalence
 * ------------------------------------------------------------ */

_Static_assert(0b1001 == 9);
_Static_assert(0b1001 == 011);
_Static_assert(0b1001 == 0x9);

_Static_assert(0b11111111 == 255);
_Static_assert(0b11111111 == 0377);
_Static_assert(0b11111111 == 0xff);

_Static_assert(0b10101010 == 170);
_Static_assert(0b10101010 == 0252);
_Static_assert(0b10101010 == 0xaa);

/* ------------------------------------------------------------
 * 26. Long binary patterns
 * ------------------------------------------------------------ */

_Static_assert(
    0b1010101010101010 == 0xAAAA
);

_Static_assert(
    0b0101010101010101 == 0x5555
);

_Static_assert(
    0b1111000011110000 == 0xF0F0
);

_Static_assert(
    0b0000111100001111 == 0x0F0F
);

/* ------------------------------------------------------------
 * 27. 32-bit patterns
 * ------------------------------------------------------------ */

_Static_assert(
    0b11111111111111111111111111111111u
    == UINT32_MAX
);

/* ------------------------------------------------------------
 * 28. Compound expressions
 * ------------------------------------------------------------ */

_Static_assert(
    ((0b1010 << 4) | 0b0101) == 0b10100101
);

_Static_assert(
    ((0b11110000 >> 4) & 0b1111) == 0b1111
);

_Static_assert(
    (((0b1010 ^ 0b1100) & 0b1111) == 0b0110)
);

/* ------------------------------------------------------------
 * 29. Binary literals in switch/case
 * ------------------------------------------------------------ */

static int test_switch(int value)
{
    switch (value) {
    case 0b0001:
        return 1;

    case 0b0010:
        return 2;

    case 0b0100:
        return 4;

    case 0b1000:
        return 8;

    default:
        return -1;
    }
}

/* ------------------------------------------------------------
 * 30. Binary literals in runtime expressions
 * ------------------------------------------------------------ */

int main(void)
{
    if (0b1001 != 9)
        return 1;

    if (0B1001 != 9)
        return 2;

    if (0b1010 + 0b0101 != 0b1111)
        return 3;

    if ((0b11110000 & 0b10101010) != 0b10100000)
        return 4;

    if ((0b00001111 | 0b10100000) != 0b10101111)
        return 5;

    if ((0b11111111 ^ 0b10101010) != 0b01010101)
        return 6;

    if ((0b1 << 8) != 0b100000000)
        return 7;

    if ((0b100000000 >> 4) != 0b10000)
        return 8;

    if (test_switch(0b0001) != 1)
        return 9;

    if (test_switch(0b0010) != 2)
        return 10;

    if (test_switch(0b0100) != 4)
        return 11;

    if (test_switch(0b1000) != 8)
        return 12;

    return 0;
}
