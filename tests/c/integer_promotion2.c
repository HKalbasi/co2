//@ mode: c
//@ run-status: 0

/* C11 6.3.1.1p2 integer promotion: char/short and their unsigned siblings
 * promote to `int` when used in arithmetic, bitwise, shift or comparison
 * contexts, so the operation happens in `int`, not in the 8/16-bit type. */

int main(void) {
    unsigned char a = 200, b = 100;

    int sub = b - a;    /* 100 - 200 = -100, not 156 */
    int sum = a + a;    /* 200 + 200 = 400, not 144 */
    int prod = a * b;   /* 200 * 100 = 20000, not 32 */

    if (sub != -100) return 1;
    if (sum != 400) return 2;
    if (prod != 20000) return 3;

    if (sizeof(a + a) != sizeof(int)) return 4;       /* result is int, not u8 */
    if (sizeof(-a) != sizeof(int)) return 5;

    signed char sc = -5;
    if (sc + 1 != -4) return 6;
    if (-sc != 5) return 7;
    if (~sc != 4) return 8;

    short s = 30000;
    if (s + 1 != 30001) return 9;
    if (s * 2 != 60000) return 10;
    if (-s != -30000) return 11;

    unsigned short us = 60000;
    if (us + 1 != 60001) return 12;
    if (~us != -60001) return 13;

    /* shifts: the left operand is promoted to int */
    if (a << 1 != 400) return 14;
    if (a >> 1 != 100) return 15;
    if (a << 8 != 51200) return 16;

    /* comparisons happen in the promoted type */
    if ((b < a) != 1) return 17;
    if ((a == b) != 0) return 18;
    if ((a < sc) != 0) return 19;

    /* mixed small/int arithmetic */
    if (a + 1 != 201) return 20;
    if (b - 1 != 99) return 21;
    if ((a & 0xffff) != 200) return 22;

    char ch = 'A';
    if (ch + 1 != 'B') return 23;
    if (ch == 'A') { } else return 24;
    if ((ch > 'a') != 0) return 25;

    return 0;
}
