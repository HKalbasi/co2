//@ mode: c
//@ run-status: 0

/* Compound assignment and increment/decrement on small integer types must
 * keep the destination as a place and still produce the correct wrapped
 * result after converting the promoted computation back to the target type. */

int main(void) {
    unsigned char a = 200;

    a += a;                 /* 200 + 200 = 400 -> (u8)400 = 144 */
    if (a != 144) return 1;

    a = 255;
    a += 1;                 /* 256 -> 0 */
    if (a != 0) return 2;

    a = 200;
    a++;                    /* 201 */
    if (a != 201) return 3;
    a--;                    /* 200 */
    if (a != 200) return 4;

    a = 200;
    a <<= 1;                /* 400 -> 144 */
    if (a != 144) return 5;

    a = 200;
    a *= 2;                 /* 400 -> 144 */
    if (a != 144) return 6;

    signed char sc = -5;
    sc += 3;
    if (sc != -2) return 7;

    short s = 30000;
    s += 1;
    if (s != 30001) return 8;

    return 0;
}
