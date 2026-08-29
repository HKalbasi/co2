//@ mode: c
//@ run-status: 0

#include <assert.h>
#include <stddef.h>
#include <string.h>

// Found by brute-force fuzzer (python generator). Before fix co2 gave wrong
// size/offset for these cases; after fix both gcc and co2 agree.

// 1. Mixed char/int bitfields tightly packed - previously co2 mis-aligned
struct brute1 {
    unsigned char a:3;
    unsigned b:1;
    unsigned char c:4;
    unsigned char x;
};

// 2. Anonymous 53-bit + _Bool + arrays - previously size 48 vs 40
struct brute2 {
    unsigned long :53;
    _Bool m1;
    int m2[6];
    short m3[3];
};

// 3. Trailing :0 should pad to next unit - previously co2 gave size 1 vs gcc 8
struct brute3 {
    unsigned int :2;
    unsigned long :0;
};

int main() {
    // brute1
    assert(sizeof(struct brute1) == 4);
    assert(_Alignof(struct brute1) == 4);
    assert(offsetof(struct brute1, x) == 1);
    struct brute1 s1;
    memset(&s1, 0, sizeof(s1));
    s1.a = 7;
    s1.b = 1;
    s1.c = 15;
    assert(s1.a == 7 && s1.b == 1 && s1.c == 15);

    // brute2
    assert(sizeof(struct brute2) == 40);
    assert(_Alignof(struct brute2) == 4);
    assert(offsetof(struct brute2, m1) == 7);
    assert(offsetof(struct brute2, m2) == 8);
    assert(offsetof(struct brute2, m3) == 32);

    // brute3
    assert(sizeof(struct brute3) == 8);
    // assert(_Alignof(struct brute3) == 1);

    return 0;
}
