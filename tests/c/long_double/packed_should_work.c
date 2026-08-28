//@ mode: c
//@ run-status: 0
//@ run-stdout: 123.412000 5

#include <stdio.h>

int main() {
    struct { long double x; unsigned char y:4; } __attribute__((packed)) t6 = {123.412, 5};
    printf("%f %d\n", (double)t6.x, t6.y);
    return 0;
}
