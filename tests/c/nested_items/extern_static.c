//@ mode: c
//@ run-status: 0
//@ run-stdout: 420\n42\n1

#include <stdio.h>

int g = 420;

int test_libc_extern(void) {
    extern int abs(int);
    return abs(-42);
}

int main(void) {
    extern int g;
    extern int optind;
    printf("%d\n", g);
    printf("%d\n", test_libc_extern());
    printf("%d\n", optind);
    return 0;
}
