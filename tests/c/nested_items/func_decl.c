//@ mode: c
//@ run-status: 0
//@ run-stdout: 420\n42

#include <stdio.h>

int test_libc(void) {
    int abs(int);
    return abs(-420);
}

int test_libc_extern(void) {
    extern int abs(int);
    return abs(-42);
}

int main(void) {
    printf("%d\n", test_libc());
    printf("%d\n", test_libc_extern());
    return 0;
}
