//@ mode: c
//@ run-status: 0
//@ run-stdout: 012345

#include <stdio.h>

int counter() {
    static int x = 0;
    return x++;
}

int main(void) {
    printf("%d", counter());
    printf("%d", counter());
    printf("%d", counter());
    printf("%d", counter());
    printf("%d", counter());
    printf("%d", counter());
    return 0;
}
