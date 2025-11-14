#include <stdio.h>

void foo1(int a, int b) {
    int x = a && a || b;
    int y = a && a | b;
    printf("%d %d\n", x, y);
}

void foo2(int a, int b) {
    int x = a && b || b;
    int y = a && b | b;
    printf("%d %d\n", x, y);
}

int main() {
    printf("foo1\n");
    foo1(0, 0);
    foo1(0, 1);
    foo1(1, 0);
    foo1(1, 1);
    printf("foo2\n");
    foo2(0, 0);
    foo2(0, 1);
    foo2(1, 0);
    foo2(1, 1);
}