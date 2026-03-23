//@ mode: c
//@ run-status: 0

#include <stdarg.h>

int simple_varargs(int foo, ...) {
    return foo;
}

int implicit_varargs() {
    return 12;
}

struct s7 { char x[7]; } s7 = { "lmnopqr" };

int multiple_types(int normal_arg, ...) {
    if (normal_arg != 5) {
        return 10;
    }

    va_list args;
    va_start(args, normal_arg);

    if (va_arg(args, int) != 1) {
        return 1;
    }

    if (*va_arg(args, int *) != 1) {
        return 2;
    }

    struct s7 s = va_arg(args, struct s7);
    if (s.x[2] != 'n') {
        return 3;
    }

    va_end(args);

    return 0;
}

int main() {
    if (simple_varargs(5, 2, "salam") != 5) {
        return 1;
    }
    if (implicit_varargs(5, 2, "salam") != 12) {
        return 2;
    }
    int p = 1;
    if (multiple_types(5, p, &p, s7)) {
        return 3;
    }


    return 0;
}
