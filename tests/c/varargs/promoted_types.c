//@ mode: c
//@ compile-fail

#include <stdarg.h>

int test_bool(int n, ...) {
    va_list ap;
    va_start(ap, n);
    _Bool x = va_arg(ap, _Bool);
           // ^^^^^^^^^^^^^^^^^ error: second argument to 'va_arg' is not va_arg safe
    va_end(ap);
    return x;
}

int test_char(int n, ...) {
    va_list ap;
    va_start(ap, n);
    char x = va_arg(ap, char);
          // ^^^^^^^^^^^^^^^^ error: second argument to 'va_arg' is not va_arg safe
    va_end(ap);
    return x;
}

int test_schar(int n, ...) {
    va_list ap;
    va_start(ap, n);
    signed char x = va_arg(ap, signed char);
                 // ^^^^^^^^^^^^^^^^^^^^^^^ error: second argument to 'va_arg' is not va_arg safe
    va_end(ap);
    return x;
}

int test_uchar(int n, ...) {
    va_list ap;
    va_start(ap, n);
    unsigned char x = va_arg(ap, unsigned char);
                   // ^^^^^^^^^^^^^^^^^^^^^^^^^ error: second argument to 'va_arg' is not va_arg safe
    va_end(ap);
    return x;
}

int test_short(int n, ...) {
    va_list ap;
    va_start(ap, n);
    short x = va_arg(ap, short);
           // ^^^^^^^^^^^^^^^^^ error: second argument to 'va_arg' is not va_arg safe
    va_end(ap);
    return x;
}

int test_ushort(int n, ...) {
    va_list ap;
    va_start(ap, n);
    unsigned short x = va_arg(ap, unsigned short);
                    // ^^^^^^^^^^^^^^^^^^^^^^^^^^ error: second argument to 'va_arg' is not va_arg safe
    va_end(ap);
    return x;
}

int test_float2(int n, ...) {
    va_list ap;
    va_start(ap, n);
    float x = va_arg(ap, float);
           // ^^^^^^^^^^^^^^^^^ error: second argument to 'va_arg' is not va_arg safe
    va_end(ap);
    return (int)x;
}

int main(void) { return 0; }
