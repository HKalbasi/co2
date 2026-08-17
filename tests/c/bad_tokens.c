//@ mode: c
//@ compile-fail

#include <stddef.h>

int f1() {
    int x = 0x;
         // ^^ error: Invalid hexadecimal int literal
}

int f2() {
    double x = 0e;
            // ^^ error: Invalid float literal
}

int f3() {
    int x = 0b;
         // ^^ error: Invalid binary int literal
}

int f4() {
    double x = 1e;
            // ^^ error: Invalid float literal
}

int f5() {
    double x = 0x1p;
            // ^^^^ error: Invalid float literal
}

int f6() {
    int x = 0X;
         // ^^ error: Invalid hexadecimal int literal
}

int f7() {
    double x = 1.2e;
            // ^^^^ error: Invalid float literal
}

int f8() {
    double x = 0x.;
            // ^^^ error: Invalid float literal
}

int f9() {
    wchar_t *p = L"a" u"b";
              // ^^^^^^^^^ error: unsupported concatenation of string literals with different encoding prefixes
}

int main() {
    return 0;
}
