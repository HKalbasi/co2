//@ mode: c
//@ compile-fail

int f1() {
    int x = 0x;
         // ^^ error: Invalid hexadecimal int literal
}

int f2() {
    double x = 0e;
            // ^^ error: Invalid float literal
}

int f3() {
    char x = '\x';
          // ^^^^ error: Invalid character constant
}

int f4() {
    int x = 0b;
         // ^^ error: Invalid binary int literal
}

int f5() {
    double x = 1e;
            // ^^ error: Invalid float literal
}

int f6() {
    double x = 0x1p;
            // ^^^^ error: Invalid float literal
}

int f7() {
    char x = '\u123';
          // ^^^^^^^ error: Invalid character constant
}

int f8() {
    int x = 0X;
         // ^^ error: Invalid hexadecimal int literal
}

int f9() {
    double x = 1.2e;
            // ^^^^ error: Invalid float literal
}

int f10() {
    double x = 0x.;
            // ^^^ error: Invalid float literal
}

int main() {}
