//@ mode: c
//@ compile-fail

int f1() {
    static_assert(0, "0 is not true");
                //^ error: Static assertion failed: 0 is not true
}

int f2() {
    static_assert(2 + 2 == 5, "2 + 2 is not 5");
                //^^^^^^^^^^ error: Static assertion failed: 2 + 2 is not 5
}

int main() {
    return 0;
}
