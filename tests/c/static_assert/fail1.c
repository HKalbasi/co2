//@ mode: c
//@ compile-fail

static_assert(0, "0 is not true");
            //^ error: Static assertion failed: 0 is not true

static_assert(2 + 2 == 5, "2 + 2 is not 5");
            //^^^^^^^^^^ error: Static assertion failed: 2 + 2 is not 5

int main() {
    return 0;
}
