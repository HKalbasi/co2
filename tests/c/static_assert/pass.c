//@ mode: c
//@ run-status: 0

static_assert(1, "1 is true");
_Static_assert(2 + 2 == 4, "2 + 2 is 4");

int main() {
    static_assert(2 + 2 == 4, "2 + 2 is 4");
    return 0;
}
