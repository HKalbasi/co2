//@ mode: c
//@ compile-fail

int f(int inp) {
    static_assert(inp + 3, "inp + 3 is not true");
                //^^^ error: unsupported identifier in constant expression: Local(0)
}

int main() {
    return 0;
}
