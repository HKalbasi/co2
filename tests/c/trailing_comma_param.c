//@ mode: c
//@ compile-fail

// Trailing comma in a parameter list is rejected, like gcc.
// (Top-level decl indented by 2 so the `//^^^` annotation can address it.)

  int f(int,) {
//^^^ error: found 'int' expected ';'
    return 42;
}

int main() {
    return 0;
}
