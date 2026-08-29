//@ mode: c
//@ compile-fail

void f1(int* a, int* b) {
    a + b;
  //^^^^^ error: type error: adding two pointers is invalid
}

void f2(int* a, int* b) {
    a[b];
  //^^^^ error: type error: adding two pointers is invalid
}

void f3(int a, int b) {
    a[b];
  //^^^^ error: subscript requires one pointer and one integer operand
}

void f4(int* a, long* b) {
    a - b;
  //^^^^^ error: type error: subtracting pointers of incompatible type `i32` and `i64` is invalid
}

void f5(int* a, void* b) {
    a - b;
  //^^^^^ error: type error: subtracting pointers of incompatible type `i32` and `()` is invalid
}

int main() {
    return 0;
}
