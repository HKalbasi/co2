//@ mode: c
//@ compile-fail

int f1() {
    return;
  //^^^^^^^ error: `return;` is not valid for functions returning value i32
}

int main() {
    return 0;
}
