//@ mode: c
//@ compile-fail

#include <stdio.h>

int main() {
  int *p;
  long *q;
  int x = 1;
  long y = 2;

  p = &x;
  q = &y;

  void *result = 1 ? p : q;
//               ^^^^^^^^^ error: ternary operator branches have mismatched types: expected *mut i32, got *mut i64

  return 0;
}
