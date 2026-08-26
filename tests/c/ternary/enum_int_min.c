//@ mode: c
//@ run-status: 0

#include <stdio.h>
#include <limits.h>
#include <stdlib.h>

enum e { a = INT_MIN };
int *p;
enum e *q;

int main() {
  enum e x = a;
  q = &x;
  if (*(1 ? q : p) > 0) abort();
  return 0;
}
