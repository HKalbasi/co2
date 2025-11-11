#include "test.h"

struct Foo {
  int a;
  int b;
};

int main() {
  ASSERT(1, ({ struct Foo x; x.a=1; x.b=2; x.a; }));
  return 0;
}