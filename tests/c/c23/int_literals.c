//@ mode: c
//@ run-status: 0

#include <assert.h>

#define ASSERT_LIT_TYPE(lit, ty) { auto a = (lit); assert(_Generic(a, ty: 1, default: 0)); }

int main() {
    ASSERT_LIT_TYPE(123, int);
    ASSERT_LIT_TYPE(123l, long int);
    ASSERT_LIT_TYPE(123ll, long long);
    ASSERT_LIT_TYPE(120'000, int);
    ASSERT_LIT_TYPE(123'000'000'000, long int);
    ASSERT_LIT_TYPE(123'222ll, long long int);
    ASSERT_LIT_TYPE(123'000'000ul, unsigned long);
    return 0;
}
