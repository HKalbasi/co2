#include <assert.h>
#include <stdio.h>

/*
 * This file demonstrates many corner cases of C initializer lists.
 * Each block uses assertions to show what the compiler produces.
 * Comments explain the rules minimally.
 */

/* 1. Scalar initialization: the first value initializes, extras are an error.
 */
int scalar = {42}; /* braces allowed for scalar */

/* 2. Array with complete size inferred. */
int arr1[] = {1, 2, 3}; /* size is 3 */

/* 3. Array with explicit size, fewer initializers -> rest zero. */
int arr2[5] = {1, 2}; /* remaining: 0,0,0 */

/* 4. Array with designated initializers. */
int arr3[5] = {[2] = 10, [4] = 20}; /* non-designated zero */

/* 5. Mixing designated and non-designated. Order follows initialization rules.
 */
int arr4[6] = {
    1, [3] = 7,
    9}; /* last '9' goes to next index after last explicit non-designated */

/* 6. String literal initializes array of char. */
char s1[] = "hi";  /* size 3 incl. null */
char s2[5] = "hi"; /* padded with zeros */

/* 7. Too long literal for fixed array is an error, so avoid. */

/* 8. Struct initialization by order. */
struct S {
  int a;
  int b;
  int c;
} sA = {1, 2, 3};

/* 9. Struct designated initialization. */
struct S sB = {.c = 5, .a = 1}; /* missing b -> zero */

/* 10. Nested struct initialization. */
struct T {
  struct S s;
  int x;
} tA = {{9, 8, 7}, 4};

struct T tA2 = {.s.b = 9, 8, 7, 4};

struct T2 {
  struct S s;
  int x;
  struct T s2;
};

int x[] = {1, 2, 3, [10] = 5, 4, 6, 2, [12] = 3, 4, 5, 6};

struct T2 t3[] = {[0].s.b = 9, 8, 7, {2, 5}, [1] = {2}, 5, 3, 4, {5}};

struct T3 {
  int x[5];
  struct T s2;
};

struct T3 t4[] = {
    1, 2, 1, 1, 1, 1, 1,
};

/* 11. Nested with designators. */
struct T tB = {.s = {.b = 20}, .x = 3}; /* s.a=0,s.b=20,s.c=0,x=3 */

/* 12. Union initialization uses first named member unless designated. */
union U {
  int i;
  float f;
} uA = {99}; /* initializes i */

union U uB = {.f = 3.14f}; /* initializes f */

/* 13. Array of structs with mixed designators. */
struct S arrS[3] = {
    [1] = {.b = 10}, /* s: a=0,b=10,c=0 */
    {1, 2, 3}        /* goes to index 2 */
};

/* 14. Multidimensional arrays. */
int md1[2][3] = {
    {1, 2, 3}, {4} /* rest zero */
};

/* 15. Flattening rule: nested braces optional for inner arrays. */
int md2[2][3] = {1, 2, 3, 4}; /* row-major */

/* 16. Designated in multidimensional. */
int md3[2][3] = {[1][2] = 42};

int main(void) {
  assert(scalar == 42);

  assert(arr1[0] == 1 && arr1[2] == 3);

  assert(arr2[0] == 1 && arr2[1] == 2 && arr2[2] == 0 && arr2[4] == 0);

  assert(arr3[0] == 0 && arr3[2] == 10 && arr3[4] == 20);

  /* arr4: index 0=1,1=0,2=0,3=7,4=9,5=0 */
  assert(arr4[0] == 1 && arr4[3] == 7 && arr4[4] == 9);

  assert(s1[0] == 'h' && s1[1] == 'i' && s1[2] == '\0');
  assert(s2[3] == '\0');

  assert(sA.a == 1 && sA.b == 2 && sA.c == 3);
  assert(sB.a == 1 && sB.b == 0 && sB.c == 5);

  assert(tA.s.a == 9 && tA.s.c == 7 && tA.x == 4);
  assert(tB.s.b == 20 && tB.x == 3);

  assert(uA.i == 99);
  /* reading uB.f is valid, but reading uB.i would be type-punned */
  assert(uB.f > 3.1f && uB.f < 3.2f);

  assert(arrS[1].b == 10);
  assert(arrS[2].c == 3);

  assert(md1[1][1] == 0);

  assert(md2[0][0] == 1 && md2[1][0] == 4);

  assert(md3[1][2] == 42);

  printf("All initializer cases passed.\n");
  return 0;
}
