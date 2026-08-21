//@ mode: c
//@ run-status: 0

/* ================================================================
 * 1. Basic __LINE__
 * ================================================================ */

#line 100
_Static_assert(__LINE__ == 100, "basic");


/* ================================================================
 * 2. Consecutive lines
 * ================================================================ */

#line 200
_Static_assert(__LINE__ == 200, "200");
_Static_assert(__LINE__ == 201, "201");
_Static_assert(__LINE__ == 202, "202");


/* ================================================================
 * 3. Macro expansion uses invocation location
 * ================================================================ */

#define GET_LINE __LINE__

#line 300
_Static_assert(GET_LINE == 300, "macro invocation");


/* ================================================================
 * 4. Function-like macro
 * ================================================================ */

#define GET_LINE_FN() __LINE__

#line 400
_Static_assert(GET_LINE_FN() == 400, "function macro");


/* ================================================================
 * 5. Multiple expansion layers
 * ================================================================ */

#define L1 __LINE__
#define L2 L1
#define L3 L2
#define L4 L3

#line 500
_Static_assert(L4 == 500, "nested expansion");


/* ================================================================
 * 6. Argument expansion
 * ================================================================ */

#define ID(x) x

#line 600
_Static_assert(ID(__LINE__) == 600, "argument expansion");


/* ================================================================
 * 7. Stringification
 * ================================================================ */

#define STR_RAW(x) #x
#define STR(x) STR_RAW(x)

#line 700
_Static_assert(sizeof(STR(__LINE__)) == 4,
               "stringified line 700");

#line 9999
_Static_assert(sizeof(STR(__LINE__)) == 5,
               "stringified line 9999");


/* ================================================================
 * 8. Token pasting
 * ================================================================ */

#define CAT_RAW(a, b) a##b
#define CAT(a, b) CAT_RAW(a, b)
#define LINE_NAME(x) CAT(line_, x)

#define line_10000 123

#line 10000
_Static_assert(LINE_NAME(__LINE__) == 123,
               "line token paste");


/* ================================================================
 * 9. Token pasting through more expansion layers
 * ================================================================ */

#define X1(x) LINE_NAME(x)
#define X2(x) X1(x)
#define X3(x) X2(x)

#define line_11000 456

#line 11000
_Static_assert(X3(__LINE__) == 456,
               "deep line token paste");


/* ================================================================
 * 10. Same __LINE__ twice on same source line
 * ================================================================ */

#define FIRST(a, b) a
#define SECOND(a, b) b

#line 12000
_Static_assert(FIRST(__LINE__, __LINE__) == 12000,
               "first same-line expansion");

#line 12001
_Static_assert(SECOND(__LINE__, __LINE__) == 12001,
               "second same-line expansion");


/* ================================================================
 * 11. __LINE__ inside a multiline macro invocation
 * ================================================================ */

#define ID2(x) x

#line 13000
_Static_assert(
    ID2(__LINE__) == 13001,
    "line inside multiline invocation"
);


/* ================================================================
 * 12. Backslash-newline
 * ================================================================ */

#line 14000
_Static_assert(__LINE__ \
               == 14000,
               "spliced line");


/* ================================================================
 * 13. Macro definition split over physical lines
 * ================================================================ */

#define MULTILINE \
    __LINE__

#line 15000
_Static_assert(MULTILINE == 15000,
               "multiline macro");


/* ================================================================
 * 14. Macro defined before #line, expanded after it
 * ================================================================ */

#define DYNAMIC_LINE __LINE__

#line 16000
_Static_assert(DYNAMIC_LINE == 16000,
               "dynamic line");


#line 17000
_Static_assert(DYNAMIC_LINE == 17000,
               "dynamic line again");


/* ================================================================
 * 15. Several calls to same macro at known locations
 * ================================================================ */

#define HERE() __LINE__

#line 18000
_Static_assert(HERE() == 18000, "here 18000");
_Static_assert(HERE() == 18001, "here 18001");

#line 19000
_Static_assert(HERE() == 19000, "here 19000");


/* ================================================================
 * 16. __LINE__ in #if
 * ================================================================ */

#line 20000
#if __LINE__ != 20000
#error "__LINE__ in #if broken"
#endif

#line 20010
#if __LINE__ != 20010
#error "__LINE__ in second #if broken"
#endif


/* ================================================================
 * 17. Conditional nesting
 * ================================================================ */

#line 21000
#if 1
# if __LINE__ != 21001
# error "nested #if line broken"
# endif
#endif


/* ================================================================
 * 18. #line changes repeatedly
 * ================================================================ */

#line 30000
_Static_assert(__LINE__ == 30000, "30000");

#line 1
_Static_assert(__LINE__ == 1, "1");

#line 500000
_Static_assert(__LINE__ == 500000, "500000");

#line 42
_Static_assert(__LINE__ == 42, "42");


/* ================================================================
 * 19. Large value
 * ================================================================ */

#line 2147483647
_Static_assert(__LINE__ == 2147483647,
               "maximum 32-bit signed line");

int main() {
    return 0;
}
