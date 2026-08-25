//@ mode: c
//@ run-status: 0

#include <stddef.h>
#include <assert.h>
#include <string.h>

// 1. Array initializer: insert a comma only when arguments exist.
#define ARRAY_WITH_OPT(...) (int[]){ 0 __VA_OPT__(,) __VA_ARGS__ }
#define ARRAY_SIZE(...)     (sizeof(ARRAY_WITH_OPT(__VA_ARGS__)) / sizeof(int))

// 2. Comma operator: last element is returned.
#define LAST(x, ...) (x __VA_OPT__(,) __VA_ARGS__)

// 3. Detect presence of arguments: adds +1 if any arg exists.
#define HAS_ARGS(...) (0 __VA_OPT__(+ 1))

// 4. Nested __VA_OPT__: inner macro adds +1 for each non‑empty argument.
#define INNER(...) (1 __VA_OPT__(+ 1))
#define OUTER(x, ...) (x __VA_OPT__(+ INNER(__VA_ARGS__)))

// 5. Multiple independent __VA_OPT__ instances.
#define MULTI_OPT(...) (0 __VA_OPT__(+ 1) __VA_OPT__(+ 2))

// 6. __VA_OPT__ containing a comma expression as its whole argument.
//    When args exist, we get (0 , (1,2)) → 2; otherwise (0) → 0.
#define COMMA_EXPR(...) (0 __VA_OPT__(,) __VA_ARGS__)

// 7. __VA_OPT__ with a comma inside its own content (not as separator).
//    Here the comma is inside the parentheses of the expansion.
#define COMMA_INSIDE(...) (0 __VA_OPT__(+ (1,2)))
//    When args exist: (0 + (1,2)) → (0 + 2) → 2; otherwise (0) → 0.

// 8. Empty __VA_OPT__() parens and blank-only variable arguments.
#define OPT_EMPTY(...) (1 __VA_OPT__())
#define SUPPRESS(...)  (0 __VA_OPT__(+ 1))

// 9. Arguments that expand to nothing do not make the variable arguments
//    non-empty: C23 6.10.5.2 judges emptiness after macro expansion.
#define EMPTY_ARG

// 10. Trailing comma in an initializer list via __VA_OPT__(,).
#define TRAIL(...) (int[]){ 0 __VA_OPT__(,) }

// 11. __VA_OPT__ content referencing named parameters.
#define USE_PARAM(x, ...) (0 __VA_OPT__(+ (x)))

// 12. Stringification inside __VA_OPT__ content.
#define OPT_STR(x, ...) __VA_OPT__(#x "=" #__VA_ARGS__)

// 13. __VA_OPT__ as an operand of ##.
//     Non-empty: paste uses its last (left) / first (right) token.
//     Empty: behaves like a placemarker, neighbors are not glued together.
#define PASTE_R(a, ...) a ## __VA_OPT__(b)
#define PASTE_L(a, ...) __VA_OPT__(p) ## q

// 14. ## with multi-token __VA_OPT__ content pastes only the first token.
#define PASTE_FIRST(a, ...) a ## __VA_OPT__(signed)

// 15. Deferred function-like call connected through __VA_OPT__ output.
#define FN(v) ((v) * 11)
#define MAYBE_FN(...) __VA_OPT__(FN)

// 16. __VA_OPT__ evaluated while macro-expanding arguments of another macro.
#define INNER_SUM(...) (0 __VA_OPT__(+ 100))
#define APPLY(...) __VA_ARGS__

// 17. Token paste (##) inside __VA_OPT__ content.
#define OPT_PASTE(...) __VA_OPT__(ab ## cd)

// 18. __VA_ARGS__ referenced inside __VA_OPT__ content.
#define JOINARGS(...) \
    (0 __VA_OPT__(+ (int)(sizeof((int[]){__VA_ARGS__}) / sizeof(int))))

// 19. Nested macro invocations inside __VA_OPT__ content, including a
//     nested variadic macro that uses __VA_OPT__ itself.
#define SUM3(a, b, c) ((a) + (b) + (c))
#define CALLSUM(...) __VA_OPT__(SUM3(__VA_ARGS__))
#define DEEP2(...) (5 __VA_OPT__(+ 1))
#define DEEP(...) __VA_OPT__(DEEP2(__VA_ARGS__))

// 20. Paren-like characters inside string/char literals in __VA_OPT__
//     content must not confuse __VA_OPT__ argument collection.
#define STR_PAREN(...) __VA_OPT__(strcmp(")", "(") == 0)
#define CHR_PAREN(...) __VA_OPT__('(' ? 3 : 0)

// 21. Adjacent __VA_OPT__ instances with no separating whitespace.
#define ADJACENT(...) (0 __VA_OPT__(+ 1)__VA_OPT__(+ 2))

// 22. __VA_OPT__ absence/presence must leave a well-formed expression.
#define TIGHT(...) (x_ __VA_OPT__(+ y))

// 23. __VA_OPT__ content spanning a backslash-newline continuation.
#define SPAN(...) (0 __VA_OPT__( \
    + 1))

// 24. __VA_OPT__ as the entire replacement list.
#define ONLY(...) __VA_OPT__(77)

// 25. __VA_OPT__ reached through an object-like macro.
#define OBJ_RELAY CALLSUM(9, 8, 7)

// 26. __VA_OPT__ output feeding another variadic macro's arguments.
#define RELAY_VA(...) APPLY(__VA_OPT__(INNER_SUM(k)))

int main(void) {
    // ---- Array size (comma insertion) ----
    assert(ARRAY_SIZE() == 1);
    assert(ARRAY_SIZE(5) == 2);
    assert(ARRAY_SIZE(5, 6) == 3);
    assert(ARRAY_SIZE(5, 6, 7) == 4);

    // ---- Comma operator with LAST ----
    assert(LAST(5) == 5);
    assert(LAST(5, 6) == 6);
    assert(LAST(5, 6, 7) == 7);
    assert(LAST(5, 6, 7, 8) == 8);

    // ---- Presence detection ----
    assert(HAS_ARGS() == 0);
    assert(HAS_ARGS(1) == 1);
    assert(HAS_ARGS(1, 2) == 1);

    // ---- Nested __VA_OPT__ ----
    assert(OUTER(0) == 0);          // no args → (0)
    assert(OUTER(0, 1) == 2);       // (0 + INNER(1)) → (0 + (1+1)) = 2
    assert(OUTER(0, 1, 2) == 2);    // (0 + INNER(1,2)) → (0 + (1+1)) = 2

    // ---- Multiple __VA_OPT__ ----
    assert(MULTI_OPT() == 0);
    assert(MULTI_OPT(1) == 3);      // 0+1+2
    assert(MULTI_OPT(1, 2) == 3);

    // ---- __VA_OPT__ with comma inside its content (not as separator) ----
    assert(COMMA_INSIDE() == 0);
    assert(COMMA_INSIDE(1) == 2);
    assert(COMMA_INSIDE(1, 2) == 2);

    // ---- __VA_OPT__ whose argument is a comma expression ----
    assert(COMMA_EXPR() == 0);
    assert(COMMA_EXPR((1, 2)) == 2);   // (0 , (1,2)) → (1,2) → 2
    // With multiple arguments, the comma expression is only the first argument.
    // But we can test that the comma is inserted before all args:
    assert(COMMA_EXPR((1, 2), 3) == 3); // (0 , (1,2), 3) → last is 3

    // ---- Array with a single argument that is a comma expression ----
    assert(ARRAY_SIZE((1, 2)) == 2);
    // The array becomes {0, (1,2)} → {0, 2} but we only check size.

    // ---- __VA_OPT__ in macro arguments (passing through) ----
    #define WRAP(m, ...) m(__VA_ARGS__)
    #define HAS_ARGS_WRAP(...) (0 __VA_OPT__(+ 1))
    assert(WRAP(HAS_ARGS_WRAP) == 0);
    assert(WRAP(HAS_ARGS_WRAP, 1) == 1);
    assert(WRAP(HAS_ARGS_WRAP, 1, 2) == 1);

    // ---- Empty __VA_OPT__() and blank-only variable arguments ----
    // C23 6.10.4: variable arguments include their separating commas, so two
    // or more variable arguments are never empty even when all of them are.
    assert(OPT_EMPTY(9) == 1);
    assert(SUPPRESS() == 0);
    assert(SUPPRESS(,) == 1);
    assert(SUPPRESS( ) == 0);
    assert(SUPPRESS( , ) == 1);
    assert(SUPPRESS(,,) == 1);

    // ---- Emptiness judged after macro expansion of the arguments ----
    assert(SUPPRESS(EMPTY_ARG) == 0);
    assert(SUPPRESS(EMPTY_ARG EMPTY_ARG) == 0);
    assert(SUPPRESS(EMPTY_ARG, 1) == 1);
    assert(SUPPRESS(1, EMPTY_ARG) == 1);
    assert(SUPPRESS(EMPTY_ARG, EMPTY_ARG, 9) == 1);
    assert(SUPPRESS(EMPTY_ARG, 2, EMPTY_ARG) == 1);
    assert(SUPPRESS(1,) == 1);

    // ---- Trailing comma insertion in an initializer list ----
    assert(sizeof(TRAIL()) / sizeof(int) == 1);   // { 0 }
    assert(sizeof(TRAIL(9)) / sizeof(int) == 1);  // { 0, }: legal trailing comma

    // ---- Named parameters referenced inside __VA_OPT__ content ----
    assert(USE_PARAM(7) == 0);
    assert(USE_PARAM(7, extra) == 7);
    assert(USE_PARAM(7, extra, more) == 7);

    // ---- Stringification inside __VA_OPT__ ----
    assert(strcmp(OPT_STR(a, b c), "a=b c") == 0);

    // ---- __VA_OPT__ as an operand of ## ----
    {
        int pr = 1, prb = 2, pq = 3, q = 4;
        assert(PASTE_R(pr) == 1);       // empty: no paste, yields pr
        assert(PASTE_R(pr, zz) == 2);   // pastes pr with first token b -> prb
        assert(PASTE_L(w, ee) == 3);    // p ## q -> pq
        assert(PASTE_L(w) == 4);        // empty left operand: yields q alone
    }

    // ---- ## pastes only the first token of multi-token content ----
    {
        PASTE_FIRST(un, ignored) int pf = 5; // un ## signed -> unsigned
        assert(pf == 5);
    }

    // ---- Deferred call connected through __VA_OPT__ output ----
    assert(MAYBE_FN(any)(3) == 33);     // FN connects with following (3)
    assert(MAYBE_FN()(3) == 3);         // empty: plain parenthesized (3)

    // ---- __VA_OPT__ evaluated while expanding macro arguments ----
    assert(APPLY(INNER_SUM(q)) == 100);
    assert(APPLY(INNER_SUM()) == 0);

    // ---- Token paste inside __VA_OPT__ content ----
    {
        int abcd = 7;
        assert(OPT_PASTE(zz) == 7);     // ab ## cd -> abcd
    }

    // ---- __VA_ARGS__ inside __VA_OPT__ content ----
    assert(JOINARGS() == 0);
    assert(JOINARGS(4) == 1);
    assert(JOINARGS(4, 5, 6) == 3);

    // ---- Nested invocations inside __VA_OPT__ content ----
    assert(CALLSUM(1, 2, 3) == 6);      // SUM3(1, 2, 3)
    assert((DEEP(q)) == 6);             // DEEP2(q) -> (5 + 1)

    // ---- Parens inside string/char literals within content ----
    assert(STR_PAREN(x) == 0);          // strcmp(")", "(") != 0
    assert(CHR_PAREN(y) == 3);

    // ---- Adjacent __VA_OPT__ instances ----
    assert(ADJACENT() == 0);
    assert(ADJACENT(z) == 3);

    // ---- Absence leaves a well-formed expression ----
    {
        int x_ = 13, y = 14;
        assert(TIGHT(a) == 27);
        assert(TIGHT() == 13);
    }

    // ---- Content spanning a line continuation ----
    assert(SPAN(z) == 1);
    assert(SPAN() == 0);

    // ---- __VA_OPT__ as the entire replacement list ----
    assert((ONLY(anything)) == 77);

    // ---- Stringify joins multiple variable arguments ----
    assert(strcmp(OPT_STR(x, 1, 2), "x=1, 2") == 0);

    // ---- Empty string literal argument is a token (non-empty) ----
    assert(SUPPRESS("") == 1);

    // ---- Reached through an object-like macro ----
    {
        const int via_obj = OBJ_RELAY;
        assert(via_obj == 24);
    }

    // ---- Output feeding another variadic macro's arguments ----
    assert(RELAY_VA(j) == 100);
    RELAY_VA(); // expands to nothing: bare empty statement

    return 0;
}
