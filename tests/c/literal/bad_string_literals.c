//@ mode: c
//@ compile-fail

/* Bad string and character literals that are rejected during preprocessing
 * (tokenization). These all live in one translation unit because they are
 * detected in the same stage; a preprocessor-stage error terminates the
 * compile before the parser runs, so they cannot be mixed with parser-stage
 * errors (see bad_tokens.c for those).
 *
 * Cases:
 *   - a universal character name naming a surrogate (0xD800-0xDFFF) is not a
 *     valid universal character (matching gcc and clang)
 *   - a universal character name with a value >= 0x80000000 is not valid
 *     (matching gcc's boundary)
 *   - a universal character name needs exactly 4 (\u) or 8 (\U) hex digits
 *   - a hexadecimal escape (lowercase \x only) requires at least one hex digit
 *   - in a char8_t literal (u8'...'), a universal character name naming a
 *     non-ASCII code point is not encodable in a single code unit
 */

int main(void) {
    const char *a = "\uD800";
//                   ^^^^^^ error: \uD800 is not a valid universal character
    const char *b = "\U80000000";
//                   ^^^^^^^^^^ error: \U80000000 is not a valid universal character
    const char *c = "\u123";
//                   ^^^^^ error: incomplete universal character name \u123
    const char *d = "\x";
//                   ^^ error: `\x` used with no following hex digits
    unsigned char e = u8'\u00E9';
//                       ^^^^^^ error: character not encodable in a single code unit
    (void)a;
    (void)b;
    (void)c;
    (void)d;
    (void)e;
    return 0;
}
