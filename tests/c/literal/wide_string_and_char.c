//@ mode: c
//@ run-status: 0

#include <assert.h>
#include <stddef.h>

/*
 * ============================================================
 * C23 wide character / wide string literal torture test
 *
 * Tests:
 *   L'a'       wide character constants
 *   L"foo"     wide string literals
 *
 * Expected:
 *   compile successfully
 *   return 0
 * ============================================================
 */

/* ------------------------------------------------------------
 * 1. Basic wide character constants
 * ------------------------------------------------------------ */

_Static_assert(L'a' == L'a');
_Static_assert(L'f' == L'f');
_Static_assert(L'z' == L'z');

_Static_assert(L'0' == L'0');
_Static_assert(L'9' == L'9');

_Static_assert(L'a' < L'b');
_Static_assert(L'b' < L'c');
_Static_assert(L'x' < L'y');
_Static_assert(L'y' < L'z');

_Static_assert(L'0' < L'1');
_Static_assert(L'1' < L'9');

_Static_assert(L'a' != L'A');
_Static_assert(L'z' != L'Z');


/* ------------------------------------------------------------
 * 2. Wide character escape sequences
 * ------------------------------------------------------------ */

_Static_assert(L'\0' == 0);

_Static_assert(L'\x41' == L'A');
_Static_assert(L'\x42' == L'B');
_Static_assert(L'\x61' == L'a');
_Static_assert(L'\x7A' == L'z');

_Static_assert(L'\101' == L'A');
_Static_assert(L'\102' == L'B');
_Static_assert(L'\141' == L'a');
_Static_assert(L'\172' == L'z');


/* ------------------------------------------------------------
 * 3. Wide character arithmetic
 * ------------------------------------------------------------ */

_Static_assert(L'a' + 1 == L'b');
_Static_assert(L'b' + 1 == L'c');

_Static_assert(L'z' - L'a' == 25);
_Static_assert(L'9' - L'0' == 9);


/* ------------------------------------------------------------
 * 4. Wide string sizes
 *
 * These ARE suitable for compile-time checking.
 * ------------------------------------------------------------ */

_Static_assert(sizeof(L"") == sizeof(wchar_t));

_Static_assert(sizeof(L"a") == 2 * sizeof(wchar_t));
_Static_assert(sizeof(L"ab") == 3 * sizeof(wchar_t));
_Static_assert(sizeof(L"foo") == 4 * sizeof(wchar_t));
_Static_assert(sizeof(L"hello") == 6 * sizeof(wchar_t));

_Static_assert(sizeof(L"0123456789") == 11 * sizeof(wchar_t));


/* ------------------------------------------------------------
 * 5. Wide string concatenation sizes
 * ------------------------------------------------------------ */

_Static_assert(
    sizeof(L"foo" L"bar") == 7 * sizeof(wchar_t)
);

_Static_assert(
    sizeof(L"hello" L" world") == 12 * sizeof(wchar_t)
);


/* ------------------------------------------------------------
 * 6. Wide string arrays
 * ------------------------------------------------------------ */

static const wchar_t hello[] = L"hello";

_Static_assert(
    sizeof(hello) == 6 * sizeof(wchar_t)
);

static const wchar_t foo[] = L"foo";

_Static_assert(
    sizeof(foo) == 4 * sizeof(wchar_t)
);


/* ------------------------------------------------------------
 * 7. Runtime string indexing
 * ------------------------------------------------------------ */

int main(void)
{
    /* --------------------------------------------------------
     * Basic L"foo"
     * -------------------------------------------------------- */

    assert(L"foo"[0] == L'f');
    assert(L"foo"[1] == L'o');
    assert(L"foo"[2] == L'o');
    assert(L"foo"[3] == L'\0');


    /* --------------------------------------------------------
     * L"hello"
     * -------------------------------------------------------- */

    assert(L"hello"[0] == L'h');
    assert(L"hello"[1] == L'e');
    assert(L"hello"[2] == L'l');
    assert(L"hello"[3] == L'l');
    assert(L"hello"[4] == L'o');
    assert(L"hello"[5] == L'\0');


    /* --------------------------------------------------------
     * Numeric characters
     * -------------------------------------------------------- */

    assert(L"0123456789"[0] == L'0');
    assert(L"0123456789"[1] == L'1');
    assert(L"0123456789"[5] == L'5');
    assert(L"0123456789"[9] == L'9');
    assert(L"0123456789"[10] == L'\0');


    /* --------------------------------------------------------
     * Empty string
     * -------------------------------------------------------- */

    assert(L""[0] == L'\0');


    /* --------------------------------------------------------
     * Escape sequences
     * -------------------------------------------------------- */

    assert(L"\n"[0] == L'\n');
    assert(L"\t"[0] == L'\t');
    assert(L"\r"[0] == L'\r');
    assert(L"\a"[0] == L'\a');
    assert(L"\b"[0] == L'\b');
    assert(L"\f"[0] == L'\f');
    assert(L"\v"[0] == L'\v');
    assert(L"\0"[0] == L'\0');


    /* --------------------------------------------------------
     * Hexadecimal escapes
     * -------------------------------------------------------- */

    assert(L"\x41"[0] == L'A');
    assert(L"\x42"[0] == L'B');
    assert(L"\x61"[0] == L'a');
    assert(L"\x7A"[0] == L'z');


    /* --------------------------------------------------------
     * Octal escapes
     * -------------------------------------------------------- */

    assert(L"\101"[0] == L'A');
    assert(L"\102"[0] == L'B');
    assert(L"\141"[0] == L'a');
    assert(L"\172"[0] == L'z');


    /* --------------------------------------------------------
     * Multiple escape characters
     * -------------------------------------------------------- */

    assert(L"\x41\x42"[0] == L'A');
    assert(L"\x41\x42"[1] == L'B');

    assert(L"\101\102\103"[0] == L'A');
    assert(L"\101\102\103"[1] == L'B');
    assert(L"\101\102\103"[2] == L'C');


    /* --------------------------------------------------------
     * Adjacent wide string concatenation
     * -------------------------------------------------------- */

    assert(L"foo" L"bar"[0] == L'f');
    assert(L"foo" L"bar"[1] == L'o');
    assert(L"foo" L"bar"[2] == L'o');
    assert(L"foo" L"bar"[3] == L'b');
    assert(L"foo" L"bar"[4] == L'a');
    assert(L"foo" L"bar"[5] == L'r');
    assert(L"foo" L"bar"[6] == L'\0');


    /* --------------------------------------------------------
     * Longer concatenation
     * -------------------------------------------------------- */

    assert(L"hello" L" world"[0] == L'h');
    assert(L"hello" L" world"[5] == L' ');
    assert(L"hello" L" world"[6] == L'w');
    assert(L"hello" L" world"[10] == L'd');
    assert(L"hello" L" world"[11] == L'\0');


    /* --------------------------------------------------------
     * Embedded null
     * -------------------------------------------------------- */

    assert(L"a\0b"[0] == L'a');
    assert(L"a\0b"[1] == L'\0');
    assert(L"a\0b"[2] == L'b');
    assert(L"a\0b"[3] == L'\0');

    assert(sizeof(L"a\0b") == 4 * sizeof(wchar_t));


    /* --------------------------------------------------------
     * Punctuation
     * -------------------------------------------------------- */

    assert(L"!@#$%"[0] == L'!');
    assert(L"!@#$%"[1] == L'@');
    assert(L"!@#$%"[2] == L'#');
    assert(L"!@#$%"[3] == L'$');
    assert(L"!@#$%"[4] == L'%');


    /* --------------------------------------------------------
     * Spaces
     * -------------------------------------------------------- */

    assert(L" "[0] == L' ');
    assert(L"  "[0] == L' ');
    assert(L"  "[1] == L' ');


    /* --------------------------------------------------------
     * Wide character literals vs wide strings
     * -------------------------------------------------------- */

    assert(L'f' == L"foo"[0]);
    assert(L'o' == L"foo"[1]);
    assert(L'o' == L"foo"[2]);


    /* --------------------------------------------------------
     * Unicode escape sequences
     * -------------------------------------------------------- */

    assert(L'\u0041' == L'A');
    assert(L'\u0061' == L'a');

    assert(L"\u0041"[0] == L'A');
    assert(L"\u0061"[0] == L'a');

    assert(L"\u0041\u0042"[0] == L'A');
    assert(L"\u0041\u0042"[1] == L'B');

    assert(L"\U00000041"[0] == L'A');
    assert(L"\U00000061"[0] == L'a');


    /* --------------------------------------------------------
     * Wide strings stored in arrays
     * -------------------------------------------------------- */

    assert(hello[0] == L'h');
    assert(hello[1] == L'e');
    assert(hello[2] == L'l');
    assert(hello[3] == L'l');
    assert(hello[4] == L'o');
    assert(hello[5] == L'\0');

    assert(foo[0] == L'f');
    assert(foo[1] == L'o');
    assert(foo[2] == L'o');
    assert(foo[3] == L'\0');


    /* --------------------------------------------------------
     * Explicit wchar_t array
     * -------------------------------------------------------- */

    static const wchar_t word[] = {
        L'f',
        L'o',
        L'o',
        L'\0'
    };

    assert(word[0] == L'f');
    assert(word[1] == L'o');
    assert(word[2] == L'o');
    assert(word[3] == L'\0');

    wchar_t c1 = L'\x92';
    assert((int)c1 == 0x92);
    wchar_t c2 = L'\xff';
    assert((int)c2 == 0xff);
    wchar_t c3 = '\xff';
    assert((int)c3 == -1);

    assert(_Generic('a', char: 0, int: 1, default: 0));
    assert(_Generic(L'a', char: 0, int: 1, default: 0));

    assert(L'ف' ==1601);

    /* --------------------------------------------------------
     * char16_t (u"...") — 2-byte code units, little-endian
     * -------------------------------------------------------- */

    _Static_assert(sizeof(u"ab") == 6);

    {
        unsigned char *b16 = (unsigned char *)u"ab";
        assert(b16[0] == 0x61);
        assert(b16[1] == 0x00);
        assert(b16[2] == 0x62);
        assert(b16[3] == 0x00);
        assert(b16[4] == 0x00);
        assert(b16[5] == 0x00);
    }

    {
        unsigned short s16[3];
        const unsigned char *src = (const unsigned char *)u"ab";
        s16[0] = (unsigned short)(src[0] | ((unsigned short)src[1] << 8));
        s16[1] = (unsigned short)(src[2] | ((unsigned short)src[3] << 8));
        s16[2] = (unsigned short)(src[4] | ((unsigned short)src[5] << 8));
        assert(s16[0] == 0x0061);
        assert(s16[1] == 0x0062);
        assert(s16[2] == 0x0000);
    }


    /* --------------------------------------------------------
     * Wide string escapes are code units, not UTF-8 decoded
     * -------------------------------------------------------- */

    {
        wchar_t a[] = L"\x92";
        assert((int)a[0] == 0x92);
        assert((int)a[1] == 0);
    }

    {
        wchar_t u[] = L"\xc3\xa9";
        assert((int)u[0] == 0xC3);
        assert((int)u[1] == 0xA9);
        assert((int)u[2] == 0);
    }

    {
        wchar_t raw[] = L"é";
        assert((int)raw[0] == 0xE9);
        assert((int)raw[1] == 0);
    }


    /* --------------------------------------------------------
     * Wide string deref through pointers (element alignment)
     * -------------------------------------------------------- */

    {
        const wchar_t *p = L"abcdef";
        assert(p[0] == L'a');
        assert(p[1] == L'b');
        assert(p[2] == L'c');
        assert(p[3] == L'd');
        assert(p[4] == L'e');
        assert(p[5] == L'f');
        assert(p[6] == L'\0');
    }

    {
        const wchar_t *q = L"\x92\x93\x94";
        assert((int)q[0] == 0x92);
        assert((int)q[1] == 0x93);
        assert((int)q[2] == 0x94);
    }

    /* --------------------------------------------------------
     * Runtime success
     * -------------------------------------------------------- */

    return 0;
}
