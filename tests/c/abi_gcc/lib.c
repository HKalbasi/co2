#include "lib.h"

int abi_global = 40;

int abi_add(int a, int b) {
    return a + b;
}

long long abi_add_long(long long a, long long b) {
    return a + b;
}

double abi_add_double(double a, double b) {
    return a + b;
}

float abi_mul_float(float a, float b) {
    return a * b;
}

int abi_str_eq(const char *a, const char *b) {
    int i = 0;
    while (a[i] != '\0' && b[i] != '\0') {
        if (a[i] != b[i]) {
            return 0;
        }
        i += 1;
    }
    return a[i] == b[i];
}

struct abi_pair abi_make_pair(int x, int y) {
    struct abi_pair p;
    p.x = x;
    p.y = y;
    return p;
}

int abi_pair_sum(struct abi_pair p) {
    return p.x + p.y;
}

long long abi_sum_many(
    long long a1, long long a2, long long a3, long long a4,
    long long a5, long long a6, long long a7, long long a8)
{
    return a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8;
}

double abi_mix(int a, double b, long long c, double d, int e) {
    return (double)a + b + (double)c + d + (double)e;
}

unsigned int abi_bf_pack(struct abi_bf bf) {
    unsigned int out = (unsigned int)bf.a;
    out |= bf.b << 3;
    out |= bf.c << 8;
    out |= (unsigned int)(bf.s + 8) << 18;
    return out;
}

struct abi_bf abi_bf_make(unsigned int a, unsigned int b, unsigned int c, int s) {
    struct abi_bf bf;
    bf.a = a;
    bf.b = b;
    bf.c = c;
    bf.s = s;
    return bf;
}

double abi_union_as_double(union abi_num n) {
    return (double)n.f;
}

union abi_num abi_union_make(double d) {
    union abi_num n;
    n.f = (float)d;
    return n;
}

int abi_packed_get(struct abi_packed p) {
    return p.c + p.x + p.s;
}

struct abi_packed abi_packed_make(int x) {
    struct abi_packed p;
    p.c = 1;
    p.x = x;
    p.s = 2;
    return p;
}

enum abi_color abi_enum_next(enum abi_color c) {
    return (enum abi_color)((c + 1) % 4);
}

long long abi_big_sum(struct abi_big b) {
    return b.a + b.b + b.c + b.d;
}

struct abi_big abi_big_make(long long a, long long b, long long c, long long d) {
    struct abi_big x;
    x.a = a;
    x.b = b;
    x.c = c;
    x.d = d;
    return x;
}

int abi_apply(abi_binop_t f, int a, int b) {
    return f(a, b);
}

_Bool abi_not_bool(_Bool b) {
    return !b;
}

_Thread_local int abi_tls = 123;

int abi_get_tls(void) {
    return abi_tls;
}

void abi_set_tls(int v) {
    abi_tls = v;
}
