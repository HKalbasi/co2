#ifndef ABI_GCC_LIB_H
#define ABI_GCC_LIB_H

struct abi_pair {
    int x;
    int y;
};

int abi_add(int a, int b);

long long abi_add_long(long long a, long long b);

double abi_add_double(double a, double b);

float abi_mul_float(float a, float b);

int abi_str_eq(const char *a, const char *b);

struct abi_pair abi_make_pair(int x, int y);

int abi_pair_sum(struct abi_pair p);

long long abi_sum_many(
    long long a1, long long a2, long long a3, long long a4,
    long long a5, long long a6, long long a7, long long a8);

double abi_mix(int a, double b, long long c, double d, int e);

extern int abi_global;

struct abi_bf {
    unsigned int a : 3;
    unsigned int b : 5;
    unsigned int c : 10;
    signed int s : 4;
};

unsigned int abi_bf_pack(struct abi_bf bf);
struct abi_bf abi_bf_make(unsigned int a, unsigned int b, unsigned int c, int s);

union abi_num {
    int i;
    float f;
    unsigned long long bits;
};

double abi_union_as_double(union abi_num n);
union abi_num abi_union_make(double d);

#pragma pack(push, 1)
struct abi_packed {
    char c;
    int x;
    short s;
};
#pragma pack(pop)

int abi_packed_get(struct abi_packed p);
struct abi_packed abi_packed_make(int x);

enum abi_color { ABI_RED, ABI_GREEN, ABI_BLUE, ABI_YELLOW };
enum abi_color abi_enum_next(enum abi_color c);

struct abi_big {
    long long a, b, c, d;
};

long long abi_big_sum(struct abi_big b);
struct abi_big abi_big_make(long long a, long long b, long long c, long long d);

typedef int (*abi_binop_t)(int, int);
int abi_apply(abi_binop_t f, int a, int b);

_Bool abi_not_bool(_Bool b);

extern _Thread_local int abi_tls;

int abi_get_tls(void);
void abi_set_tls(int v);

#endif
