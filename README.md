Minimal big integer library
===========================

API:

~~~ c
typedef struct {
    z_digit* d;  // digits, 0 if allocation failed
    z_size size; // number of digits
    bool neg;    // integer is negative
} z_int;

// comparison
int32_t z_cmp(z_int a, z_int a);

// unary functions
z_res z_not(z_int a);

// addition and subtraction
z_res z_add(z_int a, z_int b);
z_res z_add_1(z_int a, z_digit b);
z_res z_sub(z_int a, z_int b);
z_res z_sub_1(z_int a, z_digit b);

// multiplication
z_res z_mul(z_int a, z_int b);

// division
bool z_divmod(z_int* dp, z_int* mp, z_int a, z_int b); // precondition: b!=0
bool z_quorem(z_int* qp, z_int* rp, z_int a, z_int b); // precondition: b!=0
z_res z_div(z_int a, z_int b); // precondition: b!=0
z_res z_mod(z_int a, z_int b); // precondition: b!=0
z_res z_quo(z_int a, z_int b); // precondition: b!=0
z_res z_rem(z_int a, z_int b); // precondition: b!=0

// two-complements bitwise operations
z_res z_and(z_int a, z_int b);
z_res z_or(z_int a, z_int b);
z_res z_xor(z_int a, z_int b);
z_res z_shl(z_int a, uint16_t b);
z_res z_shr(z_int a, uint16_t b);

// conversion
double z_to_d(z_int a);
uint64_t z_to_u64(z_int a);
z_res z_from_b(const uint8_t *buf, size_t size);
z_res z_from_d(double b);
z_res z_from_i64(int64_t b);
z_res z_from_u64(uint64_t b);
~~~

Configuration:

~~~ c
#define Z_BITS      64 // 8, 16, 32, 64
#define Z_GMP       0  // 0 = do not use GMP, 1 = use GMP mpn functions
#define Z_SCRATCH   64 // scratch space on the stack in digits
#define Z_ASSERT(x) assert(x)
#define Z_ALLOC(x)  malloc(x)
#define Z_FREE(x)   free(x)
#include "z.h"
~~~

License
-------

MIT
