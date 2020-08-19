#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define _z_inl    static inline __attribute__((always_inline))
#define _z_static static __attribute__((unused))
#define _z_noinl  _z_static __attribute__((noinline))
#define _z_wu     __attribute__((warn_unused_result))
#define _z_swap(a, b)          \
    ({                         \
        typeof(a) _z_swap = a; \
        a = b;                 \
        b = _z_swap;           \
    })
#define _z_min(a, b)                            \
    ({                                          \
        typeof(a) _z_min1 = (a), _z_min2 = (b); \
        _z_min1 < _z_min2 ? _z_min1 : _z_min2;  \
    })
#define _z_max(a, b)                            \
    ({                                          \
        typeof(a) _z_max1 = (a), _z_max2 = (b); \
        _z_max1 > _z_max2 ? _z_max1 : _z_max2;  \
    })
#define _z_digits(n)    (((n) + Z_BITS - 1) / Z_BITS)
#define _z_cpy(d, s, n) memcpy((d), (s), (size_t)(n) * sizeof(z_digit))
#define _z_clear(d, n)  memset((d), 0, (size_t)(n) * sizeof(z_digit))
#define z_none          ((z_int){ .size = 0 })
#define z_auto(x, i)    z_int x __attribute__((cleanup(_z_free))) = (i)
#define z_tryx(i, ...)      \
    ({                      \
        z_res _z_try = (i); \
        if (!_z_try.z.d) {  \
            __VA_ARGS__;    \
        };                  \
        _z_try.z;           \
    })
#define z_try(i)     z_tryx(i, return _z_try)
#define z_trybool(i) z_tryx(i, return false)
#define z_ok(i)      ((z_res){ i })
#define z_err        ((z_res){ { .d = 0 } })

#if Z_GMP
    #include "zgmp.h"
#else
    #include "znogmp.h"
#endif

typedef struct {
    z_digit* d;  // digits
    z_size size; // number of digits
    bool neg;    // integer is negative
} z_int;

typedef struct {
    z_int z;
} z_res;

_z_inl void _z_free(z_int* a) {
    if (a->d)
        Z_FREE(a->d);
}

_z_static _z_wu int32_t z_cmp(z_int a, z_int b) {
    if (a.neg != b.neg)
        return a.neg ? -1 : 1;
    if (a.neg)
        _z_swap(a, b);
    if (a.size != b.size)
        return a.size < b.size ? -1 : 1;
    int32_t cmp = zd_cmp(a.d, b.d, a.size);
    return cmp ? (cmp > 0 ? 1 : -1) : 0;
}

_z_inl void _z_move(z_int** p, z_int* a) {
    if (*p) {
        Z_ASSERT(a->d);
        **p = *a;
        a->d = 0;
    }
}

_z_inl _z_wu z_res _z_new(bool neg, z_size size, z_size alloc) {
    return (z_res){ { .neg = neg, .size = size, .d = Z_ALLOC(alloc) } };
}

_z_inl void _z_grow(z_int* a, z_digit b) {
    a->d[a->size] = b;
    a->size += !!b;
}

_z_inl void _z_trim(z_int* a) {
    while (a->size && !a->d[a->size - 1])
        --a->size;
    if (!a->size)
        a->neg = false;
}

_z_inl void _z_trim_1(z_int* a) {
    Z_ASSERT(a->size > 0);
    if (!a->d[a->size - 1])
        --a->size;
}

_z_inl _z_wu z_res _z_addsub_1(z_int a, z_digit b, bool aneg, bool bneg) {
    z_int r = z_try(_z_new(aneg, a.size, a.size + 1));
    if (!a.size) {
        r.d[0] = b;
        r.neg = bneg;
        r.size = 1;
        return z_ok(r);
    }

    if (aneg == bneg) {
        _z_grow(&r, zd_add_1(r.d, a.d, a.size, b));
    } else if (a.size == 1 && a.d[0] < b) {
        r.d[0] = b - a.d[0];
        r.neg = bneg;
    } else {
        zd_sub_1(r.d, a.d, a.size, b);
        _z_trim(&r);
    }

    return z_ok(r);
}

_z_inl _z_wu z_res _z_add_1(z_int a, z_digit b) {
    return _z_addsub_1(a, b, a.neg, false);
}

_z_inl _z_wu z_res _z_sub_1(z_int a, z_digit b) {
    return _z_addsub_1(a, b, a.neg, true);
}

_z_noinl _z_wu z_res _z_inc(z_int a) {
    return _z_add_1(a, 1);
}

_z_noinl _z_wu z_res _z_dec(z_int a) {
    return _z_sub_1(a, 1);
}

_z_static _z_wu z_res z_add_1(z_int a, z_digit b) {
    return _z_add_1(a, b);
}

_z_static _z_wu z_res z_sub_1(z_int a, z_digit b) {
    return _z_sub_1(a, b);
}

_z_inl _z_wu z_res _z_addsub(z_int a, z_int b, bool aneg, bool bneg) {
    if (a.size < b.size) {
        _z_swap(aneg, bneg);
        _z_swap(a, b);
    }

    if (b.size == 1)
        return _z_addsub_1(a, b.d[0], aneg, bneg);

    z_int r = z_try(_z_new(aneg, a.size, a.size + 1));
    if (aneg == bneg) {
        _z_grow(&r, zd_add(r.d, a.d, a.size, b.d, b.size));
    } else if (a.size != b.size) {
        zd_sub(r.d, a.d, a.size, b.d, b.size);
        _z_trim(&r);
    } else {
        if (zd_cmp(a.d, b.d, a.size) < 0) {
            _z_swap(a, b);
            r.neg = bneg;
        }
        zd_sub_n(r.d, a.d, b.d, a.size);
        _z_trim(&r);
    }

    return z_ok(r);
}

_z_noinl _z_wu z_res z_sub(z_int a, z_int b) {
    return _z_addsub(a, b, a.neg, b.size ? !b.neg : false);
}

_z_noinl _z_wu z_res z_add(z_int a, z_int b) {
    return _z_addsub(a, b, a.neg, b.neg);
}

_z_inl _z_wu bool _z_identical(z_int a, z_int b) {
    return a.d == b.d && a.size == b.size && a.neg == b.neg;
}

_z_static _z_wu z_res z_mul(z_int a, z_int b) {
    if (a.size < b.size)
        _z_swap(a, b);
    if (!b.size)
        return _z_new(false, 0, 0);
    z_int r = z_try(_z_new(a.neg != b.neg, a.size + b.size, a.size + b.size));
    if (_z_identical(a, b)) {
        zd_sqr(r.d, a.d, a.size);
        _z_trim_1(&r);
    } else if (b.size == 1) {
        r.d[a.size] = zd_mul_1(r.d, a.d, a.size, b.d[0]);
        _z_trim_1(&r);
    } else {
        r.size -= !zd_mul(r.d, a.d, a.size, b.d, b.size);
    }
    return z_ok(r);
}

_z_static _z_wu bool z_quorem(z_int* qp, z_int* rp, z_int a, z_int b) {
    Z_ASSERT(b.size); // non-zero
    z_size qsize = _z_max(a.size - b.size + 1, 0);
    z_auto(q, z_trybool(_z_new(a.neg != b.neg && qsize, qsize, qsize)));
    z_auto(r, z_trybool(_z_new(a.neg, b.size, b.size)));
    if (!qsize) {
        if (rp) {
            _z_cpy(r.d, a.d, a.size);
            r.size = a.size;
        }
    } else {
        if (!zd_divmod(q.d, r.d, a.d, a.size, b.d, b.size))
            return false;
        if (rp)
            _z_trim(&r);
        if (qp) {
            _z_trim_1(&q);
            if (!q.size)
                q.neg = false;
        }
    }
    _z_move(&qp, &q);
    _z_move(&rp, &r);
    return true;
}

_z_static _z_wu z_res z_quo(z_int a, z_int b) {
    return z_quorem(&a, 0, a, b) ? z_ok(a) : z_err;
}

_z_static _z_wu z_res z_rem(z_int a, z_int b) {
    return z_quorem(0, &a, a, b) ? z_ok(a) : z_err;
}

_z_static _z_wu bool z_divmod(z_int* dp, z_int* mp, z_int a, z_int b) {
    z_auto(q, z_none);
    z_auto(r, z_none);
    if (!z_quorem(&q, &r, a, b))
        return false;
    if (r.size && a.neg != b.neg) {
        z_auto(d, dp ? z_trybool(_z_dec(q)) : z_none);
        z_auto(m, mp ? z_trybool(z_add(r, b)) : z_none);
        _z_move(&dp, &d);
        _z_move(&mp, &m);
    } else {
        _z_move(&dp, &q);
        _z_move(&mp, &r);
    }
    return true;
}

_z_static _z_wu z_res z_div(z_int a, z_int b) {
    return z_divmod(&a, 0, a, b) ? z_ok(a) : z_err;
}

_z_static _z_wu z_res z_mod(z_int a, z_int b) {
    return z_divmod(0, &a, a, b) ? z_ok(a) : z_err;
}

_z_noinl _z_wu z_res _z_unsigned_xor(z_int a, z_int b) {
    if (a.size < b.size)
        _z_swap(a, b);
    z_int r = z_try(_z_new(false, a.size, a.size));
    if (b.size)
        zd_xor_n(r.d, a.d, b.d, b.size);
    if (a.size > b.size)
        _z_cpy(r.d + b.size, a.d + b.size, a.size - b.size);
    else
        _z_trim(&r);
    return z_ok(r);
}

_z_noinl _z_wu z_res _z_unsigned_and(z_int a, z_int b) {
    z_size size = _z_min(a.size, b.size);
    z_int r = z_try(_z_new(false, size, size));
    if (r.size) {
        zd_and_n(r.d, a.d, b.d, r.size);
        _z_trim(&r);
    }
    return z_ok(r);
}

_z_noinl _z_wu z_res _z_unsigned_andnot(z_int a, z_int b) {
    z_int r = z_try(_z_new(false, a.size, a.size));
    z_size size = _z_min(a.size, b.size);
    if (size)
        zd_andnot_n(r.d, a.d, b.d, size);
    if (size < a.size)
        _z_cpy(r.d + size, a.d + size, a.size - size);
    _z_trim(&r);
    return z_ok(r);
}

_z_noinl _z_wu z_res _z_unsigned_or(z_int a, z_int b) {
    if (a.size < b.size)
        _z_swap(a, b);
    z_int r = z_try(_z_new(false, a.size, a.size));
    if (b.size)
        zd_or_n(r.d, a.d, b.d, b.size);
    if (a.size > b.size)
        _z_cpy(r.d + b.size, a.d + b.size, a.size - b.size);
    return z_ok(r);
}

_z_noinl _z_wu z_res _z_unsigned_dec(z_int a) {
    Z_ASSERT(a.size);
    z_int r = z_try(_z_new(false, a.size, a.size + 1));
    zd_sub_1(r.d, a.d, a.size, 1);
    _z_trim(&r);
    return z_ok(r);
}

_z_static _z_wu z_res z_xor(z_int a, z_int b) {
    if (!a.neg && !b.neg)
        return _z_unsigned_xor(a, b);

    if (a.neg)
        _z_swap(a, b);

    z_auto(x, z_try(_z_unsigned_dec(b)));
    if (a.neg && b.neg) {
        z_auto(y, z_try(_z_unsigned_dec(a)));
        return _z_unsigned_xor(x, y);
    }

    z_auto(y, z_try(_z_unsigned_xor(a, x)));
    z_int r = z_try(_z_inc(y));
    r.neg = true;
    return z_ok(r);
}

_z_static _z_wu z_res z_and(z_int a, z_int b) {
    if (!a.neg && !b.neg)
        return _z_unsigned_and(a, b);

    if (a.neg)
        _z_swap(a, b);

    z_auto(x, z_try(_z_unsigned_dec(b)));
    if (a.neg && b.neg) {
        z_auto(y, z_try(_z_unsigned_dec(a)));
        z_auto(z, z_try(_z_unsigned_or(x, y)));
        z_int r = z_try(_z_inc(z));
        r.neg = true;
        return z_ok(r);
    }

    return _z_unsigned_andnot(a, x);
}

_z_static _z_wu z_res z_or(z_int a, z_int b) {
    if (!a.neg && !b.neg)
        return _z_unsigned_or(a, b);

    if (a.neg)
        _z_swap(a, b);

    z_auto(x, z_try(_z_unsigned_dec(b)));
    z_int r;
    if (a.neg && b.neg) {
        z_auto(y, z_try(_z_unsigned_dec(a)));
        z_auto(z, z_try(_z_unsigned_and(x, y)));
        r = z_try(_z_inc(z));
    } else {
        z_auto(y, z_try(_z_unsigned_andnot(x, a)));
        r = z_try(_z_inc(y));
    }
    r.neg = true;
    return z_ok(r);
}

_z_static _z_wu z_res z_not(z_int a) {
    a.neg = !a.neg && a.size; // negate
    return _z_dec(a);
}

_z_static _z_wu uint64_t z_to_u64(z_int a) {
    z_size i = _z_min(a.size, _z_digits(64));
    uint64_t b = 0;
    while (i --> 0) {
        b <<= 64 <= Z_BITS ? 0 : Z_BITS;
        b |= (uint64_t)a.d[i];
        if (64 <= Z_BITS)
            break;
    }
    return a.neg ? (uint64_t)(-(int64_t)b) : b;
}

_z_inl _z_wu z_int z_from_u64_noalloc(uint64_t b, uint64_t* d) {
    z_int r = { .d = (z_digit*)d };
    uint64_t mask = 64 <= Z_BITS ? ~(uint64_t)0 : ((uint64_t)1 << (64 <= Z_BITS ? 0 : Z_BITS)) - 1;
    while (b) {
        r.d[r.size++] = (z_digit)(b & mask);
        if (64 <= Z_BITS)
            break;
        b >>= 64 <= Z_BITS ? 0 : Z_BITS;
    }
    return r;
}

_z_static _z_wu z_res z_from_u64(uint64_t b) {
    return z_ok(z_from_u64_noalloc(b, (uint64_t*)z_try(_z_new(false, 0, _z_digits(64))).d));
}

_z_inl _z_wu z_int z_from_i64_noalloc(int64_t b, uint64_t* d) {
    z_int r = z_from_u64_noalloc(b < 0 ? -(uint64_t)b : (uint64_t)b, d);
    r.neg = b < 0;
    return r;
}

_z_static _z_wu z_res z_from_i64(int64_t b) {
    return z_ok(z_from_i64_noalloc(b, (uint64_t*)z_try(_z_new(false, 0, _z_digits(64))).d));
}

_z_static _z_wu z_res z_shl(z_int a, uint16_t b) {
    if (!a.size)
        return _z_new(false, 0, 0);
    z_size n = b / Z_BITS;
    z_int r = z_try(_z_new(a.neg, a.size + n, a.size + n + 1));
    b %= Z_BITS;
    if (b)
        _z_grow(&r, zd_shl(r.d + n, a.d, a.size, b));
    else
        _z_cpy(r.d + n, a.d, a.size);
    _z_clear(r.d, n);
    return z_ok(r);
}

_z_static _z_wu z_res z_shr(z_int a, uint16_t b) {
    z_size n = b / Z_BITS;
    if (a.size <= n && a.neg)
        return z_from_i64(-1);
    if (!a.size || a.size <= n)
        return _z_new(false, 0, 0);
    z_int r = z_try(_z_new(a.neg, a.size - n, a.size - n));
    b %= Z_BITS;
    if (b) {
        zd_shr(r.d, a.d + n, r.size, b);
        _z_trim_1(&r);
    } else {
        _z_cpy(r.d, a.d + n, r.size);
    }
    return z_ok(r);
}

_z_static _z_wu double z_to_d(z_int a) {
    if (!a.size)
        return 0;
    double d = 0, p = 2.0 * (double)((z_digit)1 << (Z_BITS - 1));
    for (z_size i = a.size; i --> 0;)
        d = d * p + (double)a.d[i];
    return a.neg ? -d : d;
}

_z_static _z_wu z_res z_from_d(double b) {
    uint64_t bits;
    memcpy(&bits, &b, sizeof(bits));
    int32_t exp = (int32_t)((bits >> 52) & 0x7FF);
    if (exp == 0x7FF)
        return _z_new(false, 0, 0); // convention: return 0 for +-inf, NaN
    exp -= 1023 + 52;
    uint64_t frac = (bits & (((uint64_t)1 << 52) - (uint64_t)1)) | ((uint64_t)1 << 52), tmp;
    z_int f = z_from_u64_noalloc(frac, &tmp),
          r = z_try(exp < 0 ? z_shr(f, (uint16_t)-exp) : z_shl(f, (uint16_t)exp));
    r.neg = (bits >> 63) && r.size;
    return z_ok(r);
}

_z_static _z_wu z_res z_from_b(const uint8_t* buf, size_t size) {
    Z_ASSERT(size);
    z_int r = z_try(_z_new(false, 0, (z_size)_z_digits(8 * size)));
    z_digit c = 0;
    for (size_t s = 0, i = size; i --> 0;) {
        if (!s) {
            Z_ASSERT((size_t)r.size < _z_digits(8 * size));
            ++r.size;
            r.d[r.size - 1] = c;
        }
        r.d[r.size - 1] |= (z_digit)buf[i] << s;
        s += 8;
        if (s >= Z_BITS) {
            c = Z_BITS % 8 == 0 ? 0 : (z_digit)buf[i] >> (8 + Z_BITS - s);
            s = 0;
        }
    }
    Z_ASSERT(r.d[r.size - 1]);
    return z_ok(r);
}
