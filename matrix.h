#include <iostream>

#include "biginteger.h"

long long gcd(long long a, long long b, long long& x, long long& y) {
    if (a == 0) {
        x = 0;
        y = 1;
        return b;
    }
    long long res = gcd(b % a, a, y, x);
    x = x - (b / a) * y;
    return res;
}
long long mod(long long x, long long MOD) {
    return (x % MOD + MOD) % MOD;
}

long long inverse(long long x, long long MOD) {
    long long a, b;
    gcd(x, MOD, a, b);
    return mod(a, MOD);
}

template <long long N>
class Residue {
   private:
   public:
    long long val;

    Residue() : val(0) {}
    Residue(long long x) : val(mod(x)) {}

    Residue<N>& operator+=(const Residue<N>& other) {
        val = (val + other.val) % N;
        return *this;
    }
    Residue<N>& operator-=(const Residue<N>& other) {
        val = mod(val - other.val, N);
        return *this;
    }
    Residue<N>& operator*=(const Residue<N>& other) {
        val = (val * other.val) % N;
        return *this;
    }
    Residue<N>& operator/=(const Residue<N>& other) {
        static_assert(true);
        long long rev = inverse(other.val, N);
        *this *= rev;
        return *this;
    }
    Residue<N> operator-() {
        return Residue(-val + N);
    }
    Residue<N>& operator++() {
        *this += 1;
        return *this;
    }
    Residue<N>& operator--() {
        *this -= 1;
        return *this;
    }
    Residue<N> operator++(int) {
        Residue res = *this;
        *this += 1;
        return res;
    }
    Residue<N> operator--(int) {
        Residue res = *this;
        *this -= 1;
        return res;
    }

    Residue<N>& operator=(const Residue<N>& other) {
        val = other.val;
        return *this;
    }
};
