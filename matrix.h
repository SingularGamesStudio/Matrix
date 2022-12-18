#pragma once

#include <limits.h>

#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <compare>
#include <complex>
#include <deque>
#include <iostream>
#include <string>
#include <vector>

using std::vector, std::string, std::deque, std::complex;

enum class signs { neg = -1, zero = 0, pos = 1 };

signs mulsigns(signs a, signs b) {
    if (a == signs::zero || b == signs::zero)
        return signs::zero;
    if (a == b)
        return signs::pos;
    return signs::neg;
}

size_t reversebits(size_t x, size_t pw2) {
    size_t res = 0;
    for (size_t i = 0; i < pw2; i++) {
        if ((x >> i) & 1)
            res |= (1 << (pw2 - i - 1));
    }
    return res;
}

void FFT(vector<complex<double>>& a, complex<double> q, bool reverse) {
    if (reverse) {
        q = complex<double>(q.real(), q.imag() * -1);
    }
    size_t n = a.size();
    size_t pw2 = 0;
    while (static_cast<size_t>((1 << pw2)) < n)
        pw2++;
    for (size_t i = 0; i < n; i++) {
        size_t rev = reversebits(i, pw2);
        if (i < rev)
            std::swap(a[i], a[rev]);
    }
    for (size_t l = 2; l <= n; l *= 2) {
        complex<double> cur = q;
        for (size_t ll = n; ll > l; ll /= 2)
            cur *= cur;
        for (size_t start = 0; start < n; start += l) {
            size_t mid = start + l / 2;
            complex<double> qdeg = 1;
            size_t pos = start;
            while (pos < mid) {
                complex<double> u = a[pos];
                complex<double> v = a[pos + l / 2] * qdeg;
                a[pos] = u + v;
                a[pos + l / 2] = u - v;
                qdeg *= cur;
                pos++;
            }
        }
    }
    if (reverse) {
        for (size_t i = 0; i < n; i++) {
            a[i] = complex<double>(round(a[i].real() / static_cast<double>(n)),
                                   round(a[i].imag() / static_cast<double>(n)));
        }
    }
}

complex<double> sopr(complex<double> x) {
    return complex<double>(x.real(), -x.imag());
}

complex<double> divi(complex<double> x) {
    return complex<double>(x.imag(), -x.real());
}

namespace BigIntConst {
const int MOD = 100;
const int DIGITS = 2;
const int TEN = 10;
}  // namespace BigIntConst

class PoweredInteger;

class BigInteger {
private:
    deque<int> digits;
    signs sign;
    int pw10() const {
        int ans = 0;
        for (size_t i = 0; i < digits.size() - 1; i++) {
            if (digits[i] != 0)
                return -1;
            ans += BigIntConst::DIGITS;
        }
        int x = digits[digits.size() - 1];
        while (x % BigIntConst::TEN == 0) {
            ans++;
            x /= BigIntConst::TEN;
        }
        if (x != 1)
            return -1;
        return ans;
    }

    void upgrade(int x, int& zeros) {
        if (x) {
            for (int j = 0; j < zeros; j++) {
                digits.push_back(0);
            }
            digits.push_back(x);
            zeros = 0;
        } else {
            ++zeros;
        }
    }

    void add1() {  // add 1 to the abs
        if (sign == signs::zero) {
            digits.push_back(1);
            sign = signs::pos;
            return;
        }
        int delta = 1;
        for (size_t i = 0; i < digits.size(); i++) {
            digits[i] += delta;
            delta = digits[i] / BigIntConst::MOD;
            digits[i] = digits[i] % BigIntConst::MOD;
            if (delta == 0)
                break;
        }
        if (delta != 0)
            digits.push_back(delta);
    }

    void sub1() {  // substract 1 from the abs
        if (sign == signs::zero) {
            digits.push_back(1);
            sign = signs::neg;
            return;
        }
        int delta = -1;
        for (size_t i = 0; i < digits.size(); i++) {
            digits[i] += delta;
            if (digits[i] < 0) {
                delta = -1;
                digits[i] += BigIntConst::MOD;
            } else {
                break;
            }
        }
        while (!digits.empty() && digits[digits.size() - 1] == 0)
            digits.pop_back();
        if (digits.empty())
            sign = signs::zero;
    }

    std::strong_ordering cmpabs(const BigInteger& second) const {
        if (digits.size() != second.digits.size())
            return digits.size() <=> second.digits.size();
        for (int i = static_cast<int>(digits.size()) - 1; i >= 0; --i) {
            if (digits[static_cast<size_t>(i)] != second.digits[static_cast<size_t>(i)])
                return digits[static_cast<size_t>(i)] <=> second.digits[static_cast<size_t>(i)];
        }
        return std::strong_ordering::equal;
    }

    BigInteger add(const BigInteger& second, signs sign1 = signs::pos) const {
        signs sign2 = mulsigns(second.sign, sign1);
        if (sign2 == signs::zero)
            return BigInteger(*this);
        if (sign == signs::zero)
            return BigInteger(second, sign2);
        BigInteger res = BigInteger();
        size_t size = std::max(digits.size(), second.digits.size()) + 1;
        int delta = 0;
        int zeros = 0;
        if (sign == sign2) {
            for (size_t i = 0; i < size; i++) {
                int now = get(i) + second.get(i) + delta;
                delta = now / BigIntConst::MOD;
                now = now % BigIntConst::MOD;
                res.upgrade(now, zeros);
            }
            res.sign = sign;
            return res;
        }
        const BigInteger* abs1 = this;
        const BigInteger* abs2 = &second;
        bool swapped = false;
        if (cmpabs(second) == std::strong_ordering::less) {
            std::swap(abs1, abs2);
            swapped = true;
        }
        for (size_t i = 0; i < size; i++) {
            int now = (*abs1).get(i) - (*abs2).get(i) + delta;
            delta = 0;
            if (now < 0) {
                delta = -1;
                now = now + BigIntConst::MOD;
            }
            res.upgrade(now, zeros);
        }
        res.sign = swapped ? sign2 : sign;
        if (zeros == static_cast<int>(size))
            res.sign = signs::zero;
        return res;
    }

    long double getfirst(size_t cnt) const {
        long double res = 0;
        long double power = static_cast<long double>(1) / BigIntConst::MOD;
        for (size_t i = 0; i < std::min(cnt / BigIntConst::DIGITS + 2, digits.size()); i++) {
            res += power * digits[digits.size() - i - 1];
            power /= BigIntConst::MOD;
        }
        while (res < static_cast<long double>(1) / static_cast<long double>(BigIntConst::TEN))
            res *= BigIntConst::TEN;
        return res;
    }

public:
    BigInteger() : sign(signs::zero) {}

    BigInteger(long long n) {
        if (n == 0) {
            sign = signs::zero;
        } else if (n > 0) {
            sign = signs::pos;
        } else {
            sign = signs::neg;
        }
        n = std::abs(n);
        while (n > 0) {
            digits.push_back(static_cast<int>(n % BigIntConst::MOD));
            n /= BigIntConst::MOD;
        }
    }

    BigInteger(const BigInteger& base, signs sign) : digits(base.digits), sign(sign) {}

    BigInteger& operator++() {
        *this += 1;
        return *this;
    }

    BigInteger& operator--() {
        *this -= 1;
        return *this;
    }

    BigInteger operator++(int) {
        BigInteger res = *this;
        ++(*this);
        return res;
    }

    BigInteger operator--(int) {
        BigInteger res = *this;
        --(*this);
        return res;
    }

    BigInteger operator-() const {
        BigInteger res = *this;
        res.sign = mulsigns(res.sign, signs::neg);
        return res;
    }

    string toString() const {
        string s = "";
        if (sign == signs::neg)
            s += '-';
        for (int i = static_cast<int>(digits.size()) - 1; i >= 0; i--) {
            string s0 = std::to_string(digits[static_cast<size_t>(i)]);
            if (i != static_cast<int>(digits.size()) - 1) {
                while (s0.size() < BigIntConst::DIGITS) {
                    s0 = "0" + s0;
                }
            }
            s += s0;
        }
        if (sign == signs::zero)
            s = "0";
        return s;
    }

    explicit operator bool() const {
        return sign != signs::zero;
    }

    BigInteger& operator+=(const BigInteger& second) {
        *this = add(second);
        return *this;
    }

    BigInteger& operator-=(const BigInteger& second) {
        *this = add(second, signs::neg);
        return *this;
    }

    BigInteger& operator*=(const BigInteger& second) {
        if (sign == signs::zero || second.sign == signs::zero) {
            digits.clear();
            sign = signs::zero;
            return *this;
        }
        if (second == BigIntConst::MOD) {
            digits.push_front(0);
            return *this;
        }
        if (second == -1) {
            sign = mulsigns(sign, signs::neg);
            return *this;
        }
        size_t n = 1;
        while (n < digits.size() || n < second.digits.size())
            n *= 2;
        n *= 2;
        vector<complex<double>> a(n, complex<double>(0, 0));
        for (size_t i = 0; i < digits.size(); i++) {
            a[i] = complex<double>(digits[i], 0);
        }
        for (size_t i = 0; i < second.digits.size(); i++) {
            a[i] = complex<double>(a[i].real(), second.digits[i]);
        }
        double phi = 2 * acos(-1) / static_cast<double>(n);
        complex<double> q = complex<double>(cos(phi), sin(phi));
        FFT(a, q, false);
        for (size_t i = 0; i <= n / 2; i++) {
            complex<double> v1 = a[i] / 2.0;
            complex<double> v2 = a[(n - i) % n] / 2.0;
            a[i] = (v1 + sopr(v2)) * divi(v1 - sopr(v2));
            a[(n - i) % n] = (v2 + sopr(v1)) * divi(v2 - sopr(v1));
        }
        FFT(a, q, true);
        digits.clear();
        long long delta = 0;
        size_t pos = 0;
        int cntzero = 0;
        while (pos < n || delta) {
            delta += static_cast<long long>(a[pos].real());
            if (delta % BigIntConst::MOD) {
                for (int i = 0; i < cntzero; i++)
                    digits.push_back(0);
                cntzero = 0;
                digits.push_back(static_cast<int>(delta % BigIntConst::MOD));
            } else {
                cntzero++;
            }
            delta /= BigIntConst::MOD;
            pos++;
        }
        sign = mulsigns(sign, second.sign);
        return *this;
    }

    int get(size_t id) const {
        if (id < digits.size())
            return digits[id];
        return 0;
    }

    size_t size() const {
        return digits.size();
    }
    BigInteger abs() const {
        BigInteger res = *this;
        if (sign == signs::neg)
            res.sign = signs::pos;
        return res;
    }

    int pop_front() {
        int res = digits.front();
        digits.pop_front();
        if (digits.empty())
            sign = signs::zero;
        return res;
    }

    std::strong_ordering operator<=>(const BigInteger& second) const {
        if (sign == signs::pos && second.sign != signs::pos)
            return std::strong_ordering::greater;
        if (sign == signs::neg && second.sign != signs::neg)
            return std::strong_ordering::less;
        if (sign == signs::zero)
            return 0 <=> static_cast<int>(second.sign);
        const BigInteger& swapped1 = (sign == signs::pos) ? *this : second;
        const BigInteger& swapped2 = (sign == signs::pos) ? second : *this;
        return swapped1.cmpabs(swapped2);
    }

    bool operator==(const BigInteger& second) const = default;

    friend std::istream& operator>>(std::istream& input, BigInteger& target);
    // couldn't unfriend these, they require many operations with signs and digits
    // also couldn't make them class members, as they require both classes BigInteger and PoweredInteger
    friend PoweredInteger divide(const BigInteger& first, const BigInteger& second, size_t precision);
    friend BigInteger& operator/=(BigInteger& first, const BigInteger& second);
};

std::istream& operator>>(std::istream& input, BigInteger& target) {
    target.digits.clear();
    target.sign = signs::pos;
    char c = 0;
    while (input.peek()) {
        if (std::isspace(input.peek())) {
            input.get(c);
        } else {
            break;
        }
    }
    bool started = false;
    vector<int> pool;
    while (input.get(c) && !std::isspace(c)) {
        if (started) {
            assert(c >= '0' && c <= '9');
            pool.push_back(c - '0');
        } else {
            if (c == '-')
                target.sign = signs::neg;
            if (c > '0' && c <= '9') {
                started = true;
                pool.push_back(c - '0');
            }
        }
    }
    std::reverse(pool.begin(), pool.end());
    for (int i = 0; i < static_cast<int>(pool.size()); i += BigIntConst::DIGITS) {
        int x = 0;
        for (int j = i + BigIntConst::DIGITS - 1; j >= i; j--) {
            if (j < static_cast<int>(pool.size())) {
                x *= BigIntConst::TEN;
                x += pool[static_cast<size_t>(j)];
            }
        }
        target.digits.push_back(x);
    }
    if (!started)
        target.sign = signs::zero;
    return input;
}

std::ostream& operator<<(std::ostream& output, const BigInteger& val) {
    output << val.toString();
    return output;
}

bool operator!=(const BigInteger& first, const BigInteger& second) {
    return !(first == second);
}

BigInteger operator+(const BigInteger& first, const BigInteger& second) {
    BigInteger res = first;
    res += second;
    return res;
}

BigInteger operator*(const BigInteger& first, const BigInteger& second) {
    BigInteger res = first;
    res *= second;
    return res;
}

BigInteger operator-(const BigInteger& first, const BigInteger& second) {
    BigInteger res = first;
    res -= second;
    return res;
}

class PoweredInteger {
public:
    BigInteger val;
    long long power;
    PoweredInteger(BigInteger val, long long power) : val(val), power(power) {}
    PoweredInteger() : val(BigInteger(0)), power(0) {}

    PoweredInteger operator*(const PoweredInteger& second) const {
        PoweredInteger res;
        res.val = val * second.val;
        res.power = power + second.power;
        return res;
    }

    PoweredInteger operator+(const PoweredInteger& second) const {
        long long minpower = std::min(power, second.power);
        PoweredInteger a = *this;
        PoweredInteger b = second;
        if (a.val) {
            while (a.power > minpower) {
                a.val *= BigIntConst::MOD;
                a.power--;
            }
        }
        if (b.val) {
            while (b.power > minpower) {
                b.val *= BigIntConst::MOD;
                b.power--;
            }
        }
        return PoweredInteger(a.val + b.val, minpower);
    }

    PoweredInteger operator-(const PoweredInteger& second) const {
        long long minpower = std::min(power, second.power);
        PoweredInteger a = *this;
        PoweredInteger b = second;
        if (a.val) {
            while (a.power > minpower) {
                a.val *= BigIntConst::MOD;
                a.power--;
            }
        }
        if (b.val) {
            while (b.power > minpower) {
                b.val *= BigIntConst::MOD;
                b.power--;
            }
        }
        return PoweredInteger(a.val - b.val, minpower);
    }

    void cut(int length) {  // rounds to closest
        int delta = 0;
        while (val.size() > static_cast<size_t>(length)) {
            delta = val.pop_front();
            power++;
        }

        if (delta >= BigIntConst::MOD / 2)
            val++;
    }

    string toString(int precision10) const {  // TODO: rewrite this shit
        string s = val.toString();
        string o = "";
        for (int j = 0; j < BigIntConst::DIGITS; j++)
            o += '0';
        if (power >= 0) {
            for (int i = 0; i < power; i++)
                s += o;
            if (precision10 > 0) {
                s.push_back('.');
                for (int i = 0; i < precision10; i++)
                    s.push_back('0');
            }
            return s;
        }

        bool neg = (s[0] == '-');
        string s0 = "";
        for (size_t i = neg; i < s.size(); i++)
            s0 += s[i];
        while (static_cast<int>(s0.length()) < -BigIntConst::DIGITS * power + 1) {
            s0 = "0" + s0;
        }
        if (-power * BigIntConst::DIGITS > precision10) {
            if (s0[static_cast<size_t>(static_cast<long long>(s0.size()) + power * BigIntConst::DIGITS +
                                       precision10)] >= '5') {
                int temp = 1;
                for (int i = precision10 % BigIntConst::DIGITS; i != BigIntConst::DIGITS; i++)
                    temp *= BigIntConst::TEN;
                PoweredInteger delta(temp, -precision10 / BigIntConst::DIGITS - 1);
                delta = delta + *this;
                s = delta.val.toString();
                neg = (s[0] == '-');
                s0 = "";
                for (size_t i = neg; i < s.size(); i++)
                    s0 += s[i];
                while (static_cast<int>(s0.length()) < -BigIntConst::DIGITS * delta.power + 1) {
                    s0 = "0" + s0;
                }
            }
        }
        string s1 = neg ? "-" : "";

        int cnt = 0;
        for (size_t i = 0; i < s0.length(); i++) {
            s1.push_back(s0[i]);
            if (cnt) {
                cnt++;
                if (cnt >= precision10 + 1)
                    break;
            }
            if (static_cast<int>(s0.length()) - static_cast<int>(i) - 1 == -BigIntConst::DIGITS * power) {
                if (precision10 == 0)
                    break;
                s1.push_back('.');
                cnt++;
            }
        }
        while (cnt < precision10 + 1) {
            s1.push_back('0');
            cnt++;
        }
        return s1;
    }

    explicit operator BigInteger() {  // rounds to zero
        BigInteger res = val;
        if (power > 0) {
            for (int i = 0; i < power; i++) {
                res *= BigIntConst::MOD;
            }
        } else {
            for (int i = 0; i < -power; i++) {
                if (res == 0)
                    return BigInteger(0);
                res.pop_front();
            }
        }
        return res;
    }

    explicit operator double() {
        double pw10 = pow(BigIntConst::MOD, static_cast<double>(power));
        double ans = 0;
        for (size_t i = 0; i < val.size(); i++) {
            ans += pw10 * val.get(i);
            pw10 *= BigIntConst::MOD;
        }
        if (val < 0)
            ans *= -1;
        return ans;
    }
};

std::ostream& operator<<(std::ostream& output, const PoweredInteger& val) {
    output << val.toString(BigIntConst::TEN * BigIntConst::TEN);
    return output;
}

PoweredInteger divide(const BigInteger& first, const BigInteger& second, size_t precision) {
    assert(second.sign != signs::zero);
    if (first.sign == signs::zero)
        return PoweredInteger(BigInteger(0), 0);
    int temp = second.pw10();
    signs ressign = mulsigns(first.sign, second.sign);
    if (temp != -1) {
        int sizediff = 1;
        for (int i = temp % BigIntConst::DIGITS; i < BigIntConst::DIGITS; i++) {
            sizediff *= BigIntConst::TEN;
        }
        PoweredInteger ans = PoweredInteger(sizediff * first, -temp / BigIntConst::DIGITS - 1);
        ans.val.sign = ressign;
        return ans;
    } else {
        long double firstiter = static_cast<long double>(1.0) / second.getfirst(BigIntConst::TEN);
        const int pwr = 8;
        PoweredInteger rev = PoweredInteger(
            BigInteger(static_cast<long long>(
                std::pow(static_cast<long double>(BigIntConst::TEN), static_cast<long double>(pwr)) * firstiter)),
            -pwr / BigIntConst::DIGITS);
        PoweredInteger two = PoweredInteger(2, 0);
        int sizediff = 1;
        int temp = second.digits[second.digits.size() - 1];
        while (temp * BigIntConst::TEN < BigIntConst::MOD) {
            temp *= BigIntConst::TEN;
            sizediff *= BigIntConst::TEN;
        }
        PoweredInteger cur = PoweredInteger(second * sizediff, -static_cast<long long>(second.digits.size()));
        cur.val.sign = signs::pos;
        rev.val.sign = signs::pos;
        int maxsigns = 1;
        while (static_cast<size_t>(maxsigns) < first.digits.size() + precision) {
            maxsigns *= 2;
        }
        maxsigns *= 2;
        for (int iter = 1; static_cast<size_t>((1 << std::max(0, (iter - 1)))) < first.digits.size() + precision;
             iter++) {
            PoweredInteger temp = cur * rev;
            temp.cut(maxsigns);
            rev = rev * (two - temp);
            rev.cut(maxsigns);
        }
        cur = PoweredInteger(first * sizediff, -static_cast<long long>(second.digits.size()));
        rev = cur * rev;
        rev.val.sign = ressign;
        return rev;
    }
}

BigInteger& operator/=(BigInteger& first, const BigInteger& second) {
    PoweredInteger res = divide(first, second, 0);
    signs ressign = res.val.sign;
    BigInteger ans = static_cast<BigInteger>(res);
    res.val.digits.clear();
    ans.add1();
    if ((ans * second).cmpabs(first) ==
        std::strong_ordering::greater)  // for example, 228/3 = 75.999999999999999999999999999999=76, but rounded down
                                        // to 75
        ans.sub1();
    if (ans.sign != signs::zero)
        ans.sign = ressign;
    first = ans;
    return first;
}

BigInteger operator/(const BigInteger& first, const BigInteger& second) {
    BigInteger res = first;
    res /= second;
    return res;
}

BigInteger& operator%=(BigInteger& first, const BigInteger& second) {
    first = first - (first / second) * second;
    return first;
}

BigInteger operator%(const BigInteger& first, const BigInteger& second) {
    BigInteger res = first;
    res %= second;
    return res;
}

BigInteger operator"" _bi(unsigned long long x) {
    BigInteger res(static_cast<long long>(x));
    return res;
}

BigInteger gcd(BigInteger a, BigInteger b) {
    if (!a)
        return b;
    if (!b)
        return a;
    a = a.abs();
    b = b.abs();
    while (b) {
        std::swap(a, b);
        b = b % a;
    }
    return a;
}

class Rational {
public:
    BigInteger numerator;
    BigInteger denominator;
    Rational() : numerator(0), denominator(1) {}
    Rational(const BigInteger& x) : numerator(x), denominator(1) {}
    Rational(const BigInteger& first, const BigInteger& second) : numerator(first), denominator(second) {
        // assert(q.sign != signs::zero);
        if (denominator < 0) {
            denominator *= -1;
            numerator *= -1;
        }
    }
    Rational(long long x) : numerator(x), denominator(1) {}

    Rational operator-() const {
        Rational res = *this;
        res.numerator *= -1;
        return res;
    }

    void normalize() {
        BigInteger div = gcd(numerator, denominator);
        numerator /= div;
        denominator /= div;
    }

    string toString() {
        normalize();
        if (!numerator)
            return "0";
        if (denominator == BigInteger(1))
            return numerator.toString();
        return numerator.toString() + "/" + denominator.toString();
    }

    string asDecimal(size_t precision10 = 0) {
        PoweredInteger res = divide(numerator, denominator, precision10 / BigIntConst::DIGITS + 2);
        return res.toString(static_cast<int>(precision10));
    }

    explicit operator double() {
        PoweredInteger res = divide(numerator, denominator, 2 * BigIntConst::TEN);
        return static_cast<double>(res);
    }

    Rational& operator+=(const Rational& second) {
        *this =
            Rational(numerator * second.denominator + second.numerator * denominator, denominator * second.denominator);
        normalize();
        return *this;
    }

    Rational& operator-=(const Rational& second) {
        *this =
            Rational(numerator * second.denominator - second.numerator * denominator, denominator * second.denominator);
        normalize();
        return *this;
    }

    Rational& operator*=(const Rational& second) {
        *this = Rational(numerator * second.numerator, denominator * second.denominator);
        normalize();
        return *this;
    }

    Rational& operator/=(const Rational& second) {
        *this = Rational(numerator * second.denominator, denominator * second.numerator);
        normalize();
        return *this;
    }
};

Rational operator+(const Rational& first, const Rational& second) {
    Rational res = first;
    res += second;
    return res;
}

Rational operator-(const Rational& first, const Rational& second) {
    Rational res = first;
    res -= second;
    return res;
}

Rational operator*(const Rational& first, const Rational& second) {
    Rational res = first;
    res *= second;
    return res;
}

Rational operator/(const Rational& first, const Rational& second) {
    Rational res = first;
    res /= second;
    return res;
}

std::strong_ordering operator<=>(const Rational& first, const Rational& second) {
    if (first.numerator > 0 && second.numerator <= 0)
        return std::strong_ordering::greater;
    if (first.numerator < 0 && second.numerator >= 0)
        return std::strong_ordering::less;
    if (!first.numerator)
        return 0 <=> second.numerator;
    return first.numerator * second.denominator <=> second.numerator * first.denominator;
}

bool operator==(const Rational& first, const Rational& second) {
    return first.numerator * second.denominator == second.numerator * first.denominator;
}

bool operator!=(const Rational& first, const Rational& second) {
    return !(first == second);
}

// EXTRA

std::istream& operator>>(std::istream& input, Rational& target) {
    BigInteger cur;
    input >> cur;
    target = Rational(cur, 1);
    return input;
}
// MATRIX

int gcd(int a, int b, int& x, int& y) {
    if (a == 0) {
        x = 0;
        y = 1;
        return b;
    }
    int res = gcd(b % a, a, y, x);
    x = x - (b / a) * y;
    return res;
}
int mod(int x, int MOD) {
    return (x % MOD + MOD) % MOD;
}

int inverse(int x, int MOD) {
    int a = 0, b = 0;
    gcd(x, MOD, a, b);
    return mod(a, MOD);
}

template <long long N, long long L, long long R>
struct Sqrt {
    static const long long value =
        ((((L + R + 1) / 2) * ((L + R + 1) / 2) <= N) ? Sqrt<N, ((L + R + 1) / 2), R>::value
                                                      : Sqrt<N, L, ((L + R + 1) / 2) - 1>::value);
};

template <long long N, long long R>
struct Sqrt<N, R, R> {
    static const long long value = R;
};

template <int N, int M>
struct PrimeHelper {
    static const bool value = (N % M == 0) ? false : PrimeHelper<N, M - 1>::value;
};

template <int N>
struct PrimeHelper<N, 1> {
    static const bool value = true;
};

template <int N>
struct Prime {
    static const bool value = PrimeHelper<N, Sqrt<N, 0, N>::value + 1>::value;
};

template <>
struct Prime<2> {
    static const bool value = true;
};

template <int N, int L, int R>
struct Log2 {
    static const int value = (((1 << ((L + R + 1) / 2)) <= N) ? Log2<N, ((L + R + 1) / 2), R>::value
                                                              : Log2<N, L, ((L + R + 1) / 2) - 1>::value);
};
template <int N, int R>
struct Log2<N, R, R> {
    static const int value = (1 << R);
};

template <int N>
class Residue {
private:
public:
    int val;

    Residue() : val(0) {}
    Residue(int x) : val(mod(x, N)) {}

    Residue<N>& operator+=(const Residue<N>& other) {
        val = (val + other.val) % N;
        return *this;
    }
    Residue<N>& operator-=(const Residue<N>& other) {
        val = mod(val - other.val, N);
        return *this;
    }
    Residue<N>& operator*=(const Residue<N>& other) {
        val = static_cast<int>(static_cast<long long>(val) * static_cast<long long>(other.val)) % N;
        return *this;
    }
    Residue<N>& operator/=(const Residue<N>& other) {
        static_assert(Prime<N>::value);
        Residue<N> rev = static_cast<Residue<N>>(inverse(other.val, N));
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

    Residue<N> operator+(const Residue<N>& other) const {
        Residue<N> res = *this;
        res += other;
        return res;
    }
    Residue<N> operator*(const Residue<N>& other) const {
        Residue<N> res = *this;
        res *= other;
        return res;
    }
    Residue<N> operator-(const Residue<N>& other) const {
        Residue<N> res = *this;
        res -= other;
        return res;
    }
    Residue<N> operator/(const Residue<N>& other) const {
        Residue<N> res = *this;
        res /= other;
        return res;
    }

    bool operator==(const Residue<N>& other) const {
        return val == other.val;
    }

    explicit operator int() {
        return val;
    }
};

template <size_t N, size_t M, typename Field = Rational>
class Matrix {
public:
    Field val[N][M];
    Matrix() {}
    Matrix(std::initializer_list<std::initializer_list<Field>> data) {
        size_t i = 0;
        for (auto line : data) {
            std::copy(line.begin(), line.end(), val[i]);
            i++;
        }
    }

    /*template <typename T>
    Matrix(int pos, T i) {
        static_assert(std::is_same<T, std::initializer_list<Field>>::value);
        std::copy(i.begin(), i.end(), val[pos]);
    }

    template <typename T, typename... R>
    Matrix(int pos, T i, R... r) : Matrix(pos + 1, r...) {
        static_assert(std::is_same<T, std::initializer_list<Field>>::value);
        std::copy(i.begin(), i.end(), val[pos]);
    }

    template <typename T, typename... R>
    Matrix(T i, R... r) : Matrix(0, i, r...) {}*/

    Matrix<N, M, Field>& operator+=(const Matrix<N, M, Field>& other) {
        for (size_t i = 0; i < N; i++) {
            for (size_t j = 0; j < M; j++) {
                val[i][j] += other.val[i][j];
            }
        }
        return *this;
    }
    Matrix<N, M, Field>& operator-=(const Matrix<N, M, Field>& other) {
        for (size_t i = 0; i < N; i++) {
            for (size_t j = 0; j < M; j++) {
                val[i][j] -= other.val[i][j];
            }
        }
        return *this;
    }
    Matrix<N, M, Field>& operator*=(const Field& a) {
        for (size_t i = 0; i < N; i++) {
            for (size_t j = 0; j < M; j++) {
                val[i][j] *= a;
            }
        }
        return *this;
    }

    bool operator==(const Matrix<N, M, Field>& other) const {
        for (size_t i = 0; i < N; i++) {
            for (size_t j = 0; j < M; j++) {
                if (val[i][j] != other.val[i][j])
                    return false;
            }
        }
        return true;
    }

    Matrix<N / 2, N / 2, Field>* getQuarters() const {
        static_assert(N == M);
        Matrix<N / 2, N / 2, Field>* quarters = new Matrix<N / 2, N / 2, Field>[2 + 2];
        for (size_t i = 0; i < N / 2; i++) {
            for (size_t j = 0; j < N / 2; j++) {
                quarters[0].val[i][j] = val[i][j + N / 2];
                quarters[1].val[i][j] = val[i][j];
                quarters[2].val[i][j] = val[i + N / 2][j];
                quarters[2 + 1].val[i][j] = val[i + N / 2][j + N / 2];
            }
        }
        return quarters;
    }

    template <size_t K>
    Matrix<K, K, Field> mul(const Matrix<K, K, Field>& other) const {
        static_assert(N == K && N == M);
        const int c3 = 3;  // clang-tidy is stupid, these are ids of coordinate quarters
        Matrix<K / 2, K / 2, Field>* A = getQuarters();
        Matrix<K / 2, K / 2, Field>* B = other.getQuarters();
        Matrix<K / 2, K / 2, Field> D = (A[1] + A[c3]).mul(B[1] + B[c3]);
        Matrix<K / 2, K / 2, Field> D1 = (A[0] - A[c3]).mul(B[2] + B[c3]);
        Matrix<K / 2, K / 2, Field> D2 = (A[2] - A[1]).mul(B[1] + B[0]);
        Matrix<K / 2, K / 2, Field> H1 = (A[0] + A[1]).mul(B[c3]);
        Matrix<K / 2, K / 2, Field> H2 = (A[2] + A[c3]).mul(B[1]);
        Matrix<K / 2, K / 2, Field> V1 = (A[c3]).mul(B[2] - B[1]);
        Matrix<K / 2, K / 2, Field> V2 = (A[1]).mul(B[0] - B[c3]);
        Matrix<K / 2, K / 2, Field> C[2 + 2] = {V2 + H1, D + D1 + V1 - H1, V1 + H2, D + D2 + V2 - H2};
        Matrix<K, K, Field> res;
        for (size_t i = 0; i < K / 2; i++) {
            for (size_t j = 0; j < K / 2; j++) {
                res.val[i][j + K / 2] = C[0].val[i][j];
                res.val[i][j] = C[1].val[i][j];
                res.val[i + K / 2][j] = C[2].val[i][j];
                res.val[i + K / 2][j + K / 2] = C[c3].val[i][j];
            }
        }
        delete[] A;
        delete[] B;
        return res;
    }

    Matrix<1, 1, Field> mul(const Matrix<1, 1, Field>& other) const {
        static_assert(N == 1 && N == M);
        Matrix<1, 1, Field> res;
        res.val[0][0] = val[0][0] * other.val[0][0];
        return res;
    }

    template <size_t K>
    Matrix<N, K, Field> operator*(const Matrix<M, K, Field>& other) const {
        const size_t sz =
            2 * static_cast<size_t>(std::max(std::max(Log2<N - 1, 0, 30>::value, Log2<M - 1, 0, 30>::value),
                                             Log2<K - 1, 0, 30>::value));
        Matrix<sz, sz, Field> first;
        Matrix<sz, sz, Field> second;
        for (size_t i = 0; i < sz; i++) {
            for (size_t j = 0; j < sz; j++) {
                first.val[i][j] = 0;
                second.val[i][j] = 0;
            }
        }
        for (size_t i = 0; i < N; i++) {
            for (size_t j = 0; j < M; j++) {
                first.val[i][j] = val[i][j];
            }
        }
        for (size_t i = 0; i < M; i++) {
            for (size_t j = 0; j < K; j++) {
                second.val[i][j] = other.val[i][j];
            }
        }
        first = first.mul(second);
        Matrix<N, K, Field> res;
        for (size_t i = 0; i < N; i++) {
            for (size_t j = 0; j < K; j++) {
                res.val[i][j] = first.val[i][j];
            }
        }
        return res;
    }

    Matrix<N, M, Field>& operator*=(const Matrix<N, M, Field>& other) {
        static_assert(N == M);
        Matrix<N, M, Field> res = *this * other;
        *this = res;
        return *this;
    }

    Matrix<N, M, Field> operator/=(const Field& a) {
        for (size_t i = 0; i < N; i++) {
            for (size_t j = 0; j < M; j++) {
                val[i][j] /= a;
            }
        }
    }
    Matrix<N, M, Field> operator+(const Matrix<N, M, Field>& other) const {
        Matrix<N, M, Field> res = *this;
        res += other;
        return res;
    }
    Matrix<N, M, Field> operator-(const Matrix<N, M, Field>& other) const {
        Matrix<N, M, Field> res = *this;
        res -= other;
        return res;
    }
    Matrix<N, M, Field> operator*(const Field& a) const {
        Matrix<N, M, Field> res = *this;
        res *= a;
        return res;
    }
    Matrix<N, M, Field> operator/(const Field& a) const {
        Matrix<N, M, Field> res = *this;
        res /= a;
        return res;
    }

    Matrix<M, N, Field> transposed() const {
        Matrix<M, N, Field> res;
        for (size_t i = 0; i < N; i++) {
            for (size_t j = 0; j < M; j++) {
                res.val[j][i] = val[i][j];
            }
        }
        return res;
    }

    std::array<Field, M> getRow(size_t x) const {
        std::array<Field, M> row;
        for (size_t i = 0; i < M; i++)
            row[i] = val[x][i];
        return row;
    }

    std::array<Field, N> getColumn(size_t y) const {
        std::array<Field, N> col;
        for (size_t i = 0; i < N; i++)
            col[i] = val[i][y];
        return col;
    }

    Field trace() const {
        static_assert(N == M);
        Field ans = Field(0);
        for (size_t i = 0; i < N; i++)
            ans += val[i][i];
        return ans;
    }

    Matrix<N, M, Field> triangulated(Field& det, size_t& rank, bool calcdet) const {
        if (calcdet)
            det = 1;
        Matrix<N, M, Field> res = *this;
        size_t start = 0;
        for (size_t j = 0; j < M; j++) {
            size_t notzero = N;
            for (size_t i = start; i < N; i++) {
                if (res.val[i][j] != 0) {
                    notzero = i;
                    break;
                }
            }
            if (notzero == N)
                continue;
            std::swap(res.val[start], res.val[notzero]);
            if (calcdet && notzero != start)
                det *= Field(-1);
            double t = static_cast<double>(clock()) / CLOCKS_PER_SEC;
            double t1 = 0, t2 = 0, t3 = 0;
            int sz = 0;
            int cnt = 1;
            for (size_t i = 0; i < N; i++) {
                if (res.val[i][j] != 0 && i != start) {
                    double t0 = static_cast<double>(clock()) / CLOCKS_PER_SEC;
                    Field a = res.val[start][j] / res.val[i][j];
                    t1 += static_cast<double>(clock()) / CLOCKS_PER_SEC - t0;
                    if (calcdet)
                        det /= a;
                    for (size_t j1 = 0; j1 < M; j1++) {
                        if constexpr (std::is_same<Rational, Field>::value) {
                            sz += res[i][j1].denominator.size() + res[i][j1].numerator.size();
                            cnt++;
                        }
                        t0 = static_cast<double>(clock()) / CLOCKS_PER_SEC;
                        res.val[i][j1] *= a;
                        t2 += static_cast<double>(clock()) / CLOCKS_PER_SEC - t0;
                        t0 = static_cast<double>(clock()) / CLOCKS_PER_SEC;
                        res.val[i][j1] -= res.val[start][j1];
                        t3 += static_cast<double>(clock()) / CLOCKS_PER_SEC - t0;
                    }
                }
            }
            if constexpr (std::is_same<Rational, Field>::value) {
                std::cerr << sz / cnt << " " << cnt << " " << static_cast<double>(clock()) / CLOCKS_PER_SEC - t << " "
                          << t1 << " " << t2 << " " << t3 << "\n";
            }
            /*if constexpr (std::is_same<Rational, Field>::value) {
                for (size_t i2 = 0; i2 < N; i2++) {
                    for (size_t j2 = 0; j2 < M; j2++) {
                        std::cerr << res.val[i2][j2].asDecimal() << " ";
                    }
                    std::cerr << "\n";
                }
            }
            std::cerr << "\n";
            if (j >= 1)
                assert(0);*/
            start++;
        }
        rank = start;
        if (calcdet) {
            for (size_t i = 0; i < std::min(N, M); i++)
                det *= res.val[i][i];
        }
        return res;
    }

    Field det() const {
        static_assert(N == M);
        Field res;
        size_t temp = 0;
        triangulated(res, temp, true);
        return res;
    }

    size_t rank() const {
        Field temp;
        size_t res = 0;
        triangulated(temp, res, false);
        return res;
    }
    Matrix<N, N, Field> inverted() const {
        static_assert(N == M);
        Matrix<N, 2 * N, Field> gauss;
        for (size_t i = 0; i < N; i++) {
            for (size_t j = 0; j < N; j++) {
                gauss.val[i][j] = val[i][j];
                gauss.val[i][j + N] = 0;
            }

            gauss.val[i][i + N] = 1;
        }
        Field temp1;
        size_t temp2 = 0;

        gauss = gauss.triangulated(temp1, temp2, false);
        /*for (size_t i = N - 1;; i--) {
            for (size_t i1 = 0; i1 < i; i1++) {
                if (gauss.val[i1][i] != 0) {
                    Field b = gauss.val[i][i] / gauss.val[i1][i];
                    for (size_t j = 0; j < 2 * N; j++) {
                        gauss.val[i1][j] *= b;
                        gauss.val[i1][j] -= gauss.val[i][j];
                    }
                }
            }
            if (i == 0)
                break;
        }*/
        for (size_t i = 0; i < N; i++) {
            for (size_t j = N; j < 2 * N; j++) {
                gauss.val[i][j] /= gauss.val[i][i];
            }
            gauss.val[i][i] = 1;
        }
        Matrix<N, N, Field> res;
        for (size_t i = 0; i < N; i++) {
            for (size_t j = 0; j < N; j++) {
                res.val[i][j] = gauss.val[i][j + N];
            }
        }
        return res;
    }

    Matrix<N, N, Field>& invert() {
        *this = inverted();
        return *this;
    }

    const Field* operator[](size_t x) const {
        return val[x];
    }

    Field* operator[](size_t x) {
        return val[x];
    }
};

template <size_t N, size_t M, typename Field>
Matrix<N, M, Field> operator*(const Field& a, const Matrix<N, M, Field>& m) {
    Matrix<N, M, Field> res = m;
    res *= a;
    return res;
}

template <size_t N, typename Field = Rational>
using SquareMatrix = Matrix<N, N, Field>;