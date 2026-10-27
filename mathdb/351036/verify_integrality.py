"""Exact low-memory checks for the repaired MathDB #351036 conjecture.

No floating-point root-of-unity arithmetic is used.  A sum is represented by
its polynomial in a primitive k-th root and reduced modulo the cyclotomic
polynomial Phi_k.
"""

from __future__ import annotations

from functools import lru_cache
from math import gcd, isqrt


def divisors(n: int) -> list[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def phi(n: int) -> int:
    ans = n
    p = 2
    m = n
    while p * p <= m:
        if m % p == 0:
            ans -= ans // p
            while m % p == 0:
                m //= p
        p += 1
    if m > 1:
        ans -= ans // m
    return ans


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % p for p in range(3, isqrt(n) + 1, 2))


def prime_in_class(a: int, n: int) -> int:
    """Small witness q = a (mod n), used only in finite test ranges."""
    if n == 1:
        return 2
    q = a % n
    if q < 2:
        q += n
    while not is_prime(q):
        q += n
    return q


def trim(p: list[int]) -> list[int]:
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def divide_monic_exact(num: list[int], den: list[int]) -> list[int]:
    num = num[:]
    q = [0] * max(1, len(num) - len(den) + 1)
    while len(num) >= len(den):
        c = num[-1]
        shift = len(num) - len(den)
        q[shift] = c
        for j, value in enumerate(den):
            num[shift + j] -= c * value
        trim(num)
    assert num == [0]
    return trim(q)


_cyclotomics: dict[int, list[int]] = {}


def cyclotomic(n: int) -> list[int]:
    if n not in _cyclotomics:
        p = [-1] + [0] * (n - 1) + [1]
        for d in divisors(n):
            if d < n:
                p = divide_monic_exact(p, cyclotomic(d))
        _cyclotomics[n] = p
    return _cyclotomics[n]


def poly_mod(num: list[int], den: list[int]) -> list[int]:
    num = trim(num[:])
    while len(num) >= len(den):
        c = num[-1]
        shift = len(num) - len(den)
        for j, value in enumerate(den):
            num[shift + j] -= c * value
        trim(num)
    return num


def geometric_mod(n: int, a: int, d: int, i: int) -> int:
    return sum(pow(a, i * ell, n) for ell in range(d)) % n if n > 1 else 0


@lru_cache(maxsize=None)
def gcd_word(n: int, a: int, d: int) -> tuple[int, ...]:
    return tuple(
        gcd(n, geometric_mod(n, a, d, i)) for i in range(1, phi(n) + 1)
    )


@lru_cache(maxsize=None)
def fourier_numerator(n: int, a: int, d: int, k: int) -> tuple[int, ...]:
    coeffs = [0] * k
    for i, value in enumerate(gcd_word(n, a, d), start=1):
        coeffs[i % k] += value
    return tuple(coeffs)


def reduced_value(n: int, a: int, d: int, k: int) -> list[int]:
    return poly_mod(list(fourier_numerator(n, a, d, k)), cyclotomic(k))


def coprime_part(n: int, a: int) -> int:
    n0 = 1
    m = n
    p = 2
    while p * p <= m:
        if m % p == 0:
            power = 1
            while m % p == 0:
                m //= p
                power *= p
            if a % p:
                n0 *= power
        p += 1
    if m > 1 and a % m:
        n0 *= m
    return n0


def assert_integral(n: int, a: int, d: int, k: int) -> int:
    h = phi(n)
    rem = reduced_value(n, a, d, k)
    assert all(c == 0 for c in rem[1:]), (n, a, d, k, rem)
    assert rem[0] % h == 0, (n, a, d, k, rem, h)
    return rem[0] // h


def mobius(n: int) -> int:
    sign = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
            while n % p == 0:
                n //= p
        p += 1
    return -sign if n > 1 else sign


def ramanujan(m: int, t: int) -> int:
    return sum(s * mobius(m // s) for s in divisors(gcd(m, t)))


def divisor_formula(n: int, a: int, d: int, k: int) -> int:
    """Ramanujan-divisor formula after deleting prime factors dividing a."""
    n0 = coprime_part(n, a)
    h0 = phi(n0)
    if h0 % k:
        return 0
    numerator = sum(
        gcd(n0, geometric_mod(n0, a, d, g))
        * ramanujan(h0 // g, h0 // k)
        for g in divisors(h0)
    )
    assert numerator % h0 == 0
    return numerator // h0


def main() -> None:
    # The literal MathDB statement lacks k | phi(n) and is false.
    literal = reduced_value(2, 2, 1, 3)
    assert literal == [0, 1]

    cases = 0
    reduction_cases = 0
    transfer_cases = 0
    even_function_checks = 0
    divisor_formula_checks = 0
    for n in range(1, 121):
        h = phi(n)
        for a in range(1, 17):
            n0 = coprime_part(n, a)
            h0 = phi(n0)
            q = prime_in_class(a, n) if gcd(a, n) == 1 else None
            for d in range(1, 11):
                word0 = gcd_word(n0, a, d)
                for i, value in enumerate(word0, start=1):
                    expected = gcd(
                        n0, geometric_mod(n0, a, d, gcd(i, h0))
                    )
                    assert value == expected
                    even_function_checks += 1
                if q is not None:
                    assert gcd_word(n, a, d) == gcd_word(n, q, d)
                    transfer_cases += 1
                for k in divisors(h):
                    value = assert_integral(n, a, d, k)
                    cases += 1
                    assert value == divisor_formula(n, a, d, k)
                    divisor_formula_checks += 1

                    # Verify the nonunit block decomposition exactly in
                    # Z[x]/(Phi_k), after clearing both averages.
                    lhs = fourier_numerator(n, a, d, k)
                    if h0 % k:
                        assert poly_mod(list(lhs), cyclotomic(k)) == [0]
                    else:
                        rhs = fourier_numerator(n0, a, d, k)
                        length = max(len(lhs), len(rhs))
                        diff = [0] * length
                        for j in range(length):
                            diff[j] = h0 * (lhs[j] if j < len(lhs) else 0)
                            diff[j] -= h * (rhs[j] if j < len(rhs) else 0)
                        assert poly_mod(diff, cyclotomic(k)) == [0]
                    reduction_cases += 1

    print("literal counterexample: n=2, a=2, d=1, k=3 -> zeta_3")
    print(f"corrected exact integrality cases: {cases}")
    print(f"nonunit decomposition checks: {reduction_cases}")
    print(f"coprime prime-transfer checks: {transfer_cases}")
    print(f"h-even function checks: {even_function_checks}")
    print(f"Ramanujan-divisor formula checks: {divisor_formula_checks}")


if __name__ == "__main__":
    main()
