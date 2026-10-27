"""Exact checks for the MathDB #333222 Bernstein-basis proof.

The script independently constructs U_n from its survival probabilities,
constructs G_n from the defining integrals, converts power coefficients to
Bernstein coefficients, and checks every closed formula using Fraction
arithmetic.  It is evidence for the algebra, not a substitute for the proof.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb


Polynomial = list[Fraction]  # coefficient of x**j is entry j


def harmonic(m: int) -> Fraction:
    return sum((Fraction(1, j) for j in range(1, m + 1)), Fraction())


def trim(poly: Polynomial) -> Polynomial:
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def add_shifted(
    target: Polynomial, source: Polynomial, shift: int, scale: Fraction
) -> None:
    required = shift + len(source)
    if len(target) < required:
        target.extend(Fraction() for _ in range(required - len(target)))
    for j, coefficient in enumerate(source):
        target[shift + j] += scale * coefficient


def integral_x_to_one(poly: Polynomial) -> Polynomial:
    """Return the polynomial integral from x to 1."""

    total = sum(
        (coefficient / (j + 1) for j, coefficient in enumerate(poly)),
        Fraction(),
    )
    result = [total]
    result.extend(-coefficient / (j + 1) for j, coefficient in enumerate(poly))
    return trim(result)


def u_from_survival(n: int) -> Polynomial:
    """Sum P(at most one exceedance among the first r trials), r=0..n-1."""

    result = [Fraction() for _ in range(n)]
    result[0] += 1
    for r in range(1, n):
        # x**r + r*(1-x)*x**(r-1)
        result[r - 1] += r
        result[r] += 1 - r
    return trim(result)


def u_closed(n: int) -> Polynomial:
    result = [Fraction() for _ in range(n)]
    for j in range(n - 1):
        result[j] = 2
    result[n - 1] = -(n - 2)
    return trim(result)


def g_from_definition(n: int) -> Polynomial:
    result = u_from_survival(n)
    for k in range(1, n):
        continuation = integral_x_to_one(u_from_survival(n - k))
        add_shifted(result, continuation, k - 1, Fraction(-1))
    return trim(result)


def g_closed(n: int) -> Polynomial:
    result = [
        3 - 2 * harmonic(n - j - 1) + 2 * harmonic(j) for j in range(n)
    ]
    result[-1] -= 2 * n
    return trim(result)


def bernstein_coefficients(power: Polynomial, degree: int) -> list[Fraction]:
    padded = power + [Fraction() for _ in range(degree + 1 - len(power))]
    return [
        sum(
            (
                padded[j] * Fraction(comb(k, j), comb(degree, j))
                for j in range(k + 1)
            ),
            Fraction(),
        )
        for k in range(degree + 1)
    ]


def bernstein_closed(n: int) -> list[Fraction]:
    d = n - 1
    result: list[Fraction] = []
    for k in range(d):
        r = d - k
        result.append(Fraction(n, r + 1) * (3 - 2 * harmonic(r)))
    result.append(Fraction(n))
    return result


def sign_variations(values: list[Fraction]) -> int:
    signs = [1 if value > 0 else -1 for value in values if value]
    return sum(signs[j] != signs[j - 1] for j in range(1, len(signs)))


def verify(limit: int = 200) -> None:
    for n in range(1, limit + 1):
        assert u_from_survival(n) == u_closed(n)
        assert g_from_definition(n) == g_closed(n)

        observed = bernstein_coefficients(g_closed(n), n - 1)
        expected = bernstein_closed(n)
        assert observed == expected

        if n >= 4:
            assert sign_variations(observed) == 1
            assert g_closed(n)[0] < 0
            assert sum(g_closed(n), Fraction()) == n
        else:
            assert sign_variations(observed) == 0

    assert g_closed(1) == [Fraction(1)]
    assert g_closed(2) == [Fraction(1), Fraction(1)]
    assert g_closed(3) == [Fraction(0), Fraction(3)]
    print(f"all exact checks passed for 1 <= n <= {limit}")
    print("G_1=1, G_2=1+x, G_3=3x")
    print("for n >= 4: one Bernstein sign variation and opposite endpoint signs")


if __name__ == "__main__":
    verify()
