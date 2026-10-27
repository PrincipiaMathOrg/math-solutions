#!/usr/bin/env python3
"""Finite-dimensional sanity checks for the infinite l1 counterexample.

This is not a substitute for the proof in proof-skeleton.md.  It checks the
index convention and identities on finite truncations, where every coordinate
used by a tested product is present.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product


def l1_norm(x: tuple[Fraction, ...]) -> Fraction:
    return sum((abs(value) for value in x), Fraction(0))


def apply_a(n: int, x: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    """A(n)x = x[n-1] e_n for n>=1; A(0)=0."""
    result = [Fraction(0) for _ in x]
    if n >= 1:
        result[n] = x[n - 1]
    return tuple(result)


def evolution(m: int, k: int, x: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    """The source convention A_m^k=A(m)...A(k+1), and A_m^m=I."""
    if k == m:
        return x
    result = x
    for n in range(k + 1, m + 1):
        result = apply_a(n, result)
    return result


def expected(m: int, k: int, x: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    if k == m:
        return x
    result = [Fraction(0) for _ in x]
    result[m] = x[k]
    return tuple(result)


def main() -> None:
    dimension = 9
    vectors = [
        tuple(Fraction(v) for v in values)
        for values in product((-2, -1, 0, 1, 2), repeat=4)
    ]
    vectors = [x + (Fraction(0),) * (dimension - len(x)) for x in vectors]

    product_checks = 0
    sum_checks = 0
    for m in range(dimension):
        for k in range(m + 1):
            for x in vectors:
                assert evolution(m, k, x) == expected(m, k, x)
                product_checks += 1
        for x in vectors:
            backward_sum = sum(
                (l1_norm(evolution(m, k, x)) for k in range(m + 1)),
                Fraction(0),
            )
            assert backward_sum <= 2 * l1_norm(x)
            sum_checks += 1

    # Every nontrivial evolution product has norm at least one, witnessed by e_k.
    nondecay_checks = 0
    for m in range(1, dimension):
        for k in range(m):
            basis = tuple(Fraction(int(j == k)) for j in range(dimension))
            assert l1_norm(evolution(m, k, basis)) == 1
            nondecay_checks += 1

    print(
        {
            "dimension": dimension,
            "vectors_checked": len(vectors),
            "product_identity_checks": product_checks,
            "backward_sum_checks": sum_checks,
            "nondecay_checks": nondecay_checks,
            "result": "all checks passed",
        }
    )


if __name__ == "__main__":
    main()

