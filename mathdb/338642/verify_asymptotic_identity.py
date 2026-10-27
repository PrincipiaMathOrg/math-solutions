#!/usr/bin/env python3
"""Exact, low-memory checks for the formula resolving MathDB #338642.

Dependencies: Python 3.9+ standard library only.  All checks use explicit
exceptions and therefore remain active under ``python -O``.
"""

from argparse import ArgumentParser
from fractions import Fraction
from math import comb


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def source_count(k: int) -> tuple[int, int, int]:
    """Return ``(n, exceptional_layer, upper_odd_tail)``."""
    require(k >= 2, f"k must be at least 2, received {k}")
    m = 4 * k
    r = 2 * k
    n = m + 7
    exceptional = (
        7 * comb(m, r)
        + 21 * comb(m, r + 1)
        + 7 * comb(m, r + 2)
        + comb(m, r + 3)
    )
    tail = sum(comb(n, j) for j in range(r + 5, n + 1, 2))
    return n, exceptional, tail


def verify_one(k: int) -> tuple[int, int]:
    m = 4 * k
    r = 2 * k
    n, exceptional, tail = source_count(k)
    total = exceptional + tail
    excess = total - 2 ** (n - 2)

    # Exact alternating-tail identity.
    require(
        Fraction(tail) == 2 ** (n - 2) - Fraction(comb(n - 1, r + 3), 2),
        f"odd-tail identity failed at k={k}",
    )

    # Exact Vandermonde expansion, checked before using symmetry.
    vandermonde = sum(
        comb(6, i) * comb(m, r + 3 - i) for i in range(7)
    )
    require(vandermonde == comb(n - 1, r + 3), f"Vandermonde failed at k={k}")

    B0 = comb(m, r)
    B1 = comb(m, r + 1)
    B2 = comb(m, r + 2)
    B3 = comb(m, r + 3)
    require(
        Fraction(comb(n - 1, r + 3), 2)
        == 10 * B0 + 15 * B1 + 6 * B2 + B3,
        f"symmetric Vandermonde collection failed at k={k}",
    )
    require(excess == -3 * B0 + 6 * B1 + B2, f"layer subtraction failed at k={k}")

    closed = Fraction(
        2 * (4 * k + 3) * (2 * k - 1) * B0,
        (2 * k + 1) * (2 * k + 2),
    )
    require(closed.denominator == 1, f"closed form is not integral at k={k}")
    require(excess == closed, f"closed identity failed at k={k}")
    require(excess > 0, f"expected positive excess at k={k}")
    return n, excess


def main() -> None:
    parser = ArgumentParser()
    parser.add_argument("--max-k", type=int, default=249)
    args = parser.parse_args()
    require(args.max_k >= 2, "--max-k must be at least 2")

    first = verify_one(2)
    last = first
    for k in range(3, args.max_k + 1):
        last = verify_one(k)

    print("PASS: exact source count, odd-tail identity, Vandermonde reduction,")
    print(f"      and closed excess verified for k=2..{args.max_k}.")
    print(f"      k=2: n={first[0]}, excess={first[1]}")
    print(
        f"      k={args.max_k}: n={last[0]}, "
        f"excess has {len(str(last[1]))} decimal digits"
    )


if __name__ == "__main__":
    main()
