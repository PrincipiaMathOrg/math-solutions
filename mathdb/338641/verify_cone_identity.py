#!/usr/bin/env python3
"""Exact low-memory checks for the formula resolving MathDB #338641.

Dependencies: Python 3.9+ standard library only.  Checks use explicit
exceptions, so they remain active under ``python -O``.
"""

from argparse import ArgumentParser
from fractions import Fraction
from math import comb


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def choose(n: int, r: int) -> int:
    """Binomial coefficient with the usual zero convention."""
    return comb(n, r) if 0 <= r <= n else 0


def source_layers(k: int) -> tuple[int, int, int, int, int]:
    """Return ``(n, layer_r1, layer_r3, layer_r5, full_odd_tail)``."""
    require(k >= 2, f"k must be at least 2, received {k}")
    m = 4 * k
    r = 2 * k
    n = m + 7
    layer_r1 = comb(m, r + 1)
    layer_r3 = (
        7 * comb(m, r)
        + 21 * comb(m, r + 1)
        + 7 * comb(m, r + 2)
        + comb(m, r + 3)
    )
    layer_r5 = sum(comb(7, i) * choose(m, r + 5 - i) for i in range(6))
    full_odd_tail = sum(comb(n, j) for j in range(r + 7, n + 1, 2))
    return n, layer_r1, layer_r3, layer_r5, full_odd_tail


def verify_one(k: int) -> tuple[int, int]:
    m = 4 * k
    r = 2 * k
    n, layer_r1, layer_r3, layer_r5, tail = source_layers(k)
    total = layer_r1 + layer_r3 + layer_r5 + tail

    # Complement symmetry plus the alternating upper-tail identity.
    tail_from_identity = (
        2 ** (n - 2)
        - Fraction(comb(n - 1, r + 3), 2)
        - comb(n, r + 5)
    )
    require(tail_from_identity.denominator == 1, f"nonintegral tail at k={k}")
    require(tail == tail_from_identity, f"odd-tail identity failed at k={k}")

    # Check each raw Vandermonde convolution before collecting symmetric terms.
    vandermonde_6 = sum(
        comb(6, i) * choose(m, r + 3 - i) for i in range(7)
    )
    require(vandermonde_6 == comb(n - 1, r + 3), f"Vandermonde-6 failed at k={k}")
    vandermonde_7 = sum(
        comb(7, i) * choose(m, r + 5 - i) for i in range(8)
    )
    require(vandermonde_7 == comb(n, r + 5), f"Vandermonde-7 failed at k={k}")

    B = [comb(m, r + i) for i in range(6)]
    require(
        Fraction(comb(n - 1, r + 3), 2)
        == 10 * B[0] + 15 * B[1] + 6 * B[2] + B[3],
        f"symmetric Vandermonde-6 collection failed at k={k}",
    )
    require(
        comb(n, r + 5)
        == B[5] + 7 * B[4] + 21 * B[3]
        + 36 * B[2] + 42 * B[1] + 21 * B[0],
        f"symmetric Vandermonde-7 collection failed at k={k}",
    )

    closed_total = 2 ** (n - 2) - 3 * comb(m, r)
    require(total == closed_total, f"closed cone identity failed at k={k}")
    require(total < 2 ** (n - 2), f"expected a strict deficit at k={k}")

    # Independent redundancy: compare with the source's neighboring D system
    # and its exact Lemma-11 difference.
    d_exceptional = layer_r3
    d_tail = sum(comb(n, j) for j in range(r + 5, n + 1, 2))
    d_total = d_exceptional + d_tail
    source_gap = comb(m, r - 2) + 6 * comb(m, r - 1)
    require(d_total - total == source_gap, f"D-minus-Cone gap failed at k={k}")
    return n, 3 * comb(m, r)


def main() -> None:
    parser = ArgumentParser()
    parser.add_argument("--max-k", type=int, default=249)
    args = parser.parse_args()
    require(args.max_k >= 2, "--max-k must be at least 2")

    first = verify_one(2)
    last = first
    for k in range(3, args.max_k + 1):
        last = verify_one(k)

    print("PASS: source layers, odd tail, both Vandermonde reductions,")
    print(f"      and exact cone deficit verified for k=2..{args.max_k}.")
    print(f"      k=2: n={first[0]}, deficit={first[1]}")
    print(
        f"      k={args.max_k}: n={last[0]}, "
        f"deficit has {len(str(last[1]))} decimal digits"
    )


if __name__ == "__main__":
    main()
