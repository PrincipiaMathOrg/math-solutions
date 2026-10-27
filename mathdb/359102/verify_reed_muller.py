#!/usr/bin/env python3
"""Exact finite checks for the Reed--Muller construction in MathDB #359102.

The all-r distance and duality facts are proved in solution.md.  This script
independently constructs the first three block codes, exhausts their words,
checks every projection on at most four coordinates, and checks exact complex
second/fourth moments.  It uses only the Python standard library.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from math import comb


def require(condition: bool, message: object) -> None:
    if not condition:
        raise AssertionError(message)


def gf2_rank(rows: list[int]) -> int:
    work = [row for row in rows if row]
    rank = 0
    while work:
        pivot = max(work)
        work.remove(pivot)
        lead = pivot.bit_length() - 1
        work = [row ^ pivot if (row >> lead) & 1 else row for row in work]
        rank += 1
    return rank


def monomial_masks(r: int, degree: int) -> list[int]:
    masks: list[int] = []
    for size in range(degree + 1):
        for variables in combinations(range(r), size):
            mask = 0
            for variable in variables:
                mask |= 1 << variable
            masks.append(mask)
    return masks


def rm_rows(r: int, degree: int) -> list[int]:
    """Generator rows as bitsets indexed by points of F_2^r."""

    rows: list[int] = []
    for monomial in monomial_masks(r, degree):
        row = 0
        for point in range(1 << r):
            if point & monomial == monomial:
                row |= 1 << point
        rows.append(row)
    return rows


def codewords(rows: list[int]) -> list[int]:
    words = [0]
    for row in rows:
        words += [word ^ row for word in words]
    return words


def minimum_weight(words: list[int]) -> int:
    return min(word.bit_count() for word in words if word)


def column_vectors(rows: list[int], length: int) -> list[int]:
    columns: list[int] = []
    for coordinate in range(length):
        column = 0
        for index, row in enumerate(rows):
            column |= ((row >> coordinate) & 1) << index
        columns.append(column)
    return columns


def check_moment(words: list[int], coefficients: list[tuple[int, int]]) -> None:
    second = 0
    fourth = 0
    for word in words:
        real = 0
        imaginary = 0
        for index, (a, b) in enumerate(coefficients):
            sign = -1 if (word >> index) & 1 else 1
            real += sign * a
            imaginary += sign * b
        square = real * real + imaginary * imaginary
        second += square
        fourth += square * square

    count = len(words)
    sigma_squared = sum(a * a + b * b for a, b in coefficients)
    require(Fraction(second, count) == sigma_squared, ("second moment", second))
    require(
        Fraction(fourth, count) <= 3 * sigma_squared * sigma_squared,
        ("fourth moment", fourth),
    )


def main() -> None:
    total_words = 0
    total_projections = 0
    moment_tests = 0

    for r in range(3, 6):
        length = 1 << r
        rows = rm_rows(r, 2)
        dual_rows = rm_rows(r, r - 3)
        expected_dimension = sum(comb(r, degree) for degree in range(3))
        expected_dual_dimension = length - expected_dimension

        require(gf2_rank(rows) == expected_dimension, ("dimension", r))
        require(
            gf2_rank(dual_rows) == expected_dual_dimension,
            ("dual dimension", r),
        )
        for row in rows:
            for dual_row in dual_rows:
                require((row & dual_row).bit_count() % 2 == 0, ("orthogonal", r))

        words = codewords(rows)
        dual_words = codewords(dual_rows)
        require(len(words) == 1 << expected_dimension, ("code size", r))
        require(len(dual_words) == 1 << expected_dual_dimension, ("dual size", r))
        require(minimum_weight(words) == length // 4, ("minimum distance", r))
        require(minimum_weight(dual_words) == 8, ("dual minimum distance", r))
        total_words += len(words) + len(dual_words)

        columns = column_vectors(rows, length)
        projections = 0
        for size in range(1, 5):
            for selected in combinations(columns, size):
                require(gf2_rank(list(selected)) == size, ("projection", r, size))
                projections += 1
        total_projections += projections

        coefficient_families = [
            [((3 * i + 1) % 7 - 3, (5 * i + 2) % 9 - 4) for i in range(length)],
            [((i * i + 2) % 11 - 5, (i * i * i + 1) % 7 - 3) for i in range(length)],
        ]
        for coefficients in coefficient_families:
            check_moment(words, coefficients)
            moment_tests += 1

        print(
            f"r={r} length={length} dim={expected_dimension} "
            f"dual_dim={expected_dual_dimension} dmin={length // 4} "
            f"dual_dmin=8 projections={projections}"
        )

    require(total_projections == 44_126, total_projections)
    require(moment_tests == 6, moment_tests)
    print(f"exhausted_codewords={total_words}")
    print(f"checked_coordinate_projections={total_projections}")
    print(f"checked_exact_complex_moments={moment_tests}")
    print("minimum_squared_separation=1")
    print("PASS")


if __name__ == "__main__":
    main()
