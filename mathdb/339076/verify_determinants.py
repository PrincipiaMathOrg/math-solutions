"""Exact supplemental checks; the all-size proof is in solution.tex."""
import json
from pathlib import Path

from flint import fmpz_poly

Q = fmpz_poly([0, 1])
ONE = fmpz_poly([1])
KAPPA = (1, 1, 0, -1, -1, 0)
LIMIT = 16


def det(matrix):
    """Fraction-free elimination with row pivoting, including zero determinants."""
    a = [row[:] for row in matrix]
    n = len(a)
    if not n:
        return ONE
    previous, sign = ONE, 1
    for k in range(n - 1):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None:
            return fmpz_poly()
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = a[i][j] * pivot - a[i][k] * a[k][j]
                a[i][j], remainder = divmod(numerator, previous)
                assert not remainder
        for i in range(k + 1, n):
            a[i][k] = fmpz_poly()
        previous = pivot
    return sign * a[-1][-1]


def square_sum(n):
    return n * (n - 1) * (2 * n - 1) // 6


def expected(n, shift):
    if shift == 0:
        return Q ** square_sum(n)
    if shift == 1:
        return KAPPA[n % 6] * Q ** (square_sum(n) + n * (n - 1) // 2)
    return sum((Q ** (square_sum(n) + n * n - j)
                for j in range(n + 1) if j % 3 != 2), fmpz_poly())


def main():
    moments = [ONE]
    for n in range(2 * LIMIT):
        moments.append(moments[n] + sum(
            (Q ** (r + 1) * moments[r] * moments[n - r - 1]
             for r in range(n)), fmpz_poly()))
    computed, rows = {}, []
    for n in range(LIMIT + 1):
        for shift in range(3):
            actual = det([[moments[i + j + shift] for j in range(n)]
                          for i in range(n)])
            assert actual == expected(n, shift), (n, shift)
            computed[n, shift] = actual
        if n % 3 == 0:
            normalized = sum((Q ** j for j in range(n + 1) if j % 3 != 1),
                             fmpz_poly())
        else:
            normalized = (ONE + Q) * sum(
                (Q ** (3 * j) for j in range(n // 3 + 1)), fmpz_poly())
        exponent = square_sum(n) + n * n - n + int(n % 3 == 2)
        assert computed[n, 2] == Q ** exponent * normalized
        assert normalized[0] == 1
        assert all(c in (0, 1) for c in normalized)
        rows.append(dict(n=n, exact_valuation=exponent,
                         normalized_coefficients=[int(c) for c in normalized]))
    for n in range(1, LIMIT):
        assert (computed[n + 1, 0] * computed[n - 1, 2]
                == computed[n, 0] * computed[n, 2] - computed[n, 1] ** 2)
    assert computed[3, 2] == Q ** 11 * (ONE + Q ** 2 + Q ** 3)
    certificate = dict(
        mathdb_number=339076, arithmetic="Exact integer polynomials, python-flint",
        determinant_checks=3 * (LIMIT + 1),
        normalized_formula_checks=LIMIT + 1, condensation_checks=LIMIT - 1,
        rows=rows, all_passed=True,
        limitation="Finite checks audit the universal condensation proof; "
                   "they do not establish source eligibility or priority.")
    path = Path(__file__).with_name("exact-certificate.json")
    path.write_text(json.dumps(certificate, indent=2) + "\n",
                    encoding="utf-8", newline="\n")
    print(json.dumps({k: v for k, v in certificate.items() if k != "rows"}))


if __name__ == "__main__":
    main()
