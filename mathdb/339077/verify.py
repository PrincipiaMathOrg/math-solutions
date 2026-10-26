"""Exact finite counterexample; run with Python and python-flint."""
from datetime import datetime, timezone
from itertools import permutations
from pathlib import Path
import json

from flint import fmpz_poly

Q = fmpz_poly([0, 1])
ONE = fmpz_poly([1])
ZERO = fmpz_poly()


def determinant(matrix):
    """Bareiss elimination with exact polynomial divisions and row pivoting."""
    a = [row[:] for row in matrix]
    n = len(a)
    previous, sign = ONE, 1
    for k in range(n - 1):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None:
            return ZERO
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                a[i][j], rem = divmod(
                    a[i][j] * pivot - a[i][k] * a[k][j], previous)
                assert not rem
        for i in range(k + 1, n):
            a[i][k] = ZERO
        previous = pivot
    return sign * a[-1][-1]


def main():
    groups = []
    integers = [1]
    moments = [ONE]
    for n in range(11):
        integers.append(integers[n] + sum(
            (-1) ** (r + 1) * integers[r] * integers[n - r - 1]
            for r in range(n)))
        moments.append(moments[n] + sum(
            (Q ** (r + 1) * moments[r] * moments[n - r - 1]
             for r in range(n)), ZERO))
    expected = [1, 1, 0, 0, 1, 1, -1, -1, 3, 3, -6, -6]
    assert integers == expected
    assert [int(m(-1)) for m in moments] == integers
    groups.append(dict(name="defining recurrence and specialization",
                       passed=True, moments=integers))

    matrix = [[integers[i + j + 3] for j in range(5)] for i in range(5)]
    leibniz = 0
    for perm in permutations(range(5)):
        inversions = sum(perm[i] > perm[j] for i in range(5)
                         for j in range(i + 1, 5))
        term = (-1) ** inversions
        for i, j in enumerate(perm):
            term *= matrix[i][j]
        leibniz += term
    a = [row[:] for row in matrix]
    a[0], a[1] = a[1], a[0]
    for k in range(2):
        assert a[k][k] == 1
        for i in range(k + 1, 5):
            factor = a[i][k]
            a[i] = [x - factor * y for x, y in zip(a[i], a[k])]
    block = [row[2:] for row in a[2:]]
    assert block == [[2, 2, -2], [2, 2, -3], [-2, -3, 1]]
    block[1] = [x - y for x, y in zip(block[1], block[0])]
    block[2] = [x + y for x, y in zip(block[2], block[0])]
    assert block == [[2, 2, -2], [0, 0, -1], [0, -1, -1]]
    assert -2 * (0 * (-1) - (-1) * (-1)) == leibniz == 2
    groups.append(dict(name="Leibniz sum and displayed row certificate",
                       passed=True, permutations=120, determinant=leibniz,
                       matrix=matrix))

    poly_matrix = [[moments[i + j + 3] for j in range(5)] for i in range(5)]
    actual = determinant(poly_matrix)
    normalized = ONE + 2 * Q + 2 * Q ** 3 + 2 * Q ** 4 + Q ** 6 + 2 * Q ** 7
    assert actual == -Q ** 62 * normalized
    quotient, remainder = divmod(actual, ONE + Q ** 3)
    assert remainder == fmpz_poly([2])
    assert quotient * (ONE + Q ** 3) + remainder == actual
    groups.append(dict(name="full polynomial determinant and division",
                       passed=True, valuation=62, normalized_coefficients=
                       [int(c) for c in normalized], remainder=2))

    # Motzkin walk weights: up=1; horizontal at height h=q^h;
    # down from height h=q^(2h-1). This uses a height-state dynamic
    # program, separate from the first-return convolution above.
    row = [ONE] + [ZERO] * 12
    walk_moments = [ONE]
    for length in range(1, 12):
        nxt = [ZERO] * 13
        for height in range(12):
            nxt[height] += row[height] * Q ** height
            nxt[height + 1] += row[height]
            if height:
                nxt[height - 1] += row[height] * Q ** (2 * height - 1)
        row = nxt
        walk_moments.append(row[0])
    assert walk_moments == moments
    groups.append(dict(name="independent weighted-walk moment computation",
                       passed=True, coefficientwise_comparisons=12))
    result = dict(mathdb_number=339077, passed=True, exact_groups=4,
                  arithmetic="Exact integers and integer polynomials",
                  verified_at_utc=datetime.now(timezone.utc).isoformat(),
                  groups=groups, limitation="Finite exact counterexample; "
                  "no source eligibility or independent peer review established.")
    Path(__file__).with_name("verification-results.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(dict(passed=True, exact_groups=4,
                         determinant_at_minus_one=2, polynomial_remainder=2)))


if __name__ == "__main__":
    main()
