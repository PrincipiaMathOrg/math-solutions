"""Exact certificates for the Hoggatt infinite log-convexity counterexamples."""
from datetime import datetime, timezone
from fractions import Fraction as F
from math import comb, prod
from pathlib import Path
import json
import sympy as s


def binomial_entry(n, k, m):
    N = n + m - 2
    return F(prod(comb(N, k + i) for i in range(m)),
             prod(comb(N, j) for j in range(1, m)))


def box_entry(k, ell, m):
    return prod((F(m + i + j - 1, i + j - 1)
                 for i in range(1, k + 1) for j in range(1, ell + 1)), start=F(1))


def sequence(m, end):
    a = [sum(binomial_entry(n, k, m) for k in range(n)) for n in range(1, end + 1)]
    assert all(x.denominator == 1 for x in a)
    return [int(x) for x in a]


def step(row):
    return [row[i] * row[i + 2] - row[i + 1] ** 2 for i in range(len(row) - 2)]


def triangle(row, order):
    rows = [row]
    for _ in range(order):
        rows.append(step(rows[-1]))
    return rows


def main():
    started = datetime.now(timezone.utc).isoformat()
    groups = []
    count = 0
    for m in range(1, 13):
        for n in range(1, 13):
            for k in range(n):
                a = binomial_entry(n, k, m)
                b = box_entry(k, n - 1 - k, m)
                assert a == b and a.denominator == 1
                count += 1
    groups.append(dict(name='two_defining_products', status='passed', exact_entry_comparisons=count))

    expected4 = [
        [1,2,7,32,177,1122,7898,60398,494078,4274228],
        [3,15,215,4575,139062,5388152,254309640,14041752660],
        [420,22400,8967705,5312555556,6332625182576,10985704681554720],
        [3264676100,38581511487375,28565867977326238944,18260024739573021120028544],
        [91769773432681865098581647775,-111509459048444462640611465400686603136]]
    expected5 = [1,2,8,44,310,2606,25202,272582,3233738,41454272]
    rows4 = triangle(sequence(4, 10), 4)
    rows5 = triangle(sequence(5, 10), 4)
    assert rows4 == expected4 and rows5[0] == expected5
    assert rows5[4][1] == -44045680773437284570849713497906508911110782976
    assert rows4[4][1] < 0 and rows5[4][1] < 0
    groups.append(dict(name='finite_fourth_iterate_certificates', status='passed',
                       starting_index=1, negative_index=2, rows_m4=rows4, rows_m5=rows5))

    m = s.symbols('m')
    row = []
    for n in range(2, 9):
        p = sum(s.prod(m + i + j - 1 for i in range(1, k + 1)
                       for j in range(1, n - k)) /
                s.Integer(prod(i + j - 1 for i in range(1, k + 1)
                               for j in range(1, n - k))) for k in range(n))
        p = s.Poly(p, m)
        assert p.degree() <= (n - 1) ** 2 // 4
        row.append(p)
    symbolic = triangle(row, 3)[3][0].as_expr()
    coefficients = [1,42,723,6462,27742,-16148,-934842,-5962420,-21758691,
                    -53818158,-97778329,-138523978,-159475276,-154920392,
                    -129902448,-88784352,-37081152,-2892672]
    P = s.Poly.from_list(coefficients, m).as_expr()
    Q = m**4 + 9*m**3 + 26*m**2 + 36*m + 72
    expected = -m**4*(m-1)**4*(m+1)**5*(m+2)**2*Q*P/s.Integer(1547934105600)
    assert s.Poly(symbolic - expected, m).is_zero
    assert s.Poly(symbolic, m).degree() == 36
    # Independent evaluation of the source binomial sums at 37 points checks
    # the degree-36 identity without using symbolic factorization.
    for value in range(1, 38):
        direct = triangle(sequence(value, 8)[1:], 3)[3][0]
        assert direct == expected.subs(m, value)
    groups.append(dict(name='degree_36_identity', status='passed',
                       degree=36, independent_exact_evaluation_points=37,
                       polynomial=str(s.factor(expected))))

    assert all(c > 0 for c in coefficients[:5])
    assert all(c < 0 for c in coefficients[5:])
    assert P.subs(m, 6) == 264264378826752
    shifted = s.Poly(P.subs(m, m + 6), m)
    assert all(c > 0 for c in shifted.all_coeffs())
    # The manuscript proves that P(m)/m^13 is strictly increasing for m>0.
    # This independent shifted-coefficient certificate proves the same sign
    # on m>=6 over the reals, not merely at finitely many integer parameters.
    groups.append(dict(name='uniform_positive_polynomial_certificate', status='passed',
                       P_at_6=str(P.subs(m, 6)), positive_shift=6,
                       P_shifted_coefficients_descending=list(map(str, shifted.all_coeffs()))))
    result = dict(status='passed', started_at_utc=started,
                  checked_at_utc=datetime.now(timezone.utc).isoformat(),
                  arithmetic='Exact integers and rationals only', sympy_version=s.__version__,
                  groups=groups)
    Path(__file__).with_name('verification-results.json').write_text(
        json.dumps(result, indent=2) + '\n', encoding='utf-8', newline='\n')
    print(json.dumps(dict(status='passed', groups=len(groups), checked_at_utc=result['checked_at_utc'])))


if __name__ == '__main__':
    main()
