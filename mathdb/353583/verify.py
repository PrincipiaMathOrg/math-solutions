"""Exact checks for MathDB 353583. Requires SymPy; run from any directory."""
from pathlib import Path
from datetime import datetime, timezone
import json
import sympy as s

ROOT = Path(__file__).resolve().parent
x, t = s.symbols("x t")
h, N, v, j, u = s.symbols("h N v j u", integer=True, nonnegative=True)
limit = 240


def direct(n):
    total = 0
    for c in range(n // 6 + 1):
        for b in range((n - 6 * c) // 2 + 1):
            a = n - 2 * b - 6 * c
            length = a + b + c
            total += (-1) ** length * length ** 2
    return total


def identity(a, b):
    assert s.cancel(a - b) == 0


# 1. Independent coin-change dynamic programming counts partitions by length.
dp = [[0] * (limit + 1) for _ in range(limit + 1)]
dp[0][0] = 1
for part in (1, 2, 6):
    for n in range(part, limit + 1):
        for length in range(1, n + 1):
            dp[n][length] += dp[n - part][length - 1]
coefficients = [
    sum((-1) ** length * length ** 2 * count
        for length, count in enumerate(dp[n]))
    for n in range(limit + 1)
]
assert coefficients == [direct(n) for n in range(limit + 1)]

# 2. Euler derivatives of the bivariate product give the same coefficients.
F = 1 / ((1 - t*x) * (1 - t*x**2) * (1 - t*x**6))
G = s.cancel((t * s.diff(t * s.diff(F, t), t)).subs(t, -1))
num, den = [s.Poly(p, x) for p in s.fraction(G)]
assert den.nth(0) == 1
series = []
for n in range(limit + 1):
    series.append(num.nth(n) - sum(
        den.nth(q) * series[n-q] for q in range(1, min(n, den.degree())+1)))
assert series == coefficients

# 3. Universal alternating-square identities, using the adjacent pairs.
pair = (N - 2*v)**2 - (N - 2*v - 1)**2
identity(pair, 2*N - 4*v - 1)
odd = s.summation(pair, (v, 0, h))
even = s.summation(pair, (v, 0, h-1)) + (N - 2*h)**2
identity(odd, (h+1) * (2*N - 2*h - 1))
identity(even, N**2 - 2*h*N + 2*h**2 + h)
assert even.subs(h, 0).expand() == N**2

# 4. Symbolic pairing over c, exact summation, and positive final factors.
E = odd.subs({h: 3*v+1, N: 2*j+6+10*v})
O = even.subs({h: 3*v, N: 2*j+1+10*v})
identity(E-O, -16*v**2 + (38-16*j)*v - 4*j**2 + 4*j + 17)
closed = -(j+1) * (52*j**2 - 61*j - 51) / 3
identity(s.summation(E-O, (v, 0, j)), closed)
negative = -(u+3) * (52*u**2 + 147*u + 35) / 3
identity(closed.subs(j, u+2), negative)
assert all(c > 0 for c in s.Poly(-3*negative, u).all_coeffs())
for jj in range(101):
    assert direct(12*jj+6) == closed.subs(j, jj)
assert direct(30) == -35

result = dict(
    checked_at_utc=datetime.now(timezone.utc).isoformat(),
    passed=True, groups=4, arithmetic="Exact integers and rational symbolic identities",
    partition_counts=dict(n_min=0, n_max=limit, values=limit+1),
    generating_function=dict(numerator=str(s.factor(num.as_expr())),
                             denominator=str(s.factor(den.as_expr())),
                             coefficient_values=limit+1),
    alternating_square_lemmas="Both universal polynomial identities verified",
    progression=dict(symbolic_identity=str(closed), values_checked=101,
                     first_n=6, last_n=1206, negative_formula=str(negative),
                     first_negative_progression_value=dict(n=30, value=-35)),
    limitations="Finite checks supplement the written proof; no proof assistant.")
(ROOT / "verification-results.json").write_text(
    json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
print(json.dumps(result, indent=2))
