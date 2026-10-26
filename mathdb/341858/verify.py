"""Exact checks supplementing the all-order proof. Requires SymPy."""
from pathlib import Path
from datetime import datetime, timezone
import json
import sympy as s

x, t = s.symbols("x t")


def constant(r):
    return (s.prod(s.factorial(j) for j in range(1, r)) ** 3
            / s.prod(s.factorial(j) for j in range(r, 2 * r)))


def normalized(r, value):
    return constant(r) * s.prod((value**2-j**2)**(r-j) for j in range(1, r))


def moment(k, shift, length):
    return s.cancel((s.bernoulli(k+1, shift+length)-s.bernoulli(k+1, shift))
                    / ((k+1)*length))


checks = {}
for r in range(1, 6):
    matrix = s.Matrix(r, r, lambda i, j: moment(i+j, x, t))
    assert s.expand(matrix.det(method="domain-ge")-normalized(r, t)) == 0
checks["symbolic_normalized_determinants"] = 5

for r in range(1, 5):
    def entry(i, j):
        m, v = divmod(j, 2)
        if i < r:
            return s.Integer(i == m)
        k = i-r+m+1
        return s.bernoulli(k, x if v == 0 else x+t)/k
    matrix = s.Matrix(2*r, 2*r, entry)
    expected = (-1)**(r*(r-1)//2)*t**r*normalized(r, t)
    assert s.expand(matrix.det(method="domain-ge")-expected) == 0
checks["original_block_determinants"] = 4

count = 0
for r in range(2, 9):
    for a in list(range(1, r))+list(range(-r+1, 0)):
        matrix = s.Matrix(r, r, lambda i, j: moment(i+j, 0, s.Integer(a)))
        assert matrix.rank() == abs(a)
        count += 1
checks["positive_and_negative_integer_ranks"] = count

for r in range(1, 11):
    assert s.Matrix(r, r, lambda i, j: s.Rational(1, i+j+1)).det() == constant(r)
checks["hilbert_leading_coefficients"] = 10

count = 0
for r in range(1, 9):
    for length in range(r+1, r+5):
        matrix = s.Matrix(r, r, lambda i, j: sum(s.Integer(a)**(i+j)
                                               for a in range(length)))
        hahn = s.prod(s.factorial(k)**3*s.factorial(length+k)
                      / (s.factorial(length-1-k)*s.factorial(r+k))
                      for k in range(r))
        assert matrix.det() == hahn == length**r*normalized(r, length)
        count += 1
checks["published_hahn_specialization"] = count

report = dict(checked_at_utc=datetime.now(timezone.utc).isoformat(),
              all_passed=True, sympy_version=s.__version__, groups=checks,
              verification_scope="Exact finite checks; general proof is in solution.tex.",
              reviewer="Authoring agent only; no independent review.",
              new_problem_credit=0)
Path(__file__).with_name("verification-results.json").write_text(
    json.dumps(report, indent=2)+"\n", encoding="utf-8", newline="\n")
print(json.dumps(report, indent=2))
