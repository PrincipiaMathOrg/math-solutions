"""Exact algebra and rational certificate for MathDB 335189.

Python 3 and SymPy are sufficient. The analytic remainder argument
and ground-state integration identity are proved in solution.tex.
This program does not approximate a Bessel zero.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import sympy as s


checks = {}


def check(name, condition):
    checks[name] = bool(condition)
    assert checks[name], name


v, t, h = s.symbols("v t h", positive=True)
calj = sum((-t / 4) ** k / (s.factorial(k) * s.rf(v + 1, k))
           for k in range(3))
nextj = calj.subs(v, v + 1)
logratio = s.expand((nextj - 1) - (nextj - 1) ** 2 / 2
                    - (calj - 1) + (calj - 1) ** 2 / 2)
c1 = 1 / (4 * (v + 1) * (v + 2))
c2 = (3 * v + 5) / (32 * (v + 1) ** 2 * (v + 2) ** 2 * (v + 3))
check("logarithmic_x2_coefficient", s.cancel(logratio.coeff(t, 1) - c1) == 0)
check("logarithmic_x4_coefficient", s.cancel(logratio.coeff(t, 2) - c2) == 0)
U = 3 * (2 * v + 7) * (2 * v + 8) / 10
T = 4 * (v + 1) * (v + 2) * (v + 3) / (3 * v + 5)
beta_ratio = 9 * s.factorial(4) / s.factorial(6) * (2 * v + 7) * (2 * v + 8)
check("beta_integral_quotient", s.cancel(beta_ratio - U) == 0)
poly = s.cancel(10 * (3 * v + 5) * (T - U))
check("shifted_positive_polynomial",
      s.expand(poly.subs(v, 28 + h)) == 4*h**3 + 246*h**2 + 3854*h + 2256)
check("all_shifted_coefficients_strictly_positive",
      all(c > 0 for c in s.Poly(poly.subs(v, 28 + h), h).all_coeffs()))
check("order30_quotient", U.subs(v, 30) == s.Rational(6834, 5))
check("order30_threshold", T.subs(v, 30) == s.Rational(130944, 95))
check("order30_fourth_coefficient_bound",
      s.cancel((c2 - 1/(8*(v+1)*(v+2)*U)).subs(v, 30))
      == -s.Rational(305, 394538811392))


def partial(nu, n):
    term = total = F(1)
    for k in range(1, n + 1):
        term *= F(-1, 4 * k * (nu + k))
        total += term
    return total


bottom = partial(30, 5)
top = partial(31, 4)
check("denominator_partial_sum",
      bottom == F(4748440055099, 4786893619200))
check("numerator_partial_sum", top == F(7660705361, 7720796160))
check("positive_denominator_partial_sum", bottom > 0)
ratio = top / bottom
check("rational_ratio", ratio == F(4749637323820, 4748440055099))
d = F(252139378, 10**12)
margin = d - (ratio - 1)
check("rational_ratio_majorant",
      margin == F(481473794211, 2374220027549500000000000) and margin > 0)
upper_log = d - d*d/2 + d*d*d/3
lower_log = F(1, 3968) + F(1, 2*3968) / F(6834, 5)
gap = lower_log - upper_log
check("logarithmic_gap_exact",
      gap == F(9597654965608638275835585186379,
               13240875000000000000000000000000000000000))
check("logarithmic_gap_strict", gap > F(7, 10**10))
check("positivity_on_unit_interval", 1 - F(1, 124) > 0)

# Verify the energy simplification symbolically before integration.
r = s.symbols("r", positive=True)
w = s.Function("w")(r)
u = r**v * w
energy = r*s.diff(u, r)**2 + v**2*u**2/r
check("energy_cross_term_identity",
      s.simplify(energy-r**(2*v+1)*s.diff(w,r)**2
                 -s.diff(v*r**(2*v)*w**2,r)) == 0)
# A general trial exponent gives the proposed follow-up formula.
p = s.symbols("p", positive=True)
general = p**2*(2*v+2*p+1)*(2*v+2*p+2)/(2*p*(2*p-1))
check("general_trial_formula",
      s.cancel(general-p*(2*v+2*p+1)*(2*v+2*p+2)/(2*(2*p-1))) == 0)
check("general_trial_specialization", s.cancel(general.subs(p,3)-U) == 0)

certificate = dict(
    problem=335189, all_passed=all(checks.values()),
    arithmetic="SymPy symbolic rational functions and Python Fraction",
    checks=checks, number_of_exact_checks=len(checks),
    explicit_counterexample=dict(nu=30, x=1, first_zero_squared_upper_bound="6834/5"),
    logarithmic_gap_lower_bound="7/10^10",
    rational_gap=str(gap),
    family="For each real nu>=28, all sufficiently small nonzero real x.",
    limits="Analytic signs and endpoint justifications are proved in the LaTeX text; no numerical Bessel zeros are used.",
)
Path(__file__).with_name("exact-certificate.json").write_text(
    json.dumps(certificate, indent=2) + "\n", encoding="utf-8", newline="\n")
print(json.dumps(certificate, indent=2))
