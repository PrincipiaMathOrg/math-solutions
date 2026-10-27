#!/usr/bin/env python3
"""Exact dependency checks for the counterexample to MathDB #355738."""

from fractions import Fraction


a = Fraction(2, 3)
b = Fraction(2, 3)

# The original function and the weight are separately locally integrable,
# while their aligned singularities in the even component are not.
assert 0 < a < 1
assert 0 < b < 1
assert a + b > 1


def truncated_power_integral(power: Fraction, reciprocal_cutoff: int) -> float:
    """Return integral from 1/N to 1 of t**(-power) dt."""

    cutoff = 1.0 / reciprocal_cutoff
    p = float(power)
    return (1.0 - cutoff ** (1.0 - p)) / (1.0 - p)


# Check algebraically on a generic finite coefficient vector that averaging
# f(z) and f(-z) extracts exactly the even residue class.
coefficients = [Fraction(3 * k - 7, k + 2) for k in range(12)]
even_projection = [c if k % 2 == 0 else Fraction(0) for k, c in enumerate(coefficients)]
averaged = [
    (c + ((-1) ** k) * c) / 2 for k, c in enumerate(coefficients)
]
assert averaged == even_projection

print(f"a={a}, b={b}, a+b={a+b}")
print("separate endpoint singularities: integrable")
print("aligned even-component singularity: nonintegrable")
print("truncated model integrals")
for reciprocal_cutoff in (10**3, 10**6, 10**9, 10**12):
    good = truncated_power_integral(a, reciprocal_cutoff)
    bad = truncated_power_integral(a + b, reciprocal_cutoff)
    print(
        f"  epsilon=1e-{len(str(reciprocal_cutoff)) - 1:02d} "
        f"power_2/3={good:.9f} power_4/3={bad:.9f}"
    )
print("Fourier residue projection identity: passed")
print("ALL CHECKS PASSED")
