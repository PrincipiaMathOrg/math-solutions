"""Exact and Arb-certified checks for MathDB problem #364074.

Dependencies:
    Python 3.9+
    python-flint (tested with Arb at 220-bit precision)

The script verifies the finite range 8 <= n <= 10000 using exact integer
arithmetic, then certifies every numerical inequality in the effective
circle-method proof using Arb real balls.  It deliberately uses one thread
and no array package so that its memory footprint stays small.
"""

from collections import defaultdict
from fractions import Fraction as Q
import math
import time
import tracemalloc

import flint
from flint import arb, ctx


START = time.time()
tracemalloc.start()
ctx.prec = 220
ctx.threads = 1


def B(value):
    """Embed an integer, decimal string, or Fraction in an Arb ball."""
    if isinstance(value, Q):
        return arb(value.numerator) / value.denominator
    if isinstance(value, str):
        return arb(value)
    return arb(value)


# =====================================================================
# Part I. Exact finite verification, 8 <= n <= 10000
#
# E(q) = P(q) - 4 U_1(q), and
#
# (q;q)_infinity E(q) = K(q)
#   = 1 + 4 sum_{r>=2} (-1)^(r+1)
#              sum_{j=0}^{r-2} q^(r(r+1)/2 + jr).
#
# Euler's pentagonal theorem gives an O(N sqrt(N)) exact recurrence.
# =====================================================================

NMAX = 10_000

Kq = [0] * (NMAX + 1)
Kq[0] = 1

r = 2
while r * (r + 1) // 2 <= NMAX:
    triangular = r * (r + 1) // 2
    coefficient = -4 if r % 2 == 0 else 4
    for j in range(r - 1):
        exponent = triangular + j * r
        if exponent > NMAX:
            break
        Kq[exponent] += coefficient
    r += 1

# If
# (q;q)_infinity = 1 + sum_{k>=1} (-1)^k
#   (q^(k(3k-1)/2) + q^(k(3k+1)/2)),
# then coefficient comparison determines E_n from earlier values.
Eq = [0] * (NMAX + 1)

for n in range(NMAX + 1):
    value = Kq[n]
    k = 1
    while True:
        gminus = k * (3 * k - 1) // 2
        if gminus > n:
            break
        pentagonal_sign = -1 if k % 2 else 1
        value -= pentagonal_sign * Eq[n - gminus]
        gplus = k * (3 * k + 1) // 2
        if gplus <= n:
            value -= pentagonal_sign * Eq[n - gplus]
        k += 1
    Eq[n] = value

assert Eq[:15] == [
    1, 1, 2, -1, 1, -1, 3, -1,
    2, 2, 2, 0, 5, 1, 3,
]
assert all(Eq[n] >= 0 for n in range(8, NMAX + 1))
assert [n for n in range(8, NMAX + 1) if Eq[n] == 0] == [11]

print(
    "finite: PASS; min E[8..10000] =",
    min(Eq[8:]),
    "; only zero = 11",
)


# =====================================================================
# Part II. Order-16 two-variable Euler--Boole certificate
#
# H(e^-z) = 1 - 4 Theta(z), where
#
# Theta(z) = sum_{a,b>=0} (-1)^(a+b) exp(-z Q(a,b)),
# Q(a,b) = 3a^2/2 + 2ab + b^2/2 + (a+b)/2.
#
# On |arg z| <= pi/4, put h=|z|^(1/2), omega=z/|z| and
#
# f(X,Y)=exp[-omega(3X^2/2+2XY+Y^2/2+h(X+Y)/2)].
#
# Every polynomial coefficient below is an exact Fraction.  Arb is used
# only for the transcendental Gaussian moments and final inequalities.
# =====================================================================

# A monomial tuple denotes X^i Y^j h^k omega^ell.
PCACHE = {(0, 0): {(0, 0, 0, 0): Q(1)}}


def poly_step(poly, variable):
    """Differentiate P*f in one variable and divide the result by f."""
    result = defaultdict(Q)
    derivative_index = 0 if variable == "x" else 1

    if variable == "x":
        logarithmic_derivative = (
            ((1, 0, 0, 1), Q(-3)),
            ((0, 1, 0, 1), Q(-2)),
            ((0, 0, 1, 1), Q(-1, 2)),
        )
    else:
        logarithmic_derivative = (
            ((1, 0, 0, 1), Q(-2)),
            ((0, 1, 0, 1), Q(-1)),
            ((0, 0, 1, 1), Q(-1, 2)),
        )

    for monomial, coefficient in poly.items():
        if monomial[derivative_index]:
            lowered = list(monomial)
            lowered[derivative_index] -= 1
            result[tuple(lowered)] += (
                coefficient * monomial[derivative_index]
            )

        for shift, factor in logarithmic_derivative:
            new_monomial = tuple(
                monomial[i] + shift[i] for i in range(4)
            )
            result[new_monomial] += coefficient * factor

    return {
        monomial: coefficient
        for monomial, coefficient in result.items()
        if coefficient
    }


def Pab(a, b):
    """Return (partial_X^a partial_Y^b f)/f exactly."""
    key = (a, b)
    if key not in PCACHE:
        if a:
            PCACHE[key] = poly_step(Pab(a - 1, b), "x")
        else:
            PCACHE[key] = poly_step(Pab(a, b - 1), "y")
    return PCACHE[key]


sqrt2 = B(2).sqrt()
pi = arb.pi()

# At n=10000,
# x0 = sqrt((pi^2/6)/(10000-1/24)) = 2*pi/sqrt(239999).
x0 = 2 * pi / B(239999).sqrt()
rho = sqrt2 * x0
h0 = rho.sqrt()

# |f(X,Y)| <= exp(-alpha X^2-beta Y^2).
alpha = B(3) / (2 * sqrt2)
beta = B(1) / (2 * sqrt2)


def moment(power, gaussian_coefficient):
    """Integral_0^infinity t^power exp(-c t^2) dt, as an Arb ball."""
    exponent = B(power + 1) / 2
    return exponent.gamma() / (2 * gaussian_coefficient**exponent)


def integral_bound(poly, kind):
    """Coefficientwise absolute bound for a derivative integral."""
    total = B(0)
    for (i, j, k, _ell), coefficient in poly.items():
        if kind == "y0" and j:
            continue
        if kind == "x0" and i:
            continue

        term = B(abs(coefficient)) * h0**k
        if kind == "y0":
            term *= moment(i, alpha)
        elif kind == "x0":
            term *= moment(j, beta)
        elif kind == "2d":
            term *= moment(i, alpha) * moment(j, beta)
        else:
            raise ValueError(kind)
        total += term
    return total


BERNOULLI = {
    2: Q(1, 6),
    4: Q(-1, 30),
    6: Q(1, 42),
    8: Q(-1, 30),
    10: Q(5, 66),
    12: Q(-691, 2730),
    14: Q(7, 6),
    16: Q(-3617, 510),
}

DERIVATIVE_ORDERS = [0] + list(range(1, 16, 2))

# Euler--Boole coefficients:
# c_0=1/2, c_(2k-1)=-(4^k-1) B_(2k)/(2k)!.
boole = {0: Q(1, 2)}
for derivative_order in DERIVATIVE_ORDERS[1:]:
    k = (derivative_order + 1) // 2
    boole[derivative_order] = (
        -Q(4**k - 1)
        * BERNOULLI[2 * k]
        / math.factorial(2 * k)
    )

# From the periodic-Euler Fourier bound:
# |R_16| <= (4/pi^16) h^15 integral |f^(16)|.
remainder_constant = B(4) / pi**16

remainder_x = (
    remainder_constant
    * h0**15
    * sum(
        (
            B(abs(boole[d]))
            * h0**d
            * integral_bound(Pab(16, d), "y0")
            for d in DERIVATIVE_ORDERS
        ),
        B(0),
    )
)

remainder_y = (
    remainder_constant
    * h0**15
    * sum(
        (
            B(abs(boole[d]))
            * h0**d
            * integral_bound(Pab(d, 16), "x0")
            for d in DERIVATIVE_ORDERS
        ),
        B(0),
    )
)

remainder_xy = (
    remainder_constant**2
    * h0**30
    * integral_bound(Pab(16, 16), "2d")
)

# Construct the finite L_x L_y polynomial exactly.
theta_polynomial = defaultdict(Q)
for a in DERIVATIVE_ORDERS:
    for b in DERIVATIVE_ORDERS:
        for (i, j, k, ell), coefficient in Pab(a, b).items():
            if i == 0 and j == 0:
                # h^(a+b+k) omega^ell = z^ell.
                assert a + b + k == 2 * ell
                theta_polynomial[ell] += (
                    boole[a] * boole[b] * coefficient
                )

H_polynomial = defaultdict(Q, {0: Q(1)})
for degree, coefficient in theta_polynomial.items():
    H_polynomial[degree] -= 4 * coefficient

assert H_polynomial[0] == 0
assert H_polynomial[1] == 0

expected_coefficients = {
    2: Q(3, 16),
    3: Q(3, 8),
    4: Q(227, 256),
    5: Q(41, 16),
    6: Q(181499, 20480),
    7: Q(1101083, 30720),
    8: Q(1144044847, 6881280),
}
assert all(
    H_polynomial[k] == value
    for k, value in expected_coefficients.items()
)

polynomial_tail = sum(
    (
        B(abs(coefficient)) * rho**degree
        for degree, coefficient in H_polynomial.items()
        if degree >= 3
    ),
    B(0),
)

H_remainder = 4 * (remainder_x + remainder_y + remainder_xy)
H_lead = B(3) / 16 * rho**2
H_epsilon = (polynomial_tail + H_remainder) / H_lead

# Conservative outward rational thresholds.
assert remainder_x < B("4.357e-8")
assert remainder_y < B("1.760e-11")
assert remainder_xy < B("9.583e-10")
assert H_remainder < B("1.79e-7")
assert polynomial_tail < B("2.34e-6")
assert H_lead > B("6.168e-5")
assert H_epsilon < B("0.041")

print("Euler-Boole: PASS")
print(" remainder_x =", remainder_x)
print(" remainder_y =", remainder_y)
print(" remainder_xy =", remainder_xy)
print(" H remainder =", H_remainder)
print(" polynomial tail =", polynomial_tail)
print(" lead =", H_lead)
print(" epsilon =", H_epsilon)


# =====================================================================
# Part III. Major/minor arc inequalities
# =====================================================================

A = pi**2 / 6
sqrt_x0 = x0.sqrt()
S = B(3) / 2
gaussian_c = 4 * A / 5

# Main E-series.
core_phase_E = (A + B(5) / 2) * sqrt_x0
phase_15_E = ((B(27) / 8) * A + B(15) / 4) * sqrt_x0
core_E = (-(A)).exp() * (-(B(47) / 100)).cos()

far_E = (
    B(2) ** (B(5) / 4)
    / (2 * sqrt_x0)
    * (-(A / (5 * x0))).exp()
)

tail_E = (
    (B(5) / 4) ** (B(5) / 4)
    * (-(gaussian_c * S**2)).exp()
    / (2 * gaussian_c * S)
    + far_E
)

absolute_E = (
    (B(5) / 4) ** (B(5) / 4)
    * pi.sqrt()
    / (2 * gaussian_c.sqrt())
    + far_E
)

half_integral_E = core_E - tail_E - B("0.041") * absolute_E
full_integral_E = 2 * half_integral_E

assert core_phase_E < B("0.47")
assert phase_15_E < pi / 2
assert core_E > B("0.172")
assert tail_E < B("0.0175")
assert absolute_E < B("1.022")
assert half_integral_E > B("0.1125")
assert full_integral_E > B("0.22")

# On |y|<=x, Re(4*pi^2/z)>=2*pi^2/x.
eta_residual_exponent = 2 * pi**2 / x0
assert eta_residual_exponent > B(1539)

# The transformed product P(exp(-4*pi^2/z)) differs from one by less
# than 3r when |r| <= exp(-2*pi^2/x).  Fold this into the major-arc
# relative error instead of merely noting that it is negligible.
eta_major_error = 3 * (-eta_residual_exponent).exp()
combined_major_error = (
    (1 + H_epsilon) * (1 + eta_major_error) - 1
)
assert combined_major_error < B("0.041")

# Minor-arc product loss D(x,y) > 0.49/x.
minor_loss_constant = (
    (1 - x0)
    * (2 - x0)
    * (B(1) / 2 - x0**2 / 24)
    / 2
)

# x times the global H bound is at most this quantity.
H_global_coefficient = 3 * x0 + 4 + 8 * (pi * x0 / 2).sqrt()

minor_major_ratio_E = (
    2
    * pi
    * B("5.174")
    / ((B(3) / 16) * B("0.22"))
    * x0 ** (-B(9) / 2)
    * (-(B("0.49") / x0)).exp()
)

# On the real modular transform the residual exponent is 4*pi^2/x.
eta_minor_error = 3 * (-(4 * pi**2 / x0)).exp()
minor_major_ratio_E *= 1 + eta_minor_error

assert minor_loss_constant > B("0.49")
assert H_global_coefficient < B("5.174")
assert x0 < B("0.49") / (B(9) / 2)
assert minor_major_ratio_E < B("0.000007")

# Optional certification of the observed six-step strengthening.
six_factor_error = ((6 * rho).exp() - 1 - 6 * rho) / (6 * rho)
six_relative_error = (1 + B("0.041")) * (1 + six_factor_error) - 1

core_phase_six = (A + B(7) / 2) * sqrt_x0
phase_15_six = ((B(27) / 8) * A + B(21) / 4) * sqrt_x0
core_six = (-(A)).exp() * (-(B(583) / 1000)).cos()

far_six = (
    B(2) ** (B(7) / 4)
    / (2 * sqrt_x0)
    * (-(A / (5 * x0))).exp()
)

tail_six = (
    (B(5) / 4) ** (B(7) / 4)
    * (-(gaussian_c * S**2)).exp()
    / (2 * gaussian_c * S)
    + far_six
)

absolute_six = (
    (B(5) / 4) ** (B(7) / 4)
    * pi.sqrt()
    / (2 * gaussian_c.sqrt())
    + far_six
)

half_integral_six = (
    core_six - tail_six - B("0.101") * absolute_six
)
full_integral_six = 2 * half_integral_six

minor_major_ratio_six = (
    4
    * pi
    * B("5.174")
    / (6 * (B(3) / 16) * B("0.05"))
    * x0 ** (-B(11) / 2)
    * (-(B("0.49") / x0)).exp()
)

assert six_factor_error < B("0.057")
assert six_relative_error < B("0.101")
assert core_phase_six < B("0.583")
assert phase_15_six < pi / 2
assert core_six > B("0.161")
assert tail_six < B("0.0194")
assert absolute_six < B("1.142")
assert full_integral_six > B("0.05")
assert x0 < B("0.49") / (B(11) / 2)
assert minor_major_ratio_six < B("0.0008")

print("major/minor: PASS")
print(" python-flint =", flint.__version__, "; Arb precision =", ctx.prec)
print(" x0 =", x0)
print(" core E =", core_E)
print(" tail E =", tail_E)
print(" absolute E =", absolute_E)
print(" full normalized E integral =", full_integral_E)
print(" minor loss c0 =", minor_loss_constant)
print(" H coefficient =", H_global_coefficient)
print(" minor/major E =", minor_major_ratio_E)
print(" eta exponent =", eta_residual_exponent)
print(" combined major error =", combined_major_error)
print(" eta minor factor - 1 =", eta_minor_error)
print(" six-step relative error =", six_relative_error)
print(" six-step minor/major =", minor_major_ratio_six)

_current, peak = tracemalloc.get_traced_memory()
tracemalloc.stop()
print(
    "elapsed %.2fs; traced Python peak %.1f MiB"
    % (time.time() - START, peak / 2**20)
)
