"""Exact structural checks for the counterexample to MathDB #365102."""

from __future__ import annotations

from fractions import Fraction


def require(condition: bool, message: str) -> None:
    """Raise an optimization-stable error when a check fails."""
    if not condition:
        raise RuntimeError(message)


def main() -> None:
    center = Fraction(1)

    # Reflection about 1 preserves (x-1)^2.  Use a broad exact rational grid
    # as a regression check on the displayed counterexample.
    reflection_checks = 0
    for numerator in range(-2000, 2001):
        x = Fraction(numerator, 37)
        reflected = 2 * center - x
        require(
            (reflected - center) ** 2 == (x - center) ** 2,
            "reflection identity failed",
        )
        reflection_checks += 1

    # The proof uses 1+(x-1)^2 >= |x|^2/4 for |x| >= 4.
    growth_checks = 0
    for denominator in (1, 7, 31):
        for numerator in range(4 * denominator, 400 * denominator + 1):
            for sign in (-1, 1):
                x = sign * Fraction(numerator, denominator)
                require(abs(x) >= 4, "growth grid escaped its domain")
                require(
                    1 + (x - center) ** 2 >= abs(x) ** 2 / 4,
                    "logarithmic-confinement bound failed",
                )
                growth_checks += 1

    # For each escape direction and every y in [-1,1], the proof bounds
    # |y-sign*t-1| by t+2 and then 1+(t+2)^2 by (t+3)^2.
    escape_checks = 0
    for t_integer in range(0, 251):
        t = Fraction(t_integer)
        for sign in (-1, 1):
            for y_numerator in range(-40, 41):
                y = Fraction(y_numerator, 40)
                displacement = y - sign * t - center
                require(
                    abs(displacement) <= t + 2,
                    "escape displacement bound failed",
                )
                require(
                    1 + displacement**2 <= (t + 3) ** 2,
                    "escape potential bound failed",
                )
                escape_checks += 1

    # Certify the elementary logarithm comparison used to make divergence
    # quantitative.  e^4 exceeds its degree-4 Taylor partial sum, which is
    # already greater than 19, so log(19)<4.  Also
    # (t+3)^2-4t=(t+1)^2+8>0, hence sqrt(t)-log(t+3) is increasing for t>=16.
    exp4_partial = sum(Fraction(4**k, 1) / factorial for k, factorial in (
        (0, 1),
        (1, 1),
        (2, 2),
        (3, 6),
        (4, 24),
    ))
    require(exp4_partial > 19, "Taylor certificate for log(19)<4 failed")

    derivative_checks = 0
    for t_integer in range(16, 10001):
        t = Fraction(t_integer)
        require(
            (t + 3) ** 2 - 4 * t == (t + 1) ** 2 + 8,
            "derivative comparison identity failed",
        )
        require((t + 1) ** 2 + 8 > 0, "derivative comparison lost positivity")
        derivative_checks += 1

    # For q=|lambda|, 4 log(t+3) <= 4 sqrt(t) once t>=16.  The exact square
    # t_n=(8n/q+4)^2 makes q*t_n-4*sqrt(t_n) an explicitly diverging lower
    # bound.  Check several rational scales without floating-point arithmetic.
    divergence_checks = 0
    for q in (Fraction(1, 100), Fraction(1, 3), Fraction(1), Fraction(17, 5)):
        previous: Fraction | None = None
        for n in range(1, 251):
            root = Fraction(8 * n, 1) / q + 4
            t = root**2
            require(t >= 16, "divergence sequence fell below logarithm threshold")
            lower_bound = q * t - 4 * root
            if previous is not None:
                require(lower_bound > previous, "escape lower bound is not increasing")
            previous = lower_bound
            divergence_checks += 1
        require(previous is not None and previous > 1_000_000,
                "escape lower bound did not become arbitrarily large on the test range")

    print("PASS: structural counterexample checks for MathDB #365102")
    print(f"reflection_rational_checks={reflection_checks}")
    print(f"growth_rational_checks={growth_checks}")
    print(f"escape_rectangle_checks={escape_checks}")
    print(f"derivative_identity_checks={derivative_checks}")
    print(f"divergence_sequence_checks={divergence_checks}")
    print(f"exp4_degree4_partial={exp4_partial}")
    print("all checks are exact and remain active under -OO")


if __name__ == "__main__":
    main()
