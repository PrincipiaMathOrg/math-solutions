"""Exact low-memory checks for the normalization counterexample.

Only Python's standard library is used.  The script verifies the finite
identities underlying the counterexample for n = 1,...,20.  The proof
that eta_n(A) <= lambda_n(A) for every A is pointwise and therefore does
not require enumerating subsets.
"""

from fractions import Fraction


def lambda_measure(n: int) -> dict[int, Fraction]:
    weight = Fraction(1, 2 * n)
    return {x: weight for x in range(1, 2 * n + 1)}


def eta_measure(n: int) -> dict[int, Fraction]:
    return {x: w for x, w in lambda_measure(n).items() if x % 2 == 0}


def shifted_value(mu: dict[int, Fraction], x: int) -> Fraction:
    """Value of the source's shift x |-> mu(x+1)."""

    return mu.get(x + 1, Fraction(0))


def l1_shift_defect(mu: dict[int, Fraction]) -> Fraction:
    support = set(mu)
    support.update(x - 1 for x in mu)
    return sum(
        (abs(mu.get(x, Fraction(0)) - shifted_value(mu, x)) for x in support),
        Fraction(0),
    )


def check(n: int) -> tuple[Fraction, Fraction]:
    lam = lambda_measure(n)
    eta = eta_measure(n)

    assert sum(lam.values(), Fraction(0)) == 1
    assert sum(eta.values(), Fraction(0)) == Fraction(1, 2)
    assert all(eta.get(x, Fraction(0)) <= w for x, w in lam.items())
    assert l1_shift_defect(eta) == 1
    assert l1_shift_defect(lam) == Fraction(1, n)

    return l1_shift_defect(lam), l1_shift_defect(eta)


def main() -> None:
    for n in range(1, 21):
        lambda_defect, eta_defect = check(n)
        print(
            f"n={n:2d}  "
            f"lambda mass=1 defect={lambda_defect}  "
            f"eta mass=1/2 defect={eta_defect}"
        )
    print("All exact checks passed.")


if __name__ == "__main__":
    main()
