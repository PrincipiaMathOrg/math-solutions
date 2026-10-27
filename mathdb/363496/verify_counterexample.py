"""Exact finite-monoid verifier for the counterexample to MathDB #363496."""

from __future__ import annotations

from itertools import combinations


ELEMENTS = ("e", "u", "v", "z")
A = frozenset(("e", "u", "v"))

# Rows are left factors and columns are right factors: left o right.
TABLE = {
    "e": {"e": "e", "u": "u", "v": "v", "z": "z"},
    "u": {"e": "u", "u": "z", "v": "z", "z": "z"},
    "v": {"e": "v", "u": "u", "v": "v", "z": "z"},
    "z": {"e": "z", "u": "z", "v": "z", "z": "z"},
}


def compose(left: str, right: str) -> str:
    return TABLE[left][right]


def generated_semigroup(generators: frozenset[str]) -> frozenset[str]:
    closure = set(generators)
    while True:
        enlarged = closure | {
            compose(left, right) for left in closure for right in closure
        }
        if enlarged == closure:
            return frozenset(closure)
        closure = enlarged


def nonempty_subsets(items: tuple[str, ...]):
    for size in range(1, len(items) + 1):
        for subset in combinations(items, size):
            yield frozenset(subset)


def is_right_ideal(candidate: frozenset[str], semigroup: frozenset[str]) -> bool:
    return all(
        compose(left, right) in candidate
        for left in candidate
        for right in semigroup
    )


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> None:
    # Verify associativity and the identity/zero rows directly.
    for left in ELEMENTS:
        require(
            compose("e", left) == left == compose(left, "e"),
            f"identity rule failed at {left}",
        )
        require(
            compose("z", left) == "z" == compose(left, "z"),
            f"zero rule failed at {left}",
        )
        for middle in ELEMENTS:
            for right in ELEMENTS:
                require(
                    compose(compose(left, middle), right)
                    == compose(left, compose(middle, right)),
                    f"associativity failed at {(left, middle, right)}",
                )

    semigroup = generated_semigroup(A)
    require(semigroup == frozenset(ELEMENTS), "generated semigroup mismatch")

    # On X, a table element f preserves all three listed spaces exactly
    # when f o A is contained in A.
    preservers_in_semigroup = frozenset(
        left
        for left in semigroup
        if all(compose(left, right) in A for right in A)
    )
    require(
        preservers_in_semigroup == frozenset(("e", "v")),
        "preserver set mismatch",
    )

    # Intended convention: right ideals of [A] that are contained in A.
    contained_right_ideals = tuple(
        candidate
        for candidate in nonempty_subsets(tuple(sorted(A)))
        if is_right_ideal(candidate, semigroup)
    )
    require(contained_right_ideals == (), "unexpected contained right ideal")
    intended_lhs = frozenset(("e",))
    require(
        "v" in preservers_in_semigroup - intended_lhs,
        "intended-reading witness missing",
    )

    # Literal convention: the union of all right ideals is the entire
    # semigroup because the semigroup itself is a right ideal.
    all_right_ideals = tuple(
        candidate
        for candidate in nonempty_subsets(ELEMENTS)
        if is_right_ideal(candidate, semigroup)
    )
    literal_union = frozenset().union(*all_right_ideals)
    require(literal_union == semigroup, "literal right-ideal union mismatch")
    require(
        "z" in literal_union - preservers_in_semigroup,
        "literal-reading witness missing",
    )

    print("PASS")
    print("generated semigroup:", " ".join(ELEMENTS))
    print("preservers inside [A]:", " ".join(sorted(preservers_in_semigroup)))
    print("right ideals contained in A:", len(contained_right_ideals))
    print("all nonempty right ideals:", len(all_right_ideals))


if __name__ == "__main__":
    main()
