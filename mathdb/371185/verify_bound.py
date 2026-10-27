#!/usr/bin/env python3
"""Exact recurrence checks for the bound proved for MathDB #371185."""

from __future__ import annotations

import itertools


PROFILES = ("FF", "AF", "FA", "AA")
DUAL = {"FF": "FF", "AF": "FA", "FA": "AF", "AA": "AA"}


def require(condition: bool, message: object) -> None:
    if not condition:
        raise AssertionError(message)


def check_rules(
    rules: tuple[int, ...], limit: int, wanted: set[int] | None = None
) -> tuple[int, dict[int, dict[str, tuple[int, int]]]]:
    """Stream the source recurrence and check every pair of profiles."""

    require(
        bool(rules) and tuple(sorted(set(rules))) == rules and rules[0] > 0,
        ("invalid rules", rules),
    )
    width = rules[-1] + 1
    history = {profile: [(0, 0)] * width for profile in PROFILES}
    snapshots: dict[int, dict[str, tuple[int, int]]] = {}
    largest = 0

    for heap in range(1, limit + 1):
        for profile in PROFILES:
            candidates: list[tuple[int, int]] = []
            other_profile = DUAL[profile]
            for move in rules:
                if move > heap:
                    break
                prior = history[other_profile][(heap - move) % width]
                candidates.append((move + prior[1], prior[0]))

            if not candidates:
                outcome = (0, 0)
            else:
                best_self = max(candidate[0] for candidate in candidates)
                indifferent = [c for c in candidates if c[0] == best_self]
                outcome = (
                    max(indifferent, key=lambda c: c[1])
                    if profile[0] == "F"
                    else min(indifferent, key=lambda c: c[1])
                )
            history[profile][heap % width] = outcome

        current = {
            profile: history[profile][heap % width] for profile in PROFILES
        }
        if wanted is not None and heap in wanted:
            snapshots[heap] = current.copy()

        for left, right in itertools.combinations(PROFILES, 2):
            for player in (0, 1):
                gap = abs(current[left][player] - current[right][player])
                largest = max(largest, gap)
                require(
                    gap <= rules[0] - 1,
                    (rules, heap, left, right, player, gap),
                )

    return largest, snapshots


def main() -> None:
    _, source = check_rules((3, 5), 15, {14})
    require(source[14]["FF"] == (8, 6), source[14])
    require(source[14]["AA"] == (8, 5), source[14])

    sharp_max, sharp = check_rules((3, 5, 8), 23, {23})
    require(sharp[23]["FF"] == (13, 10), sharp[23])
    require(sharp[23]["AF"] == (13, 8), sharp[23])
    require(sharp_max == 2, sharp_max)

    ruleset_count = 0
    max_observed = 0
    universe = range(1, 10)
    for size in range(1, 10):
        for rules in itertools.combinations(universe, size):
            observed, _ = check_rules(rules, 2_000)
            max_observed = max(max_observed, observed)
            ruleset_count += 1

    long_rules = (
        (3, 5),
        (3, 5, 8),
        (4, 5, 9),
        (3, 8, 11, 13),
        (13, 17, 18, 25, 26),
    )
    for rules in long_rules:
        observed, _ = check_rules(rules, 100_000)
        max_observed = max(max_observed, observed)

    print("source table: S=(3,5), h=14, FF=(8,6), AA=(8,5)")
    print("sharpness: S=(3,5,8), h=23, FF=(13,10), AF=(13,8)")
    print(f"exhaustive rulesets on moves 1..9: {ruleset_count}")
    print(f"exhaustive heaps per ruleset: 2000")
    print(f"profile/player comparisons: {ruleset_count * 2000 * 12}")
    print(f"long-horizon rulesets through heap 100000: {len(long_rules)}")
    print(f"largest discrepancy observed: {max_observed}")
    print("all exact recurrence checks passed")


if __name__ == "__main__":
    main()
