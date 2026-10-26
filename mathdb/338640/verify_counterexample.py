"""Exact verifier for the counterexample to MathDB #338640."""

from __future__ import annotations

import hashlib
import itertools
import json
from math import comb
from pathlib import Path


CERTIFICATE_SHA256 = (
    "a66d12048d963de70180540eff002c7f3a97d6dce080c7fcd4ee78b7ecd523b7"
)


def require(condition: bool, message: str) -> None:
    """Raise an optimization-stable error when a check fails."""
    if not condition:
        raise RuntimeError(message)


def subset_mask(elements: tuple[int, ...]) -> int:
    """Encode a subset of [15] using bit i-1 for element i."""
    return sum(1 << (element - 1) for element in elements)


def all_uniform_masks(n: int, size: int) -> list[int]:
    return [subset_mask(elements) for elements in itertools.combinations(range(1, n + 1), size)]


def disjoint_uniform_masks(mask: int, full_mask: int) -> list[int]:
    """Return all seven-subsets disjoint from a seven-subset of [15]."""
    complement = full_mask ^ mask
    bits = [1 << bit for bit in range(15) if complement & (1 << bit)]
    require(len(bits) == 8, "a seven-set does not have an eight-element complement")
    return [complement ^ bit for bit in bits]


def reconstruct_source_family() -> tuple[set[int], tuple[int, int, int, int]]:
    """Reconstruct Bovdi--Leung's A_m at k=2 from its four classes."""
    core = tuple(range(1, 9))
    tail = tuple(range(9, 16))
    fano_lines = (
        (9, 10, 13),
        (9, 11, 14),
        (9, 12, 15),
        (10, 11, 15),
        (11, 12, 13),
        (13, 14, 15),
        (10, 12, 14),
    )

    fano_class = {
        subset_mask(line + core_part)
        for line in fano_lines
        for core_part in itertools.combinations(core, 4)
    }
    two_tail_class = {
        subset_mask(tail_part + core_part)
        for tail_part in itertools.combinations(tail, 2)
        for core_part in itertools.combinations(core, 5)
    }
    one_tail_class = {
        subset_mask(tail_part + core_part)
        for tail_part in itertools.combinations(tail, 1)
        for core_part in itertools.combinations(core, 6)
    }
    core_only_class = {
        subset_mask(core_part) for core_part in itertools.combinations(core, 7)
    }

    terms = (
        len(fano_class),
        len(two_tail_class),
        len(one_tail_class),
        len(core_only_class),
    )
    family = fano_class | two_tail_class | one_tail_class | core_only_class
    return family, terms


def verify_bicommutative(
    family: set[int], universe: list[int], full_mask: int, label: str
) -> tuple[int, int, int, int]:
    """Check pairwise intersection and inclusion-maximality exactly."""
    pairwise_checks = 0
    for first, second in itertools.combinations(sorted(family), 2):
        require(first & second != 0, f"{label} contains a disjoint pair")
        pairwise_checks += 1

    outside_checks = 0
    disjoint_incidences = 0
    minimum_witnesses: int | None = None
    maximum_witnesses: int | None = None
    for mask in universe:
        if mask in family:
            continue
        witnesses = sum(
            candidate in family
            for candidate in disjoint_uniform_masks(mask, full_mask)
        )
        require(witnesses > 0, f"{label} is not maximal")
        outside_checks += 1
        disjoint_incidences += witnesses
        minimum_witnesses = witnesses if minimum_witnesses is None else min(minimum_witnesses, witnesses)
        maximum_witnesses = witnesses if maximum_witnesses is None else max(maximum_witnesses, witnesses)

    require(minimum_witnesses is not None, f"{label} unexpectedly equals the universe")
    require(maximum_witnesses is not None, f"{label} unexpectedly equals the universe")
    return pairwise_checks, outside_checks, disjoint_incidences, maximum_witnesses


def main() -> None:
    certificate_path = Path(__file__).with_name("certificate.json")
    raw = certificate_path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    require(digest == CERTIFICATE_SHA256, "certificate hash mismatch")
    data = json.loads(raw)

    require(
        set(data)
        == {
            "format",
            "problem",
            "universe_size",
            "subset_size",
            "source_parameters",
            "source_family_size",
            "certificate_size",
            "encoding",
            "discovery",
            "masks",
        },
        "unexpected certificate schema",
    )
    require(data["format"] == "mathdb-338640-bicommutative-v1", "wrong format")
    require(data["problem"] == 338640, "wrong problem number")
    require(data["universe_size"] == 15, "wrong universe size")
    require(data["subset_size"] == 7, "wrong uniform-set size")
    require(data["source_parameters"] == {"k": 2, "n": 15, "m": 7}, "wrong parameters")
    require(data["source_family_size"] == 1870, "wrong claimed source size")
    require(data["certificate_size"] == 1173, "wrong claimed certificate size")
    require(
        set(data["discovery"])
        == {"algorithm", "seed", "trials", "best_trial_zero_based", "sample_size"},
        "unexpected discovery metadata",
    )
    require(data["discovery"]["seed"] == 338640, "wrong discovery seed")
    require(data["discovery"]["trials"] == 42, "wrong discovery trial count")
    require(data["discovery"]["best_trial_zero_based"] == 41, "wrong best trial")
    require(data["discovery"]["sample_size"] == 192, "wrong discovery sample size")

    masks = data["masks"]
    require(all(type(mask) is int for mask in masks), "a mask is not an integer")
    require(masks == sorted(masks), "certificate masks are not sorted")
    require(len(masks) == len(set(masks)) == 1173, "duplicate or missing masks")

    n = data["universe_size"]
    size = data["subset_size"]
    full_mask = (1 << n) - 1
    require(
        all(0 < mask <= full_mask and mask.bit_count() == size for mask in masks),
        "a mask does not encode a seven-subset of [15]",
    )

    universe = all_uniform_masks(n, size)
    require(len(universe) == comb(15, 7) == 6435, "wrong uniform universe")
    require(set(masks) <= set(universe), "certificate mask outside the universe")

    source, source_terms = reconstruct_source_family()
    expected_terms = (
        7 * comb(8, 4),
        comb(7, 2) * comb(8, 5),
        7 * comb(8, 6),
        comb(8, 7),
    )
    require(source_terms == expected_terms == (490, 1176, 196, 8), "wrong source terms")
    require(len(source) == sum(source_terms) == 1870, "wrong reconstructed source size")
    require(all(mask.bit_count() == 7 for mask in source), "source family is not 7-uniform")

    certificate_stats = verify_bicommutative(set(masks), universe, full_mask, "certificate")
    source_stats = verify_bicommutative(source, universe, full_mask, "source family")

    require(certificate_stats[0] == comb(1173, 2), "wrong certificate pair count")
    require(certificate_stats[1] == 6435 - 1173, "wrong certificate outside count")
    require(source_stats[0] == comb(1870, 2), "wrong source pair count")
    require(source_stats[1] == 6435 - 1870, "wrong source outside count")
    require(1173 < 1870 and 1870 - 1173 == 697, "counterexample is not smaller")

    print("PASS: exact bicommutative-system counterexample for MathDB #338640")
    print(f"certificate_sha256={digest}")
    print(f"uniform_universe={len(universe)}")
    print("source_terms=490+1176+196+8=1870")
    print("certificate_size=1173; source_size=1870; improvement=697")
    print(
        "certificate_pairwise_checks="
        f"{certificate_stats[0]}; outside_maximality_checks={certificate_stats[1]}; "
        f"disjoint_witness_incidences={certificate_stats[2]}; "
        f"maximum_witnesses_for_one_outside_set={certificate_stats[3]}"
    )
    print(
        "source_pairwise_checks="
        f"{source_stats[0]}; outside_maximality_checks={source_stats[1]}; "
        f"disjoint_witness_incidences={source_stats[2]}; "
        f"maximum_witnesses_for_one_outside_set={source_stats[3]}"
    )
    print("all checks use exact integer arithmetic and remain active under -OO")


if __name__ == "__main__":
    main()
