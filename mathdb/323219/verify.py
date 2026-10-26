"""Exact finite checks for MathDB 323219; the all-m proof is in solution.tex."""
from collections import defaultdict
from datetime import datetime, timezone
from itertools import permutations
from math import comb, factorial
from pathlib import Path
import json


SOURCE_C = [
    [1],
    [0, 1, 1],
    [0, 1, 3, 6, 3],
    [0, 1, 7, 20, 46, 45, 15],
    [0, 1, 11, 61, 198, 480, 645, 420, 105],
    [0, 1, 18, 138, 706, 2508, 6441, 10395, 9660, 4725, 945],
    [0, 1, 26, 296, 2052, 10375, 38809, 105392, 192668, 224595,
     159075, 62370, 10395],
    [0, 1, 38, 577, 5428, 36285, 184624, 713402, 2032500, 4080195,
     5580855, 5051970, 2889810, 945945, 135135],
    [0, 1, 52, 1092, 13226, 114220, 751639, 3854487, 15231326,
     45159822, 97613505, 150613155, 162889650, 120270150, 57702645,
     16216200, 2027025],
    [0, 1, 73, 1963, 30648, 332035, 2747799, 17918432, 92357844,
     370929320, 1136808010, 2609559315, 4427605050, 5488733250,
     4892112225, 3047969925, 1259458200, 310134825, 34459425],
]


def falling(k):
    a = [1]
    for j in range(k):
        b = [0] * (len(a) + 1)
        for i, v in enumerate(a):
            b[i] -= j * v
            b[i + 1] += v
        a = b
    return a


def add_scaled(out, a, scale):
    for i, v in enumerate(a):
        out[i] += scale * v


def evaluate(a, r):
    out = 0
    for v in reversed(a):
        out = out * r + v
    return out


def layers(r, maximum):
    zero = (0,) * r
    units = [tuple(int(i == j) for i in range(r)) for j in range(r)]
    base = frozenset([zero] + units)
    current = {frozenset()}
    yield current
    for _ in range(maximum):
        nxt = set()
        for extra in current:
            diagram = extra | base
            candidates = set()
            for v in diagram:
                for j in range(r):
                    w = v[:j] + (v[j] + 1,) + v[j + 1:]
                    if w not in diagram:
                        candidates.add(w)
            for w in candidates:
                if all(w[:j] + (w[j] - 1,) + w[j + 1:] in diagram
                       for j in range(r) if w[j]):
                    nxt.add(extra | {w})
        current = nxt
        yield current


def full_support(extra, r):
    return all(any(v[j] for v in extra) for j in range(r))


def graph_pairs(extra, k):
    neighbors = [set() for _ in range(k)]
    loops = set()
    for v in extra:
        if sum(v) != 2:
            continue
        support = [j for j in range(k) if v[j]]
        if len(support) == 1:
            loops.add(support[0])
        else:
            a, b = support
            neighbors[a].add(b)
            neighbors[b].add(a)
    assert all(neighbors[j] or j in loops for j in range(k))
    return [(a, b) for a in range(k) for b in neighbors[a]
            if a < b and neighbors[a] == {b} and neighbors[b] == {a}
            and a not in loops and b not in loops]


def main():
    strict = {}
    totals = {}
    for r in range(1, 9):
        for m, layer in enumerate(layers(r, 4)):
            totals[m, r] = len(layer)
            reduced = {s for s in layer if full_support(s, r)}
            strict[m, r] = reduced
            expected = SOURCE_C[m][r] if r < len(SOURCE_C[m]) else 0
            assert len(reduced) == expected, (m, r, len(reduced), expected)
        print(f"Enumerated dimensions {r}/8", flush=True)

    orbit_records = []
    normalized = {0: [1]}
    for m in range(1, 5):
        denominator = 2 ** m * factorial(m)
        coefficients = [0] * (2 * m + 1)
        for k in range(1, 2 * m + 1):
            remaining = set(strict[m, k])
            while remaining:
                representative = min(remaining, key=lambda s: tuple(sorted(s)))
                nodes = sorted(representative)
                node_index = {v: i for i, v in enumerate(nodes)}
                pairs = graph_pairs(representative, k)
                pair_vertices = set(v for pair in pairs for v in pair)
                orbit, images, automorphisms, kernel = set(), set(), 0, 0
                for p in permutations(range(k)):
                    transformed = [tuple(v[p[j]] for j in range(k)) for v in nodes]
                    shape = frozenset(transformed)
                    orbit.add(shape)
                    if shape != representative:
                        continue
                    automorphisms += 1
                    node_permutation = tuple(node_index[v] for v in transformed)
                    images.add(node_permutation)
                    if node_permutation == tuple(range(m)):
                        kernel += 1
                        assert all(p[j] == j for j in range(k) if j not in pair_vertices)
                        assert all({p[a], p[b]} == {a, b} for a, b in pairs)
                assert orbit <= strict[m, k]
                assert len(orbit) * automorphisms == factorial(k)
                assert automorphisms == kernel * len(images)
                assert (2 ** len(pairs)) % kernel == 0
                assert factorial(m) % len(images) == 0
                assert denominator % automorphisms == 0
                remaining.difference_update(orbit)
                add_scaled(coefficients, falling(k), denominator // automorphisms)
                orbit_records.append(dict(m=m, k=k, nodes=nodes, automorphisms=automorphisms,
                                          kernel=kernel, image=len(images), isolated_pairs=len(pairs)))
        assert coefficients[-1] == 1 and coefficients[0] == 0
        normalized[m] = coefficients
    print("All automorphism groups and orbit identities passed", flush=True)

    direct_checks = 0
    for m, coefficients in normalized.items():
        denominator = 2 ** m * factorial(m)
        for r in range(1, 9):
            assert evaluate(coefficients, r) == denominator * totals[m, r]
            assert totals[m, r] == sum(comb(r, k) * c for k, c in enumerate(SOURCE_C[m]) if k <= r)
            direct_checks += 1

    table_checks = 0
    for m in range(5, 10):
        denominator = 2 ** m * factorial(m)
        coefficients = [0] * (2 * m + 1)
        assert len(SOURCE_C[m]) == 2 * m + 1
        for k, c in enumerate(SOURCE_C[m]):
            assert (denominator * c) % factorial(k) == 0
            add_scaled(coefficients, falling(k), denominator * c // factorial(k))
            table_checks += 1
        assert coefficients[-1] == 1 and coefficients[0] == 0
        normalized[m] = coefficients

    result = dict(passed=True, groups=4, checked_at_utc=datetime.now(timezone.utc).isoformat(),
                  method="Python standard-library exact integer enumeration; no floating point.",
                  labeled_enumeration=dict(maximum_added_nodes=4, dimensions=list(range(1, 9)),
                                           compared_source="arXiv:1203.4419v1 Table 3"),
                  group_checks=dict(orbits=len(orbit_records), records=orbit_records),
                  polynomial_evaluation_checks=direct_checks,
                  additional_source_table_checks=table_checks,
                  alpha_rows={str(m): list(reversed(a)) for m, a in normalized.items()},
                  limits="Finite checks support the self-contained all-m proof; they do not establish it.")
    target = Path(__file__).with_name("verification-results.json")
    target.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ['group_checks', 'alpha_rows']}))
    print("Orbits checked:", len(orbit_records))


if __name__ == "__main__":
    main()
