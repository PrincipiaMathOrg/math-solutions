"""Exact verifier for the five-dimensional representation of X_{2,9}."""

from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path


CERTIFICATE_SHA256 = (
    "db557b4c51e033d699eece7478bcc155dad7f36165163c9e8f0b218366e64981"
)


def affine_lines(vertices: list[tuple[int, int]]) -> set[frozenset[int]]:
    """Reconstruct all collinear triples in AG(2,3)."""
    lines: set[frozenset[int]] = set()
    for triple in itertools.combinations(range(len(vertices)), 3):
        (x1, y1), (x2, y2), (x3, y3) = (vertices[v] for v in triple)
        determinant = (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1)
        if determinant % 3 == 0:
            lines.add(frozenset(triple))
    return lines


def main() -> None:
    if not __debug__:
        raise RuntimeError("run without -O; the exact checks use assert")

    path = Path(__file__).with_name("certificate.json")
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    assert digest == CERTIFICATE_SHA256
    data = json.loads(raw)

    assert set(data) == {
        "format",
        "problem",
        "dimension",
        "threshold",
        "box_radius",
        "vertices",
        "lines",
        "normals",
        "witnesses",
    }
    assert data["format"] == "mathdb-347688-affine-nerve-v1"
    assert data["problem"] == 347688
    assert data["dimension"] == 5
    assert data["threshold"] == 1
    assert data["box_radius"] == 42

    expected_vertices = [(x, y) for x in range(3) for y in range(3)]
    vertices = [tuple(v) for v in data["vertices"]]
    assert vertices == expected_vertices

    reconstructed = affine_lines(vertices)
    stored_order = [tuple(line) for line in data["lines"]]
    assert all(len(line) == 3 for line in stored_order)
    stored = [frozenset(line) for line in stored_order]
    assert len(reconstructed) == 12
    assert len(stored) == len(set(stored)) == 12
    assert set(stored) == reconstructed

    # Every pair determines exactly one affine line.
    pair_counts = {pair: 0 for pair in itertools.combinations(range(9), 2)}
    for line in stored:
        for pair in itertools.combinations(sorted(line), 2):
            pair_counts[pair] += 1
    assert set(pair_counts.values()) == {1}

    normals = data["normals"]
    assert len(normals) == 12
    row_for: dict[tuple[frozenset[int], int], list[int]] = {}
    for line_tuple, line, rows in zip(stored_order, stored, normals):
        assert len(rows) == 3
        assert all(len(row) == 6 for row in rows)
        assert all(type(entry) is int for row in rows for entry in row)
        assert [sum(row[j] for row in rows) for j in range(6)] == [0] * 6
        for vertex, row in zip(line_tuple, rows):
            key = (line, vertex)
            assert key not in row_for
            row_for[key] = row
    assert len(row_for) == 36

    caps = {
        frozenset(combination)
        for combination in itertools.combinations(range(9), 4)
        if not any(line <= frozenset(combination) for line in reconstructed)
    }
    assert len(caps) == 54

    witnesses: dict[frozenset[int], list[int]] = {}
    for key, point in data["witnesses"].items():
        assert len(key) == 4 and key == "".join(sorted(key))
        assert all(character in "012345678" for character in key)
        cap = frozenset(int(character) for character in key)
        assert len(cap) == 4 and cap not in witnesses
        witnesses[cap] = point
    assert set(witnesses) == caps

    minimum = None
    maximum = None
    evaluations = 0
    for cap, point in witnesses.items():
        assert len(point) == 5
        assert all(type(coordinate) is int for coordinate in point)
        assert all(abs(coordinate) <= data["box_radius"] for coordinate in point)
        for vertex in cap:
            incident = [line for line in reconstructed if vertex in line]
            assert len(incident) == 4
            for line in incident:
                row = row_for[(line, vertex)]
                value = row[0] + sum(
                    coefficient * coordinate
                    for coefficient, coordinate in zip(row[1:], point)
                )
                assert value >= data["threshold"]
                minimum = value if minimum is None else min(minimum, value)
                maximum = value if maximum is None else max(maximum, value)
                evaluations += 1
    assert evaluations == 54 * 4 * 4 == 864
    assert (minimum, maximum) == (50, 1834)

    # Certify the nerve answer independently for every vertex subset.
    face_count = 0
    for mask in range(1 << 9):
        subset = frozenset(v for v in range(9) if mask & (1 << v))
        containing_lines = [line for line in reconstructed if line <= subset]
        containing_caps = [cap for cap in caps if subset <= cap]
        if containing_lines:
            assert not containing_caps
        else:
            assert containing_caps
            face_count += 1
    assert face_count == 172

    print("PASS: exact R^5 nerve certificate for MathDB #347688")
    print(f"certificate sha256: {digest}")
    print("12 lines; 54 caps; 512 subsets; 864 incident evaluations")
    print(f"incident-evaluation range: {minimum}..{maximum}")


if __name__ == "__main__":
    main()
