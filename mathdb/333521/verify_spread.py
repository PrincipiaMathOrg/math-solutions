#!/usr/bin/env python3
"""Exact and exhaustive checks for the proof of MathDB #333521."""

from __future__ import annotations

from collections import deque
from fractions import Fraction
from itertools import combinations
from math import copysign, sqrt


def require(condition: bool, message: object) -> None:
    if not condition:
        raise AssertionError(message)


def theta_for_parts(a: int, b: int) -> tuple[Fraction, str]:
    """Return the proof's convex weight, assuming a >= b >= 2."""

    n = a + b
    if b >= 4:
        if a * (b - 2) <= b * b:
            return Fraction(0), "zero"
        return Fraction(a * (b - 2) - b * b, n * (b - 2)), "Y"
    if b == 3:
        if a <= 9:
            return Fraction(0), "zero"
        return Fraction(a * (a - 9), n * (a - 3)), "Z"
    require(b == 2, (a, b))
    if a <= 6:
        return Fraction(0), "zero"
    return Fraction(a * (a - 6), n * (a - 2)), "Z"


def coefficients(a: int, b: int, theta: Fraction) -> tuple[Fraction, ...]:
    n = a + b
    return (
        Fraction(4, n) - theta * Fraction(2 * (a - 2), a * (a - 1)),
        Fraction(4, n)
        - (1 - theta) * Fraction(2 * (b - 2), b * (b - 1)),
        Fraction(4, n) - theta * Fraction(1, a) - (1 - theta) * Fraction(1, b),
    )


def base_bound(a: int, b: int, theta: Fraction) -> Fraction:
    """The lower bound at X=a(a-1), Y=b(b-1), Z=ab."""

    n = a + b
    d = a - b
    compact = Fraction(3 * n, 2) + Fraction(d, 2) + Fraction(d * d, n) - theta * d

    x = a * (a - 1)
    y = b * (b - 1)
    z = a * b
    w = x + y + z
    r_a = Fraction(2 * (a - 2) * x + (a - 1) * z, a * (a - 1))
    r_b = Fraction(2 * (b - 2) * y + (b - 1) * z, b * (b - 1))
    raw = Fraction(4 * w, n) - theta * r_a - (1 - theta) * r_b
    require(raw == compact, (a, b, theta, raw, compact))
    require(r_a == n + a - 4 and r_b == n + b - 4, (a, b, r_a, r_b))
    return raw


def rational_gt_sqrt(value: Fraction, radicand: int) -> bool:
    return value > 0 and value * value > radicand


def rational_lt_sqrt(value: Fraction, radicand: int) -> bool:
    return value <= 0 or value * value < radicand


def check_symbolic_ranges(limit: int = 2_000) -> dict[str, int]:
    regimes = {"zero": 0, "Y": 0, "Z": 0, "star": 0}
    partitions = 0

    for n in range(4, limit + 1):
        for b in range(1, n // 2 + 1):
            a = n - b
            partitions += 1
            d = a - b

            if b == 1:
                regimes["star"] += 1
                delta = 9 * n * n - 32 * n + 32
                require(delta > (n + 2) ** 2, ("least star eigenvalue", n))
                if n % 2 == 0:
                    require(Fraction(delta) > Fraction(9 * n * n, 4), ("star", n))
                else:
                    require(delta > (2 * n - 1) ** 2, ("star lower", n))
                    require((2 * n - 3) ** 2 > n * n + 8, ("star target", n))
                continue

            theta, regime = theta_for_parts(a, b)
            regimes[regime] += 1
            require(Fraction(0) <= theta <= Fraction(1), (a, b, theta))
            c_x, c_y, c_z = coefficients(a, b, theta)
            require(min(c_x, c_y, c_z) >= 0, (a, b, theta, c_x, c_y, c_z))

            # This is the theta-independent numerator proving c_X >= 0.
            require(a * (a - b) + 2 * b > 0, ("c_X numerator", a, b))

            bound = base_bound(a, b, theta)
            if regime == "Y":
                expected = Fraction(3 * n, 2) + Fraction(d * (b * n - 2 * d), 2 * n * (b - 2))
                require(bound == expected, ("Y identity", a, b, bound, expected))
                require(bound - Fraction(3 * n, 2) >= Fraction(d, 2), ("Y surplus", a, b))
            elif regime == "Z":
                require(bound == 2 * n, ("Z identity", a, b, bound))

            if n % 2 == 0:
                target = Fraction(3 * n, 2)
                if d == 0:
                    require(theta == 0 and bound == target, ("even equality", a, b))
                    require(min(c_x, c_y, c_z) > 0, ("even coefficients", a, b))
                else:
                    require(bound > target, ("even strict", a, b, bound, target))
            elif d == 1:
                # Complete K_{b+1,b} attains the target. A nonedge raises Z by at
                # least two, and the resulting 2*c_Z closes the small base deficit.
                require(n >= 5 and theta == 0, ("odd balanced regime", a, b, theta))
                target_offset = Fraction(2 * n + 1, 1)
                twice_base = 2 * bound
                require(rational_lt_sqrt(twice_base - target_offset, n * n + 8),
                        ("base deficit", a, b, bound))
                improved = bound + 2 * c_z
                require(rational_gt_sqrt(2 * improved - target_offset, n * n + 8),
                        ("noncomplete improvement", a, b, improved))
                require(2 * c_z > Fraction(1, n), ("simple gap", a, b, c_z))
            else:
                require(d >= 3, ("odd imbalance", a, b, d))
                require(rational_gt_sqrt(2 * bound - (2 * n + 1), n * n + 8),
                        ("odd strict", a, b, bound))

    return {"partitions": partitions, **regimes}


def classify_graph(n: int, mask: int, edge_list: list[tuple[int, int]]) -> tuple[list[list[int]], list[int]] | None:
    adjacency = [[] for _ in range(n)]
    for bit, (u, v) in enumerate(edge_list):
        if mask & (1 << bit):
            adjacency[u].append(v)
            adjacency[v].append(u)

    color = [-1] * n
    color[0] = 0
    queue = deque([0])
    seen = 1
    while queue:
        u = queue.popleft()
        for v in adjacency[u]:
            if color[v] < 0:
                color[v] = 1 - color[u]
                seen += 1
                queue.append(v)
            elif color[v] == color[u]:
                return None
    if seen != n:
        return None
    return adjacency, color


def all_distances(adjacency: list[list[int]]) -> list[list[int]]:
    n = len(adjacency)
    result = []
    for root in range(n):
        distance = [-1] * n
        distance[root] = 0
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v in adjacency[u]:
                if distance[v] < 0:
                    distance[v] = distance[u] + 1
                    queue.append(v)
        require(min(distance) >= 0, ("disconnected", root, adjacency))
        result.append(distance)
    return result


def jacobi_eigenvalues(matrix: list[list[float]]) -> list[float]:
    a = [row[:] for row in matrix]
    n = len(a)
    for _ in range(100 * n * n):
        p, q = 0, 1
        largest = 0.0
        for i in range(n):
            for j in range(i + 1, n):
                if abs(a[i][j]) > largest:
                    largest = abs(a[i][j])
                    p, q = i, j
        if largest < 1e-12:
            return sorted(a[i][i] for i in range(n))

        apq = a[p][q]
        tau = (a[q][q] - a[p][p]) / (2.0 * apq)
        t = copysign(1.0, tau) / (abs(tau) + sqrt(1.0 + tau * tau)) if tau else 1.0
        c = 1.0 / sqrt(1.0 + t * t)
        s = t * c
        app, aqq = a[p][p], a[q][q]
        for k in range(n):
            if k in (p, q):
                continue
            akp, akq = a[k][p], a[k][q]
            a[k][p] = a[p][k] = c * akp - s * akq
            a[k][q] = a[q][k] = s * akp + c * akq
        a[p][p] = c * c * app - 2.0 * s * c * apq + s * s * aqq
        a[q][q] = s * s * app + 2.0 * s * c * apq + c * c * aqq
        a[p][q] = a[q][p] = 0.0
    raise AssertionError(("Jacobi nonconvergence", matrix))


def target_spread(n: int) -> float:
    if n == 2:
        return 2.0
    if n == 3:
        return (5.0 + sqrt(17.0)) / 2.0
    if n % 2 == 0:
        return 1.5 * n
    return (2.0 * n + 1.0 + sqrt(n * n + 8.0)) / 2.0


def analytic_bound(distance: list[list[int]], color: list[int]) -> Fraction | None:
    parts = [[v for v, c in enumerate(color) if c == side] for side in (0, 1)]
    parts.sort(key=len, reverse=True)
    a, b = map(len, parts)
    if b == 1:
        return None
    theta, _ = theta_for_parts(a, b)
    x = sum(distance[u][v] for u, v in combinations(parts[0], 2))
    y = sum(distance[u][v] for u, v in combinations(parts[1], 2))
    z = sum(distance[u][v] for u in parts[0] for v in parts[1])
    n = a + b
    r_a = Fraction(2 * (a - 2) * x + (a - 1) * z, a * (a - 1))
    r_b = Fraction(2 * (b - 2) * y + (b - 1) * z, b * (b - 1))
    return Fraction(4 * (x + y + z), n) - theta * r_a - (1 - theta) * r_b


def check_graphs(max_n: int = 6) -> dict[str, int]:
    connected_bipartite = 0
    equality_graphs = 0
    nonextremal = 0
    smallest_gap = float("inf")

    for n in range(2, max_n + 1):
        edge_list = list(combinations(range(n), 2))
        target = target_spread(n)
        for mask in range(1 << len(edge_list)):
            classified = classify_graph(n, mask, edge_list)
            if classified is None:
                continue
            adjacency, color = classified
            connected_bipartite += 1
            distance = all_distances(adjacency)
            transmissions = [sum(row) for row in distance]
            q_matrix = [
                [float(distance[i][j] + (transmissions[i] if i == j else 0)) for j in range(n)]
                for i in range(n)
            ]
            eigenvalues = jacobi_eigenvalues(q_matrix)
            spread = eigenvalues[-1] - eigenvalues[0]

            part_sizes = sorted((color.count(0), color.count(1)))
            edge_count = sum(map(len, adjacency)) // 2
            extremal = part_sizes == [n // 2, (n + 1) // 2] and edge_count == part_sizes[0] * part_sizes[1]
            if extremal:
                equality_graphs += 1
                require(abs(spread - target) < 1e-8, ("target spectrum", n, mask, spread, target))
            else:
                nonextremal += 1
                gap = spread - target
                smallest_gap = min(smallest_gap, gap)
                require(gap > 1e-8, ("counterexample", n, mask, spread, target))

            lower = analytic_bound(distance, color)
            if lower is not None:
                require(spread + 1e-8 >= float(lower), ("Rayleigh bound", n, mask, spread, lower))

    return {
        "connected_bipartite_labeled": connected_bipartite,
        "labeled_equality_graphs": equality_graphs,
        "labeled_nonextremal_graphs": nonextremal,
        "smallest_nonzero_gap_scaled": round(smallest_gap * 1_000_000),
    }


def main() -> None:
    symbolic = check_symbolic_ranges()
    exhaustive = check_graphs()
    print(f"exact part-size pairs through n=2000: {symbolic['partitions']}")
    print(f"theta regimes: zero={symbolic['zero']}, Y={symbolic['Y']}, Z={symbolic['Z']}, star={symbolic['star']}")
    print(f"connected labeled bipartite graphs through n=6: {exhaustive['connected_bipartite_labeled']}")
    print(f"labeled balanced-complete equality graphs: {exhaustive['labeled_equality_graphs']}")
    print(f"labeled strict nonextremal graphs: {exhaustive['labeled_nonextremal_graphs']}")
    print(f"smallest strict spectral gap x 1e6: {exhaustive['smallest_nonzero_gap_scaled']}")
    print("all exact algebra and exhaustive spectral checks passed")


if __name__ == "__main__":
    main()
