#!/usr/bin/env python3
"""Exact checks for the construction resolving MathDB #361027.

The checker independently validates the Walecki edge partitions, constructs
the incidence coloring from arbitrary edge signs, and checks the signed-color
axioms directly.  It exhausts every signature through n=4 and uses fixed
pseudorandom signatures for larger orders.
"""

from __future__ import annotations

import itertools
import random
from collections import defaultdict


Edge = tuple[int, int]
Incidence = tuple[int, int]


def require(condition: bool, message: str = "verification failed") -> None:
    """Optimization-stable assertion used by both normal and -O runs."""
    if not condition:
        raise AssertionError(message)


def edge(u: int, v: int) -> Edge:
    return (u, v) if u < v else (v, u)


def complete_edges(vertices: list[int]) -> set[Edge]:
    return {edge(u, v) for u, v in itertools.combinations(vertices, 2)}


def walecki_cycles(m: int) -> list[list[int]]:
    """Hamilton cycles of K_(2m+1), with infinity represented by 2m."""
    infinity = 2 * m
    cycles: list[list[int]] = []
    for i in range(m):
        finite = [i]
        for j in range(1, m):
            finite.extend(((i - j) % (2 * m), (i + j) % (2 * m)))
        finite.append((i - m) % (2 * m))
        cycles.append([infinity, *finite])
    return cycles


def path_edges(path: list[int]) -> set[Edge]:
    return {edge(u, v) for u, v in itertools.pairwise(path)}


def cycle_edges(cycle: list[int]) -> set[Edge]:
    return path_edges([*cycle, cycle[0]])


def even_paths(n: int) -> list[list[int]]:
    require(n >= 2 and n % 2 == 0)
    return [cycle[1:] for cycle in walecki_cycles(n // 2)]


def odd_paths_and_matching(n: int, distinguished: int) -> tuple[list[list[int]], set[Edge]]:
    require(n >= 3 and n % 2 == 1)
    m = (n - 1) // 2
    others = [v for v in range(n) if v != distinguished]
    relabel = {2 * m: distinguished, **{v: others[v] for v in range(2 * m)}}
    paths: list[list[int]] = []
    matching: set[Edge] = set()
    for cycle in walecki_cycles(m):
        finite = cycle[1:]
        left = finite[m - 1]
        right = finite[m]
        matching.add(edge(relabel[left], relabel[right]))
        path = finite[m:] + [cycle[0]] + finite[:m]
        paths.append([relabel[v] for v in path])
    return paths, matching


def assert_partitions() -> None:
    for m in range(1, 40):
        cycles = walecki_cycles(m)
        target = complete_edges(list(range(2 * m + 1)))
        seen: set[Edge] = set()
        for cycle in cycles:
            require(len(cycle) == len(set(cycle)) == 2 * m + 1)
            current = cycle_edges(cycle)
            require(seen.isdisjoint(current))
            seen |= current
        require(seen == target)

        even = even_paths(2 * m)
        seen = set()
        for path in even:
            require(len(path) == len(set(path)) == 2 * m)
            current = path_edges(path)
            require(seen.isdisjoint(current))
            seen |= current
        require(seen == complete_edges(list(range(2 * m))))
        endpoint_count = defaultdict(int)
        for path in even:
            endpoint_count[path[0]] += 1
            endpoint_count[path[-1]] += 1
        require(set(endpoint_count.values()) == {1})

        for distinguished in (0, m, 2 * m):
            odd, matching = odd_paths_and_matching(2 * m + 1, distinguished)
            seen = set(matching)
            for path in odd:
                require(len(path) == len(set(path)) == 2 * m + 1)
                require(path[0] != distinguished != path[-1])
                current = path_edges(path)
                require(seen.isdisjoint(current))
                seen |= current
            require(seen == target)
            require(len(matching) == m)
            matched = {v for current in matching for v in current}
            require(matched == target_vertices(2 * m + 1) - {distinguished})


def target_vertices(n: int) -> set[int]:
    return set(range(n))


def color_path(
    path: list[int],
    magnitude: int,
    signs: dict[Edge, int],
    colors: dict[Incidence, int],
    start: int = 1,
) -> None:
    arrival: int | None = None
    for index, (u, v) in enumerate(itertools.pairwise(path)):
        at_u = start * magnitude if index == 0 else -arrival
        at_v = -signs[edge(u, v)] * at_u
        colors[(u, v)] = at_u
        colors[(v, u)] = at_v
        arrival = at_v


def clique_coloring(
    vertices: list[int],
    distinguished: int,
    signs: dict[Edge, int],
) -> tuple[dict[Incidence, int], int]:
    n = len(vertices)
    local_of = {vertex: index for index, vertex in enumerate(vertices)}
    vertex_of = {index: vertex for vertex, index in local_of.items()}
    colors: dict[Incidence, int] = {}

    if n % 2 == 0:
        local_paths = even_paths(n)
        endpoint_index = next(
            i
            for i, path in enumerate(local_paths)
            if local_of[distinguished] in (path[0], path[-1])
        )
        local_paths[0], local_paths[endpoint_index] = (
            local_paths[endpoint_index],
            local_paths[0],
        )
        for magnitude, local_path in enumerate(local_paths, 1):
            path = [vertex_of[v] for v in local_path]
            color_path(path, magnitude, signs, colors)
    else:
        local_paths, local_matching = odd_paths_and_matching(
            n, local_of[distinguished]
        )
        for magnitude, local_path in enumerate(local_paths, 1):
            path = [vertex_of[v] for v in local_path]
            color_path(path, magnitude, signs, colors)
        for local_u, local_v in local_matching:
            u, v = vertex_of[local_u], vertex_of[local_v]
            colors[(u, v)] = colors[(v, u)] = 0

    used = {colors[(distinguished, v)] for v in vertices if v != distinguished}
    palette = set(range(-(n // 2), n // 2 + 1))
    if n % 2 == 0:
        palette.remove(0)
    missing = palette - used
    require(len(missing) == 1)
    return colors, missing.pop()


def construct_coloring(n: int, signs: dict[Edge, int]) -> dict[Incidence, int]:
    if n == 1:
        return {(0, 1): 0, (1, 0): 0}

    left = list(range(n))
    right = list(range(n, 2 * n))
    u, v = left[0], right[0]
    left_colors, left_missing = clique_coloring(left, u, signs)
    right_colors, right_missing = clique_coloring(right, v, signs)

    if n % 2 == 0:
        # Both endpoint paths use magnitude 1.  Flipping all colors on the
        # right magnitude-1 path changes which signed color is missing.
        required_right = -signs[edge(u, v)] * left_missing
        if right_missing != required_right:
            for incidence, value in list(right_colors.items()):
                if abs(value) == 1:
                    right_colors[incidence] = -value
            right_missing = -right_missing
        require(right_missing == required_right)
        bridge_left, bridge_right = left_missing, right_missing
    else:
        require(left_missing == right_missing == 0)
        bridge_left = bridge_right = 0

    colors = {**left_colors, **right_colors}
    colors[(u, v)] = bridge_left
    colors[(v, u)] = bridge_right
    return colors


def graph_edges(n: int) -> list[Edge]:
    left = list(range(n))
    right = list(range(n, 2 * n))
    return sorted(
        complete_edges(left)
        | complete_edges(right)
        | {edge(left[0], right[0])}
    )


def verify_coloring(n: int, signs: dict[Edge, int], colors: dict[Incidence, int]) -> None:
    edges = graph_edges(n)
    palette = set(range(-(n // 2), n // 2 + 1))
    if n % 2 == 0:
        palette.remove(0)
    at_vertex: dict[int, list[int]] = defaultdict(list)
    for u, v in edges:
        require((u, v) in colors and (v, u) in colors)
        cu, cv = colors[(u, v)], colors[(v, u)]
        require(cu in palette and cv in palette)
        require(cu == -signs[(u, v)] * cv)
        at_vertex[u].append(cu)
        at_vertex[v].append(cv)
    for values in at_vertex.values():
        require(len(values) == len(set(values)))
    require(max(map(len, at_vertex.values())) == n)


def signs_from_mask(edges: list[Edge], mask: int) -> dict[Edge, int]:
    return {current: (-1 if mask >> i & 1 else 1) for i, current in enumerate(edges)}


def run() -> None:
    assert_partitions()

    exhaustive = 0
    for n in range(1, 5):
        edges = graph_edges(n)
        for mask in range(1 << len(edges)):
            signs = signs_from_mask(edges, mask)
            verify_coloring(n, signs, construct_coloring(n, signs))
            exhaustive += 1

    rng = random.Random(361027)
    sampled = 0
    for n in range(5, 41):
        edges = graph_edges(n)
        patterns = [
            {current: 1 for current in edges},
            {current: -1 for current in edges},
        ]
        for _ in range(12):
            patterns.append({current: rng.choice((-1, 1)) for current in edges})
        for signs in patterns:
            verify_coloring(n, signs, construct_coloring(n, signs))
            sampled += 1

    print("MathDB #361027 construction verified")
    print("Walecki decompositions: all orders 2..80 and 3..79")
    print(f"Exhaustive full-graph signatures through n=4: {exhaustive}")
    print(f"Deterministic/random signatures for n=5..40: {sampled}")


if __name__ == "__main__":
    run()
