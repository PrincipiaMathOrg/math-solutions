"""Exact certificates; run with Python 3 and SymPy. No network access."""
from collections import Counter, deque
from datetime import datetime, timezone
from hashlib import sha256
from itertools import combinations
from math import comb
from pathlib import Path
import json
import sympy as sp


def boundary(facets):
    ridges = sorted({g for f in facets for g in combinations(f, len(f)-1)})
    index = {g: i for i, g in enumerate(ridges)}
    b = sp.zeros(len(ridges), len(facets))
    for j, f in enumerate(facets):
        for k in range(len(f)):
            b[index[f[:k]+f[k+1:]], j] = (-1)**k
    return ridges, b


def acyclic(vertex_count, arrows):
    out = [[] for _ in range(vertex_count)]
    indegree = [0] * vertex_count
    for a, b in arrows:
        out[a].append(b)
        indegree[b] += 1
    queue = deque(i for i, deg in enumerate(indegree) if deg == 0)
    visited = 0
    while queue:
        v = queue.popleft()
        visited += 1
        for w in out[v]:
            indegree[w] -= 1
            if indegree[w] == 0:
                queue.append(w)
    return visited == vertex_count


def gradient_counts(b):
    n, m = b.shape
    supports = [[i for i in range(n) if b[i,j]] for j in range(m)]
    incidence = [(n+j, i) for j in range(m) for i in supports[j]]
    counts = Counter()
    total = 0

    def visit(j, used, pairs):
        nonlocal total
        if j == m:
            total += 1
            selected = {(n+k, i) for i, k in pairs}
            arrows = [(v,u) if (u,v) in selected else (u,v) for u,v in incidence]
            if acyclic(n+m, arrows):
                counts[len(pairs)] += 1
            return
        visit(j+1, used, pairs)
        for i in supports[j]:
            if i not in used:
                visit(j+1, used | {i}, pairs+[(i,j)])

    visit(0, set(), [])
    return counts, total


def main():
    x = sp.Symbol('lambda')
    groups = []
    for d, r in [(2,3),(2,4),(3,3),(4,3),(3,5)]:
        facets = [tuple(range(d))+(d+j,) for j in range(r)]
        ridges, b = boundary(facets)
        n, m = b.shape
        assert (n,m) == (1+d*r,r)
        assert b.T*b == d*sp.eye(r)+sp.ones(r)
        # Count directly from incidences, without using the closed formula.
        counts, total = gradient_counts(b)
        expected = {i: comb(r,i)*(d**i + (i*d**(i-1) if i else 0)) for i in range(r+1)}
        assert dict(counts) == expected
        assert total == sum(counts.values())
        counted = sp.Poly(sum(counts[i]*x**(n-i) for i in counts), x)
        # Independently compute the characteristic polynomial of the full Laplacian.
        direct = sp.Poly((-(b*b.T)).charpoly(x).as_expr(), x)
        factored = sp.Poly(x**(n-r)*(x+d)**(r-1)*(x+d+r), x)
        assert counted == direct == factored
        degrees = [sum(bool(b[i,j]) for j in range(m)) for i in range(n)]
        assert max(degrees) == r > 2
        groups.append(dict(d=d,r=r,facets=facets,ridges=ridges,
                           matching_counts_by_size=dict(sorted(counts.items())),
                           all_matchings_acyclic=True,polynomial=str(factored.as_expr()),
                           shared_ridge_degree=max(degrees)))
    assert groups[0]['matching_counts_by_size'] == {0:1,1:9,2:24,3:20}
    p = Path(__file__).resolve()
    result = dict(status='passed',checked_at_utc=datetime.now(timezone.utc).isoformat(),
                  arithmetic='Exact integer boundary matrices, determinants, and finite enumeration.',
                  groups=groups,verifier_sha256=sha256(p.read_bytes()).hexdigest(),
                  scope='Five exact certificates; the universal theorem is proved in solution.tex.')
    p.with_name('verification-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
