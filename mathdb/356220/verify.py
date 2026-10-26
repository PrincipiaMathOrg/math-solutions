"""Exact checks for MathDB 356220; Python standard library only."""
from pathlib import Path
import json

N = 58
checks = []


def check(name, condition, **data):
    assert condition, name
    checks.append(dict(name=name, passed=True, **data))


def partitions(n):
    a = [1] + [0] * n
    for k in range(1, n + 1):
        for j in range(k, n + 1):
            a[j] += a[j - k]
    return a


def euler(n):
    a = [1] + [0] * n
    for k in range(1, n + 1):
        for j in range(n, k - 1, -1):
            a[j] -= a[j - k]
    return a


def mobius(n):
    sign, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n > 1 else sign


def reciprocal(c):
    r = [1]
    for n in range(1, len(c)):
        r.append(-sum(c[j] * r[n - j] for j in range(1, n + 1)))
    return r


def geometric_matrix(c):
    """Form C(q)*q^k/(1-q^(2k+1)) directly, without divisor formulas."""
    s = [[0] * (N + 1) for _ in range(N + 1)]
    for k in range(1, N + 1):
        for exponent in range(k, N + 1, 2 * k + 1):
            for n in range(exponent, N + 1):
                s[n][k] += c[n - exponent]
    return s


def inverse(s):
    t = [[0] * (N + 1) for _ in range(N + 1)]
    for k in range(1, N + 1):
        t[k][k] = 1
        for n in range(k + 1, N + 1):
            t[n][k] = -sum(s[n][j] * t[j][k] for j in range(k, n))
    return t


def corrected(n, k, r):
    return sum(mobius(d) * r[((2*n+1)//d-1)//2-k]
               for d in range(1, 2*n+2)
               if (2*n+1) % d == 0 and ((2*n+1)//d-1)//2 >= k)


p = partitions(N + 1)
c = euler(N)
check("Euler product times partition generating function",
      all(sum(c[j] * p[n-j] for j in range(n+1)) == int(n == 0)
          for n in range(N+1)))

inverses = {}
for name, coefficients in [
    ("Euler product", c),
    ("1-q", [1, -1] + [0] * (N-1)),
    ("1+2q-3q^2", [1, 2, -3] + [0] * (N-2)),
]:
    s = geometric_matrix(coefficients)
    t = inverse(s)
    r = reciprocal(coefficients)
    check(name + ": all 1711 lower-triangular entries",
          all(t[n][k] == corrected(n, k, r)
              for n in range(1, N+1) for k in range(1, n+1)))
    check(name + ": direct matrix product",
          all(sum(s[n][j]*t[j][k] for j in range(k, n+1)) == int(n == k)
              for n in range(1, N+1) for k in range(1, n+1)))
    inverses[name] = t


def proposed_terms(n, k):
    negative, positive = [], []
    for i in range(1, n+1):
        num, den = n-i, 2*i+1
        if num % den == 0 and num//den >= k:
            negative.append(dict(i=i, partition_index=num//den-k,
                                 value=p[num//den-k]))
    for m in range(2, n+1):
        for i in range(1, n+1):
            num, den = n-p[m+1]*i-p[m-1], p[m+1]*(2*i+1)
            if num >= 0 and num % den == 0 and num//den >= k:
                positive.append(dict(m=m, i=i, partition_index=num//den-k,
                                     value=p[num//den-k]))
    return negative, positive


def proposed(n, k):
    neg, pos = proposed_terms(n, k)
    return p[n-k]-sum(x["value"] for x in neg)+sum(x["value"] for x in pos)


t = inverses["Euler product"]
differences = [(n, k, proposed(n, k), t[n][k])
               for n in range(1, N+1) for k in range(1, n+1)
               if proposed(n, k) != t[n][k]]
check("first disagreement", differences[0] == (58, 1, 613766, 613767),
      first= differences[0], differences_through_row_58=differences)
neg, pos = proposed_terms(58, 1)
check("counterexample partition values",
      [p[j] for j in [57, 18, 5, 3, 0]] == [614154, 385, 7, 3, 1])
check("counterexample negative terms",
      [(x["i"], x["partition_index"]) for x in neg] == [(1, 18), (4, 5), (6, 3), (19, 0)],
      terms=neg)
check("counterexample positive terms",
      [(x["m"], x["i"], x["partition_index"]) for x in pos] == [(2, 1, 5), (2, 6, 0)],
      terms=pos)
check("corrected counterexample",
      p[57]-p[18]-p[3]+p[0] == t[58][1] == 613767)

certificate = dict(all_passed=True, check_count=len(checks), checks=checks,
                   bound=N, arithmetic="exact Python integers",
                   scope="Finite regression checks; the manuscript proves the formula for all entries.")
Path(__file__).with_name("exact-certificate.json").write_text(
    json.dumps(certificate, indent=2)+"\n", encoding="utf-8", newline="\n")
print(json.dumps(dict(all_passed=True, check_count=len(checks),
                     first_disagreement=differences[0])))
