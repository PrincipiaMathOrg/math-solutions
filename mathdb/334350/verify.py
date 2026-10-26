"""Exact, standard-library verification for MathDB 334350."""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
from itertools import combinations_with_replacement
from math import comb
from pathlib import Path
import json


def convolution(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def rhs_coefficients(n, j):
    base, power = [0] + [1]*n, [1]
    result = [0] * (n*j+1)
    for ell in range(1, j+1):
        power = convolution(power, base)
        factor = comb(j*(n+1), j-ell)
        for r, value in enumerate(power):
            result[r] += factor*value
    return result


def brute_counts(n, j):
    return Counter(value-i*n
                   for lam in combinations_with_replacement(range(1, n*j+1), j)
                   for i, value in enumerate(lam))


def order_statistic_counts(n, j):
    """Count equal-coordinate marked tuples directly, allowing ties."""
    out = Counter()
    a = n*j
    for i in range(1, j+1):
        for value in range(1, a+1):
            left = comb(value+i-2, i-1)
            right = comb(a-value+j-i, j-i)
            out[value-(i-1)*n] += left*right
    return out


def compare(n, j, counts):
    rr = rhs_coefficients(n, j)
    assert sum(counts.values()) == j*comb(j*(n+1)-1, j)
    for r in set(counts) | {n+1-r for r in counts}:
        assert counts[r] == counts[n+1-r]
    for r in range(1, n*j+1):
        assert counts[r]-counts[-r] == rr[r]
        assert rr[r] > 0
    return rr


def coefficient_lemma(a, j, b):
    direct = sum(Fraction(comb(j+p-1, p))*b**(p-a) for p in range(a))
    pp = sum(Fraction(comb(a+q-1, q))*(1-b)**(q-j) for q in range(j))
    assert direct == b**(-a)*(1-b)**(-j)-pp


def main():
    brute = []
    for n in range(1, 6):
        for j in range(1, 7):
            tuples = comb(j*(n+1)-1, j)
            if tuples > 100000:
                continue
            counts = brute_counts(n, j)
            assert counts == order_statistic_counts(n, j)
            compare(n, j, counts)
            brute.append({'n': n, 'j': j, 'weak_tuples': tuples})
    larger = []
    for n in range(1, 13):
        for j in range(1, 17):
            counts = order_statistic_counts(n, j)
            rr = compare(n, j, counts)
            larger.append({'n': n, 'j': j, 'positive_coefficients': n*j,
                           'signed_mass': sum(rr)})
    functions_checked = 0
    for n, j in [(1, 9), (2, 7), (3, 5), (5, 4)]:
        counts = brute_counts(n, j)
        rr = rhs_coefficients(n, j)
        functions = [lambda r, k=k: r**(2*k+1) for k in range(13)]
        functions += [lambda r: (r > 0)-(r < 0),
                      lambda r: ((r > 0)-(r < 0))*2**abs(r),
                      lambda r: Fraction(r, 1+r*r)]
        for func in functions:
            lhs = sum(amount*func(r) for r, amount in counts.items())
            rhs = sum(amount*func(r) for r, amount in enumerate(rr))
            assert lhs == rhs
            functions_checked += 1
    rational_checks = 0
    for a in range(1, 13):
        for j in range(1, 13):
            for b in [Fraction(2, 3), Fraction(-3, 5), Fraction(7, 4)]:
                coefficient_lemma(a, j, b)
                rational_checks += 1
    result = {'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'passed': True, 'groups': 4,
              'brute_tuple_distributions': brute,
              'order_statistic_distributions': larger,
              'summary': {'brute_parameter_pairs': len(brute),
                          'brute_tuples': sum(v['weak_tuples'] for v in brute),
                          'larger_parameter_pairs': len(larger),
                          'odd_function_checks': functions_checked,
                          'rational_lemma_checks': rational_checks},
              'limitation': 'Finite exact checks supplement the proof for all positive n,j and every odd function.'}
    Path(__file__).with_name('verification-results.json').write_text(
        json.dumps(result, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'passed': True, 'groups': 4, **result['summary']}))


if __name__ == '__main__':
    main()
