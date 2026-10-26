"""Exact finite checks supplementing the all-size proof in solution.tex."""
from functools import lru_cache
from itertools import product
from pathlib import Path
from datetime import datetime, timezone
import json

def trim(a):
    a=list(a)
    while len(a)>1 and a[-1]==0:a.pop()
    return tuple(a)

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return trim(c)

def qfactorial(n):
    a=(1,)
    for r in range(1,n+1):a=mul(a,(1,)*r)
    return a

def unimodal(a):
    decreasing=False
    for x,y in zip(a,a[1:]):
        if y<x:decreasing=True
        elif y>x and decreasing:return False
    return True

@lru_cache(None)
def pluck(delays):
    if not delays:return (1,)
    result=[0]
    # The tuple orders leaves from right to left, so index=right-edge count.
    for i,value in enumerate(delays):
        if value!=1:continue
        rest=tuple(max(1,d-1) for j,d in enumerate(delays) if j!=i)
        polynomial=pluck(rest)
        if len(result)<i+len(polynomial):result += [0]*(i+len(polynomial)-len(result))
        for j,c in enumerate(polynomial):result[i+j]+=c
    return trim(result)

def run():
    factorization_cases=0
    for n in range(10):
        for delays in product((1,2),repeat=n):
            actual=pluck(delays)
            expected=(1,) if n==0 else mul(tuple(int(d==1) for d in delays),qfactorial(n-1))
            assert actual==expected and unimodal(actual),(delays,actual,expected)
            factorization_cases+=1

    weighted_cases=0
    for length in range(1,8):
        kernel=qfactorial(length-1)
        for a in product(range(4),repeat=length):
            assert unimodal(mul(a,kernel)),a
            weighted_cases+=1
    additional_binary_cases=0
    for length in range(8,13):
        kernel=qfactorial(length-1)
        for a in product(range(2),repeat=length):
            assert unimodal(mul(a,kernel)),a
            additional_binary_cases+=1

    moving_cases=0
    unimodal_inputs=0
    for length in range(1,8):
        for a in product(range(4),repeat=length):
            if not unimodal(a):continue
            unimodal_inputs+=1
            for width in range(1,9):
                assert unimodal(mul(a,(1,)*width)),(a,width)
                moving_cases+=1

    examples=[((1,1,4,4,1,1),(0,0,1,5,12,18,19,17,17,19,18,12,5,1)),
              ((2,1,4,1,2),(0,0,1,4,5,4,5,4,1))]
    for delays,expected in examples:
        actual=pluck(delays)
        assert actual==expected and not unimodal(actual),(delays,actual)

    return dict(passed=True,groups=4,checked_at_utc=datetime.now(timezone.utc).isoformat(),
                arithmetic='Exact Python integers throughout.',
                recursive_factorization=dict(cases=factorization_cases,leaf_counts='0..9',delay_values=[1,2]),
                theorem_checks=dict(weighted_cases=weighted_cases,coefficient_alphabet=[0,1,2,3],weighted_lengths='1..7',additional_binary_cases=additional_binary_cases,additional_binary_lengths='8..12'),
                moving_sums=dict(unimodal_inputs=unimodal_inputs,cases=moving_cases,widths='1..8'),
                known_scope_counterexamples=dict(cases=2,source='Preprint Example3.1(a) and Remark3.4; both have delay4 and are prior results.'),
                reviewer='Authoring agent only; no independent review or proof assistant.')

if __name__=='__main__':
    result=run()
    Path(__file__).with_name('verification-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(result))
