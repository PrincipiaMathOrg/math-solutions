"""Exact supplementary checks; the general proofs are in solution.tex."""
from math import comb
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib

def gauss(a,b):
    a=[[F(x) for x in row]+[F(v)] for row,v in zip(a,b)]
    n=len(a)
    for k in range(n):
        pivot=next(i for i in range(k,n) if a[i][k])
        a[k],a[pivot]=a[pivot],a[k]
        v=a[k][k];a[k]=[x/v for x in a[k]]
        for i in range(n):
            if i!=k:
                v=a[i][k];a[i]=[x-v*y for x,y in zip(a[i],a[k])]
    return [row[-1] for row in a]

for n in range(1,26):
    matrix=[[(-1)**j*comb(s+n-j-1,n-j) for j in range(n+1)] for s in range(1,n+2)]
    e=gauss(matrix,[comb(2*s+n-1,n) for s in range(1,n+2)])
    expected=[2**(n-2*j)*comb(n-j,j) if 2*j<=n else 0 for j in range(n+1)]
    assert e==expected
for n in range(81):
    for s in range(1,21):
        assert comb(2*s+n-1,n)==sum((-1)**j*2**(n-2*j)*comb(n-j,j)*comb(s+n-j-1,n-j) for j in range(n//2+1))
group1=dict(name='Independent rational recovery of Hilbert coefficients',status='passed',dimensions=list(range(1,26)),additional_integer_identity_cases=81*20)

@lru_cache(None)
def words(n):
    if n==0:return ((),)
    result=[]
    for tile,size in [('A',1),('B',1),('D',2)]:
        if size<=n:result.extend((tile,)+w for w in words(n-size))
    return tuple(result)

def compositions(n,s):
    if s==1:
        yield (n,);return
    for a in range(n+1):
        for tail in compositions(n-a,s-1):yield (a,)+tail

def flip(obj):
    for i,w in enumerate(obj):
        for j,t in enumerate(w):
            if t=='D':new=w[:j]+('A','B')+w[j+1:]
            elif w[j:j+2]==('A','B'):new=w[:j]+('D',)+w[j+2:]
            else:continue
            return obj[:i]+(new,)+obj[i+1:]
    return obj

def sign(obj):return (-1)**sum(w.count('D') for w in obj)
total=0
for s in range(1,4):
    for n in range(8):
        universe=set()
        for sizes in compositions(n,s):universe.update(product(*(words(m) for m in sizes)))
        fixed=0;signed=0
        for obj in universe:
            total+=1;partner=flip(obj)
            assert partner in universe and flip(partner)==obj
            signed+=sign(obj)
            if partner==obj:
                fixed+=1;assert sign(obj)==1
                assert all('D' not in w and all(w[j:j+2]!=('A','B') for j in range(len(w))) for w in obj)
            else:assert sign(partner)==-sign(obj)
        assert fixed==signed==comb(n+2*s-1,n)
group2=dict(name='Exhaustive independent word-involution checks',status='passed',objects_checked=total,word_counts=[1,2,3],sizes=list(range(8)))
assert comb(2*5+4-1,4)==16*comb(8,4)-12*comb(7,3)+comb(6,2)
assert 2*1!=2*(1+1)
group3=dict(name='Source example and printed-index error',status='passed',correct_n4_s5=comb(13,4),printed_n1_s1_sides=[2,4])
p=Path(__file__)
result=dict(checked_at_utc=datetime.now(timezone.utc).isoformat(),status='passed',groups=[group1,group2,group3],verifier_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),limitation='Finite exact checks supplement two general proofs; no novelty or independent peer review claimed.')
p.with_name('verification-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(result,indent=2))
