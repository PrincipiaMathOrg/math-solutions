"""Exact finite certificates supporting solution.tex's infinite disproof."""
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
from fractions import Fraction
import json,hashlib
import sympy as s

x=s.symbols('x');polynomials={1:s.Poly(1,x)}
for n in range(1,7):
 p=polynomials[n].as_expr()
 polynomials[n+1]=s.Poly((1+x+(2*n-1)*x*x)*p+x*(1-x*x)*s.diff(p,x),x)
expected=[1,63,1023,4641,16479,26481,37759,26481,16479,4641,1023,63,1]
p=polynomials[7]
assert [int(p.nth(k)) for k in range(13)]==expected
assert p.eval(s.Rational(-1,20))==-s.Rational(316770843280059,4096000000000000)
assert p.eval(-1)==10395 and p.eval(0)==1
assert p.eval(-20)==-316770843280059

def dual_permutations(n):
 if n==0:
  yield ()
 else:
  for word in dual_permutations(n-1):
   for pos in range(len(word)+1):
    yield word[:pos]+(2*n,2*n-1)+word[pos:]

counts=Counter()
for word in dual_permutations(7):
 directions=[word[j+1]>word[j] for j in range(len(word)-1)]
 runs=1+sum(a!=b for a,b in zip(directions,directions[1:]))
 counts[runs]+=1
assert sum(counts.values())==135135
assert [counts[k] for k in range(1,14)]==expected

sturm=[]
for n,pn in polynomials.items():
 if n==1:continue
 negative=int(pn.count_roots(-s.oo,0));positive=int(pn.count_roots(0,s.oo))
 assert positive==0
 assert negative==(0 if n<7 else 4)
 assert list(pn.all_coeffs())==list(reversed(pn.all_coeffs()))
 assert pn.eval(0)==1 and pn.eval(-1)>0
 sturm.append({'n':n,'negative_real_roots':negative,'positive_real_roots':positive})

root=Path(__file__).resolve().parent
result=dict(status='passed',checked_at_utc=datetime.now(timezone.utc).isoformat(),
 verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 groups=[
  dict(name='exact recurrence and sign certificate',exact=True,coefficients_P7=expected,
       value_at_minus_one_over_twenty='-316770843280059/4096000000000000'),
  dict(name='independent dual-Stirling-permutation enumeration',exact=True,
       objects=135135,runs_histogram=dict(sorted(counts.items()))),
  dict(name='exact Sturm counts and reciprocity',exact=True,cases=sturm)],
 limitation='The infinite n>=7 extension uses the analytic negative-minimum argument, not the finite checks.')
(root/'verification-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(result,indent=2))
