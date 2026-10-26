"""Exact finite checks of the defining equations; the proof handles all n."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
import sympy as s
x,q=s.symbols('x q')
qi=lambda n:sum(q**j for j in range(n))
limit=7
fac=[s.Integer(1)]
for n in range(1,limit):fac.append(s.expand(fac[-1]*qi(n)))
cat=[s.Integer(1)]
for n in range(limit):
    cat.append(s.expand(sum(q**j*cat[j]*cat[n-j] for j in range(n+1))))
polys=[None,s.Integer(1)]
for n in range(1,limit):
    value=(qi(2*n-1)+x*q**(2*n-1))*polys[n]
    for j in range(n-1):
        value+=q**(2*j+1)*qi(n-j-1)*cat[j]*s.prod(
            qi(t) for t in range(n-j,n))*polys[n-j]
    polys.append(s.expand(value))
equations=0
for n in range(1,limit):
    # Independent defining Hahn equation, after clearing the q-factorials.
    residual=polys[n+1].subs(x,1+q*x)-polys[n+1]
    residual-=q*qi(n)*(1+(q-1)*x)*polys[n].subs(x,q*q*x+q+1)
    assert s.expand(residual)==0
    assert s.cancel(polys[n+1].subs(x,-1/q))==0
    equations+=2
term_counts=[]
for n in range(1,limit+1):
    poly=s.Poly(polys[n],x,q)
    assert all(c>0 for c in poly.coeffs())
    assert {a for (a,b) in poly.monoms()}==set(range(n))
    assert s.Poly(polys[n],x).LC()==q**((n-1)**2)
    assert s.gcd(polys[n],fac[n-1])==1
    term_counts.append(poly.length())
assert polys[2]==1+q*x
assert s.expand(polys[3]-(1+q)**2-(q+2*q*q+2*q**3)*x-q**4*x*x)==0
here=Path(__file__).resolve().parent
result=dict(status='passed',checked_at_utc=datetime.now(timezone.utc).isoformat(),
    verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    groups=[
        dict(name='Original Hahn equations and boundary condition',status='passed',
             exact_identities=equations,n_range=[1,limit-1]),
        dict(name='Coefficient positivity and full x-degree support',status='passed',
             n_range=[1,limit],monomial_counts=term_counts),
        dict(name='Leading coefficient, coprimality, and initial examples',status='passed',
             n_range=[1,limit])],
    limitation='Finite checks supplement the all-n induction. Zero credit pending final-source and prior-implication review.')
(here/'verification-results.json').write_text(json.dumps(result,indent=2)+'\n',
    encoding='utf-8',newline='\n')
print(json.dumps(result))
