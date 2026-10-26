"""Exact supplemental checks for the Bernstein positivity theorem."""
from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction as F
from math import comb,factorial
import hashlib,json

def bernoulli(n):
    out=[F(1)]
    for k in range(1,n+1):
        out.append(-sum((F(comb(k+1,j))*out[j] for j in range(k)),F(0))/(k+1))
    return out

def coefficients(n,b):
    return [1-F(2**n,factorial(n))*sum((F(comb(r,j))*b[n-j] for j in range(r+1)),F(0))
            for r in range(n+1)]

def main():
    b=bernoulli(100);groups=[]
    for n in range(1,31):
        out=[F(0)]*(n+1)
        for r,c in enumerate(coefficients(n,b)):
            for ell in range(n-r+1):
                out[r+ell]+=c*comb(n,r)*comb(n-r,ell)*(-1)**ell
        expected=[F(j==0)-F(2**n,factorial(n))*comb(n,j)*b[n-j] for j in range(n+1)]
        assert out==expected
    groups.append(dict(name='exact reconstruction of all power coefficients',degrees=30))
    finite=[]
    for n in range(1,9):
        row=coefficients(n,b)
        assert all(c>0 for c in row) if n>=2 else row==[F(2),F(0)]
        finite.append(dict(n=n,coefficients=[str(c) for c in row],minimum=str(min(row))))
    groups.append(dict(name='complete finite base cases',cases=finite))
    count=0
    for n in range(9,101):
        row=coefficients(n,b)
        assert all(c>0 for c in row)
        count+=len(row)
    groups.append(dict(name='supplemental positivity beyond analytic cutoff',n_range=[9,100],coefficients=count))
    for n in range(1,81):
        row=coefficients(n,b)
        assert sum(row)==n+1
        assert all(row[n-r] == (row[r] if n%2==0 else 2-row[r]) for r in range(n+1))
    groups.append(dict(name='density normalization and Bernoulli reflection',degrees=80))
    out=dict(status='passed',checked_at_utc=datetime.now(timezone.utc).isoformat(),
        verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        groups=groups,dependencies='Python standard library only',
        limitation='Finite exact checks supplement the analytic bound for every n>=9.')
    Path(__file__).with_name('verification-results.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(dict(status=out['status'],base_case_minima=[(x['n'],x['minimum']) for x in finite],
        groups=len(groups),extra_coefficients=count,checked_at_utc=out['checked_at_utc'])))

if __name__=='__main__':main()
