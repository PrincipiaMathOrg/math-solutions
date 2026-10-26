"""Exact certificate checks for MathDB 356988. Requires SymPy."""
from fractions import Fraction as F
from pathlib import Path
from datetime import datetime,timezone
import json,sympy as s

t=s.symbols('mu',nonnegative=True)
HOUSE=[(0,1),(0,3),(0,4),(1,2),(2,3),(3,4)]
THETA=[(0,1),(0,4),(0,5),(1,2),(2,3),(3,4),(3,5)]
D=9*t**3+87*t**2+263*t+241
E=361*t**2+10488*t+59951
HNUM=[6*(t+5)*(3*t**2+16*t+19),3*(7*t**3+67*t**2+201*t+181),
      21*t**3+199*t**2+595*t+553,6*(4*t**3+39*t**2+120*t+113),
      3*(9*t**3+85*t**2+247*t+211),2*(12*t**3+115*t**2+346*t+319)]
HORB=[[(0,3),(3,0)],[(0,1),(3,2)],[(0,4),(3,4)],[(1,0),(2,3)],[(1,2),(2,1)],[(4,0),(4,3)]]
TNUM=[893*t**2+26754*t+151753,893*t**2+25944*t+152563,
      12*(76*t**2+2283*t+13091),3*(361*t**2+9918*t+51521),12*(76*t**2+2208*t+12941)]
TORB=[[(0,1),(3,2)],[(0,4),(0,5),(3,4),(3,5)],[(1,0),(2,3)],[(1,2),(2,1)],[(4,0),(4,3),(5,0),(5,3)]]
CASES=[('house',5,HOUSE,F(1,2),HNUM,HORB,30*D),('theta',6,THETA,F(9,10),TNUM,TORB,36*E)]

def orient(edges):return sorted(edges+[(b,a) for a,b in edges])
def graphdata(n,edges):
    arcs=orient(edges);adj=[[] for _ in range(n)]
    for a,b in edges:adj[a].append(b);adj[b].append(a)
    return arcs,adj,{a:i for i,a in enumerate(arcs)}
def rational(z):return F(int(s.numer(z)),int(s.denom(z)))
def fraction_matrix(n,edges,ep,mu):
    arcs,adj,index=graphdata(n,edges);k=len(arcs)
    p=[[F(0) for _ in arcs] for _ in arcs]
    for j,(a,b) in enumerate(arcs):
        for c in adj[b]:p[index[b,c]][j]=(mu if c==a else F(1))/(len(adj[b])-1+mu)
    u=[F(1,n*len(adj[a])) for a,b in arcs]
    assert sum(u)==1 and all(sum(p[i][j] for i in range(k))==1 for j in range(k))
    return arcs,p,u
def project(n,arcs,y):return [sum((z for (a,b),z in zip(arcs,y) if a==v),F(0)) for v in range(n)]
def exact_solve(n,edges,ep,mu):
    arcs,p,u=fraction_matrix(n,edges,ep,mu);k=len(arcs)
    a=[[F(i==j)-ep*p[i][j] for j in range(k)]+[(1-ep)*u[i]] for i in range(k)]
    for j in range(k):
        pivot=next(i for i in range(j,k) if a[i][j]);a[j],a[pivot]=a[pivot],a[j]
        q=a[j][j];a[j]=[v/q for v in a[j]]
        for i in range(k):
            if i!=j and a[i][j]:
                q=a[i][j];a[i]=[v-q*w for v,w in zip(a[i],a[j])]
    y=[row[-1] for row in a];assert sum(y)==1 and min(y)>0
    return project(n,arcs,y)

def main():
    groups=[];cert={};count=0
    for name,n,edges,ep,nums,orbits,den in CASES:
        arcs,adj,index=graphdata(n,edges);k=len(arcs)
        assert min(map(len,adj))>=2
        assert set(sum(orbits,[]))==set(arcs) and sum(map(len,orbits))==k
        masses={edge:num/den for num,orb in zip(nums,orbits) for edge in orb}
        assert all(all(c>0 for c in s.Poly(num,t).all_coeffs()) for num in nums)
        T=s.Matrix(n,k,lambda i,j:int(arcs[j][0]==i))
        S=s.Matrix(k,n,lambda i,j:int(arcs[i][1]==j))
        tau=s.Matrix(k,k,lambda i,j:int(arcs[i]==arcs[j][::-1]))
        p=(S*T-(1-t)*tau).T*s.diag(*[1/(len(adj[b])-1+t) for a,b in arcs])
        u=T.T*s.diag(*[s.Rational(1,len(adj[i])) for i in range(n)])*s.ones(n,1)/n
        y=s.Matrix([masses[edge] for edge in arcs]);eps=s.Rational(ep.numerator,ep.denominator)
        assert all(s.cancel(z)==0 for z in y-eps*p*y-(1-eps)*u)
        assert s.cancel(sum(y)-1)==0
        vertex=[s.factor(z) for z in T*y];cert[name]=vertex;count+=k
    groups.append(dict(name='Source-matrix symbolic stationary certificates',oriented_edges=count,status='passed'))
    roof=cert['house'][4]
    assert s.cancel(roof-2*(12*t**3+115*t**2+346*t+319)/(15*D))==0
    hpoly=9*t**4+84*t**3+206*t**2-76*t-511
    assert s.cancel(s.diff(roof,t)-2*hpoly/(15*D**2))==0
    assert s.Poly(hpoly,t).count_roots(0,s.oo)==1
    assert roof.subs(t,s.Rational(1,2))-roof.subs(t,1)==s.Rational(142,1186125)
    assert roof.subs(t,2)-roof.subs(t,1)==s.Rational(8,445125)
    va,vb,vc=[cert['theta'][i] for i in [0,1,4]]
    assert s.cancel(va-vb-(19*t**2+597*t+4034)/E)==0
    assert s.cancel(vb-vc-(19*t**2+462*t+119)/(4*E))==0
    spread=s.factor(va-vc)
    assert s.cancel(s.diff(spread,t)+855*(t-1)*(19*t+221)/(2*E**2))==0
    assert spread.subs(t,1)-spread.subs(t,s.Rational(1,2))==s.Rational(57,20543092)
    assert spread.subs(t,1)-spread.subs(t,2)==s.Rational(57,6479852)
    groups.append(dict(name='Exact coordinate, spread, derivative and ordering identities',house_positive_critical_points=1,status='passed'))
    samples=sorted(set([F(0),F(1,100),F(1,2),F(1),F(2),F(10),F(100)]+[F(i,7) for i in range(1,22)]))
    count=0
    for name,n,edges,ep,*_ in CASES:
        for mu in samples:
            direct=exact_solve(n,edges,ep,mu)
            expected=[rational(z.subs(t,s.Rational(mu.numerator,mu.denominator))) for z in cert[name]]
            assert direct==expected;count+=1
    groups.append(dict(name='Independent Fraction Gaussian elimination',systems=count,status='passed'))
    intervals={};steps={}
    for name,n,edges,ep,*_ in CASES:
        steps[name]=70 if name=='house' else 300;ivs=[]
        for mu in [F(1,2),F(1),F(2)]:
            arcs,p,u=fraction_matrix(n,edges,ep,mu);k=len(arcs);rho=u[:];partial=[F(0)]*k;factor=1-ep
            for _ in range(steps[name]+1):
                partial=[v+factor*w for v,w in zip(partial,rho)]
                rho=[sum((p[i][j]*rho[j] for j in range(k) if p[i][j]),F(0)) for i in range(k)]
                factor*=ep
            tail=ep**(steps[name]+1);lower=project(n,arcs,partial)
            expected=[rational(z.subs(t,s.Rational(mu.numerator,mu.denominator))) for z in cert[name]]
            assert all(a<=b<=a+tail for a,b in zip(lower,expected))
            if name=='house':ivs.append((lower[4],lower[4]+tail))
            else:ivs.append((lower[0]-lower[4]-tail,lower[0]-lower[4]+tail))
        if name=='house':assert ivs[0][0]>ivs[1][1] and ivs[2][0]>ivs[1][1]
        else:assert ivs[1][0]>ivs[0][1] and ivs[1][0]>ivs[2][1]
        intervals[name]=len(ivs)
    groups.append(dict(name='Independent finite Neumann-series rational enclosures',certified_intervals=intervals,last_series_index=steps,status='passed'))
    record=dict(status='passed',checked_at_utc=datetime.now(timezone.utc).isoformat(),sympy_version=s.__version__,
        arithmetic='Exact integer, polynomial and Fraction arithmetic; no floating point.',groups=groups)
    Path(__file__).with_name('verification-results.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(record,indent=2))
if __name__=='__main__':main()
