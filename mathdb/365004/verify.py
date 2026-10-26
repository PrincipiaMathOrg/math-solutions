"""Exact identities for a full stationary-orthocenter counterexample."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json
import sympy as sp
import mpmath as mp

R=sp.Rational
f,g=R(4,5),R(3,4)
s,p=f+g,f*g
h=R(31,16)
cx,ax2,by2=R(31,20),R(4,25),R(63,1600)
q,r,v,z,lam=sp.symbols('q r v z lam')
groups=[]
pre_cx,pre_ax2=cx/2,ax2/4
norm2=(pre_cx+sp.sqrt(pre_ax2)*v)**2+by2*(1-v**2)
assert sp.factor(norm2-(v**2+496*v+1024)/1600)==0
assert sp.diff(norm2,v).subs(v,-1)>0 and sp.diff(norm2,v,2)>0
assert norm2.subs(v,1)==R(1521,1600)<1
assert 0<f<1 and 0<g<1 and f*g==R(3,5)
assert s==R(31,20) and ax2!=by2 and cx!=0 and h**2!=3
assert (h-cx)**2/ax2<R(1)
groups.append(dict(name='Strict nesting, positive axes, and exclusion of all three configurations',
    status='passed',largest_normalized_radius_squared='1521/1600',
    h_inside_caustic=True))

Bnum=z*(z-f)*(z-g)
Bden=(1-f*z)*(1-g*z)
P=z**3-(s+p*lam)*z**2+(p+s*lam)*z-lam
assert sp.factor(Bnum-lam*Bden-P)==0
pair=q*q-s*(1+r)*q+p*(1+r*r)+(s*s-1-p*p)*r
relation=(r-p)*(1-p*r)-(s-q)*(s*r-q)
assert sp.factor(relation+pair)==0
tangent=1600*q*q-2480*q*(r+1)+897*(r+1)**2+63*(r-1)**2
assert sp.factor(tangent-1600*pair)==0
assert sp.factor(P.subs(lam,1)-(z-1)*(z*z-R(23,20)*z+1))==0
groups.append(dict(name='Blaschke cubic, pair relation, and exact caustic tangency',
                   status='passed',identities=4))

a,b,c=sp.symbols('a b c',nonzero=True)
A,D=R(3,2),R(1,2)
Z=lambda a:A*a+D/a
Zbar=lambda a:A/a+D*a
L=a*b*c
s1=a+b+c
s2=a*b+a*c+b*c
# Twice the Euclidean altitude dot product in complex coordinates.
dot=(h-Z(a))*(Zbar(b)-Zbar(c))+(h-Zbar(a))*(Z(b)-Z(c))
short=(b-c)/L*((D*L-A*a)*h+(A*L-D*a)*h
            -2*A*D*L*a+(A*A+D*D)*s1*a-(A*A+D*D)*s2+2*A*D)
assert sp.factor(dot-short)==0
reduced=((D*lam-A*a)*h+(A*lam-D*a)*h-2*A*D*lam*a
    +(A*A+D*D)*(s+p*lam)*a-(A*A+D*D)*(p+s*lam)+2*A*D)
assert sp.factor(reduced)==0
initial=[sp.Matrix([2,0]),sp.Matrix([R(23,20),3*sp.sqrt(119)/40]),
         sp.Matrix([R(23,20),-3*sp.sqrt(119)/40])]
H=sp.Matrix([h,0])
for i in range(3):
    assert sp.simplify((H-initial[i]).dot(initial[(i+1)%3]-initial[(i+2)%3]))==0
groups.append(dict(name='Exact universal altitude identity and initial triangle',
                   status='passed',orthocenter=['31/16','0'],identities=5))

mp.mp.dps=90
fm,gm=mp.mpf(4)/5,mp.mpf(3)/4
sm,pm=fm+gm,fm*gm
maxres=mp.mpf(0)
cases=0
def note(x):
    global maxres
    maxres=max(maxres,abs(x))
for k in range(48):
    lm=mp.exp(mp.j*(mp.mpf('.123')+2*mp.pi*k/48))
    zs=mp.polyroots([1,-sm-pm*lm,pm+sm*lm,-lm],maxsteps=500)
    zs=sorted(zs,key=mp.arg)
    vs=[mp.mpc(2*mp.re(z),mp.im(z)) for z in zs]
    for zz in zs:note(abs(zz)-1)
    hm=mp.mpc(mp.mpf(31)/16,0)
    cm=mp.mpc(mp.mpf(31)/20,0)
    for i in range(3):
        a0,b0,c0=vs[i],vs[(i+1)%3],vs[(i+2)%3]
        note(mp.re((hm-a0)*mp.conj(b0-c0)))
        edge=b0-a0
        normal=mp.j*edge/abs(edge)
        distance=abs(mp.re((cm-a0)*mp.conj(normal)))
        support=mp.sqrt(mp.mpf(4)/25*mp.re(normal)**2+
                        mp.mpf(63)/1600*mp.im(normal)**2)
        note(distance-support)
        assert mp.im(mp.conj(edge)*(cm-a0))>0
    cases+=1
assert cases==48 and maxres<mp.mpf('1e-75')
groups.append(dict(name='Independent Euclidean numerical check',
    status='passed',configurations=cases,decimal_precision=90,
    largest_residual=mp.nstr(maxres,14),
    checks='Outer incidence, all altitude dot products, caustic support equality, strict interior side.'))
data=dict(status='passed',checked_at_utc=datetime.now(timezone.utc).isoformat(),
          verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          groups=groups,limitation='Finite numerical checks supplement the exact proof; eligibility remains pending the unread identified journal final.')
Path(__file__).with_name('verification-results.json').write_text(
    json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status=data['status'],groups=len(groups),
                      numerical_cases=cases,largest_residual=mp.nstr(maxres,14))))
