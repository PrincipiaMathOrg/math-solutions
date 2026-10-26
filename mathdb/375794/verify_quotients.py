from fractions import Fraction as F
from pathlib import Path
import json
import sympy as s

x,t=s.symbols("x t")
U6=2/x**2-2/x**4+s.Rational(14,3)/x**6
L8=U6-s.Rational(62,3)/x**8
U10=L8+s.Rational(762,5)/x**10
L12=U10-s.Rational(5110,3)/x**12
checks=[]

def positive(label,expr,shift=0):
    num,den=s.fraction(s.cancel(expr))
    a=s.Poly(num.subs(x,t+shift),t).all_coeffs()
    b=s.Poly(den.subs(x,t+shift),t).all_coeffs()
    ok=all(c>=0 for c in a+b) and a[-1]>0 and b[-1]>0
    if shift==0:
        ok=all(c>=0 for c in a+b) and any(c>0 for c in a) and any(c>0 for c in b)
    assert ok,(label,num,den,a,b)
    checks.append(dict(label=label,numerator=str(s.factor(num)),denominator=str(s.factor(den)),
                       shift=shift,shifted_numerator=[str(c) for c in a],
                       shifted_denominator=[str(c) for c in b],passed=True))
    print(label,s.factor(num),s.factor(den))

for name,f,sign in [("U6",U6,1),("L8",L8,-1),("U10",U10,1),("L12",L12,-1)]:
    positive("signed defect "+name,sign*(f-f.subs(x,x+2)-8/(x+1)**3))
positive("lower R for a2",L8-2/(x+1/(2*x))**2,3)
positive("upper R for a2",2/(x+1/(2*x+1))**2-U6,5)
u_lo=x+6*x/(12*x*x+19)
u_hi=x+(6*x*x+19)/(x*(12*x*x+57))
positive("lower x3",2/u_lo**2-U10,5)
positive("upper x3",L8-2/u_hi**2,39)
positive("improved upper x3",L12-2/u_hi**2,5)
for q in range(5,19,2):
    v=F(6*q,19)
    assert v+F(1,q)<v.numerator//v.denominator+1
    checks.append(dict(label=f"floor gap Q={q}",polynomial_part=str(v),
                       upper_correction=str(F(1,q)),
                       gap=str(v.numerator//v.denominator+1-v-F(1,q)),passed=True))

J=50
q=2*J+1
lo=F(str(L8.subs(x,q)))
hi=min(F(str(U6.subs(x,q))),F(str(U10.subs(x,q))))
small_upper=sum((F(1,j**3) for j in range(2,21)),F(0))+F(1,800)
assert small_upper<F(1011,5000)<F(49,242)
checks.append(dict(label="elementary N=1 upper bound",tail_endpoint=20,
                   rational_upper=str(small_upper),intermediate_upper="1011/5000",
                   first_two_threshold="49/242",passed=True))
for n in range(1,19):
    q=2*n+1
    tail=sum((F(1,j**3) for j in range(n+1,J+1)),F(0))
    rlo,rhi=tail+lo,tail+hi
    lower2=F(2)/(q+F(1,2*q))**2
    upper2=F(2)/(q+F(1,2*q+1))**2
    assert lower2<rlo<rhi<upper2,(n,"first two")
    m=(6*q)//19 if n>=2 else 1
    # x3 is increasing in delta and decreasing in R.
    u_m=q+F(m,1+2*q*m)
    u_next=q+F(m+1,1+2*q*(m+1))
    assert F(2)/u_next**2<rlo<rhi<F(2)/u_m**2,(n,m,"third")
    checks.append(dict(label=f"finite N={n}",Q=q,first_three=[q,2*q,m],
                       tail_endpoint=J,R_lower=str(rlo),R_upper=str(rhi),
                       comparisons=dict(a2_lower_gap=str(rlo-lower2),
                                        a2_upper_gap=str(upper2-rhi),
                                        a3_lower_R_gap=str(rlo-F(2)/u_next**2),
                                        a3_upper_R_gap=str(F(2)/u_m**2-rhi)),
                       passed=True))
print("FINITE",[(r["Q"],r["first_three"]) for r in checks if "Q" in r])

y=s.symbols("y")
R=2*y**2-2*y**4+s.Rational(14,3)*y**6-s.Rational(62,3)*y**8+s.Rational(762,5)*y**10
u=s.series(s.sqrt(2/R),y,0,8)
delta=u.removeO()-1/y
a2=s.series(1/delta,y,0,6)
x3=s.series(1/(a2.removeO()-2/y),y,0,4)
assert s.expand(u.removeO()).coeff(y,3)==-s.Rational(19,24)
assert s.expand(x3.removeO()).coeff(y,-1)==s.Rational(6,19)
assert s.expand(x3.removeO()).coeff(y,1)==s.Rational(713,722)
checks.append(dict(label="formal leading terms",u=str(u),second_complete=str(a2),third_complete=str(x3),passed=True))
result=dict(all_passed=True,check_count=len(checks),checks=checks,
            scope="Exact algebra and rational interval certificates; global proofs are in solution.tex.")
Path(__file__).with_name("exact-certificate.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8",newline="\n")
print("PASSED",len(checks))
