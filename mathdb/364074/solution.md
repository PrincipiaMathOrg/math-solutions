# An effective circle-method proof of the rank-difference conjecture

## Statement and first reduction

Let `p(n)` be the partition function, let `N(0,n)` count partitions of `n`
with Dyson rank zero, and let `u(m,n)` count strongly unimodal sequences of
weight `n` and rank `m`.  We prove that

\[
u(0,n)-u(1,n)\geq \frac{N(0,n)}2\qquad(n\geq 8).       \tag{1}
\]

The source proves

\[
u(0,n)+u(1,n)=\frac{p(n)+N(0,n)}2.                     \tag{2}
\]

Consequently (1) is equivalent to

\[
E_n:=p(n)-4u(1,n)\geq0.                                \tag{3}
\]

We establish (3) exactly for `8 <= n <= 10000` and analytically for every
`n >= 10000`.  The overlap is deliberate.

## The exact false-theta kernel

Put

\[
P(q)=\frac1{(q;q)_\infty}=\sum_{n\geq0}p(n)q^n,
\qquad
U_1(q)=\sum_{n\geq0}u(1,n)q^n.
\]

The fixed-rank generating function of Bringmann--Jennings-Shaffer--Mahlburg--
Rhoades, specialized at rank one, gives

\[
(q;q)_\infty U_1(q)
=\sum_{r\geq2}(-1)^r\sum_{j=0}^{r-2}q^{T_r+jr},
\qquad T_r=\frac{r(r+1)}2.                              \tag{4}
\]

Thus, if `E(q)=sum E_n q^n`, then

\[
E(q)=P(q)K(q),
\quad
K(q)=1+4\sum_{r\geq2}(-1)^{r+1}
                    \sum_{j=0}^{r-2}q^{T_r+jr}.        \tag{5}
\]

Euler's pentagonal theorem supplies the two omitted endpoints `j=r-1,r`.
It follows that

\[
K(q)=4(q;q)_\infty+H(q),                               \tag{6}
\]

where

\[
H(q)=-3+4\sum_{r\geq1}(-1)^{r+1}
                    \sum_{j=0}^{r}q^{T_r+jr}.          \tag{7}
\]

Writing `r=a+b` and `j=a` in (7), and putting `q=e^{-z}`, gives

\[
H(e^{-z})=1-4\Theta(z),                                \tag{8}
\]

\[
\Theta(z)=\sum_{a,b\geq0}(-1)^{a+b}e^{-zQ(a,b)},
\quad
Q(a,b)=\frac32a^2+2ab+\frac12b^2+\frac{a+b}{2}.       \tag{9}
\]

Since `P(q)(q;q)_infinity=1`, equations (5)--(6) imply, for every `n>=1`,

\[
E_n=[q^n]P(q)H(q).                                     \tag{10}
\]

## A certified local estimate

Set

\[
x_0=\frac{2\pi}{\sqrt{239999}}
=0.01282552502149\ldots,
\qquad \rho=\sqrt2\,x_0.
\]

The central effective estimate is

\[
\boxed{
\left|H(e^{-z})-\frac3{16}z^2\right|
<0.041\frac3{16}|z|^2
}                                                       \tag{11}
\]

whenever `|arg z|<=pi/4` and `|z|<=rho`.

Here is a reproducible proof of (11).  Write `z=h^2 omega`, where `h` is
real and positive and `|omega|=1`, and set

\[
f(X,Y)=\exp\!\left[-\omega\left(
 \frac32X^2+2XY+\frac12Y^2+\frac h2(X+Y)\right)\right].
\]

Then `Theta(z)=sum_{a,b>=0}(-1)^(a+b)f(ha,hb)`.  Apply the
order-16 Euler--Boole formula in each variable:

\[
\sum_{m\geq0}(-1)^m f(mh)
=\sum_{d\in D}c_dh^df^{(d)}(0)+R_{16},                 \tag{12}
\]

where

\[
D=\{0,1,3,5,\ldots,15\},\quad c_0=\frac12,
\quad
c_{2k-1}=-\frac{(4^k-1)B_{2k}}{(2k)!},                 \tag{13}
\]

and the Fourier series of the periodic Euler function gives

\[
|R_{16}|\leq \frac4{\pi^{16}}h^{15}
                  \int_0^\infty |f^{(16)}(t)|\,dt.    \tag{14}
\]

The double remainder is the sum of the `R_x L_y`, `L_x R_y`, and
`R_x R_y` terms.  On the sector in (11),

\[
|f(X,Y)|\leq
\exp\!\left(-\frac{3X^2}{2\sqrt2}
             -\frac{Y^2}{2\sqrt2}\right).             \tag{15}
\]

Every derivative is `f` times a polynomial in `X,Y,h,omega`.  The verifier
constructs these polynomials over the exact rationals and integrates the
absolute value of each monomial in (15) using

\[
\int_0^\infty t^j e^{-ct^2}\,dt
=\frac{\Gamma((j+1)/2)}{2c^{(j+1)/2}}.                 \tag{16}
\]

The finite boundary operator in (12) gives, exactly,

\[
H(e^{-z})=\frac3{16}z^2+\frac38z^3
+\frac{227}{256}z^4+\frac{41}{16}z^5
+\frac{181499}{20480}z^6+\cdots+R.                    \tag{17}
\]

At `|z|=rho`, 220-bit Arb ball arithmetic certifies

\[
\begin{array}{rcl}
|R_xL_y|&<&4.357\cdot10^{-8},\\
|L_xR_y|&<&1.760\cdot10^{-11},\\
|R_xR_y|&<&9.583\cdot10^{-10},\\
4|R|&<&1.79\cdot10^{-7},\\
\left|\text{terms of (17) of degree at least 3}\right|
 &<&2.34\cdot10^{-6}.
\end{array}                                             \tag{18}
\]

The leading term is greater than `6.168e-5`, and the certified ratio of the
last two error bounds to it is

\[
0.040807231164\ldots<0.041.                             \tag{19}
\]

This endpoint calculation is uniform on the whole disk.  If `h_0=sqrt(rho)`,
then every polynomial-tail ratio after division by the leading `h^4` gains
at least `(h/h_0)^2`; the one-variable remainders gain at least
`(h/h_0)^11`, and the double remainder gains at least `(h/h_0)^26`.
Consequently the relative bound is maximal at `h=h_0`.

All polynomial coefficients used here are exact fractions; Arb encloses
only the transcendental quantities and Gaussian moments.  Thus (18)--(19)
are interval proofs, not floating-point samples.

## The major arc

Let

\[
A=\frac{\pi^2}{6},\qquad N=n-\frac1{24},
\qquad x=\sqrt{\frac A N}.
\]

For `n>=10000`, `x<=x_0`.  Cauchy's formula applied to (10), with
`z=x+iy`, is

\[
E_n=\frac1{2\pi}\int_{-\pi}^{\pi}
 P(e^{-z})H(e^{-z})e^{nz}\,dy.                          \tag{20}
\]

Dedekind eta inversion gives exactly

\[
P(e^{-z})=\sqrt{\frac z{2\pi}}
 e^{A/z-z/24}
 \prod_{m\geq1}(1-e^{-4\pi^2m/z})^{-1}.                \tag{21}
\]

On the major arc `|y|<=x`, the product in (21) differs from one by less than
`3e^{-1539}`: indeed `Re(1/z)>=1/(2x)` and
`2pi^2/x_0>1539`.  Combined with the sharper value in (19), this leaves the
relative error strictly below `0.041`.

Put `y=x^(3/2)s`.  After extracting the leading term in (11), the major-arc
integral is

\[
\frac{3x^4e^{2A/x}}{16\,2\pi\sqrt{2\pi}}J,             \tag{22}
\]

where the unperturbed normalized amplitude and phase are

\[
W_x(s)=(1+xs^2)^{5/4}
       \exp\!\left(-\frac{As^2}{1+xs^2}\right),        \tag{23}
\]

\[
\Phi_x(s)=\frac{A\sqrt{x}\,s^3}{1+xs^2}
           +\frac52\arctan(\sqrt{x}s).                 \tag{24}
\]

The following elementary bounds hold uniformly for `0<x<=x_0`.

- On `0<=s<=1`, `Phi_x(s)<0.47`, so this part of the half-integral is
  greater than `e^{-A}cos(0.47)>0.172`.
- The phase is still below `pi/2` through `s=3/2`, so the interval from
  `1` to `3/2` contributes nonnegatively.
- For `3/2<=s<=1/(2sqrt(x))`, use
  `W_x(s)<=(5/4)^(5/4)exp(-4As^2/5)`.  For the remaining interval use
  `W_x(s)<=2^(5/4)exp(-A/(5x))`.  Their total is below `0.0175`.
- The corresponding absolute half-integral is below `1.022`.

Allowing the relative error in (11) and (21), symmetry therefore gives

\[
J>2(0.172-0.0175-0.041\cdot1.022)>0.22.                \tag{25}
\]

In particular the major arc is positive and exceeds

\[
M_n:=\frac{(3/16)\,0.22}{2\pi\sqrt{2\pi}}
             x^4e^{2A/x}.                              \tag{26}
\]

## The minor arc

For `a=e^{-x}` and `x<=|y|<=pi`, the Euler product gives

\[
\log P(e^{-x})-\log|P(e^{-x-iy})|
\geq\sum_{m\geq1}a^m(1-\cos(my)).                     \tag{27}
\]

Keeping this whole geometric sum yields

\[
\frac{a(1+a)(1-\cos y)}
 {(1-a)((1-a)^2+2a(1-\cos y))}.                        \tag{28}
\]

It is increasing in `1-cos y`.  The elementary estimates
`a>=1-x`, `1-a<=x`, and
`x^2/2-x^4/24<=1-cos x<=x^2/2` show that (28) is greater than

\[
\frac{(1-x_0)(2-x_0)(1/2-x_0^2/24)}{2x}
>\frac{0.49}{x}.                                       \tag{29}
\]

From (7), `T_r>=r^2/2`, and elementary integral comparison,

\[
|H(e^{-x-iy})|
\leq3+\frac4x+8\sqrt{\frac{\pi}{2x}}
<\frac{5.174}{x}.                                      \tag{30}
\]

The real version of (21), (27), and (29)--(30), divided by the major lower
bound (26), gives

\[
\frac{|\text{minor arc}|}{M_n}
<\frac{2\pi\,5.174}{(3/16)\,0.22}
 x^{-9/2}e^{-0.49/x}.                                  \tag{31}
\]

The right side increases on `0<x<=x_0` and its Arb-certified endpoint value
is

\[
6.576516\cdot10^{-6}<7\cdot10^{-6}.                   \tag{32}
\]

The exponentially tiny eta-product residual in the real form of (21) is
also included in this outward rounding.  Equations (25) and (32) prove

\[
E_n>0\qquad(n\geq10000).                               \tag{33}
\]

## Exact finite range

Equation (5) and Euler's pentagonal theorem give an integer recurrence.  If
`k_n=[q^n]K(q)` and `E_j=0` for `j<0`, then

\[
E_n=k_n-\sum_{r\geq1}(-1)^r
 \left(E_{n-r(3r-1)/2}+E_{n-r(3r+1)/2}\right).         \tag{34}
\]

The attached verifier evaluates (34) with Python integers for every
`n<=10000`.  It finds

\[
E_n\geq0\quad(8\leq n\leq10000),
\qquad E_n=0\text{ only for }n=11.                     \tag{35}
\]

Combining (33) and (35) proves (3), hence (1), for every `n>=8`.  Moreover,
equality in (1) occurs only at `n=11`.

## Verification record

- Primary source: https://arxiv.org/html/2407.18186v1
- Fixed-rank generating function and Wright framework:
  https://arxiv.org/abs/1806.03217
- Euler--Boole formula and remainder: https://dlmf.nist.gov/24.17
- Exact/Arb certificate: `verify_conjecture.py`
- Recorded output: `verification.out`
- Dependency/status audit: `proof-skeleton.md` and `literature-audit.md`

The certificate was run with `python-flint 0.9.0`, Arb precision 220 bits,
one thread, and no array library.  It completed in 20.3 seconds with a traced
Python allocation peak of 26.3 MiB.  Run it with ordinary Python, not
`python -O`, because its certified comparisons are expressed as assertions.
