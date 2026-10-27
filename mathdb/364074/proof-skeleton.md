# MathDB #364074 -- proof skeleton

## Claim

For every `n>=8`,

\[
u(0,n)-u(1,n)\geq N(0,n)/2.
\]

## Gate G0 -- correct the extracted notation

The primary source uses lowercase `u(0,n)`.  MathDB's initial `\nu(0,n)` is
an extraction typo.  Corollary 4.2 of the source implies

\[
u(0,n)+u(1,n)=(p(n)+N(0,n))/2.
\]

Therefore the conjecture is equivalent to `E_n=p(n)-4u(1,n)>=0`.

Status: closed from the primary source.

## Gate G1 -- exact kernel

The fixed-rank generating function gives

\[
(q;q)_\infty U_1(q)=
\sum_{r\geq2}(-1)^r\sum_{j=0}^{r-2}q^{T_r+jr}.
\]

After adjoining the two Euler-pentagonal endpoints,

\[
E_n=[q^n]P(q)H(q)\quad(n\geq1),
\]

where, for `q=e^-z`,

\[
H(e^{-z})=1-4\sum_{a,b\geq0}(-1)^{a+b}e^{-zQ(a,b)}
\]

and `Q(a,b)=3a^2/2+2ab+b^2/2+(a+b)/2`.

Status: closed by exact reindexing; checked coefficientwise by the verifier.

## Gate G2 -- uniform local expansion

For `x0=2pi/sqrt(239999)` and `rho=sqrt(2)x0`, prove

\[
|H(e^{-z})-(3/16)z^2|<0.041(3/16)|z|^2
\]

on `|arg z|<=pi/4`, `|z|<=rho`.

Apply the order-16 Euler--Boole formula in both lattice variables after the
scaling `z=h^2 omega`.  Construct every derivative polynomial over
`Fraction`, bound it by separated Gaussian moments, and enclose the moments
with 220-bit Arb balls.  The exact local coefficients begin

\[
3z^2/16+3z^3/8+227z^4/256+41z^5/16+\cdots.
\]

The certified relative error is `0.040807231164...`.
After division by the leading `h^4`, every retained tail and remainder bound
is increasing in `h`; hence the endpoint `h=sqrt(rho)` controls the entire
sector, including arbitrarily small `|z|`.

Status: closed by `verify_conjecture.py`; the interval computation passed.

## Gate G3 -- positive major arc

Set `A=pi^2/6`, `N=n-1/24`, and `x=sqrt(A/N)`.  Dedekind inversion and
`y=x^(3/2)s` reduce the leading normalized integral to amplitude

\[
(1+xs^2)^{5/4}e^{-As^2/(1+xs^2)}
\]

and phase

\[
A\sqrt{x}s^3/(1+xs^2)+(5/2)\arctan(\sqrt{x}s).
\]

The interval `0<=s<=1` contributes more than `0.172`; the contribution
through `s=3/2` stays nonnegative; the remaining absolute tail is below
`0.0175`; and the absolute half-integral is below `1.022`.  Including the
local relative error gives a normalized full integral above `0.22`.

The eta-product residual is below `3e^-1539` and is absorbed before rounding
the combined relative error to `0.041`.

Status: closed by elementary inequalities and Arb endpoint checks.

## Gate G4 -- exponentially smaller minor arc

Retaining the first logarithmic layer of the Euler product yields

\[
\log P(e^{-x})-\log|P(e^{-x-iy})|>0.49/x
\]

for `x<=|y|<=pi` and `x<=x0`.  Also

\[
|H(e^{-x-iy})|<5.174/x.
\]

Relative to the major lower bound, the minor arc is at most

\[
\frac{2\pi\,5.174}{(3/16)0.22}
x^{-9/2}e^{-0.49/x}<7\cdot10^{-6}.
\]

Status: closed; monotonicity and the endpoint inequality are interval
certified.

## Gate G5 -- finite range

Euler's pentagonal theorem turns `(q;q)_infinity E=K` into an exact integer
recurrence.  Exhaustive evaluation gives `E_n>=0` for `8<=n<=10000`, with
equality only at `n=11`.

Status: closed by exact integer arithmetic.

## Audit state

- Primary-source and current-status audit: complete.
- Exact finite verifier: passed.
- Arb analytic certificate: passed at 220-bit precision.
- Independent hostile proof audit: complete.  The auditor reran verifier SHA
  `cf20d5f69b8db8896d36be5d13d2626a54bbd457aad50f9ea16709de9e679241`
  with python-flint/Arb and independently checked every generating-function,
  Euler--Boole, eta, major/minor, and range-overlap step.
