# A Bernstein-basis proof of the stopping-region monotonicity

## Source correction

There are two typographical indexing errors in the source formulas.  They can
be resolved from the probability model itself.

If there are `n` stages to go, including the present record of value `x`, its
rank remains at most two at stage `r+1` precisely when at most one of the first
`r` future observations exceeds `x`.  Consequently

\[
\begin{aligned}
U_n(x)
 &=\sum_{r=0}^{n-1}\bigl(x^r+r(1-x)x^{r-1}\bigr)\\
 &=2\sum_{r=0}^{n-2}x^r-(n-2)x^{n-1}. \tag{1}
\end{aligned}
\]

The summand with `r=0` in the first line is interpreted as `1`.  In
particular, `U_1=1` and `U_2=2`.  Kurushima--Ano's preceding probability sum
is exactly the first line of (1), but both that paper and the later survey
print `-n x^{n-1}` in the simplified formula.  That cannot be correct: it
would give `U_1=-1`, and direct simplification of the preceding line gives
`-(n-2)x^{n-1}`.

We use the definition

\[
G_n(x)=U_n(x)-\sum_{k=1}^{n-1}x^{k-1}
                 \int_x^1U_{n-k}(y)\,dy. \tag{2}
\]

This is the expected advantage of stopping over one-stage look-ahead.

## Power coefficients

Let `H_m=1+1/2+...+1/m`, with `H_0=0`.  Since

\[
\int_0^1U_m(y)\,dy=2H_m-1,
\]

expanding (2) gives

\[
\boxed{
G_n(x)=\sum_{j=0}^{n-1}
 \bigl(3-2H_{n-j-1}+2H_j\bigr)x^j-2n x^{n-1}.} \tag{3}
\]

This is also the coefficient representation in Kurushima--Ano.  Equivalently,
the fully expanded formula is

\[
\begin{aligned}
G_n(x)={}&3\sum_{k=1}^{n}x^{k-1}-2nx^{n-1}
-2\sum_{k=1}^{n-1}H_{n-k}x^{k-1}
+2\sum_{k=1}^{n-1}H_kx^k. \tag{4}
\end{aligned}
\]

The displayed threshold equation in both sources has `H_{n-k-1}` where (4)
requires `H_{n-k}`.  Formula (3), the probability calculation, and the
defining integral all agree with (4).

## Bernstein coefficients

Put `d=n-1` and write `G_n` in the degree-`d` Bernstein basis:

\[
G_n(x)=\sum_{k=0}^{d}\beta_k {d\choose k}x^k(1-x)^{d-k}. \tag{5}
\]

For `k<d`, put `r=d-k`.  Then

\[
\boxed{\displaystyle
\beta_k=\frac{n}{r+1}\bigl(3-2H_r\bigr),\qquad
\beta_d=n.} \tag{6}
\]

To verify (6), if `c_j=3-2H_{d-j}+2H_j` denotes the power coefficient
before the final correction, the power-to-Bernstein conversion is

\[
\beta_k=\sum_{j=0}^{k}c_j
          \frac{{k\choose j}}{{d\choose j}}.
\]

The two elementary identities

\[
\sum_{j=0}^{k}\frac{{k\choose j}}{{d\choose j}}
 =\frac{d+1}{r+1},
\]

and

\[
\sum_{j=0}^{k}(H_{d-j}-H_j)
          \frac{{k\choose j}}{{d\choose j}}
 =H_r\frac{d+1}{r+1}
\]

give the first part of (6).  They follow on putting `j=k-l` from the
hockey-stick identity and its harmonic convolution.  Finally,
`beta_d=G_n(1)=U_n(1)=n`.

## One sign change

For `r>=3`, `H_r>3/2`, while `H_2=3/2` and `H_1=1`.  Thus, in increasing
order of `k`, the nonzero Bernstein coefficients consist of

- negative coefficients through `k=d-3`;
- `beta_{d-2}=0`;
- `beta_{d-1}=n/2>0` and `beta_d=n>0`.

There is exactly one sign variation when `n>=4`.  Set
`t=x/(1-x)`.  For `0<x<1`, equation (5) becomes

\[
G_n(x)=(1-x)^d
 \sum_{k=0}^{d}\beta_k {d\choose k}t^k. \tag{7}
\]

The polynomial in `t` has one coefficient sign change, so Descartes' rule of
signs gives at most one root in `(0,infinity)`, hence `G_n` has at most one
root in `(0,1)`.

For `n>=4`,

\[
G_n(0)=3-2H_{n-1}<0,
\qquad G_n(1)=n>0.
\]

Therefore `G_n` has exactly one root `s_n` in `(0,1)`, is negative before
`s_n`, and positive after it.  The small cases are

\[
G_1(x)=1,\qquad G_2(x)=1+x,\qquad G_3(x)=3x.
\]

It follows for every `n` and every `0<=x<=y<=1` that

\[
G_n(x)\geq0\quad\Longrightarrow\quad G_n(y)\geq0.
\]

This proves the monotonicity assertion in MathDB #333222 and establishes the
threshold form of the one-stage-look-ahead stopping region for the intended
expected-duration model.

## Verification record

- Kurushima--Ano primary PDF:
  https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1682-07.pdf
- 2016 survey: https://arxiv.org/html/1605.08364
- MathDB: https://mathdb.com/p/333222
- Exact coefficient checks: `verify_bernstein.py`
- Dependency and source audit: `proof-skeleton.md`

No indexed published resolution of this exact monotonicity assertion was
located through 2026-08-18.  This is an internally verified proof, not yet a
claim of external peer review or publication.
