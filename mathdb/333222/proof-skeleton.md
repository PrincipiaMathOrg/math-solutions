# MathDB #333222 -- proof skeleton

## Claim

For the expected-duration model intended by Kurushima--Ano, the stopping
advantage `G_n` has an upper-interval nonnegative set.  More strongly, for
`n>=4` it has exactly one zero in `(0,1)`.

## Gate G0 -- reconcile the source formulas

With `n` stages including the present observation, survival for at least
`r+1` stages means at most one of `r` future uniforms exceeds the current
record `x`.  Hence

\[
U_n(x)=\sum_{r=0}^{n-1}\{x^r+r(1-x)x^{r-1}\}
      =2\sum_{r=0}^{n-2}x^r-(n-2)x^{n-1}.
\]

This agrees with the unsimplified probability expression in the 2010 paper.
The printed `-nx^{n-1}` is missing the `+2x^{n-1}` term and gives the
impossible value `U_1=-1`.

Status: closed by direct probability and algebra.

## Gate G1 -- expand the defining integral

Let `H_0=0`.  From

\[
\int_0^1 U_m(y)dy=2H_m-1
\]

and direct coefficient collection in

\[
G_n=U_n-\sum_{k=1}^{n-1}x^{k-1}\int_x^1U_{n-k},
\]

obtain

\[
G_n(x)=\sum_{j=0}^{n-1}
 (3-2H_{n-j-1}+2H_j)x^j-2nx^{n-1}. \tag{G1}
\]

For `j<=n-2`, the terms are: `2` from `U_n`,
`1-2H_{n-j-1}` from the integrals' constant parts, and `2H_j` from the
antiderivative convolution.  At degree `n-1`, the same unified expression
minus `2n` gives `3+2H_{n-1}-2n`.

Status: closed; independently checked by exact polynomial arithmetic.

## Gate G2 -- power-to-Bernstein transform

Put `d=n-1` and

\[
G_n=\sum_{k=0}^d\beta_k {d\choose k}x^k(1-x)^{d-k}.
\]

For a power polynomial `sum c_j x^j`,

\[
\beta_k=\sum_{j=0}^k c_j
          \frac{{k\choose j}}{{d\choose j}}. \tag{B}
\]

For `k<d`, set `r=d-k`.  The required finite-sum identities are

\[
S_0:=\sum_{j=0}^k\frac{{k\choose j}}{{d\choose j}}
    =\frac{d+1}{r+1}, \tag{H1}
\]

\[
S_1:=\sum_{j=0}^k(H_{d-j}-H_j)
             \frac{{k\choose j}}{{d\choose j}}
    =H_r\frac{d+1}{r+1}. \tag{H2}
\]

For (H1), put `j=k-l` and use

\[
\frac{{k\choose j}}{{d\choose j}}
=\frac{{r+l\choose r}}{{d\choose k}},
\qquad
\sum_{l=0}^k{r+l\choose r}={d+1\choose r+1}.
\]

For (H2), the two standard sums after the same substitution are

\[
\sum_{l=0}^k{r+l\choose r}H_{r+l}
 ={d+1\choose r+1}\left(H_{d+1}-\frac1{r+1}\right),
\]

\[
\sum_{l=0}^k{r+l\choose r}H_{k-l}
 ={d+1\choose r+1}(H_{d+1}-H_{r+1}).
\]

Their difference is `{d+1 choose r+1}H_r`.  The first follows by
differentiating the generalized hockey-stick identity; the second follows by
extracting the coefficient of `z^k` in
`-log(1-z)/(1-z)^(r+2)`.

Substitution in (B) gives

\[
\beta_k=\frac{n}{r+1}(3-2H_r),\quad k<d,
\qquad \beta_d=G_n(1)=n. \tag{G2}
\]

Status: closed; checked exactly through `n=200`.

## Gate G3 -- variation argument

Because `H_1=1`, `H_2=3/2`, and `H_r>3/2` for `r>=3`, the Bernstein
coefficient list has, ignoring its single zero, exactly one sign change:

\[
(-,\ldots,-,0,n/2,n).
\]

Under `t=x/(1-x)`, multiplication by the positive factor `(1-x)^d` turns
the Bernstein expansion into a power polynomial in `t` with the same
coefficient signs.  Descartes' rule gives at most one zero in `(0,1)`.

Status: closed.

## Gate G4 -- endpoints and small cases

For `n>=4`, `G_n(0)=3-2H_{n-1}<0` and `G_n(1)=n>0`, so there is exactly
one zero and the sign changes from negative to positive.  Directly,
`G_1=1`, `G_2=1+x`, and `G_3=3x`.

Status: closed.

## Audit state

- Exact verifier: passed for all `1<=n<=200`.
- Primary-source reconciliation: complete.
- Current-literature search: recorded separately.
- Independent hostile proof audit: passed.
