# A counterexample to the pointwise Barbashin criterion

## Result

The conjecture in Section 7 of Popa--Ceaușu--Megan, *On exponential
stability for linear discrete-time systems in Banach spaces*, is false for
general Banach spaces.

The source considers a sequence `A(n)` of bounded operators and defines

\[
A_m^k=A(m)\cdots A(k+1)\quad(k<m),\qquad A_m^m=I.
\]

It asks whether the existence of `B≥1` such that

\[
\tag{1}
\sum_{k=0}^{m}\lVert A_m^k x\rVert\le B\lVert x\rVert
\]

for every `m` and `x` forces uniform exponential stability.

## Counterexample

Take `X=ℓ¹(ℕ₀)` with unit vectors `e_0,e_1,…`. Put `A(0)=0`, and for
`n≥1` define

\[
A(n)x=x_{n-1}e_n.
\]

These are bounded rank-one operators of norm one.

For `0≤k<m`,

\[
\tag{2}
A_m^k x=x_ke_m.
\]

Indeed, `A(k+1)` first maps `x` to `x_ke_{k+1}`, and every subsequent
factor moves that same coefficient forward by one coordinate. Since
`A_m^m=I`, equation (2) gives

\[
\begin{aligned}
\sum_{k=0}^{m}\lVert A_m^k x\rVert_1
&=\lVert x\rVert_1+\sum_{k=0}^{m-1}|x_k|\\
&\le 2\lVert x\rVert_1.
\end{aligned}
\]

Thus (1) holds with `B=2`.

On the other hand, for every `k<m`,

\[
A_m^ke_k=e_m,
\]

so `‖A_m^k‖=1`. If the system were uniformly exponentially stable, there
would be constants `N≥1` and `α>0` satisfying

\[
1=\lVert A_m^ke_k\rVert_1
\le Ne^{-\alpha(m-k)}
\]

for all `m>k`. Letting `m-k→∞` is a contradiction. Therefore (1) does not
imply uniform exponential stability. ∎

## Robustness

The proof skeleton records a weighted bilateral-shift variant on `ℓ¹(ℤ)` in
which every generator is invertible, `‖A(n)‖=1`, and the inverses are uniformly
bounded. Hence noninvertibility is not the underlying obstruction.

The obstruction is instead the order of a supremum and a sum. Condition (1)
bounds

\[
\sup_{\lVert x\rVert=1}\sum_k\lVert A_m^kx\rVert,
\]

whereas the known operator-norm criterion controls

\[
\sum_k\sup_{\lVert x\rVert=1}\lVert A_m^kx\rVert.
\]

On `ℓ¹`, different products can read disjoint coordinates of the same vector,
so the first quantity stays bounded while every individual operator norm is
one.

## Verification record

- Primary statement: https://arxiv.org/html/1305.2036#S7
- Published source: https://doi.org/10.1016/j.camwa.2012.01.027
- MathDB record: https://mathdb.com/p/381167
- Exact finite-truncation checks: `verify_counterexample.py`
- Detailed dependency and scope audit: `proof-skeleton.md`

No indexed published resolution of the exact conjecture was located in a
forward-citation and erratum/correction audit through 2026-08-18. This is a
mathematical proof of refutation, not yet a claim of external peer review or
publication.

