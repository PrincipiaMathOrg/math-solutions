# MathDB #372212 -- proof skeleton

## Claim

For all positive-definite covariance matrices `A,B` on `R^d`,

\[
\lim_{\varepsilon\downarrow0}
\frac{\mathcal W_2^2(\pi_\varepsilon,\pi_0)}{\varepsilon}
\le d/2.
\]

The sharp constant is `C_d=d/2`, and equality occurs exactly for `A=B`.

## Gate G0 -- source formula and hypotheses

In finite dimension, positive definiteness makes reachability automatic and
the properly aligned Green operators `G,M` invertible.  With

\[
X=G^*G,\quad Y=M^*M,\quad C=G^*M=M^*G\succ0,
\]

Theorem 3.10 of the source reads

\[
W_2^2=2\operatorname{tr}(X+Y-\sqrt{Q_\varepsilon}),
\quad
Q_\varepsilon=X^2+Y^2+XR_\varepsilon Y+YR_\varepsilon X.
\]

Status: checked against arXiv:2512.19457v2.  The equality
`tr(A+B)=tr(X+Y)` accounts for the source's marginal-space notation.

## Gate G1 -- first-order collapse

Functional calculus gives

\[
R_\varepsilon=I-(\varepsilon/2)C^{-1}+O(\varepsilon^2).
\]

Since `M=G^{-*}C`,

\[
Y=CX^{-1}C,\qquad XC^{-1}Y=YC^{-1}X=C.
\]

Consequently, for `S=X+Y`,

\[
Q_\varepsilon=S^2-\varepsilon C+O(\varepsilon^2).
\]

Status: closed by direct matrix algebra.

## Gate G2 -- trace-square-root derivative

Since `S^2` is positive definite, the principal square root is Frechet
differentiable near it.  If `sqrt(S^2+tH)=S+tZ+O(t^2)`, then `SZ+ZS=H`.
Multiplying by
`S^{-1}` and taking traces gives

\[
\operatorname{tr}Z=\tfrac12\operatorname{tr}(S^{-1}H).
\]

It follows that the limit exists and equals

\[
L(A,B)=\operatorname{tr}(S^{-1}C).
\]

Status: closed; no commutativity between `S` and `C` is assumed.

## Gate G3 -- dimension-only bound

Proper alignment gives

\[
S-2C=(G-M)^*(G-M)\succeq0.
\]

Hence `S^{-1/2}CS^{-1/2} <= I/2`, and

\[
L(A,B)=\operatorname{tr}(S^{-1/2}CS^{-1/2})\le d/2.
\]

Trace equality forces `S=2C`, then `G=M`, then `A=B`.  Conversely `A=B`
gives `L=d/2`.

Status: closed, including sharpness and equality.

## Audit state

- Primary-source version, formulation, and entropy normalization: checked
  against arXiv:2512.19457v2.
- Exact-title, phrase, author/topic, and forward-record status search: complete;
  no indexed later resolution located through 2026-08-18.
- Deterministic aligned-root and finite-`epsilon` checks: passed.  Verifier
  SHA-256: `f32d2bee86162547ee7e3947f4eff18d3443cb0e03058aecf8b6e8ce7540436c`.
- Independent hostile proof audit: complete.  The auditor independently
  rederived Theorem 3.10 from the block covariance, checked reachability,
  every noncommutative identity, the trace derivative, normalization, and
  the equality case, and found no gap.
