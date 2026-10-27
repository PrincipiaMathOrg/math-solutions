# Literature and status audit for MathDB #372212

Checked through: 2026-08-18.

## Primary formulation

Ho Yun, *Spectral Shrinkage of Gaussian Entropic Optimal Transport*,
arXiv:2512.19457v2, states Conjecture 3.1 (Universal Bounds) for
positive-definite covariance matrices `A,B` on `R^d`:

\[
\limsup_{\varepsilon\downarrow0}
\frac{\mathcal W_2^2(\pi_\varepsilon,\pi_0)}{\varepsilon}
\le C_d
\]

for a constant depending only on the dimension.  The source notes that the
case `A=B` forces `C_d>=d/2` and explicitly asks whether this identity case is
the worst case.

- Abstract and submission history: https://arxiv.org/abs/2512.19457
- Current full text: https://arxiv.org/html/2512.19457v2
- Exact statement: Conjecture 3.1 in Section 3.3
- Exact distance formula used here: Theorem 3.10 in Section 3.3

The submission history contains v1 (22 December 2025) and v2 (26 May 2026),
with no v3 or journal reference as of the audit date.  MathDB's mathematical
statement is faithful to v2.  Its strings `\mathbfboldsymbol` and `\rhd 0`
are rendering defects; the source hypotheses are `\mathbf A,\mathbf B\succ0`.

## Source ingredients used by the proof

For properly aligned Green operators `G,M`, the source defines

\[
R_\varepsilon=f_\varepsilon(G^*M),\qquad
f_\varepsilon(t)=
\frac{2t}{\sqrt{4t^2+\varepsilon^2}+\varepsilon}.
\]

Theorem 3.10 expresses the squared Wasserstein distance exactly as a trace of
the square root of a matrix `Q_epsilon` on the marginal space.  The proof in
this directory differentiates that formula at zero.  No asymptotic estimate
or numerical pattern from the source is assumed.

## Current-status search

Exact-title, arXiv-identifier, exact-phrase, author/topic, and forward-record
searches located no later proof or counterexample.  The exact-title and
identifier searches return only arXiv:2512.19457v2; the broader Gaussian-EOT
searches return the source and earlier background work but no resolution.

The OpenAlex record
https://openalex.org/W7117147915 was last updated 28 July 2026 and reports zero
citations.  The DataCite record
https://api.datacite.org/dois/10.48550/arxiv.2512.19457 reports version 2 and
no related identifiers.  Crossref has no record; Semantic Scholar was rate
limited and is not used as evidence.

This is necessarily a search report rather than proof that no unpublished or
unindexed argument exists.  The defensible conclusion is: **no indexed later
resolution was located through 2026-08-18; arXiv v2 still labels the statement
Conjecture 3.1.**
