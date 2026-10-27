# Literature and status audit for MathDB #333222

Checked through: 2026-08-18.

## Primary formulation

Aiko Kurushima and Katsunori Ano, *Full-information duration problem and its
generalizations*, RIMS Kokyuroku 1682 (2010), 50--54, formulate the
one-stage-look-ahead region and explicitly leave its monotonicity in the
observed record value unsolved.

- Volume contents: https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/1682.html
- Primary PDF: https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1682-07.pdf

Section 3, pp. 51--53, gives the probability expression for `U_n`, defines
`G_n`, proves the time-index implication, and says that
`G_n(x)>=0 => G_n(y)>=0` for `y>=x` remains unsolved.

## Formula reconciliation

The primary paper contains two algebraic/indexing errors:

1. Its unsimplified probability sum for `U_n` simplifies to
   `2 sum_{r=0}^{n-2} x^r - (n-2)x^(n-1)`, whereas the next line prints
   `-n x^(n-1)`.  The printed version would give the impossible expected
   duration `U_1=-1`.
2. Its coefficient representation
   `a_j^(n)=3-2H_(n-j-1)+2H_j` is consistent with the corrected `U_n` and
   the defining integral.  The final expanded threshold equation instead
   uses an inner harmonic sum ending at `n-k-1`; consistency requires
   `n-k`.

The proof in this directory starts from the probability model, derives the
correct `U_n`, and then independently derives the coefficient formula from
the defining integral.

## 2016 restatement

Zdzislaw Porosinski, Marek Skarupski, and Krzysztof Szajowski,
*Duration problem: basic concept and some extensions*, Mathematica Applicanda
44(1) (2016), 87--112, repeats the definition and states that the value
monotonicity remains open.

- arXiv: https://arxiv.org/abs/1605.08364
- Relevant HTML section: https://arxiv.org/html/1605.08364#S3.SS5
- Published DOI: https://doi.org/10.14708/ma.v44i1.829

The survey copies both the erroneous simplified `U_n` formula and the
off-by-one expanded threshold equation.  These are not independent evidence
against the correction because its discussion is explicitly based on
Kurushima--Ano.

## Current-status search

Exact-title, exact-formula, author/citation, and optimal-stopping threshold
searches found no published proof or counterexample resolving this finite-
horizon monotonicity assertion through 2026-08-18.  Later work located in the
search addresses geometrically distributed horizons or different stopping
models rather than the polynomial `G_n` above.

The defensible wording is: **no indexed published resolution was located
through 2026-08-18; the intended monotonicity statement is proved by the
Bernstein-basis argument in this directory.**  Absolute novelty and
publication priority are not claimed.
