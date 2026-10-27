# Literature audit for MathDB #381167

Last updated: 2026-08-18 (America/Toronto).

## Primary record

- MathDB: https://mathdb.com/p/381167
- arXiv: https://arxiv.org/abs/1305.2036
- HTML, open-problem section: https://arxiv.org/html/1305.2036#S7
- Published paper: https://doi.org/10.1016/j.camwa.2012.01.027

The arXiv source has one version, submitted 2013-05-09. The published article
predates the arXiv deposit. Section 7 explicitly asks for the implication from
the pointwise sum condition to uniform exponential stability on Banach spaces.

## Distinctions that must not be conflated

The same paper proves related statements with:

- the sum of the **operator norms** `Σ ||A_m^k||`; and
- the pointwise sum for the **adjoint products** `Σ ||(A_m^k)^*x^*||`.

The candidate counterexample concerns only the later open condition
`Σ ||A_m^k x|| ≤ B||x||`. It does not contradict those theorems.

## Searches completed

- Inspected the exact TeX and current arXiv HTML for definitions, quantifiers,
  and product indexing.
- Enumerated the works linked as citations to both the published DOI record and
  the arXiv mirror in OpenAlex (11 and 3 records respectively at check time).
- Inspected the accessible 2017 follow-up arXiv:1710.02191; it cites the paper
  but addresses a different sequence-space characterization.
- Queried arXiv and general web indexes for the exact title and displayed
  pointwise condition.

## Outcome

The forward-citation, erratum/correction, exact-phrase, and mechanism searches
located no published resolution of the exact primal condition through
2026-08-18. The most relevant later works change the setting or hypothesis:

- Lupa--Popescu, arXiv:1710.02191, gives a sequence-space/invertibility
  characterization.
- Dragičević, DOI 10.1007/s00605-020-01438-z, studies ergodic linear cocycles.
- Other citing papers treat the 2012 article as stability background rather
  than recording a solution to Section 7.

An independent source-level audit reproduced both the rank-one `ℓ¹(ℕ₀)`
counterexample and a stronger uniformly invertible weighted-shift version on
`ℓ¹(ℤ)`.

The defensible bibliographic wording is: **no indexed published resolution was
located through 2026-08-18; the statement is refuted by the explicit
counterexample developed in this campaign**.

