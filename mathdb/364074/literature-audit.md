# Literature and status audit for MathDB #364074

Checked through: 2026-08-18.

## Primary formulation

Wenston J. T. Zang, *Unimodality of the Rank on Strongly Unimodal Sequences*,
arXiv:2407.18186v1 (25 July 2024), states Conjecture 5.1 as

\[
u(0,n)-u(1,n)\geq N(0,n)/2\qquad(n\geq8)
\]

and says it was verified for `8<=n<=10000`.

- Abstract record: https://arxiv.org/abs/2407.18186
- Exact HTML: https://arxiv.org/html/2407.18186v1
- Conjecture 5.1: Section 5 of the HTML version

The arXiv record lists only v1.  The MathDB rendering starts the left side
with `\nu(0,n)`; the source has the counting function `u(0,n)`, so this is an
extraction typo rather than a second function.

## Identities used by the proof

Corollary 4.2 and equations (4.6)--(4.7) of the primary source imply

\[
u(0,n)+u(1,n)=(p(n)+N(0,n))/2.
\]

This makes Conjecture 5.1 equivalent to `p(n)-4u(1,n)>=0`.

The exact fixed-rank generating function used to obtain the false-theta
kernel comes from Kathrin Bringmann, Chris Jennings-Shaffer, Karl Mahlburg,
and Robert Rhoades, *Peak positions of strongly unimodal sequences*,
Transactions of the AMS 371 (2019), 7087--7109.

- arXiv record: https://arxiv.org/abs/1806.03217
- The paper also develops the relevant Wright circle-method framework and
  notes that its method yields arbitrarily long asymptotic expansions.

The effective proof here does not infer positivity from an asymptotic with an
unspecified error.  It supplies explicit major/minor bounds and uses the
standard Euler--Boole formula and remainder recorded at
https://dlmf.nist.gov/24.17.

## Current-status search

Exact-conjecture, exact-phrase, title/author, arXiv, and forward-literature
searches found no later paper claiming a proof or counterexample.  The author
has not posted a revision after v1, and v1 still presents the inequality as
Conjecture 5.1.

This is a current evidence report, not a claim that no unpublished or
unindexed proof exists.  The defensible wording is: **no indexed published
resolution was located through 2026-08-18; the effective proof and certificate
in this directory resolve the stated conjecture internally.**
