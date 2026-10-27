# Literature and status audit for MathDB #359102

Checked 19 August 2026.

## Database identity

MathDB #359102 is titled *Uniformly separated bounded sets are
\(\ell^1\)-bounded*.  A live API check still reported `status=open` and
`post_type=open_problem`, with no edit, moderator edit, comment, reply, model
attempt, or human solve.  The normalized live-statement SHA-256 was

    014e80013be8ad2e05cfc4569f601b0d4b107141e08256abd84dbef1d2c0781d

which exactly matches the immutable ledger entry.

## Primary source and exact scope

The source is Christopher Heil and Pu-Ting Yu,
[*\(\ell^1\)-Bounded Sets*](https://arxiv.org/abs/2307.05536),
arXiv:2307.05536v1, submitted 8 July 2023.  It was published in the
*Journal of Mathematical Analysis and Applications* **539**(2) (2024),
article 128528,
[doi:10.1016/j.jmaa.2024.128528](https://doi.org/10.1016/j.jmaa.2024.128528).
The [author-hosted final text](https://heil.math.gatech.edu/papers/ell1bounded.pdf)
was checked directly.

Definition 2.1 says that a subset \(M\) of the separable
infinite-dimensional complex Hilbert space \(H\) is \(\ell^1\)-bounded if
some Riesz basis \(E=\{e_n\}\) satisfies

\[
\sup_{x\in M}\sum_n|\langle x,e_n\rangle|<\infty.
\]

Conjecture 4.10 then states exactly that every bounded uniformly separated
subset of \(H\) is \(\ell^1\)-bounded.  The dossier uses these conventions
without changing the space, the coefficient functional, or either
quantifier.  It proves the stronger fact that the constructed set is not
\(\ell^1\)-frame-bounded.

## Forward-result search

The arXiv record still has only version 1.  Exact-title, exact-conjecture,
uniform-separation/Riesz-basis, \(\ell^1\)-frame-bounded, author/title, DOI,
and counterexample searches located no public proof or refutation.

OpenAlex indexed one forward citation: Pu-Ting Yu,
[*Frame-normalizable sequences*](https://doi.org/10.1007/s10444-024-10182-z),
*Advances in Computational Mathematics* **50** (2024).  Its topic is
normalization of iterative frame systems, not Conjecture 4.10.  Semantic
Scholar returned that paper plus two malformed bibliographic rows, neither
of which supplies a result about uniformly separated sets.

Pu-Ting Yu's Georgia Tech dissertation,
[*Convergence of Frame Series from Hilbert Spaces to Banach Spaces and
\(\ell^1\)-Boundedness*](https://hdl.handle.net/1853/75669) (2024), repeats the
same assertion as Conjecture 4.2.9 and gives no resolution.  The dissertation
is useful independent evidence that the question remained open after the
preprint and through the publication process.

## Status conclusion

No prior explicit public resolution was located.  The counterexample here is
self-contained and addresses the exact published conjecture.  Publication
priority is not claimed.
