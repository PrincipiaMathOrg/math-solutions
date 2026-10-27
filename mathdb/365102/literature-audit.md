# Literature and status audit for MathDB #365102

Checked 19 August 2026.

## Database identity

MathDB #365102 is titled *The barycenter conjecture for one-dimensional free
Gibbs measures*.  A live API check reported *status=open* and
*post_type=open_problem*, with no edit, moderator edit, comment, reply, model
attempt, human solve, or alternate formulation.  The normalized
live-statement SHA-256 was

    5722e18b51fe734e24794e05d6a92951cfb156adfecfc4f1f5a16f9635097423

which exactly matches the immutable batch and deduplication-ledger entry.
The record has no origin links, and the identifier occurs only once in the
campaign ledger.

The MathDB prose refers to an assumption labelled *(gibbs)* and contains two
malformed TeX escapes.  The linked primary source removes the ambiguity: its
Conjecture 1 explicitly points to numbered condition (14).

## Primary source and exact scope

The source is Charles-Philippe Diez,
[*A sharp symmetrized free transport-entropy inequality for the semicircular
law*](https://arxiv.org/abs/2410.02715), arXiv:2410.02715v2.  Version 1 was
submitted 3 October 2024 and the current version 2 was submitted 25 December
2024.  The [current HTML text](https://arxiv.org/html/2410.02715v2) and the
[University of Luxembourg repository copy](https://hdl.handle.net/10993/62153)
were checked.  The current arXiv record gives no journal reference; DataCite
classifies the arXiv DOI as a preprint, and no matching version of record was
located.

Definition 1 defines \(\nu_u\) as the unique maximizer, when it exists, of

\[
\chi_u(\mu)=\chi(\mu)-\int u\,d\mu.
\]

The text immediately before condition (14) says that in one dimension a
lower-semicontinuous potential has a unique compactly supported equilibrium
measure when

\[
\lim_{|x|\to\infty}(u(x)-2\log|x|)=+\infty.
\]

Conjecture 1 then asks, for **every continuous** \(f\) satisfying condition
(14), whether some \(\lambda\in\mathbb R\) makes
\(\nu_{f+\lambda\operatorname{id}}\) have barycenter zero.  The dossier uses
exactly those quantifiers and the source's variational definition.

There is a visible hypothesis mismatch in the paragraph preceding the
conjecture: it says the finite-dimensional partition functions are defined
because \(f\) grows faster than every linear function, although condition
(14) only requires growth beyond \(2\log|x|\).  The counterexample exploits
precisely this gap.

## Forward-result search

Exact-title, arXiv-identifier, exact-conjecture, free-Gibbs/barycenter,
linear-tilt, logarithmic-growth, proof, and counterexample searches located no
public proof, refutation, corrigendum, or later source version addressing
Conjecture 1.

The discoverable forward records inspected included Diez's companion
preprint,
[*Free Stein Kernel and Moments maps*](https://arxiv.org/abs/2410.02470),
arXiv:2410.02470v2, and David Jekel,
[*Information geometry for types in the large-\(n\) limit of random
matrices*](https://arxiv.org/abs/2501.00703), arXiv:2501.00703v2, published in
*Communications in Mathematical Physics* **406** (2025), article 272,
[doi:10.1007/s00220-025-05451-x](https://doi.org/10.1007/s00220-025-05451-x).
The companion paper cites the transport-entropy preprint in its background.
Jekel cites it as a free symmetrized Talagrand result while developing a
different multivariable/type-space problem.  Neither discusses Conjecture 1,
the logarithmic-versus-superlinear mismatch, or the counterexample here.

The source itself proves in Proposition 5 that an even potential has a
symmetric equilibrium measure.  That is consistent with, but does not state,
the shifted-reflection observation used here; it supplies no conclusion about
nonconfining linear tilts.

## Status conclusion

No prior explicit public resolution was located.  The literal conjecture is
refuted by a self-contained smooth example.  A repaired superlinear version
remains outside the scope of this result, and publication priority is not
claimed.
