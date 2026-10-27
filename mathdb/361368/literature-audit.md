# Literature and status audit for MathDB #361368

Checked through: 2026-08-18.

## Verdict

The equality recorded by MathDB is an **arXiv-v1-only conjecture and is
false as written**.  The best-supported publication-history conclusion is
that it was omitted, rather than retained or repaired, in the revised
peer-reviewed line.  No public correction, erratum, or later paper resolving
the arXiv-v1 assertion was located.

There is one access qualification: the main body of the Springer version of
record is paywalled, so this audit did not directly compare every page of the
VOR with arXiv v1.  The omission conclusion is instead supported by the
official version metadata, the public VOR material, and especially the
author's April 2025 dissertation, whose preface identifies the relevant
chapter's content with the paper but which contains no such conjecture.

## Exact arXiv-v1 statement

Junjie Zhu, *Fourier dimension of conical and cylindrical hypersurfaces*:

- arXiv record and complete version history:
  https://arxiv.org/abs/2401.01455
- arXiv v1 HTML, Section 8, “A new question”:
  https://arxiv.org/html/2401.01455#S8

The record contains only v1, submitted 2 January 2024.  Conjecture 8.1 lets
\(A\subset\mathbb R^d\) satisfy \(\dim_F A=s\le d\), explicitly says that
\(A\) need not lie on a hypersurface, defines

\[
C_A=\{h(x,1):x\in A,\ h\in\mathbb R\},
\qquad D_A=A\times\mathbb R,
\]

and asserts

\[
\dim_F(C_A)=\dim_F(D_A)=\dim_F(A)=s.
\]

The displayed definition in v1 actually prints \(D_A:=S\times\mathbb R\)
while the set-builder expression uses \(x\in A\); \(S\) is an evident typo
for \(A\).  MathDB should also use \(A\subset\mathbb R^d\), not
\(A\ni\mathbb R^d\), if that transcription remains in the database.

## Disposition in the peer-reviewed line

The version of record is:

- Springer VOR: https://doi.org/10.1007/s12220-025-02157-3
- publication page:
  https://link.springer.com/article/10.1007/s12220-025-02157-3

It was received 8 January 2024, accepted 11 August 2025, and published 18
August 2025 in the *Journal of Geometric Analysis*, volume 35, article 318.
The public VOR abstract is revised relative to arXiv v1, but the paywall
conceals the main body.  Neither the public VOR text nor its exposed end
matter and appendices contains “Conjecture 8.1,” “A new question,” or the
\(C_A,D_A\) equality.  This negative observation alone would not establish
omission because of the paywall.

The strongest public evidence is Zhu's April 2025 UBC dissertation, *On
applications of oscillatory integrals*:

- official DOI: https://doi.org/10.14288/1.0448447
- UBC Open Collections record:
  https://open.library.ubc.ca/soa/cIRcle/collections/ubctheses/24/items/1.0448447
- author's research page linking both the paper and dissertation:
  https://sites.google.com/view/junjie-zhu/researchtalks

Its preface identifies the content of Chapter 4 as having resulted in
arXiv:2401.01455 (then under peer review).  Chapter 4 has only Sections
4.1--4.4 and does not contain Section 8 of arXiv v1, Conjecture 8.1, its
equality, or the cylinder question.  The dissertation's actual “Future
directions” chapter instead asks broadly about Fourier decay for
non-self-similar measures and lists the Fourier dimension of a generated
cone among possible applications; it does not assert the universal equality
and does not mention the cylinder.  The dissertation predates VOR acceptance
by about four months and therefore provides strong accepted-era evidence
that the false conjecture had been withdrawn rather than revised into a new
precise equality.

Accordingly, the cautious source-disposition wording is: **Conjecture 8.1
appears only in arXiv v1; the available public evidence indicates that it
was omitted from the author's revised peer-reviewed treatment.**  It should
not be described as a conjecture
retained by the final journal article unless a reader with VOR access checks
the hidden body and finds otherwise.

## Mathematical status

The literal v1 statement is refuted by the compact convex choice
\(A=\overline B_d\subset\mathbb R^d\).  It has \(\dim_F(A)=d\), while

\[
D_A=A\times\mathbb R,
\qquad
C_A=\{(y,h):\lVert y\rVert\le |h|\}
\]

both have nonempty interior in \(\mathbb R^{d+1}\).  A Borel set with
nonempty interior has full ambient Fourier dimension (use a smooth
probability density supported in an interior ball), so

\[
\dim_F(C_A)=\dim_F(D_A)=d+1>d=\dim_F(A).
\]

This uses the expressly allowed endpoint \(s=d\).  It does not decide a
different problem imposing \(s<d\), empty interior, or another thinness
hypothesis.  Those repairs do not occur as a precise replacement conjecture
in the accepted-era material audited here.

## Corrections and forward citations

Springer's Crossmark record for the DOI says “Document is current” and lists
no correction, update, or retraction:
https://crossmark.crossref.org/dialog/?doi=10.1007%2Fs12220-025-02157-3&domain=link.springer.com&uri_scheme=https%3A

Crossref and OpenAlex reported zero linked forward citations on the audit
date, while Semantic Scholar reported two; this discrepancy is ordinary
indexing lag, so the two identifiable primary texts were inspected directly:

- Zhu, *Fourier dimension of constant rank hypersurfaces*,
  https://arxiv.org/abs/2410.09711.  It cites the conical/cylindrical paper
  for its hypersurface theorem and does not state or resolve the arbitrary-set
  equality.
- Jacob Denson, *The Maximum Codimension of a Salem Submanifold*,
  https://arxiv.org/abs/2606.25157.  It mentions Zhu's conical and cylindrical
  hypersurface techniques in historical context and does not discuss
  Conjecture 8.1.

Exact searches included the paper title and DOI with `correction`, `erratum`,
and `corrigendum`, as well as `"Conjecture 8.1" "Fourier dimension"`,
`"dim_F(C_A)=dim_F(D_A)"`, and
`"not necessarily lying on a hypersurface" "Fourier dimension"`.  They
located the arXiv source but no public correction, independent proof,
counterexample, or later adoption of the statement.

## Recommended MathDB disposition

Mark #361368 **refuted / obsolete as an open problem** and identify its
provenance precisely as arXiv:2401.01455v1, Conjecture 8.1.  A suitable note
is:

> The literal arXiv-v1 conjecture is false, already for a compact ball at
> the allowed endpoint \(s=d\).  The conjecture appears to have been omitted
> from the revised peer-reviewed line; no replacement statement or public
> correction was found through 2026-08-18.

This is stronger and more accurate than calling the entry merely “open” or
“stale”: the recorded claim has a direct counterexample, while any repaired
thin-set question would be a new statement requiring its own formulation.
