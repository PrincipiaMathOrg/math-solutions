# Source and formulation audit

## Primary source

Szilárd Gy. Révész and Imre Z. Ruzsa,
[Densitometria I. Discrete groups](https://arxiv.org/abs/2511.18064),
arXiv:2511.18064v1, 22 November 2025.

The relevant items are Definition 12.1, Problem 12.2, and Conjecture
12.3.  The structural facts used in the proof are Definition 9.1 and
Statement 9.3(c),(e).

## Exact scope

The paper assumes throughout that \(G\) is an infinite commutative
discrete group.  The MathDB wording “a discrete group” is broader than
the cited source.

An upper density is, by Definition 9.1, the restriction to indicators
of an upper mean.  Definition 12.1 says it is mensural if

\[
\overline d(A)=\limsup_j\mu_j(A)
\]

for a sequence of measures and every subset \(A\).  Problem 12.2 asks
which sequences do this.  Conjecture 12.3 answers: those satisfying

\[
\sum_x|\mu_n(x)-\mu_n(x+t)|\to0
\]

for every \(t\in G\).

The MathDB statement accidentally presents the proposed condition once
as if it were a definition and then repeats it as the conjecture.  The
first occurrence should instead be the formula
\(\overline d(A)=\limsup_n\mu_n(A)\).

## Missing normalization

The paper does not use the phrase “probability measure” and gives no
normalization in Section 12.  Read literally, Conjecture 12.3 is false.

Let \(\lambda_n\) be uniform on \(\{1,\ldots,2n\}\), let
\(\eta_n={\bf1}_{2\mathbb Z}\lambda_n\), and interleave
\(\mu_{2n}=\lambda_n\), \(\mu_{2n-1}=\eta_n\).  Then
\(\eta_n\leq\lambda_n\) pointwise, so the represented upper density is
the ordinary asymptotic upper density.  Nevertheless

\[
\|\eta_n-\tau_1\eta_n\|_1=1.
\]

Thus the literal necessity claim fails.  The all-zero sequence also
satisfies the displayed Reiter condition but violates norming
\(\overline d(G)=1\), so literal sufficiency fails too.

The statement “This condition is easily seen to be sufficient” strongly
indicates that probability measures were intended.  With that repair,
the conjecture is proved in solution.md.

## Status

**Public status (checked 18 August 2026).**  The arXiv history exposes only
version 1 (22 November 2025); a version-2 URL returns 404, no journal
reference is listed, and the text still labels the assertion Conjecture
12.3.  DataCite reports version 1, zero indexed citations, and no related
identifiers.  OpenAlex's two ingestion variants both report zero forward
citations, while a Crossref title-and-author query returns no exact-title
record.

Searches used the exact title, arXiv identifier, exact Problem 12.2 wording,
`"Conjecture 12.3" "measures" "density"`, author/topic combinations, and
site-restricted Scholar, Semantic Scholar, OpenAlex, and Crossref queries.
They located no later public proof, counterexample, or citing paper.  The
Semantic Scholar API was rate-limited, so no count from it is asserted.  This
is a negative-search conclusion, not a guarantee against unindexed or private
work.

The closest classical tools found do not by themselves settle the question.
Phillips' lemma and the Schur property upgrade actual setwise convergence to
total variation, whereas the conjecture initially gives only a limsup set
functional.  The selector lemma in `solution.md` supplies precisely that
missing bridge.  No occurrence of its indicator-domination statement was
located in the exact searches.

The closest primary precedent found is G. G. Lorentz, *A Contribution to the
Theory of Divergent Sequences*, Acta Math. 80 (1948), 167--190,
<https://doi.org/10.1007/BF02393648>.  Its Theorem 7 is a matrix analogue for
`G=Z`, but not the arbitrary-group limsup-density statement.  Phillips'
classical lemma (Trans. AMS 48 (1940), Lemma 3.3,
<https://doi.org/10.1090/S0002-9947-1940-0004094-3>) and the modern statement
in <https://arxiv.org/abs/2208.13468> begin with actual setwise convergence;
they therefore do not supply the selector lemma needed here.
