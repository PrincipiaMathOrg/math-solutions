# Literature and provenance audit for MathDB #347688

Status date: **2026-08-18**.

## Primary source and exact statement

The source is Alan Lew, “Representability and boxicity of simplicial
complexes,” [arXiv:2008.09997](https://arxiv.org/abs/2008.09997).  The arXiv
record has only version 1, submitted 23 August 2020; the HTML identifies it as
`arXiv:2008.09997v1`, and the DataCite record also reports `version: 1`:

- <https://arxiv.org/html/2008.09997>
- <https://api.datacite.org/dois/10.48550/arxiv.2008.09997>

The peer-reviewed version of record is:

> Alan Lew, “Representability and Boxicity of Simplicial Complexes,”
> *Discrete & Computational Geometry* **68** (2022), 592–607,
> <https://doi.org/10.1007/s00454-021-00332-1>.

The [publisher record](https://link.springer.com/article/10.1007/s00454-021-00332-1)
reports receipt on 25 August 2020, revision and acceptance on 13 July 2021,
online publication/version of record on 27 October 2021, and a September 2022
issue date.

The source convention is important.  For a finite family
\(\mathcal F=(F_i)_{i=1}^n\),

\[
N(\mathcal F)=\left\{\sigma\subseteq[n]:
\bigcap_{i\in\sigma}F_i\ne\varnothing\right\}.
\]

A complex is \(d\)-representable when it is isomorphic to the nerve of a
family of **compact convex sets** in \(\mathbb R^d\), and
\(\operatorname{rep}(X)\) is the least such \(d\).  Thus an explicit family of
compact polytopes meets the source definition without any convention change.
A missing face is a nonface all of whose proper subsets are faces.

The paper states, verbatim in substance, as **Conjecture 20**:

> Let \(X_{2,9}\) be the simplicial complex whose missing faces form a
> Steiner \((2,3,9)\)-system (that is, they are the lines of the affine plane
> of order 3). Then \(\operatorname{rep}(X_{2,9})\le 5\).

There are \(\binom 92/\binom32=12\) missing triples.  Equivalently,
\(X_{2,9}\) consists of the subsets of the nine points of \(AG(2,3)\) that
contain no affine line.

The number 5 is not a transcription error.  Lew's more general Conjecture 17
predicts

\[
\operatorname{rep}(X)\le
\left\lfloor\frac{dn}{d+1}\right\rfloor.
\]

For \(d=2,n=9\), this gives 6.  Its proposed equality characterization says
that equality can occur only when the missing faces are three pairwise
disjoint triples.  The twelve affine-plane lines do not have that form, so
the conjectured strict inequality and integrality give the stated bound 5.

## Later author restatement

Lew's August 2021 Technion PhD thesis,
[“Studies in topological combinatorics”](https://www.math.cmu.edu/users/alanlew/files/theses/phd%20thesis.pdf),
repeats the statement as **Conjecture 6.5.5** on printed page 117 (PDF page
129).  The
preceding sentence calls its solution “a (very modest) step towards” the
general representability conjecture.  This thesis postdates the journal
revision/acceptance and supplies a later full-text author restatement; it
does not contain a solution.

The same thesis denotes the complex of line-free subsets of
\(\mathbb F_3^2\) by \(X_3\).  It computes
\(\widetilde H_3(X_3;\mathbb Z)\cong\mathbb Z^{11}\).  Since a
\(d\)-representable complex is \(d\)-Leray, this gives only
\(\operatorname{rep}(X_{2,9})\ge4\), not a lower bound of 5.

## Earlier and nearby results do not settle the target

- Wegner's general construction, as recalled in Lew's paper/thesis, gives
  \(\operatorname{rep}(X)\le n-2\) here, hence only the bound 7.
- H. S. Witsenhausen,
  [“On intersections of interval graphs”](https://doi.org/10.1016/0012-365X(80)90038-2),
  *Discrete Mathematics* **31** (1980), 211–216, studies the higher
  boxicity/intersection-product parameter.  Lew's theorem gives
  \(\operatorname{box}_2(X_{2,9})=12\), but this is not a representation of
  the single nerve in \(\mathbb R^5\).
- Martin Tancer,
  [“Non-representability of finite projective planes by convex sets”](https://arxiv.org/abs/0908.4038),
  *Proc. Amer. Math. Soc.* **138** (2010), 3285–3291, concerns the nerve whose
  vertices are projective-plane **lines** and whose faces are concurrent
  line families.  That dual incidence complex is not the line-free complex
  here, whose vertices are affine-plane points and whose minimal nonfaces are
  lines.
- Design-theory papers using “representation,” “embedding,” or
  “visualization” of a Steiner triple system concern a different notion from
  convex-nerve representability.

Accordingly, none of these results supplies the requested nine-set convex
nerve in \(\mathbb R^5\).

## Current-status search

The following forward-citation records all returned zero citing works on the
status date:

- [Crossref DOI metadata](https://api.crossref.org/works/10.1007/s00454-021-00332-1):
  `is-referenced-by-count: 0`;
- [OpenAlex work W3080453488](https://api.openalex.org/works/https://doi.org/10.1007/s00454-021-00332-1):
  `cited_by_count: 0`;
- [Semantic Scholar DOI record](https://api.semanticscholar.org/graph/v1/paper/DOI:10.1007/s00454-021-00332-1?fields=title,year,citationCount,externalIds,citations.title,citations.year,citations.externalIds):
  `citationCount: 0` and an empty citing-paper list.

Exact-title, DOI, arXiv-number, phrase, and notation searches included:

```text
"Representability and Boxicity of Simplicial Complexes"
"10.1007/s00454-021-00332-1"
"2008.09997"
"X_{2,9}" representability
"rep(X_{2,9})"
"Conjecture 20" "affine plane of order 3"
"Steiner (2,3,9)" representability
"lines of the affine plane of order 3" simplicial complex
"Let X_{2,9} be the simplicial complex"
```

They located the source, the author's thesis, the author's slides/seminar
pages, bibliographic mirrors, and unrelated uses of “representation,” but no
proof, counterexample, or explicit convex-nerve construction.  The author's
[current publication page](https://alanlew22.github.io/) lists publications
through 2026 and no follow-up resolving this problem.

Citation databases and web indexing cannot exclude private or unindexed
work.  The defensible public-literature conclusion is therefore:

> **No published or publicly posted resolution of Conjecture 20 was located
> through 2026-08-18.  Subject to the stated search limitations, the explicit
> \(\mathbb R^5\) construction in this dossier appears to be the first public
> resolution of the conjectured upper bound.**

It should not be described as proving
\(\operatorname{rep}(X_{2,9})=5\).  It proves only the requested upper bound
\(\operatorname{rep}(X_{2,9})\le5\); together with the known homological lower
bound, the exact value remains either 4 or 5.
