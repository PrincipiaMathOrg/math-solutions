# Literature audit for MathDB #332161

Audit date: 2026-08-18.

## Primary source and provenance

The primary public source is Xiongping Dai, *Grünwald version of van der Waerden's theorem for semi-modules*:

- [arXiv record and version history](https://arxiv.org/abs/1512.08695)
- [current arXiv text, v4](https://arxiv.org/html/1512.08695)
- earlier texts: [v1](https://arxiv.org/html/1512.08695v1), [v2](https://arxiv.org/html/1512.08695v2), and [v3](https://arxiv.org/html/1512.08695v3)

The version dates are 2015-12-29 (v1), 2016-01-10 (v2), 2016-06-17 (v3), and 2018-09-14 (v4).  The same proposed statement occurs as Conjecture 3.18 in v1, Conjecture 3.20 in v2 and v3, and Conjecture 3.26 in current v4.  Thus the counterexample below applies to every public arXiv version, not merely to an obsolete formulation.

Current v4 states:

> Let \(M=B_1\cup\cdots\cup B_q\) be any finite partition of a semimodule \((M,\boldsymbol +)\) over a semiring \((R,+,\cdot)\). One of the sets \(B_j\) has the property that if \(F\) is any finite subset of \(R\), then there are \(a\in M\) and \(b\in B_j\), with \(b\ne\boldsymbol o\), such that \(a\boldsymbol +Fb\subseteq B_j\).

The source explicitly defines a semiring to have additive zero and multiplicative unit, and a left semimodule to have \(1g=g\) and \(0g=\boldsymbol o\), in addition to the usual distributive laws.  Hence fields, including \(\mathbb F_2\), are within the literal scope.  The \(*\)-semiring condition is used for the preceding finitary theorem (v4 Theorem 3.25), but Conjecture 3.26 itself assumes only a semiring; the same separation is present in the earlier versions.

The arXiv header says only `Journal: IJM`.  No DOI, volume/pages, or independently identifiable version of record was found in exact-title, author-title, Crossref, zbMATH, or publisher searches.  The defensible citation is therefore the current arXiv v4, without asserting a journal publication.

## Literal counterexample

Take the semiring and semimodule

\[
R=M=\mathbb F_2,
\]

with its usual left action, partition

\[
B_1=\{0\},\qquad B_2=\{1\},
\]

and choose the finite set \(F=\{0,1\}\subseteq R\).

The cell \(B_1\) cannot be the asserted cell because it contains no nonzero candidate \(b\).  In \(B_2\), the only possible choice is \(b=1\).  But

\[
Fb=\{0,1\}=\mathbb F_2,
\qquad
a+Fb=\mathbb F_2
\]

for each \(a\in\mathbb F_2\).  This two-point set is not contained in the singleton \(B_2\).  Thus neither cell works even for this one \(F\), and the conjecture is false exactly as stated.

The failure is not a quantifier subtlety: it refutes both the source's stronger reading, in which one cell must work for every finite \(F\), and the weaker reading in which the cell might be allowed to depend on \(F\).

## Current-status and prior-art search

The following were checked through the audit date:

- all four arXiv versions and exact searches for `Conjecture 3.18`, `Conjecture 3.20`, and `Conjecture 3.26` together with `Schur-Brauer`;
- exact-title and arXiv-identifier searches combined with `counterexample`, `finite field`, `semiring`, `correction`, and `erratum`;
- author/title and prospective `IJM` publication searches;
- forward references indexed by OpenAlex.

[OpenAlex](https://api.openalex.org/works?filter=cites:W2221505571) lists three citing records.  Two are the preprint/published-record pair for Zhijing Chen and Xiongping Dai, *Chaotic dynamics of minimal center of attraction of discrete amenable group actions* ([arXiv:1707.07786](https://arxiv.org/abs/1707.07786), published as [10.1016/j.jmaa.2017.07.053](https://doi.org/10.1016/j.jmaa.2017.07.053)); the third is Dai, *An extension of Furstenberg's structure theorem for Noetherian modules and multiple recurrence theorems III* ([arXiv:1605.08599](https://arxiv.org/abs/1605.08599)).  Inspection of the public texts finds the source only in their bibliographies; neither mentions the Schur--Brauer conjecture or a finite-semiring obstruction.  A [2018 conference abstract](https://math.stu.edu.cn/__local/0/DF/7F/C6F999689B75BB6BC5A88108560_823BA147_64992.pdf?e=.pdf) located by exact-title search likewise restates the paper's main recurrence theorem and does not address the conjecture.

No later version, public correction, proof, or previously published counterexample to this exact semimodule conjecture was found.  Recommended wording is therefore: **the conjecture is false as literally stated; the \(\mathbb F_2\) counterexample appears not to have been recorded in the public literature located by this audit.**  The novelty clause is necessarily search-based and does not exclude unindexed private communication.

## Possible repaired scope

The example shows that some hypothesis excluding this finite torsion situation is indispensable.  Requiring an infinite cancellative setting, or reinstating a suitable \(*\)-semiring/nondegeneracy condition, would remove this particular example, but no such repair occurs in Conjecture 3.26.  This audit does not claim that any repaired formulation is true.
