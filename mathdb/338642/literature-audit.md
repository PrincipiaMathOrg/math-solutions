# Literature and status audit for MathDB #338642

Checked 19 August 2026.

## Primary statement

The source is Victor A. Bovdi and Ho-Hon Leung, *Maximal commutative
subalgebras of a Grassmann algebra*,
[arXiv:1803.03457v1](https://arxiv.org/abs/1803.03457), submitted
9 March 2018.  ArXiv lists only that version.  The exact public text is
available in the [arXiv HTML](https://arxiv.org/html/1803.03457v1).

In Section 4 the authors define, for \(n=4k+7\),

\[
\mathcal D_{2k+3}=\bigcup_{i=1}^{10}\mathcal B_i,
\qquad
\mathcal D_j=\mathcal P_n(j)
\quad(j\ge2k+5\text{ odd}),
\]

with all other layers empty (HTML lines 475--484).  They report that
\(d_k=|\mathcal D|/2^{n-2}\) decreases numerically from about
\(1.0188\) toward \(1\), and Conjecture 4 asks whether

\[
\lim_{k\to\infty}\frac{|\mathcal D|}{2^{n-2}}=1
\]

(HTML lines 510--522).  This is the statement represented by MathDB
#338642.

The paper was published as *Journal of Algebra and Its Applications*
18(7), article 1950139 (2019), DOI
[10.1142/S0219498819501391](https://doi.org/10.1142/S0219498819501391).
The [authors' institutional record](https://research.uaeu.ac.ae/en/publications/maximal-commutative-subalgebras-of-a-grassmann-algebra/)
gives 1 July 2019 as the publication date.  The version-of-record body
was not publicly accessible during this audit, so this dossier makes no
claim about whether its wording differs from the public arXiv text.

## The later follow-up solves a different conjecture

Ho-Hon Leung's follow-up,
[arXiv:1810.08781v1](https://arxiv.org/abs/1810.08781), explicitly says
that it proves Conjecture 5 of the Bovdi--Leung paper: the construction
for \(n=4k+1\) has dimension below \(3\cdot2^{n-2}\) for every relevant
\(k\).  Its scalar named \(D=C_1+C_2\) is part of an inequality
\(D<E\); it is not the family \(\mathcal D\) occurring in Conjecture 4.
Thus that follow-up, later published with F. Kamalov, does not resolve
the asymptotic question treated here.  The publication record is
[Leung--Kamalov, *Journal of Algebra and Applied Mathematics* 20(1)
(2022), 47--55](https://research.uaeu.ac.ae/en/publications/a-remark-on-commutative-subalgebras-of-grassmann-algebra/).

## Resolution and prior-art search

The source itself gives the exact exceptional-layer count

\[
7\binom{4k}{2k}+21\binom{4k}{2k+1}
+7\binom{4k}{2k+2}+\binom{4k}{2k+3}.
\]

Combining it with the elementary alternating-binomial tail identity
immediately reduces the conjecture to the fact that a central binomial
coefficient is \(O(2^{4k}/\sqrt{k})\).  The solution in this dossier
sharpens this to an exact formula for the excess.  The conjecture is
therefore mathematically resolved, although the argument is elementary
and essentially implicit in the source's displayed formulas.

Exact-title, DOI, exact-number (including `d_249=1.0031`), and
Conjecture-4 formula searches located no later source explicitly proving
this limit.  The only directly identified author follow-up was the
distinct Conjecture-5 paper above.  Crossref reported
`is-referenced-by-count = 0`, and the OpenAlex DOI record
`W2791202660` reported `cited_by_count = 0`; those database counts are
search evidence only, not proof that no unindexed citation exists.

**Status conclusion.** No explicit public resolution of Conjecture 4
was located through 19 August 2026.  This dossier supplies an apparently
first explicit written proof found in that search, but no strong priority
claim is appropriate: the proof is a short consequence of the source's
own exact formulas and standard binomial estimates, and may have been
regarded as implicit or folklore.
