# Literature and status audit for MathDB #338640

Checked 19 August 2026.

## Database identity

MathDB #338640 is titled *Minimality conjecture for the constructed
bicommutative system*. A live API check reported status=open and
post_type=open_problem, with no edit, moderator edit, comment, reply, model
attempt, human solve, or alternate formulation. The normalized live-statement
SHA-256 was

    d546bbd3622da6d587af3d864e943a4388efb4b300d6cf32ccaf5cd4a31c6ba3

which exactly matches the immutable batch and deduplication-ledger entry.
The record has no origin links, and the identifier occurs only once in the
campaign ledger.

## Primary source and exact scope

The source is Victor A. Bovdi and Ho-Hon Leung,
[*Maximal commutative subalgebras of a Grassmann
algebra*](https://arxiv.org/abs/1803.03457),
arXiv:1803.03457v1, submitted 9 March 2018. ArXiv has only that version.
The version of record is in *Journal of Algebra and Its Applications*
**18**(7) (2019), article 1950139,
[doi:10.1142/S0219498819501391](https://doi.org/10.1142/S0219498819501391).

Section 3 defines an \(s\)-bicommutative system as a pairwise-intersecting
family in \(\mathcal P_n(s)\) that is maximal: every outside \(s\)-set is
disjoint from a family member. Theorem 1 constructs \(\mathcal A_m\) for
\(n=4k+7,m=2k+3,k\ge2\). The paper computes

\[
|\mathcal A_m|
=7\binom{4k}{2k}
 +\binom72\binom{4k}{2k+1}
 +7\binom{4k}{2k+2}
 +\binom{4k}{2k+3},
\]

and Conjecture 2 asks whether this family has minimum size among all such
systems. At \(k=2\), the formula is \(1870\).

## Prior refutation

The graph-theoretic translation predates the source. A maximal intersecting
family of \(r\)-subsets of \([n]\) is exactly an independent dominating set
in the Kneser graph \(KG(n,r)\); Igor Gorodezky reviews this equivalence in
Chapter 8 of his 2007 University of Waterloo master's thesis,
[*Dominating sets in Kneser
graphs*](https://dspacemainprd01.lib.uwaterloo.ca/server/api/core/bitstreams/933ccaf6-db63-4845-bb42-336ea77611c1/content).

More decisively, Ahmed Ibrahim Al-Herz,
[*Independent Domination in Odd
Graphs*](https://eprints.kfupm.edu.sa/id/eprint/138607/),
M.S. thesis, King Fahd University of Petroleum and Minerals, 2012, gives
approximation algorithms for precisely these graphs. The repository record
and the [Saudi Digital Library
mirror](https://drepo.sdl.edu.sa/items/c278cf5e-ef9d-4824-9be7-b97b568d5fba)
confirm the title, author, institution, and date. The archived primary PDF is
[available here](https://web.archive.org/web/20240615192111id_/https://eprints.kfupm.edu.sa/id/eprint/138607/1/INDEPENDENT_DOMINATION_IN_ODD_GRAPHS.pdf).

In Al-Herz's convention the odd graph of dimension \(d\) has
\(\binom{2d-1}{d-1}\) vertices, with disjoint subsets adjacent. Therefore
his \(d=8\) graph is exactly

\[
O_8=KG(15,7),
\]

the \(k=2\) instance of the Bovdi--Leung conjecture. Table 1 on printed page
78 (PDF page 88) records

\[
|V|=6435,\qquad |E|=25740,\qquad
|\mathrm{IDS}|=1097
\]

for the valid Approx. 2 construction; the same table reports greedy and
randomized values 1310 and 1519. The thesis proves the approximation
algorithm's correctness in Section 4.3.2 and explicitly says in its conclusion
that Approx. 2 remains valid above dimension seven. Thus a public independent
dominating set of size \(1097<1870\) existed in 2012, six years before the
conjecture was posted.

## Later records

Ho-Hon Leung's
[*A remark on commutative subalgebras of Grassmann
algebra*](https://arxiv.org/abs/1810.08781),
arXiv:1810.08781v1, proves the source's distinct Conjecture 5 concerning
maximal commutative subalgebras when \(n=4k+1\). It does not discuss the
finite \(m\)-bicommutative minimality question.

The current OEIS entry
[A296852](https://oeis.org/A296852), *Domination and lower independence
number of the n-odd graph*, lists only
\(1,1,3,7,26,66\), through \(n=6\), and does not supply an \(O_8\) optimum.
Exact-title, conjecture-phrase, Spec(k,2), \(KG(15,7)\), \(O_8\), and
independent-domination searches found no later claim that the exact minimum
is known.

## Status conclusion

MathDB #338640 is **stale/already refuted**, not a newly solved open problem.
The exact 1173-set certificate in this dossier independently confirms the
failure of the conjecture, but it is weaker than Al-Herz's prior 1097-set
construction and receives no campaign credit. No claim of priority or of
the exact minimum is made.
