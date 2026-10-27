# Literature and status audit for MathDB #333521

Checked 19 August 2026.

## Database identity

MathDB #333521 is titled *Minimum distance signless Laplacian spread among
bipartite graphs*.  A live API check still reported status open and post type
open_problem, with no edit, moderator edit, comment, reply, model attempt, or
human solve.  The normalized live-statement SHA-256 was

    2419bbed35875c6c5d0d75ac1e410be111e45fbba485aa1f31db9078dfbd1587

which exactly matches the immutable ledger entry.

## Primary source and scope

The source is Lihua You, Liyong Ren, and Guanglong Yu, *Distance and
distance signless Laplacian spread of connected graphs*,
[arXiv:1607.00473](https://arxiv.org/abs/1607.00473).  ArXiv exposes one
version, submitted 2 July 2016.  The paper was published in *Discrete
Applied Mathematics* 223 (2017), 140--147, DOI
[10.1016/j.dam.2016.12.030](https://doi.org/10.1016/j.dam.2016.12.030).
The arXiv source archive and the eight-page version-of-record PDF were both
checked directly.

The global convention at the start of the paper is that graphs are simple,
connected, and undirected.  The published Conjecture 4.4 is exactly the
MathDB inequality and equality characterization.  It follows computer
checks of some bipartite graphs through order ten.  The preceding Theorem 4.3
proves only that the balanced graph minimizes the spread among *complete*
bipartite graphs.  The solution dossier proves the missing comparison with
every connected bipartite graph.

## Forward-result search

Exact-title, exact-conjecture, displayed-formula, balanced-complete-
bipartite, author/title, DOI, and citation searches located no public proof
or counterexample through the audit date.  OpenAlex returned twelve works
citing the source.  The directly relevant records were screened rather than
being inferred from citation counts alone.

Pirzada, Ganie, Alhevaz, and Baghipur,
[*On spectral spread of generalized distance matrix of a graph*](https://arxiv.org/abs/1907.09462),
define \(D_\alpha=\alpha\operatorname{Tr}+(1-\alpha)\mathcal D\), so that
\(2D_{1/2}=\mathcal Q\).  Their source text again leaves the balanced
complete bipartite minimizer as an open problem for general \(\alpha\);
the published article is in *Linear and Multilinear Algebra* 70 (2022),
2819--2835, DOI 10.1080/03081087.2020.1814194.

The full text of Ma and Shao, *Some properties of generalized distance
eigenvalues of graphs*, *Czechoslovak Mathematical Journal* 74 (2024),
1--15, was searched directly.  It cites the source but contains no
bipartite or complete-bipartite result.  Other indexed spread papers give
parameter bounds, not this extremal theorem.  The May 2026 survey
*Distance signless Laplacian spectra of graphs: A survey*, DOI
10.1016/j.dam.2025.12.044, is the newest indexed citation.  Its public
abstract, searchable record, and reference index were checked, and exact
result searches located no claim resolving Conjecture 4.4.

## Status conclusion

No prior explicit public resolution was located.  The proof here is
self-contained apart from standard Rayleigh--Ritz facts and proves the
exact source/MathDB conjecture, including uniqueness.  Publication priority
is not claimed.
