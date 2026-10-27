# Literature and status audit for MathDB #361027

Checked 19 August 2026.

## Primary statement

The source is Robert Janczewski, Krzysztof Turowski, and Bartlomiej
Wroblewski, *Edge coloring of products of signed graphs*.  The current
[arXiv record](https://arxiv.org/abs/2312.02691) has three versions, with v3
dated 14 June 2024.  The paper was subsequently published in
*Discussiones Mathematicae Graph Theory* 45(2) (2025), 763--786, DOI
[10.7151/dmgt.2553](https://doi.org/10.7151/dmgt.2553).  The authors'
institutional repository provides the
[open version of record](https://ruj.uj.edu.pl/server/api/core/bitstreams/cc7a0787-d78e-4ded-9183-59b4073f8323/content).

The version of record defines a signed \(k\)-edge-coloring by incidence
colors from \(M_k\), the edge relation

\[
f(u:uv)=-\sigma(uv)f(v:uv),
\]

and pairwise distinct incidence colors at each vertex (page 765).  On page
785, Conjecture 26 states that for an arbitrary signature on two copies of
\(K_n\) joined by one edge,

\[
\chi'(S)=\Delta(S)=n.
\]

Thus the MathDB record represents the published quantifiers correctly,
apart from notation lost by its parser.

The live MathDB API was queried again on 19 August 2026.  Record #361027
still reported `status=open`, `post_type=open_problem`, and the same arXiv
source.  That database state is only a screening signal; the primary-source
and forward searches below are the substantive status check.

## Search for a later resolution

Exact-title, exact-conjecture-sentence, author-name, DOI, and combinations
of `signed complete graph`, `two cliques`, and `chromatic index` were
searched.  The current arXiv v3 and the 2025 version of record still contain
the conjecture.  The authors' current publication listing contains the 2025
paper but no later signed-edge-coloring paper resolving Conjecture 26.

The closest indexed works located were the authors' earlier
[class-1/class-2 paper](https://arxiv.org/abs/2205.15425), which develops the
general decomposition criterion, and Richard Behr's foundational
[signed-edge-coloring paper](https://arxiv.org/abs/1807.11465), which proves
the signed Vizing bound.  Neither contains this two-clique construction.
No public proof or counterexample to Conjecture 26 was located through the
audit date.

## Resolution supplied here

The solution uses only a standard Walecki Hamilton decomposition and a
direct coloring of signed paths.  For even \(n\), each clique decomposes into
\(n/2\) Hamilton paths.  For odd \(n\), it decomposes into
\((n-1)/2\) Hamilton paths plus a near-perfect matching that can be chosen
to miss the joining vertex.  Assigning a separate nonzero color pair to each
path and color zero to the matching makes the joining colors compatible for
either bridge sign.

**Status conclusion.** The 2025 primary source explicitly records the claim
as open, and no later public resolution was found in the searches above.
The accompanying dossier gives a complete constructive proof.  This is a
literature-search conclusion, not a claim that unindexed or unpublished
prior work cannot exist.
