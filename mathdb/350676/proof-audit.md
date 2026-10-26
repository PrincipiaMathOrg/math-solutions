# Proof audit

The target is the equivalence in Conjecture 1 on page 18 of Contreras–Tawfeek, arXiv:2105.05388v2. This audit concerns that completely read preprint; it does not assert that the unread journal version retains precisely the same formulation.

The source defines its top boundary Laplacian as `B B^T`, acting on codimension-one faces, rather than the full combinatorial Hodge Laplacian. The proof uses that exact convention and the source's definition of `M_l`: only top and codimension-one cells are paired; all lower cells remain critical.

For the complex with facets `S union {u_j}`, there are `r` top faces and `1+rd` codimension-one faces. Distinct columns of the boundary matrix share only the row indexed by `S`. Their orientations can all be chosen positive in that row, so their Gram matrix is `d I + J`. Its positive eigenvalues and the remaining nullity give the determinant in the theorem.

The top incidence graph is a tree with a common center, `r` intermediate vertices and `d` private leaves at each intermediate vertex. Every matching is acyclic. No lower Hasse level can enter a directed cycle, since there are no upward matched edges in those levels. Assigning values that strictly decrease along arrows constructs a discrete Morse function; the lower critical cells can be assigned smaller values increasing with their dimensions. Thus the counted matchings are exactly the gradient equivalence classes in the source.

After choosing `i` matched top faces, the cases in which the common row is unused or used contribute `d^i` and `i d^(i-1)` respectively. These cases are disjoint and exhaustive. The binomial theorem gives exactly the same polynomial as the Laplacian. The common face has degree `r >= 3`, ruling out pseudomanifold status. The complex is finite, connected, pure and strongly connected through codimension-one faces; the counterexample does not depend on the dimension-one special case, a disconnected union, a transcription error, or solely on boundary conventions.

For the five-vertex example, exact verification independently constructs the 7-by-3 boundary matrix, computes the full 7-by-7 Laplacian characteristic polynomial, and enumerates all 54 top-level matchings. The counts by number of matched pairs are `(1,9,24,20)`. Four further examples check the same construction in different dimensions and sizes. These finite checks are supplementary certificates; the written proof covers all `d >= 2, r >= 3`.

The additional incidence-forest result follows from expansion into principal minors and Cauchy–Binet: each square submatrix has at most one perfect matching, hence determinant zero or plus/minus one. This standard matching argument is fully proved and attributed as classical linear algebra, without a novelty claim for Cauchy–Binet or matching enumeration.

Logical scope: one counterexample disproves the equivalence, and no proof of its separate forward implication is asserted. All mathematical review was by the authoring agent. There was no independent peer review or formal proof-assistant verification.
