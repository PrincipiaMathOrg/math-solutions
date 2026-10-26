# Proof audit: MathDB 356988

Mathematical result: exact counterexamples to coordinate monotonicity
and to either direction of spread monotonicity, using the intended
Definition 2.4 in the current source.

1. **Scope.** Both examples use uniform vertex personalization and
   connected, simple, undirected graphs with minimum degree two.
   Both damping parameters lie strictly between 0 and 1. Every finite
   comparison uses strictly positive backtracking parameters.
2. **Normalization and projection.** Teleportation to oriented edge
   (i,j) has mass 1/(n d_i). The transition column for (h,i) is
   normalized by d_i−1+mu. Vertex scores sum stationary masses over
   outgoing edges, precisely the source's matrix T projection.
   This avoids confusing the tail projection with the head projection.
3. **Stationary certificate.** The house graph has six oriented-edge
   orbits, each of size two. The theta graph has five orbits, of sizes
   2,4,2,2,4. Every table entry is positive for mu >= 0; the weighted
   sums are one. Direct substitution verifies all stationary equations.
   The stochastic transition has induced one-norm one, so damping
   makes the Neumann series converge and proves uniqueness.
4. **House graph.** The roof scores at mu=1/2,1,2 have respective
   values 8356/47445, 22/125, 3134/17805. The differences above the
   middle value are 142/1186125 and 8/445125. This rules out both
   coordinate directions. The derivative quartic has one sign change
   and changes sign between zero and infinity, proving one positive
   critical point.
5. **Theta graph.** Explicit positive rational differences establish
   the order A > B > C for all mu >= 0; no maximum/minimum switching
   is assumed. The derivative of the spread is
   −855(mu−1)(19mu+221)/(2E(mu)^2). Thus it increases before 1 and
   decreases after 1. Exact three-point differences also certify this.
6. **No transcription-based result.** The current displayed range
   inequality increases, while the original motivating prose describes
   shrinkage. The theta example disproves both possible directions,
   and the house example independently refutes the coordinate claim.
   Unrelated source transposes and code implementation details are not
   used to claim a counterexample.

Four exact groups passed with SymPy 1.14.0 and Python Fraction arithmetic:
the full source-matrix residuals for all 26 oriented edges; score, ordering,
derivative and exact-gap identities; 52 independent rational Gaussian
eliminations; and six finite Neumann-series interval certificates. The
last group uses the geometric tail bound epsilon^(N+1), with N=70 for
the house graph and N=300 for the theta graph. It separates all required
strict inequalities without using a linear solver. No floating point
is used in the verifier. The initial numerical search was exploratory.

Task 1 is the complete disproof; exactly four subsequent tasks propose
follow-ups. Review is by the authoring agent only. The final-source
eligibility limitation is distinct from the proved mathematical result
and is retained explicitly in the package.
