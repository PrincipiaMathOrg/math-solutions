# Proof audit

The result is a complete counterexample to Conjecture 2.4.1 in arXiv:1307.0805v3, p. 4. The current primary was read in all nine pages. Algorithm 1, p. 3, supplies the Fourier/slice-SVD/inverse-Fourier definition. The conjectured functional is the sum of Euclidean norms of the diagonal singular tubes.

All inputs are real rational tensors of the permitted shape. Rank-deficient tensors belong to a norm's domain; the conjecture imposes no invertibility assumption. Each frequency uses ordinary sorted nonnegative singular values. Explicit orthogonal factors reconstruct the example and give real t-orthogonal factors after the length-two inverse transform. The repeated singular values of `2I` have a fixed sorted list, so freedom to choose singular vectors does not affect the calculation.

The inverse-transform normalization is included explicitly: a tube corresponding to frequency values `u,v` has squared Euclidean norm `(u*u+v*v)/2`. Thus both inputs have value `sqrt(5/2)`, while the sum has singular tubes `(2,0)` and `(1,1)` and value `2+sqrt(2)`. Squaring the positive sides reduces the strict violation to `sqrt(2)>1`.

Positive homogeneity turns the same inequality into a strict midpoint-convexity failure. It persists after arbitrary positive scaling and hence inside every norm ball about zero. This disposes of the convex-relaxation clause on the usual bounded domains without exploiting the source's unspecified domain.

The source's separate TNN is a different function. Its values are 3, 3 and 6 on this example, so its triangle inequality is respected. The proof does not rely on the source's nearby TNN/TTN prose typo or on the later omission of the conjecture.

The verifier recomputes sorted singular spectra from exact Gram-matrix eigenvalues, checks the real circular-convolution t-products, and certifies the strict algebraic inequality and an explicit scaling inside the Frobenius ball. These calculations supplement the displayed finite exact proof. Review is by the authoring agent only.
