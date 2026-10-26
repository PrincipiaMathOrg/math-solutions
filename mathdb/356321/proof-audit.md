# Proof audit

Date: 21 September 2026. Full intended theorem; source review pending.

1. **Exact target.** The degree is exactly \(n\). Raising the degree to obtain positivity would not suffice. The basis is the binomial Bernstein basis summing to one.
2. **Boundary scope.** The \(n=1\) coefficient row is \((2,0)\). This disproves a literal assertion of strict positivity for every positive \(n\), but the package proves the intended all-degree nonnegative theorem and strict positivity in every degree \(n\ge2\). The endpoint correction is not counted as a research result.
3. **Bernoulli normalization.** The proof uses \(B_1=-1/2\) and \(b_n=B_n/n!\). The uniform bound \(|(2\pi)^\ell b_\ell(0)|\le4\) treats \(\ell=0,1\), positive odd indices, and positive even indices separately.
4. **Basis conversion.** Counting successful trial subsets proves \(x^j=\sum_r\binom rj/\binom nj\,\mathcal B_{r,n}(x)\). All ratios lie in \([0,1]\), including the \(j=0\) case.
5. **Analytic tail.** Summing the power-coefficient majorant gives \(|c_{n,r}-1|\le4e^{2\pi}\pi^{-n}\). For every \(n\ge9\), \(3<\pi<7/2\) and \(e<3\) imply a strict bound below \(4/9\). There is no asymptotic extrapolation.
6. **Finite certificate.** The proof displays all 44 coefficients for \(1\le n\le8\), after multiplication by explicit positive denominators. The necessary Bernoulli numbers are displayed as well. Every entry is positive except the single boundary zero at \(n=1\).
7. **Mixture interpretation.** These coefficients sum to \(n+1\), not one. Division by \(n+1\) gives weights for normalized beta densities. The normalization and reflection checks passed exactly.
8. **Attribution and review.** Classical Bernoulli and Bernstein identities are attributed. This target concerns positivity at degree \(n\); the separate 356320 package proves approximation at degree \(2n-1\). No additional follow-up is claimed solved. Review is by the authoring agent only.
