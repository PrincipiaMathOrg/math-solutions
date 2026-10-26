# Proof audit

Result: the lower inequality in MathDB 335189 is false at nu = 30,
x = 1. It is also false near zero at each real order nu >= 28.
This refutes the universal conjecture in the inspected primary
preprint, with its actual intended hypotheses.

1. The normalized entire series fixes all conventions, including the
   real even extension for negative x. Both logarithms used in the
   local argument are analytic and real near zero.
2. The Bessel ground state on (0, 1) gives an upper bound on its
   eigenvalue, not a lower bound. The written proof derives the
   identity by integration by parts and verifies both endpoints
   for the trial function r^nu (1-r)^3.
3. The energy cross term is an exact derivative. The beta integrals
   give U_nu = 3(2nu+7)(2nu+8)/10. The difference from the
   Taylor obstruction threshold has strictly positive coefficients
   after the substitution nu = 28+s.
4. The first nonzero logarithmic difference coefficient is negative.
   Analyticity gives a whole punctured interval of counterexamples
   at each order; no inference about infinitely many inputs is made
   from experimental samples.
5. For the explicit pair (30,1), alternating-series remainders bound
   the numerator above and the denominator below. The denominator
   bound is positive. The same series proves j_(30,1) > 1, so this
   pair is in the conjectured domain.
6. A rational upper bound for the ratio, the elementary inequality
   log(1+d) <= d-d^2/2+d^3/3, and a positive two-term lower
   bound for the proposed logarithm prove a gap exceeding 7/10^10.
   Every comparison is exact; no Bessel zero is approximated.
7. The upper bound and its optimal exponent are explicitly credited
   as prior results recorded by the source. They earn no credit.
8. Task 1 contains the complete disproof. Tasks 2--5 are four
   proposed directions, not additional claimed solutions.

Validation: 19 exact symbolic/rational checks passed; Tectonic built
the PDF; all four pages were visually inspected with no clipping.
The verifier checks the algebra, while the written proof supplies
the infinite-series and endpoint reasoning.

Review scope: authoring-agent verification only. Complete journal
source and prior-claim eligibility remain pending as described in
the literature audit.
