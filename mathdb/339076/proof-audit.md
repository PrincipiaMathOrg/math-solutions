# Proof audit: 339076

1. The moment recurrence is precisely the one in Appendix A of
   arXiv:1805.00113v1 and Cigler's equation (37).
2. Cigler equations (39)--(40) supply the zero- and one-shift
   determinants. These established results are explicitly credited.
3. Desnanot--Jacobi on the unshifted matrix of size n+1 gives the
   correctly signed condensation identity, also for n=1.
4. Division uses only the zero-shift determinants, which are nonzero
   monomials over Q(q). Periodic zeros in the one-shift determinants
   therefore cause no gap.
5. Normalizing by the zero-shift determinant of size n+1 gives
   E_n-E_(n-1) = kappa_n^2 q^(-n). The initial value E_0=1 includes
   the constant summand, which is essential.
6. The exact six-periodic kappa sequence has a zero precisely at
   indices congruent to 2 modulo 3. Telescoping gives the all-n formula.
7. Reversing the permitted indices yields all three residue classes,
   the nonnegative monomial exponent, and a polynomial with constant
   term one. The displayed exponent is thus the exact valuation.
8. Polynomial identity extends the result to q=0 and every complex
   parameter, even though the intermediate derivation used Q(q).
9. The printed multiple-of-three branch omits the constant term.
   The all-size evaluation is the mathematical result; no credit is
   awarded merely for exposing this printing error.

The independent exact determinant computations use the defining
moment recurrence, not the conjectured determinant formula. Row pivoting
handles the zero one-shift determinants. Finite checks support the proof
but do not replace its universal argument.

This is an authoring-agent audit, without independent peer review.
Source eligibility remains pending and campaign credit is zero.
