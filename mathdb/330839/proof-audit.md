# Proof audit

1. Both original source versions define the same polynomial recurrence. The published Conjecture 4.1 asserts nonreal zeros plus coordinate separation. The negative-real-zero counterexample does not exploit the narrower, unintended reading of imaginary as purely imaginary.
2. Dividing T_n by x gives the displayed P_n recurrence, with P_n(0)=1 and P_n(-1)=(2n-3)!!>0.
3. Exact recurrence arithmetic gives all 13 coefficients of P_7. Substituting -1/20 gives -316770843280059/4096000000000000, strictly negative. Two intermediate-value crossings lie in (-1,0).
4. A negative minimum on [-1,0] is interior and has derivative zero. The coefficient 1+a+(2n-1)a^2 is strictly positive there, so the next polynomial is also negative at that point. Positive endpoint values persist. This induction proves the assertion for every n>=7.
5. The source's symmetry result, also immediate from the coefficient recurrence, supplies reciprocal roots below -1. The four roots are distinct; their simplicity for every n is not asserted.
6. This refutes the universal conjunction without asserting an answer to every possible reformulation of coordinate separation. Negative real zeros remain compatible with the earlier Hurwitz theorem, which is explicitly credited.

Three exact groups passed: recurrence and rational sign; direct enumeration of 135135 order-seven dual Stirling permutations; Sturm counts for n=2 through 7 and reciprocal-coefficient checks. The counts additionally locate the first real-root failure at n=7. The infinite extension uses the written induction. Both PDF pages visually reviewed with no layout warnings. Authoring-agent review only.
