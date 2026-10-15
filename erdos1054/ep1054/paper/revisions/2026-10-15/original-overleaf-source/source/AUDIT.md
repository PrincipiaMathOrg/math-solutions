# Proof and citation audit

**Document audited:** `sections/principia-math.tex`  
**Date:** July 19, 2026  
**Verdict:** After the revisions recorded below, I found no mathematical gap in the section. The two theorems and the corollary follow from the stated analytic inputs.

## Corrections made during the audit

1. **Removed an inappropriate historical citation.** The former Alaoglu--Erdős citation does not source the nondivisibility estimate for `sigma(n)` used here; their 1944 note concerns iteration questions involving arithmetic functions. The revised section proves the required estimate from the Hall--Tenenbaum mean-value theorem and Siegel--Walfisz, and cites those sources directly.
2. **Made the multiplicative majorant unambiguous.** The function `h_q` is now defined on every prime power, with value zero exactly when the relevant prime occurs to the first power.
3. **Expanded the mean-value argument.** The Euler product, the bounded contribution of primes outside the progression, and the decay at primes congruent to `-1 mod q` are now written out.
4. **Added precise source locators.** The mean-value estimate is cited as Tenenbaum, Theorem III.3.5; Siegel--Walfisz as Chapter II.8; the standard prime estimates as Chapter I.1; and the Goldbach exceptional-set result as Montgomery--Vaughan, Theorem 1.
5. **Expanded compressed proof transitions.** The revised text now displays the common-multiple count in the high-moment lemma, defines the subset variables `y_S` explicitly, writes out the fixed-level parameter balance, gives the periodic count for the sifted interval, proves `C_k=E^{o(1)}`, and derives the final iterated-logarithm exponent explicitly.
6. **Added stable links to the actual sources.** The bibliography uses the DOI for the Montgomery--Vaughan article and the AMS DOI for Tenenbaum's book.

## Mathematical audit, step by step

### 1. Uniform nondivisibility of `sigma(n)`

- If a prime `p = -1 (mod q)` occurs exactly once in `n`, then `q | sigma(p) | sigma(n)`.
- The multiplicative function `h_q` therefore majorizes the indicator of `q` not dividing `sigma(n)`.
- Tenenbaum's mean-value theorem applies with constants independent of `q`: the prime condition follows from Chebyshev's estimate, and the prime-power tail converges.
- For primes in the progression, the local factor is at most `exp(-1/(2p))`; all other local factors contribute a bounded product.
- Siegel--Walfisz is used only where `q <= (log t)^(1/2)`, ensured by taking `t >= exp(Cq^2)`.
- Summing over dyadic intervals yields the required reciprocal-prime lower bound uniformly for `q <= c log_2 y/log_3 y`.
- The parity statement `sigma(n)` odd iff `n` is a square or twice a square gives the `q=2` estimate.

**Status:** correct.

### 2. Almost-everywhere representability

Montgomery and Vaughan prove that the number of even integers up to `X` not expressible as a sum of two primes is `O(X^(1-eta))`. For odd `N`, apply this to `N-1`. Equal-prime representations `N-1=2p` account for only `O(X/log X)` values. Otherwise `N-1=p+q` with distinct primes `p<q`, and the first three divisors of `pq` are `1,p,q`, so `N=1+p+q` is represented.

**Status:** correct.

### 3. Divisor reflection and the bounded-cofactor congruence

- The involution `r -> ed/r` bijects divisors `r >= e` of `ed` with divisors at most `d`, proving `F_e(d)=ed g_e(ed)`.
- Complementary divisors give
  `sigma(m)-N = m sum_{r|m, r<e} 1/r`.
- The empty and singleton cases are valid separately.
- In the remaining case, with `M=lcm(D)` and `C=sum M/r`, one has `M|m`, `C>=2`, and `C<e Lambda_e`; any prime divisor of `C` yields the congruence.
- For `e<=E` and `N<=X`, the final divisor satisfies `d<=N`, hence `m=ed<=EX`. The primorial coprimality condition then converts the congruence into a failure of divisibility of `sigma(m)`, and overcounting witnessing pairs gives the stated bound.

**Status:** correct.

### 4. High-moment estimate for large cofactors

- Expanding `g_e(m)^k` and counting common multiples gives the displayed least-common-multiple sum.
- The inequality extracting `E^(1-k)` follows from `r_1...r_k >= e^k`.
- The prime-adic subset decomposition is exact for tuples `(x_0,...,x_k)`; dropping the nesting restrictions only enlarges the sum.
- The resulting independent sums give the stated zeta-product constant `C_k`.
- The bound on `log C_k` follows from `zeta(1+u)<=1+1/u` and the sum of the binomial coefficients.
- Markov's inequality applied to witnessing pairs `(m,e)` gives the large-cofactor counting estimate with the correct power `A^(k+1)`.

**Status:** correct.

### 5. Fixed-level theorem

- Mertens and the Chebyshev bound `log Lambda_E << E` give sifted density `delta_E >> 1/E`.
- For fixed `E`, the bounded-cofactor set is `o_E(X)` by the uniform nondivisibility lemma.
- Choosing `alpha=(k+1)/(k-2)` and `E` of order `A^alpha` balances the large-cofactor term against the sifted density because `alpha(k-2)=k+1`.
- The Goldbach exceptional set is negligible once `A` and `epsilon` are fixed.
- The surviving represented integers have no representation of size at most `AN`, yielding lower density `>>_epsilon A^(-1-epsilon)`.

**Status:** correct.

### 6. Growing-level theorem

- With `P` of order `log_2 X/log_3 X`, Mertens gives `phi(Q)/Q` of order `1/log_3 X`, and Chebyshev gives `Q=X^(o(1))`.
- Periodicity modulo `Q` yields the sifted-interval count with error `O(Q)`.
- Choosing `E` as a sufficiently small constant multiple of `log_3 X` ensures `E Lambda_E<P`, using `log Lambda_E <= C_Lambda E`.
- The uniform `sigma` estimate makes all bounded cofactors negligible compared with `X/log_3 X`.
- The chosen moment order satisfies `C_k=E^(o(1))`; with `G=E^(1-4/(k+1))`, the large-cofactor set is `E^(-2+o(1))X`, also negligible.
- The Goldbach exceptional set is negligible on the same scale.
- The final logarithmic calculation gives
  `G >= (log_3 N)^(1-C/log_5 N)` uniformly for `X/2<N<=X`.

**Status:** correct.

### 7. Corollary

On the set supplied by the growing-level theorem, division by `N(log_3 N)^(1-epsilon)` leaves the factor `(log_3 N)^(epsilon-C/log_5 N)`, which tends to infinity. This proves both the counting statement and the limsup statement.

**Status:** correct.

## Citation audit

| Citation | Claim supported | Audit result |
|---|---|---|
| G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, 3rd ed., AMS, 2015, DOI `10.1090/gsm/163` | Hall--Tenenbaum mean value (Theorem III.3.5); primes in arithmetic progressions/Siegel--Walfisz (Chapter II.8); Mertens and Chebyshev estimates, including `log lcm(1,...,u) << u` (Chapter I.1) | Correct and appropriately pinpointed. The DOI resolves to the AMS book. |
| H. L. Montgomery and R. C. Vaughan, *The exceptional set in Goldbach's problem*, Acta Arith. 27 (1975), 353--370, DOI `10.4064/aa-27-1-353-370` | Power-saving exceptional set for binary Goldbach (Theorem 1) | Correct. The DOI resolves to the original journal article, whose Theorem 1 states `E(X)<X^(1-delta)` for some effective `delta>0`. |
| Former Alaoglu--Erdős reference | Formerly attached to the `sigma(n)` divisibility estimate | Removed. It was not the right source for the estimate used in this proof. |

The attribution of the divisor-prefix congruence to Terence Tao is a personal-communication attribution rather than an outsourced mathematical step: the lemma is proved in full in the section, so no bibliographic source is required for correctness.

## Build and presentation checks

- The project compiles cleanly with two runs of `pdflatex`.
- No undefined references, undefined citations, overfull boxes, or LaTeX warnings remain.
- The seven-page PDF was rendered and visually inspected page by page.
- The bibliography contains only the two sources actually used in this section.
