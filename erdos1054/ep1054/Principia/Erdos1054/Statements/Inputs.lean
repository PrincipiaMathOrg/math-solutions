/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Defs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) — the external inputs, as named `Prop`s

Every result the proofs of `Campaigns/Erdos-1054/collab-paper/EP1054.tex` take from outside the
paper is stated here as a `def … : Prop`. **Nothing here is asserted**: consumers take these as
hypotheses, so the spine records exactly which outside facts each paper result rests on.

Three groups of *trusted* inputs, and one group that is **not** trusted:

* `Cite_*` — specific research-literature results (a citation in the paper's bibliography).
* `Std_*`  — standard textbook facts the proofs use without proof, which we intend to prove or port.
* `Comp_*` — the finite computations the paper attributes to the verifier `verify.rs`
  (`[FraitureVerifier]`); they are external inputs of a third kind.
* Section (4), **derived inputs** — named `Prop`s that consumers cite, kept under their original
  names so no reference breaks, but which **follow from the trusted inputs above plus Mathlib** and
  are therefore proof-phase obligations, *not* part of the trusted base. Each carries
  `-- deps: DERIVED from …`. The trusted base is sections (1)–(3) only.

**Transcription policy.** Each input is stated in the *weakest* form the paper actually uses,
restricted to the instances it applies it to; a too-strong transcription would be silently false
and make every consumer vacuous. Each docstring records the source and locator, the paper's own
sentence where the input is used (with its `EP1054.tex` line), and whether the source itself was
checked (`SOURCE CHECKED`) or only the paper's paraphrase (`PARAPHRASE ONLY`). Where the Lean form
differs from the source by a harmless re-parametrisation, the docstring says so.

**Pinned-Mathlib audit (v4.31.0, 2026-09-25).** Mathlib has **no** prime number theorem, Mertens'
second or third theorem, Siegel–Walfisz, Brun–Titchmarsh, divisor bound `τ(n) = n^{o(1)}`, or
two-dimensional sieve bound; those are `Std_*` below (Mertens' first theorem, in the form used, is
derived: section 4). The following standard inputs **are** in the pinned Mathlib
and are deliberately *not* restated (consumers should use these names directly):

* Bertrand (`EP1054.tex` lines 790–792, 925–928): `Nat.exists_prime_lt_and_le_two_mul`
  (`n ≠ 0 → ∃ p, p.Prime ∧ n < p ∧ p ≤ 2 * n`). The paper's real, strict form "a prime `ℓ` with
  `x < ℓ < 2x`" (line 926) follows for `x > 1` by applying it at `⌊x⌋₊` (a prime `≤ 2n` equals
  `2n` only when `n = 1`).
* Chebyshev `θ(x) ≪ x`, `log(y#) ≪ y` (line 365): `Chebyshev.theta_le_log4_mul_x`,
  `Chebyshev.theta_eq_log_primorial`, `primorial_le_four_pow`. Note `primorialR y` is
  `primorial ⌊y⌋₊` by definition.
* `log Λ(u) = ψ(u) ≤ C_Λ u` (line 366): `Chebyshev.psi_eq_log_lcmUpto` together with
  `Chebyshev.psi_le_const_mul_self` (`ψ x ≤ (log 4 + 4) x`). `lcmUpTo u` in `Defs` has the same
  body as `Nat.lcmUpto ⌊u⌋₊`.
* Dirichlet's theorem (lines 2310–2312, 2332–2334): `Nat.forall_exists_prime_gt_and_modEq`,
  `Nat.infinite_setOf_prime_and_eq_mod`; the `≡ 1` case also elementarily as
  `Nat.exists_prime_gt_modEq_one`.
* Lifting the exponent (line 2318): `padicValNat.pow_sub_pow`, `Nat.emultiplicity_pow_sub_pow`,
  `Nat.two_pow_sub_pow`.
* Divergence of `∑ 1/p`, so `∏_{p ≤ z} (1 + 1/p)` is unbounded (line 1229):
  `Nat.Primes.not_summable_one_div`.
* `ζ(2) = π²/6` and `π < 22/7` (lines 3104, 3156): `hasSum_zeta_two`, `Real.pi_lt_d4`.
* `ζ(1 + u) ≤ 1 + 1/u` for `u > 0` (lines 625–627; formerly the input `Std_zeta_le`, removed
  2026-09-25): `ZetaAsymptotics.zeta_limit_aux1` (`1 < s → (∑' n, 1/(n+1)^s) − 1/(s−1) =
  1 − s · termTSum s`) with `ZetaAsymptotics.term_nonneg` (so `termTSum s ≥ 0` by `tsum_nonneg`),
  at `s = 1 + u`. The derivation of `∀ u > 0, ∑' n : ℕ, ((n + 1)^(1+u))⁻¹ ≤ 1 + 1/u` from these was
  compiled (ERRORS=0, 9 lines: `simp [one_div]`, `nlinarith`).
* Partial summation (lines 1383, 1446, 1788, 1941): `sum_mul_eq_sub_integral_mul` (`AbelSummation`).
* The measure theory of §7 — portmanteau (`MeasureTheory.tendsto_measure_of_null_frontier` and the
  `Portmanteau` file), Prokhorov (`Mathlib.MeasureTheory.Measure.Prokhorov`), Lipschitz images of
  null sets (`LipschitzOnWith.hausdorffMeasure_image_le`), Tonelli, Fatou, inner regularity, and
  Jensen (line 3118).
-/

namespace Principia.Erdos1054

open Finset Filter
open scoped Topology

/-! ## Helper objects used only to state the inputs -/

/-- `π(x; q, a) = #{p ≤ x : p prime, p ≡ a (mod q)}` for real `x`; the residue is given by a
natural representative `a`. For `q = 1` this is `π(x)`. -/
noncomputable def piAP (x : ℝ) (q a : ℕ) : ℕ :=
  ((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card

/-- `y(n) = log log n / log log log n`, the Luca–Pomerance smoothness level (LP §2: "For each
large number `n`, let `y = y(n) = log log n / log log log n`"; EP1054.tex line 1317).
Meaningful (and increasing in `n`) only for `n > e^{e^e} ≈ 3.8·10^6`. Below that,
`log log log n ≤ 1` and the formula is non-monotone: it blows up just above `e^e`
(e.g. `yLP 16 ≈ 52`), and `L/log L` attains its minimum `e` at `L = log log n = e`, i.e.
`n = e^{e^e}`. Every density-zero input absorbs this finite range. **Consumers that use `y`
pointwise or monotonically** (EP1054.tex line 1424, `y(k) = y(X) + O(1/log log log X)`;
line 1463, `Y ≤ y(t) ≤ y(X)`) must restrict to arguments `> e^{e^e}`, which "for `X`
sufficiently large" provides. -/
noncomputable def yLP (n : ℕ) : ℝ := logIt 2 (n : ℝ) / logIt 3 (n : ℝ)

/-! ## (1) `Cite_*` — research-literature inputs -/

-- deps: external — Montgomery–Vaughan, Acta Arith. 27 (1975), main theorem.
-- used by: lem:analytic-odd-representability (line 663), prop:theta-two (line 2599).
/-- **Montgomery–Vaughan, exceptional set in Goldbach's problem** `[MVGoldbach]`.
Paper, line 663: "The theorem of Montgomery and Vaughan asserts that at most `O(X^{1-c})` even
integers at most `X` fail to be sums of two primes." Line 2599 uses the same statement with `κ`.

Encoding: `∃ c > 0, ∃ C, ∀ X ≥ 1, #{1 ≤ n ≤ X : n even, n ≠ p + q for all primes p, q} ≤ C X^{1-c}`;
the two primes may coincide ("sums of two primes"). The constant `C` absorbs `n = 2` and small `X`.
PARAPHRASE ONLY (the MV theorem is classical: `E(X) ≪ X^{1-δ}` for an effective `δ > 0`). -/
def Cite_MV_exceptional : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X →
    (cnt {n : ℕ | Even n ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q} X : ℝ) ≤ C * X ^ (1 - c)

-- deps: external — Luca–Pomerance, Acta Arith. 168 (2015), Lemma 2.1 and the proof of its (4).
-- used by: lem:LP-inputs (i)–(iv) (lines 1316–1325), hence lem:sv-regular (line 1439),
--          prop:sv-second-moment (lines 1567, 1690–1693, 1741–1742, 1754).
/-- **Luca–Pomerance, Lemma 2.1** `[LucaPomerance, Lemma 2.1]`, in the form of the paper's
`lem:LP-inputs` (i)–(iv), EP1054.tex lines 1317–1325:
"Put `y(n) = log log n / log log log n`. Outside a set of integers of asymptotic density zero, the
following hold: (i) `v_p(σ(n)) > v_p(n)` for every prime `p ≤ y(n)`;
(ii) `P^+(gcd(n, σ(n))) ≤ y(n)`; (iii) `σ(n)/gcd(n, σ(n))` is divisible by every prime
`p ≤ y(n)`; (iv) every prime factor of `s(n)/gcd(n, σ(n))` exceeds `y(n)`." Line 1338: "The
first four properties are the conclusions of [LP, Lemma 2.1], with the valuation inequality in
(i) stated explicitly in the proof of its part (4)."

SOURCE CHECKED (LP, Dartmouth preprint `LucaPomeranceAA2.pdf`): Lemma 2.1 reads "On a set of
asymptotic density 1 we have (1) `p^{2a} ∣ σ(n)` for every prime power `p^a ≤ y`, (2)
`P(gcd(n, σ(n))) ≤ y`, (3) `σ(n)/gcd(n, σ(n))` is divisible by every prime `p ≤ y`, (4) every prime
factor of `s(n)/gcd(n, σ(n))` exceeds `y`", with `y = y(n)`; the proof of (4) opens "we may assume
that for each prime `p ≤ y`, we have `v_p(σ(n)) > v_p(n)`" (justified by (1) and the proof of (3)).

Encoding: one exceptional set `E` for all four parts (a finite union of density-zero sets);
`v_p` is `Nat.factorization`; `P^+(m) ≤ y` is `IsSmooth y m` (`P^+(1) = 1` is harmless);
"every prime factor exceeds `y`" is `IsRough y`. The divisions are exact
(`gcd ∣ σ(n)`, `gcd ∣ s(n)`). -/
def Cite_LP_Lemma21 : Prop :=
  ∃ E : Set ℕ, DensZero E ∧ ∀ n : ℕ, n ∉ E →
    (∀ p : ℕ, p.Prime → (p : ℝ) ≤ yLP n → n.factorization p < (sig n).factorization p) ∧
    IsSmooth (yLP n) (Nat.gcd n (sig n)) ∧
    (∀ p : ℕ, p.Prime → (p : ℝ) ≤ yLP n → p ∣ sig n / Nat.gcd n (sig n)) ∧
    IsRough (yLP n) (aliquot n / Nat.gcd n (sig n))

-- deps: external — Luca–Pomerance 2015, Lemma 2.2 (only the displayed range is used).
-- used by: lem:LP-inputs square-divisibility (lines 1326–1330), lem:sv-regular (line 1466),
--          prop:sv-second-moment ("h is squarefree", lines 1740–1747).
/-- **Luca–Pomerance, Lemma 2.2, in the range used** `[LucaPomerance, Lemma 2.2]`.
Paper, `lem:LP-inputs`, lines 1326–1330: "If in addition `P^+(n) > n^{7/9}`, then, outside another
density-zero set, `y(n) < q_0 ≤ n^{10/27}`, `q_0` prime `⟹ q_0^2 ∤ s(n)`." Line 1341: "The
square-divisibility assertion is the consequence of [LP, Lemma 2.2] needed here; we use it only in
the displayed range."

SOURCE CHECKED: LP Lemma 2.2 reads "The set of numbers `n` with `P(n) > n^{1/2}` and `π^2 ∣ s(n)`
for some prime `π > y(n)` has asymptotic density 0." The statement below is strictly weaker
(`n^{7/9} > n^{1/2}` and `q_0 ≤ n^{10/27}`), exactly as the paper restricts it.

Encoding: `P^+(n) > n^{7/9}` is `∃ p ∈ n.primeFactors, n^{7/9} < p` (false for `n = 1`). -/
def Cite_LP_Lemma22_range : Prop :=
  ∃ E : Set ℕ, DensZero E ∧ ∀ n : ℕ, n ∉ E →
    (∃ p ∈ n.primeFactors, (n : ℝ) ^ ((7 : ℝ) / 9) < (p : ℝ)) →
    ∀ q₀ : ℕ, q₀.Prime → yLP n < (q₀ : ℝ) → (q₀ : ℝ) ≤ (n : ℝ) ^ ((10 : ℝ) / 27) →
      ¬ q₀ ^ 2 ∣ aliquot n

-- deps: external — Luca–Pomerance 2015, Lemma 2.5 (via De Koninck–Luca, Lemma 5).
-- used by: lem:LP-inputs final assertion (lines 1331–1334), lem:sv-regular (eq:sv-LP25,
--          lines 1411–1413, 1467), prop:sv-second-moment (lines 1640–1646).
/-- **Luca–Pomerance, Lemma 2.5** `[LucaPomerance, Lemma 2.5]` — a sum over **prime** divisors.
Paper, lines 1331–1334: "Finally, outside a set of asymptotic density zero,
`∑_{a ∣ σ(n), a > (log log n)^2} 1/a ≤ 1`." Line 1343: "The reciprocal-divisor estimate is
[LP, Lemma 2.5]."

SOURCE CHECKED (LP, Dartmouth preprint `LucaPomeranceAA2.pdf`, re-read 2026-09-25): Lemma 2.5
reads "On a set of integers `n` of asymptotic density 1 we have
`∑_{r ∣ σ(n), r > (log log n)^2} 1/r ≤ 1`", and LP §2 fixes the notation: "We have the letters
`p, q, r, π`, with or without dashes or subscripts representing prime numbers." So `r` is a
**prime**, and the statement below sums over the prime factors of `σ(n)`.

**Paper erratum.** EP1054.tex writes the sum over *all* divisors `a ∣ σ(n)` (lines 1331–1334, and
again `eq:sv-LP25`, lines 1411–1413). That version is **false**, and it contradicts
`Cite_LP_Lemma21` (iii): outside a density-zero set every prime `≤ y(n)` divides `σ(n)`, and the
divisors `m p₁ p₂ p₃` of `σ(n)` (`m` a squarefree product of primes `≤ y^{1/10}`,
`y^{7/10} < p₁ < p₂ < p₃ ≤ y`) all exceed `(log log n)^2` and have reciprocal sum `≫ log y(n) → ∞`.
Both places should read "`q_0 ∣ σ(n)`, `q_0` prime, `q_0 > (log log n)^2`" (respectively
`(log log X)^2`). The only use site needs just the prime form: lines 1640–1642, "The primes
removed from `A_{3,2}` divide `σ(n)` and exceed `(log log X)^2`, so (eq:sv-LP25) gives
`A_{3,2}/φ(A_{3,2}) ≪ A'_{3,2}/φ(A'_{3,2})`", via `∏ p/(p−1) ≤ exp(2 ∑ 1/p) ≤ e^2`; LP use it the
same way just after (3.8) ("By Lemma 2.5, we may assume that `A_{3,2}/φ(A_{3,2}) ≪
A'_{3,2}/φ(A'_{3,2})`"). (The paper's later threshold `(log log X)^2 ≥ (log log n)^2` for `n ≤ X`
only shrinks the sum.)

Encoding: `r` runs over `(sig n).primeFactors` (empty for `n = 0`, where `σ 0 = 0`). -/
def Cite_LP_Lemma25 : Prop :=
  ∃ E : Set ℕ, DensZero E ∧ ∀ n : ℕ, n ∉ E →
    ∑ r ∈ (sig n).primeFactors.filter (fun r : ℕ => (logIt 2 (n : ℝ)) ^ 2 < (r : ℝ)),
      (1 : ℝ) / r ≤ 1

-- deps: external — Halberstam–Richert, "Sieve Methods" (1974), Theorem 2.2: the upper-bound sieve
--       for `g` linear forms, uniform in the coefficients (`g = 2` here). The paper applies it
--       "in the form used in [LP, (3.7)]"; LP cite HR Thm 2.2 for their instance.
-- used by: prop:sv-second-moment (lines 1588–1618; Claim_SvSievePairs in S4b).
/-- **Two-dimensional upper-bound sieve** `[Halberstam–Richert, Sieve Methods, Thm 2.2]`, the
general two-form upper bound, uniform in the coefficients; the paper's use is an instance.
Paper, lines 1588–1618: "For fixed `n, n'`, … every integral solution has the form
`p = p_0 + A_2 t`, `p' = p'_0 + A_1 t` (`t ∈ ℤ`). All relevant values of `t` lie in an interval of
length at most `T := X d h / (n s(n'))` … The standard two-dimensional upper-bound sieve, in the
form used in [LP, (3.7)], therefore gives `≪_δ X d h / (n n' (log X)^2) · A_1/φ(A_1) · A_2/φ(A_2) ·
A_3/φ(A_3)` possible prime pairs." Here `A_3 = |σ(n) − σ(n')|/(dh)` is the absolute determinant
`|a₁ b₂ − a₂ b₁|` of the two forms (from `p A_1 − p' A_2 = ±A_3`), and `gcd(A_1, A_2) = 1`
(line 1586).

PARAPHRASE ONLY (general form). The statement below is uniform in `a₁, a₂, b₁, b₂`, the start `u`
and the length `T`. The consumer needs that uniformity, because the forms vary with the pair
`(n, n')`. It comes from HR Theorem 2.2 ("uniformly in `a_i, b_i`" with nonzero discriminant), whose
text was **not** checked; only LP's citation of it was. SOURCE CHECKED for the **instance** only:
LP (3.7) (Dartmouth preprint), for `p = u + (s(m')/dh) t`, `p' = u' + (s(m)/dh) t`,
`0 ≤ t ≤ x d h/(m s(m'))`: "By the sieve ([HR, Theorem 2.2]), the number of such `p ≤ x/m` is
`≪ x d h/(m s(m') (log(x d h/(m s(m'))))^2) · A/φ(A) ≪ …`", with `A = A_1 A_2 A_3`.

Encoding, in terms of the interval length `T`: take **coprime** positive leading coefficients
`a₁, a₂`, a nonzero determinant `D = a₁ b₂ − a₂ b₁`, any integer start `u` and any `T ≥ 2`. Then
the number of integers `t ∈ [u, u + ⌊T⌋]` for which `a₁ t + b₁` and `a₂ t + b₂` are both
(positive) primes is `≤ C T/(log T)^2 · a₁/φ(a₁) · a₂/φ(a₂) · |D|/φ(|D|)`, with `C` absolute.
Coprimality restricts the statement to the instances used: line 1586 gives `gcd(A_1, A_2) = 1`, and
in LP `A_1, A_2` are coprime because `dh = gcd(s(m), s(m'))`. HR needs no such restriction. The
product of the three ratios dominates `A/φ(A)`, so for each instance this is weaker than LP's
form. The passage from `log T` to `log X` (`log T ≍ log X`) is left to the consumer.
`z.toNat.Prime` means `z` is a positive prime, so negative values count as non-prime. The general
form is true: every fixed-divisor case is dominated by the three ratios, and a form with a fixed
prime divisor takes at most one prime value. -/
def Cite_LP_sieve37 : Prop :=
  ∃ C : ℝ, ∀ (a₁ a₂ : ℕ) (b₁ b₂ : ℤ), 0 < a₁ → 0 < a₂ → Nat.Coprime a₁ a₂ →
    (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0 →
    ∀ (u : ℤ) (T : ℝ), 2 ≤ T →
      ((((Finset.Icc u (u + ⌊T⌋)).filter
          (fun t : ℤ =>
            ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card : ℕ)
          : ℝ) ≤
        C * T / (Real.log T) ^ 2 * ((a₁ : ℝ) / (a₁.totient : ℝ)) * ((a₂ : ℝ) / (a₂.totient : ℝ)) *
          ((((a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁).natAbs : ℝ) /
            ((((a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁).natAbs.totient : ℕ) : ℝ))

-- deps: external — Pollack, Illinois J. Math. 58 (2014), Theorem 1.4.
-- used by: lem:sv-regular (eq:sv-image-abundancy, lines 1470–1479).
/-- **Pollack 2014, Theorem 1.4, in the weak form used** `[Pollack, Theorem 1.4]`.
Paper, lines 1470–1476: "By [Pollack, Theorem 1.4], the fixed exceptional set of integers `n` for
which `s(s(n))/s(n) > s(n)/n + 1` has asymptotic density zero."

SOURCE CHECKED (Illinois J. Math. text): "Theorem 1.4. Let `x ≥ 1`. For all but
`O(x (log_3 x)^2/(log_2 x)^{1/4})` positive integers `n ≤ x`, we have
`|s(s(n))/s(n) − s(n)/n| ≤ (log_2 x)^{-1/4}`" (Pollack's `log_k` is iterated `max{1, log}`). Since
`(log_2 x)^{-1/4} ≤ 1` and the exceptional count is `o(x)`, the density-zero statement below
follows; it is the only consequence the paper uses.

Encoding: real division; `s(1) = 0` gives `0/0 = 0`, so `n = 1` is not in the set. -/
def Cite_Pollack_Thm14 : Prop :=
  DensZero {n : ℕ | (aliquot n : ℝ) / n + 1 < (aliquot (aliquot n) : ℝ) / (aliquot n : ℝ)}

-- deps: external — Pollack 2014, Lemma 2.4 (= Halberstam–Richert 1979, cf. Tenenbaum Cor. III.5.1).
-- used by: lem:sigma-rate (lines 531–541).
/-- **Halberstam–Richert mean-value bound, as `[Pollack, Lemma 2.4]`, with `λ₁ = λ₂ = 1`.**
Paper, lines 532–541: "Since `0 ≤ h_q(p^ν) ≤ 1`, the Halberstam–Richert mean-value bound, in the
form [Pollack, Lemma 2.4], applies with `λ₁ = λ₂ = 1`. It gives, with an absolute implied
constant, `B_q(y) ≤ ∑_{n≤y} h_q(n) ≪ y exp(∑_{p≤y} (h_q(p) − 1)/p)`."

SOURCE CHECKED: "Lemma 2.4. Let `f` be a nonnegative-valued multiplicative function. Suppose that
there are positive constants `λ₁` and `λ₂`, with `λ₂ < 2`, so that `f(p^k) ≤ λ₁ λ₂^{k−1}` for all
prime powers `p^k`. Then for all `x ≥ 1`, `∑_{n≤x} f(n) ≪_{λ₁,λ₂} x exp(∑_{p≤x} (f(p) − 1)/p)`."
Below: the instance `λ₁ = λ₂ = 1` (so `f(p^k) ≤ 1`), whose implied constant is absolute. -/
def Cite_Pollack_Lemma24 : Prop :=
  ∃ C : ℝ, ∀ f : ArithmeticFunction ℝ, f.IsMultiplicative → (∀ n : ℕ, 0 ≤ f n) →
    (∀ p k : ℕ, p.Prime → 1 ≤ k → f (p ^ k) ≤ 1) →
    ∀ x : ℝ, 1 ≤ x →
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n ≤
        C * x * Real.exp (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (f p - 1) / (p : ℝ))

/-- Helfgott's scale `x = H/(2 + 9/(196 √(2π)))` for the target `H` (EP1054.tex line 866). -/
noncomputable def helfgottX (H : ℕ) : ℝ :=
  (H : ℝ) / (2 + 9 / (196 * Real.sqrt (2 * Real.pi)))

open Classical in
-- deps: external — Helfgott, arXiv:1312.7748, §7.4, (7.49)–(7.50) (the weighted lower bound) and
--       (7.3), (7.19) (the sup norms of the two smoothing functions).
-- used by: the proof of lem:fraiture-balanced-goldbach (lines 856–898; S3
--          `Lem_FraitureBalancedGoldbach`, a link from this input and Cite_RosserSchoenfeld_psi).
/-- **Helfgott's weighted ternary Goldbach lower bound** `[Helfgott, §7.4]`.
Paper, lines 858–874: "Helfgott's explicit argument [Helfgott, §7.4, equations (7.49)–(7.50)] gives
a real weighted sum
```
\sum_{\substack{p+q+r=H\\p,q,r\ \mathrm{odd\ primes}}} (\log p)(\log q)(\log r)
 \eta_+(p/x)\eta_+(q/x)\eta_*(r/x) \geq0.000422H^2,
```
where `x=H/(2+9/(196\sqrt{2\pi}))`, for every odd `H\geq10^{27}`. Here `η₊` and `η_*` are the real
smoothing functions used in that proof. Their individual smoothing factors satisfy
`‖η₊‖_∞ ≤ 1.079955`, `‖η_*‖_∞ ≤ 1.414`; see [Helfgott, equations (7.3) and (7.19)]."

SOURCE CHECKED (arXiv:1312.7748v2, §7.4): for odd `N ≥ 10^{27}` the weighted sum over odd primes
`n₁ + n₂ + n₃ = N` of `Λ(n₁)Λ(n₂)Λ(n₃) η₊(n₁/x) η₊(n₂/x) η_*(n₃/x)` is `≥ 0.000422 N^2`, and
`|η₊|_∞ ≤ 1.079955`, `|η_*|_∞ ≤ 1.414` ("By (7.3) and (7.19)").

Until 2026-09-25 the trusted base held the paper's *conclusion* (`lem:fraiture-balanced-goldbach`,
as `Cite_Helfgott_balanced`) instead of this input, so a paper-proved lemma was assumed under a
citation label; it is now the link `Lem_FraitureBalancedGoldbach` (S3).

Encoding: **existential weights**, which is weaker than Helfgott's statement (his `η₊`, `η_*` are
fixed once for all `H`) and is exactly what the paper's reduction uses (only the sup norms and the
lower bound; the weights may be signed, since the reduction bounds *absolute* weights). The triple
sum runs over ordered pairs `(p, q)` with `p + q < H`; `r = H − p − q` is then determined, and the
summand is `0` unless `p, q, r` are odd primes. `log r` and `r/x` use the cast of the natural
`H − p − q`, which is exact under `p + q < H`. -/
def Cite_Helfgott_weighted : Prop :=
  ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H →
    ∃ ηp ηs : ℝ → ℝ, (∀ u : ℝ, |ηp u| ≤ 1.079955) ∧ (∀ u : ℝ, |ηs u| ≤ 1.414) ∧
      0.000422 * (H : ℝ) ^ 2 ≤
        ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H,
          if p + q < H ∧ p.Prime ∧ q.Prime ∧ (H - p - q).Prime ∧ Odd p ∧ Odd q ∧ Odd (H - p - q)
          then Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ) *
            ηp ((p : ℝ) / helfgottX H) * ηp ((q : ℝ) / helfgottX H) *
              ηs (((H - p - q : ℕ) : ℝ) / helfgottX H)
          else 0

-- deps: external — Dusart, arXiv:1002.0442, Theorem 6.9, (6.5).
-- used by: prop:fraiture-finite, third window bridge (lines 798–816), at `x = a` and `x = Y`.
/-- **Dusart 2010, Theorem 6.9, on the range used** `[Dusart2010, Theorem 6.9]`.
Paper, lines 799–805: "Dusart's explicit estimates give `x/log x < π(x) ≤ x/log x (1 + 1.2762/log x)
< 1.05 x/log x` (`x ≥ a`)", with `a = Y/2 = 199 500 000 000 000`.

SOURCE CHECKED (arXiv:1002.0442, (6.5)): `x/ln x (1 + 1/ln x) ≤ π(x)` for `x ≥ 599` and
`π(x) ≤ x/ln x (1 + 1.2762/ln x)` for `x > 1`. The strict lower bound below follows since
`1/ln x > 0`. Restricted to `x ≥ a`, as used; the final `< 1.05 x/log x` is the paper's arithmetic
(`log a > 32`), not part of the input. -/
def Cite_Dusart_Thm69 : Prop :=
  ∀ x : ℝ, 199500000000000 ≤ x →
    x / Real.log x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x / Real.log x * (1 + 1.2762 / Real.log x)

-- deps: external — Rosser–Schoenfeld, Illinois J. Math. 6 (1962), Theorem 12.
-- used by: the proof of lem:fraiture-balanced-goldbach (lines 880–888), at `t = z` and `t = H`.
/-- **Rosser–Schoenfeld: `ψ(t) ≤ 1.03883 t`** `[RosserSchoenfeld]`.
Paper, lines 880–882: "The explicit estimate `ψ(t) ≤ 1.03883 t` of [RosserSchoenfeld] bounds the
total absolute weight of triples with at least one coordinate at most `z` …".

PARAPHRASE ONLY for RS itself (RS Theorem 12: `ψ(x) < 1.03883 x` for `x > 0`); corroborated by
Helfgott §7.4, which invokes "[RS62, Thms. 12 and 13]" with the same constant. Stated with `≤`, as
the paper uses it. Consumed by the link `Lem_FraitureBalancedGoldbach` (S3), at `t = z` and
`t = H`. It is avoidable in principle: the sums bounded there run over primes, so pinned Mathlib's
`Chebyshev.theta_le_log4_mul_x` (`θ(x) ≤ x log 4`) gives `3W(log 4)^2/30000 < 0.00032 < 0.000422`;
the spine records the paper's argument, which cites RS. -/
def Cite_RosserSchoenfeld_psi : Prop :=
  ∀ t : ℝ, 0 < t → Chebyshev.psi t ≤ 1.03883 * t

-- deps: external — Axler, Ramanujan J. 61 (2023), Corollary 2 (= arXiv:2110.13478v3, Cor. 3.1).
-- used by: the proposition "If n ∈ R and f(n) ≤ n/10 then n > 10^120" (lines 1156–1181).
/-- **Axler's refinement of Robin's inequality, on the range used** `[AxlerRobin, Corollary 2]`.
Paper, lines 1172–1178: "If `n ≤ 10^{120}`, then `m ≤ 10^{119}`; hence Axler's unconditional
refinement of Robin's inequality gives
`σ(m)/m < (1 + 3.15367·10^{-7}) e^γ log log m ≤ 9.99745 < 10`."
The case `m ≤ 5040` is handled separately (line 1166), so the range used is `5040 < m ≤ 10^{119}`.

SOURCE CHECKED (arXiv:2110.13478v3, Corollary 3.1): "For every positive integer `n` with
`n ∉ 𝒜 ∪ {3, 720}`, we have `σ(n)/n < (1 + 3.15367 × 10^{-7}) e^γ log log n`", where every element
of `𝒜` is `≤ 5040`; the published Corollary 2 is stated for `n > 5040`. Restricted to the
range used. -/
def Cite_Axler_Cor2 : Prop :=
  ∀ m : ℕ, 5040 < m → m ≤ 10 ^ 119 →
    abundancy m < (1 + 3.15367e-7) * Real.exp eulerGamma * Real.log (Real.log m)

-- deps: external — Chen–Zhao, Publ. Math. Debrecen 78 (2011), Theorem 1.
-- used by: prop:theta-two (lines 2606–2612).
/-- **Chen–Zhao: the untouchable numbers have lower density `≥ 0.0602757`** `[ChenZhao]`.
Paper, lines 2606–2608: "Chen and Zhao proved that `lowerdens(𝒰) ≥ 0.0602757`", where
`𝒰 = ℕ ∖ s(ℕ)` (line 2584).

SOURCE CHECKED: Chen–Zhao define `n` *aliquot* if `n = σ(m) − m` for some positive integer `m`,
`Na(x) = {1 ≤ n ≤ x : n nonaliquot}`, and prove (Theorem 1) `|Na(x)| ≥ g_M x + o_M(x)` with
`g_M > 0.0602757` for an explicit `M`. So the lower density is `≥ g_M > 0.0602757`.

Encoding: `𝒰 = {N : N ≠ s(m) for every m ≥ 1}` (so `s(1) = 0` plays no role); `lowerDens` counts
from `1`. -/
def Cite_ChenZhao : Prop :=
  0.0602757 ≤ lowerDens {N : ℕ | ∀ m : ℕ, 1 ≤ m → aliquot m ≠ N}

-- deps: external — Pollack, Integers 15A (2015), Lemma 2 (via H. N. Shapiro).
-- used by: §7 (lines 2734–2748: the measures `ν_{a,e}`), prop:dadd:witness-means (lines 2773+),
--          thm:dadd:universal-singularity (lines 2857+), collision proposition (lines 3098–3117);
--          at `Q = 1`, `a = 0` it also supplies Davenport's theorem (`Cite_Davenport`, section (4),
--          derived), i.e. the Davenport law `𝒟` of the §7 preamble (lines 2733–2736).
/-- **Davenport's theorem in arithmetic progressions** `[PollackPalindromes, Lemma 2]`.
Paper, lines 2734–2743: "… its version for arithmetic progressions by Pollack gives an atomless
measure `ν_{a,e}` characterized by `ν_{a,e}(B) = lim_{Y→∞} (1/Y) #{n ≤ Y : n ≡ a (mod Λ(e)),
h(n) ∈ B}` for every continuity set `B`. In particular, each `ν_{a,e}` has total mass `1/Λ(e)`."

SOURCE CHECKED: "Lemma 2. Let `a` and `q` be integers with `q > 0`. For each real `u`, let
`𝒟_{a,q}(u) = {n ≡ a mod q : s(n) ≤ u n}`. Then for all `u`,
`D_{a,q}(u) := lim_{x→∞} #(𝒟_{a,q}(u) ∩ [1, x])/(x/q)` exists, and `D_{a,q}` is a continuous
function of `u` with `lim_{u→∞} D_{a,q}(u) = 1`."

Encoding: residues by a natural representative `a`; the normalisation `x/q` becomes density
`D(u)/Q`; re-parametrised to `h(n) = σ(n)/n = 1 + s(n)/n` (`abundancy`), since `s(n) ≤ u n ⟺
h(n) ≤ 1 + u` for `n ≥ 1`, and the shift `u ↦ u − 1` preserves continuity and the limit at `+∞`
(the class of `n = 0`, excluded by `cnt`, plays no role). The measure
`ν_{a,Q}` of the paper (total mass `1/Q`, atomless, `∑_a ν_{a,Q} = 𝒟`, `ν_{a,Q} ≤ 𝒟`) is the
Stieltjes measure of `D/Q`; that construction is the consumer's. -/
def Cite_PollackAP : Prop :=
  ∀ Q : ℕ, 0 < Q → ∀ a : ℕ,
    ∃ D : ℝ → ℝ, Continuous D ∧ Tendsto D atTop (𝓝 1) ∧
      ∀ u : ℝ, HasDens {n : ℕ | n % Q = a % Q ∧ abundancy n ≤ u} (D u / Q)

-- deps: external — Erdős, Pacific J. Math. 52 (1974), 59–65 (paper: "the account on p. 59").
-- used by: thm:dadd:universal-singularity (lines 2858–2861).
/-- **Erdős: the Davenport law is purely singular** `[ErdosDistribution, p. 59]`.
Paper, lines 2858–2861: "Erdős's singularity theorem asserts that the continuous Davenport law `𝒟`
is purely Lebesgue singular; see the account in [ErdosDistribution, p. 59]. By regularity there
is a `σ`-compact Lebesgue-null set `K ⊂ [1, ∞)` with `𝒟(K) = 1`."

PARAPHRASE ONLY. The 1974 abstract (checked, msp.org) speaks only of "best possible estimates for
`g(c + 1/t) − g(c)`"; singularity is not in the abstract, so the p. 59 account could not be
confirmed. The classical singularity result is usually attributed to Erdős, *On the smoothness of
the asymptotic distribution of additive arithmetical functions*, Amer. J. Math. 61 (1939) — see
the open issue in the report.

Encoding: any probability measure `μ` on `ℝ` whose distribution function is the Davenport density
of `{n : σ(n)/n ≤ u}` is mutually singular with Lebesgue measure. (Such a `μ` is unique, since its
distribution function is pinned down on every `Iic u`.) -/
def Cite_Erdos_singular : Prop :=
  ∀ μ : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure μ →
    (∀ u : ℝ, HasDens {n : ℕ | abundancy n ≤ u} (μ.real (Set.Iic u))) →
    μ.MutuallySingular MeasureTheory.volume

/-! ## (2) `Std_*` — standard textbook inputs (to be proved or ported later) -/

-- deps: standard — Mertens' second theorem (e.g. Tenenbaum, Thm I.1.10).
-- used by: lem:kovac-moment (∑_{p≤q} 1/p ≪ log log q, line 1070), the count of `𝒜_0(X)`
--          (lines 1275–1283), lem:sv-regular (∑_{Y<p≤y(X)} 1/p = o(1), line 1428),
--          lem:kernel-tails (eq:sharp-prime-sum, lines 1940–1948), prop:sv-second-moment.
/-- **Mertens' second theorem**: `∑_{p ≤ x} 1/p = log log x + M + O(1/log x)`.
Paper, line 1940: "Mertens' estimate for `∑_{p≤y} 1/p`, Chebyshev's bound, and partial summation
show that …"; line 1275: "The prime number theorem, followed by Mertens' theorem for primes". -/
def Std_Mertens2 : Prop :=
  ∃ M C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p - Real.log (Real.log x) - M| ≤
      C / Real.log x

-- deps: standard — Mertens' third (product) theorem (e.g. Tenenbaum, Thm I.1.12).
-- used by: §2 (line 364), lem:smooth-part-input (line 1371), lem:sv-classes (line 1511),
--          prop:sv-second-moment (lines 1636, 1710, 1771), cor:fm-envelope-tail (line 2038),
--          thm:subexp-growth (lines 2124–2129, 2180), prop:class-first-moment (line 2418),
--          eq:delta-A-asymptotic (line 2530).
/-- **Mertens' product theorem**: `Δ(y) = ∏_{p≤y}(1 − 1/p) ∼ e^{-γ}/log y`.
Paper, lines 362–366: "Mertens' theorem and Chebyshev's estimates give `Δ(y) ∼ e^{-γ}/log y`, …".
The variants used later (`∏_{p≤e, p∤Q}(1 − 1/p) ∼ (Q/φ(Q)) e^{-γ}/log e`, line 2420;
`∑_{P^+(d)≤Y} 1/d = ∏_{p≤Y}(1 − 1/p)^{-1} ≍ log Y`, line 1509) follow by finite algebra. -/
def Std_Mertens3 : Prop :=
  Tendsto (fun y : ℝ => Delta y * Real.log y) atTop (𝓝 (Real.exp (-eulerGamma)))

-- deps: standard — PNT in arithmetic progressions for a fixed modulus (e.g. Tenenbaum II.8).
-- used by: prop:class-first-moment (lines 2424–2430); and, as the single PNT-type trusted input,
--          the derived inputs Std_PNT (Q = 1), Std_primes_dyadic_lower (Q = 1) and
--          Std_recipPrimesAP_diverges (Q = q) of section (4).
/-- **Prime number theorem in arithmetic progressions, class `−1`, fixed modulus.**
Paper, lines 2424–2430: "For `Z ≥ 2`, the prime number theorem in arithmetic progressions, followed
by partial summation, gives, as `Z → ∞`, `∑_{e≤Z, e prime, e ≡ −1 (mod Q)} 1/log e ∼
Z/(φ(Q)(log Z)^2)`."

Encoding: for each fixed `Q ≥ 1`, `π(x; Q, −1) ∼ x/(φ(Q) log x)`, i.e.
`π(x; Q, Q−1) · log x / x → 1/φ(Q)`. Restricted to the class `−1` (always reduced), the only
class used. For `Q = 1` this is the PNT for `π`. -/
def Std_PNT_AP : Prop :=
  ∀ Q : ℕ, 1 ≤ Q →
    Tendsto (fun x : ℝ => (piAP x Q (Q - 1) : ℝ) * Real.log x / x) atTop
      (𝓝 (1 / (Q.totient : ℝ)))

-- deps: standard — Siegel–Walfisz (Tenenbaum, Cor. II.8.30), in the uniform dyadic form used.
-- used by: lem:sigma-rate (lines 543–557).
/-- **Siegel–Walfisz, dyadic lower bound uniform in `q ≤ √(log t / C)`.**
Paper, lines 543–548: "Choose `z = exp(C q^2)` with `C` sufficiently large. … By the
Siegel–Walfisz theorem, uniformly for `t ≥ z`, `π(2t; q, −1) − π(t; q, −1) ≫ t/(q log t)`." Here
`q ≥ 3` is prime (`lem:sigma-rate`, line 511).

Encoding: `∃ C > 0, ∃ c > 0` such that for every prime `q ≥ 3` and `t ≥ exp(C q^2)`,
`π(2t; q, q−1) − π(t; q, q−1) ≥ c t/(q log t)` (real subtraction). The existential `C` is harmless:
the bound for one `C` implies it for every larger `C`, which is how the paper "chooses `C`
sufficiently large". Truth: `t ≥ exp(C q^2)` forces `q ≤ (log t)^{1/2}`, inside the
Siegel–Walfisz range, whose error `t exp(−c'√(log t))` is `o(t/(q log t))`. -/
def Std_SiegelWalfisz_dyadic : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, q.Prime → 3 ≤ q →
    ∀ t : ℝ, Real.exp (C * (q : ℝ) ^ 2) ≤ t →
      c * t / ((q : ℝ) * Real.log t) ≤ (piAP (2 * t) q (q - 1) : ℝ) - (piAP t q (q - 1) : ℝ)

-- deps: standard — Brun–Titchmarsh (Montgomery–Vaughan 1973: π(x;q,a) ≤ 2x/(φ(q) log(x/q))).
-- used by: prop:sv-second-moment (eq:sv-f-sum, lines 1788–1815).
/-- **Brun–Titchmarsh inequality.**
Paper, lines 1802–1806: "Uniformly in the present ranges, `q_0 h ≤ X^{10/33} log X <
X^{7/20−ε_0}` for a fixed `ε_0 > 0`, so Brun–Titchmarsh and partial summation bound its reciprocal
prime sum by `O(1/φ(q_0 h))`"; also line 1788 and the sum over `r` (lines 1809–1815).

Encoding: `∃ C, ∀ m ≥ 1, ∀ a` coprime to `m`, `∀ x > m`,
`π(x; m, a) ≤ C x/(φ(m) log(x/m))`. (Montgomery–Vaughan give `C = 2` for all `1 ≤ m < x`.) -/
def Std_BrunTitchmarsh : Prop :=
  ∃ C : ℝ, ∀ m a : ℕ, 1 ≤ m → Nat.Coprime a m → ∀ x : ℝ, (m : ℝ) < x →
    (piAP x m a : ℝ) ≤ C * x / ((m.totient : ℝ) * Real.log (x / m))

-- deps: standard — the divisor bound (Hardy–Wright Thm 315).
-- used by: prop:sv-second-moment (`τ(s(q'ℓ)) = X^{o(1)}`, line 1726;
--          `τ(s(n'))^2 = X^{o(1)}`, line 1841).
/-- **Divisor bound `τ(n) = n^{o(1)}`**: for every `ε > 0`, `τ(n) ≤ C_ε n^ε` for all `n ≥ 1`.
Paper, line 1726: "Summing next over `h ∣ s(q'ℓ)` is bounded by `τ(s(q'ℓ)) = X^{o(1)}`"; line 1841:
"`∑_{h∣s(n')} τ(h) ≤ τ(s(n'))^2 = X^{o(1)}`". (The arguments are `≪_δ X`.) -/
def Std_divisorBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε

-- deps: standard — elementary (σ(p^a) odd iff p = 2 or a even).
-- used by: lem:sigma-rate (`B_2(y) ≪ √y`, lines 558–559), prop:theta-two (lines 2587–2589).
/-- **`σ(n)` is odd exactly when `n` is a square or twice a square.**
Paper, line 558: "Finally, `σ(n)` is odd exactly when `n` is a square or twice a square, so
`B_2(y) ≪ √y`." Line 2588 uses the same fact. -/
def Std_sigma_odd_iff : Prop :=
  ∀ n : ℕ, 1 ≤ n → (Odd (sig n) ↔ (IsSquare n ∨ ∃ m : ℕ, n = 2 * m ^ 2))

-- deps: standard — Euler products: (σ(v)/v)(φ(v)/v) = ∏_{p^a‖v}(1 − p^{−a−1}) ≥ 1/ζ(2).
-- used by: prop:sv-second-moment (eq:sv-totient, lines 1620–1629).
/-- **`v/φ(v) ≤ ζ(2) σ(v)/v`** for `v ≥ 1`.
Paper, lines 1620–1627: "If `v ∣ s(t)`, then `v/φ(v) ≤ ζ(2) σ(v)/v ≤ ζ(2) σ(s(t))/s(t) ≤ ζ(2) B_δ`."
Only the first inequality is an input; the second is monotonicity of `σ(v)/v` under divisibility. -/
def Std_totient_sigma : Prop :=
  ∀ v : ℕ, 1 ≤ v → (v : ℝ) / (v.totient : ℝ) ≤ Real.pi ^ 2 / 6 * ((sig v : ℝ) / v)

/-! ## (3) `Comp_*` — the finite computations of `verify.rs` (`[FraitureVerifier]`)

`prop:fraiture-finite` (lines 726–823) rests on three finite checks run by `verify.rs`. They are
external inputs of a computational kind: the statements below are what the verifier checks, as
the paper describes them. A local re-run (numpy sieve, 2026-09-25) **reproduced
`Comp_Verifier_small` and `Comp_Verifier_window1` exactly** (only `7` unmarked in `[6, 10^7]`;
94 primes in `(10000, 10883]` covering `[469615, 480503]`; the extension chain holds for all
5 705 894 primes in `(10^4, 99·10^6]` and ends at `273 803 744 799 153`).
`Comp_Verifier_largeSeed` was **not** re-run. -/

-- deps: external — verify.rs, check 1.
-- used by: prop:fraiture-finite, interval (eq:fraiture-small) (lines 746–755).
/-- **Verifier check 1 (small sieve).** Paper, lines 746–755: "take `1 ≤ B ≤ 1000` and a prime
`q > B`. The divisors of `Bq` consist first of the divisors of `B` and then of `q` times those
divisors, in the same order. Thus every integer of the form `σ(B) + q ∑_{i=1}^{j} d_i(B)`,
`1 ≤ j ≤ τ(B)`, is represented. A sieve through `10 000 000` marks every integer in
(eq:fraiture-small) except `7`." (`prefixSumDivisors B j` is `∑_{i≤j} d_i(B)`.) -/
def Comp_Verifier_small : Prop :=
  ∀ N : ℕ, 6 ≤ N → N ≤ 10 ^ 7 → N ≠ 7 →
    ∃ B q j : ℕ, 1 ≤ B ∧ B ≤ 1000 ∧ q.Prime ∧ B < q ∧ 1 ≤ j ∧ j ≤ B.divisors.card ∧
      N = sig B + q * prefixSumDivisors B j

-- deps: external — verify.rs, check 2.
-- used by: prop:fraiture-finite, interval (eq:fraiture-first-window) (lines 757–769).
/-- **Verifier check 2 (first prime window).** Paper, lines 757–766: "take `M = 10 000` and
`Y = 99 000 000 < M^2`. The first 94 primes in `(M, Y]`, lying between `10 007` and `10 883`, have
subset sums covering `[469 615, 480 503]`. … The verifier checks the hypothesis of
Lemma fraiture-extension for each successive prime through `98 999 987`. The resulting subset-sum
interval is `[469 615, 273 803 744 799 153]`."

Encoding: (a) the primes in `(10000, 10883]` number 94 and their subset sums cover
`[469615, 480503]`; (b) the hypothesis `p ≤ U − C + 1` of `lem:fraiture-extension`, with
`C = 469615` and `U` the current upper end, holds for every prime `10883 < p ≤ 98999987`
(written without truncated subtraction); (c) the final upper end is `273 803 744 799 153`. -/
def Comp_Verifier_window1 : Prop :=
  ((Finset.Ioc 10000 10883).filter Nat.Prime).card = 94 ∧
  (∀ N : ℕ, 469615 ≤ N → N ≤ 480503 →
    ∃ S ⊆ (Finset.Ioc 10000 10883).filter Nat.Prime, ∑ p ∈ S, p = N) ∧
  (∀ p : ℕ, p.Prime → 10883 < p → p ≤ 98999987 →
    p + 469615 ≤ 480503 + (∑ r ∈ (Finset.Ioo 10883 p).filter Nat.Prime, r) + 1) ∧
  480503 + ∑ r ∈ (Finset.Ioc 10883 98999987).filter Nat.Prime, r = 273803744799153

-- deps: external — verify.rs, check 3.
-- used by: prop:fraiture-finite, interval (eq:fraiture-large-window) (lines 771–786).
/-- **Verifier check 3 (large seed).** Paper, lines 771–777: "let `M = 20 000 000`. For every one
of the `51 000 001` integers in `[105 000 000, 156 000 000]`, the verifier constructs and checks a
sum of four or five distinct primes in `(M, 2M)`." Distinctness is carried by `Finset`. -/
def Comp_Verifier_largeSeed : Prop :=
  ∀ N : ℕ, 105000000 ≤ N → N ≤ 156000000 →
    ∃ S : Finset ℕ, (S.card = 4 ∨ S.card = 5) ∧
      (∀ p ∈ S, p.Prime ∧ 20000000 < p ∧ p < 40000000) ∧ ∑ p ∈ S, p = N

/-! ## (4) Derived inputs — NOT part of the trusted base

Each `Prop` below is cited by consumers under this name, but it **follows from the trusted inputs
of sections (1)–(3) together with pinned Mathlib**, so it is a proof-phase obligation and not an
independent outside fact. The names are kept (rather than renamed) so that every existing reference
still resolves; the spine must read the `-- deps: DERIVED from …` line, not the name prefix. The PNT
group reduces to the single PNT-type input `Std_PNT_AP`; `Cite_Davenport` reduces to
`Cite_PollackAP`; `Std_Mertens1` needs no trusted input at all (the paper derives it from
Chebyshev's bound, which pinned Mathlib has), so the spine treats it as a leaf. -/

-- deps: DERIVED from pinned Mathlib alone, as the paper says ("The last estimate follows by
--       partial summation from Chebyshev's bound", line 1383): `log p/(p − 1) ≤ 2 log p/p`, and
--       `∑_{p≤y} log p/p ≪ log y` by partial summation (`sum_mul_eq_sub_integral_mul`) from
--       `θ(x) ≤ x log 4` (`Chebyshev.theta_le_log4_mul_x`). Not an independent trusted input
--       (moved here from section (2) on 2026-09-25); a leaf of the spine.
-- used by: lem:smooth-part-input (lines 1377–1383).
/-- **`∑_{p ≤ y} log p/(p − 1) ≪ log y`** (Mertens' first theorem, in the form used). DERIVED.
Paper, lines 1377–1383: "`∑_{n≤X} log D_Y(n) = … ≤ X ∑_{p≤Y} log p/(p−1) ≪ X log Y`. The last
estimate follows by partial summation from Chebyshev's bound." -/
def Std_Mertens1 : Prop :=
  ∃ C : ℝ, ∀ y : ℝ, 2 ≤ y →
    ∑ p ∈ (Finset.Iic ⌊y⌋₊).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) ≤ C * Real.log y

-- deps: DERIVED from Std_PNT_AP at `Q = 1` (`piAP x 1 0 = π(⌊x⌋)` since `p % 1 = 0 % 1`, and
--       `φ(1) = 1`, so `π(x) log x/x → 1`) + Mathlib
--       `Chebyshev.theta_eq_primeCounting_mul_log_sub_integral`
--       (`θ(x) = π(x) log x − ∫_2^x π(t)/t dt`; the integral is `≪ x/log x = o(x)` by
--       `π(t) ≪ t/log t`) + `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`
--       (`|ψ − θ| ≪ √x log x`). Not an independent trusted input.
-- used by: eq:delta-A-asymptotic (lines 2530–2535: `log P_A = log A + ψ(A) = A + o(A)`).
/-- **Prime number theorem**: `ψ(x) = x + o(x)`. DERIVED (see `-- deps:`).
Paper, lines 2530–2533: "Mertens' theorem and the prime number theorem, in the form
`ψ(A) = A + o(A)`, give `log P_A = log A + ψ(A) = A + o(A)`". -/
def Std_PNT : Prop :=
  Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1)

-- deps: DERIVED from Std_PNT_AP at `Q = 1` (`π(x) ∼ x/log x` gives
--       `π(2t) − π(t) ≥ t/(2 log t)` for `t ≥ t₀`) + Mathlib Bertrand
--       `Nat.exists_prime_lt_and_le_two_mul` at `⌊t⌋₊` for `2 ≤ t < t₀` (a prime in
--       `(⌊t⌋, 2⌊t⌋] ⊆ (⌊t⌋, ⌊2t⌋]`, so the difference is `≥ 1 ≥ c t/log t` for `c` small in
--       terms of `t₀`). Not an independent trusted input.
-- used by: the count of `𝒜_0(X)` (lines 1274–1283: primes `p ∈ (T/2, T]`, `T ≥ X^{8/15}`).
/-- **Primes in dyadic intervals**: `π(2t) − π(t) ≫ t/log t` for `t ≥ 2`. DERIVED (see `-- deps:`).
Paper, lines 1274–1276: "For fixed `q, r, k`, the interval for `p` is `(T/2, T]`, where
`T = X/(qrk) ≥ X^{8/15}`. The prime number theorem … gives `#𝒜_0(X) ≫ X/log X ∑ …`". -/
def Std_primes_dyadic_lower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 2 ≤ t →
    c * t / Real.log t ≤ (Nat.primeCounting ⌊2 * t⌋₊ : ℝ) - (Nat.primeCounting ⌊t⌋₊ : ℝ)

-- deps: DERIVED from Std_PNT_AP at `Q = q` (`q ≥ 2` a prime power; the class `q − 1` is reduced
--       and `(q − 1) % q = q − 1`, matching `piAP`): `π(x; q, q−1) ∼ x/(φ(q) log x)`, and Abel
--       summation (Mathlib `sum_mul_eq_sub_integral_mul`) gives
--       `∑_{p ≤ x, p ≡ −1 (q)} 1/p ∼ log log x/φ(q) → ∞`. (Mathlib's
--       `ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div` concerns `Λ(n)/n`,
--       whose divergence does not imply this.) Not an independent trusted input.
-- used by: lem:fixed-modulus-normality (lines 476–478).
/-- **The primes `≡ −1 (mod q)` have divergent reciprocal sum** (`q` a prime power). DERIVED.
Paper, lines 476–478: "The reciprocal sum of the primes in the reduced residue class `−1 (mod q)`
diverges. Letting `𝒫` increase through this class makes the displayed product tend to zero."
Restricted to prime powers `q`, the only moduli used (line 462: "It suffices to prove the assertion
when `V = q` is a prime power"). -/
def Std_recipPrimesAP_diverges : Prop :=
  ∀ q : ℕ, IsPrimePow q →
    ¬ Summable (fun p : ℕ => if p.Prime ∧ p % q = q - 1 then (1 : ℝ) / p else 0)

-- deps: DERIVED from Cite_PollackAP at `Q = 1`, `a = 0` (`n % 1 = 0 % 1` always and
--       `D u / 1 = D u`): `obtain ⟨D, hc, ht, hd⟩ := h 1 one_pos 0;
--       exact ⟨D, hc, ht, fun u => by simpa [Nat.mod_one] using hd u⟩` — compiled 2026-09-25,
--       ERRORS=0. Not an independent trusted input.
-- used by: §7 preamble (lines 2733–2748: the Davenport law `𝒟`, S7 `Fact_DaddDavenportLaw`),
--          prop:dadd:witness-means, thm:dadd:universal-singularity, the collision lower-bound
--          proposition (lines 3098–3117).
/-- **Davenport's theorem: `σ(n)/n` has a continuous distribution function** `[Davenport]`.
DERIVED: the `Q = 1` case of `Cite_PollackAP`.
Paper, lines 2733–2736: "Write `𝒟` for the statistical law of `h(n) = σ(n)/n`. The
Davenport theorem and its version for arithmetic progressions by Pollack gives an atomless
measure …"

Statement as in Pollack, *Palindromic sums of proper divisors*, §2 (checked): "For each real `u`,
let `𝒟(u) = {n : s(n) ≤ u n}`. In 1933, Davenport showed that the sets `𝒟(u)` possess an asymptotic
density for every real `u`. Calling this density `D(u)`, he proved that `D(u)` is continuous
everywhere and that `lim_{u→∞} D(u) = 1`." (Davenport's 1933 paper itself was not consulted; the
derivation from `Cite_PollackAP` makes that moot.)

Encoding: re-parametrised to `h(n) = σ(n)/n` exactly as in `Cite_PollackAP`. The measure `𝒟` of the
paper is the Stieltjes measure of this `D`. -/
def Cite_Davenport : Prop :=
  ∃ D : ℝ → ℝ, Continuous D ∧ Tendsto D atTop (𝓝 1) ∧
    ∀ u : ℝ, HasDens {n : ℕ | abundancy n ≤ u} (D u)

end Principia.Erdos1054
