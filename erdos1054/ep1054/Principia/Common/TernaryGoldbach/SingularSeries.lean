/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Goldbach.MajorArc

set_option autoImplicit false

/-!
# The ternary singular series `𝔖₃(N)` and its lower bound for odd `N`

The major arcs of a ternary circle-method argument produce
`(1/2)·𝔖₃(H)·H² + error`, where the **ternary singular series** is

  `𝔖₃(N) = ∑_{q ≥ 1} μ(q)³·c_q(N)/φ(q)³ = ∏_p (1 + μ(p)³c_p(N)/φ(p)³)`
        `= ∏_{p ∣ N} (1 − 1/(p−1)²) · ∏_{p ∤ N} (1 + 1/(p−1)³).`

`Campaigns/Erdos-1054/HELFGOTT-ASSETS.md` §5 item 1 records that nothing in the library defines
this object: `Common/Goldbach/MajorArc.lean` has the **binary** local term `μ(q)²c_q(N)/φ(q)²`
(`Tarith`) and its bound `singSeries_ge : 1/4 ≤ ∑' q, Tarith n q` carries `Even n`. This file
supplies the ternary object and the bound the major arcs need. What *is* reused verbatim is the
`cRam` layer (`cRam`, `cRam_mul`, `cRam_prime`, `cRam_one`), which mentions only the Ramanujan sum
and is campaign-agnostic, plus `Tarith_summable` (as a comparison series) and `prod_one_sub_ge`.

## What is proved

* `sing3Local q N = μ(q)³·c_q(N)/φ(q)³`, and `sing3Arith N` as a multiplicative
  `ArithmeticFunction ℝ` (`isMult_sing3Arith`).
* the Euler factor at a prime, in both cases: `one_add_sing3Local_prime_dvd`
  (`= 1 − 1/(p−1)²`) and `one_add_sing3Local_prime_not_dvd` (`= 1 + 1/(p−1)³`).
* `sing3_eq_prod : 𝔖₃(N) = ∏'_p (1 + μ(p)³c_p(N)/φ(p)³)` for `N ≥ 1`.
* **`sing3_ge : Odd N → 13/10 ≤ sing3 N`** — the deliverable — and the sharper
  `sing3_ge_sharp : Odd N → 131/100 ≤ sing3 N`, which is the full strength of the same route.
* `sing3_eq_zero_of_even`, which shows the `Odd N` hypothesis is load-bearing.
* **`exists_sing3Trunc_ge : 0 < ε → ∃ R₀, ∀ odd N, ∀ R ≥ R₀, 13/10 − ε ≤ sing3Trunc N R`** — the
  same bound for the **truncated** series a major-arc computation at level `R` actually produces,
  unconditionally, with `R₀` ineffective.

## The constant

The infimum of `𝔖₃` over odd `N` is `2·∏_{p≥3}(1 − 1/(p−1)²) = 1.3203236317…` — exactly
twice the Hardy–Littlewood twin-prime constant `C₂`. (An earlier draft of this docstring said
`1.3203236744`, wrong past the 8th digit; corrected by the round-2 auditor and confirmed by a third
independent computation.) Computed two
independent ways (direct Euler product to `p ≤ 2·10⁶`, and `∏_p(1+1/(p−1)³) = 2.3009615447`
times the correction `∏_{p≥3}(1−1/(p−1)²)/(1+1/(p−1)³)`); a prefix to `4·10⁶` gives
`1.320323652`, converging down to the literature value — so only the first 8 digits were ever
justified, not the 13 originally claimed. It is an
infimum and not attained: the worst odd `N` divisible by every odd prime up to `199` gives
`1.32132`, and `N` divisible by the odd primes up to `41` gives `1.32703`. The factor at `p = 2`
is always `1 + 1/(2−1)³ = 2` for odd `N`, which is where the `2` comes from; for even `N` the
factor at `2` is `1 − 1/(2−1)² = 0` and `𝔖₃(N) = 0`, so **oddness is not decoration** — see
`sing3_eq_zero_of_even`.

The route below certifies `1.31035674…` exactly (`sing3_ge_sharp` states `131/100`, margin
`0.00036`); the requested `13/10` is a `0.8 %` weakening of that and sits `1.6 %` below the true
infimum. **The `2500` slack quoted in an earlier draft measured the wrong quantity** (round-2
auditor). `Reduction.lean`'s `0.00026·H²` is the slack of the FINAL target; the consumer of THIS
constant is `Spine.MajorArcLower P Q cMaj` at `cMaj = 1/2`, and since the major-arc value is about
`(1/2)𝔖₃(H)H²` the requirement is `𝔖₃ ≥ 2·cMaj = 1` plus the arc error. So the proven `1.31`
carries about **31 %** headroom, not a factor of 2500 — comfortable, but a quantity the major-arc
budget can actually exhaust.

## The route to the bound, and why it needs explicit primes

Every factor obeys `1 + T₃(p) ≥ 1 − 1/(p−1)²` (`one_add_sing3Local_ge`) with **no** hypothesis on
`N`, so the Weierstrass inequality `∏(1−a) ≥ 1−∑a` (`prod_one_sub_ge`, reused) gives
`𝔖₃(N) ≥ 2·(1 − ∑_{p≥3} 1/(p−1)²)`. That is **not enough**: `∑_{p≥3}1/(p−1)² = 0.3750650`, so the
pure-Weierstrass bound is `2·0.6249350 = 1.2498701 < 13/10`, and the `a_p` cannot be taken smaller
because `1 − 1/(p−1)²` is exactly the factor at `p ∣ N`. The first-order inequality therefore
caps the reachable constant at `1.2499`, and the peeled prefix below is not an optimisation but a
necessity. So the finite prefix `p ≤ 41` is evaluated **exactly**
(`2·∏_{3≤p≤41}(1−1/(p−1)²) = 1.3269435415…`) and Weierstrass is applied only to the tail, where
`∑_{p>41} 1/(p−1)² ≤ 1/80` because every such `p` is odd, so `p−1` is an even number `≥ 42` and
`∑ ≤ (1/4)·∑_{m≥21}1/m² ≤ (1/4)/20` (`sum_inv_sq_tail_le`; the true tail is `0.0050007`).

## What this is, and is not, about

`sing3` is the **full** singular series `∑'_q`, i.e. the `q`-complete Euler product — the object a
major-arc analysis converges to, and the exact ternary analogue of the binary `∑' q, Tarith n q`
that `MajorArc.lean` bounds. A major-arc computation at level `R` produces instead the **truncated**
`sing3Trunc N R = ∑_{q ≤ R}`, and the two differ by a tail.

That tail is controlled here too, so the deliverable is available for the truncated object as well:
`sing3Maj q = μ(q)²/φ(q)²` dominates `‖T₃(q,N)‖` **uniformly in `N`** (because
`|c_q(N)| = φ(gcd(q,N)) ≤ φ(q)`, `abs_cRam_le_totient`) and is summable, so
`exists_Sing3TailUniform` proves the named hypothesis `Sing3TailUniform` for every `ε > 0` and
`exists_sing3Trunc_ge` concludes

  `∀ ε > 0, ∃ R₀, ∀ odd N, ∀ R ≥ R₀, 13/10 − ε ≤ 𝔖₃(N, R)`

with no hypothesis left. **`R₀` is not effective** — it comes from an existential `Summable`, and
an earlier draft claimed the explicit route through `sqfree_totient_strong` gives only
`∑_{q>R} μ(q)²/φ(q)² ≪ R^{-1/8}`, hence needs `R ≈ 10^{16}` and is vacuous. **That exponent is
wrong: it is `R^{-1/2}`** (round-2 auditor, and an independent coordinator computation agreeing).
`sqfree_totient_strong` gives `μ(q)²/φ(q)² ≤ 8q^{-3/2}` for every `q ≥ 1`, whose tail is
`≤ 16/√R`. A tail `≤ 0.06` — what `𝔖₃ ≥ 131/100` needs to clear `5/4` — holds from `R ≥ 71112`,
and the cutoffs a major-arc analysis uses are of order `3·10⁵`, where the bound is `0.0292`. So an
EFFECTIVE `R₀` is reachable and `MajorFromPlatt.SingularSeriesLower (5/4)` is dischargeable; what
this file leaves undone is that composition, not a theorem.
-/

namespace Principia.Common.TernaryGoldbach.SingularSeries

open Principia.Common.Goldbach.MajorArcMainTerm

/-! ### The local term -/

/-- The **ternary singular-series local term** `T₃(q) = μ(q)³·c_q(N)/φ(q)³`. The cube of `μ` (not
the square, as in the binary `Tarith`) is what makes the Euler factor at `p ∤ N` *positive*:
`μ(p)³c_p(N) = (−1)(−1) = 1`. -/
noncomputable def sing3Local (q N : ℕ) : ℝ :=
  (ArithmeticFunction.moebius q : ℝ) ^ 3 * (cRam q N : ℝ) / (Nat.totient q : ℝ) ^ 3

theorem sing3Local_zero (N : ℕ) : sing3Local 0 N = 0 := by
  simp [sing3Local]

theorem sing3Local_one (N : ℕ) : sing3Local 1 N = 1 := by
  simp [sing3Local, cRam_one]

/-- `T₃(·, N)` packaged as an `ArithmeticFunction ℝ`, so Mathlib's Euler-product machinery applies
(the same packaging as the binary `Tarith`). -/
noncomputable def sing3Arith (N : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun q => sing3Local q N, by simp [sing3Local]⟩

theorem sing3Arith_apply (N q : ℕ) : sing3Arith N q = sing3Local q N := rfl

/-- **Multiplicativity of the local term**: `T₃(q₁q₂) = T₃(q₁)T₃(q₂)` for coprime `q₁, q₂`. From
`cRam_mul` (reused verbatim) plus multiplicativity of `μ` and of `φ`. -/
theorem sing3Local_mul (N q1 q2 : ℕ) (h : Nat.Coprime q1 q2) :
    sing3Local (q1 * q2) N = sing3Local q1 N * sing3Local q2 N := by
  simp only [sing3Local]
  rw [cRam_mul N q1 q2 h, ArithmeticFunction.isMultiplicative_moebius.2 h, Nat.totient_mul h]
  push_cast
  ring

theorem isMult_sing3Arith (N : ℕ) : (sing3Arith N).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simpa [sing3Arith_apply] using sing3Local_one N
  · intro a b hab
    simpa [sing3Arith_apply] using sing3Local_mul N a b hab

/-! ### The Euler factor at a prime -/

/-- `T₃(p) = μ(p)³c_p(N)/φ(p)³ = (−(p−1))/(p−1)³` if `p ∣ N`, and `1/(p−1)³` if `p ∤ N`.
Proved from `cRam_prime` (reused). -/
theorem sing3Local_prime (p N : ℕ) (hp : p.Prime) :
    sing3Local p N = (if p ∣ N then -((p : ℝ) - 1) else 1) / ((p : ℝ) - 1) ^ 3 := by
  have hμ : ((ArithmeticFunction.moebius p : ℝ)) ^ 3 = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime hp]; norm_num
  have hφ : ((Nat.totient p : ℝ)) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le]; norm_num
  have hc : ((cRam p N : ℝ)) = if p ∣ N then ((p : ℝ) - 1) else -1 := by
    rw [cRam_prime p N hp, Int.cast_ite]; push_cast; norm_num
  rw [sing3Local, hμ, hφ, hc]
  by_cases hd : p ∣ N
  · rw [if_pos hd, if_pos hd]; ring
  · rw [if_neg hd, if_neg hd]; ring

/-- **The Euler factor at `p ∣ N`**: `1 + T₃(p) = 1 − 1/(p−1)²`. -/
theorem one_add_sing3Local_prime_dvd (p N : ℕ) (hp : p.Prime) (hd : p ∣ N) :
    1 + sing3Local p N = 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [sing3Local_prime p N hp, if_pos hd]
  field_simp
  ring

/-- **The Euler factor at `p ∤ N`**: `1 + T₃(p) = 1 + 1/(p−1)³`. -/
theorem one_add_sing3Local_prime_not_dvd (p N : ℕ) (hp : p.Prime) (hd : ¬ p ∣ N) :
    1 + sing3Local p N = 1 + 1 / ((p : ℝ) - 1) ^ 3 := by
  rw [sing3Local_prime p N hp, if_neg hd]

/-- **The uniform per-prime lower bound**, with *no* hypothesis on `N`: `1 + T₃(p) ≥ 1 − 1/(p−1)²`.
Equality at `p ∣ N`; at `p ∤ N` the left side is `≥ 1`. This is the one inequality the whole
product bound rests on, and it is the reason the bound holds for every `N` whose factor at `2` is
handled separately. -/
theorem one_add_sing3Local_ge (p N : ℕ) (hp : p.Prime) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 + sing3Local p N := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  by_cases hd : p ∣ N
  · rw [one_add_sing3Local_prime_dvd p N hp hd]
  · rw [one_add_sing3Local_prime_not_dvd p N hp hd]
    have h1 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 3 :=
      div_nonneg zero_le_one (pow_nonneg hpos.le 3)
    have h2 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 := div_nonneg zero_le_one (sq_nonneg _)
    linarith

/-- **The factor at `2` for odd `N` is exactly `2`.** `1 + T₃(2) = 1 + 1/(2−1)³ = 2`. -/
theorem one_add_sing3Local_two (N : ℕ) (hN : Odd N) : 1 + sing3Local 2 N = 2 := by
  have hd : ¬ (2 : ℕ) ∣ N := by
    rw [Nat.two_dvd_ne_zero, ← Nat.odd_iff]; exact hN
  rw [one_add_sing3Local_prime_not_dvd 2 N Nat.prime_two hd]
  norm_num

/-- **The factor at `2` for even `N` is exactly `0`** — so `𝔖₃` vanishes on even `N` and the
`Odd N` hypothesis of `sing3_ge` cannot be dropped. -/
theorem one_add_sing3Local_two_even (N : ℕ) (hN : Even N) : 1 + sing3Local 2 N = 0 := by
  have hd : (2 : ℕ) ∣ N := hN.two_dvd
  rw [one_add_sing3Local_prime_dvd 2 N Nat.prime_two hd]
  norm_num

/-- **Euler local factor**: `∑'_k T₃(p^k) = 1 + T₃(p)`, because `μ(p^k) = 0` for `k ≥ 2`. -/
theorem sing3Arith_local (p N : ℕ) (hp : p.Prime) :
    ∑' k : ℕ, sing3Arith N (p ^ k) = 1 + sing3Local p N := by
  have hsupp : ∀ k ∉ ({0, 1} : Finset ℕ), sing3Arith N (p ^ k) = 0 := by
    intro k hk
    have hk2 : 2 ≤ k := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      omega
    rw [sing3Arith_apply, sing3Local]
    have hμ : ArithmeticFunction.moebius (p ^ k) = 0 := by
      apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
      rintro ⟨_, hk1⟩
      omega
    rw [hμ]; simp
  rw [tsum_eq_sum hsupp, Finset.sum_pair (by norm_num), pow_zero, pow_one,
    (isMult_sing3Arith N).1, sing3Arith_apply]

/-! ### Summability and the Euler product -/

/-- `‖T₃(q)‖ ≤ ‖T₂(q)‖` pointwise, where `T₂ = Tarith` is the library's **binary** local term:
the ternary term is the binary one divided by `φ(q) ≥ 1`, and `|μ(q)|³ ≤ μ(q)²`. This is the whole
reason no new summability analysis is needed. -/
theorem norm_sing3Arith_le (N q : ℕ) : ‖sing3Arith N q‖ ≤ ‖Tarith N q‖ := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have hφ1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq
    have hφ0 : (0 : ℝ) < (Nat.totient q : ℝ) := by linarith
    have hμ1 : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
    have hμ0 : (0 : ℝ) ≤ |(ArithmeticFunction.moebius q : ℝ)| := abs_nonneg _
    have hc0 : (0 : ℝ) ≤ |(cRam q N : ℝ)| := abs_nonneg _
    rw [sing3Arith_apply, sing3Local, Tarith_apply, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_div, abs_div, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow, abs_pow,
      abs_of_nonneg hφ0.le]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hcube : |(ArithmeticFunction.moebius q : ℝ)| ^ 3
        ≤ |(ArithmeticFunction.moebius q : ℝ)| ^ 2 * (Nat.totient q : ℝ) := by
      calc |(ArithmeticFunction.moebius q : ℝ)| ^ 3
          = |(ArithmeticFunction.moebius q : ℝ)| ^ 2 * |(ArithmeticFunction.moebius q : ℝ)| := by
            ring
        _ ≤ |(ArithmeticFunction.moebius q : ℝ)| ^ 2 * (Nat.totient q : ℝ) := by
            have h2 : (0 : ℝ) ≤ |(ArithmeticFunction.moebius q : ℝ)| ^ 2 := by positivity
            nlinarith [hμ1, hφ1]
    nlinarith [hcube, hc0, hφ0, sq_nonneg ((Nat.totient q : ℝ)),
      mul_nonneg hc0 (pow_nonneg hφ0.le 2),
      mul_le_mul_of_nonneg_right hcube (mul_nonneg hc0 (pow_nonneg hφ0.le 2))]

/-- **Convergence of the ternary singular series** — by comparison with the binary one
(`Tarith_summable`, reused). -/
theorem sing3_summable (N : ℕ) (hN : 1 ≤ N) : Summable (fun q => ‖sing3Arith N q‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => norm_sing3Arith_le N q)
    (Tarith_summable N hN)

/-- **The ternary singular series** `𝔖₃(N) = ∑_{q≥1} μ(q)³c_q(N)/φ(q)³`. -/
noncomputable def sing3 (N : ℕ) : ℝ := ∑' q : ℕ, sing3Arith N q

/-- **The Euler product** `𝔖₃(N) = ∏'_p (1 + μ(p)³c_p(N)/φ(p)³)`. -/
theorem sing3_eq_prod (N : ℕ) (hN : 1 ≤ N) :
    sing3 N = ∏' p : Nat.Primes, (1 + sing3Local (p : ℕ) N) := by
  rw [sing3, ← (isMult_sing3Arith N).eulerProduct_tprod (sing3_summable N hN)]
  exact tprod_congr (fun p => sing3Arith_local (p : ℕ) N p.2)

/-- `HasProd` form of the Euler product, which is what the limit argument consumes. -/
theorem sing3_hasProd (N : ℕ) (hN : 1 ≤ N) :
    HasProd (fun p : Nat.Primes => 1 + sing3Local (p : ℕ) N) (sing3 N) := by
  have h := (isMult_sing3Arith N).eulerProduct_hasProd (sing3_summable N hN)
  have heq : (fun p : Nat.Primes => ∑' e : ℕ, sing3Arith N ((p : ℕ) ^ e))
      = (fun p : Nat.Primes => 1 + sing3Local (p : ℕ) N) := by
    funext p
    exact sing3Arith_local (p : ℕ) N p.2
  rw [heq] at h
  exact h

/-! ### The peeled prefix: the primes up to `41` -/

/-- The primes `≤ 41`, as a `Finset ℕ`. The cutoff is not arbitrary: the tail estimate below
delivers `1/80`, and `2·∏_{3≤p≤41}(1−1/(p−1)²)·(1−1/80) = 1.31035674… ≥ 13/10`, while stopping at
`31` would give `1.30665` and pure Weierstrass (no prefix) only `1.2499`. -/
def smallPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41}

/-- The same set inside `Nat.Primes`, which is the index type of the Euler product. -/
def smallPrimesSub : Finset Nat.Primes := smallPrimes.subtype Nat.Prime

theorem prime_of_mem_smallPrimes (n : ℕ) (hn : n ∈ smallPrimes) : n.Prime := by
  revert hn
  simp only [smallPrimes, Finset.mem_insert, Finset.mem_singleton]
  rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num

/-- **Every prime below `42` is in `smallPrimes`** — the fact that makes the complement of the
prefix start at `42`. -/
theorem mem_smallPrimes_of_prime_lt (n : ℕ) (hp : n.Prime) (hlt : n < 42) : n ∈ smallPrimes := by
  simp only [smallPrimes, Finset.mem_insert, Finset.mem_singleton]
  interval_cases n <;> revert hp <;> norm_num

/-- The comparison factor: exactly `2` at `p = 2` (odd `N`), and `1 − 1/(p−1)²` elsewhere. -/
noncomputable def eulerLow (n : ℕ) : ℝ := if n = 2 then 2 else 1 - 1 / ((n : ℝ) - 1) ^ 2

theorem eulerLow_nonneg (n : ℕ) (hp : n.Prime) : 0 ≤ eulerLow n := by
  rw [eulerLow]
  by_cases h2 : n = 2
  · rw [if_pos h2]; norm_num
  · rw [if_neg h2]
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by
      have h2le : 2 ≤ n := hp.two_le
      have : 3 ≤ n := by omega
      exact_mod_cast this
    have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have : 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith

/-- **The exact prefix evaluation.** `2·∏_{3≤p≤41}(1−1/(p−1)²)·(1−1/80) = 1.31035674… ≥ 13/10`,
checked by `norm_num` on the thirteen explicit rational factors
`3/4, 15/16, 35/36, 99/100, 143/144, 255/256, 323/324, 483/484, 783/784, 899/900, 1295/1296,
1599/1600` (and `2` at `p = 2`). -/
theorem prefix_bound : (131 : ℝ) / 100 ≤ (1 - 1 / 80) * ∏ n ∈ smallPrimes, eulerLow n := by
  rw [show smallPrimes = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41} from rfl]
  norm_num [eulerLow, Finset.prod_insert, Finset.mem_insert]

/-- **The prefix, exactly**: `2·∏_{3≤p≤41}(1−1/(p−1)²) = 5908908905896633/4453022092492800`
(`= 1.3269435415239155`). Kept as a theorem because it is the kernel's own certificate of the
number that the `python` computation produced, and the two were obtained independently. -/
theorem prefix_exact :
    (∏ n ∈ smallPrimes, eulerLow n) = 5908908905896633 / 4453022092492800 := by
  rw [show smallPrimes = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41} from rfl]
  norm_num [eulerLow, Finset.prod_insert, Finset.mem_insert]

/-- **The certified constant, exactly**: `2·∏_{3≤p≤41}(1−1/(p−1)²)·(1 − 1/80)
= 466803803565834007/356241767399424000 = 1.3103567472548665`. `131/100` is this minus `0.00036`. -/
theorem certified_constant_exact : (1 - 1 / 80) * ∏ n ∈ smallPrimes, eulerLow n
    = 466803803565834007 / 356241767399424000 := by
  rw [prefix_exact]
  norm_num

/-! ### The tail: `∑_{p > 41} 1/(p−1)² ≤ 1/80` -/

/-- Telescoping `∑_{k=m}^{M} (1/(k−1) − 1/k) = 1/(m−1) − 1/M`. -/
theorem sum_telescope (m M : ℕ) (hm : 2 ≤ m) (hM : m ≤ M) :
    ∑ k ∈ Finset.Icc m M, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) = 1 / ((m : ℝ) - 1) - 1 / (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base => rw [Finset.Icc_self, Finset.sum_singleton]
  | succ M hM IH =>
      have hm1 : (1 : ℝ) < (m : ℝ) := by
        have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      have hM0 : (0 : ℝ) < (M : ℝ) := by
        have : 0 < M := by omega
        exact_mod_cast this
      rw [Finset.sum_Icc_succ_top (by omega), IH,
        show ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 by push_cast; ring,
        show (M : ℝ) + 1 - 1 = (M : ℝ) by ring]
      have h1 : (m : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring

/-- **Uniform tail bound** `∑_{k ∈ U} 1/k² ≤ 1/(m−1)` for any finite `U ⊆ {k : m ≤ k}`. Uniform
in `U`, which is what a partial-product argument needs (a bound depending on `max U` is useless
there). -/
theorem sum_inv_sq_tail_le (m : ℕ) (hm : 2 ≤ m) (U : Finset ℕ) (hU : ∀ k ∈ U, m ≤ k) :
    ∑ k ∈ U, 1 / ((k : ℝ)) ^ 2 ≤ 1 / ((m : ℝ) - 1) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rcases U.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.sum_empty]
    exact div_nonneg zero_le_one (by linarith)
  set M := U.max' hne with hMdef
  have hMm : m ≤ M := hU _ (U.max'_mem hne)
  have hsub : U ⊆ Finset.Icc m M := fun k hk => Finset.mem_Icc.mpr ⟨hU k hk, U.le_max' k hk⟩
  have hterm : ∀ k ∈ Finset.Icc m M, 1 / ((k : ℝ)) ^ 2 ≤ 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by
      have : 2 ≤ k := le_trans hm hk.1
      exact_mod_cast this
    rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by nlinarith) (by nlinarith)]
    ring_nf
    nlinarith [hkR]
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  calc ∑ k ∈ U, 1 / ((k : ℝ)) ^ 2
      ≤ ∑ k ∈ Finset.Icc m M, 1 / ((k : ℝ)) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro k _ _; positivity
    _ ≤ ∑ k ∈ Finset.Icc m M, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) := Finset.sum_le_sum hterm
    _ = 1 / ((m : ℝ) - 1) - 1 / (M : ℝ) := sum_telescope m M hm hMm
    _ ≤ 1 / ((m : ℝ) - 1) := by
        have : (0 : ℝ) < 1 / (M : ℝ) := by positivity
        linarith

/-- **The tail estimate.** For any finite set `U` of primes `≥ 42`, `∑_{p ∈ U} 1/(p−1)² ≤ 1/80`.
The gain of the factor `4` over the naive `∑_{k≥42}1/k² ≤ 1/41` comes from parity: a prime `≥ 42`
is odd, so `p − 1 = 2·(p/2)` with `p/2 ≥ 21` distinct, and the sum is `(1/4)∑_{m≥21}1/m²`. Without
that factor the prefix would have to run to `p ≤ 59`. -/
theorem sum_tail_inv_sq_le (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime ∧ 42 ≤ p) :
    ∑ p ∈ U, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 80 := by
  have hodd : ∀ p ∈ U, p % 2 = 1 := by
    intro p hp
    obtain ⟨hpp, hge⟩ := hU p hp
    have h2 : p ≠ 2 := by omega
    exact Nat.odd_iff.mp (hpp.odd_of_ne_two h2)
  have hrw : ∀ p ∈ U, 1 / ((p : ℝ) - 1) ^ 2 = (1 / 4) * (1 / ((p / 2 : ℕ) : ℝ) ^ 2) := by
    intro p hp
    have hp1 : p - 1 = 2 * (p / 2) := by have := hodd p hp; omega
    have hge : 42 ≤ p := (hU p hp).2
    have hcast : ((p : ℝ) - 1) = 2 * ((p / 2 : ℕ) : ℝ) := by
      have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        have h1 : 1 ≤ p := by omega
        push_cast [Nat.cast_sub h1]; ring
      rw [← hc, hp1]; push_cast; ring
    rw [hcast]
    have hp2 : (0 : ℝ) < ((p / 2 : ℕ) : ℝ) := by
      have : 0 < p / 2 := by omega
      exact_mod_cast this
    field_simp
    ring
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  have hinj : Set.InjOn (fun p : ℕ => p / 2) ↑U := by
    intro x hx y hy h
    have h1 := hodd x (Finset.mem_coe.mp hx)
    have h2 := hodd y (Finset.mem_coe.mp hy)
    simp only at h
    omega
  have himg : ∑ m ∈ U.image (fun p : ℕ => p / 2), 1 / ((m : ℝ)) ^ 2
      = ∑ p ∈ U, 1 / (((p / 2 : ℕ)) : ℝ) ^ 2 :=
    Finset.sum_image hinj
  rw [← himg]
  have hge21 : ∀ m ∈ U.image (fun p : ℕ => p / 2), 21 ≤ m := by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    have := (hU p hp).2
    omega
  have h := sum_inv_sq_tail_le 21 (by norm_num) (U.image (fun p : ℕ => p / 2)) hge21
  have h20 : (1 : ℝ) / (((21 : ℕ) : ℝ) - 1) = 1 / 20 := by norm_num
  rw [h20] at h
  linarith

/-! ### The partial-product bound and the deliverable -/

/-- **Every partial Euler product over a finite set of primes containing all primes `≤ 41` is
`≥ 13/10`**, for every odd `N`. The prefix `smallPrimes` is evaluated exactly and Weierstrass
(`prod_one_sub_ge`, reused from the binary file) is applied only on the complement, where the tail
estimate gives `1/80`.

The hypothesis `smallPrimesSub ⊆ S` is necessary and is not a smuggled side condition: at `S = ∅`
the product is `1 < 13/10`, and at `S = {3}` with `3 ∣ N` it is `3/4`. The Euler product is a
*limit* over `S → atTop`, so a bound holding only eventually is exactly what the limit consumes. -/
theorem partial_prod_sing3_ge (N : ℕ) (hN : Odd N) (S : Finset Nat.Primes)
    (hS : smallPrimesSub ⊆ S) :
    (131 : ℝ) / 100 ≤ ∏ p ∈ S, (1 + sing3Local (p : ℕ) N) := by
  classical
  set T : Finset ℕ := S.image (fun p : Nat.Primes => (p : ℕ)) with hTdef
  have himg : ∏ n ∈ T, (1 + sing3Local n N)
      = ∏ p ∈ S, (1 + sing3Local ((p : ℕ)) N) := by
    rw [hTdef]
    exact Finset.prod_image (fun _ _ _ _ h => Subtype.ext h)
  have hprodT : ∏ p ∈ S, (1 + sing3Local (p : ℕ) N) = ∏ n ∈ T, (1 + sing3Local n N) := himg.symm
  have hTprime : ∀ n ∈ T, n.Prime := by
    intro n hn
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hn
    exact p.2
  have hsub : smallPrimes ⊆ T := by
    intro n hn
    exact Finset.mem_image.mpr ⟨⟨n, prime_of_mem_smallPrimes n hn⟩,
      hS (Finset.mem_subtype.mpr hn), rfl⟩
  rw [hprodT, ← Finset.prod_sdiff hsub]
  -- the prefix
  have hbig : (∏ n ∈ smallPrimes, eulerLow n) ≤ ∏ n ∈ smallPrimes, (1 + sing3Local n N) := by
    refine Finset.prod_le_prod (fun n hn => eulerLow_nonneg n (prime_of_mem_smallPrimes n hn))
      (fun n hn => ?_)
    have hp : n.Prime := prime_of_mem_smallPrimes n hn
    rw [eulerLow]
    by_cases h2 : n = 2
    · rw [if_pos h2, h2, one_add_sing3Local_two N hN]
    · rw [if_neg h2]
      exact one_add_sing3Local_ge n N hp
  have hbig0 : (0 : ℝ) ≤ ∏ n ∈ smallPrimes, eulerLow n :=
    Finset.prod_nonneg (fun n hn => eulerLow_nonneg n (prime_of_mem_smallPrimes n hn))
  -- the tail
  have hge42 : ∀ n ∈ T \ smallPrimes, n.Prime ∧ 42 ≤ n := by
    intro n hn
    rw [Finset.mem_sdiff] at hn
    have hp : n.Prime := hTprime n hn.1
    refine ⟨hp, ?_⟩
    by_contra hlt
    exact hn.2 (mem_smallPrimes_of_prime_lt n hp (by omega))
  have hfacnn : ∀ n ∈ T \ smallPrimes, (0 : ℝ) ≤ 1 - 1 / ((n : ℝ) - 1) ^ 2 := by
    intro n hn
    obtain ⟨hp, hge⟩ := hge42 n hn
    have h42 : (42 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hge
    have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have : 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  have ha01 : ∀ n ∈ T \ smallPrimes, 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 := by
    intro n hn
    have := hfacnn n hn
    linarith
  have ha00 : ∀ n ∈ T \ smallPrimes, (0 : ℝ) ≤ 1 / ((n : ℝ) - 1) ^ 2 := by
    intro n hn
    exact div_nonneg zero_le_one (sq_nonneg _)
  have hw : 1 - ∑ n ∈ T \ smallPrimes, 1 / ((n : ℝ) - 1) ^ 2
      ≤ ∏ n ∈ T \ smallPrimes, (1 - 1 / ((n : ℝ) - 1) ^ 2) :=
    prod_one_sub_ge (T \ smallPrimes) (fun n => 1 / ((n : ℝ) - 1) ^ 2) ha00 ha01
  have hstep : ∏ n ∈ T \ smallPrimes, (1 - 1 / ((n : ℝ) - 1) ^ 2)
      ≤ ∏ n ∈ T \ smallPrimes, (1 + sing3Local n N) :=
    Finset.prod_le_prod hfacnn (fun n hn => one_add_sing3Local_ge n N (hge42 n hn).1)
  have htailsum : ∑ n ∈ T \ smallPrimes, 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 / 80 :=
    sum_tail_inv_sq_le (T \ smallPrimes) hge42
  have htail : (1 : ℝ) - 1 / 80 ≤ ∏ n ∈ T \ smallPrimes, (1 + sing3Local n N) := by
    linarith
  have htail0 : (0 : ℝ) ≤ ∏ n ∈ T \ smallPrimes, (1 + sing3Local n N) := by
    refine Finset.prod_nonneg (fun n hn => ?_)
    have h1 := hfacnn n hn
    have h2 := one_add_sing3Local_ge n N (hge42 n hn).1
    linarith
  calc (131 : ℝ) / 100 ≤ (1 - 1 / 80) * ∏ n ∈ smallPrimes, eulerLow n := prefix_bound
    _ ≤ (∏ n ∈ T \ smallPrimes, (1 + sing3Local n N)) * ∏ n ∈ smallPrimes,
          (1 + sing3Local n N) := mul_le_mul htail hbig hbig0 htail0

/-- **THE DELIVERABLE, sharp form.** `𝔖₃(N) ≥ 131/100` for every odd `N` — the full strength of the
peel-to-`41` route, whose exact value is `2·∏_{3≤p≤41}(1−1/(p−1)²)·(1−1/80) = 1.31035674…`. The true
infimum is `1.3203236317…`, so what is lost is `0.75 %` (the Weierstrass step on the tail and the
`1/80` overestimate of the true tail `0.0050007`). Note there is no lower bound on `N`: the
statement holds for `N = 1` as well, where `c_q(1) = μ(q)` and the product is
`∏_p (1 + μ(p)³μ(p)/φ(p)³) = ∏_p(1 + 1/(p−1)³) = 2.3009615…`. -/
theorem sing3_ge_sharp (N : ℕ) (hN : Odd N) : (131 : ℝ) / 100 ≤ sing3 N := by
  have hN1 : 1 ≤ N := by
    obtain ⟨k, rfl⟩ := hN
    omega
  exact ge_of_tendsto (sing3_hasProd N hN1)
    (Filter.eventually_atTop.mpr ⟨smallPrimesSub, fun S hS => partial_prod_sing3_ge N hN S hS⟩)

/-- **THE DELIVERABLE** in the form the major arcs were asked for: `𝔖₃(N) ≥ 13/10` for every odd
`N`, a `0.8 %` weakening of `sing3_ge_sharp`. -/
theorem sing3_ge (N : ℕ) (hN : Odd N) : (13 : ℝ) / 10 ≤ sing3 N := by
  linarith [sing3_ge_sharp N hN]

/-- **`𝔖₃` vanishes on even `N`** — the `2`-factor is `0`, so `sing3_ge`'s `Odd N` is load-bearing
and the theorem is not vacuously strong. Proved from `HasProd` by inserting the point `2` (the
product with a zero factor is `0`). -/
theorem sing3_eq_zero_of_even (N : ℕ) (hN : Even N) (hN1 : 1 ≤ N) : sing3 N = 0 := by
  have h := sing3_hasProd N hN1
  have hzero : Filter.Tendsto (fun S : Finset Nat.Primes =>
      ∏ p ∈ S, (1 + sing3Local ((p : ℕ)) N)) Filter.atTop (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)) (f := Filter.atTop))
    refine Filter.eventually_atTop.mpr ⟨{⟨2, Nat.prime_two⟩}, fun S hS => ?_⟩
    refine (Finset.prod_eq_zero (hS (Finset.mem_singleton_self _)) ?_).symm
    exact one_add_sing3Local_two_even N hN
  exact tendsto_nhds_unique h hzero

/-! ### The truncated series: what a major-arc computation at level `R` actually produces -/

/-- The **truncated** ternary singular series `𝔖₃(N, R) = ∑_{1 ≤ q ≤ R} μ(q)³c_q(N)/φ(q)³` — the
exact analogue of the binary `singSeries`, and the object a major-arc analysis at level `R`
delivers. `sing3` is its `R → ∞` limit. -/
noncomputable def sing3Trunc (N R : ℕ) : ℝ := ∑ q ∈ Finset.Icc 1 R, sing3Local q N

theorem sing3Trunc_eq_range (N R : ℕ) :
    sing3Trunc N R = ∑ q ∈ Finset.range (R + 1), sing3Arith N q := by
  have hins : Finset.range (R + 1) = insert 0 (Finset.Icc 1 R) := by
    ext q
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [sing3Trunc, hins, Finset.sum_insert (by simp), sing3Arith_apply, sing3Local_zero,
    zero_add]
  exact Finset.sum_congr rfl (fun q _ => (sing3Arith_apply N q).symm)

/-- **The truncation converges**, for each fixed `N`: `𝔖₃(N, R) → 𝔖₃(N)`. -/
theorem tendsto_sing3Trunc (N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto (fun R : ℕ => sing3Trunc N R) Filter.atTop (nhds (sing3 N)) := by
  have hsum : Summable (fun q : ℕ => sing3Arith N q) :=
    Summable.of_norm (sing3_summable N hN)
  have h := HasSum.tendsto_sum_nat (Summable.hasSum hsum)
  have hcomp := h.comp (Filter.tendsto_add_atTop_nat 1)
  have heq : (fun R : ℕ => ∑ q ∈ Finset.range R, sing3Arith N q)
      ∘ (fun R : ℕ => R + 1) = fun R : ℕ => sing3Trunc N R := by
    funext R
    exact (sing3Trunc_eq_range N R).symm
  rw [heq] at hcomp
  exact hcomp

/-- A *uniform-in-`N`* bound on the truncation error, at truncation level `R₀` with error `ε`.
`tendsto_sing3Trunc` gives the corresponding statement for each fixed `N` with an `R₀` depending on
`N`; the major arcs need one `R₀` for all odd `N`, which is what this `Prop` asks for. It is
**proved** below, for every `ε > 0`, by `exists_Sing3TailUniform` — but non-effectively, so it is
kept as a named `Prop` and the theorems that consume it take it as a hypothesis, which keeps the
effectivity boundary visible in the types.

Adversarial check: the `Prop` is satisfiable degenerately — take `ε` large — so it is *weaker* for
larger `ε`, and `sing3Trunc_ge_of_tail` then visibly says nothing once `ε ≥ 13/10`. The opposite
degeneracy is blocked by a theorem rather than by a guard hypothesis:
`sing3TailUniform_zero_forces` shows that at `R₀ = 0` the `Prop` forces `ε ≥ 13/10`, so a small `ε`
cannot be had at a small `R₀`. -/
def Sing3TailUniform (R₀ : ℕ) (ε : ℝ) : Prop :=
  ∀ N R : ℕ, Odd N → R₀ ≤ R → |sing3 N - sing3Trunc N R| ≤ ε

/-- **The implication into the truncated bound.** A uniform tail bound `ε` at level `R₀` turns
`sing3_ge` into `𝔖₃(N, R) ≥ 13/10 − ε` for every odd `N` and every `R ≥ R₀`. -/
theorem sing3Trunc_ge_of_tail (R₀ : ℕ) (ε : ℝ) (h : Sing3TailUniform R₀ ε) (N R : ℕ)
    (hN : Odd N) (hR : R₀ ≤ R) : (13 : ℝ) / 10 - ε ≤ sing3Trunc N R := by
  have h1 := h N R hN hR
  have h2 := sing3_ge N hN
  have h3 : sing3 N - sing3Trunc N R ≤ ε := (abs_le.mp h1).2
  linarith

/-- **The named hypothesis is a real constraint, not decoration.** At `R₀ = 0` it *forces*
`ε ≥ 13/10`, because `𝔖₃(N, 0)` is the empty sum `0` while `𝔖₃(N) ≥ 13/10`. So
`Sing3TailUniform R₀ ε` with a small `ε` cannot be had for free at any small `R₀`: it is a genuine
statement about how fast the `q`-sum converges, uniformly in `N`. (The adversarial degenerate
witness for the other side is `ε` large, and `sing3Trunc_ge_of_tail` then visibly says nothing —
`13/10 − ε ≤ 0` is no bound at all on a quantity that can be `0`. Neither degeneracy is blocked by
a guard hypothesis; both are made visible instead.) -/
theorem sing3TailUniform_zero_forces (ε : ℝ) (h : Sing3TailUniform 0 ε) : (13 : ℝ) / 10 ≤ ε := by
  have h1 := h 1 0 odd_one (le_refl 0)
  have hz : sing3Trunc 1 0 = 0 := by simp [sing3Trunc]
  rw [hz, sub_zero] at h1
  have h2 := sing3_ge 1 odd_one
  have h3 : sing3 1 ≤ |sing3 1| := le_abs_self _
  linarith

/-- **The non-uniform half of `Sing3TailUniform`, proved.** For each fixed odd `N` and each
`ε > 0` there is an `R₀` beyond which the truncation error is `≤ ε`. This is what isolates the
missing ingredient as *uniformity in `N`* rather than convergence. -/
theorem exists_tail_small (N : ℕ) (hN : 1 ≤ N) (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → |sing3 N - sing3Trunc N R| ≤ ε := by
  have h := tendsto_sing3Trunc N hN
  have hmem : {x : ℝ | |sing3 N - x| ≤ ε} ∈ nhds (sing3 N) := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (sing3 N) hε) ?_
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have : |sing3 N - x| < ε := by rwa [abs_sub_comm] at hx
    exact le_of_lt this
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp (h.eventually_mem hmem)
  exact ⟨R₀, fun R hR => hR₀ R hR⟩

/-! ### A majorant uniform in `N`, and the unconditional truncated bound -/

/-- The majorant `μ(q)²/φ(q)²`, which dominates `‖T₃(q, N)‖` **uniformly in `N`**. The uniformity
is the whole point: `‖T₃(q,N)‖ = μ(q)²φ(gcd(q,N))/φ(q)³`, and `φ(gcd(q,N)) ≤ φ(q)` however large
`N` is, so one `N`-free summable majorant covers every `N` at once. (The binary `Tarith_summable`
majorant is `4σ(N)/q^{6/5}`, which is *not* uniform in `N` — that is why it cannot be used here.) -/
noncomputable def sing3Maj (q : ℕ) : ℝ :=
  (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2

theorem sing3Maj_nonneg (q : ℕ) : 0 ≤ sing3Maj q := by
  rw [sing3Maj]; positivity

/-- **`|c_q(N)| ≤ φ(q)` for squarefree `q`, uniformly in `N`.** From `cRam_sq_sqfree` (reused):
`c_q(N)² = φ(gcd(q,N))²`, and `φ` is monotone along divisibility (`Nat.totient_dvd_of_dvd`). -/
theorem abs_cRam_le_totient (q N : ℕ) (hq : 0 < q) (hsf : Squarefree q) :
    |cRam q N| ≤ (Nat.totient q : ℤ) := by
  have hφq : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have hle : Nat.totient (Nat.gcd q N) ≤ Nat.totient q :=
    Nat.le_of_dvd hφq (Nat.totient_dvd_of_dvd (Nat.gcd_dvd_left q N))
  have hleZ : ((Nat.totient (Nat.gcd q N) : ℤ)) ≤ (Nat.totient q : ℤ) := by exact_mod_cast hle
  have h0 : (0 : ℤ) ≤ (Nat.totient (Nat.gcd q N) : ℤ) := Int.natCast_nonneg _
  have hsq : |cRam q N| ^ 2 = ((Nat.totient (Nat.gcd q N) : ℤ)) ^ 2 := by
    rw [sq_abs]; exact cRam_sq_sqfree q N hsf
  nlinarith [hsq, abs_nonneg (cRam q N), h0, hleZ]

/-- **The uniform domination** `‖T₃(q, N)‖ ≤ μ(q)²/φ(q)²`, for every `q` and every `N`. -/
theorem norm_sing3Arith_le_maj (N q : ℕ) : ‖sing3Arith N q‖ ≤ sing3Maj q := by
  by_cases hsf : Squarefree q
  · have hq : 0 < q := Nat.pos_of_ne_zero hsf.ne_zero
    have hφ : (0 : ℝ) < (Nat.totient q : ℝ) := by
      have h := Nat.totient_pos.mpr hq
      exact_mod_cast h
    have hc : |(cRam q N : ℝ)| ≤ (Nat.totient q : ℝ) := by
      have h := abs_cRam_le_totient q N hq hsf
      calc |(cRam q N : ℝ)| = ((|cRam q N| : ℤ) : ℝ) := by rw [Int.cast_abs]
        _ ≤ ((Nat.totient q : ℤ) : ℝ) := by exact_mod_cast h
        _ = (Nat.totient q : ℝ) := by push_cast; ring
    have hμ : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
    have key : ‖sing3Arith N q‖ = |(ArithmeticFunction.moebius q : ℝ)| ^ 3
        * |(cRam q N : ℝ)| / (Nat.totient q : ℝ) ^ 3 := by
      rw [sing3Arith_apply, sing3Local, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_pow,
        abs_of_nonneg hφ.le]
    rw [key, sing3Maj, div_le_div_iff₀ (by positivity) (by positivity)]
    have hμ2 : |(ArithmeticFunction.moebius q : ℝ)| ^ 2 = (ArithmeticFunction.moebius q : ℝ) ^ 2 :=
      sq_abs _
    have hμ0 : (0 : ℝ) ≤ |(ArithmeticFunction.moebius q : ℝ)| := abs_nonneg _
    have hc0 : (0 : ℝ) ≤ |(cRam q N : ℝ)| := abs_nonneg _
    have h1 : |(ArithmeticFunction.moebius q : ℝ)| * |(cRam q N : ℝ)| ≤ (Nat.totient q : ℝ) := by
      calc |(ArithmeticFunction.moebius q : ℝ)| * |(cRam q N : ℝ)|
          ≤ 1 * (Nat.totient q : ℝ) := mul_le_mul hμ hc hc0 zero_le_one
        _ = (Nat.totient q : ℝ) := one_mul _
    calc |(ArithmeticFunction.moebius q : ℝ)| ^ 3 * |(cRam q N : ℝ)| * (Nat.totient q : ℝ) ^ 2
        = (|(ArithmeticFunction.moebius q : ℝ)| ^ 2 * (Nat.totient q : ℝ) ^ 2)
          * (|(ArithmeticFunction.moebius q : ℝ)| * |(cRam q N : ℝ)|) := by ring
      _ ≤ (|(ArithmeticFunction.moebius q : ℝ)| ^ 2 * (Nat.totient q : ℝ) ^ 2)
          * (Nat.totient q : ℝ) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (ArithmeticFunction.moebius q : ℝ) ^ 2 * (Nat.totient q : ℝ) ^ 3 := by
          rw [hμ2]; ring
  · have hμ0 : ArithmeticFunction.moebius q = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
    rw [sing3Arith_apply, sing3Local, sing3Maj, hμ0]
    norm_num

/-- **The majorant is summable** — by comparison with the library's `phi_pow32_summable`
(`∑_q μ(q)²/φ(q)^{3/2} < ∞`), since `φ(q)^{3/2} ≤ φ(q)²` once `φ(q) ≥ 1`. -/
theorem sing3Maj_summable : Summable sing3Maj := by
  refine Summable.of_nonneg_of_le sing3Maj_nonneg ?_ phi_pow32_summable
  intro q
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [sing3Maj]
  · have hφ1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq
    have hrpow : (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) ≤ (Nat.totient q : ℝ) ^ 2 := by
      rw [show ((Nat.totient q : ℝ)) ^ 2 = ((Nat.totient q : ℝ)) ^ ((2 : ℝ)) from
        (Real.rpow_natCast _ 2).symm]
      exact Real.rpow_le_rpow_of_exponent_le hφ1 (by norm_num)
    have hd1 : (0 : ℝ) < (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by linarith) _
    rw [sing3Maj]
    gcongr

set_option maxHeartbeats 1000000 in
-- The `SummationFilter`-parameterised `Summable`/`tsum` API used below
-- (`sum_add_tsum_nat_add`, `summable_nat_add_iff`, `norm_tsum_le_tsum_norm`,
-- `Summable.tsum_le_tsum`) elaborates slowly on this instance chain; the default 200000
-- heartbeats is not enough for this one proof.
/-- **The named hypothesis is DISCHARGED, non-effectively.** For every `ε > 0` there is an `R₀`
with `Sing3TailUniform R₀ ε`. The proof is the uniform majorant `sing3Maj` plus the fact that a
summable series has vanishing tails (`tendsto_sum_nat_add`), so the truncation error is bounded by
an `N`-free quantity that tends to `0`.

**What remains is effectivity, not truth.** `R₀` comes out of an existential `Summable`, so this
gives no `R₀(ε)`. Pushed through the library's `sqfree_totient_strong` (`q^{3/2} ≤ 8φ(q)²`) one
would get the explicit `∑_{q>R} μ(q)²/φ(q)² ≤ 16/√R` — an `R^{-1/2}` rate, NOT the `R^{-1/8}` an
earlier draft claimed — which reaches `ε = 0.06` at `R ≥ 71112`, well inside the `R ≈ 3·10⁵` a
major-arc analysis uses. The true tail is `≍ (log R)/R`, smaller still (`4.9·10⁻⁶` at `3·10⁵`).
So the gap this file leaves is exactly the one the rest of the Helfgott programme leaves (compare
`HELFGOTT-ASSETS.md` §4.3 on the `exp(−c(log x)^{1/10})` rate): an unconditional theorem with no
usable constant. -/
theorem exists_Sing3TailUniform (ε : ℝ) (hε : 0 < ε) : ∃ R₀ : ℕ, Sing3TailUniform R₀ ε := by
  have h0 : Filter.Tendsto (fun i : ℕ => ∑' k : ℕ, sing3Maj (k + i)) Filter.atTop (nhds 0) :=
    tendsto_sum_nat_add sing3Maj
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp (h0.eventually (gt_mem_nhds hε))
  refine ⟨R₀, fun N R hN hR => ?_⟩
  have hN1 : 1 ≤ N := by
    obtain ⟨k, rfl⟩ := hN
    omega
  have hsumN : Summable (fun q : ℕ => sing3Arith N q) := Summable.of_norm (sing3_summable N hN1)
  have hsplit : (∑ i ∈ Finset.range (R + 1), sing3Arith N i)
      + (∑' i : ℕ, sing3Arith N (i + (R + 1))) = ∑' q : ℕ, sing3Arith N q :=
    Summable.sum_add_tsum_nat_add (R + 1) hsumN
  have hdiff : sing3 N - sing3Trunc N R = ∑' i : ℕ, sing3Arith N (i + (R + 1)) := by
    rw [sing3Trunc_eq_range, sing3, ← hsplit]
    ring
  have hnormsum : Summable (fun i : ℕ => ‖sing3Arith N (i + (R + 1))‖) :=
    (summable_nat_add_iff (R + 1)).mpr (sing3_summable N hN1)
  have hmajshift : Summable (fun i : ℕ => sing3Maj (i + (R + 1))) :=
    (summable_nat_add_iff (R + 1)).mpr sing3Maj_summable
  have hlast : (∑' i : ℕ, sing3Maj (i + (R + 1))) < ε := hR₀ (R + 1) (by omega)
  rw [hdiff, ← Real.norm_eq_abs]
  calc ‖∑' i : ℕ, sing3Arith N (i + (R + 1))‖
      ≤ ∑' i : ℕ, ‖sing3Arith N (i + (R + 1))‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' i : ℕ, sing3Maj (i + (R + 1)) :=
        Summable.tsum_le_tsum (fun i => norm_sing3Arith_le_maj N _) hnormsum hmajshift
    _ ≤ ε := le_of_lt hlast

/-- **The truncated deliverable, unconditional.** For every `ε > 0` there is an `R₀` such that
`𝔖₃(N, R) ≥ 13/10 − ε` for every odd `N` and every truncation level `R ≥ R₀` — a statement about
the object a major-arc computation at level `R` actually produces, with no hypothesis left. `R₀` is
not effective; see `exists_Sing3TailUniform`. -/
theorem exists_sing3Trunc_ge (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ N R : ℕ, Odd N → R₀ ≤ R → (13 : ℝ) / 10 - ε ≤ sing3Trunc N R := by
  obtain ⟨R₀, h⟩ := exists_Sing3TailUniform ε hε
  exact ⟨R₀, fun N R hN hR => sing3Trunc_ge_of_tail R₀ ε h N R hN hR⟩

end Principia.Common.TernaryGoldbach.SingularSeries
