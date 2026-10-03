/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EspagnWrap
import Mathlib.NumberTheory.Primorial

set_option autoImplicit false

/-!
# `HX.EspagnLargeQ`: the spine (`ternvin.tex` 3025-3211)

`HX.EspagnLargeQ` is `λ(q) ≤ ϖ(q)` for every `q` outside Helfgott's checked range, i.e. for
`q ≥ 3.3·10⁹` with `210 ∤ q` and for `q ≥ 2.2·10¹⁰`. This file writes his argument as a spine:
the links are named `Prop`s, and `espagnLargeQ_of_links` composes them by case analysis on `q`.

## The literature it rests on (Rosser–Schoenfeld 1962, NAMED, never stronger)

`RS62_316`, `RS62_324`, `RS62_330`, `RS62_332` transcribe the four equations Helfgott cites,
each RESTRICTED to the range he consumes (so weaker than RS62's own statement):
* (3.16) `x(1 − 1/log x) < θ(x)` — RS62 states it for `x ≥ 41`; used at primes `≥ 200`;
* (3.24) `Σ_{p≤x} log p/p < log x` — RS62: `x > 1`; used at integers `≥ 29`;
* (3.30) `Π_{p≤x} p/(p−1) < e^γ log x (1 + 1/log²x)` — RS62: `x > 1`; used at integers `≥ 47`;
* (3.32) `θ(x) < 1.01624x` — RS62: `x > 0`; used for `x ≥ 10⁴`.
The primary could not be fetched from this machine; the forms are as Helfgott consumes them
(`ternvin.tex` 3072, 3087, 3113, 3160) and as the numbers he derives from them require.

## The spine

```
 q ≥ 3.3·10⁹, 210 ∤ q                          q ≥ 2.2·10¹⁰, 210 ∣ q
   q < q₀ = ∏_{p≤31,p≠7}p : HipoWo, n = 30       q < ∏_{p≤31}p : Hipo, n = 30
     λ ≤ hipowoFirst(29,q) ≤ … at 3.3·10⁹          λ ≤ victoFirst(29,q) ≤ … at 2.2·10¹⁰
       ≤ 475.513 < 477.465 ≤ ϖ₀(3.3·10⁹)             ≤ 838.227 < 846.765 ≤ ϖ₀(2.2·10¹⁰)
   q < ∏_{p≤37,p≠7}p : HipoWo, n = 36            (cited: HC.EspagnEvalCited)
     λ ≤ hipowoFirst(31,q) ≤ … at q₀
       ≤ 429.731 < 916.322 ≤ ϖ₀(q₀)            then ϖ₀ is non-decreasing: Varpi0Mono
   beyond: TailWo                              beyond: TailGen
```

`Hipo`/`HipoWo` are `eq:modo`/`eq:hipo` (and the `210 ∤ q` variants): rearrangement over the
prime factors of `q`. `F1Seven` is the numeric fact behind Helfgott's `7.44586`
(`f₁(7) = 1.1241327 ≥ 7.44586/6.62365 = 1.1241317`). The tails are `eq:drolo`/`eq:mutuso`.
PROVED here: the composition, the `λ` algebra (`lam_le`), the `victo`/`hipowo` bounds at `p₁ = 29,
31` from the cited small runs, their monotonicity in `q`, and the constants
`1 − ω ≥ 0.37268`, `7.284(1 + β) ≤ 7.45235`, `c_Δ ≥ 0.02741`.
-/

namespace Principia.Common.TernaryGoldbach.LQ

open Principia.Common.TernaryGoldbach.HC (omegaE cDeltaE kappaE betaE lambdaE tauE cSig cRho2
  varpi0 varpiE sumLogP mertProd logSum victoFirst hipowoFirst)

/-! ## (0) Objects -/

/-- `S(n) = Σ_{p≤n} log p/p`. -/
noncomputable def sumLP (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p

/-- `F(n) = Π_{p≤n} f₁(p)`. -/
noncomputable def f1Prod (n : ℕ) : ℝ := ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, CY.f1 p

/-! ## (1) Rosser–Schoenfeld 1962, NAMED on the consumed ranges -/

/-- **NAMED (literature) — RS62 (3.16)**, `x(1 − 1/log x) < θ(x)` (RS62: for `x ≥ 41`),
restricted to `x ≥ 200` (`ternvin.tex` 3160-3162). A cited THEOREM: an owner question. -/
def RS62_316 : Prop := ∀ x : ℝ, 200 ≤ x → x * (1 - 1 / Real.log x) < Chebyshev.theta x

/-- **NAMED (literature) — RS62 (3.24)**, `Σ_{p≤x} log p/p < log x` (RS62: for `x > 1`),
restricted to integers `n ≥ 29` (`ternvin.tex` 3113-3114). An owner question. -/
def RS62_324 : Prop := ∀ n : ℕ, 29 ≤ n → sumLP n < Real.log n

/-- **NAMED (literature) — RS62 (3.30)**, `Π_{p≤x} p/(p−1) < e^γ log x (1 + 1/log²x)` (RS62: for
`x > 1`), restricted to integers `n ≥ 47` (`ternvin.tex` 3072-3077). An owner question. -/
def RS62_330 : Prop :=
  ∀ n : ℕ, 47 ≤ n →
    mertProd n < Real.exp Real.eulerMascheroniConstant * Real.log n * (1 + 1 / Real.log n ^ 2)

/-- **NAMED (literature) — RS62 (3.32)**, `θ(x) < 1.01624x` (RS62: for `x > 0`), restricted to
`x ≥ 10⁴` (`ternvin.tex` 3087-3097). An owner question. -/
def RS62_332 : Prop := ∀ x : ℝ, 10000 ≤ x → Chebyshev.theta x < 1.01624 * x

/-! ## (2) The links -/

/-- **Link — `eq:modo` + `eq:hipo`** (`ternvin.tex` 3034-3048): if `q < Π_{p≤n+1} p` then `q` has
at most `π(n)` prime factors, so (by rearrangement: `log p/p` and `(p/(p−1))f₁(p)` decrease on the
odd primes and their value at `p ≥ 7` is below that at `2`) `Σ_{p∣q} log p/p ≤ S(n)` and
`(q/φ(q))f₁(q) ≤ Π_{p≤n} p/(p−1) · F(n)`. -/
def Hipo : Prop :=
  ∀ q n : ℕ, 1 ≤ q → 7 ≤ n → q < primorial (n + 1) →
    sumLogP q ≤ sumLP n ∧ (q : ℝ) / q.totient * CY.f1 q ≤ mertProd n * f1Prod n

/-- **Link — `eq:modowo` + `eq:hipowo`** (`ternvin.tex` 3049-3064): the same when `210 ∤ q` and
`q < Π_{p≤n+1, p≠7} p`, with `7` left out of the targets (the "least helpful" prime of
`2,3,5,7`). -/
def HipoWo : Prop :=
  ∀ q n : ℕ, 1 ≤ q → 7 ≤ n → ¬210 ∣ q → q < primorial (n + 1) / 7 →
    sumLogP q ≤ sumLP n - Real.log 7 / 7 ∧
      (q : ℝ) / q.totient * CY.f1 q ≤ mertProd n * f1Prod n / (7 / 6 * CY.f1 7)

/-- **Link — `ϖ₀` is non-decreasing** from `3.3·10⁹` on, where its branch is taken
(`ternvin.tex` 3129-3144). -/
def Varpi0Mono : Prop :=
  ∀ q1 q2 : ℝ, 3.3e9 ≤ q1 → q1 ≤ q2 → 0 < varpi0 q1 → varpi0 q1 ≤ varpi0 q2

/-- **Link — the numeric fact behind `7.44586`** (`ternvin.tex` 3184-3185):
`6.62365 f₁(7) ≥ 7.44586`, i.e. `f₁(7) ≥ 1.1241317` (true value `1.1241327`). -/
def F1Seven : Prop := 7.44586 ≤ 6.62365 * CY.f1 7

/-- **Link — the general tail** (`eq:drolo`, `eq:mutuso`, `ternvin.tex` 3152-3175):
`λ(q) ≤ ϖ(q)` for `q ≥ Π_{p≤31} p = 200560490130`. -/
def TailGen : Prop := CY.CERange → ∀ q : ℕ, 200560490130 ≤ q → lambdaE q ≤ varpiE q

/-- **Link — the `210 ∤ q` tail** (`ternvin.tex` 3203-3208): `λ(q) ≤ ϖ(q)` for `210 ∤ q`,
`q ≥ Π_{p≤37, p≠7} p = 1060105447830`. -/
def TailWo : Prop :=
  CY.CERange → ∀ q : ℕ, 1060105447830 ≤ q → ¬210 ∣ q → lambdaE q ≤ varpiE q

/-! ## (3) Constants -/

/-- `log 10 ≥ 2.302585` (`log 10 = 3 log 2 − log(1 − 1/5)`). -/
theorem log_ten_ge : (2.302585 : ℝ) ≤ Real.log 10 := by
  have hb := (Principia.Erdos1054.Proofs.SmallRatio.log_series_bounds (x := 1 / 5) (by norm_num)
    (by norm_num) 12).1
  have h10 : Real.log 10 = 3 * Real.log 2 - Real.log (1 - 1 / 5) := by
    rw [show (10 : ℝ) = 2 ^ 3 / (1 - 1 / 5) by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have h2 := Real.log_two_gt_d9
  norm_num [Finset.sum_range_succ] at hb
  rw [h10]
  norm_num at h2 ⊢
  linarith

/-- `log 10⁵ ≥ 11.512925`. -/
theorem logQ0_ge : (11.512925 : ℝ) ≤ Real.log 100000 := by
  rw [show (100000 : ℝ) = 10 ^ 5 by norm_num, Real.log_pow]
  have := log_ten_ge
  push_cast
  linarith

/-- **`ω(0.6) ≤ 0.62732`**, so `1 − ω ≥ 0.37268` (`ternvin.tex` 3080: `ω ≤ 0.627312`). -/
theorem omegaE_le (cer : CY.CERange) : omegaE ≤ 0.62732 := by
  rw [HX.omegaE_eq]
  have hL := logQ0_ge
  have hc := cer.1
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- `20000^{1/3} ≥ 27.144`. -/
theorem cbrt20000_ge : (27.144 : ℝ) ≤ (20000 : ℝ) ^ ((1 : ℝ) / 3) := by
  have hy0 : 0 < (20000 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
  have hy3 : ((20000 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 20000 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  by_contra h
  have := pow_lt_pow_left₀ (not_le.mp h) hy0.le (by norm_num : (3 : ℕ) ≠ 0)
  rw [hy3] at this
  norm_num at this

/-- **`7.284(1 + β) ≤ 7.45235`** (`ternvin.tex` 3081, 3121: `β ≤ 0.023111`). -/
theorem beta_const_le (cer : CY.CERange) : 7.284 * (1 + betaE) ≤ 7.45235 := by
  unfold betaE
  have hw := omegaE_le cer
  have hw0 := (HX.omegaE_pos cer).le
  have hc := cbrt20000_ge
  have hd : omegaE / (20000 : ℝ) ^ ((1 : ℝ) / 3) ≤ 0.62732 / 27.144 :=
    div_le_div₀ (by norm_num) hw (by norm_num) hc
  have : (0.62732 : ℝ) / 27.144 ≤ 0.0231109 := by norm_num
  linarith

/-- **`c_Δ ≥ 0.02741`** (`1.36 − 1.3325823`). -/
theorem cDelta_ge (cer : CY.CERange) : (0.02741 : ℝ) ≤ cDeltaE := by
  unfold cDeltaE
  linarith [cer.2]

/-! ## (4) The `λ` algebra -/

/-- **`λ(q) ≤ (C·P/K)³`** from `(q/φ)f₁(q) ≤ P`, `0 < K ≤ κ(q)` and `7.284(1+β) ≤ C`. -/
theorem lam_le (cer : CY.CERange) (q : ℕ) (hq : 1 ≤ q) (P K C : ℝ)
    (hP : (q : ℝ) / q.totient * CY.f1 q ≤ P) (hK0 : 0 < K) (hK : K ≤ kappaE q)
    (hC : 7.284 * (1 + betaE) ≤ C) : lambdaE q ≤ (C * P / K) ^ 3 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hκ : 0 < kappaE q := lt_of_lt_of_le hK0 hK
  have hf := HX.f1_nonneg q
  have hX0 : 0 ≤ (q : ℝ) / q.totient * CY.f1 q := mul_nonneg (div_nonneg hq0.le hφ.le) hf
  have hβ0 : 0 ≤ betaE := div_nonneg (HX.omegaE_pos cer).le (Real.rpow_nonneg (by norm_num) _)
  have hA0 : 0 ≤ 7.284 * (1 + betaE) := by positivity
  have hbase : (q : ℝ) / q.totient * (7.284 * (1 + betaE) * CY.f1 q / kappaE q) =
      7.284 * (1 + betaE) * ((q : ℝ) / q.totient * CY.f1 q) / kappaE q := by ring
  unfold lambdaE
  rw [hbase]
  have hb0 : 0 ≤ 7.284 * (1 + betaE) * ((q : ℝ) / q.totient * CY.f1 q) / kappaE q :=
    div_nonneg (mul_nonneg hA0 hX0) hκ.le
  refine pow_le_pow_left₀ hb0 ?_ 3
  have hP0 : 0 ≤ P := le_trans hX0 hP
  have h1 : 7.284 * (1 + betaE) * ((q : ℝ) / q.totient * CY.f1 q) ≤ C * P :=
    mul_le_mul hC hP hX0 (le_trans hA0 hC)
  calc 7.284 * (1 + betaE) * ((q : ℝ) / q.totient * CY.f1 q) / kappaE q
      ≤ C * P / kappaE q := div_le_div_of_nonneg_right h1 hκ.le
    _ ≤ C * P / K := div_le_div_of_nonneg_left (mul_nonneg (le_trans hA0 hC) hP0) hK0 hK

/-- Primes `≤ n` are primes `≤ p₁` when there is none in `(p₁, n]`. -/
theorem filter_prime_eq {p1 n : ℕ} (hle : p1 ≤ n) (hgap : ∀ m < n + 1, p1 < m → ¬m.Prime) :
    (Finset.range (n + 1)).filter Nat.Prime = (Finset.range (p1 + 1)).filter Nat.Prime := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hm, hp⟩
    refine ⟨?_, hp⟩
    by_contra h
    exact hgap m hm (by omega) hp
  · rintro ⟨hm, hp⟩
    exact ⟨by omega, hp⟩

/-- `F(n) ≥ 0`. -/
theorem f1Prod_nonneg (n : ℕ) : 0 ≤ f1Prod n :=
  Finset.prod_nonneg fun p _ => HX.f1_nonneg p

/-- `Π_{p≤n} p/(p−1) ≥ 0`. -/
theorem mertProd_nonneg (n : ℕ) : 0 ≤ mertProd n := by
  unfold mertProd
  refine Finset.prod_nonneg fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
  exact div_nonneg (by linarith) (by linarith)

/-- The denominator of `f₁(p)`, `D(p) = 1 + (p^{1/3} + p^{2/3})/(p(p−1)) ≥ 1` for `p ≥ 2`. -/
theorem one_le_den (p : ℕ) (hp : 2 ≤ p) :
    1 ≤ 1 + ((p : ℝ) ^ ((1 : ℝ) / 3) + (p : ℝ) ^ ((2 : ℝ) / 3)) / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have : 0 ≤ ((p : ℝ) ^ ((1 : ℝ) / 3) + (p : ℝ) ^ ((2 : ℝ) / 3)) / ((p : ℝ) * ((p : ℝ) - 1)) :=
    div_nonneg (add_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _))
      (mul_nonneg (by linarith) (by linarith))
  linarith

/-- `f₁(p)` at a prime is its single factor. -/
theorem f1_prime (p : ℕ) (hp : p.Prime) :
    CY.f1 p = (1 + (p : ℝ) ^ (-(2 : ℝ) / 3)) /
      (1 + ((p : ℝ) ^ ((1 : ℝ) / 3) + (p : ℝ) ^ ((2 : ℝ) / 3)) / ((p : ℝ) * ((p : ℝ) - 1))) := by
  unfold CY.f1
  rw [Nat.Prime.primeFactors hp, Finset.prod_singleton]

/-- **`F(n) ≤ exp(Σ_{p≤n} log(1 + p^{−2/3}))/6.62365`** for `n ≥ 29` (`ternvin.tex` 3108-3111),
from the cited `6.62365 ≤ Π_{p≤29} D(p)` and `D ≥ 1`. -/
theorem f1Prod_le (hf1 : HC.F1ProdCited) (n : ℕ) (hn : 29 ≤ n) :
    f1Prod n ≤ Real.exp (logSum n) / 6.62365 := by
  unfold f1Prod
  set s := (Finset.range (n + 1)).filter Nat.Prime with hs
  have hD : ∀ p ∈ s, 1 ≤
      1 + ((p : ℝ) ^ ((1 : ℝ) / 3) + (p : ℝ) ^ ((2 : ℝ) / 3)) / ((p : ℝ) * ((p : ℝ) - 1)) :=
    fun p hp => one_le_den p (Finset.mem_filter.mp hp).2.two_le
  have hN : ∀ p ∈ s, 0 < 1 + (p : ℝ) ^ (-(2 : ℝ) / 3) := fun p hp => by
    have := Real.rpow_nonneg (Nat.cast_nonneg p) (-(2 : ℝ) / 3)
    linarith
  rw [Finset.prod_congr rfl fun p hp => f1_prime p (Finset.mem_filter.mp hp).2,
    Finset.prod_div_distrib]
  have hnum : ∏ p ∈ s, (1 + (p : ℝ) ^ (-(2 : ℝ) / 3)) = Real.exp (logSum n) := by
    unfold logSum
    rw [← hs, Real.exp_sum]
    exact Finset.prod_congr rfl fun p hp => (Real.exp_log (hN p hp)).symm
  have hsub : (Finset.range 30).filter Nat.Prime ⊆ s := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    rw [hs, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp.2⟩
  have hden : (6.62365 : ℝ) ≤ ∏ p ∈ s,
      (1 + ((p : ℝ) ^ ((1 : ℝ) / 3) + (p : ℝ) ^ ((2 : ℝ) / 3)) / ((p : ℝ) * ((p : ℝ) - 1))) := by
    refine le_trans hf1 (Finset.prod_le_prod_of_subset_of_one_le hsub (fun p hp => ?_)
      fun p hp _ => hD p hp)
    exact le_trans zero_le_one (hD p (hsub hp))
  rw [hnum]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hden

/-! ## (5) `victo` and `hipowo` -/

/-- **`eq:victo`, first line** (`ternvin.tex` 3117-3124): for `q < Π_{p≤n+1} p`, `p₁ ≤ q` the
largest prime `≤ n`, `p₁ ≥ 29`, from the bounds at `p₁`: `λ(q) ≤ victoFirst(p₁, q)`. -/
theorem lam_le_victo (cer : CY.CERange) (hf1 : HC.F1ProdCited) (hp : Hipo) (q n p1 : ℕ)
    (hq : 1 ≤ q) (h29 : 29 ≤ p1) (hle : p1 ≤ n) (hgap : ∀ m < n + 1, p1 < m → ¬m.Prime)
    (hqn : q < primorial (n + 1)) (hpq : p1 ≤ q) (hM : mertProd p1 ≤ 1.90516 * Real.log p1)
    (hL : logSum p1 ≤ 0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) (hS : sumLP p1 ≤ Real.log p1) :
    lambdaE q ≤ victoFirst p1 q := by
  have hfe := filter_prime_eq hle hgap
  obtain ⟨hs, hx⟩ := hp q n hq (by omega) hqn
  have hsn : sumLP n = sumLP p1 := by unfold sumLP; rw [hfe]
  have hmn : mertProd n = mertProd p1 := by unfold mertProd; rw [hfe]
  have hfn : f1Prod n = f1Prod p1 := by unfold f1Prod; rw [hfe]
  rw [hsn] at hs
  rw [hmn, hfn] at hx
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p1 := by exact_mod_cast (by omega : 0 < p1)
  have hlog : Real.log p1 ≤ Real.log q := Real.log_le_log hp0 (by exact_mod_cast hpq)
  have hF := f1Prod_le hf1 p1 h29
  have hE : Real.exp (logSum p1) ≤ Real.exp (0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) :=
    Real.exp_le_exp.mpr hL
  have hF' : f1Prod p1 ≤ Real.exp (0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) / 6.62365 :=
    le_trans hF (div_le_div_of_nonneg_right hE (by norm_num))
  have hP : (q : ℝ) / q.totient * CY.f1 q ≤
      1.90516 * Real.log p1 * (Real.exp (0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) / 6.62365) :=
    le_trans hx (mul_le_mul hM hF' (f1Prod_nonneg _) (le_trans (mertProd_nonneg _) hM))
  have hW := omegaE_le cer
  have hcd := cDelta_ge cer
  have hK : 0.37268 * (Real.log q - Real.log p1) + 0.02741 ≤ kappaE q := by
    unfold kappaE
    have h1 : 0 ≤ Real.log q - sumLogP q := by linarith
    have h2 : 0.37268 * (Real.log q - Real.log p1) ≤ 0.37268 * (Real.log q - sumLogP q) :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    have h3 : 0.37268 * (Real.log q - sumLogP q) ≤ (1 - omegaE) * (Real.log q - sumLogP q) :=
      mul_le_mul_of_nonneg_right (by linarith) h1
    linarith
  have hK0 : 0 < 0.37268 * (Real.log q - Real.log p1) + 0.02741 := by nlinarith
  have h := lam_le cer q hq _ _ 7.45235 hP hK0 hK (beta_const_le cer)
  refine le_trans h (le_of_eq ?_)
  unfold victoFirst
  ring

/-- **`eq:hipowo`, first line** (`ternvin.tex` 3187-3195): for `210 ∤ q`, `q < Π_{p≤n+1,p≠7} p`,
`p₁ ≤ q` the largest prime `≤ n`, `p₁ ≥ 29`: `λ(q) ≤ hipowoFirst(p₁, q)`. -/
theorem lam_le_hipowo (cer : CY.CERange) (hf1 : HC.F1ProdCited) (hw : HipoWo) (f7 : F1Seven)
    (q n p1 : ℕ) (hq : 1 ≤ q) (h29 : 29 ≤ p1) (hle : p1 ≤ n)
    (hgap : ∀ m < n + 1, p1 < m → ¬m.Prime) (h210 : ¬210 ∣ q) (hqn : q < primorial (n + 1) / 7)
    (hpq : p1 ≤ q) (hM : mertProd p1 ≤ 1.90516 * Real.log p1)
    (hL : logSum p1 ≤ 0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) (hS : sumLP p1 ≤ Real.log p1) :
    lambdaE q ≤ hipowoFirst p1 q := by
  have hfe := filter_prime_eq hle hgap
  obtain ⟨hs, hx⟩ := hw q n hq (by omega) h210 hqn
  have hsn : sumLP n = sumLP p1 := by unfold sumLP; rw [hfe]
  have hmn : mertProd n = mertProd p1 := by unfold mertProd; rw [hfe]
  have hfn : f1Prod n = f1Prod p1 := by unfold f1Prod; rw [hfe]
  rw [hsn] at hs
  rw [hmn, hfn] at hx
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p1 := by exact_mod_cast (by omega : 0 < p1)
  have hlog : Real.log p1 ≤ Real.log q := Real.log_le_log hp0 (by exact_mod_cast hpq)
  have hl7 : 0 ≤ Real.log 7 / 7 := div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  have hF := f1Prod_le hf1 p1 h29
  have hE : Real.exp (logSum p1) ≤ Real.exp (0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) :=
    Real.exp_le_exp.mpr hL
  have hF' : f1Prod p1 ≤ Real.exp (0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) / 6.62365 :=
    le_trans hF (div_le_div_of_nonneg_right hE (by norm_num))
  have f7' : 7.44586 ≤ 6.62365 * CY.f1 7 := f7
  have hf7 : 0 < CY.f1 7 := by
    have : (7.44586 : ℝ) / 6.62365 ≤ CY.f1 7 := by
      rw [div_le_iff₀ (by norm_num)]
      linarith [f7']
    linarith
  have hP : (q : ℝ) / q.totient * CY.f1 q ≤
      1.633 * Real.log p1 * (Real.exp (0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) / 7.44586) := by
    refine le_trans hx ?_
    have hEp := Real.exp_pos (0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3))
    have hlp : 0 ≤ Real.log p1 := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p1))
    have hMF : mertProd p1 * f1Prod p1 ≤ 1.90516 * Real.log p1 *
        (Real.exp (0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) / 6.62365) :=
      mul_le_mul hM hF' (f1Prod_nonneg _) (le_trans (mertProd_nonneg _) hM)
    rw [div_le_iff₀ (mul_pos (by norm_num) hf7)]
    have hkey : 1.90516 * Real.log p1 * (Real.exp (0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) /
        6.62365) ≤ 1.633 * Real.log p1 * (Real.exp (0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) /
          7.44586) * (7 / 6 * CY.f1 7) := by
      have hc : (1.90516 : ℝ) / 6.62365 ≤ 1.633 / 7.44586 * (7 / 6) * (7.44586 / 6.62365) := by
        norm_num
      have h1 : 1.633 / 7.44586 * (7 / 6) * (7.44586 / 6.62365) ≤
          1.633 / 7.44586 * (7 / 6) * CY.f1 7 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [div_le_iff₀ (by norm_num)]
        linarith [f7']
      have h2 : 0 ≤ Real.log p1 * Real.exp (0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) := by positivity
      have e1 : 1.90516 * Real.log p1 * (Real.exp (0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) /
          6.62365) = (1.90516 / 6.62365) *
            (Real.log p1 * Real.exp (0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3))) := by ring
      have e2 : 1.633 * Real.log p1 * (Real.exp (0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3)) /
          7.44586) * (7 / 6 * CY.f1 7) = (1.633 / 7.44586 * (7 / 6) * CY.f1 7) *
            (Real.log p1 * Real.exp (0.74914 * (p1 : ℝ) ^ ((1 : ℝ) / 3))) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (le_trans hc h1) h2
    linarith
  have hW := omegaE_le cer
  have hcd := cDelta_ge cer
  have hK : 0.37268 * (Real.log q - Real.log p1 + Real.log 7 / 7) + 0.02741 ≤ kappaE q := by
    unfold kappaE
    have h1 : 0 ≤ Real.log q - sumLogP q := by linarith
    have h2 : 0.37268 * (Real.log q - Real.log p1 + Real.log 7 / 7) ≤
        0.37268 * (Real.log q - sumLogP q) :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    have h3 : 0.37268 * (Real.log q - sumLogP q) ≤ (1 - omegaE) * (Real.log q - sumLogP q) :=
      mul_le_mul_of_nonneg_right (by linarith) h1
    linarith
  have hK0 : 0 < 0.37268 * (Real.log q - Real.log p1 + Real.log 7 / 7) + 0.02741 := by nlinarith
  have h := lam_le cer q hq _ _ 7.45235 hP hK0 hK (beta_const_le cer)
  refine le_trans h (le_of_eq ?_)
  unfold hipowoFirst
  ring

/-- `victoFirst(p₁, ·)` is non-increasing on `q ≥ p₁`. -/
theorem victo_anti (p1 q q' : ℝ) (hp1 : 1 ≤ p1) (hq : p1 ≤ q) (hqq : q ≤ q') :
    victoFirst p1 q' ≤ victoFirst p1 q := by
  unfold victoFirst
  have hp0 : 0 < p1 := by linarith
  have hl : Real.log p1 ≤ Real.log q := Real.log_le_log hp0 hq
  have hl' : Real.log q ≤ Real.log q' := Real.log_le_log (by linarith) hqq
  have hlp : 0 ≤ Real.log p1 := Real.log_nonneg hp1
  have hN : 0 ≤ 1.90516 * Real.log p1 * (7.45235 *
      (Real.exp (0.74914 * p1 ^ ((1 : ℝ) / 3)) / 6.62365)) := by positivity
  have hd : 0 < 0.37268 * (Real.log q - Real.log p1) + 0.02741 := by nlinarith
  refine pow_le_pow_left₀ (div_nonneg hN (by nlinarith)) ?_ 3
  exact div_le_div_of_nonneg_left hN hd (by nlinarith)

/-- `hipowoFirst(p₁, ·)` is non-increasing on `q ≥ p₁`. -/
theorem hipowo_anti (p1 q q' : ℝ) (hp1 : 1 ≤ p1) (hq : p1 ≤ q) (hqq : q ≤ q') :
    hipowoFirst p1 q' ≤ hipowoFirst p1 q := by
  unfold hipowoFirst
  have hp0 : 0 < p1 := by linarith
  have hl : Real.log p1 ≤ Real.log q := Real.log_le_log hp0 hq
  have hl' : Real.log q ≤ Real.log q' := Real.log_le_log (by linarith) hqq
  have hlp : 0 ≤ Real.log p1 := Real.log_nonneg hp1
  have hl7 : 0 ≤ Real.log 7 / 7 := div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  have hN : 0 ≤ 1.633 * Real.log p1 * (7.45235 *
      (Real.exp (0.74914 * p1 ^ ((1 : ℝ) / 3)) / 7.44586)) := by positivity
  have hd : 0 < 0.37268 * (Real.log q - Real.log p1 + Real.log 7 / 7) + 0.02741 := by nlinarith
  refine pow_le_pow_left₀ (div_nonneg hN (by nlinarith)) ?_ 3
  exact div_le_div_of_nonneg_left hN hd (by nlinarith)

/-! ## (6) The composition -/

/-- `Σ_{p≤29} log p/p < log 29` etc. at `n = 30`, `36`: the prime gaps used. -/
theorem gap30 : ∀ m < 30 + 1, 29 < m → ¬m.Prime := by decide

/-- No prime in `(31, 36]`. -/
theorem gap36 : ∀ m < 36 + 1, 31 < m → ¬m.Prime := by decide

/-- `varpi0` at a cited point is on its branch, so positive. -/
theorem varpi0_ge_of {x a : ℝ} (ha : 0 < a) (h : a ≤ varpi0 x) : 0 < varpi0 x := by linarith

/-- **`HX.EspagnLargeQ` from its links** — the case analysis of the module docstring, with
Helfgott's cited evaluations (`HC.EspagnEvalCited`) at `2.2·10¹⁰`, `3.3·10⁹` and `q₀`, his cited
small runs (`HC.ProdSmallCited`, `HC.LogSumCited`, `HC.F1ProdCited`) at `p₁ = 29, 31`, and
RS62 (3.24) at `29`, `31`. -/
theorem espagnLargeQ_of_links (h324 : RS62_324) (hp : Hipo) (hw : HipoWo) (hmo : Varpi0Mono)
    (f7 : F1Seven) (tg : TailGen) (tw : TailWo) : HX.EspagnLargeQ := by
  intro cer sm q hq hnr
  obtain ⟨-, hps, hls, -, hf1, -, hev⟩ := sm
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hev
  have hvE : varpi0 (q : ℝ) ≤ varpiE q := le_max_left _ _
  have hS29 : sumLP 29 ≤ Real.log (29 : ℕ) := (h324 29 le_rfl).le
  have hS31 : sumLP 31 ≤ Real.log (31 : ℕ) := (h324 31 (by norm_num)).le
  have hM29 : mertProd 29 ≤ 1.90516 * Real.log (29 : ℕ) :=
    (hps 29 (by norm_num) le_rfl (by norm_num)).le
  have hM31 : mertProd 31 ≤ 1.90516 * Real.log (31 : ℕ) :=
    (hps 31 (by norm_num) (by norm_num) (by norm_num)).le
  have hL29 : logSum 29 ≤ 0.74914 * ((29 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) :=
    hls 29 (by norm_num) le_rfl (by norm_num)
  have hL31 : logSum 31 ≤ 0.74914 * ((31 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) :=
    hls 31 (by norm_num) (by norm_num) (by norm_num)
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hP31 : primorial (30 + 1) = 200560490130 := by decide
  have hP31w : primorial (30 + 1) / 7 = 28651498590 := by decide
  have hP37w : primorial (36 + 1) / 7 = 1060105447830 := by decide
  have hq33 : (3.3e9 : ℝ) ≤ q := by
    by_contra h
    exact hnr (Or.inl (not_le.mp h))
  have hq22 : (q : ℝ) < 2.2e10 → ¬210 ∣ q := fun h1 h2 => hnr (Or.inr ⟨h1, h2⟩)
  by_cases h210 : 210 ∣ q
  · -- `q ≥ 2.2·10¹⁰`
    have hq22' : (2.2e10 : ℝ) ≤ q := by
      by_contra h
      exact hq22 (not_le.mp h) h210
    by_cases hbig : 200560490130 ≤ q
    · exact tg cer q hbig
    have hqn : q < primorial (30 + 1) := by rw [hP31]; omega
    have hpq : 29 ≤ q := by
      have : (29 : ℝ) ≤ q := by linarith
      exact_mod_cast this
    have hv := lam_le_victo cer hf1 hp q 30 29 hq le_rfl (by norm_num) gap30 hqn hpq hM29 hL29
      hS29
    have hmono := hmo 2.2e10 q (by norm_num) hq22' (varpi0_ge_of (by norm_num) e1)
    have ha := victo_anti 29 2.2e10 q (by norm_num) (by norm_num) hq22'
    push_cast at hv
    linarith
  · -- `210 ∤ q`, `q ≥ 3.3·10⁹`
    by_cases hbig : 1060105447830 ≤ q
    · exact tw cer q hbig h210
    by_cases hmid : 28651498590 ≤ q
    · have hqn : q < primorial (36 + 1) / 7 := by rw [hP37w]; omega
      have hv := lam_le_hipowo cer hf1 hw f7 q 36 31 hq (by norm_num) (by norm_num) gap36 h210
        hqn (by omega) hM31 hL31 hS31
      have hq0' : (28651498590 : ℝ) ≤ q := by exact_mod_cast hmid
      have hmono := hmo 28651498590 q (by norm_num) hq0' (varpi0_ge_of (by norm_num) e5)
      have ha := hipowo_anti 31 28651498590 q (by norm_num) (by norm_num) hq0'
      push_cast at hv
      linarith
    · have hqn : q < primorial (30 + 1) / 7 := by rw [hP31w]; omega
      have hpq : 29 ≤ q := by
        have : (29 : ℝ) ≤ q := by linarith
        exact_mod_cast this
      have hv := lam_le_hipowo cer hf1 hw f7 q 30 29 hq le_rfl (by norm_num) gap30 h210 hqn hpq
        hM29 hL29 hS29
      have hmono := hmo 3.3e9 q le_rfl hq33 (varpi0_ge_of (by norm_num) e3)
      have ha := hipowo_anti 29 3.3e9 q (by norm_num) (by norm_num) hq33
      push_cast at hv
      linarith

end Principia.Common.TernaryGoldbach.LQ
