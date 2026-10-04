/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EspagnEdgeResSpine

set_option autoImplicit false

/-!
# Regime W of `EE.EspagnEdgeRes`: the inequality itself, for `q < 70000` and `ϖ(q) < 3`

**(A) Algebra.** `c_E` cancels: the residue's inequality at `R = ϖ` is
`G_q(ϖ) + ω·7.284(20000ϖ)^{−1/3}f₁(q) ≤ (φ/q)((1 − ω)log q + ωS(q) + log ϖ + 1.36)`
(`resIneq_of`), `S(q) = Σ_{p∣q} log p/p`.

**(B) Three uniform bounds.**
* `ϖ < 3` leaves only `r = 1, 2` in `G_q`: `G_q(ϖ) ≤ 1 + [q odd]` (`gQ_lt3`).
* `ϖ ≥ 1`: `ω·7.284(20000ϖ)^{−1/3} ≤ 0.62732·7.284/27.144 ≤ 0.16834`.
* **The bracket does not depend on `q`**: `ϖ ≥ K − log q` (the second term of `eq:armor`) and
  `1 < ϖ < 3` give `(1 − ω)log q + log ϖ ≥ (1 − ω)(K − 1)` (`log_bracket`, from
  `log x ≥ 0.38(x − 1)` on `[1, 3]`), so the right side is at least
  `(φ/q)(5.4967 + 0.6273·S(q))` with `K ≥ 12.1`.

**(C) The finite exact case split.** Dividing by `φ/q`, what remains is
`G·Π_{p∣q} p/(p−1) + 0.16834·Π_{p∣q} g(p) ≤ 5.4967 + 0.6273·Σ_{p∣q} log p/p`,
`g(p) = (p/(p−1))f₁(p)` (`win_comb`). Split the prime set `P = s ∪ L`, `s ⊆ {2,3,5,7,11,13}`,
`L` the primes `≥ 17`: `p/(p−1) ≤ 17/16` and `g(p) ≤ g(17) ≤ 1.1833` on `L` (`g` decreases from
`5` on, `LQ.gP_anti5`), `log p/p ≥ 0` there, and `Π_s p · 17^{#L} ≤ q < 70000`. On `s` the values
are bracketed exactly (`gP_le_gHi`: cube roots to `10⁻⁶`; `fP_ge_sLo`: certified logs). The
`64 × 4` resulting rational inequalities are checked by `decide +kernel` (`winOK_all`); the
smallest margin is `0.508` (at `s = {3,5,7,11}`, `#L = 1`). No modulus is enumerated.
-/

namespace Principia.Common.TernaryGoldbach.ER

open Principia.Common.PSieve (gQ)
open Principia.Common.TernaryGoldbach.HC (omegaE cDeltaE kappaE tauE cSig cRho2 varpi0 varpiE
  errE sumLogP)

/-! ## (1) `G_q` below `3` -/

/-- **`G_q(R) ≤ 1 + [q odd]` for `R < 3`**: only `r = 1, 2` can contribute. -/
theorem gQ_lt3 (q : ℕ) (R : ℝ) (hR : R < 3) : gQ q R ≤ if Odd q then 2 else 1 := by
  have hfl : ⌊R⌋₊ ≤ 2 := by
    have h : ⌊R⌋₊ < 3 := (Nat.floor_lt' (by norm_num)).mpr (by exact_mod_cast hR)
    omega
  unfold gQ
  have hsub : (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Nat.Coprime r q) ⊆
      (Finset.Icc 1 2).filter (fun r => Nat.Coprime r q) :=
    Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl hfl)
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => by positivity) ?_
  rw [Finset.sum_filter]
  have e : Finset.Icc 1 2 = {1, 2} := by decide
  rw [e, Finset.sum_insert (by decide), Finset.sum_singleton,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two, Nat.totient_two]
  simp only [Nat.coprime_one_left_eq_true, if_true, ArithmeticFunction.moebius_apply_one,
    Nat.totient_one, Nat.coprime_two_left]
  split_ifs <;> norm_num

/-! ## (2) The bracket -/

/-- `log x ≥ 0.38(x − 1)` on `[1, 3]`. -/
theorem log_ge_lin (x : ℝ) (h1 : 1 ≤ x) (h3 : x ≤ 3) : 0.38 * (x - 1) ≤ Real.log x := by
  rcases le_or_gt x 2 with h2 | h2
  · have h := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < x)
    have e : 1 - x⁻¹ = (x - 1) / x := by field_simp
    rw [e, div_le_iff₀ (by linarith)] at h
    have hl0 := Real.log_nonneg h1
    nlinarith
  · have hx0 : (0 : ℝ) < x / 2 := by linarith
    have h := Real.one_sub_inv_le_log_of_pos hx0
    have hl : Real.log x = Real.log 2 + Real.log (x / 2) := by
      rw [← Real.log_mul (by norm_num) hx0.ne']
      congr 1
      ring
    have e : 1 - (x / 2)⁻¹ = (x - 2) / x := by field_simp
    rw [e] at h
    have h' : (x - 2) / 3 ≤ (x - 2) / x :=
      div_le_div_of_nonneg_left (by linarith) (by linarith) h3
    have hl2 := Real.log_two_gt_d9
    linarith

/-- **The bracket is uniform in `q`**: `K − ℓ ≤ v`, `1 < v < 3`, `0 ≤ a ≤ 0.38` ⟹
`aℓ + log v ≥ a(K − 1)`. -/
theorem log_bracket (a K l v : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 0.38) (hv : K - l ≤ v) (hv1 : 1 < v)
    (hv3 : v < 3) : a * (K - 1) ≤ a * l + Real.log v := by
  rcases le_or_gt (K - l) 1 with h | h
  · have h1 : a * (K - 1) ≤ a * l := mul_le_mul_of_nonneg_left (by linarith) ha0
    have h2 : 0 ≤ Real.log v := Real.log_nonneg hv1.le
    linarith
  · have hx := log_ge_lin (K - l) h.le (by linarith)
    have hlog : Real.log (K - l) ≤ Real.log v := Real.log_le_log (by linarith) hv
    have h1 : a * (K - l - 1) ≤ 0.38 * (K - l - 1) :=
      mul_le_mul_of_nonneg_right ha (by linarith)
    have e : a * (K - 1) = a * l + a * (K - l - 1) := by ring
    linarith

/-! ## (3) The algebra: `c_E` cancels -/

/-- **`eq:luce` at `R = ϖ` is the `c_E`-free inequality.** -/
theorem resIneq_of (q : ℕ) (Tm : ℝ)
    (hT : omegaE * (7.284 * (20000 * varpiE q) ^ (-(1 : ℝ) / 3) * CY.f1 q) ≤ Tm)
    (h : gQ q (varpiE q) + Tm ≤ (q.totient : ℝ) / q *
      ((1 - omegaE) * Real.log q + omegaE * sumLogP q + Real.log (varpiE q) + 1.36)) :
    ResIneq q := by
  unfold ResIneq errE kappaE cDeltaE
  have e : (q.totient : ℝ) / q * ((1 - omegaE) * Real.log q + omegaE * sumLogP q +
      Real.log (varpiE q) + 1.36) = (q.totient : ℝ) / q * ((1 - omegaE) * (Real.log q -
        sumLogP q) + (1.36 - CY.cE)) + (q.totient : ℝ) / q * (Real.log (varpiE q) + CY.cE +
          sumLogP q) := by ring
  linarith

/-! ## (4) The rational data and the exact case split -/

/-- Upper brackets of `g(p) = (p/(p−1))f₁(p)` at the six small primes. -/
def gHi : ℕ → ℚ
  | 2 => 13451 / 10000
  | 3 => 3499 / 2500
  | 5 => 681 / 500
  | 7 => 2623 / 2000
  | 11 => 2483 / 2000
  | 13 => 6089 / 5000
  | _ => 0

/-- Lower brackets of `log p/p` at the six small primes. -/
def sLo : ℕ → ℚ
  | 2 => 693 / 2000
  | 3 => 1831 / 5000
  | 5 => 1609 / 5000
  | 7 => 2779 / 10000
  | 11 => 2179 / 10000
  | 13 => 1973 / 10000
  | _ => 0

/-- **The case inequality** for a small-prime part `s` and `m` primes `≥ 17`. -/
def WinOK (s : Finset ℕ) (m : ℕ) : Prop :=
  (if 2 ∈ s then 1 else 2) * (∏ p ∈ s, (p : ℚ) / ((p : ℚ) - 1)) * (17 / 16) ^ m +
      16834 / 100000 * (∏ p ∈ s, gHi p) * (11833 / 10000) ^ m ≤
    54967 / 10000 + 6273 / 10000 * ∑ p ∈ s, sLo p

instance (s : Finset ℕ) (m : ℕ) : Decidable (WinOK s m) := by
  unfold WinOK
  infer_instance

/-- **Every case passes** (`64 × 4` rational inequalities, exact). -/
theorem winOK_all : ∀ s ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ).powerset, ∀ m ∈ Finset.range 4,
    (∏ p ∈ s, p) * 17 ^ m < 70000 → WinOK s m := by
  decide +kernel

/-- `g(p) ≤ B` from a cube-root bracket `a ≤ p^{1/3} ≤ b`. -/
theorem gP_le_of (p : ℕ) (hp : p.Prime) (a b B : ℝ) (ha1 : 1 ≤ a) (ha : a ^ 3 ≤ p) (hb0 : 0 ≤ b)
    (hb : (p : ℝ) ≤ b ^ 3) (hB : (b ^ 5 + b ^ 3) / (a ^ 5 - a ^ 2 + a + 1) ≤ B) :
    LQ.gP p ≤ B := by
  rw [LQ.gP_eq p hp]
  have hu := (LQ.gG3_bracket ha1 (LQ.le_cbrt (Nat.cast_nonneg p) ha)
    (LQ.cbrt_le hb0 (Nat.cast_nonneg p) hb)).2
  linarith

/-- `log p/p ≥ s` from a certified `e^{ps} ≤ p`. -/
theorem fP_ge_of (p : ℕ) (hp : 1 ≤ p) (s : ℝ) (h : Real.exp (p * s) ≤ p) : s ≤ LQ.fP p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hl := log_ge_of hp0 h
  unfold LQ.fP
  rw [le_div_iff₀ hp0]
  linarith

/-- The brackets `g(p) ≤ gHi(p)`. -/
theorem gP_le_gHi (p : ℕ) (hp : p ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ)) :
    LQ.gP p ≤ (gHi p : ℝ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · have h := gP_le_of 2 (by norm_num) 1.259921 1.259922 1.3451 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    have e : ((gHi 2 : ℚ) : ℝ) = 1.3451 := by norm_num [gHi]
    rw [e]
    exact h
  · have h := gP_le_of 3 (by norm_num) 1.442249 1.44225 1.3996 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    have e : ((gHi 3 : ℚ) : ℝ) = 1.3996 := by norm_num [gHi]
    rw [e]
    exact h
  · have h := gP_le_of 5 (by norm_num) 1.709975 1.709976 1.362 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    have e : ((gHi 5 : ℚ) : ℝ) = 1.362 := by norm_num [gHi]
    rw [e]
    exact h
  · have h := gP_le_of 7 (by norm_num) 1.912931 1.912932 1.3115 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    have e : ((gHi 7 : ℚ) : ℝ) = 1.3115 := by norm_num [gHi]
    rw [e]
    exact h
  · have h := gP_le_of 11 (by norm_num) 2.22398 2.223981 1.2415 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    have e : ((gHi 11 : ℚ) : ℝ) = 1.2415 := by norm_num [gHi]
    rw [e]
    exact h
  · have h := gP_le_of 13 (by norm_num) 2.351334 2.351335 1.2178 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    have e : ((gHi 13 : ℚ) : ℝ) = 1.2178 := by norm_num [gHi]
    rw [e]
    exact h

/-- `log p/p ≥ s` at a small prime, from a certified exponential. -/
theorem fP_ge_cert (p : ℕ) (hp : 1 ≤ p) (s : ℝ) (y : ℚ) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hx : (p : ℝ) * s ≤ (8 : ℕ) * (y : ℝ)) (h : (tayQ y 12 + remQ y 12) ^ 8 ≤ (p : ℚ)) :
    s ≤ LQ.fP p := by
  have he := exp_hi ((p : ℝ) * s) y 12 8 (p : ℚ) hy hy1 (by norm_num) hx h
  push_cast at he
  exact fP_ge_of p hp s he

/-- The brackets `log p/p ≥ sLo(p)`, from certified exponentials. -/
theorem fP_ge_sLo (p : ℕ) (hp : p ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ)) :
    (sLo p : ℝ) ≤ LQ.fP p := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · have e : ((sLo 2 : ℚ) : ℝ) = 693 / 2000 := by norm_num [sLo]
    rw [e]
    exact fP_ge_cert 2 (by norm_num) _ (693 / 8000) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel)
  · have e : ((sLo 3 : ℚ) : ℝ) = 1831 / 5000 := by norm_num [sLo]
    rw [e]
    exact fP_ge_cert 3 (by norm_num) _ (5493 / 40000) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel)
  · have e : ((sLo 5 : ℚ) : ℝ) = 1609 / 5000 := by norm_num [sLo]
    rw [e]
    exact fP_ge_cert 5 (by norm_num) _ (1609 / 8000) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel)
  · have e : ((sLo 7 : ℚ) : ℝ) = 2779 / 10000 := by norm_num [sLo]
    rw [e]
    exact fP_ge_cert 7 (by norm_num) _ (19453 / 80000) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel)
  · have e : ((sLo 11 : ℚ) : ℝ) = 2179 / 10000 := by norm_num [sLo]
    rw [e]
    exact fP_ge_cert 11 (by norm_num) _ (23969 / 80000) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel)
  · have e : ((sLo 13 : ℚ) : ℝ) = 1973 / 10000 := by norm_num [sLo]
    rw [e]
    exact fP_ge_cert 13 (by norm_num) _ (25649 / 80000) (by norm_num) (by norm_num)
      (by push_cast; norm_num) (by decide +kernel)

/-- `g(p) ≤ 1.1833` for every prime `p ≥ 17` (`g(17) = 1.18326`, `g` decreasing from `5`). -/
theorem gP_le_17 (p : ℕ) (hp : p.Prime) (h17 : 17 ≤ p) : LQ.gP p ≤ 11833 / 10000 := by
  have h := LQ.gP_anti5 17 p (by norm_num) hp (by norm_num) h17
  have h17' := gP_le_of 17 (by norm_num) 2.571281 2.571282 (11833 / 10000) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- **`q/φ(q) = Π_{p∣q} p/(p−1)`**. -/
theorem ratio_eq (q : ℕ) (hq : 1 ≤ q) :
    (q : ℝ) / q.totient = ∏ p ∈ q.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have h1 := PSieve.prod_inv_eq q hq
  have hf : (q.primeFactors.filter fun p => p.Prime) = q.primeFactors :=
    Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp
  rw [hf] at h1
  rw [← h1]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have h0 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h1' : (p : ℝ) ≠ 0 := by linarith
  field_simp

/-- A prime `> 13` is `≥ 17`. -/
theorem prime_gt13 (p : ℕ) (hp : p.Prime) (h : ¬p ≤ 13) : 17 ≤ p := by
  by_contra hc
  have h1 : 14 ≤ p := by omega
  have h2 : p ≤ 16 := by omega
  interval_cases p <;> norm_num at hp

/-- A prime `≤ 13` is one of the six. -/
theorem prime_le13 (p : ℕ) (hp : p.Prime) (h : p ≤ 13) :
    p ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ) := by
  have h2 := hp.two_le
  interval_cases p <;> first | decide | norm_num at hp

/-- **The case split, assembled** (`q < 70000`): with `G = 1 + [q odd]`,
`G·q/φ + 0.16834·(q/φ)f₁ ≤ 5.4967 + 0.6273·S(q)`. -/
theorem win_comb (q : ℕ) (hq : 1 ≤ q) (hq7 : q < 70000) :
    (if Odd q then (2 : ℝ) else 1) * ((q : ℝ) / q.totient) +
        16834 / 100000 * ((q : ℝ) / q.totient * CY.f1 q) ≤
      54967 / 10000 + 6273 / 10000 * sumLogP q := by
  obtain ⟨P, hPdef⟩ : ∃ P : Finset ℕ, P = q.primeFactors := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : Finset ℕ, s = P.filter (fun p => p ≤ 13) := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : Finset ℕ, L = P.filter (fun p => ¬p ≤ 13) := ⟨_, rfl⟩
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hPdef ▸ hp)
  have hsP : ∀ p ∈ s, p ∈ P := fun p hp => (Finset.mem_filter.mp (hsdef ▸ hp)).1
  have hLP : ∀ p ∈ L, p ∈ P := fun p hp => (Finset.mem_filter.mp (hLdef ▸ hp)).1
  have hL17 : ∀ p ∈ L, 17 ≤ p := fun p hp => by
    rw [hLdef, Finset.mem_filter] at hp
    exact prime_gt13 p (hPp p hp.1) hp.2
  -- the three objects, split over `s ∪ L`
  have hM : (q : ℝ) / q.totient =
      (∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1)) * ∏ p ∈ L, (p : ℝ) / ((p : ℝ) - 1) := by
    rw [ratio_eq q hq, ← hPdef, hsdef, hLdef, Finset.prod_filter_mul_prod_filter_not]
  have hG : (q : ℝ) / q.totient * CY.f1 q = (∏ p ∈ s, LQ.gP p) * ∏ p ∈ L, LQ.gP p := by
    rw [LQ.ratio_f1_eq q hq, ← hPdef, hsdef, hLdef, Finset.prod_filter_mul_prod_filter_not]
  have hS : sumLogP q = ∑ p ∈ s, Real.log p / p + ∑ p ∈ L, Real.log p / p := by
    unfold sumLogP
    rw [← hPdef, hsdef, hLdef, Finset.sum_filter_add_sum_filter_not]
  -- the large primes
  have hML : ∏ p ∈ L, (p : ℝ) / ((p : ℝ) - 1) ≤ (17 / 16) ^ L.card := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have h17 : (17 : ℝ) ≤ p := by exact_mod_cast hL17 p hp
      exact div_nonneg (by linarith) (by linarith)
    · have h17 : (17 : ℝ) ≤ p := by exact_mod_cast hL17 p hp
      rw [div_le_iff₀ (by linarith)]
      linarith
  have hGL : ∏ p ∈ L, LQ.gP p ≤ (11833 / 10000) ^ L.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod
      (fun p hp => le_trans zero_le_one (LQ.one_le_gP p (hPp p (hLP p hp))))
      fun p hp => gP_le_17 p (hPp p (hLP p hp)) (hL17 p hp)
  have hGL0 : 0 ≤ ∏ p ∈ L, LQ.gP p := Finset.prod_nonneg fun p hp =>
    le_trans zero_le_one (LQ.one_le_gP p (hPp p (hLP p hp)))
  have hSL : 0 ≤ ∑ p ∈ L, Real.log p / p := Finset.sum_nonneg fun p _ => LQ.fP_nonneg p
  -- the small primes
  have hs6 : s ⊆ ({2, 3, 5, 7, 11, 13} : Finset ℕ) := fun p hp => by
    rw [hsdef, Finset.mem_filter] at hp
    exact prime_le13 p (hPp p hp.1) hp.2
  have hMs0 : 0 ≤ ∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1) := Finset.prod_nonneg fun p hp => by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hPp p (hsP p hp)).two_le
    exact div_nonneg (by linarith) (by linarith)
  have hGs : ∏ p ∈ s, LQ.gP p ≤ ∏ p ∈ s, (gHi p : ℝ) :=
    Finset.prod_le_prod
      (fun p hp => le_trans zero_le_one (LQ.one_le_gP p (hPp p (hsP p hp))))
      fun p hp => gP_le_gHi p (hs6 hp)
  have hGs0 : 0 ≤ ∏ p ∈ s, LQ.gP p := Finset.prod_nonneg fun p hp =>
    le_trans zero_le_one (LQ.one_le_gP p (hPp p (hsP p hp)))
  have hSs : ∑ p ∈ s, (sLo p : ℝ) ≤ ∑ p ∈ s, Real.log p / p :=
    Finset.sum_le_sum fun p hp => fP_ge_sLo p (hs6 hp)
  -- the size constraint
  have hprodP : ∏ p ∈ P, p ≤ q := by rw [hPdef]; exact LQ.prod_pf_le q hq
  have hprodL : 17 ^ L.card ≤ ∏ p ∈ L, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun p _ => Nat.zero_le _) hL17
  have hsplit : (∏ p ∈ s, p) * ∏ p ∈ L, p = ∏ p ∈ P, p := by
    rw [hsdef, hLdef, Finset.prod_filter_mul_prod_filter_not]
  have hmul := Nat.mul_le_mul_left (∏ p ∈ s, p) hprodL
  have hsz : (∏ p ∈ s, p) * 17 ^ L.card < 70000 := by
    have h1 : (∏ p ∈ s, p) * 17 ^ L.card ≤ q := le_trans hmul (hsplit ▸ hprodP)
    exact lt_of_le_of_lt h1 hq7
  have hs1 : 1 ≤ ∏ p ∈ s, p :=
    Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun p hp =>
      (hPp p (hsP p hp)).ne_zero)
  have hm4 : L.card ∈ Finset.range 4 := by
    rw [Finset.mem_range]
    by_contra hc
    have h4 : 17 ^ 4 ≤ 17 ^ L.card := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 := Nat.mul_le_mul hs1 h4
    norm_num at h5
    linarith
  have hok := winOK_all s (Finset.mem_powerset.mpr hs6) L.card hm4 hsz
  unfold WinOK at hok
  -- the parity of `q` is `2 ∉ s`
  have h2s : 2 ∈ s ↔ ¬Odd q := by
    rw [hsdef, Finset.mem_filter, hPdef, Nat.mem_primeFactors, Nat.not_odd_iff_even,
      even_iff_two_dvd]
    constructor
    · rintro ⟨⟨-, h2, -⟩, -⟩
      exact h2
    · intro h2
      exact ⟨⟨Nat.prime_two, h2, by omega⟩, by norm_num⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℚ, G = if 2 ∈ s then 1 else 2 := ⟨_, rfl⟩
  have hGeq : (if Odd q then (2 : ℝ) else 1) = (G : ℝ) := by
    rw [hGdef]
    by_cases ho : Odd q
    · rw [if_pos ho, if_neg (fun h => h2s.mp h ho)]
      norm_num
    · rw [if_neg ho, if_pos (h2s.mpr ho)]
      norm_num
  have hG0 : (0 : ℝ) ≤ G := by rw [← hGeq]; split_ifs <;> norm_num
  rw [← hGdef] at hok
  have hokR : ((G * (∏ p ∈ s, (p : ℚ) / ((p : ℚ) - 1)) * (17 / 16) ^ L.card +
      16834 / 100000 * (∏ p ∈ s, gHi p) * (11833 / 10000) ^ L.card : ℚ) : ℝ) ≤
      ((54967 / 10000 + 6273 / 10000 * ∑ p ∈ s, sLo p : ℚ) : ℝ) := by exact_mod_cast hok
  push_cast at hokR
  rw [hGeq, hG, hM, hS]
  have hA : (G : ℝ) * ((∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1)) * ∏ p ∈ L, (p : ℝ) / ((p : ℝ) - 1))
      ≤ G * (∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1)) * (17 / 16) ^ L.card := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hML hMs0) hG0
  have hB : (∏ p ∈ s, LQ.gP p) * ∏ p ∈ L, LQ.gP p ≤
      (∏ p ∈ s, (gHi p : ℝ)) * (11833 / 10000) ^ L.card :=
    mul_le_mul hGs hGL hGL0 (le_trans hGs0 hGs)
  have hB' := mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 16834 / 100000)
  have hS' := mul_le_mul_of_nonneg_left (add_le_add hSs hSL)
    (by norm_num : (0 : ℝ) ≤ 6273 / 10000)
  linarith

/-! ## (5) Regime W -/

/-- **Regime W, PROVED** (`q < 70000`, `1 < ϖ(q) < 3`). -/
theorem regWin (cer : CY.CERange) : RegWin := by
  intro q hq hq7 hv1 hv3
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hu : 0 < (q.totient : ℝ) / q := div_pos hφ hq0
  have hω := LQ.omegaE_le cer
  have hω0 := omega_lo cer
  have hf := HX.f1_nonneg q
  -- the `tR` term
  have hc20 := LQ.cbrt20000_ge
  have hcube : (20000 * varpiE q) ^ (-(1 : ℝ) / 3) ≤ 1 / 27.144 := by
    have h1 : (20000 * varpiE q) ^ (-(1 : ℝ) / 3) ≤ (20000 : ℝ) ^ (-(1 : ℝ) / 3) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by nlinarith) (by norm_num)
    have h2 : (20000 : ℝ) ^ (-(1 : ℝ) / 3) = 1 / (20000 : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [show (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) by ring, Real.rpow_neg (by norm_num), inv_eq_one_div]
    rw [h2] at h1
    exact le_trans h1 (one_div_le_one_div_of_le (by norm_num) hc20)
  have hcube0 : 0 ≤ (20000 * varpiE q) ^ (-(1 : ℝ) / 3) := Real.rpow_nonneg (by nlinarith) _
  have hT : omegaE * (7.284 * (20000 * varpiE q) ^ (-(1 : ℝ) / 3) * CY.f1 q) ≤
      16834 / 100000 * CY.f1 q := by
    have h1 : omegaE * (7.284 * (20000 * varpiE q) ^ (-(1 : ℝ) / 3)) ≤
        0.62732 * (7.284 * (1 / 27.144)) :=
      mul_le_mul hω (by nlinarith) (by positivity) (by norm_num)
    have h2 : (0.62732 : ℝ) * (7.284 * (1 / 27.144)) ≤ 16834 / 100000 := by norm_num
    have h3 := mul_le_mul_of_nonneg_right (le_trans h1 h2) hf
    have e : omegaE * (7.284 * (20000 * varpiE q) ^ (-(1 : ℝ) / 3) * CY.f1 q) =
        omegaE * (7.284 * (20000 * varpiE q) ^ (-(1 : ℝ) / 3)) * CY.f1 q := by ring
    rw [e]
    exact h3
  -- `G_q(ϖ) ≤ 1 + [q odd]`
  have hG := gQ_lt3 q (varpiE q) hv3
  -- the bracket
  have ht2 : Kc - Real.log q ≤ varpiE q := by
    unfold varpiE Kc
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hbr := log_bracket (1 - omegaE) Kc (Real.log q) (varpiE q) (by linarith) (by linarith)
    ht2 hv1 hv3
  have hK := Kc_lo
  have hS0 := HX.sumLogP_nonneg q
  have hcomb := win_comb q hq hq7
  refine resIneq_of q (16834 / 100000 * CY.f1 q) hT ?_
  have hKw : (0.37268 : ℝ) * 11.1 ≤ (1 - omegaE) * (Kc - 1) :=
    mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  have hwS : (6273 / 10000 : ℝ) * sumLogP q ≤ omegaE * sumLogP q :=
    mul_le_mul_of_nonneg_right (by linarith) hS0
  have hR : (54967 / 10000 : ℝ) + 6273 / 10000 * sumLogP q ≤
      (1 - omegaE) * Real.log q + omegaE * sumLogP q + Real.log (varpiE q) + 1.36 := by
    linarith
  obtain ⟨Gq, hGq⟩ : ∃ Gq : ℝ, Gq = if Odd q then (2 : ℝ) else 1 := ⟨_, rfl⟩
  rw [← hGq] at hG hcomb
  have hqq : (q.totient : ℝ) / q * ((q : ℝ) / q.totient) = 1 := by field_simp
  have key : Gq + 16834 / 100000 * CY.f1 q ≤
      (q.totient : ℝ) / q * (54967 / 10000 + 6273 / 10000 * sumLogP q) := by
    have h1 := mul_le_mul_of_nonneg_left hcomb hu.le
    have e : (q.totient : ℝ) / q * (Gq * ((q : ℝ) / q.totient) + 16834 / 100000 *
        ((q : ℝ) / q.totient * CY.f1 q)) = Gq + 16834 / 100000 * CY.f1 q := by
      linear_combination (Gq + 16834 / 100000 * CY.f1 q) * hqq
    linarith
  have h2 := mul_le_mul_of_nonneg_left hR hu.le
  linarith

end Principia.Common.TernaryGoldbach.ER
