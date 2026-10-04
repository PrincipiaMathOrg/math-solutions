/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EspagnEdgeResB

set_option autoImplicit false

/-!
# Regime L of `EE.EspagnEdgeRes`: `λ(q) ≤ ϖ(q)` on `[1.2·10¹⁰, 2.2·10¹⁰)`

The `λ` side is `LQ`'s rearrangement (`LQ.hipo` at `n = 30`, valid for `q < Π_{p≤31} p`) with the
ten primes `≤ 29` evaluated EXACTLY rather than through Helfgott's cited bounds
(`Π_{p≤29} g(p) ≤ 9.1341`, `Σ_{p≤29} log p/p ≤ 2.3025`, `P29_le`, `S29_le`): then
`λ(q) ≤ (7.45235·9.1341/(0.37268(23.2081 − 2.3025) + 0.02741))³ = 659.95` (`lam_QB`). (Helfgott's
`victoFirst(29, ·)`, built on the cited `1.90516 log p₁` and `e^{0.74914p₁^{1/3}}/6.62365`, gives
only `887` at `1.5·10¹⁰` and so cannot be used below `2.2·10¹⁰`.)

The `ϖ` side: `ϖ₀(1.2·10¹⁰) ≥ 700` (`varpi0_QB`: `A ≥ 167.307`, `D^b ≥ 4.2189`,
`E ≥ 161.8059`, `E^{1/(1−τ)} ≥ e^{5.0863/0.77541628} ≥ 700`), and `ϖ₀` is non-decreasing from
`3.3·10⁹` on (`LQ.varpi0Mono`). The edge round's float scan put the crossover of the exact-signature
bound at `q ≈ 1.029·10¹⁰`; at `1.2·10¹⁰` the margin is `6%` in `ϖ`.
-/

namespace Principia.Common.TernaryGoldbach.ER

open Principia.Common.TernaryGoldbach.HC (omegaE kappaE lambdaE tauE cSig varpi0 varpiE sumLogP
  mertProd)

/-! ## (1) The ten primes `≤ 29`, exactly -/

/-- The primes `≤ 30`. -/
theorem primes30 :
    (Finset.range (30 + 1)).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} := by
  decide

/-- Upper brackets of `g(p)` at the primes `≤ 29`. -/
def gHi29 : ℕ → ℚ
  | 2 => 13451 / 10000
  | 3 => 3499 / 2500
  | 5 => 681 / 500
  | 7 => 2623 / 2000
  | 11 => 2483 / 2000
  | 13 => 6089 / 5000
  | 17 => 11833 / 10000
  | 19 => 1463 / 1250
  | 23 => 11499 / 10000
  | 29 => 11281 / 10000
  | _ => 0

/-- Upper brackets of `log p/p` at the primes `≤ 29`. -/
def sHi : ℕ → ℚ
  | 2 => 1733 / 5000
  | 3 => 3663 / 10000
  | 5 => 3219 / 10000
  | 7 => 139 / 500
  | 11 => 109 / 500
  | 13 => 987 / 5000
  | 17 => 1667 / 10000
  | 19 => 31 / 200
  | 23 => 341 / 2500
  | 29 => 581 / 5000
  | _ => 0

/-- `log p/p ≤ s` from a certified `p ≤ e^{ps}`. -/
theorem fP_le_cert (p : ℕ) (hp : 1 ≤ p) (s : ℝ) (y : ℚ) (hy : 0 ≤ y)
    (hx : (8 : ℕ) * (y : ℝ) ≤ (p : ℝ) * s) (h : (p : ℚ) ≤ tayQ y 14 ^ 8) : LQ.fP p ≤ s := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have he := exp_lo ((p : ℝ) * s) y 14 8 (p : ℚ) hy hx h
  push_cast at he
  have hl := log_le_of hp0 he
  unfold LQ.fP
  rw [div_le_iff₀ hp0]
  linarith

/-- The brackets `g(p) ≤ gHi29(p)`. -/
theorem gP_le_29 (p : ℕ) (hp : p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ)) :
    LQ.gP p ≤ (gHi29 p : ℝ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have e : ((gHi29 2 : ℚ) : ℝ) = 1.3451 := by norm_num [gHi29]
    rw [e]
    exact gP_le_of 2 (by norm_num) 1.259921 1.259922 1.3451 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · have e : ((gHi29 3 : ℚ) : ℝ) = 1.3996 := by norm_num [gHi29]
    rw [e]
    exact gP_le_of 3 (by norm_num) 1.442249 1.44225 1.3996 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · have e : ((gHi29 5 : ℚ) : ℝ) = 1.362 := by norm_num [gHi29]
    rw [e]
    exact gP_le_of 5 (by norm_num) 1.709975 1.709976 1.362 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · have e : ((gHi29 7 : ℚ) : ℝ) = 1.3115 := by norm_num [gHi29]
    rw [e]
    exact gP_le_of 7 (by norm_num) 1.912931 1.912932 1.3115 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · have e : ((gHi29 11 : ℚ) : ℝ) = 1.2415 := by norm_num [gHi29]
    rw [e]
    exact gP_le_of 11 (by norm_num) 2.22398 2.223981 1.2415 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · have e : ((gHi29 13 : ℚ) : ℝ) = 1.2178 := by norm_num [gHi29]
    rw [e]
    exact gP_le_of 13 (by norm_num) 2.351334 2.351335 1.2178 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · have e : ((gHi29 17 : ℚ) : ℝ) = 1.1833 := by norm_num [gHi29]
    rw [e]
    exact gP_le_of 17 (by norm_num) 2.571281 2.571282 1.1833 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · have e : ((gHi29 19 : ℚ) : ℝ) = 1.1704 := by norm_num [gHi29]
    rw [e]
    exact gP_le_of 19 (by norm_num) 2.668401 2.668402 1.1704 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · have e : ((gHi29 23 : ℚ) : ℝ) = 1.1499 := by norm_num [gHi29]
    rw [e]
    exact gP_le_of 23 (by norm_num) 2.843866 2.843867 1.1499 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · have e : ((gHi29 29 : ℚ) : ℝ) = 1.1281 := by norm_num [gHi29]
    rw [e]
    exact gP_le_of 29 (by norm_num) 3.072316 3.072317 1.1281 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

/-- The brackets `log p/p ≤ sHi(p)`. -/
theorem fP_le_29 (p : ℕ) (hp : p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ)) :
    LQ.fP p ≤ (sHi p : ℝ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have e : ((sHi 2 : ℚ) : ℝ) = 1733 / 5000 := by norm_num [sHi]
    rw [e]
    exact fP_le_cert 2 (by norm_num) _ (1733 / 20000) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
  · have e : ((sHi 3 : ℚ) : ℝ) = 3663 / 10000 := by norm_num [sHi]
    rw [e]
    exact fP_le_cert 3 (by norm_num) _ (10989 / 80000) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
  · have e : ((sHi 5 : ℚ) : ℝ) = 3219 / 10000 := by norm_num [sHi]
    rw [e]
    exact fP_le_cert 5 (by norm_num) _ (3219 / 16000) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
  · have e : ((sHi 7 : ℚ) : ℝ) = 139 / 500 := by norm_num [sHi]
    rw [e]
    exact fP_le_cert 7 (by norm_num) _ (973 / 4000) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
  · have e : ((sHi 11 : ℚ) : ℝ) = 109 / 500 := by norm_num [sHi]
    rw [e]
    exact fP_le_cert 11 (by norm_num) _ (1199 / 4000) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
  · have e : ((sHi 13 : ℚ) : ℝ) = 987 / 5000 := by norm_num [sHi]
    rw [e]
    exact fP_le_cert 13 (by norm_num) _ (12831 / 40000) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
  · have e : ((sHi 17 : ℚ) : ℝ) = 1667 / 10000 := by norm_num [sHi]
    rw [e]
    exact fP_le_cert 17 (by norm_num) _ (28339 / 80000) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
  · have e : ((sHi 19 : ℚ) : ℝ) = 31 / 200 := by norm_num [sHi]
    rw [e]
    exact fP_le_cert 19 (by norm_num) _ (589 / 1600) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
  · have e : ((sHi 23 : ℚ) : ℝ) = 341 / 2500 := by norm_num [sHi]
    rw [e]
    exact fP_le_cert 23 (by norm_num) _ (7843 / 20000) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)
  · have e : ((sHi 29 : ℚ) : ℝ) = 581 / 5000 := by norm_num [sHi]
    rw [e]
    exact fP_le_cert 29 (by norm_num) _ (16849 / 40000) (by norm_num) (by push_cast; norm_num)
      (by decide +kernel)

/-- **`Π_{p≤29} p/(p−1) · Π_{p≤29} f₁(p) = Π_{p≤29} g(p) ≤ 9.1341`** (true value `9.130628`). -/
theorem P29_le : mertProd 30 * LQ.f1Prod 30 ≤ 9.1341 := by
  rw [LQ.mert_f1_eq 30, primes30]
  have hpr : ∀ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), p.Prime := by decide
  have h := Finset.prod_le_prod (fun p hp => le_trans zero_le_one (LQ.one_le_gP p (hpr p hp)))
    fun p hp => gP_le_29 p hp
  have hv : (∏ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), gHi29 p : ℚ) ≤
      91341 / 10000 := by
    decide +kernel
  have hv' : ((∏ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), gHi29 p : ℚ) : ℝ) ≤
      ((91341 / 10000 : ℚ) : ℝ) := by
    exact_mod_cast hv
  push_cast at hv'
  linarith

/-- **`Σ_{p≤29} log p/p ≤ 2.3025`** (true value `2.302016`). -/
theorem S29_le : LQ.sumLP 30 ≤ 2.3025 := by
  unfold LQ.sumLP
  rw [primes30]
  have h := Finset.sum_le_sum fun p hp => fP_le_29 p hp
  have hv : (∑ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), sHi p : ℚ) ≤
      23025 / 10000 := by
    decide +kernel
  have hv' : ((∑ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), sHi p : ℚ) : ℝ) ≤
      ((23025 / 10000 : ℚ) : ℝ) := by
    exact_mod_cast hv
  push_cast at hv'
  have e : ∑ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), Real.log p / p =
      ∑ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), LQ.fP p := rfl
  linarith

/-! ## (2) `ϖ₀(1.2·10¹⁰) ≥ 700` -/

/-- `log(1.2·10¹⁰) ∈ [23.2081, 23.2083]`. -/
theorem logQB : 23.2081 ≤ Real.log 1.2e10 ∧ Real.log 1.2e10 ≤ 23.2083 := by
  constructor
  · have h := exp_hi 23.2081 (232081 / 320000) 16 32 12000000000 (by norm_num) (by norm_num)
      (by norm_num) (by push_cast; norm_num) (by decide +kernel)
    have e : ((12000000000 : ℚ) : ℝ) = 1.2e10 := by norm_num
    rw [e] at h
    exact log_ge_of (by norm_num) h
  · have h := exp_lo 23.2083 (232083 / 80000) 14 8 12000000000 (by norm_num)
      (by push_cast; norm_num) (by decide +kernel)
    have e : ((12000000000 : ℚ) : ℝ) = 1.2e10 := by norm_num
    rw [e] at h
    exact log_le_of (by norm_num) h

/-- `A(ℓ) ≥ 167.307` for `ℓ ≥ 23.2081`. -/
theorem vq_A (l : ℝ) (hl1 : 23.2081 ≤ l) : (167.307 : ℝ) ≤ Af l := by
  refine le_trans ?_ (Af_ge l 23.2081 hl1 (by norm_num))
  have h := exp_lo (0.5614593 * (2 / 5 * 23.2081 - 3371 / 20500)) (639979451 / 1000000000) 14 8
    (167307 / 1000) (by norm_num) (by push_cast; norm_num) (by decide +kernel)
  have e : ((167307 / 1000 : ℚ) : ℝ) = 167.307 := by norm_num
  rw [e] at h
  exact h

/-- `b₀ ≤ b`: `τ/(1 − τ)` is at least its value at `τ₀ = 0.22458372`. -/
theorem vq_b : (0.22458372 / (1 - 0.22458372) : ℝ) ≤ tauE / (1 - tauE) := by
  obtain ⟨hτlo, hτhi⟩ := tau_bounds
  rw [div_le_div_iff₀ (by norm_num) (by linarith)]
  linarith

/-- `e^{4.9704} ≤ 144.0987`. -/
theorem vq_e1 : Real.exp 4.9704 ≤ (144.0987 : ℝ) := by
  have h := exp_hi 4.9704 (6213 / 10000) 12 8 (1440987 / 10000) (by norm_num) (by norm_num)
    (by norm_num) (by push_cast; norm_num) (by decide +kernel)
  have e : ((1440987 / 10000 : ℚ) : ℝ) = 144.0987 := by norm_num
  rw [e] at h
  exact h

/-- `4.2189 ≤ e^{b₀·4.9704}`. -/
theorem vq_e2 : (4.2189 : ℝ) ≤ Real.exp (0.22458372 / (1 - 0.22458372) * 4.9704) := by
  have h := exp_lo (0.22458372 / (1 - 0.22458372) * 4.9704) (179947041 / 1000000000) 14 8
    (42189 / 10000) (by norm_num) (by push_cast; norm_num) (by decide +kernel)
  have e : ((42189 / 10000 : ℚ) : ℝ) = 4.2189 := by norm_num
  rw [e] at h
  exact h

/-- `D ≥ 144.0987` ⟹ `D^b ≥ 4.2189`. (Routed through `rpow_ge_of` at a variable base: a goal
holding the numeral power `144.0987^{b₀}` does not elaborate in reasonable time.) -/
theorem vq_Db (D : ℝ) (hD : 144.0987 ≤ D) : (4.2189 : ℝ) ≤ D ^ (tauE / (1 - tauE)) := by
  have hD0 : 0 < D := by linarith
  have hP := rpow_ge_of D 4.9704 4.2189 hD0 (le_trans vq_e1 hD) vq_e2
  have h2 : D ^ (0.22458372 / (1 - 0.22458372) : ℝ) ≤ D ^ (tauE / (1 - tauE)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) vq_b
  exact le_trans hP h2

/-- `E ≥ 161.8059` ⟹ `E^{1/(1−τ)} ≥ 700`. -/
theorem vq_E (E : ℝ) (hE : 161.8059 ≤ E) : (700 : ℝ) ≤ E ^ (1 / (1 - tauE)) := by
  obtain ⟨hτlo, hτhi⟩ := tau_bounds
  have hE0 : 0 < E := by linarith
  have hexp : (1 / (1 - 0.22458372) : ℝ) ≤ 1 / (1 - tauE) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have h1 : E ^ (1 / (1 - 0.22458372) : ℝ) ≤ E ^ (1 / (1 - tauE)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
  have hlE : 5.0863 ≤ Real.log E := by
    refine log_ge_of hE0 (le_trans ?_ hE)
    have h := exp_hi 5.0863 (50863 / 80000) 12 8 (1618059 / 10000) (by norm_num) (by norm_num)
      (by norm_num) (by push_cast; norm_num) (by decide +kernel)
    have e : ((1618059 / 10000 : ℚ) : ℝ) = 161.8059 := by norm_num
    rw [e] at h
    exact h
  have h2 : (700 : ℝ) ≤ E ^ (1 / (1 - 0.22458372) : ℝ) := by
    rw [Real.rpow_def_of_pos hE0]
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (1 - 0.22458372) := ⟨_, rfl⟩
    rw [← hc]
    have hc1 : (1.2896 : ℝ) ≤ c := by rw [hc]; norm_num
    have hm : 5.0863 * 1.2896 ≤ Real.log E * c :=
      mul_le_mul hlE hc1 (by norm_num) (by linarith)
    have h := exp_lo (Real.log E * c) (8195 / 10000) 14 8 700
      (by norm_num) (by push_cast; linarith) (by decide +kernel)
    have e : ((700 : ℚ) : ℝ) = 700 := by norm_num
    rw [e] at h
    exact h
  linarith

/-- **`ϖ₀(Q) ≥ 700` whenever `log Q ∈ [23.2081, 23.2083]`**: `A ≥ 167.307`, `D^b ≥ 4.2189`,
`E ≥ 161.8059`, `E^{1/(1−τ)} ≥ 700`. -/
theorem varpi0_ge (Q : ℝ) (hQ : 0 < Q) (hl1 : 23.2081 ≤ Real.log Q)
    (hl2 : Real.log Q ≤ 23.2083) : (700 : ℝ) ≤ varpi0 Q := by
  have hcq := cq_eq Q hQ
  have hA := vq_A (Real.log Q) hl1
  have hbr : Real.log Q + 1 < cSig 1.36 * Q ^ tauE := by rw [hcq]; linarith
  unfold varpi0
  rw [if_pos hbr, hcq]
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = Real.log Q := ⟨_, rfl⟩
  rw [← hl] at hA hl1 hl2 ⊢
  have hDb := vq_Db (Af l - l) (by linarith)
  have hE : (161.8059 : ℝ) ≤ Af l - l / (Af l - l) ^ (tauE / (1 - tauE)) := by
    have h1 : l / (Af l - l) ^ (tauE / (1 - tauE)) ≤ 23.2083 / 4.2189 :=
      div_le_div₀ (by norm_num) hl2 (by norm_num) hDb
    have h2 : (167.307 : ℝ) - 23.2083 / 4.2189 ≥ 161.8059 := by norm_num
    linarith
  exact vq_E _ hE

/-- **`ϖ₀(1.2·10¹⁰) ≥ 700`** (true value `705.99`). -/
theorem varpi0_QB : (700 : ℝ) ≤ varpi0 1.2e10 :=
  varpi0_ge 1.2e10 (by norm_num) logQB.1 logQB.2

/-! ## (3) `λ(q) ≤ 700` and Regime L -/

/-- **`λ(q) ≤ 700` for `1.2·10¹⁰ ≤ q < 2.2·10¹⁰`** (`659.95`): `LQ.hipo` at `n = 30` with the
exact values at the primes `≤ 29`, and `LQ.lam_le`. -/
theorem lam_QB (cer : CY.CERange) (q : ℕ) (hq : (1.2e10 : ℝ) ≤ q) (hq2 : (q : ℝ) < 2.2e10) :
    lambdaE q ≤ 700 := by
  have hq1 : 1 ≤ q := by
    have : (1 : ℝ) ≤ q := by linarith
    exact_mod_cast this
  have hqn : q < primorial (30 + 1) := by
    have h : primorial (30 + 1) = 200560490130 := by decide
    rw [h]
    have : (q : ℝ) < 200560490130 := by linarith
    exact_mod_cast this
  obtain ⟨hs, hx⟩ := LQ.hipo q 30 hq1 (by norm_num) hqn
  have hP := P29_le
  have hS := S29_le
  have hlq : 23.2081 ≤ Real.log q := le_trans logQB.1 (Real.log_le_log (by norm_num) hq)
  have hW := LQ.omegaE_le cer
  have hcd := LQ.cDelta_ge cer
  have hK : 0.37268 * (23.2081 - 2.3025) + 0.02741 ≤ kappaE q := by
    unfold kappaE
    have h1 : 0 ≤ Real.log q - sumLogP q := by linarith
    have h2 : 0.37268 * (23.2081 - 2.3025) ≤ 0.37268 * (Real.log q - sumLogP q) :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    have h3 : 0.37268 * (Real.log q - sumLogP q) ≤ (1 - omegaE) * (Real.log q - sumLogP q) :=
      mul_le_mul_of_nonneg_right (by linarith) h1
    linarith
  have h := LQ.lam_le cer q hq1 9.1341 _ 7.45235 (le_trans hx hP) (by norm_num) hK
    (LQ.beta_const_le cer)
  refine le_trans h ?_
  norm_num

/-- **Regime L, PROVED.** -/
theorem regL (cer : CY.CERange) : RegL := by
  intro q hq hq2
  have hv := varpi0_QB
  have hmono := LQ.varpi0Mono 1.2e10 q (by norm_num) hq (by linarith)
  have hvE : varpi0 q ≤ varpiE q := le_max_left _ _
  have hlam := lam_QB cer q hq hq2
  linarith

end Principia.Common.TernaryGoldbach.ER
