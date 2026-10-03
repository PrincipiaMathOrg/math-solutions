/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.I2Final
import Principia.Common.TernaryGoldbach.I2Kall

set_option autoImplicit false

/-!
# `MPc.I2Arith` PROVED

`i2Arith : MPc.I2Arith` — the Totals algebra of `S_{I,2}` (`minarctotals.tex` 150-455,
1448-1550, `eq:putbarat`/`eq:douze`/`eq:cheaslu` → `eq:cleson`), for EVERY `x ≥ 3.4·10²³`, from
Chebyshev's `ψ(n) ≤ 1.1096 n + 1150000` (`Principia.Common.Chebyshev.psi_nat_le`) and Mertens'
`∑ Λ(n)/n ≤ log N + log 4 + 4` — no enumeration of `v`, no cited `ψ`-bound (the book uses
Ramaré–Rumely's `ψ(y) ≤ 1.0004y`; with Chebyshev's `1.1096` the book's own route fails, and the
`eq:kallervo2` log-term must be summed by Abel instead of cut by `t log⁺(B/t) ≤ B/e` per `v`).

`T(v) ≤ Gv(v)` (`I2Sum.b2v_le`), `∑ Λ f Gv ≤ TOT` (`I2Sum.sum_le_tot`), `TOT ≤ bI2`
(`tot_le` here, from the allocations of `I2Final` and `I2Kall`).
-/

namespace Principia.Common.TernaryGoldbach.I2A

open ArithmeticFunction
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPA Principia.Common.TernaryGoldbach.MPI1
open Finset

/-! ## (1) Facts in `u`-coordinates -/

/-- `V = 4.5u²`. -/
theorem vA_u (Y : ℝ) (hY0 : 0 < Y) : vA Y = 4.5 * (Y ^ ((1 : ℝ) / 6)) ^ 2 := by
  obtain ⟨-, -, e13, -, -⟩ := rpow_facts Y hY0
  unfold vA; rw [e13]; norm_num

/-- `1 ≤ N ≤ 4.5u²`. -/
theorem NN_facts (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    1 ≤ NN Y ∧ (NN Y : ℝ) ≤ 4.5 * (Y ^ ((1 : ℝ) / 6)) ^ 2 := by
  have hY0 : 0 < Y := by linarith
  have hu := u_ge Y hY
  have hV := vA_u Y hY0
  have hV0 : 0 ≤ vA Y := by rw [hV]; positivity
  unfold NN
  refine ⟨Nat.le_floor ?_, ?_⟩
  · rw [hV]; push_cast; nlinarith
  · rw [← hV]; exact Nat.floor_le hV0

/-- `Ψ ≤ 5.0112u²`. -/
theorem Psi_le (Y : ℝ) (hY : 3.4e23 ≤ Y) : Psi Y ≤ 5.0112 * (Y ^ ((1 : ℝ) / 6)) ^ 2 := by
  have hu := u_ge Y hY
  obtain ⟨-, hN⟩ := NN_facts Y hY
  unfold Psi
  have hu2 : (64000000 : ℝ) ≤ (Y ^ ((1 : ℝ) / 6)) ^ 2 := by nlinarith
  nlinarith

/-- `s² = δ₀q`, `3s² ≤ u²`. -/
theorem s_sq (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    sq δ q ^ 2 = OC.dz δ * q ∧ 3 * sq δ q ^ 2 ≤ (Y ^ ((1 : ℝ) / 6)) ^ 2 := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨-, -, e13, -, -⟩ := rpow_facts Y hY0
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd := dz_ge δ
  have e : sq δ q ^ 2 = OC.dz δ * q := by unfold sq; exact Real.sq_sqrt (by positivity)
  refine ⟨e, ?_⟩
  rw [e, ← e13]
  have := dz_q_le δ _ q hdq hy
  linarith

/-- `log⁺ z ≤ log(4s)`, `z = |δ|q/s`. -/
theorem lz_le (δ : ℝ) (q : ℕ) (hq : 1 ≤ q) : lz δ q ≤ Real.log (4 * sq δ q) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd := dz_ge δ
  have hs1 : 1 ≤ sq δ q := by
    unfold sq; exact Real.one_le_sqrt.mpr (by nlinarith)
  have hs2 : sq δ q ^ 2 = OC.dz δ * q := by unfold sq; exact Real.sq_sqrt (by positivity)
  have hdl : |δ| ≤ 4 * OC.dz δ := by unfold OC.dz; have := le_max_right 2 (|δ| / 4); linarith
  have hz : |δ| * q / sq δ q ≤ 4 * sq δ q := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  unfold lz logp
  have h4 : 0 ≤ Real.log (4 * sq δ q) := Real.log_nonneg (by linarith)
  apply max_le _ h4
  rcases eq_or_lt_of_le (show 0 ≤ |δ| * q / sq δ q by positivity) with h0 | h0
  · rw [← h0, Real.log_zero]; exact h4
  · exact Real.log_le_log h0 hz

/-- `log(4s) ≤ λ + 0.8496` from `3s² ≤ u²`. -/
theorem log4s_lam (u s : ℝ) (hu : 0 < u) (hs : 0 < s) (hs3 : 3 * s ^ 2 ≤ u ^ 2) :
    Real.log (4 * s) ≤ Real.log u + 0.8496 := by
  have h4s : 4 * s ≤ 2.30941 * u := by nlinarith
  have h1 : Real.log (4 * s) ≤ Real.log (2.30941 * u) := Real.log_le_log (by positivity) h4s
  rw [Real.log_mul (by norm_num) hu.ne'] at h1
  have := log_le_div_e 2.30941 (by norm_num)
  linarith

/-- `0 ≤ mR ≤ 1`, `mR·ℓ* ≤ 1.6R`. -/
theorem mR_facts (Y : ℝ) (q : ℕ) (hR : 0 ≤ Rq q) :
    0 ≤ mR Y q ∧ mR Y q ≤ 1 ∧ mR Y q * lstar Y q ≤ 1.6 * Rq q := by
  unfold mR
  split_ifs with h
  · refine ⟨le_min (by norm_num) (div_nonneg (by positivity) h.le), min_le_left _ _, ?_⟩
    calc min 1 (1.6 * Rq q / lstar Y q) * lstar Y q ≤ 1.6 * Rq q / lstar Y q * lstar Y q :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) h.le
      _ = 1.6 * Rq q := by field_simp
  · have h' : lstar Y q ≤ 0 := not_lt.mp h
    refine ⟨by norm_num, le_refl _, ?_⟩
    linarith

/-- `log N ≤ ℓ* + 2 log q + 4.6822`. -/
theorem logN_le (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q) :
    Real.log (NN Y) ≤ lstar Y q + 2 * Real.log q + 4.6822 := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨-, -, e13, -, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  obtain ⟨hN1, hN⟩ := NN_facts Y hY
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hN0 : (0 : ℝ) < NN Y := by exact_mod_cast hN1
  have h1 : Real.log (NN Y) ≤ Real.log (4.5 * u ^ 2) := Real.log_le_log hN0 hN
  have e : 4.5 * u ^ 2 = u ^ 2 / (24 * (q : ℝ) ^ 2) * (108 * (q : ℝ) ^ 2) := by
    field_simp; ring
  rw [e, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
  have hl108 : Real.log 108 ≤ 4.6822 := by
    have e2 : (108 : ℝ) = 2 ^ 2 * 3 ^ 3 := by norm_num
    rw [e2, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    have := Real.log_two_lt_d9
    have := MN.log3_le
    push_cast
    linarith
  unfold lstar
  rw [e13]
  push_cast at h1
  linarith

/-! ## (2) The `Gc` pieces -/

/-- `Gc(1) ≤ 4.27996 U + 1.7721 + log⁺z/2`. -/
theorem Gc_one (Y δ : ℝ) (q : ℕ) (hU : 0 ≤ uA Y δ q) :
    Gc Y δ q 1 ≤ 4.27996 * uA Y δ q + 1.7721 + lz δ q / 2 := by
  unfold Gc
  have hm : min (KK Y δ q / ((1 : ℕ) : ℝ)) (2 * uA Y δ q) ≤ 2 * uA Y δ q := min_le_right _ _
  have hs : Real.sqrt (2 * uA Y δ q * min (KK Y δ q / ((1 : ℕ) : ℝ)) (2 * uA Y δ q)) ≤
      2 * uA Y δ q := by
    rw [Real.sqrt_le_left (by linarith)]
    have h0 : 0 ≤ 2 * uA Y δ q := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hm h0]
  linarith

/-- `∑_{1 < n ≤ N} Gc(n) = 1.7721 S_min + 0.36788 S_√ + (N − 1)(1.7721 + log⁺z/2)`. -/
theorem Gc_sum (Y δ : ℝ) (q N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Ioc 1 N, Gc Y δ q n =
      1.7721 * ∑ n ∈ Ioc 1 N, min (KK Y δ q / n) (2 * uA Y δ q) +
        0.36788 * ∑ n ∈ Ioc 1 N, Real.sqrt (2 * uA Y δ q * min (KK Y δ q / n) (2 * uA Y δ q)) +
        ((N : ℝ) - 1) * (1.7721 + lz δ q / 2) := by
  unfold Gc
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_const,
    sum_const, Nat.card_Ioc, nsmul_eq_mul, nsmul_eq_mul]
  have e : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub hN]; norm_num
  rw [e]
  ring

/-! ## (3) The `eq:kallervo2` main part, by regime -/

/-- Shared facts for the regimes. -/
theorem kp_facts (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    0 < sq δ q ∧ Y / sq δ q = sq δ q * (Y / sq δ q ^ 2) ∧ 0 ≤ Y / sq δ q ^ 2 ∧
      0 ≤ Real.sqrt (cP δ q) ∧ Real.sqrt (cP δ q) ^ 2 = 1 + eta1 / (2 * sq δ q) ∧
      Real.sqrt (cP δ q) ≤ 1 + 1.3863 / sq δ q ∧ 0 ≤ KK Y δ q ∧
      NN Y = ⌊4.5 * (Y ^ ((1 : ℝ) / 6)) ^ 2⌋₊ := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨hs1, -, hP1, -, -⟩ := s_facts Y δ q hY hq hdq hy
  have hs0 : 0 < sq δ q := by linarith
  have hcP0 : 0 ≤ cP δ q := by linarith
  obtain ⟨-, he1b⟩ := eta1_bounds
  refine ⟨hs0, by field_simp, by positivity, Real.sqrt_nonneg _, Real.sq_sqrt hcP0, ?_,
    by unfold KK; positivity, by unfold NN; rw [vA_u Y hY0]⟩
  have h := sqrt_le_half (cP δ q) hcP0
  have : eta1 / (2 * sq δ q) / 2 ≤ 1.3863 / sq δ q := by
    rw [div_div, div_le_div_iff₀ (by positivity) hs0]; nlinarith
  have e : cP δ q = 1 + eta1 / (2 * sq δ q) := rfl
  linarith

/-- **(R3)** at the `Y`-level. -/
theorem kp_R3 (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (h8 : 8 ≤ |δ|) :
    4.24378 * Real.sqrt (cP δ q) *
        (1.7721 * ∑ n ∈ Ioc 1 (NN Y), min (KK Y δ q / n) (2 * uA Y δ q) +
          0.36788 * ∑ n ∈ Ioc 1 (NN Y),
            Real.sqrt (2 * uA Y δ q * min (KK Y δ q / n) (2 * uA Y δ q))) ≤
      0.40 * (Y / sq δ q) +
        (81.917 + 26.8032 * Real.log q + 3.59676 * Real.log (OC.dz δ)) * (Y / sq δ q ^ 2) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  obtain ⟨hs1, hsu, -, -, hsP⟩ := s_facts Y δ q hY hq hdq hy
  obtain ⟨hs2, -⟩ := s_sq Y δ q hY hq hdq hy
  obtain ⟨hs0, hW1, hW2, hsP0, -, -, hKK0, hNdef⟩ := kp_facts Y δ q hY hq hdq hy
  have hUe : uA Y δ q = (Y ^ ((1 : ℝ) / 6)) ^ 4 / (9 * sq δ q) := uA_eq Y δ q hY0
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd0 := dz_ge δ
  have hdz : OC.dz δ = |δ| / 4 := by unfold OC.dz; exact max_eq_right (by linarith)
  have hdq4 : |δ| * q = 4 * sq δ q ^ 2 := by rw [hs2, hdz]; ring
  have hKKe : KK Y δ q = Y / sq δ q ^ 2 / 4 := by unfold KK; rw [hdq4]; field_simp
  have hKz : KK Y δ q * (4 * sq δ q) = (Y ^ ((1 : ℝ) / 6)) ^ 6 / sq δ q := by
    rw [hKKe, ← eY]; field_simp
  obtain ⟨hSm, hSq⟩ := S_regime (Y ^ ((1 : ℝ) / 6)) (sq δ q) (KK Y δ q) (uA Y δ q)
    (4 * sq δ q) hu hs0 hsu hUe hKK0 hKz (by linarith) le_rfl
  rw [← hNdef] at hSm hSq
  have hSm' : ∑ n ∈ Ioc 1 (NN Y), min (KK Y δ q / n) (2 * uA Y δ q) ≤
      Y / sq δ q ^ 2 / 4 * (1.000112 + Real.log (4 * sq δ q)) := by rw [← hKKe]; exact hSm
  have hSq' : ∑ n ∈ Ioc 1 (NN Y), Real.sqrt (2 * uA Y δ q * min (KK Y δ q / n) (2 * uA Y δ q)) ≤
      Y / sq δ q ^ 2 / 4 * (1 + 2 * Real.sqrt (4 * sq δ q)) := by rw [← hKKe]; exact hSq
  have h := R3_alloc (sq δ q) (Real.sqrt (cP δ q)) _ _ (Y / sq δ q ^ 2) hs1 hsP0 hsP hW2 hSm' hSq'
  have hls : 2 * Real.log (sq δ q) = Real.log q + Real.log (OC.dz δ) := by
    have h1 : Real.log (sq δ q ^ 2) = 2 * Real.log (sq δ q) := by
      rw [Real.log_pow]; push_cast; ring
    rw [← h1, hs2, Real.log_mul (by linarith) (by linarith)]
    ring
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hqR
  rw [hW1]
  have hB : (81.917 + 7.19352 * Real.log (sq δ q)) * (Y / sq δ q ^ 2) ≤
      (81.917 + 26.8032 * Real.log q + 3.59676 * Real.log (OC.dz δ)) * (Y / sq δ q ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hW2
  linarith

/-- **(R1)** at the `Y`-level. -/
theorem kp_R1 (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (hs26 : sq δ q ≤ 2.6863) :
    4.24378 * Real.sqrt (cP δ q) *
        (1.7721 * ∑ n ∈ Ioc 1 (NN Y), min (KK Y δ q / n) (2 * uA Y δ q) +
          0.36788 * ∑ n ∈ Ioc 1 (NN Y),
            Real.sqrt (2 * uA Y δ q * min (KK Y δ q / n) (2 * uA Y δ q))) ≤
      0.40 * (Y / sq δ q) +
        (81.917 + 26.8032 * Real.log q + 3.59676 * Real.log (OC.dz δ)) * (Y / sq δ q ^ 2) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨hs1, -, -, -, -⟩ := s_facts Y δ q hY hq hdq hy
  obtain ⟨hs0, hW1, hW2, hsP0, hsc, -, -, -⟩ := kp_facts Y δ q hY hq hdq hy
  have hUe : uA Y δ q = (Y ^ ((1 : ℝ) / 6)) ^ 4 / (9 * sq δ q) := uA_eq Y δ q hY0
  have hU0 := (uA_pos Y δ q hY0 hq).le
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd0 := dz_ge δ
  obtain ⟨he1a, he1b⟩ := eta1_bounds
  have hm1 := smin_le1 (KK Y δ q) (uA Y δ q) hU0 (NN Y)
  have hq1 := ssq_le1 (KK Y δ q) (uA Y δ q) hU0 (NN Y)
  obtain ⟨-, hN⟩ := NN_facts Y hY
  have h2U : 2 * uA Y δ q * (NN Y : ℝ) ≤ sq δ q * (Y / sq δ q ^ 2) := by
    rw [← hW1, hUe]
    have hY6 : Y / sq δ q = (Y ^ ((1 : ℝ) / 6)) ^ 6 / sq δ q := by rw [← eY]
    rw [hY6]
    have : 2 * ((Y ^ ((1 : ℝ) / 6)) ^ 4 / (9 * sq δ q)) * (NN Y : ℝ) ≤
        2 * ((Y ^ ((1 : ℝ) / 6)) ^ 4 / (9 * sq δ q)) * (4.5 * (Y ^ ((1 : ℝ) / 6)) ^ 2) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    have e : 2 * ((Y ^ ((1 : ℝ) / 6)) ^ 4 / (9 * sq δ q)) * (4.5 * (Y ^ ((1 : ℝ) / 6)) ^ 2) =
        (Y ^ ((1 : ℝ) / 6)) ^ 6 / sq δ q := by field_simp; ring
    linarith
  have h := R1_alloc (sq δ q) (Real.sqrt (cP δ q)) eta1 (Y / sq δ q ^ 2) _ _ hs1 hs26 hsP0 hsc
    (by linarith) he1b hW2 (hm1.trans h2U) (hq1.trans h2U)
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hqR
  have hld0 : 0 ≤ Real.log (OC.dz δ) := Real.log_nonneg (by linarith)
  have hB : 34.8 * (Y / sq δ q ^ 2) ≤
      (81.917 + 26.8032 * Real.log q + 3.59676 * Real.log (OC.dz δ)) * (Y / sq δ q ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hW2
  have hW10 : 0 ≤ Y / sq δ q := by positivity
  linarith

/-- **(R2)** at the `Y`-level. -/
theorem kp_R2 (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (hd : ¬ |δ| ≤ 1 / (2 * c2)) (h8 : |δ| < 8) (hs26 : 2.6863 < sq δ q) :
    4.24378 * Real.sqrt (cP δ q) *
        (1.7721 * ∑ n ∈ Ioc 1 (NN Y), min (KK Y δ q / n) (2 * uA Y δ q) +
          0.36788 * ∑ n ∈ Ioc 1 (NN Y),
            Real.sqrt (2 * uA Y δ q * min (KK Y δ q / n) (2 * uA Y δ q))) ≤
      0.40 * (Y / sq δ q) +
        (81.917 + 26.8032 * Real.log q + 3.59676 * Real.log (OC.dz δ)) * (Y / sq δ q ^ 2) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  obtain ⟨-, hsu, -, -, -⟩ := s_facts Y δ q hY hq hdq hy
  obtain ⟨hs2, -⟩ := s_sq Y δ q hY hq hdq hy
  obtain ⟨hs0, hW1, hW2, hsP0, -, hscle, hKK0, hNdef⟩ := kp_facts Y δ q hY hq hdq hy
  have hUe : uA Y δ q = (Y ^ ((1 : ℝ) / 6)) ^ 4 / (9 * sq δ q) := uA_eq Y δ q hY0
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨hc2a, hc2b⟩ := c2_bounds
  have hδ7 : 0.7446 ≤ |δ| := by
    have h1 : 0.7446 ≤ 1 / (2 * c2) := by rw [le_div_iff₀ (by linarith)]; nlinarith
    linarith [not_le.mp hd]
  have hdz : OC.dz δ = 2 := by unfold OC.dz; exact max_eq_left (by linarith)
  have hq2 : (q : ℝ) = sq δ q ^ 2 / 2 := by rw [hs2, hdz]; ring
  have hz1 : |δ| * q / sq δ q = |δ| * sq δ q / 2 := by rw [hq2]; field_simp
  have hz37 : 0.3723 * sq δ q ≤ |δ| * q / sq δ q := by rw [hz1]; nlinarith
  have hzge : 1 ≤ |δ| * q / sq δ q := by nlinarith
  have hz4 : |δ| * q / sq δ q ≤ 4 * sq δ q := by rw [hz1]; nlinarith
  have hKz : KK Y δ q * (|δ| * q / sq δ q) = (Y ^ ((1 : ℝ) / 6)) ^ 6 / sq δ q := by
    rw [← eY]; unfold KK
    have : (0 : ℝ) < |δ| * q := by positivity
    field_simp
  obtain ⟨hSm, hSq⟩ := S_regime (Y ^ ((1 : ℝ) / 6)) (sq δ q) (KK Y δ q) (uA Y δ q)
    (|δ| * q / sq δ q) hu hs0 hsu hUe hKK0 hKz hzge hz4
  rw [← hNdef] at hSm hSq
  have hKz' : KK Y δ q * (|δ| * q / sq δ q) = sq δ q * (Y / sq δ q ^ 2) := by
    rw [hKz, ← eY, ← hW1]
  have h := R2_alloc (sq δ q) (Real.sqrt (cP δ q)) (KK Y δ q) _ _ _ _ hs26.le hsP0 hscle hKK0
    hKz' hz37 hW2 hSm hSq
  have hlq : Real.log q = 2 * Real.log (sq δ q) - Real.log 2 := by
    rw [hq2, Real.log_div (by positivity) (by norm_num), Real.log_pow]; push_cast; ring
  have hl2 := Real.log_two_lt_d9
  have hB : (65.83 + 53.6064 * Real.log (sq δ q)) * (Y / sq δ q ^ 2) ≤
      (81.917 + 26.8032 * Real.log q + 3.59676 * Real.log (OC.dz δ)) * (Y / sq δ q ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ hW2
    rw [hlq, hdz]
    linarith
  rw [hW1]
  linarith

/-- **`4.24378√c₊(1.7721 S_min + 0.36788 S_√) ≤ 0.40 W₁ + B₂ W₂`**, `|δ| > 1/2c₂`. -/
theorem kp_le (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (hd : ¬ |δ| ≤ 1 / (2 * c2)) :
    4.24378 * Real.sqrt (cP δ q) *
        (1.7721 * ∑ n ∈ Ioc 1 (NN Y), min (KK Y δ q / n) (2 * uA Y δ q) +
          0.36788 * ∑ n ∈ Ioc 1 (NN Y),
            Real.sqrt (2 * uA Y δ q * min (KK Y δ q / n) (2 * uA Y δ q))) ≤
      0.40 * (Y / sq δ q) +
        (81.917 + 26.8032 * Real.log q + 3.59676 * Real.log (OC.dz δ)) * (Y / sq δ q ^ 2) := by
  by_cases h8 : 8 ≤ |δ|
  · exact kp_R3 Y δ q hY hq hdq hy h8
  · by_cases hs26 : sq δ q ≤ 2.6863
    · exact kp_R1 Y δ q hY hq hdq hy hs26
    · exact kp_R2 Y δ q hY hq hdq hy hd (not_le.mp h8) (not_le.mp hs26)

/-! ## (4) `TOT ≤ bI2` -/

/-- `k_q ≤ 12.3006 λ + 38.07`. -/
theorem kq_le (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    kq δ q (uA Y δ q) ≤ 12.3006 * Real.log (Y ^ ((1 : ℝ) / 6)) + 38.07 ∧
      0 ≤ kq δ q (uA Y δ q) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hu := u_ge Y hY
  obtain ⟨hs1, -, hP1, hP2, hsP⟩ := s_facts Y δ q hY hq hdq hy
  have hUe : uA Y δ q = (Y ^ ((1 : ℝ) / 6)) ^ 4 / (9 * sq δ q) := uA_eq Y δ q hY0
  have hU1 := uA_ge_one Y δ q hY hq hdq hy
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := by linarith
  have hl0 : 0 ≤ Real.log (2 * uA Y δ q) := Real.log_nonneg (by linarith)
  have hl1 : Real.log (2 * uA Y δ q) ≤ 4 * Real.log u - 0.7777 := by
    have h2U : 2 * uA Y δ q ≤ 2 / 9 * u ^ 4 := by
      rw [hUe]
      have : u ^ 4 / (9 * sq δ q) ≤ u ^ 4 / 9 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      linarith
    have h1 : Real.log (2 * uA Y δ q) ≤ Real.log (2 / 9 * u ^ 4) :=
      Real.log_le_log (by linarith) h2U
    have h2 : Real.log (2 / 9 * u ^ 4) = Real.log (2 / 9) + 4 * Real.log u := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 / 9 by norm_num)
    linarith
  have hsP0 := Real.sqrt_nonneg (cP δ q)
  unfold kq
  constructor
  · have h1 : Real.sqrt (cP δ q) * Real.log (2 * uA Y δ q) ≤ 1.7207 * (4 * Real.log u - 0.7777) :=
      mul_le_mul hsP hl1 hl0 (by norm_num)
    nlinarith
  · positivity

/-- **The keks combination**, abstractly. -/
theorem keks_final (A1 A2 M K R2 W1 W2 Lq LD lam u4 u2 : ℝ)
    (h1 : A1 ≤ R2 + (0.5 * Lq + 6.1864) * W2) (h2 : A2 ≤ 0.6524 * W2 + 9 * u2)
    (h3 : M ≤ 1.99018 * W1 + 2.759 * W2)
    (h4 : K ≤ 0.45764 * W1 + 1.269 * W2 + (10.28 * lam + 32) * u4) (hW1 : 0 ≤ W1)
    (hW2 : 0 ≤ W2) (hLq : 0 ≤ Lq * W2) (hLD : 0 ≤ LD * W2) (hu : 9 * u2 ≤ u4)
    (hlam : 0 ≤ lam * u4) (hu4 : 0 ≤ u4) :
    A1 + A2 + M + K ≤
      2.49157 * W1 + R2 + (3.59676 * LD + 27.3032 * Lq + 91.515) * W2 +
        (22.9812 * (6 * lam) + 411.424) * u4 := by
  linarith

/-- The `x`-level right side, rewritten. -/
theorem bI2_eq (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    bI2 Y δ q = 2.49157 * (Y / sq δ q) +
      capM (4 * 0.798437) δ * (Y / Nat.totient q) * (3 / 2 * Real.log q + 2.74107) +
      (3.59676 * Real.log (OC.dz δ) + 27.3032 * Real.log q + 91.515) * (Y / sq δ q ^ 2) +
      (22.9812 * (6 * Real.log (Y ^ ((1 : ℝ) / 6))) + 411.424) * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, -, -, -, eL⟩ := rpow_facts Y hY0
  obtain ⟨hs2, -⟩ := s_sq Y δ q hY hq hdq hy
  have hsq : Real.sqrt (OC.dz δ * q) = sq δ q := rfl
  have hW2e : Y / (q * OC.dz δ) = Y / sq δ q ^ 2 := by rw [hs2, mul_comm]
  unfold bI2
  rw [hsq, hW2e, e23, eL]
  ring

/-- **`TOT ≤ bI2` for `|δ| ≤ 1/2c₂`.** -/
theorem tot_keks (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (hd : |δ| ≤ 1 / (2 * c2)) : TOT Y δ q ≤ bI2 Y δ q := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨hu, hlam1, -, -, -, -, -, -, -, -⟩ := u_data Y δ q hY hq hdq hy
  obtain ⟨hs1, -, -, -, -⟩ := s_facts Y δ q hY hq hdq hy
  obtain ⟨hs2, -⟩ := s_sq Y δ q hY hq hdq hy
  obtain ⟨-, hN⟩ := NN_facts Y hY
  have hPsi := Psi_le Y hY
  have hUe : uA Y δ q = (Y ^ ((1 : ℝ) / 6)) ^ 4 / (9 * sq δ q) := uA_eq Y δ q hY0
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd0 := dz_ge δ
  have hR := r_ge_one q hq
  obtain ⟨hm0, hm1, hml⟩ := mR_facts Y q (by unfold Rq; positivity)
  have hLN := logN_le Y q hY hq
  obtain ⟨hk, -⟩ := kq_le Y δ q hY hq hdq hy
  obtain ⟨he1a, he1b⟩ := eta1_bounds
  have hcap0 : 0 ≤ capM (c0 / Real.pi ^ 2) δ := capM_nonneg _ δ (by unfold c0; positivity)
  have hcapd : capM (c0 / Real.pi ^ 2) δ ≤ 2 / OC.dz δ := by
    obtain ⟨hp1, -⟩ := pi_sq_bounds
    apply capM_le _ δ (by unfold c0; positivity)
    rw [div_le_iff₀ (by positivity)]; unfold c0; nlinarith
  have hPsi0 : 0 ≤ Psi Y := by unfold Psi; positivity
  have hq6 : (q : ℝ) ≤ (Y ^ ((1 : ℝ) / 6)) ^ 2 / 6 := by rw [← e13]; exact hy
  have hA1 := a1_alloc _ _ (OC.dz δ) (Rq q) (mR Y q) (Real.log q) (lstar Y q) (Real.log (NN Y))
    (Y / (2 * q)) hcap0 (cap1_le δ) (by linarith) hcapd hR hm0 hm1 hml hLN
    (Real.log_nonneg hqR) (by positivity)
  have hA2 := a2_alloc (Y ^ ((1 : ℝ) / 6)) (sq δ q) (uA Y δ q) (NN Y) (Psi Y) q hu hs1 hUe hN
    hPsi0 hPsi (by positivity) hq6
  have hM := m_alloc (Y ^ ((1 : ℝ) / 6)) (sq δ q) (uA Y δ q) (NN Y) (Psi Y) eta1 hu hs1 hUe
    (by positivity) hN hPsi0 hPsi (by linarith) he1b
  have hK := keks_alloc (Y ^ ((1 : ℝ) / 6)) (sq δ q) (uA Y δ q) (Psi Y) q (cP δ q)
    (kq δ q (uA Y δ q)) (Real.log (Y ^ ((1 : ℝ) / 6))) eta1 hs1 hUe hPsi0 hPsi (by positivity)
    hq6 rfl (by linarith) he1b hk (by linarith)
  rw [← eY] at hA2 hM hK
  have hYphi : Y / Nat.totient q = 2 * (Y / (2 * q)) * Rq q := by
    unfold Rq
    have : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    field_simp
  have hYdz : 2 * (Y / (2 * q)) / OC.dz δ = Y / sq δ q ^ 2 := by
    rw [hs2]; field_simp
  rw [← hYphi, hYdz] at hA1
  have hs0 : 0 < sq δ q := by linarith
  have hW10 : 0 ≤ Y / sq δ q := by positivity
  have hW20 : 0 ≤ Y / sq δ q ^ 2 := by positivity
  have hlq : 0 ≤ Real.log q * (Y / sq δ q ^ 2) :=
    mul_nonneg (Real.log_nonneg hqR) hW20
  have hld : 0 ≤ Real.log (OC.dz δ) * (Y / sq δ q ^ 2) :=
    mul_nonneg (Real.log_nonneg (by linarith)) hW20
  have hu0 : 0 < Y ^ ((1 : ℝ) / 6) := by linarith
  have hu2 : 9 * (Y ^ ((1 : ℝ) / 6)) ^ 2 ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
    have h1 : (9 : ℝ) ≤ (Y ^ ((1 : ℝ) / 6)) ^ 2 :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 2)
    have e : (Y ^ ((1 : ℝ) / 6)) ^ 4 = (Y ^ ((1 : ℝ) / 6)) ^ 2 * (Y ^ ((1 : ℝ) / 6)) ^ 2 := by
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hlam : 0 ≤ Real.log (Y ^ ((1 : ℝ) / 6)) * (Y ^ ((1 : ℝ) / 6)) ^ 4 :=
    mul_nonneg (by linarith) (by positivity)
  rw [bI2_eq Y δ q hY hq hdq hy]
  unfold TOT
  rw [if_pos hd]
  exact keks_final _ _ _ _ _ _ _ _ _ _ _ _ hA1 hA2 hM hK hW10 hW20 hlq hld hu2 hlam
    (by positivity)

/-- **The kallervo combination**, abstractly. -/
theorem kall_final (A1 A2 M SGv Gnc Lt R2 W1 W2 Lq LD lam u4 u2 cpr X N1 c Gc1 G1b : ℝ)
    (h1 : A1 ≤ R2 + (0.5 * Lq + 6.1864) * W2) (h2 : A2 ≤ 0.6524 * W2 + 9 * u2)
    (h3 : M ≤ 1.99018 * W1 + 2.759 * W2)
    (hsg : SGv ≤ (1.1096 + 1150000) * Gc1 + 1.1096 * (X + N1 * c)) (hgc : Gc1 ≤ G1b)
    (hB : 3.8246 * cpr * ((1.1096 + 1150000) * G1b + 1.1096 * N1 * c + Gnc) ≤ 0.0605 * W1)
    (hKP : 4.24378 * cpr * X ≤ 0.40 * W1 + (81.917 + 26.8032 * Lq + 3.59676 * LD) * W2)
    (hL : Lt ≤ (137.887 * lam + 411.424) * u4 + 0.035 * W1)
    (hcpr : 0 ≤ cpr) (hX : 0 ≤ X) (hW1 : 0 ≤ W1) (hW2 : 0 ≤ W2) (hLq : 0 ≤ Lq * W2)
    (hLD : 0 ≤ LD * W2) (h9 : 9 * u2 ≤ 0.001 * W1) (hlam : 0 ≤ lam * u4) :
    A1 + A2 + M + (3.8246 * cpr * (SGv + Gnc) + Lt) ≤
      2.49157 * W1 + R2 + (3.59676 * LD + 27.3032 * Lq + 91.515) * W2 +
        (22.9812 * (6 * lam) + 411.424) * u4 := by
  have hc0 : 0 ≤ 3.8246 * cpr := by positivity
  have e1 : 3.8246 * cpr * SGv ≤
      3.8246 * cpr * ((1.1096 + 1150000) * Gc1 + 1.1096 * (X + N1 * c)) :=
    mul_le_mul_of_nonneg_left hsg hc0
  have e2 : 3.8246 * cpr * ((1.1096 + 1150000) * Gc1) ≤
      3.8246 * cpr * ((1.1096 + 1150000) * G1b) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgc (by norm_num)) hc0
  have e3 : 3.8246 * 1.1096 * (cpr * X) ≤ 4.24378 * (cpr * X) :=
    mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hcpr hX)
  linarith

/-- `log q ≤ 2λ`. -/
theorem logq_le2 (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    Real.log q ≤ 2 * Real.log (Y ^ ((1 : ℝ) / 6)) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, -, -⟩ := rpow_facts Y hY0
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : (q : ℝ) ≤ (Y ^ ((1 : ℝ) / 6)) ^ 2 := by
    rw [← e13]
    exact hy.trans (div_le_self (Real.rpow_pos_of_pos hY0 _).le (by norm_num))
  have h1 : Real.log q ≤ Real.log ((Y ^ ((1 : ℝ) / 6)) ^ 2) := Real.log_le_log (by linarith) hq2
  rw [Real.log_pow] at h1; push_cast at h1; linarith

/-- `log N ≤ 2λ + 1.6555`. -/
theorem logN_le2 (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    Real.log (NN Y) ≤ 2 * Real.log (Y ^ ((1 : ℝ) / 6)) + 1.6555 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hu := u_ge Y hY
  obtain ⟨hN1, hN⟩ := NN_facts Y hY
  have hN0 : (0 : ℝ) < NN Y := by exact_mod_cast hN1
  have h1 : Real.log (NN Y) ≤ Real.log (4.5 * (Y ^ ((1 : ℝ) / 6)) ^ 2) := Real.log_le_log hN0 hN
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
  have := log_le_div_e 4.5 (by norm_num)
  push_cast at h1; linarith

/-- `9u² ≤ 0.001·x/s`. -/
theorem nine_le (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    9 * (Y ^ ((1 : ℝ) / 6)) ^ 2 ≤ 0.001 * (Y / sq δ q) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  obtain ⟨hs1, hsu, -, -, -⟩ := s_facts Y δ q hY hq hdq hy
  have hs0 : 0 < sq δ q := by linarith
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := by linarith
  rw [mul_div_assoc', le_div_iff₀ hs0]
  have h1 : 9 * u ^ 2 * sq δ q ≤ 9 * u ^ 3 := by
    have := mul_le_mul_of_nonneg_left hsu (by positivity : (0 : ℝ) ≤ 9 * u ^ 2)
    nlinarith
  have h3 : (9000 : ℝ) ≤ u ^ 3 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 3)
  have h2 : 9000 * u ^ 3 ≤ u ^ 6 := by
    have e : u ^ 6 = u ^ 3 * u ^ 3 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h3 (by positivity)
  rw [eY]
  nlinarith

/-- **`TOT ≤ bI2` for `|δ| > 1/2c₂`.** -/
theorem tot_kall (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (hd : ¬ |δ| ≤ 1 / (2 * c2)) : TOT Y δ q ≤ bI2 Y δ q := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨hu, hlam1, -, -, -, -, -, -, hlamU, hlam2⟩ := u_data Y δ q hY hq hdq hy
  obtain ⟨hs1, hsu, hP1, -, hsP⟩ := s_facts Y δ q hY hq hdq hy
  obtain ⟨hs2, hs3⟩ := s_sq Y δ q hY hq hdq hy
  obtain ⟨hN1, hN⟩ := NN_facts Y hY
  have hPsi := Psi_le Y hY
  have hUe : uA Y δ q = (Y ^ ((1 : ℝ) / 6)) ^ 4 / (9 * sq δ q) := uA_eq Y δ q hY0
  have hU0 := (uA_pos Y δ q hY0 hq).le
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd0 := dz_ge δ
  have hR := r_ge_one q hq
  obtain ⟨hm0, hm1, hml⟩ := mR_facts Y q (by unfold Rq; positivity)
  have hLN := logN_le Y q hY hq
  obtain ⟨he1a, he1b⟩ := eta1_bounds
  have hcap0 : 0 ≤ capM (c0 / Real.pi ^ 2) δ := capM_nonneg _ δ (by unfold c0; positivity)
  have hcapd : capM (c0 / Real.pi ^ 2) δ ≤ 2 / OC.dz δ := by
    obtain ⟨hp1, -⟩ := pi_sq_bounds
    apply capM_le _ δ (by unfold c0; positivity)
    rw [div_le_iff₀ (by positivity)]; unfold c0; nlinarith
  have hPsi0 : 0 ≤ Psi Y := by unfold Psi; positivity
  have hq6 : (q : ℝ) ≤ (Y ^ ((1 : ℝ) / 6)) ^ 2 / 6 := by rw [← e13]; exact hy
  have hs0 : 0 < sq δ q := by linarith
  have hu0 : 0 < Y ^ ((1 : ℝ) / 6) := by linarith
  -- the common parts
  have hA1 := a1_alloc _ _ (OC.dz δ) (Rq q) (mR Y q) (Real.log q) (lstar Y q) (Real.log (NN Y))
    (Y / (2 * q)) hcap0 (cap1_le δ) (by linarith) hcapd hR hm0 hm1 hml hLN
    (Real.log_nonneg hqR) (by positivity)
  have hA2 := a2_alloc (Y ^ ((1 : ℝ) / 6)) (sq δ q) (uA Y δ q) (NN Y) (Psi Y) q hu hs1 hUe hN
    hPsi0 hPsi (by positivity) hq6
  have hM := m_alloc (Y ^ ((1 : ℝ) / 6)) (sq δ q) (uA Y δ q) (NN Y) (Psi Y) eta1 hu hs1 hUe
    (by positivity) hN hPsi0 hPsi (by linarith) he1b
  -- the `eq:kallervo2` parts
  have hlz0 : 0 ≤ lz δ q := le_max_right _ _
  have hlz4 := lz_le δ q hq
  have hl4s := log4s_lam (Y ^ ((1 : ℝ) / 6)) (sq δ q) hu0 hs0 hs3
  have hKK0 : 0 ≤ KK Y δ q := by unfold KK; positivity
  have hSG := sg_abel Y δ q hKK0 hU0 hlz0 hN1
  rw [Gc_sum Y δ q (NN Y) hN1] at hSG
  have hGc1 := Gc_one Y δ q hU0
  have hKP := kp_le Y δ q hY hq hdq hy hd
  have hl3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]; have := Real.exp_one_lt_d9; linarith
  have hLq2 := logq_le2 Y q hY hq hy
  have hLN2 := logN_le2 Y hY
  have hB := B_alloc (Y ^ ((1 : ℝ) / 6)) (sq δ q) (Real.log (Y ^ ((1 : ℝ) / 6))) (uA Y δ q)
    (NN Y) (Real.sqrt (cP δ q)) (lz δ q) (Real.log q) (Real.log (NN Y)) (Real.log 3) hu hs1 hsu
    hUe hsP hlz0 (hlz4.trans hl4s) hlam1 hlamU hlam2 (by exact_mod_cast hN1) hN
    (Real.log_nonneg hqR) hLq2 (Real.log_nonneg (by exact_mod_cast hN1)) hLN2 hl3
  have hL := L_alloc (Y ^ ((1 : ℝ) / 6)) (sq δ q) (Real.log (Y ^ ((1 : ℝ) / 6))) (cP δ q)
    (lz δ q) (Psi Y) q eta1 hu hs1 hs3 rfl (by linarith) he1b hlz0 hlz4 rfl hlamU hPsi0 hPsi hq6
  rw [← eY] at hA2 hM hB hL
  rw [← e13] at hL
  -- rewrite `bI2`'s parts
  have hYphi : Y / Nat.totient q = 2 * (Y / (2 * q)) * Rq q := by
    unfold Rq
    have : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    field_simp
  have hYdz : 2 * (Y / (2 * q)) / OC.dz δ = Y / sq δ q ^ 2 := by
    rw [hs2]; field_simp
  rw [← hYphi, hYdz] at hA1
  have hW20 : 0 ≤ Y / sq δ q ^ 2 := by positivity
  have hlq : 0 ≤ Real.log q * (Y / sq δ q ^ 2) := mul_nonneg (Real.log_nonneg hqR) hW20
  have hld : 0 ≤ Real.log (OC.dz δ) * (Y / sq δ q ^ 2) :=
    mul_nonneg (Real.log_nonneg (by linarith)) hW20
  have hlam : 0 ≤ Real.log (Y ^ ((1 : ℝ) / 6)) * (Y ^ ((1 : ℝ) / 6)) ^ 4 :=
    mul_nonneg (by linarith) (by positivity)
  have h9 := nine_le Y δ q hY hq hdq hy
  have hX : 0 ≤ 1.7721 * ∑ n ∈ Ioc 1 (NN Y), min (KK Y δ q / n) (2 * uA Y δ q) +
      0.36788 * ∑ n ∈ Ioc 1 (NN Y),
        Real.sqrt (2 * uA Y δ q * min (KK Y δ q / n) (2 * uA Y δ q)) := by
    have h1 : 0 ≤ ∑ n ∈ Ioc 1 (NN Y), min (KK Y δ q / n) (2 * uA Y δ q) :=
      sum_nonneg fun n _ => le_min (by positivity) (by linarith)
    have h2 : 0 ≤ ∑ n ∈ Ioc 1 (NN Y),
        Real.sqrt (2 * uA Y δ q * min (KK Y δ q / n) (2 * uA Y δ q)) :=
      sum_nonneg fun n _ => Real.sqrt_nonneg _
    positivity
  rw [bI2_eq Y δ q hY hq hdq hy]
  unfold TOT
  rw [if_neg hd]
  exact kall_final _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA1 hA2 hM hSG hGc1 hB hKP hL
    (Real.sqrt_nonneg _) hX (by positivity) hW20 hlq hld h9 hlam

/-- **`TOT ≤ bI2`.** -/
theorem tot_le (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    TOT Y δ q ≤ bI2 Y δ q := by
  by_cases hd : |δ| ≤ 1 / (2 * c2)
  · exact tot_keks Y δ q hY hq hdq hy hd
  · exact tot_kall Y δ q hY hq hdq hy hd

/-! ## (5) `I2Arith` -/

/-- **`MPc.I2Arith`, PROVED.** -/
theorem i2Arith : I2Arith := by
  intro Y hY δ q hq hdq hy T hT
  have hY0 : (0 : ℝ) < Y := by linarith
  have hN1 := (NN_facts Y hY).1
  have hV0 : 0 ≤ vA Y := by rw [vA_u Y hY0]; positivity
  calc ∑ v ∈ Ioc 0 ⌊vA Y⌋₊, Λ v * fOdd v * T v
      ≤ ∑ v ∈ Ioc 0 ⌊vA Y⌋₊, Λ v * fOdd v * Gv Y δ q v := by
        refine sum_le_sum fun v hv => ?_
        have hv1 : 1 ≤ v := (mem_Ioc.mp hv).1
        have hvN : v ≤ ⌊vA Y⌋₊ := (mem_Ioc.mp hv).2
        obtain ⟨M, s, hM1, -, hs, hron, hTv⟩ := hT v hv1 hvN
        have hvV : (v : ℝ) ≤ vA Y := le_trans (by exact_mod_cast hvN) (Nat.floor_le hV0)
        have hsm : Nat.Coprime v q → |s| ≤ mR Y q := fun hc =>
          s_le_mR Y δ q hY hq hdq hy v hv1 hvV hc M s hM1 hs hron
        exact mul_le_mul_of_nonneg_left
          (hTv.trans (b2v_le Y δ q hY hq hdq hy v hv1 hvV s hs hsm)) (lf_nonneg v)
    _ ≤ TOT Y δ q := sum_le_tot Y δ q hY hq hdq hy hN1
    _ ≤ bI2 Y δ q := tot_le Y δ q hY hq hdq hy

end Principia.Common.TernaryGoldbach.I2A
