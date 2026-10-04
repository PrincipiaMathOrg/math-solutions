/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIISpineC
import Principia.Common.TernaryGoldbach.HelfgottCited

set_option autoImplicit false

/-!
# `T2SC.Menson2C` spined; its `HOkC` half PROVED for Helfgott's explicit `H₂`

`T2SC.Menson2C` asks for ONE `H` with `T2SC.HOkC H` bounding every `S₁(U, W)`. The book's `H₂`
(`eq:palmiped`) is `(4/π²)G₂(S)` on `[1, 16)` and `0.15107` above, where `G₂` is the exact value
of `eq:grotto` (`HC.cortoLHS 2`) on `[1, 16)`: "`G_v(S) = K_{v,1}(⌊S⌋) + K_{v,2}(⌊S⌋)/S`, where
`K_{v,1}(n)`, `K_{v,2}(n)` can be computed explicitly" (`typeII.tex` 783-790; not printed).
`K1t`, `K2t` below are those values, computed exactly in rationals from `eq:greco`
(`scratchpad/t2s/ktab.py`; checks: `1 − 1/S` on `[1, 2)` as printed, `1/2` on `[2, 3)`,
`1/3 + 1/(2S)` on `[3, 4)`).

```
 h2OkC        HOkC H2tab: 0 ≤ H₂ ≤ 2/π², integrable, ∫_1^T H₂/s ≤ 0.15107 log T + 0.0231   PROVED
 MonroFleming eq:crusto, eq:cudo, lem:monro (eq:mudo), eq:flatow, eq:fleming        DEEP; OPEN
 GrottoTab    eq:grotto = G₂tab on [1, 16)   (eq:greco summed; a finite identity)  FINITE; OPEN
 CortoLarge   eq:corto for S ≥ 10⁵ (lem:yutto, HC.RamareCited, HC.CortoC0Cited)    DEEP; OPEN
 HC.CortoSmallCited   eq:corto on [16, 10⁵)                                          CITED
 menson2C_of_links : Menson2C                                                      PROVED
```

**`h2OkC` is a real computation, done in the kernel.** On `[n, n+1)`, `H₂(s)/s` is
`(4/π²)(K₁ + K₂/s)/s`, whose integral is `K₁ log + K₂(1/n − 1/T)` (FTC). With `4/π² ≤ 0.405285`
(`π > 3.141592`) and `log((j+1)/j)` to `10⁻⁷` (Mathlib's `abs_log_sub_add_sum_range_le`, 14
terms), the excess `φ(T) = ∫_1^T H₂/s − 0.15107 log T` is bounded piece by piece: on `[1, 2]` by
`log T ≤ 2(√T − 1)`; on `[n, n+1]`, `2 ≤ n ≤ 14`, `φ` is increasing (`G₂ ≥ 0.15107π²/4` there) so
`φ(T) ≤ φ(n+1)`; on `[15, 16]` by `log(T/15) ≥ 1 − 15/T`; above `16` `φ` is constant.

**Finding (minor, harmless).** The `TypeIISpineC` note says the excess "peaks at `0.023051` at
`T = 16`". It does not: on `[15, 16]` `G₂` crosses `0.15107π²/4` at `S ≈ 15.578`, where
`φ = 0.0230589`; `φ(16) = 0.0230508`. Both are below `0.0231`, so `HOkC` holds as stated.
-/

namespace Principia.Common.TernaryGoldbach.M2H

open MeasureTheory Set
open Principia.Common.TernaryGoldbach.T2S Principia.Common.TernaryGoldbach.T2SC

/-- `K_{2,1}(n)`, `1 ≤ n ≤ 15` (`G₂ = K₁ + K₂/S` on `[n, n+1)`). -/
noncomputable def K1t : ℕ → ℝ
  | 1 => 1 | 2 => 1 / 2 | 3 => 1 / 3 | 4 => 1 / 3 | 5 => 17 / 60 | 6 => 11 / 30
  | 7 => 611 / 1680 | 8 => 611 / 1680 | 9 => 1553 / 5040 | 10 => 1679 / 5040
  | 11 => 9637 / 27720 | 12 => 9637 / 27720 | 13 => 16712 / 45045 | 14 => 536929 / 1441440
  | 15 => 113819 / 360360 | _ => 0

/-- `K_{2,2}(n)`, `1 ≤ n ≤ 15`. -/
noncomputable def K2t : ℕ → ℝ
  | 1 => -1 | 2 => 0 | 3 => 1 / 2 | 4 => 1 / 2 | 5 => 3 / 4 | 6 => 1 / 4 | 7 => 13 / 48
  | 8 => 13 / 48 | 9 => 37 / 48 | 10 => 25 / 48 | 11 => 13 / 36 | 12 => 13 / 36
  | 13 => 29 / 504 | 14 => 37 / 1008 | 15 => 1787 / 2016 | _ => 0

/-- **`G₂(S) = K₁(⌊S⌋) + K₂(⌊S⌋)/S`** (`typeII.tex` 786-790). -/
noncomputable def G2tab (S : ℝ) : ℝ := K1t ⌊S⌋₊ + K2t ⌊S⌋₊ / S

/-- **Helfgott's `H₂`** (`eq:palmiped`): `(4/π²)G₂(S)` below `16`, `0.15107` from `16` on. -/
noncomputable def H2tab (S : ℝ) : ℝ := if S < 16 then 4 / Real.pi ^ 2 * G2tab S else 0.15107

/-- `H₂` with `4/π²` replaced by the upper bound `0.405285` (the integral's majorant). -/
noncomputable def Hh (S : ℝ) : ℝ := if S < 16 then 0.405285 * G2tab S else 0.15107

/-! ## (1) Elementary facts -/

theorem floor_eq (n : ℕ) (s : ℝ) (h1 : (n : ℝ) ≤ s) (h2 : s < n + 1) : ⌊s⌋₊ = n :=
  (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg n) h1)).mpr ⟨h1, h2⟩

theorem piece_of (s : ℝ) (h1 : 1 ≤ s) (h16 : s < 16) :
    1 ≤ ⌊s⌋₊ ∧ ⌊s⌋₊ ≤ 15 ∧ (⌊s⌋₊ : ℝ) ≤ s ∧ s < ⌊s⌋₊ + 1 := by
  have hs0 : 0 ≤ s := by linarith
  refine ⟨Nat.le_floor (by exact_mod_cast h1), ?_, Nat.floor_le hs0, Nat.lt_floor_add_one s⟩
  have : ⌊s⌋₊ < 16 := (Nat.floor_lt hs0).mpr (by exact_mod_cast h16)
  omega

theorem k_bounds : 0.405284 ≤ 4 / Real.pi ^ 2 ∧ 4 / Real.pi ^ 2 ≤ 0.405285 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  have hp : 0 < Real.pi ^ 2 := by positivity
  have hl : (3.141592 : ℝ) ^ 2 < Real.pi ^ 2 := pow_lt_pow_left₀ h1 (by norm_num) two_ne_zero
  have hu : Real.pi ^ 2 < (3.141593 : ℝ) ^ 2 := pow_lt_pow_left₀ h2 (by positivity) two_ne_zero
  constructor
  · rw [le_div_iff₀ hp]
    nlinarith
  · rw [div_le_iff₀ hp]
    nlinarith

/-- **`0 ≤ G₂ ≤ 1/2` on `[1, 16)`** (so `0 ≤ H₂ ≤ 2/π²`, `eq:demimond`). -/
theorem g2tab_bounds (s : ℝ) (h1 : 1 ≤ s) (h16 : s < 16) : 0 ≤ G2tab s ∧ G2tab s ≤ 1 / 2 := by
  obtain ⟨hn1, hn15, hns, hsn⟩ := piece_of s h1 h16
  have hs0 : 0 < s := by linarith
  have hn0 : (0 : ℝ) < ⌊s⌋₊ := by exact_mod_cast hn1
  have hiu : s⁻¹ ≤ 1 / (⌊s⌋₊ : ℝ) := by
    rw [one_div]
    exact inv_anti₀ hn0 hns
  have hil : 1 / ((⌊s⌋₊ : ℝ) + 1) < s⁻¹ := by
    rw [one_div]
    exact inv_strictAnti₀ hs0 hsn
  unfold G2tab
  rw [div_eq_mul_inv]
  generalize ⌊s⌋₊ = n at hn1 hn15 hiu hil
  interval_cases n <;> simp only [K1t, K2t] <;> norm_num at hiu hil ⊢ <;>
    constructor <;> nlinarith [inv_pos.mpr hs0]

theorem meas_G : Measurable G2tab :=
  ((measurable_from_nat (f := K1t)).comp Nat.measurable_floor).add
    (((measurable_from_nat (f := K2t)).comp Nat.measurable_floor).div measurable_id)

theorem meas_H : Measurable H2tab :=
  Measurable.ite measurableSet_Iio (measurable_const.mul meas_G) measurable_const

theorem meas_Hh : Measurable Hh :=
  Measurable.ite measurableSet_Iio (measurable_const.mul meas_G) measurable_const

/-- A measurable function bounded on `(a, b]` is interval integrable there. -/
theorem ii_of_bdd (f : ℝ → ℝ) (hf : Measurable f) (M a b : ℝ) (hab : a ≤ b)
    (hM : ∀ s ∈ Ioc a b, |f s| ≤ M) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
    hf.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  rw [Real.norm_eq_abs]
  exact hM s hs

/-- `0 ≤ H₂ ≤ 2/π²` for `s ≥ 1` (`eq:demimond`). -/
theorem h2_bounds (s : ℝ) (h1 : 1 ≤ s) : 0 ≤ H2tab s ∧ H2tab s ≤ 2 / Real.pi ^ 2 := by
  have hp : 0 < Real.pi ^ 2 := by positivity
  unfold H2tab
  split_ifs with h
  · obtain ⟨g0, g1⟩ := g2tab_bounds s h1 h
    refine ⟨by positivity, ?_⟩
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hp]
    linarith
  · refine ⟨by norm_num, ?_⟩
    have h2 := Real.pi_lt_d2
    have hu : Real.pi ^ 2 < (3.15 : ℝ) ^ 2 := pow_lt_pow_left₀ h2 (by positivity) two_ne_zero
    rw [le_div_iff₀ hp]
    nlinarith

theorem hh_bounds (s : ℝ) (h1 : 1 ≤ s) : 0 ≤ Hh s ∧ Hh s ≤ 1 := by
  unfold Hh
  split_ifs with h
  · obtain ⟨g0, g1⟩ := g2tab_bounds s h1 h
    constructor <;> nlinarith
  · constructor <;> norm_num

/-- `H₂ ≤ Ĥ` on `[1, ∞)`. -/
theorem h2_le_hh (s : ℝ) (h1 : 1 ≤ s) : H2tab s ≤ Hh s := by
  unfold H2tab Hh
  split_ifs with h
  · exact mul_le_mul_of_nonneg_right k_bounds.2 (g2tab_bounds s h1 h).1
  · exact le_rfl

theorem ii_H (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) : IntervalIntegrable H2tab volume a b := by
  refine ii_of_bdd _ meas_H 1 a b hab fun s hs => ?_
  obtain ⟨h0, h2⟩ := h2_bounds s (by linarith [hs.1])
  have hp := Real.pi_gt_d2
  have : 2 / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  rw [abs_of_nonneg h0]
  linarith

theorem ii_Hs (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun s => H2tab s / s) volume a b := by
  refine ii_of_bdd (fun s => H2tab s / s) (meas_H.div measurable_id) 1 a b hab fun s hs => ?_
  have hs1 : 1 ≤ s := by linarith [hs.1]
  obtain ⟨h0, h2⟩ := h2_bounds s hs1
  have hp := Real.pi_gt_d2
  have : 2 / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  rw [abs_of_nonneg (div_nonneg h0 (by linarith)), div_le_one (by linarith)]
  linarith

theorem ii_Hhs (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun s => Hh s / s) volume a b := by
  refine ii_of_bdd (fun s => Hh s / s) (meas_Hh.div measurable_id) 1 a b hab fun s hs => ?_
  have hs1 : 1 ≤ s := by linarith [hs.1]
  obtain ⟨h0, h2⟩ := hh_bounds s hs1
  rw [abs_of_nonneg (div_nonneg h0 (by linarith)), div_le_one (by linarith)]
  linarith

/-! ## (2) The integral, piece by piece -/

/-- **FTC**: `∫_a^b (A + B/s)/s ds = A(log b − log a) + B(1/a − 1/b)`, `0 < a ≤ b`. -/
theorem int_piece (A B a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ s in a..b, (A + B / s) / s = A * (Real.log b - Real.log a) + B * (1 / a - 1 / b) := by
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun s => A * Real.log s - B * s⁻¹) ((A + B / x) / x) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have hxne : x ≠ 0 := hx0.ne'
    have h1 := (Real.hasDerivAt_log hx0.ne').const_mul A
    have h2 := (hasDerivAt_inv hx0.ne').const_mul B
    refine (h1.sub h2).congr_deriv ?_
    field_simp
    ring
  have hcont : ContinuousOn (fun x => (A + B / x) / x) (uIcc a b) := by
    have hne : ∀ x ∈ uIcc a b, x ≠ 0 := by
      intro x hx
      rw [uIcc_of_le hab] at hx
      exact (lt_of_lt_of_le ha hx.1).ne'
    exact (continuousOn_const.add (continuousOn_const.div continuousOn_id hne)).div
      continuousOn_id hne
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hb : 0 < b := lt_of_lt_of_le ha hab
  field_simp
  ring

/-- **`∫_a^b Ĥ(s)/s ds` on a piece** `[a, b] ⊆ [j, j+1]`, `1 ≤ j ≤ 15`. -/
theorem int_piece_Hh (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ 15) (a b : ℝ) (ha : (j : ℝ) ≤ a)
    (hab : a ≤ b) (hb : b ≤ (j : ℝ) + 1) :
    ∫ s in a..b, Hh s / s =
      0.405285 * K1t j * (Real.log b - Real.log a) + 0.405285 * K2t j * (1 / a - 1 / b) := by
  have hj0 : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hj16 : (j : ℝ) + 1 ≤ 16 := by
    have : (j : ℝ) ≤ 15 := by exact_mod_cast hj
    linarith
  rw [intervalIntegral.integral_congr_Ioo_of_le hab
    (g := fun s => (0.405285 * K1t j + 0.405285 * K2t j / s) / s)]
  · exact int_piece _ _ a b (by linarith) hab
  · intro s hs
    have h16 : s < 16 := by linarith [hs.2]
    have hfl : ⌊s⌋₊ = j := floor_eq j s (by linarith [hs.1]) (by linarith [hs.2])
    simp only [Hh, if_pos h16, G2tab, hfl]
    ring

/-- `∫_a^b Ĥ(s)/s ds = 0.15107 (log b − log a)` for `16 ≤ a ≤ b`. -/
theorem int_tail (a b : ℝ) (ha : 16 ≤ a) (hab : a ≤ b) :
    ∫ s in a..b, Hh s / s = 0.15107 * (Real.log b - Real.log a) := by
  rw [intervalIntegral.integral_congr_Ioo_of_le hab (g := fun s => (0.15107 + 0 / s) / s)]
  · rw [int_piece _ _ a b (by linarith) hab]
    ring
  · intro s hs
    have h16 : ¬ s < 16 := by linarith [hs.1]
    simp only [Hh, if_neg h16]
    ring

/-- `P j = ∫_j^{j+1} Ĥ(s)/s ds`. -/
noncomputable def P (j : ℕ) : ℝ :=
  0.405285 * K1t j * (Real.log ((j : ℝ) + 1) - Real.log j) +
    0.405285 * K2t j * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))

/-- **`∫_1^n Ĥ(s)/s ds = ∑_{j < n} P j`**, `1 ≤ n ≤ 16`. -/
theorem prefix_eq (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 16) :
    ∫ s in (1 : ℝ)..n, Hh s / s = ∑ k ∈ Finset.range (n - 1), P (k + 1) := by
  have hint : ∀ k < n - 1, IntervalIntegrable (fun s => Hh s / s) volume
      ((fun k : ℕ => (k : ℝ) + 1) k) ((fun k : ℕ => (k : ℝ) + 1) (k + 1)) := by
    intro k _
    simp only [Nat.cast_add, Nat.cast_one]
    exact ii_Hhs _ _ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (by linarith)
  have hs := intervalIntegral.sum_integral_adjacent_intervals hint
  have e : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    rw [Nat.cast_sub hn1]
    push_cast
    ring
  simp only [Nat.cast_zero, zero_add] at hs
  rw [e] at hs
  rw [← hs]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k + 1 ≤ 15 := by
    have := Finset.mem_range.mp hk
    omega
  rw [int_piece_Hh (k + 1) (by omega) hk' _ _ (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith)]
  simp only [P, Nat.cast_add, Nat.cast_one]

/-! ## (3) `log((j+1)/j)` to `10⁻⁷` -/

/-- Mathlib's `abs_log_sub_add_sum_range_le` at `x = 1/(j+1)`. -/
theorem logL_bd (j : ℕ) (hj : 1 ≤ j) (n : ℕ) :
    |(∑ i ∈ Finset.range n, (1 / ((j : ℝ) + 1)) ^ (i + 1) / (i + 1)) -
        (Real.log ((j : ℝ) + 1) - Real.log j)| ≤
      (1 / ((j : ℝ) + 1)) ^ (n + 1) / (1 - 1 / ((j : ℝ) + 1)) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hx : |1 / ((j : ℝ) + 1)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_of_pos (show (0 : ℝ) < 1 / ((j : ℝ) + 1) by positivity)] at h
  have e : Real.log (1 - 1 / ((j : ℝ) + 1)) = Real.log j - Real.log ((j : ℝ) + 1) := by
    rw [← Real.log_div hj0.ne' (by positivity)]
    congr 1
    field_simp
    ring
  rw [e] at h
  have e2 : (∑ i ∈ Finset.range n, (1 / ((j : ℝ) + 1)) ^ (i + 1) / (i + 1)) -
      (Real.log ((j : ℝ) + 1) - Real.log j) =
      (∑ i ∈ Finset.range n, (1 / ((j : ℝ) + 1)) ^ (i + 1) / (i + 1)) +
      (Real.log j - Real.log ((j : ℝ) + 1)) := by ring
  rw [e2]
  exact h

/-- `log(3/2)` to `10⁻⁷` (`logL_bd`, 14 terms). -/
theorem lb2 : (0.4054649968 : ℝ) ≤ Real.log 3 - Real.log 2 ∧
    Real.log 3 - Real.log 2 ≤ 0.4054652059 := by
  have h := logL_bd 2 (by norm_num) 14
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log(4/3)` to `10⁻⁷` (`logL_bd`, 14 terms). -/
theorem lb3 : (0.2876820711 : ℝ) ≤ Real.log 4 - Real.log 3 ∧
    Real.log 4 - Real.log 3 ≤ 0.2876820737 := by
  have h := logL_bd 3 (by norm_num) 14
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log(5/4)` to `10⁻⁷` (`logL_bd`, 14 terms). -/
theorem lb4 : (0.2231435512 : ℝ) ≤ Real.log 5 - Real.log 4 ∧
    Real.log 5 - Real.log 4 ≤ 0.2231435514 := by
  have h := logL_bd 4 (by norm_num) 14
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log(6/5)` to `10⁻⁷` (`logL_bd`, 14 terms). -/
theorem lb5 : (0.1823215567 : ℝ) ≤ Real.log 6 - Real.log 5 ∧
    Real.log 6 - Real.log 5 ≤ 0.1823215568 := by
  have h := logL_bd 5 (by norm_num) 14
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log(7/6)` to `10⁻⁷` (`logL_bd`, 14 terms). -/
theorem lb6 : (0.1541506798 : ℝ) ≤ Real.log 7 - Real.log 6 ∧
    Real.log 7 - Real.log 6 ≤ 0.1541506799 := by
  have h := logL_bd 6 (by norm_num) 14
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log(8/7)` to `10⁻⁷` (`logL_bd`, 14 terms). -/
theorem lb7 : (0.1335313926 : ℝ) ≤ Real.log 8 - Real.log 7 ∧
    Real.log 8 - Real.log 7 ≤ 0.1335313927 := by
  have h := logL_bd 7 (by norm_num) 14
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log(9/8)` to `10⁻⁷` (`logL_bd`, 14 terms). -/
theorem lb8 : (0.1177830356 : ℝ) ≤ Real.log 9 - Real.log 8 ∧
    Real.log 9 - Real.log 8 ≤ 0.1177830357 := by
  have h := logL_bd 8 (by norm_num) 14
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log(10/9)` to `10⁻⁷` (`logL_bd`, 14 terms). -/
theorem lb9 : (0.1053605156 : ℝ) ≤ Real.log 10 - Real.log 9 ∧
    Real.log 10 - Real.log 9 ≤ 0.1053605157 := by
  have h := logL_bd 9 (by norm_num) 14
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log(11/10)` to `10⁻⁷` (`logL_bd`, 14 terms). -/
theorem lb10 : (0.0953101798 : ℝ) ≤ Real.log 11 - Real.log 10 ∧
    Real.log 11 - Real.log 10 ≤ 0.0953101799 := by
  have h := logL_bd 10 (by norm_num) 14
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log(12/11)` to `10⁻⁷` (`logL_bd`, 14 terms). -/
theorem lb11 : (0.0870113769 : ℝ) ≤ Real.log 12 - Real.log 11 ∧
    Real.log 12 - Real.log 11 ≤ 0.0870113770 := by
  have h := logL_bd 11 (by norm_num) 14
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log(13/12)` to `10⁻⁷` (`logL_bd`, 14 terms). -/
theorem lb12 : (0.0800427076 : ℝ) ≤ Real.log 13 - Real.log 12 ∧
    Real.log 13 - Real.log 12 ≤ 0.0800427077 := by
  have h := logL_bd 12 (by norm_num) 14
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log(14/13)` to `10⁻⁷` (`logL_bd`, 14 terms). -/
theorem lb13 : (0.0741079721 : ℝ) ≤ Real.log 14 - Real.log 13 ∧
    Real.log 14 - Real.log 13 ≤ 0.0741079722 := by
  have h := logL_bd 13 (by norm_num) 14
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log(15/14)` to `10⁻⁷` (`logL_bd`, 14 terms). -/
theorem lb14 : (0.0689928714 : ℝ) ≤ Real.log 15 - Real.log 14 ∧
    Real.log 15 - Real.log 14 ≤ 0.0689928715 := by
  have h := logL_bd 14 (by norm_num) 14
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-- `log(16/15)` to `10⁻⁷` (`logL_bd`, 14 terms). -/
theorem lb15 : (0.0645385211 : ℝ) ≤ Real.log 16 - Real.log 15 ∧
    Real.log 16 - Real.log 15 ≤ 0.0645385212 := by
  have h := logL_bd 15 (by norm_num) 14
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

/-! ## (4) The excess, piece by piece -/

/-- **`[1, 2]`**: `φ ≤ 0.02`, from `log T = 2 log √T ≤ 2(√T − 1)`. -/
theorem piece1 (T : ℝ) (h1 : 1 ≤ T) (h2 : T ≤ 2) :
    0.405285 * 1 * (Real.log T - Real.log 1) + 0.405285 * (-1) * (1 / 1 - 1 / T) -
      0.15107 * (Real.log T - Real.log 1) ≤ 0.02 := by
  rw [Real.log_one]
  have hT0 : 0 < T := by linarith
  set r := Real.sqrt T with hr
  have hr2 : r ^ 2 = T := Real.sq_sqrt hT0.le
  have hr0 : 0 ≤ r := Real.sqrt_nonneg T
  have hr1 : 1 ≤ r := by nlinarith
  have hrl : r ≤ 1.4143 := by nlinarith
  have hlog : Real.log T ≤ 2 * (r - 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < r by linarith)
    have e : Real.log T = 2 * Real.log r := by
      rw [← hr2, Real.log_pow]
      norm_num
    linarith
  have hlogc : (0.405285 - 0.15107) * Real.log T ≤ (0.405285 - 0.15107) * (2 * (r - 1)) :=
    mul_le_mul_of_nonneg_left hlog (by norm_num)
  have hinv : 1 / T = 1 / r ^ 2 := by rw [hr2]
  have hq : 0.50843 * r ^ 2 - 0.405285 * r - 0.405285 ≤ 0.039 := by nlinarith
  have hprod : (r - 1) * (0.50843 * r ^ 2 - 0.405285 * r - 0.405285) ≤ 0.02 * r ^ 2 := by
    rcases le_or_gt (0.50843 * r ^ 2 - 0.405285 * r - 0.405285) 0 with hn | hp
    · have : (r - 1) * (0.50843 * r ^ 2 - 0.405285 * r - 0.405285) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hn
      nlinarith
    · have : (r - 1) * (0.50843 * r ^ 2 - 0.405285 * r - 0.405285) ≤ 0.4143 * 0.039 :=
        mul_le_mul (by linarith) hq hp.le (by norm_num)
      nlinarith
  have hr2pos : 0 < r ^ 2 := by positivity
  have key : 0.405285 * (1 - 1 / r ^ 2) * r ^ 2 = 0.405285 * (r ^ 2 - 1) := by
    field_simp
  have hfin : 2 * (0.405285 - 0.15107) * (r - 1) - 0.405285 * (1 - 1 / r ^ 2) ≤ 0.02 := by
    have e : (2 * (0.405285 - 0.15107) * (r - 1) - 0.405285 * (1 - 1 / r ^ 2)) * r ^ 2 =
        (r - 1) * (0.50843 * r ^ 2 - 0.405285 * r - 0.405285) := by
      field_simp
      ring
    have h3 : (2 * (0.405285 - 0.15107) * (r - 1) - 0.405285 * (1 - 1 / r ^ 2)) * r ^ 2 ≤
        0.02 * r ^ 2 := by rw [e]; exact hprod
    exact le_of_mul_le_mul_right h3 hr2pos
  rw [hinv]
  nlinarith

/-- **`[n, n+1]`, `G₂ ≥ 0.15107π²/4` at the right end**: `φ` is increasing, so `φ(T) ≤ φ(n+1)`. -/
theorem mono_piece (n A B T : ℝ) (hn : 1 ≤ n) (hB : 0 ≤ B)
    (hm : 0.15107 ≤ 0.405285 * A + 0.405285 * B / (n + 1)) (hT1 : n ≤ T) (hT2 : T ≤ n + 1) :
    0.405285 * A * (Real.log T - Real.log n) + 0.405285 * B * (1 / n - 1 / T) -
        0.15107 * (Real.log T - Real.log n) ≤
      0.405285 * A * (Real.log (n + 1) - Real.log n) + 0.405285 * B * (1 / n - 1 / (n + 1)) -
        0.15107 * (Real.log (n + 1) - Real.log n) := by
  have hT0 : 0 < T := by linarith
  have hn0 : 0 < n + 1 := by linarith
  set w := (n + 1) / T - 1 with hw
  have hw0 : 0 ≤ w := by
    rw [hw, sub_nonneg, le_div_iff₀ hT0]
    linarith
  have hl0 : 0 ≤ Real.log (n + 1) - Real.log T := sub_nonneg.mpr (Real.log_le_log hT0 hT2)
  have hl1 : Real.log (n + 1) - Real.log T ≤ w := by
    rw [← Real.log_div hn0.ne' hT0.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hn0 hT0)
  have hinv : 1 / T - 1 / (n + 1) = w / (n + 1) := by
    rw [hw]
    field_simp
  have key : 0 ≤ (0.405285 * A - 0.15107) * (Real.log (n + 1) - Real.log T) +
      0.405285 * B * (w / (n + 1)) := by
    have hBw : 0 ≤ 0.405285 * B * (w / (n + 1)) := by positivity
    rcases le_or_gt 0 (0.405285 * A - 0.15107) with h | h
    · have := mul_nonneg h hl0
      linarith
    · have h1 : (0.405285 * A - 0.15107) * w ≤
          (0.405285 * A - 0.15107) * (Real.log (n + 1) - Real.log T) :=
        mul_le_mul_of_nonpos_left hl1 h.le
      have h2 : 0 ≤ w * ((0.405285 * A - 0.15107) + 0.405285 * B / (n + 1)) :=
        mul_nonneg hw0 (by linarith)
      have h3 : w * ((0.405285 * A - 0.15107) + 0.405285 * B / (n + 1)) =
          (0.405285 * A - 0.15107) * w + 0.405285 * B * (w / (n + 1)) := by ring
      linarith
  have e : (0.405285 * A * (Real.log (n + 1) - Real.log n) +
        0.405285 * B * (1 / n - 1 / (n + 1)) - 0.15107 * (Real.log (n + 1) - Real.log n)) -
      (0.405285 * A * (Real.log T - Real.log n) + 0.405285 * B * (1 / n - 1 / T) -
        0.15107 * (Real.log T - Real.log n)) =
      (0.405285 * A - 0.15107) * (Real.log (n + 1) - Real.log T) +
        0.405285 * B * (1 / T - 1 / (n + 1)) := by ring
  rw [hinv] at e
  linarith

/-- **`[15, 16]`**: `φ(T) − φ(15) ≤ 0.0000556`, from `log(T/15) ≥ 1 − 15/T`. -/
theorem piece15 (T : ℝ) (h1 : 15 ≤ T) (h2 : T ≤ 16) :
    0.405285 * (113819 / 360360) * (Real.log T - Real.log 15) +
        0.405285 * (1787 / 2016) * (1 / 15 - 1 / T) -
      0.15107 * (Real.log T - Real.log 15) ≤ 0.0000556 := by
  have hT0 : 0 < T := by linarith
  have hl : 1 - 15 / T ≤ Real.log T - Real.log 15 := by
    rw [← Real.log_div hT0.ne' (by norm_num)]
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hT0 (by norm_num : (0 : ℝ) < 15))
    rwa [inv_div] at h
  have hu : 1 - 15 / T ≤ 1 / 16 := by
    have : 15 / 16 ≤ 15 / T := div_le_div_of_nonneg_left (by norm_num) hT0 h2
    linarith
  have hu0 : 0 ≤ 1 - 15 / T := by
    have : 15 / T ≤ 1 := by rw [div_le_one hT0]; linarith
    linarith
  have e : 1 / 15 - 1 / T = (1 - 15 / T) / 15 := by
    field_simp
  rw [e]
  have ha : 0.405285 * (113819 / 360360) - 0.15107 ≤ (0 : ℝ) := by norm_num
  have h3 := mul_le_mul_of_nonpos_left hl ha
  nlinarith

/-! ## (5) The numerics: `∫_1^m Ĥ/s − 0.15107 log m` at the integers -/

set_option maxHeartbeats 4000000 in
-- Thirteen `interval_cases` branches, each a `norm_num` over up to fourteen `log` pieces and a
-- `linarith` over twenty-eight bounds; the default budget runs out on the whole declaration.
/-- `m ∈ [3, 15]`: `∑_{j < m} P j ≤ 0.15107 log m + 0.023043` (the excess `≤ 0.0230426`). -/
theorem prefix_num (m : ℕ) (h3 : 3 ≤ m) (h15 : m ≤ 15) :
    ∑ k ∈ Finset.range (m - 1), P (k + 1) ≤ 0.15107 * Real.log m + 0.023043 := by
  have L2 := Real.log_two_gt_d9
  have L2' := Real.log_two_lt_d9
  have := lb2
  have := lb3
  have := lb4
  have := lb5
  have := lb6
  have := lb7
  have := lb8
  have := lb9
  have := lb10
  have := lb11
  have := lb12
  have := lb13
  have := lb14
  interval_cases m <;> norm_num [Finset.sum_range_succ, P, K1t, K2t] <;> linarith

set_option maxHeartbeats 1000000 in
-- One `norm_num` over fifteen `log` pieces and a `linarith` over thirty bounds.
/-- `m = 16`: `∑_{j < 16} P j ≤ 0.15107 log 16 + 0.0230515` (the excess `≤ 0.0230511`). -/
theorem prefix16 :
    ∑ k ∈ Finset.range (16 - 1), P (k + 1) ≤ 0.15107 * Real.log 16 + 0.0230515 := by
  have L2 := Real.log_two_gt_d9
  have L2' := Real.log_two_lt_d9
  have := lb2
  have := lb3
  have := lb4
  have := lb5
  have := lb6
  have := lb7
  have := lb8
  have := lb9
  have := lb10
  have := lb11
  have := lb12
  have := lb13
  have := lb14
  have := lb15
  norm_num [Finset.sum_range_succ, P, K1t, K2t]
  linarith

/-! ## (6) `HOkC H₂` -/

/-- **`∫_1^T Ĥ(s)/s ds ≤ 0.15107 log T + 0.0231`** for every `T ≥ 1`. -/
theorem hh_int_le (T : ℝ) (hT : 1 ≤ T) :
    ∫ s in (1 : ℝ)..T, Hh s / s ≤ 0.15107 * Real.log T + 0.0231 := by
  rcases lt_or_ge T 16 with h16 | h16
  · obtain ⟨hn1, hn15, hnT, hTn⟩ := piece_of T hT h16
    generalize hn : ⌊T⌋₊ = n at hn1 hn15 hnT hTn
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hsplit : ∫ s in (1 : ℝ)..T, Hh s / s =
        (∫ s in (1 : ℝ)..n, Hh s / s) + ∫ s in (n : ℝ)..T, Hh s / s :=
      (intervalIntegral.integral_add_adjacent_intervals (ii_Hhs _ _ le_rfl hn0)
        (ii_Hhs _ _ hn0 hnT)).symm
    have hpre := prefix_eq n hn1 (by omega)
    have hpc := int_piece_Hh n hn1 hn15 n T le_rfl hnT hTn.le
    rcases (show n = 1 ∨ n = 15 ∨ (2 ≤ n ∧ n ≤ 14) by omega) with h1 | h15 | ⟨h2, h14⟩
    · subst h1
      have hp1 := piece1 T hT (by push_cast at hTn; linarith)
      simp only [K1t, K2t, Nat.cast_one] at hpc hpre hsplit
      simp only [Nat.sub_self, Finset.range_zero, Finset.sum_empty] at hpre
      rw [Real.log_one] at hp1 hpc
      linarith
    · subst h15
      have hp15 := piece15 T (by exact_mod_cast hnT) (by push_cast at hTn; linarith)
      simp only [K1t, K2t, Nat.cast_ofNat] at hpc hpre hsplit
      have hnum := prefix_num 15 (by norm_num) le_rfl
      simp only [Nat.cast_ofNat] at hnum
      linarith
    · have hB : 0 ≤ K2t n := by interval_cases n <;> norm_num [K2t]
      have hm : 0.15107 ≤ 0.405285 * K1t n + 0.405285 * K2t n / ((n : ℝ) + 1) := by
        interval_cases n <;> norm_num [K1t, K2t]
      have hmono := mono_piece (n : ℝ) (K1t n) (K2t n) T hn0 hB hm hnT hTn.le
      have hnum := prefix_num (n + 1) (by omega) (by omega)
      push_cast at hnum
      have hsum : ∑ k ∈ Finset.range n, P (k + 1) =
          (∑ k ∈ Finset.range (n - 1), P (k + 1)) + P n := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [Nat.add_sub_cancel, Finset.sum_range_succ]
      have hP : P n = 0.405285 * K1t n * (Real.log ((n : ℝ) + 1) - Real.log n) +
          0.405285 * K2t n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := rfl
      have hlogT : Real.log T ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) hTn.le
      linarith
  · have h16' : (1 : ℝ) ≤ 16 := by norm_num
    have hsplit : ∫ s in (1 : ℝ)..T, Hh s / s =
        (∫ s in (1 : ℝ)..16, Hh s / s) + ∫ s in (16 : ℝ)..T, Hh s / s :=
      (intervalIntegral.integral_add_adjacent_intervals (ii_Hhs _ _ le_rfl h16')
        (ii_Hhs _ _ h16' h16)).symm
    have hpre := prefix_eq 16 (by norm_num) le_rfl
    have e16 : ((16 : ℕ) : ℝ) = 16 := by norm_num
    rw [e16] at hpre
    have ht := int_tail 16 T le_rfl h16
    have hnum := prefix16
    linarith

/-- **`HOkC H₂`, PROVED** — Helfgott's explicit `H₂` meets the corrected `eq:velib` and
`eq:demimond`: `0 ≤ H₂ ≤ 2/π²` on `[1, ∞)`, integrable, `∫_1^T H₂/s ≤ 0.15107 log T + 0.0231`. -/
theorem h2OkC : HOkC H2tab := by
  refine ⟨fun s hs => h2_bounds s hs, fun T hT => ii_H 1 T le_rfl hT, fun T hT => ?_⟩
  refine le_trans ?_ (hh_int_le T hT)
  exact intervalIntegral.integral_mono_on hT (ii_Hs 1 T le_rfl hT) (ii_Hhs 1 T le_rfl hT)
    fun s hs => div_le_div_of_nonneg_right (h2_le_hh s hs.1) (by linarith [hs.1])

/-! ## (7) The `S₁` half, spined -/

/-- **Link [MonroFleming] — `eq:crusto` → `eq:fleming`** (`typeII.tex` 147-372): `S₁(U, W)`
(`eq:mahalobi`, `v = 2`) is at most its main term `(6x/π²W)(v/σ(v))·eq:grotto` at
`S = x/WU` (`6v/π²σ(v) = 4/π²`) plus `lem:monro`'s error (`eq:mudo`, summed in `eq:flatow`:
`1.27ζ(3/2)³(1 + 1/√2)(1 − 2^{−3/2})³·S√(x/W) ≤ 22.6418·(x/W)^{3/2}/U`). DEEP; OPEN. -/
def MonroFleming : Prop :=
  ∀ x U W : ℝ, 1 ≤ U → 1 ≤ W → U * W ≤ x →
    s1 x U W ≤ x / W * (4 / Real.pi ^ 2 * HC.cortoLHS 2 (x / (W * U))) +
      22.6418 * (x / W) ^ ((3 : ℝ) / 2) / U

/-- **Link [GrottoTab] — `eq:grotto` equals `G₂` below `16`** (`eq:greco` summed over
`m ≤ S`, exact; `typeII.tex` 680-707, 783-790). A FINITE identity (15 pieces); OPEN. -/
def GrottoTab : Prop := ∀ S : ℝ, 1 ≤ S → S < 16 → HC.cortoLHS 2 S ≤ G2tab S

/-- **Link [CortoLarge] — `eq:corto` for `S ≥ 10⁵`, `v = 2`** (`typeII.tex` 709-781:
`lem:yutto` (Rankin's trick, `eq:marraki`/`HC.RamareCited`, `HC.YuttoSmallCited`), Euler–Maclaurin
`eq:etex`, `HC.CortoC0Cited`). DEEP; OPEN. -/
def CortoLarge : Prop := ∀ S : ℝ, 100000 ≤ S → HC.cortoLHS 2 S ≤ 0.37273

/-- `(4/π²)·eq:grotto ≤ H₂` on `[1, ∞)`, from the three `S`-ranges. PROVED. -/
theorem grotto_le (gt : GrottoTab) (cl : CortoLarge) (cs : HC.CortoSmallCited) (S : ℝ)
    (hS : 1 ≤ S) : 4 / Real.pi ^ 2 * HC.cortoLHS 2 S ≤ H2tab S := by
  have hk0 : 0 ≤ 4 / Real.pi ^ 2 := by positivity
  unfold H2tab
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left (gt S hS h) hk0
  · have hc : HC.cortoLHS 2 S ≤ 0.37273 := by
      rcases lt_or_ge S 100000 with h' | h'
      · exact cs.2 S (not_lt.mp h) h'
      · exact cl S h'
    have h1 := mul_le_mul_of_nonneg_left hc hk0
    have hk := k_bounds.2
    linarith

/-- **`T2SC.Menson2C` from its links, PROVED** (`H := H2tab`, `h2OkC`). -/
theorem menson2C_of_links (mf : MonroFleming) (gt : GrottoTab) (cl : CortoLarge)
    (cs : HC.CortoSmallCited) : Menson2C := by
  refine ⟨H2tab, h2OkC, fun x U W hU hW hUW => ?_⟩
  have hW0 : 0 < W := by linarith
  have hU0 : 0 < U := by linarith
  have hx : 0 < x := by nlinarith
  have hS : 1 ≤ x / (W * U) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [mul_comm W U]
  unfold S1Bd
  refine (mf x U W hU hW hUW).trans ?_
  have hxW : 0 ≤ x / W := by positivity
  have h := mul_le_mul_of_nonneg_left (grotto_le gt cl cs _ hS) hxW
  linarith

end Principia.Common.TernaryGoldbach.M2H
