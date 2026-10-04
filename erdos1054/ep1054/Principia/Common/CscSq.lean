/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries

set_option autoImplicit false

/-!
# `∑_{n ∈ ℤ} 1/(y + n)² = π²/sin²(πy)` for real `y ∉ ℤ`

Mathlib has the Mittag-Leffler expansion of `π cot πz` on `ℂ \ ℤ` (`cot_series_rep'`) and its
iterated derivatives on the upper half-plane only. This file differentiates the expansion on the
REAL line (term by term, on a small interval around `y`, `hasDerivAt_tsum_of_isPreconnected`),
which is what the Poisson-summation bound of `eq:trompais` consumes.
-/

namespace Principia.Common.CscSq

open Real Set

/-- The real cotangent term `1/(y − (n+1)) + 1/(y + (n+1))`. -/
noncomputable def cT (n : ℕ) (y : ℝ) : ℝ := 1 / (y - (n + 1)) + 1 / (y + (n + 1))

/-- Its derivative `−1/(y − (n+1))² − 1/(y + (n+1))²`. -/
noncomputable def cT' (n : ℕ) (y : ℝ) : ℝ := -(1 / (y - (n + 1)) ^ 2) - 1 / (y + (n + 1)) ^ 2

/-- **The real Mittag-Leffler expansion**: `π cot πy − 1/y = ∑_{n ≥ 0} cT n y` for `y ∉ ℤ`. -/
theorem cot_rep (y : ℝ) (hy : ∀ n : ℤ, y + n ≠ 0) :
    π * Real.cot (π * y) - 1 / y = ∑' n : ℕ, cT n y := by
  have hz : (y : ℂ) ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    apply hy (-n)
    have : (n : ℝ) = y := by exact_mod_cast hn
    push_cast
    linarith
  have h := cot_series_rep' hz
  have hs := summable_cotTerm hz
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  push_cast
  rw [h]
  refine tsum_congr fun n => ?_
  unfold cT
  push_cast
  ring

/-- `|z − m| ≥ |y − m|/2` near `y` when `|y − m| ≥ 2r`. -/
theorem half_le (y z m r : ℝ) (hm : 2 * r ≤ |y - m|) (hz : |z - y| < r) :
    |y - m| / 2 ≤ |z - m| := by
  have := abs_sub_abs_le_abs_sub (y - m) (z - m)
  have e : y - m - (z - m) = -(z - y) := by ring
  rw [e, abs_neg] at this
  linarith


/-- `1/b² ≤ 4/a²` when `|b| ≥ |a|/2 > 0`. -/
theorem inv_sq_le (a b : ℝ) (ha : 0 < |a|) (h : |a| / 2 ≤ |b|) : 1 / b ^ 2 ≤ 4 * (1 / a ^ 2) := by
  have ha' : a ≠ 0 := abs_pos.mp ha
  have hb : 0 < |b| := lt_of_lt_of_le (by positivity) h
  have hb' : b ≠ 0 := abs_pos.mp hb
  have h2 : |a| ≤ 2 * |b| := by linarith
  have h3 := mul_self_le_mul_self (abs_nonneg a) h2
  rw [abs_mul_abs_self, show 2 * |b| * (2 * |b|) = 4 * (|b| * |b|) by ring,
    abs_mul_abs_self] at h3
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- A real `y ∉ ℤ` keeps a positive distance `2r` from every integer. -/
theorem exists_dist (y : ℝ) (hy : ∀ n : ℤ, y + n ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ m : ℤ, 2 * r ≤ |y - m| := by
  have hk1 : (⌊y⌋ : ℝ) < y := by
    rcases (Int.floor_le y).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hy (-⌊y⌋)
      rw [Int.cast_neg]
      linarith
  have hk2 : y < ⌊y⌋ + 1 := Int.lt_floor_add_one y
  refine ⟨min (y - ⌊y⌋) (⌊y⌋ + 1 - y) / 2, half_pos (lt_min (by linarith) (by linarith)),
    fun m => ?_⟩
  have h1 := min_le_left (y - ⌊y⌋) (⌊y⌋ + 1 - y)
  have h2 := min_le_right (y - ⌊y⌋) (⌊y⌋ + 1 - y)
  rcases le_or_gt m ⌊y⌋ with h | h
  · have : (m : ℝ) ≤ ⌊y⌋ := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]
    linarith
  · have : (⌊y⌋ : ℝ) + 1 ≤ m := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]
    linarith

/-- `π cot πz − 1/z` has derivative `−π²/sin²πy + 1/y²` at `y`. -/
theorem hasDerivAt_cotL (y : ℝ) (hs : Real.sin (π * y) ≠ 0) (hy0 : y ≠ 0) :
    HasDerivAt (fun z => π * Real.cot (π * z) - 1 / z)
      (-(π ^ 2 / Real.sin (π * y) ^ 2) + 1 / y ^ 2) y := by
  have hc : HasDerivAt (fun z => π * z) π y := by
    simpa using (hasDerivAt_id y).const_mul π
  have h3 := ((hc.cos.div hc.sin hs).const_mul π).sub (hasDerivAt_inv hy0)
  have hf : (fun z => π * Real.cot (π * z) - 1 / z) =
      fun z => π * (Real.cos (π * z) / Real.sin (π * z)) - z⁻¹ := by
    funext z
    rw [Real.cot_eq_cos_div_sin, one_div]
  rw [hf]
  refine h3.congr_deriv ?_
  have hsc := Real.sin_sq_add_cos_sq (π * y)
  have e : -Real.sin (π * y) * π * Real.sin (π * y) - Real.cos (π * y) * (Real.cos (π * y) * π) =
      -π * (Real.sin (π * y) ^ 2 + Real.cos (π * y) ^ 2) := by ring
  rw [e, hsc]
  field_simp
  ring

/-- The bound `‖cT' n z‖ ≤ 4/(y − (n+1))² + 4/(y + (n+1))²` near `y`. -/
theorem cT'_le (y z r : ℝ) (hd : ∀ m : ℤ, 2 * r ≤ |y - m|) (hr : 0 < r) (hz : |z - y| < r)
    (n : ℕ) : ‖cT' n z‖ ≤ 4 * (1 / (y - (n + 1)) ^ 2) + 4 * (1 / (y + (n + 1)) ^ 2) := by
  have d1 := hd ((n : ℤ) + 1)
  have d2 := hd (-((n : ℤ) + 1))
  push_cast at d1 d2
  rw [sub_neg_eq_add] at d2
  have b1 := half_le y z ((n : ℝ) + 1) r d1 hz
  have b2 := half_le y z (-((n : ℝ) + 1)) r (by rwa [sub_neg_eq_add]) hz
  rw [sub_neg_eq_add, sub_neg_eq_add] at b2
  have q1 := inv_sq_le (y - (n + 1)) (z - (n + 1)) (by linarith) b1
  have q2 := inv_sq_le (y + (n + 1)) (z + (n + 1)) (by linarith) b2
  unfold cT'
  rw [Real.norm_eq_abs]
  refine (abs_sub _ _).trans ?_
  rw [abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  linarith

/-- `∑ 4/(y − (n+1))² + 4/(y + (n+1))²` converges. -/
theorem summable_u (y : ℝ) :
    Summable fun n : ℕ => 4 * (1 / (y - (n + 1)) ^ 2) + 4 * (1 / (y + (n + 1)) ^ 2) := by
  have s1 := ((Real.summable_one_div_nat_add_rpow (-y + 1) 2).mpr (by norm_num)).mul_left 4
  have s2 := ((Real.summable_one_div_nat_add_rpow (y + 1) 2).mpr (by norm_num)).mul_left 4
  refine (s1.add s2).congr fun n => ?_
  rw [Real.rpow_two, Real.rpow_two, sq_abs, sq_abs]
  ring

/-- **`∑_{n ≥ 0} cT' n y = −π²/sin²πy + 1/y²`** (term-by-term differentiation), PROVED. -/
theorem hasSum_cT' (y : ℝ) (hy : ∀ n : ℤ, y + n ≠ 0) :
    HasSum (fun n => cT' n y) (-(π ^ 2 / Real.sin (π * y) ^ 2) + 1 / y ^ 2) := by
  obtain ⟨r, hr, hd⟩ := exists_dist y hy
  have hne : ∀ z : ℝ, |z - y| < r → ∀ m : ℤ, z - m ≠ 0 := by
    intro z hz m h0
    have := half_le y z m r (hd m) hz
    rw [h0, abs_zero] at this
    have := hd m
    linarith
  have hmem : ∀ z ∈ Ioo (y - r) (y + r), |z - y| < r := by
    intro z hz
    rw [abs_lt]
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hderiv : ∀ n : ℕ, ∀ z ∈ Ioo (y - r) (y + r), HasDerivAt (cT n) (cT' n z) z := by
    intro n z hz
    have h1 : z - (n + 1) ≠ 0 := by
      have := hne z (hmem z hz) ((n : ℤ) + 1)
      push_cast at this
      exact this
    have h2 : z + (n + 1) ≠ 0 := by
      have := hne z (hmem z hz) (-((n : ℤ) + 1))
      push_cast at this
      rwa [sub_neg_eq_add] at this
    have d1 : HasDerivAt (fun w : ℝ => w - (n + 1)) 1 z := (hasDerivAt_id z).sub_const _
    have d2 : HasDerivAt (fun w : ℝ => w + (n + 1)) 1 z := (hasDerivAt_id z).add_const _
    have := ((hasDerivAt_const z (1 : ℝ)).div d1 h1).add ((hasDerivAt_const z (1 : ℝ)).div d2 h2)
    unfold cT cT'
    refine this.congr_deriv ?_
    field_simp
    ring
  have hyt : y ∈ Ioo (y - r) (y + r) := ⟨by linarith, by linarith⟩
  have hz : (y : ℂ) ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    apply hy (-n)
    have : (n : ℝ) = y := by exact_mod_cast hn
    push_cast
    linarith
  have hsum0 : Summable fun n => cT n y := by
    have h1 := summable_cotTerm hz
    have h2 : (fun n => ((cT n y : ℝ) : ℂ)) = fun n => cotTerm (y : ℂ) n := by
      funext n
      unfold cT
      push_cast
      rfl
    rw [← h2] at h1
    exact Complex.summable_ofReal.mp h1
  have hD := hasDerivAt_tsum_of_isPreconnected (summable_u y) isOpen_Ioo isPreconnected_Ioo
    hderiv (fun n z hz => cT'_le y z r hd hr (hmem z hz) n) hyt hsum0 hyt
  have hsin : Real.sin (π * y) ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp h
    apply hy (-m)
    have : (m : ℝ) = y := by
      have := Real.pi_pos
      have h' : (m : ℝ) * π = y * π := by rw [hm]; ring
      exact mul_right_cancel₀ (ne_of_gt this) h'
    push_cast
    linarith
  have hy0 : y ≠ 0 := by simpa using hy 0
  have heq : (fun z => π * Real.cot (π * z) - 1 / z) =ᶠ[nhds y] fun z => ∑' n, cT n z := by
    filter_upwards [isOpen_Ioo.mem_nhds hyt] with z hz
    refine cot_rep z fun m h0 => ?_
    have := hne z (hmem z hz) (-m)
    push_cast at this
    rw [sub_neg_eq_add] at this
    exact this h0
  have hval := (hasDerivAt_cotL y hsin hy0).unique (hD.congr_of_eventuallyEq heq)
  have hs' : Summable fun n => cT' n y :=
    (summable_u y).of_norm_bounded fun n => cT'_le y y r hd hr (by simpa using hr) n
  rw [hval]
  exact hs'.hasSum

/-- **`∑_{n ∈ ℤ} 1/(y + n)² = π²/sin²(πy)` for real `y ∉ ℤ`, PROVED.** -/
theorem hasSum_inv_sq (y : ℝ) (hy : ∀ n : ℤ, y + n ≠ 0) :
    HasSum (fun n : ℤ => 1 / (y + n) ^ 2) (π ^ 2 / Real.sin (π * y) ^ 2) := by
  have hc := hasSum_cT' y hy
  have sA : Summable fun n : ℕ => 1 / (y + ((n : ℤ) + 1 : ℤ)) ^ 2 := by
    have := (Real.summable_one_div_nat_add_rpow (y + 1) 2).mpr (by norm_num)
    refine this.congr fun n => ?_
    rw [Real.rpow_two, sq_abs]
    push_cast
    ring_nf
  have sB : Summable fun n : ℕ => 1 / (y + ((-((n : ℤ) + 1) : ℤ) : ℝ)) ^ 2 := by
    have := (Real.summable_one_div_nat_add_rpow (-y + 1) 2).mpr (by norm_num)
    refine this.congr fun n => ?_
    rw [Real.rpow_two, sq_abs]
    push_cast
    ring_nf
  have hall := HasSum.of_add_one_of_neg_add_one (f := fun n : ℤ => 1 / (y + n) ^ 2)
    sA.hasSum sB.hasSum
  have hAB : (∑' n : ℕ, 1 / (y + ((n : ℤ) + 1 : ℤ)) ^ 2) +
      ∑' n : ℕ, 1 / (y + ((-((n : ℤ) + 1) : ℤ) : ℝ)) ^ 2 = -∑' n, cT' n y := by
    rw [← sA.tsum_add sB, ← tsum_neg]
    refine tsum_congr fun n => ?_
    unfold cT'
    push_cast
    ring
  rw [hc.tsum_eq] at hAB
  have hv : π ^ 2 / Real.sin (π * y) ^ 2 = (∑' n : ℕ, 1 / (y + ((n : ℤ) + 1 : ℤ)) ^ 2) +
      1 / (y + ((0 : ℤ) : ℝ)) ^ 2 + ∑' n : ℕ, 1 / (y + ((-((n : ℤ) + 1) : ℤ) : ℝ)) ^ 2 := by
    simp only [Int.cast_zero, add_zero]
    linarith
  rw [hv]
  exact hall

end Principia.Common.CscSq
