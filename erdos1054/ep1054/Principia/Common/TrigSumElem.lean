/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

/-!
# Elementary trigonometric inequalities for the trigonometric-sum lemmas

The one-variable facts behind `lem:gotog`, `lem:couscous` and `lem:thina` (Helfgott,
arXiv:1501.05438, `typeI.tex` 49-457), each proved from Mathlib's `sin`/`cos` bounds:

* Taylor bounds `x - x³/6 ≤ sin x`, `cos x ≤ 1 - x²/2 + x⁴/24` (`x ≥ 0`);
* `tan(h/2) ≥ h/2` and `tan h ≥ h` in multiplied-out form;
* the **monotone step** `h·csc²θ ≤ cot(θ - h) - cot θ` (`csc_sq_step`) and the **midpoint step**
  `h·csc²m ≤ cot(m - h/2) - cot(m + h/2)` (`csc_sq_mid`), the discrete forms of `∫ csc² = -cot`;
* the **log step** `(b - a)·csc b ≤ L(b) - L(a)` for `L θ = log(sin θ) - log(1 + cos θ)`
  `= log tan(θ/2)` (`lg_step`, by the mean value theorem);
* `θ + sin θ cos θ ≤ 2 sin θ` on `[0, π/2]` (`theta_add_sin_mul_cos_le`), i.e. the book's
  `arcsin x + x√(1 - x²) ≤ 2x`;
* `h²csc²h + h·cot(3h/2) ≤ 5/3` on `(0, π/4]` (`csc_sq_add_cot_le`);
* `|sin(πx)| ≥ sin(πd)` whenever `d ≤ |x - m| ≤ 1/2` (`sin_pi_le_abs_sin`).
-/

namespace Principia.Common.TrigSum

open Real

/-- `cot x = cos x / sin x`. -/
noncomputable def ct (x : ℝ) : ℝ := cos x / sin x

/-- `L θ = log(sin θ) - log(1 + cos θ) = log tan(θ/2)`, an antiderivative of `csc`. -/
noncomputable def lg (θ : ℝ) : ℝ := log (sin θ) - log (1 + cos θ)

/-! ## 1. Monotonicity from a derivative -/

/-- A function with nonnegative derivative on `[0, ∞)` and `f 0 = 0` is nonnegative there. -/
theorem nonneg_of_hasDerivAt {f f' : ℝ → ℝ} (hd : ∀ t, HasDerivAt f (f' t) t)
    (hpos : ∀ t, 0 < t → 0 ≤ f' t) (h0 : f 0 = 0) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hd t).deriv]
      exact hpos t ht
  have h := hmono Set.self_mem_Ici (Set.mem_Ici.mpr hx) hx
  rw [h0] at h
  exact h

/-- **`x - x³/6 ≤ sin x`** for `x ≥ 0`. -/
theorem sin_ge_cubic {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ sin x := by
  have h3 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t ^ 3) (3 * t ^ 2) t := by
    intro t; simpa using hasDerivAt_pow 3 t
  have hd : ∀ t : ℝ, HasDerivAt (fun t => sin t - (t - t ^ 3 / 6))
      (cos t - (1 - 3 * t ^ 2 / 6)) t := fun t =>
    (hasDerivAt_sin t).sub ((hasDerivAt_id' t).sub ((h3 t).div_const 6))
  have h := nonneg_of_hasDerivAt hd (fun t _ => by
    nlinarith [one_sub_sq_div_two_le_cos (x := t)]) (by simp) hx
  linarith

/-- **`cos x ≤ 1 - x²/2 + x⁴/24`** for `x ≥ 0`. -/
theorem cos_le_quartic {x : ℝ} (hx : 0 ≤ x) : cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have h2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
    intro t; simpa using hasDerivAt_pow 2 t
  have h4 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t ^ 4) (4 * t ^ 3) t := by
    intro t; simpa using hasDerivAt_pow 4 t
  have hd : ∀ t : ℝ, HasDerivAt (fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - cos t)
      (0 - 2 * t / 2 + 4 * t ^ 3 / 24 - -sin t) t := fun t =>
    ((((hasDerivAt_const t (1 : ℝ)).sub ((h2 t).div_const 2)).add ((h4 t).div_const 24)).sub
      (hasDerivAt_cos t))
  have h := nonneg_of_hasDerivAt hd (fun t ht => by
    nlinarith [sin_ge_cubic ht.le]) (by simp) hx
  linarith

/-! ## 2. `tan h ≥ h` -/

/-- `h cos h ≤ sin h` for `0 ≤ h < π/2`. -/
theorem mul_cos_le_sin {h : ℝ} (h0 : 0 ≤ h) (h1 : h < π / 2) : h * cos h ≤ sin h := by
  have hc : 0 < cos h := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], h1⟩
  have ht := le_tan h0 h1
  rw [tan_eq_sin_div_cos, le_div_iff₀ hc] at ht
  exact ht

/-- `h cos(h/2) ≤ 2 sin(h/2)` for `0 ≤ h ≤ π/2` (`tan(h/2) ≥ h/2`). -/
theorem mul_cos_half_le {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ π / 2) :
    h * cos (h / 2) ≤ 2 * sin (h / 2) := by
  have := mul_cos_le_sin (h := h / 2) (by linarith) (by linarith [pi_pos])
  linarith

/-! ## 3. The monotone and midpoint steps for `csc²` -/

/-- **Monotone step**: `h/sin²θ ≤ cot(θ - h) - cot θ` for `0 < h < θ ≤ π/2`. -/
theorem csc_sq_step {θ h : ℝ} (hh : 0 < h) (hθh : h < θ) (hθ : θ ≤ π / 2) :
    h / sin θ ^ 2 ≤ ct (θ - h) - ct θ := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have hs' : 0 < sin (θ - h) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have hc : 0 ≤ cos θ := cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [pi_pos]) hθ
  have hhc : h * cos h ≤ sin h := mul_cos_le_sin hh.le (by linarith)
  have hsh : 0 ≤ sin h := sin_nonneg_of_nonneg_of_le_pi hh.le (by linarith [pi_pos])
  have e1 : sin (θ - h) = sin θ * cos h - cos θ * sin h := sin_sub θ h
  have e2 : cos (θ - h) = cos θ * cos h + sin θ * sin h := cos_sub θ h
  have key : ct (θ - h) - ct θ = sin h / (sin (θ - h) * sin θ) := by
    unfold ct
    rw [div_sub_div _ _ hs'.ne' hs.ne']
    congr 1
    rw [e1, e2]
    linear_combination (sin h) * (sin_sq_add_cos_sq θ)
  rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : h * sin (θ - h) ≤ sin θ * sin h := by
    rw [e1]
    nlinarith [mul_le_mul_of_nonneg_left hhc hs.le, mul_nonneg (mul_nonneg hh.le hc) hsh]
  nlinarith [mul_le_mul_of_nonneg_right h1 hs.le]

/-- **Midpoint step**: `h/sin²m ≤ cot(m - h/2) - cot(m + h/2)` for `0 < h ≤ π/2`,
`h/2 < m`, `m + h/2 < π` (the discrete form of convexity of `csc²`). -/
theorem csc_sq_mid {m h : ℝ} (hh : 0 < h) (hh2 : h ≤ π / 2) (hm : h / 2 < m)
    (hm' : m + h / 2 < π) : h / sin m ^ 2 ≤ ct (m - h / 2) - ct (m + h / 2) := by
  have ha : 0 < sin (m - h / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hb : 0 < sin (m + h / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hS : 0 < sin m := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc2 : 0 ≤ cos (h / 2) :=
    cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [pi_pos]) (by linarith [pi_pos])
  have ea : sin (m - h / 2) = sin m * cos (h / 2) - cos m * sin (h / 2) := sin_sub m (h / 2)
  have eb : sin (m + h / 2) = sin m * cos (h / 2) + cos m * sin (h / 2) := sin_add m (h / 2)
  have eca : cos (m - h / 2) = cos m * cos (h / 2) + sin m * sin (h / 2) := cos_sub m (h / 2)
  have ecb : cos (m + h / 2) = cos m * cos (h / 2) - sin m * sin (h / 2) := cos_add m (h / 2)
  have esh : sin h = 2 * sin (h / 2) * cos (h / 2) := by
    rw [← sin_two_mul]; ring_nf
  have pm := sin_sq_add_cos_sq m
  have p2 := sin_sq_add_cos_sq (h / 2)
  have hprod : sin (m - h / 2) * sin (m + h / 2) = sin m ^ 2 - sin (h / 2) ^ 2 := by
    rw [ea, eb]
    linear_combination sin m ^ 2 * p2 - sin (h / 2) ^ 2 * pm
  have key : ct (m - h / 2) - ct (m + h / 2) =
      sin h / (sin (m - h / 2) * sin (m + h / 2)) := by
    unfold ct
    rw [div_sub_div _ _ ha.ne' hb.ne']
    congr 1
    rw [eca, ecb, ea, eb, esh]
    linear_combination (2 * sin (h / 2) * cos (h / 2)) * pm
  rw [key, hprod]
  have hD : 0 < sin m ^ 2 - sin (h / 2) ^ 2 := by rw [← hprod]; positivity
  rw [div_le_div_iff₀ (by positivity) hD, esh]
  have k1 := mul_cos_half_le hh.le hh2
  have k2 : h * cos (h / 2) ^ 2 ≤ 2 * sin (h / 2) * cos (h / 2) := by
    nlinarith [mul_le_mul_of_nonneg_right k1 hc2]
  have k3 : 0 ≤ h - 2 * sin (h / 2) * cos (h / 2) := by
    rw [← esh]; linarith [sin_le hh.le]
  have k4 : sin m ^ 2 ≤ 1 := sin_sq_le_one m
  have k5 : sin m ^ 2 * (h - 2 * sin (h / 2) * cos (h / 2)) ≤
      h - 2 * sin (h / 2) * cos (h / 2) := by nlinarith
  nlinarith

/-! ## 4. The log step for `csc` -/

/-- `L' = csc` on `(0, π/2]`. -/
theorem lg_hasDerivAt {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ π / 2) :
    HasDerivAt lg (1 / sin θ) θ := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])
  have hc : 0 ≤ cos θ := cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [pi_pos]) h1
  have hd1 := (hasDerivAt_sin θ).log hs.ne'
  have hd2 := ((hasDerivAt_cos θ).const_add 1).log (by linarith : (1 : ℝ) + cos θ ≠ 0)
  have hd := hd1.sub hd2
  have e : cos θ / sin θ - -sin θ / (1 + cos θ) = 1 / sin θ := by
    field_simp
    linear_combination sin_sq_add_cos_sq θ
  rw [e] at hd
  exact hd

/-- **Log step**: `(b - a)/sin b ≤ L(b) - L(a)` for `0 < a < b ≤ π/2`. -/
theorem lg_step {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ π / 2) :
    (b - a) / sin b ≤ lg b - lg a := by
  have hcont : ContinuousOn lg (Set.Icc a b) := fun t ht =>
    (lg_hasDerivAt (by linarith [ht.1]) (by linarith [ht.2])).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope lg (fun t => 1 / sin t) hab hcont
    (fun t ht => lg_hasDerivAt (by linarith [ht.1]) (by linarith [ht.2]))
  have hsξ : 0 < sin ξ := sin_pos_of_pos_of_lt_pi (by linarith [hξ.1]) (by linarith [hξ.2, pi_pos])
  have hle : sin ξ ≤ sin b :=
    sin_le_sin_of_le_of_le_pi_div_two (by linarith [hξ.1, pi_pos]) hb hξ.2.le
  have hba : 0 < b - a := by linarith
  have e : lg b - lg a = (b - a) * (1 / sin ξ) := by
    rw [hξe]; field_simp
  rw [e, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hsξ hle) hba.le

/-- `L` is monotone on `(0, π/2]`. -/
theorem lg_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ π / 2) : lg a ≤ lg b := by
  rcases hab.lt_or_eq with h | h
  · have := lg_step ha h hb
    have hsb : 0 < sin b := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
    have : 0 ≤ (b - a) / sin b := div_nonneg (by linarith) hsb.le
    linarith
  · rw [h]

/-- `L(π/2) = 0`. -/
theorem lg_pi_div_two : lg (π / 2) = 0 := by
  simp [lg]

/-- `-L(h) ≤ log(2/h)` for `0 < h ≤ π/2` (`cot(h/2) ≤ 2/h`). -/
theorem neg_lg_le {h : ℝ} (h0 : 0 < h) (h1 : h ≤ π / 2) : -lg h ≤ log (2 / h) := by
  have hs : 0 < sin h := sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])
  have hc : 0 ≤ cos h := cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [pi_pos]) h1
  have hc2 : 0 ≤ cos (h / 2) :=
    cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [pi_pos]) (by linarith [pi_pos])
  have esh : sin h = 2 * sin (h / 2) * cos (h / 2) := by
    rw [← sin_two_mul]; ring_nf
  have ech : cos h = 2 * cos (h / 2) ^ 2 - 1 := by
    rw [← cos_two_mul]; ring_nf
  have k1 := mul_cos_half_le h0.le h1
  have key : (1 + cos h) / sin h ≤ 2 / h := by
    rw [div_le_div_iff₀ hs h0, esh, ech]
    nlinarith [mul_le_mul_of_nonneg_right k1 hc2]
  have e : -lg h = log ((1 + cos h) / sin h) := by
    unfold lg
    rw [log_div (by linarith) hs.ne']
    ring
  rw [e]
  exact log_le_log (div_pos (by linarith) hs) key

/-! ## 5. `θ + sin θ cos θ ≤ 2 sin θ` -/

/-- **`θ + sin θ cos θ ≤ 2 sin θ`** on `[0, π/2]` (the book's `arcsin x + x√(1-x²) ≤ 2x`). -/
theorem theta_add_sin_mul_cos_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2) :
    θ + sin θ * cos θ ≤ 2 * sin θ := by
  set f : ℝ → ℝ := fun t => 2 * sin t - sin t * cos t - t with hf
  have hd : ∀ t : ℝ, HasDerivAt f
      (2 * cos t - (cos t * cos t + sin t * -sin t) - 1) t := fun t =>
    ((((hasDerivAt_sin t).const_mul 2).sub ((hasDerivAt_sin t).mul (hasDerivAt_cos t))).sub
      (hasDerivAt_id' t))
  have hmono : MonotoneOn f (Set.Icc 0 (π / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (π / 2))
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t).deriv]
      have hc : 0 ≤ cos t :=
        cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [ht.1, pi_pos]) ht.2.le
      have hc1 : cos t ≤ 1 := cos_le_one t
      nlinarith [sin_sq_add_cos_sq t, mul_nonneg hc (sub_nonneg.mpr hc1)]
  have h := hmono ⟨le_rfl, by linarith [pi_pos]⟩ ⟨h0, h1⟩ h0
  simp only [hf, sin_zero, cos_zero, mul_zero, zero_mul, sub_zero] at h
  linarith

/-! ## 6. The `5/3` inequality and `h/sin h` -/

/-- `π²/16 < 0.6169`. -/
theorem pi_sq_div_sixteen_lt : π ^ 2 / 16 < 0.6169 := by
  have := pi_lt_d4
  nlinarith [pi_pos]

/-- **`h²csc²h + h·cot(3h/2) ≤ 5/3`** for `0 < h ≤ π/4`. -/
theorem csc_sq_add_cot_le {h : ℝ} (h0 : 0 < h) (h1 : h ≤ π / 4) :
    h ^ 2 / sin h ^ 2 + h * ct (3 / 2 * h) ≤ 5 / 3 := by
  have hu : h ^ 2 ≤ 0.6169 := by
    have := pi_sq_div_sixteen_lt
    nlinarith [pi_pos]
  set u := h ^ 2 with hu_def
  have hu0 : 0 < u := by positivity
  have hs1 : h * (1 - u / 6) ≤ sin h := by
    have := sin_ge_cubic h0.le
    nlinarith
  have hs15 : 3 / 2 * h * (1 - 3 * u / 8) ≤ sin (3 / 2 * h) := by
    have := sin_ge_cubic (x := 3 / 2 * h) (by positivity)
    nlinarith
  have hc15 : cos (3 / 2 * h) ≤ 1 - 9 * u / 8 + 27 * u ^ 2 / 128 := by
    have := cos_le_quartic (x := 3 / 2 * h) (by positivity)
    nlinarith
  have hD1 : 0 < 1 - u / 6 := by linarith
  have hD2 : 0 < 1 - 3 * u / 8 := by linarith
  have hN : 0 < 1 - 9 * u / 8 + 27 * u ^ 2 / 128 := by nlinarith
  have hsp : 0 < sin h := lt_of_lt_of_le (by positivity) hs1
  have hsp15 : 0 < sin (3 / 2 * h) := lt_of_lt_of_le (by positivity) hs15
  have b1 : h ^ 2 / sin h ^ 2 ≤ 1 / (1 - u / 6) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (h * (1 - u / 6)) ^ 2 ≤ sin h ^ 2 := pow_le_pow_left₀ (by positivity) hs1 2
    nlinarith
  have b2 : h * ct (3 / 2 * h) ≤
      (1 - 9 * u / 8 + 27 * u ^ 2 / 128) / (3 / 2 * (1 - 3 * u / 8)) := by
    unfold ct
    rw [← mul_div_assoc, div_le_div_iff₀ hsp15 (by positivity)]
    have e1 : h * cos (3 / 2 * h) * (3 / 2 * (1 - 3 * u / 8)) ≤
        h * (1 - 9 * u / 8 + 27 * u ^ 2 / 128) * (3 / 2 * (1 - 3 * u / 8)) := by
      have := mul_le_mul_of_nonneg_left hc15 h0.le
      nlinarith
    have e2 : h * (1 - 9 * u / 8 + 27 * u ^ 2 / 128) * (3 / 2 * (1 - 3 * u / 8)) ≤
        (1 - 9 * u / 8 + 27 * u ^ 2 / 128) * sin (3 / 2 * h) := by
      have := mul_le_mul_of_nonneg_left hs15 hN.le
      nlinarith
    linarith
  have hP : 0 ≤ u * (384 - 356 * u + 116 * u ^ 2 - 9 * u ^ 3) := by
    have : 0 ≤ 384 - 356 * u + 116 * u ^ 2 - 9 * u ^ 3 := by nlinarith
    positivity
  have b3 : 1 / (1 - u / 6) ^ 2 + (1 - 9 * u / 8 + 27 * u ^ 2 / 128) / (3 / 2 * (1 - 3 * u / 8))
      ≤ 5 / 3 := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- `h/sin h ≤ 1.115` for `0 < h ≤ π/4`. -/
theorem div_sin_le {h : ℝ} (h0 : 0 < h) (h1 : h ≤ π / 4) : h / sin h ≤ 1.115 := by
  have hu : h ^ 2 ≤ 0.6169 := by
    have := pi_sq_div_sixteen_lt
    nlinarith [pi_pos]
  have hs1 : h * (1 - h ^ 2 / 6) ≤ sin h := by
    have := sin_ge_cubic h0.le
    nlinarith
  have hsp : 0 < sin h := lt_of_lt_of_le (by nlinarith) hs1
  rw [div_le_iff₀ hsp]
  nlinarith

/-! ## 7. `log(1 + μ) ≥ μ log 2` and the sine of a distance -/

/-- `μ - log(1 + μ) ≤ 1 - log 2` for `0 ≤ μ ≤ 1` (concavity of `log`). -/
theorem sub_log_one_add_le {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) :
    μ - log (1 + μ) ≤ 1 - log 2 := by
  have hc := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr one_pos)
    (Set.mem_Ioi.mpr two_pos) (sub_nonneg.mpr h1) h0 (by ring : (1 - μ) + μ = 1)
  simp only [smul_eq_mul, log_one, mul_zero, zero_add] at hc
  have e : (1 - μ) * 1 + μ * 2 = 1 + μ := by ring
  rw [e] at hc
  have hl2 : 0 < 1 - log 2 := by linarith [log_two_lt_d9]
  nlinarith

/-- **`sin(πd) ≤ |sin(πx)|`** whenever `0 ≤ d ≤ |x - m| ≤ 1/2` for an integer `m`. -/
theorem sin_pi_le_abs_sin (x d : ℝ) (m : ℤ) (hd0 : 0 ≤ d) (hd : d ≤ |x - m|)
    (hw : |x - m| ≤ 1 / 2) : sin (π * d) ≤ |sin (π * x)| := by
  have e : sin (π * x) = (-1) ^ m * sin (π * (x - m)) := by
    rw [← sin_add_int_mul_pi]; ring_nf
  have habs : |sin (π * x)| = |sin (π * (x - m))| := by
    rw [e, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  rw [habs]
  have hw' : |π * (x - m)| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos pi_pos]; nlinarith [pi_pos]
  have hsin : |sin (π * (x - m))| = sin (π * |x - m|) := by
    rcases le_total 0 (x - m) with h | h
    · have hx1 : x - m ≤ 1 / 2 := (le_abs_self (x - m)).trans hw
      rw [abs_of_nonneg h]
      exact abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (by nlinarith [pi_pos]))
    · have hx1 : -(1 / 2) ≤ x - m := (neg_le_neg hw).trans (neg_abs_le (x - m))
      rw [abs_of_nonpos h, mul_neg, sin_neg]
      have hle : π * (x - m) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos pi_pos.le h
      rw [abs_of_nonpos (sin_nonpos_of_nonpos_of_neg_pi_le hle (by nlinarith [pi_pos]))]
  rw [hsin]
  apply sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [pi_pos]) (by nlinarith [pi_pos])
  exact mul_le_mul_of_nonneg_left hd pi_pos.le

end Principia.Common.TrigSum
