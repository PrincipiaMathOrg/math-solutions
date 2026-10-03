/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Perron kernel `(1/2π) ∫ y^s / (s(s+1)) dt` from Mellin inversion

For `σ > 0` and `s = σ + it`,

* `(1/2π) ∫_ℝ y^s / (s(s+1)) dt = 1 − 1/y` when `y > 1` (`perron_kernel_gtOne`), and
* `(1/2π) ∫_ℝ y^s / (s(s+1)) dt = 0` when `0 < y < 1` (`perron_kernel_ltOne`).

These are exactly the two statements the Siegel–Walfisz master (`SiegelWalfiszMaster.lean`) took
from PrimeNumberTheoremAnd's `Perron.formulaGtOne` / `Perron.formulaLtOne` (as the shims
`perron_kernel_gtOne` / `perron_kernel_ltOne`). PNT+ pins another Mathlib, so they are re-proved
here from Mathlib's `mellinInv_mellin_eq`: the kernel `k(u) = (1 − u)·1_{(0,1]}(u)` has Mellin
transform `∫₀¹ u^{s−1}(1 − u) du = 1/s − 1/(s+1) = 1/(s(s+1))` (`hasMellin_one_Ioc`,
`hasMellin_cpow_Ioc`), the transform is integrable on vertical lines
(`‖1/(s(s+1))‖ ≤ max 1 σ⁻² · (1 + t²)⁻¹`), and `k` is continuous away from `u = 1`. Mellin
inversion at `u = 1/y` gives `k(1/y)`.
-/

set_option autoImplicit false

namespace Principia.Common.SW

open Complex MeasureTheory Set Filter Topology

/-- The kernel `k(u) = (1 − u)·1_{(0,1]}(u)`, written as a difference of the two indicator functions
whose Mellin transforms Mathlib computes. -/
noncomputable def perronKer : ℝ → ℂ := fun u =>
  indicator (Ioc 0 1) (fun _ => (1 : ℂ)) u - indicator (Ioc 0 1) (fun u : ℝ => (u : ℂ) ^ (1 : ℂ)) u

lemma hasMellin_perronKer {s : ℂ} (hs : 0 < s.re) :
    HasMellin perronKer s (1 / s - 1 / (s + 1)) := by
  have h1 := hasMellin_one_Ioc hs
  have h2 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by rw [one_re]; linarith)
  have h3 := hasMellin_sub h1.1 h2.1
  rw [h1.2, h2.2] at h3
  exact h3

lemma mellin_perronKer {s : ℂ} (hs : 0 < s.re) :
    mellin perronKer s = 1 / (s * (s + 1)) := by
  rw [(hasMellin_perronKer hs).2]
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, zero_re] at hs
    exact lt_irrefl 0 hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have h' : (s + 1).re = 0 := by rw [h, zero_re]
    rw [add_re, one_re] at h'
    linarith
  rw [div_sub_div _ _ hs0 hs1]
  congr 1
  ring

lemma re_ofReal_add_mul_I (σ t : ℝ) : ((σ : ℂ) + t * I).re = σ := by
  simp

lemma perron_denom_ne_zero {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1) ≠ 0 := by
  apply mul_ne_zero
  · intro h
    have h' := congrArg Complex.re h
    rw [re_ofReal_add_mul_I, zero_re] at h'
    linarith
  · intro h
    have h' := congrArg Complex.re h
    rw [add_re, re_ofReal_add_mul_I, one_re, zero_re] at h'
    linarith

/-- `‖1/(s(s+1))‖ ≤ max 1 σ⁻² · (1 + t²)⁻¹` on the line `Re s = σ > 0`. -/
lemma norm_perron_le {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ‖1 / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1))‖ ≤ max 1 (σ ^ 2)⁻¹ * (1 + t ^ 2)⁻¹ := by
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hn : ‖s‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hs]
    simp
    ring
  have hn1 : ‖s + 1‖ ^ 2 = (σ + 1) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hs]
    simp
    ring
  have hP0 : 0 ≤ ‖s‖ * ‖s + 1‖ := by positivity
  have hPsq : (‖s‖ * ‖s + 1‖) ^ 2 = (σ ^ 2 + t ^ 2) * ((σ + 1) ^ 2 + t ^ 2) := by
    rw [mul_pow, hn, hn1]
  set m : ℝ := min (σ ^ 2) 1 with hm
  have hm0 : 0 < m := lt_min (by positivity) one_pos
  have hmσ : m ≤ σ ^ 2 := min_le_left _ _
  have hm1 : m ≤ 1 := min_le_right _ _
  have hk0 : 0 ≤ m * (1 + t ^ 2) := by positivity
  have hkle : m * (1 + t ^ 2) ≤ σ ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hkle' : m * (1 + t ^ 2) ≤ (σ + 1) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hsq : (m * (1 + t ^ 2)) ^ 2 ≤ (‖s‖ * ‖s + 1‖) ^ 2 := by
    rw [hPsq, sq]
    exact mul_le_mul hkle hkle' hk0 (by positivity)
  have hP : m * (1 + t ^ 2) ≤ ‖s‖ * ‖s + 1‖ := by nlinarith
  have hkpos : 0 < m * (1 + t ^ 2) := by positivity
  rw [norm_div, norm_one, norm_mul]
  have hmax : m⁻¹ = max 1 (σ ^ 2)⁻¹ := by
    rw [hm]
    rcases le_total (σ ^ 2) 1 with h | h
    · rw [min_eq_left h, max_eq_right (one_le_inv_iff₀.mpr ⟨by positivity, h⟩)]
    · rw [min_eq_right h, inv_one, max_eq_left (inv_le_one_of_one_le₀ h)]
  rw [← hmax]
  calc 1 / (‖s‖ * ‖s + 1‖) ≤ 1 / (m * (1 + t ^ 2)) :=
        one_div_le_one_div_of_le hkpos hP
    _ = m⁻¹ * (1 + t ^ 2)⁻¹ := by rw [one_div, mul_inv]

lemma verticalIntegrable_perronKer {σ : ℝ} (hσ : 0 < σ) :
    VerticalIntegrable (mellin perronKer) σ := by
  unfold VerticalIntegrable
  have hpt : (fun t : ℝ => mellin perronKer ((σ : ℂ) + t * I)) =
      fun t : ℝ => 1 / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1)) := by
    funext t
    exact mellin_perronKer (by rw [re_ofReal_add_mul_I]; exact hσ)
  rw [hpt]
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (max 1 (σ ^ 2)⁻¹)) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    exact Continuous.div continuous_const (by fun_prop) (perron_denom_ne_zero hσ)
  · exact Eventually.of_forall (norm_perron_le hσ)

lemma perronKer_of_mem {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : perronKer u = 1 - (u : ℂ) := by
  have hu' : u ∈ Ioc (0 : ℝ) 1 := Ioo_subset_Ioc_self hu
  simp only [perronKer, indicator_of_mem hu', cpow_one]

lemma perronKer_of_one_lt {u : ℝ} (hu : 1 < u) : perronKer u = 0 := by
  have hu' : u ∉ Ioc (0 : ℝ) 1 := fun h => by linarith [h.2]
  simp only [perronKer, indicator_of_notMem hu', sub_zero]

lemma continuousAt_perronKer {u : ℝ} (hu : 0 < u) (hu1 : u ≠ 1) : ContinuousAt perronKer u := by
  rcases lt_or_gt_of_ne hu1 with h | h
  · have hc : ContinuousAt (fun v : ℝ => 1 - (v : ℂ)) u := by fun_prop
    refine hc.congr ?_
    filter_upwards [Ioo_mem_nhds hu h] with v hv
    exact (perronKer_of_mem hv).symm
  · have hc : ContinuousAt (fun _ : ℝ => (0 : ℂ)) u := continuousAt_const
    refine hc.congr ?_
    filter_upwards [Ioi_mem_nhds h] with v hv
    exact (perronKer_of_one_lt hv).symm

/-- Mellin inversion for the Perron kernel, at a point `u ≠ 1`. -/
theorem perron_kernel_mellin (σ : ℝ) (hσ : 0 < σ) (u : ℝ) (hu : 0 < u) (hu1 : u ≠ 1) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, (u : ℂ) ^ (-((σ : ℂ) + t * I)) *
        (1 / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1))) = perronKer u := by
  have hconv : MellinConvergent perronKer (σ : ℂ) :=
    (hasMellin_perronKer (by rw [ofReal_re]; exact hσ)).1
  have h := mellinInv_mellin_eq σ perronKer hu hconv (verticalIntegrable_perronKer hσ)
    (continuousAt_perronKer hu hu1)
  rw [← h, mellinInv, Complex.real_smul]
  congr 1
  · push_cast
    ring
  · congr 1
    funext t
    rw [smul_eq_mul, mellin_perronKer (by rw [re_ofReal_add_mul_I]; exact hσ)]

lemma inv_cpow_neg_of_pos {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ((y⁻¹ : ℝ) : ℂ) ^ (-s) = (y : ℂ) ^ s := by
  have harg : (y : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg hy.le]
    exact Real.pi_ne_zero.symm
  rw [ofReal_inv, inv_cpow _ _ harg, cpow_neg, inv_inv]

/-- **Perron kernel, `y > 1`** (the master's shim `perron_kernel_gtOne`). -/
theorem perron_kernel_gtOne (y : ℝ) (hy : 1 < y) (σ : ℝ) (hσ : 0 < σ) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        ((y : ℂ) ^ ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1))
      = 1 - 1 / (y : ℂ) := by
  have hy0 : 0 < y := by linarith
  have hu : 0 < y⁻¹ := inv_pos.mpr hy0
  have hu1 : y⁻¹ < 1 := inv_lt_one_of_one_lt₀ hy
  have h := perron_kernel_mellin σ hσ y⁻¹ hu hu1.ne
  rw [perronKer_of_mem ⟨hu, hu1⟩] at h
  have hfun : (fun t : ℝ => ((y⁻¹ : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) *
      (1 / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1)))) =
      fun t : ℝ => ((y : ℂ) ^ ((σ : ℂ) + t * I)) /
        (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1)) := by
    funext t
    rw [inv_cpow_neg_of_pos hy0, ← div_eq_mul_one_div]
  rw [hfun] at h
  rw [h, ofReal_inv, one_div]

/-- **Perron kernel, `0 < y < 1`** (the master's shim `perron_kernel_ltOne`). -/
theorem perron_kernel_ltOne (y : ℝ) (hy0 : 0 < y) (hy : y < 1) (σ : ℝ) (hσ : 0 < σ) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        ((y : ℂ) ^ ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1))
      = 0 := by
  have hu : 0 < y⁻¹ := inv_pos.mpr hy0
  have hu1 : 1 < y⁻¹ := (one_lt_inv₀ hy0).mpr hy
  have h := perron_kernel_mellin σ hσ y⁻¹ hu hu1.ne'
  rw [perronKer_of_one_lt hu1] at h
  have hfun : (fun t : ℝ => ((y⁻¹ : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) *
      (1 / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1)))) =
      fun t : ℝ => ((y : ℂ) ^ ((σ : ℂ) + t * I)) /
        (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1)) := by
    funext t
    rw [inv_cpow_neg_of_pos hy0, ← div_eq_mul_one_div]
  rw [hfun] at h
  exact h

end Principia.Common.SW
