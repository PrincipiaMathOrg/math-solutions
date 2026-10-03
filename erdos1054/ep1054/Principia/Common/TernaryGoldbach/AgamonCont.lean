/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.ExplicitSpine

set_option autoImplicit false

/-!
# `EF.Continuation` PROVED: `G = M f` continues to `−1 < Re s < b`, `b > 3/2`

**`continuation_holds : EF.Continuation`**, with no hypothesis. The link of
`ExplicitSpine.lean` (survey EF1) asserts that `EF.Gcont η δ` (`G = M f` for `Re s > 0`, `G(0)` at
`0`, `−M f'(s + 1)/s` otherwise) is holomorphic on `−1 < Re s < b` for some `b > 3/2`, for every
`η` with `HM.AgamonReg η` and `η(0) = 0`.

Route (the docstring's): with `(a, b)` the strip of `HM.AgamonReg`,
* `M f` is holomorphic on `0 < Re s < b` (`differentiableOn_gm`), by differentiating under the
  integral sign (`mellin_hasDerivAt_int`, a version of Mathlib's
  `mellin_hasDerivAt_of_isBigO_rpow` whose hypotheses are two weighted `L¹` bounds instead of
  `O`-bounds at `0` and `∞`: `|log t| t^{x ± v − 1} ≤ (2/v)(t^{σ₂−1} + t^{σ₁−1})`, `log_weight_le`);
* `F(s) = M f'(s + 1)` is holomorphic on `−1 < Re s < 1/2` (same lemma at `s + 1`);
* integration by parts (`ibp`): `s·M f(s) = −F(s)` on `0 < Re s < 1/2` (boundary terms: `t^s f → 0`
  at `0⁺` since `Re s > 0`, and at `∞` by Mathlib's `tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi`
  since `t^s f ∈ L¹` for `Re s + 1 < b`);
* `F(0) = ∫ f' = f(∞) − f(0) = 0` (`fd_zero`: here `η(0) = 0` is used), and
  `F'(0) = ∫ f' log t = −G(0)` (`hasDerivAt_fd`);
* so `G_cont = −dslope F 0` on `−1 < Re s < 1/2` (`gcont_eq_dslope`), holomorphic by Mathlib's
  removable-singularity theorem `Complex.differentiableOn_dslope`; on `Re s > 0` it is `M f`.

Also PROVED here, for `MollDecay` (`AgamonDecay.lean`): `G_cont` is bounded on the closed strip
`−1/2 ≤ Re s ≤ 3/2` (`gcont_bounded`): `|M f| ≤ ∫(t^{−1/2} + t^{1/2})|f|` for `Re s ≥ 1/2`,
`|G_cont(s)| ≤ |F(s)| ≤ ∫(t^{−1/2} + t^{1/2})|f'|` for `Re s < 1/2`, `|Im s| ≥ 1`, and continuity
on the compact rectangle `[−1/2, 1/2] × [−1, 1]`.

No falsification: the link is TRUE as stated (the hypothesis `η(0) = 0` is exactly what makes
`F(0) = 0`; without it `G_cont` has a pole at `0`).
-/

namespace Principia.Common.TernaryGoldbach.AG

open MeasureTheory Set Filter Topology Principia.Common.Goldbach
open Principia.Common.TernaryGoldbach Principia.Common.TernaryGoldbach.EF

/-! ## (1) Differentiating a Mellin transform under the integral sign -/

/-- `t^b ≤ t^c + t^a` for `a ≤ b ≤ c`, `t > 0`. -/
theorem rpow_le_add_rpow {t a b c : ℝ} (ht : 0 < t) (hab : a ≤ b) (hbc : b ≤ c) :
    t ^ b ≤ t ^ c + t ^ a := by
  rcases le_or_gt 1 t with h | h
  · have h1 := Real.rpow_le_rpow_of_exponent_le h hbc
    have h2 := Real.rpow_nonneg ht.le a
    linarith
  · have h1 := Real.rpow_le_rpow_of_exponent_ge ht h.le hab
    have h2 := Real.rpow_nonneg ht.le c
    linarith

/-- **`(t^{x+v−1} + t^{x−v−1})|log t| ≤ (2/v)(t^{σ₂−1} + t^{σ₁−1})`** when `σ₁ ≤ x − 2v` and
`x + 2v ≤ σ₂` (`log t ≤ t^v/v`). -/
theorem log_weight_le {t x v σ₁ σ₂ : ℝ} (ht : 0 < t) (hv : 0 < v) (h1 : σ₁ ≤ x - 2 * v)
    (h2 : x + 2 * v ≤ σ₂) :
    (t ^ (x + v - 1) + t ^ (x - v - 1)) * |Real.log t| ≤
      2 / v * (t ^ (σ₂ - 1) + t ^ (σ₁ - 1)) := by
  have hp1 : 0 ≤ t ^ (σ₁ - 1) := Real.rpow_nonneg ht.le _
  have hp2 : 0 ≤ t ^ (σ₂ - 1) := Real.rpow_nonneg ht.le _
  rcases le_or_gt 1 t with h | h
  · have hl : 0 ≤ Real.log t := Real.log_nonneg h
    have hlog : Real.log t ≤ t ^ v / v := Real.log_le_rpow_div ht.le hv
    have e1 : t ^ (x - v - 1) ≤ t ^ (x + v - 1) :=
      Real.rpow_le_rpow_of_exponent_le h (by linarith)
    have e2 : t ^ (x + v - 1) * t ^ v = t ^ (x + 2 * v - 1) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    have e3 : t ^ (x + 2 * v - 1) ≤ t ^ (σ₂ - 1) :=
      Real.rpow_le_rpow_of_exponent_le h (by linarith)
    have hq : 0 ≤ t ^ (x + v - 1) := Real.rpow_nonneg ht.le _
    rw [abs_of_nonneg hl]
    calc (t ^ (x + v - 1) + t ^ (x - v - 1)) * Real.log t
        ≤ (2 * t ^ (x + v - 1)) * (t ^ v / v) :=
          mul_le_mul (by linarith) hlog hl (by positivity)
      _ = 2 / v * (t ^ (x + v - 1) * t ^ v) := by field_simp
      _ = 2 / v * t ^ (x + 2 * v - 1) := by rw [e2]
      _ ≤ 2 / v * (t ^ (σ₂ - 1) + t ^ (σ₁ - 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hl : Real.log t < 0 := Real.log_neg ht h
    have hlog : -Real.log t ≤ t ^ (-v) / v := by
      have h3 := Real.log_le_rpow_div (inv_pos.mpr ht).le hv
      rwa [Real.log_inv, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at h3
    have e1 : t ^ (x + v - 1) ≤ t ^ (x - v - 1) :=
      Real.rpow_le_rpow_of_exponent_ge ht h.le (by linarith)
    have e2 : t ^ (x - v - 1) * t ^ (-v) = t ^ (x - 2 * v - 1) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    have e3 : t ^ (x - 2 * v - 1) ≤ t ^ (σ₁ - 1) :=
      Real.rpow_le_rpow_of_exponent_ge ht h.le (by linarith)
    have hq : 0 ≤ t ^ (x - v - 1) := Real.rpow_nonneg ht.le _
    rw [abs_of_neg hl]
    calc (t ^ (x + v - 1) + t ^ (x - v - 1)) * -Real.log t
        ≤ (2 * t ^ (x - v - 1)) * (t ^ (-v) / v) :=
          mul_le_mul (by linarith) hlog (by linarith) (by positivity)
      _ = 2 / v * (t ^ (x - v - 1) * t ^ (-v)) := by field_simp
      _ = 2 / v * t ^ (x - 2 * v - 1) := by rw [e2]
      _ ≤ 2 / v * (t ^ (σ₂ - 1) + t ^ (σ₁ - 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- `t ↦ t^{σ−1}` is continuous on `(0, ∞)`. -/
theorem continuousOn_rpow_sub (σ : ℝ) : ContinuousOn (fun t : ℝ => t ^ (σ - 1)) (Ioi 0) :=
  continuousOn_of_forall_continuousAt fun _ ht =>
    Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht))

/-- `t ↦ t^{z−1}` (complex) is continuous on `(0, ∞)`. -/
theorem continuousOn_cpow_sub (z : ℂ) : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (z - 1)) (Ioi 0) :=
  continuousOn_of_forall_continuousAt fun _ ht =>
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))

/-- **Two weighted `L¹` bounds give convergence in between.** -/
theorem mellinConvergent_of_two {f : ℝ → ℂ} {s : ℂ} {σ₁ σ₂ : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (h1 : σ₁ ≤ s.re) (h2 : s.re ≤ σ₂)
    (i1 : IntegrableOn (fun t : ℝ => t ^ (σ₁ - 1) * ‖f t‖) (Ioi 0))
    (i2 : IntegrableOn (fun t : ℝ => t ^ (σ₂ - 1) * ‖f t‖) (Ioi 0)) :
    MellinConvergent f s := by
  rw [MellinConvergent, mellin_convergent_iff_norm Subset.rfl measurableSet_Ioi hfm]
  refine Integrable.mono' (i2.add i1) (((continuousOn_rpow_sub s.re).aestronglyMeasurable
    measurableSet_Ioi).mul hfm.norm) ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun t ht => ?_))
  have ht' : (0 : ℝ) < t := ht
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht'.le _) (norm_nonneg _))]
  have hle := rpow_le_add_rpow ht' (show σ₁ - 1 ≤ s.re - 1 by linarith)
    (show s.re - 1 ≤ σ₂ - 1 by linarith)
  calc t ^ (s.re - 1) * ‖f t‖ ≤ (t ^ (σ₂ - 1) + t ^ (σ₁ - 1)) * ‖f t‖ :=
        mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    _ = t ^ (σ₂ - 1) * ‖f t‖ + t ^ (σ₁ - 1) * ‖f t‖ := add_mul _ _ _

/-- **`|M f(s)| ≤ ∫(t^{σ₂−1} + t^{σ₁−1})|f|`** for `σ₁ ≤ Re s ≤ σ₂`. -/
theorem norm_mellin_le_two {f : ℝ → ℂ} {s : ℂ} {σ₁ σ₂ : ℝ} (h1 : σ₁ ≤ s.re) (h2 : s.re ≤ σ₂)
    (i1 : IntegrableOn (fun t : ℝ => t ^ (σ₁ - 1) * ‖f t‖) (Ioi 0))
    (i2 : IntegrableOn (fun t : ℝ => t ^ (σ₂ - 1) * ‖f t‖) (Ioi 0)) :
    ‖mellin f s‖ ≤ ∫ t in Ioi (0 : ℝ), (t ^ (σ₂ - 1) * ‖f t‖ + t ^ (σ₁ - 1) * ‖f t‖) := by
  unfold mellin
  refine norm_integral_le_of_norm_le (i2.add i1) ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun t ht => ?_))
  have ht' : (0 : ℝ) < t := ht
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.sub_re, Complex.one_re]
  have hle := rpow_le_add_rpow ht' (show σ₁ - 1 ≤ s.re - 1 by linarith)
    (show s.re - 1 ≤ σ₂ - 1 by linarith)
  calc t ^ (s.re - 1) * ‖f t‖ ≤ (t ^ (σ₂ - 1) + t ^ (σ₁ - 1)) * ‖f t‖ :=
        mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    _ = t ^ (σ₂ - 1) * ‖f t‖ + t ^ (σ₁ - 1) * ‖f t‖ := add_mul _ _ _

/-- **Differentiation of a Mellin transform under the integral sign** from two weighted `L¹`
bounds `σ₁ < Re s < σ₂` (Mathlib's `mellin_hasDerivAt_of_isBigO_rpow` with `O`-bounds replaced by
integrability; same proof, bound `(2/v)(t^{σ₂−1} + t^{σ₁−1})|f|` from `log_weight_le`). -/
theorem mellin_hasDerivAt_int {f : ℝ → ℂ} {s : ℂ} {σ₁ σ₂ : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (h1 : σ₁ < s.re) (h2 : s.re < σ₂)
    (i1 : IntegrableOn (fun t : ℝ => t ^ (σ₁ - 1) * ‖f t‖) (Ioi 0))
    (i2 : IntegrableOn (fun t : ℝ => t ^ (σ₂ - 1) * ‖f t‖) (Ioi 0)) :
    HasDerivAt (mellin f) (mellin (fun t => (Real.log t : ℂ) * f t) s) s := by
  set F : ℂ → ℝ → ℂ := fun (z : ℂ) (t : ℝ) => (t : ℂ) ^ (z - 1) • f t with hF
  set F' : ℂ → ℝ → ℂ := fun (z : ℂ) (t : ℝ) => ((t : ℂ) ^ (z - 1) * Real.log t) • f t with hF'
  set v : ℝ := min (s.re - σ₁) (σ₂ - s.re) / 3 with hvdef
  have hmin : 0 < min (s.re - σ₁) (σ₂ - s.re) := lt_min (by linarith) (by linarith)
  have hv0 : 0 < v := by positivity
  have hv1 : σ₁ ≤ s.re - 2 * v := by
    have := min_le_left (s.re - σ₁) (σ₂ - s.re)
    rw [hvdef]
    linarith
  have hv2 : s.re + 2 * v ≤ σ₂ := by
    have := min_le_right (s.re - σ₁) (σ₂ - s.re)
    rw [hvdef]
    linarith
  have hm1 : ∀ᶠ z : ℂ in 𝓝 s, AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) :=
    Eventually.of_forall fun z =>
      ((continuousOn_cpow_sub z).aestronglyMeasurable measurableSet_Ioi).smul hfm
  have hm2 : Integrable (F s) (volume.restrict (Ioi 0)) :=
    mellinConvergent_of_two hfm h1.le h2.le i1 i2
  have hm3 : AEStronglyMeasurable (F' s) (volume.restrict (Ioi 0)) := by
    refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi).smul hfm
    exact (continuousOn_cpow_sub s).mul (Complex.continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono (subset_compl_singleton_iff.mpr self_notMem_Ioi)))
  have hm4 : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), ∀ z ∈ Metric.ball s v,
      ‖F' z t‖ ≤ 2 / v * (t ^ (σ₂ - 1) * ‖f t‖ + t ^ (σ₁ - 1) * ‖f t‖) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht z hz => ?_
    have ht' : (0 : ℝ) < t := ht
    have hzre : |z.re - s.re| < v := by
      have h3 := Complex.abs_re_le_norm (z - s)
      rw [Metric.mem_ball, dist_eq_norm] at hz
      rw [Complex.sub_re] at h3
      linarith
    have hpow : t ^ (z.re - 1) ≤ t ^ (s.re + v - 1) + t ^ (s.re - v - 1) :=
      rpow_le_add_rpow ht' (by linarith [(abs_lt.mp hzre).1])
        (by linarith [(abs_lt.mp hzre).2])
    have hw := log_weight_le ht' hv0 hv1 hv2
    simp only [hF', norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.sub_re, Complex.one_re]
    calc t ^ (z.re - 1) * |Real.log t| * ‖f t‖
        ≤ (t ^ (s.re + v - 1) + t ^ (s.re - v - 1)) * |Real.log t| * ‖f t‖ := by gcongr
      _ ≤ 2 / v * (t ^ (σ₂ - 1) + t ^ (σ₁ - 1)) * ‖f t‖ := by gcongr
      _ = 2 / v * (t ^ (σ₂ - 1) * ‖f t‖ + t ^ (σ₁ - 1) * ‖f t‖) := by ring
  have hm5 : Integrable (fun t : ℝ => 2 / v * (t ^ (σ₂ - 1) * ‖f t‖ + t ^ (σ₁ - 1) * ‖f t‖))
      (volume.restrict (Ioi 0)) := (i2.add i1).const_mul (2 / v)
  have hm6 : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), ∀ y ∈ Metric.ball s v,
      HasDerivAt (fun z : ℂ => F z t) (F' y t) y := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht y _ => ?_
    have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    have u1 : HasDerivAt (fun z : ℂ => (t : ℂ) ^ (z - 1)) ((t : ℂ) ^ (y - 1) * Real.log t) y := by
      convert ((hasDerivAt_id' y).sub_const 1).const_cpow (Or.inl ht') using 1
      rw [Complex.ofReal_log (le_of_lt ht)]
      ring
    exact u1.smul_const (f t)
  have main := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s hv0) hm1 hm2 hm3 hm4 hm5 hm6
  have e : (∫ t in Ioi (0 : ℝ), F' s t) = mellin (fun t => (Real.log t : ℂ) * f t) s := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hF', smul_eq_mul]
    ring
  rw [← e]
  exact main.2

/-! ## (2) The weight `f = η e(δ·)` under `AgamonReg` -/

/-- `|f(t)| = |η(t)|`. -/
theorem norm_fw (η : ℝ → ℝ) (δ t : ℝ) : ‖fw η δ t‖ = |η t| := by
  rw [fw, norm_mul, norm_e_eq, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- `f` is a.e.-strongly measurable on `(0, ∞)`. -/
theorem aesm_fw {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) :
    AEStronglyMeasurable (fw η δ) (volume.restrict (Ioi 0)) :=
  (continuousOn_fw hreg δ).aestronglyMeasurable measurableSet_Ioi

/-- `f'` is a.e.-strongly measurable. -/
theorem aesm_dfw (η : ℝ → ℝ) (δ : ℝ) :
    AEStronglyMeasurable (deriv (fw η δ)) (volume.restrict (Ioi 0)) :=
  (measurable_deriv _).aestronglyMeasurable

/-- `f` has derivative `deriv f` on `(0, ∞)`. -/
theorem hasDerivAt_fw' {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fw η δ) (deriv (fw η δ) t) t :=
  (hasDerivAt_fw (agamon_diff hreg ht) δ).differentiableAt.hasDerivAt

/-- **The strip of `AgamonReg`, for `f` and `f'`.** -/
theorem agamon_strip {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) :
    ∃ a b : ℝ, a ≤ 0 ∧ 3 / 2 < b ∧ ∀ σ ∈ Ioo a b,
      IntegrableOn (fun t : ℝ => t ^ (σ - 1) * ‖fw η δ t‖) (Ioi 0) ∧
        IntegrableOn (fun t : ℝ => t ^ (σ - 1) * ‖deriv (fw η δ) t‖) (Ioi 0) := by
  obtain ⟨a, b, ha, hb, hab⟩ := hreg.2.2.2
  refine ⟨a, b, ha, hb, fun σ hσ => ⟨?_, ?_⟩⟩
  · refine IntegrableOn.congr_fun (hab σ hσ).1.norm (fun t ht => ?_) measurableSet_Ioi
    have ht' : (0 : ℝ) < t := ht
    rw [norm_fw, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ht' _), mul_comm]
  · have hb' : IntegrableOn (fun t => ‖deriv η t * t ^ (σ - 1)‖ +
        2 * Real.pi * |δ| * ‖η t * t ^ (σ - 1)‖) (Ioi 0) :=
      (hab σ hσ).2.norm.add ((hab σ hσ).1.norm.const_mul _)
    refine hb'.mono' (((continuousOn_rpow_sub σ).aestronglyMeasurable measurableSet_Ioi).mul
      (aesm_dfw η δ).norm) ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t ht => ?_))
    have ht' : (0 : ℝ) < t := ht
    have hp : 0 < t ^ (σ - 1) := Real.rpow_pos_of_pos ht' _
    have hd := norm_deriv_fw_le (agamon_diff hreg ht') δ
    rw [Real.norm_of_nonneg (mul_nonneg hp.le (norm_nonneg _)), norm_mul, norm_mul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp]
    calc t ^ (σ - 1) * ‖deriv (fw η δ) t‖
        ≤ t ^ (σ - 1) * (|deriv η t| + 2 * Real.pi * |δ| * |η t|) :=
          mul_le_mul_of_nonneg_left hd hp.le
      _ = |deriv η t| * t ^ (σ - 1) + 2 * Real.pi * |δ| * (|η t| * t ^ (σ - 1)) := by ring

/-- **`G = M f` is holomorphic on `0 < Re s < b`.** -/
theorem differentiableOn_gm {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) :
    ∃ b : ℝ, 3 / 2 < b ∧ DifferentiableOn ℂ (HM.Gm η δ) {s | 0 < s.re ∧ s.re < b} := by
  obtain ⟨a, b, ha, hb, hab⟩ := agamon_strip hreg δ
  refine ⟨b, hb, fun s hs => ?_⟩
  have hs0 : 0 < s.re := hs.1
  have hsb : s.re < b := hs.2
  have h := mellin_hasDerivAt_int (aesm_fw hreg δ) (show s.re / 2 < s.re by linarith)
    (show s.re < (s.re + b) / 2 by linarith) (hab _ ⟨by linarith, by linarith⟩).1
    (hab _ ⟨by linarith, by linarith⟩).1
  exact h.differentiableAt.differentiableWithinAt

/-! ## (3) `F(s) = M f'(s + 1)`: holomorphy, `F(0) = 0`, `F'(0) = −G(0)` -/

/-- `F(s) = M f'(s + 1)`. -/
noncomputable def Fd (η : ℝ → ℝ) (δ : ℝ) (s : ℂ) : ℂ := mellin (deriv (fw η δ)) (s + 1)

/-- **`F` is holomorphic on `−1 < Re s < 1/2`**, with `F'(s) = M(log·f')(s + 1)`. -/
theorem hasDerivAt_fd {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) {s : ℂ} (h1 : -1 < s.re)
    (h2 : s.re < 1 / 2) :
    HasDerivAt (Fd η δ) (mellin (fun t => (Real.log t : ℂ) * deriv (fw η δ) t) (s + 1)) s := by
  obtain ⟨a, b, ha, hb, hab⟩ := agamon_strip hreg δ
  have hre : (s + 1).re = s.re + 1 := by simp
  have h := mellin_hasDerivAt_int (aesm_dfw η δ)
    (show (s.re + 1) / 2 < (s + 1).re by rw [hre]; linarith)
    (show (s + 1).re < (s.re + 1 + 3 / 2) / 2 by rw [hre]; linarith)
    (hab _ ⟨by linarith, by linarith⟩).2 (hab _ ⟨by linarith, by linarith⟩).2
  exact h.comp_add_const s 1

/-- `f → 0` at `∞` (`f, f' ∈ L¹`). -/
theorem tendsto_fw_atTop {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) :
    Tendsto (fw η δ) atTop (𝓝 0) := by
  obtain ⟨a, b, ha, hb, hab⟩ := agamon_strip hreg δ
  have h1 := hab 1 ⟨by linarith, by linarith⟩
  have i1 : IntegrableOn (fw η δ) (Ioi 0) := by
    refine Integrable.mono' h1.1 (aesm_fw hreg δ) ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t _ => ?_))
    rw [sub_self, Real.rpow_zero, one_mul]
  have i2 : IntegrableOn (deriv (fw η δ)) (Ioi 0) := by
    refine Integrable.mono' h1.2 (aesm_dfw η δ) ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t _ => ?_))
    rw [sub_self, Real.rpow_zero, one_mul]
  exact tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun t ht => hasDerivAt_fw' hreg δ ht) i2 i1

/-- `f` is continuous on `[0, ∞)`. -/
theorem contWithinAt_fw_zero {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) :
    ContinuousWithinAt (fw η δ) (Ici 0) 0 := by
  have hη : ContinuousWithinAt η (Ici 0) 0 := hreg.1.continuousOn 0 self_mem_Ici
  have he : Continuous fun t : ℝ => e (δ * t) := by unfold e; fun_prop
  exact (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt hη).mul
    he.continuousWithinAt

/-- **`F(0) = ∫₀^∞ f' = f(∞) − f(0) = 0`** (uses `η(0) = 0`). -/
theorem fd_zero {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (h0 : η 0 = 0) (δ : ℝ) : Fd η δ 0 = 0 := by
  obtain ⟨a, b, ha, hb, hab⟩ := agamon_strip hreg δ
  have h1 := hab 1 ⟨by linarith, by linarith⟩
  have i2 : IntegrableOn (deriv (fw η δ)) (Ioi 0) := by
    refine Integrable.mono' h1.2 (aesm_dfw η δ) ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t _ => ?_))
    rw [sub_self, Real.rpow_zero, one_mul]
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto (contWithinAt_fw_zero hreg δ)
    (fun t ht => hasDerivAt_fw' hreg δ ht) i2 (tendsto_fw_atTop hreg δ)
  have hf0 : fw η δ 0 = 0 := by rw [fw, h0]; simp
  rw [hf0, sub_zero] at hI
  unfold Fd mellin
  rw [zero_add, sub_self]
  simp only [Complex.cpow_zero, one_smul]
  exact hI

/-- **`F'(0) = −G(0)`**: `M(log·f')(1) = ∫ f' log t`. -/
theorem fd_deriv_zero {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) :
    deriv (Fd η δ) 0 = -G0 η δ := by
  rw [(hasDerivAt_fd hreg δ (by simp) (by simp)).deriv, G0, neg_neg]
  unfold mellin
  rw [zero_add, sub_self]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Complex.cpow_zero, one_smul]
  ring

/-! ## (4) Integration by parts on `0 < Re s < 1/2` -/

/-- **`s·M f(s) = −M f'(s + 1)`** for `0 < Re s < 1/2`: `∫ t^s f' = −∫ s t^{s−1} f`, the boundary
terms vanishing at `0⁺` (`Re s > 0`, `f` continuous at `0`) and at `∞` (`t^s f ∈ L¹`). -/
theorem ibp {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (δ : ℝ) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1 / 2) : s * HM.Gm η δ s = -Fd η δ s := by
  obtain ⟨a, b, ha, hb, hab⟩ := agamon_strip hreg δ
  have hsne : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs0
    exact lt_irrefl 0 hs0
  set u : ℝ → ℂ := fun t => (t : ℂ) ^ s with hu
  set u' : ℝ → ℂ := fun t => s * (t : ℂ) ^ (s - 1) with hu'
  have hud : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt u (u' t) t := fun t ht =>
    hasDerivAt_ofReal_cpow_const (ne_of_gt ht) hsne
  have hvd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fw η δ) (deriv (fw η δ) t) t :=
    fun t ht => hasDerivAt_fw' hreg δ ht
  have hre1 : (s + 1).re = s.re + 1 := by simp
  -- `u f'` and `u f` are integrable (the Mellin integrand at `s + 1`)
  have huv' : IntegrableOn (u * deriv (fw η δ)) (Ioi 0) := by
    have hc : MellinConvergent (deriv (fw η δ)) (s + 1) :=
      mellinConvergent_of_two (aesm_dfw η δ) le_rfl le_rfl
        (hab _ ⟨by rw [hre1]; linarith, by rw [hre1]; linarith⟩).2
        (hab _ ⟨by rw [hre1]; linarith, by rw [hre1]; linarith⟩).2
    refine IntegrableOn.congr_fun hc (fun t _ => ?_) measurableSet_Ioi
    simp only [hu, Pi.mul_apply, smul_eq_mul, add_sub_cancel_right]
  have huv : IntegrableOn (u * fw η δ) (Ioi 0) := by
    have hc : MellinConvergent (fw η δ) (s + 1) :=
      mellinConvergent_of_two (aesm_fw hreg δ) le_rfl le_rfl
        (hab _ ⟨by rw [hre1]; linarith, by rw [hre1]; linarith⟩).1
        (hab _ ⟨by rw [hre1]; linarith, by rw [hre1]; linarith⟩).1
    refine IntegrableOn.congr_fun hc (fun t _ => ?_) measurableSet_Ioi
    simp only [hu, Pi.mul_apply, smul_eq_mul, add_sub_cancel_right]
  have hu'v : IntegrableOn (u' * fw η δ) (Ioi 0) := by
    have hc : MellinConvergent (fw η δ) s :=
      mellinConvergent_of_two (aesm_fw hreg δ) le_rfl le_rfl
        (hab _ ⟨by linarith, by linarith⟩).1 (hab _ ⟨by linarith, by linarith⟩).1
    refine IntegrableOn.congr_fun (hc.const_smul s) (fun t _ => ?_) measurableSet_Ioi
    simp only [hu', Pi.mul_apply, smul_eq_mul]
    ring
  -- boundary terms
  have hzero : Tendsto (u * fw η δ) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousWithinAt (u * fw η δ) (Ici 0) 0 :=
      (Complex.continuousAt_ofReal_cpow_const 0 s (Or.inl hs0)).continuousWithinAt.mul
        (contWithinAt_fw_zero hreg δ)
    have h := (hc.mono Ioi_subset_Ici_self).tendsto
    simpa [hu, Complex.zero_cpow hsne] using h
  have hinf : Tendsto (u * fw η δ) atTop (𝓝 0) := by
    refine tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
      (f' := fun t => u' t * fw η δ t + u t * deriv (fw η δ) t) (fun t ht => ?_)
      (hu'v.add huv') huv
    exact (hud t ht).mul (hvd t ht)
  have hI := integral_Ioi_mul_deriv_eq_deriv_mul hud hvd huv' hu'v hzero hinf
  rw [sub_zero, zero_sub] at hI
  have hL : Fd η δ s = ∫ t in Ioi (0 : ℝ), u t * deriv (fw η δ) t := by
    unfold Fd mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hu, smul_eq_mul, add_sub_cancel_right]
  have hR : (∫ t in Ioi (0 : ℝ), u' t * fw η δ t) = s * HM.Gm η δ s := by
    rw [gm_eq]
    unfold mellin
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hu', smul_eq_mul]
    ring
  rw [hL, hI, hR, neg_neg]

/-! ## (5) The continuation -/

/-- **`G_cont = −dslope F 0` on `−1 < Re s < 1/2`.** -/
theorem gcont_eq_dslope {η : ℝ → ℝ} (hreg : HM.AgamonReg η) (h0 : η 0 = 0) (δ : ℝ) {s : ℂ}
    (h2 : s.re < 1 / 2) : Gcont η δ s = -dslope (Fd η δ) 0 s := by
  classical
  by_cases hs : s = 0
  · rw [hs, dslope_same, fd_deriv_zero hreg δ, neg_neg]
    unfold Gcont
    rw [if_neg (by simp), if_pos rfl]
  · rw [dslope_of_ne _ hs, slope_def_field, fd_zero hreg h0 δ, sub_zero, sub_zero]
    unfold Gcont
    by_cases hp : 0 < s.re
    · rw [if_pos hp]
      have hi := ibp hreg δ hp h2
      field_simp
      linear_combination hi
    · rw [if_neg hp, if_neg hs]
      unfold Fd
      ring

/-- **`EF.Continuation` HOLDS.** -/
theorem continuation_holds : Continuation := by
  intro η hreg h0 δ
  obtain ⟨b, hb, hGd⟩ := differentiableOn_gm hreg δ
  refine ⟨b, hb, fun s hs => ?_⟩
  have hs1 : -1 < s.re := hs.1
  have hsb : s.re < b := hs.2
  set U : Set ℂ := {z | -1 < z.re ∧ z.re < 1 / 2} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hFdd : DifferentiableOn ℂ (Fd η δ) U := fun z hz =>
    (hasDerivAt_fd hreg δ hz.1 hz.2).differentiableAt.differentiableWithinAt
  have hU0 : U ∈ 𝓝 (0 : ℂ) := hUo.mem_nhds ⟨by simp, by simp⟩
  have hH : DifferentiableOn ℂ (dslope (Fd η δ) 0) U :=
    (Complex.differentiableOn_dslope hU0).mpr hFdd
  by_cases hpos : 0 < s.re
  · have hV : IsOpen {z : ℂ | 0 < z.re ∧ z.re < b} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hev : Gcont η δ =ᶠ[𝓝 s] HM.Gm η δ := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos] with z hz
      unfold Gcont
      rw [if_pos hz]
    exact (((hGd s ⟨hpos, hsb⟩).differentiableAt (hV.mem_nhds ⟨hpos, hsb⟩)).congr_of_eventuallyEq
      hev).differentiableWithinAt
  · have hsU : s ∈ U := ⟨hs1, by linarith [not_lt.mp hpos]⟩
    have hev : Gcont η δ =ᶠ[𝓝 s] fun z => -dslope (Fd η δ) 0 z := by
      filter_upwards [hUo.mem_nhds hsU] with z hz
      exact gcont_eq_dslope hreg h0 δ hz.2
    exact (((hH s hsU).differentiableAt (hUo.mem_nhds hsU)).neg.congr_of_eventuallyEq
      hev).differentiableWithinAt

end Principia.Common.TernaryGoldbach.AG
