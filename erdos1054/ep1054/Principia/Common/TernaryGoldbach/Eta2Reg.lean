/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.ExplicitSpine

set_option autoImplicit false

/-!
# `EF.Eta2Reg` PROVED: the mollified `η₂` satisfies `lem:agamon`'s hypotheses

**`eta2Reg_holds : EF.Eta2Reg`** — for every mollifier `ν` (`EF.MollData`) and `0 < ε ≤ 1`,
`η₂ ∗_M ν_ε` (`EF.eta2e ν ε`) satisfies `HM.AgamonReg` and vanishes at `0`. No named hypothesis.

## Route

* **Symmetric form** (`eta2e_sym`, PNT+ `MellinConvolutionSymmetric`): for `x > 0`,
  `η₂ ∗_M ν_ε (x) = ∫₀^∞ ν_ε(u) η₂(x/u) du/u`. The smooth factor `ν_ε` is NOT differentiated:
  `η₂` is Lipschitz in `log t` (`HX.eta2_sub_le`), so `x ↦ η₂(x/u)` is `(8/x₀)`-Lipschitz near
  `x₀`, and it is differentiable at `x₀` unless `x₀/u` is a kink `1/4, 1/2, 1` — i.e. for all but
  the three values `u ∈ {x₀, 2x₀, 4x₀}`, a null set (`ae_off_kinks`). Mathlib's
  `hasDerivAt_integral_of_dominated_loc_of_lip` then gives (`hasDerivAt_eta2e`)
  `(η₂ ∗_M ν_ε)'(x) = Dfun ν ε x = ∫₀^∞ ν_ε(u) e2d(x/u) du/u²`, with `e2d = 4/t` on `(1/4, 1/2)`,
  `−4/t` on `(1/2, 1)`, `0` elsewhere (`hasDerivAt_eta2`, from `EN.eta2_left/right`).
* **Continuity of the derivative** (`continuousOn_D`): dominated convergence with an a.e.
  continuity hypothesis — `e2d` is continuous off the kinks (`continuousAt_e2d`) and
  `|e2d(y/u)/u| ≤ 4/y` (`abs_e2d_le`). So `C¹` on `(0, ∞)` (`contDiffOn_Ioi`) needs only the
  continuity and mass of `ν_ε`, not its smoothness.
* **Support**: `η₂ ∗_M ν_ε = 0` on `[0, 1/8)` (`eta2e_small`; `2^{−ε} ≥ 1/2` for `ε ≤ 1`) and
  beyond `2` (`EF.eta2e_zero_of_ge`), hence `C¹` on `[0, ∞)` (`contDiffOn_Ici`), and both the weight
  and its derivative are continuous on `(0, ∞)` and supported in `[1/8, 2]` (`eta2e_off`,
  `deriv_off`), which gives `L²` and every Mellin integrability (`reg_of_supp`; the link's
  interval is taken as `(−1, 2)`, but every `σ` works).

The derivative formula `hasDerivAt_eta2e` is also what `Eta2Norms.lean` uses for the norms.
-/

namespace Principia.Common.TernaryGoldbach.E2

open MeasureTheory Set Filter Topology

/-- The a.e. derivative of `η₂`: `4/t` on `(1/4, 1/2)`, `−4/t` on `(1/2, 1)`, `0` elsewhere. -/
noncomputable def e2d (t : ℝ) : ℝ :=
  (Ioo (1 / 4 : ℝ) (1 / 2)).indicator (fun t => 4 / t) t +
    (Ioo (1 / 2 : ℝ) 1).indicator (fun t => -4 / t) t

theorem measurable_e2d : Measurable e2d :=
  ((measurable_const.div measurable_id).indicator measurableSet_Ioo).add
    ((measurable_const.div measurable_id).indicator measurableSet_Ioo)

theorem e2d_lt {t : ℝ} (h : t < 1 / 4) : e2d t = 0 := by
  unfold e2d
  rw [indicator_of_notMem (fun hm => by linarith [hm.1]),
    indicator_of_notMem (fun hm => by linarith [hm.1]), add_zero]

theorem e2d_mid1 {t : ℝ} (h : t ∈ Ioo (1 / 4 : ℝ) (1 / 2)) : e2d t = 4 / t := by
  unfold e2d
  rw [indicator_of_mem h, indicator_of_notMem (fun hm => by linarith [hm.1, h.2]), add_zero]

theorem e2d_mid2 {t : ℝ} (h : t ∈ Ioo (1 / 2 : ℝ) 1) : e2d t = -4 / t := by
  unfold e2d
  rw [indicator_of_notMem (fun hm => by linarith [hm.2, h.1]), indicator_of_mem h, zero_add]

theorem e2d_gt {t : ℝ} (h : 1 < t) : e2d t = 0 := by
  unfold e2d
  rw [indicator_of_notMem (fun hm => by linarith [hm.2]),
    indicator_of_notMem (fun hm => by linarith [hm.2]), add_zero]

/-- `e2d` vanishes off `(1/4, 1)`. -/
theorem e2d_off {t : ℝ} (h : t ∉ Ioo (1 / 4 : ℝ) 1) : e2d t = 0 := by
  unfold e2d
  rw [indicator_of_notMem (fun hm => h ⟨hm.1, by linarith [hm.2]⟩),
    indicator_of_notMem (fun hm => h ⟨by linarith [hm.1], hm.2⟩), add_zero]

/-- `|e2d t| ≤ 4/t` for `t > 0`. -/
theorem abs_e2d_le {t : ℝ} (ht : 0 < t) : |e2d t| ≤ 4 / t := by
  have h4 : 0 ≤ 4 / t := by positivity
  by_cases h1 : t ∈ Ioo (1 / 4 : ℝ) (1 / 2)
  · rw [e2d_mid1 h1, abs_of_nonneg h4]
  by_cases h2 : t ∈ Ioo (1 / 2 : ℝ) 1
  · rw [e2d_mid2 h2, neg_div, abs_neg, abs_of_nonneg h4]
  · unfold e2d
    rw [indicator_of_notMem h1, indicator_of_notMem h2, add_zero, abs_zero]
    exact h4

/-- `η₂ = 0` below `1/4`. -/
theorem eta2_lt {t : ℝ} (h : t < 1 / 4) : HW.eta2 t = 0 := by
  rcases le_or_gt t 0 with h0 | h0
  · unfold HW.eta2
    rw [if_neg (not_lt.mpr h0)]
  · exact HW.eta2_of_le_quarter h0 h.le

/-- **`η₂' = e2d` off the kinks** `1/4, 1/2, 1`. -/
theorem hasDerivAt_eta2 {t : ℝ} (h1 : t ≠ 1 / 4) (h2 : t ≠ 1 / 2) (h3 : t ≠ 1) :
    HasDerivAt HW.eta2 (e2d t) t := by
  rcases lt_or_gt_of_ne h1 with ha | ha
  · rw [e2d_lt ha]
    refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ha] with s hs
    exact eta2_lt hs
  rcases lt_or_gt_of_ne h2 with hb | hb
  · have ht : 0 < t := by linarith
    rw [e2d_mid1 ⟨ha, hb⟩]
    have hd : HasDerivAt (fun s => 4 * (2 * Real.log 2 + Real.log s)) (4 * (0 + t⁻¹)) t :=
      ((hasDerivAt_const t _).add (Real.hasDerivAt_log ht.ne')).const_mul 4
    refine (hd.congr_deriv (by rw [zero_add, div_eq_mul_inv])).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ha hb] with s hs
    exact EN.eta2_left hs.1.le hs.2.le
  rcases lt_or_gt_of_ne h3 with hc | hc
  · have ht : 0 < t := by linarith
    rw [e2d_mid2 ⟨hb, hc⟩]
    have hd : HasDerivAt (fun s => -4 * Real.log s) (-4 * t⁻¹) t :=
      (Real.hasDerivAt_log ht.ne').const_mul (-4)
    refine (hd.congr_deriv (by rw [div_eq_mul_inv])).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hb hc] with s hs
    exact EN.eta2_right hs.1.le hs.2.le
  · rw [e2d_gt hc]
    refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hc] with s hs
    exact HW.eta2_of_one_le hs.le

/-- **`e2d` is continuous off the kinks.** -/
theorem continuousAt_e2d {t : ℝ} (h1 : t ≠ 1 / 4) (h2 : t ≠ 1 / 2) (h3 : t ≠ 1) :
    ContinuousAt e2d t := by
  rcases lt_or_gt_of_ne h1 with ha | ha
  · refine continuousAt_const.congr (f := fun _ => (0 : ℝ)) ?_
    filter_upwards [Iio_mem_nhds ha] with s hs
    exact (e2d_lt hs).symm
  rcases lt_or_gt_of_ne h2 with hb | hb
  · have ht : 0 < t := by linarith
    refine (continuousAt_const.div continuousAt_id ht.ne').congr (f := fun s => 4 / s) ?_
    filter_upwards [Ioo_mem_nhds ha hb] with s hs
    exact (e2d_mid1 hs).symm
  rcases lt_or_gt_of_ne h3 with hc | hc
  · have ht : 0 < t := by linarith
    refine (continuousAt_const.div continuousAt_id ht.ne').congr (f := fun s => -4 / s) ?_
    filter_upwards [Ioo_mem_nhds hb hc] with s hs
    exact (e2d_mid2 hs).symm
  · refine continuousAt_const.congr (f := fun _ => (0 : ℝ)) ?_
    filter_upwards [Ioi_mem_nhds hc] with s hs
    exact (e2d_gt hs).symm

/-- `|log y − log z| ≤ (2/x)|y − z|` for `y, z > x/2`. -/
theorem abs_log_sub_le {x y z : ℝ} (hx : 0 < x) (hy : x / 2 < y) (hz : x / 2 < z) :
    |Real.log y - Real.log z| ≤ 2 / x * |y - z| := by
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := by linarith
  have key : ∀ a b : ℝ, x / 2 < a → x / 2 < b → Real.log a - Real.log b ≤ 2 / x * |a - b| := by
    intro a b ha hb
    have ha0 : 0 < a := by linarith
    have hb0 : 0 < b := by linarith
    have h1 : Real.log a - Real.log b ≤ a / b - 1 := by
      rw [← Real.log_div ha0.ne' hb0.ne']
      exact Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    have hq : 1 ≤ 2 / x * b := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hx]
      linarith
    have h2 : a / b - 1 ≤ 2 / x * |a - b| := by
      rw [div_sub_one hb0.ne', div_le_iff₀ hb0]
      nlinarith [abs_nonneg (a - b), le_abs_self (a - b)]
    linarith
  rw [abs_le]
  constructor
  · have := key z y hz hy
    rw [abs_sub_comm] at this
    linarith
  · exact key y z hy hz

/-! ## The mollified weight and its derivative -/

variable {ν : ℝ → ℝ} {ε : ℝ}

theorem spike_cont (hν : EF.MollData ν) (hε : 0 < ε) : Continuous (DeltaSpike ν ε) :=
  DeltaSpikeContinuous hε (hν.1.of_le (by simp))

theorem spike_nonneg (hν : EF.MollData ν) (hε : 0 < ε) (u : ℝ) : 0 ≤ DeltaSpike ν ε u :=
  div_nonneg (hν.2.1 _) hε.le

/-- The symmetric form `η₂ ∗_M ν_ε (x) = ∫ ν_ε(u) η₂(x/u) du/u` (`x > 0`). -/
theorem eta2e_sym (ν : ℝ → ℝ) (ε : ℝ) {x : ℝ} (hx : 0 < x) :
    EF.eta2e ν ε x = ∫ u in Ioi (0 : ℝ), DeltaSpike ν ε u * HW.eta2 (x / u) / u := by
  unfold EF.eta2e
  rw [MellinConvolutionSymmetric _ _ hx]
  rfl

/-- **The derivative of `η₂ ∗_M ν_ε`**: `D(x) = ∫ ν_ε(u) η₂'(x/u) du/u²`. -/
noncomputable def Dfun (ν : ℝ → ℝ) (ε : ℝ) (x : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), DeltaSpike ν ε u * (e2d (x / u) / u) / u

/-- For a.e. `u > 0`, `x/u` is not a kink of `η₂` (only `u ∈ {x, 2x, 4x}` fail). -/
theorem ae_off_kinks (x : ℝ) :
    ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))),
      u ∈ Ioi (0 : ℝ) ∧ x / u ≠ 1 / 4 ∧ x / u ≠ 1 / 2 ∧ x / u ≠ 1 := by
  have hS : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), u ∉ ({x, 2 * x, 4 * x} : Set ℝ) :=
    ae_restrict_of_ae ((Set.toFinite _).countable.ae_notMem volume)
  filter_upwards [hS, ae_restrict_mem measurableSet_Ioi] with u hu hu0
  have hu0' : (0 : ℝ) < u := hu0
  refine ⟨hu0, fun h => hu ?_, fun h => hu ?_, fun h => hu ?_⟩
  · rw [div_eq_iff hu0'.ne'] at h
    have : u = 4 * x := by linarith
    simp [this]
  · rw [div_eq_iff hu0'.ne'] at h
    have : u = 2 * x := by linarith
    simp [this]
  · rw [div_eq_iff hu0'.ne'] at h
    have : u = x := by linarith
    simp [this]

/-- **`η₂ ∗_M ν_ε` is differentiable on `(0, ∞)` with derivative `Dfun`**: differentiation under
the integral in the symmetric form, `η₂(x/u)` being `(8/x₀)`-Lipschitz in `x` near `x₀`
(`HX.eta2_sub_le`) and differentiable for all but three `u`. -/
theorem hasDerivAt_eta2e (hν : EF.MollData ν) (hε : 0 < ε) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (EF.eta2e ν ε) (Dfun ν ε x) x := by
  have hgm := (spike_cont hν hε).measurable
  have hg0 := spike_nonneg hν hε
  have hint := EF.integrable_spike_div hν hε
  have hmeas : ∀ y : ℝ, Measurable (fun u : ℝ => DeltaSpike ν ε u * HW.eta2 (y / u) / u) :=
    fun y => (hgm.mul (EN.measurable_eta2.comp (measurable_const.div measurable_id))).div
      measurable_id
  have hmeas' : Measurable (fun u : ℝ => DeltaSpike ν ε u * (e2d (x / u) / u) / u) :=
    (hgm.mul ((measurable_e2d.comp (measurable_const.div measurable_id)).div measurable_id)).div
      measurable_id
  have hFint : Integrable (fun u : ℝ => DeltaSpike ν ε u * HW.eta2 (x / u) / u)
      (volume.restrict (Ioi 0)) := by
    refine (hint.mul_const (4 * Real.log 2)).mono' (hmeas x).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (mul_nonneg (hg0 u) (HW.eta2_nonneg _)) hu0.le)]
    calc DeltaSpike ν ε u * HW.eta2 (x / u) / u = DeltaSpike ν ε u / u * HW.eta2 (x / u) := by
          ring
      _ ≤ DeltaSpike ν ε u / u * (4 * Real.log 2) :=
          mul_le_mul_of_nonneg_left (GS.eta2_le _) (div_nonneg (hg0 u) hu0.le)
  have hlip : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))),
      LipschitzOnWith (Real.nnabs (DeltaSpike ν ε u / u * (8 / x)))
        (fun y => DeltaSpike ν ε u * HW.eta2 (y / u) / u) (Ioo (x / 2) (2 * x)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    have hgu : 0 ≤ DeltaSpike ν ε u / u := div_nonneg (hg0 u) hu0.le
    have hc : 0 ≤ DeltaSpike ν ε u / u * (8 / x) := mul_nonneg hgu (by positivity)
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    rw [Real.coe_nnabs, abs_of_nonneg hc, Real.dist_eq, Real.dist_eq]
    have hy0 : 0 < y := by linarith [hy.1]
    have hz0 : 0 < z := by linarith [hz.1]
    have e : DeltaSpike ν ε u * HW.eta2 (y / u) / u - DeltaSpike ν ε u * HW.eta2 (z / u) / u =
        DeltaSpike ν ε u / u * (HW.eta2 (y / u) - HW.eta2 (z / u)) := by ring
    rw [e, abs_mul, abs_of_nonneg hgu, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hgu
    have hl1 := HX.eta2_sub_le (div_pos hy0 hu0) (div_pos hz0 hu0)
    have hl2 := HX.eta2_sub_le (div_pos hz0 hu0) (div_pos hy0 hu0)
    have hlog : Real.log (y / u) - Real.log (z / u) = Real.log y - Real.log z := by
      rw [Real.log_div hy0.ne' hu0.ne', Real.log_div hz0.ne' hu0.ne']
      ring
    have hlog' : Real.log (z / u) - Real.log (y / u) = -(Real.log y - Real.log z) := by
      rw [Real.log_div hy0.ne' hu0.ne', Real.log_div hz0.ne' hu0.ne']
      ring
    rw [hlog] at hl1
    rw [hlog', abs_neg] at hl2
    have hb := abs_log_sub_le hx hy.1 hz.1
    have e8 : 4 * (2 / x * |y - z|) = 8 / x * |y - z| := by ring
    rw [abs_le]
    constructor <;> linarith
  have hdiff : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))),
      HasDerivAt (fun y => DeltaSpike ν ε u * HW.eta2 (y / u) / u)
        (DeltaSpike ν ε u * (e2d (x / u) / u) / u) x := by
    filter_upwards [ae_off_kinks x] with u ⟨_, h1, h2, h3⟩
    have hd := (hasDerivAt_eta2 h1 h2 h3).comp x ((hasDerivAt_id' x).div_const u)
    refine ((hd.const_mul (DeltaSpike ν ε u)).div_const u).congr_deriv ?_
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume.restrict (Ioi 0))
    (F := fun y u => DeltaSpike ν ε u * HW.eta2 (y / u) / u)
    (F' := fun u => DeltaSpike ν ε u * (e2d (x / u) / u) / u) (x₀ := x)
    (bound := fun u => DeltaSpike ν ε u / u * (8 / x))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun y => (hmeas y).aestronglyMeasurable) hFint
    hmeas'.aestronglyMeasurable hlip (hint.mul_const _) hdiff
  refine key.2.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact eta2e_sym ν ε hy

/-- **`Dfun` is continuous on `(0, ∞)`**: dominated convergence, `e2d` being continuous off the
kinks (an a.e. condition in `u`) and `|e2d(y/u)/u| ≤ 4/y`. -/
theorem continuousOn_D (hν : EF.MollData ν) (hε : 0 < ε) : ContinuousOn (Dfun ν ε) (Ioi 0) := by
  intro x₀ hx₀
  have hx₀' : (0 : ℝ) < x₀ := hx₀
  have hgm := (spike_cont hν hε).measurable
  have hg0 := spike_nonneg hν hε
  refine ContinuousAt.continuousWithinAt ?_
  unfold Dfun
  refine continuousAt_of_dominated (bound := fun u => DeltaSpike ν ε u / u * (8 / x₀)) ?_ ?_
    ((EF.integrable_spike_div hν hε).mul_const _) ?_
  · exact Eventually.of_forall fun y => ((hgm.mul ((measurable_e2d.comp
      (measurable_const.div measurable_id)).div measurable_id)).div
        measurable_id).aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds (half_lt_self hx₀')] with y hy
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    have hy0 : 0 < y := lt_trans (half_pos hx₀') hy
    have he := abs_e2d_le (div_pos hy0 hu0)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_div, abs_of_nonneg (hg0 u), abs_of_pos hu0]
    have h1 : |e2d (y / u)| / u ≤ 4 / y := by
      calc |e2d (y / u)| / u ≤ 4 / (y / u) / u := by gcongr
        _ = 4 / y := by field_simp
    have h2 : 4 / y ≤ 8 / x₀ := by
      rw [div_le_div_iff₀ hy0 hx₀']
      have : x₀ / 2 < y := hy
      linarith
    calc DeltaSpike ν ε u * (|e2d (y / u)| / u) / u =
          DeltaSpike ν ε u / u * (|e2d (y / u)| / u) := by ring
      _ ≤ DeltaSpike ν ε u / u * (8 / x₀) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (div_nonneg (hg0 u) hu0.le)
  · filter_upwards [ae_off_kinks x₀] with u ⟨_, h1, h2, h3⟩
    have hc : ContinuousAt (fun y => e2d (y / u)) x₀ :=
      (continuousAt_e2d h1 h2 h3).comp (f := fun y : ℝ => y / u) (continuousAt_id.div_const u)
    exact (continuousAt_const.mul (hc.div_const u)).div_const u

/-- **`η₂ ∗_M ν_ε` vanishes on `[0, 1/8)`** (`ε ≤ 1`): `η₂` lives on `[1/4, 1]` and `ν_ε` on
`[2^{−ε}, 2^ε] ⊆ [1/2, 2]`. -/
theorem eta2e_small (hν : EF.MollData ν) (hε0 : 0 < ε) (hε1 : ε ≤ 1) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x < 1 / 8) : EF.eta2e ν ε x = 0 := by
  unfold EF.eta2e MellinConvolution
  refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
  have hy' : (0 : ℝ) < y := hy
  by_cases hy1 : y ∈ Icc (1 / 4 : ℝ) 1
  · have h2 : (1 / 2 : ℝ) ≤ 2 ^ (-ε) := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (neg_le_neg hε1)
      rwa [Real.rpow_neg_one, ← one_div] at this
    have hxy : x / y < 1 / 2 := by
      rw [div_lt_iff₀ hy']
      linarith [hy1.1]
    have hn : x / y ∉ Icc ((2 : ℝ) ^ (-ε)) (2 ^ ε) := fun h => by linarith [h.1]
    rw [DeltaSpikeSupport hε0 (div_nonneg hx0 hy'.le) hν.2.2.1 hn]
    simp
  · rw [EF.eta2_zero_off hy' hy1]
    simp

/-- `η₂ ∗_M ν_ε` vanishes on `(0, ∞) \ [1/8, 2]`. -/
theorem eta2e_off (hν : EF.MollData ν) (hε0 : 0 < ε) (hε1 : ε ≤ 1) {t : ℝ} (ht : 0 < t)
    (hn : t ∉ Icc (1 / 8 : ℝ) 2) : EF.eta2e ν ε t = 0 := by
  rcases lt_or_ge t (1 / 8) with h | h
  · exact eta2e_small hν hε0 hε1 ht.le h
  · have h2 : 2 < t := lt_of_not_ge fun hc => hn ⟨h, hc⟩
    exact EF.eta2e_zero_of_ge hν hε0 hε1 h2

/-- `(η₂ ∗_M ν_ε)'` vanishes on `(0, ∞) \ [1/8, 2]`. -/
theorem deriv_off (hν : EF.MollData ν) (hε0 : 0 < ε) (hε1 : ε ≤ 1) {t : ℝ} (ht : 0 < t)
    (hn : t ∉ Icc (1 / 8 : ℝ) 2) : deriv (EF.eta2e ν ε) t = 0 := by
  rcases lt_or_ge t (1 / 8) with h | h
  · have heq : EF.eta2e ν ε =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds ht h] with s hs
      exact eta2e_small hν hε0 hε1 hs.1.le hs.2
    rw [heq.deriv_eq, deriv_const]
  · have h2 : 2 < t := lt_of_not_ge fun hc => hn ⟨h, hc⟩
    have heq : EF.eta2e ν ε =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds h2] with s hs
      exact EF.eta2e_zero_of_ge hν hε0 hε1 hs
    rw [heq.deriv_eq, deriv_const]

/-- **`η₂ ∗_M ν_ε` is `C¹` on `(0, ∞)`.** -/
theorem contDiffOn_Ioi (hν : EF.MollData ν) (hε : 0 < ε) :
    ContDiffOn ℝ 1 (EF.eta2e ν ε) (Ioi 0) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun x hx => (hasDerivAt_eta2e hν hε hx).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  exact (continuousOn_D hν hε).congr fun x hx => (hasDerivAt_eta2e hν hε hx).deriv

/-- **`η₂ ∗_M ν_ε` is `C¹` on `[0, ∞)`** (`0` near `0`). -/
theorem contDiffOn_Ici (hν : EF.MollData ν) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ContDiffOn ℝ 1 (EF.eta2e ν ε) (Ici 0) := by
  intro x hx
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ x from hx) with h | h
  · rw [← h]
    refine (contDiffWithinAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      (eta2e_small hν hε0 hε1 le_rfl (by norm_num))
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds
      (show (0 : ℝ) < 1 / 8 by norm_num))] with y hy hy'
    exact eta2e_small hν hε0 hε1 hy hy'
  · exact ((contDiffOn_Ioi hν hε0).contDiffAt (Ioi_mem_nhds h)).contDiffWithinAt

/-- A function continuous on `(0, ∞)` and `0` off `[1/8, 2]` is integrable on `(0, ∞)`. -/
theorem intOn_of_supp {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0))
    (hs : ∀ t, 0 < t → t ∉ Icc (1 / 8 : ℝ) 2 → f t = 0) : IntegrableOn f (Ioi 0) := by
  have h1 : IntegrableOn f (Icc (1 / 8) 2) := ContinuousOn.integrableOn_compact isCompact_Icc
    (hf.mono fun t ht => lt_of_lt_of_le (by norm_num) ht.1)
  exact h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun t ht => hs t ht.1 ht.2

/-- ... and is in `L²(0, ∞)` with every Mellin integrand `f t^{σ−1}` integrable. -/
theorem reg_of_supp {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0))
    (hs : ∀ t, 0 < t → t ∉ Icc (1 / 8 : ℝ) 2 → f t = 0) :
    MemLp f 2 (volume.restrict (Ioi 0)) ∧
      ∀ σ : ℝ, IntegrableOn (fun t => f t * t ^ (σ - 1)) (Ioi 0) := by
  refine ⟨(memLp_two_iff_integrable_sq (hf.aestronglyMeasurable measurableSet_Ioi)).mpr
    (intOn_of_supp (hf.pow 2) fun t ht hn => by simp [hs t ht hn]), fun σ => ?_⟩
  exact intOn_of_supp (hf.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)))
    fun t ht hn => by simp [hs t ht hn]

/-- **LINK `EF.Eta2Reg` — PROVED.** -/
theorem eta2Reg_holds : EF.Eta2Reg := by
  intro ν hν ε hε0 hε1
  have hc := contDiffOn_Ioi hν hε0
  have r1 := reg_of_supp hc.continuousOn fun t ht hn => eta2e_off hν hε0 hε1 ht hn
  have hdc : ContinuousOn (deriv (EF.eta2e ν ε)) (Ioi 0) :=
    (continuousOn_D hν hε0).congr fun x hx => (hasDerivAt_eta2e hν hε0 hx).deriv
  have r2 := reg_of_supp hdc fun t ht hn => deriv_off hν hε0 hε1 ht hn
  exact ⟨⟨contDiffOn_Ici hν hε0 hε1, r1.1, r2.1, -1, 2, by norm_num, by norm_num,
    fun σ _ => ⟨r1.2 σ, r2.2 σ⟩⟩, eta2e_small hν hε0 hε1 le_rfl (by norm_num)⟩

end Principia.Common.TernaryGoldbach.E2

