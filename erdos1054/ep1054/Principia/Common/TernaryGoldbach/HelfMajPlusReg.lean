/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajPhi
import Principia.Common.TernaryGoldbach.BandSharp

set_option autoImplicit false

/-!
# `HM.PlusReg` PROVED: `η₊` is `C¹` and satisfies the hypotheses of `lem:agamon`, `lem:hausierer`

Helfgott's `η₊(t) = h₂₀₀(t)·t·e^{−t²/2}` with `h_H = h ∗_M F_H` (`HW.etaPlus`). `prop:unease`
(majarcs 4389–4398) asserts the regularity `lem:agamon` and `lem:hausierer` need and infers it from
the App. B norms; `C¹` is never argued there. This file proves it.

## The route (no Mellin inversion, no Plancherel)

* **`h_H` is differentiable on `(0, ∞)`** (`hasDerivAt_hH`): differentiate `∫ h(t/y)F_H(y)dy/y`
  under the integral sign. `h` is `C¹` (`BL.hasDerivAt_hFun`), and for `t` in `(t₀/2, 2t₀)` the
  `t`-derivative `h'(t/y)F_H(y)/y²` vanishes for `y < t₀/4` and is `≤ 216·(200/π)/y²` beyond
  (`|h'(u)| ≤ 108u`, `abs_hD_le`).
* **`|t·h_H'(t)| ≤ 2·108·200/π`** (`abs_mul_hHd_le`): `t·h_H' = (u h'(u)) ∗_M F_H`, and any `f` with
  `|f(u)| ≤ Cu²` supported in `[0, 2]` has `|f ∗_M F_H| ≤ 2C·H/π` (`abs_mconv_le`, in the scaled
  variable `y = tv`: `∫_{1/2}^∞ v⁻³ = 2`).
* **`h_H(t) → 0` and `t·h_H'(t) → 0` as `t → 0⁺`** (`mconv_tendsto_zero`): in the scaled form
  `f ∗_M F_H (t) = ∫ f(1/v)F_H(tv)dv/v` (`mconv_scale`), `F_H(tv) = (H/π)sinc(H log tv) → 0`
  because `log tv → −∞` and `|sinc x| ≤ 1/|x|`; dominated convergence with the majorant
  `5C(H/π)/(1+v²)`. The same majorant gives continuity on `(0, ∞)` (`mconv_contOn`).
* Hence `η₊` is differentiable EVERYWHERE with derivative `dEP` (`0` on `(−∞, 0]`; at `0` the
  slope is `h_H(t)e^{−t²/2} → 0`), and `dEP` is continuous: `η₊ ∈ C¹(ℝ)` (`contDiff_etaPlus`).
* **Envelopes** (`abs_etaPlus_le`, `abs_dEP_le`): `|η₊(t)| ≤ 1.65·t·e^{−t²/2}`,
  `|η₊'(t)| ≤ (13752 + 1.65(1 + t²))e^{−t²/2}` for `t > 0` (`|h_H| ≤ e^{1/2} + 2.24·10⁻⁴` from
  `BS.band_le`). Every `Lᵖ` and Mellin-integrability conjunct of `PlusReg` follows.

**The Mellin strip used is `(0, 2)`, i.e. `AgamonReg`'s `a = 0`**, the largest value it allows.
That nothing below `0` would do — `η₊'(0⁺) = 0` only like `1/log(1/t)`, so `η₊'(t)t^{σ−1}` is
integrable at `0` only for `σ > 0` — is the round's pricing (after the `e3d6e31b` measurement of
`h_H` near `0`), NOT proved here.
-/

namespace Principia.Common.TernaryGoldbach.HP

open MeasureTheory Set Filter
open scoped Topology

/-! ## (1) Elementary bounds on `h` and `h'` -/

/-- `e^{3/2} ≤ 4.482`. -/
theorem exp_three_half_le : Real.exp (3 / 2) ≤ 4.482 := by
  have h1 := Real.exp_one_lt_d9
  have h2 := BL.exp_half_le
  have e : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by
    rw [← Real.exp_add]
    norm_num
  rw [e]
  nlinarith [Real.exp_pos 1, Real.exp_pos (1 / 2)]

/-- **`0 ≤ h ≤ e^{1/2}`** (`h(1) = e^{1/2}` is the maximum): `t²(2−t)³ ≤ 2 − t` on `[0, 2]` and
`(2−t)e^{t−1} ≤ 1` (`1 + (1−t) ≤ e^{1−t}`). -/
theorem hFun_le_half (t : ℝ) : |HW.hFun t| ≤ Real.exp (1 / 2) := by
  rw [abs_of_nonneg (BL.hFun_nonneg t)]
  unfold HW.hFun
  split_ifs with h
  · obtain ⟨h0, h2⟩ := h
    have hw : t * (2 - t) ≤ 1 := by nlinarith [sq_nonneg (t - 1)]
    have hw0 : 0 ≤ t * (2 - t) := mul_nonneg h0 (by linarith)
    have hsq : (t * (2 - t)) ^ 2 ≤ 1 := pow_le_one₀ hw0 hw
    have hl : 2 - t ≤ Real.exp (1 - t) := by linarith [Real.add_one_le_exp (1 - t)]
    have e1 : Real.exp (1 - t) * Real.exp (t - 1 / 2) = Real.exp (1 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hexp : (2 - t) * Real.exp (t - 1 / 2) ≤ Real.exp (1 / 2) := by
      rw [← e1]
      exact mul_le_mul_of_nonneg_right hl (Real.exp_pos _).le
    have hB : 0 ≤ (2 - t) * Real.exp (t - 1 / 2) := mul_nonneg (by linarith) (Real.exp_pos _).le
    have e2 : t ^ 2 * (2 - t) ^ 3 * Real.exp (t - 1 / 2) =
        (t * (2 - t)) ^ 2 * ((2 - t) * Real.exp (t - 1 / 2)) := by ring
    rw [e2]
    calc (t * (2 - t)) ^ 2 * ((2 - t) * Real.exp (t - 1 / 2)) ≤ 1 * Real.exp (1 / 2) :=
          mul_le_mul hsq hexp hB zero_le_one
      _ = Real.exp (1 / 2) := one_mul _
  · exact (Real.exp_pos _).le

/-- **`|h'(u)| ≤ 108u` for `u ≥ 0`** (`|(2−u)²(1−u)(4+u)e^{u−1/2}| ≤ 4·1·6·e^{3/2} ≤ 107.57`;
truth `9.71`). -/
theorem abs_hD_le {u : ℝ} (hu : 0 ≤ u) : |BL.hD u| ≤ 108 * u := by
  unfold BL.hD
  split_ifs with h
  · obtain ⟨h0, h2⟩ := h
    unfold BL.hDP
    have e1 : |u * (2 - u) ^ 2 * (1 - u) * (4 + u) * Real.exp (u - 1 / 2)| =
        u * ((2 - u) ^ 2 * |1 - u| * (4 + u) * Real.exp (u - 1 / 2)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ 4 + u), abs_of_pos (Real.exp_pos _)]
      ring
    rw [e1]
    have hA : (2 - u) ^ 2 ≤ 4 := by nlinarith
    have hB : |1 - u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hC : 4 + u ≤ 6 := by linarith
    have hE : Real.exp (u - 1 / 2) ≤ 4.482 :=
      (Real.exp_le_exp.mpr (by linarith)).trans exp_three_half_le
    have p1 : (2 - u) ^ 2 * |1 - u| ≤ 4 * 1 := mul_le_mul hA hB (abs_nonneg _) (by norm_num)
    have p2 : (2 - u) ^ 2 * |1 - u| * (4 + u) ≤ 4 * 1 * 6 :=
      mul_le_mul p1 hC (by linarith) (by norm_num)
    have p3 : (2 - u) ^ 2 * |1 - u| * (4 + u) * Real.exp (u - 1 / 2) ≤ 4 * 1 * 6 * 4.482 :=
      mul_le_mul p2 hE (Real.exp_pos _).le (by norm_num)
    have p4 := mul_le_mul_of_nonneg_left p3 h0
    linarith
  · rw [abs_zero]
    linarith

/-- `h'` vanishes on `[2, ∞)`. -/
theorem hD_of_two_le {u : ℝ} (hu : 2 ≤ u) : BL.hD u = 0 := by
  rcases eq_or_lt_of_le hu with h | h
  · rw [← h, BL.hD_eq (by norm_num) le_rfl]
    simp [BL.hDP]
  · exact if_neg fun hc => absurd hc.2 (not_le.mpr h)

/-- `k(u) = u·h'(u)`, so that `t·h_H'(t) = (k ∗_M F_H)(t)` (`mul_hHd`). -/
noncomputable def kD (u : ℝ) : ℝ := u * BL.hD u

theorem measurable_kD : Measurable kD :=
  measurable_id.mul BL.continuous_hD.measurable

theorem abs_kD_sq {u : ℝ} (hu : 0 < u) : |kD u| ≤ 108 * u ^ 2 := by
  unfold kD
  rw [abs_mul, abs_of_pos hu]
  have := mul_le_mul_of_nonneg_left (abs_hD_le hu.le) hu.le
  nlinarith

theorem kD_of_two_le {u : ℝ} (hu : 2 ≤ u) : kD u = 0 := by
  unfold kD
  rw [hD_of_two_le hu, mul_zero]

theorem abs_kD_lin {u : ℝ} (hu : 0 < u) : |kD u| ≤ 216 * u := by
  rcases le_or_gt 2 u with h | h
  · rw [kD_of_two_le h, abs_zero]
    linarith
  · have := abs_kD_sq hu
    nlinarith

theorem abs_hFun_lin {u : ℝ} (hu : 0 < u) : |HW.hFun u| ≤ 72 * u := by
  rcases le_or_gt 2 u with h | h
  · rw [HW.hFun_of_two_le h, abs_zero]
    linarith
  · have h1 := HW.abs_hFun_le u
    have h2 := exp_three_half_le
    have h3 : 8 * Real.exp (3 / 2) * u ^ 2 ≤ 8 * 4.482 * (2 * u) := by
      have : u ^ 2 ≤ 2 * u := by nlinarith
      have := mul_le_mul h2 this (sq_nonneg u) (by norm_num)
      nlinarith
    linarith

/-! ## (2) The scaled Mellin convolution against `F_H` -/

/-- **`(f ∗_M F_H)(t) = ∫₀^∞ f(1/v)F_H(tv) dv/v`** for `t > 0` (`y = tv`). -/
theorem mconv_scale (f : ℝ → ℝ) (H : ℝ) {t : ℝ} (ht : 0 < t) :
    HW.mconv f (HW.FH H) t = ∫ v in Ioi (0 : ℝ), f (1 / v) * HW.FH H (t * v) / v := by
  have ht' : t ≠ 0 := ht.ne'
  have hc := integral_comp_mul_left_Ioi (fun y => f (t / y) * HW.FH H y / y) 0 ht
  rw [mul_zero, smul_eq_mul] at hc
  have key : ∀ v ∈ Ioi (0 : ℝ), f (t / (t * v)) * HW.FH H (t * v) / (t * v) =
      t⁻¹ * (f (1 / v) * HW.FH H (t * v) / v) := by
    intro v hv
    have hv0 : v ≠ 0 := (mem_Ioi.mp hv).ne'
    rw [show t / (t * v) = 1 / v by field_simp]
    ring
  have h1 : ∫ v in Ioi (0 : ℝ), f (t / (t * v)) * HW.FH H (t * v) / (t * v) =
      t⁻¹ * ∫ v in Ioi (0 : ℝ), f (1 / v) * HW.FH H (t * v) / v := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi key
  rw [h1] at hc
  unfold HW.mconv
  exact (mul_left_cancel₀ (inv_ne_zero ht') hc).symm

/-- The scaled integrand is measurable. -/
theorem scaled_meas (f : ℝ → ℝ) (hfm : Measurable f) (H t : ℝ) :
    Measurable (fun v : ℝ => f (1 / v) * HW.FH H (t * v) / v) :=
  ((hfm.comp (measurable_const.div measurable_id)).mul
    ((HW.measurable_FH H).comp (measurable_const.mul measurable_id))).div measurable_id

/-- `1/v² ≤ 5/(1 + v²)` for `v ≥ 1/2`. -/
theorem inv_sq_le_five {v : ℝ} (hv : 1 / 2 < v) : 1 / v ^ 2 ≤ 5 * (1 + v ^ 2)⁻¹ := by
  have hv0 : 0 < v := by linarith
  rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (v - 1 / 2)]

/-- **The majorant of the scaled integrand**: `|f(1/v)F_H(tv)/v| ≤ 5C(H/π)/(1+v²)` when
`|f(u)| ≤ Cu` and `f = 0` on `[2, ∞)`. -/
theorem scaled_bound (f : ℝ → ℝ) {C H : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hf : ∀ u, 0 < u → |f u| ≤ C * u) (hf2 : ∀ u, 2 ≤ u → f u = 0) (t : ℝ) {v : ℝ}
    (hv : 0 < v) :
    ‖f (1 / v) * HW.FH H (t * v) / v‖ ≤ 5 * C * (H / Real.pi) * (1 + v ^ 2)⁻¹ := by
  have hK : 0 ≤ H / Real.pi := div_nonneg hH Real.pi_pos.le
  have hb0 : 0 ≤ 5 * C * (H / Real.pi) * (1 + v ^ 2)⁻¹ := by positivity
  rcases le_or_gt v (1 / 2) with h | h
  · have h2 : 2 ≤ 1 / v := by
      rw [le_div_iff₀ hv]
      linarith
    rw [hf2 _ h2, zero_mul, zero_div, norm_zero]
    exact hb0
  · have hfv := hf (1 / v) (by positivity)
    have hF := HW.abs_FH_le hH (t * v)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hv]
    have h1 : |f (1 / v)| * |HW.FH H (t * v)| ≤ C * (1 / v) * (H / Real.pi) :=
      mul_le_mul hfv hF (abs_nonneg _) (by positivity)
    have h3 : C * (1 / v) * (H / Real.pi) / v = C * (H / Real.pi) * (1 / v ^ 2) := by ring
    have h4 := mul_le_mul_of_nonneg_left (inv_sq_le_five h) (mul_nonneg hC hK)
    calc |f (1 / v)| * |HW.FH H (t * v)| / v ≤ C * (1 / v) * (H / Real.pi) / v :=
          div_le_div_of_nonneg_right h1 hv.le
      _ = C * (H / Real.pi) * (1 / v ^ 2) := h3
      _ ≤ C * (H / Real.pi) * (5 * (1 + v ^ 2)⁻¹) := h4
      _ = 5 * C * (H / Real.pi) * (1 + v ^ 2)⁻¹ := by ring

/-- The majorant is integrable. -/
theorem scaled_bound_int (C H : ℝ) :
    Integrable (fun v : ℝ => 5 * C * (H / Real.pi) * (1 + v ^ 2)⁻¹) (volume.restrict (Ioi 0)) :=
  (integrable_inv_one_add_sq.const_mul (5 * C * (H / Real.pi))).restrict

/-! ## (3) `f ∗_M F_H → 0` at `0⁺`, and continuity on `(0, ∞)` -/

/-- `|sinc x| ≤ |x|⁻¹`. -/
theorem abs_sinc_le_inv {x : ℝ} (hx : x ≠ 0) : |Real.sinc x| ≤ |x|⁻¹ := by
  rw [Real.sinc_of_ne_zero hx, abs_div, div_eq_mul_inv]
  exact mul_le_of_le_one_left (inv_nonneg.mpr (abs_nonneg x)) (Real.abs_sin_le_one x)

/-- **`F_H(tv) → 0` as `t → 0⁺`** (`v > 0`): `|F_H(y)| ≤ (H/π)/|H log y|` and `log(tv) → −∞`. -/
theorem FH_tendsto_zero {H v : ℝ} (hH : 0 < H) (hv : 0 < v) :
    Tendsto (fun t => HW.FH H (t * v)) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t * v) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_id.mul continuous_const).tendsto' 0 0 (by simp)).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht using mul_pos ht hv
  have h2 : Tendsto (fun t => H * Real.log (t * v)) (𝓝[>] 0) atBot :=
    (Real.tendsto_log_nhdsGT_zero.comp h1).const_mul_atBot hH
  have h3 : Tendsto (fun t => H / Real.pi * |H * Real.log (t * v)|⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have h4 := (tendsto_abs_atBot_atTop.comp h2).inv_tendsto_atTop
    have h5 := h4.const_mul (H / Real.pi)
    rw [mul_zero] at h5
    exact h5
  refine squeeze_zero_norm' ?_ h3
  filter_upwards [h2.eventually_lt_atBot 0] with t ht
  have hK : 0 ≤ H / Real.pi := div_nonneg hH.le Real.pi_pos.le
  rw [HW.FH, Real.norm_eq_abs, abs_mul, abs_of_nonneg hK]
  exact mul_le_mul_of_nonneg_left (abs_sinc_le_inv ht.ne) hK

/-- **`(f ∗_M F_H)(t) → 0` as `t → 0⁺`** for `|f(u)| ≤ Cu`, `f = 0` on `[2, ∞)` (dominated
convergence in the scaled variable). -/
theorem mconv_tendsto_zero (f : ℝ → ℝ) (hfm : Measurable f) {C H : ℝ} (hH : 0 < H)
    (hC : 0 ≤ C) (hf : ∀ u, 0 < u → |f u| ≤ C * u) (hf2 : ∀ u, 2 ≤ u → f u = 0) :
    Tendsto (HW.mconv f (HW.FH H)) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun t => ∫ v in Ioi (0 : ℝ), f (1 / v) * HW.FH H (t * v) / v) (𝓝[>] 0)
      (𝓝 (∫ v in Ioi (0 : ℝ), (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence _
      (Eventually.of_forall fun t => (scaled_meas f hfm H t).aestronglyMeasurable)
      (Eventually.of_forall fun t => (ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun v hv => scaled_bound f hH.le hC hf hf2 t hv))
      (scaled_bound_int C H) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
    have h1 := ((FH_tendsto_zero hH hv).const_mul (f (1 / v))).div_const v
    have e : f (1 / v) * 0 / v = 0 := by ring
    rw [e] at h1
    exact h1
  rw [integral_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (mconv_scale f H ht).symm

/-- **`f ∗_M F_H` is continuous on `(0, ∞)`** (same majorant). -/
theorem mconv_contOn (f : ℝ → ℝ) (hfm : Measurable f) {C H : ℝ} (hH : 0 < H) (hC : 0 ≤ C)
    (hf : ∀ u, 0 < u → |f u| ≤ C * u) (hf2 : ∀ u, 2 ≤ u → f u = 0) :
    ContinuousOn (HW.mconv f (HW.FH H)) (Ioi 0) := by
  have hc : ContinuousOn (fun t => ∫ v in Ioi (0 : ℝ), f (1 / v) * HW.FH H (t * v) / v)
      (Ioi 0) := by
    refine continuousOn_of_dominated
      (fun t _ => (scaled_meas f hfm H t).aestronglyMeasurable)
      (fun t _ => (ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun v hv => scaled_bound f hH.le hC hf hf2 t hv))
      (scaled_bound_int C H) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
    have hv0 : (0 : ℝ) < v := hv
    have h1 : ContinuousOn (fun t : ℝ => HW.FH H (t * v)) (Ioi 0) :=
      (HW.FH_contOn H).comp (continuousOn_id.mul continuousOn_const)
        (fun t ht => mul_pos (mem_Ioi.mp ht) hv0)
    exact (continuousOn_const.mul h1).div_const v
  exact hc.congr fun t ht => mconv_scale f H ht

/-- **`|(f ∗_M F_H)(t)| ≤ 2C·H/π`** for `|f(u)| ≤ Cu²`, `f = 0` on `[2, ∞)`, `t > 0`
(`∫_{1/2}^∞ C(H/π)v⁻³ dv = 2C(H/π)`). -/
theorem abs_mconv_le (f : ℝ → ℝ) {C H : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hf : ∀ u, 0 < u → |f u| ≤ C * u ^ 2) (hf2 : ∀ u, 2 ≤ u → f u = 0) {t : ℝ} (ht : 0 < t) :
    |HW.mconv f (HW.FH H) t| ≤ 2 * C * (H / Real.pi) := by
  have hK : 0 ≤ H / Real.pi := div_nonneg hH Real.pi_pos.le
  rw [mconv_scale f H ht]
  have hsub : ∫ v in Ioi (0 : ℝ), f (1 / v) * HW.FH H (t * v) / v =
      ∫ v in Ioi (1 / 2 : ℝ), f (1 / v) * HW.FH H (t * v) / v := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi (by norm_num)) fun v hv => ?_
    obtain ⟨hv0, hv1⟩ := hv
    have hv0' : 0 < v := hv0
    have hle : v ≤ 1 / 2 := not_lt.mp hv1
    have h2 : 2 ≤ 1 / v := by
      rw [le_div_iff₀ hv0']
      linarith
    rw [hf2 _ h2, zero_mul, zero_div]
  have hint : IntegrableOn (fun v : ℝ => C * (H / Real.pi) * v ^ (-3 : ℝ)) (Ioi (1 / 2)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul _
  have hpt : ∀ v ∈ Ioi (1 / 2 : ℝ),
      ‖f (1 / v) * HW.FH H (t * v) / v‖ ≤ C * (H / Real.pi) * v ^ (-3 : ℝ) := by
    intro v hv
    have hv0 : 0 < v := lt_trans (by norm_num) hv
    have hfv := hf (1 / v) (by positivity)
    have hF := HW.abs_FH_le hH (t * v)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hv0,
      show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hv0.le, Real.rpow_natCast]
    have h1 : |f (1 / v)| * |HW.FH H (t * v)| ≤ C * (1 / v) ^ 2 * (H / Real.pi) :=
      mul_le_mul hfv hF (abs_nonneg _) (by positivity)
    calc |f (1 / v)| * |HW.FH H (t * v)| / v ≤ C * (1 / v) ^ 2 * (H / Real.pi) / v :=
          div_le_div_of_nonneg_right h1 hv0.le
      _ = C * (H / Real.pi) * (v ^ 3)⁻¹ := by ring
  have hb := norm_integral_le_of_norm_le hint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hpt))
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)] at hb
  have hv : -(1 / 2 : ℝ) ^ ((-3 : ℝ) + 1) / ((-3 : ℝ) + 1) = 2 := by
    rw [show (-3 : ℝ) + 1 = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_natCast]
    norm_num
  rw [hv, Real.norm_eq_abs] at hb
  rw [hsub]
  linarith

/-! ## (4) `h_H` is differentiable on `(0, ∞)` -/

/-- **`h_H'(t) = ∫ h'(t/y)F_H(y)/y² dy`** for `t > 0` (`hasDerivAt_hH`). -/
noncomputable def hHd (t : ℝ) : ℝ := ∫ y in Ioi (0 : ℝ), BL.hD (t / y) / y * HW.FH 200 y / y

/-- `1/y² ≤ (2/a²)(1 + (y/a)²)⁻¹` for `y ≥ a > 0`. -/
theorem inv_sq_le_shift {a y : ℝ} (ha : 0 < a) (hy : a ≤ y) :
    1 / y ^ 2 ≤ 2 / a ^ 2 * (1 + (y / a) ^ 2)⁻¹ := by
  have hy0 : 0 < y := lt_of_lt_of_le ha hy
  have e : 2 / a ^ 2 * (1 + (y / a) ^ 2)⁻¹ = 2 / (a ^ 2 + y ^ 2) := by
    field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **`h_H` is differentiable on `(0, ∞)` with derivative `hHd`**: differentiation under the
integral sign, with `|h'(t/y)F_H(y)/y²| ≤ 216(200/π)/y²` on `y ≥ t₀/4` and `0` below. -/
theorem hasDerivAt_hH {t : ℝ} (ht : 0 < t) : HasDerivAt (HW.hH 200) (hHd t) t := by
  set a := t / 4 with ha
  have ha0 : 0 < a := by positivity
  have hK : 0 ≤ (200 : ℝ) / Real.pi := div_nonneg (by norm_num) Real.pi_pos.le
  have hbi : Integrable (fun y : ℝ => 216 * (200 / Real.pi) * (2 / a ^ 2 * (1 + (y / a) ^ 2)⁻¹))
      (volume.restrict (Ioi 0)) :=
    (((integrable_inv_one_add_sq.comp_div ha0.ne').const_mul (2 / a ^ 2)).const_mul
      (216 * (200 / Real.pi))).restrict
  have hmeas : ∀ x : ℝ, Measurable (fun y : ℝ => HW.hFun (x / y) * HW.FH 200 y / y) := fun x =>
    ((HW.measurable_hFun.comp (measurable_const.div measurable_id)).mul
      (HW.measurable_FH 200)).div measurable_id
  have hmeas' : Measurable (fun y : ℝ => BL.hD (t / y) / y * HW.FH 200 y / y) :=
    (((BL.continuous_hD.measurable.comp (measurable_const.div measurable_id)).div
      measurable_id).mul (HW.measurable_FH 200)).div measurable_id
  have hbound : ∀ y ∈ Ioi (0 : ℝ), ∀ x ∈ Ioo (t / 2) (2 * t),
      ‖BL.hD (x / y) / y * HW.FH 200 y / y‖ ≤
        216 * (200 / Real.pi) * (2 / a ^ 2 * (1 + (y / a) ^ 2)⁻¹) := by
    intro y hy x hx
    have hy0 : 0 < y := hy
    have hx0 : 0 < x := lt_trans (by positivity) hx.1
    have hb0 : 0 ≤ 216 * (200 / Real.pi) * (2 / a ^ 2 * (1 + (y / a) ^ 2)⁻¹) := by positivity
    rcases lt_or_ge y (x / 2) with h | h
    · have h2 : 2 ≤ x / y := by
        rw [le_div_iff₀ hy0]
        linarith
      rw [hD_of_two_le h2, zero_div, zero_mul, zero_div, norm_zero]
      exact hb0
    · have hxy : x / y ≤ 2 := by
        rw [div_le_iff₀ hy0]
        linarith
      have hD1 : |BL.hD (x / y)| ≤ 216 := by
        have := abs_hD_le (div_pos hx0 hy0).le
        linarith
      have hF := HW.abs_FH_le (by norm_num : (0 : ℝ) ≤ 200) y
      have hay : a ≤ y := by
        rw [ha]
        linarith [hx.1]
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_div, abs_of_pos hy0]
      have h1 : |BL.hD (x / y)| / y * |HW.FH 200 y| / y = |BL.hD (x / y)| * |HW.FH 200 y| *
          (1 / y ^ 2) := by
        field_simp
      have h3 : |BL.hD (x / y)| * |HW.FH 200 y| ≤ 216 * (200 / Real.pi) :=
        mul_le_mul hD1 hF (abs_nonneg _) (by norm_num)
      rw [h1]
      exact mul_le_mul h3 (inv_sq_le_shift ha0 hay) (by positivity) (by positivity)
  have hdiff : ∀ y ∈ Ioi (0 : ℝ), ∀ x ∈ Ioo (t / 2) (2 * t),
      HasDerivAt (fun x => HW.hFun (x / y) * HW.FH 200 y / y)
        (BL.hD (x / y) / y * HW.FH 200 y / y) x := by
    intro y hy x _
    have h1 := (BL.hasDerivAt_hFun (x / y)).comp x ((hasDerivAt_id' x).div_const y)
    have h2 := (h1.mul_const (HW.FH 200 y)).div_const y
    refine h2.congr_deriv ?_
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun x y => HW.hFun (x / y) * HW.FH 200 y / y)
    (F' := fun x y => BL.hD (x / y) / y * HW.FH 200 y / y) (x₀ := t)
    (bound := fun y => 216 * (200 / Real.pi) * (2 / a ^ 2 * (1 + (y / a) ^ 2)⁻¹))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun x => (hmeas x).aestronglyMeasurable)
    (HW.hH_integrable (by norm_num) ht) hmeas'.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hbound)) hbi
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hdiff))
  exact key.2

/-- **`t·h_H'(t) = (k ∗_M F_H)(t)`**, `k(u) = u h'(u)`. -/
theorem mul_hHd (t : ℝ) : t * hHd t = HW.mconv kD (HW.FH 200) t := by
  unfold hHd HW.mconv kD
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  ring

/-- **`|t·h_H'(t)| ≤ 2·108·200/π ≤ 13752`** for every `t > 0` (truth: `|t h_H'| ≤ 4.25`). -/
theorem abs_mul_hHd_le {t : ℝ} (ht : 0 < t) : |t * hHd t| ≤ 13752 := by
  rw [mul_hHd t]
  have h := abs_mconv_le kD (by norm_num : (0 : ℝ) ≤ 200) (by norm_num : (0 : ℝ) ≤ 108)
    (fun u hu => abs_kD_sq hu) (fun u hu => kD_of_two_le hu) ht
  have hpi : 2 * 108 * (200 / Real.pi) ≤ 13752 := by
    rw [mul_div_assoc', div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_d6]
  linarith

/-! ## (5) `η₊ ∈ C¹(ℝ)` -/

/-- `|h_H(t)| ≤ 1.65` for `t > 0` (`|h| ≤ e^{1/2}` and `BS.band_le`). -/
theorem abs_hH_le {t : ℝ} (ht : 0 < t) : |HW.hH 200 t| ≤ 1.65 := by
  have h1 := BS.band_le t ht
  have h2 := hFun_le_half t
  have h3 := BL.exp_half_le
  have h4 := abs_sub_abs_le_abs_sub (HW.hH 200 t) (HW.hFun t)
  linarith

/-- **`h_H(t) → 0` as `t → 0⁺`.** -/
theorem hH_tendsto_zero : Tendsto (HW.hH 200) (𝓝[>] 0) (𝓝 0) :=
  mconv_tendsto_zero HW.hFun HW.measurable_hFun (by norm_num) (by norm_num : (0 : ℝ) ≤ 72)
    (fun _ hu => abs_hFun_lin hu) (fun _ hu => HW.hFun_of_two_le hu)

/-- **`t·h_H'(t) → 0` as `t → 0⁺`.** -/
theorem mul_hHd_tendsto_zero : Tendsto (fun t => t * hHd t) (𝓝[>] 0) (𝓝 0) :=
  (mconv_tendsto_zero kD measurable_kD (by norm_num) (by norm_num : (0 : ℝ) ≤ 216)
    (fun _ hu => abs_kD_lin hu) (fun _ hu => kD_of_two_le hu)).congr fun t => (mul_hHd t).symm

/-- **`η₊'`, everywhere**: `(t h_H'(t) + h_H(t)(1 − t²))e^{−t²/2}` for `t > 0`, and `0` for
`t ≤ 0`. -/
noncomputable def dEP (t : ℝ) : ℝ :=
  if 0 < t then (t * hHd t + HW.hH 200 t * (1 - t ^ 2)) * Real.exp (-t ^ 2 / 2) else 0

theorem dEP_pos {t : ℝ} (ht : 0 < t) :
    dEP t = (t * hHd t + HW.hH 200 t * (1 - t ^ 2)) * Real.exp (-t ^ 2 / 2) := if_pos ht

theorem dEP_nonpos {t : ℝ} (ht : t ≤ 0) : dEP t = 0 := if_neg (not_lt.mpr ht)

theorem hasDerivAt_etaPlus_pos {t : ℝ} (ht : 0 < t) : HasDerivAt HW.etaPlus (dEP t) t := by
  have he := ((EN.hasDerivAt_sq' t).neg.div_const 2).exp
  have h := ((hasDerivAt_hH ht).mul (hasDerivAt_id' t)).mul he
  rw [dEP_pos ht]
  refine h.congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.neg_apply]
  ring

/-- At `0` the slope is `h_H(t)e^{−t²/2} → 0`. -/
theorem hasDerivAt_etaPlus_zero : HasDerivAt HW.etaPlus 0 0 := by
  have hl : HasDerivWithinAt HW.etaPlus 0 (Iic 0) 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr_of_mem
      (fun y hy => HW.etaPlus_of_nonpos hy) self_mem_Iic
  have hr : HasDerivWithinAt HW.etaPlus 0 (Ioi 0) 0 := by
    rw [hasDerivWithinAt_iff_tendsto_slope' (s := Ioi (0 : ℝ)) (lt_irrefl (0 : ℝ))]
    have hc : Tendsto (fun t : ℝ => Real.exp (-t ^ 2 / 2)) (𝓝[>] 0) (𝓝 1) :=
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-t ^ 2 / 2)).tendsto' 0 1
        (by norm_num)).mono_left nhdsWithin_le_nhds
    have h1 := hH_tendsto_zero.mul hc
    rw [zero_mul] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := (mem_Ioi.mp ht).ne'
    rw [slope_def_field, HW.etaPlus_of_nonpos le_rfl, sub_zero, sub_zero, HW.etaPlus]
    field_simp
  have h := hl.union hr
  rwa [Iic_union_Ioi, hasDerivWithinAt_univ] at h

/-- **`η₊` is differentiable everywhere, with derivative `dEP`.** -/
theorem hasDerivAt_etaPlus (t : ℝ) : HasDerivAt HW.etaPlus (dEP t) t := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [dEP_nonpos h.le]
    refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with y hy
    exact HW.etaPlus_of_nonpos (le_of_lt hy)
  · rw [dEP_nonpos le_rfl]
    exact hasDerivAt_etaPlus_zero
  · exact hasDerivAt_etaPlus_pos h

theorem deriv_etaPlus : deriv HW.etaPlus = dEP := funext fun t => (hasDerivAt_etaPlus t).deriv

/-- **`η₊'` is continuous** (on `(0,∞)` from `mconv_contOn`; at `0` from both `→ 0` limits). -/
theorem continuous_dEP : Continuous dEP := by
  have hA : ContinuousOn (fun t => t * hHd t) (Ioi 0) :=
    (mconv_contOn kD measurable_kD (by norm_num : (0 : ℝ) < 200) (by norm_num : (0 : ℝ) ≤ 216)
      (fun _ hu => abs_kD_lin hu) (fun _ hu => kD_of_two_le hu)).congr fun t _ => mul_hHd t
  have hB : ContinuousOn (HW.hH 200) (Ioi 0) :=
    mconv_contOn HW.hFun HW.measurable_hFun (by norm_num : (0 : ℝ) < 200)
      (by norm_num : (0 : ℝ) ≤ 72) (fun _ hu => abs_hFun_lin hu) (fun _ hu => HW.hFun_of_two_le hu)
  have hpos : ContinuousOn dEP (Ioi 0) := by
    have h : ContinuousOn (fun t => (t * hHd t + HW.hH 200 t * (1 - t ^ 2)) *
        Real.exp (-t ^ 2 / 2)) (Ioi 0) :=
      (hA.add (hB.mul (by fun_prop : Continuous fun t : ℝ => 1 - t ^ 2).continuousOn)).mul
        (by fun_prop : Continuous fun t : ℝ => Real.exp (-t ^ 2 / 2)).continuousOn
    exact h.congr fun t ht => dEP_pos ht
  have h0 : Tendsto dEP (𝓝[>] 0) (𝓝 0) := by
    have hc1 : Tendsto (fun t : ℝ => 1 - t ^ 2) (𝓝[>] 0) (𝓝 1) :=
      ((by fun_prop : Continuous fun t : ℝ => 1 - t ^ 2).tendsto' 0 1 (by norm_num)).mono_left
        nhdsWithin_le_nhds
    have hc2 : Tendsto (fun t : ℝ => Real.exp (-t ^ 2 / 2)) (𝓝[>] 0) (𝓝 1) :=
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-t ^ 2 / 2)).tendsto' 0 1
        (by norm_num)).mono_left nhdsWithin_le_nhds
    have h := (mul_hHd_tendsto_zero.add (hH_tendsto_zero.mul hc1)).mul hc2
    rw [show ((0 : ℝ) + 0 * 1) * 1 = 0 by norm_num] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (dEP_pos ht).symm
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_trichotomy t 0 with h | rfl | h
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Iio_mem_nhds h] with y hy
    exact (dEP_nonpos (le_of_lt hy)).symm
  · have hl : Tendsto dEP (𝓝[≤] 0) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (dEP_nonpos hy).symm
    have h2 := hl.sup h0
    rw [nhdsLE_sup_nhdsGT] at h2
    rw [ContinuousAt, dEP_nonpos le_rfl]
    exact h2
  · exact hpos.continuousAt (Ioi_mem_nhds h)

/-- **`η₊ ∈ C¹(ℝ)`.** -/
theorem contDiff_etaPlus : ContDiff ℝ 1 HW.etaPlus :=
  contDiff_one_iff_deriv.mpr ⟨fun t => (hasDerivAt_etaPlus t).differentiableAt,
    by rw [deriv_etaPlus]; exact continuous_dEP⟩

/-! ## (6) Envelopes -/

/-- **`|η₊(t)| ≤ 1.65·t·e^{−t²/2}`** for `t > 0`. -/
theorem abs_etaPlus_le {t : ℝ} (ht : 0 < t) :
    |HW.etaPlus t| ≤ 1.65 * (t * Real.exp (-t ^ 2 / 2)) := by
  have hw : 0 ≤ t * Real.exp (-t ^ 2 / 2) := mul_nonneg ht.le (Real.exp_pos _).le
  rw [HW.etaPlus, mul_assoc, abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_right (abs_hH_le ht) hw

/-- **`|η₊'(t)| ≤ (13752 + 1.65(1 + t²))e^{−t²/2}`** for `t > 0`. -/
theorem abs_dEP_le {t : ℝ} (ht : 0 < t) :
    |dEP t| ≤ (13752 + 1.65 * (1 + t ^ 2)) * Real.exp (-t ^ 2 / 2) := by
  rw [dEP_pos ht, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have h1 := abs_mul_hHd_le ht
  have h2 := abs_hH_le ht
  have h3 : |1 - t ^ 2| ≤ 1 + t ^ 2 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  calc |t * hHd t + HW.hH 200 t * (1 - t ^ 2)|
      ≤ |t * hHd t| + |HW.hH 200 t| * |1 - t ^ 2| := by
        rw [← abs_mul]
        exact abs_add_le _ _
    _ ≤ 13752 + 1.65 * (1 + t ^ 2) :=
        add_le_add h1 (mul_le_mul h2 h3 (abs_nonneg _) (by norm_num))

/-! ## (7) Regularity from envelopes (generic), and `PlusReg` -/

/-- An `AEStronglyMeasurable` function dominated on `(0,∞)` by an integrable one is integrable. -/
theorem int_of_le {f g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0))
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hle : ∀ t, 0 < t → ‖f t‖ ≤ g t) :
    IntegrableOn f (Ioi 0) :=
  Integrable.mono' hg hf ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun t ht => hle t ht))

/-- `t^k e^{−t²/2}`, `t^k e^{−t²}` are integrable on `(0, ∞)`. -/
theorem ie2 (k : ℕ) : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-t ^ 2 / 2)) (Ioi 0) :=
  (HM.gm2 k).1

theorem ie1 (k : ℕ) : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-t ^ 2)) (Ioi 0) :=
  (HM.gm1 k).1

/-- `t·t^{σ−1} = t^σ`. -/
theorem rpow_shift {t : ℝ} (ht : 0 < t) (n : ℕ) (σ : ℝ) :
    t ^ n * t ^ (σ - 1) = t ^ (σ - 1 + n) := by
  rw [Real.rpow_add ht, Real.rpow_natCast, mul_comm]

/-- `|a| ≤ B(t + t³)E` gives `|a/√t| ≤ B(t^{1/2}E + t^{5/2}E)`. -/
theorem div_sqrt_env {t a B E : ℝ} (ht : 0 < t)
    (ha : |a| ≤ B * ((t + t ^ 3) * E)) :
    ‖a / Real.sqrt t‖ ≤ B * (t ^ (1 / 2 : ℝ) * E + t ^ (5 / 2 : ℝ) * E) := by
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have r1 : t ^ (1 / 2 : ℝ) = Real.sqrt t := (Real.sqrt_eq_rpow t).symm
  have r2 : t ^ (5 / 2 : ℝ) = t ^ 2 * Real.sqrt t := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add ht, r1]
    norm_cast
  rw [r1, r2, Real.norm_eq_abs, abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
  have e : B * (Real.sqrt t * E + t ^ 2 * Real.sqrt t * E) * Real.sqrt t =
      B * ((Real.sqrt t ^ 2 + t ^ 2 * Real.sqrt t ^ 2) * E) := by ring
  rw [e, hs]
  have e2 : B * ((t + t ^ 3) * E) = B * ((t + t ^ 2 * t) * E) := by ring
  linarith

/-- `|a| ≤ B(t + t³)E` gives `|a·t^{σ−1}| ≤ B(t^σ E + t^{σ+2} E)`. -/
theorem mellin_env3 {t a B E σ : ℝ} (ht : 0 < t)
    (ha : |a| ≤ B * ((t + t ^ 3) * E)) :
    ‖a * t ^ (σ - 1)‖ ≤ B * (t ^ (σ - 1 + (1 : ℕ)) * E + t ^ (σ - 1 + (3 : ℕ)) * E) := by
  have hp : 0 < t ^ (σ - 1) := Real.rpow_pos_of_pos ht _
  rw [← rpow_shift ht, ← rpow_shift ht, Real.norm_eq_abs, abs_mul, abs_of_pos hp]
  have := mul_le_mul_of_nonneg_right ha hp.le
  have e : B * (t ^ 1 * t ^ (σ - 1) * E + t ^ 3 * t ^ (σ - 1) * E) =
      B * ((t + t ^ 3) * E) * t ^ (σ - 1) := by ring
  linarith

/-- `|a| ≤ D(1 + t⁶)E` gives `|a·t^{σ−1}| ≤ D(t^{σ−1}E + t^{σ+5} E)`. -/
theorem mellin_env6 {t a D E σ : ℝ} (ht : 0 < t)
    (ha : |a| ≤ D * ((1 + t ^ 6) * E)) :
    ‖a * t ^ (σ - 1)‖ ≤ D * (t ^ (σ - 1 + (0 : ℕ)) * E + t ^ (σ - 1 + (6 : ℕ)) * E) := by
  have hp : 0 < t ^ (σ - 1) := Real.rpow_pos_of_pos ht _
  rw [← rpow_shift ht, ← rpow_shift ht, Real.norm_eq_abs, abs_mul, abs_of_pos hp]
  have := mul_le_mul_of_nonneg_right ha hp.le
  have e : D * (t ^ 0 * t ^ (σ - 1) * E + t ^ 6 * t ^ (σ - 1) * E) =
      D * ((1 + t ^ 6) * E) * t ^ (σ - 1) := by ring
  linarith

/-- **`HausiererReg` from the envelope `|η(t)| ≤ B(t + t³)e^{−t²/2}`.** -/
theorem hausReg_of_env (η : ℝ → ℝ) (hm : Measurable η) {B : ℝ}
    (he : ∀ t, 0 < t → |η t| ≤ B * ((t + t ^ 3) * Real.exp (-t ^ 2 / 2))) :
    HM.HausiererReg η := by
  have hm' : AEStronglyMeasurable η (volume.restrict (Ioi 0)) := hm.aestronglyMeasurable
  have hlm : Measurable (HM.llog η) := Real.measurable_log.mul hm
  -- `|η|`
  have i1 : IntegrableOn η (Ioi 0) := by
    refine int_of_le (((ie2 1).add (ie2 3)).const_mul B) hm' fun t ht => ?_
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs]
    have h := he t ht
    linarith [show B * ((t + t ^ 3) * Real.exp (-t ^ 2 / 2)) =
      B * (t ^ 1 * Real.exp (-t ^ 2 / 2) + t ^ 3 * Real.exp (-t ^ 2 / 2)) by ring]
  -- `η²`
  have i2 : IntegrableOn (fun t => η t ^ 2) (Ioi 0) := by
    refine int_of_le ((((ie1 2).add ((ie1 4).const_mul 2)).add (ie1 6)).const_mul (B ^ 2))
      (hm.pow_const 2).aestronglyMeasurable fun t ht => ?_
    simp only [Pi.add_apply]
    have h := he t ht
    have h0 : 0 ≤ B * ((t + t ^ 3) * Real.exp (-t ^ 2 / 2)) := le_trans (abs_nonneg _) h
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    have e : (B * ((t + t ^ 3) * Real.exp (-t ^ 2 / 2))) ^ 2 =
        B ^ 2 * (t ^ 2 * Real.exp (-t ^ 2) + 2 * (t ^ 4 * Real.exp (-t ^ 2)) +
          t ^ 6 * Real.exp (-t ^ 2)) := by
      rw [mul_pow, mul_pow, HM.exp_half_sq]
      ring
    linarith
  -- `|log t|·|η|`
  have i3 : IntegrableOn (HM.llog η) (Ioi 0) := by
    refine int_of_le ((((ie2 0).add ((ie2 2).const_mul 2)).add (ie2 4)).const_mul B)
      hlm.aestronglyMeasurable fun t ht => ?_
    simp only [Pi.add_apply]
    have h := he t ht
    have hl := HM.abs_log_le ht
    have hE : 0 ≤ (t + t ^ 3) * Real.exp (-t ^ 2 / 2) := by positivity
    unfold HM.llog
    rw [Real.norm_eq_abs, abs_mul]
    have p := mul_le_mul hl h (abs_nonneg _) (by positivity)
    have e : (t + 1 / t) * (B * ((t + t ^ 3) * Real.exp (-t ^ 2 / 2))) =
        B * (t ^ 0 * Real.exp (-t ^ 2 / 2) + 2 * (t ^ 2 * Real.exp (-t ^ 2 / 2)) +
          t ^ 4 * Real.exp (-t ^ 2 / 2)) := by
      field_simp
      ring
    linarith
  -- `log²t·η²`
  have i4 : IntegrableOn (fun t => HM.llog η t ^ 2) (Ioi 0) := by
    refine int_of_le (((((ie1 1).add ((ie1 3).const_mul 3)).add ((ie1 5).const_mul 3)).add
      (ie1 7)).const_mul (B ^ 2)) (hlm.pow_const 2).aestronglyMeasurable fun t ht => ?_
    simp only [Pi.add_apply]
    have h := he t ht
    have hl : Real.log t ^ 2 ≤ t + 1 / t := by
      have := HM.log_sq_le ht
      linarith
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at h2
    unfold HM.llog
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
    have p := mul_le_mul hl h2 (sq_nonneg _) (by positivity)
    have e : (t + 1 / t) * (B * ((t + t ^ 3) * Real.exp (-t ^ 2 / 2))) ^ 2 =
        B ^ 2 * (t ^ 1 * Real.exp (-t ^ 2) + 3 * (t ^ 3 * Real.exp (-t ^ 2)) +
          3 * (t ^ 5 * Real.exp (-t ^ 2)) + t ^ 7 * Real.exp (-t ^ 2)) := by
      rw [mul_pow, mul_pow, HM.exp_half_sq]
      field_simp
      ring
    linarith
  -- `η/√t`
  have i5 : IntegrableOn (fun t => η t / Real.sqrt t) (Ioi 0) :=
    int_of_le (((HM.rint2 (s := 1 / 2) (by norm_num)).add
      (HM.rint2 (s := 5 / 2) (by norm_num))).const_mul B)
      (hm.div Real.continuous_sqrt.measurable).aestronglyMeasurable fun t ht =>
        div_sqrt_env ht (he t ht)
  -- the Mellin strip `(0, 1)`
  have i6 : ∀ σ ∈ Ioo (0 : ℝ) 1, IntegrableOn (fun t => η t * t ^ (σ - 1)) (Ioi 0) := by
    intro σ hσ
    exact int_of_le (((HM.rint2 (s := σ - 1 + (1 : ℕ)) (by push_cast; linarith [hσ.1])).add
      (HM.rint2 (s := σ - 1 + (3 : ℕ)) (by push_cast; linarith [hσ.1]))).const_mul B)
      (hm.mul (measurable_id.pow_const _)).aestronglyMeasurable fun t ht =>
        mellin_env3 ht (he t ht)
  have hL2 : MemLp η 2 (volume.restrict (Ioi 0)) := (memLp_two_iff_integrable_sq hm').mpr i2
  exact ⟨memLp_one_iff_integrable.mpr i1, hL2, memLp_one_iff_integrable.mpr i3,
    (memLp_two_iff_integrable_sq hlm.aestronglyMeasurable).mpr i4, i5, 0, 1, by norm_num,
    by norm_num, i6⟩

/-- **`AgamonReg` from `C¹` and the envelopes `|η| ≤ B(t + t³)e^{−t²/2}`,
`|η'| ≤ D(1 + t⁶)e^{−t²/2}`**, with the Mellin strip `(0, 2)` (`a = 0`). -/
theorem agamonReg_of_env (η : ℝ → ℝ) (hc : ContDiff ℝ 1 η) {B D : ℝ}
    (he : ∀ t, 0 < t → |η t| ≤ B * ((t + t ^ 3) * Real.exp (-t ^ 2 / 2)))
    (hd : ∀ t, 0 < t → |deriv η t| ≤ D * ((1 + t ^ 6) * Real.exp (-t ^ 2 / 2))) :
    HM.AgamonReg η := by
  have hm : Measurable η := hc.continuous.measurable
  have hdm : Measurable (deriv η) := measurable_deriv η
  have hH := hausReg_of_env η hm he
  have i2 : IntegrableOn (fun t => deriv η t ^ 2) (Ioi 0) := by
    refine int_of_le ((((ie1 0).add ((ie1 6).const_mul 2)).add (ie1 12)).const_mul (D ^ 2))
      (hdm.pow_const 2).aestronglyMeasurable fun t ht => ?_
    simp only [Pi.add_apply]
    have h := hd t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    have e : (D * ((1 + t ^ 6) * Real.exp (-t ^ 2 / 2))) ^ 2 =
        D ^ 2 * (t ^ 0 * Real.exp (-t ^ 2) + 2 * (t ^ 6 * Real.exp (-t ^ 2)) +
          t ^ 12 * Real.exp (-t ^ 2)) := by
      rw [mul_pow, mul_pow, HM.exp_half_sq]
      ring
    linarith
  refine ⟨hc.contDiffOn, hH.2.1, (memLp_two_iff_integrable_sq hdm.aestronglyMeasurable).mpr i2,
    0, 2, le_rfl, by norm_num, fun σ hσ => ⟨?_, ?_⟩⟩
  · exact int_of_le (((HM.rint2 (s := σ - 1 + (1 : ℕ)) (by push_cast; linarith [hσ.1])).add
      (HM.rint2 (s := σ - 1 + (3 : ℕ)) (by push_cast; linarith [hσ.1]))).const_mul B)
      (hm.mul (measurable_id.pow_const _)).aestronglyMeasurable fun t ht =>
        mellin_env3 ht (he t ht)
  · exact int_of_le (((HM.rint2 (s := σ - 1 + (0 : ℕ)) (by push_cast; linarith [hσ.1])).add
      (HM.rint2 (s := σ - 1 + (6 : ℕ)) (by push_cast; linarith [hσ.1]))).const_mul D)
      (hdm.mul (measurable_id.pow_const _)).aestronglyMeasurable fun t ht =>
        mellin_env6 ht (hd t ht)

/-- `t² ≤ 1 + t⁶`. -/
theorem sq_le_one_add_six (t : ℝ) : t ^ 2 ≤ 1 + t ^ 6 := by
  nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg (t ^ 2 - 1)), sq_nonneg (t ^ 2 - 1 / 2)]

/-- The `η₊` envelope in the generic shape. -/
theorem etaPlus_env {t : ℝ} (ht : 0 < t) :
    |HW.etaPlus t| ≤ 1.65 * ((t + t ^ 3) * Real.exp (-t ^ 2 / 2)) := by
  have h := abs_etaPlus_le ht
  have : 0 ≤ t ^ 3 * Real.exp (-t ^ 2 / 2) := by positivity
  nlinarith

/-- The `η₊'` envelope in the generic shape. -/
theorem dEP_env {t : ℝ} (ht : 0 < t) :
    |deriv HW.etaPlus t| ≤ 13756 * ((1 + t ^ 6) * Real.exp (-t ^ 2 / 2)) := by
  rw [deriv_etaPlus]
  have h := abs_dEP_le ht
  have h6 := sq_le_one_add_six t
  have hE : 0 < Real.exp (-t ^ 2 / 2) := Real.exp_pos _
  have h7 : 0 ≤ t ^ 6 := by positivity
  have h8 : 13752 + 1.65 * (1 + t ^ 2) ≤ 13756 * (1 + t ^ 6) := by nlinarith
  have := mul_le_mul_of_nonneg_right h8 hE.le
  linarith

/-- **`HM.PlusReg` PROVED.** -/
theorem plusReg_holds : HM.PlusReg :=
  ⟨agamonReg_of_env HW.etaPlus contDiff_etaPlus (fun _ ht => etaPlus_env ht)
      (fun _ ht => dEP_env ht),
    hausReg_of_env HW.etaPlus contDiff_etaPlus.continuous.measurable
      (fun _ ht => etaPlus_env ht)⟩

end Principia.Common.TernaryGoldbach.HP
