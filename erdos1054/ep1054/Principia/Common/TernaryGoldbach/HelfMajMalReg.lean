/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajPlusReg

set_option autoImplicit false

/-!
# `HM.MalReg` PROVED: `η₊,₂(t) = η₊(t)² log(xt)` is `C¹` with Gaussian envelopes

The weight of Prop 1.5 (`prop:konechno`, majarcs 4453–4457). majarcs 4466–4509 argues its
regularity from sup norms (`eq:malgache`, `eq:dalida`, `eq:gobmark`) whose `eq:havana` wrapper is
broken; here it follows from `HP.contDiff_etaPlus` and the envelopes of `HelfMajPlusReg`.

* `η₊,₂` is differentiable everywhere (`hasDerivAt_eta2x`): `0` on `(−∞, 0)`; at `0` the slope is
  `(h_H(t)e^{−t²/2})²·t log(xt) → 0`; on `(0, ∞)` the derivative is
  `2η₊η₊' log(xt) + η₊²/t` (`dE2`).
* `dE2` is continuous (`continuous_dE2`): at `0⁺`, `2η₊η₊' log(xt) = 2h_H e^{−t²/2}·η₊'·t log(xt)`
  and `η₊²/t = (h_H e^{−t²/2})² t`, every factor with a limit.
* Envelopes (`eta2x_env`, `dE2_env`), for `t > 0`, `ℓ = log x ≥ 0`:
  `|η₊,₂| ≤ 2.7225(ℓ + 1)(t + t³)e^{−t²/2}`, `|η₊,₂'| ≤ 46000(ℓ + 2)(1 + t⁶)e^{−t²/2}`
  (from `|log xt| ≤ ℓ + t + 1/t` and `tᵏ ≤ 1 + t⁶`, `k ≤ 6`).
-/

namespace Principia.Common.TernaryGoldbach.HP

open MeasureTheory Set Filter
open scoped Topology

/-- `tᵏ ≤ 1 + t⁶` for `t ≥ 0`, `k ≤ 6`. -/
theorem pow_le_one_add_six {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hk : k ≤ 6) : t ^ k ≤ 1 + t ^ 6 := by
  rcases le_total t 1 with h | h
  · have := pow_le_one₀ ht h (n := k)
    have : 0 ≤ t ^ 6 := by positivity
    linarith
  · have := pow_le_pow_right₀ h hk
    linarith

/-- `|log(xt)| ≤ log x + t + 1/t` for `x ≥ 1`, `t > 0`. -/
theorem abs_log_mul_le {x t : ℝ} (hx : 1 ≤ x) (ht : 0 < t) :
    |Real.log (x * t)| ≤ Real.log x + (t + 1 / t) := by
  rw [Real.log_mul (by linarith) ht.ne']
  have h1 := HM.abs_log_le ht
  have h2 := Real.log_nonneg hx
  calc |Real.log x + Real.log t| ≤ |Real.log x| + |Real.log t| := abs_add_le _ _
    _ ≤ Real.log x + (t + 1 / t) := by rw [abs_of_nonneg h2]; linarith

/-- `t log(xt) → 0` as `t → 0⁺` (`x > 0`). -/
theorem mul_log_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun t => t * Real.log (x * t)) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t * Real.log x + t * Real.log t) (𝓝[>] 0) (𝓝 0) := by
    have ha : Tendsto (fun t : ℝ => t * Real.log x) (𝓝 0) (𝓝 0) :=
      (by fun_prop : Continuous fun t : ℝ => t * Real.log x).tendsto' 0 0 (by simp)
    have hb : Tendsto (fun t : ℝ => t * Real.log t) (𝓝 0) (𝓝 0) := by
      have := Real.continuous_mul_log.tendsto (0 : ℝ)
      rwa [zero_mul] at this
    have := (ha.add hb).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [add_zero] at this
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Real.log_mul hx.ne' (mem_Ioi.mp ht).ne']
  ring

/-- **`η₊,₂'`, everywhere**: `2η₊η₊' log(xt) + η₊²/t` for `t > 0`, `0` for `t ≤ 0`. -/
noncomputable def dE2 (x t : ℝ) : ℝ :=
  if 0 < t then 2 * HW.etaPlus t * dEP t * Real.log (x * t) + HW.etaPlus t ^ 2 / t else 0

theorem dE2_pos (x : ℝ) {t : ℝ} (ht : 0 < t) :
    dE2 x t = 2 * HW.etaPlus t * dEP t * Real.log (x * t) + HW.etaPlus t ^ 2 / t := if_pos ht

theorem dE2_nonpos (x : ℝ) {t : ℝ} (ht : t ≤ 0) : dE2 x t = 0 := if_neg (not_lt.mpr ht)

/-- `η₊,₂ = η₊·η₊·log(x·)`. -/
theorem eta2x_eq (x : ℝ) :
    HM.eta2x x = fun t => HW.etaPlus t * HW.etaPlus t * Real.log (x * t) :=
  funext fun t => by unfold HM.eta2x; ring

theorem hasDerivAt_eta2x_pos {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    HasDerivAt (HM.eta2x x) (dE2 x t) t := by
  have hP := hasDerivAt_etaPlus t
  have hL : HasDerivAt (fun t => Real.log (x * t)) (x / (x * t)) t :=
    ((hasDerivAt_id' t).const_mul x).log (mul_pos hx ht).ne' |>.congr_deriv (by ring)
  have ht0 : t ≠ 0 := ht.ne'
  have hx0 : x ≠ 0 := hx.ne'
  have e : (dEP t * HW.etaPlus t + HW.etaPlus t * dEP t) * Real.log (x * t) +
      HW.etaPlus t * HW.etaPlus t * (x / (x * t)) =
        2 * HW.etaPlus t * dEP t * Real.log (x * t) + HW.etaPlus t ^ 2 / t := by
    field_simp
    ring
  rw [eta2x_eq, dE2_pos x ht]
  refine ((hP.mul hP).mul hL).congr_deriv ?_
  exact e

/-- At `0` the slope is `(h_H(t)e^{−t²/2})²·t log(xt) → 0`. -/
theorem hasDerivAt_eta2x_zero {x : ℝ} (hx : 0 < x) : HasDerivAt (HM.eta2x x) 0 0 := by
  have hl : HasDerivWithinAt (HM.eta2x x) 0 (Iic 0) 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr_of_mem
      (fun y hy => by unfold HM.eta2x; rw [HW.etaPlus_of_nonpos hy]; ring) self_mem_Iic
  have hr : HasDerivWithinAt (HM.eta2x x) 0 (Ioi 0) 0 := by
    rw [hasDerivWithinAt_iff_tendsto_slope' (s := Ioi (0 : ℝ)) (lt_irrefl (0 : ℝ))]
    have hc : Tendsto (fun t : ℝ => Real.exp (-t ^ 2 / 2)) (𝓝[>] 0) (𝓝 1) :=
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-t ^ 2 / 2)).tendsto' 0 1
        (by norm_num)).mono_left nhdsWithin_le_nhds
    have h1 := ((hH_tendsto_zero.mul hc).pow 2).mul (mul_log_tendsto hx)
    rw [show ((0 : ℝ) * 1) ^ 2 * 0 = 0 by norm_num] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := (mem_Ioi.mp ht).ne'
    rw [slope_def_field, show HM.eta2x x 0 = 0 by
      unfold HM.eta2x; rw [HW.etaPlus_of_nonpos le_rfl]; ring, sub_zero, sub_zero]
    unfold HM.eta2x HW.etaPlus
    field_simp
  have h := hl.union hr
  rwa [Iic_union_Ioi, hasDerivWithinAt_univ] at h

/-- **`η₊,₂` is differentiable everywhere, with derivative `dE2 x`** (`x > 0`). -/
theorem hasDerivAt_eta2x {x : ℝ} (hx : 0 < x) (t : ℝ) : HasDerivAt (HM.eta2x x) (dE2 x t) t := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [dE2_nonpos x h.le]
    refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with y hy
    unfold HM.eta2x
    rw [HW.etaPlus_of_nonpos (le_of_lt hy)]
    ring
  · rw [dE2_nonpos x le_rfl]
    exact hasDerivAt_eta2x_zero hx
  · exact hasDerivAt_eta2x_pos hx h

theorem deriv_eta2x {x : ℝ} (hx : 0 < x) : deriv (HM.eta2x x) = dE2 x :=
  funext fun t => (hasDerivAt_eta2x hx t).deriv

/-- **`η₊,₂'` is continuous.** -/
theorem continuous_dE2 {x : ℝ} (hx : 0 < x) : Continuous (dE2 x) := by
  have hcP : Continuous HW.etaPlus := contDiff_etaPlus.continuous
  have hpos : ContinuousOn (dE2 x) (Ioi 0) := by
    have hlog : ContinuousOn (fun t => Real.log (x * t)) (Ioi 0) :=
      (continuousOn_const.mul continuousOn_id).log fun t ht => (mul_pos hx ht).ne'
    have h : ContinuousOn (fun t => 2 * HW.etaPlus t * dEP t * Real.log (x * t) +
        HW.etaPlus t ^ 2 / t) (Ioi 0) :=
      (((continuousOn_const.mul hcP.continuousOn).mul continuous_dEP.continuousOn).mul hlog).add
        ((hcP.continuousOn.pow 2).div continuousOn_id fun t ht => (mem_Ioi.mp ht).ne')
    exact h.congr fun t ht => dE2_pos x ht
  have h0 : Tendsto (dE2 x) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun t : ℝ => Real.exp (-t ^ 2 / 2)) (𝓝[>] 0) (𝓝 1) :=
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-t ^ 2 / 2)).tendsto' 0 1
        (by norm_num)).mono_left nhdsWithin_le_nhds
    have hD : Tendsto dEP (𝓝[>] 0) (𝓝 0) := by
      have := continuous_dEP.tendsto 0
      rw [dEP_nonpos le_rfl] at this
      exact this.mono_left nhdsWithin_le_nhds
    have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have hg := hH_tendsto_zero.mul hc
    rw [zero_mul] at hg
    have h1 := (((hg.const_mul 2).mul hD).mul (mul_log_tendsto hx)).add ((hg.pow 2).mul ht)
    rw [show (2 * 0 * 0 * 0 + (0 : ℝ) ^ 2 * 0) = 0 by norm_num] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := (mem_Ioi.mp ht).ne'
    rw [dE2_pos x ht]
    unfold HW.etaPlus
    field_simp
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_trichotomy t 0 with h | rfl | h
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Iio_mem_nhds h] with y hy
    exact (dE2_nonpos x (le_of_lt hy)).symm
  · have hl : Tendsto (dE2 x) (𝓝[≤] 0) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (dE2_nonpos x hy).symm
    have h2 := hl.sup h0
    rw [nhdsLE_sup_nhdsGT] at h2
    rw [ContinuousAt, dE2_nonpos x le_rfl]
    exact h2
  · exact hpos.continuousAt (Ioi_mem_nhds h)

/-- **`η₊,₂ ∈ C¹(ℝ)`** for `x > 0`. -/
theorem contDiff_eta2x {x : ℝ} (hx : 0 < x) : ContDiff ℝ 1 (HM.eta2x x) :=
  contDiff_one_iff_deriv.mpr ⟨fun t => (hasDerivAt_eta2x hx t).differentiableAt,
    by rw [deriv_eta2x hx]; exact continuous_dE2 hx⟩

/-- **The `η₊,₂` envelope**: `|η₊,₂(t)| ≤ 2.7225(ℓ + 1)(t + t³)e^{−t²/2}`, `ℓ = log x`. -/
theorem eta2x_env {x t : ℝ} (hx : 1 ≤ x) (ht : 0 < t) :
    |HM.eta2x x t| ≤ 2.7225 * (Real.log x + 1) * ((t + t ^ 3) * Real.exp (-t ^ 2 / 2)) := by
  have hP := abs_etaPlus_le ht
  have hL := abs_log_mul_le hx ht
  have hl0 := Real.log_nonneg hx
  have hE : Real.exp (-t ^ 2) ≤ Real.exp (-t ^ 2 / 2) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t])
  have hE0 : 0 < Real.exp (-t ^ 2) := Real.exp_pos _
  have hP2 : HW.etaPlus t ^ 2 ≤ 2.7225 * (t ^ 2 * Real.exp (-t ^ 2)) := by
    rw [← sq_abs]
    have h := pow_le_pow_left₀ (abs_nonneg _) hP 2
    have e : (1.65 * (t * Real.exp (-t ^ 2 / 2))) ^ 2 = 2.7225 * (t ^ 2 * Real.exp (-t ^ 2)) := by
      rw [mul_pow, mul_pow, HM.exp_half_sq]
      ring
    linarith
  unfold HM.eta2x
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  have h1 := mul_le_mul hP2 hL (abs_nonneg _) (by positivity)
  have e1 : 2.7225 * (t ^ 2 * Real.exp (-t ^ 2)) * (Real.log x + (t + 1 / t)) =
      2.7225 * (Real.log x * t ^ 2 + t ^ 3 + t) * Real.exp (-t ^ 2) := by
    field_simp
    ring
  have h2 : Real.log x * t ^ 2 + t ^ 3 + t ≤ (Real.log x + 1) * (t + t ^ 3) := by
    have : t ^ 2 ≤ t + t ^ 3 := by nlinarith [sq_nonneg (t - 1)]
    nlinarith
  have h3 : 0 ≤ Real.log x * t ^ 2 + t ^ 3 + t := by positivity
  have h4 := mul_le_mul h2 hE (le_of_lt hE0) (by positivity)
  nlinarith

/-- **The `η₊,₂'` envelope**: `|η₊,₂'(t)| ≤ 46000(ℓ + 2)(1 + t⁶)e^{−t²/2}`. -/
theorem dE2_env {x t : ℝ} (hx : 1 ≤ x) (ht : 0 < t) :
    |dE2 x t| ≤ 46000 * (Real.log x + 2) * ((1 + t ^ 6) * Real.exp (-t ^ 2 / 2)) := by
  have hP := abs_etaPlus_le ht
  have hD := abs_dEP_le ht
  have hL := abs_log_mul_le hx ht
  have hl0 := Real.log_nonneg hx
  have hE2 : 0 < Real.exp (-t ^ 2 / 2) := Real.exp_pos _
  have hE : Real.exp (-t ^ 2) ≤ Real.exp (-t ^ 2 / 2) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t])
  have hE1 : Real.exp (-t ^ 2 / 2) * Real.exp (-t ^ 2 / 2) = Real.exp (-t ^ 2) := by
    rw [← sq, HM.exp_half_sq]
  set ℓ := Real.log x with hℓ
  set E := Real.exp (-t ^ 2 / 2) with hEdef
  set F := Real.exp (-t ^ 2) with hFdef
  -- the first term
  have hA : |2 * HW.etaPlus t * dEP t * Real.log (x * t)| ≤
      3.3 * ((13752 + 1.65 * (1 + t ^ 2)) * (ℓ * t + t ^ 2 + 1)) * F := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have p1 := mul_le_mul hP hD (abs_nonneg _) (by positivity)
    have p2 := mul_le_mul p1 hL (abs_nonneg _) (by positivity)
    have e : 2 * (1.65 * (t * E) * ((13752 + 1.65 * (1 + t ^ 2)) * E) * (ℓ + (t + 1 / t))) =
        3.3 * ((13752 + 1.65 * (1 + t ^ 2)) * (ℓ * t + t ^ 2 + 1)) * (E * E) := by
      field_simp
      ring
    rw [hE1] at e
    nlinarith
  -- the second term
  have hB : |HW.etaPlus t ^ 2 / t| ≤ 2.7225 * t * F := by
    rw [abs_div, abs_of_pos ht, abs_of_nonneg (sq_nonneg _), div_le_iff₀ ht, ← sq_abs]
    have h := pow_le_pow_left₀ (abs_nonneg _) hP 2
    have e : (1.65 * (t * E)) ^ 2 = 2.7225 * t * F * t := by
      rw [mul_pow, mul_pow, hEdef, HM.exp_half_sq]
      ring
    linarith
  rw [dE2_pos x ht]
  have hsum := abs_add_le (2 * HW.etaPlus t * dEP t * Real.log (x * t)) (HW.etaPlus t ^ 2 / t)
  -- the polynomial
  have t0 := ht.le
  have k1 := pow_le_one_add_six t0 (k := 1) (by norm_num)
  have k2 := pow_le_one_add_six t0 (k := 2) (by norm_num)
  have k3 := pow_le_one_add_six t0 (k := 3) (by norm_num)
  have k4 := pow_le_one_add_six t0 (k := 4) (by norm_num)
  have l1 := mul_le_mul_of_nonneg_left k1 hl0
  have l3 := mul_le_mul_of_nonneg_left k3 hl0
  have hpoly : 3.3 * ((13752 + 1.65 * (1 + t ^ 2)) * (ℓ * t + t ^ 2 + 1)) + 2.7225 * t ≤
      46000 * (ℓ + 2) * (1 + t ^ 6) := by
    simp only [pow_one] at k1 l1
    have m6 := pow_nonneg t0 6
    have m7 := mul_nonneg hl0 m6
    linarith
  have hpoly0 : 0 ≤ 3.3 * ((13752 + 1.65 * (1 + t ^ 2)) * (ℓ * t + t ^ 2 + 1)) + 2.7225 * t := by
    positivity
  have hfin := mul_le_mul hpoly hE (le_of_lt (Real.exp_pos _)) (by positivity)
  nlinarith

/-- **`HM.MalReg` PROVED.** -/
theorem malReg_holds : HM.MalReg := by
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have he : ∀ t, 0 < t → |HM.eta2x x t| ≤
      2.7225 * (Real.log x + 1) * ((t + t ^ 3) * Real.exp (-t ^ 2 / 2)) :=
    fun _ ht => eta2x_env hx1 ht
  have hd : ∀ t, 0 < t → |deriv (HM.eta2x x) t| ≤
      46000 * (Real.log x + 2) * ((1 + t ^ 6) * Real.exp (-t ^ 2 / 2)) := fun t ht => by
    rw [deriv_eta2x hx0]
    exact dE2_env hx1 ht
  exact ⟨agamonReg_of_env (HM.eta2x x) (contDiff_eta2x hx0) he hd,
    hausReg_of_env (HM.eta2x x) (contDiff_eta2x hx0).continuous.measurable he⟩

end Principia.Common.TernaryGoldbach.HP
