/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.BandLimit
import Principia.Common.TernaryGoldbach.MajorSpine

set_option autoImplicit false

/-!
# `MajSp.SupN` on Helfgott's own weights, PROVED

`MajSp.SupN η₊ η*` is five sup-norm bounds on `t ≥ 0` (`eq:sazar`, `eq:muthit`, `eq:macadam`, 4744,
4723–4727). All five are theorems here, for `η₊ = HW.etaPlus`, `η* = HW.etaStar`:

1. `|η₊| ≤ 1.079955` — `BL.etaPlusSup`.
2. `|η₊·t| ≤ 1.19073` — `η₊·t = η∘·t + (h₂₀₀ − h)·t²e^{−t²/2}`, with `|η∘·t| ≤ 1.08` (on `[0,2]`
   it is at most `(1+u)(1−u²)³ ≤ 1.0743`, `u = t − 1`; true sup `1.06473`), `|h₂₀₀ − h| ≤ 0.13`
   (`BL.band_uniform`) and `t²e^{−t²/2} ≤ 2/e` (`HW.phi_le`): `1.08 + 0.13·0.73576 = 1.17566`.
3. `0 ≤ η* ≤ 1.414` — `HW.etaStar_pos`, `HW.etaStar_of_nonpos`, `HW.etaStar_le`.
4. `η*·t ≤ 3√3e^{−3/2}/49` — Helfgott's Hölder argument, done here: for `s = 49t > 0`,
   `(η₂ ∗_M φ)(s)·s = ∫ η₂(s/y)(s/y²)·y³e^{−y²/2} dy ≤ |η₂|₁·max(y³e^{−y²/2})`, with
   `∫_s^{4s} η₂(s/y) s/y² dy = |η₂|₁ = 1` EXACTLY (`int_eta2_sy2`, the fundamental theorem of
   calculus on `[s,2s]` and `[2s,4s]`: `(2 − 2 log 2) + (2 log 2 − 1)`) and
   `y³e^{−y²/2} ≤ 3√3e^{−3/2}` (`cube_exp_le`, from `a ≤ e^{(a²−1)/2}`, `a = y/√3`).
5. `η*(t)·log⁺(49t) ≤ 0.732513` — **NOT by Helfgott's route.** Helfgott's is
   `|η₂(t)/t|₁·|φ log⁺|_∞ = 1.9218121·0.3811560 = 0.7325103`, which clears `0.732513` by only
   `2.7·10⁻⁶` and would need `sup_y y²e^{−y²/2} log y` to seven digits. Instead: `log⁺ z ≤ z/e`
   for `z ≥ 0`, so `η*(t)·log⁺(49t) ≤ (49/e)·η*(t)·t ≤ 3√3e^{−5/2} = 0.42653`, from conjunct 4.
   Conjunct 5 is therefore a CONSEQUENCE of conjunct 4 at a better constant; nothing is weakened.

`supN_helf : MajSp.SupN HW.etaPlus HW.etaStar` — the link is closed on Helfgott's weights.
-/

namespace Principia.Common.TernaryGoldbach.EN

open MeasureTheory Set

/-! ## Conjunct 2: `|η₊·t| ≤ 1.19073` -/

/-- `(1+u)(1−u²)³ ≤ 1.08` on `[−1, 1]` (max `1.0743046` at `u = 1/7`). -/
theorem poly_circ_t {u : ℝ} (h0 : -1 ≤ u) (h1 : u ≤ 1) : (1 + u) * (1 - u ^ 2) ^ 3 ≤ 1.08 := by
  have hw0 : 0 ≤ 1 - u ^ 2 := by nlinarith
  have hw1 : 1 - u ^ 2 ≤ 1 := by nlinarith [sq_nonneg u]
  rcases le_total u 0 with hu | hu
  · have hc : (1 - u ^ 2) ^ 3 ≤ 1 := pow_le_one₀ hw0 hw1
    have ha : 0 ≤ 1 + u := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hc ha]
  · nlinarith [sq_nonneg (u - 1 / 7), mul_nonneg hu (sq_nonneg (u - 1 / 7)),
      mul_nonneg (mul_nonneg hu hu) (sq_nonneg (u - 1 / 7)), pow_nonneg hu 3, pow_nonneg hu 4,
      pow_nonneg hu 5, mul_nonneg hu (sub_nonneg.mpr h1)]

/-- **`|η∘(t)·t| ≤ 1.08` for every real `t`** (true sup `1.0647348`). -/
theorem etaCirc_mul_le (t : ℝ) : |HW.etaCirc t * t| ≤ 1.08 := by
  by_cases h : 0 ≤ t ∧ t ≤ 2
  · obtain ⟨h0, h2⟩ := h
    rw [HW.etaCirc_eq h0 h2]
    have he : Real.exp (-(t - 1) ^ 2 / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (t - 1)])
    have hp := poly_circ_t (u := t - 1) (by linarith) (by linarith)
    have hq0 : 0 ≤ t ^ 3 * (2 - t) ^ 3 * t := by
      have : 0 ≤ 2 - t := by linarith
      positivity
    have hq : t ^ 3 * (2 - t) ^ 3 * t = (1 + (t - 1)) * (1 - (t - 1) ^ 2) ^ 3 := by ring
    rw [abs_of_nonneg (by positivity)]
    calc t ^ 3 * (2 - t) ^ 3 * Real.exp (-(t - 1) ^ 2 / 2) * t
        = t ^ 3 * (2 - t) ^ 3 * t * Real.exp (-(t - 1) ^ 2 / 2) := by ring
      _ ≤ t ^ 3 * (2 - t) ^ 3 * t * 1 := mul_le_mul_of_nonneg_left he hq0
      _ ≤ 1.08 := by rw [mul_one, hq]; exact hp
  · rw [HW.etaCirc, HW.hFun, if_neg h]
    norm_num

/-- `2/e ≤ 0.73576` (truth `0.7357589`), from `e > 2.7182818283`. -/
theorem two_div_e_le : 2 / Real.exp 1 ≤ 0.73576 := by
  have he := Real.exp_one_gt_d9
  rw [div_le_iff₀ (Real.exp_pos 1)]
  linarith

/-- **Conjunct 2 of `SupN`**: `|η₊(t)·t| ≤ 1.19073` for every real `t`, from `BL.band_uniform`. -/
theorem etaPlus_mul_le (t : ℝ) : |HW.etaPlus t * t| ≤ 1.19073 := by
  have hsplit : HW.etaPlus t * t =
      HW.etaCirc t * t + (HW.hH 200 t - HW.hFun t) * HW.phi t := by
    rw [HW.etaPlus, HW.etaCirc, HW.phi]
    ring
  have hb := HW.band_all BL.band_uniform t
  have hphi0 := HW.phi_nonneg t
  have hphi := (HW.phi_le t).trans two_div_e_le
  rw [hsplit]
  calc |HW.etaCirc t * t + (HW.hH 200 t - HW.hFun t) * HW.phi t|
      ≤ |HW.etaCirc t * t| + |HW.hH 200 t - HW.hFun t| * HW.phi t := by
        rw [← abs_of_nonneg hphi0, ← abs_mul, abs_of_nonneg hphi0]
        exact abs_add_le _ _
    _ ≤ 1.08 + 0.13 * 0.73576 :=
        add_le_add (etaCirc_mul_le t) (mul_le_mul hb hphi hphi0 (by norm_num))
    _ ≤ 1.19073 := by norm_num

/-! ## Conjunct 4: `η*·t ≤ 3√3e^{−3/2}/49` -/

/-- `a ≤ e^{(a²−1)/2}` for every real `a` (`a ≤ (a²+1)/2 ≤ e^{(a²−1)/2}`). -/
theorem le_exp_half (a : ℝ) : a ≤ Real.exp ((a ^ 2 - 1) / 2) := by
  have h1 : a ≤ (a ^ 2 - 1) / 2 + 1 := by nlinarith [sq_nonneg (a - 1)]
  exact h1.trans (Real.add_one_le_exp _)

/-- **`max_y y³e^{−y²/2} = 3√3e^{−3/2}`** (attained at `y = √3`): `y³e^{−y²/2} ≤ 3√3e^{−3/2}` for
`y ≥ 0`. With `a = y/√3`: `a³ ≤ e^{3(a²−1)/2}`. -/
theorem cube_exp_le {y : ℝ} (hy : 0 ≤ y) :
    y ^ 3 * Real.exp (-y ^ 2 / 2) ≤ 3 * Real.sqrt 3 * Real.exp (-3 / 2) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set a := y / Real.sqrt 3 with ha
  have hy' : y = Real.sqrt 3 * a := by rw [ha]; field_simp
  have ha0 : 0 ≤ a := div_nonneg hy hs.le
  have h1 : a ^ 3 ≤ Real.exp ((a ^ 2 - 1) / 2) ^ 3 := pow_le_pow_left₀ ha0 (le_exp_half a) 3
  have h2 : Real.exp ((a ^ 2 - 1) / 2) ^ 3 * Real.exp (-y ^ 2 / 2) = Real.exp (-3 / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, hy', mul_pow, hs2]
    congr 1
    push_cast
    ring
  have h3 : y ^ 3 = 3 * Real.sqrt 3 * a ^ 3 := by
    rw [hy', mul_pow, show Real.sqrt 3 ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 by ring, hs2]
  rw [h3, ← h2]
  have he : 0 ≤ Real.exp (-y ^ 2 / 2) := (Real.exp_pos _).le
  have hc : 0 ≤ 3 * Real.sqrt 3 := by positivity
  calc 3 * Real.sqrt 3 * a ^ 3 * Real.exp (-y ^ 2 / 2)
      = 3 * Real.sqrt 3 * (a ^ 3 * Real.exp (-y ^ 2 / 2)) := by ring
    _ ≤ 3 * Real.sqrt 3 * (Real.exp ((a ^ 2 - 1) / 2) ^ 3 * Real.exp (-y ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 he) hc

/-- `∫_s^{2s} η₂(s/y)·s/y² dy = 2 − 2 log 2`, by the fundamental theorem of calculus. -/
theorem int_lo_sy2 {s : ℝ} (hs : 0 < s) :
    ∫ y in s..2 * s, HW.eta2 (s / y) * (s / y ^ 2) = 2 - 2 * Real.log 2 := by
  have hle : s ≤ 2 * s := by linarith
  have hsub : uIcc s (2 * s) ⊆ Ioi 0 := HW.uIcc_pos hs (by linarith)
  have hcongr : EqOn (fun y => HW.eta2 (s / y) * (s / y ^ 2))
      (fun y => 4 * (Real.log y - Real.log s) * (s / y ^ 2)) (uIcc s (2 * s)) := by
    intro y hy
    rw [uIcc_of_le hle] at hy
    simp only [HW.eta2_lo hs hy.1 hy.2]
  rw [intervalIntegral.integral_congr hcongr]
  have hd : ∀ y ∈ uIcc s (2 * s), HasDerivAt
      (fun y => -4 * s * ((Real.log y - Real.log s + 1) * y⁻¹))
      (4 * (Real.log y - Real.log s) * (s / y ^ 2)) y := by
    intro y hy
    have hy0 : 0 < y := hsub hy
    have h := (((Real.hasDerivAt_log hy0.ne').sub_const (Real.log s)).add_const 1).mul
      (hasDerivAt_inv hy0.ne')
    refine (h.const_mul (-4 * s)).congr_deriv ?_
    field_simp
    ring
  have hi : IntervalIntegrable (fun y => 4 * (Real.log y - Real.log s) * (s / y ^ 2)) volume s
      (2 * s) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul (continuousOn_const.mul
      ((Real.continuousOn_log.mono fun y hy => ?_).sub continuousOn_const))
      (continuousOn_const.div (continuousOn_pow 2) fun y hy => pow_ne_zero 2 (hsub hy).ne')
    exact (hsub hy).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, Real.log_mul two_ne_zero hs.ne']
  field_simp
  ring

/-- `∫_{2s}^{4s} η₂(s/y)·s/y² dy = 2 log 2 − 1`, by the fundamental theorem of calculus. -/
theorem int_hi_sy2 {s : ℝ} (hs : 0 < s) :
    ∫ y in 2 * s..4 * s, HW.eta2 (s / y) * (s / y ^ 2) = 2 * Real.log 2 - 1 := by
  have hle : 2 * s ≤ 4 * s := by linarith
  have hsub : uIcc (2 * s) (4 * s) ⊆ Ioi 0 := HW.uIcc_pos (by linarith) (by linarith)
  have hcongr : EqOn (fun y => HW.eta2 (s / y) * (s / y ^ 2))
      (fun y => 4 * (2 * Real.log 2 + Real.log s - Real.log y) * (s / y ^ 2))
      (uIcc (2 * s) (4 * s)) := by
    intro y hy
    rw [uIcc_of_le hle] at hy
    simp only [HW.eta2_hi hs hy.1 hy.2]
  rw [intervalIntegral.integral_congr hcongr]
  have hd : ∀ y ∈ uIcc (2 * s) (4 * s), HasDerivAt
      (fun y => 4 * s * ((Real.log y - (2 * Real.log 2 + Real.log s) + 1) * y⁻¹))
      (4 * (2 * Real.log 2 + Real.log s - Real.log y) * (s / y ^ 2)) y := by
    intro y hy
    have hy0 : 0 < y := hsub hy
    have h := (((Real.hasDerivAt_log hy0.ne').sub_const (2 * Real.log 2 + Real.log s)).add_const
      1).mul (hasDerivAt_inv hy0.ne')
    refine (h.const_mul (4 * s)).congr_deriv ?_
    field_simp
    ring
  have hi : IntervalIntegrable
      (fun y => 4 * (2 * Real.log 2 + Real.log s - Real.log y) * (s / y ^ 2)) volume (2 * s)
      (4 * s) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul (continuousOn_const.mul
      (continuousOn_const.sub (Real.continuousOn_log.mono fun y hy => ?_)))
      (continuousOn_const.div (continuousOn_pow 2) fun y hy => pow_ne_zero 2 (hsub hy).ne')
    exact (hsub hy).ne'
  have h4 : Real.log (4 * s) = 2 * Real.log 2 + Real.log s := by
    rw [show (4 : ℝ) * s = 2 * (2 * s) by ring, Real.log_mul two_ne_zero (by positivity),
      Real.log_mul two_ne_zero hs.ne']
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, h4, Real.log_mul two_ne_zero hs.ne']
  field_simp
  ring

/-- **`|η₂|₁ = 1`, at every scale**: `∫_s^{4s} η₂(s/y)·s/y² dy = 1` (substitute `r = s/y`). -/
theorem int_eta2_sy2 {s : ℝ} (hs : 0 < s) :
    ∫ y in s..4 * s, HW.eta2 (s / y) * (s / y ^ 2) = 1 := by
  have hc : ContinuousOn (fun y => HW.eta2 (s / y) * (s / y ^ 2)) (Ioi 0) :=
    (HW.eta2_div_contOn hs).mul (continuousOn_const.div (continuousOn_pow 2)
      fun y hy => pow_ne_zero 2 (mem_Ioi.mp hy).ne')
  have h1 : IntervalIntegrable (fun y => HW.eta2 (s / y) * (s / y ^ 2)) volume s (2 * s) :=
    (hc.mono (HW.uIcc_pos hs (by linarith))).intervalIntegrable
  have h2 : IntervalIntegrable (fun y => HW.eta2 (s / y) * (s / y ^ 2)) volume (2 * s) (4 * s) :=
    (hc.mono (HW.uIcc_pos (by linarith) (by linarith))).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, int_lo_sy2 hs, int_hi_sy2 hs]
  ring

/-- **Conjunct 4 of `SupN`**: `η*(t)·t ≤ 3√3e^{−3/2}/49` for every `t ≥ 0` (Helfgott's Hölder
bound `|η₂|₁·|t³e^{−t²/2}|_∞/κ`, with `|η₂|₁ = 1` computed exactly). -/
theorem etaStar_mul_le {t : ℝ} (ht : 0 ≤ t) :
    HW.etaStar t * t ≤ 3 * Real.sqrt 3 * Real.exp (-3 / 2) / 49 := by
  have hM : 0 ≤ 3 * Real.sqrt 3 * Real.exp (-3 / 2) / 49 := by positivity
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact hM
  set s := 49 * t with hs_def
  have hs : 0 < s := by positivity
  have hst : t = s / 49 := by rw [hs_def]; ring
  have heq : HW.etaStar t * t = ∫ y in s..4 * s, HW.eta2 (s / y) * HW.phi y / y * (s / 49) := by
    rw [HW.etaStar, ← hs_def, HW.mconv_eta2 HW.phi hs, intervalIntegral.integral_mul_const, hst]
  rw [heq]
  have hc : ContinuousOn (fun y => HW.eta2 (s / y) * (s / y ^ 2)) (Ioi 0) :=
    (HW.eta2_div_contOn hs).mul (continuousOn_const.div (continuousOn_pow 2)
      fun y hy => pow_ne_zero 2 (mem_Ioi.mp hy).ne')
  have hc2 : ContinuousOn (fun y => HW.eta2 (s / y) * HW.phi y / y * (s / 49)) (Ioi 0) :=
    ((((HW.eta2_div_contOn hs).mul HW.continuous_phi.continuousOn).div continuousOn_id
      fun y hy => (mem_Ioi.mp hy).ne').mul continuousOn_const)
  have hsub : uIcc s (4 * s) ⊆ Ioi 0 := HW.uIcc_pos hs (by linarith)
  have hmono : ∫ y in s..4 * s, HW.eta2 (s / y) * HW.phi y / y * (s / 49) ≤
      ∫ y in s..4 * s, 3 * Real.sqrt 3 * Real.exp (-3 / 2) / 49 *
        (HW.eta2 (s / y) * (s / y ^ 2)) := by
    refine intervalIntegral.integral_mono_on (by linarith) ((hc2.mono hsub).intervalIntegrable)
      (((hc.mono hsub).intervalIntegrable).const_mul _) fun y hy => ?_
    have hy0 : 0 < y := lt_of_lt_of_le hs hy.1
    have hcube := cube_exp_le hy0.le
    have he0 : 0 ≤ HW.eta2 (s / y) * (s / y ^ 2) :=
      mul_nonneg (HW.eta2_nonneg _) (div_nonneg hs.le (sq_nonneg y))
    have hr : HW.eta2 (s / y) * HW.phi y / y * (s / 49) =
        HW.eta2 (s / y) * (s / y ^ 2) * (y ^ 3 * Real.exp (-y ^ 2 / 2)) / 49 := by
      rw [HW.phi]
      field_simp
    rw [hr]
    calc HW.eta2 (s / y) * (s / y ^ 2) * (y ^ 3 * Real.exp (-y ^ 2 / 2)) / 49
        ≤ HW.eta2 (s / y) * (s / y ^ 2) * (3 * Real.sqrt 3 * Real.exp (-3 / 2)) / 49 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcube he0) (by norm_num)
      _ = 3 * Real.sqrt 3 * Real.exp (-3 / 2) / 49 * (HW.eta2 (s / y) * (s / y ^ 2)) := by ring
  rw [intervalIntegral.integral_const_mul, int_eta2_sy2 hs, mul_one] at hmono
  exact hmono

/-! ## Conjunct 5: `η*(t)·log⁺(49t) ≤ 0.732513`, from conjunct 4 -/

/-- `max(0, log z) ≤ z/e` for `z ≥ 0` (`log(z/e) ≤ z/e − 1`). -/
theorem logplus_le {z : ℝ} (hz : 0 ≤ z) : max 0 (Real.log z) ≤ z / Real.exp 1 := by
  have he := Real.exp_pos 1
  refine max_le (div_nonneg hz he.le) ?_
  rcases hz.eq_or_lt with h0 | hpos
  · rw [← h0, Real.log_zero, zero_div]
  · have h := Real.log_le_sub_one_of_pos (div_pos hpos he)
    rw [Real.log_div hpos.ne' he.ne', Real.log_exp] at h
    linarith

/-- `3√3e^{−3/2} ≤ 1.1599` (`1.1594`), from `√3 ≤ 1.7321` and `e^{−3/2} ≤ 0.2232`. -/
theorem holder_cube_le : 3 * Real.sqrt 3 * Real.exp (-3 / 2) ≤ 1.1599 := by
  have hsq : Real.sqrt 3 ≤ 1.7321 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have h0 : 0 ≤ Real.exp (-3 / 2) := (Real.exp_pos _).le
  have hc := mul_le_mul hsq MajSp.exp_neg_le h0 (by norm_num)
  linarith

/-- **Conjunct 5 of `SupN`**: `η*(t)·max(0, log 49t) ≤ 0.732513` for `t ≥ 0`, from conjunct 4:
`≤ (49/e)·η*(t)·t ≤ 3√3e^{−3/2}/e ≤ 1.1599/2.718 = 0.4267`. -/
theorem etaStar_logplus_le {t : ℝ} (ht : 0 ≤ t) :
    HW.etaStar t * max 0 (Real.log (49 * t)) ≤ 0.732513 := by
  have he := Real.exp_one_gt_d9
  have he0 := Real.exp_pos 1
  have hη0 : 0 ≤ HW.etaStar t := by
    rcases ht.eq_or_lt with h0 | hpos
    · rw [← h0, HW.etaStar_of_nonpos le_rfl]
    · exact (HW.etaStar_pos hpos).le
  have hl := logplus_le (z := 49 * t) (by positivity)
  have h4 := etaStar_mul_le ht
  have hc := holder_cube_le
  have h1 : HW.etaStar t * max 0 (Real.log (49 * t)) ≤ HW.etaStar t * (49 * t / Real.exp 1) :=
    mul_le_mul_of_nonneg_left hl hη0
  have h2 : HW.etaStar t * (49 * t / Real.exp 1) = 49 * (HW.etaStar t * t) / Real.exp 1 := by
    ring
  have h3 : 49 * (HW.etaStar t * t) ≤ 1.1599 := by linarith
  have h5 : 49 * (HW.etaStar t * t) / Real.exp 1 ≤ 1.1599 / 2.7182818283 :=
    div_le_div₀ (by norm_num) h3 (by norm_num) he.le
  have h6 : (1.1599 : ℝ) / 2.7182818283 ≤ 0.732513 := by norm_num
  linarith

/-! ## The link -/

/-- **Conjunct 3 of `SupN`**: `0 ≤ η* ≤ 1.414` on `t ≥ 0`. -/
theorem etaStar_mem {t : ℝ} (ht : 0 ≤ t) : 0 ≤ HW.etaStar t ∧ HW.etaStar t ≤ 1.414 := by
  refine ⟨?_, (le_abs_self _).trans (HW.etaStar_le t)⟩
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0, HW.etaStar_of_nonpos le_rfl]
  · exact (HW.etaStar_pos hpos).le

/-- **`MajSp.SupN` holds on Helfgott's own weights** `η₊ = HW.etaPlus`, `η* = HW.etaStar`: all
five sup-norm bounds are theorems. -/
theorem supN_helf : MajSp.SupN HW.etaPlus HW.etaStar :=
  ⟨fun t _ => BL.etaPlusSup t, fun t _ => etaPlus_mul_le t, fun _ ht => etaStar_mem ht,
    fun _ ht => etaStar_mul_le ht, fun _ ht => etaStar_logplus_le ht⟩

end Principia.Common.TernaryGoldbach.EN
