/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.KSmall

set_option autoImplicit false

/-!
# Helfgott's weights vanish linearly at `0`

The weight-aware balanced reduction (`Principia.Erdos1054.Proofs.BalancedW`) needs `|η₊(u)| ≤ A u`
and `|η_*(u)| ≤ B u` for small `u ≥ 0`. Both hold for every `u ≥ 0`:

* `etaPlus_le_lin`: `|η₊(t)| ≤ 3t`, from `KS.etaPlus_le` (`3 t e^{−t}`) and `e^{−t} ≤ 1`.
* `etaStar_bounds`: `0 ≤ η_*(t) ≤ 250 t`. For `t > 0`,
  `η_*(t) = ∫_s^{4s} η₂(s/y) φ(y)/y dy` with `s = 49t` (`HW.mconv_eta2`), where `η₂ ≤ 4 log 2`
  (`eta2_le`) and `φ(y)/y = y e^{−y²/2} ≤ e^{−1/2}` (`HW.abs_mul_exp_le`). The interval has length
  `3s`, so `η_*(t) ≤ 588 log 2 · e^{−1/2} · t < 588 · 0.6932/1.64 · t = 248.5 t`
  (`e^{1/2} > 1.64`, `HW.exp_half_gt`).

The linear bound is loose near `0`: numerically `η_*(t)/t² → 9·49² = 21609` as `t → 0`
(`∫ η₂(u) u⁻³ du = 9`), and `η_*(t) ≤ 30 log 2 · 49² t²` is also elementary. The reduction needs
only the linear form (`HelfgottAtW 2·10⁻⁸ 3 250`).
-/

namespace Principia.Common.TernaryGoldbach.WS

open MeasureTheory Set

/-- **`|η₊(t)| ≤ 3t` for `t ≥ 0`**: `KS.etaPlus_le` with `e^{−t} ≤ 1`. -/
theorem etaPlus_le_lin (t : ℝ) (ht : 0 ≤ t) : |HW.etaPlus t| ≤ 3 * t := by
  have h := KS.etaPlus_le t ht
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : t * Real.exp (-t) ≤ t := by
    calc t * Real.exp (-t) ≤ t * 1 := mul_le_mul_of_nonneg_left he ht
      _ = t := mul_one t
  linarith

/-- `η₂ ≤ 4 log 2`. -/
theorem eta2_le (t : ℝ) : HW.eta2 t ≤ 4 * Real.log 2 := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold HW.eta2
  split_ifs
  · have hm : max (Real.log 2 - |Real.log (2 * t)|) 0 ≤ Real.log 2 :=
      max_le (by linarith [abs_nonneg (Real.log (2 * t))]) hl
    linarith
  · linarith

/-- The integrand of `η_*` at `y > 0`: `0 ≤ η₂(s/y) φ(y)/y ≤ 4 log 2 · e^{−1/2}`. -/
theorem integrand_bounds (s : ℝ) {y : ℝ} (hy : 0 < y) :
    0 ≤ HW.eta2 (s / y) * HW.phi y / y ∧
      HW.eta2 (s / y) * HW.phi y / y ≤ 4 * Real.log 2 * Real.exp (-1 / 2) := by
  have he := HW.eta2_nonneg (s / y)
  have hp := HW.phi_nonneg y
  refine ⟨div_nonneg (mul_nonneg he hp) hy.le, ?_⟩
  have hpy : HW.phi y / y = |y| * Real.exp (-y ^ 2 / 2) := by
    rw [HW.phi, abs_of_pos hy, div_eq_iff hy.ne']
    ring
  have hk := HW.abs_mul_exp_le y
  have hl := eta2_le (s / y)
  have hl0 : 0 ≤ 4 * Real.log 2 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have hq0 : 0 ≤ |y| * Real.exp (-y ^ 2 / 2) := by positivity
  calc HW.eta2 (s / y) * HW.phi y / y = HW.eta2 (s / y) * (HW.phi y / y) := by ring
    _ = HW.eta2 (s / y) * (|y| * Real.exp (-y ^ 2 / 2)) := by rw [hpy]
    _ ≤ 4 * Real.log 2 * Real.exp (-1 / 2) := mul_le_mul hl hk hq0 hl0

/-- `12 log 2 · e^{−1/2} ≤ 250/49`: `log 2 < 0.6932`, `e^{−1/2} < 1/1.64`, and
`12 · 0.6932/1.64 = 5.0722 < 5.1020`. -/
theorem const_le : 4 * Real.log 2 * Real.exp (-1 / 2) * 3 ≤ 250 / 49 := by
  have hl2 : Real.log 2 < 6932 / 10000 := Real.log_two_lt_d9.trans_le (by norm_num)
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hx : (41 : ℝ) / 25 < Real.exp (1 / 2) := lt_of_eq_of_lt (by norm_num) HW.exp_half_gt
  have hen : 0 < Real.exp (-1 / 2) := Real.exp_pos _
  have hneg : Real.exp (-1 / 2) * Real.exp (1 / 2) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hm := mul_lt_mul_of_pos_left hx hen
  have he : Real.exp (-1 / 2) * (41 / 25) < 1 := by linarith
  have hp : Real.log 2 * Real.exp (-1 / 2) ≤ 6932 / 10000 * Real.exp (-1 / 2) :=
    mul_le_mul_of_nonneg_right hl2.le hen.le
  nlinarith

/-- **`0 ≤ η_*(t) ≤ 250 t` for `t ≥ 0`.** -/
theorem etaStar_bounds (t : ℝ) (ht : 0 ≤ t) : 0 ≤ HW.etaStar t ∧ HW.etaStar t ≤ 250 * t := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    rw [HW.etaStar_of_nonpos le_rfl]
    norm_num
  have hs : 0 < 49 * t := by positivity
  have h4s : 0 < 4 * (49 * t) := by positivity
  have hE : HW.etaStar t =
      ∫ y in (49 * t)..4 * (49 * t), HW.eta2 ((49 * t) / y) * HW.phi y / y :=
    HW.mconv_eta2 HW.phi hs
  have hle : 49 * t ≤ 4 * (49 * t) := by linarith
  have hsub := HW.uIcc_pos hs h4s
  have hcont : ContinuousOn (fun y => HW.eta2 ((49 * t) / y) * HW.phi y / y)
      (Set.uIcc (49 * t) (4 * (49 * t))) :=
    (((HW.eta2_div_contOn hs).mono hsub).mul HW.continuous_phi.continuousOn).div
      continuousOn_id (fun y hy => (hsub hy).ne')
  have hint : IntervalIntegrable (fun y => HW.eta2 ((49 * t) / y) * HW.phi y / y) volume
      (49 * t) (4 * (49 * t)) := hcont.intervalIntegrable
  constructor
  · rw [hE]
    exact intervalIntegral.integral_nonneg hle
      (fun y hy => (integrand_bounds (49 * t) (lt_of_lt_of_le hs hy.1)).1)
  · have hup : (∫ y in (49 * t)..4 * (49 * t), HW.eta2 ((49 * t) / y) * HW.phi y / y) ≤
        ∫ _ in (49 * t)..4 * (49 * t), 4 * Real.log 2 * Real.exp (-1 / 2) :=
      intervalIntegral.integral_mono_on hle hint intervalIntegrable_const
        (fun y hy => (integrand_bounds (49 * t) (lt_of_lt_of_le hs hy.1)).2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hup
    have hk := mul_le_mul_of_nonneg_left const_le hs.le
    rw [hE]
    nlinarith

/-- **`|η_*(u)| ≤ 250 u` for `u ≥ 0`.** -/
theorem etaStar_le_lin (u : ℝ) (hu : 0 ≤ u) : |HW.etaStar u| ≤ 250 * u := by
  obtain ⟨h0, h1⟩ := etaStar_bounds u hu
  rw [abs_of_nonneg h0]
  exact h1

end Principia.Common.TernaryGoldbach.WS
