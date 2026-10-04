/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TrompaisPoissonLog

set_option autoImplicit false

/-!
# `MPTC.EtaHatLBound` (`eq:puella`'s third part), PROVED from `MPTC.CameloSup`

The previous round recorded `EtaHatLBound` as true numerically but not reachable from Helfgott's
`η₂` grid. It IS reachable, by linearity in `L = log ρ`:

  `g_ρ = log(ρt)η₂(t) = L·η₂ + h`, `h(t) = log t·η₂(t)`, so `(2πu)²ĝ_ρ = L·a + b` with
  `a = (2πu)²η̂₂(u)`, `b = (2πu)²ĥ(u)`.

Write `L·a + b = (L − L₀)·a + (L₀·a + b)`, `L₀ = log 4`. Then `|a| ≤ c₀` (`EtaHatBound`, i.e.
`CameloSup`) and the single case `ρ = 4` (`|L₀a + b| ≤ c₀L₀`) give `|La + b| ≤ c₀L` for every
`ρ ≥ 4`. The case `ρ = 4` has a wide margin and needs no computation: by two integrations by
parts (`gl4_bound`), `|(2πu)²ĝ₄(u)| ≤ 24 log 2 + 24 ≈ 40.64 < c₀ log 4 ≈ 43.70` (the `φ'` jumps of
`g₄` are `16 log 2`, `0`, `8 log 2`, and `|φ''| ≤ 8/t²` on both pieces).
-/

namespace Principia.Common.TernaryGoldbach.MPTE

open Principia.Common.Goldbach MeasureTheory Set
open Principia.Common.TernaryGoldbach.MPTC Principia.Common.TernaryGoldbach.MPTI
  Principia.Common.TernaryGoldbach.MPTP Principia.Common.TernaryGoldbach.MPTL
  Principia.Common.TernaryGoldbach.MPc

/-- A continuous `g` vanishing off `(0, 1)` makes `g(t)e(−tu)` integrable. -/
theorem integrable_g (g : ℝ → ℝ) (hg : Continuous g) (h0 : ∀ t, t ≤ 0 → g t = 0)
    (h1 : ∀ t, 1 ≤ t → g t = 0) (u : ℝ) :
    Integrable fun t : ℝ => ((g t : ℝ) : ℂ) * e (-(t * u)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · refine (Complex.continuous_ofReal.comp hg).mul ?_
    have := continuous_eE u
    unfold eE at this
    exact this
  · refine HasCompactSupport.intro (K := Icc 0 1) isCompact_Icc fun t ht => ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · rw [h0 t h.le]; simp
    · rw [h1 t h.le]; simp

/-- **Linearity in `log ρ`**: `ĝ_ρ(u) = log ρ·η̂₂(u) + ĝ₁(u)` for `ρ > 0`. -/
theorem gl_hat_lin (ρ : ℝ) (hρ : 0 < ρ) (u : ℝ) :
    gHat (gl ρ) u = (Real.log ρ : ℂ) * etaHat u + gHat (gl 1) u := by
  have i1 := integrable_g HW.eta2 MPT.eta2_cont (fun t ht => MPT.eta2_le_quarter (by linarith))
    (fun t ht => HW.eta2_of_one_le ht) u
  have i2 := integrable_g (gl 1) (gl_cont 1 one_pos)
    (fun t ht => by unfold gl; rw [MPT.eta2_le_quarter (by linarith), mul_zero])
    (fun t ht => by unfold gl; rw [HW.eta2_of_one_le ht, mul_zero]) u
  unfold gHat etaHat
  rw [← integral_const_mul, ← integral_add (i1.const_mul _) i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [gl, one_mul]
  rcases le_or_gt t 0 with h | h
  · rw [HW.eta2_of_nonpos h]
    simp
  · rw [Real.log_mul hρ.ne' h.ne']
    push_cast
    ring

/-- `∫_p^q 8/t² = 8/p − 8/q` for `0 < p ≤ q`. -/
theorem int_inv_sq (p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) :
    ∫ x in p..q, 8 / x ^ 2 = 8 / p - 8 / q := by
  have hd : ∀ x ∈ uIcc p q, HasDerivAt (fun y : ℝ => -8 / y) (8 / x ^ 2) x := by
    intro x hx
    rw [uIcc_of_le hpq] at hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le hp hx.1).ne'
    have := (hasDerivAt_const x (-8 : ℝ)).div (hasDerivAt_id' x) hx0
    refine this.congr_deriv ?_
    field_simp
    ring
  have hi : IntervalIntegrable (fun x : ℝ => 8 / x ^ 2) volume p q := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hpq]
    exact continuousOn_const.div (continuousOn_pow 2) fun x hx =>
      pow_ne_zero 2 (lt_of_lt_of_le hp hx.1).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  ring

/-- `‖∫_p^q φ(x)E(x)‖ ≤ 8/p − 8/q` when `|φ(x)| ≤ 8/x²` on `[p, q]`. -/
theorem piece_le (φ : ℝ → ℝ) (p q u : ℝ) (hp : 0 < p) (hpq : p ≤ q)
    (hφ : ContinuousOn φ (Icc p q)) (hb : ∀ x ∈ Icc p q, |φ x| ≤ 8 / x ^ 2) :
    ‖∫ x in p..q, (φ x : ℂ) * eE u x‖ ≤ 8 / p - 8 / q := by
  refine (intervalIntegral.norm_integral_le_integral_norm hpq).trans ?_
  rw [← int_inv_sq p q hp hpq]
  refine intervalIntegral.integral_mono_on hpq ?_ ?_ fun x hx => ?_
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hpq]
    exact ((Complex.continuous_ofReal.comp_continuousOn hφ).mul
      (continuous_eE u).continuousOn).norm
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hpq]
    exact continuousOn_const.div (continuousOn_pow 2) fun y hy =>
      pow_ne_zero 2 (lt_of_lt_of_le hp hy.1).ne'
  · rw [norm_mul, MPTS.norm_eE, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hb x hx

/-- **The case `ρ = 4`**: `|(2πu)²ĝ₄(u)| ≤ 24 log 2 + 24`. -/
theorem gl4_bound (u : ℝ) :
    ‖(((2 * Real.pi * u) ^ 2 : ℝ) : ℂ) * gHat (gl 4) u‖ ≤ 24 * Real.log 2 + 24 := by
  set l2 := Real.log 2 with hl2
  have hL : Real.log 4 = 2 * l2 := by
    rw [hl2, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl2p : 0 < l2 := Real.log_pos (by norm_num)
  have hl2l : l2 < 1 := by
    have := Real.log_two_lt_d9; rw [hl2]; linarith
  have pos : ∀ x ∈ Icc (1 / 4 : ℝ) 1, 0 < x := fun x hx => by linarith [hx.1]
  set L := Real.log 4
  have IL := ibp2 (fun t => (L + Real.log t) * (4 * (2 * l2 + Real.log t)))
    (fun t => 4 * (2 * l2 + L + 2 * Real.log t) / t)
    (fun t => 4 * (2 - 2 * l2 - L - 2 * Real.log t) / t ^ 2) (1 / 4) (1 / 2) u (by norm_num)
    (fun t ht => by
      have h0 : t ≠ 0 := (pos t ⟨ht.1, by linarith [ht.2]⟩).ne'
      have := ((Real.hasDerivAt_log h0).const_add L).mul
        (((Real.hasDerivAt_log h0).const_add (2 * l2)).const_mul 4)
      refine this.congr_deriv ?_
      field_simp
      ring)
    (fun t ht => by
      have h0 : t ≠ 0 := (pos t ⟨ht.1, by linarith [ht.2]⟩).ne'
      have := ((((Real.hasDerivAt_log h0).const_mul 2).const_add (2 * l2 + L)).const_mul 4).div
        (hasDerivAt_id' t) h0
      refine this.congr_deriv ?_
      field_simp
      ring)
    (by
      refine ContinuousOn.div (continuousOn_const.mul (continuousOn_const.sub
        (continuousOn_const.mul (Real.continuousOn_log.mono fun x hx => ?_))))
        (continuousOn_pow 2) fun x hx => ?_
      · exact (pos x ⟨hx.1, by linarith [hx.2]⟩).ne'
      · exact pow_ne_zero 2 (pos x ⟨hx.1, by linarith [hx.2]⟩).ne')
  have IR := ibp2 (fun t => (L + Real.log t) * (-4 * Real.log t))
    (fun t => -4 * (L + 2 * Real.log t) / t)
    (fun t => 4 * (L + 2 * Real.log t - 2) / t ^ 2) (1 / 2) 1 u (by norm_num)
    (fun t ht => by
      have h0 : t ≠ 0 := (pos t ⟨by linarith [ht.1], ht.2⟩).ne'
      have := ((Real.hasDerivAt_log h0).const_add L).mul
        ((Real.hasDerivAt_log h0).const_mul (-4))
      refine this.congr_deriv ?_
      field_simp
      ring)
    (fun t ht => by
      have h0 : t ≠ 0 := (pos t ⟨by linarith [ht.1], ht.2⟩).ne'
      have := ((((Real.hasDerivAt_log h0).const_mul 2).const_add L).const_mul (-4)).div
        (hasDerivAt_id' t) h0
      refine this.congr_deriv ?_
      field_simp
      ring)
    (by
      refine ContinuousOn.div (continuousOn_const.mul ((continuousOn_const.add
        (continuousOn_const.mul (Real.continuousOn_log.mono fun x hx => ?_))).sub
        continuousOn_const)) (continuousOn_pow 2) fun x hx => ?_
      · exact (pos x ⟨by linarith [hx.1], hx.2⟩).ne'
      · exact pow_ne_zero 2 (pos x ⟨by linarith [hx.1], hx.2⟩).ne')
  have lq := MPTI.log_quarter
  have lh := EN.log_half
  rw [← hl2] at lq lh
  have hid : (((2 * Real.pi * u) ^ 2 : ℝ) : ℂ) * gHat (gl 4) u =
      (((16 * L - 16 * l2 : ℝ) : ℂ) * eE u (1 / 2) - ((16 * (L - 2 * l2) : ℝ) : ℂ) * eE u (1 / 4) +
        ((-4 * L : ℝ) : ℂ) * eE u 1) -
      (∫ t in (1 / 4 : ℝ)..(1 / 2), ((4 * (2 - 2 * l2 - L - 2 * Real.log t) / t ^ 2 : ℝ) : ℂ) *
        eE u t) -
      ∫ t in (1 / 2 : ℝ)..1, ((4 * (L + 2 * Real.log t - 2) / t ^ 2 : ℝ) : ℂ) * eE u t := by
    rw [gl_hat_split 4 (by norm_num) u, mul_add, IL, IR]
    simp only [Real.log_one, lq, lh]
    push_cast
    ring
  rw [hid]
  have cL : ContinuousOn (fun t : ℝ => 4 * (2 - 2 * l2 - L - 2 * Real.log t) / t ^ 2)
      (Icc (1 / 4) (1 / 2)) := by
    refine ContinuousOn.div (continuousOn_const.mul (continuousOn_const.sub
      (continuousOn_const.mul (Real.continuousOn_log.mono fun x hx => ?_))))
      (continuousOn_pow 2) fun x hx => ?_
    · exact (pos x ⟨hx.1, by linarith [hx.2]⟩).ne'
    · exact pow_ne_zero 2 (pos x ⟨hx.1, by linarith [hx.2]⟩).ne'
  have cR : ContinuousOn (fun t : ℝ => 4 * (L + 2 * Real.log t - 2) / t ^ 2) (Icc (1 / 2) 1) := by
    refine ContinuousOn.div (continuousOn_const.mul ((continuousOn_const.add
      (continuousOn_const.mul (Real.continuousOn_log.mono fun x hx => ?_))).sub
      continuousOn_const)) (continuousOn_pow 2) fun x hx => ?_
    · exact (pos x ⟨by linarith [hx.1], hx.2⟩).ne'
    · exact pow_ne_zero 2 (pos x ⟨by linarith [hx.1], hx.2⟩).ne'
  have PL := piece_le _ (1 / 4) (1 / 2) u (by norm_num) (by norm_num) cL fun x hx => by
    have hx0 : 0 < x := by linarith [hx.1]
    have h1 : Real.log x ≤ -l2 := by
      have := Real.log_le_log hx0 hx.2; rw [lh] at this; exact this
    have h2 : -(2 * l2) ≤ Real.log x := by
      have := Real.log_le_log (by norm_num) hx.1; rw [lq] at this; exact this
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2)]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rw [hL, abs_le]
    constructor <;> nlinarith
  have PR := piece_le _ (1 / 2) 1 u (by norm_num) (by norm_num) cR fun x hx => by
    have hx0 : 0 < x := by linarith [hx.1]
    have h1 : Real.log x ≤ 0 := Real.log_nonpos hx0.le hx.2
    have h2 : -l2 ≤ Real.log x := by
      have := Real.log_le_log (by norm_num) hx.1; rw [lh] at this; exact this
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2)]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rw [hL, abs_le]
    constructor <;> nlinarith
  have e1 : ‖((16 * L - 16 * l2 : ℝ) : ℂ) * eE u (1 / 2)‖ = 16 * l2 := by
    rw [norm_mul, MPTS.norm_eE, mul_one, Complex.norm_real, Real.norm_eq_abs, hL,
      show 16 * (2 * l2) - 16 * l2 = 16 * l2 by ring, abs_of_pos (by positivity)]
  have e2 : ‖((16 * (L - 2 * l2) : ℝ) : ℂ) * eE u (1 / 4)‖ = 0 := by
    rw [hL, sub_self, mul_zero]; simp
  have e3 : ‖((-4 * L : ℝ) : ℂ) * eE u 1‖ = 8 * l2 := by
    rw [norm_mul, MPTS.norm_eE, mul_one, Complex.norm_real, Real.norm_eq_abs, hL,
      show -4 * (2 * l2) = -(8 * l2) by ring, abs_neg, abs_of_pos (by positivity)]
  calc _ ≤ ‖((16 * L - 16 * l2 : ℝ) : ℂ) * eE u (1 / 2) -
          ((16 * (L - 2 * l2) : ℝ) : ℂ) * eE u (1 / 4) + ((-4 * L : ℝ) : ℂ) * eE u 1‖ +
        ‖∫ t in (1 / 4 : ℝ)..(1 / 2), ((4 * (2 - 2 * l2 - L - 2 * Real.log t) / t ^ 2 : ℝ) : ℂ) *
          eE u t‖ +
        ‖∫ t in (1 / 2 : ℝ)..1, ((4 * (L + 2 * Real.log t - 2) / t ^ 2 : ℝ) : ℂ) * eE u t‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (16 * l2 + 0 + 8 * l2) + (8 / (1 / 4) - 8 / (1 / 2)) + (8 / (1 / 2) - 8 / 1) := by
        refine add_le_add (add_le_add ?_ PL) PR
        refine (norm_add_le _ _).trans ((add_le_add (norm_sub_le _ _) le_rfl).trans (le_of_eq ?_))
        rw [e1, e2, e3]
    _ = 24 * l2 + 24 := by norm_num; ring

/-- **`MPTC.EtaHatLBound` from `MPTC.EtaHatBound`, PROVED.** -/
theorem etaHatLBound_of (hB : EtaHatBound) : EtaHatLBound := by
  intro ρ hρ u
  have hρ0 : 0 < ρ := by linarith
  set w : ℝ := (2 * Real.pi * u) ^ 2 with hw
  have hw0 : 0 ≤ w := by positivity
  set a : ℂ := (w : ℂ) * etaHat u
  set b : ℂ := (w : ℂ) * gHat (gl 1) u
  have ha : ‖a‖ ≤ c0 := by
    simp only [a, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
    rw [mul_comm]; exact hB u
  have h4 : ‖(Real.log 4 : ℂ) * a + b‖ ≤ c0 * Real.log 4 := by
    have := gl4_bound u
    rw [gl_hat_lin 4 (by norm_num) u] at this
    have e : (w : ℂ) * ((Real.log 4 : ℂ) * etaHat u + gHat (gl 1) u) =
        (Real.log 4 : ℂ) * a + b := by simp only [a, b]; ring
    rw [← hw, e] at this
    have hl2 : Real.log 2 > 0.6931471803 := Real.log_two_gt_d9
    have hL : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    refine this.trans ?_
    unfold c0
    rw [hL]
    linarith
  have hL4 : Real.log 4 ≤ Real.log ρ := Real.log_le_log (by norm_num) hρ
  have hL40 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have e : (w : ℂ) * etaHatL ρ u = ((Real.log ρ - Real.log 4 : ℝ) : ℂ) * a +
      ((Real.log 4 : ℂ) * a + b) := by
    change (w : ℂ) * gHat (gl ρ) u = _
    rw [gl_hat_lin ρ hρ0 u]
    simp only [a, b]
    push_cast
    ring
  have hn := congrArg norm e
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0] at hn
  rw [mul_comm, hn]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have := mul_le_mul_of_nonneg_left ha (by linarith : 0 ≤ Real.log ρ - Real.log 4)
  nlinarith

/-- **`MPT.TrompaisLogC` from the two cited computer checks alone, PROVED.** -/
theorem trompaisLogC_of_cited (hG : HC.CameloGridCited) (hW : HC.WollustCited) :
    MPT.TrompaisLogC :=
  trompaisLogC_of_L (etaHatLBound_of (etaHatBound_of etaHatIBP_holds (MPTS.cameloSup_of hG hW)))

/-- **`MPB1.TrompaisLogEta2` from the two cited computer checks alone, PROVED.** -/
theorem trompaisLogEta2_cited (hG : HC.CameloGridCited) (hW : HC.WollustCited) :
    MPB1.TrompaisLogEta2 :=
  MPT.trompaisLogEta2_of (trompaisLogC_of_cited hG hW)

end Principia.Common.TernaryGoldbach.MPTE
