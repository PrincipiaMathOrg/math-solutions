/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.Bosta2Main

set_option autoImplicit false

/-!
# `MPTC.PoissonOddLog`, PROVED; `MPT.TrompaisLogC` from `MPTC.EtaHatLBound` alone

`g_ρ(t) = log(ρt)η₂(t)` is continuous, vanishes off `(1/4, 1)`, and on the two pieces is
`φ_L = (log ρ + log t)·4(2 log 2 + log t)` and `φ_R = −4(log ρ + log t) log t`. Two integrations
by parts per piece (`MPTI.ibp2`) give `(2πu)²ĝ_ρ(u)` as the `φ'`-jumps minus `∫φ''E` (the
`φ`-boundary terms cancel: `φ_L(1/4) = φ_R(1) = 0`, `φ_L(1/2) = φ_R(1/2)`), whence the crude
`|ĝ_ρ(u)|(2πu)² ≤ 1000(1 + |log ρ|)` (`gl_hat_le`) — all `MPTP.poisson_odd` needs.
-/

namespace Principia.Common.TernaryGoldbach.MPTL

open Principia.Common.Goldbach MeasureTheory Set
open Principia.Common.TernaryGoldbach.MPTC Principia.Common.TernaryGoldbach.MPTI
  Principia.Common.TernaryGoldbach.MPTP Principia.Common.TernaryGoldbach.MPB1

/-- `g_ρ(t) = log(ρt)η₂(t)`. -/
noncomputable def gl (ρ : ℝ) (t : ℝ) : ℝ := Real.log (ρ * t) * HW.eta2 t

/-- `g_ρ` is continuous (`η₂` vanishes near `t ≤ 0`, where `log` jumps). -/
theorem gl_cont (ρ : ℝ) (hρ : 0 < ρ) : Continuous (gl ρ) := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_or_ge t (1 / 4) with h | h
  · have hev : gl ρ =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with s hs
      unfold gl
      rw [MPT.eta2_le_quarter (le_of_lt hs), mul_zero]
    exact continuousAt_const.congr hev.symm
  · have ht : 0 < t := by linarith
    unfold gl
    refine ContinuousAt.mul ?_ (MPT.eta2_cont.continuousAt)
    exact (Real.continuousAt_log (by positivity)).comp (continuousAt_const.mul continuousAt_id)

/-- `|log t| ≤ 2 log 2` on `[1/4, 1]`. -/
theorem abs_log_le (t : ℝ) (h1 : 1 / 4 ≤ t) (h2 : t ≤ 1) : |Real.log t| ≤ 2 * Real.log 2 := by
  have ht : 0 < t := by linarith
  rw [abs_of_nonpos (Real.log_nonpos ht.le h2)]
  have := Real.log_le_log (by norm_num) h1
  rw [MPTI.log_quarter] at this
  linarith

/-- **`ĝ_ρ(u) = ∫_{1/4}^{1/2} φ_L E + ∫_{1/2}^1 φ_R E`.** -/
theorem gl_hat_split (ρ : ℝ) (hρ : 0 < ρ) (u : ℝ) :
    gHat (gl ρ) u = (∫ t in (1 / 4 : ℝ)..(1 / 2),
        (((Real.log ρ + Real.log t) * (4 * (2 * Real.log 2 + Real.log t)) : ℝ) : ℂ) * eE u t) +
      ∫ t in (1 / 2 : ℝ)..1, (((Real.log ρ + Real.log t) * (-4 * Real.log t) : ℝ) : ℂ) *
        eE u t := by
  have hc : Continuous fun t => ((gl ρ t : ℝ) : ℂ) * eE u t :=
    (Complex.continuous_ofReal.comp (gl_cont ρ hρ)).mul (continuous_eE u)
  have h0 : gHat (gl ρ) u = ∫ t in (1 / 4 : ℝ)..1, ((gl ρ t : ℝ) : ℂ) * eE u t := by
    unfold gHat
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
    rw [mem_Ioc, not_and_or, not_lt, not_le] at ht
    unfold gl
    rcases ht with h | h
    · simp [MPT.eta2_le_quarter h]
    · simp [HW.eta2_of_one_le h.le]
  rw [h0, ← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  congr 1
  · refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    simp only [gl]
    rw [EN.eta2_left ht.1 ht.2, Real.log_mul hρ.ne' ht0.ne']
  · refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    simp only [gl]
    rw [EN.eta2_right ht.1 ht.2, Real.log_mul hρ.ne' ht0.ne']

/-- A pointwise bound `|φ''(x)E(x)| ≤ 64·K` from `|x²φ''(x)| ≤ 4K` on a piece of `[1/4, 1]`. -/
theorem piece_int_le (φ2 : ℝ → ℝ) (p q u K : ℝ) (hpq : p ≤ q) (hp : 1 / 4 ≤ p)
    (hb : ∀ x ∈ Icc p q, |φ2 x| * x ^ 2 ≤ 4 * K) :
    ‖∫ x in p..q, (φ2 x : ℂ) * eE u x‖ ≤ 64 * K * (q - p) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := p) (b := q) (C := 64 * K)
    (f := fun x => (φ2 x : ℂ) * eE u x) fun x hx => by
      rw [uIoc_of_le hpq] at hx
      have hx' : x ∈ Icc p q := ⟨hx.1.le, hx.2⟩
      have hx0 : 1 / 4 ≤ x := hp.trans hx'.1
      have hsq : 1 / 16 ≤ x ^ 2 := by nlinarith
      rw [norm_mul, MPTS.norm_eE, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have := hb x hx'
      have hK : 0 ≤ K := by nlinarith [abs_nonneg (φ2 x), sq_nonneg x]
      nlinarith [abs_nonneg (φ2 x)]
  rw [abs_of_nonneg (by linarith : 0 ≤ q - p)] at h
  exact h

/-- **`|ĝ_ρ(u)|(2πu)² ≤ 1000(1 + |log ρ|)`.** -/
theorem gl_hat_le (ρ : ℝ) (hρ : 0 < ρ) (u : ℝ) :
    ‖gHat (gl ρ) u‖ * (2 * Real.pi * u) ^ 2 ≤ 1000 * (1 + |Real.log ρ|) := by
  set L := Real.log ρ with hL
  set l2 := Real.log 2 with hl2
  have hl2p : 0 < l2 := Real.log_pos (by norm_num)
  have hl2l : l2 < 1 := by
    have := Real.log_two_lt_d9; rw [hl2]; linarith
  have pos : ∀ x ∈ Icc (1 / 4 : ℝ) 1, 0 < x := fun x hx => by linarith [hx.1]
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
        (continuousOn_const.mul (Real.continuousOn_log.mono fun x hx => ?_)))) (continuousOn_pow 2)
        fun x hx => ?_
      · exact (pos x ⟨hx.1, by linarith [hx.2]⟩).ne'
      · exact pow_ne_zero 2 (pos x ⟨hx.1, by linarith [hx.2]⟩).ne')
  have IR := ibp2 (fun t => (L + Real.log t) * (-4 * Real.log t))
    (fun t => -4 * (L + 2 * Real.log t) / t)
    (fun t => 4 * (L + 2 * Real.log t - 2) / t ^ 2) (1 / 2) 1 u (by norm_num)
    (fun t ht => by
      have h0 : t ≠ 0 := (pos t ⟨by linarith [ht.1], ht.2⟩).ne'
      have := ((Real.hasDerivAt_log h0).const_add L).mul ((Real.hasDerivAt_log h0).const_mul (-4))
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
  -- the identity
  have hid : (((2 * Real.pi * u) ^ 2 : ℝ) : ℂ) * gHat (gl ρ) u =
      (((16 * L - 16 * l2 : ℝ) : ℂ) * eE u (1 / 2) - ((16 * (L - 2 * l2) : ℝ) : ℂ) * eE u (1 / 4) +
        ((-4 * L : ℝ) : ℂ) * eE u 1) -
      (∫ t in (1 / 4 : ℝ)..(1 / 2), ((4 * (2 - 2 * l2 - L - 2 * Real.log t) / t ^ 2 : ℝ) : ℂ) *
        eE u t) -
      ∫ t in (1 / 2 : ℝ)..1, ((4 * (L + 2 * Real.log t - 2) / t ^ 2 : ℝ) : ℂ) * eE u t := by
    rw [gl_hat_split ρ hρ u, mul_add, IL, IR]
    simp only [Real.log_one, lq, lh]
    push_cast
    ring
  have hn := congrArg norm hid
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hn
  rw [mul_comm, hn]
  have b1 : ∀ x ∈ Icc (1 / 4 : ℝ) (1 / 2),
      |4 * (2 - 2 * l2 - L - 2 * Real.log x) / x ^ 2| * x ^ 2 ≤ 4 * (8 + |L|) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hlx := abs_log_le x hx.1 (by linarith [hx.2])
    rw [← hl2] at hlx
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2), div_mul_cancel₀ _ (by positivity),
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have : |2 - 2 * l2 - L - 2 * Real.log x| ≤ 2 + 2 * l2 + |L| + 2 * |Real.log x| := by
      have h1 := abs_sub (2 - 2 * l2 - L) (2 * Real.log x)
      have h2 := abs_sub (2 - 2 * l2) L
      have h3 := abs_sub (2 : ℝ) (2 * l2)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hl2p] at h3
      linarith
    nlinarith
  have b2 : ∀ x ∈ Icc (1 / 2 : ℝ) 1,
      |4 * (L + 2 * Real.log x - 2) / x ^ 2| * x ^ 2 ≤ 4 * (6 + |L|) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hlx := abs_log_le x (by linarith [hx.1]) hx.2
    rw [← hl2] at hlx
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2), div_mul_cancel₀ _ (by positivity),
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have : |L + 2 * Real.log x - 2| ≤ |L| + 2 * |Real.log x| + 2 := by
      have h1 := abs_sub (L + 2 * Real.log x) 2
      have h2 := abs_add_le L (2 * Real.log x)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
      norm_num at h1
      linarith
    nlinarith
  have PL := piece_int_le _ (1 / 4) (1 / 2) u (8 + |L|) (by norm_num) le_rfl b1
  have PR := piece_int_le _ (1 / 2) 1 u (6 + |L|) (by norm_num) (by norm_num) b2
  have e1 : ‖((16 * L - 16 * l2 : ℝ) : ℂ) * eE u (1 / 2)‖ ≤ 16 * |L| + 16 := by
    rw [norm_mul, MPTS.norm_eE, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have := abs_sub (16 * L) (16 * l2)
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16), abs_of_pos hl2p] at this
    linarith
  have e2 : ‖((16 * (L - 2 * l2) : ℝ) : ℂ) * eE u (1 / 4)‖ ≤ 16 * |L| + 32 := by
    rw [norm_mul, MPTS.norm_eE, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 16)]
    have := abs_sub L (2 * l2)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hl2p] at this
    linarith
  have e3 : ‖((-4 * L : ℝ) : ℂ) * eE u 1‖ ≤ 4 * |L| := by
    rw [norm_mul, MPTS.norm_eE, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    norm_num
  have hL0 := abs_nonneg L
  calc _ ≤ ‖((16 * L - 16 * l2 : ℝ) : ℂ) * eE u (1 / 2) -
          ((16 * (L - 2 * l2) : ℝ) : ℂ) * eE u (1 / 4) + ((-4 * L : ℝ) : ℂ) * eE u 1‖ +
        ‖∫ t in (1 / 4 : ℝ)..(1 / 2), ((4 * (2 - 2 * l2 - L - 2 * Real.log t) / t ^ 2 : ℝ) : ℂ) *
          eE u t‖ +
        ‖∫ t in (1 / 2 : ℝ)..1, ((4 * (L + 2 * Real.log t - 2) / t ^ 2 : ℝ) : ℂ) * eE u t‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (16 * |L| + 16 + (16 * |L| + 32) + 4 * |L|) + 64 * (8 + |L|) * (1 / 2 - 1 / 4) +
        64 * (6 + |L|) * (1 - 1 / 2) := by
        refine add_le_add (add_le_add ?_ PL) PR
        exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add e1 e2)) e3)
    _ ≤ 1000 * (1 + |L|) := by nlinarith

/-- **`MPTC.PoissonOddLog`, PROVED.** -/
theorem poissonOddLog_holds : PoissonOddLog := by
  intro x γ hx d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hρ : 0 < x / d := by positivity
  have hP := poisson_odd (gl (x / d)) (gl_cont _ hρ)
    (fun t ht => by unfold gl; rw [MPT.eta2_le_quarter (by linarith), mul_zero])
    (fun t ht => by unfold gl; rw [HW.eta2_of_one_le ht, mul_zero]) _ (gl_hat_le _ hρ)
    (x / d) (d * γ) hρ
  have hv : tlo x γ d = ∑ m ∈ Finset.Ioc 0 ⌊x / d⌋₊,
      ((MT.fOdd m : ℝ) : ℂ) * (((gl (x / d) ((m : ℝ) / (x / d)) : ℝ) : ℂ) *
        e ((m : ℝ) * (d * γ))) := by
    unfold tlo
    rw [Nat.floor_div_natCast]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold MT.wt gl
    rw [show x / d * ((m : ℝ) / (x / d)) = m by field_simp]
    have e1 : (((d * m : ℕ) : ℝ) / x) = (m : ℝ) / (x / d) := by push_cast; field_simp
    have e2 : ((d * m : ℕ) : ℝ) * γ = (m : ℝ) * (d * γ) := by push_cast; ring
    rw [e1, e2]
    push_cast
    ring
  rw [hv]
  exact hP

/-- **`MPT.TrompaisLogC` from `MPTC.EtaHatLBound` alone, PROVED.** -/
theorem trompaisLogC_of_L (hB : EtaHatLBound) : MPT.TrompaisLogC :=
  trompaisLogC_of poissonOddLog_holds hB

end Principia.Common.TernaryGoldbach.MPTL
