/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TrompaisCSpine

set_option autoImplicit false

/-!
# `MPTC.EtaHatIBP`, PROVED: `(2πu)²η̂₂(u) = −(4g(u) + f̂(u))`

Two integrations by parts on each of `[1/4, 1/2]` (`η₂ = 4(2 log 2 + log t)`) and `[1/2, 1]`
(`η₂ = −4 log t`), done without dividing by `u`: with `E(t) = e(−tu)` and
`G = φ'E + 2πiu·φE`, one has `G' = φ''E + (2πu)²φE` (`ibp2`). The `φ`-boundary terms cancel
(`φ(1/4) = φ(1) = 0`, `φ` continuous at `1/2`), the `φ'`-boundary terms are
`16E(1/2) − 16E(1/4) − 4E(1) = −4g(u)`, and `∫φ''E = f̂(u)` with Helfgott's `f` (`HC.cameloF`).
-/

namespace Principia.Common.TernaryGoldbach.MPTI

open Principia.Common.Goldbach MeasureTheory Set
open Principia.Common.TernaryGoldbach.MPTC

/-- `E(t) = e(−tu)`. -/
noncomputable def eE (u t : ℝ) : ℂ := e (-(t * u))

/-- `E' = −2πiu·E`. -/
theorem hasDerivAt_eE (u t : ℝ) :
    HasDerivAt (eE u) (-(2 * Real.pi * Complex.I * u) * eE u t) t := by
  have h1 : HasDerivAt (fun s : ℝ => -(s * u)) (-u) t := by
    have h := ((hasDerivAt_id' t).mul_const u).neg
    rw [one_mul] at h
    exact h
  have h2 := (h1.ofReal_comp).const_mul (2 * Real.pi * Complex.I)
  have h3 := h2.cexp
  unfold eE e
  convert h3 using 1
  push_cast
  ring

/-- `E` is continuous. -/
theorem continuous_eE (u : ℝ) : Continuous (eE u) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_eE u t).continuousAt

/-- **Two integrations by parts, without dividing by `u`**: for `φ` twice differentiable on
`[a, b]` with `φ''` continuous there, `(2πu)²∫_a^b φE = G(b) − G(a) − ∫_a^b φ''E`,
`G = φ'E + 2πiu·φE`. -/
theorem ibp2 (φ φ1 φ2 : ℝ → ℝ) (a b u : ℝ) (hab : a ≤ b)
    (h1 : ∀ t ∈ Icc a b, HasDerivAt φ (φ1 t) t) (h2 : ∀ t ∈ Icc a b, HasDerivAt φ1 (φ2 t) t)
    (hc : ContinuousOn φ2 (Icc a b)) :
    (((2 * Real.pi * u) ^ 2 : ℝ) : ℂ) * ∫ t in a..b, (φ t : ℂ) * eE u t =
      ((φ1 b : ℂ) * eE u b + 2 * Real.pi * Complex.I * u * ((φ b : ℂ) * eE u b)) -
        ((φ1 a : ℂ) * eE u a + 2 * Real.pi * Complex.I * u * ((φ a : ℂ) * eE u a)) -
          ∫ t in a..b, (φ2 t : ℂ) * eE u t := by
  have hφc : ContinuousOn φ (Icc a b) := fun t ht => (h1 t ht).continuousAt.continuousWithinAt
  have hEc := continuous_eE u
  have i1 : IntervalIntegrable (fun t => (φ t : ℂ) * eE u t) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    exact (Complex.continuous_ofReal.comp_continuousOn hφc).mul hEc.continuousOn
  have i2 : IntervalIntegrable (fun t => (φ2 t : ℂ) * eE u t) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    exact (Complex.continuous_ofReal.comp_continuousOn hc).mul hEc.continuousOn
  have hG : ∀ t ∈ uIcc a b, HasDerivAt
      (fun s => (φ1 s : ℂ) * eE u s + 2 * Real.pi * Complex.I * u * ((φ s : ℂ) * eE u s))
      ((φ2 t : ℂ) * eE u t + (((2 * Real.pi * u) ^ 2 : ℝ) : ℂ) * ((φ t : ℂ) * eE u t)) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have d1 := (h1 t ht).ofReal_comp
    have d2 := (h2 t ht).ofReal_comp
    have dE := hasDerivAt_eE u t
    have := (d2.mul dE).add (((d1.mul dE).const_mul (2 * Real.pi * Complex.I * u)))
    refine this.congr_deriv ?_
    push_cast
    linear_combination (-(4 : ℂ) * (Real.pi : ℂ) ^ 2 * (u : ℂ) ^ 2 * (φ t : ℂ) * eE u t) *
      Complex.I_sq
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hG (i2.add (i1.const_mul _))
  rw [intervalIntegral.integral_add i2 (i1.const_mul _), intervalIntegral.integral_const_mul]
    at hint
  linear_combination hint

/-- `log(1/4) = −2 log 2`. -/
theorem log_quarter : Real.log (1 / 4) = -(2 * Real.log 2) := by
  rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

/-- `η̂₂(u) = ∫_{1/4}^{1/2} 4(2 log 2 + log t)E + ∫_{1/2}^1 (−4 log t)E`. -/
theorem etaHat_split (u : ℝ) :
    etaHat u = (∫ t in (1 / 4 : ℝ)..(1 / 2),
        ((4 * (2 * Real.log 2 + Real.log t) : ℝ) : ℂ) * eE u t) +
      ∫ t in (1 / 2 : ℝ)..1, ((-4 * Real.log t : ℝ) : ℂ) * eE u t := by
  have hc : Continuous fun t => ((HW.eta2 t : ℝ) : ℂ) * eE u t :=
    (Complex.continuous_ofReal.comp MPT.eta2_cont).mul (continuous_eE u)
  have h0 : etaHat u = ∫ t in (1 / 4 : ℝ)..1, ((HW.eta2 t : ℝ) : ℂ) * eE u t := by
    unfold etaHat
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
    rw [mem_Ioc, not_and_or, not_lt, not_le] at ht
    rcases ht with h | h
    · simp [MPT.eta2_le_quarter h]
    · simp [HW.eta2_of_one_le h.le]
  rw [h0, ← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  congr 1
  · refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    rw [EN.eta2_left ht.1 ht.2]
  · refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    rw [EN.eta2_right ht.1 ht.2]

/-- `f̂(u) = ∫_{1/4}^{1/2} (−4/t²)E + ∫_{1/2}^1 (4/t²)E`. -/
theorem cameloFHat_split (u : ℝ) :
    HC.cameloFHat u = (∫ t in (1 / 4 : ℝ)..(1 / 2), ((-4 / t ^ 2 : ℝ) : ℂ) * eE u t) +
      ∫ t in (1 / 2 : ℝ)..1, ((4 / t ^ 2 : ℝ) : ℂ) * eE u t := by
  have cL : ContinuousOn (fun t : ℝ => ((-4 / t ^ 2 : ℝ) : ℂ) * eE u t) (uIcc (1 / 4) (1 / 2)) := by
    rw [uIcc_of_le (by norm_num)]
    refine (Complex.continuous_ofReal.comp_continuousOn ?_).mul (continuous_eE u).continuousOn
    exact continuousOn_const.div (continuousOn_pow 2) fun t ht => by
      have : (0 : ℝ) < t := by linarith [ht.1]
      positivity
  have cR : ContinuousOn (fun t : ℝ => ((4 / t ^ 2 : ℝ) : ℂ) * eE u t) (uIcc (1 / 2) 1) := by
    rw [uIcc_of_le (by norm_num)]
    refine (Complex.continuous_ofReal.comp_continuousOn ?_).mul (continuous_eE u).continuousOn
    exact continuousOn_const.div (continuousOn_pow 2) fun t ht => by
      have : (0 : ℝ) < t := by linarith [ht.1]
      positivity
  have eqL : EqOn (fun t : ℝ => ((-4 / t ^ 2 : ℝ) : ℂ) * eE u t)
      (fun t => (HC.cameloF t : ℂ) * e (-(t * u))) (uIoo (1 / 4) (1 / 2)) := by
    intro t ht
    rw [uIoo_of_le (by norm_num)] at ht
    simp only [HC.cameloF, eE]
    rw [if_pos ⟨ht.1.le, ht.2⟩]
  have eqR : EqOn (fun t : ℝ => ((4 / t ^ 2 : ℝ) : ℂ) * eE u t)
      (fun t => (HC.cameloF t : ℂ) * e (-(t * u))) (uIoo (1 / 2) 1) := by
    intro t ht
    rw [uIoo_of_le (by norm_num)] at ht
    simp only [HC.cameloF, eE]
    rw [if_neg (fun h => by linarith [h.2, ht.1]), if_pos ⟨ht.1.le, ht.2⟩]
  have iL := (cL.intervalIntegrable (μ := volume)).congr_uIoo eqL
  have iR := (cR.intervalIntegrable (μ := volume)).congr_uIoo eqR
  unfold HC.cameloFHat
  rw [← intervalIntegral.integral_add_adjacent_intervals iL iR,
    intervalIntegral.integral_congr_uIoo eqL, intervalIntegral.integral_congr_uIoo eqR]

/-- **`MPTC.EtaHatIBP`, PROVED**: `(2πu)²η̂₂(u) = −(4g(u) + f̂(u))` for every real `u`. -/
theorem etaHatIBP_holds : EtaHatIBP := by
  intro u
  have pos : ∀ t ∈ Icc (1 / 4 : ℝ) 1, 0 < t := fun t ht => by linarith [ht.1]
  have L := ibp2 (fun t => 4 * (2 * Real.log 2 + Real.log t)) (fun t => 4 / t)
    (fun t => -4 / t ^ 2) (1 / 4) (1 / 2) u (by norm_num)
    (fun t ht => by
      have h0 : t ≠ 0 := (pos t ⟨ht.1, by linarith [ht.2]⟩).ne'
      have := ((Real.hasDerivAt_log h0).const_add (2 * Real.log 2)).const_mul 4
      exact this.congr_deriv (by rw [div_eq_mul_inv]))
    (fun t ht => by
      have h0 : t ≠ 0 := (pos t ⟨ht.1, by linarith [ht.2]⟩).ne'
      have := (hasDerivAt_const t (4 : ℝ)).div (hasDerivAt_id' t) h0
      exact this.congr_deriv (by ring))
    (continuousOn_const.div (continuousOn_pow 2) fun t ht =>
      by have := pos t ⟨ht.1, by linarith [ht.2]⟩; positivity)
  have R := ibp2 (fun t => -4 * Real.log t) (fun t => -4 / t)
    (fun t => 4 / t ^ 2) (1 / 2) 1 u (by norm_num)
    (fun t ht => by
      have h0 : t ≠ 0 := (pos t ⟨by linarith [ht.1], ht.2⟩).ne'
      have := (Real.hasDerivAt_log h0).const_mul (-4)
      exact this.congr_deriv (by rw [div_eq_mul_inv]))
    (fun t ht => by
      have h0 : t ≠ 0 := (pos t ⟨by linarith [ht.1], ht.2⟩).ne'
      have := (hasDerivAt_const t (-4 : ℝ)).div (hasDerivAt_id' t) h0
      exact this.congr_deriv (by ring))
    (continuousOn_const.div (continuousOn_pow 2) fun t ht =>
      by have := pos t ⟨by linarith [ht.1], ht.2⟩; positivity)
  rw [etaHat_split, mul_add, L, R, cameloFHat_split]
  have l2 := EN.log_half
  have l4 := log_quarter
  simp only [Real.log_one, l2, l4]
  unfold HC.wollG eE
  have q1 : -((1 : ℝ) / 4 * u) = -u / 4 := by ring
  have q2 : -((1 : ℝ) / 2 * u) = -u / 2 := by ring
  have q3 : -((1 : ℝ) * u) = -u := by ring
  rw [q1, q2, q3]
  push_cast
  ring

end Principia.Common.TernaryGoldbach.MPTI
