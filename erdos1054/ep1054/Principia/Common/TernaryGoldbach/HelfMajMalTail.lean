/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajMoments

set_option autoImplicit false

/-!
# The tail integral of Prop 1.5 — `HM.MalTailInt` PROVED

`HM.malTailInt_holds : HM.MalTailInt`: for `x ≥ 10¹²`,
`∫_{450}^∞ fmal(x,t)·gw(1,t) dt ≤ 10⁻¹² log x`, `fmal(x,t) = 10(log x + 10)e^{−0.7(t−400)}`.

The weight grows at most exponentially slowly: `gw(1,t) ≤ 2·e^{0.1(t−450)}` on `t > 450`
(`log(t/2π) ≤ log(450/2π) + t/450 − 1`, `log(450/2π) ≤ 5`, `π > 3`, `1 + u ≤ eᵘ`), so the
integrand is at most `20(log x + 10)e^{235}e^{−0.6t}`, whose integral is
`20(log x + 10)e^{−35}/0.6 ≤ 2.14·10⁻¹⁴(log x + 10)` (`integral_exp_mul_Ioi`) — within the claimed
`10⁻¹² log x` by a factor `≈ 34` at `log x ≥ 27`.

`helfMajR_of_16`: `MR.HelfMajR η₊ (η₂ ∗_M φ)` from sixteen named links (`GarmolaDecr`,
`Eta2Moments`, `MalTailInt` discharged).
-/

namespace Principia.Common.TernaryGoldbach.HM

open MeasureTheory Set

/-- `gw(1,t) ≤ 2·e^{0.1(t−450)}` for `t ≥ 450`. -/
theorem gw_one_le {t : ℝ} (ht : 450 ≤ t) : gw 1 t ≤ 2 * Real.exp (0.1 * (t - 450)) := by
  have ht0 : 0 < t := by linarith
  have hpi := Real.pi_gt_three
  have hlog : Real.log (1 * t / (2 * Real.pi)) ≤ 5 + (t / 450 - 1) := by
    have e : 1 * t / (2 * Real.pi) = (450 / (2 * Real.pi)) * (t / 450) := by
      field_simp
    rw [e, Real.log_mul (by positivity) (by positivity)]
    have h1 : Real.log (450 / (2 * Real.pi)) ≤ 5 := by
      have h := log_le_nat 5 (y := 450 / (2 * Real.pi)) (by positivity) (by
        rw [div_le_iff₀ (by positivity)]
        nlinarith)
      push_cast at h
      exact h
    have h2 := Real.log_le_sub_one_of_pos (show 0 < t / 450 by positivity)
    linarith
  have hlog0 : 0 ≤ Real.log (1 * t / (2 * Real.pi)) :=
    Real.log_nonneg ((one_le_div (by positivity)).mpr (by linarith [Real.pi_lt_four]))
  have hmax : max (Real.log (1 * t / (2 * Real.pi)) / Real.pi) 0 ≤
      (5 + (t / 450 - 1)) / 3 := by
    rw [max_eq_left (div_nonneg hlog0 Real.pi_pos.le)]
    rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]
    nlinarith
  have hinv : 1 / (2 * t) ≤ 1 / 900 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hexp := Real.add_one_le_exp (0.1 * (t - 450))
  unfold gw
  nlinarith

/-- `e^{−35} ≤ 6.4·10⁻¹⁶`. -/
theorem exp_35 : Real.exp (-35) ≤ 6.4e-16 := by
  have e : (-35 : ℝ) = -(((35 : ℕ) : ℝ) + 0) := by norm_num
  rw [e]
  exact exp_neg_le 35 (by norm_num) (by norm_num)

/-- **`MalTailInt` PROVED.** -/
theorem malTailInt_holds : MalTailInt := by
  intro x hx
  have hℓ : 27 ≤ Real.log x := by
    have h := nat_le_log 27 (y := x) (le_trans (by norm_num) hx)
    push_cast at h
    exact h
  set K : ℝ := 20 * (Real.log x + 10) * Real.exp 235 with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ t ∈ Ioi (450 : ℝ), ENNReal.ofReal (fmal x t * gw 1 t) ≤
      ENNReal.ofReal (K * Real.exp (-0.6 * t)) := by
    intro t ht
    refine ENNReal.ofReal_le_ofReal ?_
    have hg := gw_one_le (le_of_lt ht)
    have hc : 0 ≤ 10 * (Real.log x + 10) * Real.exp (-0.7 * (t - 400)) := by positivity
    have e : K * Real.exp (-0.6 * t) =
        10 * (Real.log x + 10) * Real.exp (-0.7 * (t - 400)) *
          (2 * Real.exp (0.1 * (t - 450))) := by
      rw [hK]
      have e1 : Real.exp (-0.7 * (t - 400)) * Real.exp (0.1 * (t - 450)) =
          Real.exp 235 * Real.exp (-0.6 * t) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
      linear_combination (-20 * (Real.log x + 10)) * e1
    rw [e]
    unfold fmal
    exact mul_le_mul_of_nonneg_left hg hc
  have hint : IntegrableOn (fun t => K * Real.exp (-0.6 * t)) (Ioi 450) :=
    (integrableOn_exp_mul_Ioi (by norm_num) 450).const_mul K
  have hval : ∫ t in Ioi (450 : ℝ), K * Real.exp (-0.6 * t) = K * (Real.exp (-270) / 0.6) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num)]
    congr 1
    rw [show (-0.6 : ℝ) * 450 = -270 by norm_num]
    ring
  have hlint : ∫⁻ t in Ioi (450 : ℝ), ENNReal.ofReal (K * Real.exp (-0.6 * t)) =
      ENNReal.ofReal (K * (Real.exp (-270) / 0.6)) := by
    rw [← hval]
    exact (ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun t => by positivity)).symm
  have hfin : K * (Real.exp (-270) / 0.6) ≤ 1e-12 * Real.log x := by
    have e : K * (Real.exp (-270) / 0.6) = 20 * (Real.log x + 10) * Real.exp (-35) / 0.6 := by
      have : Real.exp 235 * Real.exp (-270) = Real.exp (-35) := by
        rw [← Real.exp_add]
        norm_num
      rw [hK, ← this]
      ring
    rw [e]
    have h35 := exp_35
    have hpos : 0 ≤ 20 * (Real.log x + 10) := by linarith
    have := mul_le_mul_of_nonneg_left h35 hpos
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  calc ∫⁻ t in Ioi (450 : ℝ), ENNReal.ofReal (fmal x t * gw 1 t)
      ≤ ∫⁻ t in Ioi (450 : ℝ), ENNReal.ofReal (K * Real.exp (-0.6 * t)) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal (K * (Real.exp (-270) / 0.6)) := hlint
    _ ≤ ENNReal.ofReal (1e-12 * Real.log x) := ENNReal.ofReal_le_ofReal hfin

/-- **THE HEADLINE, SIXTEEN NAMED LINKS**: `GarmolaDecr`, `Eta2Moments` and `MalTailInt`
discharged. -/
theorem helfMajR_of_16 (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer)
    (pr : PlusReg) (pn : PlusNorms) (pd : PlusDecay) (pt : PlusTailInt)
    (fr : PhiReg) (fn : PhiNorms) (fd : PhiDecay) (ft : PhiTailInt) (ko : Kolona)
    (mr : MalReg) (mn : MalNorms) (md : MalDecay) (mm : MalMain) :
    MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi) :=
  helfMajR_of_links'' hEF hZC hHs pr pn pd pt fr fn fd ft ko mr mn md malTailInt_holds mm

end Principia.Common.TernaryGoldbach.HM
