/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajMalMainB
import Principia.Common.TernaryGoldbach.HelfMajMalNorms

set_option autoImplicit false

/-!
# `HM.MalMain` PROVED at its stated constants, from two VNODE-LP values

**`malMain_of_vnode`**: the first two values `HC.MalMainCited` cites (`∫η∘² = 0.64020599736635
± 10⁻¹⁴`, `∫η∘² log t = −0.021094778698867 ± 10⁻¹⁵`) imply the STATED link `HM.MalMain`: for
`x ≥ 10¹²`, `|∫η₊² log(xt) − (0.640206 log x − 0.021095)| ≤ 3.9·10⁻⁶ log x + 1.3·10⁻⁶`.
Helfgott's `eq:impath` (`C₄ = 2013.18`, a run with a wrong interior integral) is NOT used, and
neither is the third cited value `|η∘ log|₂ ≤ 0.214`: the elementary
`∫(η∘ log)² ≤ ∫₀²(t−1)²t⁵(2−t)⁶ = 512/9009` (`HP.gi_gP`) suffices.

## The proof (`ℓ = log x ≥ 27`, `D = h_H − h`, `|D| ≤ c = 2.24·10⁻⁴` by `HP.band_le_all`)

* `η₊² − η∘² = D²t²e^{−t²} + 2D·k₀`, `k₀ = h t²e^{−t²}` (`sq_diff_eq`). Hence
  `∫η₊² − ∫η∘² = 2∫Dk₀ + Q`, `0 ≤ Q ≤ c²√π/4 = 2.2·10⁻⁸`, and `|∫Dk₀| ≤ 5·10⁻⁷`
  (`MM.cross_le`: Mellin inversion of `h`, `A(r) = O(r⁻⁴)` and `Mk₀(1 + ir) = O(r⁻¹)` on
  `|r| > 200`). So `|∫η₊² − 0.640206| ≤ α = 1.025·10⁻⁶`.
* `|(η₊² − η∘²) log t| ≤ c²t²e^{−t²}(λ + (t + 1/t − 1)/2) + (η∘ log t)²/λ` (`λ = 1599`;
  `2|Dte^{−t²/2}||η∘ log| ≤ λ(Dte^{−t²/2})² + (η∘ log)²/λ`, `|log| ≤ (1 + log²)/2`,
  `log² t ≤ t + 1/t − 2`), so `|∫η₊² log t − ∫η∘² log t| ≤ 7.1109·10⁻⁵` and
  `|∫η₊² log t + 0.021095| ≤ β = 7.1331·10⁻⁵`.
* `ℓα + β ≤ 3.9·10⁻⁶ℓ + 1.3·10⁻⁶` because `β − 1.3·10⁻⁶ = 7.003·10⁻⁵ ≤ 27(3.9·10⁻⁶ − α) =
  7.76·10⁻⁵` (margin 10 %).

The constant term is NOT within `1.3·10⁻⁶` on its own (Cauchy–Schwarz charges it `7.1·10⁻⁵`);
it closes because `ℓ ≥ 27` turns the slack in the `ℓ`-coefficient (`3.9·10⁻⁶` against
`α ≈ 1.0·10⁻⁶`) into room for it — the device `HP.malNormsL_holds` already uses.
-/

namespace Principia.Common.TernaryGoldbach.MM

open MeasureTheory Set Filter

/-! ## (1) Pointwise identities and integrability -/

/-- `η₊² − η∘² = D²t²e^{−t²} + 2D·k₀`. -/
theorem sq_diff_eq (t : ℝ) : HW.etaPlus t ^ 2 - HW.etaCirc t ^ 2 =
    (HW.hH 200 t - HW.hFun t) ^ 2 * (t ^ 2 * Real.exp (-t ^ 2)) +
      2 * ((HW.hH 200 t - HW.hFun t) * k0 t) := by
  unfold HW.etaPlus HW.etaCirc k0
  rw [← HM.exp_half_sq t]
  ring

theorem measurable_etaPlus' : Measurable HW.etaPlus := HP.contDiff_etaPlus.continuous.measurable

theorem iC2 : IntegrableOn (fun t => HW.etaCirc t ^ 2) (Ioi 0) :=
  EN.integrableOn_of_cont _ (EN.continuous_etaCirc.pow 2)
    fun t ht => by rw [EN.etaCirc_of_two_lt ht]; ring

theorem iDk : IntegrableOn (fun t => (HW.hH 200 t - HW.hFun t) * k0 t) (Ioi 0) := by
  refine (integrableOn_k0.abs.const_mul 2.24e-4).mono'
    ((measurable_hH200.sub HW.measurable_hFun).mul continuous_k0.measurable).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (HP.band_le_all t) (abs_nonneg _)

/-- `|a²L| ≤ (a² + (La)²)/2`. -/
theorem abs_sq_mul_le (a L : ℝ) : |a ^ 2 * L| ≤ (a ^ 2 + (L * a) ^ 2) / 2 := by
  have e : |a ^ 2 * L| = |a| * |L * a| := by
    rw [abs_mul, abs_mul, abs_pow]
    ring
  rw [e]
  nlinarith [sq_nonneg (|a| - |L * a|), sq_abs a, sq_abs (L * a)]

theorem iPL : IntegrableOn (fun t => HW.etaPlus t ^ 2 * Real.log t) (Ioi 0) := by
  refine ((HP.int_etaPlus_sq.add HP.int_llog_etaPlus_sq).div_const 2).mono'
    ((measurable_etaPlus'.pow_const 2).mul Real.measurable_log).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs]
  exact abs_sq_mul_le _ _

theorem iCL : IntegrableOn (fun t => HW.etaCirc t ^ 2 * Real.log t) (Ioi 0) := by
  refine ((iC2.add HP.gi_gP.1).div_const 2).mono'
    ((EN.continuous_etaCirc.measurable.pow_const 2).mul Real.measurable_log).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  rw [Real.norm_eq_abs]
  have h1 := abs_sq_mul_le (HW.etaCirc t) (Real.log t)
  have h2 := HP.llog_circ_sq_le (t := t) ht
  simp only [Pi.add_apply]
  linarith

theorem iCL2 : IntegrableOn (fun t => (HW.etaCirc t * Real.log t) ^ 2) (Ioi 0) := by
  refine HP.gi_gP.1.mono' ((EN.continuous_etaCirc.measurable.mul
    Real.measurable_log).pow_const 2).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_comm]
  exact HP.llog_circ_sq_le ht

/-! ## (2) The `ℓ`-coefficient: `∫η₊² − ∫η∘² = 2∫Dk₀ + Q`, `0 ≤ Q ≤ c²√π/4` -/

theorem i0_split :
    0 ≤ (∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2) - (∫ t in Ioi (0 : ℝ), HW.etaCirc t ^ 2) -
        2 * ∫ t in Ioi (0 : ℝ), (HW.hH 200 t - HW.hFun t) * k0 t ∧
      (∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2) - (∫ t in Ioi (0 : ℝ), HW.etaCirc t ^ 2) -
          2 * (∫ t in Ioi (0 : ℝ), (HW.hH 200 t - HW.hFun t) * k0 t) ≤
        (2.24e-4 : ℝ) ^ 2 * (Real.sqrt Real.pi / 4) := by
  have e : (∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2) - (∫ t in Ioi (0 : ℝ), HW.etaCirc t ^ 2) -
      2 * (∫ t in Ioi (0 : ℝ), (HW.hH 200 t - HW.hFun t) * k0 t) =
        ∫ t in Ioi (0 : ℝ), (HW.hH 200 t - HW.hFun t) ^ 2 * (t ^ 2 * Real.exp (-t ^ 2)) := by
    have hf : Integrable (fun t => HW.etaPlus t ^ 2 - HW.etaCirc t ^ 2)
        (volume.restrict (Ioi 0)) := HP.int_etaPlus_sq.sub iC2
    have hg : Integrable (fun t => 2 * ((HW.hH 200 t - HW.hFun t) * k0 t))
        (volume.restrict (Ioi 0)) := iDk.const_mul 2
    have e2 : ∫ t in Ioi (0 : ℝ), (HW.hH 200 t - HW.hFun t) ^ 2 * (t ^ 2 * Real.exp (-t ^ 2)) =
        ∫ t in Ioi (0 : ℝ), (HW.etaPlus t ^ 2 - HW.etaCirc t ^ 2 -
          2 * ((HW.hH 200 t - HW.hFun t) * k0 t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [sq_diff_eq]
      ring
    rw [e2, integral_sub hf hg, integral_sub HP.int_etaPlus_sq iC2, integral_const_mul]
  rw [e]
  constructor
  · exact setIntegral_nonneg measurableSet_Ioi fun t _ => by positivity
  · refine HM.int_le_of_pt (HP.gi_smul ((2.24e-4 : ℝ) ^ 2) HM.I2) (fun t => by positivity)
      fun t _ => ?_
    have hd : (HW.hH 200 t - HW.hFun t) ^ 2 ≤ (2.24e-4 : ℝ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (HP.band_le_all t) 2
    exact mul_le_mul_of_nonneg_right hd (by positivity)

/-! ## (3) The constant: `|∫(η₊² − η∘²) log t| ≤ 7.1109·10⁻⁵` -/

/-- The pointwise majorant of `|(η₊² − η∘²) log t|`, shaped as `HM.gi_lin` builds it. -/
theorem log_part_pt {t : ℝ} (ht : 0 < t) :
    |(HW.etaPlus t ^ 2 - HW.etaCirc t ^ 2) * Real.log t| ≤
      (2.24e-4 : ℝ) ^ 2 * (1599 * (t ^ 2 * Real.exp (-t ^ 2)) +
        1 / 2 * (1 * (1 * (t ^ 3 * Real.exp (-t ^ 2)) + 1 * (t ^ 1 * Real.exp (-t ^ 2))) +
          -1 * (t ^ 2 * Real.exp (-t ^ 2)))) +
        1 / 1599 * (HW.etaCirc t * Real.log t) ^ 2 := by
  have hlog := HM.log_sq_le ht
  have hD2 : (HW.hH 200 t - HW.hFun t) ^ 2 ≤ (2.24e-4 : ℝ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (HP.band_le_all t) 2
  have hk : (HW.hH 200 t - HW.hFun t) * k0 t * Real.log t =
      ((HW.hH 200 t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2))) *
        (HW.etaCirc t * Real.log t) := by
    unfold k0 HW.etaCirc
    rw [← HM.exp_half_sq t]
    ring
  have hsplit : (HW.etaPlus t ^ 2 - HW.etaCirc t ^ 2) * Real.log t =
      (HW.hH 200 t - HW.hFun t) ^ 2 * (t ^ 2 * Real.exp (-t ^ 2)) * Real.log t +
        2 * ((HW.hH 200 t - HW.hFun t) * k0 t * Real.log t) := by
    rw [sq_diff_eq]
    ring
  have hgg : (t * Real.exp (-t ^ 2 / 2)) ^ 2 = t ^ 2 * Real.exp (-t ^ 2) := by
    rw [mul_pow, HM.exp_half_sq]
  have e : t ^ 2 * Real.exp (-t ^ 2) * (t + 1 / t - 1) =
      1 * (1 * (t ^ 3 * Real.exp (-t ^ 2)) + 1 * (t ^ 1 * Real.exp (-t ^ 2))) +
        -1 * (t ^ 2 * Real.exp (-t ^ 2)) := by
    field_simp
    ring
  rw [hsplit, hk]
  generalize HW.hH 200 t - HW.hFun t = D at hD2 ⊢
  generalize Real.log t = L at hlog ⊢
  generalize t ^ 2 * Real.exp (-t ^ 2) = G at hgg e ⊢
  generalize t * Real.exp (-t ^ 2 / 2) = g at hgg ⊢
  generalize HW.etaCirc t * L = Y
  have hG0 : 0 ≤ G := by rw [← hgg]; positivity
  have hL1 : |L| ≤ (1 + L ^ 2) / 2 := by nlinarith [sq_nonneg (|L| - 1), sq_abs L]
  have h1 : |D ^ 2 * G * L| ≤ (2.24e-4 : ℝ) ^ 2 * (G * (t + 1 / t - 1) / 2) := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg D) hG0)]
    have p1 : D ^ 2 * G ≤ (2.24e-4 : ℝ) ^ 2 * G := mul_le_mul_of_nonneg_right hD2 hG0
    have p2 : |L| ≤ (t + 1 / t - 1) / 2 := by linarith
    have hp : 0 ≤ (t + 1 / t - 1) / 2 := le_trans (abs_nonneg _) p2
    calc D ^ 2 * G * |L| ≤ (2.24e-4 : ℝ) ^ 2 * G * ((t + 1 / t - 1) / 2) :=
          mul_le_mul p1 p2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have h2 : 2 * |D * g * Y| ≤ 1599 * ((2.24e-4 : ℝ) ^ 2 * G) + 1 / 1599 * Y ^ 2 := by
    rw [abs_mul]
    have hDg : (D * g) ^ 2 ≤ (2.24e-4 : ℝ) ^ 2 * G := by
      rw [mul_pow, hgg]
      exact mul_le_mul_of_nonneg_right hD2 hG0
    nlinarith [sq_nonneg (1599 * |D * g| - |Y|), sq_abs (D * g), sq_abs Y]
  calc |D ^ 2 * G * L + 2 * (D * g * Y)| ≤ |D ^ 2 * G * L| + |2 * (D * g * Y)| :=
        abs_add_le _ _
    _ = |D ^ 2 * G * L| + 2 * |D * g * Y| := by rw [abs_mul (2 : ℝ), abs_two]
    _ ≤ (2.24e-4 : ℝ) ^ 2 * (G * (t + 1 / t - 1) / 2) + (1599 * ((2.24e-4 : ℝ) ^ 2 * G) +
          1 / 1599 * Y ^ 2) := add_le_add h1 h2
    _ = _ := by rw [e]; ring

/-- `∫(η∘ log)² ≤ 512/9009` (`(log t·η∘)² ≤ g_P`, `HP.gi_gP`). -/
theorem int_circ_log_sq_le :
    ∫ t in Ioi (0 : ℝ), (HW.etaCirc t * Real.log t) ^ 2 ≤ 512 / 9009 :=
  HM.int_le_of_pt HP.gi_gP (fun _ => sq_nonneg _) fun t ht => by
    rw [mul_comm]
    exact HP.llog_circ_sq_le ht

/-- **`|∫η₊² log t − ∫η∘² log t| ≤ 7.1109·10⁻⁵`** (no citation). -/
theorem log_part_le :
    |(∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log t) -
        ∫ t in Ioi (0 : ℝ), HW.etaCirc t ^ 2 * Real.log t| ≤ 7.1109e-5 := by
  have hV := int_circ_log_sq_le
  have gV : HM.GI (fun t => (HW.etaCirc t * Real.log t) ^ 2)
      (∫ t in Ioi (0 : ℝ), (HW.etaCirc t * Real.log t) ^ 2) := ⟨iCL2, rfl⟩
  have M1 := HM.gi_lin 1599 (1 / 2) HM.I2 (HM.gi_lin 1 (-1) (HM.gi_lin 1 1 HM.I3 HP.I1) HM.I2)
  have M := HM.gi_lin ((2.24e-4 : ℝ) ^ 2) (1 / 1599) M1 gV
  have hb := HM.int_le_of_pt M (fun t => abs_nonneg _) fun t ht => log_part_pt ht
  have e : (∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log t) -
      ∫ t in Ioi (0 : ℝ), HW.etaCirc t ^ 2 * Real.log t =
        ∫ t in Ioi (0 : ℝ), (HW.etaPlus t ^ 2 - HW.etaCirc t ^ 2) * Real.log t := by
    rw [← integral_sub iPL iCL]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [e]
  refine (abs_integral_le_integral_abs).trans (hb.trans ?_)
  have hs := HM.sqrt_pi_bounds
  nlinarith [hs.1, hs.2]

/-! ## (4) `HM.MalMain` -/

/-- **`HM.MalMain` from two VNODE-LP values** (exactly the first two conjuncts of
`HC.MalMainCited`). -/
theorem malMain_of_vnode
    (h0 : |(∫ t in Ioi (0 : ℝ), HW.etaCirc t ^ 2) - 0.64020599736635| ≤ 1e-14)
    (h1 : |(∫ t in Ioi (0 : ℝ), HW.etaCirc t ^ 2 * Real.log t) - -0.021094778698867| ≤ 1e-15) :
    HM.MalMain := by
  intro x hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hℓ := HP.log_x_ge hx
  have hsplit : ∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t) =
      Real.log x * (∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2) +
        ∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log t := by
    have e : ∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t) =
        ∫ t in Ioi (0 : ℝ), (Real.log x * HW.etaPlus t ^ 2 + HW.etaPlus t ^ 2 * Real.log t) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : (0 : ℝ) < t := ht
      rw [Real.log_mul hx0.ne' ht0.ne']
      ring
    rw [e, integral_add (HP.int_etaPlus_sq.const_mul (Real.log x)) iPL, integral_const_mul]
  rw [hsplit]
  have hc := abs_le.mp cross_le
  obtain ⟨q0, q1⟩ := i0_split
  have hlp := abs_le.mp log_part_le
  have hs := HM.sqrt_pi_bounds
  have hq : (2.24e-4 : ℝ) ^ 2 * (Real.sqrt Real.pi / 4) ≤ 2.2234e-8 := by nlinarith [hs.2]
  have h0' := abs_le.mp h0
  have h1' := abs_le.mp h1
  have hA1 : (∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2) - 0.640206 ≤ 1.025e-6 := by linarith
  have hA2 : -1.025e-6 ≤ (∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2) - 0.640206 := by linarith
  have hB1 : (∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log t) + 0.021095 ≤ 7.1331e-5 := by
    linarith
  have hB2 : -7.1331e-5 ≤ (∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log t) + 0.021095 := by
    linarith
  have hℓ0 : 0 ≤ Real.log x := by linarith
  have p1 := mul_le_mul_of_nonneg_left hA1 hℓ0
  have p2 := mul_le_mul_of_nonneg_left hA2 hℓ0
  rw [abs_le]
  constructor <;> nlinarith [p1, p2, hB1, hB2]

end Principia.Common.TernaryGoldbach.MM
