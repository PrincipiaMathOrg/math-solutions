/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajPlusReg

set_option autoImplicit false

/-!
# `HM.PlusNorms` REPLACED by a proved `PlusNormsL`; Thm 1.4 re-derived at it

**`plusNormsL_holds : PlusNormsL`**, and **`malporR_of_linksL`: `MR.MalporR η₊` from
`ExplicitFormula`, `ZeroCount`, `Hausierer`, `GarmolaDecr`, `PlusDecay`, `PlusTailInt` and
Platt** — `PlusReg` (`HP.plusReg_holds`) and the norms are supplied, not assumed.

| conjunct | `PlusNorms` (stated) | `PlusNormsL` (proved) |
|---|---|---|
| `|η₊|₂` | `0.80044` | `0.80044` |
| `|η₊ log|₂` | `0.83` | `0.83` |
| `|η₊/√t|₁` | `1.00007` | `1.00007` |
| `|η₊'|₂` | `10.845789` | `13000` |
| `c₀` | `6.5363 + 9.3196|δ|` | `37200 + 12.2|δ|` |

Routes: `|η₊|₂` from `(η∘ + dw)² ≤ η∘² + 2cw + c²w²`, `c = 2.24·10⁻⁴` (`BS.band_le`),
`|η∘|₂² ≤ 0.6402109`; `|η₊ log|₂` from `log² ≤ t + 1/t − 2` and `|η₊| ≤ 1.65te^{−t²/2}`
(`≤ √(2.7225(1 − √π/2)) = 0.5566`); `|η₊/√t|₁` from `|η∘|/√t ≤ t²(t+1)(2−t)³/2` (`∫ = 104/105`)
plus the band (`0.99073`); `|η₊'|₂` from `|η₊'| ≤ (13752 + 1.65(1+t²))e^{−t²/2}`
(`HP.abs_dEP_le`; `12948.4`); `c₀` from the same envelope, with `e^{−t²/2} ≤ e^{1/2}e^{−t}` for the
`t^{−1/2}` weight.

**Why the derivative conjuncts are loose and why it does not matter.** `|t h_H'(t)| ≤ 13752` is a
crude bound (the truth is `≤ 4.25`); Helfgott's `10.85` needs `|η₊'|₂` to `1 %`. Both enter
`prop:unease` only through `R/x`, where the consumer has room: re-deriving the chain
(`plus_errL` → `Rplus_leL` → `malpor_gen_arithL`, `Rplus_one_leL` → `malpor_one_arithL`), the
`R/x` term is `≤ (0.03721 + 14.641/√q)/√x` (was `(6.6·10⁻⁶ + 11.19/√q)/√x`) for general `q`, and
`≤ 7.4/√x` (was `5.6/√x`) at `q = 1`. The retyped targets still close:
* general `q`: `769400/√q + 100.24 + 14.641/√q ≤ 900000/√q + 52` for `√q ≤ 548`
  (margin `130585/√q − 48.24 ≥ 190`; it was `130589/√q − 48.20`);
* `q = 1`: `10⁻¹³ + (295900 + 7.4)/√x ≤ 3.34·10⁻¹¹ + 320000/√x` (margin `24092/√x`).
-/

namespace Principia.Common.TernaryGoldbach.HP

open MeasureTheory Set Filter

/-! ## (1) Gaussian and Euler majorants -/

theorem gi_smul {f : ℝ → ℝ} {A : ℝ} (c : ℝ) (hf : HM.GI f A) :
    HM.GI (fun t => c * f t) (c * A) :=
  ⟨hf.1.const_mul c, by rw [integral_const_mul, hf.2]⟩

theorem I0 : HM.GI (fun t => t ^ 0 * Real.exp (-t ^ 2)) (Real.sqrt Real.pi / 2) := by
  have h := HM.gm1 0
  rw [show (((0 : ℕ) : ℝ) + 1) / 2 = 1 / 2 by norm_num, Real.Gamma_one_half_eq] at h
  exact h

theorem I1 : HM.GI (fun t => t ^ 1 * Real.exp (-t ^ 2)) (1 / 2) := by
  have h := HM.gm1 1
  rw [show (((1 : ℕ) : ℝ) + 1) / 2 = 1 by norm_num, Real.Gamma_one] at h
  exact h

/-- **The Euler integral at `1/2`**: `∫₀^∞ e^{−t}t^{−1/2} dt = Γ(1/2) = √π`. -/
theorem gam_half_gi :
    HM.GI (fun t => Real.exp (-t) * t ^ ((1 : ℝ) / 2 - 1)) (Real.sqrt Real.pi) :=
  ⟨Real.GammaIntegral_convergent (by norm_num),
    by rw [← Real.Gamma_eq_integral (by norm_num), Real.Gamma_one_half_eq]⟩

/-- `e^{−t²/2} ≤ e^{1/2}e^{−t} ≤ 1.6488e^{−t}` (`(t − 1)² ≥ 0`). -/
theorem exp_half_sq_le (t : ℝ) : Real.exp (-t ^ 2 / 2) ≤ 1.6488 * Real.exp (-t) := by
  have h1 : Real.exp (-t ^ 2 / 2) ≤ Real.exp (1 / 2) * Real.exp (-t) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (t - 1)])
  have h2 := mul_le_mul_of_nonneg_right BL.exp_half_le (Real.exp_pos (-t)).le
  linarith

/-- `√t ≤ (1 + t)/2`. -/
theorem sqrt_le_avg {t : ℝ} (ht : 0 ≤ t) : Real.sqrt t ≤ (1 + t) / 2 := by
  have h := Real.sq_sqrt ht
  nlinarith [sq_nonneg (Real.sqrt t - 1)]

/-- `1/√t = t^{1/2 − 1}`. -/
theorem inv_sqrt_eq {t : ℝ} (ht : 0 < t) : 1 / Real.sqrt t = t ^ ((1 : ℝ) / 2 - 1) := by
  rw [show (1 : ℝ) / 2 - 1 = -(1 / 2) by norm_num, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow,
    one_div]

/-- `t·E/√t = √t·E ≤ ((1 + t)/2)·E`. -/
theorem mul_div_sqrt_le {t E : ℝ} (ht : 0 < t) (hE : 0 ≤ E) :
    t * E / Real.sqrt t ≤ (1 + t) / 2 * E := by
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  rw [div_le_iff₀ hs0]
  have := mul_le_mul_of_nonneg_left (sqrt_le_avg ht.le) (mul_nonneg (Real.sqrt_nonneg t) hE)
  nlinarith

/-! ## (2) `|η₊|₂ ≤ 0.80044` -/

/-- `∫₋₁¹ (1−u²)⁶e^{−u²} ≤ 3213595904/5019589575 = 0.64021089` (`EN.int_Phi`). -/
theorem G6_hi :
    ∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ 6 * Real.exp (-u ^ 2) ≤ 3213595904 / 5019589575 := by
  have hG : IntervalIntegrable (fun u : ℝ => (1 - u ^ 2) ^ 6 * Real.exp (-u ^ 2)) volume (-1) 1 :=
    (by fun_prop : Continuous fun u : ℝ => (1 - u ^ 2) ^ 6 * Real.exp (-u ^ 2)).intervalIntegrable
      _ _
  have hhi : IntervalIntegrable
      (fun u : ℝ => (1 - u ^ 2) ^ 6 * (EN.T4 (u ^ 2) + (u ^ 2) ^ 5 / 100)) volume (-1) 1 := by
    refine Continuous.intervalIntegrable ?_ _ _
    unfold EN.T4
    fun_prop
  have h := intervalIntegral.integral_mono_on (by norm_num) hG hhi fun u hu =>
    mul_le_mul_of_nonneg_left (EN.exp_sq_taylor hu).2 (by positivity : (0 : ℝ) ≤ (1 - u ^ 2) ^ 6)
  rw [EN.int_Phi] at h
  exact h

/-- **The band split**: `η₊ = η∘ + (h_H − h)·te^{−t²/2}`. -/
theorem etaPlus_split (t : ℝ) :
    HW.etaPlus t = HW.etaCirc t + (HW.hH 200 t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2)) := by
  unfold HW.etaPlus HW.etaCirc
  ring

/-- **`|η₊|₂ ≤ 0.80044`** (Helfgott's `eq:mastodon` constant): `|η₊|₂² ≤ 0.64021089 + 2c +
c²√π/4 = 0.6406589`, `c = 2.24·10⁻⁴`. -/
theorem l2_etaPlus_le : MajSp.l2 HW.etaPlus ≤ 0.80044 := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ), HW.etaPlus t ^ 2 ≤
      HW.etaCirc t ^ 2 + 2 * 2.24e-4 * (t * Real.exp (-t ^ 2 / 2)) +
        (2.24e-4 : ℝ) ^ 2 * (t ^ 2 * Real.exp (-t ^ 2)) := by
    intro t ht
    have hw0 : 0 ≤ t * Real.exp (-t ^ 2 / 2) := mul_nonneg (le_of_lt ht) (Real.exp_pos _).le
    have e2 : (t * Real.exp (-t ^ 2 / 2)) ^ 2 = t ^ 2 * Real.exp (-t ^ 2) := by
      rw [mul_pow, HM.exp_half_sq]
    have ha1 : |HW.etaCirc t| ≤ 1 := HW.etaCirc_le t
    have hd1 : |HW.hH 200 t - HW.hFun t| ≤ 2.24e-4 := BS.band_le t ht
    have hab : 2 * HW.etaCirc t * ((HW.hH 200 t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2))) ≤
        2 * 2.24e-4 * (t * Real.exp (-t ^ 2 / 2)) := by
      have h1 : |HW.etaCirc t * (HW.hH 200 t - HW.hFun t)| ≤ 2.24e-4 := by
        rw [abs_mul]
        calc |HW.etaCirc t| * |HW.hH 200 t - HW.hFun t| ≤ 1 * 2.24e-4 :=
              mul_le_mul ha1 hd1 (abs_nonneg _) zero_le_one
          _ = 2.24e-4 := one_mul _
      have h2 : HW.etaCirc t * (HW.hH 200 t - HW.hFun t) ≤ 2.24e-4 := (le_abs_self _).trans h1
      nlinarith [mul_le_mul_of_nonneg_right h2 hw0]
    have hdd : ((HW.hH 200 t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2))) ^ 2 ≤
        (2.24e-4 : ℝ) ^ 2 * (t * Real.exp (-t ^ 2 / 2)) ^ 2 := by
      rw [mul_pow]
      have : (HW.hH 200 t - HW.hFun t) ^ 2 ≤ (2.24e-4 : ℝ) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hd1 2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    rw [etaPlus_split, ← e2]
    nlinarith [hab, hdd]
  have hA : Integrable (fun t => HW.etaCirc t ^ 2) (volume.restrict (Ioi 0)) :=
    EN.integrableOn_of_cont _ (EN.continuous_etaCirc.pow 2) fun t ht => by
      rw [EN.etaCirc_of_two_lt ht]
      ring
  have hB := EN.integrable_t_exp.const_mul (2 * 2.24e-4)
  have hC := EN.integrable_t2_exp.const_mul ((2.24e-4 : ℝ) ^ 2)
  have hAB : Integrable (fun t => HW.etaCirc t ^ 2 + 2 * 2.24e-4 * (t * Real.exp (-t ^ 2 / 2)))
      (volume.restrict (Ioi 0)) := hA.add hB
  have hg : Integrable (fun t => HW.etaCirc t ^ 2 + 2 * 2.24e-4 * (t * Real.exp (-t ^ 2 / 2)) +
      (2.24e-4 : ℝ) ^ 2 * (t ^ 2 * Real.exp (-t ^ 2))) (volume.restrict (Ioi 0)) := hAB.add hC
  have hI := integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg _) hg
    (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  rw [integral_add hAB hC, integral_add hA hB, integral_const_mul, integral_const_mul,
    EN.int_t_exp, EN.int_t2_exp, EN.circ_sq_int] at hI
  have hG := G6_hi
  have hq := EN.sqrt_pi_quarter_le
  unfold MajSp.l2
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith

/-! ## (3) `|η₊·log|₂ ≤ 0.83` -/

/-- `η₊² ≤ 2.7225 t²e^{−t²}` for `t > 0`. -/
theorem etaPlus_sq_le {t : ℝ} (ht : 0 < t) :
    HW.etaPlus t ^ 2 ≤ 2.7225 * (t ^ 2 * Real.exp (-t ^ 2)) := by
  rw [← sq_abs]
  have h := pow_le_pow_left₀ (abs_nonneg _) (abs_etaPlus_le ht) 2
  have e : (1.65 * (t * Real.exp (-t ^ 2 / 2))) ^ 2 = 2.7225 * (t ^ 2 * Real.exp (-t ^ 2)) := by
    rw [mul_pow, mul_pow, HM.exp_half_sq]
    ring
  linarith

/-- **`|η₊·log|₂ ≤ 0.83`** (Helfgott's `eq:pamiatka` constant; here `≤ 0.5566`). -/
theorem l2_llog_etaPlus_le : MajSp.l2 (HM.llog HW.etaPlus) ≤ 0.83 := by
  have hG : HM.GI (fun t => 2.7225 * (1 * (1 * (t ^ 3 * Real.exp (-t ^ 2)) +
      1 * (t ^ 1 * Real.exp (-t ^ 2))) + -2 * (t ^ 2 * Real.exp (-t ^ 2))))
      (2.7225 * (1 * (1 * (1 / 2) + 1 * (1 / 2)) + -2 * (Real.sqrt Real.pi / 4))) :=
    gi_smul 2.7225 (HM.gi_lin 1 (-2) (HM.gi_lin 1 1 HM.I3 I1) HM.I2)
  have hpt : ∀ t : ℝ, 0 < t → HM.llog HW.etaPlus t ^ 2 ≤ 2.7225 * (1 * (1 * (t ^ 3 *
      Real.exp (-t ^ 2)) + 1 * (t ^ 1 * Real.exp (-t ^ 2))) +
        -2 * (t ^ 2 * Real.exp (-t ^ 2))) := by
    intro t ht
    have hl := HM.log_sq_le ht
    have hl0 : 0 ≤ t + 1 / t - 2 := le_trans (sq_nonneg _) hl
    unfold HM.llog
    rw [mul_pow]
    have p := mul_le_mul hl (etaPlus_sq_le ht) (sq_nonneg _) hl0
    have e : (t + 1 / t - 2) * (2.7225 * (t ^ 2 * Real.exp (-t ^ 2))) =
        2.7225 * (1 * (1 * (t ^ 3 * Real.exp (-t ^ 2)) + 1 * (t ^ 1 * Real.exp (-t ^ 2))) +
          -2 * (t ^ 2 * Real.exp (-t ^ 2))) := by
      field_simp
      ring
    linarith
  have h := HM.int_le_of_pt hG (fun t => sq_nonneg _) hpt
  unfold MajSp.l2
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith [HM.sqrt_pi_bounds.1]

/-! ## (4) `|η₊/√t|₁ ≤ 0.991` -/

/-- `g∘(t) = t²(t+1)max(2−t, 0)³/2`, a continuous majorant of `|η∘(t)|/√t`. -/
noncomputable def gcirc (t : ℝ) : ℝ := t ^ 2 * (t + 1) * max (2 - t) 0 ^ 3 / 2

theorem continuous_gcirc : Continuous gcirc := by
  unfold gcirc
  fun_prop

/-- `∫₀^∞ g∘ = ∫₀² t²(t+1)(2−t)³/2 = 104/105`. -/
theorem gi_gcirc : HM.GI gcirc (104 / 105) := by
  have h2 : ∀ t : ℝ, 2 < t → gcirc t = 0 := fun t ht => by
    unfold gcirc
    rw [max_eq_right (by linarith)]
    ring
  refine ⟨EN.integrableOn_of_cont _ continuous_gcirc h2, ?_⟩
  rw [EN.setInt_Ioi_02 _ h2]
  have h : EqOn gcirc (fun u => ∑ k : Fin 7, (![0, 0, 4, -2, -3, 5 / 2, -1 / 2] : Fin 7 → ℝ) k *
      u ^ (k : ℕ)) (uIcc 0 2) := by
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    unfold gcirc
    rw [max_eq_left (by linarith [hu.2])]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_succ]
    ring
  rw [intervalIntegral.integral_congr h, EN.int_poly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  norm_num

/-- `|η∘(t)|/√t ≤ g∘(t)`: on `[0,2]`, `η∘ = t³(2−t)³e^{−(t−1)²/2} ≤ t³(2−t)³` and
`t ≤ √t(1+t)/2`. -/
theorem circ_div_sqrt_le {t : ℝ} (ht : 0 < t) : |HW.etaCirc t| / Real.sqrt t ≤ gcirc t := by
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  rcases le_or_gt t 2 with h2 | h2
  · rw [HW.etaCirc_eq ht.le h2]
    have hE : Real.exp (-(t - 1) ^ 2 / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (t - 1)])
    have h20 : 0 ≤ 2 - t := by linarith
    have hp0 : 0 ≤ t ^ 3 * (2 - t) ^ 3 := by positivity
    rw [abs_of_nonneg (mul_nonneg hp0 (Real.exp_pos _).le), div_le_iff₀ hs0]
    unfold gcirc
    rw [max_eq_left h20]
    have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
    have hst : t ≤ (1 + t) / 2 * Real.sqrt t := by
      have := mul_le_mul_of_nonneg_left (sqrt_le_avg ht.le) (Real.sqrt_nonneg t)
      nlinarith
    have hq : 0 ≤ t ^ 2 * (2 - t) ^ 3 := by positivity
    have key : t ^ 3 * (2 - t) ^ 3 ≤ t ^ 2 * (t + 1) * (2 - t) ^ 3 / 2 * Real.sqrt t := by
      have := mul_le_mul_of_nonneg_left hst hq
      nlinarith
    calc t ^ 3 * (2 - t) ^ 3 * Real.exp (-(t - 1) ^ 2 / 2) ≤ t ^ 3 * (2 - t) ^ 3 * 1 :=
          mul_le_mul_of_nonneg_left hE hp0
      _ ≤ t ^ 2 * (t + 1) * (2 - t) ^ 3 / 2 * Real.sqrt t := by linarith
  · rw [EN.etaCirc_of_two_lt h2, abs_zero, zero_div]
    unfold gcirc
    rw [max_eq_right (by linarith)]
    norm_num

/-- `|η₊| ≤ |η∘| + c·te^{−t²/2}` (`BS.band_le`). -/
theorem abs_etaPlus_band {t : ℝ} (ht : 0 < t) :
    |HW.etaPlus t| ≤ |HW.etaCirc t| + 2.24e-4 * (t * Real.exp (-t ^ 2 / 2)) := by
  have hw0 : 0 ≤ t * Real.exp (-t ^ 2 / 2) := mul_nonneg ht.le (Real.exp_pos _).le
  rw [etaPlus_split]
  calc |HW.etaCirc t + (HW.hH 200 t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2))|
      ≤ |HW.etaCirc t| + |(HW.hH 200 t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2))| :=
        abs_add_le _ _
    _ ≤ |HW.etaCirc t| + 2.24e-4 * (t * Real.exp (-t ^ 2 / 2)) := by
        rw [abs_mul, abs_of_nonneg hw0]
        exact add_le_add_right (mul_le_mul_of_nonneg_right (BS.band_le t ht) hw0) _

/-- **`|η₊/√t|₁ ≤ 0.991`** (`104/105 + c((√(2π)/2)/2 + 1/2) = 0.99073`). -/
theorem n1h_etaPlus_le : HM.n1h HW.etaPlus ≤ 0.991 := by
  have hG := HM.gi_lin 1 2.24e-4 gi_gcirc (HM.gi_lin (1 / 2) (1 / 2) HM.M0 HM.M1)
  have hpt : ∀ t : ℝ, 0 < t → |HW.etaPlus t| / Real.sqrt t ≤ 1 * gcirc t + 2.24e-4 *
      (1 / 2 * (t ^ 0 * Real.exp (-t ^ 2 / 2)) + 1 / 2 * (t ^ 1 * Real.exp (-t ^ 2 / 2))) := by
    intro t ht
    have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have h1 := abs_etaPlus_band ht
    have h2 := circ_div_sqrt_le ht
    have h3 := mul_div_sqrt_le ht (Real.exp_pos (-t ^ 2 / 2)).le
    have h4 : |HW.etaPlus t| / Real.sqrt t ≤ |HW.etaCirc t| / Real.sqrt t +
        2.24e-4 * (t * Real.exp (-t ^ 2 / 2) / Real.sqrt t) := by
      rw [mul_div_assoc', ← add_div]
      exact div_le_div_of_nonneg_right h1 hs0.le
    have e : (1 + t) / 2 * Real.exp (-t ^ 2 / 2) = 1 / 2 * (t ^ 0 * Real.exp (-t ^ 2 / 2)) +
        1 / 2 * (t ^ 1 * Real.exp (-t ^ 2 / 2)) := by ring
    nlinarith
  have h := HM.int_le_of_pt hG (fun t => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hpt
  unfold HM.n1h
  nlinarith [HM.sqrt_2pi_bounds.2]

/-! ## (5) The derivative norms and `c₀` -/

/-- `|η₊'(t)| ≤ (13753.65 + 1.65t²)e^{−t²/2}` for `t > 0`. -/
theorem abs_deriv_etaPlus_le {t : ℝ} (ht : 0 < t) :
    |deriv HW.etaPlus t| ≤ (13753.65 + 1.65 * t ^ 2) * Real.exp (-t ^ 2 / 2) := by
  rw [deriv_etaPlus]
  have h := abs_dEP_le ht
  have e : (13752 + 1.65 * (1 + t ^ 2)) * Real.exp (-t ^ 2 / 2) =
      (13753.65 + 1.65 * t ^ 2) * Real.exp (-t ^ 2 / 2) := by ring
  linarith

/-- **`|η₊'|₂ ≤ 13000`** (`|η₊'|₂² ≤ 13753.65²√π/2 + 45387.045√π/4 + 2.7225(3√π/8)`). -/
theorem l2_deriv_etaPlus_le : MajSp.l2 (deriv HW.etaPlus) ≤ 13000 := by
  have hG := HM.gi_lin (13753.65 ^ 2) 1 I0 (HM.gi_lin (2 * 13753.65 * 1.65) 2.7225 HM.I2 HM.I4)
  have hpt : ∀ t : ℝ, 0 < t → deriv HW.etaPlus t ^ 2 ≤ 13753.65 ^ 2 * (t ^ 0 * Real.exp (-t ^ 2)) +
      1 * (2 * 13753.65 * 1.65 * (t ^ 2 * Real.exp (-t ^ 2)) +
        2.7225 * (t ^ 4 * Real.exp (-t ^ 2))) := by
    intro t ht
    have h := abs_deriv_etaPlus_le ht
    rw [← sq_abs]
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    have e : ((13753.65 + 1.65 * t ^ 2) * Real.exp (-t ^ 2 / 2)) ^ 2 =
        13753.65 ^ 2 * (t ^ 0 * Real.exp (-t ^ 2)) + 1 * (2 * 13753.65 * 1.65 *
          (t ^ 2 * Real.exp (-t ^ 2)) + 2.7225 * (t ^ 4 * Real.exp (-t ^ 2))) := by
      rw [mul_pow, HM.exp_half_sq]
      ring
    linarith
  have h := HM.int_le_of_pt hG (fun t => sq_nonneg _) hpt
  unfold MajSp.l2
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith [HM.sqrt_pi_bounds.2]

/-- **`|η₊'/√t|₁ ≤ 40200`**: `13753.65e^{−t²/2}/√t ≤ 13753.65·1.6488·e^{−t}t^{−1/2}` (Euler at
`1/2`) and `1.65t²e^{−t²/2}/√t ≤ 1.65t(1+t)e^{−t²/2}/2`. -/
theorem n1h_deriv_etaPlus_le : HM.n1h (deriv HW.etaPlus) ≤ 40200 := by
  have hG := HM.gi_lin (13753.65 * 1.6488) (1.65 / 2) gam_half_gi (HM.gi_lin 1 1 HM.M1 HM.M2)
  have hpt : ∀ t : ℝ, 0 < t → |deriv HW.etaPlus t| / Real.sqrt t ≤ 13753.65 * 1.6488 *
      (Real.exp (-t) * t ^ ((1 : ℝ) / 2 - 1)) + 1.65 / 2 * (1 * (t ^ 1 *
        Real.exp (-t ^ 2 / 2)) + 1 * (t ^ 2 * Real.exp (-t ^ 2 / 2))) := by
    intro t ht
    have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have h := abs_deriv_etaPlus_le ht
    have hE0 : 0 < Real.exp (-t ^ 2 / 2) := Real.exp_pos _
    have hd := div_le_div_of_nonneg_right h hs0.le
    have hA : 13753.65 * Real.exp (-t ^ 2 / 2) / Real.sqrt t ≤
        13753.65 * 1.6488 * (Real.exp (-t) * t ^ ((1 : ℝ) / 2 - 1)) := by
      rw [← inv_sqrt_eq ht]
      have := exp_half_sq_le t
      have hi : 0 < 1 / Real.sqrt t := by positivity
      have e : 13753.65 * Real.exp (-t ^ 2 / 2) / Real.sqrt t =
          13753.65 * Real.exp (-t ^ 2 / 2) * (1 / Real.sqrt t) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this
        (by norm_num : (0 : ℝ) ≤ 13753.65)) hi.le
      linarith
    have hB : 1.65 * t ^ 2 * Real.exp (-t ^ 2 / 2) / Real.sqrt t ≤
        1.65 / 2 * (1 * (t ^ 1 * Real.exp (-t ^ 2 / 2)) + 1 * (t ^ 2 * Real.exp (-t ^ 2 / 2))) := by
      have h3 := mul_div_sqrt_le ht (mul_nonneg ht.le hE0.le)
      have e : 1.65 * t ^ 2 * Real.exp (-t ^ 2 / 2) / Real.sqrt t =
          1.65 * (t * (t * Real.exp (-t ^ 2 / 2)) / Real.sqrt t) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 1.65)
      have e2 : 1.65 * ((1 + t) / 2 * (t * Real.exp (-t ^ 2 / 2))) = 1.65 / 2 * (1 * (t ^ 1 *
          Real.exp (-t ^ 2 / 2)) + 1 * (t ^ 2 * Real.exp (-t ^ 2 / 2))) := by ring
      linarith
    have e : (13753.65 + 1.65 * t ^ 2) * Real.exp (-t ^ 2 / 2) / Real.sqrt t =
        13753.65 * Real.exp (-t ^ 2 / 2) / Real.sqrt t +
          1.65 * t ^ 2 * Real.exp (-t ^ 2 / 2) / Real.sqrt t := by ring
    linarith
  have h := HM.int_le_of_pt hG (fun t => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hpt
  unfold HM.n1h
  nlinarith [HM.sqrt_pi_bounds.2, HM.sqrt_2pi_bounds.2]

/-- **`|η₊'√t|₁ ≤ 15500`** (`√t ≤ (1+t)/2`). -/
theorem n1s_deriv_etaPlus_le : HM.n1s (deriv HW.etaPlus) ≤ 15500 := by
  have hG := HM.gi_lin (13753.65 / 2) (1.65 / 2) (HM.gi_lin 1 1 HM.M0 HM.M1)
    (HM.gi_lin 1 1 HM.M2 HM.M3)
  have hpt : ∀ t : ℝ, 0 < t → |deriv HW.etaPlus t| * Real.sqrt t ≤ 13753.65 / 2 *
      (1 * (t ^ 0 * Real.exp (-t ^ 2 / 2)) + 1 * (t ^ 1 * Real.exp (-t ^ 2 / 2))) + 1.65 / 2 *
        (1 * (t ^ 2 * Real.exp (-t ^ 2 / 2)) + 1 * (t ^ 3 * Real.exp (-t ^ 2 / 2))) := by
    intro t ht
    have h := abs_deriv_etaPlus_le ht
    have hsa := sqrt_le_avg ht.le
    have hE0 : 0 < Real.exp (-t ^ 2 / 2) := Real.exp_pos _
    have hP : 0 ≤ (13753.65 + 1.65 * t ^ 2) * Real.exp (-t ^ 2 / 2) := by positivity
    have p := mul_le_mul h hsa (Real.sqrt_nonneg t) hP
    have e : (13753.65 + 1.65 * t ^ 2) * Real.exp (-t ^ 2 / 2) * ((1 + t) / 2) =
        13753.65 / 2 * (1 * (t ^ 0 * Real.exp (-t ^ 2 / 2)) + 1 * (t ^ 1 *
          Real.exp (-t ^ 2 / 2))) + 1.65 / 2 * (1 * (t ^ 2 * Real.exp (-t ^ 2 / 2)) +
            1 * (t ^ 3 * Real.exp (-t ^ 2 / 2))) := by ring
    linarith
  have h := HM.int_le_of_pt hG (fun t => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hpt
  unfold HM.n1s
  nlinarith [HM.sqrt_2pi_bounds.2]

/-- **`|η₊√t|₁ ≤ 1.9`**. -/
theorem n1s_etaPlus_le : HM.n1s HW.etaPlus ≤ 1.9 := by
  have hG := HM.gi_lin (1.65 / 2) (1.65 / 2) HM.M1 HM.M2
  have hpt : ∀ t : ℝ, 0 < t → |HW.etaPlus t| * Real.sqrt t ≤ 1.65 / 2 *
      (t ^ 1 * Real.exp (-t ^ 2 / 2)) + 1.65 / 2 * (t ^ 2 * Real.exp (-t ^ 2 / 2)) := by
    intro t ht
    have h := abs_etaPlus_le ht
    have hsa := sqrt_le_avg ht.le
    have hP : 0 ≤ 1.65 * (t * Real.exp (-t ^ 2 / 2)) := by positivity
    have p := mul_le_mul h hsa (Real.sqrt_nonneg t) hP
    have e : 1.65 * (t * Real.exp (-t ^ 2 / 2)) * ((1 + t) / 2) = 1.65 / 2 *
        (t ^ 1 * Real.exp (-t ^ 2 / 2)) + 1.65 / 2 * (t ^ 2 * Real.exp (-t ^ 2 / 2)) := by ring
    linarith
  have h := HM.int_le_of_pt hG (fun t => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hpt
  unfold HM.n1s
  nlinarith [HM.sqrt_2pi_bounds.2]

/-- **`c₀(η₊, δ) ≤ 37200 + 12.2|δ|`**. -/
theorem c0_etaPlus_le (δ : ℝ) : HM.c0 HW.etaPlus δ ≤ 37200 + 12.2 * |δ| := by
  have h1 := n1h_deriv_etaPlus_le
  have h2 := n1s_deriv_etaPlus_le
  have h3 := n1h_etaPlus_le
  have h4 := n1s_etaPlus_le
  have hpd : 0 ≤ 2 * Real.pi * |δ| := by positivity
  have h5 : 2 * Real.pi * |δ| * (HM.n1h HW.etaPlus + HM.n1s HW.etaPlus) ≤
      2 * Real.pi * |δ| * (0.991 + 1.9) := mul_le_mul_of_nonneg_left (add_le_add h3 h4) hpd
  have hpi : 2 * Real.pi * |δ| * (0.991 + 1.9) ≤ 18.17 * |δ| := by
    have := Real.pi_lt_d6
    nlinarith [abs_nonneg δ]
  unfold HM.c0
  linarith

/-! ## (6) `PlusNormsL` -/

/-- **`PlusNorms` with the derivative conjuncts loosened** (the first three at Helfgott's
stated constants). -/
def PlusNormsL : Prop :=
  MajSp.l2 HW.etaPlus ≤ 0.80044 ∧ MajSp.l2 (HM.llog HW.etaPlus) ≤ 0.83 ∧
    HM.n1h HW.etaPlus ≤ 1.00007 ∧ MajSp.l2 (deriv HW.etaPlus) ≤ 13000 ∧
    ∀ δ : ℝ, HM.c0 HW.etaPlus δ ≤ 37200 + 12.2 * |δ|

/-- **`PlusNormsL` PROVED.** -/
theorem plusNormsL_holds : PlusNormsL :=
  ⟨l2_etaPlus_le, l2_llog_etaPlus_le, n1h_etaPlus_le.trans (by norm_num), l2_deriv_etaPlus_le,
    c0_etaPlus_le⟩

/-! ## (7) `prop:unease` at `PlusNormsL` (copy of `HM.plus_err` with the new residue term) -/

/-- The residue-and-`x^{−3/2}` numerator of `prop:unease` for `η₊` at `PlusNormsL`. -/
noncomputable def RplusL (q δ x : ℝ) : ℝ :=
  37200 + 12.2 * |δ| + (Real.log q + 8) * (13000 + 2 * Real.pi * |δ| * 0.80044) / Real.sqrt x

/-- **`prop:unease`, CORRECTED, at the PROVED `PlusReg` and `PlusNormsL`**: at `T ≥ 450`,
`T ≥ 200 + 4π²|δ|`, GRH to `T`: `|err| ≤ tailP + hbC(…; 0.80044, 0.83, 1.00007)/√x + RplusL/x`
(and `hbR` for a real `χ`). -/
theorem plus_errL (hEF : HM.ExplicitFormula) (hZC : HM.ZeroCount) (hHs : HM.Hausierer)
    (hG : HM.GarmolaDecr) (pd : HM.PlusDecay) (pt : HM.PlusTailInt)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : q ≤ 400000)
    {δ x T : ℝ} (hx : 1 ≤ x) (hT : 450 ≤ T) (hTd : 200 + 4 * Real.pi ^ 2 * |δ| ≤ T)
    (hgrh : HM.GRHTo χ T) :
    ‖MajSp.err HW.etaPlus χ δ x‖ ≤
        HM.tailP q T δ + HM.hbC q T 0.80044 0.83 1.00007 / Real.sqrt x + RplusL q δ x / x ∧
      (HM.IsRealChar χ → ‖MajSp.err HW.etaPlus χ δ x‖ ≤
        HM.tailP q T δ + HM.hbR q T 0.80044 0.83 1.00007 / Real.sqrt x + RplusL q δ x / x) := by
  obtain ⟨n2, nl, n1, nd, nc⟩ := plusNormsL_holds
  have pr := plusReg_holds
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqT : 37 ≤ (q : ℝ) * T := by nlinarith
  have hH := hHs hZC HW.etaPlus pr.2 q χ hχ δ T (by linarith) hqT hgrh
  have hTail := HM.plus_high hZC hG pd pt hχ hq hT hTd
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hlq : 0 ≤ Real.log q + 8 := by linarith [Real.log_nonneg hq1']
  have hR : HM.c0 HW.etaPlus δ + (Real.log q + 8) *
      (MajSp.l2 (deriv HW.etaPlus) + 2 * Real.pi * |δ| * MajSp.l2 HW.etaPlus) / Real.sqrt x ≤
        RplusL q δ x := by
    unfold RplusL
    have hpd : 0 ≤ 2 * Real.pi * |δ| := by positivity
    have h1 : MajSp.l2 (deriv HW.etaPlus) + 2 * Real.pi * |δ| * MajSp.l2 HW.etaPlus ≤
        13000 + 2 * Real.pi * |δ| * 0.80044 :=
      add_le_add nd (mul_le_mul_of_nonneg_left n2 hpd)
    have h2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hlq) hs0.le
    linarith [nc δ]
  have h0 : HW.etaPlus 0 = 0 := HW.etaPlus_of_nonpos le_rfl
  have hTb := HM.tailP_nonneg (q := (q : ℝ)) (δ := δ) hq1' hT
  refine ⟨HM.err_le_of_zero_sums hEF pr.1 h0 hχ hx hgrh
    (HM.hbC_nonneg hq1' hqT (by norm_num) (by norm_num) (by norm_num)) hTb
    (le_trans hH.1 (ENNReal.ofReal_le_ofReal (HM.hbC_mono hq1' hqT n2 nl n1))) hTail hR,
    fun hr => HM.err_le_of_zero_sums hEF pr.1 h0 hχ hx hgrh
      (HM.hbR_nonneg hq1' hqT (by norm_num) (by norm_num) (by norm_num)) hTb
      (le_trans (hH.2 hr) (ENNReal.ofReal_le_ofReal (HM.hbR_mono hq1' hqT n2 nl n1))) hTail hR⟩

/-! ## (8) Thm 1.4 RETYPED at `PlusNormsL`: the arithmetic -/

/-- `RplusL/x ≤ (0.03721 + 14.641/√q)/√x` (`|δ| ≤ 1.2·10⁶/q`, `x ≥ 10¹²`). -/
theorem Rplus_leL {Q r δ x : ℝ} (hQ : 1 ≤ Q) (hr : r ≤ 300000) (hQr : Q ≤ r)
    (hδ : |δ| ≤ 4 * r / Q) (hx : 10 ^ 12 ≤ x) :
    RplusL Q δ x / x ≤ (0.03721 + 14.641 * (1 / Real.sqrt Q)) / Real.sqrt x := by
  have hQ0 : 0 < Q := by linarith
  have hsx := HM.sqrt_x_ge' hx
  have hsx0 : 0 < Real.sqrt x := by linarith
  have hδ' : |δ| ≤ 1.2e6 * (1 / Q) := by
    have e : 1.2e6 * (1 / Q) = 1.2e6 / Q := by ring
    rw [e]
    exact hδ.trans (div_le_div_of_nonneg_right (by linarith) hQ0.le)
  have hlq := HM.logQ_le hQ (by linarith)
  have hlq0 : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hv : 0 ≤ 1 / Q := by positivity
  have h1 : 13000 + 2 * Real.pi * |δ| * 0.80044 ≤ 13000 + 5.0294 * (1.2e6 * (1 / Q)) := by
    have := mul_le_mul HM.twopi_plus hδ' (abs_nonneg δ) (by norm_num)
    linarith
  have hN : (Real.log Q + 8) * (13000 + 2 * Real.pi * |δ| * 0.80044) ≤
      21 * (13000 + 5.0294 * (1.2e6 * (1 / Q))) :=
    mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
  have hN2 : (Real.log Q + 8) * (13000 + 2 * Real.pi * |δ| * 0.80044) / Real.sqrt x ≤
      21 * (13000 + 5.0294 * (1.2e6 * (1 / Q))) / 1000000 :=
    div_le_div₀ (by positivity) hN (by norm_num) hsx
  have hR : RplusL Q δ x ≤ 37200 + 12.2 * (1.2e6 * (1 / Q)) +
      21 * (13000 + 5.0294 * (1.2e6 * (1 / Q))) / 1000000 := by
    unfold RplusL
    have := mul_le_mul_of_nonneg_left hδ' (by norm_num : (0 : ℝ) ≤ 12.2)
    linarith
  have hQs : 1 / Q ≤ 1 / Real.sqrt Q :=
    one_div_le_one_div_of_le (by positivity) (HM.sqrt_le_self' hQ)
  have hxx : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt (by linarith)).symm
  have hR2 : RplusL Q δ x / Real.sqrt x ≤ 0.03721 + 14.641 * (1 / Real.sqrt Q) := by
    have := div_le_div₀ (by positivity) hR (by norm_num : (0 : ℝ) < 1000000) hsx
    have e : (37200 + 12.2 * (1.2e6 * (1 / Q)) +
        21 * (13000 + 5.0294 * (1.2e6 * (1 / Q))) / 1000000) / 1000000 =
        0.0372 + 14.64 * (1 / Q) + 2.73e-7 + 126.74088 * (1 / Q) / 1000000 := by
      ring
    rw [e] at this
    linarith
  calc RplusL Q δ x / x = RplusL Q δ x / Real.sqrt x / Real.sqrt x := by
        rw [div_div, ← hxx]
    _ ≤ (0.03721 + 14.641 * (1 / Real.sqrt Q)) / Real.sqrt x :=
        div_le_div_of_nonneg_right hR2 hsx0.le

/-- **Thm 1.4 for general `q`, RETYPED, at `PlusNormsL`**: `769400/√q + 100.2 + 0.03721 +
14.641/√q ≤ 900000/√q + 52` for `√q ≤ 548` (margin `130585/√q − 48.24 ≥ 190`). -/
theorem malpor_gen_arithL {Q r δ x : ℝ} (hQ : 1 ≤ Q) (hr : r ≤ 300000) (hQr : Q ≤ r)
    (hδ : |δ| ≤ 4 * r / Q) (hx : 10 ^ 12 ≤ x) :
    HM.tailP Q (200 + 250 * r / Q) δ +
        HM.hbC Q (200 + 250 * r / Q) 0.80044 0.83 1.00007 / Real.sqrt x + RplusL Q δ x / x ≤
      6.18e-11 / Real.sqrt Q + 1.14e-9 / Q + (900000 / Real.sqrt Q + 52) / Real.sqrt x := by
  have h1 := HM.tailP_le hQ hr hQr hδ
  have h2 := HM.hbC_plus_le hQ hr hQr
  have h3 := Rplus_leL hQ hr hQr hδ hx
  have hsx0 : 0 < Real.sqrt x := by linarith [HM.sqrt_x_ge' hx]
  have hs548 : Real.sqrt Q ≤ 548 := (Real.sqrt_le_left (by norm_num)).mpr (by nlinarith)
  have hu : 1 / 548 ≤ 1 / Real.sqrt Q :=
    one_div_le_one_div_of_le (by linarith [HM.one_le_sqrt' hQ]) hs548
  have h4 := div_le_div_of_nonneg_right h2 hsx0.le
  have h5 : (769400 * (1 / Real.sqrt Q) + 100.2) / Real.sqrt x +
      (0.03721 + 14.641 * (1 / Real.sqrt Q)) / Real.sqrt x ≤
        (900000 * (1 / Real.sqrt Q) + 52) / Real.sqrt x := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hsx0.le
  have e : (900000 / Real.sqrt Q + 52) / Real.sqrt x =
      (900000 * (1 / Real.sqrt Q) + 52) / Real.sqrt x := by ring
  rw [e]
  linarith

/-- The residue terms at `q = 1`, `|δ| ≤ 6·10⁵`: `RplusL/x ≤ 7.4/√x`. -/
theorem Rplus_one_leL {δ x : ℝ} (hδ : |δ| ≤ 600000) (hx : 10 ^ 12 ≤ x) :
    RplusL 1 δ x / x ≤ 7.4 / Real.sqrt x := by
  have hsx := HM.sqrt_x_ge' hx
  have hsx0 : 0 < Real.sqrt x := by linarith
  have h1 : 13000 + 2 * Real.pi * |δ| * 0.80044 ≤ 13000 + 5.0294 * 600000 := by
    have := mul_le_mul HM.twopi_plus hδ (abs_nonneg δ) (by norm_num)
    linarith
  have hN : (0 + 8) * (13000 + 2 * Real.pi * |δ| * 0.80044) / Real.sqrt x ≤
      8 * (13000 + 5.0294 * 600000) / 1000000 :=
    div_le_div₀ (by norm_num) (by linarith) (by norm_num) hsx
  have hR1 : RplusL 1 δ x ≤ 7400000 := by
    unfold RplusL
    rw [Real.log_one]
    linarith
  have hxx : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt (by linarith)).symm
  have hR2 : RplusL 1 δ x / Real.sqrt x ≤ 7.4 := by
    have h0 : RplusL 1 δ x / Real.sqrt x ≤ 7400000 / Real.sqrt x :=
      div_le_div_of_nonneg_right hR1 hsx0.le
    have h2 : 7400000 / Real.sqrt x ≤ 7400000 / 1000000 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsx
    linarith
  calc RplusL 1 δ x / x = RplusL 1 δ x / Real.sqrt x / Real.sqrt x := by rw [div_div, ← hxx]
    _ ≤ 7.4 / Real.sqrt x := div_le_div_of_nonneg_right hR2 hsx0.le

/-- **Thm 1.4 at `q = 1`, RETYPED, at `PlusNormsL`**: `10⁻¹³ + (295900 + 7.4)/√x ≤ 3.34·10⁻¹¹ +
320000/√x`. -/
theorem malpor_one_arithL {δ x : ℝ} (hδ : |δ| ≤ 600000) (hx : 10 ^ 12 ≤ x) :
    HM.tailP 1 42000000 δ + HM.hbR 1 42000000 0.80044 0.83 1.00007 / Real.sqrt x +
        RplusL 1 δ x / x ≤ 3.34e-11 + 320000 / Real.sqrt x := by
  have hsx0 : 0 < Real.sqrt x := by linarith [HM.sqrt_x_ge' hx]
  have h1 := HM.tail_one_le hδ
  have h2 := div_le_div_of_nonneg_right HM.hbR_one_le hsx0.le
  have h3 := Rplus_one_leL hδ hx
  have h5 : 295900 / Real.sqrt x + 7.4 / Real.sqrt x ≤ 320000 / Real.sqrt x := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) hsx0.le
  linarith

/-! ## (9) `MR.MalporR η₊` from the links, `PlusReg` and `PlusNorms` supplied -/

/-- Thm 1.4's general clause at one conductor, at `PlusNormsL`. -/
theorem malpor_generalL (hEF : HM.ExplicitFormula) (hZC : HM.ZeroCount) (hHs : HM.Hausierer)
    (hG : HM.GarmolaDecr) (pd : HM.PlusDecay) (pt : HM.PlusTailInt)
    (pf : RT.PlattFull) {x : ℝ} (hx : 10 ^ 12 ≤ x) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq4 : q ≤ 400000) {r δ : ℝ}
    (hr : r ≤ 300000) (hqr : (q : ℝ) ≤ r) (hT : 200 + 250 * r / q ≤ RT.plattHeight q)
    (hδ : |δ| ≤ 4 * r / q) :
    ‖MajSp.err HW.etaPlus χ δ x‖ ≤
      6.18e-11 / Real.sqrt q + 1.14e-9 / q + (900000 / Real.sqrt q + 52) / Real.sqrt x := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hQ0 : (0 : ℝ) < q := by linarith
  have hTge : 450 ≤ 200 + 250 * r / q := by
    have : 250 ≤ 250 * r / q := by rw [le_div_iff₀ hQ0]; nlinarith
    linarith
  have hb := (plus_errL hEF hZC hHs hG pd pt hχ hq4 (le_trans (by norm_num) hx) hTge
    (HM.Td_ok hQ0 (by linarith) hδ) (HM.grh_of_platt pf hq4 hχ hT)).1
  exact hb.trans (malpor_gen_arithL hq1 hr hqr hδ hx)

/-- **`MR.MalporR η₊` — HelfMaj Thm 1.4 RETYPED — from `ExplicitFormula`, `ZeroCount`,
`Hausierer`, `GarmolaDecr`, `PlusDecay`, `PlusTailInt` and Platt**: `PlusReg` and the norms are
PROVED (`plusReg_holds`, `plusNormsL_holds`). -/
theorem malporR_of_linksL (hEF : HM.ExplicitFormula) (hZC : HM.ZeroCount) (hHs : HM.Hausierer)
    (hG : HM.GarmolaDecr) (pd : HM.PlusDecay) (pt : HM.PlusTailInt)
    (pf : RT.PlattFull) : MR.MalporR HW.etaPlus := by
  intro x hx q hq1 hodd hev χ hχ δ hδ
  haveI : NeZero q := ⟨by omega⟩
  refine ⟨?_, fun h1 => ?_⟩
  · rcases MajSp.gcd_two q with ⟨ho, hg⟩ | ⟨he, hg⟩
    · have hqr := hodd ho
      rw [hg, Nat.cast_one, mul_one] at hδ
      have hδ' : |δ| ≤ 4 * 150000 / (q : ℝ) := by
        rw [show (4 : ℝ) * 150000 = 600000 by norm_num]
        exact hδ
      have hT : 200 + 250 * 150000 / (q : ℝ) ≤ RT.plattHeight q := by
        rw [show (250 : ℝ) * 150000 = 3.75e7 by norm_num]
        exact RT.odd_height q ho
      exact malpor_generalL hEF hZC hHs hG pd pt pf hx hχ (by omega) (by norm_num)
        (by exact_mod_cast hqr) hT hδ'
    · have hqr := hev he
      rw [hg] at hδ
      have hδ' : |δ| ≤ 4 * 300000 / (q : ℝ) := by
        have e : (600000 : ℝ) * ((2 : ℕ) : ℝ) = 4 * 300000 := by norm_num
        rw [← e]
        exact hδ
      have hT : 200 + 250 * 300000 / (q : ℝ) ≤ RT.plattHeight q := by
        rw [show (250 : ℝ) * 300000 = 7.5e7 by norm_num]
        exact RT.even_height q he
      exact malpor_generalL hEF hZC hHs hG pd pt pf hx hχ (by omega) (by norm_num)
        (by exact_mod_cast hqr) hT hδ'
  · subst h1
    have hδ1 : |δ| ≤ 600000 := by
      have e : (600000 : ℝ) * ((Nat.gcd 1 2 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) = 600000 := by norm_num
      rw [e] at hδ
      exact hδ
    have hT : (42000000 : ℝ) ≤ RT.plattHeight 1 := by
      rw [PC.plattHeight_one]
      norm_num
    have hTd : 200 + 4 * Real.pi ^ 2 * |δ| ≤ 42000000 := by
      have hpi : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
      have := mul_le_mul hpi hδ1 (abs_nonneg δ) (by norm_num)
      nlinarith
    have hb := (plus_errL hEF hZC hHs hG pd pt hχ (by norm_num) (le_trans (by norm_num) hx)
      (by norm_num) hTd (HM.grh_of_platt pf (by norm_num) hχ hT)).2 (HM.isRealChar_one χ)
    rw [Nat.cast_one] at hb
    exact hb.trans (malpor_one_arithL hδ1 hx)

end Principia.Common.TernaryGoldbach.HP
