/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajMalReg
import Principia.Common.TernaryGoldbach.HelfMajPlusNorms

set_option autoImplicit false

/-!
# `HM.MalNorms` REPLACED by a proved `MalNormsL`; Prop 1.5 re-derived at it

**`malNormsL_holds : MalNormsL`** and **`malheurR_of_linksL`: `MR.MalheurR η₊` from
`ExplicitFormula`, `ZeroCount`, `Hausierer`, `GarmolaDecr`, `MalDecay`, `MalTailInt`, `MalMain`
and Platt** — `MalReg` (`HP.malReg_holds`) and the norms are supplied.

| conjunct (`ℓ = log x`) | `MalNorms` (stated) | `MalNormsL` (proved) |
|---|---|---|
| `|η₊,₂|₂` | `0.99811ℓ + 0.32612` | same |
| `|η₊,₂·log|₂` | `0.32612ℓ + 0.33816` | same |
| `|η₊,₂/√t|₁` | `1.24703ℓ + 0.40745` | same |
| `|η₊,₂'|₂` | `27.05ℓ + 9.872` | `560000(ℓ + 2)` |
| `c₀(η₊,₂, 0)` | `18.15014ℓ + 7.84532` | `1.6·10⁶(ℓ + 2)` |

**The three stated conjuncts are proved at Helfgott's (F13-corrected) constants, not through his
sup norms** (`eq:dalida`, `eq:gobmark` rest on the broken `eq:havana`). Ingredients:
`|η₊|_∞ ≤ 1.000137` (`HW.jorat_unif` at `BS.band_le`), `(ℓ + L)² ≤ 1.5ℓ² + 3L²`, and
* `∫ η₊² ≤ 0.80044²`, `∫ (η₊ log)² ≤ 0.83²` (`HP.PlusNormsL`): `|η₊,₂|₂² ≤ 0.96132ℓ² + 2.07`;
* the SHARP `∫ (η₊ log)² ≤ 0.05741` (`int_llog_etaPlus_sharp`: `log² ≤ (t−1)²/t` against
  `η∘² ≤ t⁶(2−t)⁶`, `∫₀²(t−1)²t⁵(2−t)⁶ = 512/9009`, plus the band) — Helfgott's
  `|η₊ log|_∞ ≤ 0.40742` is not needed: `|η₊,₂ log|₂² ≤ 0.08614ℓ² + 2.07`;
* `|η₊/√t|₁ ≤ 0.991`: `|η₊,₂/√t|₁ ≤ 0.99114ℓ + 3.18`.
Each closes because `ℓ ≥ 27` (`x ≥ 10¹²`) turns the slack in the `ℓ`-coefficient into room for
the constant.

**The derivative conjuncts are loose (from `HP.dE2_env`) and the consumer does not care**: they
enter `prop:konechno` only through `Rmal/x`, and `malheur_close` tolerates any `R ≤ 1.09·10⁸ℓ`.
At `MalNormsL`, `RmalL ≤ 1.6·10⁶(ℓ + 2) + 4.48(ℓ + 2) ≤ 1.75·10⁶ℓ` (`malheur_closeL`; was
`18.5ℓ`); the low-zero term `hbR ≤ 391ℓ` is unchanged (the first three conjuncts are the stated
ones). Prop 1.5's retyped constants `5·10⁻⁶ + 500/√x` still close: `391 + 1.75 ≤ 500` on the
`√x`-term.
-/

namespace Principia.Common.TernaryGoldbach.HP

open MeasureTheory Set Filter

/-! ## (1) `|η₊|_∞ ≤ 1.000137`, and the Gaussian moments needed -/

/-- `|h_H − h| ≤ 2.24·10⁻⁴` for EVERY real `t` (both vanish on `(−∞, 0]`). -/
theorem band_le_all (t : ℝ) : |HW.hH 200 t - HW.hFun t| ≤ 2.24e-4 := by
  rcases le_or_gt t 0 with ht | ht
  · rw [HW.hH_of_nonpos 200 ht, HW.hFun_of_nonpos ht, sub_zero, abs_zero]
    norm_num
  · exact BS.band_le t ht

/-- **`|η₊|_∞ ≤ 1.000137`** (`1 + 2.24·10⁻⁴e^{−1/2}`, `HW.jorat_unif`). -/
theorem abs_etaPlus_sup (t : ℝ) : |HW.etaPlus t| ≤ 1.000137 := by
  have h := HW.jorat_unif (HW.hH 200) 2.24e-4 (by norm_num) band_le_all t
  have he : Real.exp (-1 / 2) * Real.exp (1 / 2) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hg := HW.exp_half_gt
  have hp := Real.exp_pos (-1 / 2)
  have hb : Real.exp (-1 / 2) ≤ 0.6098 := by nlinarith
  exact h.trans (by linarith)

theorem etaPlus_sq_sup (t : ℝ) : HW.etaPlus t ^ 2 ≤ 1.000275 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (abs_etaPlus_sup t) 2
  rw [sq_abs] at h
  linarith

theorem gam_13_2 : Real.Gamma (13 / 2) = 10395 / 64 * Real.sqrt Real.pi := by
  have h1 : Real.Gamma (13 / 2) = 11 / 2 * Real.Gamma (11 / 2) := by
    rw [show (13 / 2 : ℝ) = 11 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
  have h2 : Real.Gamma (11 / 2) = 9 / 2 * Real.Gamma (9 / 2) := by
    rw [show (11 / 2 : ℝ) = 9 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
  have h3 : Real.Gamma (9 / 2) = 7 / 2 * Real.Gamma (7 / 2) := by
    rw [show (9 / 2 : ℝ) = 7 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
  rw [h1, h2, h3, HM.gam_7_2]
  ring

theorem I12 : HM.GI (fun t => t ^ 12 * Real.exp (-t ^ 2)) (10395 / 128 * Real.sqrt Real.pi) := by
  have h := HM.gm1 12
  rw [show (((12 : ℕ) : ℝ) + 1) / 2 = 13 / 2 by norm_num, gam_13_2] at h
  exact ⟨h.1, by rw [h.2]; ring⟩

theorem M6 : HM.GI (fun t => t ^ 6 * Real.exp (-t ^ 2 / 2))
    (15 / 2 * (Real.sqrt 2 * Real.sqrt Real.pi)) := by
  have h := HM.gm2 6
  rw [show (((6 : ℕ) : ℝ) + 1) / 2 = 7 / 2 by norm_num, HM.gam_7_2] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, show (6 + 1 : ℕ) = 2 * 3 + 1 from rfl, pow_succ, pow_mul, HM.sqrt2_sq]
  ring

theorem M7 : HM.GI (fun t => t ^ 7 * Real.exp (-t ^ 2 / 2)) 48 := by
  have h := HM.gm2 7
  rw [show (((7 : ℕ) : ℝ) + 1) / 2 = 3 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    HM.gam_3] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, show (7 + 1 : ℕ) = 2 * 4 from rfl, pow_mul, HM.sqrt2_sq]
  norm_num

/-- `∫ f² ≤ y²` from `|f|₂ ≤ y`. -/
theorem sq_int_of_l2 {f : ℝ → ℝ} {y : ℝ} (h : MajSp.l2 f ≤ y) (hy : 0 ≤ y) :
    ∫ t in Ioi (0 : ℝ), f t ^ 2 ≤ y ^ 2 := by
  unfold MajSp.l2 at h
  exact (Real.sqrt_le_left hy).mp h

/-! ## (2) The sharp `∫ (η₊ log)² ≤ 0.05741` -/

/-- `g_P(t) = (t−1)²t⁵max(2−t, 0)⁶`, a continuous majorant of `(η∘ log)²`. -/
noncomputable def gP (t : ℝ) : ℝ := (t - 1) ^ 2 * t ^ 5 * max (2 - t) 0 ^ 6

theorem continuous_gP : Continuous gP := by
  unfold gP
  fun_prop

/-- `∫₀^∞ g_P = ∫₀²(t−1)²t⁵(2−t)⁶ = 512/9009`. -/
theorem gi_gP : HM.GI gP (512 / 9009) := by
  have h2 : ∀ t : ℝ, 2 < t → gP t = 0 := fun t ht => by
    unfold gP
    rw [max_eq_right (by linarith)]
    ring
  refine ⟨EN.integrableOn_of_cont _ continuous_gP h2, ?_⟩
  rw [EN.setInt_Ioi_02 _ h2]
  have h : EqOn gP (fun u => ∑ k : Fin 14, (![0, 0, 0, 0, 0, 64, -320, 688, -832, 620, -292, 85,
      -14, 1] : Fin 14 → ℝ) k * u ^ (k : ℕ)) (uIcc 0 2) := by
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    unfold gP
    rw [max_eq_left (by linarith [hu.2])]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_succ]
    ring
  rw [intervalIntegral.integral_congr h, EN.int_poly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  norm_num

/-- `(log t·η∘(t))² ≤ g_P(t)`: `log² ≤ t + 1/t − 2 = (t−1)²/t`, `η∘² ≤ (t(2−t))⁶`. -/
theorem llog_circ_sq_le {t : ℝ} (ht : 0 < t) : (Real.log t * HW.etaCirc t) ^ 2 ≤ gP t := by
  rcases le_or_gt t 2 with h2 | h2
  · have hl := HM.log_sq_le ht
    have hl0 : 0 ≤ t + 1 / t - 2 := le_trans (sq_nonneg _) hl
    have hc := EN.etaCirc_sq_eq ht.le h2
    have hE : Real.exp (-(t - 1) ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
    have hc2 : HW.etaCirc t ^ 2 ≤ (1 - (t - 1) ^ 2) ^ 6 := by
      rw [hc]
      have : 0 ≤ (1 - (t - 1) ^ 2) ^ 6 := by positivity
      nlinarith
    rw [mul_pow]
    have p := mul_le_mul hl hc2 (sq_nonneg _) hl0
    have e : (t + 1 / t - 2) * (1 - (t - 1) ^ 2) ^ 6 = gP t := by
      unfold gP
      rw [max_eq_left (by linarith)]
      field_simp
      ring
    linarith
  · rw [EN.etaCirc_of_two_lt h2, mul_zero]
    unfold gP
    rw [max_eq_right (by linarith)]
    norm_num

/-- **`∫₀^∞ (η₊ log)² ≤ 0.05741`** (truth `0.0458`): `(a + b)² ≤ 1.01a² + 101b²` with
`a = η∘ log`, `b = (h_H − h)te^{−t²/2} log`. -/
theorem int_llog_etaPlus_sharp : ∫ t in Ioi (0 : ℝ), HM.llog HW.etaPlus t ^ 2 ≤ 0.05741 := by
  have hG := HM.gi_lin 1.01 (101 * (2.24e-4 : ℝ) ^ 2) gi_gP
    (HM.gi_lin 1 (-2) (HM.gi_lin 1 1 HM.I3 I1) HM.I2)
  have hpt : ∀ t : ℝ, 0 < t → HM.llog HW.etaPlus t ^ 2 ≤ 1.01 * gP t +
      101 * (2.24e-4 : ℝ) ^ 2 * (1 * (1 * (t ^ 3 * Real.exp (-t ^ 2)) +
        1 * (t ^ 1 * Real.exp (-t ^ 2))) + -2 * (t ^ 2 * Real.exp (-t ^ 2))) := by
    intro t ht
    have ha := llog_circ_sq_le ht
    have hl := HM.log_sq_le ht
    have hl0 : 0 ≤ t + 1 / t - 2 := le_trans (sq_nonneg _) hl
    have hd : (HW.hH 200 t - HW.hFun t) ^ 2 ≤ (2.24e-4 : ℝ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (BS.band_le t ht) 2
    have hw : (t * Real.exp (-t ^ 2 / 2)) ^ 2 = t ^ 2 * Real.exp (-t ^ 2) := by
      rw [mul_pow, HM.exp_half_sq]
    have hb : (Real.log t * ((HW.hH 200 t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2)))) ^ 2 ≤
        (2.24e-4 : ℝ) ^ 2 * (1 * (1 * (t ^ 3 * Real.exp (-t ^ 2)) +
          1 * (t ^ 1 * Real.exp (-t ^ 2))) + -2 * (t ^ 2 * Real.exp (-t ^ 2))) := by
      have e1 : (Real.log t * ((HW.hH 200 t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2)))) ^ 2 =
          Real.log t ^ 2 * ((HW.hH 200 t - HW.hFun t) ^ 2 * (t ^ 2 * Real.exp (-t ^ 2))) := by
        rw [← hw]
        ring
      have hE : 0 ≤ t ^ 2 * Real.exp (-t ^ 2) := by positivity
      have p1 := mul_le_mul_of_nonneg_right hd hE
      have p2 := mul_le_mul hl p1 (by positivity) hl0
      have e2 : (t + 1 / t - 2) * ((2.24e-4 : ℝ) ^ 2 * (t ^ 2 * Real.exp (-t ^ 2))) =
          (2.24e-4 : ℝ) ^ 2 * (1 * (1 * (t ^ 3 * Real.exp (-t ^ 2)) +
            1 * (t ^ 1 * Real.exp (-t ^ 2))) + -2 * (t ^ 2 * Real.exp (-t ^ 2))) := by
        field_simp
        ring
      rw [e1]
      linarith
    have hsplit : HM.llog HW.etaPlus t = Real.log t * HW.etaCirc t +
        Real.log t * ((HW.hH 200 t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2))) := by
      unfold HM.llog
      rw [etaPlus_split]
      ring
    rw [hsplit]
    nlinarith [sq_nonneg (0.1 * (Real.log t * HW.etaCirc t) -
      10 * (Real.log t * ((HW.hH 200 t - HW.hFun t) * (t * Real.exp (-t ^ 2 / 2)))))]
  have h := HM.int_le_of_pt hG (fun t => sq_nonneg _) hpt
  nlinarith [HM.sqrt_pi_bounds.1]

/-! ## (3) The three stated `MalNorms` conjuncts -/

/-- `ℓ = log x ≥ 27` for `x ≥ 10¹²`. -/
theorem log_x_ge {x : ℝ} (hx : 10 ^ 12 ≤ x) : 27 ≤ Real.log x := by
  have h := HM.nat_le_log 27 (y := x) (le_trans (by norm_num) hx)
  push_cast at h
  exact h

/-- `(ℓ + L)² ≤ 1.5ℓ² + 3L²`. -/
theorem sq_add_le (ℓ L : ℝ) : (ℓ + L) ^ 2 ≤ 1.5 * ℓ ^ 2 + 3 * L ^ 2 := by
  nlinarith [sq_nonneg (ℓ - 2 * L)]

theorem int_etaPlus_sq : Integrable (fun t => HW.etaPlus t ^ 2) (volume.restrict (Ioi 0)) :=
  (memLp_two_iff_integrable_sq contDiff_etaPlus.continuous.measurable.aestronglyMeasurable).mp
    plusReg_holds.2.2.1

theorem int_llog_etaPlus_sq :
    Integrable (fun t => HM.llog HW.etaPlus t ^ 2) (volume.restrict (Ioi 0)) :=
  (memLp_two_iff_integrable_sq (Real.measurable_log.mul
    contDiff_etaPlus.continuous.measurable).aestronglyMeasurable).mp plusReg_holds.2.2.2.2.1

/-- **`|η₊,₂|₂ ≤ 0.99811ℓ + 0.32612`** (the stated constant). -/
theorem l2_eta2x_le {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    MajSp.l2 (HM.eta2x x) ≤ 0.99811 * Real.log x + 0.32612 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hℓ := log_x_ge hx
  have hg : Integrable (fun t => 1.5 * 1.000275 * Real.log x ^ 2 * HW.etaPlus t ^ 2 +
      3 * 1.000275 * HM.llog HW.etaPlus t ^ 2) (volume.restrict (Ioi 0)) :=
    (int_etaPlus_sq.const_mul (1.5 * 1.000275 * Real.log x ^ 2)).add
      (int_llog_etaPlus_sq.const_mul (3 * 1.000275))
  have hpt : ∀ t ∈ Ioi (0 : ℝ), HM.eta2x x t ^ 2 ≤ 1.5 * 1.000275 * Real.log x ^ 2 *
      HW.etaPlus t ^ 2 + 3 * 1.000275 * HM.llog HW.etaPlus t ^ 2 := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hS2 := etaPlus_sq_sup t
    have hq := sq_add_le (Real.log x) (Real.log t)
    have hP0 : 0 ≤ HW.etaPlus t ^ 2 := sq_nonneg _
    unfold HM.eta2x HM.llog
    rw [Real.log_mul hx0.ne' ht0.ne']
    calc (HW.etaPlus t ^ 2 * (Real.log x + Real.log t)) ^ 2
        = HW.etaPlus t ^ 2 * (HW.etaPlus t ^ 2 * (Real.log x + Real.log t) ^ 2) := by ring
      _ ≤ HW.etaPlus t ^ 2 * (1.000275 * (1.5 * Real.log x ^ 2 + 3 * Real.log t ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hS2 hq (sq_nonneg _) (by norm_num)) hP0
      _ = 1.5 * 1.000275 * Real.log x ^ 2 * HW.etaPlus t ^ 2 +
            3 * 1.000275 * (Real.log t * HW.etaPlus t) ^ 2 := by ring
  have hI := integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg _) hg
    (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  rw [integral_add (int_etaPlus_sq.const_mul _) (int_llog_etaPlus_sq.const_mul _),
    integral_const_mul, integral_const_mul] at hI
  have h1 := sq_int_of_l2 l2_etaPlus_le (by norm_num)
  have h2 := sq_int_of_l2 l2_llog_etaPlus_le (by norm_num)
  have hL2 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
  have p1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1.5 * 1.000275 *
    Real.log x ^ 2)
  unfold MajSp.l2
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith

/-- **`|η₊,₂·log|₂ ≤ 0.32612ℓ + 0.33816`** (the stated, F13-corrected constant). -/
theorem l2_llog_eta2x_le {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    MajSp.l2 (HM.llog (HM.eta2x x)) ≤ 0.32612 * Real.log x + 0.33816 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hℓ := log_x_ge hx
  have hG := HM.gi_lin 1 (-4) (HM.gi_lin 1 6 (HM.gi_lin 1 (-4) (HM.gi_lin 1 1 HM.I6 HM.I2)
    HM.I3) HM.I4) HM.I5
  have hg : Integrable (fun t => 1.5 * 1.000275 * Real.log x ^ 2 * HM.llog HW.etaPlus t ^ 2 +
      3 * 7.41200625 * (1 * (1 * (1 * (1 * (t ^ 6 * Real.exp (-t ^ 2)) +
        1 * (t ^ 2 * Real.exp (-t ^ 2))) + -4 * (t ^ 3 * Real.exp (-t ^ 2))) +
          6 * (t ^ 4 * Real.exp (-t ^ 2))) + -4 * (t ^ 5 * Real.exp (-t ^ 2))))
      (volume.restrict (Ioi 0)) :=
    (int_llog_etaPlus_sq.const_mul (1.5 * 1.000275 * Real.log x ^ 2)).add
      (hG.1.const_mul (3 * 7.41200625))
  have hpt : ∀ t ∈ Ioi (0 : ℝ), HM.llog (HM.eta2x x) t ^ 2 ≤
      1.5 * 1.000275 * Real.log x ^ 2 * HM.llog HW.etaPlus t ^ 2 + 3 * 7.41200625 *
        (1 * (1 * (1 * (1 * (t ^ 6 * Real.exp (-t ^ 2)) + 1 * (t ^ 2 * Real.exp (-t ^ 2))) +
          -4 * (t ^ 3 * Real.exp (-t ^ 2))) + 6 * (t ^ 4 * Real.exp (-t ^ 2))) +
            -4 * (t ^ 5 * Real.exp (-t ^ 2))) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hS2 := etaPlus_sq_sup t
    have hq := sq_add_le (Real.log x) (Real.log t)
    have hl := HM.log_sq_le ht0
    have hl0 : 0 ≤ t + 1 / t - 2 := le_trans (sq_nonneg _) hl
    have hP := etaPlus_sq_le ht0
    have hE : Real.exp (-t ^ 2) ^ 2 ≤ Real.exp (-t ^ 2) := by
      rw [sq, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t])
    -- the `L⁴ η₊⁴` piece
    have h4 : Real.log t ^ 4 * HW.etaPlus t ^ 4 ≤ 7.41200625 * ((t - 1) ^ 4 * t ^ 2 *
        Real.exp (-t ^ 2)) := by
      have a1 : Real.log t ^ 4 ≤ (t + 1 / t - 2) ^ 2 := by
        have := pow_le_pow_left₀ (sq_nonneg _) hl 2
        rw [← pow_mul] at this
        exact this
      have a2 : HW.etaPlus t ^ 4 ≤ (2.7225 * (t ^ 2 * Real.exp (-t ^ 2))) ^ 2 := by
        have := pow_le_pow_left₀ (sq_nonneg _) hP 2
        rw [← pow_mul] at this
        exact this
      have p := mul_le_mul a1 a2 (by positivity) (by positivity)
      have e : (t + 1 / t - 2) ^ 2 * (2.7225 * (t ^ 2 * Real.exp (-t ^ 2))) ^ 2 =
          7.41200625 * ((t - 1) ^ 4 * t ^ 2 * Real.exp (-t ^ 2) ^ 2) := by
        field_simp
        ring
      have hE' := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ 7.41200625 *
        ((t - 1) ^ 4 * t ^ 2))
      nlinarith
    have hdef : HM.llog (HM.eta2x x) t = Real.log t * (HW.etaPlus t ^ 2 * Real.log (x * t)) := rfl
    have hdef2 : HM.llog HW.etaPlus t = Real.log t * HW.etaPlus t := rfl
    rw [hdef, hdef2, Real.log_mul hx0.ne' ht0.ne']
    have hP0 : 0 ≤ HW.etaPlus t ^ 2 := sq_nonneg _
    have hL0 : 0 ≤ Real.log t ^ 2 := sq_nonneg _
    have k1 : (Real.log t * (HW.etaPlus t ^ 2 * (Real.log x + Real.log t))) ^ 2 ≤
        Real.log t ^ 2 * HW.etaPlus t ^ 2 * (HW.etaPlus t ^ 2 *
          (1.5 * Real.log x ^ 2 + 3 * Real.log t ^ 2)) := by
      have e : (Real.log t * (HW.etaPlus t ^ 2 * (Real.log x + Real.log t))) ^ 2 =
          Real.log t ^ 2 * HW.etaPlus t ^ 2 * (HW.etaPlus t ^ 2 *
            (Real.log x + Real.log t) ^ 2) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hP0) (by positivity)
    have k2 : Real.log t ^ 2 * HW.etaPlus t ^ 2 * (HW.etaPlus t ^ 2 * (1.5 * Real.log x ^ 2)) ≤
        1.5 * 1.000275 * Real.log x ^ 2 * (Real.log t * HW.etaPlus t) ^ 2 := by
      have e : Real.log t ^ 2 * HW.etaPlus t ^ 2 * (HW.etaPlus t ^ 2 * (1.5 * Real.log x ^ 2)) =
          HW.etaPlus t ^ 2 * (1.5 * Real.log x ^ 2 * (Real.log t * HW.etaPlus t) ^ 2) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_right hS2 (by positivity : (0 : ℝ) ≤ 1.5 * Real.log x ^ 2 *
        (Real.log t * HW.etaPlus t) ^ 2)
      linarith
    have e3 : (1 * (1 * (1 * (1 * (t ^ 6 * Real.exp (-t ^ 2)) + 1 * (t ^ 2 * Real.exp (-t ^ 2))) +
        -4 * (t ^ 3 * Real.exp (-t ^ 2))) + 6 * (t ^ 4 * Real.exp (-t ^ 2))) +
          -4 * (t ^ 5 * Real.exp (-t ^ 2))) = (t - 1) ^ 4 * t ^ 2 * Real.exp (-t ^ 2) := by ring
    rw [e3]
    nlinarith
  have hI := integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg _) hg
    (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  rw [integral_add (int_llog_etaPlus_sq.const_mul _) (hG.1.const_mul _), integral_const_mul,
    integral_const_mul, hG.2] at hI
  have h1 := int_llog_etaPlus_sharp
  have hL2 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
  have p1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1.5 * 1.000275 *
    Real.log x ^ 2)
  have hsp := HM.sqrt_pi_bounds.2
  unfold MajSp.l2
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith

/-- **`|η₊,₂/√t|₁ ≤ 1.24703ℓ + 0.40745`** (the stated constant). -/
theorem n1h_eta2x_le {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    HM.n1h (HM.eta2x x) ≤ 1.24703 * Real.log x + 0.40745 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hℓ := log_x_ge hx
  have hreg := plusReg_holds.2
  have i1 : Integrable (fun t => |HW.etaPlus t| / Real.sqrt t) (volume.restrict (Ioi 0)) := by
    refine (hreg.2.2.2.2.1.abs).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ => ?_)
    change |HW.etaPlus t / Real.sqrt t| = |HW.etaPlus t| / Real.sqrt t
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg t)]
  have hG := HM.gi_lin 1 1 (HM.gi_lin 1 1 (HM.gi_lin 1 1 I0 I1) HM.I2) HM.I3
  have hg : Integrable (fun t => Real.log x * 1.000137 * (|HW.etaPlus t| / Real.sqrt t) +
      2.7225 / 2 * (1 * (1 * (1 * (t ^ 0 * Real.exp (-t ^ 2)) + 1 * (t ^ 1 * Real.exp (-t ^ 2))) +
        1 * (t ^ 2 * Real.exp (-t ^ 2))) + 1 * (t ^ 3 * Real.exp (-t ^ 2))))
      (volume.restrict (Ioi 0)) :=
    (i1.const_mul (Real.log x * 1.000137)).add (hG.1.const_mul (2.7225 / 2))
  have hpt : ∀ t ∈ Ioi (0 : ℝ), |HM.eta2x x t| / Real.sqrt t ≤
      Real.log x * 1.000137 * (|HW.etaPlus t| / Real.sqrt t) + 2.7225 / 2 *
        (1 * (1 * (1 * (t ^ 0 * Real.exp (-t ^ 2)) + 1 * (t ^ 1 * Real.exp (-t ^ 2))) +
          1 * (t ^ 2 * Real.exp (-t ^ 2))) + 1 * (t ^ 3 * Real.exp (-t ^ 2))) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hS := abs_etaPlus_sup t
    have hP := etaPlus_sq_le ht0
    have hl := HM.abs_log_le ht0
    have hℓ0 : 0 ≤ Real.log x := by linarith
    have hE0 : 0 ≤ Real.exp (-t ^ 2) := (Real.exp_pos _).le
    unfold HM.eta2x
    rw [Real.log_mul hx0.ne' ht0.ne', abs_mul, abs_of_nonneg (sq_nonneg _)]
    have a1 : HW.etaPlus t ^ 2 * |Real.log x + Real.log t| ≤
        Real.log x * 1.000137 * |HW.etaPlus t| + HW.etaPlus t ^ 2 * |Real.log t| := by
      have b1 : |Real.log x + Real.log t| ≤ Real.log x + |Real.log t| := by
        have := abs_add_le (Real.log x) (Real.log t)
        rw [abs_of_nonneg hℓ0] at this
        exact this
      have b2 : HW.etaPlus t ^ 2 ≤ 1.000137 * |HW.etaPlus t| := by
        rw [← sq_abs, sq]
        exact mul_le_mul_of_nonneg_right hS (abs_nonneg _)
      have := mul_le_mul_of_nonneg_left b1 (sq_nonneg (HW.etaPlus t))
      nlinarith [abs_nonneg (HW.etaPlus t)]
    have a2 : HW.etaPlus t ^ 2 * |Real.log t| ≤
        t * ((t ^ 2 + 1) * (2.7225 * Real.exp (-t ^ 2))) := by
      have := mul_le_mul hP hl (abs_nonneg _) (by positivity)
      have e : 2.7225 * (t ^ 2 * Real.exp (-t ^ 2)) * (t + 1 / t) =
          t * ((t ^ 2 + 1) * (2.7225 * Real.exp (-t ^ 2))) := by
        field_simp
      linarith
    have a3 := mul_div_sqrt_le ht0 (by positivity : (0 : ℝ) ≤ (t ^ 2 + 1) * (2.7225 *
      Real.exp (-t ^ 2)))
    have a4 : HW.etaPlus t ^ 2 * |Real.log x + Real.log t| / Real.sqrt t ≤
        Real.log x * 1.000137 * (|HW.etaPlus t| / Real.sqrt t) +
          t * ((t ^ 2 + 1) * (2.7225 * Real.exp (-t ^ 2))) / Real.sqrt t := by
      rw [mul_div_assoc', ← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hs0.le
    have e : (1 + t) / 2 * ((t ^ 2 + 1) * (2.7225 * Real.exp (-t ^ 2))) = 2.7225 / 2 *
        (1 * (1 * (1 * (t ^ 0 * Real.exp (-t ^ 2)) + 1 * (t ^ 1 * Real.exp (-t ^ 2))) +
          1 * (t ^ 2 * Real.exp (-t ^ 2))) + 1 * (t ^ 3 * Real.exp (-t ^ 2))) := by ring
    linarith
  have hI := integral_mono_of_nonneg (ae_of_all _ fun t =>
    div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hg
    (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  rw [integral_add (i1.const_mul _) (hG.1.const_mul _), integral_const_mul, integral_const_mul,
    hG.2] at hI
  have h1 := n1h_etaPlus_le
  unfold HM.n1h at h1 ⊢
  have p1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ Real.log x * 1.000137)
  have hsp := HM.sqrt_pi_bounds.2
  nlinarith

/-! ## (4) The derivative conjuncts -/

/-- **`|η₊,₂'|₂ ≤ 560000(ℓ + 2)`** (`dE2_env`; `∫(1 + t⁶)²e^{−t²} = √π(1/2 + 15/8 + 10395/128)`). -/
theorem l2_deriv_eta2x_le {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    MajSp.l2 (deriv (HM.eta2x x)) ≤ 560000 * (Real.log x + 2) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hℓ := log_x_ge hx
  have hG := gi_smul ((46000 * (Real.log x + 2)) ^ 2) (HM.gi_lin 1 1 (HM.gi_lin 1 2 I0 HM.I6) I12)
  have hpt : ∀ t : ℝ, 0 < t → deriv (HM.eta2x x) t ^ 2 ≤ (46000 * (Real.log x + 2)) ^ 2 *
      (1 * (1 * (t ^ 0 * Real.exp (-t ^ 2)) + 2 * (t ^ 6 * Real.exp (-t ^ 2))) +
        1 * (t ^ 12 * Real.exp (-t ^ 2))) := by
    intro t ht
    rw [deriv_eta2x hx0]
    have h := dE2_env hx1 ht
    rw [← sq_abs]
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    have e : (46000 * (Real.log x + 2) * ((1 + t ^ 6) * Real.exp (-t ^ 2 / 2))) ^ 2 =
        (46000 * (Real.log x + 2)) ^ 2 * (1 * (1 * (t ^ 0 * Real.exp (-t ^ 2)) +
          2 * (t ^ 6 * Real.exp (-t ^ 2))) + 1 * (t ^ 12 * Real.exp (-t ^ 2))) := by
      rw [mul_pow, mul_pow, mul_pow, HM.exp_half_sq]
      ring
    linarith
  have h := HM.int_le_of_pt hG (fun t => sq_nonneg _) hpt
  have hsp := HM.sqrt_pi_bounds.2
  have hA : 0 ≤ (46000 * (Real.log x + 2)) ^ 2 := sq_nonneg _
  have hv : 1 * (1 * (Real.sqrt Real.pi / 2) + 2 * (15 / 16 * Real.sqrt Real.pi)) +
      1 * (10395 / 128 * Real.sqrt Real.pi) ≤ 148.2 := by nlinarith
  have p := mul_le_mul_of_nonneg_left hv hA
  unfold MajSp.l2
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith

/-- **`|η₊,₂'/√t|₁ ≤ 46000(ℓ + 2)(1.6488√π + (8 + 7.5√(2π))/2)`**. -/
theorem n1h_deriv_eta2x_le {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    HM.n1h (deriv (HM.eta2x x)) ≤ 46000 * (Real.log x + 2) * 16.33 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hℓ := log_x_ge hx
  have hD0 : 0 ≤ 46000 * (Real.log x + 2) := by positivity
  have hG := gi_smul (46000 * (Real.log x + 2))
    (HM.gi_lin 1.6488 (1 / 2) gam_half_gi (HM.gi_lin 1 1 HM.M5 M6))
  have hpt : ∀ t : ℝ, 0 < t → |deriv (HM.eta2x x) t| / Real.sqrt t ≤
      46000 * (Real.log x + 2) * (1.6488 * (Real.exp (-t) * t ^ ((1 : ℝ) / 2 - 1)) +
        1 / 2 * (1 * (t ^ 5 * Real.exp (-t ^ 2 / 2)) + 1 * (t ^ 6 * Real.exp (-t ^ 2 / 2)))) := by
    intro t ht
    rw [deriv_eta2x hx0]
    have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have h := dE2_env hx1 ht
    have hE0 : 0 < Real.exp (-t ^ 2 / 2) := Real.exp_pos _
    have hd := div_le_div_of_nonneg_right h hs0.le
    have hA : Real.exp (-t ^ 2 / 2) / Real.sqrt t ≤
        1.6488 * (Real.exp (-t) * t ^ ((1 : ℝ) / 2 - 1)) := by
      rw [← inv_sqrt_eq ht, div_eq_mul_one_div]
      have hi : 0 < 1 / Real.sqrt t := by positivity
      have := mul_le_mul_of_nonneg_right (exp_half_sq_le t) hi.le
      linarith
    have hB : t ^ 6 * Real.exp (-t ^ 2 / 2) / Real.sqrt t ≤
        1 / 2 * (1 * (t ^ 5 * Real.exp (-t ^ 2 / 2)) + 1 * (t ^ 6 * Real.exp (-t ^ 2 / 2))) := by
      have h3 := mul_div_sqrt_le ht (by positivity : (0 : ℝ) ≤ t ^ 5 * Real.exp (-t ^ 2 / 2))
      have e : t ^ 6 * Real.exp (-t ^ 2 / 2) = t * (t ^ 5 * Real.exp (-t ^ 2 / 2)) := by ring
      rw [e]
      have e2 : (1 + t) / 2 * (t ^ 5 * Real.exp (-t ^ 2 / 2)) = 1 / 2 * (1 * (t ^ 5 *
          Real.exp (-t ^ 2 / 2)) + 1 * (t ^ 6 * Real.exp (-t ^ 2 / 2))) := by ring
      linarith
    have e : 46000 * (Real.log x + 2) * ((1 + t ^ 6) * Real.exp (-t ^ 2 / 2)) / Real.sqrt t =
        46000 * (Real.log x + 2) * (Real.exp (-t ^ 2 / 2) / Real.sqrt t +
          t ^ 6 * Real.exp (-t ^ 2 / 2) / Real.sqrt t) := by ring
    have := mul_le_mul_of_nonneg_left (add_le_add hA hB) hD0
    linarith
  have h := HM.int_le_of_pt hG (fun t => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hpt
  have hsp := HM.sqrt_pi_bounds.2
  have hs2 := HM.sqrt_2pi_bounds.2
  have hv : 1.6488 * Real.sqrt Real.pi + 1 / 2 * (1 * 8 + 1 * (15 / 2 * (Real.sqrt 2 *
      Real.sqrt Real.pi))) ≤ 16.33 := by nlinarith
  have p := mul_le_mul_of_nonneg_left hv hD0
  unfold HM.n1h
  nlinarith

/-- **`|η₊,₂'√t|₁ ≤ 46000(ℓ + 2)(M₀ + M₁ + M₆ + M₇)/2`**. -/
theorem n1s_deriv_eta2x_le {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    HM.n1s (deriv (HM.eta2x x)) ≤ 46000 * (Real.log x + 2) * 34.53 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hℓ := log_x_ge hx
  have hD0 : 0 ≤ 46000 * (Real.log x + 2) := by positivity
  have hG := gi_smul (46000 * (Real.log x + 2) / 2)
    (HM.gi_lin 1 1 (HM.gi_lin 1 1 (HM.gi_lin 1 1 HM.M0 HM.M1) M6) M7)
  have hpt : ∀ t : ℝ, 0 < t → |deriv (HM.eta2x x) t| * Real.sqrt t ≤
      46000 * (Real.log x + 2) / 2 * (1 * (1 * (1 * (t ^ 0 * Real.exp (-t ^ 2 / 2)) +
        1 * (t ^ 1 * Real.exp (-t ^ 2 / 2))) + 1 * (t ^ 6 * Real.exp (-t ^ 2 / 2))) +
          1 * (t ^ 7 * Real.exp (-t ^ 2 / 2))) := by
    intro t ht
    rw [deriv_eta2x hx0]
    have h := dE2_env hx1 ht
    have hsa := sqrt_le_avg ht.le
    have hP : 0 ≤ 46000 * (Real.log x + 2) * ((1 + t ^ 6) * Real.exp (-t ^ 2 / 2)) := by
      positivity
    have p := mul_le_mul h hsa (Real.sqrt_nonneg t) hP
    have e : 46000 * (Real.log x + 2) * ((1 + t ^ 6) * Real.exp (-t ^ 2 / 2)) * ((1 + t) / 2) =
        46000 * (Real.log x + 2) / 2 * (1 * (1 * (1 * (t ^ 0 * Real.exp (-t ^ 2 / 2)) +
          1 * (t ^ 1 * Real.exp (-t ^ 2 / 2))) + 1 * (t ^ 6 * Real.exp (-t ^ 2 / 2))) +
            1 * (t ^ 7 * Real.exp (-t ^ 2 / 2))) := by ring
    linarith
  have h := HM.int_le_of_pt hG (fun t => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hpt
  have hs2 := HM.sqrt_2pi_bounds.2
  have hv : 1 * (1 * (1 * (Real.sqrt 2 * Real.sqrt Real.pi / 2) + 1 * 1) +
      1 * (15 / 2 * (Real.sqrt 2 * Real.sqrt Real.pi))) + 1 * 48 ≤ 2 * 34.53 := by nlinarith
  have p := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ 46000 * (Real.log x + 2) / 2)
  unfold HM.n1s
  nlinarith

/-- **`c₀(η₊,₂, 0) ≤ 1.6·10⁶(ℓ + 2)`**. -/
theorem c0_eta2x_le {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    HM.c0 (HM.eta2x x) 0 ≤ 1.6e6 * (Real.log x + 2) := by
  have h1 := n1h_deriv_eta2x_le hx
  have h2 := n1s_deriv_eta2x_le hx
  have hℓ := log_x_ge hx
  unfold HM.c0
  rw [abs_zero, mul_zero, zero_mul, add_zero]
  nlinarith

/-! ## (5) `MalNormsL` -/

/-- **`MalNorms` with the derivative conjuncts loosened** (the first three at Helfgott's
F13-corrected constants). -/
def MalNormsL : Prop :=
  ∀ x : ℝ, 10 ^ 12 ≤ x →
    MajSp.l2 (HM.eta2x x) ≤ 0.99811 * Real.log x + 0.32612 ∧
      MajSp.l2 (HM.llog (HM.eta2x x)) ≤ 0.32612 * Real.log x + 0.33816 ∧
      HM.n1h (HM.eta2x x) ≤ 1.24703 * Real.log x + 0.40745 ∧
      MajSp.l2 (deriv (HM.eta2x x)) ≤ 560000 * (Real.log x + 2) ∧
      HM.c0 (HM.eta2x x) 0 ≤ 1.6e6 * (Real.log x + 2)

/-- **`MalNormsL` PROVED.** -/
theorem malNormsL_holds : MalNormsL := fun _ hx =>
  ⟨l2_eta2x_le hx, l2_llog_eta2x_le hx, n1h_eta2x_le hx, l2_deriv_eta2x_le hx, c0_eta2x_le hx⟩

/-! ## (6) Prop 1.5 RETYPED at `MalNormsL` (copies of `HM.mal_err`, `HM.malheur_close`,
`HM.malheurAt_of_links` with the new residue term) -/

/-- The residue numerator of `prop:konechno` at `MalNormsL` (`q = 1`, `δ = 0`). -/
noncomputable def RmalL (x : ℝ) : ℝ :=
  1.6e6 * (Real.log x + 2) + 8 * (560000 * (Real.log x + 2)) / Real.sqrt x

/-- **`prop:konechno`, CORRECTED, at the PROVED `MalReg` and `MalNormsL`.** -/
theorem mal_errL (hEF : HM.ExplicitFormula) (hZC : HM.ZeroCount) (hHs : HM.Hausierer)
    (hG : HM.GarmolaDecr) (md : HM.MalDecay) (mt : HM.MalTailInt) (pf : RT.PlattFull)
    {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    ‖MajSp.err (HM.eta2x x) (1 : DirichletCharacter ℂ 1) 0 x‖ ≤
      (1e-12 * Real.log x + 2 * HM.fmal x 450 * HM.gZ 1 450) +
        HM.hbR 1 450 (0.99811 * Real.log x + 0.32612) (0.32612 * Real.log x + 0.33816)
          (1.24703 * Real.log x + 0.40745) / Real.sqrt x + RmalL x / x := by
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have hL0 := Real.log_nonneg hx1
  have mr := malReg_holds
  obtain ⟨n2, nl, n1, nd, nc⟩ := malNormsL_holds x hx
  have hT : (450 : ℝ) ≤ RT.plattHeight 1 := by
    rw [PC.plattHeight_one]
    norm_num
  have hgrh := HM.grh_of_platt pf (by norm_num) DirichletCharacter.isPrimitive_one_level_one hT
  have hH := (hHs hZC (HM.eta2x x) (mr x hx).2 1 1 DirichletCharacter.isPrimitive_one_level_one
    0 450 (by norm_num) (by norm_num) hgrh).2 (HM.isRealChar_one 1)
  simp only [Nat.cast_one] at hH
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hR : HM.c0 (HM.eta2x x) 0 + (Real.log ((1 : ℕ) : ℝ) + 8) *
      (MajSp.l2 (deriv (HM.eta2x x)) + 2 * Real.pi * |(0 : ℝ)| * MajSp.l2 (HM.eta2x x)) /
        Real.sqrt x ≤ RmalL x := by
    unfold RmalL
    rw [Nat.cast_one, Real.log_one, abs_zero, mul_zero, zero_mul, add_zero, zero_add]
    have h2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left nd (by norm_num : (0 : ℝ) ≤ 8)) hs0.le
    linarith
  have hHb : 0 ≤ HM.hbR 1 450 (0.99811 * Real.log x + 0.32612) (0.32612 * Real.log x + 0.33816)
      (1.24703 * Real.log x + 0.40745) :=
    HM.hbR_nonneg (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity)
  have hTb : 0 ≤ 1e-12 * Real.log x + 2 * HM.fmal x 450 * HM.gZ 1 450 := by
    have := HM.fmal_nonneg hx1 450
    have := HM.gZ_nonneg (q := 1) (T := 450) (by norm_num)
    positivity
  exact HM.err_le_of_zero_sums hEF (mr x hx).1 (HM.eta2x_zero x)
    DirichletCharacter.isPrimitive_one_level_one hx1 hgrh hHb hTb
    (le_trans hH (ENNReal.ofReal_le_ofReal (HM.hbR_mono (by norm_num) (by norm_num) n2 nl n1)))
    (HM.mal_high hZC hG md mt hx) hR

/-- The closing arithmetic of Prop 1.5 at `MalNormsL` (`R ≤ 1.75·10⁶ℓ`, was `18.5ℓ`; any
`R ≤ 1.09·10⁸ℓ` closes). -/
theorem malheur_closeL {ℓ sx X E Tm H R D : ℝ} (hℓ : 27 ≤ ℓ) (hsx : 1000000 ≤ sx)
    (hX : X = sx * sx) (hE : E ≤ Tm + H / sx + R / X) (hTm : Tm ≤ 1.4e-12 * ℓ)
    (hH : H ≤ 391 * ℓ) (hR : R ≤ 1.75e6 * ℓ) (hD : D ≤ 3.9e-6 * ℓ + 1.3e-6) :
    X * E + X * D ≤ (5e-6 + 500 / sx) * X * ℓ := by
  have hsx0 : 0 < sx := by linarith
  have hX0 : 0 < X := by rw [hX]; positivity
  have e1 : X * (H / sx) = sx * H := by
    rw [hX]
    field_simp
  have e2 : X * (R / X) = R := by field_simp
  have e3 : (5e-6 + 500 / sx) * X * ℓ = 5e-6 * X * ℓ + 500 * sx * ℓ := by
    rw [hX]
    field_simp
  have p0 := mul_le_mul_of_nonneg_left hE hX0.le
  have p1 := mul_le_mul_of_nonneg_left hTm hX0.le
  have p2 := mul_le_mul_of_nonneg_left hH hsx0.le
  have p3 : R ≤ 1.75 * sx * ℓ := by nlinarith
  have p4 := mul_le_mul_of_nonneg_left hD hX0.le
  have p5 : X * 1.3e-6 ≤ X * (1.3e-6 / 27 * ℓ) :=
    mul_le_mul_of_nonneg_left (by linarith) hX0.le
  have p6 : 0 ≤ sx * ℓ := by positivity
  rw [e3]
  have e4 : X * (Tm + H / sx + R / X) = X * Tm + X * (H / sx) + X * (R / X) := by ring
  nlinarith

/-- **`MR.MalheurAtR η₊ x` at `MalNormsL`** (copy of `HM.malheurAt_of_links`). -/
theorem malheurAt_of_linksL (hEF : HM.ExplicitFormula) (hZC : HM.ZeroCount)
    (hHs : HM.Hausierer) (hG : HM.GarmolaDecr) (md : HM.MalDecay) (mt : HM.MalTailInt)
    (mm : HM.MalMain) (pf : RT.PlattFull) (x : ℝ) (hx : 10 ^ 12 ≤ x) :
    MR.MalheurAtR HW.etaPlus x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have he0 : ∀ y : ℝ, y = 0 → Principia.Common.Goldbach.e y = 1 := fun y hy => by
    rw [hy]
    simp [Principia.Common.Goldbach.e]
  have htw : MajSp.twSum (HM.eta2x x) (1 : DirichletCharacter ℂ 1) x (0 / x) =
      ((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.log n *
        HW.etaPlus ((n : ℝ) / x) ^ 2 : ℝ) : ℂ) := by
    rw [zero_div, Complex.ofReal_tsum]
    unfold MajSp.twSum
    congr 1
    funext n
    have hxn : x * ((n : ℝ) / x) = n := by field_simp
    rw [MulChar.one_apply (isUnit_of_subsingleton _), he0 _ (mul_zero _)]
    unfold HM.eta2x
    rw [hxn]
    push_cast
    ring
  have hft : MajSp.mainFT (HM.eta2x x) 0 =
      ((∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t) : ℝ) : ℂ) := by
    unfold MajSp.mainFT
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [he0 _ (zero_mul t), mul_one]
    rfl
  have herr : MajSp.err (HM.eta2x x) (1 : DirichletCharacter ℂ 1) 0 x =
      ((((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.log n *
        HW.etaPlus ((n : ℝ) / x) ^ 2) / x -
        ∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t) : ℝ)) : ℂ) := by
    unfold MajSp.err
    rw [htw, hft, if_pos (rfl : (1 : ℕ) = 1), Complex.ofReal_sub, Complex.ofReal_div]
  have hb := mal_errL hEF hZC hHs hG md mt pf hx
  rw [herr, Complex.norm_real, Real.norm_eq_abs] at hb
  have hm := mm x hx
  obtain ⟨hs450, hL7, hL3, hg, hE⟩ := HM.malT_facts
  have hℓ := log_x_ge hx
  have hsx : 1000000 ≤ Real.sqrt x := HM.sqrt_x_ge' hx
  have hTm : 1e-12 * Real.log x + 2 * HM.fmal x 450 * HM.gZ 1 450 ≤ 1.4e-12 * Real.log x := by
    unfold HM.fmal
    have h1 : Real.exp (-0.7 * (450 - 400)) * HM.gZ 1 450 ≤ 6.4e-16 * 21.2 :=
      mul_le_mul hE hg (HM.gZ_nonneg (by norm_num)) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * 10 * (Real.log x + 10))
    have e : 2 * (10 * (Real.log x + 10) * Real.exp (-0.7 * (450 - 400))) * HM.gZ 1 450 =
        2 * 10 * (Real.log x + 10) * (Real.exp (-0.7 * (450 - 400)) * HM.gZ 1 450) := by ring
    rw [e]
    nlinarith
  have hH : HM.hbR 1 450 (0.99811 * Real.log x + 0.32612) (0.32612 * Real.log x + 0.33816)
      (1.24703 * Real.log x + 0.40745) ≤ 391 * Real.log x := by
    unfold HM.hbR
    rw [Real.log_one]
    exact HM.hbR_mal_close hs450 (Real.sqrt_nonneg _) hL7 hL3 hℓ
  have hR : RmalL x ≤ 1.75e6 * Real.log x := by
    unfold RmalL
    have h1 : 8 * (560000 * (Real.log x + 2)) / Real.sqrt x ≤
        8 * (560000 * (Real.log x + 2)) / 1000000 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hsx
    linarith
  have key := malheur_closeL hℓ hsx (Real.mul_self_sqrt hx0.le).symm hb hTm hH hR hm
  unfold MR.MalheurAtR
  have e1 : ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.log n *
      HW.etaPlus ((n : ℝ) / x) ^ 2 - (0.640206 * x * Real.log x - 0.021095 * x) =
        x * ((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.log n *
          HW.etaPlus ((n : ℝ) / x) ^ 2) / x -
          ∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t)) +
        x * ((∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t)) -
          (0.640206 * Real.log x - 0.021095)) := by
    field_simp
    ring
  rw [e1]
  calc |x * ((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.log n *
          HW.etaPlus ((n : ℝ) / x) ^ 2) / x -
          ∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t)) +
        x * ((∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t)) -
          (0.640206 * Real.log x - 0.021095))|
      ≤ |x * ((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.log n *
          HW.etaPlus ((n : ℝ) / x) ^ 2) / x -
          ∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t))| +
        |x * ((∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t)) -
          (0.640206 * Real.log x - 0.021095))| := abs_add_le _ _
    _ = x * |(∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.log n *
          HW.etaPlus ((n : ℝ) / x) ^ 2) / x -
          ∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t)| +
        x * |(∫ t in Ioi (0 : ℝ), HW.etaPlus t ^ 2 * Real.log (x * t)) -
          (0.640206 * Real.log x - 0.021095)| := by
        rw [abs_mul, abs_mul, abs_of_pos hx0]
    _ ≤ (5e-6 + 500 / Real.sqrt x) * x * Real.log x := key

/-- **`MR.MalheurR η₊` from `ExplicitFormula`, `ZeroCount`, `Hausierer`, `GarmolaDecr`,
`MalDecay`, `MalTailInt`, `MalMain` and Platt**: `MalReg` and the norms are PROVED. -/
theorem malheurR_of_linksL (hEF : HM.ExplicitFormula) (hZC : HM.ZeroCount) (hHs : HM.Hausierer)
    (hG : HM.GarmolaDecr) (md : HM.MalDecay) (mt : HM.MalTailInt) (mm : HM.MalMain)
    (pf : RT.PlattFull) : MR.MalheurR HW.etaPlus :=
  fun x hx => malheurAt_of_linksL hEF hZC hHs hG md mt mm pf x hx

end Principia.Common.TernaryGoldbach.HP
