/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajMalMainA

set_option autoImplicit false

/-!
# The cross term `∫(h_H − h)·h·t²e^{−t²}` is at most `5·10⁻⁷`

**`cross_le`**: `|∫₀^∞ (h_H(t) − h(t))·k₀(t) dt| ≤ 5·10⁻⁷`, `k₀(t) = h(t)t²e^{−t²}` — the
cross term of `∫η₊² − ∫η∘² = ∫(h_H − h)²t²e^{−t²} + 2∫(h_H − h)k₀`. Cauchy–Schwarz would charge
it `2|η₊ − η∘|₂|η∘|₂`, which needs Helfgott's `eq:impath` `|η₊ − η∘|₂ ≲ 2.4·10⁻⁶` (built on his
`C₄ = 2013.18`, a run whose interior integral is wrong — not citable). Here it is computed in
Mellin space instead, where `h_H − h` lives on `|r| > 200` and `k₀` is smooth:
* `h_rep` — **Mellin inversion of `h`** on `Re s = 0` (Mathlib's `mellinInv_mellin_eq`; its
  vertical integrability is `MM.integrable_Ah`, i.e. the `r⁻⁴` decay of `MM.Ah_ibp`):
  `h(t) = (1/2π)∫_ℝ A(r)e^{ir log t}dr`;
* `mellin_h_mul` — the full-line twin of `HP.mellin_hH_mul`:
  `M(h·φ)(s) = (1/2π)∫_ℝ A(r)Mφ(s + ir)dr`, so with `HP.mellin_hH_mul` at `s = 1`,
  `∫(h_H − h)k₀ = −(1/2π)∫_{|r|>200} A(r)Mk₀(1 + ir)dr` (`cross_eq`);
* `norm_mk0_le` — one integration by parts: `|Mk₀(1 + ir)| ≤ (3232/315)/|r|`
  (`|k₀'(t)|t ≤ t⁴(2−t)²(8 + 3t − 2t²)`, `∫₀² = 3232/315`);
* the tail: `|A(r)Mk₀(1 + ir)| ≤ 976·(3232/315)/|r|⁵` on `|r| ≥ 200`, and
  `2∫_{200}^∞ r⁻⁵dr = 2/(4·200⁴)`, so `|cross| ≤ (1/2π)·2·976·(3232/315)/(4·200⁴) ≤ 4.99·10⁻⁷`.
The true value is far smaller; nothing finer is needed (`HelfMajMalMain.lean`).
-/

namespace Principia.Common.TernaryGoldbach.MM

open MeasureTheory Set Filter Complex

/-! ## (1) Mellin inversion of `h` -/

/-- `h_H` is measurable (the parametric-integral argument of `RW.measurable_hH`, repeated here to
keep the import light). -/
theorem measurable_hH200 : Measurable (HW.hH 200) := by
  have hj : Measurable fun p : ℝ × ℝ => HW.hFun (p.1 / p.2) * HW.FH 200 p.2 / p.2 :=
    ((HW.measurable_hFun.comp (measurable_fst.div measurable_snd)).mul
      ((HW.measurable_FH 200).comp measurable_snd)).div measurable_snd
  have hm : StronglyMeasurable
      (Function.uncurry fun t y : ℝ => HW.hFun (t / y) * HW.FH 200 y / y) :=
    hj.stronglyMeasurable
  exact (hm.integral_prod_right (ν := volume.restrict (Ioi (0 : ℝ)))).measurable

/-- `h(t)/t ≤ e^{3/2}·g₀(t)` for `t > 0`. -/
theorem hFun_div_le {t : ℝ} (ht : 0 < t) : HW.hFun t / t ≤ Real.exp (3 / 2) * HP.g0 t := by
  rcases le_or_gt t 2 with h2 | h2
  · have hE : Real.exp (t - 1 / 2) ≤ Real.exp (3 / 2) := Real.exp_le_exp.mpr (by linarith)
    rw [BL.hFun_eq_hP ht.le h2]
    unfold BL.hP HP.g0
    rw [max_eq_left (by linarith)]
    have hp : 0 ≤ t * (2 - t) ^ 3 := mul_nonneg ht.le (pow_nonneg (by linarith) 3)
    have e : t ^ 2 * (2 - t) ^ 3 * Real.exp (t - 1 / 2) / t =
        t * (2 - t) ^ 3 * Real.exp (t - 1 / 2) := by
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hE hp
    linarith
  · rw [HW.hFun_of_two_le h2.le, zero_div]
    unfold HP.g0
    rw [max_eq_right (by linarith)]
    norm_num

/-- `h` is Mellin-convergent at `0`. -/
theorem mellinConv_h0 : MellinConvergent (fun t => (HW.hFun t : ℂ)) 0 := by
  unfold MellinConvergent
  have hg : IntegrableOn (fun t => Real.exp (3 / 2) * HP.g0 t) (Ioi 0) :=
    (HP.gi_smul (Real.exp (3 / 2)) HP.gi_g0).1
  refine hg.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun t ht => ?_))
  · exact ((Complex.measurable_ofReal.pow_const _).smul
      (Complex.measurable_ofReal.comp HW.measurable_hFun)).aestronglyMeasurable
  · have ht0 : (0 : ℝ) < t := ht
    rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (BL.hFun_nonneg t)]
    have e : t ^ ((0 : ℂ) - 1).re = t⁻¹ := by
      rw [show ((0 : ℂ) - 1).re = -1 by simp, Real.rpow_neg_one]
    rw [e, inv_mul_eq_div]
    exact hFun_div_le ht0

/-- `M h(iy) = A(−y)`. -/
theorem mellin_h_vert (y : ℝ) :
    mellin (fun t => (HW.hFun t : ℂ)) (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I) = HP.Ah (-y) := by
  rw [Ah_eq_mellin]
  congr 1
  push_cast
  ring

/-- **Mellin inversion of `h`**: `h(t) = (1/2π)∫_ℝ A(r)e^{ir log t}dr` for `t > 0`. -/
theorem h_rep {t : ℝ} (ht : 0 < t) :
    (HW.hFun t : ℂ) = 1 / (2 * Real.pi) *
      ∫ r : ℝ, HP.Ah r * Complex.exp (((r * Real.log t : ℝ) : ℂ) * Complex.I) := by
  have hvert : Complex.VerticalIntegrable (mellin fun t => (HW.hFun t : ℂ)) 0 := by
    unfold Complex.VerticalIntegrable
    refine (integrable_Ah.comp_neg).congr (Eventually.of_forall fun y => ?_)
    exact (mellin_h_vert y).symm
  have hinv := mellinInv_mellin_eq 0 (fun t => (HW.hFun t : ℂ)) ht mellinConv_h0 hvert
    (Complex.continuous_ofReal.comp BL.continuous_hFun).continuousAt
  rw [← hinv]
  unfold mellinInv
  have hpt : ∀ y : ℝ, (t : ℂ) ^ (-(((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) •
      mellin (fun t => (HW.hFun t : ℂ)) (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
        HP.Ah (-y) * Complex.exp ((((-y) * Real.log t : ℝ) : ℂ) * Complex.I) := by
    intro y
    rw [smul_eq_mul, mellin_h_vert, mul_comm,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'), ← Complex.ofReal_log ht.le]
    congr 2
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_neg_eq_self (fun r : ℝ => HP.Ah r *
    Complex.exp (((r * Real.log t : ℝ) : ℂ) * Complex.I)), Complex.real_smul]
  push_cast
  ring

/-! ## (2) The full-line Parseval formula -/

/-- **`M(h·φ)(s) = (1/2π)∫_ℝ A(r)·Mφ(s + ir) dr`** (and the integrand is in `L¹`), for measurable
`φ` with `t^{Re s − 1}φ ∈ L¹(0, ∞)`. The full-line twin of `HP.mellin_hH_mul`. -/
theorem mellin_h_mul {φ : ℝ → ℂ} {s : ℂ} (hφm : Measurable φ)
    (hφ : IntegrableOn (fun t => t ^ (s.re - 1) * ‖φ t‖) (Ioi 0)) :
    Integrable (fun r : ℝ => HP.Ah r * mellin φ (s + (r : ℂ) * Complex.I)) ∧
      mellin (fun t => (HW.hFun t : ℂ) * φ t) s =
        1 / (2 * Real.pi) * ∫ r : ℝ, HP.Ah r * mellin φ (s + (r : ℂ) * Complex.I) := by
  set F : ℝ → ℝ → ℂ := fun r t => HP.Ah r * ((t : ℂ) ^ (s - 1) *
    Complex.exp (((r * Real.log t : ℝ) : ℂ) * Complex.I) * φ t) with hF
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
    refine Measurable.aestronglyMeasurable ?_
    refine (HP.continuous_Ah.measurable.comp measurable_fst).mul (((?_ : Measurable fun z : ℝ × ℝ =>
      (z.2 : ℂ) ^ (s - 1)).mul (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
        (measurable_fst.mul (Real.measurable_log.comp measurable_snd))).mul
          measurable_const))).mul (hφm.comp measurable_snd))
    exact (Complex.measurable_ofReal.comp measurable_snd).pow_const _
  have hφ' : Integrable (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) * φ t‖) (volume.restrict (Ioi 0)) := by
    refine IntegrableOn.congr_fun hφ (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
  have hint : Integrable (Function.uncurry F)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
    have hmaj : Integrable (fun z : ℝ × ℝ => ‖HP.Ah z.1‖ * ‖(z.2 : ℂ) ^ (s - 1) * φ z.2‖)
        ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) :=
      Integrable.mul_prod integrable_Ah.norm hφ'
    refine hmaj.mono' hmeas (Eventually.of_forall fun z => ?_)
    simp only [Function.uncurry, hF]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hin : ∀ r : ℝ, ∫ t in Ioi (0 : ℝ), F r t = HP.Ah r * mellin φ (s + (r : ℂ) * Complex.I) :=
    fun r => by
      simp only [hF]
      rw [integral_const_mul]
      congr 1
      unfold mellin
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [smul_eq_mul, ← HP.cpow_shift ht s r]
  have hI : Integrable (fun r : ℝ => HP.Ah r * mellin φ (s + (r : ℂ) * Complex.I)) := by
    refine hint.integral_prod_left.congr (Eventually.of_forall fun r => ?_)
    exact hin r
  refine ⟨hI, ?_⟩
  have hswap := integral_integral_swap hint
  have hR : mellin (fun t => (HW.hFun t : ℂ) * φ t) s =
      1 / (2 * Real.pi) * ∫ t in Ioi (0 : ℝ), ∫ r : ℝ, F r t := by
    unfold mellin
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [hF]
    rw [h_rep ht, smul_eq_mul]
    have e : ∫ r : ℝ, HP.Ah r * ((t : ℂ) ^ (s - 1) *
        Complex.exp (((r * Real.log t : ℝ) : ℂ) * Complex.I) * φ t) =
          ((t : ℂ) ^ (s - 1) * φ t) * ∫ r : ℝ,
            HP.Ah r * Complex.exp (((r * Real.log t : ℝ) : ℂ) * Complex.I) := by
      rw [← integral_const_mul]
      congr 1
      funext r
      ring
    rw [e]
    ring
  rw [hR, ← hswap]
  congr 1
  exact integral_congr_ae (Eventually.of_forall hin)

/-! ## (3) `k₀ = h·t²e^{−t²}`: one integration by parts -/

/-- `k₀(t) = t⁴(2−t)³e^{t−1/2−t²}` (`= h(t)t²e^{−t²}` on `[0, 2]`). -/
noncomputable def k0P (t : ℝ) : ℝ := t ^ 4 * (2 - t) ^ 3 * Real.exp (t - 1 / 2 - t ^ 2)

/-- `k₀'(t) = t³(2−t)²(2t³ − 5t² − 5t + 8)e^{t−1/2−t²}`. -/
noncomputable def k0D (t : ℝ) : ℝ :=
  t ^ 3 * (2 - t) ^ 2 * (2 * t ^ 3 - 5 * t ^ 2 - 5 * t + 8) * Real.exp (t - 1 / 2 - t ^ 2)

theorem hasDerivAt_k0P (x : ℝ) : HasDerivAt k0P (k0D x) x := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (t - 1 / 2 - t ^ 2))
      (Real.exp (x - 1 / 2 - x ^ 2) * (1 - 2 * x)) x := by
    have h := (((hasDerivAt_id' x).sub_const (1 / 2)).sub (hasDerivAt_pow 2 x)).exp
    refine h.congr_deriv ?_
    norm_num
  have hp : HasDerivAt (fun t : ℝ => t ^ 4 * (2 - t) ^ 3)
      (4 * x ^ 3 * (2 - x) ^ 3 - 3 * x ^ 4 * (2 - x) ^ 2) x := by
    have h := (hasDerivAt_pow 4 x).mul (((hasDerivAt_id' x).const_sub 2).pow 3)
    refine h.congr_deriv ?_
    norm_num
    ring
  have h := hp.mul he
  unfold k0P
  refine h.congr_deriv ?_
  unfold k0D
  ring

theorem continuous_k0D : Continuous k0D := by
  unfold k0D
  fun_prop

/-- `k₀ = h·t²e^{−t²}` as a function on `ℝ`. -/
noncomputable def k0 (t : ℝ) : ℝ := HW.hFun t * t ^ 2 * Real.exp (-t ^ 2)

theorem k0_eq {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2) : k0 t = k0P t := by
  unfold k0 k0P
  rw [BL.hFun_eq_hP h0 h2]
  unfold BL.hP
  rw [show t - 1 / 2 - t ^ 2 = (t - 1 / 2) + -t ^ 2 by ring, Real.exp_add]
  ring

theorem k0_of_two_lt {t : ℝ} (ht : 2 < t) : k0 t = 0 := by
  unfold k0
  rw [HW.hFun_of_two_le ht.le]
  ring

theorem continuous_k0 : Continuous k0 := by
  unfold k0
  exact (BL.continuous_hFun.mul (continuous_pow 2)).mul (by fun_prop)

theorem integrableOn_k0 : IntegrableOn k0 (Ioi 0) :=
  EN.integrableOn_of_cont _ continuous_k0 fun _ ht => k0_of_two_lt ht

/-- `|k₀'(t)|·t ≤ t⁴(2−t)²(8 + 3t − 2t²)` on `(0, 2]`. -/
theorem abs_k0D_le {t : ℝ} (ht0 : 0 < t) (ht2 : t ≤ 2) :
    |k0D t| * t ≤ t ^ 4 * (2 - t) ^ 2 * (8 + 3 * t - 2 * t ^ 2) := by
  have h2t : 0 ≤ 2 - t := by linarith
  have hq0 : 0 ≤ 8 + 3 * t - 2 * t ^ 2 := by nlinarith [mul_nonneg ht0.le h2t]
  have hq : |2 * t ^ 3 - 5 * t ^ 2 - 5 * t + 8| ≤ 8 + 3 * t - 2 * t ^ 2 := by
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg h2t hq0]
    · nlinarith [mul_nonneg ht0.le hq0]
  have hE : Real.exp (t - 1 / 2 - t ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (t - 1 / 2)])
  have hE0 := Real.exp_pos (t - 1 / 2 - t ^ 2)
  unfold k0D
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht0.le 3),
    abs_of_nonneg (pow_nonneg h2t 2), abs_of_pos hE0]
  have hA : 0 ≤ t ^ 3 * (2 - t) ^ 2 := by positivity
  have p1 := mul_le_mul_of_nonneg_left hq hA
  have p2 : t ^ 3 * (2 - t) ^ 2 * |2 * t ^ 3 - 5 * t ^ 2 - 5 * t + 8| *
      Real.exp (t - 1 / 2 - t ^ 2) ≤ t ^ 3 * (2 - t) ^ 2 * (8 + 3 * t - 2 * t ^ 2) := by
    have h0 : 0 ≤ t ^ 3 * (2 - t) ^ 2 * |2 * t ^ 3 - 5 * t ^ 2 - 5 * t + 8| := by positivity
    calc _ ≤ t ^ 3 * (2 - t) ^ 2 * |2 * t ^ 3 - 5 * t ^ 2 - 5 * t + 8| * 1 :=
          mul_le_mul_of_nonneg_left hE h0
      _ ≤ _ := by rw [mul_one]; exact p1
  have p3 := mul_le_mul_of_nonneg_right p2 ht0.le
  calc _ ≤ t ^ 3 * (2 - t) ^ 2 * (8 + 3 * t - 2 * t ^ 2) * t := p3
    _ = _ := by ring

/-- `∫₀² t⁴(2−t)²(8 + 3t − 2t²) dt = 3232/315`. -/
theorem int_k0_maj : ∫ t in (0 : ℝ)..2,
    ∑ k : Fin 9, (![0, 0, 0, 0, 32, -20, -12, 11, -2] : Fin 9 → ℝ) k * t ^ (k : ℕ) =
      3232 / 315 := by
  rw [EN.int_poly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  norm_num

/-- The complex weight `φ₀ = k₀`. -/
noncomputable def phi0 (t : ℝ) : ℂ := (k0 t : ℂ)

theorem measurable_phi0 : Measurable phi0 :=
  Complex.measurable_ofReal.comp continuous_k0.measurable

/-- **`|M k₀(1 + ir)| ≤ (3232/315)/|1 + ir|`** (one integration by parts; `k₀(2) = 0`). -/
theorem norm_mk0_le (r : ℝ) :
    ‖mellin phi0 (1 + (r : ℂ) * Complex.I)‖ ≤ 3232 / 315 * ‖(1 : ℂ) + (r : ℂ) * Complex.I‖⁻¹ := by
  have hw : 0 < ((1 : ℂ) + (r : ℂ) * Complex.I).re := by simp
  have hm : mellin phi0 (1 + (r : ℂ) * Complex.I) =
      ∫ t in (0 : ℝ)..2, (k0P t : ℂ) * (t : ℂ) ^ ((1 + (r : ℂ) * Complex.I) - 1) :=
    mellin_eq_int02 (f := k0) (fun t ht0 ht2 => k0_eq ht0.le ht2) (fun t ht => k0_of_two_lt ht) _
  have hi := ibp02 hasDerivAt_k0P continuous_k0D hw
  have h2 : (k0P 2 : ℂ) = 0 := by simp [k0P]
  rw [hm, hi, h2, zero_mul, zero_div, zero_sub, norm_neg, norm_one_div_mul]
  have hpt : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 2 →
      ‖(k0D t : ℂ) * (t : ℂ) ^ (1 + (r : ℂ) * Complex.I)‖ ≤
        ∑ k : Fin 9, (![0, 0, 0, 0, 32, -20, -12, 11, -2] : Fin 9 → ℝ) k * t ^ (k : ℕ) := by
    intro t ht
    obtain ⟨ht0, ht2⟩ := ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have e : ((1 : ℂ) + (r : ℂ) * Complex.I).re = 1 := by simp
    rw [e, Real.rpow_one]
    have hs : ∑ k : Fin 9, (![0, 0, 0, 0, 32, -20, -12, 11, -2] : Fin 9 → ℝ) k * t ^ (k : ℕ) =
        t ^ 4 * (2 - t) ^ 2 * (8 + 3 * t - 2 * t ^ 2) := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.val_zero, Fin.val_succ]
      ring
    rw [hs]
    exact abs_k0D_le ht0 ht2
  have hint : IntervalIntegrable (fun t : ℝ =>
      ∑ k : Fin 9, (![0, 0, 0, 0, 32, -20, -12, 11, -2] : Fin 9 → ℝ) k * t ^ (k : ℕ))
      volume 0 2 := by
    refine Continuous.intervalIntegrable ?_ 0 2
    fun_prop
  have hb := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 2)
    (Eventually.of_forall hpt) hint
  rw [int_k0_maj] at hb
  exact mul_le_mul_of_nonneg_right hb (inv_nonneg.mpr (norm_nonneg _))

/-- `|1 + ir| ≥ |r|`. -/
theorem abs_le_norm_one_add (r : ℝ) : |r| ≤ ‖(1 : ℂ) + (r : ℂ) * Complex.I‖ := by
  have h := Complex.abs_im_le_norm ((1 : ℂ) + (r : ℂ) * Complex.I)
  simpa using h

/-! ## (4) The cross term -/

/-- The integrand `F(r) = A(r)·Mk₀(1 + ir)`. -/
noncomputable def Fc (r : ℝ) : ℂ := HP.Ah r * mellin phi0 (1 + (r : ℂ) * Complex.I)

theorem phi0_int : IntegrableOn (fun t => t ^ ((1 : ℂ).re - 1) * ‖phi0 t‖) (Ioi 0) := by
  have e : ∀ t : ℝ, t ^ ((1 : ℂ).re - 1) * ‖phi0 t‖ = |k0 t| := fun t => by
    rw [Complex.one_re, sub_self, Real.rpow_zero, one_mul]
    unfold phi0
    rw [Complex.norm_real, Real.norm_eq_abs]
  simp_rw [e]
  exact integrableOn_k0.abs

/-- **`∫(h_H − h)k₀ = −(1/2π)(∫_{−∞}^{−200} + ∫_{200}^∞) A(r)Mk₀(1 + ir) dr`.** -/
theorem cross_eq : ((∫ t in Ioi (0 : ℝ), (HW.hH 200 t - HW.hFun t) * k0 t : ℝ) : ℂ) =
    -(1 / (2 * Real.pi)) * ((∫ r in Iic (-200 : ℝ), Fc r) + ∫ r in Ioi (200 : ℝ), Fc r) := by
  obtain ⟨hFi, hfull⟩ := mellin_h_mul measurable_phi0 phi0_int
  have hband := HP.mellin_hH_mul measurable_phi0 phi0_int
  have m1 : ∀ f : ℝ → ℂ, mellin f 1 = ∫ t in Ioi (0 : ℝ), f t := fun f => by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [sub_self, Complex.cpow_zero, one_smul]
  rw [m1] at hfull hband
  have hI1 : Integrable (fun t => (HW.hH 200 t : ℂ) * phi0 t) (volume.restrict (Ioi 0)) := by
    refine (integrableOn_k0.abs.const_mul 1.65).mono' ((Complex.measurable_ofReal.comp
      measurable_hH200).mul measurable_phi0).aestronglyMeasurable ((ae_restrict_iff'
        measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    unfold phi0
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (HP.abs_hH_le ht) (abs_nonneg _)
  have hI2 : Integrable (fun t => (HW.hFun t : ℂ) * phi0 t) (volume.restrict (Ioi 0)) := by
    refine (integrableOn_k0.abs.const_mul (Real.exp (1 / 2))).mono'
      ((Complex.measurable_ofReal.comp HW.measurable_hFun).mul
        measurable_phi0).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    unfold phi0
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (HP.hFun_le_half t) (abs_nonneg _)
  have hsplit : ∫ r : ℝ, Fc r = (∫ r in Iic (-200 : ℝ), Fc r) +
      ((∫ r in (-200 : ℝ)..200, Fc r) + ∫ r in Ioi (200 : ℝ), Fc r) := by
    have hFc : Integrable Fc := hFi
    rw [← intervalIntegral.integral_Iic_add_Ioi hFc.integrableOn hFc.integrableOn,
      intervalIntegral.integral_of_le (by norm_num),
      ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hFc.integrableOn
        hFc.integrableOn, Ioc_union_Ioi_eq_Ioi (by norm_num)]
  have hdiff : ((∫ t in Ioi (0 : ℝ), (HW.hH 200 t - HW.hFun t) * k0 t : ℝ) : ℂ) =
      (∫ t in Ioi (0 : ℝ), (HW.hH 200 t : ℂ) * phi0 t) -
        ∫ t in Ioi (0 : ℝ), (HW.hFun t : ℂ) * phi0 t := by
    rw [← integral_sub hI1 hI2, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    unfold phi0
    push_cast
    ring
  unfold Fc at hsplit ⊢
  rw [hdiff, hband, hfull, hsplit]
  ring

/-- `∫_{200}^∞ r⁻⁵ dr = 1/(4·200⁴)`. -/
theorem int_Ioi_rpow5 : ∫ r in Ioi (200 : ℝ), r ^ (-5 : ℝ) = 1 / (4 * 200 ^ 4) := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num),
    show (-5 : ℝ) + 1 = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_natCast]
  norm_num

/-- `|F(r)| ≤ 976·(3232/315)·|r|⁻⁵` for `|r| ≥ 200`. -/
theorem norm_Fc_le {r : ℝ} (hr : 200 ≤ |r|) :
    ‖Fc r‖ ≤ 976 * (3232 / 315) * |r| ^ (-5 : ℝ) := by
  have hR : 0 < |r| := by linarith
  have h1 := norm_Ah_le_r4 hr
  have h2 := norm_mk0_le r
  have h3 : ‖(1 : ℂ) + (r : ℂ) * Complex.I‖⁻¹ ≤ |r|⁻¹ := inv_anti₀ hR (abs_le_norm_one_add r)
  have h4 : ‖mellin phi0 (1 + (r : ℂ) * Complex.I)‖ ≤ 3232 / 315 * |r|⁻¹ :=
    h2.trans (mul_le_mul_of_nonneg_left h3 (by norm_num))
  unfold Fc
  rw [norm_mul, show (-5 : ℝ) = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg hR.le,
    Real.rpow_natCast]
  calc ‖HP.Ah r‖ * ‖mellin phi0 (1 + (r : ℂ) * Complex.I)‖
      ≤ 976 / |r| ^ 4 * (3232 / 315 * |r|⁻¹) :=
        mul_le_mul h1 h4 (norm_nonneg _) (by positivity)
    _ = 976 * (3232 / 315) * (|r| ^ 5)⁻¹ := by
        field_simp

/-- `‖∫_{200}^∞ g‖ ≤ 976·(3232/315)/(4·200⁴)` when `|g(r)| ≤ 976·(3232/315)r⁻⁵` there. -/
theorem tail_le {g : ℝ → ℂ} (hg : ∀ r : ℝ, 200 < r → ‖g r‖ ≤ 976 * (3232 / 315) * r ^ (-5 : ℝ)) :
    ‖∫ r in Ioi (200 : ℝ), g r‖ ≤ 976 * (3232 / 315) * (1 / (4 * 200 ^ 4)) := by
  have hint : IntegrableOn (fun r : ℝ => 976 * (3232 / 315) * r ^ (-5 : ℝ)) (Ioi 200) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul _
  have h := norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun r hr => hg r hr))
  rw [integral_const_mul, int_Ioi_rpow5] at h
  exact h

/-- **`|∫₀^∞ (h_H − h)k₀| ≤ 5·10⁻⁷`.** -/
theorem cross_le : |∫ t in Ioi (0 : ℝ), (HW.hH 200 t - HW.hFun t) * k0 t| ≤ 5e-7 := by
  have hR : ‖∫ r in Ioi (200 : ℝ), Fc r‖ ≤ 976 * (3232 / 315) * (1 / (4 * 200 ^ 4)) :=
    tail_le fun r hr => by
      have h := norm_Fc_le (r := r) (by rw [abs_of_pos (by linarith)]; linarith)
      rwa [abs_of_pos (by linarith)] at h
  have hL : ‖∫ r in Iic (-200 : ℝ), Fc r‖ ≤ 976 * (3232 / 315) * (1 / (4 * 200 ^ 4)) := by
    rw [← integral_comp_neg_Ioi]
    refine tail_le fun r hr => ?_
    have h := norm_Fc_le (r := -r) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
    rwa [abs_neg, abs_of_pos (by linarith)] at h
  have he := cross_eq
  have hn : ‖((∫ t in Ioi (0 : ℝ), (HW.hH 200 t - HW.hFun t) * k0 t : ℝ) : ℂ)‖ =
      |∫ t in Ioi (0 : ℝ), (HW.hH 200 t - HW.hFun t) * k0 t| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [← hn, he, norm_mul, norm_neg]
  have hpi : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hpi]
  have hs := norm_add_le (∫ r in Iic (-200 : ℝ), Fc r) (∫ r in Ioi (200 : ℝ), Fc r)
  have hpi2 : 1 / (2 * Real.pi) ≤ 1 / (2 * 3.14) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [Real.pi_gt_d2])
  have hp0 : 0 ≤ 1 / (2 * Real.pi) := by positivity
  calc 1 / (2 * Real.pi) * ‖(∫ r in Iic (-200 : ℝ), Fc r) + ∫ r in Ioi (200 : ℝ), Fc r‖
      ≤ 1 / (2 * Real.pi) * (2 * (976 * (3232 / 315) * (1 / (4 * 200 ^ 4)))) :=
        mul_le_mul_of_nonneg_left (by linarith) hp0
    _ ≤ 1 / (2 * 3.14) * (2 * (976 * (3232 / 315) * (1 / (4 * 200 ^ 4)))) :=
        mul_le_mul_of_nonneg_right hpi2 (by norm_num)
    _ ≤ 5e-7 := by norm_num

end Principia.Common.TernaryGoldbach.MM
