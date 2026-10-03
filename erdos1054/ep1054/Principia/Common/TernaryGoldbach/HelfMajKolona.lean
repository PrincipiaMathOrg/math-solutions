/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajMalTail
import Principia.Common.TernaryGoldbach.EasyStar

set_option autoImplicit false

/-!
# The `η₂`-transfer of Cor 1.3 — `HM.Kolona` PROVED

`kolona_holds : HM.Kolona` (`eq:chemdames`, `eq:braca`, majarcs 4074–4085, 4128–4168): for every
character `χ` mod any `q`, every `δ` and every `x > 0`,
`|err_{η₂∗_Mφ,χ}(δ,x)| ≤ ∫_{1/4}^{1} |err_{φ,χ}(δw, wx)| η₂(w) dw`.

## The proof: an exact identity, then the triangle inequality

`err_mconv_eq`: `err_{η₂∗_Mφ,χ}(δ,x) = ∫_{1/4}^{1} η₂(w)·err_{φ,χ}(δw, wx) dw`, EXACTLY, for every
`χ` (the trivial-character main term included). Three steps:

1. **The `w`-form of the Mellin convolution** (`mconv_w`): `(η₂ ∗_M φ)(s) = ∫_{1/4}^{1}
   η₂(w)φ(s/w) dw/w` for `s > 0`, from the library's `y`-form (`HW.mconv_eta2`) by the substitution
   `y = s/w` (`intervalIntegral.integral_comp_mul_deriv'`).
2. **The prime sum** (`twSum_mconv_eq`): `S_{η₂∗_Mφ}(δ/x, x)/x = ∫ η₂(w)·S_φ(δ/x, wx)/(wx) dw` —
   the sum over `n` and the integral over `w` are swapped by `integral_tsum`, with the summable
   majorant `Λ(n)φ(n/wx) ≤ (16/x²)n³e^{−n/(2x²)}` on `w ∈ [1/4, 1]` (`kterm_norm_le`). The same
   majorant makes `w ↦ S_φ(δ/x, wx)` continuous on `[1/4, 1]` (`continuousOn_tsum`), hence
   integrable. The frequency is the same on both sides: `(δw)/(wx) = δ/x`.
3. **The main term** (`mainFT_mconv_eq`): `∫₀^∞ (η₂∗_Mφ)(t)e(δt)dt = ∫ η₂(w)·∫₀^∞ φ(u)e(δwu)du dw`
   by Fubini on `(0,∞) × [1/4,1]` (`integral_integral_swap`, dominated by `192φ(t)`) and `t = wu`.

Then `‖∫ η₂·err_φ‖ ≤ ∫ η₂‖err_φ‖` (`enorm_integral_le_lintegral_enorm`).
-/

namespace Principia.Common.TernaryGoldbach.HM

open MeasureTheory Set Principia.Common.Goldbach ArithmeticFunction
open scoped ArithmeticFunction

/-! ## (1) Elementary facts -/

/-- `e` is continuous. -/
theorem continuous_e' : Continuous e := by
  unfold e
  fun_prop

/-- `η₂ ≤ 3` (`4 log 2 = 2.7726`). -/
theorem eta2_le_three (w : ℝ) : HW.eta2 w ≤ 3 := by
  unfold HW.eta2
  split_ifs
  · have h1 : max (Real.log 2 - |Real.log (2 * w)|) 0 ≤ Real.log 2 :=
      max_le (by linarith [abs_nonneg (Real.log (2 * w))]) (Real.log_nonneg (by norm_num))
    have h2 := Real.log_two_lt_d9
    linarith
  · norm_num

/-- `n ≤ n²` for a natural number. -/
theorem nat_le_sq (n : ℕ) : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith

/-- `φ(t/w) ≤ 16φ(t)` for `w ∈ [1/4, 1]`. -/
theorem phi_div_le {t w : ℝ} (hw : w ∈ Icc (1 / 4 : ℝ) 1) : HW.phi (t / w) ≤ 16 * HW.phi t := by
  have hw0 : 0 < w := by linarith [hw.1]
  have h1 : t ^ 2 ≤ (t / w) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    have : w ^ 2 ≤ 1 := by nlinarith [hw.2]
    nlinarith [sq_nonneg t]
  have h2 : (t / w) ^ 2 ≤ 16 * t ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    have : 1 / 16 ≤ w ^ 2 := by nlinarith [hw.1]
    nlinarith [sq_nonneg t]
  unfold HW.phi
  have h3 : Real.exp (-(t / w) ^ 2 / 2) ≤ Real.exp (-t ^ 2 / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  calc (t / w) ^ 2 * Real.exp (-(t / w) ^ 2 / 2) ≤ (16 * t ^ 2) * Real.exp (-t ^ 2 / 2) :=
        mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity)
    _ = 16 * (t ^ 2 * Real.exp (-t ^ 2 / 2)) := by ring

/-! ## (2) The `w`-form of `η₂ ∗_M φ` -/

/-- **`(η₂ ∗_M φ)(s) = ∫_{1/4}^{1} η₂(w)φ(s/w)/w dw`** for `s > 0` (substitute `y = s/w` in the
library's `∫_s^{4s} η₂(s/y)φ(y)/y dy`). -/
theorem mconv_w {s : ℝ} (hs : 0 < s) :
    HW.mconv HW.eta2 HW.phi s = ∫ w in Icc (1 / 4 : ℝ) 1, HW.eta2 w * HW.phi (s / w) / w := by
  rw [HW.mconv_eta2 HW.phi hs]
  have hpos : ∀ w ∈ uIcc (1 / 4 : ℝ) 1, 0 < w := fun w hw => by
    rw [uIcc_of_le (by norm_num)] at hw
    linarith [hw.1]
  have hd : ∀ w ∈ uIcc (1 / 4 : ℝ) 1, HasDerivAt (fun w => s / w) (-s / w ^ 2) w := by
    intro w hw
    have hw0 := (hpos w hw).ne'
    refine ((hasDerivAt_const w s).div (hasDerivAt_id w) hw0).congr_deriv ?_
    simp only [id]
    ring
  have hc' : ContinuousOn (fun w : ℝ => -s / w ^ 2) (uIcc (1 / 4 : ℝ) 1) :=
    continuousOn_const.div (continuousOn_pow 2) fun w hw => pow_ne_zero 2 (hpos w hw).ne'
  have hg : ContinuousOn (fun y => HW.eta2 (s / y) * HW.phi y / y)
      ((fun w => s / w) '' uIcc (1 / 4 : ℝ) 1) := by
    have h1 : ContinuousOn (fun y => HW.eta2 (s / y) * HW.phi y / y) (Ioi 0) :=
      ((HW.eta2_div_contOn hs).mul HW.continuous_phi.continuousOn).div continuousOn_id
        fun y hy => (mem_Ioi.mp hy).ne'
    refine h1.mono ?_
    rintro _ ⟨w, hw, rfl⟩
    exact div_pos hs (hpos w hw)
  have hsub : ∫ w in (1 / 4 : ℝ)..1, HW.eta2 (s / (s / w)) * HW.phi (s / w) / (s / w) *
      (-s / w ^ 2) = ∫ y in s / (1 / 4)..s / 1, HW.eta2 (s / y) * HW.phi y / y :=
    intervalIntegral.integral_comp_mul_deriv' hd hc' hg
  have hcongr : ∫ w in (1 / 4 : ℝ)..1, HW.eta2 (s / (s / w)) * HW.phi (s / w) / (s / w) *
      (-s / w ^ 2) = ∫ w in (1 / 4 : ℝ)..1, -(HW.eta2 w * HW.phi (s / w) / w) := by
    refine intervalIntegral.integral_congr fun w hw => ?_
    have hw0 := (hpos w hw).ne'
    have hsw : s / (s / w) = w := by field_simp
    rw [hsw]
    field_simp
  rw [hcongr, intervalIntegral.integral_neg, show s / (1 / 4) = 4 * s by ring, div_one,
    intervalIntegral.integral_symm s (4 * s)] at hsub
  have key : ∫ y in s..4 * s, HW.eta2 (s / y) * HW.phi y / y =
      ∫ w in (1 / 4 : ℝ)..1, HW.eta2 w * HW.phi (s / w) / w := by linarith
  rw [key, intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]

/-! ## (3) The prime sum -/

/-- The `n`-th term of `S_φ(δ/x, X)`: `Λ(n)χ(n)φ(n/X)e(nδ/x)`. -/
noncomputable def kterm {q : ℕ} (χ : DirichletCharacter ℂ q) (δ x X : ℝ) (n : ℕ) : ℂ :=
  ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((HW.phi ((n : ℝ) / X) : ℝ) : ℂ) * e ((n : ℝ) * (δ / x))

/-- The summable majorant `(16/x²)n³e^{−n/(2x²)}`. -/
noncomputable def kb (x : ℝ) (n : ℕ) : ℝ :=
  16 / x ^ 2 * ((n : ℝ) ^ 3 * Real.exp (-(1 / (2 * x ^ 2)) * n))

theorem kb_nonneg (x : ℝ) (n : ℕ) : 0 ≤ kb x n := by
  unfold kb
  positivity

theorem summable_kb {x : ℝ} (hx : 0 < x) : Summable (kb x) :=
  (Real.summable_pow_mul_exp_neg_nat_mul 3 (by positivity : (0 : ℝ) < 1 / (2 * x ^ 2))).mul_left
    (16 / x ^ 2)

/-- **The majorant**: `|Λ(n)χ(n)φ(n/wx)e(·)| ≤ (16/x²)n³e^{−n/(2x²)}` for `w ∈ [1/4, 1]`. -/
theorem kterm_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (δ : ℝ) {x w : ℝ} (hx : 0 < x)
    (hw : w ∈ Icc (1 / 4 : ℝ) 1) (n : ℕ) : ‖kterm χ δ x (w * x) n‖ ≤ kb x n := by
  have hw0 : 0 < w := by linarith [hw.1]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hΛ : Λ n ≤ n := vonMangoldt_le_log.trans (Real.log_le_self hn0)
  have hΛ0 : 0 ≤ Λ n := vonMangoldt_nonneg
  have hχ := χ.norm_le_one (n : ZMod q)
  have hy1 : (n : ℝ) / (w * x) ≤ 4 * ((n : ℝ) / x) := by
    rw [div_le_iff₀ (by positivity)]
    have : (n : ℝ) / x * x = n := by field_simp
    nlinarith [hw.1, div_nonneg hn0 hx.le]
  have hy2 : (n : ℝ) / x ≤ (n : ℝ) / (w * x) :=
    div_le_div_of_nonneg_left hn0 (by positivity) (by nlinarith [hw.2])
  have hy0 : 0 ≤ (n : ℝ) / x := div_nonneg hn0 hx.le
  have hsq : ((n : ℝ) / (w * x)) ^ 2 ≤ 16 * (n : ℝ) ^ 2 / x ^ 2 := by
    have := pow_le_pow_left₀ (le_trans hy0 hy2) hy1 2
    have e : (4 * ((n : ℝ) / x)) ^ 2 = 16 * (n : ℝ) ^ 2 / x ^ 2 := by ring
    linarith
  have hexp : Real.exp (-((n : ℝ) / (w * x)) ^ 2 / 2) ≤ Real.exp (-(1 / (2 * x ^ 2)) * n) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 := pow_le_pow_left₀ hy0 hy2 2
    have h2 : (n : ℝ) / x ^ 2 ≤ ((n : ℝ) / x) ^ 2 := by
      rw [div_pow]
      exact div_le_div_of_nonneg_right (nat_le_sq n) (by positivity)
    have e : -(1 / (2 * x ^ 2)) * (n : ℝ) = -((n : ℝ) / x ^ 2) / 2 := by
      field_simp
    rw [e]
    linarith
  have hphi : HW.phi ((n : ℝ) / (w * x)) ≤ 16 * (n : ℝ) ^ 2 / x ^ 2 *
      Real.exp (-(1 / (2 * x ^ 2)) * n) := by
    unfold HW.phi
    exact mul_le_mul hsq hexp (Real.exp_pos _).le (by positivity)
  unfold kterm kb
  rw [norm_mul, norm_mul, norm_mul, e_norm, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hΛ0, Real.norm_of_nonneg (HW.phi_nonneg _)]
  have p1 : Λ n * ‖χ (n : ZMod q)‖ ≤ n := by nlinarith [norm_nonneg (χ (n : ZMod q))]
  calc Λ n * ‖χ (n : ZMod q)‖ * HW.phi ((n : ℝ) / (w * x))
      ≤ n * (16 * (n : ℝ) ^ 2 / x ^ 2 * Real.exp (-(1 / (2 * x ^ 2)) * n)) :=
        mul_le_mul p1 hphi (HW.phi_nonneg _) hn0
    _ = 16 / x ^ 2 * ((n : ℝ) ^ 3 * Real.exp (-(1 / (2 * x ^ 2)) * n)) := by ring

/-- Each term is continuous in `w` on `[1/4, 1]`. -/
theorem kterm_contOn {q : ℕ} (χ : DirichletCharacter ℂ q) (δ : ℝ) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ContinuousOn (fun w => kterm χ δ x (w * x) n) (Icc (1 / 4 : ℝ) 1) := by
  unfold kterm
  refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_) continuousOn_const
  refine Complex.continuous_ofReal.comp_continuousOn (HW.continuous_phi.comp_continuousOn ?_)
  exact continuousOn_const.div (continuousOn_id.mul continuousOn_const)
    fun w hw => (mul_pos (by linarith [hw.1]) hx).ne'

/-- **`w ↦ S_φ(δ/x, wx)` is continuous on `[1/4, 1]`** (uniform convergence, `kb` majorant). -/
theorem twSum_phi_contOn {q : ℕ} (χ : DirichletCharacter ℂ q) (δ : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousOn (fun w => MajSp.twSum HW.phi χ (w * x) (δ / x)) (Icc (1 / 4 : ℝ) 1) :=
  continuousOn_tsum (fun n => kterm_contOn χ δ hx n) (summable_kb hx)
    fun n _ hw => kterm_norm_le χ δ hx hw n

/-- The `w`-integrand of the swapped prime sum: `η₂(w)·Λ(n)χ(n)φ(n/wx)e(nδ/x)/(wx)`. -/
noncomputable def kF {q : ℕ} (χ : DirichletCharacter ℂ q) (δ x : ℝ) (n : ℕ) (w : ℝ) : ℂ :=
  (HW.eta2 w : ℂ) * (kterm χ δ x (w * x) n / ((w * x : ℝ) : ℂ))

theorem kF_contOn {q : ℕ} (χ : DirichletCharacter ℂ q) (δ : ℝ) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ContinuousOn (kF χ δ x n) (Icc (1 / 4 : ℝ) 1) := by
  unfold kF
  refine (Complex.continuous_ofReal.comp_continuousOn eta2_contOn).mul
    ((kterm_contOn χ δ hx n).div
      (Complex.continuous_ofReal.comp_continuousOn (continuousOn_id.mul continuousOn_const))
      fun w hw => ?_)
  exact Complex.ofReal_ne_zero.mpr (mul_pos (by linarith [hw.1]) hx).ne'

/-- `|kF| ≤ (12/x)·kb` on `[1/4, 1]`. -/
theorem kF_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (δ : ℝ) {x w : ℝ} (hx : 0 < x)
    (hw : w ∈ Icc (1 / 4 : ℝ) 1) (n : ℕ) : ‖kF χ δ x n w‖ ≤ 12 / x * kb x n := by
  have hw0 : 0 < w := by linarith [hw.1]
  have hk := kterm_norm_le χ δ hx hw n
  have hb0 := kb_nonneg x n
  unfold kF
  rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (HW.eta2_nonneg w), Real.norm_of_nonneg (by positivity)]
  have h1 : ‖kterm χ δ x (w * x) n‖ / (w * x) ≤ kb x n / (x / 4) :=
    div_le_div₀ hb0 hk (by positivity) (by nlinarith [hw.1])
  have h2 := mul_le_mul (eta2_le_three w) h1 (by positivity) (by norm_num)
  have e : 3 * (kb x n / (x / 4)) = 12 / x * kb x n := by
    field_simp
    ring
  linarith

/-- **The prime sum, swapped**: `S_{η₂∗_Mφ}(δ/x, x)/x = ∫_{1/4}^{1} η₂(w)S_φ(δ/x, wx)/(wx) dw`. -/
theorem twSum_mconv_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (δ : ℝ) {x : ℝ} (hx : 0 < x) :
    MajSp.twSum (HW.mconv HW.eta2 HW.phi) χ x (δ / x) / (x : ℂ) =
      ∫ w in Icc (1 / 4 : ℝ) 1,
        (HW.eta2 w : ℂ) * (MajSp.twSum HW.phi χ (w * x) (δ / x) / ((w * x : ℝ) : ℂ)) := by
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  -- the swap
  have hF : ∀ n, AEStronglyMeasurable (kF χ δ x n) (volume.restrict (Icc (1 / 4 : ℝ) 1)) :=
    fun n => (kF_contOn χ δ hx n).aestronglyMeasurable measurableSet_Icc
  have hle : ∀ n : ℕ, ∫⁻ w in Icc (1 / 4 : ℝ) 1, ‖kF χ δ x n w‖ₑ ≤
      ENNReal.ofReal (9 / x * kb x n) := by
    intro n
    calc ∫⁻ w in Icc (1 / 4 : ℝ) 1, ‖kF χ δ x n w‖ₑ
        ≤ ∫⁻ _ in Icc (1 / 4 : ℝ) 1, ENNReal.ofReal (12 / x * kb x n) := by
          refine setLIntegral_mono' measurableSet_Icc fun w hw => ?_
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (kF_norm_le χ δ hx hw n)
      _ = ENNReal.ofReal (12 / x * kb x n) * ENNReal.ofReal (3 / 4) := by
          rw [setLIntegral_const, Real.volume_Icc]
          norm_num
      _ = ENNReal.ofReal (9 / x * kb x n) := by
          rw [← ENNReal.ofReal_mul (by have := kb_nonneg x n; positivity)]
          congr 1
          ring
  have hsum : ∑' n, ∫⁻ w in Icc (1 / 4 : ℝ) 1, ‖kF χ δ x n w‖ₑ ≠ ⊤ := by
    have hs := (summable_kb hx).mul_left (9 / x)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by have := kb_nonneg x n; positivity) hs]
    exact ENNReal.ofReal_ne_top
  have hswap := integral_tsum hF hsum
  -- each term
  have hterm : ∀ n : ℕ, ∫ w in Icc (1 / 4 : ℝ) 1, kF χ δ x n w =
      ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) *
        ((HW.mconv HW.eta2 HW.phi ((n : ℝ) / x) : ℝ) : ℂ) * e ((n : ℝ) * (δ / x)) / (x : ℂ) := by
    intro n
    have hF' : ∀ w ∈ Icc (1 / 4 : ℝ) 1, kF χ δ x n w =
        (((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * e ((n : ℝ) * (δ / x))) *
          ((HW.eta2 w * HW.phi ((n : ℝ) / (w * x)) / (w * x) : ℝ) : ℂ) := by
      intro _ _
      unfold kF kterm
      push_cast
      ring
    rw [setIntegral_congr_fun measurableSet_Icc hF', integral_const_mul, integral_complex_ofReal]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp
    · have hs : 0 < (n : ℝ) / x := div_pos (Nat.cast_pos.mpr hpos) hx
      have hint : ∫ w in Icc (1 / 4 : ℝ) 1, HW.eta2 w * HW.phi ((n : ℝ) / (w * x)) / (w * x) =
          1 / x * HW.mconv HW.eta2 HW.phi ((n : ℝ) / x) := by
        rw [mconv_w hs, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Icc fun w hw => ?_
        have hw0 : 0 < w := by linarith [hw.1]
        have e1 : (n : ℝ) / x / w = (n : ℝ) / (w * x) := by
          rw [div_div, mul_comm]
        rw [e1]
        field_simp
      rw [hint]
      push_cast
      field_simp
  calc MajSp.twSum (HW.mconv HW.eta2 HW.phi) χ x (δ / x) / (x : ℂ)
      = ∑' n : ℕ, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) *
          ((HW.mconv HW.eta2 HW.phi ((n : ℝ) / x) : ℝ) : ℂ) * e ((n : ℝ) * (δ / x)) /
            (x : ℂ) := by
        unfold MajSp.twSum
        rw [tsum_div_const]
    _ = ∑' n : ℕ, ∫ w in Icc (1 / 4 : ℝ) 1, kF χ δ x n w := tsum_congr fun n => (hterm n).symm
    _ = ∫ w in Icc (1 / 4 : ℝ) 1, ∑' n : ℕ, kF χ δ x n w := hswap.symm
    _ = ∫ w in Icc (1 / 4 : ℝ) 1,
          (HW.eta2 w : ℂ) * (MajSp.twSum HW.phi χ (w * x) (δ / x) / ((w * x : ℝ) : ℂ)) := by
        congr 1
        funext w
        unfold kF MajSp.twSum
        rw [tsum_mul_left, tsum_div_const]
        rfl

/-! ## (4) The main term -/

/-- **`δ ↦ ∫₀^∞ φ(u)e(δu)du` is continuous** (dominated by `φ`). -/
theorem continuous_mainFT_phi : Continuous fun d : ℝ => MajSp.mainFT HW.phi d := by
  unfold MajSp.mainFT
  refine continuous_of_dominated (bound := HW.phi) (fun d => ?_) (fun d => ?_) EN.integrable_phi ?_
  · exact ((Complex.continuous_ofReal.comp HW.continuous_phi).mul
      (continuous_e'.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => le_of_eq ?_
    rw [norm_mul, e_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (HW.phi_nonneg t)]
  · exact Filter.Eventually.of_forall fun t =>
      continuous_const.mul (continuous_e'.comp (continuous_id.mul continuous_const))

/-- **The main term, transferred**:
`∫₀^∞ (η₂∗_Mφ)(t)e(δt)dt = ∫_{1/4}^{1} η₂(w)·∫₀^∞ φ(u)e(δwu)du dw`
(Fubini on `(0,∞) × [1/4, 1]`, then `t = wu`). -/
theorem mainFT_mconv_eq (δ : ℝ) :
    MajSp.mainFT (HW.mconv HW.eta2 HW.phi) δ =
      ∫ w in Icc (1 / 4 : ℝ) 1, (HW.eta2 w : ℂ) * MajSp.mainFT HW.phi (δ * w) := by
  set G : ℝ → ℝ → ℂ := fun t w => ((HW.eta2 w * HW.phi (t / w) / w : ℝ) : ℂ) * e (δ * t) with hG
  -- integrability on the product
  have hmeas : Measurable (Function.uncurry G) := by
    rw [hG]
    exact (Complex.measurable_ofReal.comp (((measurable_eta2.comp measurable_snd).mul
      (HW.continuous_phi.measurable.comp (measurable_fst.div measurable_snd))).div
        measurable_snd)).mul (continuous_e'.measurable.comp (measurable_const.mul measurable_fst))
  have hbound : ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Icc (1 / 4 : ℝ) 1))),
      ‖Function.uncurry G p‖ ≤ 192 * HW.phi p.1 := by
    rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Icc) fun p hp => ?_
    have hw := hp.2
    have hw0 : 0 < p.2 := by linarith [hw.1]
    simp only [Function.uncurry, hG]
    rw [norm_mul, e_norm, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (div_nonneg (mul_nonneg (HW.eta2_nonneg _) (HW.phi_nonneg _)) hw0.le)]
    have h1 := phi_div_le (t := p.1) hw
    have h2 := eta2_le_three p.2
    have h3 : 1 / p.2 ≤ 4 := by
      rw [div_le_iff₀ hw0]
      linarith [hw.1]
    have h4 : HW.eta2 p.2 * HW.phi (p.1 / p.2) ≤ 3 * (16 * HW.phi p.1) :=
      mul_le_mul h2 h1 (HW.phi_nonneg _) (by norm_num)
    have h5 := mul_le_mul h4 h3 (by positivity)
      (by have := HW.phi_nonneg p.1; positivity)
    have e : HW.eta2 p.2 * HW.phi (p.1 / p.2) / p.2 =
        HW.eta2 p.2 * HW.phi (p.1 / p.2) * (1 / p.2) := by ring
    rw [e]
    linarith
  have hint : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Icc (1 / 4 : ℝ) 1))) :=
    Integrable.mono' ((EN.integrable_phi.const_mul 192).comp_fst _) hmeas.aestronglyMeasurable
      hbound
  -- the `t`-integral as a `w`-integral, then swap
  have hL : MajSp.mainFT (HW.mconv HW.eta2 HW.phi) δ =
      ∫ t in Ioi (0 : ℝ), ∫ w in Icc (1 / 4 : ℝ) 1, G t w := by
    unfold MajSp.mainFT
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [hG]
    rw [mconv_w ht, ← integral_complex_ofReal, ← integral_mul_const]
  have hin : ∀ w ∈ Icc (1 / 4 : ℝ) 1,
      ∫ t in Ioi (0 : ℝ), G t w = (HW.eta2 w : ℂ) * MajSp.mainFT HW.phi (δ * w) := by
    intro w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have hwc : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw0.ne'
    have e1 : ∀ t, G t w = ((HW.eta2 w / w : ℝ) : ℂ) *
        (((HW.phi (t / w)) : ℂ) * e (δ * t)) := fun t => by
      simp only [hG]
      push_cast
      ring
    simp_rw [e1]
    rw [integral_const_mul]
    have hsub := integral_comp_mul_left_Ioi
      (fun u => ((HW.phi u : ℝ) : ℂ) * e (δ * w * u)) 0 (inv_pos.mpr hw0)
    have e2 : ∀ t : ℝ, ((HW.phi (w⁻¹ * t) : ℝ) : ℂ) * e (δ * w * (w⁻¹ * t)) =
        ((HW.phi (t / w) : ℝ) : ℂ) * e (δ * t) := fun t => by
      rw [inv_mul_eq_div, show δ * w * (t / w) = δ * t by field_simp]
    simp only [e2, mul_zero, inv_inv] at hsub
    rw [hsub, Complex.real_smul]
    unfold MajSp.mainFT
    push_cast
    field_simp
  rw [hL, integral_integral_swap hint]
  exact setIntegral_congr_fun measurableSet_Icc hin

/-! ## (5) The identity and `Kolona` -/

/-- **`err_{η₂∗_Mφ,χ}(δ,x) = ∫_{1/4}^{1} η₂(w)·err_{φ,χ}(δw, wx) dw`** — exactly, every `χ`. -/
theorem err_mconv_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (δ : ℝ) {x : ℝ} (hx : 0 < x) :
    MajSp.err (HW.mconv HW.eta2 HW.phi) χ δ x =
      ∫ w in Icc (1 / 4 : ℝ) 1, (HW.eta2 w : ℂ) * MajSp.err HW.phi χ (δ * w) (w * x) := by
  have hA := twSum_mconv_eq χ δ hx
  have hB := mainFT_mconv_eq δ
  have hIA : IntegrableOn (fun w => (HW.eta2 w : ℂ) *
      (MajSp.twSum HW.phi χ (w * x) (δ / x) / ((w * x : ℝ) : ℂ))) (Icc (1 / 4 : ℝ) 1) := by
    refine ContinuousOn.integrableOn_Icc ?_
    refine (Complex.continuous_ofReal.comp_continuousOn eta2_contOn).mul
      ((twSum_phi_contOn χ δ hx).div
        (Complex.continuous_ofReal.comp_continuousOn (continuousOn_id.mul continuousOn_const))
        fun w hw => ?_)
    exact Complex.ofReal_ne_zero.mpr (mul_pos (by linarith [hw.1]) hx).ne'
  have hIB : IntegrableOn (fun w => (HW.eta2 w : ℂ) * MajSp.mainFT HW.phi (δ * w))
      (Icc (1 / 4 : ℝ) 1) := by
    refine ContinuousOn.integrableOn_Icc ?_
    exact (Complex.continuous_ofReal.comp_continuousOn eta2_contOn).mul
      (continuous_mainFT_phi.comp (continuous_const.mul continuous_id)).continuousOn
  have hβ : ∀ w ∈ Icc (1 / 4 : ℝ) 1, (δ * w) / (w * x) = δ / x := fun w hw => by
    have hw0 : 0 < w := by linarith [hw.1]
    field_simp
  by_cases hq : q = 1
  · have hc : ∫ w in Icc (1 / 4 : ℝ) 1, (HW.eta2 w : ℂ) * MajSp.err HW.phi χ (δ * w) (w * x) =
        ∫ w in Icc (1 / 4 : ℝ) 1, ((HW.eta2 w : ℂ) *
          (MajSp.twSum HW.phi χ (w * x) (δ / x) / ((w * x : ℝ) : ℂ)) -
            (HW.eta2 w : ℂ) * MajSp.mainFT HW.phi (δ * w)) := by
      refine setIntegral_congr_fun measurableSet_Icc fun w hw => ?_
      unfold MajSp.err
      rw [hβ w hw, if_pos hq]
      ring
    rw [hc, integral_sub hIA hIB, ← hA, ← hB]
    unfold MajSp.err
    rw [if_pos hq]
  · have hc : ∫ w in Icc (1 / 4 : ℝ) 1, (HW.eta2 w : ℂ) * MajSp.err HW.phi χ (δ * w) (w * x) =
        ∫ w in Icc (1 / 4 : ℝ) 1, (HW.eta2 w : ℂ) *
          (MajSp.twSum HW.phi χ (w * x) (δ / x) / ((w * x : ℝ) : ℂ)) := by
      refine setIntegral_congr_fun measurableSet_Icc fun w hw => ?_
      unfold MajSp.err
      rw [hβ w hw, if_neg hq, sub_zero]
    rw [hc, ← hA]
    unfold MajSp.err
    rw [if_neg hq, sub_zero]

/-- **`Kolona` PROVED.** -/
theorem kolona_holds : Kolona := by
  intro q χ δ x hx
  rw [err_mconv_eq χ δ hx]
  calc ENNReal.ofReal ‖∫ w in Icc (1 / 4 : ℝ) 1,
        (HW.eta2 w : ℂ) * MajSp.err HW.phi χ (δ * w) (w * x)‖
      = ‖∫ w in Icc (1 / 4 : ℝ) 1, (HW.eta2 w : ℂ) * MajSp.err HW.phi χ (δ * w) (w * x)‖ₑ :=
        ofReal_norm _
    _ ≤ ∫⁻ w in Icc (1 / 4 : ℝ) 1, ‖(HW.eta2 w : ℂ) * MajSp.err HW.phi χ (δ * w) (w * x)‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ w in Icc (1 / 4 : ℝ) 1,
          ENNReal.ofReal (‖MajSp.err HW.phi χ (δ * w) (w * x)‖ * HW.eta2 w) := by
        refine lintegral_congr fun w => ?_
        rw [← ofReal_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg (HW.eta2_nonneg w),
          mul_comm]

end Principia.Common.TernaryGoldbach.HM
