/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajBandRep

set_option autoImplicit false

/-!
# `A(r) = Mh(−ir)` decays like `r⁻⁴`: five integrations by parts on `[0, 2]`

`HP.Ah r = ∫₀^∞ h(1/v)v^{ir}dv/v` is the coefficient of `HP.hH_rep`. This module proves
* `Ah_eq_mellin`: `A(r) = M h(−ir)` (Mathlib's `mellin_comp_inv`);
* `Ah_eq_int`: `A(r) = ∫₀² h_Q(t) t^{w₁−1} dt`, `h_Q(t) = h(t)/t = t(2−t)³e^{t−1/2}`,
  `w_k = k − ir`;
* `Ah_ibp`: FIVE integrations by parts (`ibp02`, Mathlib's
  `integral_mul_deriv_eq_deriv_mul_of_hasDerivAt` against `t^{w}/w`, which is continuous on
  `[0, 2]` because `Re w > 0`; the boundary term at `0` is `0^w = 0`). Every derivative of `h_Q` is
  a quartic times `e^{t−1/2}` (`qE`, `hasDerivAt_qE`: `(a,b,c,d,e) ↦ (a, 4a+b, 3b+c, 2c+d, d+e)`);
  the first three vanish at `2` (`h` has a triple zero there), the fourth does not — that is the
  jump of `h'''` at `2`, and it is why the decay is exactly `r⁻⁴`:
  `A(r) = −(w₁w₂w₃)⁻¹(q₃(2)2^{w₄}/w₄ − w₄⁻¹(q₄(2)2^{w₅}/w₅ − w₅⁻¹∫₀²q₅(t)t^{w₅}dt))`,
  `q₃(2) = −12e^{3/2}`, `q₄(2) = −72e^{3/2}`;
* `norm_Ah_le_r4`: `|A(r)| ≤ 976/r⁴` for `|r| ≥ 200` (the leading boundary term is
  `192e^{3/2} = 860.5`, the rest `≤ 25.6e^{3/2}` there);
* `norm_Ah_le_sq`: `|A(r)| ≤ 455/(1 + r²)` for every `r`, hence `integrable_Ah`.

No Plancherel, no Mellin inversion, no citation.
-/

namespace Principia.Common.TernaryGoldbach.MM

open MeasureTheory Set Filter Complex

/-! ## (1) Quartics times `e^{t−1/2}` -/

/-- `(at⁴ + bt³ + ct² + dt + e)·e^{t−1/2}`. -/
noncomputable def qE (a b c d e t : ℝ) : ℝ :=
  (a * t ^ 4 + b * t ^ 3 + c * t ^ 2 + d * t + e) * Real.exp (t - 1 / 2)

/-- `(p·e^{t−1/2})' = (p' + p)e^{t−1/2}`. -/
theorem hasDerivAt_qE (a b c d e x : ℝ) :
    HasDerivAt (qE a b c d e) (qE a (4 * a + b) (3 * b + c) (2 * c + d) (d + e) x) x := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (t - 1 / 2)) (Real.exp (x - 1 / 2) * 1) x :=
    ((hasDerivAt_id' x).sub_const (1 / 2)).exp
  have h4 := (hasDerivAt_pow 4 x).const_mul a
  have h3 := (hasDerivAt_pow 3 x).const_mul b
  have h2 := (hasDerivAt_pow 2 x).const_mul c
  have h1 := (hasDerivAt_id' x).const_mul d
  have hp : HasDerivAt (fun t : ℝ => a * t ^ 4 + b * t ^ 3 + c * t ^ 2 + d * t + e)
      (4 * a * x ^ 3 + 3 * b * x ^ 2 + 2 * c * x + d) x := by
    refine ((((h4.add h3).add h2).add h1).add_const e).congr_deriv ?_
    norm_num
    ring
  have h := hp.mul he
  unfold qE
  refine h.congr_deriv ?_
  ring

/-- The step with the next coefficients named. -/
theorem hasDerivAt_qE' (a b c d e b' c' d' e' : ℝ) (h1 : b' = 4 * a + b) (h2 : c' = 3 * b + c)
    (h3 : d' = 2 * c + d) (h4 : e' = d + e) (x : ℝ) :
    HasDerivAt (qE a b c d e) (qE a b' c' d' e' x) x := by
  rw [h1, h2, h3, h4]
  exact hasDerivAt_qE a b c d e x

theorem continuous_qE (a b c d e : ℝ) : Continuous (qE a b c d e) := by
  unfold qE
  fun_prop

theorem qE_two (a b c d e : ℝ) :
    qE a b c d e 2 = (16 * a + 8 * b + 4 * c + 2 * d + e) * Real.exp (3 / 2) := by
  unfold qE
  rw [show (2 : ℝ) - 1 / 2 = 3 / 2 by norm_num]
  ring

/-- `h_Q(t) = h(t)/t = t(2−t)³e^{t−1/2}`. -/
noncomputable def hQ : ℝ → ℝ := qE (-1) 6 (-12) 8 0

theorem hP_eq (t : ℝ) : BL.hP t = t * hQ t := by
  unfold BL.hP hQ qE
  ring

/-! ## (2) Integration by parts on `[0, 2]` against `t^{w−1}` -/

/-- **`∫₀² u t^{w−1} = u(2)2^w/w − w⁻¹∫₀² u' t^w`** for `Re w > 0` (`0^w = 0`). -/
theorem ibp02 {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') {w : ℂ}
    (hw : 0 < w.re) :
    ∫ t in (0 : ℝ)..2, (u t : ℂ) * (t : ℂ) ^ (w - 1) =
      (u 2 : ℂ) * (2 : ℂ) ^ w / w - 1 / w * ∫ t in (0 : ℝ)..2, (u' t : ℂ) * (t : ℂ) ^ w := by
  have hw0 : w ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hw
    exact lt_irrefl 0 hw
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun x => (hu x).continuousAt
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := 0) (b := 2) (u := fun t => (u t : ℂ)) (v := fun t => (t : ℂ) ^ w / w)
    (u' := fun t => (u' t : ℂ)) (v' := fun t => (t : ℂ) ^ (w - 1))
    (Complex.continuous_ofReal.comp huc).continuousOn
    (fun t _ => ((continuousAt_ofReal_cpow_const t w (Or.inl hw)).div_const w).continuousWithinAt)
    (fun x _ => (hu x).ofReal_comp)
    (fun x hx => by
      rw [min_eq_left (by norm_num), max_eq_right (by norm_num)] at hx
      have h := hasDerivAt_ofReal_cpow_const' hx.1.ne' (r := w - 1) (fun h => hw0 (by
        linear_combination h))
      simpa only [sub_add_cancel] using h)
    ((Complex.continuous_ofReal.comp hu').intervalIntegrable 0 2)
    (intervalIntegral.intervalIntegrable_cpow' (by
      rw [Complex.sub_re, Complex.one_re]
      linarith))
  have e : ∫ x in (0 : ℝ)..2, (u' x : ℂ) * ((x : ℂ) ^ w / w) =
      (∫ x in (0 : ℝ)..2, (u' x : ℂ) * (x : ℂ) ^ w) / w := by
    rw [← intervalIntegral.integral_div]
    congr 1
    funext x
    ring
  rw [key, e, Complex.ofReal_zero, Complex.zero_cpow hw0]
  push_cast
  ring

/-! ## (3) `A(r)` as a Mellin transform and as an integral over `[0, 2]` -/

/-- **`A(r) = M h(−ir)`**. -/
theorem Ah_eq_mellin (r : ℝ) :
    HP.Ah r = mellin (fun t => (HW.hFun t : ℂ)) (-((r : ℂ) * Complex.I)) := by
  rw [← mellin_comp_inv]
  unfold HP.Ah mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv0 : (0 : ℝ) < v := hv
  have h1 := HP.cpow_shift hv0 0 r
  rw [zero_add] at h1
  rw [smul_eq_mul, ← h1, zero_sub, Complex.cpow_neg_one]
  unfold HP.aH
  rw [one_div]
  push_cast
  ring

/-- **A Mellin transform of a function supported in `[0, 2]`** as an interval integral. -/
theorem mellin_eq_int02 {f u : ℝ → ℝ} (hfu : ∀ t, 0 < t → t ≤ 2 → f t = u t)
    (hf2 : ∀ t, 2 < t → f t = 0) (w : ℂ) :
    mellin (fun t => (f t : ℂ)) w = ∫ t in (0 : ℝ)..2, (u t : ℂ) * (t : ℂ) ^ (w - 1) := by
  unfold mellin
  rw [intervalIntegral.integral_of_le (by norm_num),
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      (fun t ht => ?_)]
  · refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    simp only [smul_eq_mul]
    rw [hfu t ht.1 ht.2, mul_comm]
  · obtain ⟨h1, h2⟩ := ht
    have h3 : 2 < t := by
      by_contra hc
      exact h2 ⟨h1, not_lt.mp hc⟩
    simp only [hf2 t h3, Complex.ofReal_zero, smul_zero]

/-- `w_k = k − ir`. -/
noncomputable def wv (k r : ℝ) : ℂ := (k : ℂ) - (r : ℂ) * Complex.I

theorem wv_re (k r : ℝ) : (wv k r).re = k := by simp [wv]

theorem wv_im (k r : ℝ) : (wv k r).im = -r := by simp [wv]

theorem wv_succ (k r : ℝ) : wv (k + 1) r - 1 = wv k r := by
  unfold wv
  push_cast
  ring

theorem abs_le_norm_wv (k r : ℝ) : |r| ≤ ‖wv k r‖ := by
  have h := Complex.abs_im_le_norm (wv k r)
  rwa [wv_im, abs_neg] at h

theorem le_norm_wv {k : ℝ} (hk : 0 ≤ k) (r : ℝ) : k ≤ ‖wv k r‖ := by
  have h := Complex.abs_re_le_norm (wv k r)
  rwa [wv_re, abs_of_nonneg hk] at h

theorem sq_norm_wv (k r : ℝ) : ‖wv k r‖ ^ 2 = k ^ 2 + r ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, wv_re, wv_im]
  ring

/-- `|w₁||w₂| ≥ 1 + r²`. -/
theorem norm_w12_ge (r : ℝ) : 1 + r ^ 2 ≤ ‖wv 1 r‖ * ‖wv 2 r‖ := by
  have h : (1 + r ^ 2) ^ 2 ≤ (‖wv 1 r‖ * ‖wv 2 r‖) ^ 2 := by
    rw [mul_pow, sq_norm_wv, sq_norm_wv]
    nlinarith [sq_nonneg r]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h

/-- **`A(r) = ∫₀² h_Q(t) t^{w₁−1} dt`**. -/
theorem Ah_eq_int (r : ℝ) :
    HP.Ah r = ∫ t in (0 : ℝ)..2, (hQ t : ℂ) * (t : ℂ) ^ (wv 1 r - 1) := by
  rw [Ah_eq_mellin, mellin_eq_int02 (u := BL.hP) (fun t ht0 ht2 => BL.hFun_eq_hP ht0.le ht2)
    (fun t ht => HW.hFun_of_two_le ht.le)]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le (by norm_num)] at ht
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    simp [BL.hP, hQ, qE]
  · have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0.ne'
    have e1 : wv 1 r - 1 = -((r : ℂ) * Complex.I) := by
      unfold wv
      push_cast
      ring
    rw [e1, hP_eq, Complex.cpow_sub _ _ ht0, Complex.cpow_one]
    push_cast
    field_simp

/-! ## (4) Five integrations by parts -/

/-- `∫₀² q₅(t)t^{w₅}dt`, `q₅ = (−t⁴ − 14t³ − 42t² + 8t + 40)e^{t−1/2}`. -/
noncomputable def J5 (r : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..2, (qE (-1) (-14) (-42) 8 40 t : ℂ) * (t : ℂ) ^ wv 5 r

/-- **`A(r)` after five integrations by parts.** -/
theorem Ah_ibp (r : ℝ) :
    HP.Ah r = -(1 / (wv 1 r * wv 2 r * wv 3 r)) *
      ((qE (-1) (-6) 6 20 (-12) 2 : ℂ) * (2 : ℂ) ^ wv 4 r / wv 4 r -
        1 / wv 4 r * ((qE (-1) (-10) (-12) 32 8 2 : ℂ) * (2 : ℂ) ^ wv 5 r / wv 5 r -
          1 / wv 5 r * J5 r)) := by
  have d0 := hasDerivAt_qE' (-1) 6 (-12) 8 0 2 6 (-16) 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have d1 := hasDerivAt_qE' (-1) 2 6 (-16) 8 (-2) 12 (-4) (-8) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have d2 := hasDerivAt_qE' (-1) (-2) 12 (-4) (-8) (-6) 6 20 (-12) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have d3 := hasDerivAt_qE' (-1) (-6) 6 20 (-12) (-10) (-12) 32 8 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have d4 := hasDerivAt_qE' (-1) (-10) (-12) 32 8 (-14) (-42) 8 40 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have i0 := ibp02 d0 (continuous_qE _ _ _ _ _) (w := wv 1 r) (by rw [wv_re]; norm_num)
  have i1 := ibp02 d1 (continuous_qE _ _ _ _ _) (w := wv 2 r) (by rw [wv_re]; norm_num)
  have i2 := ibp02 d2 (continuous_qE _ _ _ _ _) (w := wv 3 r) (by rw [wv_re]; norm_num)
  have i3 := ibp02 d3 (continuous_qE _ _ _ _ _) (w := wv 4 r) (by rw [wv_re]; norm_num)
  have i4 := ibp02 d4 (continuous_qE _ _ _ _ _) (w := wv 5 r) (by rw [wv_re]; norm_num)
  have e2 : wv 2 r - 1 = wv 1 r := by rw [show (2 : ℝ) = 1 + 1 by norm_num, wv_succ]
  have e3 : wv 3 r - 1 = wv 2 r := by rw [show (3 : ℝ) = 2 + 1 by norm_num, wv_succ]
  have e4 : wv 4 r - 1 = wv 3 r := by rw [show (4 : ℝ) = 3 + 1 by norm_num, wv_succ]
  have e5 : wv 5 r - 1 = wv 4 r := by rw [show (5 : ℝ) = 4 + 1 by norm_num, wv_succ]
  rw [e2] at i1
  rw [e3] at i2
  rw [e4] at i3
  rw [e5] at i4
  have z0 : (qE (-1) 6 (-12) 8 0 2 : ℂ) = 0 := by rw [qE_two]; norm_num
  have z1 : (qE (-1) 2 6 (-16) 8 2 : ℂ) = 0 := by rw [qE_two]; norm_num
  have z2 : (qE (-1) (-2) 12 (-4) (-8) 2 : ℂ) = 0 := by rw [qE_two]; norm_num
  rw [Ah_eq_int]
  unfold hQ
  rw [i0, z0, i1, z1, i2, z2, i3, i4]
  unfold J5
  ring

/-! ## (5) The bounds -/

theorem norm_two_cpow_wv (k r : ℝ) : ‖(2 : ℂ) ^ wv k r‖ = (2 : ℝ) ^ k := by
  have h := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (wv k r)
  push_cast at h
  rw [h, wv_re]

/-- `S₅ = ∫₀²(t⁴ + 14t³ + 42t² + 8t + 40)t⁵dt = 886976/315`. -/
theorem S5_eq : ∫ t in (0 : ℝ)..2,
    ∑ k : Fin 10, (![0, 0, 0, 0, 0, 40, 8, 42, 14, 1] : Fin 10 → ℝ) k * t ^ (k : ℕ) =
      886976 / 315 := by
  rw [EN.int_poly]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ]
  norm_num

/-- **`|J₅(r)| ≤ e^{3/2}·886976/315`**. -/
theorem norm_J5_le (r : ℝ) : ‖J5 r‖ ≤ Real.exp (3 / 2) * (886976 / 315) := by
  have hb : ∀ t : ℝ, 0 < t → t ≤ 2 → ‖(qE (-1) (-14) (-42) 8 40 t : ℂ) * (t : ℂ) ^ wv 5 r‖ ≤
      Real.exp (3 / 2) *
        ∑ k : Fin 10, (![0, 0, 0, 0, 0, 40, 8, 42, 14, 1] : Fin 10 → ℝ) k * t ^ (k : ℕ) := by
    intro t ht0 ht2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
      wv_re, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_succ]
    unfold qE
    have hE : Real.exp (t - 1 / 2) ≤ Real.exp (3 / 2) := Real.exp_le_exp.mpr (by linarith)
    have hE0 := Real.exp_pos (t - 1 / 2)
    have hp : |-1 * t ^ 4 + -14 * t ^ 3 + -42 * t ^ 2 + 8 * t + 40| ≤
        t ^ 4 + 14 * t ^ 3 + 42 * t ^ 2 + 8 * t + 40 := by
      rw [abs_le]
      constructor <;> nlinarith [pow_pos ht0 2, pow_pos ht0 3, pow_pos ht0 4]
    rw [abs_mul, abs_of_pos hE0]
    have h5 : 0 ≤ t ^ 5 := by positivity
    have hq0 : 0 ≤ t ^ 4 + 14 * t ^ 3 + 42 * t ^ 2 + 8 * t + 40 := by positivity
    calc |-1 * t ^ 4 + -14 * t ^ 3 + -42 * t ^ 2 + 8 * t + 40| * Real.exp (t - 1 / 2) * t ^ 5
        ≤ (t ^ 4 + 14 * t ^ 3 + 42 * t ^ 2 + 8 * t + 40) * Real.exp (3 / 2) * t ^ 5 := by
          gcongr
      _ = _ := by ring
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (3 / 2) *
      ∑ k : Fin 10, (![0, 0, 0, 0, 0, 40, 8, 42, 14, 1] : Fin 10 → ℝ) k * t ^ (k : ℕ))
      volume 0 2 := by
    refine Continuous.intervalIntegrable ?_ 0 2
    fun_prop
  have h := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 2)
    (Eventually.of_forall fun t ht => hb t ht.1 ht.2) hint
  unfold J5
  rw [intervalIntegral.integral_const_mul, S5_eq] at h
  exact h

/-- `|c·2^{w_k}/w_k| = |c|·2^k/|w_k|`. -/
theorem norm_bdry (c k r : ℝ) :
    ‖(c : ℂ) * (2 : ℂ) ^ wv k r / wv k r‖ = |c| * (2 : ℝ) ^ k * ‖wv k r‖⁻¹ := by
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_two_cpow_wv, div_eq_mul_inv]

theorem norm_one_div_mul (w z : ℂ) : ‖1 / w * z‖ = ‖z‖ * ‖w‖⁻¹ := by
  rw [norm_mul, norm_div, norm_one, one_div, mul_comm]

/-- **The norm of `A(r)` through the five-fold identity**:
`|A(r)| ≤ e^{3/2}(192/|w₄| + (2304 + S₅)/(|w₄||w₅|))/(|w₁||w₂||w₃|)`. -/
theorem norm_Ah_le_w (r : ℝ) :
    ‖HP.Ah r‖ ≤ Real.exp (3 / 2) * (192 * ‖wv 4 r‖⁻¹ +
      (2304 + 886976 / 315) * (‖wv 4 r‖⁻¹ * ‖wv 5 r‖⁻¹)) *
        (‖wv 1 r‖⁻¹ * ‖wv 2 r‖⁻¹ * ‖wv 3 r‖⁻¹) := by
  have q3 : (qE (-1) (-6) 6 20 (-12) 2 : ℂ) = ((-12 * Real.exp (3 / 2) : ℝ) : ℂ) := by
    rw [qE_two]
    norm_num
  have q4 : (qE (-1) (-10) (-12) 32 8 2 : ℂ) = ((-72 * Real.exp (3 / 2) : ℝ) : ℂ) := by
    rw [qE_two]
    norm_num
  have hE := Real.exp_pos (3 / 2)
  have a12 : |(-12 * Real.exp (3 / 2))| = 12 * Real.exp (3 / 2) := by
    rw [abs_of_neg (by linarith)]
    ring
  have a72 : |(-72 * Real.exp (3 / 2))| = 72 * Real.exp (3 / 2) := by
    rw [abs_of_neg (by linarith)]
    ring
  have r4 : (2 : ℝ) ^ (4 : ℝ) = 16 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have r5 : (2 : ℝ) ^ (5 : ℝ) = 32 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hJ := norm_J5_le r
  have i4 : 0 ≤ ‖wv 4 r‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have i5 : 0 ≤ ‖wv 5 r‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hX : ‖((-72 * Real.exp (3 / 2) : ℝ) : ℂ) * (2 : ℂ) ^ wv 5 r / wv 5 r -
      1 / wv 5 r * J5 r‖ ≤ (72 * Real.exp (3 / 2) * 32 + Real.exp (3 / 2) * (886976 / 315)) *
        ‖wv 5 r‖⁻¹ :=
    calc _ ≤ ‖((-72 * Real.exp (3 / 2) : ℝ) : ℂ) * (2 : ℂ) ^ wv 5 r / wv 5 r‖ +
          ‖1 / wv 5 r * J5 r‖ := norm_sub_le _ _
      _ = 72 * Real.exp (3 / 2) * 32 * ‖wv 5 r‖⁻¹ + ‖J5 r‖ * ‖wv 5 r‖⁻¹ := by
          rw [norm_bdry, norm_one_div_mul, a72, r5]
      _ ≤ 72 * Real.exp (3 / 2) * 32 * ‖wv 5 r‖⁻¹ +
          Real.exp (3 / 2) * (886976 / 315) * ‖wv 5 r‖⁻¹ :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hJ i5)
      _ = _ := by ring
  have hT : ‖((-12 * Real.exp (3 / 2) : ℝ) : ℂ) * (2 : ℂ) ^ wv 4 r / wv 4 r -
      1 / wv 4 r * (((-72 * Real.exp (3 / 2) : ℝ) : ℂ) * (2 : ℂ) ^ wv 5 r / wv 5 r -
        1 / wv 5 r * J5 r)‖ ≤ Real.exp (3 / 2) * (192 * ‖wv 4 r‖⁻¹ +
          (2304 + 886976 / 315) * (‖wv 4 r‖⁻¹ * ‖wv 5 r‖⁻¹)) :=
    calc _ ≤ ‖((-12 * Real.exp (3 / 2) : ℝ) : ℂ) * (2 : ℂ) ^ wv 4 r / wv 4 r‖ +
          ‖1 / wv 4 r * (((-72 * Real.exp (3 / 2) : ℝ) : ℂ) * (2 : ℂ) ^ wv 5 r / wv 5 r -
            1 / wv 5 r * J5 r)‖ := norm_sub_le _ _
      _ = 12 * Real.exp (3 / 2) * 16 * ‖wv 4 r‖⁻¹ +
          ‖((-72 * Real.exp (3 / 2) : ℝ) : ℂ) * (2 : ℂ) ^ wv 5 r / wv 5 r -
            1 / wv 5 r * J5 r‖ * ‖wv 4 r‖⁻¹ := by
          rw [norm_bdry, norm_one_div_mul, a12, r4]
      _ ≤ 12 * Real.exp (3 / 2) * 16 * ‖wv 4 r‖⁻¹ +
          (72 * Real.exp (3 / 2) * 32 + Real.exp (3 / 2) * (886976 / 315)) * ‖wv 5 r‖⁻¹ *
            ‖wv 4 r‖⁻¹ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hX i4)
      _ = _ := by ring
  rw [Ah_ibp, q3, q4, norm_mul, norm_neg, norm_div, norm_one, norm_mul, norm_mul]
  have h0 : 0 ≤ 1 / (‖wv 1 r‖ * ‖wv 2 r‖ * ‖wv 3 r‖) := by positivity
  calc _ ≤ 1 / (‖wv 1 r‖ * ‖wv 2 r‖ * ‖wv 3 r‖) * (Real.exp (3 / 2) * (192 * ‖wv 4 r‖⁻¹ +
          (2304 + 886976 / 315) * (‖wv 4 r‖⁻¹ * ‖wv 5 r‖⁻¹))) := mul_le_mul_of_nonneg_left hT h0
    _ = _ := by
        rw [one_div, mul_inv, mul_inv]
        ring

/-- **`|A(r)| ≤ 976/r⁴` for `|r| ≥ 200`.** -/
theorem norm_Ah_le_r4 {r : ℝ} (hr : 200 ≤ |r|) : ‖HP.Ah r‖ ≤ 976 / |r| ^ 4 := by
  have hR : 0 < |r| := by linarith
  have hk : ∀ k : ℝ, ‖wv k r‖⁻¹ ≤ |r|⁻¹ := fun k => inv_anti₀ hR (abs_le_norm_wv k r)
  have h := norm_Ah_le_w r
  have hE := HP.exp_three_half_le
  have hE0 := Real.exp_pos (3 / 2)
  have hX : 0 < |r|⁻¹ := inv_pos.mpr hR
  have hX2 : |r|⁻¹ ≤ 1 / 200 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hr
  have hb : Real.exp (3 / 2) * (192 * ‖wv 4 r‖⁻¹ +
      (2304 + 886976 / 315) * (‖wv 4 r‖⁻¹ * ‖wv 5 r‖⁻¹)) *
        (‖wv 1 r‖⁻¹ * ‖wv 2 r‖⁻¹ * ‖wv 3 r‖⁻¹) ≤
      Real.exp (3 / 2) * (192 * |r|⁻¹ + (2304 + 886976 / 315) * (|r|⁻¹ * |r|⁻¹)) *
        (|r|⁻¹ * |r|⁻¹ * |r|⁻¹) := by
    gcongr <;> exact abs_le_norm_wv _ r
  have hc : Real.exp (3 / 2) * (192 * |r|⁻¹ + (2304 + 886976 / 315) * (|r|⁻¹ * |r|⁻¹)) *
      (|r|⁻¹ * |r|⁻¹ * |r|⁻¹) ≤ 976 * |r|⁻¹ ^ 4 := by
    have h1 : (2304 + 886976 / 315) * |r|⁻¹ ≤ (2304 + 886976 / 315) * (1 / 200) :=
      mul_le_mul_of_nonneg_left hX2 (by norm_num)
    have h2 : Real.exp (3 / 2) * (192 + (2304 + 886976 / 315) * |r|⁻¹) ≤ 976 := by
      have h3 : 192 + (2304 + 886976 / 315) * |r|⁻¹ ≤ 217.6 := by
        have : (2304 + 886976 / 315 : ℝ) * (1 / 200) ≤ 25.6 := by norm_num
        linarith
      have h4 : 0 ≤ 192 + (2304 + 886976 / 315) * |r|⁻¹ := by positivity
      nlinarith
    have hX4 : 0 ≤ |r|⁻¹ ^ 4 := by positivity
    have e : Real.exp (3 / 2) * (192 * |r|⁻¹ + (2304 + 886976 / 315) * (|r|⁻¹ * |r|⁻¹)) *
        (|r|⁻¹ * |r|⁻¹ * |r|⁻¹) =
          (Real.exp (3 / 2) * (192 + (2304 + 886976 / 315) * |r|⁻¹)) * |r|⁻¹ ^ 4 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h2 hX4
  rw [div_eq_mul_inv, ← inv_pow]
  linarith

/-- **`|A(r)| ≤ 455/(1 + r²)` for every `r`.** -/
theorem norm_Ah_le_sq (r : ℝ) : ‖HP.Ah r‖ ≤ 455 * (1 + r ^ 2)⁻¹ := by
  have h := norm_Ah_le_w r
  have hE := HP.exp_three_half_le
  have hE0 := Real.exp_pos (3 / 2)
  have h12 : ‖wv 1 r‖⁻¹ * ‖wv 2 r‖⁻¹ ≤ (1 + r ^ 2)⁻¹ := by
    rw [← mul_inv]
    exact inv_anti₀ (by positivity) (norm_w12_ge r)
  have h3 : ‖wv 3 r‖⁻¹ ≤ 3⁻¹ := inv_anti₀ (by norm_num) (le_norm_wv (by norm_num) r)
  have h4 : ‖wv 4 r‖⁻¹ ≤ 4⁻¹ := inv_anti₀ (by norm_num) (le_norm_wv (by norm_num) r)
  have h5 : ‖wv 5 r‖⁻¹ ≤ 5⁻¹ := inv_anti₀ (by norm_num) (le_norm_wv (by norm_num) r)
  have hb : Real.exp (3 / 2) * (192 * ‖wv 4 r‖⁻¹ +
      (2304 + 886976 / 315) * (‖wv 4 r‖⁻¹ * ‖wv 5 r‖⁻¹)) *
        (‖wv 1 r‖⁻¹ * ‖wv 2 r‖⁻¹ * ‖wv 3 r‖⁻¹) ≤
      Real.exp (3 / 2) * (192 * 4⁻¹ + (2304 + 886976 / 315) * (4⁻¹ * 5⁻¹)) *
        ((1 + r ^ 2)⁻¹ * 3⁻¹) := by
    gcongr
  have hS : 0 ≤ (1 + r ^ 2)⁻¹ := by positivity
  have hc : Real.exp (3 / 2) * (192 * 4⁻¹ + (2304 + 886976 / 315) * (4⁻¹ * 5⁻¹)) * 3⁻¹ ≤ 455 := by
    norm_num
    nlinarith
  calc ‖HP.Ah r‖ ≤ _ := h
    _ ≤ _ := hb
    _ = Real.exp (3 / 2) * (192 * 4⁻¹ + (2304 + 886976 / 315) * (4⁻¹ * 5⁻¹)) * 3⁻¹ *
        (1 + r ^ 2)⁻¹ := by ring
    _ ≤ 455 * (1 + r ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hc hS

/-- **`A ∈ L¹(ℝ)`.** -/
theorem integrable_Ah : Integrable HP.Ah :=
  (integrable_inv_one_add_sq.const_mul 455).mono' HP.continuous_Ah.aestronglyMeasurable
    (Eventually.of_forall fun r => norm_Ah_le_sq r)

end Principia.Common.TernaryGoldbach.MM
