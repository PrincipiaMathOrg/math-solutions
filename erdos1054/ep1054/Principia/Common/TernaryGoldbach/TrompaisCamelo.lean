/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TrompaisPoisson

set_option autoImplicit false

/-!
# `MPTC.CameloSup` from Helfgott's cited grid and `lem:wollust`, PROVED

`h(t) = 4g(t) + f̂(t)` (`g = HC.wollG`, `f̂ = HC.cameloFHat`). The cited computer check
`HC.CameloGridCited` bounds `|h|` at `t = j/1000`, `j ≤ 655000`, by `31.520705`; the rest is
analysis, done here:

* **Interpolation** (`h_interp`): `|h(t) − μh(a) − νh(b)| ≤ 48π²·(t − a)(b − t)/2` on a cell
  `[a, b]` (`μ = (b − t)/(b − a)`, `ν = (t − a)/(b − a)`). Each exponential `e(ct)` obeys the
  linear-interpolation bound with constant `(2πc)²` (`e_interp`: the real part of `w̄·e(c·)`
  plus a convex quadratic is convex, `interp_le`); `g` contributes `4·9π²` and `f̂` contributes
  `∫|f(x)|(2πx)² dx = 12π²`. On a cell of length `1/1000` this is `≤ 6·10⁻⁵`, so
  `|h| ≤ 31.520765` on `[0, 655]`.
* **Tail** (`tail_le`): for `t ≥ 655`, `|h(t)| ≤ 4·7.87052 + 160/(2πt) ≤ 31.52098`, with
  `HC.WollustCited` and one integration by parts on each piece of `f` (`ibp1`; total variation
  of `f` with its jumps: `64 + 16 + 16 + 4 + 48 + 12 = 160`).
* **Negative `t`**: `h(−t) = conj h(t)` (`h_neg`).
-/

namespace Principia.Common.TernaryGoldbach.MPTS

open Principia.Common.Goldbach MeasureTheory Set
open Principia.Common.TernaryGoldbach.MPTC Principia.Common.TernaryGoldbach.MPTI
  Principia.Common.TernaryGoldbach.MPTP

/-! ## (1) Linear interpolation of a `C²` real function -/

/-- **Linear-interpolation error from a lower bound on `ψ''`**: if `ψ'' ≥ −M` then
`ψ(t) ≤ μψ(a) + νψ(b) + M(t − a)(b − t)/2` on `[a, b]`. -/
theorem interp_le (ψ ψ1 ψ2 : ℝ → ℝ) (M a b t : ℝ) (hab : a < b) (hta : a ≤ t) (htb : t ≤ b)
    (h1 : ∀ x, HasDerivAt ψ (ψ1 x) x) (h2 : ∀ x, HasDerivAt ψ1 (ψ2 x) x)
    (hM : ∀ x, -M ≤ ψ2 x) :
    ψ t ≤ (b - t) / (b - a) * ψ a + (t - a) / (b - a) * ψ b + M * ((t - a) * (b - t)) / 2 := by
  set χ : ℝ → ℝ := fun x => ψ x + M * ((x - a) * (x - b)) / 2 with hχ
  have d1 : ∀ x, HasDerivAt χ (ψ1 x + M * (2 * x - a - b) / 2) x := by
    intro x
    have hq : HasDerivAt (fun y : ℝ => M * ((y - a) * (y - b)) / 2)
        (M * (2 * x - a - b) / 2) x := by
      have := ((((hasDerivAt_id' x).sub_const a).mul ((hasDerivAt_id' x).sub_const b)).const_mul
        M).div_const 2
      exact this.congr_deriv (by ring)
    exact (h1 x).add hq
  have d2 : ∀ x, HasDerivAt (fun y => ψ1 y + M * (2 * y - a - b) / 2) (ψ2 x + M) x := by
    intro x
    have hq : HasDerivAt (fun y : ℝ => M * (2 * y - a - b) / 2) M x := by
      have := ((((hasDerivAt_id' x).const_mul 2).sub_const a).sub_const b |>.const_mul
        M).div_const 2
      exact this.congr_deriv (by ring)
    exact (h2 x).add hq
  have hconv : ConvexOn ℝ (Icc a b) χ :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
      (fun x _ => (d1 x).continuousAt.continuousWithinAt)
      (fun x _ => (d1 x).hasDerivWithinAt) (fun x _ => (d2 x).hasDerivWithinAt)
      (fun x _ => by linarith [hM x])
  have hba : 0 < b - a := by linarith
  have hμ : 0 ≤ (b - t) / (b - a) := div_nonneg (by linarith) hba.le
  have hν : 0 ≤ (t - a) / (b - a) := div_nonneg (by linarith) hba.le
  have hsum : (b - t) / (b - a) + (t - a) / (b - a) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hba.ne']
    ring
  have := hconv.2 (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hμ hν hsum
  have ht : ((b - t) / (b - a)) • a + ((t - a) / (b - a)) • b = t := by
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [ht] at this
  simp only [smul_eq_mul, hχ, sub_self, zero_mul, mul_zero, zero_div, add_zero] at this
  nlinarith [this]

/-! ## (2) The exponential -/

/-- `d/dx e(cx) = 2πic·e(cx)`. -/
theorem hasDerivAt_ec (c x : ℝ) :
    HasDerivAt (fun y : ℝ => e (c * y)) (2 * Real.pi * Complex.I * c * e (c * x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa using (hasDerivAt_id' x).const_mul c
  have h3 := ((h1.ofReal_comp).const_mul (2 * Real.pi * Complex.I)).cexp
  unfold e
  convert h3 using 1
  push_cast
  ring

/-- The real part of a derivative. -/
theorem hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).re) f'.re x :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf

/-- **Linear interpolation of `e(c·)`**:
`|e(ct) − μe(ca) − νe(cb)| ≤ (2πc)²(t − a)(b − t)/2` on `[a, b]`. -/
theorem e_interp (c a b t : ℝ) (hab : a < b) (hta : a ≤ t) (htb : t ≤ b) :
    ‖e (c * t) - (((b - t) / (b - a) : ℝ) : ℂ) * e (c * a) -
        (((t - a) / (b - a) : ℝ) : ℂ) * e (c * b)‖ ≤
      (2 * Real.pi * c) ^ 2 * ((t - a) * (b - t)) / 2 := by
  set z := e (c * t) - (((b - t) / (b - a) : ℝ) : ℂ) * e (c * a) -
    (((t - a) / (b - a) : ℝ) : ℂ) * e (c * b) with hz
  set w := (starRingEnd ℂ) z
  obtain ⟨k, hkdef⟩ : ∃ k : ℂ, k = 2 * Real.pi * Complex.I * c := ⟨_, rfl⟩
  have hk : ‖k‖ = 2 * Real.pi * |c| := by
    rw [hkdef]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, abs_of_pos Real.pi_pos]
  have dE : ∀ x, HasDerivAt (fun y : ℝ => e (c * y)) (k * e (c * x)) x := by
    intro x
    rw [hkdef]
    exact hasDerivAt_ec c x
  have d1 : ∀ x, HasDerivAt (fun y => (w * e (c * y)).re) (w * (k * e (c * x))).re x :=
    fun x => hasDerivAt_re ((dE x).const_mul w)
  have d2 : ∀ x, HasDerivAt (fun y => (w * (k * e (c * y))).re)
      (w * (k * (k * e (c * x)))).re x :=
    fun x => hasDerivAt_re (((dE x).const_mul k).const_mul w)
  have hM : ∀ x, -(‖w‖ * (2 * Real.pi * c) ^ 2) ≤ (w * (k * (k * e (c * x)))).re := by
    intro x
    have h1 := Complex.abs_re_le_norm (w * (k * (k * e (c * x))))
    have h2 : ‖w * (k * (k * e (c * x)))‖ = ‖w‖ * (2 * Real.pi * c) ^ 2 := by
      rw [norm_mul, norm_mul, norm_mul, norm_e, hk, mul_one]
      rw [show 2 * Real.pi * |c| * (2 * Real.pi * |c|) = (2 * Real.pi * |c|) ^ 2 by ring,
        mul_pow, mul_pow, sq_abs]
      ring
    rw [h2] at h1
    linarith [neg_abs_le (w * (k * (k * e (c * x)))).re]
  have hI := interp_le _ _ _ _ a b t hab hta htb d1 d2 hM
  have hre : (w * z).re = (w * e (c * t)).re - (b - t) / (b - a) * (w * e (c * a)).re -
      (t - a) / (b - a) * (w * e (c * b)).re := by
    rw [hz, mul_sub, mul_sub, Complex.sub_re, Complex.sub_re, mul_left_comm w,
      mul_left_comm w, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hwz : (w * z).re = ‖z‖ ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hnw : ‖w‖ = ‖z‖ := Complex.norm_conj z
  have hK : 0 ≤ (t - a) * (b - t) := mul_nonneg (by linarith) (by linarith)
  have key : ‖z‖ ^ 2 ≤ ‖z‖ * ((2 * Real.pi * c) ^ 2 * ((t - a) * (b - t)) / 2) := by
    rw [← hwz, hre]
    rw [hnw] at hI
    nlinarith [hI]
  rcases (norm_nonneg z).lt_or_eq with hpos | hzero
  · nlinarith [key]
  · rw [← hzero]
    positivity

/-! ## (3) Interpolation of `h = 4g + f̂` -/

/-- `h(t) = 4g(t) + f̂(t)`. -/
noncomputable def hC (t : ℝ) : ℂ := 4 * HC.wollG t + HC.cameloFHat t

/-- `e(−(x·u)) = e((−x)u)`, `e(−u/k) = e((−1/k)u)`. -/
theorem eE_eq (u x : ℝ) : eE u x = e ((-x) * u) := by
  unfold eE; congr 1; ring

/-- The interpolation error of one piece `∫_p^q φ(x)e(−xu) dx` with `|φ(x)|x² ≤ 4`. -/
theorem piece_interp (φ : ℝ → ℝ) (p q a b t : ℝ) (hpq : p ≤ q) (hp : 0 < p)
    (hφ : ContinuousOn φ (Icc p q)) (hb : ∀ x ∈ Icc p q, |φ x| * x ^ 2 ≤ 4)
    (hab : a < b) (hta : a ≤ t) (htb : t ≤ b) :
    ‖(∫ x in p..q, (φ x : ℂ) * eE t x) -
        (((b - t) / (b - a) : ℝ) : ℂ) * (∫ x in p..q, (φ x : ℂ) * eE a x) -
        (((t - a) / (b - a) : ℝ) : ℂ) * (∫ x in p..q, (φ x : ℂ) * eE b x)‖ ≤
      16 * Real.pi ^ 2 * ((t - a) * (b - t)) / 2 * (q - p) := by
  have hint : ∀ u : ℝ, IntervalIntegrable (fun x => (φ x : ℂ) * eE u x) volume p q := by
    intro u
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hpq]
    exact (Complex.continuous_ofReal.comp_continuousOn hφ).mul (continuous_eE u).continuousOn
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hint t) ((hint a).const_mul _),
    ← intervalIntegral.integral_sub ((hint t).sub ((hint a).const_mul _)) ((hint b).const_mul _)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := p) (b := q)
    (C := 16 * Real.pi ^ 2 * ((t - a) * (b - t)) / 2)
    (f := fun x => (φ x : ℂ) * eE t x - (((b - t) / (b - a) : ℝ) : ℂ) * ((φ x : ℂ) * eE a x) -
      (((t - a) / (b - a) : ℝ) : ℂ) * ((φ x : ℂ) * eE b x)) fun x hx => by
    rw [uIoc_of_le hpq] at hx
    have hx' : x ∈ Icc p q := ⟨hx.1.le, hx.2⟩
    have hx0 : 0 < x := lt_of_lt_of_le hp hx'.1
    have e1 : (φ x : ℂ) * eE t x - (((b - t) / (b - a) : ℝ) : ℂ) * ((φ x : ℂ) * eE a x) -
        (((t - a) / (b - a) : ℝ) : ℂ) * ((φ x : ℂ) * eE b x) = (φ x : ℂ) *
        (e ((-x) * t) - (((b - t) / (b - a) : ℝ) : ℂ) * e ((-x) * a) -
          (((t - a) / (b - a) : ℝ) : ℂ) * e ((-x) * b)) := by
      rw [eE_eq, eE_eq, eE_eq]; ring
    rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hE := e_interp (-x) a b t hab hta htb
    have hK : 0 ≤ (t - a) * (b - t) := mul_nonneg (by linarith) (by linarith)
    calc |φ x| * ‖e ((-x) * t) - (((b - t) / (b - a) : ℝ) : ℂ) * e ((-x) * a) -
          (((t - a) / (b - a) : ℝ) : ℂ) * e ((-x) * b)‖
        ≤ |φ x| * ((2 * Real.pi * -x) ^ 2 * ((t - a) * (b - t)) / 2) :=
          mul_le_mul_of_nonneg_left hE (abs_nonneg _)
      _ = (|φ x| * x ^ 2) * (4 * Real.pi ^ 2 * ((t - a) * (b - t)) / 2) := by ring
      _ ≤ 4 * (4 * Real.pi ^ 2 * ((t - a) * (b - t)) / 2) :=
          mul_le_mul_of_nonneg_right (hb x hx') (by positivity)
      _ = 16 * Real.pi ^ 2 * ((t - a) * (b - t)) / 2 := by ring
  rw [abs_of_nonneg (by linarith : 0 ≤ q - p)] at h
  exact h

/-- **Interpolation of `h`**: `|h(t) − μh(a) − νh(b)| ≤ 48π²(t − a)(b − t)/2`. -/
theorem h_interp (a b t : ℝ) (hab : a < b) (hta : a ≤ t) (htb : t ≤ b) :
    ‖hC t - (((b - t) / (b - a) : ℝ) : ℂ) * hC a - (((t - a) / (b - a) : ℝ) : ℂ) * hC b‖ ≤
      48 * Real.pi ^ 2 * ((t - a) * (b - t)) / 2 := by
  have hK : 0 ≤ (t - a) * (b - t) := mul_nonneg (by linarith) (by linarith)
  set μ : ℂ := (((b - t) / (b - a) : ℝ) : ℂ)
  set ν : ℂ := (((t - a) / (b - a) : ℝ) : ℂ)
  have hcL : ContinuousOn (fun x : ℝ => -4 / x ^ 2) (Icc (1 / 4) (1 / 2)) :=
    continuousOn_const.div (continuousOn_pow 2) fun x hx => by
      have : (0 : ℝ) < x := by linarith [hx.1]
      positivity
  have hcR : ContinuousOn (fun x : ℝ => 4 / x ^ 2) (Icc (1 / 2) 1) :=
    continuousOn_const.div (continuousOn_pow 2) fun x hx => by
      have : (0 : ℝ) < x := by linarith [hx.1]
      positivity
  have bL : ∀ x ∈ Icc (1 / 4 : ℝ) (1 / 2), |-4 / x ^ 2| * x ^ 2 ≤ 4 := by
    intro x hx
    have : (0 : ℝ) < x := by linarith [hx.1]
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos (by positivity),
      div_mul_cancel₀ _ (by positivity)]
  have bR : ∀ x ∈ Icc (1 / 2 : ℝ) 1, |4 / x ^ 2| * x ^ 2 ≤ 4 := by
    intro x hx
    have : (0 : ℝ) < x := by linarith [hx.1]
    rw [abs_of_pos (by positivity), div_mul_cancel₀ _ (by positivity)]
  have PL := piece_interp (fun x => -4 / x ^ 2) (1 / 4) (1 / 2) a b t (by norm_num)
    (by norm_num) hcL bL hab hta htb
  have PR := piece_interp (fun x => 4 / x ^ 2) (1 / 2) 1 a b t (by norm_num)
    (by norm_num) hcR bR hab hta htb
  have E1 := e_interp (-1 / 4) a b t hab hta htb
  have E2 := e_interp (-1 / 2) a b t hab hta htb
  have E3 := e_interp (-1) a b t hab hta htb
  have hw : ∀ u : ℝ, HC.wollG u =
      4 * e ((-1 / 4) * u) - 4 * e ((-1 / 2) * u) + e ((-1) * u) := by
    intro u
    unfold HC.wollG
    congr 3 <;> ring_nf
  have hsplit : hC t - μ * hC a - ν * hC b =
      4 * (4 * (e ((-1 / 4) * t) - μ * e ((-1 / 4) * a) - ν * e ((-1 / 4) * b)) -
        4 * (e ((-1 / 2) * t) - μ * e ((-1 / 2) * a) - ν * e ((-1 / 2) * b)) +
        (e ((-1) * t) - μ * e ((-1) * a) - ν * e ((-1) * b))) +
      (((∫ x in (1 / 4 : ℝ)..(1 / 2), ((-4 / x ^ 2 : ℝ) : ℂ) * eE t x) -
          μ * (∫ x in (1 / 4 : ℝ)..(1 / 2), ((-4 / x ^ 2 : ℝ) : ℂ) * eE a x) -
          ν * (∫ x in (1 / 4 : ℝ)..(1 / 2), ((-4 / x ^ 2 : ℝ) : ℂ) * eE b x)) +
        ((∫ x in (1 / 2 : ℝ)..1, ((4 / x ^ 2 : ℝ) : ℂ) * eE t x) -
          μ * (∫ x in (1 / 2 : ℝ)..1, ((4 / x ^ 2 : ℝ) : ℂ) * eE a x) -
          ν * (∫ x in (1 / 2 : ℝ)..1, ((4 / x ^ 2 : ℝ) : ℂ) * eE b x))) := by
    unfold hC
    rw [hw, hw, hw, cameloFHat_split, cameloFHat_split, cameloFHat_split]
    ring
  rw [hsplit]
  have hpi2 : (2 * Real.pi * (-1 / 4)) ^ 2 = Real.pi ^ 2 / 4 := by ring
  have hpi3 : (2 * Real.pi * (-1 / 2)) ^ 2 = Real.pi ^ 2 := by ring
  have hpi4 : (2 * Real.pi * (-1)) ^ 2 = 4 * Real.pi ^ 2 := by ring
  rw [hpi2] at E1
  rw [hpi3] at E2
  rw [hpi4] at E3
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  calc _ ≤ ‖(4 : ℂ) * (4 * (e ((-1 / 4) * t) - μ * e ((-1 / 4) * a) - ν * e ((-1 / 4) * b)) -
        4 * (e ((-1 / 2) * t) - μ * e ((-1 / 2) * a) - ν * e ((-1 / 2) * b)) +
        (e ((-1) * t) - μ * e ((-1) * a) - ν * e ((-1) * b)))‖ +
      (‖(∫ x in (1 / 4 : ℝ)..(1 / 2), ((-4 / x ^ 2 : ℝ) : ℂ) * eE t x) -
          μ * (∫ x in (1 / 4 : ℝ)..(1 / 2), ((-4 / x ^ 2 : ℝ) : ℂ) * eE a x) -
          ν * (∫ x in (1 / 4 : ℝ)..(1 / 2), ((-4 / x ^ 2 : ℝ) : ℂ) * eE b x)‖ +
        ‖(∫ x in (1 / 2 : ℝ)..1, ((4 / x ^ 2 : ℝ) : ℂ) * eE t x) -
          μ * (∫ x in (1 / 2 : ℝ)..1, ((4 / x ^ 2 : ℝ) : ℂ) * eE a x) -
          ν * (∫ x in (1 / 2 : ℝ)..1, ((4 / x ^ 2 : ℝ) : ℂ) * eE b x)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ 4 * (4 * (Real.pi ^ 2 / 4 * ((t - a) * (b - t)) / 2) +
          4 * (Real.pi ^ 2 * ((t - a) * (b - t)) / 2) +
          4 * Real.pi ^ 2 * ((t - a) * (b - t)) / 2) +
        (16 * Real.pi ^ 2 * ((t - a) * (b - t)) / 2 * (1 / 2 - 1 / 4) +
          16 * Real.pi ^ 2 * ((t - a) * (b - t)) / 2 * (1 - 1 / 2)) := by
      refine add_le_add ?_ (add_le_add PL PR)
      rw [norm_mul, h4]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) E3)
      rw [norm_mul, norm_mul, h4]
      exact add_le_add (mul_le_mul_of_nonneg_left E1 (by norm_num))
        (mul_le_mul_of_nonneg_left E2 (by norm_num))
    _ = 48 * Real.pi ^ 2 * ((t - a) * (b - t)) / 2 := by ring

/-! ## (4) The grid: `[0, 655)` -/

/-- `‖E‖ = 1`. -/
theorem norm_eE (u x : ℝ) : ‖eE u x‖ = 1 := norm_e _

/-- **`|h(t)| ≤ c₀` on `[0, 655)`** from the cited grid and `h_interp`. -/
theorem grid_le (hG : HC.CameloGridCited) (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 655) :
    ‖hC t‖ ≤ MPc.c0 := by
  set j := ⌊1000 * t⌋₊ with hj
  have hjt : (j : ℝ) ≤ 1000 * t := Nat.floor_le (by positivity)
  have htj : 1000 * t < j + 1 := Nat.lt_floor_add_one _
  have hj6 : j < 655000 := by
    rw [hj, Nat.floor_lt (by positivity)]
    push_cast
    linarith
  set a : ℝ := (j : ℝ) / 1000 with ha
  set b : ℝ := ((j + 1 : ℕ) : ℝ) / 1000 with hb
  have hb' : b = ((j : ℝ) + 1) / 1000 := by rw [hb]; push_cast; ring
  have hab : a < b := by rw [hb', ha]; linarith
  have hta : a ≤ t := by rw [ha]; linarith
  have htb : t ≤ b := by rw [hb']; linarith
  have Ga : ‖hC a‖ ≤ 31.52066 + 4.5e-5 := hG j (by omega)
  have Gb : ‖hC b‖ ≤ 31.52066 + 4.5e-5 := hG (j + 1) (by omega)
  have hI := h_interp a b t hab hta htb
  have hμ : 0 ≤ (b - t) / (b - a) := div_nonneg (by linarith) (by linarith)
  have hν : 0 ≤ (t - a) / (b - a) := div_nonneg (by linarith) (by linarith)
  have hsum : (b - t) / (b - a) + (t - a) / (b - a) = 1 := by
    rw [← add_div, div_eq_one_iff_eq (by linarith)]
    ring
  have hba : b - a = 1 / 1000 := by rw [hb', ha]; ring
  have hK : (t - a) * (b - t) ≤ 1 / 4000000 := by
    nlinarith [sq_nonneg (t - (a + b) / 2)]
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hpi2 : Real.pi ^ 2 < 9.9225 := by nlinarith
  have herr : 48 * Real.pi ^ 2 * ((t - a) * (b - t)) / 2 ≤ 6e-5 := by
    have hK0 : 0 ≤ (t - a) * (b - t) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have htri : ‖hC t‖ ≤ ‖(((b - t) / (b - a) : ℝ) : ℂ) * hC a‖ +
      ‖(((t - a) / (b - a) : ℝ) : ℂ) * hC b‖ +
      ‖hC t - (((b - t) / (b - a) : ℝ) : ℂ) * hC a - (((t - a) / (b - a) : ℝ) : ℂ) * hC b‖ := by
    have e : hC t = (((b - t) / (b - a) : ℝ) : ℂ) * hC a +
        (((t - a) / (b - a) : ℝ) : ℂ) * hC b +
        (hC t - (((b - t) / (b - a) : ℝ) : ℂ) * hC a - (((t - a) / (b - a) : ℝ) : ℂ) * hC b) := by
      ring
    calc ‖hC t‖ = ‖_‖ := congrArg norm e
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hμ, abs_of_nonneg hν] at htri
  have ma := mul_le_mul_of_nonneg_left Ga hμ
  have mb := mul_le_mul_of_nonneg_left Gb hν
  unfold MPc.c0
  nlinarith

/-! ## (5) The tail: `t ≥ 655` -/

/-- **One integration by parts**: `2πiu∫_a^b φE = ∫_a^b φ'E − (φ(b)E(b) − φ(a)E(a))`. -/
theorem ibp1 (φ φ1 : ℝ → ℝ) (a b u : ℝ) (hab : a ≤ b)
    (h1 : ∀ t ∈ Icc a b, HasDerivAt φ (φ1 t) t) (hc : ContinuousOn φ1 (Icc a b)) :
    2 * Real.pi * Complex.I * u * ∫ t in a..b, (φ t : ℂ) * eE u t =
      (∫ t in a..b, (φ1 t : ℂ) * eE u t) - ((φ b : ℂ) * eE u b - (φ a : ℂ) * eE u a) := by
  have hφc : ContinuousOn φ (Icc a b) := fun t ht => (h1 t ht).continuousAt.continuousWithinAt
  have hEc := continuous_eE u
  have i1 : IntervalIntegrable (fun t => (φ t : ℂ) * eE u t) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    exact (Complex.continuous_ofReal.comp_continuousOn hφc).mul hEc.continuousOn
  have i2 : IntervalIntegrable (fun t => (φ1 t : ℂ) * eE u t) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    exact (Complex.continuous_ofReal.comp_continuousOn hc).mul hEc.continuousOn
  have hG : ∀ t ∈ uIcc a b, HasDerivAt (fun s => (φ s : ℂ) * eE u s)
      ((φ1 t : ℂ) * eE u t - 2 * Real.pi * Complex.I * u * ((φ t : ℂ) * eE u t)) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have := ((h1 t ht).ofReal_comp).mul (hasDerivAt_eE u t)
    refine this.congr_deriv ?_
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hG (i2.sub (i1.const_mul _))
  rw [intervalIntegral.integral_sub i2 (i1.const_mul _), intervalIntegral.integral_const_mul]
    at hint
  linear_combination -hint

/-- `∫_p^q 8/x³ = 4/p² − 4/q²` for `0 < p ≤ q`. -/
theorem int_inv_cube (p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) :
    ∫ x in p..q, 8 / x ^ 3 = 4 / p ^ 2 - 4 / q ^ 2 := by
  have hd : ∀ x ∈ uIcc p q, HasDerivAt (fun y : ℝ => -4 / y ^ 2) (8 / x ^ 3) x := by
    intro x hx
    rw [uIcc_of_le hpq] at hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le hp hx.1).ne'
    have := (hasDerivAt_const x (-4 : ℝ)).div ((hasDerivAt_id' x).pow 2) (pow_ne_zero 2 hx0)
    refine this.congr_deriv ?_
    simp only [Pi.pow_apply]
    field_simp
    ring
  have hi : IntervalIntegrable (fun x : ℝ => 8 / x ^ 3) volume p q := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hpq]
    exact continuousOn_const.div (continuousOn_pow 3) fun x hx =>
      pow_ne_zero 3 (lt_of_lt_of_le hp hx.1).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  ring

/-- `‖∫_p^q ψ(x)E(x) dx‖ ≤ 4/p² − 4/q²` when `|ψ(x)| = 8/x³`. -/
theorem norm_piece_le (ψ : ℝ → ℝ) (p q u : ℝ) (hp : 0 < p) (hpq : p ≤ q)
    (hψ : ∀ x ∈ Icc p q, |ψ x| = 8 / x ^ 3) :
    ‖∫ x in p..q, (ψ x : ℂ) * eE u x‖ ≤ 4 / p ^ 2 - 4 / q ^ 2 := by
  refine (intervalIntegral.norm_integral_le_integral_norm hpq).trans (le_of_eq ?_)
  rw [← int_inv_cube p q hp hpq]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le hpq] at hx
  rw [norm_mul, norm_eE, mul_one, Complex.norm_real, Real.norm_eq_abs, hψ x hx]

/-- **`2π|u|·|f̂(u)| ≤ 160`** (variation of `f` with its jumps). -/
theorem fhat_tail (u : ℝ) : 2 * Real.pi * |u| * ‖HC.cameloFHat u‖ ≤ 160 := by
  have pos : ∀ x ∈ Icc (1 / 4 : ℝ) 1, 0 < x := fun x hx => by linarith [hx.1]
  have L := ibp1 (fun x => -4 / x ^ 2) (fun x => 8 / x ^ 3) (1 / 4) (1 / 2) u (by norm_num)
    (fun x hx => by
      have hx0 : x ≠ 0 := (pos x ⟨hx.1, by linarith [hx.2]⟩).ne'
      have := (hasDerivAt_const x (-4 : ℝ)).div ((hasDerivAt_id' x).pow 2) (pow_ne_zero 2 hx0)
      refine this.congr_deriv ?_
      simp only [Pi.pow_apply]
      field_simp
      ring)
    (continuousOn_const.div (continuousOn_pow 3) fun x hx =>
      pow_ne_zero 3 (pos x ⟨hx.1, by linarith [hx.2]⟩).ne')
  have R := ibp1 (fun x => 4 / x ^ 2) (fun x => -8 / x ^ 3) (1 / 2) 1 u (by norm_num)
    (fun x hx => by
      have hx0 : x ≠ 0 := (pos x ⟨by linarith [hx.1], hx.2⟩).ne'
      have := (hasDerivAt_const x (4 : ℝ)).div ((hasDerivAt_id' x).pow 2) (pow_ne_zero 2 hx0)
      refine this.congr_deriv ?_
      simp only [Pi.pow_apply]
      field_simp
      ring)
    (continuousOn_const.div (continuousOn_pow 3) fun x hx =>
      pow_ne_zero 3 (pos x ⟨by linarith [hx.1], hx.2⟩).ne')
  have NL := norm_piece_le (fun x => 8 / x ^ 3) (1 / 4) (1 / 2) u (by norm_num) (by norm_num)
    fun x hx => abs_of_pos (by have := pos x ⟨hx.1, by linarith [hx.2]⟩; positivity)
  have NR := norm_piece_le (fun x => -8 / x ^ 3) (1 / 2) 1 u (by norm_num) (by norm_num)
    fun x hx => by
      have := pos x ⟨by linarith [hx.1], hx.2⟩
      rw [neg_div, abs_neg, abs_of_pos (by positivity)]
  have hk : ‖2 * (Real.pi : ℂ) * Complex.I * u‖ = 2 * Real.pi * |u| := by
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, abs_of_pos Real.pi_pos]
  rw [← hk, ← norm_mul, cameloFHat_split, mul_add, L, R]
  have b1 : ‖((-4 / (1 / 2) ^ 2 : ℝ) : ℂ) * eE u (1 / 2)‖ = 16 := by
    rw [norm_mul, norm_eE, mul_one, Complex.norm_real]; norm_num
  have b2 : ‖((-4 / (1 / 4) ^ 2 : ℝ) : ℂ) * eE u (1 / 4)‖ = 64 := by
    rw [norm_mul, norm_eE, mul_one, Complex.norm_real]; norm_num
  have b3 : ‖((4 / 1 ^ 2 : ℝ) : ℂ) * eE u 1‖ = 4 := by
    rw [norm_mul, norm_eE, mul_one, Complex.norm_real]; norm_num
  have b4 : ‖((4 / (1 / 2) ^ 2 : ℝ) : ℂ) * eE u (1 / 2)‖ = 16 := by
    rw [norm_mul, norm_eE, mul_one, Complex.norm_real]; norm_num
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_sub_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _)))
    ((norm_sub_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _)))).trans ?_
  rw [b1, b2, b3, b4]
  have c1 : (4 : ℝ) / (1 / 4) ^ 2 - 4 / (1 / 2) ^ 2 = 48 := by norm_num
  have c2 : (4 : ℝ) / (1 / 2) ^ 2 - 4 / 1 ^ 2 = 12 := by norm_num
  rw [c1] at NL
  rw [c2] at NR
  linarith

/-- **`|h(t)| ≤ c₀` for `t ≥ 655`** from `lem:wollust` and `fhat_tail`. -/
theorem tail_le (hW : HC.WollustCited) (t : ℝ) (ht : 655 ≤ t) : ‖hC t‖ ≤ MPc.c0 := by
  have hpi := Real.pi_gt_d2
  have hF := fhat_tail t
  rw [abs_of_pos (by linarith)] at hF
  have hpos : 0 < 2 * Real.pi * t := by positivity
  have hF' : ‖HC.cameloFHat t‖ ≤ 160 / (2 * Real.pi * t) := by
    rw [le_div_iff₀ hpos]; linarith
  have h655 : 160 / (2 * Real.pi * t) ≤ 0.0389 := by
    rw [div_le_iff₀ hpos]; nlinarith
  have hw := hW t
  unfold hC MPc.c0
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [h4]
  linarith

/-! ## (6) Negative `t`, and the assembly -/

/-- `conj e(x) = e(−x)`. -/
theorem e_conj (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **`h(−t) = conj h(t)`.** -/
theorem h_neg (t : ℝ) : hC (-t) = (starRingEnd ℂ) (hC t) := by
  unfold hC HC.wollG HC.cameloFHat
  rw [map_add, map_mul, map_ofNat, map_add, map_sub, map_mul, map_mul, map_ofNat, e_conj, e_conj,
    e_conj, ← intervalIntegral.intervalIntegral_conj]
  congr 1
  · congr 3 <;> ring_nf
  · refine intervalIntegral.integral_congr fun x _ => ?_
    rw [map_mul, Complex.conj_ofReal, e_conj]
    congr 2
    ring

/-- **`MPTC.CameloSup` from Helfgott's cited grid and `lem:wollust`, PROVED.** -/
theorem cameloSup_of (hG : HC.CameloGridCited) (hW : HC.WollustCited) : CameloSup := by
  have key : ∀ t : ℝ, 0 ≤ t → ‖hC t‖ ≤ MPc.c0 := by
    intro t ht
    rcases lt_or_ge t 655 with h | h
    · exact grid_le hG t ht h
    · exact tail_le hW t h
  intro t
  show ‖hC t‖ ≤ MPc.c0
  rcases le_total 0 t with h | h
  · exact key t h
  · have := key (-t) (by linarith)
    rw [h_neg, Complex.norm_conj] at this
    exact this

/-- **`MPT.TrompaisC` from the two cited computer checks alone, PROVED.** -/
theorem trompaisC_of_cited (hG : HC.CameloGridCited) (hW : HC.WollustCited) : MPT.TrompaisC :=
  trompaisC_of_sup (cameloSup_of hG hW)

/-- **`MPB2.TrompaisEta2` from the two cited computer checks alone, PROVED.** -/
theorem trompaisEta2_of_cited (hG : HC.CameloGridCited) (hW : HC.WollustCited) :
    MPB2.TrompaisEta2 :=
  trompaisEta2_of_sup (cameloSup_of hG hW)

end Principia.Common.TernaryGoldbach.MPTS
