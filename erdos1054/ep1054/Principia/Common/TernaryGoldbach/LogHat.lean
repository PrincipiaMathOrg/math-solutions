/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EtaHatL

set_option autoImplicit false

/-!
# The transform of `h(t) = log t·η₂(t)`, and one `T^{log}_{d,∘}` (for `lem:bostb1`'s main term)

`ĥ = MPTP.gHat (MPTL.gl 1)`. The main term of `lem:bostb1` charges
`|ĥ(−δ/2)| ≤ min(2 − log 4, 96 log 2/(π²δ²))` (`MinPieces.mainI1`):

* `hHat_le`: `|ĥ(u)| ≤ ∫|h| = 2 − log 4` (exact antiderivatives of `log t` and `log² t`);
* `hHat_ibp`: `|ĥ(u)|(2πu)² ≤ 96 log 2` (two integrations by parts; the total variation of `h'`
  is EXACTLY `96 log 2`: jumps `32 log 2`, `16 log 2`, `0` and `∫|h''| = 32 log 2 + 16 log 2`).

`tlo_main` is `MPBM.tmo_main` for `T^{log}`: Poisson (`PoissonOddLog`), the `j₀` term and
`EtaHatLBound` for the rest, `≤ (c₀ log(x/d)·d/2π²x)(π² − 4)`.
-/

namespace Principia.Common.TernaryGoldbach.MPTH

open Principia.Common.Goldbach MeasureTheory Set
open Principia.Common.TernaryGoldbach.MPTC Principia.Common.TernaryGoldbach.MPTI
  Principia.Common.TernaryGoldbach.MPTP Principia.Common.TernaryGoldbach.MPTL
  Principia.Common.TernaryGoldbach.MPc Principia.Common.TernaryGoldbach.MPB1
  Principia.Common.TernaryGoldbach.MPTE

/-- `∫_a^b f = F(b) − F(a)` for `F' = f` on `[a, b] ⊂ (0, ∞)`, `f` continuous there. -/
theorem ftc (F f : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hd : ∀ x, 0 < x → HasDerivAt F (f x) x) (hc : ContinuousOn f (Icc a b)) :
    ∫ x in a..b, f x = F b - F a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hd x ?_) ?_
  · rw [uIcc_of_le hab] at hx; linarith [hx.1]
  · exact ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le hab])

/-- `(t log t − t)' = log t`. -/
theorem hasDerivAt_A (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => t * Real.log t - t) (Real.log x) x := by
  have := ((hasDerivAt_id' x).mul (Real.hasDerivAt_log hx.ne')).sub (hasDerivAt_id' x)
  refine this.congr_deriv ?_
  field_simp
  ring

/-- `(t log² t − 2t log t + 2t)' = log² t`. -/
theorem hasDerivAt_B (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => t * Real.log t ^ 2 - 2 * (t * Real.log t) + 2 * t) (Real.log x ^ 2) x := by
  have hl := Real.hasDerivAt_log hx.ne'
  have := (((hasDerivAt_id' x).mul (hl.pow 2)).sub (((hasDerivAt_id' x).mul hl).const_mul 2)).add
    ((hasDerivAt_id' x).const_mul 2)
  refine this.congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- **`|ĥ(u)| ≤ ∫|h| = 2 − log 4`.** -/
theorem hHat_le (u : ℝ) : ‖gHat (gl 1) u‖ ≤ 2 - Real.log 4 := by
  set l2 := Real.log 2 with hl2
  have hL : Real.log 4 = 2 * l2 := by
    rw [hl2, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have lq := MPTI.log_quarter
  have lh := EN.log_half
  rw [← hl2] at lq lh
  rw [gl_hat_split 1 one_pos u, Real.log_one, hL]
  have pos : ∀ x ∈ Icc (1 / 4 : ℝ) 1, 0 < x := fun x hx => by linarith [hx.1]
  have cL : ContinuousOn (fun t : ℝ => -(Real.log t * (4 * (2 * l2 + Real.log t))))
      (Icc (1 / 4) (1 / 2)) := by
    have : ContinuousOn Real.log (Icc (1 / 4 : ℝ) (1 / 2)) :=
      Real.continuousOn_log.mono fun x hx => (pos x ⟨hx.1, by linarith [hx.2]⟩).ne'
    exact (this.mul (continuousOn_const.mul (continuousOn_const.add this))).neg
  have cR : ContinuousOn (fun t : ℝ => 4 * Real.log t ^ 2) (Icc (1 / 2) 1) := by
    have : ContinuousOn Real.log (Icc (1 / 2 : ℝ) 1) :=
      Real.continuousOn_log.mono fun x hx => (pos x ⟨by linarith [hx.1], hx.2⟩).ne'
    exact continuousOn_const.mul (this.pow 2)
  have NL : ‖∫ t in (1 / 4 : ℝ)..(1 / 2),
      (((0 + Real.log t) * (4 * (2 * l2 + Real.log t)) : ℝ) : ℂ) * eE u t‖ ≤
      ∫ t in (1 / 4 : ℝ)..(1 / 2), -(Real.log t * (4 * (2 * l2 + Real.log t))) := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans
      (le_of_eq (intervalIntegral.integral_congr fun t ht => ?_))
    rw [uIcc_of_le (by norm_num)] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h1 : Real.log t ≤ 0 := Real.log_nonpos ht0.le (by linarith [ht.2])
    have h2 : -(2 * l2) ≤ Real.log t := by
      have := Real.log_le_log (by norm_num) ht.1; rwa [lq] at this
    rw [norm_mul, MPTS.norm_eE, mul_one, Complex.norm_real, Real.norm_eq_abs, zero_add,
      abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg h1 (by linarith))]
  have NR : ‖∫ t in (1 / 2 : ℝ)..1, (((0 + Real.log t) * (-4 * Real.log t) : ℝ) : ℂ) * eE u t‖ ≤
      ∫ t in (1 / 2 : ℝ)..1, 4 * Real.log t ^ 2 := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans
      (le_of_eq (intervalIntegral.integral_congr fun t ht => ?_))
    rw [norm_mul, MPTS.norm_eE, mul_one, Complex.norm_real, Real.norm_eq_abs, zero_add,
      show Real.log t * (-4 * Real.log t) = -(4 * Real.log t ^ 2) by ring, abs_neg,
      abs_of_nonneg (by positivity)]
  have IL : ∫ t in (1 / 4 : ℝ)..(1 / 2), -(Real.log t * (4 * (2 * l2 + Real.log t))) =
      -(2 - 2 * l2 - 2 * l2 ^ 2) := by
    rw [ftc (fun t => -(4 * (2 * l2 * (t * Real.log t - t) +
        (t * Real.log t ^ 2 - 2 * (t * Real.log t) + 2 * t)))) _ (1 / 4) (1 / 2) (by norm_num)
        (by norm_num) (fun x hx => ?_) cL]
    · simp only [lq, lh]
      ring
    · have := (((hasDerivAt_A x hx).const_mul (2 * l2)).add (hasDerivAt_B x hx)).const_mul 4 |>.neg
      refine this.congr_deriv ?_
      ring
  have IR : ∫ t in (1 / 2 : ℝ)..1, 4 * Real.log t ^ 2 = 4 - 4 * l2 - 2 * l2 ^ 2 := by
    rw [ftc (fun t => 4 * (t * Real.log t ^ 2 - 2 * (t * Real.log t) + 2 * t)) _ (1 / 2) 1
        (by norm_num) (by norm_num) (fun x hx => ((hasDerivAt_B x hx).const_mul 4)) cR]
    simp only [lh, Real.log_one]
    ring
  rw [IL] at NL
  rw [IR] at NR
  refine (norm_add_le _ _).trans ?_
  linarith

/-- **`|ĥ(u)|(2πu)² ≤ 96 log 2`** (the total variation of `h'`, exactly). -/
theorem hHat_ibp (u : ℝ) : ‖gHat (gl 1) u‖ * (2 * Real.pi * u) ^ 2 ≤ 96 * Real.log 2 := by
  set l2 := Real.log 2 with hl2
  have hl2p : 0 < l2 := Real.log_pos (by norm_num)
  have pos : ∀ x ∈ Icc (1 / 4 : ℝ) 1, 0 < x := fun x hx => by linarith [hx.1]
  set L := Real.log 1 with hL
  have hL0 : L = 0 := Real.log_one
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
        (continuousOn_const.mul (Real.continuousOn_log.mono fun x hx => ?_))))
        (continuousOn_pow 2) fun x hx => ?_
      · exact (pos x ⟨hx.1, by linarith [hx.2]⟩).ne'
      · exact pow_ne_zero 2 (pos x ⟨hx.1, by linarith [hx.2]⟩).ne')
  have IR := ibp2 (fun t => (L + Real.log t) * (-4 * Real.log t))
    (fun t => -4 * (L + 2 * Real.log t) / t)
    (fun t => 4 * (L + 2 * Real.log t - 2) / t ^ 2) (1 / 2) 1 u (by norm_num)
    (fun t ht => by
      have h0 : t ≠ 0 := (pos t ⟨by linarith [ht.1], ht.2⟩).ne'
      have := ((Real.hasDerivAt_log h0).const_add L).mul
        ((Real.hasDerivAt_log h0).const_mul (-4))
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
  have hid : (((2 * Real.pi * u) ^ 2 : ℝ) : ℂ) * gHat (gl 1) u =
      (((16 * L - 16 * l2 : ℝ) : ℂ) * eE u (1 / 2) - ((16 * (L - 2 * l2) : ℝ) : ℂ) * eE u (1 / 4) +
        ((-4 * L : ℝ) : ℂ) * eE u 1) -
      (∫ t in (1 / 4 : ℝ)..(1 / 2), ((4 * (2 - 2 * l2 - L - 2 * Real.log t) / t ^ 2 : ℝ) : ℂ) *
        eE u t) -
      ∫ t in (1 / 2 : ℝ)..1, ((4 * (L + 2 * Real.log t - 2) / t ^ 2 : ℝ) : ℂ) * eE u t := by
    rw [gl_hat_split 1 one_pos u, mul_add, IL, IR]
    simp only [lq, lh, Real.log_one]
    rw [hL0]
    push_cast
    ring
  have hn := congrArg norm hid
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hn
  rw [mul_comm, hn]
  rw [hL0]
  -- the two `φ''` integrals, exactly
  have cL : ContinuousOn (fun t : ℝ => 4 * (2 - 2 * l2 - 0 - 2 * Real.log t) / t ^ 2)
      (Icc (1 / 4) (1 / 2)) := by
    refine ContinuousOn.div (continuousOn_const.mul (continuousOn_const.sub
      (continuousOn_const.mul (Real.continuousOn_log.mono fun x hx => ?_))))
      (continuousOn_pow 2) fun x hx => ?_
    · exact (pos x ⟨hx.1, by linarith [hx.2]⟩).ne'
    · exact pow_ne_zero 2 (pos x ⟨hx.1, by linarith [hx.2]⟩).ne'
  have cR' : ContinuousOn (fun t : ℝ => 4 * (2 - 2 * Real.log t) / t ^ 2) (Icc (1 / 2) 1) := by
    refine ContinuousOn.div (continuousOn_const.mul (continuousOn_const.sub
      (continuousOn_const.mul (Real.continuousOn_log.mono fun x hx => ?_))))
      (continuousOn_pow 2) fun x hx => ?_
    · exact (pos x ⟨by linarith [hx.1], hx.2⟩).ne'
    · exact pow_ne_zero 2 (pos x ⟨by linarith [hx.1], hx.2⟩).ne'
  have dG : ∀ c : ℝ, ∀ x, 0 < x →
      HasDerivAt (fun t => 4 * ((c + 2 * Real.log t) / t)) (4 * (2 - c - 2 * Real.log x) / x ^ 2)
        x := by
    intro c x hx
    have := ((((Real.hasDerivAt_log hx.ne').const_mul 2).const_add c).div (hasDerivAt_id' x)
      hx.ne').const_mul 4
    refine this.congr_deriv ?_
    field_simp
    ring
  have NL : ‖∫ t in (1 / 4 : ℝ)..(1 / 2),
      ((4 * (2 - 2 * l2 - 0 - 2 * Real.log t) / t ^ 2 : ℝ) : ℂ) * eE u t‖ ≤ 32 * l2 := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans (le_of_eq ?_)
    rw [intervalIntegral.integral_congr
      (g := fun t => 4 * (2 - 2 * l2 - 0 - 2 * Real.log t) / t ^ 2) fun t ht => ?_]
    · rw [ftc _ _ (1 / 4) (1 / 2) (by norm_num) (by norm_num)
        (fun x hx => (dG (2 * l2) x hx).congr_deriv (by ring)) cL]
      simp only [lq, lh]
      ring
    · rw [uIcc_of_le (by norm_num)] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      have h1 : Real.log t ≤ -l2 := by
        have := Real.log_le_log ht0 ht.2; rwa [lh] at this
      rw [norm_mul, MPTS.norm_eE, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (by nlinarith) (by positivity))]
  have NR : ‖∫ t in (1 / 2 : ℝ)..1, ((4 * (0 + 2 * Real.log t - 2) / t ^ 2 : ℝ) : ℂ) * eE u t‖ ≤
      16 * l2 := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans (le_of_eq ?_)
    rw [intervalIntegral.integral_congr (g := fun t => 4 * (2 - 2 * Real.log t) / t ^ 2)
      fun t ht => ?_]
    · rw [ftc _ _ (1 / 2) 1 (by norm_num) (by norm_num)
        (fun x hx => (dG 0 x hx).congr_deriv (by ring)) cR']
      simp only [lh, Real.log_one]
      ring
    · rw [uIcc_of_le (by norm_num)] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      have h1 : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht.2
      rw [norm_mul, MPTS.norm_eE, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div,
        abs_of_pos (by positivity : (0 : ℝ) < t ^ 2), abs_of_nonpos (by nlinarith)]
      ring
  have e1 : ‖((16 * 0 - 16 * l2 : ℝ) : ℂ) * eE u (1 / 2)‖ = 16 * l2 := by
    rw [norm_mul, MPTS.norm_eE, mul_one, Complex.norm_real, Real.norm_eq_abs,
      show (16 : ℝ) * 0 - 16 * l2 = -(16 * l2) by ring, abs_neg, abs_of_pos (by positivity)]
  have e2 : ‖((16 * (0 - 2 * l2) : ℝ) : ℂ) * eE u (1 / 4)‖ = 32 * l2 := by
    rw [norm_mul, MPTS.norm_eE, mul_one, Complex.norm_real, Real.norm_eq_abs,
      show (16 : ℝ) * (0 - 2 * l2) = -(32 * l2) by ring, abs_neg, abs_of_pos (by positivity)]
  have e3 : ‖((-4 * 0 : ℝ) : ℂ) * eE u 1‖ = 0 := by simp
  calc _ ≤ ‖((16 * 0 - 16 * l2 : ℝ) : ℂ) * eE u (1 / 2) -
          ((16 * (0 - 2 * l2) : ℝ) : ℂ) * eE u (1 / 4) + ((-4 * 0 : ℝ) : ℂ) * eE u 1‖ +
        ‖∫ t in (1 / 4 : ℝ)..(1 / 2), ((4 * (2 - 2 * l2 - 0 - 2 * Real.log t) / t ^ 2 : ℝ) : ℂ) *
          eE u t‖ +
        ‖∫ t in (1 / 2 : ℝ)..1, ((4 * (0 + 2 * Real.log t - 2) / t ^ 2 : ℝ) : ℂ) * eE u t‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (16 * l2 + 32 * l2 + 0) + 32 * l2 + 16 * l2 := by
        refine add_le_add (add_le_add ?_ NL) NR
        refine (norm_add_le _ _).trans ((add_le_add (norm_sub_le _ _) le_rfl).trans (le_of_eq ?_))
        rw [e1, e2, e3]
    _ = 96 * l2 := by ring

/-- **`|ĥ(−δ/2)| ≤ min(2 − log 4, 96 log 2/(π²δ²))`**, in `mainI1`'s `capM` form. -/
theorem hHat_capM (δ : ℝ) :
    ‖gHat (gl 1) (-δ / 2)‖ ≤
      (2 - Real.log 4) * MT.capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ := by
  have hpi := Real.pi_pos
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h4 : 0 < 2 - Real.log 4 := by rw [hL]; linarith
  have hc : 0 < 96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4) := by positivity
  unfold MT.capM
  rcases le_total (δ ^ 2) (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) with h | h
  · rw [max_eq_left h, div_self hc.ne', mul_one]
    exact hHat_le _
  · rw [max_eq_right h]
    have hd : 0 < δ ^ 2 := lt_of_lt_of_le hc h
    have := hHat_ibp (-δ / 2)
    rw [show (2 * Real.pi * (-δ / 2)) ^ 2 = Real.pi ^ 2 * δ ^ 2 by ring] at this
    rw [show (2 - Real.log 4) * (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4) / δ ^ 2) =
      96 * Real.log 2 / (Real.pi ^ 2 * δ ^ 2) by field_simp, le_div_iff₀ (by positivity)]
    linarith

/-- **Per-`d` main term of `T^{log}`, PROVED** (given `EtaHatLBound`): for `d ≤ x/4` and
`j₀/2 − dβ = −y/2`, `|y| ≤ 1/2`:
`|T^{log}_{d,∘}(β) − (x/2d)(−1)^{j₀}ĝ_{x/d}((x/d)(−y/2))| ≤ (c₀ log(x/d)·d/2π²x)(π² − 4)`. -/
theorem tlo_main (hL : EtaHatLBound) (x β : ℝ) (hx : 0 < x) (d : ℕ) (hd : 1 ≤ d)
    (hdx : (d : ℝ) ≤ x / 4) (j0 : ℤ) (y : ℝ) (hy : |y| ≤ 1 / 2)
    (hj0 : (j0 : ℝ) / 2 - d * β = -y / 2) :
    ‖tlo x β d - ((x / d / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ j0 * etaHatL (x / d) (x / d * (-y / 2))‖ ≤
      c0 * Real.log (x / d) * d / (2 * Real.pi ^ 2 * x) * (Real.pi ^ 2 - 4) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hρ : 0 < x / d := by positivity
  have hρ4 : 4 ≤ x / d := by rw [le_div_iff₀ hdR]; linarith
  have hlog : 0 ≤ Real.log (x / d) := Real.log_nonneg (by linarith)
  have hpi := Real.pi_pos
  have hc0 : (0 : ℝ) ≤ c0 := by unfold c0; norm_num
  have P := poissonOddLog_holds x β hx d hd
  have U := P.update j0 0
  obtain ⟨S, hS, hSle⟩ := MPBM.off_sum (c0 * Real.log (x / d) * d / (2 * Real.pi ^ 2 * x)) y
    (by positivity) hy j0
  have hle := U.norm_le_of_bounded hS fun j => by
    by_cases h : j = j0
    · rw [h, Function.update_self, norm_zero, if_pos rfl]
    · rw [Function.update_of_ne h, if_neg h]
      set k : ℝ := ((j - j0 : ℤ) : ℝ) with hk
      have hk1 : 1 ≤ |k| := by
        rw [hk]
        have : (j - j0 : ℤ) ≠ 0 := sub_ne_zero.mpr h
        have h1 : (1 : ℤ) ≤ |j - j0| := Int.one_le_abs this
        exact_mod_cast h1
      have hky : k - y ≠ 0 := by
        intro h0
        have : |k| = |y| := by rw [sub_eq_zero.mp h0]
        linarith
      have harg : (j : ℝ) / 2 - d * β = (k - y) / 2 := by
        rw [hk]
        push_cast
        linarith
      rw [harg]
      set u := x / d * ((k - y) / 2) with hu
      have hu2 : (2 * Real.pi * u) ^ 2 = Real.pi ^ 2 * (x / d) ^ 2 * (k - y) ^ 2 := by
        rw [hu]; ring
      have hpos : 0 < (2 * Real.pi * u) ^ 2 := by
        rw [hu2]
        have : 0 < (k - y) ^ 2 := by positivity
        positivity
      have hH : ‖etaHatL (x / d) u‖ ≤ c0 * Real.log (x / d) / (2 * Real.pi * u) ^ 2 := by
        rw [le_div_iff₀ hpos]; exact hL (x / d) hρ4 u
      rw [norm_mul, norm_mul, norm_neg_one_zpow, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      calc x / d / 2 * ‖etaHatL (x / d) u‖
          ≤ x / d / 2 * (c0 * Real.log (x / d) / (2 * Real.pi * u) ^ 2) :=
            mul_le_mul_of_nonneg_left hH (by positivity)
        _ = c0 * Real.log (x / d) * d / (2 * Real.pi ^ 2 * x) * (1 / (k - y) ^ 2) := by
            rw [hu2]
            field_simp
  rw [hj0] at hle
  have e : (0 : ℂ) - ((x / d / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ j0 * etaHatL (x / d) (x / d * (-y / 2)) +
      tlo x β d = tlo x β d -
        ((x / d / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ j0 * etaHatL (x / d) (x / d * (-y / 2)) := by
    ring
  rw [e] at hle
  linarith

end Principia.Common.TernaryGoldbach.MPTH
