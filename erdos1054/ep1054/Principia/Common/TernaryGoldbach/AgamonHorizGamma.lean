/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.SW.ZeroFreeA

set_option autoImplicit false

/-!
# `EF.Horizontal` (EF5), part 2: crude bounds for `Γ_ℝ(s) = π^{−s/2} Γ(s/2)`

What the completed `L`-functions need from the archimedean factor, all crude (no Stirling):

* `norm_Gamma_le_Gamma_re`: `|Γ(w)| ≤ Γ(Re w)` for `Re w > 0` (the Euler integral).
* `norm_GammaR_eq`, `norm_GammaR_le`: `|Γ_ℝ(s)| = π^{−σ/2}|Γ(s/2)| ≤ Γ(σ/2)` for `σ > 0`, and
  `gammaR_upper`: `Γ_ℝ` is bounded on every strip `a ≤ Re s ≤ b`, `a > 0` (continuity of `Γ`).
* `gammaR_anchor`: `|Γ_ℝ(1 + iy)| ≥ e^{−π|y|/2}`, from the reflection formula
  `Γ_ℝ(1 − s)Γ_ℝ(1 + s) = 1/cos(πs/2)` (Mathlib `Gammaℝ_one_sub_mul_Gammaℝ_one_add`) at `s = iy`,
  `|Γ_ℝ(1 − iy)| ≤ π^{−1/2}Γ(1/2) = 1` and `cosh x ≤ e^{|x|}`.
* `gammaR_ball`: `|Γ_ℝ| ≤ B` on `−7 < Re s < 9`, `|Im s| ≥ 2` (four steps of
  `Γ_ℝ(s) = 2πΓ_ℝ(s + 2)/s`).
* `gammaR_logDeriv`: `|Γ'_ℝ/Γ_ℝ(w)| ≤ C(|Im w| + 2)` on `−1/2 ≤ Re w ≤ 5/2`, `|Im w| ≥ 10` — the SW
  brick `logDeriv_bound_of_ne_zero` (Borel–Carathéodory) on `B(1 + i Im w, 8)`, where `Γ_ℝ` has
  no zeros or poles, with the anchor and ball bounds above.
-/

namespace Principia.Common.TernaryGoldbach.AH

open Complex Metric

/-- **`|Γ(w)| ≤ Γ(Re w)`** for `Re w > 0`. -/
theorem norm_Gamma_le_Gamma_re {w : ℂ} (hw : 0 < w.re) :
    ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral hw, Real.Gamma_eq_integral hw, Complex.GammaIntegral]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx' : (0 : ℝ) < x := hx
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx', Complex.sub_re, Complex.one_re]

/-- `|π^{−s/2}| = π^{−σ/2}`. -/
theorem norm_pi_cpow (s : ℂ) : ‖(Real.pi : ℂ) ^ (-s / 2)‖ = Real.pi ^ (-s.re / 2) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 1
  simp

/-- **`|Γ_ℝ(s)| = π^{−σ/2}|Γ(s/2)|`.** -/
theorem norm_GammaR_eq (s : ℂ) :
    ‖Gammaℝ s‖ = Real.pi ^ (-s.re / 2) * ‖Complex.Gamma (s / 2)‖ := by
  rw [Gammaℝ_def, norm_mul, norm_pi_cpow]

/-- **`|Γ_ℝ(s)| ≤ π^{−σ/2}Γ(σ/2)`** for `σ > 0`. -/
theorem norm_GammaR_le_pi {s : ℂ} (hs : 0 < s.re) :
    ‖Gammaℝ s‖ ≤ Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2) := by
  rw [norm_GammaR_eq]
  have h2 : ‖Complex.Gamma (s / 2)‖ ≤ Real.Gamma (s.re / 2) := by
    have h := norm_Gamma_le_Gamma_re (w := s / 2) (by simp; linarith)
    simpa using h
  exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg Real.pi_pos.le _)

/-- **`|Γ_ℝ(s)| ≤ Γ(σ/2)`** for `σ > 0`. -/
theorem norm_GammaR_le {s : ℂ} (hs : 0 < s.re) : ‖Gammaℝ s‖ ≤ Real.Gamma (s.re / 2) := by
  refine (norm_GammaR_le_pi hs).trans ?_
  have h1 : Real.pi ^ (-s.re / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have h0 : 0 ≤ Real.Gamma (s.re / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
  nlinarith

/-- **`Γ_ℝ` is bounded on `a ≤ Re s ≤ b`**, `a > 0`. -/
theorem gammaR_upper (a b : ℝ) (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Gammaℝ s‖ ≤ B := by
  have hcont : ContinuousOn Real.Gamma (Set.Icc (a / 2) (b / 2)) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    refine (Real.differentiableAt_Gamma fun m hm => ?_).continuousAt.continuousWithinAt
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  obtain ⟨B, hB⟩ := (isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨max B 0, le_max_right _ _, fun s h1 h2 => ?_⟩
  refine (norm_GammaR_le (by linarith)).trans ?_
  have hmem : s.re / 2 ∈ Set.Icc (a / 2) (b / 2) := ⟨by linarith, by linarith⟩
  have := hB _ hmem
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

/-- `cosh x ≤ e^{|x|}`. -/
theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

/-- **`|Γ_ℝ(1 + iy)| ≥ e^{−π|y|/2}`** (reflection formula). -/
theorem gammaR_anchor (y : ℝ) : Real.exp (-(Real.pi * |y| / 2)) ≤ ‖Gammaℝ (1 + y * I)‖ := by
  have hrefl := Gammaℝ_one_sub_mul_Gammaℝ_one_add ((y : ℂ) * I)
  have hup : ‖Gammaℝ (1 - (y : ℂ) * I)‖ ≤ 1 := by
    have hre : (1 - (y : ℂ) * I).re = 1 := by simp
    have h := norm_GammaR_le_pi (s := 1 - (y : ℂ) * I) (by rw [hre]; norm_num)
    rw [hre, show (1 : ℝ) / 2 = 1 / 2 from rfl, Real.Gamma_one_half_eq] at h
    have hpi : Real.pi ^ (-1 / 2 : ℝ) * Real.sqrt Real.pi = 1 := by
      rw [Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num,
        Real.rpow_neg Real.pi_pos.le]
      exact inv_mul_cancel₀ (Real.rpow_pos_of_pos Real.pi_pos _).ne'
    linarith
  have hcos : ‖Complex.cos (Real.pi * ((y : ℂ) * I) / 2)‖ = Real.cosh (Real.pi * y / 2) := by
    have e1 : (Real.pi : ℂ) * ((y : ℂ) * I) / 2 = ((Real.pi * y / 2 : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [e1, Complex.cos_mul_I, ← Complex.ofReal_cosh, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.cosh_pos _)]
  have hprod : ‖Gammaℝ (1 - (y : ℂ) * I)‖ * ‖Gammaℝ (1 + (y : ℂ) * I)‖ =
      (Real.cosh (Real.pi * y / 2))⁻¹ := by
    rw [← norm_mul, hrefl, norm_inv, hcos]
  have hcosh := cosh_le_exp_abs (Real.pi * y / 2)
  have habs : |Real.pi * y / 2| = Real.pi * |y| / 2 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
  rw [habs] at hcosh
  have hinv : Real.exp (-(Real.pi * |y| / 2)) ≤ (Real.cosh (Real.pi * y / 2))⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.cosh_pos _) hcosh
  have h0 : 0 ≤ ‖Gammaℝ (1 + (y : ℂ) * I)‖ := norm_nonneg _
  have h1 : ‖Gammaℝ (1 - (y : ℂ) * I)‖ * ‖Gammaℝ (1 + (y : ℂ) * I)‖ ≤
      ‖Gammaℝ (1 + (y : ℂ) * I)‖ := by nlinarith [norm_nonneg (Gammaℝ (1 - (y : ℂ) * I))]
  linarith

/-- One step of the recursion: `|Γ_ℝ(s)| ≤ π|Γ_ℝ(s + 2)|` when `|Im s| ≥ 2`. -/
theorem gammaR_step {s : ℂ} (hs : 2 ≤ |s.im|) : ‖Gammaℝ s‖ ≤ Real.pi * ‖Gammaℝ (s + 2)‖ := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_im, abs_zero] at hs
    norm_num at hs
  have h := Gammaℝ_add_two hs0
  have hn : ‖Gammaℝ (s + 2)‖ = ‖Gammaℝ s‖ * ‖s‖ / 2 / Real.pi := by
    rw [h, norm_div, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_ofNat]
  have hsn : 2 ≤ ‖s‖ := hs.trans (Complex.abs_im_le_norm s)
  have hpi : 0 < Real.pi := Real.pi_pos
  have he : Real.pi * (‖Gammaℝ s‖ * ‖s‖ / 2 / Real.pi) = ‖Gammaℝ s‖ * ‖s‖ / 2 := by
    field_simp
  rw [hn, he]
  nlinarith [norm_nonneg (Gammaℝ s)]

/-- **`|Γ_ℝ| ≤ B` on `−7 < Re s < 9`, `|Im s| ≥ 2`** (four recursion steps, then `gammaR_upper` on
`1 ≤ Re ≤ 17`). -/
theorem gammaR_ball : ∃ B : ℝ, 1 ≤ B ∧ ∀ s : ℂ, -7 < s.re → s.re < 9 → 2 ≤ |s.im| →
    ‖Gammaℝ s‖ ≤ B := by
  obtain ⟨B₀, hB₀, hB⟩ := gammaR_upper 1 17 (by norm_num)
  refine ⟨max 1 (Real.pi ^ 4 * B₀), le_max_left _ _, fun s h1 h2 him => ?_⟩
  have him2 : ∀ k : ℂ, k.im = 0 → 2 ≤ |(s + k).im| := by
    intro k hk
    rw [Complex.add_im, hk, add_zero]
    exact him
  have e1 := gammaR_step him
  have e2 := gammaR_step (him2 2 (by simp))
  have e3 := gammaR_step (him2 (2 + 2) (by simp))
  have e4 := gammaR_step (him2 (2 + 2 + 2) (by simp))
  have hre : 1 ≤ (s + 2 + 2 + 2 + 2).re ∧ (s + 2 + 2 + 2 + 2).re ≤ 17 := by
    simp only [Complex.add_re, Complex.re_ofNat]
    constructor <;> linarith
  have e5 := hB _ hre.1 hre.2
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [show s + (2 + 2) = s + 2 + 2 by ring] at e3
  rw [show s + (2 + 2 + 2) = s + 2 + 2 + 2 by ring] at e4
  have : ‖Gammaℝ s‖ ≤ Real.pi ^ 4 * B₀ := by
    have f1 := mul_le_mul_of_nonneg_left e5 hpi.le
    have f2 := mul_le_mul_of_nonneg_left (e4.trans f1) hpi.le
    have f3 := mul_le_mul_of_nonneg_left (e3.trans f2) hpi.le
    have f4 := e1.trans (mul_le_mul_of_nonneg_left (e2.trans f3) hpi.le)
    calc ‖Gammaℝ s‖ ≤ _ := f4
      _ = Real.pi ^ 4 * B₀ := by ring
  exact this.trans (le_max_right _ _)

/-- `Γ_ℝ(z) ≠ 0` off the real axis. -/
theorem gammaR_ne_zero {z : ℂ} (hz : z.im ≠ 0) : Gammaℝ z ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff]
  rintro ⟨n, hn⟩
  apply hz
  rw [hn]
  simp

/-- `Γ_ℝ` is differentiable off the real axis (`1/Γ_ℝ` is entire). -/
theorem differentiableAt_gammaR {z : ℂ} (hz : z.im ≠ 0) : DifferentiableAt ℂ Gammaℝ z := by
  have h := (differentiable_Gammaℝ_inv z).inv (inv_ne_zero (gammaR_ne_zero hz))
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => (inv_inv _).symm)

open Principia.Common.SW in
/-- **`|Γ'_ℝ/Γ_ℝ(w)| ≤ C(|Im w| + 2)`** on `−1/2 ≤ Re w ≤ 5/2`, `|Im w| ≥ 10`. -/
theorem gammaR_logDeriv : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, -1 / 2 ≤ w.re → w.re ≤ 5 / 2 →
    10 ≤ |w.im| → ‖logDeriv Gammaℝ w‖ ≤ C * (|w.im| + 2) := by
  obtain ⟨B, hB1, hB⟩ := gammaR_ball
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  refine ⟨Real.log B + 4, by linarith, fun w h1 h2 him => ?_⟩
  set c : ℂ := 1 + (w.im : ℂ) * I with hc
  have hcre : c.re = 1 := by simp [hc]
  have hcim : c.im = w.im := by simp [hc]
  have hball : ∀ z ∈ ball c 8, -7 < z.re ∧ z.re < 9 ∧ 2 ≤ |z.im| := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hre := Complex.abs_re_le_norm (z - c)
    have him' := Complex.abs_im_le_norm (z - c)
    rw [Complex.sub_re, hcre] at hre
    rw [Complex.sub_im, hcim] at him'
    obtain ⟨r1, r2⟩ := abs_lt.mp (lt_of_le_of_lt hre hz)
    have hz1 := abs_sub_abs_le_abs_sub w.im z.im
    rw [abs_sub_comm] at hz1
    refine ⟨by linarith, by linarith, by linarith⟩
  have himne : ∀ z ∈ ball c 8, z.im ≠ 0 := by
    intro z hz h0
    have := (hball z hz).2.2
    rw [h0, abs_zero] at this
    norm_num at this
  have hdiff : DifferentiableOn ℂ Gammaℝ (ball c 8) := fun z hz =>
    (differentiableAt_gammaR (himne z hz)).differentiableWithinAt
  have hne : ∀ z ∈ ball c 8, Gammaℝ z ≠ 0 := fun z hz => gammaR_ne_zero (himne z hz)
  have hMb : ∀ z ∈ ball c 8, ‖Gammaℝ z‖ ≤ B := fun z hz =>
    hB z (hball z hz).1 (hball z hz).2.1 (hball z hz).2.2
  have hml : 0 < Real.exp (-(Real.pi * |w.im| / 2)) := Real.exp_pos _
  have hlow : Real.exp (-(Real.pi * |w.im| / 2)) ≤ ‖Gammaℝ c‖ := gammaR_anchor w.im
  have hw : w ∈ ball c (8 / 4) := by
    rw [mem_ball, dist_eq_norm]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    rw [Complex.sub_re, Complex.sub_im, hcre, hcim, sub_self, abs_zero, add_zero]
    have h3 : |w.re - 1| ≤ 3 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hb := logDeriv_bound_of_ne_zero Gammaℝ c 8 B _ (by norm_num) hdiff hne hMb hml hlow w hw
  rw [← logDeriv_apply] at hb
  have hlog : Real.log (B / Real.exp (-(Real.pi * |w.im| / 2))) =
      Real.log B + Real.pi * |w.im| / 2 := by
    rw [Real.log_div (by linarith) (Real.exp_pos _).ne', Real.log_exp]
    ring
  rw [hlog] at hb
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have habs : 0 ≤ |w.im| := abs_nonneg _
  have hfin : 8 * (Real.log B + Real.pi * |w.im| / 2 + 1) / 8 ≤
      (Real.log B + 4) * (|w.im| + 2) := by
    have hp : Real.pi * |w.im| ≤ 4 * |w.im| := mul_le_mul_of_nonneg_right hpi.le habs
    nlinarith
  linarith

end Principia.Common.TernaryGoldbach.AH
