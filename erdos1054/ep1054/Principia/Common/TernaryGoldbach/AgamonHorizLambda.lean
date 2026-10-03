/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.AgamonHorizPick
import Principia.Common.TernaryGoldbach.AgamonHorizGamma
import Principia.Common.PNT.Medium.ZetaBounds

set_option autoImplicit false

/-!
# `EF.Horizontal` (EF5), part 3: `LFactor χ` for every primitive `χ` (`allFactor_holds`)

* **`q ≠ 1`** (`lfactor_completed`): `F = Λ(·, χ)` (Mathlib `completedLFunction`, entire since
  `χ ≠ 1`), `L = Λ/Γ_ℝ(· + a)` (`a = 0` even, `1` odd), `E = Γ'_ℝ/Γ_ℝ(· + a)`.
  Growth `|Λ(s)| ≤ K(|t| + 2)` on `−40 ≤ σ ≤ 40` (`completed_growth`): for `σ ≥ 1/2`,
  `|Λ| = |L|·|Γ_ℝ| ≤ N(2 + |s|/σ)·B` (SW `LFunction_strip_bound`, `gammaR_upper`); for
  `σ < 1/2`, the functional equation `Λ(s, χ) = N^{1/2−s} ε(χ) Λ(1 − s, χ̄)` (Mathlib
  `IsPrimitive.completedLFunction_one_sub`; `|ε|` is just a constant here).
  Anchor at `σ₀ = 3 − a`: `|L(σ₀ + it)| ≥ (σ₀ − 1)/σ₀ ≥ 1/2` (SW `LFunction_anchor_quantitative`)
  and `|Γ_ℝ(3 + it)| ≥ e^{−π|t|/2}/(2π)` (`gammaR_three`).
* **`q = 1`** (`lfactor_xi`): `F = ξ(s) = s(s − 1)Λ₀(s) + 1 = s(s − 1)Λ(s)` (entire),
  `ξ(1 − s) = ξ(s)`, `ζ = ξ/(s(s − 1)Γ_ℝ)`, `E = 1/s + 1/(s − 1) + Γ'_ℝ/Γ_ℝ`.
  Growth `|ξ| ≤ K(|t| + 2)³` from `|ζ(s)| ≤ 5/2 + |s|/σ` on `σ > 0` (`zeta_bound`: PNT+
  `Zeta0EqZeta` at `N = 1` and `ZetaBnd_aux1b`, ported in `Common/PNT/Medium/ZetaBounds`),
  anchor at `σ₀ = 3`.
-/

namespace Principia.Common.TernaryGoldbach.AH

open Complex Metric

/-! ## Elementary helpers -/

/-- `A·u ≤ e^{(A+1)u}` for `A ≥ 0`, `u ≥ 1`. -/
theorem mul_le_exp {A u : ℝ} (hA : 0 ≤ A) (hu : 1 ≤ u) : A * u ≤ Real.exp ((A + 1) * u) := by
  have h1 : A ≤ Real.exp A := by linarith [Real.add_one_le_exp A]
  have h2 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  calc A * u ≤ Real.exp A * Real.exp u := mul_le_mul h1 h2 (by linarith) (Real.exp_pos _).le
    _ = Real.exp (A + u) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((A + 1) * u) := Real.exp_le_exp.mpr (by nlinarith)

/-- `A·u³ ≤ e^{(6A+1)u}` for `A ≥ 0`, `u ≥ 1`. -/
theorem mul_cube_le_exp {A u : ℝ} (hA : 0 ≤ A) (hu : 1 ≤ u) :
    A * u ^ 3 ≤ Real.exp ((6 * A + 1) * u) := by
  have h3 : u ^ 3 / 6 ≤ Real.exp u := by
    have h := Real.pow_div_factorial_le_exp u (by linarith) 3
    norm_num [Nat.factorial] at h
    linarith
  have h1 : 6 * A ≤ Real.exp (6 * A) := by linarith [Real.add_one_le_exp (6 * A)]
  calc A * u ^ 3 = 6 * A * (u ^ 3 / 6) := by ring
    _ ≤ Real.exp (6 * A) * Real.exp u := mul_le_mul h1 h3 (by positivity) (Real.exp_pos _).le
    _ = Real.exp (6 * A + u) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((6 * A + 1) * u) := Real.exp_le_exp.mpr (by nlinarith)

/-- `e^{−C(|t|+2)} ≤ e^{−π|t|/2}/(4π)` for `C ≥ 3` (`e⁶ ≥ 36 > 4π`). -/
theorem exp_le_anchor {C : ℝ} (hC : 3 ≤ C) (t : ℝ) :
    Real.exp (-(C * (|t| + 2))) ≤ Real.exp (-(Real.pi * |t| / 2)) / (4 * Real.pi) := by
  have hpi := Real.pi_pos
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have h6 : 36 ≤ Real.exp 6 := by
    have h := Real.pow_div_factorial_le_exp 6 (by norm_num) 3
    norm_num [Nat.factorial] at h
    linarith
  have hle : Real.exp (-(C * (|t| + 2))) ≤ Real.exp (-(Real.pi * |t| / 2) - 6) := by
    apply Real.exp_le_exp.mpr
    have h1 : Real.pi * |t| ≤ 4 * |t| := mul_le_mul_of_nonneg_right hpi4.le (abs_nonneg t)
    have h2 : 0 ≤ (C - 3) * (|t| + 2) := mul_nonneg (by linarith) (by positivity)
    nlinarith [abs_nonneg t]
  rw [Real.exp_sub] at hle
  have hE := Real.exp_pos (-(Real.pi * |t| / 2))
  rw [le_div_iff₀ (by positivity)]
  calc Real.exp (-(C * (|t| + 2))) * (4 * Real.pi)
      ≤ Real.exp (-(Real.pi * |t| / 2)) / Real.exp 6 * (4 * Real.pi) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
    _ ≤ Real.exp (-(Real.pi * |t| / 2)) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (Real.exp_pos 6)]
        nlinarith

/-- **`|Γ_ℝ(3 + it)| ≥ e^{−π|t|/2}/(2π)`** (`Γ_ℝ(s + 2) = Γ_ℝ(s)s/(2π)` at `s = 1 + it`). -/
theorem gammaR_three (t : ℝ) :
    Real.exp (-(Real.pi * |t| / 2)) / (2 * Real.pi) ≤ ‖Gammaℝ (3 + t * I)‖ := by
  have hre : ((1 : ℂ) + t * I).re = 1 := by simp
  have hs0 : (1 : ℂ) + t * I ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hre
    norm_num at hre
  have h := Gammaℝ_add_two hs0
  rw [show (1 : ℂ) + t * I + 2 = 3 + t * I by ring] at h
  rw [h, norm_div, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_ofNat, div_div]
  have h1 : 1 ≤ ‖(1 : ℂ) + t * I‖ := by
    have := Complex.abs_re_le_norm ((1 : ℂ) + t * I)
    rwa [hre, abs_one] at this
  have h2 := gammaR_anchor t
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [norm_nonneg (Gammaℝ (1 + t * I))]

/-- `logDeriv` only depends on the germ. -/
theorem logDeriv_congr_nhds {f g : ℂ → ℂ} {x : ℂ} (h : f =ᶠ[nhds x] g) :
    logDeriv f x = logDeriv g x := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

/-! ## `q ≠ 1`: the completed `L`-function -/

section Completed

variable {N : ℕ} [NeZero N]

open Classical in
/-- The parity shift `a ∈ {0, 1}`: `gammaFactor χ s = Γ_ℝ(s + a)`. -/
noncomputable def aSh (χ : DirichletCharacter ℂ N) : ℝ := if χ.Even then 0 else 1

omit [NeZero N] in
theorem aSh_nonneg (χ : DirichletCharacter ℂ N) : 0 ≤ aSh χ := by
  unfold aSh
  split_ifs <;> norm_num

omit [NeZero N] in
theorem aSh_le_one (χ : DirichletCharacter ℂ N) : aSh χ ≤ 1 := by
  unfold aSh
  split_ifs <;> norm_num

omit [NeZero N] in
theorem gammaFactor_eq (χ : DirichletCharacter ℂ N) (s : ℂ) :
    DirichletCharacter.gammaFactor χ s = Gammaℝ (s + aSh χ) := by
  unfold aSh
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def, if_pos h]
    simp
  · rw [h.gammaFactor_def, if_neg h.not_even]
    simp

omit [NeZero N] in
theorem gF_ne_zero_re (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rw [gammaFactor_eq]
  apply Gammaℝ_ne_zero_of_re_pos
  simp only [Complex.add_re, Complex.ofReal_re]
  linarith [aSh_nonneg χ]

omit [NeZero N] in
theorem gF_ne_zero_im (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s.im ≠ 0) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rw [gammaFactor_eq]
  exact gammaR_ne_zero (by simpa using hs)

omit [NeZero N] in
theorem gF_differentiableAt (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s.im ≠ 0) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
  have hfun : DirichletCharacter.gammaFactor χ = fun z => Gammaℝ (z + aSh χ) :=
    funext (gammaFactor_eq χ)
  rw [hfun]
  exact (differentiableAt_gammaR (by simpa using hs)).comp s (differentiableAt_id.add_const _)

omit [NeZero N] in
theorem logDeriv_gammaFactor (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s.im ≠ 0) :
    logDeriv (DirichletCharacter.gammaFactor χ) s = logDeriv Gammaℝ (s + aSh χ) := by
  have hfun : DirichletCharacter.gammaFactor χ = fun z => Gammaℝ (z + aSh χ) :=
    funext (gammaFactor_eq χ)
  rw [hfun]
  have h := logDeriv_comp (f := Gammaℝ) (g := fun z : ℂ => z + (aSh χ : ℂ)) (x := s)
    (differentiableAt_gammaR (by simpa using hs)) (differentiableAt_id.add_const _)
  have hd : deriv (fun z : ℂ => z + (aSh χ : ℂ)) s = 1 := by simp
  rw [hd, mul_one] at h
  exact h

/-- `Λ = L·Γ-factor` where the Γ-factor does not vanish. -/
theorem completed_eq_mul (hN : N ≠ 1) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hG : DirichletCharacter.gammaFactor ψ s ≠ 0) :
    DirichletCharacter.completedLFunction ψ s =
      DirichletCharacter.LFunction ψ s * DirichletCharacter.gammaFactor ψ s := by
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ s (Or.inr hN),
    div_mul_cancel₀ _ hG]

open Principia.Common.SW in
/-- **`|Λ(s, ψ)| ≤ B·N(84 + 2|t|)`** on `1/2 ≤ σ ≤ 41`, for any `ψ ≠ 1`. -/
theorem completed_bound_right (hN : N ≠ 1) (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1) {B : ℝ}
    (hB : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 42 → ‖Gammaℝ s‖ ≤ B) (s : ℂ)
    (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 41) :
    ‖DirichletCharacter.completedLFunction ψ s‖ ≤ B * (N * (84 + 2 * |s.im|)) := by
  have ha0 := aSh_nonneg ψ
  have ha1 := aSh_le_one ψ
  have hG : ‖DirichletCharacter.gammaFactor ψ s‖ ≤ B := by
    rw [gammaFactor_eq]
    apply hB <;> simp only [Complex.add_re, Complex.ofReal_re] <;> linarith
  have hG0 : DirichletCharacter.gammaFactor ψ s ≠ 0 :=
    gF_ne_zero_re ψ (by linarith)
  rw [completed_eq_mul hN ψ s hG0, norm_mul]
  have hL := LFunction_strip_bound N ψ hψ s (by linarith)
  have hsn : ‖s‖ ≤ 41 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [abs_of_pos (by linarith : 0 < s.re)]
    linarith
  have hdiv : ‖s‖ / s.re ≤ 2 * ‖s‖ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg s]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hLb : ‖DirichletCharacter.LFunction ψ s‖ ≤ N * (84 + 2 * |s.im|) :=
    hL.trans (mul_le_mul_of_nonneg_left (by linarith) hN0)
  calc ‖DirichletCharacter.LFunction ψ s‖ * ‖DirichletCharacter.gammaFactor ψ s‖
      ≤ (N * (84 + 2 * |s.im|)) * B :=
        mul_le_mul hLb hG (norm_nonneg _) (by positivity)
    _ = B * (N * (84 + 2 * |s.im|)) := by ring

/-- A primitive character modulo `N ≠ 1` is nontrivial. -/
theorem ne_one_of_primitive (hN : N ≠ 1) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    χ ≠ 1 := by
  intro h
  apply hN
  rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hχ
  exact hχ.symm

/-- **Growth of `Λ(·, χ)`**: `|Λ(s)| ≤ K(|t| + 2)` on `−40 ≤ σ ≤ 40` (functional equation on the
left). -/
theorem completed_growth (hN : N ≠ 1) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, -40 ≤ s.re → s.re ≤ 40 →
      ‖DirichletCharacter.completedLFunction χ s‖ ≤ K * (|s.im| + 2) := by
  have hχ1 := ne_one_of_primitive hN hχ
  have hχi : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ1
  obtain ⟨B, hB0, hB⟩ := gammaR_upper (1 / 2) 42 (by norm_num)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  set ε : ℝ := ‖χ.rootNumber‖ with hε
  have hε0 : 0 ≤ ε := norm_nonneg _
  have hP0 : 0 ≤ (N : ℝ) ^ (41 : ℝ) := Real.rpow_nonneg hN0 _
  refine ⟨42 * B * N * (1 + (N : ℝ) ^ (41 : ℝ) * ε), by positivity, fun s h1 h2 => ?_⟩
  have habs : 0 ≤ |s.im| := abs_nonneg _
  have hBN : 0 ≤ B * N := mul_nonneg hB0 hN0
  have hbase : B * (N * (84 + 2 * |s.im|)) ≤ 42 * B * N * (|s.im| + 2) := by nlinarith
  rcases le_or_gt (1 / 2) s.re with hs | hs
  · refine (completed_bound_right hN χ hχ1 hB s hs (by linarith)).trans (hbase.trans ?_)
    have h3 : 0 ≤ 42 * B * N * (|s.im| + 2) * ((N : ℝ) ^ (41 : ℝ) * ε) := by positivity
    nlinarith
  · have hfe := hχ.completedLFunction_one_sub (1 - s)
    rw [sub_sub_cancel] at hfe
    rw [hfe, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (NeZero.pos N)]
    have hre : ((1 - s) - 1 / 2 : ℂ).re = 1 / 2 - s.re := by
      simp only [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re]
      ring
    rw [hre]
    have hNpow : (N : ℝ) ^ (1 / 2 - s.re) ≤ (N : ℝ) ^ (41 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hb := completed_bound_right hN χ⁻¹ hχi hB (1 - s)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    have him : |(1 - s).im| = |s.im| := by
      simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
    rw [him] at hb
    have hΛ0 := norm_nonneg (DirichletCharacter.completedLFunction χ⁻¹ (1 - s))
    have hpow0 : 0 ≤ (N : ℝ) ^ (1 / 2 - s.re) := Real.rpow_nonneg hN0 _
    calc (N : ℝ) ^ (1 / 2 - s.re) * ε * ‖DirichletCharacter.completedLFunction χ⁻¹ (1 - s)‖
        ≤ (N : ℝ) ^ (41 : ℝ) * ε * (42 * B * N * (|s.im| + 2)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hNpow hε0) (hb.trans hbase) hΛ0
          positivity
      _ ≤ 42 * B * N * (1 + (N : ℝ) ^ (41 : ℝ) * ε) * (|s.im| + 2) := by
          have h3 : 0 ≤ 42 * B * N * (|s.im| + 2) := by positivity
          nlinarith

open Principia.Common.SW in
/-- **The anchor of `Λ(·, χ)`** at `σ₀ = 3 − a`: `|Λ(σ₀ + it)| ≥ e^{−π|t|/2}/(4π)`. -/
theorem completed_anchor (hN : N ≠ 1) (χ : DirichletCharacter ℂ N) (t : ℝ) :
    Real.exp (-(Real.pi * |t| / 2)) / (4 * Real.pi) ≤
      ‖DirichletCharacter.completedLFunction χ (((3 - aSh χ : ℝ) : ℂ) + t * I)‖ := by
  set s : ℂ := ((3 - aSh χ : ℝ) : ℂ) + t * I with hs
  have ha0 := aSh_nonneg χ
  have ha1 := aSh_le_one χ
  have hsre : s.re = 3 - aSh χ := by simp [hs]
  have hG0 : DirichletCharacter.gammaFactor χ s ≠ 0 :=
    gF_ne_zero_re χ (by rw [hsre]; linarith)
  rw [completed_eq_mul hN χ s hG0, norm_mul, gammaFactor_eq]
  have hsa : s + (aSh χ : ℂ) = 3 + t * I := by
    rw [hs]
    push_cast
    ring
  rw [hsa]
  have hL := LFunction_anchor_quantitative N χ s (by rw [hsre]; linarith)
  rw [hsre] at hL
  have hL2 : 1 / 2 ≤ ‖DirichletCharacter.LFunction χ s‖ := by
    refine le_trans ?_ hL
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hΓ := gammaR_three t
  have hE : 0 ≤ Real.exp (-(Real.pi * |t| / 2)) / (2 * Real.pi) := by positivity
  calc Real.exp (-(Real.pi * |t| / 2)) / (4 * Real.pi)
      = 1 / 2 * (Real.exp (-(Real.pi * |t| / 2)) / (2 * Real.pi)) := by ring
    _ ≤ ‖DirichletCharacter.LFunction χ s‖ * ‖Gammaℝ (3 + t * I)‖ :=
        mul_le_mul hL2 hΓ hE (norm_nonneg _)

/-- **`LFactor χ` for primitive `χ` modulo `N ≠ 1`.** -/
theorem lfactor_completed (hN : N ≠ 1) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    LFactor χ := by
  have hχ1 := ne_one_of_primitive hN hχ
  obtain ⟨K, hK0, hK⟩ := completed_growth hN hχ
  obtain ⟨CΓ, hCΓ0, hCΓ⟩ := gammaR_logDeriv
  have ha0 := aSh_nonneg χ
  have ha1 := aSh_le_one χ
  set C : ℝ := K + 1 + CΓ + 3 with hC
  refine ⟨DirichletCharacter.completedLFunction χ,
    fun s => logDeriv (DirichletCharacter.gammaFactor χ) s, 3 - aSh χ, C, 10,
    DirichletCharacter.differentiable_completedLFunction hχ1, by linarith, by linarith,
    by positivity, by norm_num, ?_, ?_, ?_, ?_⟩
  · -- growth
    intro s h1 h2 _
    refine (hK s h1 h2).trans ((mul_le_exp hK0 (by linarith [abs_nonneg s.im])).trans ?_)
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (by linarith) (by linarith [abs_nonneg s.im]))
  · -- anchor
    intro t _
    exact (exp_le_anchor (by linarith) t).trans (completed_anchor hN χ t)
  · -- the split `L'/L = Λ'/Λ − Γ'/Γ` and the bound on `Γ'/Γ`
    intro s h1 h2 him hF
    have himne : s.im ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at him
      norm_num at him
    refine ⟨?_, ?_⟩
    · have hfun : DirichletCharacter.LFunction χ = fun z =>
          DirichletCharacter.completedLFunction χ z / DirichletCharacter.gammaFactor χ z :=
        funext fun z => DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inr hN)
      rw [hfun]
      exact logDeriv_div s hF (gF_ne_zero_im χ himne)
        ((DirichletCharacter.differentiable_completedLFunction hχ1) s)
        (gF_differentiableAt χ himne)
    · simp only
      rw [logDeriv_gammaFactor χ himne]
      have hw := hCΓ (s + aSh χ) (by simp only [Complex.add_re, Complex.ofReal_re]; linarith)
        (by simp only [Complex.add_re, Complex.ofReal_re]; linarith)
        (by simpa using him)
      have him' : (s + (aSh χ : ℂ)).im = s.im := by simp
      rw [him'] at hw
      refine hw.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · -- zeros of `L` are zeros of `Λ`
    intro ρ hρ h0 _ _
    rw [completed_eq_mul hN χ ρ (gF_ne_zero_re χ h0), hρ, zero_mul]

end Completed

/-! ## `q = 1`: `ξ(s) = s(s − 1)Λ(s)` -/

section Xi

/-- **`ξ(s) = s(s − 1)Λ₀(s) + 1`**, entire, `= s(s − 1)Λ(s)` off `{0, 1}`. -/
noncomputable def xi (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1

theorem differentiable_xi : Differentiable ℂ xi := by
  unfold xi
  exact ((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1

theorem xi_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s - 1) * completedRiemannZeta s := by
  rw [xi, completedRiemannZeta_eq]
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1'' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp
  ring

theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  rw [xi, xi, completedRiemannZeta₀_one_sub]
  ring

theorem completed_eq_zeta_mul {s : ℂ} (h0 : s ≠ 0) (hG : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
  rw [riemannZeta_def_of_ne_zero h0, div_mul_cancel₀ _ hG]

theorem ne_zero_of_im {s : ℂ} (h : 1 ≤ |s.im|) : s ≠ 0 := by
  intro h0
  rw [h0, Complex.zero_im, abs_zero] at h
  norm_num at h

theorem ne_one_of_im {s : ℂ} (h : 1 ≤ |s.im|) : s ≠ 1 := by
  intro h0
  rw [h0, Complex.one_im, abs_zero] at h
  norm_num at h

/-- **`|ζ(s)| ≤ 5/2 + |s|/σ`** for `σ > 0`, `|t| ≥ 1` (PNT+ `Zeta0EqZeta` at `N = 1`:
`ζ(s) = 1 − 1/(1 − s) − 1/2 + s∫_1^∞ (⌊x⌋ + 1/2 − x)x^{−s−1}dx`, and `ZetaBnd_aux1b`). -/
theorem zeta_bound {s : ℂ} (hσ : 0 < s.re) (h1 : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 5 / 2 + ‖s‖ / s.re := by
  have hs0 := ne_zero_of_im h1
  have hs1 := ne_one_of_im h1
  have hI := ZetaBnd_aux1b 1 le_rfl (σ := s.re) (t := s.im) hσ
  rw [Complex.re_add_im] at hI
  set J : ℂ := ∫ x in Set.Ioi ((1 : ℕ) : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) with hJ
  have hz : riemannZeta s = 1 + (-1) / (1 - s) + (-1) / 2 + s * J := by
    rw [← Zeta0EqZeta (N := 1) one_pos hσ hs1, riemannZeta0, hJ]
    simp [Finset.sum_range_succ, zero_cpow hs0]
  rw [hz]
  have h1s : 1 ≤ ‖1 - s‖ := by
    have := Complex.abs_im_le_norm (1 - s)
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at this
    linarith
  have hq : ‖(-1 : ℂ) / (1 - s)‖ ≤ 1 := by
    rw [norm_div, norm_neg, norm_one, div_le_one (by linarith)]
    exact h1s
  have hJb : ‖J‖ ≤ 1 / s.re := by
    have := hI
    rw [Nat.cast_one, Real.one_rpow] at this
    exact this
  have hsJ : ‖s * J‖ ≤ ‖s‖ / s.re := by
    rw [norm_mul]
    calc ‖s‖ * ‖J‖ ≤ ‖s‖ * (1 / s.re) := mul_le_mul_of_nonneg_left hJb (norm_nonneg _)
      _ = ‖s‖ / s.re := by ring
  have h2 : ‖(-1 : ℂ) / 2‖ = 1 / 2 := by
    rw [norm_div, norm_neg, norm_one, Complex.norm_ofNat]
  calc ‖1 + (-1) / (1 - s) + (-1) / 2 + s * J‖
      ≤ ‖(1 : ℂ)‖ + ‖(-1 : ℂ) / (1 - s)‖ + ‖(-1 : ℂ) / 2‖ + ‖s * J‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_add_le _ _
    _ ≤ 5 / 2 + ‖s‖ / s.re := by rw [norm_one, h2]; linarith

/-- `|ξ(s)| ≤ 2783·B·(|t| + 2)³` on `1/2 ≤ σ ≤ 41`, `|t| ≥ 2`. -/
theorem xi_bound_right {B : ℝ}
    (hB : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 42 → ‖Gammaℝ s‖ ≤ B) (s : ℂ)
    (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 41) (him : 2 ≤ |s.im|) :
    ‖xi s‖ ≤ 2783 * B * (|s.im| + 2) ^ 3 := by
  have hs0 := ne_zero_of_im (by linarith : 1 ≤ |s.im|)
  have hs1 := ne_one_of_im (by linarith : 1 ≤ |s.im|)
  have hG0 : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [xi_eq hs0 hs1, completed_eq_zeta_mul hs0 hG0, norm_mul, norm_mul, norm_mul]
  have hsn : ‖s‖ ≤ 41 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [abs_of_pos (by linarith : 0 < s.re)]
    linarith
  have hs1n : ‖s - 1‖ ≤ 42 + |s.im| := by
    refine (norm_sub_le s 1).trans ?_
    rw [norm_one]
    linarith
  have hz := zeta_bound (s := s) (by linarith) (by linarith)
  have hdiv : ‖s‖ / s.re ≤ 2 * ‖s‖ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg s]
  have hzb : ‖riemannZeta s‖ ≤ 23 * (|s.im| + 2) := by linarith
  have hsb : ‖s‖ ≤ 11 * (|s.im| + 2) := by linarith
  have hs1b : ‖s - 1‖ ≤ 11 * (|s.im| + 2) := by linarith
  have hΓ := hB s h1 (by linarith)
  have hu : 0 ≤ |s.im| + 2 := by positivity
  calc ‖s‖ * ‖s - 1‖ * (‖riemannZeta s‖ * ‖Gammaℝ s‖)
      ≤ (11 * (|s.im| + 2)) * (11 * (|s.im| + 2)) * ((23 * (|s.im| + 2)) * B) := by
        apply mul_le_mul (mul_le_mul hsb hs1b (norm_nonneg _) (by positivity))
          (mul_le_mul hzb hΓ (norm_nonneg _) (by positivity))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = 2783 * B * (|s.im| + 2) ^ 3 := by ring

/-- **Growth of `ξ`**: `|ξ(s)| ≤ K(|t| + 2)³` on `−40 ≤ σ ≤ 40`, `|t| ≥ 2` (`ξ(1 − s) = ξ(s)` on
the left). -/
theorem xi_growth : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, -40 ≤ s.re → s.re ≤ 40 → 2 ≤ |s.im| →
    ‖xi s‖ ≤ K * (|s.im| + 2) ^ 3 := by
  obtain ⟨B, hB0, hB⟩ := gammaR_upper (1 / 2) 42 (by norm_num)
  refine ⟨2783 * B, by positivity, fun s h1 h2 him => ?_⟩
  rcases le_or_gt (1 / 2) s.re with hs | hs
  · exact xi_bound_right hB s hs (by linarith) him
  · rw [← xi_one_sub]
    have him' : |(1 - s).im| = |s.im| := by
      simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
    have h := xi_bound_right hB (1 - s)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith) (by rw [him']; exact him)
    rwa [him'] at h

open Principia.Common.SW in
/-- **The anchor of `ξ`** at `σ₀ = 3`: `|ξ(3 + it)| ≥ e^{−π|t|/2}/(4π)`. -/
theorem xi_anchor (t : ℝ) :
    Real.exp (-(Real.pi * |t| / 2)) / (4 * Real.pi) ≤ ‖xi (((3 : ℝ) : ℂ) + t * I)‖ := by
  set s : ℂ := ((3 : ℝ) : ℂ) + t * I with hs
  have hsre : s.re = 3 := by simp [hs]
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hsre
    norm_num at hsre
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hsre
    norm_num at hsre
  have hG0 : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num)
  rw [xi_eq hs0 hs1, completed_eq_zeta_mul hs0 hG0, norm_mul, norm_mul, norm_mul]
  have hn1 : 3 ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s
    rw [hsre] at this
    linarith [abs_of_pos (show (0 : ℝ) < 3 by norm_num)]
  have hn2 : 2 ≤ ‖s - 1‖ := by
    have := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, hsre, Complex.one_re] at this
    norm_num at this
    linarith
  have hζ : 2 / 3 ≤ ‖riemannZeta s‖ := by
    have h := LFunction_anchor_quantitative 1 (1 : DirichletCharacter ℂ 1) s
      (by rw [hsre]; norm_num)
    rw [DirichletCharacter.LFunction_modOne_eq, hsre] at h
    norm_num at h
    linarith
  have hsΓ : s = 3 + t * I := by rw [hs]; push_cast; ring
  have hΓ := gammaR_three t
  rw [← hsΓ] at hΓ
  have hE : 0 ≤ Real.exp (-(Real.pi * |t| / 2)) / (2 * Real.pi) := by positivity
  have hpi := Real.pi_pos
  calc Real.exp (-(Real.pi * |t| / 2)) / (4 * Real.pi)
      ≤ 3 * 2 * (2 / 3 * (Real.exp (-(Real.pi * |t| / 2)) / (2 * Real.pi))) := by
        rw [div_le_iff₀ (by positivity)]
        have hE' := Real.exp_pos (-(Real.pi * |t| / 2))
        field_simp
        nlinarith
    _ ≤ ‖s‖ * ‖s - 1‖ * (‖riemannZeta s‖ * ‖Gammaℝ s‖) := by
        apply mul_le_mul (mul_le_mul hn1 hn2 (by norm_num) (by positivity))
          (mul_le_mul hζ hΓ hE (by positivity)) (by positivity) (by positivity)

/-- `ζ = ξ/(s(s − 1)Γ_ℝ)` near every `s ∉ {0, 1}`. -/
theorem zeta_eventuallyEq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    riemannZeta =ᶠ[nhds s] fun z => xi z / (z * (z - 1) * Gammaℝ z) := by
  have hU : IsOpen {z : ℂ | z ≠ 0 ∧ z ≠ 1} := isOpen_ne.inter isOpen_ne
  filter_upwards [hU.mem_nhds ⟨h0, h1⟩] with z hz
  obtain ⟨hz0, hz1⟩ := hz
  have hzz : z * (z - 1) ≠ 0 := mul_ne_zero hz0 (sub_ne_zero.mpr hz1)
  have hΛ : completedRiemannZeta z = xi z / (z * (z - 1)) := by
    rw [xi_eq hz0 hz1, mul_div_cancel_left₀ _ hzz]
  rw [riemannZeta_def_of_ne_zero hz0, hΛ, div_div]

/-- **The split for `ζ`**: `ζ'/ζ = ξ'/ξ − (1/s + 1/(s − 1) + Γ'_ℝ/Γ_ℝ)` off the real axis. -/
theorem logDeriv_zeta_eq {s : ℂ} (him : 1 ≤ |s.im|) (hxi : xi s ≠ 0) :
    logDeriv riemannZeta s = logDeriv xi s - (1 / s + 1 / (s - 1) + logDeriv Gammaℝ s) := by
  have h0 := ne_zero_of_im him
  have h1 := ne_one_of_im him
  have himne : s.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at him
    norm_num at him
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hG0 : Gammaℝ s ≠ 0 := gammaR_ne_zero himne
  have hGd : DifferentiableAt ℂ Gammaℝ s := differentiableAt_gammaR himne
  have hpd : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1)) s := by fun_prop
  have hgd : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1) * Gammaℝ z) s := hpd.mul hGd
  have hgne : s * (s - 1) * Gammaℝ s ≠ 0 := mul_ne_zero (mul_ne_zero h0 hs1) hG0
  have e1 := logDeriv_congr_nhds (zeta_eventuallyEq h0 h1)
  have e2 := logDeriv_div (f := xi) (g := fun z : ℂ => z * (z - 1) * Gammaℝ z) s hxi hgne
    (differentiable_xi s) hgd
  have e3 := logDeriv_mul (f := fun z : ℂ => z * (z - 1)) (g := Gammaℝ) s (mul_ne_zero h0 hs1)
    hG0 hpd hGd
  have e4 := logDeriv_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1) s h0 hs1
    differentiableAt_id (differentiableAt_id.sub_const 1)
  have e5 := Principia.Common.SW.logDeriv_sub_const 1 s h1
  have hid : logDeriv (fun z : ℂ => z) s = 1 / s := by
    rw [logDeriv_apply, deriv_id'']
  rw [e1, e2, e3, e4, e5, hid]

/-- **`LFactor` for the character modulo `1`** (`F = ξ`, `σ₀ = 3`). -/
theorem lfactor_xi (χ : DirichletCharacter ℂ 1) : LFactor χ := by
  obtain ⟨K, hK0, hK⟩ := xi_growth
  obtain ⟨CΓ, hCΓ0, hCΓ⟩ := gammaR_logDeriv
  set C : ℝ := 6 * K + 1 + CΓ + 3 with hC
  rw [LFactor, DirichletCharacter.LFunction_modOne_eq]
  refine ⟨xi, fun s => 1 / s + 1 / (s - 1) + logDeriv Gammaℝ s, 3, C, 10,
    differentiable_xi, by norm_num, by norm_num, by positivity, by norm_num, ?_, ?_, ?_, ?_⟩
  · -- growth
    intro s h1 h2 him
    have hu : 1 ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
    refine (hK s h1 h2 (by linarith)).trans ((mul_cube_le_exp hK0 hu).trans ?_)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  · -- anchor
    intro t _
    exact (exp_le_anchor (by linarith) t).trans (xi_anchor t)
  · -- split and bound
    intro s h1 h2 him hF
    refine ⟨logDeriv_zeta_eq (by linarith) hF, ?_⟩
    have hsn : 10 ≤ ‖s‖ := him.trans (Complex.abs_im_le_norm s)
    have hs1n : 10 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
      linarith
    have hq1 : ‖1 / s‖ ≤ 1 := by
      rw [norm_div, norm_one, div_le_one (by linarith)]
      linarith
    have hq2 : ‖1 / (s - 1)‖ ≤ 1 := by
      rw [norm_div, norm_one, div_le_one (by linarith)]
      linarith
    have hΓ := hCΓ s h1 (by linarith) him
    calc ‖1 / s + 1 / (s - 1) + logDeriv Gammaℝ s‖
        ≤ ‖1 / s‖ + ‖1 / (s - 1)‖ + ‖logDeriv Gammaℝ s‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ C * (|s.im| + 2) := by
          have h3 : CΓ * (|s.im| + 2) ≤ (C - 1) * (|s.im| + 2) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          nlinarith [abs_nonneg s.im]
  · -- zeros of `ζ` are zeros of `ξ`
    intro ρ hρ h0 _ him
    have hρ0 := ne_zero_of_im (by linarith : 1 ≤ |ρ.im|)
    have hρ1 := ne_one_of_im (by linarith : 1 ≤ |ρ.im|)
    rw [xi_eq hρ0 hρ1, completed_eq_zeta_mul hρ0 (Gammaℝ_ne_zero_of_re_pos h0), hρ, zero_mul,
      mul_zero]

end Xi

/-- **`AllFactor` PROVED**: `q = 1` by `ξ`, `q ≠ 1` by the completed `L`-function. -/
theorem allFactor_holds : AllFactor := by
  intro q _ χ hχ
  rcases eq_or_ne q 1 with rfl | hq
  · exact lfactor_xi χ
  · exact lfactor_completed hq hχ

end Principia.Common.TernaryGoldbach.AH
