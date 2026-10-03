/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.AgamonLeftLD

set_option autoImplicit false

/-!
# `AG.LDFE` PROVED: the functional equation in log-derivative form on `Re s = −1/2`

**`ldfe_holds : LDFE`**: for primitive `χ` mod `q` and `s = −1/2 + iτ`,
`L'/L(s, χ) = −log q + log 2π − ψ(1 − s) + (π/2)U(s) − L'/L(1 − s, χ̄)`.

Route. On the open strip `V = {−1 < Re s < 0}` (`asym_fe`):
`L(s, χ) = q^{1/2 − s} ε(χ) L(1 − s, χ⁻¹) Γ_ℂ(1 − s) T(s)`, from Mathlib's
`IsPrimitive.completedLFunction_one_sub` at `1 − s`, `LFunction_eq_completed_div_gammaFactor` (at
`s`, and at `1 − s` for `χ⁻¹`, whose parity is `χ`'s: `gammaFactor_inv`), and the Gamma-factor
ratio `G(1 − s)/G(s) = Γ_ℂ(1 − s)T(s)` (`gamma_ratio`, from `Gammaℝ_div_Gammaℝ_one_sub`; for odd
`χ` with `Gammaℝ_add_two`, `Gammaℂ_add_one`). `T = sin(πs/2)` (even) or `cos(πs/2)` (odd).
The log-derivative of the right side is a sum of four terms (`logDeriv_mul`): `−log q`,
`−L'/L(1 − s, χ⁻¹)` (`logDeriv_comp`), `log 2π − ψ(1 − s)` (`logDeriv_Gammaℂ`: `Γ_ℂ(w) =
2(2π)^{−w}Γ(w)`, `ψ = logDeriv Γ` by definition), and `(π/2)cot` or `−(π/2)tan`. `ε(χ) ≠ 0` is read
off the functional equation itself at `s = −1` (`rootNumber_ne_zero`): `Λ(2, χ) ≠ 0`.
-/

namespace Principia.Common.TernaryGoldbach.AG

open MeasureTheory Set Filter Topology Complex
open Principia.Common.TernaryGoldbach Principia.Common.TernaryGoldbach.EF

/-! ## (1) Parity and the Gamma factor -/

theorem even_inv_iff {q : ℕ} (χ : DirichletCharacter ℂ q) : χ⁻¹.Even ↔ χ.Even := by
  unfold DirichletCharacter.Even
  rw [MulChar.inv_apply_eq_inv']
  constructor
  · intro h
    have h2 := congrArg (fun z : ℂ => z⁻¹) h
    simpa using h2
  · intro h
    rw [h, inv_one]

theorem gammaFactor_inv {q : ℕ} (χ : DirichletCharacter ℂ q) :
    DirichletCharacter.gammaFactor χ⁻¹ = DirichletCharacter.gammaFactor χ := by
  funext s
  unfold DirichletCharacter.gammaFactor
  by_cases h : χ.Even
  · rw [if_pos ((even_inv_iff χ).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((even_inv_iff χ).mp h')), if_neg h]

open Classical in
/-- The trigonometric factor `T(s) = sin(πs/2)` (even `χ`) or `cos(πs/2)` (odd `χ`). -/
noncomputable def Tfac {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  if χ.Even then Complex.sin (Real.pi * s / 2) else Complex.cos (Real.pi * s / 2)

/-- `Re w > 0` excludes the poles `−(2n + 1)`. -/
theorem ne_neg_odd {w : ℂ} (hw : 0 < w.re) (n : ℕ) : w ≠ -(2 * n + 1) := by
  intro h
  have := congrArg Complex.re h
  simp at this
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- **`G(1 − s)/G(s) = Γ_ℂ(1 − s)T(s)`** on `−1 < Re s < 0`. -/
theorem gamma_ratio {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (h1 : -1 < s.re)
    (h2 : s.re < 0) :
    DirichletCharacter.gammaFactor χ (1 - s) / DirichletCharacter.gammaFactor χ s =
      Gammaℂ (1 - s) * Tfac χ s := by
  unfold DirichletCharacter.gammaFactor Tfac
  by_cases he : χ.Even
  · rw [if_pos he, if_pos he, if_pos he]
    have h := Gammaℝ_div_Gammaℝ_one_sub (s := 1 - s)
      (ne_neg_odd (by simp; linarith))
    rw [sub_sub_cancel] at h
    rw [h]
    congr 1
    rw [show (Real.pi : ℂ) * (1 - s) / 2 = Real.pi / 2 - Real.pi * s / 2 by ring,
      Complex.cos_pi_div_two_sub]
  · rw [if_neg he, if_neg he, if_neg he]
    have hw : (2 - s) = (1 - s) + 1 := by ring
    have h := Gammaℝ_div_Gammaℝ_one_sub (s := 2 - s) (ne_neg_odd (by simp; linarith))
    rw [show (1 : ℂ) - (2 - s) = s - 1 by ring] at h
    have hs1 : s - 1 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    have h1s : (1 : ℂ) - s ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    have hG : Gammaℝ (s - 1) ≠ 0 := by
      rw [Ne, Gammaℝ_eq_zero_iff]
      rintro ⟨n, hn⟩
      have := congrArg Complex.re hn
      simp at this
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0] at this
        simp at this
        linarith
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hpos
        linarith
    have hA : Gammaℝ (s + 1) = Gammaℝ (s - 1) * (s - 1) / 2 / Real.pi := by
      rw [← Gammaℝ_add_two hs1]
      ring_nf
    have hB : Gammaℂ (2 - s) = Gammaℂ (1 - s) * (1 - s) / 2 / Real.pi := by
      rw [hw, Gammaℂ_add_one h1s]
    have hC : Complex.cos (Real.pi * (2 - s) / 2) = -Complex.cos (Real.pi * s / 2) := by
      rw [show (Real.pi : ℂ) * (2 - s) / 2 = Real.pi - Real.pi * s / 2 by ring,
        Complex.cos_pi_sub]
    rw [show (1 : ℂ) - s + 1 = 2 - s by ring, hA]
    rw [div_eq_iff hG, hB, hC] at h
    rw [h]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring

/-! ## (2) The asymmetric functional equation on the strip -/

/-- **`ε(χ) ≠ 0`**, read off the functional equation at `s = −1`: `Λ(2, χ) ≠ 0`. -/
theorem rootNumber_ne_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : DirichletCharacter.rootNumber χ ≠ 0 := by
  intro h0
  have hfe := hχ.completedLFunction_one_sub (-1)
  rw [h0, mul_zero, zero_mul, show (1 : ℂ) - -1 = 2 by ring] at hfe
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 2
    (Or.inl two_ne_zero)
  rw [hfe, zero_div] at hL
  have hne := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num))
    (show (1 : ℝ) ≤ (2 : ℂ).re by norm_num)
  exact hne hL

/-- **`L(s, χ) = q^{1/2 − s} ε L(1 − s, χ⁻¹) Γ_ℂ(1 − s) T(s)`** on `−1 < Re s < 0`. -/
theorem asym_fe {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ}
    (h1 : -1 < s.re) (h2 : s.re < 0) :
    DirichletCharacter.LFunction χ s =
      DirichletCharacter.rootNumber χ * (q : ℂ) ^ (1 / 2 - s) *
        DirichletCharacter.LFunction χ⁻¹ (1 - s) * Gammaℂ (1 - s) * Tfac χ s := by
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at h2
    exact lt_irrefl 0 h2
  have h1s : (1 : ℂ) - s ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  have hfe := hχ.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at hfe
  have hL' := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s)
    (Or.inl h1s)
  rw [gammaFactor_inv] at hL'
  have hGne : DirichletCharacter.gammaFactor χ (1 - s) ≠ 0 := by
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    · exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  rw [eq_div_iff hGne] at hL'
  have hr := gamma_ratio χ h1 h2
  rw [hL, hfe, ← hL', show (1 : ℂ) - s - 1 / 2 = 1 / 2 - s by ring]
  have e : (q : ℂ) ^ (1 / 2 - s) * DirichletCharacter.rootNumber χ *
      (DirichletCharacter.LFunction χ⁻¹ (1 - s) * DirichletCharacter.gammaFactor χ (1 - s)) /
        DirichletCharacter.gammaFactor χ s =
      DirichletCharacter.rootNumber χ * (q : ℂ) ^ (1 / 2 - s) *
        DirichletCharacter.LFunction χ⁻¹ (1 - s) *
        (DirichletCharacter.gammaFactor χ (1 - s) / DirichletCharacter.gammaFactor χ s) := by
    ring
  rw [e, hr]
  ring

/-! ## (3) The four log-derivatives -/

theorem logDeriv_Gammaℂ {w : ℂ} (hw : 0 < w.re) :
    logDeriv Gammaℂ w = -Complex.log (2 * Real.pi) + Complex.digamma w := by
  have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw
  have hGd : DifferentiableAt ℂ Complex.Gamma w :=
    Complex.differentiableAt_Gamma w (fun m h => by
      have := congrArg Complex.re h
      simp at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hP : HasDerivAt (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (-z))
      ((2 * (Real.pi : ℂ)) ^ (-w) * Complex.log (2 * Real.pi) * (-1)) w :=
    (hasDerivAt_neg w).const_cpow (Or.inl h2pi)
  have hc : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := fun h =>
    h2pi ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hfun : Gammaℂ = fun z => (2 * (2 * (Real.pi : ℂ)) ^ (-z)) * Complex.Gamma z := by
    funext z
    rw [Gammaℂ_def]
  rw [hfun, logDeriv_mul (f := fun z : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-z))
    (g := Complex.Gamma) w (mul_ne_zero two_ne_zero hc) hG ((hP.const_mul 2).differentiableAt)
    hGd, logDeriv_const_mul w 2 two_ne_zero, ← Complex.digamma_def, logDeriv_apply, hP.deriv]
  field_simp

/-- `Γ_ℂ` is differentiable and nonzero on `Re w > 0`. -/
theorem gammaC_props {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ Gammaℂ w ∧ Gammaℂ w ≠ 0 := by
  have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw
  have hGd : DifferentiableAt ℂ Complex.Gamma w :=
    Complex.differentiableAt_Gamma w (fun m h => by
      have := congrArg Complex.re h
      simp at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hc : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := fun h =>
    h2pi ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hfun : Gammaℂ = fun z => (2 * (2 * (Real.pi : ℂ)) ^ (-z)) * Complex.Gamma z := by
    funext z
    rw [Gammaℂ_def]
  rw [hfun]
  refine ⟨?_, mul_ne_zero (mul_ne_zero two_ne_zero hc) hG⟩
  exact ((differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow (Or.inl h2pi)
    |>.const_mul 2).mul hGd

/-! ## (4) The log-derivative on `Re s = −1/2` -/

/-- `logDeriv` sees only a neighbourhood. -/
theorem logDeriv_congr_nhds {f g : ℂ → ℂ} {x : ℂ} (h : f =ᶠ[𝓝 x] g) :
    logDeriv f x = logDeriv g x := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

/-- `Re(sL τ) = −1/2`. -/
theorem sL_re (τ : ℝ) : (sL τ).re = -(1 / 2) := by
  simp [sL]
  norm_num

/-- **`logDeriv T = (π/2)U`** on `Re s = −1/2`. -/
theorem logDeriv_Tfac {q : ℕ} (χ : DirichletCharacter ℂ q) (τ : ℝ) :
    logDeriv (Tfac χ) (sL τ) = ((Real.pi / 2 : ℝ) : ℂ) * Ufac χ τ := by
  obtain ⟨-, hs, hc⟩ := cos_sin_sL τ
  have hlin : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) * s / 2) ((Real.pi : ℂ) * 1 / 2) (sL τ) :=
    ((hasDerivAt_id (sL τ)).const_mul (Real.pi : ℂ)).div_const 2
  by_cases he : χ.Even
  · have hT : Tfac χ = fun s => Complex.sin (Real.pi * s / 2) := by
      funext s
      simp [Tfac, he]
    rw [hT, logDeriv_apply, hlin.csin.deriv]
    unfold Ufac
    rw [if_pos he, Complex.cot_eq_cos_div_sin]
    push_cast
    field_simp
  · have hT : Tfac χ = fun s => Complex.cos (Real.pi * s / 2) := by
      funext s
      simp [Tfac, he]
    rw [hT, logDeriv_apply, hlin.ccos.deriv]
    unfold Ufac
    rw [if_neg he, Complex.tan_eq_sin_div_cos]
    push_cast
    field_simp

/-- **`LDFE` HOLDS.** -/
theorem ldfe_holds : LDFE := by
  intro q _ χ hχ τ
  have hre := sL_re τ
  have h1 : -1 < (sL τ).re := by rw [hre]; norm_num
  have h2 : (sL τ).re < 0 := by rw [hre]; norm_num
  have hR : 1 - sL τ = sR τ := one_sub_sL τ
  have hRre : (1 - sL τ).re = 3 / 2 := by rw [hR, sR_re]
  set ε := DirichletCharacter.rootNumber χ with hεdef
  have hε : ε ≠ 0 := rootNumber_ne_zero hχ
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  -- the four factors
  set A : ℂ → ℂ := fun s => ε * (q : ℂ) ^ (1 / 2 - s) with hA
  set B : ℂ → ℂ := fun s => DirichletCharacter.LFunction χ⁻¹ (1 - s) with hB
  set C : ℂ → ℂ := fun s => Gammaℂ (1 - s) with hC
  have hV : IsOpen {s : ℂ | -1 < s.re ∧ s.re < 0} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hEq : DirichletCharacter.LFunction χ =ᶠ[𝓝 (sL τ)]
      fun s => A s * B s * C s * Tfac χ s := by
    filter_upwards [hV.mem_nhds ⟨h1, h2⟩] with s hs
    rw [asym_fe hχ hs.1 hs.2]
  -- derivatives of the pieces
  have hsub : HasDerivAt (fun s : ℂ => 1 - s) (-1) (sL τ) := by
    simpa using (hasDerivAt_id (sL τ)).const_sub (1 : ℂ)
  have hApow : HasDerivAt (fun s : ℂ => (q : ℂ) ^ (1 / 2 - s))
      ((q : ℂ) ^ (1 / 2 - sL τ) * Complex.log q * (-1)) (sL τ) :=
    ((hasDerivAt_id (sL τ)).const_sub (1 / 2 : ℂ)).const_cpow (Or.inl hq0)
  have hLd : DifferentiableAt ℂ (DirichletCharacter.LFunction χ⁻¹) (1 - sL τ) :=
    DirichletCharacter.differentiableAt_LFunction χ⁻¹ (1 - sL τ) (Or.inl (by
      intro h0
      have := congrArg Complex.re h0
      rw [hRre] at this
      norm_num at this))
  have hLne : DirichletCharacter.LFunction χ⁻¹ (1 - sL τ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inr (by
      intro h0
      have := congrArg Complex.re h0
      rw [hRre] at this
      norm_num at this)) (by rw [hRre]; norm_num)
  obtain ⟨hGd, hGne⟩ := gammaC_props (w := 1 - sL τ) (by rw [hRre]; norm_num)
  obtain ⟨-, hsn, hcn⟩ := cos_sin_sL τ
  have hTne : Tfac χ (sL τ) ≠ 0 := by
    unfold Tfac
    split_ifs
    · exact hsn
    · exact hcn
  have hTd : DifferentiableAt ℂ (Tfac χ) (sL τ) := by
    have hlin : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) * s / 2) (sL τ) := by fun_prop
    by_cases he : χ.Even
    · have hT : Tfac χ = fun s => Complex.sin (Real.pi * s / 2) := by
        funext s
        simp [Tfac, he]
      rw [hT]
      exact hlin.csin
    · have hT : Tfac χ = fun s => Complex.cos (Real.pi * s / 2) := by
        funext s
        simp [Tfac, he]
      rw [hT]
      exact hlin.ccos
  have hAd : DifferentiableAt ℂ A (sL τ) := hApow.differentiableAt.const_mul ε
  have hBd : DifferentiableAt ℂ B (sL τ) := hLd.comp (sL τ) hsub.differentiableAt
  have hCd : DifferentiableAt ℂ C (sL τ) := hGd.comp (sL τ) hsub.differentiableAt
  have hAne : A (sL τ) ≠ 0 := mul_ne_zero hε (by
    intro h0
    exact hq0 ((Complex.cpow_eq_zero_iff _ _).mp h0).1)
  -- assemble
  unfold LD
  rw [logDeriv_congr_nhds hEq,
    logDeriv_mul (f := fun s => A s * B s * C s) (g := Tfac χ) (sL τ)
      (mul_ne_zero (mul_ne_zero hAne hLne) hGne) hTne ((hAd.mul hBd).mul hCd) hTd,
    logDeriv_mul (f := fun s => A s * B s) (g := C) (sL τ) (mul_ne_zero hAne hLne) hGne
      (hAd.mul hBd) hCd,
    logDeriv_mul (f := A) (g := B) (sL τ) hAne hLne hAd hBd,
    logDeriv_Tfac]
  have eA : logDeriv A (sL τ) = -(Real.log q : ℂ) := by
    rw [hA, logDeriv_const_mul (sL τ) ε hε, logDeriv_apply, hApow.deriv]
    have hc : (q : ℂ) ^ (1 / 2 - sL τ) ≠ 0 := fun h0 =>
      hq0 ((Complex.cpow_eq_zero_iff _ _).mp h0).1
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg q),
      Complex.ofReal_natCast, mul_assoc, mul_div_cancel_left₀ _ hc]
    ring
  have eB : logDeriv B (sL τ) = -LD χ⁻¹ (sR τ) := by
    have h := logDeriv_comp (f := DirichletCharacter.LFunction χ⁻¹) (g := fun s : ℂ => 1 - s)
      hLd hsub.differentiableAt
    rw [hsub.deriv] at h
    rw [hB, ← hR]
    unfold LD
    rw [show (fun s : ℂ => DirichletCharacter.LFunction χ⁻¹ (1 - s)) =
      DirichletCharacter.LFunction χ⁻¹ ∘ fun s : ℂ => 1 - s from rfl, h]
    ring
  have eC : logDeriv C (sL τ) = (Real.log (2 * Real.pi) : ℂ) - Complex.digamma (sR τ) := by
    have h := logDeriv_comp (f := Gammaℂ) (g := fun s : ℂ => 1 - s) hGd hsub.differentiableAt
    rw [hsub.deriv, logDeriv_Gammaℂ (by rw [hRre]; norm_num)] at h
    rw [hC, show (fun s : ℂ => Gammaℂ (1 - s)) = Gammaℂ ∘ fun s : ℂ => 1 - s from rfl, h, hR,
      Complex.ofReal_log (by positivity)]
    push_cast
    ring
  rw [eA, eB, eC]
  unfold LD
  ring

end Principia.Common.TernaryGoldbach.AG
