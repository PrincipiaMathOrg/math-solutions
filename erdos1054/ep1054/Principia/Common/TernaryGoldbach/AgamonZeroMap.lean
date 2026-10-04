/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.AgamonLocalRes
import Mathlib.NumberTheory.LSeries.ZetaZeros

set_option autoImplicit false

/-!
# The zero map of `L(s, χ)` on `−1/2 ≤ Re s ≤ 3/2`, and its local structure

For a primitive `χ` mod `q`:
* `asym_fe'`: `L(s, χ) = ε q^{1/2 − s} L(1 − s, χ⁻¹) Γ_ℂ(1 − s) T(s)` on `−1 < Re s < 1/2` (when
  `s ≠ 0 ∨ q ≠ 1`) — `AG.asym_fe` on a wider strip;
* `L_ne_zero_left`: no zeros on `−1 < Re s ≤ 0` except `s = 0`; `L_zero_iff`: `L(0, χ) = 0` iff
  `q ≠ 1` and `χ` is even (the trivial zero), and then `analyticOrderNatAt L 0 = 1`
  (`order_trivial_zero`, from `L'(0) = A(0)·π/2 ≠ 0`);
* `zeta_pole`: `ζ = g/(s − 1)` near `1` with `g` analytic, `g(1) = 1` (`riemannZeta_residue_one`
  and the removable-singularity theorem);
* `zeros_finite`: finitely many zeros in any compact set (`ζ`: Mathlib
  `IsCompact.inter_riemannZetaZeros_finite`; `χ ≠ 1`: the zeros of an entire function that is
  not identically zero are discrete and closed); `order_ne_top`: every zero has finite order.
-/

namespace Principia.Common.TernaryGoldbach.AG

open Complex Set Filter Topology Asymptotics
open Principia.Common.TernaryGoldbach Principia.Common.TernaryGoldbach.EF

/-! ## (1) The functional equation on `−1 < Re s < 1/2` -/

/-- `G(1 − s)/G(s) = Γ_ℂ(1 − s)T(s)` on `−1 < Re s < 1/2`. -/
theorem gamma_ratio' {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (h1 : -1 < s.re)
    (h2 : s.re < 1 / 2) :
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

/-- **`L(s, χ) = ε q^{1/2 − s} L(1 − s, χ⁻¹) Γ_ℂ(1 − s) T(s)`** on `−1 < Re s < 1/2`. -/
theorem asym_fe' {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ}
    (h1 : -1 < s.re) (h2 : s.re < 1 / 2) (hs : s ≠ 0 ∨ q ≠ 1) :
    DirichletCharacter.LFunction χ s =
      DirichletCharacter.rootNumber χ * (q : ℂ) ^ (1 / 2 - s) *
        DirichletCharacter.LFunction χ⁻¹ (1 - s) * Gammaℂ (1 - s) * Tfac χ s := by
  have h1s : (1 : ℂ) - s ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s hs
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
  have hr := gamma_ratio' χ h1 h2
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

/-! ## (2) The zero map on `−1 < Re s ≤ 0` -/

/-- A primitive character mod `q ≠ 1` is not trivial. -/
theorem ne_one_of_primitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) : χ ≠ 1 := by
  intro h
  rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hχ
  exact hq hχ.symm

/-- **`T(s) ≠ 0`** on `−1 < Re s ≤ 0`, `s ≠ 0`. -/
theorem Tfac_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (h1 : -1 < s.re)
    (h2 : s.re ≤ 0) (hs : s ≠ 0) : Tfac χ s ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold Tfac
  split_ifs
  · rw [Ne, Complex.sin_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hs2 : s = 2 * k := by
      field_simp at hk
      linear_combination hk
    have hre := congrArg Complex.re hs2
    simp at hre
    have hk1 : (k : ℝ) ≤ 0 := by linarith
    have hk2 : -1 < 2 * (k : ℝ) := by linarith
    have hk0 : k = 0 := by
      have : -1 < k := by exact_mod_cast (show ((-1 : ℤ) : ℝ) < k by push_cast; linarith)
      have : k ≤ 0 := by exact_mod_cast hk1
      omega
    rw [hk0] at hs2
    simp at hs2
    exact hs hs2
  · rw [Ne, Complex.cos_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hs2 : s = 2 * k + 1 := by
      field_simp at hk
      linear_combination hk
    have hre := congrArg Complex.re hs2
    simp at hre
    have hk1 : 2 * (k : ℝ) + 1 ≤ 0 := by linarith
    have hk2 : -1 < 2 * (k : ℝ) + 1 := by linarith
    have : (-1 : ℝ) < k := by linarith
    have : (k : ℝ) < 0 := by linarith
    have hka : -1 < k := by exact_mod_cast (show ((-1 : ℤ) : ℝ) < k by push_cast; linarith)
    have hkb : k < 0 := by exact_mod_cast (show (k : ℝ) < ((0 : ℤ) : ℝ) by push_cast; linarith)
    omega

/-- **No zeros on `−1 < Re s ≤ 0` except `0`.** -/
theorem L_ne_zero_left {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {s : ℂ} (h1 : -1 < s.re) (h2 : s.re ≤ 0) (hs : s ≠ 0) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hre1 : 1 ≤ (1 - s).re := by simp; linarith
  rw [asym_fe' hχ h1 (by linarith) (Or.inl hs)]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (rootNumber_ne_zero hχ) ?_) ?_)
    (gammaC_props (by linarith)).2) (Tfac_ne_zero χ h1 h2 hs)
  · intro h0
    exact hq0 ((Complex.cpow_eq_zero_iff _ _).mp h0).1
  · refine DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inr ?_) hre1
    intro h0
    exact hs (by linear_combination -h0)

/-- **`L(0, χ) = 0` iff `q ≠ 1` and `χ` is even.** -/
theorem L_zero_iff {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    DirichletCharacter.LFunction χ 0 = 0 ↔ (q ≠ 1 ∧ χ.Even) := by
  constructor
  · intro h0
    by_contra hn
    rcases eq_or_ne q 1 with hq | hq
    · subst hq
      rw [DirichletCharacter.LFunction_modOne_eq, riemannZeta_zero] at h0
      norm_num at h0
    · have hodd : ¬χ.Even := fun he => hn ⟨hq, he⟩
      rw [asym_fe' hχ (by simp) (by simp) (Or.inr hq)] at h0
      have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
      have hT : Tfac χ 0 = 1 := by simp [Tfac, hodd]
      rw [hT, mul_one] at h0
      simp only [sub_zero] at h0
      have hL1 := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹
        (Or.inl (inv_ne_one.mpr (ne_one_of_primitive hχ hq))) (show (1 : ℝ) ≤ (1 : ℂ).re by simp)
      have hG := (gammaC_props (w := 1) (by simp)).2
      have hc : (q : ℂ) ^ (1 / 2 - 0 : ℂ) ≠ 0 := fun h =>
        hq0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
      rw [sub_zero] at hc
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (rootNumber_ne_zero hχ) hc) hL1) hG) h0
  · rintro ⟨hq, he⟩
    rw [asym_fe' hχ (by simp) (by simp) (Or.inr hq)]
    simp [Tfac, he]

/-! ## (3) Finite analytic order -/

/-- `L` is analytic at every point other than `1`, and everywhere if `q ≠ 1`. -/
theorem analyticAt_L {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {s : ℂ} (hs : q ≠ 1 ∨ s ≠ 1) : AnalyticAt ℂ (DirichletCharacter.LFunction χ) s := by
  rcases hs with hq | hs
  · exact (DirichletCharacter.differentiable_LFunction (ne_one_of_primitive hχ hq)).analyticAt s
  · have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {1}ᶜ := fun z hz =>
      (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
    exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hs)

/-- **Every point other than `1` has finite order.** -/
theorem order_ne_top {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {s : ℂ} (hs : s ≠ 1) : analyticOrderAt (DirichletCharacter.LFunction χ) s ≠ ⊤ := by
  have hU : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {1}ᶜ := fun z hz =>
    analyticAt_L hχ (Or.inr hz)
  have h2 : analyticOrderAt (DirichletCharacter.LFunction χ) 2 ≠ ⊤ := by
    rw [(analyticAt_L hχ (Or.inr (by norm_num))).analyticOrderAt_eq_zero.mpr]
    · simp
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num))
        (by norm_num)
  exact hU.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num) hs h2

/-- **A simple zero**: `f(p) = 0`, `f'(p) ≠ 0` give order `1`. -/
theorem order_one_of_deriv {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) (h0 : f p = 0)
    (hd : deriv f p ≠ 0) : analyticOrderAt f p = 1 := by
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, hf.analyticOrderAt_eq_natCast]
  obtain ⟨U, hUo, hpU, hU⟩ : ∃ U : Set ℂ, IsOpen U ∧ p ∈ U ∧ DifferentiableOn ℂ f U := by
    obtain ⟨V, hV, hVo, hpV⟩ := eventually_nhds_iff.mp hf.eventually_analyticAt
    exact ⟨V, hVo, hpV, fun z hz => (hV z hz).differentiableAt.differentiableWithinAt⟩
  have hds : DifferentiableOn ℂ (dslope f p) U :=
    (Complex.differentiableOn_dslope (hUo.mem_nhds hpU)).mpr hU
  refine ⟨dslope f p, hds.analyticAt (hUo.mem_nhds hpU), by rw [dslope_same]; exact hd,
    Eventually.of_forall fun z => ?_⟩
  have := sub_smul_dslope f p z
  rw [h0, sub_zero] at this
  rw [pow_one, this]

/-- **The trivial zero at `0` is simple** (`q ≠ 1`, `χ` even). -/
theorem order_trivial_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) (he : χ.Even) :
    analyticOrderAt (DirichletCharacter.LFunction χ) 0 = 1 ∧
      analyticOrderNatAt (DirichletCharacter.LFunction χ) 0 = 1 := by
  set A : ℂ → ℂ := fun s => DirichletCharacter.rootNumber χ * (q : ℂ) ^ (1 / 2 - s) *
    DirichletCharacter.LFunction χ⁻¹ (1 - s) * Gammaℂ (1 - s) with hA
  have hV : IsOpen {s : ℂ | -1 < s.re ∧ s.re < 1 / 2} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hEq : DirichletCharacter.LFunction χ =ᶠ[𝓝 0] fun s => A s * Complex.sin (Real.pi * s / 2) :=
    by
    filter_upwards [hV.mem_nhds (show (0 : ℂ) ∈ {s : ℂ | -1 < s.re ∧ s.re < 1 / 2} by
      simp only [mem_setOf_eq, Complex.zero_re]; norm_num)] with s hs
    rw [asym_fe' hχ hs.1 hs.2 (Or.inr hq)]
    simp [Tfac, he, hA]
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  -- `A` is differentiable at `0` with `A(0) ≠ 0`
  have hχ1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr (ne_one_of_primitive hχ hq)
  have hsub : HasDerivAt (fun s : ℂ => 1 - s) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_sub (1 : ℂ)
  have hAd : DifferentiableAt ℂ A 0 := by
    have h1 : DifferentiableAt ℂ (fun s : ℂ => (q : ℂ) ^ (1 / 2 - s)) 0 :=
      ((hasDerivAt_id (0 : ℂ)).const_sub (1 / 2 : ℂ)).const_cpow (Or.inl hq0) |>.differentiableAt
    have h2 : DifferentiableAt ℂ (fun s : ℂ => DirichletCharacter.LFunction χ⁻¹ (1 - s)) 0 :=
      ((DirichletCharacter.differentiable_LFunction hχ1) (1 - 0)).comp (0 : ℂ)
        hsub.differentiableAt
    have h3 : DifferentiableAt ℂ (fun s : ℂ => Gammaℂ (1 - s)) 0 :=
      (gammaC_props (w := 1 - 0) (by simp)).1.comp (0 : ℂ) hsub.differentiableAt
    exact ((h1.const_mul _).mul h2).mul h3
  have hA0 : A 0 ≠ 0 := by
    simp only [hA, sub_zero]
    have hL1 := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχ1)
      (show (1 : ℝ) ≤ (1 : ℂ).re by simp)
    have hG := (gammaC_props (w := 1) (by simp)).2
    have hc : (q : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := fun h => hq0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (rootNumber_ne_zero hχ) hc) hL1) hG
  have hlin : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) * s / 2) ((Real.pi : ℂ) * 1 / 2) 0 :=
    ((hasDerivAt_id (0 : ℂ)).const_mul (Real.pi : ℂ)).div_const 2
  have hprod : HasDerivAt (fun s => A s * Complex.sin (Real.pi * s / 2))
      (deriv A 0 * Complex.sin (Real.pi * 0 / 2) +
        A 0 * (Complex.cos (Real.pi * 0 / 2) * (Real.pi * 1 / 2))) 0 :=
    hAd.hasDerivAt.mul hlin.csin
  have hderiv : deriv (DirichletCharacter.LFunction χ) 0 ≠ 0 := by
    rw [hEq.deriv_eq, hprod.deriv]
    simp only [mul_zero, zero_div, Complex.sin_zero, mul_zero, zero_add, Complex.cos_zero,
      one_mul]
    exact mul_ne_zero hA0 (by simp)
  have hL0 : DirichletCharacter.LFunction χ 0 = 0 := (L_zero_iff hχ).mpr ⟨hq, he⟩
  have hord := order_one_of_deriv (analyticAt_L hχ (Or.inl hq)) hL0 hderiv
  refine ⟨hord, ?_⟩
  unfold analyticOrderNatAt
  rw [hord]
  rfl

/-! ## (4) The pole of `ζ` -/

/-- **`ζ = g/(s − 1)` near `1`, `g` analytic, `g(1) = 1`.** -/
theorem zeta_pole : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ g 1 = 1 ∧
    ∀ᶠ z in 𝓝[≠] (1 : ℂ), riemannZeta z = g z / (z - 1) := by
  classical
  set g₀ : ℂ → ℂ := fun z => (z - 1) * riemannZeta z with hg₀
  set g : ℂ → ℂ := Function.update g₀ 1 1 with hg
  have hcont : ContinuousAt g 1 := by
    rw [hg, continuousAt_update_same]
    exact riemannZeta_residue_one
  have hdiff : DifferentiableOn ℂ g ({1}ᶜ : Set ℂ) := by
    intro z hz
    have hz1 : z ≠ 1 := hz
    have h1 : DifferentiableAt ℂ g₀ z :=
      (differentiableAt_id.sub (differentiableAt_const _)).mul (differentiableAt_riemannZeta hz1)
    have h2 : g =ᶠ[𝓝 z] g₀ := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz1] with w hw
      rw [hg, Function.update_of_ne hw]
    exact (h1.congr_of_eventuallyEq h2).differentiableWithinAt
  have hU : (univ : Set ℂ) ∈ 𝓝 (1 : ℂ) := univ_mem
  have hdiffU : DifferentiableOn ℂ g univ := by
    have := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hU).mp
      ⟨hdiff.mono (fun z hz => hz.2), hcont⟩
    exact this
  refine ⟨g, hdiffU.analyticAt hU, by rw [hg, Function.update_self], ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  rw [hg, Function.update_of_ne hz, hg₀]
  field_simp

/-! ## (5) Finitely many zeros in a compact set -/

/-- **Finitely many zeros of `L` in a compact set.** -/
theorem zeros_finite {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ DirichletCharacter.LFunction χ ⁻¹' {0}).Finite := by
  rcases eq_or_ne q 1 with hq | hq
  · subst hq
    have h := hK.inter_riemannZetaZeros_finite
    refine h.subset fun z hz => ⟨hz.1, ?_⟩
    have := hz.2
    simp only [mem_preimage, mem_singleton_iff, DirichletCharacter.LFunction_modOne_eq] at this
    exact this
  · have hent := DirichletCharacter.differentiable_LFunction (ne_one_of_primitive hχ hq)
    have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) univ := fun z _ =>
      hent.analyticAt z
    have h2 : DirichletCharacter.LFunction χ 2 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num)
    have hcod := han.preimage_zero_mem_codiscrete h2
    have hcl : IsClosed (DirichletCharacter.LFunction χ ⁻¹' {0}) :=
      isClosed_singleton.preimage hent.continuous
    have hdisc : IsDiscrete (DirichletCharacter.LFunction χ ⁻¹' {0}) := by
      simpa using (mem_codiscrete'.mp hcod).2
    exact (hK.inter_right hcl).finite (hdisc.mono inter_subset_right)

end Principia.Common.TernaryGoldbach.AG
