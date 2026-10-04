/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.AgamonZeroMap

set_option autoImplicit false

/-!
# `EF.Rectangle` PROVED: the residue theorem for `Ψ = −(L'/L)Φx^s` on `[−1/2, 3/2] × [−T, T]`

**`rectangle_holds : EF.Rectangle`**, with no hypothesis. For primitive `χ` mod `q`, `Φ`
holomorphic on `−1 < Re s < b` (`b > 3/2`), `x > 0` and a height `T > 0` that is no ordinate of a
non-trivial zero: the zeros `S = {ρ ∈ zeroSet χ : |Im ρ| < T}` form a finite set
(`AG.zeros_finite`), and `∮ Ψ = 2πi·resSum`.

The poles of `Ψ` in the closed rectangle are exactly `S`, the pole `1` of `ζ` (`q = 1`), and the
trivial zero `0` of an even `χ` with `q ≠ 1` (`hzm`, from `AG.L_ne_zero_left`, `AG.L_zero_iff`,
Mathlib `LFunction_ne_zero_of_one_le_re`, and the hypothesis on `T` for the horizontal edges). At a
zero `ρ` of order `m`, `L'/L − m/(s − ρ) = O(1)` (`AG.logDeriv_sub_order`, with `AG.order_ne_top`;
at `0` the order is `1`, `AG.order_trivial_zero`); at `1`, `ζ'/ζ + 1/(s − 1) = O(1)`
(`AG.logDeriv_sub_pole`, `AG.zeta_pole`). Multiplying by the holomorphic `−Φ x^s`
(`AG.mul_principal`) gives the residues `−mΦ(ρ)x^ρ`, `Φ(1)x`, `−Φ(0)`, and the finite residue
theorem `AG.rect_residue_finset` sums them to `resSum`.
-/

namespace Principia.Common.TernaryGoldbach.AG

open Complex Set Filter Topology Asymptotics
open Principia.Common.TernaryGoldbach Principia.Common.TernaryGoldbach.EF
open scoped Interval

/-- **`EF.Rectangle` HOLDS.** -/
theorem rectangle_holds : Rectangle := by
  classical
  intro q _ χ hχ Φ ⟨b, hb, hΦ⟩ x hx T hT hTz
  set z₀ : ℂ := -1 / 2 - T * I with hz₀
  set w₀ : ℂ := 3 / 2 + T * I with hw₀
  have hz0re : z₀.re = -1 / 2 := by simp [hz₀]
  have hz0im : z₀.im = -T := by simp [hz₀]
  have hw0re : w₀.re = 3 / 2 := by simp [hw₀]
  have hw0im : w₀.im = T := by simp [hw₀]
  set L := DirichletCharacter.LFunction χ with hL
  -- the closed rectangle and its interior
  have hmemR : ∀ s : ℂ, s ∈ Complex.Rectangle z₀ w₀ →
      (-1 / 2 ≤ s.re ∧ s.re ≤ 3 / 2) ∧ (-T ≤ s.im ∧ s.im ≤ T) := by
    intro s hs
    rw [Complex.Rectangle, Complex.mem_reProdIm, hz0re, hw0re, hz0im, hw0im,
      uIcc_of_le (by norm_num), uIcc_of_le (by linarith)] at hs
    exact ⟨hs.1, hs.2⟩
  have hmemR' : ∀ s : ℂ, (-1 / 2 ≤ s.re ∧ s.re ≤ 3 / 2) → (-T ≤ s.im ∧ s.im ≤ T) →
      s ∈ Complex.Rectangle z₀ w₀ := by
    intro s h1 h2
    rw [Complex.Rectangle, Complex.mem_reProdIm, hz0re, hw0re, hz0im, hw0im,
      uIcc_of_le (by norm_num), uIcc_of_le (by linarith)]
    exact ⟨h1, h2⟩
  have hint : ∀ p : ℂ, (-1 / 2 < p.re ∧ p.re < 3 / 2) → (-T < p.im ∧ p.im < T) →
      Complex.Rectangle z₀ w₀ ∈ 𝓝 p := by
    intro p h1 h2
    rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm, hz0re, hw0re, hz0im, hw0im,
      uIoo_of_le (by norm_num), uIoo_of_le (by linarith)]
    exact ⟨h1, h2⟩
  -- the finite set of zeros
  have hRc : IsCompact (Complex.Rectangle z₀ w₀) := isCompact_uIcc.reProdIm isCompact_uIcc
  have hZsub : {ρ | ρ ∈ HM.zeroSet χ ∧ |ρ.im| < T} ⊆ Complex.Rectangle z₀ w₀ ∩ L ⁻¹' {0} := by
    rintro ρ ⟨⟨h0, h1, h2⟩, h3⟩
    refine ⟨hmemR' ρ ⟨by linarith, by linarith⟩ ⟨?_, ?_⟩, h0⟩
    · linarith [neg_abs_le ρ.im]
    · linarith [le_abs_self ρ.im]
  have hZfin := (zeros_finite hχ hRc).subset hZsub
  set S := hZfin.toFinset with hSdef
  have hS : (↑S : Set ℂ) = {ρ | ρ ∈ HM.zeroSet χ ∧ |ρ.im| < T} := hZfin.coe_toFinset
  have hmemS : ∀ ρ, ρ ∈ S ↔ ρ ∈ HM.zeroSet χ ∧ |ρ.im| < T := by
    intro ρ
    rw [← Finset.mem_coe, hS]
    rfl
  refine ⟨S, hS, ?_⟩
  -- the extra poles and the residues
  set E : Finset ℂ := (if q = 1 then {1} else ∅) ∪ (if q ≠ 1 ∧ χ.Even then {0} else ∅) with hE
  set P : Finset ℂ := S ∪ E with hP
  set c : ℂ → ℂ := fun p => if q = 1 ∧ p = 1 then Φ 1 * x else
    -(analyticOrderNatAt L p : ℂ) * Φ p * (x : ℂ) ^ p with hc
  have h1notS : (1 : ℂ) ∉ S := fun h => by
    have := ((hmemS 1).mp h).1.2.2
    simp at this
  have h0notS : (0 : ℂ) ∉ S := fun h => by
    have := ((hmemS 0).mp h).1.2.1
    simp at this
  have hEmem : ∀ p ∈ E, (q = 1 ∧ p = 1) ∨ (q ≠ 1 ∧ χ.Even ∧ p = 0) := by
    intro p hp
    rw [hE, Finset.mem_union] at hp
    rcases hp with hp | hp
    · split_ifs at hp with hq
      · exact Or.inl ⟨hq, Finset.mem_singleton.mp hp⟩
      · simp at hp
    · split_ifs at hp with hq
      · exact Or.inr ⟨hq.1, hq.2, Finset.mem_singleton.mp hp⟩
      · simp at hp
  have h1E : q = 1 → (1 : ℂ) ∈ P := fun hq => by
    rw [hP, Finset.mem_union]
    right
    rw [hE, Finset.mem_union]
    left
    rw [if_pos hq]
    exact Finset.mem_singleton_self 1
  have h0E : q ≠ 1 → χ.Even → (0 : ℂ) ∈ P := fun hq he => by
    rw [hP, Finset.mem_union]
    right
    rw [hE, Finset.mem_union]
    right
    rw [if_pos ⟨hq, he⟩]
    exact Finset.mem_singleton_self 0
  -- (a) the poles are interior points
  have ha : ∀ p ∈ P, Complex.Rectangle z₀ w₀ ∈ 𝓝 p := by
    intro p hp
    rw [hP, Finset.mem_union] at hp
    rcases hp with hp | hp
    · obtain ⟨⟨-, h1, h2⟩, h3⟩ := (hmemS p).mp hp
      exact hint p ⟨by linarith, by linarith⟩ ⟨by linarith [neg_abs_le p.im],
        by linarith [le_abs_self p.im]⟩
    · rcases hEmem p hp with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
      · exact hint 1 ⟨by norm_num, by norm_num⟩ ⟨by simp; linarith, by simp; linarith⟩
      · exact hint 0 ⟨by norm_num, by norm_num⟩ ⟨by simp; linarith, by simp; linarith⟩
  -- the zero map: off `P`, `L` has no zero in the closed rectangle
  have hzm : ∀ s ∈ Complex.Rectangle z₀ w₀, s ∉ P → L s ≠ 0 := by
    intro s hs hsP h0
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := hmemR s hs
    rcases le_or_gt 1 s.re with hre | hre
    · have hs1 : χ ≠ 1 ∨ s ≠ 1 := by
        rcases eq_or_ne q 1 with hq | hq
        · right
          rintro rfl
          exact hsP (h1E hq)
        · left
          exact ne_one_of_primitive hχ hq
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hs1 hre h0
    · rcases le_or_gt s.re 0 with hre0 | hre0
      · by_cases hs0 : s = 0
        · rw [hs0] at h0 hsP
          obtain ⟨hq, he⟩ := (L_zero_iff hχ).mp h0
          exact hsP (h0E hq he)
        · exact L_ne_zero_left hχ (by linarith) hre0 hs0 h0
      · have hz : s ∈ HM.zeroSet χ := ⟨h0, hre0, hre⟩
        have him : |s.im| < T := lt_of_le_of_ne (abs_le.mpr ⟨hi1, hi2⟩) (hTz s hz)
        exact hsP (Finset.mem_union_left _ ((hmemS s).mpr ⟨hz, him⟩))
  -- the holomorphic factor `H = −Φ x^s`
  set H : ℂ → ℂ := fun s => -(Φ s) * (x : ℂ) ^ s with hH
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hVo : IsOpen {s : ℂ | -1 < s.re ∧ s.re < b} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hHd : ∀ s : ℂ, -1 < s.re → s.re < b → DifferentiableAt ℂ H s := by
    intro s h1 h2
    have hΦs : DifferentiableAt ℂ Φ s := hΦ.differentiableAt (hVo.mem_nhds ⟨h1, h2⟩)
    have hxs : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) s :=
      differentiableAt_id.const_cpow (Or.inl hx0)
    exact hΦs.neg.mul hxs
  have hPsi : Psi χ Φ x = fun s => LD χ s * H s := by
    funext s
    simp only [Psi, hH]
    ring
  -- (b) holomorphy off the poles
  have hb' : HolomorphicOn (Psi χ Φ x) (Complex.Rectangle z₀ w₀ \ ↑P) := by
    intro s hs
    obtain ⟨⟨hr1, hr2⟩, -⟩ := hmemR s hs.1
    have hsP : s ∉ P := hs.2
    have hLs : L s ≠ 0 := hzm s hs.1 hsP
    have hs1 : q ≠ 1 ∨ s ≠ 1 := by
      rcases eq_or_ne q 1 with hq | hq
      · right
        rintro rfl
        exact hsP (h1E hq)
      · exact Or.inl hq
    have hA := analyticAt_L hχ hs1
    have hLD : DifferentiableAt ℂ (LD χ) s := by
      unfold LD
      have h1 : DifferentiableAt ℂ (deriv L) s := hA.deriv.differentiableAt
      exact h1.div hA.differentiableAt hLs
    rw [hPsi]
    exact (hLD.mul (hHd s (by linarith) (by linarith))).differentiableWithinAt
  -- (c) the local conditions
  have hc' : ∀ p ∈ P, (Psi χ Φ x - fun s => c p / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    intro p hp
    have hpre : -1 / 2 < p.re ∧ p.re < 3 / 2 := by
      have := ha p hp
      rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm, hz0re, hw0re,
        uIoo_of_le (by norm_num)] at this
      exact this.1
    have hHp := hHd p (by linarith [hpre.1]) (by linarith [hpre.2])
    rw [hPsi]
    by_cases hp1 : q = 1 ∧ p = 1
    · -- the pole of `ζ`
      obtain ⟨hq, rfl⟩ := hp1
      have hcp : c 1 = (-1 : ℂ) * H 1 := by
        simp only [hc, hH, if_pos (show q = 1 ∧ (1 : ℂ) = 1 from ⟨hq, rfl⟩), Complex.cpow_one]
        ring
      rw [hcp]
      obtain ⟨g, hg, hg1, hfg⟩ := zeta_pole
      subst hq
      have hLz : DirichletCharacter.LFunction χ = riemannZeta :=
        DirichletCharacter.LFunction_modOne_eq
      have hpole := logDeriv_sub_pole hg (by rw [hg1]; exact one_ne_zero) hfg
      have hLD : LD χ = logDeriv riemannZeta := by
        funext s
        simp only [LD, hLz]
      rw [hLD]
      exact mul_principal hpole hHp
    · -- a zero of `L`: `S` or the trivial zero
      have hp1' : p ≠ 1 := by
        intro h
        rw [hP, Finset.mem_union] at hp
        rcases hp with hp | hp
        · exact h1notS (h ▸ hp)
        · rcases hEmem p hp with ⟨hq, -⟩ | ⟨-, -, h0⟩
          · exact hp1 ⟨hq, h⟩
          · rw [h0] at h
            exact zero_ne_one h
      have hcp : c p = (analyticOrderNatAt L p : ℂ) * H p := by
        simp only [hc, hH, if_neg hp1]
        ring
      rw [hcp]
      have hord := logDeriv_sub_order (analyticAt_L hχ (Or.inr hp1')) (order_ne_top hχ hp1')
      exact mul_principal hord hHp
  -- the residue theorem
  have hres := rect_residue_finset (by rw [hz0re, hw0re]; norm_num)
    (by rw [hz0im, hw0im]; linarith) P c (Psi χ Φ x) ha hb' hc'
  have hdisj : Disjoint S E := by
    rw [Finset.disjoint_left]
    intro p hpS hpE
    rcases hEmem p hpE with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
    · exact h1notS hpS
    · exact h0notS hpS
  have hSsum : ∑ p ∈ S, c p =
      -∑ ρ ∈ S, (analyticOrderNatAt L ρ : ℂ) * Φ ρ * (x : ℂ) ^ ρ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hρ1 : ¬(q = 1 ∧ ρ = 1) := fun h => h1notS (h.2 ▸ hρ)
    simp only [hc, if_neg hρ1]
    ring
  have hEsum : ∑ p ∈ E, c p =
      (if q = 1 then Φ 1 * x else 0) - (if q ≠ 1 ∧ χ.Even then Φ 0 else 0) := by
    rcases eq_or_ne q 1 with hq | hq
    · have hE1 : E = {1} := by
        rw [hE, if_pos hq, if_neg (fun h => h.1 hq), Finset.union_empty]
      rw [hE1, Finset.sum_singleton, if_pos hq, if_neg (fun h => h.1 hq), sub_zero]
      simp only [hc, if_pos (show q = 1 ∧ (1 : ℂ) = 1 from ⟨hq, rfl⟩)]
    · by_cases he : χ.Even
      · have hE0 : E = {0} := by
          rw [hE, if_neg hq, if_pos ⟨hq, he⟩, Finset.empty_union]
        rw [hE0, Finset.sum_singleton, if_neg hq, if_pos ⟨hq, he⟩, zero_sub]
        have h01 : ¬(q = 1 ∧ (0 : ℂ) = 1) := fun h => hq h.1
        have hm0 : analyticOrderNatAt L 0 = 1 := (order_trivial_zero hχ hq he).2
        simp only [hc, if_neg h01, hm0, Complex.cpow_zero]
        push_cast
        ring
      · have hEe : E = ∅ := by
          rw [hE, if_neg hq, if_neg (fun h => he h.2), Finset.union_empty]
        rw [hEe, Finset.sum_empty, if_neg hq, if_neg (fun h => he h.2), sub_zero]
  have hsum : ∑ p ∈ P, c p = resSum χ Φ x S := by
    rw [hP, Finset.sum_union hdisj, hSsum, hEsum, resSum]
    ring
  have e : RectangleIntegral (Psi χ Φ x) z₀ w₀ =
      2 * Real.pi * I * RectangleIntegral' (Psi χ Φ x) z₀ w₀ := by
    rw [RectangleIntegral', smul_eq_mul]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  rw [e, hres, hsum]

end Principia.Common.TernaryGoldbach.AG
