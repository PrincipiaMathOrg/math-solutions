/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.SW.SiegelC

/-!
# Siegel–Walfisz, `Merge`: the final zero-free region, the contour `L'/L` bound, character orthogonality

Ported **verbatim** from the axiom-clean Siegel–Walfisz master
(`Principia Application/LeanSandbox/SiegelWalfiszMaster.lean` = `C:/Users/Christian/pnt/sw_full.lean`,
lines 12247–12874; there `#print axioms siegel_walfisz_proven = [propext, Classical.choice, Quot.sound]`,
built in the PrimeNumberTheoremAnd workspace on Mathlib `db127794`, one day from ours). The master
imported `Mathlib`, `PrimeNumberTheoremAnd.MediumPNT` and `PrimeNumberTheoremAnd.PerronFormula`; here
the Mathlib imports are narrowed, the two Perron-kernel shims are re-proved from Mathlib's Mellin
inversion (`Principia.Common.SW.PerronKernel`), and the `medium_PNT` shim is not ported (see
`MediumPNTBound` in `Principia.Common.SW.Rate`). Declarations live in `Principia.Common.SW`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
open DirichletCharacter Complex PowerSeries ArithmeticFunction Finset Filter

namespace Principia.Common.SW

/-! ### ================= THE FINAL MERGE (S4b) ================= -/

/-- **THE FINAL ZERO-FREE REGION** (SW brick S4b): for every `ε > 0` there is
    `c(ε) > 0` (ineffective, via Siegel) with: EVERY zero `β + iγ` of EVERY
    nontrivial Dirichlet L-function mod `N` satisfies
    `β ≤ 1 − c·N^{−ε}/(log(N(4|γ|+7)) + 20)`.
    Non-quadratic: de la Vallée-Poussin uniform. Quadratic off-axis: the
    conjugate-pair/damped-3-4-1 region. Quadratic real zeros: Siegel. -/
theorem zero_free_region_final (ε : ℝ) (hε0 : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ∀ β γ : ℝ, DirichletCharacter.LFunction χ ((β:ℂ) + γ*Complex.I) = 0 →
      β ≤ 1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*|γ|+7)) + 20) := by
  obtain ⟨C₁, hC₁1, hC₁⟩ := dvp_zero_free_uniform
  obtain ⟨C₂, hC₂1, hC₂⟩ := dvp_zero_free_uniform_quadratic
  obtain ⟨c₃, hc₃0, hc₃⟩ := siegel_zero_free ε hε0
  obtain ⟨c, hcdef⟩ : ∃ x : ℝ,
      x = min (min (1/(335*(1360+C₁))) (1/C₂)) (min (20*c₃) 1) := ⟨_, rfl⟩
  have hA0 : (0:ℝ) < 1/(335*(1360+C₁)) := by
    apply div_pos one_pos
    nlinarith [hC₁1]
  have hB0 : (0:ℝ) < 1/C₂ := by
    apply div_pos one_pos
    linarith
  have hc0 : 0 < c := by
    rw [hcdef]
    apply lt_min (lt_min hA0 hB0)
    apply lt_min (by linarith) one_pos
  refine ⟨c, hc0, ?_⟩
  intro N _ χ hχ1 β γ hzero
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hg0 : (0:ℝ) ≤ |γ| := abs_nonneg γ
  have harg1 : (1:ℝ) ≤ (N:ℝ) * (4*|γ|+7) := by nlinarith
  have hL0 : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*|γ|+7)) := Real.log_nonneg harg1
  obtain ⟨L₀, hL₀def⟩ : ∃ Lv : ℝ, Lv = Real.log ((N:ℝ)*(4*|γ|+7)) + 20 := ⟨_, rfl⟩
  rw [← hL₀def]
  have hL20 : 20 ≤ L₀ := by rw [hL₀def]; linarith
  have hNe1 : ((N:ℝ))^(-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
  have hNe0 : (0:ℝ) < ((N:ℝ))^(-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hclose : ∀ K : ℝ, c * ((N:ℝ))^(-ε) ≤ K*L₀ → β ≤ 1 - K →
      β ≤ 1 - c*((N:ℝ))^(-ε)/L₀ := by
    intro K hK hβ
    have h1 : c*((N:ℝ))^(-ε)/L₀ ≤ K := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < L₀)]
      linarith [hK]
    linarith [h1, hβ]
  by_cases hquad : χ^2 = 1
  · by_cases hγ : γ = 0
    · -- Siegel: the real zero of a quadratic character
      subst hγ
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at hzero
      by_cases hN3 : 3 ≤ N
      · have hβ1 : β < 1 := by
          by_contra hβ'
          push_neg at hβ'
          have hre : (1:ℝ) ≤ (((β:ℝ):ℂ)).re := by
            rw [Complex.ofReal_re]
            linarith
          exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hre hzero
        have h1 := hc₃ N hN3 χ hquad hχ1 β hβ1 hzero
        apply hclose (c₃ * ((N:ℝ))^(-ε)) _ h1
        have h2 : c ≤ 20*c₃ := by
          rw [hcdef]
          exact le_trans (min_le_right _ _) (min_le_left _ _)
        have h3 : 20*c₃ ≤ c₃*L₀ := by nlinarith [hc₃0, hL20]
        have h4 := mul_le_mul_of_nonneg_right (le_trans h2 h3) hNe0.le
        have h5 : (c₃*L₀)*((N:ℝ))^(-ε) = (c₃*((N:ℝ))^(-ε))*L₀ := by ring
        linarith [h4, h5.le, h5.ge]
      · -- no nontrivial character below modulus 3
        push_neg at hN3
        exfalso
        apply hχ1
        have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
        interval_cases N
        · -- N = 1
          apply MulChar.ext
          intro a
          have ha : ∀ b : (ZMod 1)ˣ, b = 1 := by decide
          rw [ha a]
          simp
        · -- N = 2
          apply MulChar.ext
          intro a
          have ha : ∀ b : (ZMod 2)ˣ, b = 1 := by decide
          rw [ha a]
          simp
    · -- quadratic, off the real axis
      have h1 := hC₂ N χ hχ1 hquad β γ hγ hzero
      rw [← hL₀def] at h1
      apply hclose (1/(C₂*L₀)) _ h1
      have h2 : c ≤ 1/C₂ := by
        rw [hcdef]
        exact le_trans (min_le_left _ _) (min_le_right _ _)
      have h3 : c*((N:ℝ))^(-ε) ≤ c := by nlinarith [hNe1, hNe0.le, hc0]
      have hC₂0 : C₂ ≠ 0 := by linarith
      have hL₀ne : L₀ ≠ 0 := by linarith
      have h4 : (1/(C₂*L₀))*L₀ = 1/C₂ := by
        field_simp
      linarith [h2, h3, h4.le, h4.ge]
  · -- non-quadratic: de la Vallée-Poussin
    have h1 := hC₁ N χ hχ1 hquad β γ hzero
    rw [← hL₀def] at h1
    apply hclose (1/(335*(1360+C₁)*L₀)) _ h1
    have h2 : c ≤ 1/(335*(1360+C₁)) := by
      rw [hcdef]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    have h3 : c*((N:ℝ))^(-ε) ≤ c := by nlinarith [hNe1, hNe0.le, hc0]
    have hden : (335:ℝ)*(1360+C₁) ≠ 0 := by nlinarith [hC₁1]
    have hL₀ne : L₀ ≠ 0 := by linarith
    have h4 : (1/(335*(1360+C₁)*L₀))*L₀ = 1/(335*(1360+C₁)) := by
      field_simp
    linarith [h2, h3, h4.le, h4.ge]

section LandauCount
open Metric

/-- **Landau with the Jensen zero count** (SW brick B1b): the `landau_LFunction`
    package plus `∑ m ≤ 2·log(N(2|t|+7)σ₀/(σ₀−1))` — everything the contour
    `L′/L` bound consumes about one center. -/
theorem landau_LFunction_count (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (σ₀ t : ℝ) (hσ₀ : 1 < σ₀) (hσ₀2 : σ₀ ≤ 2) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ S, ρ ∈ closedBall ((σ₀ : ℂ) + t * Complex.I) (1/5) ∧
        DirichletCharacter.LFunction χ ρ = 0) ∧
      (∀ ρ ∈ S, m ρ = analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) ∧
      (∀ ρ ∈ closedBall ((σ₀ : ℂ) + t * Complex.I) (1/5),
        DirichletCharacter.LFunction χ ρ = 0 → ρ ∈ S) ∧
      (∀ ρ ∈ S, 1 ≤ m ρ) ∧
      ((∑ ρ ∈ S, (m ρ : ℝ)) ≤ 2 * Real.log ((N : ℝ) * (2 * |t| + 7) * σ₀ / (σ₀ - 1))) ∧
      ∀ z ∈ ball ((σ₀ : ℂ) + t * Complex.I) (1/20), (∀ ρ ∈ S, z ≠ ρ) →
        ‖logDeriv (DirichletCharacter.LFunction χ) z - ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖
          ≤ 40 * (Real.log ((N : ℝ) * (2 * |t| + 7) * σ₀ / (σ₀ - 1)) + 1) := by
  obtain ⟨S, m, hSz, hm, hcomp, hmpos, hbound⟩ := landau_LFunction N χ hχ σ₀ t hσ₀ hσ₀2
  refine ⟨S, m, hSz, hm, hcomp, hmpos, ?_, hbound⟩
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  set c : ℂ := (σ₀ : ℂ) + t * Complex.I with hc
  have hcre : c.re = σ₀ := by rw [hc]; simp
  have hcnorm : ‖c‖ ≤ σ₀ + |t| := by
    rw [hc]
    calc ‖(σ₀:ℂ) + t*Complex.I‖ ≤ ‖(σ₀:ℂ)‖ + ‖(t:ℂ)*Complex.I‖ := norm_add_le _ _
      _ = |σ₀| + |t| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
          simp [Real.norm_eq_abs]
      _ = σ₀ + |t| := by rw [abs_of_pos (by linarith)]
  -- the anchor: f c ≠ 0 with a quantitative lower bound
  have hanchor := LFunction_anchor_quantitative N χ c (by rw [hcre]; exact hσ₀)
  rw [hcre] at hanchor
  have hml0 : (0:ℝ) < (σ₀-1)/σ₀ := by
    apply div_pos <;> linarith
  have hfc0 : DirichletCharacter.LFunction χ c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hanchor
    linarith
  -- the sphere bound at radius 2/5
  have hM1 : (1:ℝ) ≤ (N:ℝ) * (2*|t|+7) := by nlinarith [abs_nonneg t]
  have hfbound : ∀ z ∈ sphere c (2/5),
      ‖DirichletCharacter.LFunction χ z‖ ≤ (N:ℝ) * (2*|t|+7) := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    have hzre : (3:ℝ)/5 ≤ z.re := by
      have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
      rw [hz] at h1
      have h2 := (abs_le.mp h1).1
      rw [Complex.sub_re, hcre] at h2
      linarith
    have hznorm : ‖z‖ ≤ |t| + 12/5 := by
      calc ‖z‖ = ‖c + (z - c)‖ := by ring_nf
        _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
        _ = ‖c‖ + 2/5 := by rw [hz]
        _ ≤ (σ₀ + |t|) + 2/5 := by linarith [hcnorm]
        _ ≤ |t| + 12/5 := by linarith
    have h3 := LFunction_window_bound N χ hχ (3/5) (|t| + 12/5) (by norm_num)
      (by positivity) z hzre hznorm
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ (N:ℝ) * (2 + (|t| + 12/5)/(3/5)) := h3
      _ ≤ (N:ℝ) * (2*|t|+7) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have h6 : (|t| + 12/5)/((3:ℝ)/5) = (5/3)*|t| + 4 := by ring
          linarith [abs_nonneg t, h6.le, h6.ge]
  -- Jensen
  have hanal : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (closedBall c (2/5)) :=
    fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hjensen := sum_m_le_jensen (DirichletCharacter.LFunction χ) c (1/5) (2/5)
    ((N:ℝ) * (2*|t|+7)) (by norm_num) (by norm_num) hM1 hanal hfc0 hfbound S m hSz hm
  -- massage the bound
  have hlog2 : Real.log ((2:ℝ)/5 / (1/5)) = Real.log 2 := by norm_num
  rw [hlog2] at hjensen
  have hl2 : (1:ℝ)/2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hfcpos : (0:ℝ) < ‖DirichletCharacter.LFunction χ c‖ := by
    have := norm_nonneg (DirichletCharacter.LFunction χ c)
    rcases lt_or_eq_of_le this with h | h
    · exact h
    · exact absurd (norm_eq_zero.mp h.symm) hfc0
  have hargpos : (0:ℝ) < (N:ℝ) * (2*|t|+7) * σ₀ / (σ₀-1) := by
    apply div_pos (by nlinarith [abs_nonneg t]) (by linarith)
  have hlogmono : Real.log ((N:ℝ) * (2*|t|+7) / ‖DirichletCharacter.LFunction χ c‖)
      ≤ Real.log ((N:ℝ) * (2*|t|+7) * σ₀ / (σ₀-1)) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hfcpos (by linarith : (0:ℝ) < σ₀-1)]
    have h4 : (σ₀-1)/σ₀ * σ₀ = σ₀ - 1 := by
      field_simp
    have h5 := mul_le_mul_of_nonneg_left hanchor
      (by nlinarith [abs_nonneg t] : (0:ℝ) ≤ (N:ℝ) * (2*|t|+7) * σ₀)
    nlinarith [h5, h4.le, h4.ge, hfcpos, hanchor, hml0]
  have hlogpos : (0:ℝ) ≤ Real.log ((N:ℝ) * (2*|t|+7) * σ₀ / (σ₀-1)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith : (0:ℝ) < σ₀-1)]
    nlinarith [abs_nonneg t]
  calc (∑ ρ ∈ S, (m ρ : ℝ))
      ≤ Real.log ((N:ℝ) * (2*|t|+7) / ‖DirichletCharacter.LFunction χ c‖) / Real.log 2 :=
        hjensen
    _ ≤ Real.log ((N:ℝ) * (2*|t|+7) * σ₀ / (σ₀-1)) / Real.log 2 := by
        rw [div_le_div_iff₀ (by linarith : (0:ℝ) < Real.log 2)
          (by linarith : (0:ℝ) < Real.log 2)]
        nlinarith [hlogmono, hl2]
    _ ≤ 2 * Real.log ((N:ℝ) * (2*|t|+7) * σ₀ / (σ₀-1)) := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.log 2)]
        nlinarith [hlogpos, hl2]

end LandauCount

set_option maxHeartbeats 1000000
open DirichletCharacter Complex Metric




/-- **Contour-to-zero distance** (SW brick B1a): with the final zero-free region's
    `c(ε)`, write `g := c·N^{−ε}/(log(N(4(T+1)+7))+20)` for the height-`T` window gap.
    Every point `s` with `|Im s| ≤ T` and `Re s ≥ 1 − g/2` keeps distance `≥ g/2`
    from every zero of `L(·,χ)` within `‖s − ρ‖ ≤ 1` — the input to the contour
    `L′/L` bound. -/
theorem contour_zero_distance (ε : ℝ) (hε0 : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    ∀ T : ℝ, 0 ≤ T → ∀ s : ℂ, |s.im| ≤ T →
    1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2 ≤ s.re →
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖s - ρ‖ ≤ 1 →
    c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2 ≤ ‖s - ρ‖ := by
  obtain ⟨c, hc0, hc⟩ := zero_free_region_final ε hε0
  refine ⟨c, hc0, ?_⟩
  intro N _ χ hχ1 T hT0 s hsim hsre ρ hρz hρnear
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hρform : ((ρ.re : ℝ) : ℂ) + (ρ.im : ℝ) * Complex.I = ρ := Complex.re_add_im ρ
  have hzero' : DirichletCharacter.LFunction χ (((ρ.re : ℝ) : ℂ)
      + (ρ.im : ℝ) * Complex.I) = 0 := by
    rw [hρform]
    exact hρz
  have h1 := hc N χ hχ1 ρ.re ρ.im hzero'
  have him : |ρ.im| ≤ T + 1 := by
    have h2 : |ρ.im - s.im| ≤ ‖ρ - s‖ := by
      have h3 : (ρ - s).im = ρ.im - s.im := by rw [Complex.sub_im]
      rw [← h3]
      exact Complex.abs_im_le_norm _
    have h4 : ‖ρ - s‖ = ‖s - ρ‖ := by
      rw [← norm_neg]
      congr 1
      ring
    have h5 := abs_sub_abs_le_abs_sub ρ.im s.im
    linarith [h2, h4.le, h4.ge, hsim, hρnear, h5]
  obtain ⟨LT, hLTdef⟩ : ∃ x : ℝ, x = Real.log ((N:ℝ)*(4*(T+1)+7)) + 20 := ⟨_, rfl⟩
  obtain ⟨Lρ, hLρdef⟩ : ∃ x : ℝ, x = Real.log ((N:ℝ)*(4*|ρ.im|+7)) + 20 := ⟨_, rfl⟩
  rw [← hLTdef] at hsre ⊢
  rw [← hLρdef] at h1
  have hg0' : (0:ℝ) ≤ |ρ.im| := abs_nonneg _
  have hLρ20 : 20 ≤ Lρ := by
    rw [hLρdef]
    have : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*|ρ.im|+7)) :=
      Real.log_nonneg (by nlinarith)
    linarith
  have hLT20 : 20 ≤ LT := by
    rw [hLTdef]
    have : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*(T+1)+7)) :=
      Real.log_nonneg (by nlinarith)
    linarith
  have hLmono : Lρ ≤ LT := by
    rw [hLρdef, hLTdef]
    have h6 : (N:ℝ)*(4*|ρ.im|+7) ≤ (N:ℝ)*(4*(T+1)+7) := by nlinarith [him, hN1r]
    have h7 := Real.log_le_log (by nlinarith : (0:ℝ) < (N:ℝ)*(4*|ρ.im|+7)) h6
    linarith
  have hNe0 : (0:ℝ) < ((N:ℝ))^(-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hgap : c * ((N:ℝ))^(-ε) / LT ≤ c * ((N:ℝ))^(-ε) / Lρ := by
    apply div_le_div_of_nonneg_left (by positivity) (by linarith) hLmono
  have hre : s.re - ρ.re ≤ ‖s - ρ‖ := by
    have h8 : (s - ρ).re = s.re - ρ.re := by rw [Complex.sub_re]
    calc s.re - ρ.re = (s - ρ).re := h8.symm
      _ ≤ |(s - ρ).re| := le_abs_self _
      _ ≤ ‖s - ρ‖ := Complex.abs_re_le_norm _
  linarith [h1, hgap, hre, hsre]

set_option maxHeartbeats 2000000 in
/-- **The contour `L′/L` bound** (SW brick B1c): with `c(ε)` from the zero-free
    region and `L_T := log(N(4(T+1)+7))+20`, every `s` in the strip
    `1 − g/2 ≤ Re s ≤ 1 + g`, `|Im s| ≤ T` (`g := c·N^{−ε}/L_T`) has
    `‖L′/L(s,χ)‖ ≤ C(ε)·N^ε·L_T²` — Landau partial fractions at `1+g+i·Im s`,
    every zero at distance `≥ g/2`, at most `2·log` zeros. -/
theorem contour_logDeriv_bound (ε : ℝ) (hε0 : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 1 ≤ C ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    ∀ T : ℝ, 0 ≤ T → ∀ s : ℂ, |s.im| ≤ T →
    1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2 ≤ s.re →
    s.re ≤ 1 + c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) →
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖
      ≤ C * ((N:ℝ))^ε * (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)^2 := by
  obtain ⟨c₀, hc₀0, hc₀⟩ := contour_zero_distance ε hε0
  obtain ⟨c, hcdef⟩ : ∃ x : ℝ, x = min c₀ (1/2) := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hcdef]
    exact lt_min hc₀0 (by norm_num)
  have hc12 : c ≤ 1/2 := by rw [hcdef]; exact min_le_right _ _
  have hcc₀ : c ≤ c₀ := by rw [hcdef]; exact min_le_left _ _
  have hlogc0 : 0 ≤ Real.log (1/c) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hc0]
    linarith
  obtain ⟨Kc, hKcdef⟩ : ∃ x : ℝ, x = 3 + ε + Real.log (1/c) := ⟨_, rfl⟩
  have hKc3 : 3 ≤ Kc := by rw [hKcdef]; linarith
  obtain ⟨C, hCdef⟩ : ∃ x : ℝ, x = 4*Kc/c + 80*Kc := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := by
    rw [hCdef]
    have h1 : (0:ℝ) ≤ 4*Kc/c := by positivity
    linarith [hKc3]
  refine ⟨c, C, hc0, hc12, hC1, ?_⟩
  intro N _ χ hχ1 T hT0 s hsim hsre1 hsre2
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hNe0 : (0:ℝ) < ((N:ℝ))^(-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hNe1 : ((N:ℝ))^(-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
  have hNp1 : (1:ℝ) ≤ ((N:ℝ))^ε :=
    Real.one_le_rpow hN1r (by linarith)
  have hNcancel : ((N:ℝ))^(-ε) * ((N:ℝ))^ε = 1 := by
    rw [← Real.rpow_add (by linarith : (0:ℝ) < (N:ℝ))]
    simp
  obtain ⟨LT, hLTdef⟩ : ∃ x : ℝ, x = Real.log ((N:ℝ)*(4*(T+1)+7)) + 20 := ⟨_, rfl⟩
  rw [← hLTdef] at hsre1 hsre2 ⊢
  have hargT1 : (1:ℝ) ≤ (N:ℝ)*(4*(T+1)+7) := by nlinarith
  have hLT20 : 20 ≤ LT := by
    rw [hLTdef]
    have := Real.log_nonneg hargT1
    linarith
  obtain ⟨g, hgdef⟩ : ∃ x : ℝ, x = c * ((N:ℝ))^(-ε) / LT := ⟨_, rfl⟩
  rw [← hgdef] at hsre1 hsre2
  have hg0 : 0 < g := by
    rw [hgdef]
    positivity
  have hg40 : g ≤ 1/40 := by
    rw [hgdef, div_le_iff₀ (by linarith : (0:ℝ) < LT)]
    nlinarith [hNe1, hNe0.le, hc12, hLT20, hc0]
  -- Landau at the center 1+g + i·Im s
  obtain ⟨S, m, hSz, hm, hcomp, hmpos, hcount, hbound⟩ :=
    landau_LFunction_count N χ hχ1 (1+g) s.im (by linarith) (by linarith)
  have hs1g : (1 + g) - 1 = g := by ring
  rw [hs1g] at hcount hbound
  -- s is in the evaluation ball
  have hsc : ‖s - (((1+g : ℝ) : ℂ) + s.im * Complex.I)‖ = |s.re - (1+g)| := by
    have h1 : s - (((1+g : ℝ) : ℂ) + s.im * Complex.I)
        = ((s.re - (1+g) : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
      · simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
  have hsc20 : ‖s - (((1+g : ℝ) : ℂ) + s.im * Complex.I)‖ ≤ 3/80 := by
    rw [hsc, abs_le]
    constructor <;> nlinarith [hsre1, hsre2, hg0, hg40]
  have hsball : s ∈ ball (((1+g : ℝ) : ℂ) + s.im * Complex.I) (1/20) := by
    rw [mem_ball, dist_eq_norm]
    calc ‖s - (((1+g : ℝ) : ℂ) + s.im * Complex.I)‖ ≤ 3/80 := hsc20
      _ < 1/20 := by norm_num
  -- every Landau zero keeps distance ≥ g/2
  have hsre1' : 1 - c₀ * ((N:ℝ))^(-ε)
      / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2 ≤ s.re := by
    rw [← hLTdef]
    have h3 : c * ((N:ℝ))^(-ε) / LT ≤ c₀ * ((N:ℝ))^(-ε) / LT := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < LT) (by linarith : (0:ℝ) < LT)]
      have h4 := mul_le_mul_of_nonneg_right hcc₀ hNe0.le
      nlinarith [h4, hLT20]
    linarith [hsre1, h3, hgdef.le, hgdef.ge]
  have hdist : ∀ ρ ∈ S, g/2 ≤ ‖s - ρ‖ := by
    intro ρ hρ
    obtain ⟨hρball, hρzero⟩ := hSz ρ hρ
    rw [mem_closedBall, dist_eq_norm] at hρball
    have h1 : ‖s - ρ‖ ≤ 1 := by
      have h1b : ‖(((1+g : ℝ) : ℂ) + s.im * Complex.I) - ρ‖ ≤ 1/5 := by
        rw [norm_sub_rev]
        exact hρball
      calc ‖s - ρ‖ = ‖(s - (((1+g : ℝ) : ℂ) + s.im * Complex.I))
            + ((((1+g : ℝ) : ℂ) + s.im * Complex.I) - ρ)‖ := by ring_nf
        _ ≤ ‖s - (((1+g : ℝ) : ℂ) + s.im * Complex.I)‖
            + ‖(((1+g : ℝ) : ℂ) + s.im * Complex.I) - ρ‖ := norm_add_le _ _
        _ ≤ 3/80 + 1/5 := by linarith [hsc20, h1b]
        _ ≤ 1 := by norm_num
    have h2 := hc₀ N χ hχ1 T hT0 s hsim hsre1' ρ hρzero h1
    rw [← hLTdef] at h2
    have h3 : c * ((N:ℝ))^(-ε) / LT ≤ c₀ * ((N:ℝ))^(-ε) / LT := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < LT) (by linarith : (0:ℝ) < LT)]
      have h4 := mul_le_mul_of_nonneg_right hcc₀ hNe0.le
      nlinarith [h4, hLT20]
    rw [hgdef]
    linarith [h2, h3]
  have hzS : ∀ ρ ∈ S, s ≠ ρ := by
    intro ρ hρ heq
    have h5 := hdist ρ hρ
    rw [heq, sub_self, norm_zero] at h5
    linarith [hg0]
  have hb := hbound s hsball hzS
  -- the partial-fraction sum
  have hsum : ‖∑ ρ ∈ S, ((m ρ : ℂ)) / (s - ρ)‖ ≤ (∑ ρ ∈ S, (m ρ : ℝ)) * (2/g) := by
    calc ‖∑ ρ ∈ S, ((m ρ : ℂ)) / (s - ρ)‖ ≤ ∑ ρ ∈ S, ‖((m ρ : ℂ)) / (s - ρ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ ρ ∈ S, (m ρ : ℝ) * (2/g) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          rw [norm_div, Complex.norm_natCast]
          have h5 := hdist ρ hρ
          have h6 : (0:ℝ) < ‖s - ρ‖ := by linarith [hg0]
          rw [div_le_iff₀ h6]
          have h7 := mul_le_mul_of_nonneg_left h5
            (by positivity : (0:ℝ) ≤ (m ρ : ℝ) * (2/g))
          have h8 : (m ρ : ℝ) * (2/g) * (g/2) = (m ρ : ℝ) := by
            field_simp
          linarith [h7, h8.le, h8.ge]
      _ = (∑ ρ ∈ S, (m ρ : ℝ)) * (2/g) := by
          rw [← Finset.sum_mul]
  -- the log-argument bound
  have hg1 : (1:ℝ)/g = LT * ((N:ℝ))^ε / c := by
    have h9 : g * (LT * ((N:ℝ))^ε / c) = 1 := by
      rw [hgdef]
      calc c * ((N:ℝ))^(-ε) / LT * (LT * ((N:ℝ))^ε / c)
          = (((N:ℝ))^(-ε) * ((N:ℝ))^ε) * ((c/c) * (LT/LT)) := by ring
        _ = 1 := by
            rw [hNcancel, div_self (ne_of_gt hc0),
              div_self (by linarith : LT ≠ 0)]
            norm_num
    rw [div_eq_iff (ne_of_gt hg0)]
    linarith [h9]
  have hlog1g : Real.log (1/g) ≤ (1+ε)*LT + Real.log (1/c) := by
    rw [hg1]
    have hNlog : Real.log ((N:ℝ)) ≤ LT - 20 := by
      rw [hLTdef]
      have h11 : (N:ℝ) ≤ (N:ℝ)*(4*(T+1)+7) := by nlinarith
      have h12 := Real.log_le_log (by linarith : (0:ℝ) < (N:ℝ)) h11
      linarith
    have hLTlog : Real.log LT ≤ LT - 1 :=
      Real.log_le_sub_one_of_pos (by linarith)
    calc Real.log (LT * ((N:ℝ))^ε / c)
        = Real.log (LT * ((N:ℝ))^ε) - Real.log c := by
          rw [Real.log_div (by positivity) (ne_of_gt hc0)]
      _ = Real.log LT + ε * Real.log ((N:ℝ)) - Real.log c := by
          rw [Real.log_mul (by linarith : LT ≠ 0) (by positivity),
            Real.log_rpow (by linarith : (0:ℝ) < (N:ℝ))]
      _ ≤ (LT - 1) + ε * (LT - 20) - Real.log c := by
          have h13 := mul_le_mul_of_nonneg_left hNlog (le_of_lt hε0)
          linarith [hLTlog, h13]
      _ ≤ (1+ε)*LT + Real.log (1/c) := by
          have h14 : Real.log (1/c) = - Real.log c := by
            rw [one_div, Real.log_inv]
          nlinarith [hε0, h14.le, h14.ge, hLT20]
  have hA : Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g) ≤ Kc * LT := by
    have h15 : (N:ℝ)*(2*|s.im|+7)*(1+g)/g ≤ (2*((N:ℝ)*(4*(T+1)+7))) * (1/g) := by
      rw [div_le_iff₀ hg0]
      have h16 : (2*|s.im|+7)*(1+g) ≤ 2*(4*(T+1)+7) := by
        nlinarith [hsim, hg40, hg0, abs_nonneg s.im, hT0]
      have h17 : (N:ℝ)*(2*|s.im|+7)*(1+g) ≤ 2*((N:ℝ)*(4*(T+1)+7)) := by
        nlinarith [h16, hN1r, abs_nonneg s.im, hg0]
      have h18 : (1:ℝ)/g * g = 1 := by field_simp
      nlinarith [h17, h18, hg0]
    calc Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g)
        ≤ Real.log ((2*((N:ℝ)*(4*(T+1)+7))) * (1/g)) := by
          apply Real.log_le_log _ h15
          apply div_pos _ hg0
          exact mul_pos (mul_pos (by linarith : (0:ℝ) < (N:ℝ))
            (by nlinarith [abs_nonneg s.im] : (0:ℝ) < 2*|s.im|+7))
            (by linarith [hg0] : (0:ℝ) < 1+g)
      _ = Real.log 2 + Real.log ((N:ℝ)*(4*(T+1)+7)) + Real.log (1/g) := by
          rw [Real.log_mul (by nlinarith) (by positivity),
            Real.log_mul (by norm_num) (by nlinarith)]
      _ ≤ 1 + (LT - 20) + ((1+ε)*LT + Real.log (1/c)) := by
          have hlog2le : Real.log 2 ≤ 1 := by
            rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
            apply Real.log_le_log (by norm_num)
            have := Real.exp_one_gt_d9
            linarith
          have h19 : Real.log ((N:ℝ)*(4*(T+1)+7)) = LT - 20 := by
            rw [hLTdef]
            ring
          linarith [hlog2le, h19.le, h19.ge, hlog1g]
      _ ≤ Kc * LT := by
          rw [hKcdef]
          have h20 : Real.log (1/c) * 1 ≤ Real.log (1/c) * LT :=
            mul_le_mul_of_nonneg_left (by linarith) hlogc0
          nlinarith [hLT20, hε0, h20]
  have hA0 : (0:ℝ) ≤ Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hg0]
    have p1 : (7:ℝ) ≤ (2*|s.im|+7) := by linarith [abs_nonneg s.im]
    have p2 : (1:ℝ) ≤ 1+g := by linarith
    have p3 : (7:ℝ) ≤ (N:ℝ)*(2*|s.im|+7) := by nlinarith [hN1r, p1]
    have p4 : (7:ℝ) ≤ (N:ℝ)*(2*|s.im|+7)*(1+g) := by nlinarith [p3, p2]
    linarith [p4, hg40, hg0]
  -- assemble
  have htri : ‖logDeriv (DirichletCharacter.LFunction χ) s‖
      ≤ (∑ ρ ∈ S, (m ρ : ℝ)) * (2/g)
        + 40 * (Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g) + 1) := by
    calc ‖logDeriv (DirichletCharacter.LFunction χ) s‖
        = ‖(logDeriv (DirichletCharacter.LFunction χ) s
            - ∑ ρ ∈ S, ((m ρ : ℂ)) / (s - ρ)) + ∑ ρ ∈ S, ((m ρ : ℂ)) / (s - ρ)‖ := by
          congr 1
          ring
      _ ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s
            - ∑ ρ ∈ S, ((m ρ : ℂ)) / (s - ρ)‖ + ‖∑ ρ ∈ S, ((m ρ : ℂ)) / (s - ρ)‖ :=
          norm_add_le _ _
      _ ≤ (∑ ρ ∈ S, (m ρ : ℝ)) * (2/g)
            + 40 * (Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g) + 1) := by
          linarith [hb, hsum]
  have hsumA : (∑ ρ ∈ S, (m ρ : ℝ)) * (2/g)
      ≤ (4*Kc/c) * ((N:ℝ))^ε * LT^2 := by
    have h21 : (∑ ρ ∈ S, (m ρ : ℝ)) * (2/g)
        ≤ (2 * Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g)) * (2/g) := by
      apply mul_le_mul_of_nonneg_right hcount (by positivity)
    have h22 : (2 * Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g)) * (2/g)
        ≤ (2 * (Kc * LT)) * (2/g) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith [hA]
    have h23 : (2 * (Kc * LT)) * (2/g) = 4*Kc*LT*(1/g) := by ring
    have h24 : 4*Kc*LT*(1/g) = (4*Kc/c) * ((N:ℝ))^ε * LT^2 := by
      rw [hg1]
      ring
    linarith [h21, h22, h23.le, h23.ge, h24.le, h24.ge]
  have h40A : 40 * (Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g) + 1)
      ≤ 80*Kc * ((N:ℝ))^ε * LT^2 := by
    have h25 : 40 * (Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g) + 1)
        ≤ 40 * (Kc*LT) + 40 := by linarith [hA]
    have h26 : (40:ℝ) ≤ 40 * (Kc*LT) := by nlinarith [hKc3, hLT20]
    have h27 : 80 * (Kc*LT) ≤ 80*Kc*LT^2 := by nlinarith [hKc3, hLT20]
    have h28 : 80*Kc*LT^2 ≤ 80*Kc*LT^2 * ((N:ℝ))^ε := by
      nlinarith [hNp1, hKc3, hLT20]
    have h29 : 80*Kc*LT^2 * ((N:ℝ))^ε = 80*Kc * ((N:ℝ))^ε * LT^2 := by ring
    linarith [h25, h26, h27, h28, h29.le, h29.ge]
  have hCexp : C * ((N:ℝ))^ε * LT^2
      = (4*Kc/c) * ((N:ℝ))^ε * LT^2 + 80*Kc * ((N:ℝ))^ε * LT^2 := by
    rw [hCdef]
    ring
  linarith [htri, hsumA, h40A, hCexp.le, hCexp.ge]

open Finset in
open scoped ArithmeticFunction in
/-- **Character orthogonality for the AP prime-counting sum** (SW brick B5a): for a
    unit residue `a` mod `q`, exactly
    `φ(q)·∑_{n<X, n≡a} Λ(n) = ∑_χ χ(a⁻¹)·∑_{n<X} χ(n)Λ(n)` — the bridge from the
    twisted sums `ψ(X,χ)` to primes in the progression. EXACT identity: terms with
    `gcd(n,q) > 1` vanish on both sides. -/
theorem psi_ap_orthogonality (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (X : ℕ) :
    (q.totient : ℂ) * (∑ n ∈ Finset.range X,
        if a = ((n : ZMod q)) then ((Λ n : ℝ) : ℂ) else 0)
      = ∑ χ : DirichletCharacter ℂ q, (χ a⁻¹) *
          (∑ n ∈ Finset.range X, χ ((n : ZMod q)) * ((Λ n : ℝ) : ℂ)) := by
  symm
  calc ∑ χ : DirichletCharacter ℂ q, (χ a⁻¹) *
      (∑ n ∈ Finset.range X, χ ((n : ZMod q)) * ((Λ n : ℝ) : ℂ))
      = ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.range X,
          (χ a⁻¹ * χ ((n : ZMod q))) * ((Λ n : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro χ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ = ∑ n ∈ Finset.range X, ∑ χ : DirichletCharacter ℂ q,
          (χ a⁻¹ * χ ((n : ZMod q))) * ((Λ n : ℝ) : ℂ) := Finset.sum_comm
    _ = ∑ n ∈ Finset.range X,
          (if a = ((n : ZMod q)) then (q.totient : ℂ) else 0) * ((Λ n : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [← Finset.sum_mul,
          DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) ha ((n : ZMod q))]
    _ = (q.totient : ℂ) * (∑ n ∈ Finset.range X,
          if a = ((n : ZMod q)) then ((Λ n : ℝ) : ℂ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        split_ifs
        · ring
        · ring

/-- **−L′/L(χ) as the χ·Λ Dirichlet series** (SW Perron input, brick B2a): for `Re s > 1`, the
    negative logarithmic derivative of `LFunction χ` equals `∑_n χ(n)Λ(n) n^{-s}`. Bridges the contour
    `logDeriv` bounds (`contour_logDeriv_bound`, stated for `LFunction χ`) to the Perron integrand
    (the twisted von-Mangoldt series). Mathlib `deriv_LFunction_eq_deriv_LSeries` +
    `LFunction_eq_LSeries` + `LSeries_twist_vonMangoldt_eq`. (`↗` avoided — `open Metric` shadows the
    `scoped[LSeries.notation]` arrow.) -/
lemma neg_logDeriv_LFunction_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
      = LSeries (fun n : ℕ => χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s := by
  rw [deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs]
  exact (LSeries_twist_vonMangoldt_eq χ hs).symm

/-- **`LFunction χ` is entire for `χ ≠ 1`** (SW brick B3 input): no poles inside the contour
    rectangle. Mathlib `differentiable_LFunction`. -/
lemma LFunction_entire {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    Differentiable ℂ (DirichletCharacter.LFunction χ) :=
  differentiable_LFunction hχ

/-- **`LFunction χ` has no zeros on `Re s ≥ 1` for `χ ≠ 1`** (SW brick B3 input): the contour's
    right edge `Re = σ₀ > 1` (and the boundary `Re = 1`) is zero-free, so `L′/L` is holomorphic there.
    Mathlib `LFunction_ne_zero_of_one_le_re`. -/
lemma LFunction_ne_zero_re_ge_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 ≤ s.re) : DirichletCharacter.LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs


/-- **Perron-integrand reshape** (SW brick W1j): `(−L′/L · X^s)/(s(s+1)) = −L′/L · (X^s/(s(s+1)))`
    under the integral — aligns `smoothed_perron_LFunction`'s form with the `G`-form used by every
    W1 estimate lemma (`mul_div_assoc` under `funext`). -/
lemma perron_integrand_reshape {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (X σ : ℝ) :
    (∫ t : ℝ, (-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ:ℂ) + t * I))
        * (X:ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1)))
      = ∫ t : ℝ, (-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ:ℂ) + t * I))
        * ((X:ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1))) := by
  congr 1
  funext t
  rw [mul_div_assoc]

end Principia.Common.SW
