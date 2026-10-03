/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.SW.Perron

/-!
# Siegel–Walfisz, `Rate`: the per-character rate, the sharp twisted-psi bound, Siegel-Walfisz

Ported **verbatim** from the axiom-clean Siegel–Walfisz master
(`Principia Application/LeanSandbox/SiegelWalfiszMaster.lean` = `C:/Users/Christian/pnt/sw_full.lean`,
lines 14033–15806; there `#print axioms siegel_walfisz_proven = [propext, Classical.choice, Quot.sound]`,
built in the PrimeNumberTheoremAnd workspace on Mathlib `db127794`, one day from ours). The master
imported `Mathlib`, `PrimeNumberTheoremAnd.MediumPNT` and `PrimeNumberTheoremAnd.PerronFormula`; here
the Mathlib imports are narrowed, the two Perron-kernel shims are re-proved from Mathlib's Mellin
inversion (`Principia.Common.SW.PerronKernel`), and the `medium_PNT` shim is not ported (see
`MediumPNTBound` in `Principia.Common.SW.Rate`). Declarations live in `Principia.Common.SW`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DirichletCharacter Complex PowerSeries ArithmeticFunction Finset Filter Metric MeasureTheory

namespace Principia.Common.SW

set_option maxHeartbeats 1000000
open DirichletCharacter Complex Metric MeasureTheory


















/-- **The χ≠1 smoothed ψ bound** (W1 MAIN): for every nontrivial character, the smoothed sum obeys
    `‖ψ_smooth(X,χ)‖ ≤ (6M·X^{1−g/2} + 2·(3g/2)·M·X^{1+g}/T² + 2B·X^{1+g}/T)/(2π)` with
    `g = c·N^{−ε}/L_T`, `M = C·N^ε·L_T²`. All five skeleton hypotheses discharged. -/
theorem psi_smooth_bound_chi_ne_one (ε : ℝ) (hε0 : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 1 ≤ C ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    ∀ X : ℝ, 1 < X → ∀ T : ℝ, 0 < T →
    ∃ B : ℝ, 0 ≤ B ∧
    ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X)‖
      ≤ (6 * (C * ((N:ℝ))^ε * (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)^2)
            * X ^ (1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2)
          + 2 * (((1 + c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20))
                - (1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2))
              * ((C * ((N:ℝ))^ε * (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)^2)
                * X ^ (1 + c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)) / T ^ 2))
          + 2 * (B * X ^ (1 + c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20))) / T)
        / (2 * Real.pi) := by
  obtain ⟨c, C, hc0, hc12, hC1, hcc⟩ := contour_combined ε hε0
  refine ⟨c, C, hc0, hc12, hC1, ?_⟩
  intro N _ χ hχ X hX T hT
  have hX0 : (0:ℝ) < X := by linarith
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hNe0 : (0:ℝ) < ((N:ℝ))^(-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hNe1 : ((N:ℝ))^(-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
  have hNp1 : (1:ℝ) ≤ ((N:ℝ))^ε := Real.one_le_rpow hN1r (by linarith)
  set LT := Real.log ((N:ℝ)*(4*(T+1)+7)) + 20 with hLTdef
  have hLT20 : (20:ℝ) ≤ LT := by
    rw [hLTdef]
    have : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*(T+1)+7)) := Real.log_nonneg (by nlinarith)
    linarith
  obtain ⟨hg0, hg40, hσ'34, hσ1, hσ'σ, hσ2⟩ :=
    strip_numerics c (((N:ℝ))^(-ε)) LT hc0 hc12 hNe0 hNe1 hLT20
  set g := c * ((N:ℝ))^(-ε) / LT with hgdef
  set σ' := 1 - g / 2 with hσ'def
  set σ := 1 + g with hσdef
  set M := C * ((N:ℝ))^ε * LT^2 with hMdef
  have hM0 : (0:ℝ) ≤ M := by rw [hMdef]; positivity
  -- the contour_combined data in strip_point_M_bound's hcc shape
  have hccM : ∀ s : ℂ, |s.im| ≤ T → σ' ≤ s.re → s.re ≤ σ →
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ M := by
    intro s him hre1 hre2
    exact ((hcc N χ hχ T hT.le s him hre1).2 hre2)
  have hzf : ∀ s : ℂ, |s.im| ≤ T → σ' ≤ s.re → DirichletCharacter.LFunction χ s ≠ 0 := by
    intro s him hre
    exact (hcc N χ hχ T hT.le s him hre).1
  -- B from the σ-line tail
  obtain ⟨B, hB0, hBt⟩ := sigma_line_tail_bound χ X σ hX0 hσ1
  refine ⟨B, hB0, ?_⟩
  -- the five skeleton hypotheses
  have hrep : (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
      χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X))
      = (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, G' χ X ((σ : ℂ) + t * I) := by
    rw [smoothed_perron_LFunction χ X hX σ hσ1, perron_integrand_reshape]
    rfl
  have htail : ‖(∫ t : ℝ, G' χ X ((σ : ℂ) + t * I))
      - ∫ t in (-T)..T, G' χ X ((σ : ℂ) + t * I)‖ ≤ 2 * (B * X ^ σ) / T :=
    truncation_tail_bound _ (integrand_integrable_on_line χ hχ X hX0 σ hσ1)
      (B * X ^ σ) T hT (fun t ht => hBt t ht)
  have hMseg : ∀ tt : ℝ, |tt| ≤ T → ∀ x ∈ Set.uIcc σ' σ,
      ‖-deriv (DirichletCharacter.LFunction χ) ((x:ℂ) + tt * I) / DirichletCharacter.LFunction χ ((x:ℂ) + tt * I)‖ ≤ M := by
    intro tt httT x hx
    rw [Set.uIcc_of_le hσ'σ] at hx
    exact strip_point_M_bound χ M T σ' σ hccM x tt hx.1 hx.2 httT
  have hconnT : ‖∫ x in σ'..σ, G' χ X ((x:ℂ) + ((T : ℝ) : ℂ) * I)‖
      ≤ (σ - σ') * (M * X ^ σ / T ^ 2) :=
    horizontal_connector_bound χ X hX.le σ' σ T M hσ'σ hT.ne' hM0
      (hMseg T (by rw [abs_of_pos hT]))
  have hconnB : ‖∫ x in σ'..σ, G' χ X ((x:ℂ) + ((-T : ℝ) : ℂ) * I)‖
      ≤ (σ - σ') * (M * X ^ σ / T ^ 2) := by
    have hb := horizontal_connector_bound χ X hX.le σ' σ (-T) M hσ'σ
      (by simpa using hT.ne') hM0 (hMseg (-T) (by rw [abs_neg, abs_of_pos hT]))
    rwa [neg_sq] at hb
  have hline : ‖∫ y in (-T)..T, G' χ X ((σ':ℂ) + (y:ℂ) * I)‖ ≤ 6 * M * X ^ σ' := by
    apply shifted_line_integral_bound _ M (X ^ σ') σ' T hM0 (Real.rpow_nonneg hX0.le _) hσ'34 hT.le
    intro t ht
    have htT : |t| ≤ T := by
      rw [abs_le]
      exact ⟨ht.1.le, ht.2⟩
    exact integrand_pointwise_bound χ X σ' t M hX0 (by linarith) hM0
      (strip_point_M_bound χ M T σ' σ hccM σ' t le_rfl hσ'σ htT)
  exact psi_smooth_bound_skeleton χ hχ _ X hX σ' σ T M B hσ'34 hσ'σ hT hM0
    hrep htail hconnT hconnB hline hzf



open ArithmeticFunction in
/-- **Quantitative −L′/L on the σ-line** (SW brick W2a′): `‖−L′/L(σ+it,χ)‖ ≤ 6/(σ−1)²` for
    `1 < σ ≤ 2` — makes the tail constant `B` explicit (`Λ ≤ log`, `log n ≤ (2/(σ−1))·n^{(σ−1)/2}`,
    `∑ n^{−(σ+1)/2} ≤ (σ+1)/(σ−1)`). -/
lemma neg_logDeriv_quantitative {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (σ : ℝ) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (t : ℝ) :
    ‖-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ:ℂ) + t * I)‖
      ≤ 6 / (σ - 1) ^ 2 := by
  have hre : ((σ:ℂ) + t * I).re = σ := by simp
  have hs : 1 < ((σ:ℂ) + t * I).re := by rw [hre]; exact hσ1
  rw [neg_logDeriv_LFunction_eq χ hs]
  have hsummable : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n : ℕ => χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)) ((σ:ℂ) + t * I) n‖) :=
    summable_norm_iff.mpr (LSeriesSummable_twist_vonMangoldt χ hs)
  have hmaj : Summable (fun n : ℕ => (2 / (σ - 1)) * (1 / (n : ℝ) ^ ((σ + 1) / 2))) :=
    (Real.summable_one_div_nat_rpow.mpr (by linarith)).mul_left _
  have hterm : ∀ n : ℕ,
      ‖LSeries.term (fun n : ℕ => χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)) ((σ:ℂ) + t * I) n‖
        ≤ (2 / (σ - 1)) * (1 / (n : ℝ) ^ ((σ + 1) / 2)) := by
    intro n
    rw [LSeries.norm_term_eq, hre]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [if_pos rfl]
      positivity
    · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have hn0 : (0:ℝ) < (n:ℝ) := by linarith
      rw [if_neg hn.ne']
      have h1 : ‖χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)‖ ≤ vonMangoldt n := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg vonMangoldt_nonneg]
        calc ‖χ (n : ZMod N)‖ * vonMangoldt n ≤ 1 * vonMangoldt n :=
              mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) vonMangoldt_nonneg
          _ = vonMangoldt n := one_mul _
      have h2 : vonMangoldt n ≤ Real.log n := vonMangoldt_le_log
      have h3 : Real.log n ≤ (2 / (σ - 1)) * (n:ℝ) ^ ((σ - 1) / 2) := by
        have := Real.log_le_rpow_div hn0.le (by linarith : (0:ℝ) < (σ - 1) / 2)
        calc Real.log n ≤ (n:ℝ) ^ ((σ - 1) / 2) / ((σ - 1) / 2) := this
          _ = (2 / (σ - 1)) * (n:ℝ) ^ ((σ - 1) / 2) := by
              field_simp
      have h4 : (n:ℝ) ^ ((σ - 1) / 2) / (n:ℝ) ^ σ = 1 / (n:ℝ) ^ ((σ + 1) / 2) := by
        rw [← Real.rpow_sub hn0, one_div, ← Real.rpow_neg hn0.le]
        congr 1
        ring
      calc ‖χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)‖ / (n : ℝ) ^ σ
          ≤ Real.log n / (n : ℝ) ^ σ := by
            apply div_le_div_of_nonneg_right (le_trans h1 h2) (Real.rpow_pos_of_pos hn0 σ).le
        _ ≤ ((2 / (σ - 1)) * (n:ℝ) ^ ((σ - 1) / 2)) / (n : ℝ) ^ σ := by
            apply div_le_div_of_nonneg_right h3 (Real.rpow_pos_of_pos hn0 σ).le
        _ = (2 / (σ - 1)) * ((n:ℝ) ^ ((σ - 1) / 2) / (n:ℝ) ^ σ) := by ring
        _ = (2 / (σ - 1)) * (1 / (n : ℝ) ^ ((σ + 1) / 2)) := by rw [h4]
  calc ‖LSeries (fun n : ℕ => χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)) ((σ:ℂ) + t * I)‖
      ≤ ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)) ((σ:ℂ) + t * I) n‖ :=
        norm_tsum_le_tsum_norm hsummable
    _ ≤ ∑' n : ℕ, (2 / (σ - 1)) * (1 / (n : ℝ) ^ ((σ + 1) / 2)) :=
        hsummable.tsum_le_tsum hterm hmaj
    _ = (2 / (σ - 1)) * ∑' n : ℕ, 1 / (n : ℝ) ^ ((σ + 1) / 2) := tsum_mul_left
    _ ≤ (2 / (σ - 1)) * (((σ + 1) / 2) / (((σ + 1) / 2) - 1)) := by
        apply mul_le_mul_of_nonneg_left (tsum_one_div_nat_rpow_le _ (by linarith)) (by positivity)
    _ ≤ 6 / (σ - 1) ^ 2 := by
        have hσ1' : (0:ℝ) < σ - 1 := by linarith
        have heq : (2 / (σ - 1)) * (((σ + 1) / 2) / (((σ + 1) / 2) - 1))
            = (2 * (σ + 1)) / (σ - 1) ^ 2 := by
          rw [show ((σ + 1) / 2) - 1 = (σ - 1) / 2 by ring]
          field_simp
        rw [heq]
        gcongr
        linarith


/-- **Quantitative σ-line tail** (SW brick W2a″): the smoothed integrand on `Re = σ ∈ (1,2]` is
    dominated by `((6/(σ−1)²)·X^σ)/t²` — `truncation_tail_bound`'s input with EXPLICIT constant,
    replacing the existential `B` of `sigma_line_tail_bound`. -/
lemma sigma_line_tail_quantitative {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (X σ : ℝ) (hX : 0 < X) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) :
    ∀ t : ℝ, t ≠ 0 →
      ‖G' χ X ((σ:ℂ) + t * I)‖ ≤ ((6 / (σ - 1) ^ 2) * X ^ σ) / t ^ 2 := by
  intro t ht
  have him : ((σ:ℂ) + t * I).im = t := by simp
  have hre : ((σ:ℂ) + t * I).re = σ := by simp
  have hkd := perron_kernel_decay X hX ((σ:ℂ) + t * I) (by rw [him]; exact ht)
  rw [hre, him] at hkd
  have hq := neg_logDeriv_quantitative χ σ hσ1 hσ2 t
  have hq0 : (0:ℝ) ≤ 6 / (σ - 1) ^ 2 := by positivity
  rw [G', norm_mul]
  calc ‖-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ:ℂ) + t * I)‖
        * ‖(X:ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1))‖
      ≤ (6 / (σ - 1) ^ 2) * (X ^ σ / t ^ 2) := mul_le_mul hq hkd (norm_nonneg _) hq0
    _ = ((6 / (σ - 1) ^ 2) * X ^ σ) / t ^ 2 := by ring

/-- **The χ≠1 smoothed ψ bound, fully quantitative** (W1 MAIN′): every constant explicit —
    `‖ψ_smooth(X,χ)‖ ≤ (6M·X^{1−g/2} + 3g·M·X^{1+g}/T² + 2·(6/g²)·X^{1+g}/T)/(2π)`. -/
theorem psi_smooth_bound_quantitative (ε : ℝ) (hε0 : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 1 ≤ C ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    ∀ X : ℝ, 1 < X → ∀ T : ℝ, 0 < T →
    ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X)‖
      ≤ (6 * (C * ((N:ℝ))^ε * (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)^2)
            * X ^ (1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2)
          + 2 * (((1 + c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20))
                - (1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2))
              * ((C * ((N:ℝ))^ε * (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)^2)
                * X ^ (1 + c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)) / T ^ 2))
          + 2 * ((6 / (c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)) ^ 2)
              * X ^ (1 + c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20))) / T)
        / (2 * Real.pi) := by
  obtain ⟨c, C, hc0, hc12, hC1, hcc⟩ := contour_combined ε hε0
  refine ⟨c, C, hc0, hc12, hC1, ?_⟩
  intro N _ χ hχ X hX T hT
  have hX0 : (0:ℝ) < X := by linarith
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hNe0 : (0:ℝ) < ((N:ℝ))^(-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hNe1 : ((N:ℝ))^(-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
  set LT := Real.log ((N:ℝ)*(4*(T+1)+7)) + 20 with hLTdef
  have hLT20 : (20:ℝ) ≤ LT := by
    rw [hLTdef]
    have : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*(T+1)+7)) := Real.log_nonneg (by nlinarith)
    linarith
  obtain ⟨hg0, hg40, hσ'34, hσ1, hσ'σ, hσ2⟩ :=
    strip_numerics c (((N:ℝ))^(-ε)) LT hc0 hc12 hNe0 hNe1 hLT20
  set g := c * ((N:ℝ))^(-ε) / LT with hgdef
  set σ' := 1 - g / 2 with hσ'def
  set σ := 1 + g with hσdef
  set M := C * ((N:ℝ))^ε * LT^2 with hMdef
  have hM0 : (0:ℝ) ≤ M := by rw [hMdef]; positivity
  have hccM : ∀ s : ℂ, |s.im| ≤ T → σ' ≤ s.re → s.re ≤ σ →
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ M := by
    intro s him hre1 hre2
    exact ((hcc N χ hχ T hT.le s him hre1).2 hre2)
  have hzf : ∀ s : ℂ, |s.im| ≤ T → σ' ≤ s.re → DirichletCharacter.LFunction χ s ≠ 0 := by
    intro s him hre
    exact (hcc N χ hχ T hT.le s him hre).1
  have hσm1 : σ - 1 = g := by rw [hσdef]; ring
  have hrep : (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
      χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X))
      = (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, G' χ X ((σ : ℂ) + t * I) := by
    rw [smoothed_perron_LFunction χ X hX σ hσ1, perron_integrand_reshape]
    rfl
  have htail : ‖(∫ t : ℝ, G' χ X ((σ : ℂ) + t * I))
      - ∫ t in (-T)..T, G' χ X ((σ : ℂ) + t * I)‖ ≤ 2 * ((6 / g ^ 2) * X ^ σ) / T := by
    have hq := sigma_line_tail_quantitative χ X σ hX0 hσ1 hσ2
    have := truncation_tail_bound _ (integrand_integrable_on_line χ hχ X hX0 σ hσ1)
      ((6 / (σ - 1) ^ 2) * X ^ σ) T hT (fun t ht => hq t ht)
    rwa [hσm1] at this
  have hMseg : ∀ tt : ℝ, |tt| ≤ T → ∀ x ∈ Set.uIcc σ' σ,
      ‖-deriv (DirichletCharacter.LFunction χ) ((x:ℂ) + tt * I) / DirichletCharacter.LFunction χ ((x:ℂ) + tt * I)‖ ≤ M := by
    intro tt httT x hx
    rw [Set.uIcc_of_le hσ'σ] at hx
    exact strip_point_M_bound χ M T σ' σ hccM x tt hx.1 hx.2 httT
  have hconnT : ‖∫ x in σ'..σ, G' χ X ((x:ℂ) + ((T : ℝ) : ℂ) * I)‖
      ≤ (σ - σ') * (M * X ^ σ / T ^ 2) :=
    horizontal_connector_bound χ X hX.le σ' σ T M hσ'σ hT.ne' hM0
      (hMseg T (by rw [abs_of_pos hT]))
  have hconnB : ‖∫ x in σ'..σ, G' χ X ((x:ℂ) + ((-T : ℝ) : ℂ) * I)‖
      ≤ (σ - σ') * (M * X ^ σ / T ^ 2) := by
    have hb := horizontal_connector_bound χ X hX.le σ' σ (-T) M hσ'σ
      (by simpa using hT.ne') hM0 (hMseg (-T) (by rw [abs_neg, abs_of_pos hT]))
    rwa [neg_sq] at hb
  have hline : ‖∫ y in (-T)..T, G' χ X ((σ':ℂ) + (y:ℂ) * I)‖ ≤ 6 * M * X ^ σ' := by
    apply shifted_line_integral_bound _ M (X ^ σ') σ' T hM0 (Real.rpow_nonneg hX0.le _) hσ'34 hT.le
    intro t ht
    have htT : |t| ≤ T := by
      rw [abs_le]
      exact ⟨ht.1.le, ht.2⟩
    exact integrand_pointwise_bound χ X σ' t M hX0 (by linarith) hM0
      (strip_point_M_bound χ M T σ' σ hccM σ' t le_rfl hσ'σ htT)
  exact psi_smooth_bound_skeleton χ hχ _ X hX σ' σ T M (6 / g ^ 2) hσ'34 hσ'σ hT hM0
    hrep htail hconnT hconnB hline hzf

/-- **R1: L_T two-sided bounds at `T = exp u`** — for `u ≥ (4B+23)²` and `1 ≤ Nr ≤ u^{2B}`:
    `u ≤ log(Nr·(4(e^u+1)+7)) + 20 ≤ 2u`. Upper: `log Nr ≤ 2B·log u ≤ 4B·√u` (`log_le_rpow_div`),
    `4e^u+11 ≤ 15e^u`, `log 15 ≤ 3`; lower: the argument dominates `e^u`. -/
lemma LT_bounds_at_exp (B : ℝ) (hB : 1 ≤ B) :
    ∀ u : ℝ, (4*B + 23)^2 ≤ u → ∀ Nr : ℝ, 1 ≤ Nr → Nr ≤ u ^ (2*B : ℝ) →
    u ≤ Real.log (Nr * (4*(Real.exp u + 1) + 7)) + 20 ∧
    Real.log (Nr * (4*(Real.exp u + 1) + 7)) + 20 ≤ 2*u := by
  intro u hu Nr hNr1 hNru
  have hB0 : (0:ℝ) < B := by linarith
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le (by nlinarith) hu
  have hu1 : (1:ℝ) ≤ u := le_trans (by nlinarith) hu
  have hexp0 : (0:ℝ) < Real.exp u := Real.exp_pos u
  have harg0 : (0:ℝ) < Nr * (4*(Real.exp u + 1) + 7) := by positivity
  constructor
  · -- lower: Nr·(4(e^u+1)+7) ≥ e^u
    have h1 : Real.exp u ≤ Nr * (4*(Real.exp u + 1) + 7) := by nlinarith
    have h2 := Real.log_le_log hexp0 h1
    rw [Real.log_exp] at h2
    linarith
  · -- upper
    have hsplit : Real.log (Nr * (4*(Real.exp u + 1) + 7))
        = Real.log Nr + Real.log (4*(Real.exp u + 1) + 7) := by
      rw [Real.log_mul (by linarith) (by positivity)]
    have hlogNr : Real.log Nr ≤ 4 * B * u ^ ((1:ℝ)/2) := by
      have h3 : Real.log Nr ≤ Real.log (u ^ (2*B : ℝ)) := Real.log_le_log (by linarith) hNru
      rw [Real.log_rpow hu0] at h3
      have h4 : Real.log u ≤ u ^ ((1:ℝ)/2) / ((1:ℝ)/2) :=
        Real.log_le_rpow_div hu0.le (by norm_num)
      have h5 : u ^ ((1:ℝ)/2) / ((1:ℝ)/2) = 2 * u ^ ((1:ℝ)/2) := by ring
      rw [h5] at h4
      have hlogu0 : (0:ℝ) ≤ Real.log u := Real.log_nonneg hu1
      calc Real.log Nr ≤ 2*B * Real.log u := h3
        _ ≤ 2*B * (2 * u ^ ((1:ℝ)/2)) := by
            apply mul_le_mul_of_nonneg_left h4 (by linarith)
        _ = 4 * B * u ^ ((1:ℝ)/2) := by ring
    have hlogT : Real.log (4*(Real.exp u + 1) + 7) ≤ 3 + u := by
      have h6 : 4*(Real.exp u + 1) + 7 ≤ 15 * Real.exp u := by
        nlinarith [Real.one_le_exp (le_of_lt hu0)]
      have h7 := Real.log_le_log (by positivity) h6
      rw [Real.log_mul (by norm_num) hexp0.ne', Real.log_exp] at h7
      have h8 : Real.log 15 ≤ 3 := by
        have h9 : (15:ℝ) ≤ Real.exp 3 := by
          have h10 : (2.7:ℝ) ≤ Real.exp 1 := by
            have := Real.exp_one_gt_d9
            linarith
          calc (15:ℝ) ≤ 2.7^3 := by norm_num
            _ ≤ (Real.exp 1)^3 := pow_le_pow_left₀ (by norm_num) h10 3
            _ = Real.exp 3 := by
                rw [← Real.exp_one_rpow 3]
                norm_num
        calc Real.log 15 ≤ Real.log (Real.exp 3) := Real.log_le_log (by norm_num) h9
          _ = 3 := Real.log_exp 3
      linarith
    have hsq : (4*B + 23) ≤ u ^ ((1:ℝ)/2) := by
      have h11 : ((4*B + 23)^2) ^ ((1:ℝ)/2) ≤ u ^ ((1:ℝ)/2) :=
        Real.rpow_le_rpow (by positivity) hu (by norm_num)
      rwa [show ((4*B + 23):ℝ)^2 = (4*B+23)*(4*B+23) by ring,
        ← Real.sqrt_eq_rpow, Real.sqrt_mul_self (by linarith)] at h11
    have hsqu : u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/2) = u := by
      rw [← Real.rpow_add hu0]
      norm_num
    have hsqnn : (0:ℝ) ≤ u ^ ((1:ℝ)/2) := Real.rpow_nonneg hu0.le _
    have hsq1 : (1:ℝ) ≤ u ^ ((1:ℝ)/2) := by nlinarith
    -- 4B√u + 3 + u + 20 ≤ 2u ⟸ 4B√u + 23 ≤ u = √u·√u
    have hmain : 4 * B * u ^ ((1:ℝ)/2) + 23 ≤ u := by
      have h12 : (4*B + 23) * u ^ ((1:ℝ)/2) ≤ u := by
        calc (4*B + 23) * u ^ ((1:ℝ)/2) ≤ u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/2) := by
              apply mul_le_mul_of_nonneg_right hsq hsqnn
          _ = u := hsqu
      nlinarith
    rw [hsplit]
    linarith

/-- **R2+R3: the gap–saving balance at `T = exp u`** — with `u ≤ LT ≤ 2u`, `u^{−1/2} ≤ Ne ≤ 1`,
    `0 < c ≤ 1/2`: the exponential saving grows, `(c/2)·u^{1/2} ≤ g·u²` (R2), while the strip stays
    thin enough that `g·u² ≤ u/2` (R3) — so `X^g/T = exp(g·u² − u) ≤ exp(−u/2)`. Here `g = c·Ne/LT`,
    `u² = log X`. -/
lemma rate_g_bounds (c u LT Ne : ℝ) (hc0 : 0 < c) (hc12 : c ≤ 1/2)
    (hu1 : 1 ≤ u) (hLTlo : u ≤ LT) (hLThi : LT ≤ 2*u)
    (hNe_lo : u ^ (-(1:ℝ)/2) ≤ Ne) (hNe_hi : Ne ≤ 1) :
    (c/2) * u ^ ((1:ℝ)/2) ≤ (c * Ne / LT) * (u * u) ∧ (c * Ne / LT) * (u * u) ≤ u/2 := by
  have hu0 : (0:ℝ) < u := by linarith
  have hLT0 : (0:ℝ) < LT := by linarith
  have hNe0 : (0:ℝ) < Ne := lt_of_lt_of_le (Real.rpow_pos_of_pos hu0 _) hNe_lo
  have hu2 : u * u = u ^ ((2:ℕ):ℝ) := by
    rw [Real.rpow_natCast]
    ring
  have e1 : u ^ ((1:ℝ)/2) * u = u ^ ((3:ℝ)/2) := by
    nth_rewrite 2 [show u = u ^ (1:ℝ) from (Real.rpow_one u).symm]
    rw [← Real.rpow_add hu0]
    norm_num
  have e2 : u ^ (-(1:ℝ)/2) * (u * u) = u ^ ((3:ℝ)/2) := by
    rw [hu2, ← Real.rpow_add hu0]
    norm_num
  constructor
  · -- R2: (c/2)·u^{1/2} ≤ g·u²
    rw [show (c * Ne / LT) * (u * u) = (c * Ne * (u * u)) / LT from by ring,
        le_div_iff₀ hLT0]
    have h1 : (c/2) * u ^ ((1:ℝ)/2) * LT ≤ (c/2) * u ^ ((1:ℝ)/2) * (2*u) := by
      apply mul_le_mul_of_nonneg_left hLThi (by positivity)
    have h2 : (c/2) * u ^ ((1:ℝ)/2) * (2*u) = c * (u ^ ((1:ℝ)/2) * u) := by ring
    have h3 : u ^ ((3:ℝ)/2) ≤ Ne * (u * u) := by
      calc u ^ ((3:ℝ)/2) = u ^ (-(1:ℝ)/2) * (u * u) := e2.symm
        _ ≤ Ne * (u * u) := by
            apply mul_le_mul_of_nonneg_right hNe_lo (by positivity)
    have h4 : c * (u ^ ((1:ℝ)/2) * u) ≤ c * (Ne * (u * u)) := by
      apply mul_le_mul_of_nonneg_left _ hc0.le
      rw [e1]
      exact h3
    calc (c/2) * u ^ ((1:ℝ)/2) * LT ≤ c * (u ^ ((1:ℝ)/2) * u) := by linarith
      _ ≤ c * (Ne * (u * u)) := h4
      _ = c * Ne * (u * u) := by ring
  · -- R3: g·u² ≤ u/2
    have h5 : c * Ne / LT ≤ c / u := by
      have h5a : c * Ne / LT ≤ c / LT := by
        apply div_le_div_of_nonneg_right _ hLT0.le
        nlinarith
      have h5b : c / LT ≤ c / u := div_le_div_of_nonneg_left hc0.le hu0 hLTlo
      linarith
    have h6 : (c / u) * (u * u) = c * u := by
      field_simp
    calc (c * Ne / LT) * (u * u) ≤ (c / u) * (u * u) := by
          apply mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = c * u := h6
      _ ≤ u/2 := by nlinarith

/-- **R4a: polylog absorption into the exponential saving** — for `u ≥ max((80/c)⁴, 256)`:
    `C·u^{5/2}·e^{−(c/4)√u} + K·u³·e^{−u/2} ≤ (C+K)·e^{−(c/8)√u}`. Via `log a ≤ x−y ⇒
    a·e^{−x} ≤ e^{−y}` + `log u ≤ 4u^{1/4}` (`log_le_rpow_div`). -/
lemma poly_exp_absorption (c C K : ℝ) (hc0 : 0 < c) (hc12 : c ≤ 1/2)
    (hC0 : 0 ≤ C) (hK0 : 0 ≤ K) :
    ∀ u : ℝ, max ((80/c)^4) 256 ≤ u →
      C * u ^ ((5:ℝ)/2) * Real.exp (-((c/4) * u ^ ((1:ℝ)/2)))
        + K * u ^ (3:ℝ) * Real.exp (-(u/2))
      ≤ (C + K) * Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) := by
  intro u hu
  have hu256 : (256:ℝ) ≤ u := le_trans (le_max_right _ _) hu
  have hu80c : (80/c)^4 ≤ u := le_trans (le_max_left _ _) hu
  have hu0 : (0:ℝ) < u := by linarith
  have hu1 : (1:ℝ) ≤ u := by linarith
  have hs0 : (0:ℝ) < u ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hu0 _
  have hq0 : (0:ℝ) < u ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hu0 _
  -- log u ≤ 4·u^{1/4}
  have hlogu : Real.log u ≤ 4 * u ^ ((1:ℝ)/4) := by
    have := Real.log_le_rpow_div hu0.le (by norm_num : (0:ℝ) < 1/4)
    calc Real.log u ≤ u ^ ((1:ℝ)/4) / (1/4) := this
      _ = 4 * u ^ ((1:ℝ)/4) := by ring
  -- u^{1/4}·u^{1/4} = u^{1/2}
  have hqq : u ^ ((1:ℝ)/4) * u ^ ((1:ℝ)/4) = u ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_add hu0]; norm_num
  have hss : u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/2) = u := by
    rw [← Real.rpow_add hu0]; norm_num
  -- (80/c) ≤ u^{1/4}
  have h80 : 80/c ≤ u ^ ((1:ℝ)/4) := by
    have h1 : ((80/c)^4 : ℝ) ^ ((1:ℝ)/4) ≤ u ^ ((1:ℝ)/4) :=
      Real.rpow_le_rpow (by positivity) hu80c (by norm_num)
    rwa [show ((80/c):ℝ)^4 = ((80/c):ℝ)^((4:ℕ):ℝ) from by rw [Real.rpow_natCast],
      ← Real.rpow_mul (by positivity), show ((4:ℕ):ℝ) * ((1:ℝ)/4) = 1 by norm_num,
      Real.rpow_one] at h1
  -- 4 ≤ u^{1/4} (from u ≥ 256)
  have h4q : (4:ℝ) ≤ u ^ ((1:ℝ)/4) := by
    have h1 : ((256:ℝ)) ^ ((1:ℝ)/4) ≤ u ^ ((1:ℝ)/4) :=
      Real.rpow_le_rpow (by norm_num) hu256 (by norm_num)
    rwa [show (256:ℝ) = (4:ℝ)^((4:ℕ):ℝ) from by rw [Real.rpow_natCast]; norm_num,
      ← Real.rpow_mul (by norm_num), show ((4:ℕ):ℝ) * ((1:ℝ)/4) = 1 by norm_num,
      Real.rpow_one] at h1
  -- helper: log a ≤ x − y ⇒ a·e^{−x} ≤ e^{−y}
  have haux : ∀ a x y : ℝ, 0 < a → Real.log a ≤ x - y →
      a * Real.exp (-x) ≤ Real.exp (-y) := by
    intro a x y ha hlog
    have h1 : a ≤ Real.exp (x - y) := (Real.log_le_iff_le_exp ha).mp hlog
    calc a * Real.exp (-x) ≤ Real.exp (x - y) * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (-y) := by rw [← Real.exp_add]; ring_nf
  -- term 1
  have hterm1 : u ^ ((5:ℝ)/2) * Real.exp (-((c/4) * u ^ ((1:ℝ)/2)))
      ≤ Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) := by
    apply haux _ _ _ (Real.rpow_pos_of_pos hu0 _)
    rw [Real.log_rpow hu0]
    have h1 : (5:ℝ)/2 * Real.log u ≤ 10 * u ^ ((1:ℝ)/4) := by
      have hlogu0 : (0:ℝ) ≤ Real.log u := Real.log_nonneg hu1
      nlinarith
    have h2 : 10 * u ^ ((1:ℝ)/4) ≤ (c/8) * u ^ ((1:ℝ)/2) := by
      have h3 : (80:ℝ) ≤ c * u ^ ((1:ℝ)/4) := by
        have := mul_le_mul_of_nonneg_left h80 hc0.le
        calc (80:ℝ) = c * (80/c) := by field_simp
          _ ≤ c * u ^ ((1:ℝ)/4) := this
      calc 10 * u ^ ((1:ℝ)/4) = (80 * (u ^ ((1:ℝ)/4) * u ^ ((1:ℝ)/4))) / (8 * u ^ ((1:ℝ)/4)) := by
            field_simp
            ring
        _ ≤ ((c * u ^ ((1:ℝ)/4)) * (u ^ ((1:ℝ)/4) * u ^ ((1:ℝ)/4))) / (8 * u ^ ((1:ℝ)/4)) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = (c/8) * (u ^ ((1:ℝ)/4) * u ^ ((1:ℝ)/4)) := by
            field_simp
        _ = (c/8) * u ^ ((1:ℝ)/2) := by rw [hqq]
    have hgoal : (c/4) * u ^ ((1:ℝ)/2) - (c/8) * u ^ ((1:ℝ)/2) = (c/8) * u ^ ((1:ℝ)/2) := by ring
    linarith
  -- term 2
  have hterm2 : u ^ (3:ℝ) * Real.exp (-(u/2))
      ≤ Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) := by
    apply haux _ _ _ (Real.rpow_pos_of_pos hu0 _)
    rw [Real.log_rpow hu0]
    have h1 : (3:ℝ) * Real.log u ≤ 12 * u ^ ((1:ℝ)/4) := by
      have hlogu0 : (0:ℝ) ≤ Real.log u := Real.log_nonneg hu1
      nlinarith
    -- 12·u^{1/4} ≤ u/4: 12 ≤ (1/4)·u^{3/4} ⟸ u^{3/4} = u^{1/4}·u^{1/2} ≥ 4·16 = 64 ≥ 48
    have h16 : (16:ℝ) ≤ u ^ ((1:ℝ)/2) := by
      have h := mul_le_mul h4q h4q (by norm_num) hq0.le
      rw [hqq] at h
      linarith
    have h2 : 12 * u ^ ((1:ℝ)/4) ≤ u/4 := by
      have h3 : 48 * u ^ ((1:ℝ)/4) ≤ u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/2) := by
        calc 48 * u ^ ((1:ℝ)/4) ≤ (16 * u ^ ((1:ℝ)/4)) * 4 := by ring_nf; nlinarith [hq0]
          _ ≤ (u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/4)) * u ^ ((1:ℝ)/4) := by
              apply mul_le_mul _ h4q (by norm_num) (by positivity)
              apply mul_le_mul_of_nonneg_right h16 hq0.le
          _ = u ^ ((1:ℝ)/2) * (u ^ ((1:ℝ)/4) * u ^ ((1:ℝ)/4)) := by ring
          _ = u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/2) := by rw [hqq]
      rw [hss] at h3
      linarith
    -- u/2 − (c/8)√u ≥ u/4: (c/8)√u ≤ √u/16 ≤ u/4
    have h5 : (c/8) * u ^ ((1:ℝ)/2) ≤ u/4 := by
      have h6 : (c/8) * u ^ ((1:ℝ)/2) ≤ (1/16) * u ^ ((1:ℝ)/2) := by
        apply mul_le_mul_of_nonneg_right (by linarith) hs0.le
      have h7 : u ^ ((1:ℝ)/2) ≤ u := by
        calc u ^ ((1:ℝ)/2) = 1 * u ^ ((1:ℝ)/2) := (one_mul _).symm
          _ ≤ u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/2) := by
              apply mul_le_mul_of_nonneg_right _ hs0.le
              nlinarith [h16]
          _ = u := hss
      linarith
    linarith
  -- assemble
  calc C * u ^ ((5:ℝ)/2) * Real.exp (-((c/4) * u ^ ((1:ℝ)/2)))
        + K * u ^ (3:ℝ) * Real.exp (-(u/2))
      = C * (u ^ ((5:ℝ)/2) * Real.exp (-((c/4) * u ^ ((1:ℝ)/2))))
        + K * (u ^ (3:ℝ) * Real.exp (-(u/2))) := by ring
    _ ≤ C * Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) + K * Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) :=
        add_le_add (mul_le_mul_of_nonneg_left hterm1 hC0) (mul_le_mul_of_nonneg_left hterm2 hK0)
    _ = (C + K) * Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) := by ring

/-- **R4b-pre: modulus-power bounds at `ε = 1/(4B)`** — for `1 ≤ Nr ≤ u^{2B}`, `u ≥ 1`:
    `Nr^{1/(4B)} ≤ u^{1/2}` and `u^{−1/2} ≤ Nr^{−1/(4B)} ≤ 1` (the `Ne`-window `rate_g_bounds`
    and the `M`-bound need). -/
lemma N_eps_bounds (B : ℝ) (hB : 1 ≤ B) (u Nr : ℝ) (hu1 : 1 ≤ u) (hNr1 : 1 ≤ Nr)
    (hNru : Nr ≤ u ^ (2*B : ℝ)) :
    Nr ^ ((1:ℝ)/(4*B)) ≤ u ^ ((1:ℝ)/2) ∧
    u ^ (-(1:ℝ)/2) ≤ Nr ^ (-((1:ℝ)/(4*B))) ∧ Nr ^ (-((1:ℝ)/(4*B))) ≤ 1 := by
  have hu0 : (0:ℝ) < u := by linarith
  have hNr0 : (0:ℝ) < Nr := by linarith
  have hB0 : (0:ℝ) < B := by linarith
  have hε0 : (0:ℝ) < (1:ℝ)/(4*B) := by positivity
  have hup : Nr ^ ((1:ℝ)/(4*B)) ≤ u ^ ((1:ℝ)/2) := by
    have h1 : Nr ^ ((1:ℝ)/(4*B)) ≤ (u ^ (2*B : ℝ)) ^ ((1:ℝ)/(4*B)) :=
      Real.rpow_le_rpow hNr0.le hNru hε0.le
    rwa [← Real.rpow_mul hu0.le, show (2*B) * ((1:ℝ)/(4*B)) = 1/2 from by
      field_simp
      ring] at h1
  have hpos : (0:ℝ) < Nr ^ ((1:ℝ)/(4*B)) := Real.rpow_pos_of_pos hNr0 _
  refine ⟨hup, ?_, ?_⟩
  · rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg hu0.le,
      Real.rpow_neg hNr0.le]
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hpos hup
  · exact Real.rpow_le_one_of_one_le_of_nonpos hNr1 (neg_nonpos.mpr hε0.le)

set_option maxHeartbeats 4000000 in
open ArithmeticFunction in
/-- **R4b: THE PER-CHARACTER SIEGEL–WALFISZ BOUND** — for every `B ≥ 1` there are `c₂, C₂, X₀ > 0`
    with: for all `X ≥ X₀`, moduli `q ≤ (log X)^B`, and nontrivial `χ mod q`,
    `‖ψ_smooth(X,χ)‖ ≤ C₂·X·exp(−c₂·(log X)^{1/10})`. Instantiates
    `psi_smooth_bound_quantitative` at `ε = 1/(4B)`, `T = exp(√(log X))` and collapses via
    R1 (`LT_bounds_at_exp`), R2/R3 (`rate_g_bounds`), R4b-pre (`N_eps_bounds`),
    `rpow_shift_as_exp`, and R4a (`poly_exp_absorption`). -/
theorem psi_smooth_SW_rate (B : ℝ) (hB : 1 ≤ B) :
    ∃ c₂ C₂ X₀ : ℝ, 0 < c₂ ∧ 0 < C₂ ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    (N:ℝ) ≤ Real.log X ^ (B : ℝ) →
    ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X)‖
      ≤ C₂ * X * Real.exp (-(c₂ * Real.log X ^ ((1:ℝ)/10))) := by
  obtain ⟨c, C, hc0, hc12, hC1, hmain⟩ := psi_smooth_bound_quantitative (1/(4*B)) (by positivity)
  set M₀ := max ((4*B+23)^2) (max ((80/c)^4) 256) with hM₀def
  have hM₀256 : (256:ℝ) ≤ M₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hM₀1 : (1:ℝ) ≤ M₀ := by linarith
  have hM₀0 : (0:ℝ) ≤ M₀ := by linarith
  refine ⟨c/8, 30*C + 48/c^2, Real.exp (M₀^2), by positivity, by positivity, ?_⟩
  intro X hX N _ χ hχ hNB
  -- basic scales
  have hL : M₀^2 ≤ Real.log X := by
    have h1 : Real.log (Real.exp (M₀^2)) ≤ Real.log X :=
      Real.log_le_log (Real.exp_pos _) hX
    rwa [Real.log_exp] at h1
  have hL1 : (1:ℝ) ≤ Real.log X := by nlinarith
  have hL0 : (0:ℝ) < Real.log X := by linarith
  have hX1 : (1:ℝ) < X := by
    have h1 : Real.exp 1 ≤ Real.exp (M₀^2) := Real.exp_le_exp.mpr (by nlinarith)
    have h2 := Real.add_one_le_exp 1
    linarith
  have hX0 : (0:ℝ) < X := by linarith
  set L := Real.log X with hLdef
  set u := L ^ ((1:ℝ)/2) with hudef
  have hu0 : (0:ℝ) < u := Real.rpow_pos_of_pos hL0 _
  have huM : M₀ ≤ u := by
    have h1 : (M₀^2) ^ ((1:ℝ)/2) ≤ L ^ ((1:ℝ)/2) :=
      Real.rpow_le_rpow (by positivity) hL (by norm_num)
    rwa [show (M₀:ℝ)^2 = M₀ * M₀ by ring, ← Real.sqrt_eq_rpow,
      Real.sqrt_mul_self hM₀0] at h1
  have hu1 : (1:ℝ) ≤ u := le_trans hM₀1 huM
  have hLuu : u * u = L := by
    rw [hudef, ← Real.rpow_add hL0]
    norm_num
  set T := Real.exp u with hTdef
  have hT0 : (0:ℝ) < T := Real.exp_pos _
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  -- N ≤ u^{2B}
  have hNru : (N:ℝ) ≤ u ^ (2*B : ℝ) := by
    have h1 : L ^ (B:ℝ) = u ^ (2*B : ℝ) := by
      rw [← hLuu, show u * u = u ^ ((2:ℕ):ℝ) from by rw [Real.rpow_natCast]; ring,
        ← Real.rpow_mul hu0.le]
      norm_num
    rwa [h1] at hNB
  -- R1
  obtain ⟨hLTlo, hLThi⟩ := LT_bounds_at_exp B hB u
    (le_trans (le_max_left _ _) huM) (N:ℝ) hN1 hNru
  set LTv := Real.log ((N:ℝ) * (4*(T+1)+7)) + 20 with hLTvdef
  -- R4b-pre
  obtain ⟨hNup, hNe_lo, hNe_hi⟩ := N_eps_bounds B hB u (N:ℝ) hu1 hN1 hNru
  set Ne := (N:ℝ) ^ (-((1:ℝ)/(4*B))) with hNedef
  set g := c * Ne / LTv with hgdef
  have hLT0 : (0:ℝ) < LTv := by linarith
  have hNe0 : (0:ℝ) < Ne := Real.rpow_pos_of_pos (by linarith) _
  have hg0 : (0:ℝ) < g := by rw [hgdef]; positivity
  -- R2/R3
  obtain ⟨hR2, hR3⟩ := rate_g_bounds c u LTv Ne hc0 hc12 hu1 hLTlo hLThi hNe_lo hNe_hi
  set M := C * (N:ℝ) ^ ((1:ℝ)/(4*B)) * LTv^2 with hMdef
  have hM0 : (0:ℝ) ≤ M := by rw [hMdef]; positivity
  -- M ≤ 4C·u^{5/2}
  have hMle : M ≤ 4*C * u ^ ((5:ℝ)/2) := by
    have h1 : LTv^2 ≤ 4 * (u*u) := by nlinarith
    have h2 : (N:ℝ) ^ ((1:ℝ)/(4*B)) * LTv^2 ≤ u ^ ((1:ℝ)/2) * (4*(u*u)) := by
      apply mul_le_mul hNup h1 (by positivity) (by positivity)
    have h3 : u ^ ((1:ℝ)/2) * (4*(u*u)) = 4 * u ^ ((5:ℝ)/2) := by
      rw [show u * u = u ^ ((2:ℕ):ℝ) from by rw [Real.rpow_natCast]; ring,
        show u ^ ((1:ℝ)/2) * (4 * u ^ (((2:ℕ):ℝ))) = 4 * (u ^ ((1:ℝ)/2) * u ^ (((2:ℕ):ℝ))) from by ring,
        ← Real.rpow_add hu0]
      norm_num
    calc M = C * ((N:ℝ) ^ ((1:ℝ)/(4*B)) * LTv^2) := by rw [hMdef]; ring
      _ ≤ C * (u ^ ((1:ℝ)/2) * (4*(u*u))) := by
          apply mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = 4*C * u ^ ((5:ℝ)/2) := by rw [h3]; ring
  -- the main bound
  have hbound := hmain N χ hχ X hX1 T hT0
  -- identify: the main's terms with our abbreviations (they are literally the same after `set`)
  -- term bounds
  have hXg : X ^ (g : ℝ) = Real.exp (g * L) := by
    rw [Real.rpow_def_of_pos hX0, mul_comm]
  have hgL2 : (c/4) * u ^ ((1:ℝ)/2) ≤ (g/2) * L := by
    have := hR2
    rw [← hLuu]
    nlinarith
  have hgLu : g * L ≤ u/2 := by rw [← hLuu]; exact hR3
  -- fold the abbreviations into hbound
  rw [← hLTvdef] at hbound
  rw [← hNedef] at hbound
  rw [← hgdef] at hbound
  rw [← hMdef] at hbound
  -- exponentials
  have hexpX : ∀ a : ℝ, X ^ (1 + a : ℝ) = X * Real.exp (a * L) := by
    intro a
    rw [Real.rpow_add hX0, Real.rpow_one, Real.rpow_def_of_pos hX0, mul_comm L a]
  have hT2 : T^2 = Real.exp (2*u) := by
    rw [hTdef, sq, ← Real.exp_add]
    ring_nf
  -- t1
  have ht1 : 6 * M * X ^ (1 - g/2 : ℝ)
      ≤ 24*C * u ^ ((5:ℝ)/2) * (X * Real.exp (-((c/4) * u ^ ((1:ℝ)/2)))) := by
    rw [rpow_shift_as_exp X g hX0]
    have h1 : Real.exp (-(g/2) * L) ≤ Real.exp (-((c/4) * u ^ ((1:ℝ)/2))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hgL2]
    calc 6 * M * (X * Real.exp (-(g/2) * L))
        ≤ 6 * (4*C * u ^ ((5:ℝ)/2)) * (X * Real.exp (-(g/2) * L)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left hMle (by norm_num)
      _ ≤ 6 * (4*C * u ^ ((5:ℝ)/2)) * (X * Real.exp (-((c/4) * u ^ ((1:ℝ)/2)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left h1 hX0.le
      _ = 24*C * u ^ ((5:ℝ)/2) * (X * Real.exp (-((c/4) * u ^ ((1:ℝ)/2)))) := by ring
  have hgle : g ≤ 1/2 := by
    rw [hgdef]
    have h1 : c * Ne ≤ 1/2 := by nlinarith
    have h2 : c * Ne / LTv ≤ c * Ne / 1 := by
      apply div_le_div_of_nonneg_left (by positivity) one_pos (by linarith)
    simpa using le_trans h2 (by linarith)
  have hXgT2 : X ^ (1 + g : ℝ) / T^2 ≤ X * Real.exp (-(u/2)) := by
    rw [hexpX g, hT2, mul_div_assoc, ← Real.exp_sub]
    apply mul_le_mul_of_nonneg_left _ hX0.le
    apply Real.exp_le_exp.mpr
    nlinarith [hgLu, hu0]
  have hXgT : X ^ (1 + g : ℝ) / T ≤ X * Real.exp (-(u/2)) := by
    rw [hexpX g, hTdef, mul_div_assoc, ← Real.exp_sub]
    apply mul_le_mul_of_nonneg_left _ hX0.le
    apply Real.exp_le_exp.mpr
    nlinarith [hgLu, hu0]
  have hu53 : u ^ ((5:ℝ)/2) ≤ u ^ (3:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
  -- t2
  have ht2 : 2 * (((1 + g) - (1 - g/2)) * (M * X ^ (1 + g : ℝ) / T^2))
      ≤ 6*C * u ^ (3:ℝ) * (X * Real.exp (-(u/2))) := by
    have hd : (1 + g) - (1 - g/2) = (3/2)*g := by ring
    rw [hd]
    have h1 : M * X ^ (1 + g : ℝ) / T^2 ≤ (4*C * u ^ (3:ℝ)) * (X * Real.exp (-(u/2))) := by
      rw [mul_div_assoc]
      apply mul_le_mul (le_trans hMle (by nlinarith [Real.rpow_nonneg hu0.le ((5:ℝ)/2)]))
        hXgT2 (by positivity) (by positivity)
    calc 2 * ((3/2)*g * (M * X ^ (1 + g : ℝ) / T^2)) = 3*g * (M * X ^ (1 + g : ℝ) / T^2) := by ring
      _ ≤ 3*(1/2) * ((4*C * u ^ (3:ℝ)) * (X * Real.exp (-(u/2)))) := by
          apply mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
      _ = 6*C * u ^ (3:ℝ) * (X * Real.exp (-(u/2))) := by ring
  -- 1/g² bound
  have hginv : 6 / g^2 ≤ 6 * ((4/c^2) * u ^ (3:ℝ)) := by
    have h1 : 1/g ≤ (2/c) * u ^ ((3:ℝ)/2) := by
      rw [hgdef]
      have h2 : (1:ℝ)/(c * Ne / LTv) = LTv / (c * Ne) := by
        field_simp
      rw [h2]
      have h3 : c * u ^ (-(1:ℝ)/2) ≤ c * Ne := by
        apply mul_le_mul_of_nonneg_left hNe_lo hc0.le
      have h4 : LTv / (c * Ne) ≤ (2*u) / (c * u ^ (-(1:ℝ)/2)) := by
        have h4a : LTv / (c * Ne) ≤ (2*u) / (c * Ne) :=
          div_le_div_of_nonneg_right hLThi (by positivity)
        have h4b : (2*u) / (c * Ne) ≤ (2*u) / (c * u ^ (-(1:ℝ)/2)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h3
        linarith
      refine le_trans h4 (le_of_eq ?_)
      rw [show u ^ (-(1:ℝ)/2) = (u ^ ((1:ℝ)/2))⁻¹ from by
        rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg hu0.le]]
      rw [div_eq_mul_inv, mul_inv, inv_inv]
      rw [show u ^ ((3:ℝ)/2) = u * u ^ ((1:ℝ)/2) from by
        rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add hu0, Real.rpow_one]]
      ring
    have h5 : (1/g)^2 ≤ ((2/c) * u ^ ((3:ℝ)/2))^2 := by
      apply pow_le_pow_left₀ (by positivity) h1
    have h6 : ((2/c) * u ^ ((3:ℝ)/2))^2 = (4/c^2) * u ^ (3:ℝ) := by
      rw [mul_pow, div_pow, show (u ^ ((3:ℝ)/2))^2 = u ^ ((3:ℝ)/2) * u ^ ((3:ℝ)/2) by ring,
        ← Real.rpow_add hu0]
      norm_num
    have h7 : (1/g)^2 = 1/g^2 := by
      rw [div_pow, one_pow]
    rw [h7, h6] at h5
    have h8 : 6/g^2 = 6*(1/g^2) := by ring
    rw [h8]
    linarith
  -- t3
  have ht3 : 2 * ((6 / g^2) * X ^ (1 + g : ℝ)) / T
      ≤ (48/c^2) * u ^ (3:ℝ) * (X * Real.exp (-(u/2))) := by
    have h1 : 2 * ((6 / g^2) * X ^ (1 + g : ℝ)) / T
        = 2 * (6 / g^2) * (X ^ (1 + g : ℝ) / T) := by ring
    rw [h1]
    calc 2 * (6 / g^2) * (X ^ (1 + g : ℝ) / T)
        ≤ 2 * (6 * ((4/c^2) * u ^ (3:ℝ))) * (X * Real.exp (-(u/2))) := by
          apply mul_le_mul (by linarith) hXgT (by positivity) (by positivity)
      _ = (48/c^2) * u ^ (3:ℝ) * (X * Real.exp (-(u/2))) := by ring
  have hR4a := poly_exp_absorption c (24*C) (6*C + 48/c^2) hc0 hc12 (by positivity) (by positivity)
    u (le_trans (le_max_right _ _) huM)
  have hsum : 6 * M * X ^ (1 - g/2 : ℝ)
      + 2 * (((1 + g) - (1 - g/2)) * (M * X ^ (1 + g : ℝ) / T^2))
      + 2 * ((6 / g^2) * X ^ (1 + g : ℝ)) / T
      ≤ (30*C + 48/c^2) * X * Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) := by
    have h2 : X * (24*C * u ^ ((5:ℝ)/2) * Real.exp (-((c/4) * u ^ ((1:ℝ)/2)))
          + (6*C + 48/c^2) * u ^ (3:ℝ) * Real.exp (-(u/2)))
        ≤ X * ((24*C + (6*C + 48/c^2)) * Real.exp (-((c/8) * u ^ ((1:ℝ)/2)))) := by
      apply mul_le_mul_of_nonneg_left hR4a hX0.le
    calc 6 * M * X ^ (1 - g/2 : ℝ)
        + 2 * (((1 + g) - (1 - g/2)) * (M * X ^ (1 + g : ℝ) / T^2))
        + 2 * ((6 / g^2) * X ^ (1 + g : ℝ)) / T
        ≤ 24*C * u ^ ((5:ℝ)/2) * (X * Real.exp (-((c/4) * u ^ ((1:ℝ)/2))))
          + 6*C * u ^ (3:ℝ) * (X * Real.exp (-(u/2)))
          + (48/c^2) * u ^ (3:ℝ) * (X * Real.exp (-(u/2))) := by
          exact add_le_add (add_le_add ht1 ht2) ht3
      _ = X * (24*C * u ^ ((5:ℝ)/2) * Real.exp (-((c/4) * u ^ ((1:ℝ)/2)))
          + (6*C + 48/c^2) * u ^ (3:ℝ) * Real.exp (-(u/2))) := by ring
      _ ≤ X * ((24*C + (6*C + 48/c^2)) * Real.exp (-((c/8) * u ^ ((1:ℝ)/2)))) := h2
      _ = (30*C + 48/c^2) * X * Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) := by ring
  have hfin : Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) ≤ Real.exp (-(c/8 * L ^ ((1:ℝ)/10))) := by
    apply Real.exp_le_exp.mpr
    have h1 : u ^ ((1:ℝ)/2) = L ^ ((1:ℝ)/4) := by
      rw [hudef, ← Real.rpow_mul hL0.le]
      norm_num
    have h2 : L ^ ((1:ℝ)/10) ≤ L ^ ((1:ℝ)/4) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    rw [h1]
    nlinarith
  have h2pi : (1:ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  calc ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X)‖
      ≤ (6 * M * X ^ (1 - g/2 : ℝ)
        + 2 * (((1 + g) - (1 - g/2)) * (M * X ^ (1 + g : ℝ) / T^2))
        + 2 * ((6 / g^2) * X ^ (1 + g : ℝ)) / T) / (2 * Real.pi) := hbound
    _ ≤ ((30*C + 48/c^2) * X * Real.exp (-((c/8) * u ^ ((1:ℝ)/2)))) / (2 * Real.pi) := by
        apply div_le_div_of_nonneg_right hsum (by positivity)
    _ ≤ (30*C + 48/c^2) * X * Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) := by
        apply div_le_self (by positivity) h2pi
    _ ≤ (30*C + 48/c^2) * X * Real.exp (-(c/8 * L ^ ((1:ℝ)/10))) := by
        apply mul_le_mul_of_nonneg_left hfin (by positivity)

open scoped Classical in
open ArithmeticFunction in
/-- **W3b-i: per-prime power-mass bound** — for a prime `p` and `X ≥ 2`, the von Mangoldt mass on
    powers of `p` up to `X` is at most `(log X / log 2 + 1)·log p`: there are at most
    `log X / log 2 + 1` exponents `k ≥ 1` with `p^k ≤ X`, each contributing `Λ(p^k) = log p`. -/
lemma vonMangoldt_prime_powers_le (p : ℕ) (hp : p.Prime) (X : ℕ) (hX : 2 ≤ X) :
    ∑ n ∈ (Finset.range (X+1)).filter (fun n => ∃ k, 1 ≤ k ∧ p ^ k = n),
      vonMangoldt n
    ≤ (Real.log X / Real.log 2 + 1) * Real.log p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : (0:ℝ) ≤ Real.log X := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  have hlogp : (0:ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  set K : ℕ := ⌊Real.log X / Real.log 2⌋₊ with hKdef
  -- the filter is the image of the exponents k ∈ Icc 1 K under k ↦ p^k
  have hsub : (Finset.range (X+1)).filter (fun n => ∃ k, 1 ≤ k ∧ p ^ k = n)
      ⊆ (Finset.Icc 1 K).image (fun k => p ^ k) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnX, k, hk1, hkn⟩ := hn
    rw [Finset.mem_image]
    refine ⟨k, ?_, hkn⟩
    rw [Finset.mem_Icc]
    refine ⟨hk1, ?_⟩
    -- p^k ≤ X ⇒ 2^k ≤ X ⇒ k·log2 ≤ logX ⇒ k ≤ K
    have h1 : p ^ k ≤ X := by omega
    have h2 : 2 ^ k ≤ X := le_trans (Nat.pow_le_pow_left hp2 k) h1
    have h3 : (k:ℝ) * Real.log 2 ≤ Real.log X := by
      have h4 : ((2:ℕ):ℝ) ^ k ≤ (X:ℝ) := by exact_mod_cast h2
      have h5 := Real.log_le_log (by positivity) h4
      rwa [Real.log_pow, Nat.cast_ofNat] at h5
    apply Nat.le_floor
    rw [le_div_iff₀ hlog2]
    exact h3
  have hnonneg : ∀ n ∈ (Finset.Icc 1 K).image (fun k => p ^ k), 0 ≤ vonMangoldt n :=
    fun n _ => vonMangoldt_nonneg
  calc ∑ n ∈ (Finset.range (X+1)).filter (fun n => ∃ k, 1 ≤ k ∧ p ^ k = n), vonMangoldt n
      ≤ ∑ n ∈ (Finset.Icc 1 K).image (fun k => p ^ k), vonMangoldt n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => vonMangoldt_nonneg)
    _ = ∑ k ∈ Finset.Icc 1 K, vonMangoldt (p ^ k) := by
        rw [Finset.sum_image]
        intro a _ b _ hab
        exact Nat.pow_right_injective hp2 hab
    _ = ∑ k ∈ Finset.Icc 1 K, Real.log p := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Icc] at hk
        rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0),
          ArithmeticFunction.vonMangoldt_apply_prime hp]
    _ = (K : ℝ) * Real.log p := by
        rw [Finset.sum_const, Nat.card_Icc]
        simp [nsmul_eq_mul]
    _ ≤ (Real.log X / Real.log 2 + 1) * Real.log p := by
        apply mul_le_mul_of_nonneg_right _ hlogp
        have := Nat.floor_le (by positivity : (0:ℝ) ≤ Real.log X / Real.log 2)
        rw [hKdef]
        linarith

open scoped Classical in
open ArithmeticFunction in
/-- **W3b-ii: the non-unit von Mangoldt mass is polylog** — for `q ≥ 1`, `X ≥ 2`:
    `∑_{n≤X, ¬IsUnit(n mod q)} Λ(n) ≤ (log X/log 2 + 1)·log q`. Prime-power support: each
    contributing `n = p^k` has `p ∣ q`; per-prime mass ≤ `(logX/log2+1)·log p` (W3b-i);
    `∑_{p∣q} log p = log ∏ p ≤ log q`. -/
lemma vonMangoldt_nonunit_sum_le (q : ℕ) [NeZero q] (X : ℕ) (hX : 2 ≤ X) :
    ∑ n ∈ (Finset.range (X+1)).filter (fun n => ¬ IsUnit ((n : ℕ) : ZMod q)), vonMangoldt n
    ≤ (Real.log X / Real.log 2 + 1) * Real.log q := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : (0:ℝ) ≤ Real.log X := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  have hcoef : (0:ℝ) ≤ Real.log X / Real.log 2 + 1 := by positivity
  -- drop the Λ = 0 terms
  rw [← Finset.sum_filter_ne_zero]
  -- the surviving support embeds in the union of p-power filters, p ∈ q.primeFactors
  set T := ((Finset.range (X+1)).filter (fun n => ¬ IsUnit ((n : ℕ) : ZMod q))).filter
    (fun n => vonMangoldt n ≠ 0) with hTdef
  have hsub : T ⊆ q.primeFactors.biUnion
      (fun p => (Finset.range (X+1)).filter (fun n => ∃ k, 1 ≤ k ∧ p ^ k = n)) := by
    intro n hn
    rw [hTdef, Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨⟨hnX, hnu⟩, hΛ⟩ := hn
    have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    obtain ⟨p, k, hp, hk, hpk⟩ := hpp
    have hpN : p.Prime := Nat.prime_iff.mpr hp
    -- ¬IsUnit(p^k mod q) ⇒ ¬coprime p q ⇒ p ∣ q
    have hpq : p ∣ q := by
      by_contra hnd
      apply hnu
      rw [ZMod.isUnit_iff_coprime]
      have h1 : Nat.Coprime p q := (Nat.Prime.coprime_iff_not_dvd hpN).mpr hnd
      have h2 : Nat.Coprime n q := by
        rw [← hpk]
        exact Nat.Coprime.pow_left k h1
      exact h2
    rw [Finset.mem_biUnion]
    refine ⟨p, ?_, ?_⟩
    · rw [Nat.mem_primeFactors]
      exact ⟨hpN, hpq, hq0⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hnX, k, hk, hpk⟩
  -- distinct primes give disjoint power filters
  have hdisj : ∀ p ∈ q.primeFactors, ∀ p' ∈ q.primeFactors, p ≠ p' →
      Disjoint ((Finset.range (X+1)).filter (fun n => ∃ k, 1 ≤ k ∧ p ^ k = n))
        ((Finset.range (X+1)).filter (fun n => ∃ k, 1 ≤ k ∧ p' ^ k = n)) := by
    intro p hp p' hp' hne
    rw [Finset.disjoint_left]
    intro n hn hn'
    rw [Finset.mem_filter] at hn hn'
    obtain ⟨-, k, hk1, hkn⟩ := hn
    obtain ⟨-, k', hk1', hkn'⟩ := hn'
    have hpN : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpN' : p'.Prime := (Nat.mem_primeFactors.mp hp').1
    apply hne
    have h1 : p ∣ p' ^ k' := by
      rw [hkn', ← hkn]
      exact dvd_pow_self p (by omega)
    have h2 : p ∣ p' := hpN.dvd_of_dvd_pow h1
    exact (Nat.prime_dvd_prime_iff_eq hpN hpN').mp h2
  calc ∑ n ∈ T, vonMangoldt n
      ≤ ∑ n ∈ q.primeFactors.biUnion
          (fun p => (Finset.range (X+1)).filter (fun n => ∃ k, 1 ≤ k ∧ p ^ k = n)),
          vonMangoldt n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n _ _
        exact vonMangoldt_nonneg
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ (Finset.range (X+1)).filter
          (fun n => ∃ k, 1 ≤ k ∧ p ^ k = n), vonMangoldt n :=
        Finset.sum_biUnion hdisj
    _ ≤ ∑ p ∈ q.primeFactors, (Real.log X / Real.log 2 + 1) * Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        exact vonMangoldt_prime_powers_le p (Nat.mem_primeFactors.mp hp).1 X hX
    _ = (Real.log X / Real.log 2 + 1) * ∑ p ∈ q.primeFactors, Real.log p := by
        rw [Finset.mul_sum]
    _ ≤ (Real.log X / Real.log 2 + 1) * Real.log q := by
        apply mul_le_mul_of_nonneg_left _ hcoef
        have h1 : ∑ p ∈ q.primeFactors, Real.log p
            = Real.log (∏ p ∈ q.primeFactors, (p:ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.mem_primeFactors.mp hp).1.pos.ne'
        rw [h1]
        have h2 : (∏ p ∈ q.primeFactors, p) ∣ q := Nat.prod_primeFactors_dvd q
        have h5 : 0 < ∏ p ∈ q.primeFactors, p :=
          Finset.prod_pos (fun p hp => (Nat.mem_primeFactors.mp hp).1.pos)
        have h3 : (∏ p ∈ q.primeFactors, p) ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) h2
        have h4 : (∏ p ∈ q.primeFactors, (p:ℝ)) = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
          push_cast
          rfl
        rw [h4]
        apply Real.log_le_log
        · exact_mod_cast h5
        · exact_mod_cast h3



/-- The explicit prime number theorem `|ψ(x) − x| ≤ C·x·exp(−c(log x)^{1/10})` (`x ≥ 2`): the
    statement of the master file's `medium_PNT` shim, which it proved from PrimeNumberTheoremAnd's
    `MediumPNT`. PNT+ pins a different Mathlib, so here it is NOT proved: the two theorems that
    need it (`psi_unit_sum_bound_of`, `siegel_walfisz_of_mediumPNT`) carry it as a hypothesis.
    Nothing else in `Principia.Common.SW` depends on it. -/
def MediumPNTBound : Prop := ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    |(∑ n ∈ Finset.range (⌊x⌋₊ + 1), ArithmeticFunction.vonMangoldt n) - x|
      ≤ C * x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10))

open scoped Classical in
open ArithmeticFunction in
/-- **W3c: the unit-restricted ψ obeys PNT with a polylog correction** — for every modulus
    `q ≥ 1` and `X ≥ 2`:
    `|∑_{n≤X, IsUnit(n mod q)} Λ(n) − X| ≤ C·X·exp(−c(log X)^{1/10}) + (logX/log2+1)·log q`.
    Split `ψ = unit-part + nonunit-part`; the hypothesis `MediumPNTBound` for the first, W3b-ii
    for the second.
    This is `ψ(X,χ₀)` (`MulChar.one_apply` gives the indicator), the χ₀ input to the W5 wiring. -/
theorem psi_unit_sum_bound_of (hPNT : MediumPNTBound) : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (q : ℕ) [NeZero q], ∀ X : ℝ, 2 ≤ X →
    |(∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0) - X|
      ≤ C * X * Real.exp (-c * Real.log X ^ ((1:ℝ)/10))
        + (Real.log X / Real.log 2 + 1) * Real.log q := by
  obtain ⟨c, C, hc, hC, hpnt⟩ := hPNT
  refine ⟨c, C, hc, hC, ?_⟩
  intro q _ X hX
  have hX0 : (0:ℝ) < X := by linarith
  have hXn : 2 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  have hfloor0 : (0:ℝ) < (⌊X⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊X⌋₊)
  have hfloorle : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX0.le
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : (0:ℝ) ≤ Real.log q := by
    apply Real.log_nonneg
    have : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast this
  -- ψ = unit + nonunit
  have hsplit : (∑ n ∈ Finset.range (⌊X⌋₊ + 1), vonMangoldt n)
      = (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0)
        + ∑ n ∈ (Finset.range (⌊X⌋₊ + 1)).filter (fun n => ¬ IsUnit ((n : ℕ) : ZMod q)),
            vonMangoldt n := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : IsUnit ((n : ℕ) : ZMod q) <;> simp [h]
  set U := ∑ n ∈ Finset.range (⌊X⌋₊ + 1),
    if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0 with hUdef
  set V := ∑ n ∈ (Finset.range (⌊X⌋₊ + 1)).filter (fun n => ¬ IsUnit ((n : ℕ) : ZMod q)),
    vonMangoldt n with hVdef
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun n _ => vonMangoldt_nonneg)
  -- V ≤ (log⌊X⌋/log2 + 1)·log q ≤ (logX/log2 + 1)·log q
  have hVle : V ≤ (Real.log X / Real.log 2 + 1) * Real.log q := by
    have h1 := vonMangoldt_nonunit_sum_le q (X := ⌊X⌋₊) hXn
    have h2 : Real.log (⌊X⌋₊ : ℝ) ≤ Real.log X := Real.log_le_log hfloor0 hfloorle
    have h3 : (Real.log (⌊X⌋₊ : ℝ) / Real.log 2 + 1) * Real.log q
        ≤ (Real.log X / Real.log 2 + 1) * Real.log q := by
      apply mul_le_mul_of_nonneg_right _ hlogq
      have := div_le_div_of_nonneg_right h2 hlog2.le
      linarith
    exact le_trans h1 h3
  have hpntX := hpnt X hX
  -- |U − X| = |(ψ − X) − V| ≤ |ψ − X| + V
  have habs : |U - X| ≤ |(∑ n ∈ Finset.range (⌊X⌋₊ + 1), vonMangoldt n) - X| + V := by
    have h4 : U - X = ((∑ n ∈ Finset.range (⌊X⌋₊ + 1), vonMangoldt n) - X) - V := by
      rw [hsplit]
      ring
    rw [h4]
    calc |((∑ n ∈ Finset.range (⌊X⌋₊ + 1), vonMangoldt n) - X) - V|
        ≤ |(∑ n ∈ Finset.range (⌊X⌋₊ + 1), vonMangoldt n) - X| + |V| := abs_sub _ _
      _ = |(∑ n ∈ Finset.range (⌊X⌋₊ + 1), vonMangoldt n) - X| + V := by
          rw [abs_of_nonneg hV0]
  calc |U - X| ≤ |(∑ n ∈ Finset.range (⌊X⌋₊ + 1), vonMangoldt n) - X| + V := habs
    _ ≤ C * X * Real.exp (-c * Real.log X ^ ((1:ℝ)/10))
        + (Real.log X / Real.log 2 + 1) * Real.log q := add_le_add hpntX hVle

open ArithmeticFunction in
/-- **W4a: the two-scale identity** — for `0 < X ≤ Y`:
    `Y·S(Y) − X·S(X) = (Y−X)·ψ_c(X) + ∑_{⌊X⌋<n≤⌊Y⌋} χΛ(n)(Y−n)`, where `S` is the smoothed sum
    and `ψ_c` the sharp one. Pure algebra: `Y(1−n/Y) = Y−n`, split `range(⌊Y⌋+1)` at `⌊X⌋+1`. -/
lemma two_scale_identity {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (X Y : ℝ)
    (hX : 0 < X) (hXY : X ≤ Y) :
    ((Y:ℝ) : ℂ) * (∑ n ∈ Finset.range (⌊Y⌋₊+1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / Y))
      - ((X:ℝ) : ℂ) * (∑ n ∈ Finset.range (⌊X⌋₊+1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X))
    = (((Y:ℝ) : ℂ) - ((X:ℝ) : ℂ)) * (∑ n ∈ Finset.range (⌊X⌋₊+1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
      + ∑ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ)) := by
  have hY0 : (0:ℝ) < Y := lt_of_lt_of_le hX hXY
  have hXC : ((X:ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hYC : ((Y:ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY0.ne'
  have hfloor : ⌊X⌋₊ + 1 ≤ ⌊Y⌋₊ + 1 := by
    have := Nat.floor_le_floor hXY
    omega
  -- per-term unsmoothing
  have hterm : ∀ (Z : ℝ) (hZ : ((Z:ℝ) : ℂ) ≠ 0) (n : ℕ),
      ((Z:ℝ) : ℂ) * (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / Z))
      = χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Z:ℝ) : ℂ) - ((n:ℝ) : ℂ)) := by
    intro Z hZ n
    have h1 : ((Z:ℝ) : ℂ) * (1 - ((n:ℝ) : ℂ) / ((Z:ℝ) : ℂ)) = ((Z:ℝ) : ℂ) - ((n:ℝ) : ℂ) := by
      field_simp
    calc ((Z:ℝ) : ℂ) * (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / Z))
        = χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)
            * (((Z:ℝ) : ℂ) * (1 - ((n:ℝ) : ℂ) / ((Z:ℝ) : ℂ))) := by
          push_cast
          ring
      _ = χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Z:ℝ) : ℂ) - ((n:ℝ) : ℂ)) := by
          rw [h1]
  -- unsmooth both scales
  rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [hterm Y hYC, hterm X hXC]
  -- split the Y-range at ⌊X⌋+1
  have hsplit : ∑ n ∈ Finset.range (⌊Y⌋₊+1),
      χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ))
      = (∑ n ∈ Finset.range (⌊X⌋₊+1),
          χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ)))
        + ∑ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1),
          χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ)) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le _) hfloor]
  rw [hsplit]
  have hAC : (∑ n ∈ Finset.range (⌊X⌋₊+1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ)))
      - (∑ n ∈ Finset.range (⌊X⌋₊+1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((X:ℝ) : ℂ) - ((n:ℝ) : ℂ)))
      = (((Y:ℝ) : ℂ) - ((X:ℝ) : ℂ)) * ∑ n ∈ Finset.range (⌊X⌋₊+1),
          χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  linear_combination hAC

open ArithmeticFunction in
/-- **W4b: the boundary window is small** — for `2 ≤ X ≤ Y`:
    `‖∑_{⌊X⌋<n≤⌊Y⌋} χΛ(n)(Y−n)‖ ≤ (Y−X+1)·((Y−X)·log Y)`: each of the ≤ `Y−X+1` terms has
    `Λ(n) ≤ log n ≤ log Y` and `0 ≤ Y−n ≤ Y−X`. -/
lemma boundary_sum_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (X Y : ℝ)
    (hX : 2 ≤ X) (hXY : X ≤ Y) :
    ‖∑ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ))‖
      ≤ (Y - X + 1) * ((Y - X) * Real.log Y) := by
  have hY2 : (2:ℝ) ≤ Y := le_trans hX hXY
  have hYX0 : (0:ℝ) ≤ Y - X := by linarith
  have hlogY : (0:ℝ) ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hfloorle : ⌊X⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_le_floor hXY
  -- per-term bound
  have hterm : ∀ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1),
      ‖χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ))‖
        ≤ (Y - X) * Real.log Y := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hnX : X < (n:ℝ) := by
      have h1 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
      have h2 : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
      push_cast at h2
      linarith
    have hnY : (n:ℝ) ≤ Y := by
      have h1 : n ≤ ⌊Y⌋₊ := by omega
      have h2 : ((n:ℕ):ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast h1
      have h3 : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
      linarith
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by linarith
    rw [norm_mul, norm_mul]
    have h4 : ‖((vonMangoldt n : ℝ) : ℂ)‖ ≤ Real.log Y := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      calc vonMangoldt n ≤ Real.log n := vonMangoldt_le_log
        _ ≤ Real.log Y := Real.log_le_log (by linarith) hnY
    have h5 : ‖((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ)‖ ≤ Y - X := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      linarith
    calc ‖χ (n : ZMod N)‖ * ‖((vonMangoldt n : ℝ) : ℂ)‖ * ‖((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ)‖
        ≤ 1 * Real.log Y * (Y - X) := by
          apply mul_le_mul _ h5 (norm_nonneg _) (by positivity)
          apply mul_le_mul (DirichletCharacter.norm_le_one χ _) h4 (norm_nonneg _) zero_le_one
      _ = (Y - X) * Real.log Y := by ring
  -- count bound
  have hcard : ((Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1)).card : ℝ) ≤ Y - X + 1 := by
    rw [Nat.card_Ico]
    have h1 : (⌊Y⌋₊ + 1) - (⌊X⌋₊ + 1) = ⌊Y⌋₊ - ⌊X⌋₊ := by omega
    rw [h1, Nat.cast_sub hfloorle]
    have h2 : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
    have h3 : X - 1 ≤ (⌊X⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one X
      linarith
    linarith
  calc ‖∑ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ))‖
      ≤ ∑ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1),
          ‖χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1), (Y - X) * Real.log Y :=
        Finset.sum_le_sum hterm
    _ = ((Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1)).card : ℝ) * ((Y - X) * Real.log Y) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Y - X + 1) * ((Y - X) * Real.log Y) := by
        apply mul_le_mul_of_nonneg_right hcard (by positivity)

/-- **W4c-i: solve the two-scale identity for the sharp sum** — from
    `Y·SY − X·SX = (Y−X)·ψc + R` with `X < Y` and norm bounds, conclude
    `‖ψc‖ ≤ (Y·BY + X·BX + Bnd)/(Y−X)`. -/
lemma sharp_recovery_norm (ψc SY SX R : ℂ) (X Y BY BX Bnd : ℝ)
    (hX : 0 < X) (hXY : X < Y)
    (hid : ((Y:ℝ) : ℂ) * SY - ((X:ℝ) : ℂ) * SX = (((Y:ℝ) : ℂ) - ((X:ℝ) : ℂ)) * ψc + R)
    (hSY : ‖SY‖ ≤ BY) (hSX : ‖SX‖ ≤ BX) (hR : ‖R‖ ≤ Bnd) :
    ‖ψc‖ ≤ (Y * BY + X * BX + Bnd) / (Y - X) := by
  have hYX0 : (0:ℝ) < Y - X := by linarith
  have h1 : (((Y:ℝ) : ℂ) - ((X:ℝ) : ℂ)) * ψc = ((Y:ℝ) : ℂ) * SY - ((X:ℝ) : ℂ) * SX - R := by
    rw [hid]
    ring
  have h2 : ‖(((Y:ℝ) : ℂ) - ((X:ℝ) : ℂ)) * ψc‖ = (Y - X) * ‖ψc‖ := by
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hYX0]
  have h3 : ‖((Y:ℝ) : ℂ) * SY - ((X:ℝ) : ℂ) * SX - R‖ ≤ Y * BY + X * BX + Bnd := by
    have hnY : ‖((Y:ℝ) : ℂ) * SY‖ ≤ Y * BY := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      exact mul_le_mul_of_nonneg_left hSY (by linarith)
    have hnX : ‖((X:ℝ) : ℂ) * SX‖ ≤ X * BX := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX]
      exact mul_le_mul_of_nonneg_left hSX hX.le
    calc ‖((Y:ℝ) : ℂ) * SY - ((X:ℝ) : ℂ) * SX - R‖
        ≤ ‖((Y:ℝ) : ℂ) * SY - ((X:ℝ) : ℂ) * SX‖ + ‖R‖ := norm_sub_le _ _
      _ ≤ (‖((Y:ℝ) : ℂ) * SY‖ + ‖((X:ℝ) : ℂ) * SX‖) + ‖R‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ Y * BY + X * BX + Bnd := by
          have := add_le_add (add_le_add hnY hnX) hR
          linarith
  rw [le_div_iff₀ hYX0]
  calc ‖ψc‖ * (Y - X) = (Y - X) * ‖ψc‖ := by ring
    _ = ‖(((Y:ℝ) : ℂ) - ((X:ℝ) : ℂ)) * ψc‖ := h2.symm
    _ = ‖((Y:ℝ) : ℂ) * SY - ((X:ℝ) : ℂ) * SX - R‖ := by rw [h1]
    _ ≤ Y * BY + X * BX + Bnd := h3

/-- **W4c-ii: polynomial absorption at linear exponent** — `u^m·e^{−a·u} ≤ e^{−(a/2)·u}` for
    `u ≥ max 1 (4m/a)²` (`m·log u ≤ 2m·√u ≤ (a/2)·u`). -/
lemma rpow_exp_absorb (a m : ℝ) (ha : 0 < a) (hm : 0 ≤ m) :
    ∀ u : ℝ, max 1 ((4*m/a)^2) ≤ u →
    u ^ (m : ℝ) * Real.exp (-(a * u)) ≤ Real.exp (-((a/2) * u)) := by
  intro u hu
  have hu1 : (1:ℝ) ≤ u := le_trans (le_max_left _ _) hu
  have hu0 : (0:ℝ) < u := by linarith
  have hum : (4*m/a)^2 ≤ u := le_trans (le_max_right _ _) hu
  have hsq : 4*m/a ≤ u ^ ((1:ℝ)/2) := by
    have h1 : ((4*m/a)^2) ^ ((1:ℝ)/2) ≤ u ^ ((1:ℝ)/2) :=
      Real.rpow_le_rpow (by positivity) hum (by norm_num)
    rwa [show ((4*m/a):ℝ)^2 = (4*m/a) * (4*m/a) by ring, ← Real.sqrt_eq_rpow,
      Real.sqrt_mul_self (by positivity)] at h1
  have hss : u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/2) = u := by
    rw [← Real.rpow_add hu0]
    norm_num
  have hs0 : (0:ℝ) ≤ u ^ ((1:ℝ)/2) := Real.rpow_nonneg hu0.le _
  -- log(u^m) = m·log u ≤ 2m·√u ≤ (a/2)·u
  have hlog : Real.log (u ^ (m:ℝ)) ≤ (a/2) * u := by
    rw [Real.log_rpow hu0]
    have h2 : Real.log u ≤ 2 * u ^ ((1:ℝ)/2) := by
      have := Real.log_le_rpow_div hu0.le (by norm_num : (0:ℝ) < 1/2)
      calc Real.log u ≤ u ^ ((1:ℝ)/2) / (1/2) := this
        _ = 2 * u ^ ((1:ℝ)/2) := by ring
    have h3 : m * Real.log u ≤ 2*m * u ^ ((1:ℝ)/2) := by nlinarith [Real.log_nonneg hu1]
    have h4 : 2*m * u ^ ((1:ℝ)/2) ≤ (a/2) * u := by
      have h5 : (4*m/a) * u ^ ((1:ℝ)/2) ≤ u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/2) :=
        mul_le_mul_of_nonneg_right hsq hs0
      rw [hss] at h5
      have h6 : a * ((4*m/a) * u ^ ((1:ℝ)/2)) = 4*m*u ^ ((1:ℝ)/2) := by
        field_simp
      nlinarith [h5, ha]
    linarith
  have h7 : u ^ (m:ℝ) ≤ Real.exp ((a/2) * u) :=
    (Real.log_le_iff_le_exp (Real.rpow_pos_of_pos hu0 _)).mp hlog
  calc u ^ (m:ℝ) * Real.exp (-(a * u))
      ≤ Real.exp ((a/2) * u) * Real.exp (-(a * u)) :=
        mul_le_mul_of_nonneg_right h7 (Real.exp_pos _).le
    _ = Real.exp (-((a/2) * u)) := by
        rw [← Real.exp_add]
        ring_nf

/-- **W4c-pre: the δ-choice facts** — with `δ = e^{−(a/2)u}` and `u ≥ max 2 (80/a)²`:
    (i) `e^{−au}/δ = δ`; (ii) `u^{10}·δ ≤ e^{−(a/4)u}`; (iii) `2u^{10} ≤ e^{u^{10}}·e^{−(a/4)u}`
    (the standalone-polylog absorption into `X = e^{u^{10}}`). -/
lemma delta_facts (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ u : ℝ, max 2 ((80/a)^2) ≤ u →
    Real.exp (-(a * u)) / Real.exp (-((a/2) * u)) = Real.exp (-((a/2) * u)) ∧
    u ^ (10:ℝ) * Real.exp (-((a/2) * u)) ≤ Real.exp (-((a/4) * u)) ∧
    2 * u ^ (10:ℝ) ≤ Real.exp (u ^ (10:ℝ)) * Real.exp (-((a/4) * u)) := by
  intro u hu
  have hu2 : (2:ℝ) ≤ u := le_trans (le_max_left _ _) hu
  have hu1 : (1:ℝ) ≤ u := by linarith
  have hu0 : (0:ℝ) < u := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- (i) exp division
    rw [← Real.exp_sub]
    congr 1
    ring
  · -- (ii) via rpow_exp_absorb at a' := a/2
    have h1 := rpow_exp_absorb (a/2) 10 (by linarith) (by norm_num) u ?_
    · have h2 : (a/2)/2 = a/4 := by ring
      rw [h2] at h1
      exact h1
    · apply max_le
      · linarith
      · have h3 : (4*10/(a/2)) = 80/a := by
          field_simp
          ring
        rw [h3]
        exact le_trans (le_max_right _ _) hu
  · -- (iii) log route: log 2 + 10·log u ≤ u^{10} − (a/4)u
    have hu10pos : (0:ℝ) < u ^ (10:ℝ) := Real.rpow_pos_of_pos hu0 _
    have hlog : Real.log (2 * u ^ (10:ℝ)) ≤ u ^ (10:ℝ) - (a/4) * u := by
      rw [Real.log_mul (by norm_num) hu10pos.ne', Real.log_rpow hu0]
      have h4 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9
        linarith
      have h5 : Real.log u ≤ 2 * u ^ ((1:ℝ)/2) := by
        have := Real.log_le_rpow_div hu0.le (by norm_num : (0:ℝ) < 1/2)
        calc Real.log u ≤ u ^ ((1:ℝ)/2) / (1/2) := this
          _ = 2 * u ^ ((1:ℝ)/2) := by ring
      have h6 : u ^ ((1:ℝ)/2) ≤ u := by
        calc u ^ ((1:ℝ)/2) ≤ u ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
          _ = u := Real.rpow_one u
      have h7 : u ^ (9:ℝ) ≥ 512 := by
        calc (512:ℝ) = 2 ^ (9:ℝ) := by
              rw [show (9:ℝ) = ((9:ℕ):ℝ) by norm_num, Real.rpow_natCast]
              norm_num
          _ ≤ u ^ (9:ℝ) := Real.rpow_le_rpow (by norm_num) hu2 (by norm_num)
      have h8 : u ^ (10:ℝ) = u ^ (9:ℝ) * u := by
        rw [show (10:ℝ) = 9 + 1 by norm_num, Real.rpow_add hu0, Real.rpow_one]
      have h9 : (a/4) * u ≤ u := by nlinarith
      have h56 : Real.log u ≤ 2*u := by nlinarith [h5, h6, Real.log_nonneg hu1]
      have hkey : u ^ (9:ℝ) * u ≥ 512 * u := by nlinarith [h7, hu0]
      have hA : u ^ (10:ℝ) ≥ 512 * u := by
        rw [h8]
        linarith
      have hC : Real.log 2 + 10 * Real.log u ≤ 1 + 20 * u := by linarith [h4, h56]
      calc Real.log 2 + 10 * Real.log u ≤ 1 + 20 * u := hC
        _ ≤ 511 * u := by linarith
        _ = 512 * u - u := by ring
        _ ≤ u ^ (10:ℝ) - u := sub_le_sub_right hA u
        _ ≤ u ^ (10:ℝ) - (a/4) * u := sub_le_sub_left h9 _
    have h10 : (0:ℝ) < 2 * u ^ (10:ℝ) := by positivity
    have h11 := (Real.log_le_iff_le_exp h10).mp hlog
    calc 2 * u ^ (10:ℝ) ≤ Real.exp (u ^ (10:ℝ) - (a/4) * u) := h11
      _ = Real.exp (u ^ (10:ℝ)) * Real.exp (-((a/4) * u)) := by
          rw [← Real.exp_add]
          ring_nf


open ArithmeticFunction in
/-- **W4c-MAIN: THE SHARP χ≠1 SIEGEL–WALFISZ BOUND** — for every `B ≥ 1` there are
    `c₅, C₅, X₀ > 0` with: for all `X ≥ X₀`, `q ≤ (log X)^B`, `χ ≠ 1 mod q`:
    `‖ψ(X,χ)‖ = ‖∑_{n≤X} χ(n)Λ(n)‖ ≤ C₅·X·exp(−c₅(log X)^{1/10})`. Two-scale recovery at
    `Y = X(1+δ)`, `δ = e^{−(c₂'/2)(log X)^{1/10}}`, from the smoothed bound at both scales. -/
theorem psi_sharp_SW_rate (B : ℝ) (hB : 1 ≤ B) :
    ∃ c₅ C₅ X₀ : ℝ, 0 < c₅ ∧ 0 < C₅ ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    (N:ℝ) ≤ Real.log X ^ (B : ℝ) →
    ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1), χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)‖
      ≤ C₅ * X * Real.exp (-(c₅ * Real.log X ^ ((1:ℝ)/10))) := by
  obtain ⟨c₂, C₂, X₀', hc₂0, hC₂0, hrate⟩ := psi_smooth_SW_rate B hB
  set a := min c₂ 1 with hadef
  have ha0 : 0 < a := lt_min hc₂0 one_pos
  have ha1 : a ≤ 1 := min_le_right _ _
  have hac₂ : a ≤ c₂ := min_le_left _ _
  set M := max 2 ((80/a)^2) with hMdef
  have hM2 : (2:ℝ) ≤ M := le_max_left _ _
  have hM0 : (0:ℝ) ≤ M := by linarith
  refine ⟨a/4, 5*C₂ + 3, max X₀' (Real.exp (M^10)), by positivity, by positivity, ?_⟩
  intro X hX N _ χ hχ hNB
  have hXX₀ : X₀' ≤ X := le_trans (le_max_left _ _) hX
  -- scales
  have hLM : M^10 ≤ Real.log X := by
    have h1 : Real.exp (M^10) ≤ X := le_trans (le_max_right _ _) hX
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  have hM10 : (1024:ℝ) ≤ M^10 := by
    calc (1024:ℝ) = 2^10 := by norm_num
      _ ≤ M^10 := by
          apply pow_le_pow_left₀ (by norm_num) hM2
  have hL1 : (1:ℝ) ≤ Real.log X := by linarith
  have hL0 : (0:ℝ) < Real.log X := by linarith
  have hX2 : (2:ℝ) ≤ X := by
    have h1 : Real.exp (M^10) ≤ X := le_trans (le_max_right _ _) hX
    have h2 : (2:ℝ) ≤ Real.exp (M^10) := by
      have h3 := Real.add_one_le_exp (M^10)
      linarith
    linarith
  have hX1 : (1:ℝ) < X := by linarith
  have hX0 : (0:ℝ) < X := by linarith
  set u := Real.log X ^ ((1:ℝ)/10) with hudef
  have hu0 : (0:ℝ) < u := Real.rpow_pos_of_pos hL0 _
  have huM : M ≤ u := by
    have h1 : (M^10) ^ ((1:ℝ)/10) ≤ (Real.log X) ^ ((1:ℝ)/10) :=
      Real.rpow_le_rpow (by positivity) hLM (by norm_num)
    rwa [show (M:ℝ)^10 = M^((10:ℕ):ℝ) from by rw [Real.rpow_natCast],
      ← Real.rpow_mul hM0, show ((10:ℕ):ℝ) * ((1:ℝ)/10) = 1 by norm_num,
      Real.rpow_one] at h1
  have hu1 : (1:ℝ) ≤ u := by linarith
  have hu10 : u ^ (10:ℝ) = Real.log X := by
    rw [hudef, ← Real.rpow_mul hL0.le]
    norm_num
  -- δ and Y
  set δ := Real.exp (-((a/2) * u)) with hδdef
  have hδ0 : (0:ℝ) < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := by
    rw [hδdef]
    apply Real.exp_le_one_iff.mpr
    nlinarith
  set Y := X * (1 + δ) with hYdef
  have hXY : X < Y := by
    rw [hYdef]
    nlinarith
  have hY2X : Y ≤ 2*X := by
    rw [hYdef]
    nlinarith
  have hYX₀ : X₀' ≤ Y := by linarith
  have hlogXY : Real.log X ≤ Real.log Y := Real.log_le_log hX0 hXY.le
  have hNB_Y : (N:ℝ) ≤ Real.log Y ^ (B : ℝ) := by
    calc (N:ℝ) ≤ Real.log X ^ (B:ℝ) := hNB
      _ ≤ Real.log Y ^ (B:ℝ) := Real.rpow_le_rpow hL0.le hlogXY (by linarith)
  -- smoothed bounds at both scales, weakened to the a-rate at X
  have hrX : Real.exp (-(c₂ * Real.log Y ^ ((1:ℝ)/10))) ≤ Real.exp (-(a * u)) := by
    apply Real.exp_le_exp.mpr
    have h1 : u ≤ Real.log Y ^ ((1:ℝ)/10) :=
      Real.rpow_le_rpow hL0.le hlogXY (by norm_num)
    nlinarith [Real.rpow_nonneg (Real.log_nonneg (by linarith : (1:ℝ) ≤ Y)) ((1:ℝ)/10), hu0]
  have hrXX : Real.exp (-(c₂ * Real.log X ^ ((1:ℝ)/10))) ≤ Real.exp (-(a * u)) := by
    apply Real.exp_le_exp.mpr
    rw [← hudef]
    nlinarith [hu0]
  have hSX := hrate X hXX₀ N χ hχ hNB
  have hSY := hrate Y hYX₀ N χ hχ hNB_Y
  have hSX' : ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1),
      χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X)‖
      ≤ C₂ * X * Real.exp (-(a * u)) := by
    calc ‖_‖ ≤ C₂ * X * Real.exp (-(c₂ * Real.log X ^ ((1:ℝ)/10))) := hSX
      _ ≤ C₂ * X * Real.exp (-(a * u)) := by
          apply mul_le_mul_of_nonneg_left hrXX (by positivity)
  have hSY' : ‖∑ n ∈ Finset.range (⌊Y⌋₊ + 1),
      χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / Y)‖
      ≤ C₂ * (2*X) * Real.exp (-(a * u)) := by
    calc ‖_‖ ≤ C₂ * Y * Real.exp (-(c₂ * Real.log Y ^ ((1:ℝ)/10))) := hSY
      _ ≤ C₂ * (2*X) * Real.exp (-(a * u)) := by
          apply mul_le_mul (by nlinarith) hrX (Real.exp_pos _).le (by positivity)
  -- the identity, boundary bound, and recovery
  have hid := two_scale_identity χ X Y hX0 hXY.le
  have hR := boundary_sum_bound χ X Y hX2 hXY.le
  have hrec := sharp_recovery_norm
    (∑ n ∈ Finset.range (⌊X⌋₊ + 1), χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
    (∑ n ∈ Finset.range (⌊Y⌋₊ + 1), χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / Y))
    (∑ n ∈ Finset.range (⌊X⌋₊ + 1), χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X))
    (∑ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1),
      χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ)))
    X Y (C₂ * (2*X) * Real.exp (-(a * u))) (C₂ * X * Real.exp (-(a * u)))
    ((Y - X + 1) * ((Y - X) * Real.log Y))
    hX0 hXY hid hSY' hSX' hR
  -- the δ-facts
  obtain ⟨hdf1, hdf2, hdf3⟩ := delta_facts a ha0 ha1 u (hMdef ▸ huM)
  -- numeric collapse
  have hYX : Y - X = δ * X := by rw [hYdef]; ring
  have hlog2X : Real.log Y ≤ 2 * u ^ (10:ℝ) := by
    have h1 : Real.log Y ≤ Real.log (2*X) := Real.log_le_log (by linarith) hY2X
    have h2 : Real.log (2*X) = Real.log 2 + Real.log X := Real.log_mul (by norm_num) hX0.ne'
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    rw [hu10]
    linarith [hL1]
  -- numeric collapse of the recovered bound
  set E := Real.exp (-(a * u)) with hEdef
  set F := Real.exp (-((a/4) * u)) with hFdef
  have hE0 : (0:ℝ) < E := Real.exp_pos _
  have hF0 : (0:ℝ) < F := Real.exp_pos _
  have hδF : δ ≤ F := by
    rw [hδdef, hFdef]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hEδ : E / δ = δ := hdf1
  have hu10F : u ^ (10:ℝ) * δ ≤ F := hdf2
  have h2u10 : 2 * u ^ (10:ℝ) ≤ X * F := by
    have h1 : Real.exp (u ^ (10:ℝ)) = X := by
      rw [hu10, Real.exp_log hX0]
    calc 2 * u ^ (10:ℝ) ≤ Real.exp (u ^ (10:ℝ)) * F := hdf3
      _ = X * F := by rw [h1]
  -- the divided pieces
  have hδX0 : (0:ℝ) < δ * X := by positivity
  have hnum1 : Y * (C₂ * (2*X) * E) + X * (C₂ * X * E) ≤ 5 * C₂ * X^2 * E := by
    have h1 : Y * (C₂ * (2*X) * E) ≤ (2*X) * (C₂ * (2*X) * E) := by
      apply mul_le_mul_of_nonneg_right hY2X (by positivity)
    nlinarith [hE0, hX0, hC₂0]
  have hdiv1 : (5 * C₂ * X^2 * E) / (δ * X) = 5 * C₂ * X * δ := by
    rw [show (5 * C₂ * X^2 * E) / (δ * X) = 5 * C₂ * X * (E / δ) from by
      field_simp]
    rw [hEδ]
  have hdiv2 : ((δ * X + 1) * ((δ * X) * Real.log Y)) / (δ * X)
      = (δ * X + 1) * Real.log Y := by
    field_simp
  -- assemble
  have hfinal : (Y * (C₂ * (2*X) * E) + X * (C₂ * X * E)
      + (Y - X + 1) * ((Y - X) * Real.log Y)) / (Y - X)
      ≤ (5*C₂ + 3) * X * F := by
    rw [hYX]
    rw [add_div]
    have hp1 : (Y * (C₂ * (2*X) * E) + X * (C₂ * X * E)) / (δ * X)
        ≤ (5 * C₂ * X^2 * E) / (δ * X) :=
      div_le_div_of_nonneg_right hnum1 hδX0.le
    rw [hdiv1] at hp1
    rw [hdiv2]
    have hp2 : 5 * C₂ * X * δ ≤ 5 * C₂ * X * F := by
      apply mul_le_mul_of_nonneg_left hδF (by positivity)
    have hp3 : (δ * X + 1) * Real.log Y ≤ (δ * X + 1) * (2 * u ^ (10:ℝ)) := by
      apply mul_le_mul_of_nonneg_left hlog2X (by positivity)
    have hp4 : (δ * X + 1) * (2 * u ^ (10:ℝ))
        = (2 * u ^ (10:ℝ) * δ) * X + 2 * u ^ (10:ℝ) := by ring
    have hp5 : (2 * u ^ (10:ℝ) * δ) * X ≤ 2 * F * X := by
      apply mul_le_mul_of_nonneg_right _ hX0.le
      calc 2 * u ^ (10:ℝ) * δ = 2 * (u ^ (10:ℝ) * δ) := by ring
        _ ≤ 2 * F := by linarith [hu10F]
    calc (Y * (C₂ * (2*X) * E) + X * (C₂ * X * E)) / (δ * X)
          + (δ * X + 1) * Real.log Y
        ≤ 5 * C₂ * X * δ + (δ * X + 1) * (2 * u ^ (10:ℝ)) := by
          linarith [hp1, hp3]
      _ ≤ 5 * C₂ * X * F + (2 * F * X + X * F) := by
          rw [hp4]
          have := add_le_add hp5 h2u10
          linarith [hp2, this]
      _ = (5*C₂ + 3) * X * F := by ring
  calc ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1), χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)‖
      ≤ (Y * (C₂ * (2*X) * E) + X * (C₂ * X * E)
          + (Y - X + 1) * ((Y - X) * Real.log Y)) / (Y - X) := hrec
    _ ≤ (5*C₂ + 3) * X * F := hfinal


open scoped Classical in
set_option maxHeartbeats 4000000 in
open DirichletCharacter Complex ArithmeticFunction Finset in
/-- **W5: SIEGEL–WALFISZ, the statement of the RatedWindow axiom, PROVEN** — orthogonality wiring
    of the χ₀ bound (W3) and the sharp χ≠1 bound (W4) with the character count `φ(q)`. -/
theorem siegel_walfisz_of_mediumPNT (hPNT : MediumPNTBound) (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log X ^ (B : ℝ) →
    ∀ a : ZMod q, IsUnit a →
    |(∑ n ∈ Finset.range (⌊X⌋₊ + 1), if a = ((n : ZMod q)) then vonMangoldt n else 0)
      - X / q.totient| ≤ C * X * Real.exp (-c * Real.log X ^ ((1:ℝ)/10)) := by
  obtain ⟨c₃, C₃, hc₃0, hC₃0, hχ₀⟩ := psi_unit_sum_bound_of hPNT
  obtain ⟨c₅, C₅, X₅, hc₅0, hC₅0, hsharp⟩ := psi_sharp_SW_rate B hB
  set c := min (min c₃ (c₅/2)) (1/2) with hcdef
  have hc0 : 0 < c := by
    apply lt_min (lt_min hc₃0 (by linarith)) (by norm_num)
  set M := max 2 (max ((40*B/c₅)^2) (Real.log (60*B))) with hMdef
  have hM2 : (2:ℝ) ≤ M := le_max_left _ _
  refine ⟨c, C₃ + C₅ + 1, by positivity, by positivity,
    max X₅ (Real.exp (M^10)), ?_⟩
  intro X hX q _ hqB a ha
  have hXX₅ : X₅ ≤ X := le_trans (le_max_left _ _) hX
  have hLM : M^10 ≤ Real.log X := by
    have h1 : Real.exp (M^10) ≤ X := le_trans (le_max_right _ _) hX
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  have hM10 : (1024:ℝ) ≤ M^10 := by
    calc (1024:ℝ) = 2^10 := by norm_num
      _ ≤ M^10 := pow_le_pow_left₀ (by norm_num) hM2 10
  have hL1 : (1:ℝ) ≤ Real.log X := by linarith
  have hL0 : (0:ℝ) < Real.log X := by linarith
  have hX2 : (2:ℝ) ≤ X := by
    have h1 : Real.exp (M^10) ≤ X := le_trans (le_max_right _ _) hX
    have h2 := Real.add_one_le_exp (M^10)
    linarith
  have hX0 : (0:ℝ) < X := by linarith
  set u := Real.log X ^ ((1:ℝ)/10) with hudef
  have hu0 : (0:ℝ) < u := Real.rpow_pos_of_pos hL0 _
  have huM : M ≤ u := by
    have h1 : (M^10) ^ ((1:ℝ)/10) ≤ (Real.log X) ^ ((1:ℝ)/10) :=
      Real.rpow_le_rpow (by positivity) hLM (by norm_num)
    rwa [show (M:ℝ)^10 = M^((10:ℕ):ℝ) from by rw [Real.rpow_natCast],
      ← Real.rpow_mul (by linarith : (0:ℝ) ≤ M),
      show ((10:ℕ):ℝ) * ((1:ℝ)/10) = 1 by norm_num, Real.rpow_one] at h1
  have hu2 : (2:ℝ) ≤ u := le_trans hM2 huM
  have hu10 : u ^ (10:ℝ) = Real.log X := by
    rw [hudef, ← Real.rpow_mul hL0.le]
    norm_num
  -- q and totient facts
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hφ1 : 1 ≤ q.totient := Nat.totient_pos.mpr (by omega)
  have hφq : q.totient ≤ q := Nat.totient_le q
  -- the ℂ-level orthogonality split
  have hAP := psi_ap_orthogonality q a ha (⌊X⌋₊ + 1)
  have ha_inv : IsUnit (a⁻¹ : ZMod q) :=
    IsUnit.of_mul_eq_one a (ZMod.inv_mul_of_unit a ha)
  have hone : (1 : DirichletCharacter ℂ q) a⁻¹ = 1 := MulChar.one_apply ha_inv
  -- ψ₀ as the real unit-restricted sum
  have hψ₀ : (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
      (1 : DirichletCharacter ℂ q) ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ))
      = (((∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0 : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : IsUnit ((n : ℕ) : ZMod q)
    · rw [MulChar.one_apply h, if_pos h, one_mul]
    · rw [MulChar.map_nonunit _ h, if_neg h, zero_mul, Complex.ofReal_zero]
  -- the real AP-sum bridge
  have hSreal : (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
      if a = ((n : ZMod q)) then ((vonMangoldt n : ℝ) : ℂ) else 0)
      = (((∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          if a = ((n : ZMod q)) then vonMangoldt n else 0 : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : a = ((n : ZMod q))
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, Complex.ofReal_zero]
  -- split the character sum at χ₀
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q)),
    hone, one_mul, hψ₀] at hAP
  -- per-χ≠1 sharp bounds
  have hqB' : (q:ℝ) ≤ Real.log X ^ (B:ℝ) := hqB
  have hsharp' : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      ‖χ a⁻¹ * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ))‖
      ≤ C₅ * X * Real.exp (-(c₅ * u)) := by
    intro χ hχ
    have hne := Finset.ne_of_mem_erase hχ
    rw [norm_mul]
    calc ‖χ a⁻¹‖ * ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ)‖
        ≤ 1 * (C₅ * X * Real.exp (-(c₅ * u))) := by
          apply mul_le_mul (DirichletCharacter.norm_le_one χ _) _ (norm_nonneg _) zero_le_one
          rw [hudef]
          exact hsharp X hXX₅ q χ hne hqB'
      _ = C₅ * X * Real.exp (-(c₅ * u)) := one_mul _
  -- character count
  have hcard : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card
      = q.totient - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  have hsum_erase : ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      χ a⁻¹ * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ))‖
      ≤ ((q.totient - 1 : ℕ) : ℝ) * (C₅ * X * Real.exp (-(c₅ * u))) := by
    calc ‖_‖ ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖χ a⁻¹ * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
            χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ _χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          (C₅ * X * Real.exp (-(c₅ * u))) := Finset.sum_le_sum hsharp'
      _ = ((q.totient - 1 : ℕ) : ℝ) * (C₅ * X * Real.exp (-(c₅ * u))) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
  -- q ≤ u^{10B} and the character-count absorption
  have hq_u : (q:ℝ) ≤ u ^ (10*B : ℝ) := by
    calc (q:ℝ) ≤ Real.log X ^ (B:ℝ) := hqB
      _ = u ^ (10*B : ℝ) := by
          rw [← hu10, ← Real.rpow_mul (Real.rpow_nonneg hL0.le _)]
  have habsorb : u ^ (10*B : ℝ) * Real.exp (-(c₅ * u)) ≤ Real.exp (-((c₅/2) * u)) := by
    apply rpow_exp_absorb c₅ (10*B) hc₅0 (by linarith) u
    apply max_le (by linarith)
    calc (4*(10*B)/c₅)^2 = (40*B/c₅)^2 := by ring_nf
      _ ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
      _ ≤ u := huM
  have hcount : ((q.totient - 1 : ℕ) : ℝ) * (C₅ * X * Real.exp (-(c₅ * u)))
      ≤ C₅ * X * Real.exp (-((c₅/2) * u)) := by
    have h1 : ((q.totient - 1 : ℕ) : ℝ) ≤ (q:ℝ) := by
      have h2 : q.totient - 1 ≤ q := by omega
      exact_mod_cast h2
    calc ((q.totient - 1 : ℕ) : ℝ) * (C₅ * X * Real.exp (-(c₅ * u)))
        ≤ u ^ (10*B : ℝ) * (C₅ * X * Real.exp (-(c₅ * u))) := by
          apply mul_le_mul_of_nonneg_right (le_trans h1 hq_u) (by positivity)
      _ = C₅ * X * (u ^ (10*B : ℝ) * Real.exp (-(c₅ * u))) := by ring
      _ ≤ C₅ * X * Real.exp (-((c₅/2) * u)) := by
          apply mul_le_mul_of_nonneg_left habsorb (by positivity)
  -- the χ₀ deviation with its polylog absorbed
  have hχ₀X := hχ₀ q X hX2
  have hpolylog : (Real.log X / Real.log 2 + 1) * Real.log q ≤ X * Real.exp (-((1:ℝ)/2 * u)) := by
    have hlog2 : (1:ℝ)/2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have h1 : Real.log X / Real.log 2 + 1 ≤ 3 * u ^ (10:ℝ) := by
      have h2 : Real.log X / Real.log 2 ≤ 2 * Real.log X := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [hL0]
      have h3 : (1:ℝ) ≤ u ^ (10:ℝ) := by
        rw [hu10]
        exact hL1
      have h3b : u ^ (10:ℝ) = Real.log X := hu10
      linarith
    have h4 : Real.log q ≤ 20 * B * u := by
      rcases eq_or_lt_of_le hq1 with heq | hgt
      · rw [← heq]
        simp
        positivity
      · have h5 : Real.log q ≤ Real.log (Real.log X ^ (B:ℝ)) :=
          Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)) hqB
        rw [Real.log_rpow hL0, ← hu10, Real.log_rpow hu0] at h5
        have h6 : Real.log u ≤ 2 * u ^ ((1:ℝ)/2) := by
          have := Real.log_le_rpow_div hu0.le (by norm_num : (0:ℝ) < 1/2)
          calc Real.log u ≤ u ^ ((1:ℝ)/2) / (1/2) := this
            _ = 2 * u ^ ((1:ℝ)/2) := by ring
        have h7 : u ^ ((1:ℝ)/2) ≤ u := by
          calc u ^ ((1:ℝ)/2) ≤ u ^ (1:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
            _ = u := Real.rpow_one u
        calc Real.log q ≤ B * (10 * Real.log u) := h5
          _ ≤ B * (10 * (2 * u)) := by
              apply mul_le_mul_of_nonneg_left _ (by linarith)
              nlinarith [h6, h7]
          _ = 20 * B * u := by ring
    have h8 : (Real.log X / Real.log 2 + 1) * Real.log q ≤ 60 * B * u ^ (11:ℝ) := by
      have h9 : (0:ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
      have h10 : u ^ (10:ℝ) * u = u ^ (11:ℝ) := by
        rw [show (11:ℝ) = 10 + 1 by norm_num, Real.rpow_add hu0, Real.rpow_one]
      calc (Real.log X / Real.log 2 + 1) * Real.log q
          ≤ (3 * u ^ (10:ℝ)) * (20 * B * u) := by
            apply mul_le_mul h1 h4 h9 (by positivity)
        _ = 60 * B * (u ^ (10:ℝ) * u) := by ring
        _ = 60 * B * u ^ (11:ℝ) := by rw [h10]
    -- 60B·u^{11} ≤ X·e^{−u/2} via the log route
    have hB60 : (0:ℝ) < 60 * B := by linarith
    have hu11pos : (0:ℝ) < u ^ (11:ℝ) := Real.rpow_pos_of_pos hu0 _
    have h11 : Real.log (60 * B * u ^ (11:ℝ)) ≤ Real.log X - (1:ℝ)/2 * u := by
      rw [Real.log_mul hB60.ne' hu11pos.ne', Real.log_rpow hu0]
      have hlogB : Real.log (60 * B) ≤ u :=
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) huM
      have h6 : Real.log u ≤ 2 * u ^ ((1:ℝ)/2) := by
        have := Real.log_le_rpow_div hu0.le (by norm_num : (0:ℝ) < 1/2)
        calc Real.log u ≤ u ^ ((1:ℝ)/2) / (1/2) := this
          _ = 2 * u ^ ((1:ℝ)/2) := by ring
      have h7 : u ^ ((1:ℝ)/2) ≤ u := by
        calc u ^ ((1:ℝ)/2) ≤ u ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          _ = u := Real.rpow_one u
      have h6b : Real.log u ≤ 2 * u := by linarith
      have h9 : (512:ℝ) ≤ u ^ (9:ℝ) := by
        calc (512:ℝ) = 2 ^ (9:ℝ) := by
              rw [show (9:ℝ) = ((9:ℕ):ℝ) by norm_num, Real.rpow_natCast]
              norm_num
          _ ≤ u ^ (9:ℝ) := Real.rpow_le_rpow (by norm_num) hu2 (by norm_num)
      have h10' : u ^ (10:ℝ) = u ^ (9:ℝ) * u := by
        rw [show (10:ℝ) = 9 + 1 by norm_num, Real.rpow_add hu0, Real.rpow_one]
      have h512 : 512 * u ≤ u ^ (10:ℝ) := by
        rw [h10']
        nlinarith [hu0]
      have hLX : u ^ (10:ℝ) = Real.log X := hu10
      linarith
    have h12 : 60 * B * u ^ (11:ℝ) ≤ X * Real.exp (-((1:ℝ)/2 * u)) := by
      have h13 := (Real.log_le_iff_le_exp (mul_pos hB60 hu11pos)).mp h11
      calc 60 * B * u ^ (11:ℝ) ≤ Real.exp (Real.log X - (1:ℝ)/2 * u) := h13
        _ = X * Real.exp (-((1:ℝ)/2 * u)) := by
            rw [show Real.log X - (1:ℝ)/2 * u = Real.log X + -((1:ℝ)/2 * u) by ring,
              Real.exp_add, Real.exp_log hX0]
    exact le_trans h8 h12
  -- χ₀ deviation, complex side
  have hψ₀dev : ‖((((∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0) : ℝ)) : ℂ) - ((X:ℝ) : ℂ)‖
      ≤ C₃ * X * Real.exp (-(c₃ * u)) + X * Real.exp (-((1:ℝ)/2 * u)) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    calc |(∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0) - X|
        ≤ C₃ * X * Real.exp (-c₃ * Real.log X ^ ((1:ℝ)/10))
          + (Real.log X / Real.log 2 + 1) * Real.log q := hχ₀X
      _ ≤ C₃ * X * Real.exp (-(c₃ * u)) + X * Real.exp (-((1:ℝ)/2 * u)) := by
          apply add_le_add _ hpolylog
          rw [← hudef, neg_mul]
  -- exponent comparisons to the common rate c
  have hec₃ : Real.exp (-(c₃ * u)) ≤ Real.exp (-(c * u)) := by
    apply Real.exp_le_exp.mpr
    have hcc : c ≤ c₃ := le_trans (min_le_left _ _) (min_le_left _ _)
    have := mul_le_mul_of_nonneg_right hcc hu0.le
    linarith
  have hec₅ : Real.exp (-((c₅/2) * u)) ≤ Real.exp (-(c * u)) := by
    apply Real.exp_le_exp.mpr
    have hcc : c ≤ c₅/2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have := mul_le_mul_of_nonneg_right hcc hu0.le
    linarith
  have heh : Real.exp (-((1:ℝ)/2 * u)) ≤ Real.exp (-(c * u)) := by
    apply Real.exp_le_exp.mpr
    have hcc : c ≤ 1/2 := min_le_right _ _
    have := mul_le_mul_of_nonneg_right hcc hu0.le
    linarith
  -- deviation identity from orthogonality
  have hdev : ((q.totient : ℕ) : ℂ) * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        if a = ((n : ZMod q)) then ((vonMangoldt n : ℝ) : ℂ) else 0) - ((X:ℝ) : ℂ)
      = (((((∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0) : ℝ)) : ℂ) - ((X:ℝ) : ℂ))
        + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            χ a⁻¹ * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
              χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ)) := by
    linear_combination hAP
  -- complex-side master bound
  have hnorm : ‖((q.totient : ℕ) : ℂ) * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        if a = ((n : ZMod q)) then ((vonMangoldt n : ℝ) : ℂ) else 0) - ((X:ℝ) : ℂ)‖
      ≤ (C₃ + C₅ + 1) * (X * Real.exp (-(c * u))) := by
    rw [hdev]
    have hstep : ‖(((((∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0) : ℝ)) : ℂ) - ((X:ℝ) : ℂ))
        + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            χ a⁻¹ * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
              χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ))‖
        ≤ (C₃ * X * Real.exp (-(c₃ * u)) + X * Real.exp (-((1:ℝ)/2 * u)))
          + C₅ * X * Real.exp (-((c₅/2) * u)) :=
      le_trans (norm_add_le _ _) (add_le_add hψ₀dev (le_trans hsum_erase hcount))
    have b₁ : C₃ * X * Real.exp (-(c₃ * u)) ≤ C₃ * X * Real.exp (-(c * u)) :=
      mul_le_mul_of_nonneg_left hec₃ (mul_nonneg hC₃0.le hX0.le)
    have b₂ : X * Real.exp (-((1:ℝ)/2 * u)) ≤ X * Real.exp (-(c * u)) :=
      mul_le_mul_of_nonneg_left heh hX0.le
    have b₃ : C₅ * X * Real.exp (-((c₅/2) * u)) ≤ C₅ * X * Real.exp (-(c * u)) :=
      mul_le_mul_of_nonneg_left hec₅ (mul_nonneg hC₅0.le hX0.le)
    have hfold : C₃ * X * Real.exp (-(c * u)) + X * Real.exp (-(c * u))
        + C₅ * X * Real.exp (-(c * u)) = (C₃ + C₅ + 1) * (X * Real.exp (-(c * u))) := by
      ring
    linarith
  -- real bridge
  have hreal : |(q.totient : ℝ) * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        if a = ((n : ZMod q)) then vonMangoldt n else 0) - X|
      ≤ (C₃ + C₅ + 1) * (X * Real.exp (-(c * u))) := by
    have hcast : ((q.totient : ℕ) : ℂ) * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          if a = ((n : ZMod q)) then ((vonMangoldt n : ℝ) : ℂ) else 0) - ((X:ℝ) : ℂ)
        = ((((q.totient : ℝ) * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
            if a = ((n : ZMod q)) then vonMangoldt n else 0) - X) : ℝ) : ℂ) := by
      rw [hSreal]
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hnorm
    exact hnorm
  -- divide by φ(q)
  have hφ0 : (0:ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hφ1
  have hφ1' : (1:ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast hφ1
  have hfinal : |(∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        if a = ((n : ZMod q)) then vonMangoldt n else 0) - X / q.totient|
      ≤ (C₃ + C₅ + 1) * (X * Real.exp (-(c * u))) := by
    have hdiv : (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          if a = ((n : ZMod q)) then vonMangoldt n else 0) - X / q.totient
        = ((q.totient : ℝ) * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
            if a = ((n : ZMod q)) then vonMangoldt n else 0) - X) / q.totient := by
      field_simp
    rw [hdiv, abs_div, abs_of_pos hφ0]
    exact le_trans (div_le_self (abs_nonneg _) hφ1') hreal
  have hassoc : (C₃ + C₅ + 1) * (X * Real.exp (-(c * u)))
      = (C₃ + C₅ + 1) * X * Real.exp (-(c * u)) := by ring
  rw [neg_mul]
  linarith [hfinal, hassoc]

end Principia.Common.SW
