/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.SW.Merge
import Principia.Common.SW.PerronKernel

/-!
# Siegel–Walfisz, `Perron`: the smoothed Perron formula and the contour shift

Ported **verbatim** from the axiom-clean Siegel–Walfisz master
(`Principia Application/LeanSandbox/SiegelWalfiszMaster.lean` = `C:/Users/Christian/pnt/sw_full.lean`,
lines 12875–14032; there `#print axioms siegel_walfisz_proven = [propext, Classical.choice, Quot.sound]`,
built in the PrimeNumberTheoremAnd workspace on Mathlib `db127794`, one day from ours). The master
imported `Mathlib`, `PrimeNumberTheoremAnd.MediumPNT` and `PrimeNumberTheoremAnd.PerronFormula`; here
the Mathlib imports are narrowed, the two Perron-kernel shims are re-proved from Mathlib's Mellin
inversion (`Principia.Common.SW.PerronKernel`), and the `medium_PNT` shim is not ported (see
`MediumPNTBound` in `Principia.Common.SW.Rate`). Declarations live in `Principia.Common.SW`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DirichletCharacter Complex PowerSeries ArithmeticFunction Finset Filter Metric

namespace Principia.Common.SW

set_option maxHeartbeats 1000000
open DirichletCharacter Complex Metric MeasureTheory

/-- The smoothed-Perron integrand (duplicated def, identical to DirichletPsiExplicit/Frontier). -/
noncomputable def G' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (X : ℝ) : ℂ → ℂ :=
  fun s => (-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)
    * ((X : ℂ) ^ s / (s * (s + 1)))




/-- **W2d: cpow ratio of positive reals** — `(X:ℂ)^s/(n:ℂ)^s = ((X/n:ℝ):ℂ)^s` for positive real
    `X, n`: reduces the per-`n` summand `X^s·n^{−s}·kernel` to the Perron-kernel shape at
    `y = X/n`. Via `Complex.mul_cpow_ofReal_nonneg` on `X = (X/n)·n`. -/
lemma cpow_ratio (X n : ℝ) (hX : 0 < X) (hn : 0 < n) (s : ℂ) :
    (X : ℂ) ^ s / (n : ℂ) ^ s = (((X / n : ℝ)) : ℂ) ^ s := by
  have hXn : X = (X / n) * n := by field_simp
  have h1 : ((X : ℝ) : ℂ) ^ s = (((X / n : ℝ)) : ℂ) ^ s * ((n : ℝ) : ℂ) ^ s := by
    calc ((X : ℝ) : ℂ) ^ s = ((((X / n : ℝ)) : ℂ) * ((n : ℝ) : ℂ)) ^ s := by
          rw [← Complex.ofReal_mul, ← hXn]
      _ = (((X / n : ℝ)) : ℂ) ^ s * ((n : ℝ) : ℂ) ^ s :=
          Complex.mul_cpow_ofReal_nonneg (by positivity) hn.le s
  have hn0 : ((n : ℝ) : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn.ne')]
    exact Complex.exp_ne_zero _
  rw [h1]
  field_simp

open ArithmeticFunction in
/-- **W2b: the smoothed integrand as a tsum of Perron-kernel summands** — for `Re s > 1`, `X > 0`:
    `G'(s) = ∑'_n χ(n)Λ(n) · (X/n)^s/(s(s+1))` (the `n`-th summand in exactly the
    `perron_kernel_*` shape at `y = X/n`). Via `neg_logDeriv_LFunction_eq` + `tsum_mul_right` +
    per-`n` `cpow_ratio` (`n = 0` term vanishes since `Λ(0) = 0`). -/
lemma G_tsum_form {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (X : ℝ) (hX : 0 < X)
    {s : ℂ} (hs : 1 < s.re) :
    G' χ X s = ∑' n : ℕ,
      (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)) * ((((X / n : ℝ)) : ℂ) ^ s / (s * (s + 1))) := by
  rw [G', neg_logDeriv_LFunction_eq χ hs, LSeries, ← tsum_mul_right]
  apply tsum_congr
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · have hn0 : ((n:ℕ):ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [LSeries.term_of_ne_zero hn.ne']
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hratio := cpow_ratio X (n:ℝ) hX hnR s
    push_cast at hratio ⊢
    rw [← hratio]
    ring

open ArithmeticFunction in
/-- **W2c: the sum/integral interchange** — `∫_ℝ G'(σ+it) dt = ∑'_n ∫_ℝ h_n(t) dt` for `X>0`, `σ>1`:
    dominated by `Λ(n)(X/n)^σ·(1+t²)⁻¹` (integrable in `t`, summable in `n`). -/
lemma integral_G_tsum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (X σ : ℝ)
    (hX : 0 < X) (hσ : 1 < σ) :
    (∫ t : ℝ, G' χ X ((σ:ℂ) + t * I))
      = ∑' n : ℕ, ∫ t : ℝ,
        (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
          * ((((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1))) := by
  have hre : ∀ t : ℝ, ((σ:ℂ) + (t:ℂ) * I).re = σ := fun t => by simp
  have hs1 : ∀ t : ℝ, 1 < ((σ:ℂ) + (t:ℂ) * I).re := fun t => by rw [hre]; exact hσ
  set h : ℕ → ℝ → ℂ := fun n t =>
    (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
      * ((((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I) / (((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1)))
    with hdef
  have hden : ∀ t : ℝ, (1:ℝ) + t^2 ≤ ‖(σ:ℂ) + (t:ℂ) * I‖ * ‖(σ:ℂ) + (t:ℂ) * I + 1‖ := by
    intro t
    have e1 : ‖(σ:ℂ) + (t:ℂ) * I‖ = Real.sqrt (σ^2 + t^2) := Complex.norm_add_mul_I σ t
    have e2 : (σ:ℂ) + (t:ℂ) * I + 1 = ((σ + 1 : ℝ) : ℂ) + (t:ℂ) * I := by push_cast; ring
    have e3 : ‖(σ:ℂ) + (t:ℂ) * I + 1‖ = Real.sqrt ((σ+1)^2 + t^2) := by
      rw [e2]; exact Complex.norm_add_mul_I _ _
    rw [e1, e3]
    have h1 : Real.sqrt (σ^2 + t^2) * Real.sqrt (σ^2 + t^2)
        ≤ Real.sqrt (σ^2 + t^2) * Real.sqrt ((σ+1)^2 + t^2) := by
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by nlinarith)) (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt (by positivity)] at h1
    nlinarith [h1, sq_nonneg t]
  have hdenpos : ∀ t : ℝ, (0:ℝ) < ‖(σ:ℂ) + (t:ℂ) * I‖ * ‖(σ:ℂ) + (t:ℂ) * I + 1‖ := by
    intro t
    have := hden t
    nlinarith [sq_nonneg t]
  have hdenne : ∀ t : ℝ, ((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1) ≠ 0 := by
    intro t hzero
    have h2 : ‖((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1)‖ = 0 := by rw [hzero, norm_zero]
    rw [norm_mul] at h2
    nlinarith [hdenpos t]
  have hzero0 : h 0 = fun _ => 0 := by
    funext t
    simp [hdef, ArithmeticFunction.map_zero]
  have hnorm : ∀ n : ℕ, 0 < n → ∀ t : ℝ,
      ‖h n t‖ ≤ (vonMangoldt n * (X/n) ^ (σ:ℝ)) * (1 + t^2)⁻¹ := by
    intro n hn t
    have hy0 : (0:ℝ) < X / n := by positivity
    have h1 : ‖(((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I)‖ = (X/n) ^ (σ:ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0, hre]
    have h2 : ‖χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)‖ ≤ vonMangoldt n := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      calc ‖χ (n : ZMod N)‖ * vonMangoldt n ≤ 1 * vonMangoldt n :=
            mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) vonMangoldt_nonneg
        _ = vonMangoldt n := one_mul _
    have h4 : (0:ℝ) < 1 + t^2 := by positivity
    rw [hdef]
    simp only []
    rw [norm_mul, norm_mul, norm_div, h1]
    have h3 : (1:ℝ) + t^2 ≤ ‖((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1)‖ := by
      rw [norm_mul]; exact hden t
    have hΛ : ‖((vonMangoldt n : ℝ) : ℂ)‖ = vonMangoldt n := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    calc ‖χ (n : ZMod N)‖ * ‖((vonMangoldt n : ℝ) : ℂ)‖
          * ((X/n) ^ (σ:ℝ) / ‖((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1)‖)
        ≤ 1 * vonMangoldt n * ((X/n) ^ (σ:ℝ) / (1 + t^2)) := by
          apply mul_le_mul
          · exact mul_le_mul (DirichletCharacter.norm_le_one χ _) (le_of_eq hΛ)
              (norm_nonneg _) zero_le_one
          · exact div_le_div_of_nonneg_left (by positivity) h4 h3
          · positivity
          · exact mul_nonneg zero_le_one vonMangoldt_nonneg
      _ = (vonMangoldt n * (X/n) ^ (σ:ℝ)) * (1 + t^2)⁻¹ := by
          rw [div_eq_mul_inv]; ring
  have hInt : ∀ n : ℕ, Integrable (h n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hzero0]
      exact integrable_zero _ _ _
    · have hy0 : (0:ℝ) < X / n := by positivity
      have hyC : (((X / n : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy0.ne'
      have hcpow : Continuous (fun t : ℝ => (((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I)) := by
        have he : (fun t : ℝ => (((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I))
            = fun t : ℝ => Complex.exp (Complex.log (((X / n : ℝ)) : ℂ) * ((σ:ℂ) + (t:ℂ) * I)) := by
          funext t
          rw [Complex.cpow_def_of_ne_zero hyC]
        rw [he]
        fun_prop
      have hcont : Continuous (h n) := by
        rw [hdef]
        simp only []
        apply Continuous.mul continuous_const
        exact Continuous.div hcpow (by fun_prop) hdenne
      apply Integrable.mono' (g := fun t : ℝ => (vonMangoldt n * (X/n) ^ (σ:ℝ)) * (1 + t^2)⁻¹)
        (integrable_inv_one_add_sq.const_mul _) hcont.aestronglyMeasurable
      exact Filter.Eventually.of_forall (hnorm n hn)
  have hIntNorm : ∀ n : ℕ, 0 < n →
      (∫ t : ℝ, ‖h n t‖) ≤ (vonMangoldt n * (X/n) ^ (σ:ℝ)) * Real.pi := by
    intro n hn
    calc (∫ t : ℝ, ‖h n t‖)
        ≤ ∫ t : ℝ, (vonMangoldt n * (X/n) ^ (σ:ℝ)) * (1 + t^2)⁻¹ := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
            (integrable_inv_one_add_sq.const_mul _)
            (Filter.Eventually.of_forall (hnorm n hn))
      _ = (vonMangoldt n * (X/n) ^ (σ:ℝ)) * ∫ t : ℝ, (1 + t^2)⁻¹ :=
          integral_const_mul _ _
      _ = (vonMangoldt n * (X/n) ^ (σ:ℝ)) * Real.pi := by
          rw [integral_univ_inv_one_add_sq]
  have hSummable : Summable (fun n : ℕ => ∫ t : ℝ, ‖h n t‖) := by
    have hmaj : Summable (fun n : ℕ =>
        (Real.pi * X ^ (σ:ℝ)) * ‖LSeries.term (fun m : ℕ => ((vonMangoldt m : ℝ) : ℂ)) (σ:ℂ) n‖) := by
      apply Summable.mul_left
      apply summable_norm_iff.mpr
      exact LSeriesSummable_vonMangoldt (s := (σ:ℂ)) (by simpa using hσ)
    apply Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun t => norm_nonneg _)
      _ hmaj
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hzero0]
      simp
    · have hy0 : (0:ℝ) < X / n := by positivity
      have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
      calc (∫ t : ℝ, ‖h n t‖) ≤ (vonMangoldt n * (X/n) ^ (σ:ℝ)) * Real.pi := hIntNorm n hn
        _ = (Real.pi * X ^ (σ:ℝ)) * (vonMangoldt n / (n:ℝ) ^ (σ:ℝ)) := by
            rw [Real.div_rpow hX.le hnR.le]
            field_simp
        _ = (Real.pi * X ^ (σ:ℝ)) * ‖LSeries.term (fun m : ℕ => ((vonMangoldt m : ℝ) : ℂ)) (σ:ℂ) n‖ := by
            rw [LSeries.norm_term_eq]
            rw [if_neg hn.ne']
            congr 1
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
              Complex.ofReal_re]
  calc (∫ t : ℝ, G' χ X ((σ:ℂ) + t * I))
      = ∫ t : ℝ, ∑' n : ℕ, h n t := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro t
        exact G_tsum_form χ X hX (hs1 t)
    _ = ∑' n : ℕ, ∫ t : ℝ, h n t :=
        (integral_tsum_of_summable_integral_norm hInt hSummable).symm

open Filter Topology in
/-- **W2-y1: the Perron kernel at `y = 1` vanishes** — `(1/2π)·∫ 1^{σ+it}/((σ+it)(σ+it+1)) dt = 0`
    for `σ > 0`: dominated-convergence limit of `perron_kernel_gtOne` along `y_k = 1 + 1/(k+1) ↓ 1`
    (`1 − 1/y_k → 0`; domination `2^σ·(1+t²)⁻¹`-grade uniform for `y ≤ 2`). -/
lemma perron_kernel_one (σ : ℝ) (hσ : 0 < σ) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        (((1:ℝ) : ℂ) ^ ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1))
      = 0 := by
  -- the kernel and its denominator bounds
  have hre : ∀ t : ℝ, ((σ:ℂ) + (t:ℂ) * I).re = σ := fun t => by simp
  have hden : ∀ t : ℝ, min 1 (σ^2) + t^2 ≤ ‖(σ:ℂ) + (t:ℂ) * I‖ * ‖(σ:ℂ) + (t:ℂ) * I + 1‖ := by
    intro t
    have e1 : ‖(σ:ℂ) + (t:ℂ) * I‖ = Real.sqrt (σ^2 + t^2) := Complex.norm_add_mul_I σ t
    have e2 : (σ:ℂ) + (t:ℂ) * I + 1 = ((σ + 1 : ℝ) : ℂ) + (t:ℂ) * I := by push_cast; ring
    have e3 : ‖(σ:ℂ) + (t:ℂ) * I + 1‖ = Real.sqrt ((σ+1)^2 + t^2) := by
      rw [e2]; exact Complex.norm_add_mul_I _ _
    rw [e1, e3]
    have h1 : Real.sqrt (σ^2 + t^2) * Real.sqrt (σ^2 + t^2)
        ≤ Real.sqrt (σ^2 + t^2) * Real.sqrt ((σ+1)^2 + t^2) := by
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by nlinarith)) (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt (by positivity)] at h1
    have h2 : min 1 (σ^2) ≤ σ^2 := min_le_right _ _
    nlinarith [h1]
  have hm0 : (0:ℝ) < min 1 (σ^2) := lt_min one_pos (pow_pos hσ 2)
  have hdenpos : ∀ t : ℝ, (0:ℝ) < ‖(σ:ℂ) + (t:ℂ) * I‖ * ‖(σ:ℂ) + (t:ℂ) * I + 1‖ := by
    intro t
    have := hden t
    nlinarith [sq_nonneg t]
  -- the y-parameterized integrand family and its uniform bound (1 ≤ y ≤ 2)
  set F : ℕ → ℝ → ℂ := fun k t =>
    (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I)
      / (((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1)) with hFdef
  set f : ℝ → ℂ := fun t =>
    (((1:ℝ) : ℂ)) ^ ((σ:ℂ) + (t:ℂ) * I)
      / (((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1)) with hfdef
  have hyk : ∀ k : ℕ, (1:ℝ) < 1 + 1/((k:ℝ)+1) := by
    intro k
    have : (0:ℝ) < 1/((k:ℝ)+1) := by positivity
    linarith
  have hyk2 : ∀ k : ℕ, (1:ℝ) + 1/((k:ℝ)+1) ≤ 2 := by
    intro k
    have h1 : (1:ℝ) ≤ (k:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have : 1/((k:ℝ)+1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact h1
    linarith
  have hbound : ∀ k : ℕ, ∀ t : ℝ,
      ‖F k t‖ ≤ (2 ^ (σ:ℝ)) * ((min 1 (σ^2) + t^2)⁻¹) := by
    intro k t
    rw [hFdef]
    simp only []
    rw [norm_div, norm_mul]
    have h1 : ‖(((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I)‖
        = (1 + 1/((k:ℝ)+1)) ^ (σ:ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hyk k]), hre]
    rw [h1]
    have h2 : (1 + 1/((k:ℝ)+1)) ^ (σ:ℝ) ≤ 2 ^ (σ:ℝ) :=
      Real.rpow_le_rpow (by linarith [hyk k]) (hyk2 k) hσ.le
    have h3 := hden t
    have h4 : (0:ℝ) < min 1 (σ^2) + t^2 := by nlinarith [sq_nonneg t]
    calc (1 + 1/((k:ℝ)+1)) ^ (σ:ℝ) / (‖(σ:ℂ) + (t:ℂ) * I‖ * ‖(σ:ℂ) + (t:ℂ) * I + 1‖)
        ≤ 2 ^ (σ:ℝ) / (min 1 (σ^2) + t^2) := by
          have ha := div_le_div_of_nonneg_right h2 (hdenpos t).le
          have hb : (2:ℝ) ^ (σ:ℝ) / (‖(σ:ℂ) + (t:ℂ) * I‖ * ‖(σ:ℂ) + (t:ℂ) * I + 1‖)
              ≤ 2 ^ (σ:ℝ) / (min 1 (σ^2) + t^2) :=
            div_le_div_of_nonneg_left (by positivity) h4 h3
          linarith
      _ = (2 ^ (σ:ℝ)) * ((min 1 (σ^2) + t^2)⁻¹) := by rw [div_eq_mul_inv]
  -- integrability of the bound
  have hbound_int : Integrable (fun t : ℝ => (2 ^ (σ:ℝ)) * ((min 1 (σ^2) + t^2)⁻¹)) := by
    apply Integrable.const_mul
    apply Integrable.mono' (g := fun t : ℝ => (min 1 (σ^2))⁻¹ * (1 + t^2)⁻¹)
      (integrable_inv_one_add_sq.const_mul _)
    · apply Continuous.aestronglyMeasurable
      apply Continuous.inv₀ (by fun_prop)
      intro t
      nlinarith [sq_nonneg t]
    · apply Filter.Eventually.of_forall
      intro t
      have h4 : (0:ℝ) < min 1 (σ^2) + t^2 := by nlinarith [sq_nonneg t]
      rw [Real.norm_of_nonneg (by positivity)]
      rw [inv_le_iff_one_le_mul₀ h4]
      have hmin1 : min 1 (σ^2) ≤ 1 := min_le_left _ _
      have h5 : (min 1 (σ^2))⁻¹ * (1 + t^2)⁻¹ * (min 1 (σ^2) + t^2)
          = ((min 1 (σ^2) + t^2) / (min 1 (σ^2) * (1 + t^2))) := by
        field_simp
      rw [h5, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg t, hm0]
  -- measurability of each F k
  have hdenne : ∀ t : ℝ, ((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1) ≠ 0 := by
    intro t hzero
    have h2 : ‖((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1)‖ = 0 := by rw [hzero, norm_zero]
    rw [norm_mul] at h2
    nlinarith [hdenpos t]
  have hFmeas : ∀ k : ℕ, AEStronglyMeasurable (F k) (volume : Measure ℝ) := by
    intro k
    have hyC : (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by linarith [hyk k])
    have hcont : Continuous (F k) := by
      rw [hFdef]
      simp only []
      apply Continuous.div _ (by fun_prop) hdenne
      have he : (fun t : ℝ => (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I))
          = fun t : ℝ => Complex.exp (Complex.log (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ) * ((σ:ℂ) + (t:ℂ) * I)) := by
        funext t
        rw [Complex.cpow_def_of_ne_zero hyC]
      rw [he]
      fun_prop
    exact hcont.aestronglyMeasurable
  -- pointwise convergence F k t → f t
  have hlim : ∀ t : ℝ, Tendsto (fun k : ℕ => F k t) atTop (𝓝 (f t)) := by
    intro t
    have hbase : Tendsto (fun k : ℕ => (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ)) atTop (𝓝 (((1:ℝ):ℂ))) := by
      apply Tendsto.comp (Complex.continuous_ofReal.tendsto _)
      have h1 : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have := h1.const_add 1
      simpa using this
    have hcpowC : ContinuousAt (fun z : ℂ => z ^ ((σ:ℂ) + (t:ℂ) * I)) (((1:ℝ):ℂ)) := by
      apply continuousAt_cpow_const
      norm_num [Complex.mem_slitPlane_iff]
    have hnum : Tendsto (fun k : ℕ => (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I))
        atTop (𝓝 ((((1:ℝ):ℂ)) ^ ((σ:ℂ) + (t:ℂ) * I))) :=
      (hcpowC.tendsto).comp hbase
    rw [hFdef, hfdef]
    simp only []
    exact hnum.div_const _
  -- dominated convergence
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun t : ℝ => (2 ^ (σ:ℝ)) * ((min 1 (σ^2) + t^2)⁻¹)) hFmeas hbound_int
    (fun k => Filter.Eventually.of_forall (hbound k))
    (Filter.Eventually.of_forall hlim)
  -- values from the gtOne axiom
  have h2πne : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp [Complex.ofReal_ne_zero, Real.pi_ne_zero]
  have hvals : ∀ k : ℕ, (∫ t : ℝ, F k t)
      = (2 * (Real.pi : ℂ)) * (1 - 1 / (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ)) := by
    intro k
    have hax := perron_kernel_gtOne (1 + 1/((k:ℝ)+1)) (hyk k) σ hσ
    rw [hFdef]
    simp only []
    calc (∫ t : ℝ, (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I)
            / (((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1)))
        = (2 * (Real.pi : ℂ)) * ((1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
            (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I)
              / (((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1))) := by
          rw [← mul_assoc, mul_one_div, div_self h2πne, one_mul]
      _ = (2 * (Real.pi : ℂ)) * (1 - 1 / (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ)) := by rw [hax]
  have hvals_lim : Tendsto (fun k : ℕ => (2 * (Real.pi : ℂ)) * (1 - 1 / (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ)))
      atTop (𝓝 0) := by
    have hbase : Tendsto (fun k : ℕ => (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ)) atTop (𝓝 1) := by
      apply Tendsto.comp (Complex.continuous_ofReal.tendsto _)
      have h1 : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := h1.const_add 1
      simpa using h2
    have hinv : Tendsto (fun k : ℕ => 1 / (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ)) atTop (𝓝 1) := by
      have := hbase.inv₀ (by norm_num : (1:ℂ) ≠ 0)
      simpa using this
    have h3 : Tendsto (fun k : ℕ => (1:ℂ) - 1 / (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := (1:ℂ))).sub hinv
      simpa using this
    have h4 := h3.const_mul (2 * (Real.pi : ℂ))
    simpa using h4
  -- conclude
  have hint_f : (∫ t : ℝ, f t) = 0 := by
    apply tendsto_nhds_unique hDCT
    have : (fun k : ℕ => ∫ t : ℝ, F k t)
        = fun k : ℕ => (2 * (Real.pi : ℂ)) * (1 - 1 / (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ)) := by
      funext k
      exact hvals k
    rw [this]
    exact hvals_lim
  rw [hfdef] at hint_f
  simp only [] at hint_f
  rw [hint_f, mul_zero]

open ArithmeticFunction in
/-- **W2e: per-`n` Perron evaluation** — for `X > 1`, `σ > 0`, every `n`:
    `(1/2π)·∫ χ(n)Λ(n)·(X/n)^{σ+it}/((σ+it)(σ+it+1)) dt
       = χ(n)Λ(n)·(if n ≤ X then 1 − n/X else 0)`.
    Trichotomy `n < X` (`gtOne`), `n = X` (`perron_kernel_one`, both sides `0` via `1−n/X = 0`),
    `n > X` (`ltOne`); `n = 0` degenerates via `Λ(0) = 0`. -/
lemma perron_summand_eval {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (X σ : ℝ) (hX : 1 < X) (hσ : 0 < σ) (n : ℕ) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
          * ((((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1)))
      = (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
          * (if (n:ℝ) ≤ X then 1 - ((n:ℝ) : ℂ) / ((X:ℝ) : ℂ) else 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ArithmeticFunction.map_zero]
  · have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hXne : (X:ℝ) ≠ 0 := by linarith
    -- pull the constant out
    rw [MeasureTheory.integral_const_mul, show
      (1 / (2 * (Real.pi : ℂ))) * ((χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)) * ∫ t : ℝ,
        (((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1)))
      = (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)) * ((1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        (((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1)))
      from by ring]
    congr 1
    rcases lt_trichotomy ((n:ℝ)) X with hlt | heq | hgt
    · -- n < X: y = X/n > 1
      have hy : 1 < X / (n:ℝ) := by
        rw [lt_div_iff₀ hnR]
        linarith
      rw [perron_kernel_gtOne (X / (n:ℝ)) hy σ hσ, if_pos hlt.le]
      congr 1
      rw [show ((X / (n:ℝ) : ℝ) : ℂ) = ((X:ℝ):ℂ) / ((n:ℝ):ℂ) from by push_cast; ring]
      rw [one_div_div]
    · -- n = X: y = 1
      have hy1 : (X / (n:ℝ) : ℝ) = 1 := by
        rw [heq]
        field_simp
      rw [hy1, perron_kernel_one σ hσ, if_pos heq.le]
      have hcast : ((n:ℝ) : ℂ) = ((X:ℝ) : ℂ) := by
        exact_mod_cast congrArg Complex.ofReal heq
      rw [hcast, div_self (Complex.ofReal_ne_zero.mpr hXne)]
      ring
    · -- n > X: 0 < y < 1
      have hy0 : (0:ℝ) < X / (n:ℝ) := by positivity
      have hy1 : X / (n:ℝ) < 1 := by
        rw [div_lt_one hnR]
        exact hgt
      rw [perron_kernel_ltOne (X / (n:ℝ)) hy0 hy1 σ hσ, if_neg (by linarith)]


open ArithmeticFunction in
/-- **W2f: THE SMOOTHED-PERRON REPRESENTATION, PROVEN** — the exact statement of the
    `smoothed_perron_LFunction` axiom, now a theorem (modulo the two PNT kernel inputs):
    reshape → interchange (W2c) → per-`n` evaluation (W2e) → tsum collapse to the finite sum. -/
theorem smoothed_perron_LFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (X : ℝ) (hX : 1 < X) (σ : ℝ) (hσ : 1 < σ) :
    ∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X)
      = (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
          (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I)
              / DirichletCharacter.LFunction χ ((σ : ℂ) + t * I))
            * (X : ℂ) ^ ((σ : ℂ) + t * I)
            / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1)) := by
  have hX0 : (0:ℝ) < X := by linarith
  -- reshape to the G'-form and interchange
  have h1 : (∫ t : ℝ, (-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + t * I)
          / DirichletCharacter.LFunction χ ((σ:ℂ) + t * I))
        * (X:ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1)))
      = ∑' n : ℕ, ∫ t : ℝ,
        (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
          * ((((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1))) := by
    rw [perron_integrand_reshape]
    exact integral_G_tsum χ X σ hX0 hσ
  rw [h1, ← tsum_mul_left]
  -- evaluate each summand and collapse
  have h2 : ∀ n : ℕ, (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
      (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
        * ((((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1)))
      = (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
        * (if (n:ℝ) ≤ X then 1 - ((n:ℝ) : ℂ) / ((X:ℝ) : ℂ) else 0) :=
    perron_summand_eval χ X σ hX (by linarith)
  rw [tsum_congr h2]
  -- tsum → finite sum over range(⌊X⌋+1)
  have hvanish : ∀ n ∉ Finset.range (⌊X⌋₊ + 1),
      (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
        * (if (n:ℝ) ≤ X then 1 - ((n:ℝ) : ℂ) / ((X:ℝ) : ℂ) else 0) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hnX : X < (n:ℝ) := by
      have h3 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
      have h4 : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      push_cast at h4
      linarith
    rw [if_neg (by linarith)]
    ring
  rw [tsum_eq_sum hvanish]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_range] at hn
  have hnX : (n:ℝ) ≤ X := by
    have h3 : n ≤ ⌊X⌋₊ := by omega
    have h4 : ((n:ℕ):ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast h3
    have h5 : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0.le
    linarith
  rw [if_pos hnX]

/-- **Sharp ↔ smoothed bridge** (SW brick B2b): the sharp partial sum equals the smoothed one plus
    the linear-weight correction `(1/X)∑ n·a_n`. Pure algebra (regroup `a_n·(n/X)`); the correction
    is then handled at two scales `X`, `X(1+δ)` to recover the sharp sum with the smoothed rate. -/
lemma sharp_eq_smoothed_add {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (X : ℝ) (M : ℕ) :
    ∑ n ∈ Finset.range M, χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
      = (∑ n ∈ Finset.range M,
          χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X))
        + (1 / (X : ℂ)) * ∑ n ∈ Finset.range M,
            (n : ℂ) * (χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  ring

/-- **Perron-kernel holomorphy** (SW brick B3 input): the smoothed kernel `X^s/(s(s+1))` is
    holomorphic on `Re s > 0` (`s ≠ 0`, `s+1 ≠ 0`; `X^s` entire for `X > 0`). Combined with the
    zero-free-region holomorphy of `−L′/L` (`LFunction_ne_zero_re_ge_one` / the contour gap), the
    smoothed-Perron integrand is holomorphic in the shift strip, so the B3 rectangle contour picks up
    only the kernel pole at `s = 0` and (for `χ₀`) the `L`-pole at `s = 1`. -/
lemma perron_kernel_differentiableOn (X : ℝ) (hX : 0 < X) :
    DifferentiableOn ℂ (fun s : ℂ => (X : ℂ) ^ s / (s * (s + 1))) {s : ℂ | 0 < s.re} := by
  have hXne : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  apply DifferentiableOn.div
  · have hcpow : Differentiable ℂ (fun s : ℂ => (X : ℂ) ^ s) :=
      fun s => (hasStrictDerivAt_const_cpow (Or.inl hXne)).hasDerivAt.differentiableAt
    exact hcpow.differentiableOn
  · fun_prop
  · intro s hs
    simp only [Set.mem_setOf_eq] at hs
    have h1 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
    have h2 : s + 1 ≠ 0 := by
      intro h
      have : s = -1 := by linear_combination h
      rw [this] at hs; norm_num at hs
    exact mul_ne_zero h1 h2

/-- **Smoothed-kernel magnitude** (SW brick B3 input): `‖X^s/(s(s+1))‖ = X^{Re s}/(‖s‖‖s+1‖)`
    for `X > 0`. Via `norm_cpow_eq_rpow_re_of_pos`. -/
lemma perron_kernel_norm (X : ℝ) (hX : 0 < X) (s : ℂ) :
    ‖(X : ℂ) ^ s / (s * (s + 1))‖ = X ^ s.re / (‖s‖ * ‖s + 1‖) := by
  rw [norm_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hX]

/-- **Smoothed-kernel vertical decay** (SW brick B3 input): `‖X^s/(s(s+1))‖ ≤ X^{Re s}/(Im s)²` off
    the real axis (`‖s‖, ‖s+1‖ ≥ |Im s|`). The `1/t²` decay makes the top/horizontal contour
    integrals `O(X^σ/T)` in the B3 rectangle shift, and the vertical integral absolutely convergent. -/
lemma perron_kernel_decay (X : ℝ) (hX : 0 < X) (s : ℂ) (hs : s.im ≠ 0) :
    ‖(X : ℂ) ^ s / (s * (s + 1))‖ ≤ X ^ s.re / s.im ^ 2 := by
  rw [perron_kernel_norm X hX s]
  have him1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have him2 : |s.im| ≤ ‖s + 1‖ := by
    have h : (s + 1).im = s.im := by simp
    calc |s.im| = |(s + 1).im| := by rw [h]
      _ ≤ ‖s + 1‖ := Complex.abs_im_le_norm _
  have hsq : s.im ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    rw [← sq_abs, sq]
    exact mul_le_mul him1 him2 (abs_nonneg _) (norm_nonneg _)
  have hX0 : (0 : ℝ) ≤ X ^ s.re := Real.rpow_nonneg hX.le _
  have him0 : (0 : ℝ) < s.im ^ 2 := (sq_nonneg s.im).lt_of_ne (Ne.symm (pow_ne_zero 2 hs))
  exact div_le_div_of_nonneg_left hX0 him0 hsq

/-- **Derivative of the entire L-function is entire** (SW brick B3 input): for `χ ≠ 1`,
    `deriv (LFunction χ)` is differentiable everywhere (holomorphic ⇒ analytic ⇒ deriv analytic).
    Via `AnalyticOnNhd.deriv`. -/
lemma deriv_LFunction_differentiable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    Differentiable ℂ (deriv (DirichletCharacter.LFunction χ)) := by
  have hana : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
    (differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ
  have hderiv : AnalyticOnNhd ℂ (deriv (DirichletCharacter.LFunction χ)) Set.univ := hana.deriv
  intro s
  exact (hderiv s (Set.mem_univ s)).differentiableAt

/-- **Smoothed-Perron integrand holomorphy** (SW brick B3): the integrand
    `(−L′/L)·X^s/(s(s+1))` is holomorphic on `{Re s > 0 ∧ L(s,χ) ≠ 0}`. So on the zero-free strip
    (`χ ≠ 1`, `Re s > 1−g`) the B3 rectangle encloses no pole and Cauchy
    (`integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real`) gives the vertical-integral shift
    `∫_{(σ)} = ∫_{(σ')}` (horizontal connectors `→0` by `perron_kernel_decay`). -/
lemma smoothed_integrand_differentiableOn {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (X : ℝ) (hX : 0 < X) :
    DifferentiableOn ℂ
      (fun s : ℂ => (-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)
        * ((X : ℂ) ^ s / (s * (s + 1))))
      {s : ℂ | 0 < s.re ∧ DirichletCharacter.LFunction χ s ≠ 0} := by
  have hSsub : {s : ℂ | 0 < s.re ∧ DirichletCharacter.LFunction χ s ≠ 0} ⊆ {s : ℂ | 0 < s.re} :=
    fun s hs => hs.1
  apply DifferentiableOn.mul
  · apply DifferentiableOn.div
    · exact ((deriv_LFunction_differentiable χ hχ).neg).differentiableOn
    · exact (differentiable_LFunction hχ).differentiableOn
    · intro s hs; exact hs.2
  · exact (perron_kernel_differentiableOn X hX).mono hSsub

/-- **B3 rectangle Cauchy-vanishing**: for a closed rectangle `[z,w]` inside the zero-free strip
    `{Re s > 0 ∧ L(s,χ) ≠ 0}` (`χ ≠ 1`), the smoothed-Perron integrand's boundary integral vanishes
    (Cauchy–Goursat, `integral_boundary_rect_eq_zero_of_differentiableOn` +
    `smoothed_integrand_differentiableOn`). Equating the two vertical sides (as `T → ∞`, the
    horizontal sides `→0` by `perron_kernel_decay`) gives the contour shift `∫_{(σ)} = ∫_{(σ')}`
    for `χ ≠ 1` — the heart of B3. -/
lemma smoothed_integrand_rect_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (X : ℝ) (hX : 0 < X) (z w : ℂ)
    (hrect : Complex.reProdIm (Set.uIcc z.re w.re) (Set.uIcc z.im w.im)
      ⊆ {s : ℂ | 0 < s.re ∧ DirichletCharacter.LFunction χ s ≠ 0}) :
    (∫ x : ℝ in z.re..w.re,
        (-deriv (DirichletCharacter.LFunction χ) (x + z.im * I) / DirichletCharacter.LFunction χ (x + z.im * I))
          * ((X : ℂ) ^ ((x : ℂ) + z.im * I) / (((x : ℂ) + z.im * I) * ((x : ℂ) + z.im * I + 1))))
      - (∫ x : ℝ in z.re..w.re,
        (-deriv (DirichletCharacter.LFunction χ) (x + w.im * I) / DirichletCharacter.LFunction χ (x + w.im * I))
          * ((X : ℂ) ^ ((x : ℂ) + w.im * I) / (((x : ℂ) + w.im * I) * ((x : ℂ) + w.im * I + 1))))
      + I • (∫ y : ℝ in z.im..w.im,
        (-deriv (DirichletCharacter.LFunction χ) (w.re + y * I) / DirichletCharacter.LFunction χ (w.re + y * I))
          * ((X : ℂ) ^ ((w.re : ℂ) + y * I) / (((w.re : ℂ) + y * I) * ((w.re : ℂ) + y * I + 1))))
      - I • (∫ y : ℝ in z.im..w.im,
        (-deriv (DirichletCharacter.LFunction χ) (z.re + y * I) / DirichletCharacter.LFunction χ (z.re + y * I))
          * ((X : ℂ) ^ ((z.re : ℂ) + y * I) / (((z.re : ℂ) + y * I) * ((z.re : ℂ) + y * I + 1))))
      = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn _ z w
    ((smoothed_integrand_differentiableOn χ hχ X hX).mono hrect)

/-- **Integrand continuity on the vertical line `Re = σ > 1`** (SW brick B3 input): `t ↦ F(σ+it)` is
    continuous (the integrand is holomorphic on `{Re>0 ∧ L≠0}`; the line `Re=σ>1` lies inside it by
    `LFunction_ne_zero_re_ge_one`). Prerequisite for the vertical Perron integral and its `T→∞` limit. -/
lemma integrand_continuous_on_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (X : ℝ) (hX : 0 < X) (σ : ℝ) (hσ : 1 < σ) :
    Continuous (fun t : ℝ =>
      (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ : ℂ) + t * I))
        * ((X : ℂ) ^ ((σ : ℂ) + t * I) / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1)))) := by
  apply (smoothed_integrand_differentiableOn χ hχ X hX).continuousOn.comp_continuous
    (by fun_prop)
  intro t
  refine ⟨?_, ?_⟩
  · simp
    linarith
  · exact LFunction_ne_zero_re_ge_one χ hχ (by simp; linarith)

/-- **`−L′/L` uniformly bounded on the line `Re = σ > 1`** (SW brick B3 input): `‖−L′/L(σ+it,χ)‖ ≤
    ∑_n Λ(n)/n^σ` for all `t` (a constant `B_σ`). Via `neg_logDeriv_LFunction_eq` (= the χ·Λ Dirichlet
    series) + `norm_tsum_le_tsum_norm` + `norm_term_eq` (the term norm depends only on `Re s = σ`).
    With `perron_kernel_decay` (`1/t²`) this makes the vertical integrand integrable on `Re = σ`. -/
lemma neg_logDeriv_bounded_on_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (σ : ℝ) (hσ : 1 < σ) :
    ∃ B : ℝ, ∀ t : ℝ,
      ‖-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ : ℂ) + t * I)‖ ≤ B := by
  refine ⟨∑' n : ℕ, ‖LSeries.term (fun n : ℕ => χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (σ : ℂ) n‖, fun t => ?_⟩
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  have hs : 1 < ((σ : ℂ) + t * I).re := by rw [hre]; exact hσ
  rw [neg_logDeriv_LFunction_eq χ hs]
  have hsummable : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n : ℕ => χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I) n‖) :=
    summable_norm_iff.mpr (LSeriesSummable_twist_vonMangoldt χ hs)
  calc ‖LSeries (fun n : ℕ => χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I)‖
      ≤ ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I) n‖ :=
        norm_tsum_le_tsum_norm hsummable
    _ = ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (σ : ℂ) n‖ := by
        apply tsum_congr; intro n
        rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hre, Complex.ofReal_re]

open MeasureTheory in
/-- **Vertical-integrand integrability on `Re = σ > 1`** (SW brick B3): the smoothed-Perron integrand
    `t ↦ F(σ+it)` is integrable over `ℝ`. Domination: `‖F‖ = ‖−L′/L‖·‖kernel‖ ≤ B·X^σ/(σ²+t²) ≤
    B·X^σ/(1+t²)` (`neg_logDeriv_bounded_on_line`, `perron_kernel_norm`, `‖s‖‖s+1‖ ≥ σ²+t²` via
    `norm_add_mul_I`, and `σ²≥1`), dominated by the integrable `B·X^σ·(1+t²)⁻¹`
    (`integrable_inv_one_add_sq`). So the vertical Perron integral is a well-defined Bochner integral. -/
lemma integrand_integrable_on_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (X : ℝ) (hX : 0 < X) (σ : ℝ) (hσ : 1 < σ) :
    Integrable (fun t : ℝ =>
      (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ : ℂ) + t * I))
        * ((X : ℂ) ^ ((σ : ℂ) + t * I) / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1)))) := by
  obtain ⟨B, hB⟩ := neg_logDeriv_bounded_on_line χ σ hσ
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hXσ0 : 0 ≤ X ^ σ := Real.rpow_nonneg hX.le _
  refine Integrable.mono' (g := fun t : ℝ => B * X ^ σ * (1 + t ^ 2)⁻¹) ?_
    (integrand_continuous_on_line χ hχ X hX σ hσ).aestronglyMeasurable ?_
  · exact integrable_inv_one_add_sq.const_mul (B * X ^ σ)
  · apply Filter.Eventually.of_forall
    intro t
    have hknorm : ‖(X : ℂ) ^ ((σ : ℂ) + t * I) / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1))‖
        = X ^ σ / (‖(σ : ℂ) + t * I‖ * ‖(σ : ℂ) + t * I + 1‖) := by
      rw [perron_kernel_norm X hX]; congr 1; simp
    have hden : σ ^ 2 + t ^ 2 ≤ ‖(σ : ℂ) + ↑t * I‖ * ‖(σ : ℂ) + ↑t * I + 1‖ := by
      have e1 : ‖(σ : ℂ) + ↑t * I‖ = Real.sqrt (σ ^ 2 + t ^ 2) := Complex.norm_add_mul_I σ t
      have e2 : (σ : ℂ) + ↑t * I + 1 = ((σ + 1 : ℝ) : ℂ) + ↑t * I := by push_cast; ring
      have e3 : ‖(σ : ℂ) + ↑t * I + 1‖ = Real.sqrt ((σ + 1) ^ 2 + t ^ 2) := by
        rw [e2]; exact Complex.norm_add_mul_I _ _
      rw [e1, e3]
      have h4 : Real.sqrt (σ ^ 2 + t ^ 2) ≤ Real.sqrt ((σ + 1) ^ 2 + t ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
      calc σ ^ 2 + t ^ 2 = Real.sqrt (σ ^ 2 + t ^ 2) * Real.sqrt (σ ^ 2 + t ^ 2) :=
            (Real.mul_self_sqrt (by positivity)).symm
        _ ≤ Real.sqrt (σ ^ 2 + t ^ 2) * Real.sqrt ((σ + 1) ^ 2 + t ^ 2) :=
            mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
    have hσ2 : (0 : ℝ) < σ ^ 2 + t ^ 2 := by nlinarith [hσ, sq_nonneg t]
    have hle1 : (1 : ℝ) + t ^ 2 ≤ σ ^ 2 + t ^ 2 := by nlinarith
    calc ‖(-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + ↑t * I) / DirichletCharacter.LFunction χ ((σ : ℂ) + ↑t * I))
            * ((X : ℂ) ^ ((σ : ℂ) + ↑t * I) / (((σ : ℂ) + ↑t * I) * ((σ : ℂ) + ↑t * I + 1)))‖
        = ‖(-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + ↑t * I) / DirichletCharacter.LFunction χ ((σ : ℂ) + ↑t * I))‖
            * ‖(X : ℂ) ^ ((σ : ℂ) + ↑t * I) / (((σ : ℂ) + ↑t * I) * ((σ : ℂ) + ↑t * I + 1))‖ := norm_mul _ _
      _ ≤ B * (X ^ σ / (σ ^ 2 + t ^ 2)) := by
          rw [hknorm]
          refine mul_le_mul (hB t) ?_ (by positivity) hB0
          exact div_le_div_of_nonneg_left hXσ0 hσ2 hden
      _ ≤ B * X ^ σ * (1 + t ^ 2)⁻¹ := by
          rw [← mul_div_assoc, ← div_eq_mul_inv]
          exact div_le_div_of_nonneg_left (mul_nonneg hB0 hXσ0) (by positivity) hle1

open MeasureTheory intervalIntegral in
/-- **Horizontal connector bound** (SW brick B3): the top/bottom sides of the B3 rectangle at height
    `T` are `O(X^σ/T²)`: `‖∫_{σ'}^{σ} F(x+iT)‖ ≤ (σ−σ')·M·X^σ/T²`, given a uniform `‖−L′/L‖ ≤ M`
    bound on the segment (from `contour_logDeriv_bound`, `M = C·N^ε·L_T²` polylog). Via
    `perron_kernel_decay` (`‖kernel‖ ≤ X^x/T²`) + `X^x ≤ X^σ` (`X≥1`, `x≤σ`) +
    `norm_integral_le_of_norm_le_const`. Drives the connectors `→0` as `T→∞` (polylog `M`, `1/T²`). -/
lemma horizontal_connector_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (X : ℝ) (hX1 : 1 ≤ X) (σ' σ T M : ℝ) (hσ'σ : σ' ≤ σ) (hT : T ≠ 0) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Set.uIcc σ' σ,
      ‖-deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + T * I) / DirichletCharacter.LFunction χ ((x : ℂ) + T * I)‖ ≤ M) :
    ‖∫ x : ℝ in σ'..σ,
        (-deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + T * I) / DirichletCharacter.LFunction χ ((x : ℂ) + T * I))
          * ((X : ℂ) ^ ((x : ℂ) + T * I) / (((x : ℂ) + T * I) * ((x : ℂ) + T * I + 1)))‖
      ≤ (σ - σ') * (M * X ^ σ / T ^ 2) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hT2 : (0 : ℝ) < T ^ 2 := (sq_nonneg T).lt_of_ne (Ne.symm (pow_ne_zero 2 hT))
  have hkey : ∀ x ∈ Set.uIcc σ' σ,
      ‖(-deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + T * I) / DirichletCharacter.LFunction χ ((x : ℂ) + T * I))
          * ((X : ℂ) ^ ((x : ℂ) + T * I) / (((x : ℂ) + T * I) * ((x : ℂ) + T * I + 1)))‖
        ≤ M * X ^ σ / T ^ 2 := by
    intro x hx
    have hxσ : x ≤ σ := (Set.uIcc_of_le hσ'σ ▸ hx : x ∈ Set.Icc σ' σ).2
    have him : ((x : ℂ) + T * I).im = T := by simp
    have hre : ((x : ℂ) + T * I).re = x := by simp
    have hkd := perron_kernel_decay X hX0 ((x : ℂ) + T * I) (by rw [him]; exact hT)
    rw [hre, him] at hkd
    have h3 : X ^ x ≤ X ^ σ := Real.rpow_le_rpow_of_exponent_le hX1 hxσ
    have hdiv : X ^ x / T ^ 2 ≤ X ^ σ / T ^ 2 := by gcongr
    rw [norm_mul]
    calc ‖-deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + T * I) / DirichletCharacter.LFunction χ ((x : ℂ) + T * I)‖
            * ‖(X : ℂ) ^ ((x : ℂ) + T * I) / (((x : ℂ) + T * I) * ((x : ℂ) + T * I + 1))‖
        ≤ M * (X ^ x / T ^ 2) := mul_le_mul (hM x hx) hkd (norm_nonneg _) hM0
      _ ≤ M * (X ^ σ / T ^ 2) := mul_le_mul_of_nonneg_left hdiv hM0
      _ = M * X ^ σ / T ^ 2 := by ring
  calc ‖∫ x : ℝ in σ'..σ,
          (-deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + T * I) / DirichletCharacter.LFunction χ ((x : ℂ) + T * I))
            * ((X : ℂ) ^ ((x : ℂ) + T * I) / (((x : ℂ) + T * I) * ((x : ℂ) + T * I + 1)))‖
      ≤ (M * X ^ σ / T ^ 2) * |σ - σ'| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (fun x hx => hkey x (Set.uIoc_subset_uIcc hx))
    _ = (σ - σ') * (M * X ^ σ / T ^ 2) := by
        rw [abs_of_nonneg (by linarith)]; ring

open MeasureTheory Filter Topology in
/-- **Truncated → full vertical integral** (SW brick B3): `∫_{-T}^{T} g → ∫_ℝ g` as `T → ∞` for
    integrable `g` — the right/left sides of the B3 rectangle converge to the full vertical Perron
    integrals. Via `tendsto_setIntegral_of_monotone` over `Ioc(-T,T) ↗ univ`. Applied with
    `g = F(σ+·i)` (`integrand_integrable_on_line`) and `g = F(σ'+·i)`, plus the horizontal connectors
    `→0` (`horizontal_connector_bound`), the rectangle identity `smoothed_integrand_rect_zero` yields
    the contour shift `∫_{(σ)} = ∫_{(σ')}` in the limit. -/
lemma vertical_integral_tendsto (g : ℝ → ℂ) (hg : Integrable g) :
    Tendsto (fun T : ℝ => ∫ y in (-T)..T, g y) atTop (𝓝 (∫ y, g y)) := by
  have hunion : (⋃ T : ℝ, Set.Ioc (-T) T) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_univ, iff_true]
    exact ⟨|x| + 1, by have := neg_abs_le x; linarith, by have := le_abs_self x; linarith⟩
  have hmono : Monotone (fun T : ℝ => Set.Ioc (-T) T) := by
    intro a b hab; apply Set.Ioc_subset_Ioc <;> linarith
  have hint : IntegrableOn g (⋃ T : ℝ, Set.Ioc (-T) T) := by rw [hunion]; exact hg.integrableOn
  have key := tendsto_setIntegral_of_monotone (fun T : ℝ => measurableSet_Ioc) hmono hint
  rw [hunion, MeasureTheory.setIntegral_univ] at key
  refine key.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  exact (intervalIntegral.integral_of_le (by linarith : -T ≤ T)).symm

/-- **Orthogonality character-sum bound** (SW brick B5): `‖∑_χ χ(a)·f(χ)‖ ≤ ∑_χ ‖f(χ)‖` — Dirichlet
    character values have norm ≤ 1 (`norm_le_one`). Applied to `psi_ap_orthogonality` with
    `f χ = ψ(X,χ)`, this reduces the AP prime-count error `φ(q)·∑_{n≡a}Λ − ⋯` to the sum of
    per-character `ψ(X,χ)` bounds (the χ₀ main term `X` + the χ≠1 SW rate), completing the B5 assembly
    skeleton for `siegel_walfisz`. -/
lemma char_sum_norm_le {q : ℕ} [NeZero q] (a : ZMod q) (f : DirichletCharacter ℂ q → ℂ) :
    ‖∑ χ : DirichletCharacter ℂ q, χ a * f χ‖ ≤ ∑ χ : DirichletCharacter ℂ q, ‖f χ‖ := by
  calc ‖∑ χ : DirichletCharacter ℂ q, χ a * f χ‖
      ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ a * f χ‖ := norm_sum_le _ _
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖f χ‖ := by
        apply Finset.sum_le_sum
        intro χ _
        rw [norm_mul]
        calc ‖χ a‖ * ‖f χ‖ ≤ 1 * ‖f χ‖ :=
              mul_le_mul_of_nonneg_right (norm_le_one χ a) (norm_nonneg _)
          _ = ‖f χ‖ := one_mul _

open scoped Classical in
/-- **B5 principal-character separation**: `‖∑_χ χ(a)·f(χ)‖ ≤ ‖f(1)‖ + ∑_{χ≠1} ‖f(χ)‖`. Isolates the
    principal character `χ₀=1` (whose `ψ(X,χ₀)` carries the main term `X`) from the nontrivial
    characters (whose `ψ(X,χ)` is `O(SW rate)`). The B5 reduction shape for `siegel_walfisz`:
    `‖φ(q)·(AP count) − X‖ ≤ ‖ψ(X,χ₀)−X‖ + ∑_{χ≠1}‖ψ(X,χ)‖`. -/
lemma char_sum_norm_le_split {q : ℕ} [NeZero q] (a : ZMod q) (f : DirichletCharacter ℂ q → ℂ) :
    ‖∑ χ : DirichletCharacter ℂ q, χ a * f χ‖
      ≤ ‖f 1‖ + ∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)), ‖f χ‖ := by
  refine le_trans (char_sum_norm_le a f) ?_
  rw [← Finset.add_sum_erase Finset.univ (fun χ => ‖f χ‖) (Finset.mem_univ 1)]

open scoped Classical in
/-- **B5 reduction** (SW brick B5c): `‖∑_χ χ(a)·f(χ)‖ ≤ ‖f(1)‖ + (#χ − 1)·R` given a uniform bound
    `R` on the nontrivial characters. With `f χ = ψ(X,χ)` and `psi_ap_orthogonality`, this reduces
    the AP prime-count error to the χ₀ main-term error `‖ψ(X,χ₀)−X‖` plus `(φ(q)−1)×` the SW rate —
    dividing by `φ(q)` then gives the `siegel_walfisz` statement shape. -/
lemma char_sum_reduction {q : ℕ} [NeZero q] (a : ZMod q) (R : ℝ) (hR : 0 ≤ R)
    (f : DirichletCharacter ℂ q → ℂ) (hf : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖f χ‖ ≤ R) :
    ‖∑ χ : DirichletCharacter ℂ q, χ a * f χ‖
      ≤ ‖f 1‖ + (Fintype.card (DirichletCharacter ℂ q) - 1 : ℕ) * R := by
  have hcard : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card
      = Fintype.card (DirichletCharacter ℂ q) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hbound : ∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)), ‖f χ‖
      ≤ (Fintype.card (DirichletCharacter ℂ q) - 1 : ℕ) * R := by
    calc ∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)), ‖f χ‖
        ≤ (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card • R :=
          Finset.sum_le_card_nsmul _ _ _ (fun χ hχ => hf χ (Finset.ne_of_mem_erase hχ))
      _ = (Fintype.card (DirichletCharacter ℂ q) - 1 : ℕ) * R := by rw [hcard, nsmul_eq_mul]
  linarith [char_sum_norm_le_split a f, hbound]

open MeasureTheory in
/-- **Truncation tail bound** (SW brick W1a): for integrable `g` with `‖g(t)‖ ≤ C/t²` off `0`,
    `‖∫_ℝ g − ∫_{-T}^{T} g‖ ≤ 2C/T`. The quantitative σ-line truncation error for the B3 finite-T
    rectangle assembly (`g = F(σ+it)`, `C = B_σ·X^σ` via `neg_logDeriv_bounded_on_line` +
    `perron_kernel_decay`) — ties `smoothed_perron_LFunction`'s full vertical integral to the
    truncated one appearing in `smoothed_integrand_rect_zero`. -/
lemma truncation_tail_bound (g : ℝ → ℂ) (hg : Integrable g) (C T : ℝ) (hT : 0 < T)
    (hbound : ∀ t : ℝ, t ≠ 0 → ‖g t‖ ≤ C / t ^ 2) :
    ‖(∫ t, g t) - ∫ t in (-T)..T, g t‖ ≤ 2 * C / T := by
  have hC : 0 ≤ C := by
    have h1 := hbound 1 one_ne_zero
    have h2 : (0:ℝ) ≤ ‖g 1‖ := norm_nonneg _
    have h3 : C / (1:ℝ) ^ 2 = C := by norm_num
    linarith [h3 ▸ h1]
  have tailR : ∀ h : ℝ → ℂ, (∀ x ∈ Set.Ioi T, ‖h x‖ ≤ C / x ^ 2) →
      ‖∫ x in Set.Ioi T, h x‖ ≤ C / T := by
    intro h hh
    have h1 := MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi T)) h
    have hgi : Integrable (fun x : ℝ => C * x ^ (-2:ℝ)) (volume.restrict (Set.Ioi T)) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul C
    have h2 : (∫ x in Set.Ioi T, ‖h x‖) ≤ ∫ x in Set.Ioi T, C * x ^ (-2:ℝ) := by
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x => norm_nonneg _
      · exact hgi
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 < x := lt_trans hT hx
        have e : x ^ (-2:ℝ) = ((x : ℝ) ^ (2:ℕ))⁻¹ := by
          rw [Real.rpow_neg hx0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        rw [e, ← div_eq_mul_inv]
        exact hh x hx
    have h3 : ∫ x in Set.Ioi T, C * x ^ (-2:ℝ) = C / T := by
      rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT,
        show (-2:ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      ring
    linarith
  have hadd := MeasureTheory.integral_add_compl
    (measurableSet_Ioc : MeasurableSet (Set.Ioc (-T) T)) hg
  have hdiff : (∫ t, g t) - (∫ t in Set.Ioc (-T) T, g t) = ∫ t in (Set.Ioc (-T) T)ᶜ, g t := by
    rw [← hadd]; ring
  have hcompl : (Set.Ioc (-T) T)ᶜ = Set.Iic (-T) ∪ Set.Ioi T := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Ioc, Set.mem_union, Set.mem_Iic, Set.mem_Ioi]
    push_neg
    constructor
    · intro hx
      by_cases h : -T < x
      · exact Or.inr (hx h)
      · exact Or.inl (by linarith [not_lt.mp h])
    · intro hx h1
      rcases hx with h | h
      · linarith
      · linarith
  have hdisj : Disjoint (Set.Iic (-T)) (Set.Ioi T) := Set.Iic_disjoint_Ioi (by linarith)
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T), hdiff, hcompl,
    MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hg.integrableOn hg.integrableOn]
  have hleft : ‖∫ t in Set.Iic (-T), g t‖ ≤ C / T := by
    rw [← integral_comp_neg_Ioi]
    apply tailR
    intro x hx
    have hx0 : 0 < x := lt_trans hT hx
    have hb := hbound (-x) (by simpa using hx0.ne')
    rwa [show (-x) ^ 2 = x ^ 2 by ring] at hb
  have hright : ‖∫ t in Set.Ioi T, g t‖ ≤ C / T := by
    apply tailR
    intro x hx
    exact hbound x (ne_of_gt (lt_trans hT hx))
  calc ‖(∫ t in Set.Iic (-T), g t) + ∫ t in Set.Ioi T, g t‖
      ≤ ‖∫ t in Set.Iic (-T), g t‖ + ‖∫ t in Set.Ioi T, g t‖ := norm_add_le _ _
    _ ≤ C / T + C / T := add_le_add hleft hright
    _ = 2 * C / T := by ring

open MeasureTheory in
/-- **Shifted-line integral bound** (SW brick W1b): if `‖F(t)‖ ≤ M·Xσ/(σ'²+t²)` on `(-T,T]` with
    `σ' ≥ 3/4`, then `‖∫_{-T}^{T} F‖ ≤ 6·M·Xσ`. -/
lemma shifted_line_integral_bound (F : ℝ → ℂ) (M Xσ σ' T : ℝ)
    (hM : 0 ≤ M) (hXσ : 0 ≤ Xσ) (hσ' : 3/4 ≤ σ') (hT : 0 ≤ T)
    (hpt : ∀ t : ℝ, t ∈ Set.Ioc (-T) T → ‖F t‖ ≤ M * Xσ / (σ' ^ 2 + t ^ 2)) :
    ‖∫ t in (-T)..T, F t‖ ≤ 6 * M * Xσ := by
  have hd1 : ∀ t : ℝ, (0:ℝ) < σ' ^ 2 + t ^ 2 := fun t => by nlinarith [sq_nonneg t]
  have hd2 : ∀ t : ℝ, (0:ℝ) < 1 + t ^ 2 := fun t => by nlinarith [sq_nonneg t]
  have hgcont : Continuous (fun t : ℝ => M * Xσ / (σ' ^ 2 + t ^ 2)) :=
    continuous_const.div (by fun_prop) (fun t => (hd1 t).ne')
  have hhcont : Continuous (fun t : ℝ => 16/9 * (M * Xσ) * (1 + t ^ 2)⁻¹) :=
    continuous_const.mul (Continuous.inv₀ (by fun_prop) (fun t => (hd2 t).ne'))
  have step1 := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T ≤ T)
    (Filter.Eventually.of_forall hpt) (hgcont.intervalIntegrable (μ := volume) (-T) T)
  have step2 : (∫ t in (-T)..T, M * Xσ / (σ' ^ 2 + t ^ 2))
      ≤ ∫ t in (-T)..T, 16/9 * (M * Xσ) * (1 + t ^ 2)⁻¹ := by
    apply intervalIntegral.integral_mono_on (by linarith)
      (hgcont.intervalIntegrable (μ := volume) (-T) T) (hhcont.intervalIntegrable (μ := volume) (-T) T)
    intro t _
    have h9 : 9/16 * (1 + t ^ 2) ≤ σ' ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
    calc M * Xσ / (σ' ^ 2 + t ^ 2) ≤ M * Xσ / (9/16 * (1 + t ^ 2)) :=
          div_le_div_of_nonneg_left (mul_nonneg hM hXσ) (by nlinarith [hd2 t]) h9
      _ = 16/9 * (M * Xσ) * (1 + t ^ 2)⁻¹ := by
          field_simp
  have step3 : (∫ t in (-T)..T, 16/9 * (M * Xσ) * (1 + t ^ 2)⁻¹)
      = 16/9 * (M * Xσ) * ∫ t in (-T)..T, (1 + t ^ 2)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
  have step4 : (∫ t in (-T)..T, (1 + t ^ 2)⁻¹) ≤ Real.pi := by
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
    calc (∫ t in Set.Ioc (-T) T, (1 + t ^ 2)⁻¹)
        ≤ ∫ t : ℝ, (1 + t ^ 2)⁻¹ := by
          apply MeasureTheory.setIntegral_le_integral integrable_inv_one_add_sq
          exact Filter.Eventually.of_forall (fun t => by positivity)
      _ = Real.pi := integral_univ_inv_one_add_sq
  have h0 : 0 ≤ M * Xσ := mul_nonneg hM hXσ
  have hInn : (0:ℝ) ≤ ∫ t in (-T)..T, (1 + t ^ 2)⁻¹ := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t _
    positivity
  have step5 : 16/9 * (M * Xσ) * (∫ t in (-T)..T, (1 + t ^ 2)⁻¹) ≤ 6 * M * Xσ := by
    have hπ : Real.pi < 3.15 := Real.pi_lt_d2
    calc 16/9 * (M * Xσ) * (∫ t in (-T)..T, (1 + t ^ 2)⁻¹)
        ≤ 16/9 * (M * Xσ) * Real.pi := by
          apply mul_le_mul_of_nonneg_left step4 (by positivity)
      _ ≤ 6 * M * Xσ := by nlinarith [Real.pi_pos]
  linarith [step1, step2, step3.le, step3.ge, step5]

/-- **Integrand pointwise bound on a shifted line** (SW brick W1c): given `‖−L′/L(σ'+it)‖ ≤ M`,
    the smoothed integrand satisfies `‖F(σ'+it)‖ ≤ M·X^{σ'}/(σ'²+t²)` — exactly the input to
    `shifted_line_integral_bound`. -/
lemma integrand_pointwise_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (X σ' t M : ℝ) (hX : 0 < X) (hσ'0 : 0 < σ') (hM : 0 ≤ M)
    (hLL : ‖-deriv (DirichletCharacter.LFunction χ) ((σ' : ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ' : ℂ) + t * I)‖ ≤ M) :
    ‖(-deriv (DirichletCharacter.LFunction χ) ((σ' : ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ' : ℂ) + t * I))
        * ((X : ℂ) ^ ((σ' : ℂ) + t * I) / (((σ' : ℂ) + t * I) * ((σ' : ℂ) + t * I + 1)))‖
      ≤ M * X ^ σ' / (σ' ^ 2 + t ^ 2) := by
  have hknorm : ‖(X : ℂ) ^ ((σ' : ℂ) + t * I) / (((σ' : ℂ) + t * I) * ((σ' : ℂ) + t * I + 1))‖
      = X ^ σ' / (‖(σ' : ℂ) + t * I‖ * ‖(σ' : ℂ) + t * I + 1‖) := by
    rw [perron_kernel_norm X hX]; congr 1; simp
  have hden : σ' ^ 2 + t ^ 2 ≤ ‖(σ' : ℂ) + ↑t * I‖ * ‖(σ' : ℂ) + ↑t * I + 1‖ := by
    have e1 : ‖(σ' : ℂ) + ↑t * I‖ = Real.sqrt (σ' ^ 2 + t ^ 2) := Complex.norm_add_mul_I σ' t
    have e2 : (σ' : ℂ) + ↑t * I + 1 = ((σ' + 1 : ℝ) : ℂ) + ↑t * I := by push_cast; ring
    have e3 : ‖(σ' : ℂ) + ↑t * I + 1‖ = Real.sqrt ((σ' + 1) ^ 2 + t ^ 2) := by
      rw [e2]; exact Complex.norm_add_mul_I _ _
    rw [e1, e3]
    have h4 : Real.sqrt (σ' ^ 2 + t ^ 2) ≤ Real.sqrt ((σ' + 1) ^ 2 + t ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    calc σ' ^ 2 + t ^ 2 = Real.sqrt (σ' ^ 2 + t ^ 2) * Real.sqrt (σ' ^ 2 + t ^ 2) :=
          (Real.mul_self_sqrt (by positivity)).symm
      _ ≤ Real.sqrt (σ' ^ 2 + t ^ 2) * Real.sqrt ((σ' + 1) ^ 2 + t ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
  have hσt : (0:ℝ) < σ' ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  rw [norm_mul, hknorm]
  calc ‖-deriv (DirichletCharacter.LFunction χ) ((σ' : ℂ) + ↑t * I) / DirichletCharacter.LFunction χ ((σ' : ℂ) + ↑t * I)‖
        * (X ^ σ' / (‖(σ' : ℂ) + ↑t * I‖ * ‖(σ' : ℂ) + ↑t * I + 1‖))
      ≤ M * (X ^ σ' / (σ' ^ 2 + t ^ 2)) := by
        apply mul_le_mul hLL ?_ (by positivity) hM
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg hX.le _) hσt hden
    _ = M * X ^ σ' / (σ' ^ 2 + t ^ 2) := by ring

open MeasureTheory in
/-- **W1 capstone (abstract rectangle assembly)**: given the smoothed-Perron representation
    `S = (1/2π)·∫_ℝ G(σ+it)`, the σ-line truncation error `Ct`, the rectangle identity, connector
    bounds `Cc`, and the shifted-line bound `Cs`, conclude `‖S‖ ≤ (Cs + 2Cc + Ct)/(2π)`. -/
lemma rectangle_assembly (S : ℂ) (G : ℂ → ℂ) (σ' σ T Ct Cc Cs : ℝ)
    (h1 : S = (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I))
    (h2 : ‖(∫ t : ℝ, G ((σ : ℂ) + t * Complex.I))
        - ∫ t in (-T)..T, G ((σ : ℂ) + t * Complex.I)‖ ≤ Ct)
    (h3 : (∫ x in σ'..σ, G ((x:ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        - (∫ x in σ'..σ, G ((x:ℂ) + ((T:ℝ) : ℂ) * Complex.I))
        + Complex.I • (∫ y in (-T)..T, G ((σ:ℂ) + (y:ℂ) * Complex.I))
        - Complex.I • (∫ y in (-T)..T, G ((σ':ℂ) + (y:ℂ) * Complex.I)) = 0)
    (h4 : ‖∫ x in σ'..σ, G ((x:ℂ) + ((T:ℝ) : ℂ) * Complex.I)‖ ≤ Cc)
    (h5 : ‖∫ x in σ'..σ, G ((x:ℂ) + ((-T:ℝ) : ℂ) * Complex.I)‖ ≤ Cc)
    (h6 : ‖∫ y in (-T)..T, G ((σ':ℂ) + (y:ℂ) * Complex.I)‖ ≤ Cs) :
    ‖S‖ ≤ (Cs + 2 * Cc + Ct) / (2 * Real.pi) := by
  set Full := ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) with hFull
  set R := ∫ y in (-T)..T, G ((σ:ℂ) + (y:ℂ) * Complex.I) with hRdef
  set L := ∫ y in (-T)..T, G ((σ':ℂ) + (y:ℂ) * Complex.I) with hLdef
  set Btm := ∫ x in σ'..σ, G ((x:ℂ) + ((-T:ℝ) : ℂ) * Complex.I) with hBdef
  set Top := ∫ x in σ'..σ, G ((x:ℂ) + ((T:ℝ) : ℂ) * Complex.I) with hTdef
  rw [smul_eq_mul, smul_eq_mul] at h3
  have h7 : Complex.I * R = Complex.I * L + (Top - Btm) := by linear_combination h3
  have hR : ‖R‖ ≤ Cs + 2 * Cc := by
    have h8 : ‖Complex.I * R‖ = ‖R‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    have h9 : ‖Complex.I * L‖ = ‖L‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    calc ‖R‖ = ‖Complex.I * R‖ := h8.symm
      _ = ‖Complex.I * L + (Top - Btm)‖ := by rw [h7]
      _ ≤ ‖Complex.I * L‖ + ‖Top - Btm‖ := norm_add_le (Complex.I * L) (Top - Btm)
      _ ≤ ‖L‖ + (‖Top‖ + ‖Btm‖) := by
          rw [h9]
          exact add_le_add le_rfl (norm_sub_le Top Btm)
      _ ≤ Cs + (Cc + Cc) := add_le_add h6 (add_le_add h4 h5)
      _ = Cs + 2 * Cc := by ring
  have hfull : ‖Full‖ ≤ Cs + 2 * Cc + Ct := by
    have hsplit : Full = (Full - R) + R := by ring
    calc ‖Full‖ = ‖(Full - R) + R‖ := by rw [← hsplit]
      _ ≤ ‖Full - R‖ + ‖R‖ := norm_add_le (Full - R) R
      _ ≤ Ct + (Cs + 2 * Cc) := add_le_add h2 hR
      _ = Cs + 2 * Cc + Ct := by ring
  have hnrm : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  have h2π : (0:ℝ) < 2 * Real.pi := by positivity
  rw [h1, norm_mul, hnrm]
  calc 1 / (2 * Real.pi) * ‖Full‖ = ‖Full‖ / (2 * Real.pi) := by ring
    _ ≤ (Cs + 2 * Cc + Ct) / (2 * Real.pi) := by gcongr

/-- **Zero-free strip** (SW brick W1d): `L(s,χ) ≠ 0` on the contour strip
    `Re s ≥ 1 − g/2`, `|Im s| ≤ T` — a zero there would contradict its own distance bound
    (`contour_zero_distance` at `ρ = s`: `0 = ‖s−s‖ ≥ g/2 > 0`). Gives the non-vanishing half of
    the `smoothed_integrand_rect_zero` rectangle hypothesis. -/
lemma LFunction_ne_zero_in_strip (ε : ℝ) (hε0 : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    ∀ T : ℝ, 0 ≤ T → ∀ s : ℂ, |s.im| ≤ T →
    1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2 ≤ s.re →
    DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨c, hc0, hc⟩ := contour_zero_distance ε hε0
  refine ⟨c, hc0, ?_⟩
  intro N _ χ hχ1 T hT0 s hsim hsre hzero
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hkey := hc N χ hχ1 T hT0 s hsim hsre s hzero (by simp)
  have hLT : (0:ℝ) < Real.log ((N:ℝ)*(4*(T+1)+7)) + 20 := by
    have : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*(T+1)+7)) := Real.log_nonneg (by nlinarith)
    linarith
  have hg0 : (0:ℝ) < c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2 := by
    have hNe : (0:ℝ) < ((N:ℝ))^(-ε) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  simp only [sub_self, norm_zero] at hkey
  linarith

/-- **Combined contour data** (SW brick W1e): ONE constant `c` under which the strip
    `1 − g/2 ≤ Re s ≤ 1 + g`, `|Im s| ≤ T` (`g = c·N^{−ε}/L_T`) is simultaneously zero-free and
    carries the `‖L′/L‖ ≤ C·N^ε·L_T²` bound. `c := min c₁ c₂` + strip monotonicity (a narrower strip
    inherits both properties). Resolves the two independent existentials for the W1 instantiation. -/
lemma contour_combined (ε : ℝ) (hε0 : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 1 ≤ C ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    ∀ T : ℝ, 0 ≤ T → ∀ s : ℂ, |s.im| ≤ T →
    1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2 ≤ s.re →
    DirichletCharacter.LFunction χ s ≠ 0 ∧
    (s.re ≤ 1 + c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) →
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖
        ≤ C * ((N:ℝ))^ε * (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)^2) := by
  obtain ⟨c₁, hc₁0, hzf⟩ := LFunction_ne_zero_in_strip ε hε0
  obtain ⟨c₂, C, hc₂0, hc₂12, hC1, hLL⟩ := contour_logDeriv_bound ε hε0
  refine ⟨min c₁ c₂, C, lt_min hc₁0 hc₂0, le_trans (min_le_right _ _) hc₂12, hC1, ?_⟩
  intro N _ χ hχ1 T hT0 s hsim hsre
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hNe : (0:ℝ) < ((N:ℝ))^(-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hLT : (0:ℝ) < Real.log ((N:ℝ)*(4*(T+1)+7)) + 20 := by
    have : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*(T+1)+7)) := Real.log_nonneg (by nlinarith)
    linarith
  have hfac : (0:ℝ) < ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) := by positivity
  have hmono1 : min c₁ c₂ * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)
      ≤ c₁ * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) := by
    apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hNe.le) hLT.le
  have hmono2 : min c₁ c₂ * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)
      ≤ c₂ * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) := by
    apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) hNe.le) hLT.le
  constructor
  · exact hzf N χ hχ1 T hT0 s hsim (by linarith)
  · intro hsre2
    exact hLL N χ hχ1 T hT0 s hsim (by linarith) (by linarith)

/-- **`−L′/L` ↔ `logDeriv` norm bridge** (SW brick W1f): `‖−deriv L/L‖ = ‖logDeriv L‖`, so
    `contour_combined`'s `logDeriv` bound transfers to the smoothed-integrand form. -/
lemma neg_logDeriv_norm_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
      = ‖logDeriv (DirichletCharacter.LFunction χ) s‖ := by
  rw [logDeriv_apply, neg_div, norm_neg]

/-- **Strip numerics** (SW brick W1g): with `0 < c ≤ 1/2`, `0 < Ne ≤ 1`, `20 ≤ LT`, the gap
    `g = c·Ne/LT` satisfies `0 < g ≤ 1/40`, so `σ' = 1−g/2 ≥ 3/4` (`shifted_line_integral_bound`'s
    hypothesis), `σ = 1+g ∈ (1,2]`, and `σ' ≤ σ`. The arithmetic inputs of the W1 instantiation. -/
lemma strip_numerics (c Ne LT : ℝ) (hc0 : 0 < c) (hc12 : c ≤ 1/2)
    (hNe0 : 0 < Ne) (hNe1 : Ne ≤ 1) (hLT : 20 ≤ LT) :
    0 < c * Ne / LT ∧ c * Ne / LT ≤ 1/40 ∧ 3/4 ≤ 1 - c * Ne / LT / 2 ∧
      1 < 1 + c * Ne / LT ∧ 1 - c * Ne / LT / 2 ≤ 1 + c * Ne / LT ∧ 1 + c * Ne / LT ≤ 2 := by
  have hLT0 : (0:ℝ) < LT := by linarith
  have hg0 : 0 < c * Ne / LT := by positivity
  have hgle : c * Ne / LT ≤ 1/40 := by
    rw [div_le_iff₀ hLT0]
    nlinarith
  refine ⟨hg0, hgle, by linarith, by linarith, by linarith, by linarith⟩

/-- **σ-line tail constant** (SW brick W1h): the smoothed integrand on `Re = σ > 1` is dominated by
    `(B·X^σ)/t²` off `t = 0` — the exact `hbound` input of `truncation_tail_bound`. -/
lemma sigma_line_tail_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (X σ : ℝ) (hX : 0 < X) (hσ : 1 < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, t ≠ 0 →
      ‖(-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ:ℂ) + t * I))
          * ((X:ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1)))‖
        ≤ (B * X ^ σ) / t ^ 2 := by
  obtain ⟨B, hB⟩ := neg_logDeriv_bounded_on_line χ σ hσ
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  refine ⟨B, hB0, fun t ht => ?_⟩
  have him : ((σ:ℂ) + t * I).im = t := by simp
  have hre : ((σ:ℂ) + t * I).re = σ := by simp
  have hkd := perron_kernel_decay X hX ((σ:ℂ) + t * I) (by rw [him]; exact ht)
  rw [hre, him] at hkd
  rw [norm_mul]
  calc ‖-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ:ℂ) + t * I)‖
        * ‖(X:ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1))‖
      ≤ B * (X ^ σ / t ^ 2) := mul_le_mul (hB t) hkd (norm_nonneg _) hB0
    _ = (B * X ^ σ) / t ^ 2 := by ring

/-- **Strip-point `M`-bound in integrand form** (SW brick W1i): given `contour_combined`'s
    `logDeriv` bound as a hypothesis (fixed constants; `T` = height, `[rlo, rhi]` = Re-range),
    every strip point `x + t·I` (`|t| ≤ T`, `rlo ≤ x ≤ rhi`) has `‖−L′/L(x+t·I)‖ ≤ M`. One
    packaging for BOTH the horizontal connectors (`t = ±T`) and the shifted vertical line
    (`x = σ'`, `t ∈ (−T,T]`). -/
lemma strip_point_M_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (M T rlo rhi : ℝ)
    (hcc : ∀ s : ℂ, |s.im| ≤ T → rlo ≤ s.re → s.re ≤ rhi →
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ M)
    (x t : ℝ) (hx1 : rlo ≤ x) (hx2 : x ≤ rhi) (ht : |t| ≤ T) :
    ‖-deriv (DirichletCharacter.LFunction χ) ((x:ℂ) + t * I) / DirichletCharacter.LFunction χ ((x:ℂ) + t * I)‖
      ≤ M := by
  rw [neg_logDeriv_norm_eq]
  apply hcc
  · simpa using ht
  · simpa using hx1
  · simpa using hx2


/-- **Rate-extraction core** (SW brick W1k): `X^{1−g/2} = X·exp(−(g/2)·log X)` for `X > 0` — turns
    the W1 bound's `X^{σ'}` into the exponential-savings form `X·exp(−(g/2)·log X)`, whence the SW
    rate after substituting `g = c·N^{−ε}/L_T` and the `T(X)` choice. -/
lemma rpow_shift_as_exp (X g : ℝ) (hX : 0 < X) :
    X ^ (1 - g / 2 : ℝ) = X * Real.exp (-(g / 2) * Real.log X) := by
  rw [Real.rpow_sub hX, Real.rpow_one, Real.rpow_def_of_pos hX, div_eq_mul_inv, ← Real.exp_neg]
  congr 1
  ring


/-- **W1 instantiation skeleton**: with packaged strip bounds `M`, tail constant `B`, and
    zero-freeness as hypotheses, `‖ψ_smooth(X,χ)‖`-type quantities obey the explicit bound. -/
theorem psi_smooth_bound_skeleton {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (S : ℂ) (X : ℝ) (hX : 1 < X) (σ' σ T M B : ℝ)
    (hσ'34 : 3/4 ≤ σ') (hσ'σ : σ' ≤ σ) (hT : 0 < T) (hM : 0 ≤ M)
    (hrep : S = (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, G' χ X ((σ : ℂ) + t * I))
    (htail : ‖(∫ t : ℝ, G' χ X ((σ : ℂ) + t * I))
        - ∫ t in (-T)..T, G' χ X ((σ : ℂ) + t * I)‖ ≤ 2 * (B * X ^ σ) / T)
    (hconnT : ‖∫ x in σ'..σ, G' χ X ((x:ℂ) + ((T : ℝ) : ℂ) * I)‖
      ≤ (σ - σ') * (M * X ^ σ / T ^ 2))
    (hconnB : ‖∫ x in σ'..σ, G' χ X ((x:ℂ) + ((-T : ℝ) : ℂ) * I)‖
      ≤ (σ - σ') * (M * X ^ σ / T ^ 2))
    (hline : ‖∫ y in (-T)..T, G' χ X ((σ':ℂ) + (y:ℂ) * I)‖ ≤ 6 * M * X ^ σ')
    (hzf : ∀ s : ℂ, |s.im| ≤ T → σ' ≤ s.re → DirichletCharacter.LFunction χ s ≠ 0) :
    ‖S‖ ≤ (6 * M * X ^ σ' + 2 * ((σ - σ') * (M * X ^ σ / T ^ 2)) + 2 * (B * X ^ σ) / T)
      / (2 * Real.pi) := by
  have hX0 : (0:ℝ) < X := by linarith
  -- the rectangle: z = σ' − T·I, w = σ + T·I
  have hzre : ((σ' : ℂ) + ((-T : ℝ) : ℂ) * I).re = σ' := by simp
  have hzim : ((σ' : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T := by simp
  have hwre : ((σ : ℂ) + ((T : ℝ) : ℂ) * I).re = σ := by simp
  have hwim : ((σ : ℂ) + ((T : ℝ) : ℂ) * I).im = T := by simp
  have hrect : Complex.reProdIm (Set.uIcc σ' σ) (Set.uIcc (-T) T)
      ⊆ {s : ℂ | 0 < s.re ∧ DirichletCharacter.LFunction χ s ≠ 0} := by
    intro s hs
    rw [Complex.mem_reProdIm] at hs
    obtain ⟨hre, him⟩ := hs
    rw [Set.uIcc_of_le hσ'σ] at hre
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at him
    have h1 : σ' ≤ s.re := hre.1
    have h2 : |s.im| ≤ T := abs_le.mpr ⟨him.1, him.2⟩
    exact ⟨by linarith, hzf s h2 h1⟩
  have h3' := smoothed_integrand_rect_zero χ hχ X hX0
    ((σ' : ℂ) + ((-T : ℝ) : ℂ) * I) ((σ : ℂ) + ((T : ℝ) : ℂ) * I)
    (by rw [hzre, hzim, hwre, hwim]; exact hrect)
  rw [hzre, hzim, hwre, hwim] at h3'
  exact rectangle_assembly S (G' χ X) σ' σ T (2 * (B * X ^ σ) / T)
    ((σ - σ') * (M * X ^ σ / T ^ 2)) (6 * M * X ^ σ') hrep htail h3'
    hconnT hconnB
    hline

end Principia.Common.SW
