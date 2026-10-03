/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.SW.ZeroFreeA

/-!
# Siegel–Walfisz, `ZeroFreeB`: the 3-4-1 engine and the de la Vallee-Poussin zero-free regions

Ported **verbatim** from the axiom-clean Siegel–Walfisz master
(`Principia Application/LeanSandbox/SiegelWalfiszMaster.lean` = `C:/Users/Christian/pnt/sw_full.lean`,
lines 2635–4640; there `#print axioms siegel_walfisz_proven = [propext, Classical.choice, Quot.sound]`,
built in the PrimeNumberTheoremAnd workspace on Mathlib `db127794`, one day from ours). The master
imported `Mathlib`, `PrimeNumberTheoremAnd.MediumPNT` and `PrimeNumberTheoremAnd.PerronFormula`; here
the Mathlib imports are narrowed, the two Perron-kernel shims are re-proved from Mathlib's Mellin
inversion (`Principia.Common.SW.PerronKernel`), and the `medium_PNT` shim is not ported (see
`MediumPNTBound` in `Principia.Common.SW.Rate`). Declarations live in `Principia.Common.SW`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DirichletCharacter Complex

namespace Principia.Common.SW

/-! ## The 3-4-1 positivity engine (mirrored from DirichletZeroFreeComposed.lean) -/

/-- The 3-4-1 trigonometric inequality: `3 + 4cosθ + cos2θ = 2(1+cosθ)² ≥ 0`.
    Foundation of the classical de la Vallée-Poussin zero-free region (for ζ and L(s,χ)). -/
lemma three_four_one (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  have h : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  rw [h]; nlinarith [sq_nonneg (Real.cos θ + 1)]

/-- Complex 3-4-1: for a unit `w = χ(n)·n^{-it}`, `Re(3 + 4w + w²) = 2(Re w + 1)² ≥ 0`.
    This is the term-by-term positivity feeding the log-derivative combination
    `-Re[ 3·(L'/L)(σ,χ₀) + 4·(L'/L)(σ+it,χ) + (L'/L)(σ+2it,χ²) ]`. -/
lemma three_four_one_complex (w : ℂ) (hw : ‖w‖ = 1) :
    0 ≤ (3 + 4 * w + w ^ 2).re := by
  have h1 : w.re ^ 2 + w.im ^ 2 = 1 := by
    have h : (w.re * w.re + w.im * w.im : ℝ) = 1 := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hw]; norm_num
    nlinarith [h]
  have h2 : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by
    rw [sq, Complex.mul_re]; ring
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.re_ofNat,
    Complex.im_ofNat, Complex.ofReal_im, h2]
  nlinarith [sq_nonneg (w.re + 1), h1]

/-- Termwise 3-4-1 for the Dirichlet log-derivative combination: for a coprime `n`,
    `χ⁰(n)=1`, `w₀ = χ(n)` is a unit and `u = n^{-it}` is a unit, so the bracket
    `3·1 + 4·(w₀·u) + (w₀·u)²` (the `n`-th term of `3(L'/L)(σ,χ⁰)+4(L'/L)(σ+it,χ)+(L'/L)(σ+2it,χ²)`
    up to the positive weight `Λ(n)n^{-σ}`) has nonnegative real part. -/
lemma three_four_one_char (w₀ u : ℂ) (h₀ : ‖w₀‖ = 1) (hu : ‖u‖ = 1) :
    0 ≤ (3 + 4 * (w₀ * u) + (w₀ * u) ^ 2).re := by
  apply three_four_one_complex
  rw [norm_mul, h₀, hu, mul_one]

/-- The weighted term stays nonnegative: multiplying by a nonnegative real weight
    (`Λ(n)·n^{-σ} ≥ 0`) preserves the sign. -/
lemma three_four_one_char_weighted (c : ℝ) (hc : 0 ≤ c) (w₀ u : ℂ) (h₀ : ‖w₀‖ = 1)
    (hu : ‖u‖ = 1) : 0 ≤ c * (3 + 4 * (w₀ * u) + (w₀ * u) ^ 2).re :=
  mul_nonneg hc (three_four_one_char w₀ u h₀ hu)

open Complex in
/-- 1c-i: `n^{it}` (equivalently `n^{-it}`) is a unit for `n ≥ 1` — the imaginary exponent
    contributes no modulus. -/
lemma norm_nat_cpow_I (n : ℕ) (hn : 1 ≤ n) (t : ℝ) : ‖(n : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
  have hp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos hp]
  simp [Complex.mul_re, Complex.mul_im]

open Complex in
/-- 1c-ii (the analytic core): the `n`-th term of the 3-4-1 log-derivative combination has
    nonnegative real part. `c0,c1,c2 = χ⁰(n),χ(n),χ²(n)` obey the dichotomy: all zero off the
    coprime set, else `c0=1, ‖c1‖=1, c2=c1²`. -/
lemma term_combination_re_nonneg (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ) (c0 c1 c2 : ℂ)
    (hcase : (c0 = 0 ∧ c1 = 0 ∧ c2 = 0) ∨ (c0 = 1 ∧ ‖c1‖ = 1 ∧ c2 = c1 ^ 2)) :
    0 ≤ (3 * (c0 * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (σ : ℂ))
       + 4 * (c1 * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * I))
       + (c2 * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + 2 * t * I))).re := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  rcases hcase with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · subst h0 h1 h2; simp
  · subst h0 h2
    have hd1 : (n : ℂ) ^ ((σ : ℂ) + t * I) = (n : ℂ) ^ (σ : ℂ) * (n : ℂ) ^ ((t : ℂ) * I) := by
      rw [← Complex.cpow_add _ _ hn0]
    have hd2 : (n : ℂ) ^ ((σ : ℂ) + 2 * t * I)
        = (n : ℂ) ^ (σ : ℂ) * ((n : ℂ) ^ ((t : ℂ) * I)) ^ 2 := by
      rw [show (σ : ℂ) + 2 * (t : ℂ) * I = (σ : ℂ) + (t : ℂ) * I + (t : ℂ) * I by ring,
        Complex.cpow_add _ _ hn0, Complex.cpow_add _ _ hn0, sq]
      try ring
    rw [hd1, hd2]
    set P : ℂ := (n : ℂ) ^ (σ : ℂ) with hP
    set U : ℂ := (n : ℂ) ^ ((t : ℂ) * I) with hU
    set vm : ℝ := ArithmeticFunction.vonMangoldt n with hvm
    have hUnorm : ‖U‖ = 1 := norm_nat_cpow_I n hn t
    have hUne : U ≠ 0 := by
      intro h; rw [h, norm_zero] at hUnorm; norm_num at hUnorm
    have hPreal : P = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [hP, ← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ (n:ℝ))]
    have hPpos : (0 : ℝ) < (n : ℝ) ^ σ := by positivity
    have hPne : P ≠ 0 := by rw [hPreal]; exact_mod_cast ne_of_gt hPpos
    have key : 3 * ((1 : ℂ) * (vm : ℂ) / P) + 4 * (c1 * (vm : ℂ) / (P * U))
        + c1 ^ 2 * (vm : ℂ) / (P * U ^ 2)
        = (((vm / (n : ℝ) ^ σ : ℝ)) : ℂ) * (3 + 4 * (c1 * U⁻¹) + (c1 * U⁻¹) ^ 2) := by
      rw [hPreal]; push_cast; field_simp; try ring
    rw [key, Complex.re_ofReal_mul]
    apply mul_nonneg
    · apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_of_lt hPpos)
    · exact three_four_one_char c1 U⁻¹ h1 (by rw [norm_inv, hUnorm, inv_one])

/-- 1c-iii (character dichotomy): the triple `(χ⁰(n), χ(n), χ²(n))` obeys the dichotomy
    required by `term_combination_re_nonneg`. -/
lemma char_triple_dichotomy {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) :
    (((1 : DirichletCharacter ℂ N) (n : ZMod N) = 0 ∧ χ (n : ZMod N) = 0
        ∧ (χ ^ 2) (n : ZMod N) = 0)
     ∨ ((1 : DirichletCharacter ℂ N) (n : ZMod N) = 1 ∧ ‖χ (n : ZMod N)‖ = 1
        ∧ (χ ^ 2) (n : ZMod N) = (χ (n : ZMod N)) ^ 2)) := by
  by_cases h : IsUnit (n : ZMod N)
  · right
    refine ⟨MulChar.one_apply h, ?_, MulChar.pow_apply' χ (by norm_num) _⟩
    obtain ⟨u, hu⟩ := h
    rw [← hu]; exact χ.unit_norm_eq_one u
  · exact Or.inl ⟨MulChar.map_nonunit _ h, MulChar.map_nonunit _ h, MulChar.map_nonunit _ h⟩

open ArithmeticFunction Complex in
open scoped LSeries.notation ArithmeticFunction in
/-- 1c (assembled): the log-derivative 3-4-1 combination has nonnegative real part for σ>1. -/
lemma logDeriv_combo_re_nonneg {N : ℕ} (χ : DirichletCharacter ℂ N) (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ (3 * LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)
       + 4 * LSeries (↗χ * ↗Λ) ((σ : ℂ) + t * I)
       + LSeries (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + 2 * t * I)).re := by
  have hs0 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hs1 : 1 < ((σ : ℂ) + t * I).re := by simp; linarith
  have hs2 : 1 < ((σ : ℂ) + 2 * t * I).re := by simp; linarith
  have S0 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (1 : DirichletCharacter ℂ N) hs0
  have S1 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs1
  have S2 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ ^ 2) hs2
  simp only [LSeries]
  have H := ((S0.hasSum.mul_left 3).add (S1.hasSum.mul_left 4)).add S2.hasSum
  rw [← H.tsum_eq, re_tsum H.summable]
  apply tsum_nonneg
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [Pi.mul_apply]
    exact term_combination_re_nonneg n (Nat.one_le_iff_ne_zero.mpr hn) σ t _ _ _
      (char_triple_dichotomy χ n)

/-- 1d (assembly): plug the three raw `L'/L` bounds into the 1c combination `0 ≤ 3A₀+4A₁+A₂`
    (where `A₀ = Re L(χ⁰Λ,σ)`, `A₁ = Re L(χΛ,σ+iγ)`, `A₂ = Re L(χ²Λ,σ+2iγ)`) to get the combined
    bound consumed by `zero_free_region_from_bounds`. Reduces all of 1d to the raw bounds:
    (pole) `A₀ ≤ 1/(σ-1)+K`, (zero) `A₁ ≤ K - 1/(σ-β)`, (growth) `A₂ ≤ K`. -/
lemma combined_bound_from_ingredients (β σ K A₀ A₁ A₂ : ℝ)
    (hcombo : 0 ≤ 3 * A₀ + 4 * A₁ + A₂)
    (hpole : A₀ ≤ 1 / (σ - 1) + K) (hzero : A₁ ≤ K - 1 / (σ - β)) (hgrowth : A₂ ≤ K) :
    1 / (σ - β) ≤ 3 / (4 * (σ - 1)) + 2 * K := by
  have hbridge : 3 / 4 * (1 / (σ - 1)) = 3 / (4 * (σ - 1)) := by
    rw [div_mul_div_comm]; norm_num
  linarith [hcombo, hpole, hzero, hgrowth, hbridge]

open ArithmeticFunction Complex in
open scoped LSeries.notation ArithmeticFunction in
/-- **THE UNIFORM ZERO-FREE REGION** (SW brick U7 — de la Vallée-Poussin with an
    absolute constant): there is one `C` such that EVERY zero `β + iγ` of EVERY
    `L(·,χ)` with `χ` nontrivial non-quadratic satisfies
    `β ≤ 1 − 1/(335(1360+C)(log(N(4|γ|+7)) + 20))` — the classical
    `1 − c/log(N(|γ|+2))` region, fully uniform in `(N, χ, γ)`. Composition: the
    positivity engine + uniform pole (twist_re_le_uniform) + uniform zero (U5) +
    uniform growth (U6) at the single point `σ = 1 + 1/(100M)`, where
    `M = 80(log+20) + 20·max(K_P,1) + 24000` a-priori majorizes the Landau constant
    (via `log M ≤ 2√M ≤ M/160`). -/
theorem dvp_zero_free_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ ^ 2 ≠ 1 → ∀ β γ : ℝ,
      DirichletCharacter.LFunction χ ((β : ℂ) + γ * Complex.I) = 0 →
      β ≤ 1 - 1 / (335 * (1360 + C) * (Real.log ((N : ℝ) * (4 * |γ| + 7)) + 20)) := by
  obtain ⟨KP, hKP⟩ := twist_re_le_uniform
  set KP' : ℝ := max KP 1 with hKP'def
  have hKP'1 : 1 ≤ KP' := le_max_right _ _
  have hKPle : KP ≤ KP' := le_max_left _ _
  refine ⟨KP', hKP'1, ?_⟩
  intro N _ χ hχ hχ2 β γ hzero
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have h47 : (0:ℝ) < 4 * |γ| + 7 := by positivity
  have harg1 : (1:ℝ) ≤ (N : ℝ) * (4 * |γ| + 7) := by nlinarith [abs_nonneg γ]
  have hL₀ : 0 ≤ Real.log ((N : ℝ) * (4 * |γ| + 7)) := Real.log_nonneg harg1
  set M : ℝ := 80 * (Real.log ((N : ℝ) * (4 * |γ| + 7)) + 20) + 20 * KP' + 24000 with hMdef
  have hM25600 : 25600 ≤ M := by rw [hMdef]; nlinarith
  have hM0 : (0:ℝ) < M := by linarith
  set σ : ℝ := 1 + 1 / (100 * M) with hσdef
  have hinv0 : (0:ℝ) < 1 / (100 * M) := by
    apply div_pos one_pos
    linarith
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ0 : (0:ℝ) < σ := by linarith
  have hσ2 : σ ≤ 2 := by
    rw [hσdef]
    have h1 : 1 / (100 * M) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  have hσ1' : σ - 1 = 1 / (100 * M) := by rw [hσdef]; ring
  have hβ1 : β < 1 := by
    by_contra hβ'
    push_neg at hβ'
    have hre : (1:ℝ) ≤ ((β : ℂ) + γ * Complex.I).re := by simp; linarith
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hre hzero
  have hσβ0 : (0:ℝ) < σ - β := by linarith
  -- log M ≤ 2√M and 80√M ≤ M/2
  set sM : ℝ := M ^ ((1:ℝ)/2) with hsMdef
  have hsM0 : 0 ≤ sM := Real.rpow_nonneg hM0.le _
  have hsq : sM ^ (2:ℕ) = M := by
    rw [hsMdef, ← Real.rpow_natCast (M ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hM0.le]
    norm_num
  have h160 : 160 ≤ sM := by nlinarith [hsq, hM25600, hsM0]
  have hlogM : Real.log M ≤ 2 * sM := by
    have h := Real.log_le_rpow_div hM0.le (show (0:ℝ) < 1/2 by norm_num)
    rw [← hsMdef] at h
    linarith
  have h80s : 80 * sM ≤ M / 2 := by nlinarith [hsq, h160, hsM0]
  -- nonzeroness for log_mul
  have hNne : ((N:ℝ)) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hN1)
  have h47ne : (4 * |γ| + 7 : ℝ) ≠ 0 := ne_of_gt h47
  have hσne : σ ≠ 0 := ne_of_gt hσ0
  have hMne : M ≠ 0 := ne_of_gt hM0
  -- the a-priori majorant: K_A ≤ M
  have hKA : 40 * (Real.log ((N : ℝ) * (4 * |γ| + 7) * σ / (σ - 1)) + 1) ≤ M := by
    have hlogσ : Real.log σ ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos hσ0
      have hσ1e : σ - 1 ≤ 1 := by
        rw [hσ1', div_le_one (by linarith)]
        linarith
      linarith
    have hlog100 : Real.log 100 ≤ 18 := by
      have h10 : Real.log 10 ≤ 9 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 10 by norm_num)
        linarith
      have h100 : Real.log 100 = Real.log 10 + Real.log 10 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        norm_num
      linarith
    have hsplit : (N : ℝ) * (4 * |γ| + 7) * σ / (σ - 1)
        = (N : ℝ) * (4 * |γ| + 7) * σ * (100 * M) := by
      rw [hσ1', div_eq_mul_inv, one_div, inv_inv]
    rw [hsplit]
    have hlogprod : Real.log ((N : ℝ) * (4 * |γ| + 7) * σ * (100 * M))
        = Real.log ((N : ℝ) * (4 * |γ| + 7)) + Real.log σ
          + (Real.log 100 + Real.log M) := by
      rw [Real.log_mul (mul_ne_zero (mul_ne_zero hNne h47ne) hσne)
          (by norm_num; exact hMne : (100 * M : ℝ) ≠ 0),
        Real.log_mul (mul_ne_zero hNne h47ne) hσne,
        Real.log_mul (by norm_num : (100:ℝ) ≠ 0) hMne]
    rw [hlogprod]
    have hM40 : 80 * Real.log ((N : ℝ) * (4 * |γ| + 7)) + 1600 ≤ M := by
      rw [hMdef]
      nlinarith
    nlinarith [hlogσ, hlog100, hlogM, h80s]
  -- far case: trivially deep
  rcases le_or_gt (σ - β) (1/5) with hnear | hfar
  swap
  · have hsmall : 1 / (100 * M) ≤ (1:ℝ) / 2560000 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    rw [hσdef] at hfar
    have hβfar : β < (0.81 : ℝ) := by linarith
    have hCbig : (10:ℝ) ≤ 335 * (1360 + KP')
        * (Real.log ((N : ℝ) * (4 * |γ| + 7)) + 20) := by nlinarith
    have hfrac : 1 / (335 * (1360 + KP') * (Real.log ((N : ℝ) * (4 * |γ| + 7)) + 20))
        ≤ 1/10 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hCbig
    linarith
  -- main case: the 3-4-1 chain at the single σ
  · have hcombo := logDeriv_combo_re_nonneg χ σ γ hσ1
    have hlin : (3 * LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)
         + 4 * LSeries (↗χ * ↗Λ) ((σ : ℂ) + γ * I)
         + LSeries (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + 2 * γ * I)).re
        = 3 * (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)).re
          + 4 * (LSeries (↗χ * ↗Λ) ((σ : ℂ) + γ * I)).re
          + (LSeries (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + 2 * γ * I)).re := by
      simp [Complex.add_re, Complex.mul_re]
    rw [hlin] at hcombo
    have hpole : (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)).re
        ≤ 1 / (σ - 1) + M := by
      have h := hKP N (1 : DirichletCharacter ℂ N) 0 σ hσ1 hσ2
      have hpt : ((σ : ℂ) + ((0:ℝ) : ℂ) * I) = (σ : ℂ) := by push_cast; ring
      rw [hpt] at h
      have hKPM : KP ≤ M := by
        rw [hMdef]
        nlinarith
      linarith
    have hzb := zero_bound_uniform N χ hχ β γ hzero σ hσ1 hσ2 hnear
    have hKU5 : 40 * (Real.log ((N : ℝ) * (2 * |γ| + 7) * σ / (σ - 1)) + 1)
        ≤ 40 * (Real.log ((N : ℝ) * (4 * |γ| + 7) * σ / (σ - 1)) + 1) := by
      have hle : (N : ℝ) * (2 * |γ| + 7) * σ / (σ - 1)
          ≤ (N : ℝ) * (4 * |γ| + 7) * σ / (σ - 1) := by
        apply div_le_div_of_nonneg_right _ (by rw [hσ1']; exact hinv0.le)
        have h1 : (N:ℝ) * (2 * |γ| + 7) ≤ (N:ℝ) * (4 * |γ| + 7) := by
          nlinarith [abs_nonneg γ]
        exact mul_le_mul_of_nonneg_right h1 hσ0.le
      have hpos : (0:ℝ) < (N : ℝ) * (2 * |γ| + 7) * σ / (σ - 1) := by
        rw [hσ1']
        have h27 : (0:ℝ) < (N:ℝ) * (2 * |γ| + 7) := by nlinarith [abs_nonneg γ]
        have := mul_pos h27 hσ0
        exact div_pos this hinv0
      have := Real.log_le_log hpos hle
      linarith
    have hzero' : (LSeries (↗χ * ↗Λ) ((σ : ℂ) + γ * I)).re ≤ M - 1 / (σ - β) := by
      linarith [hzb, hKA, hKU5]
    have hgb := growth_bound_uniform N (χ ^ 2) hχ2 (2 * γ) σ hσ1 hσ2
    have hpt2 : ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I) = ((σ : ℂ) + 2 * (γ : ℂ) * I) := by
      push_cast
      ring
    rw [hpt2] at hgb
    have habs2 : (2:ℝ) * |2 * γ| + 7 = 4 * |γ| + 7 := by
      rw [abs_mul, abs_two]
      ring
    rw [habs2] at hgb
    have hgrowth : (LSeries (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + 2 * γ * I)).re ≤ M := by
      linarith [hKA]
    have hcb := combined_bound_from_ingredients β σ M _ _ _ hcombo hpole hzero' hgrowth
    have h34 : 3 / (4 * (σ - 1)) = 75 * M := by
      rw [hσ1']
      rw [div_eq_iff (by
        have : (0:ℝ) < 4 * (1 / (100 * M)) := by linarith
        exact ne_of_gt this)]
      field_simp
      ring
    rw [h34] at hcb
    have h77 : 1 / (σ - β) ≤ 77 * M := by linarith
    have hgap : 1 / (77 * M) ≤ σ - β := by
      have h77M0 : (0:ℝ) < 77 * M := by linarith
      rw [div_le_iff₀ h77M0]
      rw [div_le_iff₀ hσβ0] at h77
      nlinarith [h77]
    have hβbound : β ≤ 1 - 1 / (335 * M) := by
      have hstep : β ≤ σ - 1 / (77 * M) := by linarith
      rw [hσdef] at hstep
      have e1 : 1 / (100 * M) - 1 / (77 * M) = - (23 / (7700 * M)) := by
        field_simp
        ring
      have e2 : 1 / (335 * M) ≤ 23 / (7700 * M) := by
        rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 335 * M)
          (by linarith : (0:ℝ) < 7700 * M)]
        nlinarith
      linarith
    have hMC : 335 * M ≤ 335 * (1360 + KP')
        * (Real.log ((N : ℝ) * (4 * |γ| + 7)) + 20) := by
      rw [hMdef]
      nlinarith [hL₀, hKP'1]
    have hfinal : 1 / (335 * (1360 + KP') * (Real.log ((N : ℝ) * (4 * |γ| + 7)) + 20))
        ≤ 1 / (335 * M) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) hMC
    linarith

section ConjSymmetry
open Finset Filter Metric Topology

/-- Values of a quadratic character lie in `{−1, 0, 1}` (copy of the SiegelTheorem
    brick, needed here for conjugation symmetry). -/
lemma dvp_real_char_repr {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    (a : ZMod q) : χ a = -1 ∨ χ a = 0 ∨ χ a = 1 := by
  by_cases hu : IsUnit a
  · have hsq : χ a * χ a = 1 := by
      have h1 : (χ ^ 2) a = 1 := by
        rw [hχ2]
        exact MulChar.one_apply hu
      rw [pow_two, MulChar.mul_apply] at h1
      exact h1
    have hfactor : (χ a - 1) * (χ a + 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfactor with h | h
    · right; right
      exact sub_eq_zero.mp h
    · left
      exact eq_neg_of_add_eq_zero_left h
  · right; left
    exact MulChar.map_nonunit χ hu

/-- Quadratic characters are real-valued: conjugation fixes every value. -/
lemma conj_char_val {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    (a : ZMod q) : (starRingEnd ℂ) (χ a) = χ a := by
  rcases dvp_real_char_repr χ hχ2 a with h | h | h <;> rw [h] <;> simp

/-- The antiholomorphic square: if `f` is complex-differentiable at `conj z`, then
    `s ↦ conj (f (conj s))` is complex-differentiable at `z` with the conjugated
    derivative. -/
lemma hasDerivAt_conj_conj {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' ((starRingEnd ℂ) z)) :
    HasDerivAt (fun s => (starRingEnd ℂ) (f ((starRingEnd ℂ) s)))
      ((starRingEnd ℂ) f') z := by
  rw [hasDerivAt_iff_isLittleO] at hf ⊢
  have hct : Tendsto (starRingEnd ℂ) (𝓝 z) (𝓝 ((starRingEnd ℂ) z)) :=
    Complex.continuous_conj.continuousAt
  have h1 := hf.comp_tendsto hct
  simp only [Function.comp_def] at h1
  rw [Asymptotics.isLittleO_iff] at h1 ⊢
  intro c hc
  filter_upwards [h1 hc] with x hx
  have he : (starRingEnd ℂ) (f ((starRingEnd ℂ) x)) - (starRingEnd ℂ) (f ((starRingEnd ℂ) z))
      - (x - z) • (starRingEnd ℂ) f'
      = (starRingEnd ℂ) (f ((starRingEnd ℂ) x) - f ((starRingEnd ℂ) z)
          - ((starRingEnd ℂ) x - (starRingEnd ℂ) z) • f') := by
    simp only [map_sub, map_mul, smul_eq_mul, Complex.conj_conj]
  have hn : ‖(starRingEnd ℂ) x - (starRingEnd ℂ) z‖ = ‖x - z‖ := by
    rw [← map_sub, Complex.norm_conj]
  calc ‖(starRingEnd ℂ) (f ((starRingEnd ℂ) x)) - (starRingEnd ℂ) (f ((starRingEnd ℂ) z))
        - (x - z) • (starRingEnd ℂ) f'‖
      = ‖f ((starRingEnd ℂ) x) - f ((starRingEnd ℂ) z)
          - ((starRingEnd ℂ) x - (starRingEnd ℂ) z) • f'‖ := by
        rw [he, Complex.norm_conj]
    _ ≤ c * ‖(starRingEnd ℂ) x - (starRingEnd ℂ) z‖ := hx
    _ = c * ‖x - z‖ := by rw [hn]

/-- On `Re > 1` the conjugation symmetry holds by the Dirichlet series. -/
lemma LFunction_conj_series {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ2 : χ ^ 2 = 1) {w : ℂ} (hw : 1 < w.re) :
    (starRingEnd ℂ) (DirichletCharacter.LFunction χ ((starRingEnd ℂ) w))
      = DirichletCharacter.LFunction χ w := by
  have hwc : 1 < ((starRingEnd ℂ) w).re := by
    rw [Complex.conj_re]
    exact hw
  rw [DirichletCharacter.LFunction_eq_LSeries _ hwc,
    DirichletCharacter.LFunction_eq_LSeries _ hw]
  have hsum : LSeriesSummable (fun n : ℕ => χ ((n : ZMod N))) ((starRingEnd ℂ) w) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hwc
  have h1 : HasSum (fun n : ℕ => LSeries.term (fun n : ℕ => χ ((n : ZMod N)))
      ((starRingEnd ℂ) w) n)
      (LSeries (fun n : ℕ => χ ((n : ZMod N))) ((starRingEnd ℂ) w)) := hsum.hasSum
  have h2 := h1.star
  simp only [Complex.star_def] at h2
  have h3 : (fun n : ℕ => (starRingEnd ℂ)
      (LSeries.term (fun n : ℕ => χ ((n : ZMod N))) ((starRingEnd ℂ) w) n))
      = fun n : ℕ => LSeries.term (fun n : ℕ => χ ((n : ZMod N))) w n := by
    funext n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp [LSeries.term]
    · have hn0 : n ≠ 0 := hpos.ne'
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0,
        map_div₀, conj_char_val χ hχ2]
      congr 1
      have harg : ((n : ℂ)).arg ≠ Real.pi := by
        rw [Complex.natCast_arg]
        exact Real.pi_ne_zero.symm
      have hcp := Complex.cpow_conj ((n : ℂ)) w harg
      rw [map_natCast] at hcp
      rw [hcp, Complex.conj_conj]
  rw [h3] at h2
  rw [LSeries]
  exact h2.tsum_eq.symm

/-- **Conjugation symmetry of quadratic L-functions** (SW brick S4a-1): for `χ² = 1`,
    `χ ≠ 1`, `L(χ, conj s) = conj (L(χ, s))` everywhere — the coefficients are real,
    and both sides are entire. -/
theorem LFunction_conj_quadratic {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction χ ((starRingEnd ℂ) s)
      = (starRingEnd ℂ) (DirichletCharacter.LFunction χ s) := by
  have hLd : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ1
  have hgd : Differentiable ℂ (fun w => (starRingEnd ℂ)
      (DirichletCharacter.LFunction χ ((starRingEnd ℂ) w))) := by
    intro z
    exact (hasDerivAt_conj_conj (hLd ((starRingEnd ℂ) z)).hasDerivAt).differentiableAt
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2U : (2:ℂ) ∈ {w : ℂ | 1 < w.re} := by
    simp only [Set.mem_setOf_eq]
    norm_num
  have hseed : (fun w => (starRingEnd ℂ)
      (DirichletCharacter.LFunction χ ((starRingEnd ℂ) w)))
      =ᶠ[𝓝 2] DirichletCharacter.LFunction χ := by
    filter_upwards [hU.mem_nhds h2U] with w hw
    exact LFunction_conj_series χ hχ2 hw
  have heq : Set.EqOn (fun w => (starRingEnd ℂ)
      (DirichletCharacter.LFunction χ ((starRingEnd ℂ) w)))
      (DirichletCharacter.LFunction χ) Set.univ :=
    ((hgd.differentiableOn).analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
      ((hLd.differentiableOn).analyticOnNhd isOpen_univ)
      isPreconnected_univ (Set.mem_univ 2) hseed
  have hs := heq (Set.mem_univ s)
  simp only at hs
  calc DirichletCharacter.LFunction χ ((starRingEnd ℂ) s)
      = (starRingEnd ℂ) ((starRingEnd ℂ)
          (DirichletCharacter.LFunction χ ((starRingEnd ℂ) s))) := (Complex.conj_conj _).symm
    _ = (starRingEnd ℂ) (DirichletCharacter.LFunction χ s) := by rw [hs]

/-- **Zeros of quadratic L-functions pair by conjugation** (SW brick S4a-1′). -/
theorem conj_zero_quadratic {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1) {ρ : ℂ}
    (hz : DirichletCharacter.LFunction χ ρ = 0) :
    DirichletCharacter.LFunction χ ((starRingEnd ℂ) ρ) = 0 := by
  rw [LFunction_conj_quadratic χ hχ2 hχ1 ρ, hz, map_zero]

end ConjSymmetry

open Metric ArithmeticFunction in
open scoped LSeries.notation ArithmeticFunction in
/-- **The conjugate-pair zero bound at the real point** (SW brick S4a-2): if BOTH
    `β ± iγ` are zeros of `L(·,χ)` (γ ≠ 0) close to the real point `σ`, peeling the
    PAIR from Landau's partial fractions doubles the repulsion:
    `Re L(χΛ, σ) ≤ 40(log(7Nσ/(σ−1)) + 1) − 2(σ−β)/((σ−β)² + γ²)`. -/
theorem zero_pair_bound_uniform (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (β γ : ℝ) (hγ : γ ≠ 0)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + γ * Complex.I) = 0)
    (hzero' : DirichletCharacter.LFunction χ ((β : ℂ) - γ * Complex.I) = 0)
    (σ : ℝ) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hnear : (σ - β)^2 + γ^2 ≤ 1/25) :
    (LSeries (↗χ * ↗Λ) ((σ : ℂ))).re
      ≤ 40 * (Real.log ((N : ℝ) * 7 * σ / (σ - 1)) + 1)
        - 2 * (σ - β) / ((σ - β)^2 + γ^2) := by
  set c : ℂ := (σ : ℂ) + (0:ℝ) * Complex.I with hc
  have hceq : c = (σ : ℂ) := by rw [hc]; push_cast; ring
  have hcre : c.re = σ := by rw [hceq]; simp
  set ρ₀ : ℂ := (β : ℂ) + γ * Complex.I with hρ₀def
  set ρ₁ : ℂ := (β : ℂ) - γ * Complex.I with hρ₁def
  have hρ₀re : ρ₀.re = β := by rw [hρ₀def]; simp
  have hρ₁re : ρ₁.re = β := by rw [hρ₁def]; simp
  have hρ₀im : ρ₀.im = γ := by rw [hρ₀def]; simp
  have hρ₁im : ρ₁.im = -γ := by rw [hρ₁def]; simp
  have hzlt : ∀ w : ℂ, DirichletCharacter.LFunction χ w = 0 → w.re < 1 := by
    intro w hw
    by_contra hwre
    push_neg at hwre
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hwre hw
  have hβ1 : β < 1 := by
    have := hzlt ρ₀ hzero
    rwa [hρ₀re] at this
  have hσβ0 : (0:ℝ) < σ - β := by linarith
  have hd0 : (0:ℝ) < (σ - β)^2 + γ^2 := by positivity
  obtain ⟨S, m, hSz, hm, hcomp, hmpos, hbound⟩ := landau_LFunction N χ hχ σ 0 hσ1 hσ2
  -- both members of the pair lie in the Landau ball
  have hball : ∀ d : ℝ, d^2 = γ^2 → ((β : ℂ) + (d:ℝ) * Complex.I) ∈ closedBall c (1/5) := by
    intro d hd
    rw [mem_closedBall, dist_eq_norm]
    have hdiff : ((β : ℂ) + (d:ℝ) * Complex.I) - c
        = ((β - σ : ℝ) : ℂ) + (d:ℝ) * Complex.I := by
      rw [hc]; push_cast; ring
    rw [hdiff, Complex.norm_add_mul_I]
    rw [show (β - σ:ℝ)^2 + d^2 = (σ-β)^2 + γ^2 by rw [hd]; ring]
    calc Real.sqrt ((σ-β)^2 + γ^2) ≤ Real.sqrt (1/25) := Real.sqrt_le_sqrt hnear
      _ = 1/5 := by
          rw [show (1/25:ℝ) = (1/5)^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/5)]
  have hρ₀S : ρ₀ ∈ S := hcomp ρ₀ (by rw [hρ₀def]; exact hball γ rfl) hzero
  have hρ₁S : ρ₁ ∈ S := by
    apply hcomp ρ₁ _ hzero'
    have hρ₁eq : ρ₁ = (β : ℂ) + ((-γ : ℝ):ℂ) * Complex.I := by
      rw [hρ₁def]; push_cast; ring
    rw [hρ₁eq]
    exact hball (-γ) (by ring)
  have hne : ρ₀ ≠ ρ₁ := by
    intro h
    have him := congrArg Complex.im h
    rw [hρ₀im, hρ₁im] at him
    exact hγ (by linarith)
  have hcz : c ∈ ball c (1/20) := mem_ball_self (by norm_num)
  have hzS : ∀ ρ ∈ S, c ≠ ρ := by
    intro ρ hρ hEq
    have hLρ := (hSz ρ hρ).2
    rw [← hEq] at hLρ
    have := hzlt c hLρ
    rw [hcre] at this
    linarith
  have hb := hbound c hcz hzS
  -- real part of each partial-fraction term is nonneg
  have hreS : ∀ ρ ∈ S, 0 ≤ ((m ρ : ℂ) / (c - ρ)).re := by
    intro ρ hρ
    have hρre : ρ.re < 1 := hzlt ρ (hSz ρ hρ).2
    rw [div_eq_mul_inv, show ((m ρ : ℕ) : ℂ) = (((m ρ : ℕ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_ofReal_mul, Complex.inv_re]
    apply mul_nonneg (Nat.cast_nonneg _)
    apply div_nonneg _ (Complex.normSq_nonneg _)
    rw [Complex.sub_re, hcre]
    linarith
  -- each pair term is ≥ (σ−β)/((σ−β)²+γ²)
  have hcim : c.im = 0 := by rw [hceq]; simp
  have hterm : ∀ ρ, ρ ∈ S → ρ.re = β → ρ.im ^ 2 = γ^2 →
      (σ - β) / ((σ - β)^2 + γ^2) ≤ ((m ρ : ℂ) / (c - ρ)).re := by
    intro ρ hρS hρre hρim
    have hre_d : (c - ρ).re = σ - β := by rw [Complex.sub_re, hcre, hρre]
    have him_d : (c - ρ).im = -ρ.im := by rw [Complex.sub_im, hcim]; ring
    have hnsq : Complex.normSq (c - ρ) = (σ - β)^2 + γ^2 := by
      rw [Complex.normSq_apply, hre_d, him_d, show (-ρ.im) * (-ρ.im) = ρ.im ^ 2 by ring,
        hρim]
      ring
    have heq : ((m ρ : ℂ) / (c - ρ)).re
        = (m ρ : ℝ) * ((σ - β) / ((σ - β)^2 + γ^2)) := by
      rw [div_eq_mul_inv, show ((m ρ : ℕ) : ℂ) = (((m ρ : ℕ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.re_ofReal_mul, Complex.inv_re, hre_d, hnsq]
    rw [heq]
    calc (σ - β) / ((σ - β)^2 + γ^2) = 1 * ((σ - β) / ((σ - β)^2 + γ^2)) := (one_mul _).symm
      _ ≤ (m ρ : ℝ) * ((σ - β) / ((σ - β)^2 + γ^2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hmpos ρ hρS
  -- the sum dominates the pair
  have hsum : 2 * (σ - β) / ((σ - β)^2 + γ^2) ≤ (∑ ρ ∈ S, (m ρ : ℂ) / (c - ρ)).re := by
    rw [Complex.re_sum]
    have hsub : ({ρ₀, ρ₁} : Finset ℂ) ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · rw [h]; exact hρ₀S
      · rw [Finset.mem_singleton] at h
        rw [h]; exact hρ₁S
    calc 2 * (σ - β) / ((σ - β)^2 + γ^2)
        = (σ - β) / ((σ - β)^2 + γ^2) + (σ - β) / ((σ - β)^2 + γ^2) := by ring
      _ ≤ ((m ρ₀ : ℂ) / (c - ρ₀)).re + ((m ρ₁ : ℂ) / (c - ρ₁)).re :=
          add_le_add (hterm ρ₀ hρ₀S hρ₀re (by rw [hρ₀im]))
            (hterm ρ₁ hρ₁S hρ₁re (by rw [hρ₁im]; ring))
      _ = ∑ ρ ∈ ({ρ₀, ρ₁} : Finset ℂ), ((m ρ : ℂ) / (c - ρ)).re :=
          (Finset.sum_pair (f := fun ρ => ((m ρ : ℂ) / (c - ρ)).re) hne).symm
      _ ≤ ∑ ρ ∈ S, ((m ρ : ℂ) / (c - ρ)).re :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ hρ _ => hreS ρ hρ)
  have hrediff : -(40 * (Real.log ((N : ℝ) * (2 * |(0:ℝ)| + 7) * σ / (σ - 1)) + 1))
      ≤ (logDeriv (DirichletCharacter.LFunction χ) c
          - ∑ ρ ∈ S, (m ρ : ℂ) / (c - ρ)).re := by
    have habs := (Complex.abs_re_le_norm _).trans hb
    linarith [(abs_le.mp habs).1]
  have hcre1 : 1 < c.re := by rw [hcre]; exact hσ1
  have hident : LSeries (↗χ * ↗Λ) c = - logDeriv (DirichletCharacter.LFunction χ) c := by
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq _ hcre1,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ hcre1,
      ← DirichletCharacter.LFunction_eq_LSeries _ hcre1, neg_div, ← logDeriv_apply]
  have habs0 : (N : ℝ) * (2 * |(0:ℝ)| + 7) * σ / (σ - 1) = (N : ℝ) * 7 * σ / (σ - 1) := by
    norm_num
  rw [habs0] at hrediff
  rw [show ((σ:ℝ) : ℂ) = c from hceq.symm, hident, Complex.neg_re]
  rw [Complex.sub_re] at hrediff
  linarith [hrediff, hsum]

open ArithmeticFunction Complex in
open scoped LSeries.notation ArithmeticFunction in
/-- **The 1-1 positivity combo at the real point** (SW brick S4a-3a): for any `χ`,
    `0 ≤ Re(L(χ⁰Λ, σ) + L(χΛ, σ))` for real `σ > 1` — termwise `Λ(n)(1 + Re χ(n)) ≥ 0`.
    The lower comparison feeding the conjugate-pair repulsion. -/
lemma pair_combo_re_nonneg {N : ℕ} (χ : DirichletCharacter ℂ N) (σ : ℝ) (hσ : 1 < σ) :
    0 ≤ (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) ((σ : ℂ))
       + LSeries (↗χ * ↗Λ) ((σ : ℂ))).re := by
  have hs0 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have S0 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    (1 : DirichletCharacter ℂ N) hs0
  have S1 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs0
  simp only [LSeries]
  have H := S0.hasSum.add S1.hasSum
  rw [← H.tsum_eq, re_tsum H.summable]
  apply tsum_nonneg
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [Pi.mul_apply]
    by_cases h : IsUnit ((n : ZMod N))
    · have h0 : (1 : DirichletCharacter ℂ N) ((n : ZMod N)) = 1 := MulChar.one_apply h
      have h1 : ‖χ ((n : ZMod N))‖ = 1 := by
        obtain ⟨u, hu⟩ := h
        rw [← hu]
        exact χ.unit_norm_eq_one u
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hPreal : (n : ℂ) ^ ((σ:ℝ) : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast n,
          ← Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ (n:ℝ))]
      have hPpos : (0:ℝ) < (n:ℝ) ^ σ := by
        have hn1 : (0:ℝ) < (n:ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hn
        positivity
      have key : ((1 : DirichletCharacter ℂ N) ((n : ZMod N)))
            * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n:ℂ) ^ ((σ:ℝ) : ℂ)
          + (χ ((n : ZMod N))) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
            / (n:ℂ) ^ ((σ:ℝ) : ℂ)
          = (((ArithmeticFunction.vonMangoldt n / (n:ℝ)^σ : ℝ)) : ℂ)
            * (1 + χ ((n : ZMod N))) := by
        rw [h0, hPreal]
        push_cast
        ring
      rw [key, Complex.re_ofReal_mul]
      apply mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hPpos.le)
      have habs := Complex.abs_re_le_norm (χ ((n : ZMod N)))
      rw [h1] at habs
      have h2 := (abs_le.mp habs).1
      rw [Complex.add_re, Complex.one_re]
      linarith
    · rw [MulChar.map_nonunit _ h, MulChar.map_nonunit _ h]
      simp

open scoped LSeries.notation ArithmeticFunction in
/-- **The quadratic small-height zero-free region** (SW brick S4a-3b): there is an
    absolute `C` such that every zero `β + iγ` (γ ≠ 0) of every quadratic nontrivial
    `L(·,χ)` mod `N` with `|γ| ≤ 1/(C·L₀)` (`L₀ = log(N(4|γ|+7))+20`) satisfies
    `β ≤ 1 − 1/(C·L₀)` — the conjugate-pair Landau repulsion at `σ = 1+2(1−β+|γ|)`,
    with the `log(1/x) ≤ 2/√x` a-priori trick closing the self-reference. -/
theorem quad_pair_gap :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ ^ 2 = 1 → ∀ β γ : ℝ, γ ≠ 0 →
      DirichletCharacter.LFunction χ ((β : ℂ) + γ * Complex.I) = 0 →
      |γ| * (C * (Real.log ((N : ℝ) * (4 * |γ| + 7)) + 20)) ≤ 1 →
      β ≤ 1 - 1 / (C * (Real.log ((N : ℝ) * (4 * |γ| + 7)) + 20)) := by
  obtain ⟨K, hK⟩ := twist_re_le_uniform
  obtain ⟨K', hK'def⟩ : ∃ K' : ℝ, K' = max K 0 := ⟨_, rfl⟩
  have hK'0 : 0 ≤ K' := by rw [hK'def]; exact le_max_right _ _
  have hKK' : K ≤ K' := by rw [hK'def]; exact le_max_left _ _
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = 2 * (576060 * (K'/20 + 40)) + 40 := ⟨_, rfl⟩
  have hC40 : 40 ≤ C := by
    rw [hCdef]
    nlinarith [hK'0]
  refine ⟨C, by linarith, ?_⟩
  intro N _ χ hχ1 hχ2 β γ hγ hzero hsmall
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hg0 : (0:ℝ) < |γ| := abs_pos.mpr hγ
  have harg1 : (1:ℝ) ≤ (N:ℝ) * (4*|γ|+7) := by nlinarith
  have hL0 : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*|γ|+7)) := Real.log_nonneg harg1
  obtain ⟨L₀, hL₀def⟩ : ∃ Lv : ℝ, Lv = Real.log ((N:ℝ)*(4*|γ|+7)) + 20 := ⟨_, rfl⟩
  rw [← hL₀def] at hsmall ⊢
  have hL20 : 20 ≤ L₀ := by rw [hL₀def]; linarith
  have hCL : 800 ≤ C * L₀ := by nlinarith
  have hCL0 : 0 < C * L₀ := by linarith
  have hβ1 : β < 1 := by
    by_contra hβ'
    push_neg at hβ'
    have hre : (1:ℝ) ≤ ((β:ℂ) + γ*Complex.I).re := by
      simp
      linarith
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hre hzero
  by_cases hb40 : 1/40 ≤ 1 - β
  · have h1 : 1/(C*L₀) ≤ 1/40 := by
      rw [div_le_div_iff₀ hCL0 (by norm_num : (0:ℝ) < 40)]
      linarith
    linarith
  push_neg at hb40
  have hb0 : (0:ℝ) < 1 - β := by linarith
  have hgC : |γ| ≤ 1/(C*L₀) := by
    rw [le_div_iff₀ hCL0]
    exact hsmall
  have hg800 : |γ| ≤ 1/800 := by
    refine le_trans hgC ?_
    rw [div_le_div_iff₀ hCL0 (by norm_num : (0:ℝ) < 800)]
    linarith
  obtain ⟨σ, hσdef⟩ : ∃ s : ℝ, s = 1 + 2*((1-β) + |γ|) := ⟨_, rfl⟩
  have hx0 : (0:ℝ) < (1-β) + |γ| := by linarith
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ2 : σ ≤ 2 := by rw [hσdef]; linarith [hb40, hg800]
  have hσβ : σ - β = 3*(1-β) + 2*|γ| := by rw [hσdef]; ring
  have hσ1x : σ - 1 = 2*((1-β)+|γ|) := by rw [hσdef]; ring
  -- the conjugate zero
  have hconjpt : (starRingEnd ℂ) ((β:ℂ) + γ*Complex.I) = (β:ℂ) - γ*Complex.I := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hzero' : DirichletCharacter.LFunction χ ((β:ℂ) - γ*Complex.I) = 0 := by
    rw [← hconjpt]
    exact conj_zero_quadratic χ hχ2 hχ1 hzero
  -- the pair repulsion
  have hnear : (σ-β)^2 + γ^2 ≤ 1/25 := by
    have h1 : σ - β ≤ 3/40 + 2/800 := by
      rw [hσβ]
      linarith [hb40, hg800]
    have hu0' : (0:ℝ) < σ - β := by rw [hσβ]; linarith
    have h2 : γ^2 ≤ (1/800)^2 := by
      rw [← sq_abs]
      nlinarith [hg800, hg0.le]
    nlinarith [h1, h2, hu0']
  have hpair := zero_pair_bound_uniform N χ hχ1 β γ hγ hzero hzero' σ hσ1 hσ2 hnear
  -- the lower comparison
  have hcombo := pair_combo_re_nonneg χ σ hσ1
  have hA0 := hK N (1 : DirichletCharacter ℂ N) 0 σ hσ1 hσ2
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hA0
  rw [Complex.add_re] at hcombo
  have hchain : 2*(σ-β)/((σ-β)^2+γ^2)
      ≤ 1/(σ-1) + K' + 40*(Real.log ((N:ℝ)*7*σ/(σ-1))+1) := by
    linarith [hpair, hcombo, hA0, hKK']
  -- lower-bound the repulsion by 8/(15x)
  have hu0 : (0:ℝ) < σ - β := by rw [hσβ]; linarith
  have hgu : 2*|γ| ≤ σ - β := by rw [hσβ]; linarith
  have hu3x : σ - β ≤ 3*((1-β)+|γ|) := by rw [hσβ]; linarith
  have hden0 : (0:ℝ) < (σ-β)^2 + γ^2 := by nlinarith [hu0, sq_nonneg γ]
  have hden : (σ-β)^2 + γ^2 ≤ (5/4)*(σ-β)^2 := by
    have h1 : γ^2 = |γ|^2 := (sq_abs γ).symm
    nlinarith [hgu, hg0.le]
  have hLHS1 : 8/(5*(σ-β)) ≤ 2*(σ-β)/((σ-β)^2+γ^2) := by
    rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 5*(σ-β)) hden0]
    nlinarith [hden]
  have hLHS2 : 8/(15*((1-β)+|γ|)) ≤ 8/(5*(σ-β)) := by
    apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 8) (by linarith : (0:ℝ) < 5*(σ-β))
    linarith [hu3x]
  have hkey : 1/(30*((1-β)+|γ|)) ≤ K' + 40 + 40*Real.log ((N:ℝ)*7*σ/(σ-1)) := by
    have h1 : 8/(15*((1-β)+|γ|)) - 1/(2*((1-β)+|γ|)) = 1/(30*((1-β)+|γ|)) := by
      field_simp
      ring
    have h2 : 1/(σ-1) = 1/(2*((1-β)+|γ|)) := by rw [hσ1x]
    linarith [hLHS1, hLHS2, hchain, h1.le, h1.ge, h2.le, h2.ge]
  -- bound the log: log(7Nσ/(σ−1)) ≤ log(7N) + log(1/x)
  have hlogb : Real.log ((N:ℝ)*7*σ/(σ-1))
      ≤ Real.log (7*(N:ℝ)) + Real.log (1/((1-β)+|γ|)) := by
    have harg0 : (0:ℝ) < (N:ℝ)*7*σ/(σ-1) := by
      apply div_pos (by nlinarith [hN1, hσ1]) (by linarith)
    have hxx : (1/((1-β)+|γ|)) * (2*((1-β)+|γ|)) = 2 := by
      field_simp
    have hle : (N:ℝ)*7*σ/(σ-1) ≤ 7*(N:ℝ) * (1/((1-β)+|γ|)) := by
      rw [hσ1x, div_le_iff₀ (by linarith : (0:ℝ) < 2*((1-β)+|γ|))]
      nlinarith [hσ2, hN1, hxx, hx0]
    calc Real.log ((N:ℝ)*7*σ/(σ-1))
        ≤ Real.log (7*(N:ℝ) * (1/((1-β)+|γ|))) := Real.log_le_log harg0 hle
      _ = Real.log (7*(N:ℝ)) + Real.log (1/((1-β)+|γ|)) :=
          Real.log_mul (by nlinarith [hN1]) (by positivity)
  -- the √-trick
  have hsqrt : Real.log (1/((1-β)+|γ|)) ≤ 2*(1/((1-β)+|γ|))^((1:ℝ)/2) := by
    have h1 := Real.log_le_rpow_div
      (le_of_lt (by positivity : (0:ℝ) < 1/((1-β)+|γ|)))
      (by norm_num : (0:ℝ) < 1/2)
    calc Real.log (1/((1-β)+|γ|)) ≤ (1/((1-β)+|γ|))^((1:ℝ)/2) / (1/2) := h1
      _ = 2*(1/((1-β)+|γ|))^((1:ℝ)/2) := by ring
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (1/((1-β)+|γ|))^((1:ℝ)/2) := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have ht2 : t^2 = 1/((1-β)+|γ|) := by
    rw [htdef, ← Real.rpow_natCast ((1/((1-β)+|γ|))^((1:ℝ)/2)) 2,
      ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 1/((1-β)+|γ|))]
    norm_num
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = K' + 40 + 40*Real.log (7*(N:ℝ)) := ⟨_, rfl⟩
  have hD40 : 40 ≤ D := by
    rw [hDdef]
    have h1 : (0:ℝ) ≤ Real.log (7*(N:ℝ)) := Real.log_nonneg (by nlinarith [hN1])
    linarith [hK'0]
  have hquad : t^2 ≤ 30*D + 2400*t := by
    have h1 : 1/(30*((1-β)+|γ|)) = t^2/30 := by
      rw [ht2, div_div]
      ring
    rw [h1] at hkey
    have h3 : Real.log ((N:ℝ)*7*σ/(σ-1)) ≤ Real.log (7*(N:ℝ)) + 2*t := by
      rw [htdef]
      linarith [hlogb, hsqrt]
    have h4 : K' + 40 + 40*Real.log ((N:ℝ)*7*σ/(σ-1)) ≤ D + 80*t := by
      rw [hDdef]
      linarith [h3]
    linarith [hkey, h4]
  have hres : t^2 ≤ 576060*D := by
    by_cases ht48 : t ≤ 4800
    · have h8 : 2400*t ≤ 11520000 := by linarith
      have h9 : (11520000:ℝ) ≤ 288000*D := by linarith [hD40]
      have h10 : (0:ℝ) ≤ D := by linarith [hD40]
      linarith [hquad, h8, h9, h10]
    · push_neg at ht48
      have h8 : 2400*t ≤ t^2/2 := by nlinarith [ht48, ht0]
      have h10 : (0:ℝ) ≤ D := by linarith [hD40]
      linarith [hquad, h8, h10]
  have hDL : D ≤ (K'/20 + 40)*L₀ := by
    rw [hDdef]
    have h1 : Real.log (7*(N:ℝ)) ≤ L₀ - 20 := by
      rw [hL₀def]
      have h2 : 7*(N:ℝ) ≤ (N:ℝ)*(4*|γ|+7) := by nlinarith [hN1, hg0.le]
      have h3 := Real.log_le_log (by nlinarith [hN1] : (0:ℝ) < 7*(N:ℝ)) h2
      linarith
    have h4 : K' ≤ (K'/20)*L₀ := by nlinarith [hK'0, hL20]
    have hexp : (K'/20 + 40)*L₀ = (K'/20)*L₀ + 40*L₀ := by ring
    linarith [h1, h4, hexp.le, hexp.ge, hL20]
  have hxfinal : t^2 ≤ (C/2)*L₀ := by
    have hCC : 576060*(K'/20+40) = (C-40)/2 := by
      rw [hCdef]
      ring
    have h5 : 576060*D ≤ ((C-40)/2)*L₀ := by
      have h9 : 576060*((K'/20+40)*L₀) = ((C-40)/2)*L₀ := by
        rw [← mul_assoc, hCC]
      have h11 := mul_le_mul_of_nonneg_left hDL (by norm_num : (0:ℝ) ≤ 576060)
      linarith [h11, h9.le, h9.ge]
    have h7 : (C/2)*L₀ = ((C-40)/2)*L₀ + 20*L₀ := by ring
    linarith [hres, h5, h7.le, h7.ge, hL20]
  have hxfinal' : 1/((1-β)+|γ|) ≤ (C/2)*L₀ := by
    rw [← ht2]
    exact hxfinal
  have h6 : 1 ≤ ((C/2)*L₀) * ((1-β)+|γ|) := by
    rw [div_le_iff₀ hx0] at hxfinal'
    linarith [hxfinal']
  have h2CL : 2/(C*L₀) ≤ (1-β)+|γ| := by
    rw [div_le_iff₀ hCL0]
    have h10 : (((C/2)*L₀))*((1-β)+|γ|)*2 = ((1-β)+|γ|)*(C*L₀) := by ring
    linarith [h6, h10.le, h10.ge]
  have hsplit : 2/(C*L₀) - 1/(C*L₀) = 1/(C*L₀) := by
    ring
  linarith [h2CL, hgC, hsplit.le, hsplit.ge]

/-- Derivative of `u ↦ (u:ℂ)^c` at positive real `u`. -/
lemma hasDerivAt_real_cpow_const {u : ℝ} (hu : 0 < u) (c : ℂ) :
    HasDerivAt (fun v : ℝ => ((v:ℂ)) ^ c) (c * ((u:ℂ)) ^ (c - 1)) u := by
  have h1 : HasDerivAt (fun z : ℂ => z ^ c) (c * ((u:ℂ)) ^ (c - 1) * 1) ((u:ℂ)) := by
    apply HasDerivAt.cpow_const (hasDerivAt_id ((u:ℂ)))
    exact Complex.ofReal_mem_slitPlane.mpr hu
  rw [mul_one] at h1
  exact h1.comp_ofReal

/-- Inner MVT step: `‖n^{−s} − u^{−s}‖ ≤ ‖s‖·n^{−σ−1}·(u−n)` on `[n, n+1]`. -/
lemma cpow_diff_bound (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hσ : 0 < s.re)
    {u : ℝ} (hu : u ∈ Set.Icc ((n:ℝ)) ((n:ℝ)+1)) :
    ‖((n:ℂ)) ^ (-s) - ((u:ℂ)) ^ (-s)‖ ≤ ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) * (u - (n:ℝ)) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hderiv : ∀ v ∈ Set.Icc ((n:ℝ)) ((n:ℝ)+1),
      HasDerivWithinAt (fun w : ℝ => ((w:ℂ)) ^ (-s))
        ((-s) * ((v:ℂ)) ^ (-s - 1)) (Set.Icc ((n:ℝ)) ((n:ℝ)+1)) v := by
    intro v hv
    have hv0 : (0:ℝ) < v := lt_of_lt_of_le hn0 hv.1
    exact (hasDerivAt_real_cpow_const hv0 (-s)).hasDerivWithinAt
  have hbound : ∀ v ∈ Set.Icc ((n:ℝ)) ((n:ℝ)+1),
      ‖(-s) * ((v:ℂ)) ^ (-s - 1)‖ ≤ ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) := by
    intro v hv
    have hv0 : (0:ℝ) < v := lt_of_lt_of_le hn0 hv.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hv0]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
    have hexp : (-s - 1).re = -s.re - 1 := by simp
    rw [hexp]
    exact Real.rpow_le_rpow_of_nonpos hn0 hv.1 (by linarith)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Icc _ _) (Set.left_mem_Icc.mpr (by linarith)) hu
  have habs : ‖u - (n:ℝ)‖ = u - (n:ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    linarith [hu.1]
  calc ‖((n:ℂ)) ^ (-s) - ((u:ℂ)) ^ (-s)‖
      = ‖((u:ℂ)) ^ (-s) - (((n:ℝ):ℂ)) ^ (-s)‖ := by
        rw [← norm_neg]
        congr 1
        push_cast
        ring
    _ ≤ ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) * ‖u - (n:ℝ)‖ := hmvt
    _ = ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) * (u - (n:ℝ)) := by rw [habs]

/-- **The complex Abel kernel bound** (SW brick S4a-4a): for `n ≥ 1` and `Re s > 0`,
    `‖(s−1)n^{−s} − (n^{1−s} − (n+1)^{1−s})‖ ≤ ‖s−1‖·‖s‖·n^{−Re s − 1}` — the
    summand of the ζ-truncation tail, now at COMPLEX `s`. -/
lemma abel_kernel_bound (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hσ : 0 < s.re) :
    ‖(s - 1) * ((n:ℂ)) ^ (-s) - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n+1 : ℕ):ℂ)) ^ ((1:ℂ) - s))‖
      ≤ ‖s - 1‖ * ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  -- h(u) := u^{1−s} + (s−1)·u·n^{−s}; K = h(n+1) − h(n)
  have hderiv : ∀ v ∈ Set.Icc ((n:ℝ)) ((n:ℝ)+1),
      HasDerivWithinAt (fun w : ℝ => ((w:ℂ)) ^ ((1:ℂ) - s) + (s-1) * ((w:ℂ)) * ((n:ℂ)) ^ (-s))
        ((s-1) * (((n:ℂ)) ^ (-s) - ((v:ℂ)) ^ (-s))) (Set.Icc ((n:ℝ)) ((n:ℝ)+1)) v := by
    intro v hv
    have hv0 : (0:ℝ) < v := lt_of_lt_of_le hn0 hv.1
    have h1 := hasDerivAt_real_cpow_const hv0 ((1:ℂ) - s)
    have h2 : HasDerivAt (fun w : ℝ => ((w:ℂ))) 1 v := by
      exact (hasDerivAt_id ((v:ℂ))).comp_ofReal
    have h3 : HasDerivAt (fun w : ℝ => (s-1) * ((w:ℂ)) * ((n:ℂ)) ^ (-s))
        ((s-1) * ((n:ℂ)) ^ (-s)) v := by
      have h4 := (h2.const_mul (s-1)).mul_const (((n:ℂ)) ^ (-s))
      have h5 : (s-1) * 1 * ((n:ℂ)) ^ (-s) = (s-1) * ((n:ℂ)) ^ (-s) := by ring
      rw [h5] at h4
      exact h4
    have h6 := h1.add h3
    have h7 : ((1:ℂ) - s) * ((v:ℂ)) ^ ((1:ℂ) - s - 1) + (s-1) * ((n:ℂ)) ^ (-s)
        = (s-1) * (((n:ℂ)) ^ (-s) - ((v:ℂ)) ^ (-s)) := by
      have h8 : (1:ℂ) - s - 1 = -s := by ring
      rw [h8]
      ring
    rw [h7] at h6
    exact h6.hasDerivWithinAt
  have hbound : ∀ v ∈ Set.Icc ((n:ℝ)) ((n:ℝ)+1),
      ‖(s-1) * (((n:ℂ)) ^ (-s) - ((v:ℂ)) ^ (-s))‖ ≤ ‖s-1‖ * (‖s‖ * ((n:ℝ)) ^ (-s.re - 1)) := by
    intro v hv
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc ‖((n:ℂ)) ^ (-s) - ((v:ℂ)) ^ (-s)‖
        ≤ ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) * (v - (n:ℝ)) := cpow_diff_bound n hn s hσ hv
      _ ≤ ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [hv.2]
      _ = ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) := mul_one _
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Icc _ _) (Set.left_mem_Icc.mpr (by linarith))
    (Set.right_mem_Icc.mpr (by linarith))
  have hcast : (((n+1 : ℕ):ℂ)) = (((((n:ℝ))+1 : ℝ)):ℂ) := by push_cast; ring
  have hK : (fun w : ℝ => ((w:ℂ)) ^ ((1:ℂ) - s) + (s-1) * ((w:ℂ)) * ((n:ℂ)) ^ (-s)) ((n:ℝ)+1)
      - (fun w : ℝ => ((w:ℂ)) ^ ((1:ℂ) - s) + (s-1) * ((w:ℂ)) * ((n:ℂ)) ^ (-s)) ((n:ℝ))
      = (s - 1) * ((n:ℂ)) ^ (-s) - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n+1 : ℕ):ℂ)) ^ ((1:ℂ) - s)) := by
    simp only
    rw [hcast]
    push_cast
    ring
  have hnorm1 : ‖((n:ℝ)) + 1 - ((n:ℝ))‖ = 1 := by
    rw [show ((n:ℝ)) + 1 - ((n:ℝ)) = 1 by ring, norm_one]
  calc ‖(s - 1) * ((n:ℂ)) ^ (-s) - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n+1 : ℕ):ℂ)) ^ ((1:ℂ) - s))‖
      = ‖(fun w : ℝ => ((w:ℂ)) ^ ((1:ℂ) - s) + (s-1) * ((w:ℂ)) * ((n:ℂ)) ^ (-s)) ((n:ℝ)+1)
        - (fun w : ℝ => ((w:ℂ)) ^ ((1:ℂ) - s) + (s-1) * ((w:ℂ)) * ((n:ℂ)) ^ (-s)) ((n:ℝ))‖ := by
        rw [hK]
    _ ≤ ‖s-1‖ * (‖s‖ * ((n:ℝ)) ^ (-s.re - 1)) * ‖((n:ℝ)) + 1 - ((n:ℝ))‖ := hmvt
    _ = ‖s - 1‖ * ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) := by
        rw [hnorm1, mul_one, mul_assoc]

section ZetaWindow
open Finset Filter Topology Metric

-- verbatim copies from SiegelTheorem.lean (telescope machinery)
lemma tsum_cpow_telescope (x : ℕ) (hx : 1 ≤ x) {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, (if n < x then 0 else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))
      = ((x:ℂ)) ^ ((1:ℂ) - s) := by
  have hs1 : (0:ℝ) < s.re - 1 := by linarith
  -- partial sums telescope
  have hpartial : ∀ z : ℕ, x ≤ z →
      ∑ n ∈ range z, (if n < x then 0
        else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))
      = ((x:ℂ)) ^ ((1:ℂ) - s) - ((z:ℂ)) ^ ((1:ℂ) - s) := by
    intro z
    induction z with
    | zero =>
      intro h0
      omega
    | succ m ihm =>
      intro hxm
      rcases Nat.lt_or_ge m x with hlt | hge
      · have hx' : x = m + 1 := by omega
        subst hx'
        have hall : ∀ n ∈ range (m + 1), (if n < m + 1 then (0:ℂ)
            else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))) = 0 := by
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero, sub_self]
      · rw [Finset.sum_range_succ, ihm hge, if_neg (by omega)]
        push_cast
        ring
  -- the real telescoping majorant
  have hC0 : (0:ℝ) ≤ ‖s - 1‖ / (s.re - 1) := div_nonneg (norm_nonneg _) hs1.le
  have hgmono : ∀ n : ℕ, 1 ≤ n →
      (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)) ≤ ((n : ℝ)) ^ (-(s.re - 1)) := by
    intro n hn1
    apply Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1)
      (by push_cast; linarith)
    linarith
  -- majorant partial sums telescope
  have hpartialR : ∀ z : ℕ, x ≤ z →
      ∑ n ∈ range z, (if n < x then 0
        else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
          - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1))))
      = (‖s - 1‖ / (s.re - 1)) * (((x : ℝ)) ^ (-(s.re - 1)) - ((z : ℝ)) ^ (-(s.re - 1))) := by
    intro z
    induction z with
    | zero =>
      intro h0
      omega
    | succ m ihm =>
      intro hxm
      rcases Nat.lt_or_ge m x with hlt | hge
      · have hx' : x = m + 1 := by omega
        subst hx'
        have hall : ∀ n ∈ range (m + 1), (if n < m + 1 then (0:ℝ)
            else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
              - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)))) = 0 := by
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero, sub_self, mul_zero]
      · rw [Finset.sum_range_succ, ihm hge, if_neg (by omega)]
        push_cast
        ring
  -- summability from the kernel bound at s − 1
  have hsummable : Summable (fun n : ℕ => (if n < x then (0:ℂ)
      else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => if n < x then 0
      else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
        - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1))))
    · -- majorant summable: nonneg terms with telescoping bounded partials
      apply summable_of_sum_range_le (c := ‖s - 1‖ / (s.re - 1))
      · intro n
        rcases Nat.lt_or_ge n x with h | h
        · rw [if_pos h]
        · rw [if_neg (by omega)]
          apply mul_nonneg hC0
          have := hgmono n (le_trans hx h)
          linarith
      · intro z
        rcases Nat.lt_or_ge z x with hz | hz
        · -- every index n < z ≤ x: all terms vanish
          have hall : ∀ n ∈ range z, (if n < x then (0:ℝ)
              else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
                - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)))) = 0 := by
            intro n hn
            rw [Finset.mem_range] at hn
            rw [if_pos (by omega)]
          rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero]
          exact hC0
        · rw [hpartialR z hz]
          have hx1 : ((x:ℝ)) ^ (-(s.re - 1)) ≤ 1 := by
            apply Real.rpow_le_one_of_one_le_of_nonpos
              (by exact_mod_cast hx)
            linarith
          have hz0 : (0:ℝ) ≤ ((z:ℝ)) ^ (-(s.re - 1)) :=
            Real.rpow_nonneg (Nat.cast_nonneg z) _
          calc (‖s - 1‖ / (s.re - 1)) * (((x : ℝ)) ^ (-(s.re - 1)) - ((z : ℝ)) ^ (-(s.re - 1)))
              ≤ (‖s - 1‖ / (s.re - 1)) * 1 := by
                apply mul_le_mul_of_nonneg_left _ hC0
                linarith
            _ = ‖s - 1‖ / (s.re - 1) := mul_one _
    · intro n
      rcases Nat.lt_or_ge n x with h | h
      · rw [if_pos h, if_pos h, norm_zero]
      · rw [if_neg (by omega), if_neg (by omega)]
        have hn1 : 1 ≤ n := le_trans hx h
        have hker := cpow_diff_kernel_bound n hn1 (s - 1) (by
          simp only [Complex.sub_re, Complex.one_re]
          linarith)
        have he1 : ((n:ℂ)) ^ ((1:ℂ) - s) = ((n:ℂ)) ^ (-(s - 1)) := by
          congr 1
          ring
        have he2 : (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s) = (((n + 1 : ℕ):ℂ)) ^ (-(s - 1)) := by
          congr 1
          ring
        rw [he1, he2]
        have hre : (s - 1).re = s.re - 1 := by
          simp [Complex.sub_re]
        rw [hre] at hker
        exact hker
  -- conclude: tsum = limit of partials = x^{1−s}
  have hrange := hsummable.hasSum.tendsto_sum_nat
  have hlim : Tendsto (fun z : ℕ => ((x:ℂ)) ^ ((1:ℂ) - s) - ((z:ℂ)) ^ ((1:ℂ) - s))
      atTop (nhds (((x:ℂ)) ^ ((1:ℂ) - s))) := by
    have hz0 : Tendsto (fun z : ℕ => ((z:ℂ)) ^ ((1:ℂ) - s)) atTop (nhds 0) := by
      have h1s : ((1:ℂ) - s) ≠ 0 := by
        intro hc
        have := congrArg Complex.re hc
        simp at this
        linarith
      have hbnd : ∀ z : ℕ, ‖((z:ℂ)) ^ ((1:ℂ) - s)‖ ≤ ((z:ℝ)) ^ (1 - s.re) := by
        intro z
        rcases Nat.eq_zero_or_pos z with rfl | hzpos
        · simp only [Nat.cast_zero]
          rw [Complex.zero_cpow h1s, norm_zero,
            Real.zero_rpow (by linarith : (1:ℝ) - s.re ≠ 0)]
        · rw [Complex.norm_natCast_cpow_of_pos hzpos]
          have hre1 : ((1:ℂ) - s).re = 1 - s.re := by simp [Complex.sub_re]
          rw [hre1]
      have hg0 : Tendsto (fun z : ℕ => ((z:ℝ)) ^ (1 - s.re)) atTop (nhds 0) := by
        have h := tendsto_rpow_neg_atTop (show (0:ℝ) < s.re - 1 by linarith)
        have hcomp := h.comp tendsto_natCast_atTop_atTop
        simpa [Function.comp_def, neg_sub] using hcomp
      exact squeeze_zero_norm hbnd hg0
    have := (tendsto_const_nhds (x := ((x:ℂ)) ^ ((1:ℂ) - s))).sub hz0
    simpa using this
  have heq : (fun z : ℕ => ∑ n ∈ range z, (if n < x then 0
      else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))
      =ᶠ[atTop] (fun z : ℕ => ((x:ℂ)) ^ ((1:ℂ) - s) - ((z:ℂ)) ^ ((1:ℂ) - s)) := by
    filter_upwards [eventually_ge_atTop x] with z hz
    exact hpartial z hz
  have hrange' : Tendsto (fun z : ℕ => ∑ n ∈ range z, (if n < x then 0
      else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))
      atTop (nhds (((x:ℂ)) ^ ((1:ℂ) - s))) :=
    (Filter.tendsto_congr' heq).mpr hlim
  exact tendsto_nhds_unique hrange hrange'


lemma tsum_cpow_telescope_summable (x : ℕ) (hx : 1 ≤ x) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (if n < x then (0:ℂ)
      else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))) := by
  have hs1 : (0:ℝ) < s.re - 1 := by linarith
  have hC0 : (0:ℝ) ≤ ‖s - 1‖ / (s.re - 1) := div_nonneg (norm_nonneg _) hs1.le
  have hgmono : ∀ n : ℕ, 1 ≤ n →
      (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)) ≤ ((n : ℝ)) ^ (-(s.re - 1)) := by
    intro n hn1
    apply Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1)
      (by push_cast; linarith)
    linarith
  have hpartialR : ∀ z : ℕ, x ≤ z →
      ∑ n ∈ range z, (if n < x then 0
        else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
          - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1))))
      = (‖s - 1‖ / (s.re - 1)) * (((x : ℝ)) ^ (-(s.re - 1)) - ((z : ℝ)) ^ (-(s.re - 1))) := by
    intro z
    induction z with
    | zero =>
      intro h0
      omega
    | succ m ihm =>
      intro hxm
      rcases Nat.lt_or_ge m x with hlt | hge
      · have hx' : x = m + 1 := by omega
        subst hx'
        have hall : ∀ n ∈ range (m + 1), (if n < m + 1 then (0:ℝ)
            else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
              - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)))) = 0 := by
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero, sub_self, mul_zero]
      · rw [Finset.sum_range_succ, ihm hge, if_neg (by omega)]
        push_cast
        ring
  apply Summable.of_norm_bounded (g := fun n : ℕ => if n < x then 0
    else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
      - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1))))
  · apply summable_of_sum_range_le (c := ‖s - 1‖ / (s.re - 1))
    · intro n
      rcases Nat.lt_or_ge n x with h | h
      · rw [if_pos h]
      · rw [if_neg (by omega)]
        apply mul_nonneg hC0
        have := hgmono n (le_trans hx h)
        linarith
    · intro z
      rcases Nat.lt_or_ge z x with hz | hz
      · have hall : ∀ n ∈ range z, (if n < x then (0:ℝ)
            else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
              - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)))) = 0 := by
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos (by omega)]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero]
        exact hC0
      · rw [hpartialR z hz]
        have hx1 : ((x:ℝ)) ^ (-(s.re - 1)) ≤ 1 := by
          apply Real.rpow_le_one_of_one_le_of_nonpos
            (by exact_mod_cast hx)
          linarith
        have hz0 : (0:ℝ) ≤ ((z:ℝ)) ^ (-(s.re - 1)) :=
          Real.rpow_nonneg (Nat.cast_nonneg z) _
        calc (‖s - 1‖ / (s.re - 1)) * (((x : ℝ)) ^ (-(s.re - 1)) - ((z : ℝ)) ^ (-(s.re - 1)))
            ≤ (‖s - 1‖ / (s.re - 1)) * 1 := by
              apply mul_le_mul_of_nonneg_left _ hC0
              linarith
          _ = ‖s - 1‖ / (s.re - 1) := mul_one _
  · intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, if_pos h, norm_zero]
    · rw [if_neg (by omega), if_neg (by omega)]
      have hn1 : 1 ≤ n := le_trans hx h
      have hker := cpow_diff_kernel_bound n hn1 (s - 1) (by
        simp only [Complex.sub_re, Complex.one_re]
        linarith)
      have he1 : ((n:ℂ)) ^ ((1:ℂ) - s) = ((n:ℂ)) ^ (-(s - 1)) := by
        congr 1
        ring
      have he2 : (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s) = (((n + 1 : ℕ):ℂ)) ^ (-(s - 1)) := by
        congr 1
        ring
      rw [he1, he2]
      have hre : (s - 1).re = s.re - 1 := by
        simp [Complex.sub_re]
      rw [hre] at hker
      exact hker

/-- **The completed-zeta ball bound** (SW brick S4a-4b): one absolute `C₀` with
    `‖(z−1)ζ(z)‖ ≤ C₀·R²` (as `LFunctionTrivChar₁ 1`, pole removed) on every ball
    `‖z‖ < R`, `Re z > 19/20` — via the complex Abel truncation tail. -/
theorem completed_zeta_ball_bound :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, 19/20 < z.re → ‖z‖ < R →
      ‖DirichletCharacter.LFunctionTrivChar₁ 1 z‖ ≤ C₀ * R^2 := by
  have hmaj : Summable (fun k : ℕ => (((k+1 : ℕ)):ℝ) ^ (-(39:ℝ)/20)) := by
    have h1 : Summable (fun n : ℕ => ((n:ℝ)) ^ (-(39:ℝ)/20)) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    exact h1.comp_injective (add_left_injective 1)
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑' k : ℕ, (((k+1 : ℕ)):ℝ) ^ (-(39:ℝ)/20) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact tsum_nonneg (fun k => Real.rpow_nonneg (by positivity) _)
  refine ⟨1 + 3*S, by linarith, ?_⟩
  intro R hR z hzre hznorm
  obtain ⟨T, hTdef⟩ : ∃ T : ℂ → ℂ, T = fun w => ∑' k : ℕ,
      ((w - 1) * ((((k+1 : ℕ)):ℂ)) ^ (-w)
        - (((((k+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w) - ((((k+1+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w))) := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : Set ℂ, U = {w : ℂ | 19/20 < w.re} ∩ Metric.ball 0 R := ⟨_, rfl⟩
  have hUopen : IsOpen U := by
    rw [hUdef]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hterm : ∀ (k : ℕ) (w : ℂ), w ∈ U →
      ‖(w - 1) * ((((k+1 : ℕ)):ℂ)) ^ (-w)
        - (((((k+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w) - ((((k+1+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w))‖
        ≤ (R+1)*R * (((k+1 : ℕ)):ℝ) ^ (-(39:ℝ)/20) := by
    intro k w hw
    rw [hUdef] at hw
    obtain ⟨hw1, hw2⟩ := hw
    rw [Set.mem_setOf_eq] at hw1
    rw [Metric.mem_ball, dist_zero_right] at hw2
    have h1 := abel_kernel_bound (k+1) (by omega) w (by linarith)
    have h2 : ‖w - 1‖ ≤ R + 1 := by
      calc ‖w - 1‖ ≤ ‖w‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ ≤ R + 1 := by rw [norm_one]; linarith
    have h3 : (((k+1 : ℕ)):ℝ) ^ (-w.re - 1) ≤ (((k+1 : ℕ)):ℝ) ^ (-(39:ℝ)/20) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
      · linarith
    have h4 := mul_le_mul (mul_le_mul h2 hw2.le (norm_nonneg w) (by linarith)) h3
      (Real.rpow_nonneg (by positivity) _) (by positivity)
    linarith [h1, h4]
  have hTnorm : ∀ w ∈ U, ‖T w‖ ≤ (R+1)*R*S := by
    intro w hw
    have hnsum : Summable (fun k : ℕ => ‖(w - 1) * ((((k+1 : ℕ)):ℂ)) ^ (-w)
        - (((((k+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w) - ((((k+1+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w))‖) :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hterm k w hw)
        (hmaj.mul_left ((R+1)*R))
    simp only [hTdef]
    calc ‖∑' k : ℕ, ((w - 1) * ((((k+1 : ℕ)):ℂ)) ^ (-w)
          - (((((k+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w) - ((((k+1+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w)))‖
        ≤ ∑' k : ℕ, ‖(w - 1) * ((((k+1 : ℕ)):ℂ)) ^ (-w)
          - (((((k+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w) - ((((k+1+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w))‖ :=
          norm_tsum_le_tsum_norm hnsum
      _ ≤ ∑' k : ℕ, (R+1)*R * (((k+1 : ℕ)):ℝ) ^ (-(39:ℝ)/20) :=
          hnsum.tsum_le_tsum (fun k => hterm k w hw) (hmaj.mul_left ((R+1)*R))
      _ = (R+1)*R*S := by
          rw [hSdef, tsum_mul_left]
  have hTdiff : DifferentiableOn ℂ T U := by
    rw [hTdef]
    apply differentiableOn_tsum_of_summable_norm (hmaj.mul_left ((R+1)*R)) _ hUopen
      (fun k w hw => hterm k w hw)
    intro k
    apply Differentiable.differentiableOn
    have hb1 : ((((k+1 : ℕ)):ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hb2 : ((((k+1+1 : ℕ)):ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact ((differentiable_id.sub_const 1).mul
        (differentiable_id.neg.const_cpow (Or.inl hb1))).sub
      ((((differentiable_const (1:ℂ)).sub differentiable_id).const_cpow (Or.inl hb1)).sub
        (((differentiable_const (1:ℂ)).sub differentiable_id).const_cpow (Or.inl hb2)))
  have hidentity : ∀ s : ℂ, 1 < s.re →
      DirichletCharacter.LFunctionTrivChar₁ 1 s = 1 + T s := by
    intro s hs1
    have hsne : s ≠ 1 := fun h => by
      rw [h, Complex.one_re] at hs1
      exact lt_irrefl _ hs1
    have hs0 : s ≠ 0 := fun h => by
      rw [h, Complex.zero_re] at hs1
      linarith
    have hL : DirichletCharacter.LFunctionTrivChar₁ 1 s = (s - 1) * riemannZeta s := by
      rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hsne,
        DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hsne,
        Nat.primeFactors_one, Finset.prod_empty, one_mul]
    have hζ := zeta_eq_tsum_one_div_nat_cpow hs1
    have hA : Summable (fun n : ℕ => (1:ℂ)/((n:ℂ))^s) :=
      Complex.summable_one_div_nat_cpow.mpr hs1
    have hB := tsum_cpow_telescope_summable 1 (le_refl 1) hs1
    have hAeq : (fun n : ℕ => (if n < 1 then (0:ℂ) else (s - 1) * ((n:ℂ)) ^ (-s)))
        = fun n : ℕ => (s - 1) * ((1:ℂ)/((n:ℂ))^s) := by
      funext n
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        simp [Complex.zero_cpow hs0]
      · rw [if_neg (by omega), Complex.cpow_neg, one_div]
    have hAsum : Summable (fun n : ℕ =>
        (if n < 1 then (0:ℂ) else (s - 1) * ((n:ℂ)) ^ (-s))) := by
      rw [hAeq]
      exact hA.mul_left _
    have hGeq : (fun n : ℕ =>
        (if n < 1 then (0:ℂ) else ((s - 1) * ((n:ℂ)) ^ (-s)
          - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n+1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))))
        = fun n : ℕ => ((if n < 1 then (0:ℂ) else (s - 1) * ((n:ℂ)) ^ (-s))
          - (if n < 1 then (0:ℂ)
            else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n+1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))) := by
      funext n
      split_ifs
      · ring
      · ring
    have hGsum : Summable (fun n : ℕ =>
        (if n < 1 then (0:ℂ) else ((s - 1) * ((n:ℂ)) ^ (-s)
          - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n+1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) := by
      rw [hGeq]
      exact hAsum.sub hB
    have hGtsum : ∑' n : ℕ, (if n < 1 then (0:ℂ) else ((s - 1) * ((n:ℂ)) ^ (-s)
          - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n+1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))
        = (s - 1) * riemannZeta s - 1 := by
      rw [hGeq, hAsum.tsum_sub hB, tsum_cpow_telescope 1 (le_refl 1) hs1, hAeq,
        tsum_mul_left, ← hζ]
      norm_num
    have hshift := hGsum.tsum_eq_zero_add
    have hTG : T s = ∑' k : ℕ, (if k+1 < 1 then (0:ℂ)
        else ((s - 1) * (((k+1 : ℕ):ℂ)) ^ (-s)
          - ((((k+1 : ℕ):ℂ)) ^ ((1:ℂ) - s) - ((((k+1)+1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))) := by
      simp only [hTdef]
      first
      | rfl
      | congr 1
      | (congr 1
         funext k
         split_ifs with h
         · exact absurd h (by omega)
         · rfl)
    rw [hL, hTG]
    rw [if_pos (by omega), zero_add] at hshift
    rw [← hshift, hGtsum]
    ring
  have hUconv : Convex ℝ U := by
    rw [hUdef]
    exact (convex_halfSpace_re_gt _).inter (convex_ball 0 R)
  have hg1diff : Differentiable ℂ (DirichletCharacter.LFunctionTrivChar₁ 1) :=
    DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
  have h1Tdiff : DifferentiableOn ℂ (fun w => 1 + T w) U :=
    (differentiableOn_const 1).add hTdiff
  have hz₀U : ((3/2 : ℝ) : ℂ) ∈ U := by
    rw [hUdef]
    constructor
    · rw [Set.mem_setOf_eq, Complex.ofReal_re]
      norm_num
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/2)]
      linarith
  have hVopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hz₀V : ((3/2 : ℝ) : ℂ) ∈ {w : ℂ | 1 < w.re} := by
    rw [Set.mem_setOf_eq, Complex.ofReal_re]
    norm_num
  have hseed : (fun w => 1 + T w) =ᶠ[nhds ((3/2 : ℝ) : ℂ)]
      (DirichletCharacter.LFunctionTrivChar₁ 1) := by
    filter_upwards [hVopen.mem_nhds hz₀V] with w hw
    exact (hidentity w hw).symm
  have heq : Set.EqOn (fun w => 1 + T w) (DirichletCharacter.LFunctionTrivChar₁ 1) U :=
    (h1Tdiff.analyticOnNhd hUopen).eqOn_of_preconnected_of_eventuallyEq
      ((hg1diff.differentiableOn).analyticOnNhd hUopen)
      hUconv.isPreconnected hz₀U hseed
  have hzU : z ∈ U := by
    rw [hUdef]
    refine ⟨hzre, ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact hznorm
  have hval := (heq hzU).symm
  have hfinal : ‖DirichletCharacter.LFunctionTrivChar₁ 1 z‖ ≤ 1 + (R+1)*R*S := by
    rw [hval]
    calc ‖1 + T z‖ ≤ ‖(1:ℂ)‖ + ‖T z‖ := norm_add_le _ _
      _ ≤ 1 + (R+1)*R*S := by
          rw [norm_one]
          linarith [hTnorm z hzU]
  have h6 : (R+1)*R ≤ 3*R^2 := by nlinarith
  have h7 : (R+1)*R*S ≤ 3*R^2*S := mul_le_mul_of_nonneg_right h6 hS0
  have h8 : (1:ℝ) ≤ R^2 := by nlinarith
  calc ‖DirichletCharacter.LFunctionTrivChar₁ 1 z‖ ≤ 1 + (R+1)*R*S := hfinal
    _ ≤ R^2 + 3*S*R^2 := by nlinarith [h7, h8]
    _ = (1 + 3*S) * R^2 := by ring

end ZetaWindow

section TrivCharHeight
open Metric

/-- Norm of a product over prime factors, each factor of norm ≤ 2, is at most `N`. -/
lemma primeFactors_prod_norm_le (N : ℕ) [NeZero N] (g : ℕ → ℂ)
    (hg : ∀ p ∈ N.primeFactors, ‖g p‖ ≤ 2) :
    ‖∏ p ∈ N.primeFactors, g p‖ ≤ (N:ℝ) := by
  calc ‖∏ p ∈ N.primeFactors, g p‖ ≤ ∏ p ∈ N.primeFactors, ‖g p‖ :=
      (norm_prod _ _).le
    _ ≤ ∏ p ∈ N.primeFactors, (2:ℝ) := by
        apply Finset.prod_le_prod (fun p _ => norm_nonneg _) hg
    _ = (2:ℝ) ^ N.primeFactors.card := by
        rw [Finset.prod_const]
    _ ≤ (N:ℝ) := by
        have h1 : (2:ℕ) ^ N.primeFactors.card ≤ ∏ p ∈ N.primeFactors, p :=
          Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
        have h2 : ∏ p ∈ N.primeFactors, p ≤ N :=
          Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) (Nat.prod_primeFactors_dvd N)
        have h3 : (2:ℕ) ^ N.primeFactors.card ≤ N := le_trans h1 h2
        calc (2:ℝ) ^ N.primeFactors.card = (((2:ℕ) ^ N.primeFactors.card : ℕ) : ℝ) := by
              push_cast
              ring
          _ ≤ (N:ℝ) := by exact_mod_cast h3

open scoped LSeries.notation ArithmeticFunction in
/-- **The trivial-character Landau bound at height** (SW brick S4a-4c): one absolute
    `C` with, for every modulus and `σ ∈ (1,2]`, every height `t`,
    `Re L(χ⁰Λ, σ+it) ≤ (σ−1)/((σ−1)²+t²) + C(log(N(|t|+3)/(σ−1)) + 1)` — the DAMPED
    pole: Landau on the completed `(s−1)L(χ⁰,s)` (no pole, fixed radius), every zero
    term dropped by positivity. -/
theorem trivchar_height_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) [NeZero N], ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
      (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) ((σ:ℂ) + t*I)).re
        ≤ (σ-1)/((σ-1)^2 + t^2) + C * (Real.log ((N:ℝ)*(|t|+3)/(σ-1)) + 1) := by
  obtain ⟨C₀, hC₀1, hC₀⟩ := completed_zeta_ball_bound
  have hlogC₀ : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀1
  refine ⟨1000*(Real.log C₀ + 4), by linarith, ?_⟩
  intro N _ σ t hσ1 hσ2
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  set c : ℂ := (σ:ℂ) + t*I with hcdef
  have hcre : c.re = σ := by rw [hcdef]; simp
  have hcim : c.im = t := by rw [hcdef]; simp
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hcre
    linarith
  have hcnorm : ‖c‖ ≤ σ + |t| := by
    rw [hcdef]
    calc ‖(σ:ℂ) + t*I‖ ≤ ‖(σ:ℂ)‖ + ‖(t:ℂ)*I‖ := norm_add_le _ _
      _ = |σ| + |t| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
          simp [Real.norm_eq_abs]
      _ = σ + |t| := by rw [abs_of_pos (by linarith)]
  -- the ball bound for the completed function
  have hfb : ∀ z ∈ ball c (1/50),
      ‖DirichletCharacter.LFunctionTrivChar₁ N z‖ ≤ (N:ℝ) * (C₀ * (|t|+3)^2) := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hzre : 19/20 < z.re := by
      have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
      have h2 : |z.re - c.re| < 1/50 := by
        rw [← Complex.sub_re]
        exact lt_of_le_of_lt h1 hz
      have h3 := (abs_lt.mp h2).1
      rw [hcre] at h3
      linarith
    have hznorm : ‖z‖ < |t| + 3 := by
      calc ‖z‖ = ‖c + (z - c)‖ := by ring_nf
        _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
        _ < (σ + |t|) + 1/50 := by
            apply add_lt_add_of_le_of_lt hcnorm hz
        _ ≤ |t| + 3 := by linarith
    have hR3 : (2:ℝ) ≤ |t| + 3 := by
      have := abs_nonneg t
      linarith
    have hzeta := hC₀ (|t|+3) hR3 z hzre hznorm
    by_cases hz1 : z = 1
    · -- at the removed pole: the update value is the finite Euler product
      subst hz1
      rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_self]
      have hprod : ‖∏ p ∈ N.primeFactors, (1 - ((p:ℂ))⁻¹)‖ ≤ (N:ℝ) := by
        apply primeFactors_prod_norm_le
        intro p hp
        have hp2 : (2:ℝ) ≤ (p:ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        calc ‖1 - ((p:ℂ))⁻¹‖ ≤ ‖(1:ℂ)‖ + ‖((p:ℂ))⁻¹‖ := norm_sub_le _ _
          _ = 1 + ((p:ℝ))⁻¹ := by
              rw [norm_one, norm_inv]
              congr 1
              rw [show ((p:ℂ)) = (((p:ℝ)):ℂ) by push_cast; ring, Complex.norm_real,
                Real.norm_eq_abs, abs_of_pos (by linarith)]
          _ ≤ 2 := by
              have : ((p:ℝ))⁻¹ ≤ 1 := by
                rw [inv_le_one_iff₀]
                right
                linarith
              linarith
      have hbig : (1:ℝ) ≤ C₀ * (|t|+3)^2 := by
        have h9 : (9:ℝ) ≤ (|t|+3)^2 := by nlinarith [abs_nonneg t]
        nlinarith [hC₀1]
      calc ‖∏ p ∈ N.primeFactors, (1 - ((p:ℂ))⁻¹)‖ ≤ (N:ℝ) := hprod
        _ ≤ (N:ℝ) * (C₀ * (|t|+3)^2) := by nlinarith [hN1r, hbig]
    · -- away from 1: factor through the level-1 completed function
      have hfactor : DirichletCharacter.LFunctionTrivChar₁ N z
          = (∏ p ∈ N.primeFactors, (1 - ((p:ℂ)) ^ (-z)))
            * DirichletCharacter.LFunctionTrivChar₁ 1 z := by
        rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1,
          DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1,
          DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hz1,
          DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hz1,
          Nat.primeFactors_one, Finset.prod_empty, one_mul]
        ring
      rw [hfactor, norm_mul]
      have hzre0 : (0:ℝ) < z.re := by linarith
      have hprod : ‖∏ p ∈ N.primeFactors, (1 - ((p:ℂ)) ^ (-z))‖ ≤ (N:ℝ) := by
        apply primeFactors_prod_norm_le
        intro p hp
        have hp2 : (2:ℝ) ≤ (p:ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        have hp0 : (0:ℝ) < (p:ℝ) := by linarith
        calc ‖1 - ((p:ℂ)) ^ (-z)‖ ≤ ‖(1:ℂ)‖ + ‖((p:ℂ)) ^ (-z)‖ := norm_sub_le _ _
          _ = 1 + ((p:ℝ)) ^ (-z.re) := by
              rw [norm_one, show ((p:ℂ)) = (((p:ℝ)):ℂ) by push_cast; ring,
                Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.neg_re]
          _ ≤ 2 := by
              have h1 : ((p:ℝ)) ^ (-z.re) ≤ 1 :=
                Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
              linarith
      exact mul_le_mul hprod hzeta (norm_nonneg _) (by linarith)
  -- the anchor
  have hcre1 : 1 < c.re := by
    rw [hcre]
    exact hσ1
  have hLne := LFunction_anchor_quantitative N 1 c hcre1
  rw [hcre] at hLne
  have hLpos : (0:ℝ) < (σ - 1)/σ := by
    apply div_pos <;> linarith
  have hml : (σ-1)^2/2 ≤ ‖DirichletCharacter.LFunctionTrivChar₁ N c‖ := by
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hc1]
    have h1 : σ - 1 ≤ ‖c - 1‖ := by
      calc σ - 1 = (c - 1).re := by rw [Complex.sub_re, hcre, Complex.one_re]
        _ ≤ |(c - 1).re| := le_abs_self _
        _ ≤ ‖c - 1‖ := Complex.abs_re_le_norm _
    have h2 : (σ - 1)/σ ≤ ‖DirichletCharacter.LFunctionTrivChar N c‖ := hLne
    have h3 : (σ-1)/2 ≤ (σ-1)/σ := by
      apply div_le_div_of_nonneg_left (by linarith) (by linarith)
      linarith
    calc (σ-1)^2/2 = (σ-1) * ((σ-1)/2) := by ring
      _ ≤ ‖c - 1‖ * ‖DirichletCharacter.LFunctionTrivChar N c‖ := by
          apply mul_le_mul h1 (le_trans h3 h2) (by positivity) (norm_nonneg _)
      _ = ‖(c - 1) * DirichletCharacter.LFunctionTrivChar N c‖ := (norm_mul _ _).symm
  have hml0 : (0:ℝ) < (σ-1)^2/2 := by positivity
  -- Landau on the completed function
  obtain ⟨S, m, hSz, hm, hcomp, hbound⟩ := landau_log_deriv
    (DirichletCharacter.LFunctionTrivChar₁ N) c (1/50) (1/125)
    ((N:ℝ) * (C₀ * (|t|+3)^2)) ((σ-1)^2/2) (by norm_num) (by norm_num)
    ((DirichletCharacter.differentiable_LFunctionTrivChar₁ N).differentiableOn) hfb hml0 hml
  have hfc0 : DirichletCharacter.LFunctionTrivChar₁ N c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hml
    nlinarith [hml0]
  have hzS : ∀ ρ ∈ S, c ≠ ρ := by
    intro ρ hρ h
    rw [h] at hfc0
    exact hfc0 (hSz ρ hρ).2
  have hb := hbound c (mem_ball_self (by norm_num)) hzS
  -- every zero term has nonnegative real part
  have hreS : ∀ ρ ∈ S, 0 ≤ ((m ρ : ℂ) / (c - ρ)).re := by
    intro ρ hρ
    have hρz := (hSz ρ hρ).2
    have hρ1 : ρ ≠ 1 := by
      intro h
      rw [h] at hρz
      exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero N hρz
    have hLρ : DirichletCharacter.LFunctionTrivChar N ρ = 0 := by
      rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hρ1] at hρz
      rcases mul_eq_zero.mp hρz with h | h
      · exact absurd (sub_eq_zero.mp h) hρ1
      · exact h
    have hρre : ρ.re < 1 := by
      by_contra hre
      push_neg at hre
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re
        (1 : DirichletCharacter ℂ N) (Or.inr hρ1) hre hLρ
    rw [div_eq_mul_inv, show ((m ρ : ℕ) : ℂ) = (((m ρ : ℕ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_ofReal_mul, Complex.inv_re]
    apply mul_nonneg (Nat.cast_nonneg _)
    apply div_nonneg _ (Complex.normSq_nonneg _)
    rw [Complex.sub_re, hcre]
    linarith
  -- the log-derivative identity at the center
  have hLcne : DirichletCharacter.LFunctionTrivChar N c ≠ 0 := by
    intro h
    have h' : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) c = 0 := h
    rw [h', norm_zero] at hLne
    nlinarith [hLpos]
  have hld : logDeriv (DirichletCharacter.LFunctionTrivChar₁ N) c
      = 1/(c-1) + logDeriv (DirichletCharacter.LFunctionTrivChar N) c := by
    rw [logDeriv_apply, logDeriv_apply,
      DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one N hc1,
      DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hc1]
    have hcne : c - 1 ≠ 0 := sub_ne_zero_of_ne hc1
    field_simp
    ring
  -- the twist identity
  have hident : LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) c
      = - logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)) c := by
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq _ hcre1,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ hcre1,
      ← DirichletCharacter.LFunction_eq_LSeries _ hcre1, neg_div, ← logDeriv_apply]
  -- assemble
  have hrediff : -(8 * (Real.log ((N:ℝ) * (C₀ * (|t|+3)^2) / ((σ-1)^2/2)) + 1) / (1/125))
      ≤ (logDeriv (DirichletCharacter.LFunctionTrivChar₁ N) c
          - ∑ ρ ∈ S, (m ρ : ℂ) / (c - ρ)).re := by
    have habs := (Complex.abs_re_le_norm _).trans hb
    linarith [(abs_le.mp habs).1]
  have hsum0 : 0 ≤ (∑ ρ ∈ S, (m ρ : ℂ) / (c - ρ)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_nonneg hreS
  have hpole : ((1:ℂ)/(c-1)).re = (σ-1)/((σ-1)^2 + t^2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      hcre, hcim, Complex.one_re, Complex.one_im]
    ring
  -- the log arithmetic
  have hA1 : (3:ℝ) ≤ (N:ℝ)*(|t|+3)/(σ-1) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < σ-1)]
    have := abs_nonneg t
    nlinarith
  have hA0 : (0:ℝ) < (N:ℝ)*(|t|+3)/(σ-1) := by linarith
  have hlogA0 : (1:ℝ) ≤ Real.log ((N:ℝ)*(|t|+3)/(σ-1)) := by
    calc (1:ℝ) ≤ Real.log 3 := by
          rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
          apply Real.log_le_log (Real.exp_pos 1)
          have := Real.exp_one_lt_d9
          linarith
      _ ≤ Real.log ((N:ℝ)*(|t|+3)/(σ-1)) := Real.log_le_log (by norm_num) hA1
  have hMbml : (N:ℝ) * (C₀ * (|t|+3)^2) / ((σ-1)^2/2)
      ≤ 2*C₀ * ((N:ℝ)*(|t|+3)/(σ-1))^2 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (σ-1)^2/2)]
    have hexp : 2*C₀ * ((N:ℝ)*(|t|+3)/(σ-1))^2 * ((σ-1)^2/2)
        = C₀ * (N:ℝ)^2 * (|t|+3)^2 * (((σ-1)/(σ-1))^2) := by
      field_simp
    rw [hexp, div_self (by linarith : σ-1 ≠ 0)]
    have h10 : (N:ℝ) ≤ (N:ℝ)^2 := by nlinarith [hN1r]
    have h11 : (0:ℝ) ≤ C₀ * (|t|+3)^2 := by positivity
    nlinarith [h10, h11]
  have hlogMbml : Real.log ((N:ℝ) * (C₀ * (|t|+3)^2) / ((σ-1)^2/2))
      ≤ Real.log 2 + Real.log C₀ + 2 * Real.log ((N:ℝ)*(|t|+3)/(σ-1)) := by
    calc Real.log ((N:ℝ) * (C₀ * (|t|+3)^2) / ((σ-1)^2/2))
        ≤ Real.log (2*C₀ * ((N:ℝ)*(|t|+3)/(σ-1))^2) := by
          apply Real.log_le_log _ hMbml
          have hN0 : (0:ℝ) < (N:ℝ) := by linarith
          exact div_pos (mul_pos hN0 (by positivity)) (by positivity)
      _ = Real.log (2*C₀) + Real.log (((N:ℝ)*(|t|+3)/(σ-1))^2) := by
          rw [Real.log_mul (by nlinarith [hC₀1]) (by positivity)]
      _ = Real.log 2 + Real.log C₀ + 2 * Real.log ((N:ℝ)*(|t|+3)/(σ-1)) := by
          rw [Real.log_mul (by norm_num) (by linarith), Real.log_pow]
          push_cast
          ring
  -- final chain
  have hcore : (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) c).re
      ≤ ((1:ℂ)/(c-1)).re
        + 1000 * (Real.log ((N:ℝ) * (C₀ * (|t|+3)^2) / ((σ-1)^2/2)) + 1) := by
    rw [hident]
    have h1 : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)) c
        = logDeriv (DirichletCharacter.LFunctionTrivChar₁ N) c - 1/(c-1) := by
      have h2 : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)) c
          = logDeriv (DirichletCharacter.LFunctionTrivChar N) c := rfl
      rw [h2, hld]
      ring
    rw [h1, Complex.neg_re, Complex.sub_re]
    have h3 := hrediff
    rw [Complex.sub_re] at h3
    have h4 : 8 * (Real.log ((N:ℝ) * (C₀ * (|t|+3)^2) / ((σ-1)^2/2)) + 1) / (1/125)
        = 1000 * (Real.log ((N:ℝ) * (C₀ * (|t|+3)^2) / ((σ-1)^2/2)) + 1) := by
      ring
    rw [h4] at h3
    linarith [hsum0, h3]
  rw [hpole] at hcore
  have hfinal : 1000 * (Real.log ((N:ℝ) * (C₀ * (|t|+3)^2) / ((σ-1)^2/2)) + 1)
      ≤ 1000*(Real.log C₀ + 4) * (Real.log ((N:ℝ)*(|t|+3)/(σ-1)) + 1) := by
    have hlog2 : Real.log 2 ≤ 1 := by
      rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
      apply Real.log_le_log (by norm_num)
      have := Real.exp_one_gt_d9
      linarith
    have hL := hlogA0
    nlinarith [hlogMbml, hlogC₀, hL, hlog2]
  linarith [hcore, hfinal]

end TrivCharHeight

section Quad341
open Metric
set_option maxHeartbeats 2000000

open scoped LSeries.notation ArithmeticFunction in
/-- **The quadratic 3-4-1 gap away from the real axis** (SW brick S4a-5): for any
    height-threshold parameter `D ≥ 1` there is `C ≥ 1` with: every zero `β+iγ` of
    every quadratic nontrivial `χ` mod `N` with `1 ≤ |γ|·D·L₀` satisfies
    `β ≤ 1 − 1/(C·L₀)` — the classical de la Vallée-Poussin argument, with the
    trivial-character term DAMPED by the height (`trivchar_height_bound`). -/
theorem quad_341_gap (D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ ^ 2 = 1 → ∀ β γ : ℝ,
      DirichletCharacter.LFunction χ ((β:ℂ) + γ*Complex.I) = 0 →
      1 ≤ |γ| * (D * (Real.log ((N:ℝ)*(4*|γ|+7)) + 20)) →
      β ≤ 1 - 1/(C * (Real.log ((N:ℝ)*(4*|γ|+7)) + 20)) := by
  obtain ⟨KP, hKP⟩ := twist_re_le_uniform
  obtain ⟨KP', hKP'def⟩ : ∃ K' : ℝ, K' = max KP 0 := ⟨_, rfl⟩
  have hKP'0 : 0 ≤ KP' := by rw [hKP'def]; exact le_max_right _ _
  have hKPle : KP ≤ KP' := by rw [hKP'def]; exact le_max_left _ _
  obtain ⟨C₄, hC₄1, hC₄⟩ := trivchar_height_bound
  obtain ⟨C₉, hC₉def⟩ : ∃ c : ℝ, c = 3*KP' + 320 + 2*C₄ := ⟨_, rfl⟩
  have hC₉1 : 1 ≤ C₉ := by rw [hC₉def]; linarith
  obtain ⟨W, hWdef⟩ : ∃ w : ℝ, w = 4*D*(6400*C₉^2 + 1600*C₉ + 4) := ⟨_, rfl⟩
  have hW16D : 16*D ≤ W := by rw [hWdef]; nlinarith [hC₉1, hD]
  have hW6400 : 6400*C₉^2 ≤ W := by rw [hWdef]; nlinarith [hC₉1, hD]
  have hW2400 : 2400*C₉ ≤ W := by rw [hWdef]; nlinarith [hC₉1, hD]
  have hW1 : 1 ≤ W := by nlinarith [hW2400, hC₉1]
  have hW0 : (0:ℝ) < W := by linarith
  refine ⟨4*W, by linarith, ?_⟩
  intro N _ χ hχ1 hχ2 β γ hzero hbig
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hg0 : (0:ℝ) ≤ |γ| := abs_nonneg γ
  have harg1 : (1:ℝ) ≤ (N:ℝ) * (4*|γ|+7) := by nlinarith
  have hL0 : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*|γ|+7)) := Real.log_nonneg harg1
  obtain ⟨L₀, hL₀def⟩ : ∃ Lv : ℝ, Lv = Real.log ((N:ℝ)*(4*|γ|+7)) + 20 := ⟨_, rfl⟩
  rw [← hL₀def] at hbig ⊢
  have hL20 : 20 ≤ L₀ := by rw [hL₀def]; linarith
  have hCL : 4*W*L₀ ≥ 80 := by nlinarith [hW1, hL20]
  have hCL0 : (0:ℝ) < 4*W*L₀ := by linarith
  -- β < 1
  have hβ1 : β < 1 := by
    by_contra hβ'
    push_neg at hβ'
    have hre : (1:ℝ) ≤ ((β:ℂ) + γ*Complex.I).re := by
      simp
      linarith
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hre hzero
  -- the sigma
  obtain ⟨d, hddef⟩ : ∃ x : ℝ, x = 1/(W*L₀) := ⟨_, rfl⟩
  have hd0 : (0:ℝ) < d := by
    rw [hddef]
    positivity
  have hdinv : d * (W*L₀) = 1 := by
    rw [hddef]
    field_simp
  have hd20 : d ≤ 1/400 := by
    rw [hddef]
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 400)]
    nlinarith [hW1, hL20]
  have hσ1 : 1 < 1 + d := by linarith
  have hσ2 : 1 + d ≤ 2 := by linarith
  -- the height is large relative to d: |γ| ≥ 4d
  have hγ4d : 4*d ≤ |γ| := by
    have hDL0 : (0:ℝ) < D * L₀ := by nlinarith [hD, hL20]
    have h1 : 1/(D*L₀) ≤ |γ| := by
      rw [div_le_iff₀ hDL0]
      exact hbig
    have h2 : 16*d = 16/(W*L₀) := by
      rw [hddef]
      ring
    have h3 : (16:ℝ)/(W*L₀) ≤ 1/(D*L₀) := by
      rw [div_le_div_iff₀ (by positivity) hDL0]
      have h3a := mul_le_mul_of_nonneg_right hW16D (by linarith : (0:ℝ) ≤ L₀)
      have h3b : 16*D*L₀ = 16*(D*L₀) := by ring
      have h3c : 1*(W*L₀) = W*L₀ := by ring
      linarith [h3a, h3b.le, h3b.ge, h3c.le, h3c.ge]
    linarith [h1, h2.le, h2.ge, h3, hd0]
  have hγ0 : (0:ℝ) < |γ| := by linarith [hγ4d, hd0]
  -- case: far from 1 already
  by_cases hfar : (1 + d) - β ≤ 1/5
  swap
  · push_neg at hfar
    have h1 : 1/(4*W*L₀) ≤ 1/10 := by
      rw [div_le_div_iff₀ hCL0 (by norm_num : (0:ℝ) < 10)]
      linarith
    linarith [hd20]
  -- the main chain
  have hcombo := logDeriv_combo_re_nonneg χ (1+d) γ hσ1
  rw [hχ2] at hcombo
  have hlin : (3 * LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (((1+d : ℝ) : ℂ))
       + 4 * LSeries (↗χ * ↗Λ) ((((1+d : ℝ)) : ℂ) + γ * I)
       + LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) ((((1+d : ℝ)) : ℂ) + 2 * γ * I)).re
      = 3 * (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (((1+d : ℝ) : ℂ))).re
        + 4 * (LSeries (↗χ * ↗Λ) ((((1+d : ℝ)) : ℂ) + γ * I)).re
        + (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) ((((1+d : ℝ)) : ℂ) + 2 * γ * I)).re := by
    simp [Complex.add_re, Complex.mul_re]
  rw [hlin] at hcombo
  -- A0: the pole bound at t = 0
  have hA0 := hKP N (1 : DirichletCharacter ℂ N) 0 (1+d) hσ1 hσ2
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hA0
  -- A1: the zero repulsion
  have hA1 := zero_bound_uniform N χ hχ1 β γ hzero (1+d) hσ1 hσ2 hfar
  -- A2: the damped trivial-character bound at height 2γ
  have hA2 := hC₄ N (1+d) (2*γ) hσ1 hσ2
  have harg : ((((1+d : ℝ)) : ℂ) + 2 * γ * I) = ((((1+d : ℝ)) : ℂ) + ((2*γ : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [harg] at hcombo
  -- clean σ − 1 = d
  have hs1 : (1 + d) - 1 = d := by ring
  rw [hs1] at hA0 hA1 hA2
  -- damping: d/(d² + (2γ)²) ≤ (1/64)/d
  have hdamp : d/(d^2 + (2*γ)^2) ≤ 1/(64*d) := by
    have h1 : (64:ℝ)*d^2 ≤ (2*γ)^2 := by
      have h2 : (4*d)^2 ≤ γ^2 := by
        have := sq_abs γ
        nlinarith [hγ4d, hd0]
      nlinarith [h2]
    rw [div_le_div_iff₀ (by positivity) (by positivity : (0:ℝ) < 64*d)]
    nlinarith [h1, sq_nonneg d, hd0]
  -- the log bounds
  have hd1 : (1:ℝ) ≤ 1/d := by
    rw [le_div_iff₀ hd0]
    linarith [hd20]
  have hdW : 1/d = W*L₀ := by
    rw [hddef]
    field_simp
  have hlogd : Real.log (1/d) ≤ Real.log W + L₀ := by
    rw [hdW, Real.log_mul (by linarith) (by linarith)]
    have h1 : Real.log L₀ ≤ L₀ - 1 := Real.log_le_sub_one_of_pos (by linarith)
    linarith
  -- log(N(2|γ|+7)(1+d)/d) ≤ L₀ + log(1/d)
  have hlog1 : Real.log ((N:ℝ)*(2*|γ|+7)*(1+d)/d) ≤ L₀ + Real.log (1/d) := by
    have h1 : (N:ℝ)*(2*|γ|+7)*(1+d)/d ≤ ((N:ℝ)*(4*|γ|+7)) * (1/d) := by
      rw [div_le_iff₀ hd0]
      have h3 : (2*|γ|+7)*d ≤ 2*|γ| := by
        have h3a : |γ| * d ≤ |γ| * (1/400) := mul_le_mul_of_nonneg_left hd20 hg0
        nlinarith [hγ4d, hd0, hg0, h3a]
      have h5 : (2*|γ|+7)*(1+d) ≤ 4*|γ|+7 := by nlinarith [h3]
      have h2 : (N:ℝ)*((2*|γ|+7)*(1+d)) ≤ (N:ℝ)*(4*|γ|+7) :=
        mul_le_mul_of_nonneg_left h5 (by linarith)
      have h4 : (1/d) * d = 1 := by field_simp
      calc (N:ℝ)*(2*|γ|+7)*(1+d) = (N:ℝ)*((2*|γ|+7)*(1+d)) := by ring
        _ ≤ (N:ℝ)*(4*|γ|+7) := h2
        _ = ((N:ℝ)*(4*|γ|+7)) * ((1/d)*d) := by rw [h4, mul_one]
        _ = ((N:ℝ)*(4*|γ|+7)) * (1/d) * d := by ring
    calc Real.log ((N:ℝ)*(2*|γ|+7)*(1+d)/d)
        ≤ Real.log (((N:ℝ)*(4*|γ|+7)) * (1/d)) := by
          apply Real.log_le_log _ h1
          apply div_pos (by nlinarith [hN1r, hg0, hd0]) hd0
      _ = Real.log ((N:ℝ)*(4*|γ|+7)) + Real.log (1/d) := by
          rw [Real.log_mul (by nlinarith [hN1r, hg0]) (by linarith)]
      _ ≤ L₀ + Real.log (1/d) := by
          rw [hL₀def]
          linarith
  -- log(N(|2γ|+3)/d) ≤ L₀ + log(1/d)
  have hlog2 : Real.log ((N:ℝ)*(|2*γ|+3)/d) ≤ L₀ + Real.log (1/d) := by
    have habs2 : |2*γ| = 2*|γ| := by
      rw [abs_mul]
      norm_num
    have h1 : (N:ℝ)*(|2*γ|+3)/d ≤ ((N:ℝ)*(4*|γ|+7)) * (1/d) := by
      rw [habs2, div_le_iff₀ hd0, mul_assoc, mul_comm (1/d) d, ← mul_assoc]
      have h4 : d * (1/d) = 1 := by field_simp
      nlinarith [hN1r, hg0, h4]
    calc Real.log ((N:ℝ)*(|2*γ|+3)/d)
        ≤ Real.log (((N:ℝ)*(4*|γ|+7)) * (1/d)) := by
          apply Real.log_le_log _ h1
          apply div_pos (by nlinarith [hN1r, abs_nonneg (2*γ)]) hd0
      _ = Real.log ((N:ℝ)*(4*|γ|+7)) + Real.log (1/d) := by
          rw [Real.log_mul (by nlinarith [hN1r, hg0]) (by linarith)]
      _ ≤ L₀ + Real.log (1/d) := by
          rw [hL₀def]
          linarith
  -- the √-trick on W
  obtain ⟨sW, hsWdef⟩ : ∃ s : ℝ, s = W^((1:ℝ)/2) := ⟨_, rfl⟩
  have hsW0 : 0 ≤ sW := by rw [hsWdef]; positivity
  have hsW2 : sW^2 = W := by
    rw [hsWdef, ← Real.rpow_natCast (W^((1:ℝ)/2)) 2, ← Real.rpow_mul hW0.le]
    norm_num
  have hlogW : Real.log W ≤ 2*sW := by
    have h1 := Real.log_le_rpow_div hW0.le (by norm_num : (0:ℝ) < 1/2)
    calc Real.log W ≤ W^((1:ℝ)/2)/(1/2) := h1
      _ = 2*W^((1:ℝ)/2) := by ring
      _ = 2*sW := by rw [hsWdef]
  have hsW80 : 80*C₉ ≤ sW := by
    by_contra hcon
    push_neg at hcon
    have h0c : (0:ℝ) ≤ 80*C₉ := by linarith
    have h1 : sW*sW < (80*C₉)*(80*C₉) := mul_lt_mul'' hcon hcon hsW0 hsW0
    have h2 : sW*sW = W := by rw [← pow_two]; exact hsW2
    have h3 : (80*C₉)*(80*C₉) = 6400*C₉^2 := by ring
    linarith [h1, h2.le, h2.ge, h3.le, h3.ge, hW6400]
  -- assemble the extras: C₉·(2L₀ + log(1/d)) ≤ (1/400)·(1/d)
  have hextra : C₉ * (2*L₀ + Real.log (1/d)) ≤ (1/400) * (W*L₀) := by
    have h1 : Real.log (1/d) ≤ 2*sW + L₀ := by linarith [hlogd, hlogW]
    have h2 : C₉ * (2*L₀ + Real.log (1/d)) ≤ C₉*(3*L₀ + 2*sW) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith : (0:ℝ) ≤ C₉)
      linarith [h1]
    have h3 : C₉*(3*L₀) ≤ (1/800)*(W*L₀) := by
      have h3a := mul_le_mul_of_nonneg_right hW2400 (by linarith : (0:ℝ) ≤ L₀)
      have h3b : 2400*C₉*L₀ = 800*(C₉*(3*L₀)) := by ring
      have h3c : W*L₀ = 800*((1/800)*(W*L₀)) := by ring
      linarith [h3a, h3b.le, h3b.ge, h3c.le, h3c.ge]
    have h4 : C₉*(2*sW) ≤ (1/800)*(W*L₀) := by
      have h5a := mul_le_mul_of_nonneg_right hsW80 hsW0
      have h5b : sW*sW = W := by rw [← pow_two]; exact hsW2
      have h5 : 2*C₉*sW ≤ W/40 := by linarith [h5a, h5b.le, h5b.ge]
      have h6a := mul_le_mul_of_nonneg_left hL20 (by linarith : (0:ℝ) ≤ W)
      have h6b : W*20 = 800*(W/40) := by ring
      have h6c : W*L₀ = 800*((1/800)*(W*L₀)) := by ring
      linarith [h5, h6a, h6b.le, h6b.ge, h6c.le, h6c.ge]
    linarith [h2, h3, h4]
  -- generalize the three atoms to opaque reals
  obtain ⟨A₀v, hA₀v⟩ : ∃ x : ℝ,
      x = (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (((1+d : ℝ) : ℂ))).re := ⟨_, rfl⟩
  obtain ⟨A₁v, hA₁v⟩ : ∃ x : ℝ,
      x = (LSeries (↗χ * ↗Λ) ((((1+d : ℝ)) : ℂ) + γ * I)).re := ⟨_, rfl⟩
  obtain ⟨A₂v, hA₂v⟩ : ∃ x : ℝ,
      x = (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ)
        ((((1+d : ℝ)) : ℂ) + ((2*γ : ℝ) : ℂ) * I)).re := ⟨_, rfl⟩
  rw [← hA₀v, ← hA₁v, ← hA₂v] at hcombo
  rw [← hA₀v] at hA0
  rw [← hA₁v] at hA1
  rw [← hA₂v] at hA2
  -- the master chain
  have hchain : 4/((1+d) - β)
      ≤ 3/d + 1/(64*d) + (3*KP' + 320 + 2*C₄)
        + (160 + C₄) * (L₀ + Real.log (1/d)) := by
    have e1 : 3 * A₀v ≤ 3/d + 3*KP' := by
      have b1 : 3/d = 3*(1/d) := by ring
      linarith only [hA0, hKPle, b1]
    have e2 : 4 * A₁v ≤ 160 * (L₀ + Real.log (1/d)) + 160 - 4/((1+d) - β) := by
      have b2 : 4/((1+d) - β) = 4*(1/((1+d) - β)) := by ring
      linarith only [hA1, hlog1, b2]
    have e3 : A₂v ≤ 1/(64*d) + C₄ * (L₀ + Real.log (1/d)) + C₄ := by
      have h9 := mul_le_mul_of_nonneg_left hlog2 (by linarith : (0:ℝ) ≤ C₄)
      linarith only [hA2, hdamp, h9]
    linarith only [hcombo, e1, e2, e3, hC₄1, hKP'0]
  -- numeric close: 4/((1+d)−β) ≤ (31/10)/d
  have hclose : 4/((1+d) - β) ≤ (31/10)/d := by
    have h1 : (3*KP' + 320 + 2*C₄) + (160 + C₄) * (L₀ + Real.log (1/d))
        ≤ C₉ * (2*L₀ + Real.log (1/d)) := by
      have h2 : (0:ℝ) ≤ Real.log (1/d) := Real.log_nonneg hd1
      rw [hC₉def]
      have hb1 := mul_le_mul_of_nonneg_left hL20
        (by linarith : (0:ℝ) ≤ 3*KP' + 320 + 2*C₄)
      nlinarith [hL20, hKP'0, hC₄1, h2, hb1]
    have h3 : C₉ * (2*L₀ + Real.log (1/d)) ≤ (1/400)*(1/d) := by
      have h3a : (1/400)*(W*L₀) = (1/400)*(1/d) := by rw [hdW]
      linarith [hextra, h3a.le, h3a.ge]
    have h4 : 1/(64*d) = (1/64)*(1/d) := by
      rw [div_eq_mul_inv, mul_inv]
      ring
    have h5 : 3/d = 3*(1/d) := by ring
    have h6 : (31/10)/d = (31/10)*(1/d) := by ring
    have h8 : (0:ℝ) < 1/d := by positivity
    have h9 : 3*(1/d) + (1/64)*(1/d) + (1/400)*(1/d) ≤ (31/10)*(1/d) := by
      have h9a : (0:ℝ) ≤ ((31:ℝ)/10 - 3 - 1/64 - 1/400) * (1/d) := by positivity
      linarith [h9a]
    linarith [hchain, h1, h3, h4.le, h4.ge, h5.le, h5.ge, h6.le, h6.ge, h9]
  -- extract the gap
  have hσβ0 : (0:ℝ) < (1+d) - β := by linarith
  have hgap : (40/31)*d ≤ (1+d) - β := by
    rw [div_le_div_iff₀ hσβ0 hd0] at hclose
    linarith [hclose]
  have hfinal : 1/(4*W*L₀) ≤ 1 - β := by
    have h1 : d/4 ≤ 1 - β := by nlinarith [hgap, hd0]
    have h2 : 1/(4*W*L₀) = d/4 := by
      rw [hddef, div_div]
      congr 1
      ring
    linarith [h2.le, h2.ge, h1]
  linarith [hfinal]

end Quad341

/-- **THE UNIFORM ZERO-FREE REGION FOR QUADRATIC CHARACTERS OFF THE REAL AXIS**
    (SW brick S4a-6): one absolute `C` with: every zero `β + iγ`, `γ ≠ 0`, of every
    quadratic nontrivial `χ` mod `N` satisfies
    `β ≤ 1 − 1/(C(log(N(4|γ|+7)) + 20))` — the conjugate-pair repulsion for small
    `|γ|`, the damped 3-4-1 for the rest. Only REAL zeros (Siegel) remain. -/
theorem dvp_zero_free_uniform_quadratic :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ ^ 2 = 1 → ∀ β γ : ℝ, γ ≠ 0 →
      DirichletCharacter.LFunction χ ((β:ℂ) + γ*Complex.I) = 0 →
      β ≤ 1 - 1/(C * (Real.log ((N:ℝ)*(4*|γ|+7)) + 20)) := by
  obtain ⟨Cp, hCp1, hCp⟩ := quad_pair_gap
  obtain ⟨Cq, hCq1, hCq⟩ := quad_341_gap Cp hCp1
  refine ⟨max Cp Cq, le_trans hCp1 (le_max_left _ _), ?_⟩
  intro N _ χ hχ1 hχ2 β γ hγ hzero
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hg0 : (0:ℝ) ≤ |γ| := abs_nonneg γ
  have harg1 : (1:ℝ) ≤ (N:ℝ) * (4*|γ|+7) := by nlinarith
  have hL0 : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*|γ|+7)) := Real.log_nonneg harg1
  obtain ⟨L₀, hL₀def⟩ : ∃ Lv : ℝ, Lv = Real.log ((N:ℝ)*(4*|γ|+7)) + 20 := ⟨_, rfl⟩
  rw [← hL₀def] at ⊢
  have hL20 : 20 ≤ L₀ := by rw [hL₀def]; linarith
  have hmono : ∀ Cbr : ℝ, 1 ≤ Cbr → Cbr ≤ max Cp Cq →
      1/(max Cp Cq * L₀) ≤ 1/(Cbr * L₀) := by
    intro Cbr hCbr1 hCbrle
    apply div_le_div_of_nonneg_left (by norm_num) (by nlinarith [hL20])
    nlinarith [hL20, hCbr1]
  by_cases hsmall : |γ| * (Cp * L₀) ≤ 1
  · have h1 := hCp N χ hχ1 hχ2 β γ hγ hzero (by rw [hL₀def] at hsmall; exact hsmall)
    rw [← hL₀def] at h1
    have h2 := hmono Cp hCp1 (le_max_left _ _)
    linarith [h1, h2]
  · push_neg at hsmall
    have h1 := hCq N χ hχ1 hχ2 β γ hzero
      (by rw [hL₀def] at hsmall; linarith [hsmall])
    rw [← hL₀def] at h1
    have h2 := hmono Cq hCq1 (le_max_right _ _)
    linarith [h1, h2]

end Principia.Common.SW
