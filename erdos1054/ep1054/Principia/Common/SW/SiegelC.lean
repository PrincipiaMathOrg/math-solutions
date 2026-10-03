/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.SW.SiegelB

/-!
# Siegel–Walfisz, `SiegelC`: Siegel's theorem, part C: rates, the dichotomy, `siegel_zero_free`

Ported **verbatim** from the axiom-clean Siegel–Walfisz master
(`Principia Application/LeanSandbox/SiegelWalfiszMaster.lean` = `C:/Users/Christian/pnt/sw_full.lean`,
lines 9337–12246; there `#print axioms siegel_walfisz_proven = [propext, Classical.choice, Quot.sound]`,
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

/-- **Nonnegative partial sums force a nonnegative density** (Siegel brick A3-g3a):
    if `A(n) ≥ 0` and `|A(n) − λn| ≤ C·n^{3/4}(1+log n)` then `λ ≥ 0` — the error is
    `o(n)`, so a negative λ would drag `A` negative. -/
theorem lam_nonneg (A : ℕ → ℝ) (lam C : ℝ) (hC0 : 0 ≤ C)
    (hA0 : ∀ n : ℕ, 0 ≤ A n)
    (hE : ∀ n : ℕ, 1 ≤ n →
      |A n - lam * n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n))) :
    0 ≤ lam := by
  by_contra hneg
  push_neg at hneg
  have hε : (0:ℝ) < -lam := by linarith
  set ε : ℝ := -lam with hεdef
  have hy0 : (0:ℝ) ≤ 9 * C / ε + 1 := by positivity
  -- choose n with n^{1/8} ≥ 9C/ε + 1
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge ((9 * C / ε + 1) ^ (8:ℕ))
  set n : ℕ := max n₀ 1 with hn
  have hn1 : 1 ≤ n := le_max_right _ _
  have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hnr0 : (0:ℝ) < (n:ℝ) := by linarith
  have hnbig : ((9 * C / ε + 1) ^ (8:ℕ) : ℝ) ≤ (n:ℝ) := by
    calc ((9 * C / ε + 1) ^ (8:ℕ) : ℝ) ≤ (n₀:ℝ) := hn₀
      _ ≤ (n:ℝ) := by
          have : n₀ ≤ n := le_max_left _ _
          exact_mod_cast this
  -- n^{1/8} ≥ 9C/ε + 1
  have heighth : 9 * C / ε + 1 ≤ ((n:ℝ)) ^ ((1:ℝ)/8) := by
    have h1 : ((9 * C / ε + 1) ^ (8:ℕ) : ℝ) ^ ((1:ℝ)/8) ≤ ((n:ℝ)) ^ ((1:ℝ)/8) :=
      Real.rpow_le_rpow (by positivity) hnbig (by norm_num)
    have h2 : ((9 * C / ε + 1) ^ (8:ℕ) : ℝ) ^ ((1:ℝ)/8) = 9 * C / ε + 1 := by
      rw [← Real.rpow_natCast (9 * C / ε + 1) 8, ← Real.rpow_mul hy0]
      norm_num
    rw [h2] at h1
    exact h1
  -- the E-bound at n: ε·n ≤ 9C·n^{7/8}
  have hlog : 1 + Real.log n ≤ 9 * ((n:ℝ)) ^ ((1:ℝ)/8) := by
    have h1 : Real.log n ≤ ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) :=
      Real.log_le_rpow_div hnr0.le (by norm_num)
    have h2 : ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) = 8 * ((n:ℝ)) ^ ((1:ℝ)/8) := by ring
    have h3 : (1:ℝ) ≤ ((n:ℝ)) ^ ((1:ℝ)/8) := Real.one_le_rpow hn1r (by norm_num)
    linarith [h1, h2.le, h2.ge, h3]
  have hcollect : ((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) = ((n:ℝ)) ^ ((7:ℝ)/8) := by
    rw [← Real.rpow_add hnr0]
    norm_num
  have hbound : ε * (n:ℝ) ≤ 9 * C * ((n:ℝ)) ^ ((7:ℝ)/8) := by
    have h1 := (abs_le.mp (hE n hn1)).2
    have h2 : lam * n ≥ A n - C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
      linarith
    have h3 : ε * (n:ℝ) ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
      have := hA0 n
      rw [hεdef]
      nlinarith [h2, this]
    calc ε * (n:ℝ) ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := h3
      _ ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (9 * ((n:ℝ)) ^ ((1:ℝ)/8))) := by
          apply mul_le_mul_of_nonneg_left _ hC0
          apply mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hnr0.le _)
      _ = 9 * C * (((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8)) := by ring
      _ = 9 * C * ((n:ℝ)) ^ ((7:ℝ)/8) := by rw [hcollect]
  -- divide by n^{7/8}: ε·n^{1/8} ≤ 9C
  have hsplit : (n:ℝ) = ((n:ℝ)) ^ ((7:ℝ)/8) * ((n:ℝ)) ^ ((1:ℝ)/8) := by
    rw [← Real.rpow_add hnr0]
    norm_num
  have h78pos : (0:ℝ) < ((n:ℝ)) ^ ((7:ℝ)/8) := Real.rpow_pos_of_pos hnr0 _
  have hdiv : ε * ((n:ℝ)) ^ ((1:ℝ)/8) ≤ 9 * C := by
    have h1 : (ε * ((n:ℝ)) ^ ((1:ℝ)/8)) * ((n:ℝ)) ^ ((7:ℝ)/8)
        ≤ (9 * C) * ((n:ℝ)) ^ ((7:ℝ)/8) := by
      calc (ε * ((n:ℝ)) ^ ((1:ℝ)/8)) * ((n:ℝ)) ^ ((7:ℝ)/8)
          = ε * (((n:ℝ)) ^ ((7:ℝ)/8) * ((n:ℝ)) ^ ((1:ℝ)/8)) := by ring
        _ = ε * (n:ℝ) := by rw [← hsplit]
        _ ≤ 9 * C * ((n:ℝ)) ^ ((7:ℝ)/8) := hbound
    exact le_of_mul_le_mul_right h1 h78pos
  -- but ε·n^{1/8} ≥ ε·(9C/ε + 1) = 9C + ε
  have hlow : 9 * C + ε ≤ ε * ((n:ℝ)) ^ ((1:ℝ)/8) := by
    have h1 : ε * (9 * C / ε + 1) ≤ ε * ((n:ℝ)) ^ ((1:ℝ)/8) :=
      mul_le_mul_of_nonneg_left heighth hε.le
    have h2 : ε * (9 * C / ε + 1) = 9 * C + ε := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  linarith [hdiv, hlow, hε]

open scoped LSeries.notation in
/-- The quadruple cast bridge exposed (A3-g3b-i): the ℂ-cast of the coefficient
    sequence is the triple `⍟`-convolution of the four cast factors. -/
lemma quad_cast_bridge (g₁ g₂ : ℕ → ℝ) :
    (fun n => (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun m => g₁ m * g₂ m)) n : ℝ) : ℂ))
    = ((castFn (fun _ => (1:ℝ)) ⍟ castFn g₁) ⍟ castFn g₂)
        ⍟ castFn (fun m => g₁ m * g₂ m) := by
  funext n
  have step1 : (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
      * toArith (fun m => g₁ m * g₂ m)) n : ℝ) : ℂ)
      = ((fun m => (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂) m : ℝ) : ℂ))
        ⍟ castFn (fun m => g₁ m * g₂ m)) n := by
    rw [ArithmeticFunction.mul_apply, LSeries.convolution_def]
    push_cast
    apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    have h2 : p.2 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hp
      exact hp.2 hp.1.symm
    rw [castFn]
  rw [step1]
  have step2 : (fun m => (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂) m : ℝ) : ℂ))
      = (fun m => (((toArith (fun _ => (1:ℝ)) * toArith g₁) m : ℝ) : ℂ)) ⍟ castFn g₂ := by
    funext m
    rw [ArithmeticFunction.mul_apply, LSeries.convolution_def]
    push_cast
    apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    have h2 : p.2 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hp
      exact hp.2 hp.1.symm
    rw [castFn]
  rw [step2]
  have step3 : (fun m => (((toArith (fun _ => (1:ℝ)) * toArith g₁) m : ℝ) : ℂ))
      = castFn (fun _ => (1:ℝ)) ⍟ castFn g₁ := by
    funext m
    exact castFn_conv (fun _ => (1:ℝ)) g₁ m
  rw [step3]

/-- Summability of the quadruple coefficient series on `Re s > 1` (A3-g3b-ii). -/
lemma quad_LSeriesSummable (g₁ g₂ : ℕ → ℝ)
    (h1b : ∀ n, |g₁ n| ≤ 1) (h2b : ∀ n, |g₂ n| ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (((toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun m => g₁ m * g₂ m)) n : ℝ) : ℂ)) s := by
  have honeb : ∀ n : ℕ, |(fun _ : ℕ => (1:ℝ)) n| ≤ 1 := fun n => by norm_num
  have hg12b : ∀ n, |g₁ n * g₂ n| ≤ 1 := by
    intro n
    rw [abs_mul]
    calc |g₁ n| * |g₂ n| ≤ 1 * 1 := mul_le_mul (h1b n) (h2b n) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [quad_cast_bridge g₁ g₂]
  exact (((castFn_summable (fun _ => (1:ℝ)) honeb hs).convolution
    (castFn_summable g₁ h1b hs)).convolution
    (castFn_summable g₂ h2b hs)).convolution
    (castFn_summable (fun m => g₁ m * g₂ m) hg12b hs)

/-- The cast of `charFn` is the character's naive coefficient function away
    from `0` (A3-g3b-iii). -/
lemma castFn_charFn {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    {n : ℕ} (hn : n ≠ 0) :
    castFn (charFn q χ) n = χ ((n : ZMod q)) := by
  show ((toArith (charFn q χ) n : ℝ) : ℂ) = χ ((n : ZMod q))
  rw [toArith_apply _ n hn, charFn_repr χ hχ2 n]

/-- **The Goldfeld product identity at characters** (Siegel brick A3-g3b): on
    `Re s > 1` the quadruple L-series IS `ζ·L(χ₁)·L(χ₂)·L(χ₁χ₂)`. -/
theorem quad_P_identity {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (((toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
        * toArith (charFn q₂ χ₂)
        * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) n : ℝ) : ℂ)) s
    = riemannZeta s * DirichletCharacter.LFunction χ₁ s
        * DirichletCharacter.LFunction χ₂ s
        * DirichletCharacter.LFunction
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) s := by
  have h1b := fun n => charFn_bound χ₁ hχ₁2 n
  have h2b := fun n => charFn_bound χ₂ hχ₂2 n
  rw [quad_LSeries_eq (charFn q₁ χ₁) (charFn q₂ χ₂) h1b h2b hs]
  have hχ₃2 : ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
      * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ^ 2 = 1 := by
    rw [mul_pow, ← map_pow, ← map_pow, hχ₁2, hχ₂2, map_one, map_one, mul_one]
  have hz : LSeries (castFn (fun _ => (1:ℝ))) s = riemannZeta s := by
    rw [← LSeries_one_eq_riemannZeta hs]
    apply LSeries_congr
    intro n hn
    show ((toArith (fun _ => (1:ℝ)) n : ℝ) : ℂ) = (1 : ℕ → ℂ) n
    rw [toArith_apply _ n hn, Pi.one_apply, Complex.ofReal_one]
  have hL1 : LSeries (castFn (charFn q₁ χ₁)) s = DirichletCharacter.LFunction χ₁ s := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ₁ hs]
    exact LSeries_congr (fun {n} hn => castFn_charFn χ₁ hχ₁2 hn) s
  have hL2 : LSeries (castFn (charFn q₂ χ₂)) s = DirichletCharacter.LFunction χ₂ s := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ₂ hs]
    exact LSeries_congr (fun {n} hn => castFn_charFn χ₂ hχ₂2 hn) s
  have hL3 : LSeries (castFn (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) s
      = DirichletCharacter.LFunction
          ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
            * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) s := by
    rw [DirichletCharacter.LFunction_eq_LSeries _ hs]
    apply LSeries_congr
    intro n hn
    show ((toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m) n : ℝ) : ℂ) = _
    rw [toArith_apply _ n hn, ← charFn_mul_char χ₁ χ₂ hχ₁2 hχ₂2 n,
      charFn_repr _ hχ₃2 n]
  rw [hz, hL1, hL2, hL3]

/-- The four-factor product is analytic on the slit half-plane (A3-g3b-iv). -/
lemma quad_P_differentiableAt {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1)
    (s : ℂ) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun w => riemannZeta w * DirichletCharacter.LFunction χ₁ w
      * DirichletCharacter.LFunction χ₂ w
      * DirichletCharacter.LFunction
          ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
            * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) w) s := by
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · apply DifferentiableAt.mul
      · exact differentiableAt_riemannZeta hs1
      · exact (DirichletCharacter.differentiable_LFunction hχ₁1).differentiableAt
    · exact (DirichletCharacter.differentiable_LFunction hχ₂1).differentiableAt
  · exact (DirichletCharacter.differentiable_LFunction hχ₃1).differentiableAt

/-- **SIEGEL'S λ LOWER BOUND AT CHARACTERS** (Siegel brick A3-g3c): if the product
    `ζ·L(χ₁)·L(χ₂)·L(χ₁χ₂)` vanishes at a real `β ∈ (9/10, 1)` — e.g. at a real zero
    of `L(·,χ₁)` — then `λ = L₁·Lk > (1−β)/(26·x^{1−β})` for every admissible `x`,
    with `L₁, Lk` carrying their partial-sum approach rates. -/
theorem siegel_lambda_lower_for_chars {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1)
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1)
    (hzero : DirichletCharacter.LFunction χ₁ ((β:ℂ)) = 0) :
    ∃ L₁ Lk C : ℝ, 0 ≤ L₁ * Lk ∧ 0 ≤ C
      ∧ (∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, charFn q₁ χ₁ d / d| ≤ 2 * (q₁:ℝ) / (y + 1))
      ∧ (∀ y : ℕ, 1 ≤ y →
          |Lk - ∑ d ∈ Icc 1 y, (toArith (charFn q₂ χ₂)
              * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d / d|
            ≤ 7 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) / Real.sqrt y)
      ∧ ∀ x : ℕ, 2 ≤ x → ((820 * (C + 1)) ^ (40:ℕ) : ℝ) ≤ (x:ℝ) →
          1 - β ≤ 26 * (L₁ * Lk) * ((x:ℝ)) ^ (1 - β) := by
  have hq₁ : 1 ≤ q₁ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)
  have hq₂ : 1 ≤ q₂ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₂)
  obtain ⟨L₁, Lk, C, hr1, hr2, hC0, hEsys⟩ :=
    quad_system_for_chars hq₁ hq₂ χ₁ χ₂ hχ₁2 hχ₂2 hχ₁1 hχ₂1 hχ₃1
  obtain ⟨ha0, ha1⟩ := quad_conv_nonneg (charFn q₁ χ₁) (charFn q₂ χ₂)
    (charFn_mul χ₁ hχ₁2) (charFn_mul χ₂ hχ₂2)
    (charFn_one χ₁) (charFn_one χ₂)
    (charFn_values χ₁ hχ₁2) (charFn_values χ₂ hχ₂2)
  have h1b := fun n => charFn_bound χ₁ hχ₁2 n
  have h2b := fun n => charFn_bound χ₂ hχ₂2 n
  -- the E-function and its properties
  have hA0 : ∀ n : ℕ, 0 ≤ ∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ))
      * toArith (charFn q₁ χ₁) * toArith (charFn q₂ χ₂)
      * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m :=
    fun n => Finset.sum_nonneg (fun m _ => ha0 m)
  have hlam : 0 ≤ L₁ * Lk := by
    apply lam_nonneg (fun n => ∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ))
        * toArith (charFn q₁ χ₁) * toArith (charFn q₂ χ₂)
        * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m)
      (L₁ * Lk) C hC0 hA0
    intro n hn
    exact hEsys n hn
  refine ⟨L₁, Lk, C, hlam, hC0, hr1, hr2, ?_⟩
  intro x hx hxC
  apply siegel_lambda_lower
    (fun n => (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
      * toArith (charFn q₂ χ₂)
      * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) n)
    (L₁ * Lk)
    (fun n => (∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
      * toArith (charFn q₂ χ₂)
      * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m) - L₁ * Lk * n)
    C ha0 ha1 hlam
    (fun n => by ring)
    hC0
    (by
      show (∑ m ∈ Icc 1 0, (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
        * toArith (charFn q₂ χ₂)
        * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m) - L₁ * Lk * (0:ℕ) = 0
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, Nat.cast_zero, mul_zero,
        sub_zero])
    (fun n hn => hEsys n hn)
    (fun s hs => quad_LSeriesSummable (charFn q₁ χ₁) (charFn q₂ χ₂) h1b h2b hs)
    (fun w => riemannZeta w * DirichletCharacter.LFunction χ₁ w
      * DirichletCharacter.LFunction χ₂ w
      * DirichletCharacter.LFunction
          ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
            * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) w)
    (fun s _ hs1 => quad_P_differentiableAt χ₁ χ₂ hχ₁1 hχ₂1 hχ₃1 s hs1)
    (fun s hs => quad_P_identity χ₁ χ₂ hχ₁2 hχ₂2 hs)
    hβ1 hβ2
    (by
      show riemannZeta ((β:ℂ)) * DirichletCharacter.LFunction χ₁ ((β:ℂ))
        * DirichletCharacter.LFunction χ₂ ((β:ℂ))
        * DirichletCharacter.LFunction
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ((β:ℂ)) = 0
      rw [hzero, mul_zero, zero_mul, zero_mul])
    x hx hxC

/-- **The generalized Dirichlet test** (Siegel brick A5-a): `q`-bounded partial sums
    against ANY nonneg antitone weight: `|Σ_{y<d≤z} g(d)w(d)| ≤ 2q·w(y+1)` — the
    uniform-in-`s` engine for the `L(1,χ)` identifications. -/
lemma abel_tail_general (g : ℕ → ℝ) (q : ℝ) (w : ℕ → ℝ)
    (hG : ∀ t : ℕ, |∑ n ∈ Icc 1 t, g n| ≤ q)
    (hw0 : ∀ d, 0 ≤ w d) (hwa : ∀ d, w (d + 1) ≤ w d)
    (y : ℕ) : ∀ z : ℕ, y ≤ z →
    |∑ d ∈ Icc (y + 1) z, g d * w d| ≤ 2 * q * w (y + 1) := by
  have hq : 0 ≤ q := le_trans (abs_nonneg _) (hG 0)
  -- the general Abel window identity
  have hwindow : ∀ z : ℕ, y ≤ z →
      ∑ d ∈ Icc (y + 1) z, g d * w d
      = ∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))
        + (∑ n ∈ Icc 1 z, g n) * w (z + 1) - (∑ n ∈ Icc 1 y, g n) * w (y + 1) := by
    intro z
    induction z with
    | zero =>
      intro hy0
      interval_cases y
      simp
    | succ m ih =>
      intro hym
      rcases Nat.lt_or_ge m y with hlt | hge
      · have hy' : y = m + 1 := by omega
        subst hy'
        have hempty : Icc (m + 1 + 1) (m + 1) = (∅ : Finset ℕ) :=
          Finset.Icc_eq_empty (by omega)
        rw [hempty, Finset.sum_empty, Finset.sum_empty]
        ring
      · have hins : Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) := by
          ext d
          simp only [Finset.mem_insert, Finset.mem_Icc]
          omega
        have hnotmem : (m + 1) ∉ Icc (y + 1) m := by
          simp only [Finset.mem_Icc]
          omega
        rw [hins, Finset.sum_insert hnotmem, Finset.sum_insert hnotmem, ih hge]
        have hS : ∑ n ∈ Icc 1 (m + 1), g n = g (m + 1) + ∑ n ∈ Icc 1 m, g n := by
          rw [show Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) from by
            ext d
            simp only [Finset.mem_insert, Finset.mem_Icc]
            omega, Finset.sum_insert (by
              simp only [Finset.mem_Icc]
              omega)]
        rw [hS]
        ring
  -- the weight telescope
  have htel : ∀ z : ℕ, y ≤ z →
      ∑ d ∈ Icc (y + 1) z, (w d - w (d + 1)) = w (y + 1) - w (z + 1) := by
    intro z
    induction z with
    | zero =>
      intro hy0
      interval_cases y
      simp
    | succ m ih =>
      intro hym
      rcases Nat.lt_or_ge m y with hlt | hge
      · have hy' : y = m + 1 := by omega
        subst hy'
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
        ring
      · rw [show Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) from by
          ext d
          simp only [Finset.mem_insert, Finset.mem_Icc]
          omega, Finset.sum_insert (by
            simp only [Finset.mem_Icc]
            omega), ih hge]
        ring
  intro z hz
  rw [hwindow z hz]
  have hterm : ∀ d ∈ Icc (y + 1) z,
      |(∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))| ≤ q * (w d - w (d + 1)) := by
    intro d _
    rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ w d - w (d + 1) from by linarith [hwa d])]
    apply mul_le_mul_of_nonneg_right (hG d)
    linarith [hwa d]
  calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))
        + (∑ n ∈ Icc 1 z, g n) * w (z + 1) - (∑ n ∈ Icc 1 y, g n) * w (y + 1)|
      ≤ |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))|
        + |(∑ n ∈ Icc 1 z, g n) * w (z + 1)| + |(∑ n ∈ Icc 1 y, g n) * w (y + 1)| := by
        have h1 := abs_add_le (∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))
          + (∑ n ∈ Icc 1 z, g n) * w (z + 1)) (-((∑ n ∈ Icc 1 y, g n) * w (y + 1)))
        have h2 := abs_add_le (∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1)))
          ((∑ n ∈ Icc 1 z, g n) * w (z + 1))
        rw [abs_neg, ← sub_eq_add_neg] at h1
        linarith
    _ ≤ q * (w (y + 1) - w (z + 1)) + q * w (z + 1) + q * w (y + 1) := by
        have h1 : |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))|
            ≤ q * (w (y + 1) - w (z + 1)) := by
          calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))|
              ≤ ∑ d ∈ Icc (y + 1) z, |(∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ d ∈ Icc (y + 1) z, q * (w d - w (d + 1)) :=
                Finset.sum_le_sum hterm
            _ = q * ∑ d ∈ Icc (y + 1) z, (w d - w (d + 1)) := by
                rw [Finset.mul_sum]
            _ = q * (w (y + 1) - w (z + 1)) := by rw [htel z hz]
        have h2 : |(∑ n ∈ Icc 1 z, g n) * w (z + 1)| ≤ q * w (z + 1) := by
          rw [abs_mul, abs_of_nonneg (hw0 _)]
          exact mul_le_mul_of_nonneg_right (hG z) (hw0 _)
        have h3 : |(∑ n ∈ Icc 1 y, g n) * w (y + 1)| ≤ q * w (y + 1) := by
          rw [abs_mul, abs_of_nonneg (hw0 _)]
          exact mul_le_mul_of_nonneg_right (hG y) (hw0 _)
        linarith
    _ ≤ 2 * q * w (y + 1) := by
        have := hw0 (z + 1)
        linarith

/-- Character sums against `d^{−s}` decay at the `s = 1` rate, uniformly in
    `s ≥ 1` (Siegel brick A5-b1). -/
lemma char_rpow_tail_rate {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1) {s : ℝ} (hs : 1 ≤ s) (y : ℕ) :
    ∀ z : ℕ, y ≤ z →
    |∑ d ∈ Icc (y + 1) z, charFn q χ d * ((d:ℝ)) ^ (-s)| ≤ 2 * (q:ℝ) / (y + 1) := by
  intro z hz
  set w : ℕ → ℝ := fun d => if d = 0 then 1 else ((d:ℝ)) ^ (-s) with hw
  have hw0 : ∀ d, 0 ≤ w d := by
    intro d
    rw [hw]
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · simp only [if_neg hd]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hwa : ∀ d, w (d + 1) ≤ w d := by
    intro d
    rw [hw]
    rcases eq_or_ne d 0 with rfl | hd
    · norm_num [Real.one_rpow]
    · simp only [if_neg hd, if_neg (by omega : d + 1 ≠ 0)]
      have hd0 : (0:ℝ) < (d:ℝ) := by
        have : (0:ℕ) < d := by omega
        exact_mod_cast this
      apply Real.rpow_le_rpow_of_nonpos hd0 (by push_cast; linarith)
      linarith
  have hG := charFn_partial_sum_bound hq χ hχ2 hχ1
  have h := abel_tail_general (charFn q χ) ((q:ℝ)) w hG hw0 hwa y z hz
  have hcongr : ∑ d ∈ Icc (y + 1) z, charFn q χ d * w d
      = ∑ d ∈ Icc (y + 1) z, charFn q χ d * ((d:ℝ)) ^ (-s) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [hw]
    simp only [if_neg (by omega : d ≠ 0)]
  rw [hcongr] at h
  have hwy : w (y + 1) ≤ 1 / ((y:ℝ) + 1) := by
    rw [hw]
    simp only [if_neg (by omega : y + 1 ≠ 0)]
    have hy0 : (1:ℝ) ≤ ((y + 1 : ℕ):ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) y]
    calc ((y + 1 : ℕ):ℝ) ^ (-s) ≤ ((y + 1 : ℕ):ℝ) ^ (-(1:ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hy0 (by linarith)
      _ = 1 / ((y:ℝ) + 1) := by
          rw [Real.rpow_neg_one, ← one_div]
          push_cast
          ring_nf
  have hq0 : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg q
  calc |∑ d ∈ Icc (y + 1) z, charFn q χ d * ((d:ℝ)) ^ (-s)|
      ≤ 2 * (q:ℝ) * w (y + 1) := h
    _ ≤ 2 * (q:ℝ) * (1 / ((y:ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left hwy (by positivity)
    _ = 2 * (q:ℝ) / ((y:ℝ) + 1) := by ring

/-- **The real representation of `L(s,χ)` with the uniform Abel rate**
    (Siegel brick A5-b2): for real `s > 1` there is a real value `ℓ` with
    `L(s,χ) = ℓ` and `|ℓ − Σ_{d≤y}χ(d)d^{−s}| ≤ 2q/(y+1)` for every `y`. -/
theorem LFunction_real_rate {q : ℕ} [NeZero q] (hq : 1 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1)
    {s : ℝ} (hs : 1 < s) :
    ∃ ℓ : ℝ, DirichletCharacter.LFunction χ ((s:ℂ)) = ((ℓ : ℝ) : ℂ)
      ∧ ∀ y : ℕ, |ℓ - ∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-s)| ≤ 2 * (q:ℝ) / (y + 1) := by
  -- the real partial sums are Cauchy with the explicit rate
  set S : ℕ → ℝ := fun z => ∑ d ∈ Icc 1 z, charFn q χ d * ((d:ℝ)) ^ (-s) with hS
  have hsplit : ∀ y z : ℕ, y ≤ z → S z - S y
      = ∑ d ∈ Icc (y + 1) z, charFn q χ d * ((d:ℝ)) ^ (-s) := by
    intro y z hyz
    rw [hS]
    simp only
    rw [show Icc 1 z = Icc 1 y ∪ Icc (y + 1) z from by
      ext d
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega, Finset.sum_union (by
        rw [Finset.disjoint_left]
        intro d hd hd2
        rw [Finset.mem_Icc] at hd hd2
        omega)]
    ring
  have hdiff : ∀ y z : ℕ, y ≤ z → |S z - S y| ≤ 2 * (q:ℝ) / (y + 1) := by
    intro y z hyz
    rw [hsplit y z hyz]
    exact char_rpow_tail_rate hq χ hχ2 hχ1 hs.le y z hyz
  have hb0 : Tendsto (fun y : ℕ => 2 * (q:ℝ) / ((y:ℝ) + 1)) atTop (nhds 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hcauchy : CauchySeq S := by
    apply cauchySeq_of_le_tendsto_0 (b := fun y : ℕ => 2 * (q:ℝ) / ((y:ℝ) + 1)) _ hb0
    intro m n N hm hn
    rw [Real.dist_eq]
    rcases Nat.le_total m n with h | h
    · rw [abs_sub_comm]
      calc |S n - S m| ≤ 2 * (q:ℝ) / ((m:ℝ) + 1) := hdiff m n h
        _ ≤ 2 * (q:ℝ) / ((N:ℝ) + 1) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            push_cast
            have : (N:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
            linarith
    · calc |S m - S n| ≤ 2 * (q:ℝ) / ((n:ℝ) + 1) := hdiff n m h
        _ ≤ 2 * (q:ℝ) / ((N:ℝ) + 1) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            push_cast
            have : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
            linarith
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨ℓ, ?_, ?_⟩
  · -- LFunction = ofReal ℓ: both are limits of ofReal ∘ S
    have hre : ((s:ℂ)).re = s := Complex.ofReal_re s
    have hs1 : 1 < ((s:ℂ)).re := by rw [hre]; exact hs
    have hLS : DirichletCharacter.LFunction χ ((s:ℂ)) = LSeries (fun n => χ ((n : ZMod q))) ((s:ℂ)) :=
      DirichletCharacter.LFunction_eq_LSeries χ hs1
    -- LSeries summability from |χ| ≤ 1
    have hχb : ∀ n : ℕ, n ≠ 0 → ‖χ ((n : ZMod q))‖ ≤ 1 := by
      intro n _
      rw [← charFn_repr χ hχ2 n, Complex.norm_real, Real.norm_eq_abs]
      exact charFn_bound χ hχ2 n
    have hsummable : LSeriesSummable (fun n => χ ((n : ZMod q))) ((s:ℂ)) :=
      LSeriesSummable_of_bounded_of_one_lt_re (m := 1) hχb hs1
    -- ℂ partial sums equal ofReal ∘ S
    have hterm_eq : ∀ n : ℕ, 1 ≤ n →
        LSeries.term (fun n => χ ((n : ZMod q))) ((s:ℂ)) n
          = ((charFn q χ n * ((n:ℝ)) ^ (-s) : ℝ) : ℂ) := by
      intro n hn
      rw [LSeries.term_of_ne_zero (by omega), div_eq_mul_inv, ← Complex.cpow_neg,
        cpow_real_cast n s, ← charFn_repr χ hχ2 n]
      push_cast
      ring
    have hpartial : Tendsto (fun z : ℕ => ((S z : ℝ) : ℂ)) atTop
        (nhds (LSeries (fun n => χ ((n : ZMod q))) ((s:ℂ)))) := by
      have h1 : Tendsto (fun z : ℕ => ∑ n ∈ range (z + 1),
          LSeries.term (fun n => χ ((n : ZMod q))) ((s:ℂ)) n) atTop
          (nhds (LSeries (fun n => χ ((n : ZMod q))) ((s:ℂ)))) := by
        have := hsummable.hasSum.tendsto_sum_nat
        exact this.comp (tendsto_add_atTop_nat 1)
      apply h1.congr
      intro z
      show ∑ n ∈ range (z + 1), LSeries.term (fun n => χ ((n : ZMod q))) ((s:ℂ)) n
        = ((∑ d ∈ Icc 1 z, charFn q χ d * ((d:ℝ)) ^ (-s) : ℝ) : ℂ)
      rw [show range (z + 1) = insert 0 (Icc 1 z) from by
        ext d
        simp only [Finset.mem_insert, Finset.mem_range, Finset.mem_Icc]
        omega, Finset.sum_insert (by
          simp only [Finset.mem_Icc]
          omega), LSeries.term_zero, zero_add, Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun n hn => by
        rw [Finset.mem_Icc] at hn
        exact hterm_eq n hn.1)
    have hofReal : Tendsto (fun z : ℕ => ((S z : ℝ) : ℂ)) atTop (nhds ((ℓ : ℂ))) :=
      (Complex.continuous_ofReal.tendsto ℓ).comp hℓ
    rw [hLS]
    exact tendsto_nhds_unique hpartial hofReal
  · -- the rate transfers to the limit
    intro y
    have h1 : ∀ z : ℕ, y ≤ z → |S z - S y| ≤ 2 * (q:ℝ) / (y + 1) := fun z hz => hdiff y z hz
    have h2 : Tendsto (fun z : ℕ => S z - S y) atTop (nhds (ℓ - S y)) :=
      hℓ.sub tendsto_const_nhds
    have h3 : |ℓ - S y| ≤ 2 * (q:ℝ) / (y + 1) := by
      apply le_of_tendsto (h2.abs)
      filter_upwards [eventually_ge_atTop y] with z hz
      exact h1 z hz
    exact h3

/-- **`L₁ = L(1,χ)`** (Siegel brick A5-c): the abstract hyperbola limit with the
    `2q/(y+1)` rate IS the analytic `L`-value at `1` — squeeze along `s → 1⁺`. -/
theorem L1_eq_LFunction_one {q : ℕ} [NeZero q] (hq : 1 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1)
    (L₁ : ℝ)
    (hr : ∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, charFn q χ d / d| ≤ 2 * (q:ℝ) / (y + 1)) :
    DirichletCharacter.LFunction χ 1 = ((L₁ : ℝ) : ℂ) := by
  -- Step 1: the boundary rate at s = 1
  have hy : ∀ y : ℕ, ‖DirichletCharacter.LFunction χ 1
      - ((∑ d ∈ Icc 1 y, charFn q χ d / d : ℝ) : ℂ)‖ ≤ 2 * (q:ℝ) / (y + 1) := by
    intro y
    -- the finite sum at exponent −s, as a continuous function of s
    have hcont_term : ∀ d : ℕ, d ∈ Icc 1 y →
        Continuous (fun s : ℝ => charFn q χ d * ((d:ℝ)) ^ (-s)) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hd0 : (0:ℝ) < (d:ℝ) := by
        have : (0:ℕ) < d := by omega
        exact_mod_cast this
      have hrw : (fun s : ℝ => ((d:ℝ)) ^ (-s))
          = fun s : ℝ => Real.exp (Real.log d * (-s)) := by
        funext s
        rw [Real.rpow_def_of_pos hd0]
      apply Continuous.mul continuous_const
      rw [hrw]
      exact Real.continuous_exp.comp (continuous_const.mul continuous_neg)
    have hcont_sum : Continuous (fun s : ℝ =>
        ∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-s)) :=
      continuous_finset_sum _ (fun d hd => hcont_term d hd)
    -- the two limits along s → 1⁺
    have hofReal1 : Tendsto (fun s : ℝ => ((s:ℝ):ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhds ((1:ℂ))) := by
      have h := (Complex.continuous_ofReal.tendsto (1:ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (1:ℝ)))
      simpa using h
    have htends1 : Tendsto (fun s : ℝ => DirichletCharacter.LFunction χ ((s:ℂ)))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (DirichletCharacter.LFunction χ 1)) := by
      have hc : ContinuousAt (DirichletCharacter.LFunction χ) 1 :=
        (DirichletCharacter.differentiable_LFunction hχ1).continuous.continuousAt
      exact hc.tendsto.comp hofReal1
    have htends2 : Tendsto (fun s : ℝ =>
        ((∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-s) : ℝ) : ℂ))
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds ((∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-(1:ℝ)) : ℝ) : ℂ)) := by
      have h1 : Tendsto (fun s : ℝ => ∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-s))
          (nhdsWithin 1 (Set.Ioi 1))
          (nhds (∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-(1:ℝ)))) :=
        (hcont_sum.tendsto 1).mono_left nhdsWithin_le_nhds
      exact (Complex.continuous_ofReal.tendsto _).comp h1
    -- the eventual bound
    have hev : ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1),
        ‖DirichletCharacter.LFunction χ ((s:ℂ))
          - ((∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-s) : ℝ) : ℂ)‖
        ≤ 2 * (q:ℝ) / (y + 1) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [Set.mem_Ioi] at hs
      obtain ⟨ℓ, hL, hrate⟩ := LFunction_real_rate hq χ hχ2 hχ1 hs
      rw [hL, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hrate y
    -- pass to the limit
    have hlim : Tendsto (fun s : ℝ => ‖DirichletCharacter.LFunction χ ((s:ℂ))
        - ((∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-s) : ℝ) : ℂ)‖)
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds ‖DirichletCharacter.LFunction χ 1
          - ((∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-(1:ℝ)) : ℝ) : ℂ)‖) :=
      (htends1.sub htends2).norm
    have hle := le_of_tendsto hlim hev
    have hconv : ∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-(1:ℝ))
        = ∑ d ∈ Icc 1 y, charFn q χ d / d := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Real.rpow_neg_one, div_eq_mul_inv]
    rw [hconv] at hle
    exact hle
  -- Step 2: combine with the abstract rate and squeeze to equality
  have hcomb : ∀ y : ℕ, ‖DirichletCharacter.LFunction χ 1 - ((L₁ : ℝ) : ℂ)‖
      ≤ 4 * (q:ℝ) / (y + 1) := by
    intro y
    have h1 := hy y
    have h2 : ‖((∑ d ∈ Icc 1 y, charFn q χ d / d : ℝ) : ℂ) - ((L₁ : ℝ) : ℂ)‖
        ≤ 2 * (q:ℝ) / (y + 1) := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact hr y
    calc ‖DirichletCharacter.LFunction χ 1 - ((L₁ : ℝ) : ℂ)‖
        ≤ ‖DirichletCharacter.LFunction χ 1
            - ((∑ d ∈ Icc 1 y, charFn q χ d / d : ℝ) : ℂ)‖
          + ‖((∑ d ∈ Icc 1 y, charFn q χ d / d : ℝ) : ℂ) - ((L₁ : ℝ) : ℂ)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * (q:ℝ) / (y + 1) + 2 * (q:ℝ) / (y + 1) := add_le_add h1 h2
      _ = 4 * (q:ℝ) / (y + 1) := by ring
  by_contra hne
  have hpos : 0 < ‖DirichletCharacter.LFunction χ 1 - ((L₁ : ℝ) : ℂ)‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hne
  obtain ⟨y, hy'⟩ := exists_nat_gt (4 * (q:ℝ)
    / ‖DirichletCharacter.LFunction χ 1 - ((L₁ : ℝ) : ℂ)‖)
  have h1 := hcomb y
  have hy1 : (0:ℝ) < (y:ℝ) + 1 := by positivity
  rw [div_lt_iff₀ hpos] at hy'
  have h2 : 4 * (q:ℝ) / ((y:ℝ) + 1)
      < ‖DirichletCharacter.LFunction χ 1 - ((L₁ : ℝ) : ℂ)‖ := by
    rw [div_lt_iff₀ hy1]
    calc 4 * (q:ℝ) < (y:ℝ) * ‖DirichletCharacter.LFunction χ 1 - ((L₁ : ℝ) : ℂ)‖ := hy'
      _ ≤ ‖DirichletCharacter.LFunction χ 1 - ((L₁ : ℝ) : ℂ)‖ * ((y:ℝ) + 1) := by
          nlinarith [hpos, Nat.cast_nonneg (α := ℝ) y]
  linarith

/-- **The √-size partial sums against `d^{−s}` decay at the `1/√y` rate, uniformly
    in `s ∈ [1,2]`** (Siegel brick A5-d1) — the convolution-side twin of
    `char_rpow_tail_rate`, powering the `Lk` identification. -/
lemma conv_rpow_tail_rate (k : ℕ → ℝ) (B : ℝ)
    (hK : ∀ t : ℕ, |∑ n ∈ Icc 1 t, k n| ≤ B * (Real.sqrt t + 1))
    {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (y : ℕ) (hy1 : 1 ≤ y) :
    ∀ z : ℕ, y ≤ z →
    |∑ d ∈ Icc (y + 1) z, k d * ((d:ℝ)) ^ (-s)| ≤ 30 * B / Real.sqrt y := by
  have hB0 : 0 ≤ B := by
    have h0 := hK 0
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, abs_zero,
      Nat.cast_zero, Real.sqrt_zero, zero_add, mul_one] at h0
    exact h0
  set w : ℕ → ℝ := fun d => ((d:ℝ)) ^ (-s) with hw
  -- the Abel window identity (generic in w)
  have hwindow : ∀ z : ℕ, y ≤ z →
      ∑ d ∈ Icc (y + 1) z, k d * w d
      = ∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))
        + (∑ n ∈ Icc 1 z, k n) * w (z + 1) - (∑ n ∈ Icc 1 y, k n) * w (y + 1) := by
    intro z
    induction z with
    | zero =>
      intro hy0
      omega
    | succ m ih =>
      intro hym
      rcases Nat.lt_or_ge m y with hlt | hge
      · have hy' : y = m + 1 := by omega
        subst hy'
        have hempty : Icc (m + 1 + 1) (m + 1) = (∅ : Finset ℕ) :=
          Finset.Icc_eq_empty (by omega)
        rw [hempty, Finset.sum_empty, Finset.sum_empty]
        ring
      · have hins : Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) := by
          ext d
          simp only [Finset.mem_insert, Finset.mem_Icc]
          omega
        have hnotmem : (m + 1) ∉ Icc (y + 1) m := by
          simp only [Finset.mem_Icc]
          omega
        rw [hins, Finset.sum_insert hnotmem, Finset.sum_insert hnotmem, ih hge]
        have hS : ∑ n ∈ Icc 1 (m + 1), k n = k (m + 1) + ∑ n ∈ Icc 1 m, k n := by
          rw [show Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) from by
            ext d
            simp only [Finset.mem_insert, Finset.mem_Icc]
            omega, Finset.sum_insert (by
              simp only [Finset.mem_Icc]
              omega)]
        rw [hS]
        ring
  -- per-term kernel bound: |S d|(w d − w(d+1)) ≤ 4B/(d√d) for d ≥ 1
  have hkernel : ∀ d : ℕ, 1 ≤ d →
      |(∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))| ≤ 4 * B * (1 / ((d:ℝ) * Real.sqrt d)) := by
    intro d hd
    have hd0 : (0:ℝ) < (d:ℝ) := by
      have : (0:ℕ) < d := hd
      exact_mod_cast this
    have hd1r : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have hsq1 : (1:ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1r
    have hΔ0 : 0 ≤ w d - w (d + 1) := by
      rw [hw]
      simp only
      have : (((d + 1 : ℕ)):ℝ) ^ (-s) ≤ ((d:ℝ)) ^ (-s) := by
        apply Real.rpow_le_rpow_of_nonpos hd0 (by push_cast; linarith)
        linarith
      push_cast at this ⊢
      linarith
    have hΔle : w d - w (d + 1) ≤ 2 * ((d:ℝ)) ^ (-(2:ℝ)) := by
      rw [hw]
      simp only
      have h1 := rpow_diff_le d hd s (by linarith)
      have h2 : ((d:ℝ)) ^ (-s - 1) ≤ ((d:ℝ)) ^ (-(2:ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hd1r
        linarith
      have h3 : s * ((d:ℝ)) ^ (-s - 1) ≤ 2 * ((d:ℝ)) ^ (-(2:ℝ)) := by
        calc s * ((d:ℝ)) ^ (-s - 1) ≤ 2 * ((d:ℝ)) ^ (-s - 1) := by
              apply mul_le_mul_of_nonneg_right hs2 (Real.rpow_nonneg hd0.le _)
          _ ≤ 2 * ((d:ℝ)) ^ (-(2:ℝ)) := by
              apply mul_le_mul_of_nonneg_left h2 (by norm_num)

      push_cast at h1 ⊢
      linarith
    have hSb : |∑ n ∈ Icc 1 d, k n| ≤ 2 * B * Real.sqrt d := by
      calc |∑ n ∈ Icc 1 d, k n| ≤ B * (Real.sqrt d + 1) := hK d
        _ ≤ B * (Real.sqrt d + Real.sqrt d) := by
            apply mul_le_mul_of_nonneg_left _ hB0
            linarith
        _ = 2 * B * Real.sqrt d := by ring
    have hrpow2 : ((d:ℝ)) ^ (-(2:ℝ)) = 1 / ((d:ℝ) * (d:ℝ)) := by
      rw [show (-(2:ℝ)) = -(((2:ℕ)):ℝ) from by norm_num, Real.rpow_neg hd0.le,
        Real.rpow_natCast, pow_two, one_div]
    have hcollect : Real.sqrt d * (1 / ((d:ℝ) * (d:ℝ))) = 1 / ((d:ℝ) * Real.sqrt d) := by
      rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity), one_mul]
      calc Real.sqrt d * ((d:ℝ) * Real.sqrt d)
          = (Real.sqrt d * Real.sqrt d) * (d:ℝ) := by ring
        _ = (d:ℝ) * (d:ℝ) := by rw [Real.mul_self_sqrt hd0.le]
    rw [abs_mul, abs_of_nonneg hΔ0]
    calc |∑ n ∈ Icc 1 d, k n| * (w d - w (d + 1))
        ≤ (2 * B * Real.sqrt d) * (2 * ((d:ℝ)) ^ (-(2:ℝ))) := by
          apply mul_le_mul hSb hΔle hΔ0
          positivity
      _ = 4 * B * (Real.sqrt d * ((d:ℝ)) ^ (-(2:ℝ))) := by ring
      _ = 4 * B * (Real.sqrt d * (1 / ((d:ℝ) * (d:ℝ)))) := by rw [hrpow2]
      _ = 4 * B * (1 / ((d:ℝ) * Real.sqrt d)) := by rw [hcollect]
  intro z hz
  rw [hwindow z hz]
  have hy0 : (0:ℝ) < (y:ℝ) := by
    have : (0:ℕ) < y := hy1
    exact_mod_cast this
  have hz0 : (0:ℝ) < (z:ℝ) := by
    have : (0:ℕ) < z := by omega
    exact_mod_cast this
  have hsqy : (1:ℝ) ≤ Real.sqrt y := Real.one_le_sqrt.mpr (by exact_mod_cast hy1)
  have hsqy0 : (0:ℝ) < Real.sqrt y := by linarith
  have hsqz0 : (0:ℝ) < Real.sqrt z := Real.sqrt_pos.mpr hz0
  -- the three pieces
  have h1 : |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))|
      ≤ 8 * B / Real.sqrt y := by
    calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))|
        ≤ ∑ d ∈ Icc (y + 1) z, |(∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc (y + 1) z, 4 * B * (1 / ((d:ℝ) * Real.sqrt d)) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          exact hkernel d (by omega)
      _ = 4 * B * ∑ d ∈ Icc (y + 1) z, (1 : ℝ) / (d * Real.sqrt d) := by
          rw [Finset.mul_sum]
      _ ≤ 4 * B * (2 / Real.sqrt y - 2 / Real.sqrt z) := by
          apply mul_le_mul_of_nonneg_left (sum_three_half_tail_sharp y hy1 z hz)
            (by positivity)
      _ ≤ 8 * B / Real.sqrt y := by
          have h3 : (0:ℝ) ≤ 4 * B * (2 / Real.sqrt z) := by positivity
          have heq : 4 * B * (2 / Real.sqrt y - 2 / Real.sqrt z)
              = 8 * B / Real.sqrt y - 4 * B * (2 / Real.sqrt z) := by ring
          linarith [heq.le, heq.ge]
  have hwle : ∀ t : ℕ, 1 ≤ t → w (t + 1) ≤ 1 / (t:ℝ) := by
    intro t ht
    have ht0 : (0:ℝ) < (t:ℝ) := by
      have : (0:ℕ) < t := ht
      exact_mod_cast this
    have ht1 : (1:ℝ) ≤ ((t + 1 : ℕ):ℝ) := by push_cast; linarith
    rw [hw]
    simp only
    calc ((t + 1 : ℕ):ℝ) ^ (-s) ≤ ((t + 1 : ℕ):ℝ) ^ (-(1:ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
      _ = 1 / ((t + 1 : ℕ):ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / (t:ℝ) := by
          apply one_div_le_one_div_of_le ht0
          push_cast
          linarith
  have hbz : |(∑ n ∈ Icc 1 z, k n) * w (z + 1)| ≤ 2 * B / Real.sqrt y := by
    have hw0z : 0 ≤ w (z + 1) := by
      rw [hw]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hsqzz : Real.sqrt z / (z:ℝ) = 1 / Real.sqrt z := by
      rw [eq_div_iff (ne_of_gt hsqz0)]
      field_simp
      exact Real.sq_sqrt hz0.le
    calc |(∑ n ∈ Icc 1 z, k n) * w (z + 1)|
        = |∑ n ∈ Icc 1 z, k n| * w (z + 1) := by rw [abs_mul, abs_of_nonneg hw0z]
      _ ≤ (2 * B * Real.sqrt z) * (1 / (z:ℝ)) := by
          apply mul_le_mul _ (hwle z (by omega)) hw0z (by positivity)
          calc |∑ n ∈ Icc 1 z, k n| ≤ B * (Real.sqrt z + 1) := hK z
            _ ≤ B * (Real.sqrt z + Real.sqrt z) := by
                apply mul_le_mul_of_nonneg_left _ hB0
                have : (1:ℝ) ≤ Real.sqrt z := Real.one_le_sqrt.mpr (by
                  have : (1:ℕ) ≤ z := by omega
                  exact_mod_cast this)
                linarith
            _ = 2 * B * Real.sqrt z := by ring
      _ = 2 * B * (Real.sqrt z / (z:ℝ)) := by ring
      _ = 2 * B * (1 / Real.sqrt z) := by rw [hsqzz]
      _ ≤ 2 * B / Real.sqrt y := by
          rw [mul_one_div]
          apply div_le_div_of_nonneg_left (by linarith) hsqy0
          exact Real.sqrt_le_sqrt (by exact_mod_cast hz)
  have hby : |(∑ n ∈ Icc 1 y, k n) * w (y + 1)| ≤ 2 * B / Real.sqrt y := by
    have hw0y : 0 ≤ w (y + 1) := by
      rw [hw]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hsqyy : Real.sqrt y / (y:ℝ) = 1 / Real.sqrt y := by
      rw [eq_div_iff (ne_of_gt hsqy0)]
      field_simp
      exact Real.sq_sqrt hy0.le
    calc |(∑ n ∈ Icc 1 y, k n) * w (y + 1)|
        = |∑ n ∈ Icc 1 y, k n| * w (y + 1) := by rw [abs_mul, abs_of_nonneg hw0y]
      _ ≤ (2 * B * Real.sqrt y) * (1 / (y:ℝ)) := by
          apply mul_le_mul _ (hwle y hy1) hw0y (by positivity)
          calc |∑ n ∈ Icc 1 y, k n| ≤ B * (Real.sqrt y + 1) := hK y
            _ ≤ B * (Real.sqrt y + Real.sqrt y) := by
                apply mul_le_mul_of_nonneg_left _ hB0
                linarith
            _ = 2 * B * Real.sqrt y := by ring
      _ = 2 * B * (Real.sqrt y / (y:ℝ)) := by ring
      _ = 2 * B * (1 / Real.sqrt y) := by rw [hsqyy]
      _ = 2 * B / Real.sqrt y := by rw [mul_one_div]
  calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))
        + (∑ n ∈ Icc 1 z, k n) * w (z + 1) - (∑ n ∈ Icc 1 y, k n) * w (y + 1)|
      ≤ |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))|
        + |(∑ n ∈ Icc 1 z, k n) * w (z + 1)| + |(∑ n ∈ Icc 1 y, k n) * w (y + 1)| := by
        have ha := abs_add_le (∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))
          + (∑ n ∈ Icc 1 z, k n) * w (z + 1)) (-((∑ n ∈ Icc 1 y, k n) * w (y + 1)))
        have hb := abs_add_le (∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1)))
          ((∑ n ∈ Icc 1 z, k n) * w (z + 1))
        rw [abs_neg, ← sub_eq_add_neg] at ha
        linarith
    _ ≤ 8 * B / Real.sqrt y + 2 * B / Real.sqrt y + 2 * B / Real.sqrt y := by
        linarith [h1, hbz, hby]
    _ ≤ 30 * B / Real.sqrt y := by
        have h30 : (12:ℝ) * B / Real.sqrt y ≤ 30 * B / Real.sqrt y := by
          apply div_le_div_of_nonneg_right _ hsqy0.le
          linarith
        have heq : 8 * B / Real.sqrt y + 2 * B / Real.sqrt y + 2 * B / Real.sqrt y
            = 12 * B / Real.sqrt y := by ring
        linarith [heq.le, heq.ge, h30]

/-- **The pair `L(s,χ₂)L(s,χ₁χ₂)` is real with the `30B/√y` Abel rate**
    (Siegel brick A5-d2): the convolution partial sums identify the product of
    the two L-values at every real `s ∈ (1,2]`. -/
theorem LFunction_pair_real_rate {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂)
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1)
    {s : ℝ} (hs : 1 < s) (hs2 : s ≤ 2) :
    ∃ ℓ : ℝ, DirichletCharacter.LFunction χ₂ ((s:ℂ))
        * DirichletCharacter.LFunction
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ((s:ℂ)) = ((ℓ:ℝ):ℂ)
      ∧ ∀ y : ℕ, 1 ≤ y →
        |ℓ - ∑ d ∈ Icc 1 y, (toArith (charFn q₂ χ₂)
            * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d * ((d:ℝ)) ^ (-s)|
          ≤ 30 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) / Real.sqrt y := by
  have h2b := fun n => charFn_bound χ₂ hχ₂2 n
  have h12b : ∀ n, |charFn q₁ χ₁ n * charFn q₂ χ₂ n| ≤ 1 := by
    intro n
    rw [abs_mul]
    calc |charFn q₁ χ₁ n| * |charFn q₂ χ₂ n| ≤ 1 * 1 :=
        mul_le_mul (charFn_bound χ₁ hχ₁2 n) (h2b n) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hχ₃2 : ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
      * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ^ 2 = 1 := by
    rw [mul_pow, ← map_pow, ← map_pow, hχ₁2, hχ₂2, map_one, map_one, mul_one]
  have hq₁₂ : 1 ≤ q₁ * q₂ :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hG₂ := charFn_partial_sum_bound hq₂ χ₂ hχ₂2 hχ₂1
  have hG₃ := charFn_partial_sum_bound hq₁₂ _ hχ₃2 hχ₃1
  have hK2 : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (charFn q₁ χ₁ n * charFn q₂ χ₂ n)|
      ≤ (q₁:ℝ) * (q₂:ℝ) := by
    intro t
    have heq : ∑ n ∈ Icc 1 t, (charFn q₁ χ₁ n * charFn q₂ χ₂ n)
        = ∑ n ∈ Icc 1 t, charFn (q₁ * q₂)
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) n :=
      Finset.sum_congr rfl (fun n _ => (charFn_mul_char χ₁ χ₂ hχ₁2 hχ₂2 n).symm)
    rw [heq]
    have h := hG₃ t
    push_cast at h
    exact h
  have hKb : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (toArith (charFn q₂ χ₂)
      * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) n|
      ≤ (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) * (Real.sqrt t + 1) :=
    fun t => bounded_conv_sqrt_bound (charFn q₂ χ₂)
      (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m) ((q₂:ℝ)) ((q₁:ℝ) * (q₂:ℝ))
      h2b h12b hG₂ hK2 t
  set B : ℝ := 2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ) with hB
  set k : ℕ → ℝ := fun d => (toArith (charFn q₂ χ₂)
      * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d with hk
  set S : ℕ → ℝ := fun z => ∑ d ∈ Icc 1 z, k d * ((d:ℝ)) ^ (-s) with hS
  have hsplit : ∀ y z : ℕ, y ≤ z → S z - S y
      = ∑ d ∈ Icc (y + 1) z, k d * ((d:ℝ)) ^ (-s) := by
    intro y z hyz
    rw [hS]
    simp only
    rw [show Icc 1 z = Icc 1 y ∪ Icc (y + 1) z from by
      ext d
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega, Finset.sum_union (by
        rw [Finset.disjoint_left]
        intro d hd hd2
        rw [Finset.mem_Icc] at hd hd2
        omega)]
    ring
  have hdiff : ∀ y z : ℕ, 1 ≤ y → y ≤ z → |S z - S y| ≤ 30 * B / Real.sqrt y := by
    intro y z hy1 hyz
    rw [hsplit y z hyz]
    exact conv_rpow_tail_rate k B hKb hs.le hs2 y hy1 z hyz
  -- Cauchy via the shifted sequence
  have hb0 : Tendsto (fun N : ℕ => 30 * B / Real.sqrt ((N:ℝ) + 1)) atTop (nhds 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    apply Filter.Tendsto.comp Real.tendsto_sqrt_atTop
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hcauchyT : CauchySeq (fun z : ℕ => S (z + 1)) := by
    apply cauchySeq_of_le_tendsto_0 (b := fun N : ℕ => 30 * B / Real.sqrt ((N:ℝ) + 1)) _ hb0
    intro m n N hm hn
    rw [Real.dist_eq]
    have hmono : ∀ u v : ℕ, N ≤ u → u ≤ v →
        |S (v + 1) - S (u + 1)| ≤ 30 * B / Real.sqrt ((N:ℝ) + 1) := by
      intro u v hu huv
      calc |S (v + 1) - S (u + 1)| ≤ 30 * B / Real.sqrt (((u + 1 : ℕ)):ℝ) :=
            hdiff (u + 1) (v + 1) (by omega) (by omega)
        _ ≤ 30 * B / Real.sqrt ((N:ℝ) + 1) := by
            have hB0 : (0:ℝ) ≤ B := by
              have h0 := hKb 0
              rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, abs_zero,
                Nat.cast_zero, Real.sqrt_zero, zero_add, mul_one] at h0
              exact h0
            apply div_le_div_of_nonneg_left (by linarith)
              (Real.sqrt_pos.mpr (by positivity))
            apply Real.sqrt_le_sqrt
            push_cast
            have : (N:ℝ) ≤ (u:ℝ) := by exact_mod_cast hu
            linarith
    rcases Nat.le_total m n with h | h
    · rw [abs_sub_comm]
      exact hmono m n hm h
    · exact hmono n m hn h
  obtain ⟨ℓ, hℓT⟩ := cauchySeq_tendsto_of_complete hcauchyT
  have hℓ : Tendsto S atTop (nhds ℓ) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    exact hℓT
  refine ⟨ℓ, ?_, ?_⟩
  · -- the ℂ identification
    have hsc : (1:ℝ) < ((s:ℂ)).re := by
      rw [Complex.ofReal_re]
      exact hs
    have hsum2 := castFn_summable (charFn q₂ χ₂) h2b hsc
    have hsum12 := castFn_summable (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m) h12b hsc
    have hbridge : (fun n => ((k n : ℝ) : ℂ))
        = (LSeries.convolution (castFn (charFn q₂ χ₂))
            (castFn (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m))) := by
      funext n
      exact castFn_conv _ _ n
    have hsummable : LSeriesSummable (fun n => ((k n : ℝ) : ℂ)) ((s:ℂ)) := by
      rw [hbridge]
      exact hsum2.convolution hsum12
    have hprod : LSeries (fun n => ((k n : ℝ) : ℂ)) ((s:ℂ))
        = LSeries (castFn (charFn q₂ χ₂)) ((s:ℂ))
          * LSeries (castFn (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) ((s:ℂ)) := by
      rw [hbridge]
      exact LSeries_convolution' hsum2 hsum12
    have hL2 : LSeries (castFn (charFn q₂ χ₂)) ((s:ℂ))
        = DirichletCharacter.LFunction χ₂ ((s:ℂ)) := by
      rw [DirichletCharacter.LFunction_eq_LSeries χ₂ hsc]
      exact LSeries_congr (fun {n} hn => castFn_charFn χ₂ hχ₂2 hn) _
    have hL3 : LSeries (castFn (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) ((s:ℂ))
        = DirichletCharacter.LFunction
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ((s:ℂ)) := by
      rw [DirichletCharacter.LFunction_eq_LSeries _ hsc]
      apply LSeries_congr
      intro n hn
      show ((toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m) n : ℝ) : ℂ) = _
      rw [toArith_apply _ n hn, ← charFn_mul_char χ₁ χ₂ hχ₁2 hχ₂2 n,
        charFn_repr _ hχ₃2 n]
    have hterm_eq : ∀ n : ℕ, 1 ≤ n →
        LSeries.term (fun n => ((k n : ℝ) : ℂ)) ((s:ℂ)) n
          = ((k n * ((n:ℝ)) ^ (-s) : ℝ) : ℂ) := by
      intro n hn
      rw [LSeries.term_of_ne_zero (by omega), div_eq_mul_inv, ← Complex.cpow_neg,
        cpow_real_cast n s]
      push_cast
      ring
    have hpartial : Tendsto (fun z : ℕ => ((S z : ℝ) : ℂ)) atTop
        (nhds (LSeries (fun n => ((k n : ℝ) : ℂ)) ((s:ℂ)))) := by
      have h1 : Tendsto (fun z : ℕ => ∑ n ∈ range (z + 1),
          LSeries.term (fun n => ((k n : ℝ) : ℂ)) ((s:ℂ)) n) atTop
          (nhds (LSeries (fun n => ((k n : ℝ) : ℂ)) ((s:ℂ)))) := by
        have := hsummable.hasSum.tendsto_sum_nat
        exact this.comp (tendsto_add_atTop_nat 1)
      apply h1.congr
      intro z
      show ∑ n ∈ range (z + 1), LSeries.term (fun n => ((k n : ℝ) : ℂ)) ((s:ℂ)) n
        = ((∑ d ∈ Icc 1 z, k d * ((d:ℝ)) ^ (-s) : ℝ) : ℂ)
      rw [show range (z + 1) = insert 0 (Icc 1 z) from by
        ext d
        simp only [Finset.mem_insert, Finset.mem_range, Finset.mem_Icc]
        omega, Finset.sum_insert (by
          simp only [Finset.mem_Icc]
          omega), LSeries.term_zero, zero_add, Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun n hn => by
        rw [Finset.mem_Icc] at hn
        exact hterm_eq n hn.1)
    have hofReal : Tendsto (fun z : ℕ => ((S z : ℝ) : ℂ)) atTop (nhds ((ℓ : ℂ))) :=
      (Complex.continuous_ofReal.tendsto ℓ).comp hℓ
    have hval : LSeries (fun n => ((k n : ℝ) : ℂ)) ((s:ℂ)) = ((ℓ : ℝ) : ℂ) :=
      tendsto_nhds_unique hpartial hofReal
    rw [← hL2, ← hL3, ← hprod, hval]
  · -- the rate at the limit
    intro y hy1
    have h2 : Tendsto (fun z : ℕ => S z - S y) atTop (nhds (ℓ - S y)) :=
      hℓ.sub tendsto_const_nhds
    have h3 : |ℓ - S y| ≤ 30 * B / Real.sqrt y := by
      apply le_of_tendsto h2.abs
      filter_upwards [eventually_ge_atTop y] with z hz
      exact hdiff y z hy1 hz
    exact h3

/-- **`Lk = L(1,χ₂)·L(1,χ₁χ₂)`** (Siegel brick A5-d3): the abstract convolution
    limit with the `7B/√y` rate IS the product of the analytic `L`-values at `1`. -/
theorem Lk_eq_LFunction_pair_one {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂)
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1)
    (Lk : ℝ)
    (hr : ∀ y : ℕ, 1 ≤ y →
      |Lk - ∑ d ∈ Icc 1 y, (toArith (charFn q₂ χ₂)
          * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d / d|
        ≤ 7 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) / Real.sqrt y) :
    DirichletCharacter.LFunction χ₂ 1
      * DirichletCharacter.LFunction
          ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
            * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) 1
      = ((Lk : ℝ) : ℂ) := by
  set B : ℝ := 2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ) with hB
  have hB0 : (0:ℝ) ≤ B := by
    rw [hB]
    positivity
  set k : ℕ → ℝ := fun d => (toArith (charFn q₂ χ₂)
      * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d with hk
  set P1 : ℂ := DirichletCharacter.LFunction χ₂ 1
      * DirichletCharacter.LFunction
          ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
            * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) 1 with hP1
  -- Step 1: the boundary rate at s = 1
  have hy : ∀ y : ℕ, 1 ≤ y →
      ‖P1 - ((∑ d ∈ Icc 1 y, k d / d : ℝ) : ℂ)‖ ≤ 30 * B / Real.sqrt y := by
    intro y hy1
    have hcont_term : ∀ d : ℕ, d ∈ Icc 1 y →
        Continuous (fun s : ℝ => k d * ((d:ℝ)) ^ (-s)) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hd0 : (0:ℝ) < (d:ℝ) := by
        have : (0:ℕ) < d := by omega
        exact_mod_cast this
      have hrw : (fun s : ℝ => ((d:ℝ)) ^ (-s))
          = fun s : ℝ => Real.exp (Real.log d * (-s)) := by
        funext s
        rw [Real.rpow_def_of_pos hd0]
      apply Continuous.mul continuous_const
      rw [hrw]
      exact Real.continuous_exp.comp (continuous_const.mul continuous_neg)
    have hcont_sum : Continuous (fun s : ℝ => ∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-s)) :=
      continuous_finset_sum _ (fun d hd => hcont_term d hd)
    have hofReal1 : Tendsto (fun s : ℝ => ((s:ℝ):ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhds ((1:ℂ))) := by
      have h := (Complex.continuous_ofReal.tendsto (1:ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (1:ℝ)))
      simpa using h
    have htends1 : Tendsto (fun s : ℝ => DirichletCharacter.LFunction χ₂ ((s:ℂ))
        * DirichletCharacter.LFunction
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ((s:ℂ)))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds P1) := by
      have hc2 : ContinuousAt (DirichletCharacter.LFunction χ₂) 1 :=
        (DirichletCharacter.differentiable_LFunction hχ₂1).continuous.continuousAt
      have hc3 : ContinuousAt (DirichletCharacter.LFunction
          ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
            * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂))) 1 :=
        (DirichletCharacter.differentiable_LFunction hχ₃1).continuous.continuousAt
      exact (hc2.tendsto.comp hofReal1).mul (hc3.tendsto.comp hofReal1)
    have htends2 : Tendsto (fun s : ℝ =>
        ((∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-s) : ℝ) : ℂ))
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds ((∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-(1:ℝ)) : ℝ) : ℂ)) := by
      have h1 : Tendsto (fun s : ℝ => ∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-s))
          (nhdsWithin 1 (Set.Ioi 1))
          (nhds (∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-(1:ℝ)))) :=
        (hcont_sum.tendsto 1).mono_left nhdsWithin_le_nhds
      exact (Complex.continuous_ofReal.tendsto _).comp h1
    have hev : ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1),
        ‖DirichletCharacter.LFunction χ₂ ((s:ℂ))
            * DirichletCharacter.LFunction
                ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
                  * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ((s:ℂ))
          - ((∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-s) : ℝ) : ℂ)‖
        ≤ 30 * B / Real.sqrt y := by
      filter_upwards [self_mem_nhdsWithin,
        Ioo_mem_nhdsGT (show (1:ℝ) < 2 from by norm_num)] with s hs1 hs2
      rw [Set.mem_Ioi] at hs1
      rw [Set.mem_Ioo] at hs2
      obtain ⟨ℓ, hL, hrate⟩ := LFunction_pair_real_rate hq₁ hq₂ χ₁ χ₂ hχ₁2 hχ₂2
        hχ₁1 hχ₂1 hχ₃1 hs1 hs2.2.le
      rw [hL, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hrate y hy1
    have hlim : Tendsto (fun s : ℝ => ‖DirichletCharacter.LFunction χ₂ ((s:ℂ))
        * DirichletCharacter.LFunction
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ((s:ℂ))
        - ((∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-s) : ℝ) : ℂ)‖)
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds ‖P1 - ((∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-(1:ℝ)) : ℝ) : ℂ)‖) :=
      (htends1.sub htends2).norm
    have hle := le_of_tendsto hlim hev
    have hconv : ∑ d ∈ Icc 1 y, k d * ((d:ℝ)) ^ (-(1:ℝ))
        = ∑ d ∈ Icc 1 y, k d / d := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Real.rpow_neg_one, div_eq_mul_inv]
    rw [hconv] at hle
    exact hle
  -- Step 2: combine and pinch
  have hcomb : ∀ y : ℕ, 1 ≤ y → ‖P1 - ((Lk : ℝ) : ℂ)‖ ≤ 37 * B / Real.sqrt y := by
    intro y hy1
    have h1 := hy y hy1
    have h2 : ‖((∑ d ∈ Icc 1 y, k d / d : ℝ) : ℂ) - ((Lk : ℝ) : ℂ)‖
        ≤ 7 * B / Real.sqrt y := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact hr y hy1
    calc ‖P1 - ((Lk : ℝ) : ℂ)‖
        ≤ ‖P1 - ((∑ d ∈ Icc 1 y, k d / d : ℝ) : ℂ)‖
          + ‖((∑ d ∈ Icc 1 y, k d / d : ℝ) : ℂ) - ((Lk : ℝ) : ℂ)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 30 * B / Real.sqrt y + 7 * B / Real.sqrt y := add_le_add h1 h2
      _ = 37 * B / Real.sqrt y := by ring
  by_contra hne
  have hpos : 0 < ‖P1 - ((Lk : ℝ) : ℂ)‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hne
  obtain ⟨y₀, hy₀⟩ := exists_nat_gt ((37 * B / ‖P1 - ((Lk : ℝ) : ℂ)‖) ^ (2:ℕ))
  set y : ℕ := max y₀ 1 with hydef
  have hy1 : 1 ≤ y := le_max_right _ _
  have hybig : ((37 * B / ‖P1 - ((Lk : ℝ) : ℂ)‖) ^ (2:ℕ) : ℝ) < (y:ℝ) := by
    calc ((37 * B / ‖P1 - ((Lk : ℝ) : ℂ)‖) ^ (2:ℕ) : ℝ) < (y₀:ℝ) := hy₀
      _ ≤ (y:ℝ) := by
          have : y₀ ≤ y := le_max_left _ _
          exact_mod_cast this
  have hsq : 37 * B / ‖P1 - ((Lk : ℝ) : ℂ)‖ < Real.sqrt y := by
    have h0 : (0:ℝ) ≤ 37 * B / ‖P1 - ((Lk : ℝ) : ℂ)‖ := by positivity
    rw [show (37 * B / ‖P1 - ((Lk : ℝ) : ℂ)‖ : ℝ)
        = Real.sqrt ((37 * B / ‖P1 - ((Lk : ℝ) : ℂ)‖) ^ (2:ℕ)) from
      (Real.sqrt_sq h0).symm]
    exact Real.sqrt_lt_sqrt (by positivity) hybig
  have hsqy0 : (0:ℝ) < Real.sqrt y :=
    Real.sqrt_pos.mpr (by
      have : (0:ℕ) < y := hy1
      exact_mod_cast this)
  have hfinal : 37 * B / Real.sqrt y < ‖P1 - ((Lk : ℝ) : ℂ)‖ := by
    rw [div_lt_iff₀ hsqy0]
    rw [div_lt_iff₀ hpos] at hsq
    linarith [hsq]
  have := hcomb y hy1
  linarith [this, hfinal]

/-- **The `L₁` upper bound** (Siegel brick S1a): any limit with the `2q/(y+1)` rate
    of `1`-bounded coefficient means satisfies `|L₁| ≤ 3 + log q` for `q ≥ 1`. -/
lemma rate_limit_upper_log (g : ℕ → ℝ) (q : ℕ) (hq : 1 ≤ q) (L : ℝ)
    (hgb : ∀ n, |g n| ≤ 1)
    (hr : ∀ y : ℕ, |L - ∑ d ∈ Icc 1 y, g d / d| ≤ 2 * (q:ℝ) / (y + 1)) :
    |L| ≤ 3 + Real.log q := by
  have hq0 : (0:ℝ) < (q:ℝ) := by
    have : (0:ℕ) < q := hq
    exact_mod_cast this
  have h1 := hr q
  have h2 : |∑ d ∈ Icc 1 q, g d / d| ≤ 1 + Real.log q := by
    calc |∑ d ∈ Icc 1 q, g d / d| ≤ ∑ d ∈ Icc 1 q, |g d / d| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 q, (1:ℝ) / d := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          have hd0 : (0:ℝ) < (d:ℝ) := by
            have : (0:ℕ) < d := by omega
            exact_mod_cast this
          rw [abs_div, Nat.abs_cast]
          apply div_le_div_of_nonneg_right (hgb d) hd0.le
      _ ≤ 1 + Real.log q := sum_one_div_le_log q hq
  have h3 : 2 * (q:ℝ) / ((q:ℝ) + 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  calc |L| ≤ |L - ∑ d ∈ Icc 1 q, g d / d| + |∑ d ∈ Icc 1 q, g d / d| := by
        have := abs_add_le (L - ∑ d ∈ Icc 1 q, g d / d) (∑ d ∈ Icc 1 q, g d / d)
        simpa using this
    _ ≤ 2 * (q:ℝ) / ((q:ℝ) + 1) + (1 + Real.log q) := by
        push_cast at h1
        linarith [h1, h2]
    _ ≤ 3 + Real.log q := by linarith [h3]

/-- **The `Lk` upper bound** (Siegel brick S1b): any limit with the `7B/√y` rate of
    a convolution of `1`-bounded functions satisfies `|Lk| ≤ 7B + 1`. -/
lemma sqrt_rate_limit_upper (u v : ℕ → ℝ) (B : ℝ) (Lk : ℝ)
    (hub : ∀ n, |u n| ≤ 1) (hvb : ∀ n, |v n| ≤ 1)
    (hr : ∀ y : ℕ, 1 ≤ y →
      |Lk - ∑ d ∈ Icc 1 y, (toArith u * toArith v) d / d| ≤ 7 * B / Real.sqrt y) :
    |Lk| ≤ 7 * B + 1 := by
  have h1 := hr 1 (le_refl 1)
  have hs1 : Real.sqrt ((1:ℕ):ℝ) = 1 := by
    rw [Nat.cast_one, Real.sqrt_one]
  rw [hs1, div_one] at h1
  have h2 : ∑ d ∈ Icc 1 1, (toArith u * toArith v) d / d
      = (toArith u * toArith v) 1 := by
    rw [show (Icc 1 1 : Finset ℕ) = {1} from rfl, Finset.sum_singleton, Nat.cast_one,
      div_one]
  have h3 : |(toArith u * toArith v) 1| ≤ 1 := by
    rw [ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one,
      Finset.sum_singleton]
    have hu1 : |toArith u 1| ≤ 1 := by
      rw [show toArith u 1 = u 1 from by simp [toArith]]
      exact hub 1
    have hv1 : |toArith v 1| ≤ 1 := by
      rw [show toArith v 1 = v 1 from by simp [toArith]]
      exact hvb 1
    rw [abs_mul]
    calc |toArith u 1| * |toArith v 1| ≤ 1 * 1 :=
        mul_le_mul hu1 hv1 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc |Lk| ≤ |Lk - ∑ d ∈ Icc 1 1, (toArith u * toArith v) d / d|
        + |∑ d ∈ Icc 1 1, (toArith u * toArith v) d / d| := by
        have := abs_add_le (Lk - ∑ d ∈ Icc 1 1, (toArith u * toArith v) d / d)
          (∑ d ∈ Icc 1 1, (toArith u * toArith v) d / d)
        simpa using this
    _ ≤ 7 * B + 1 := by
        rw [h2] at h1 ⊢
        linarith [h1, h3]

/-- Character sums against `d^{−σ}` decay at the `(y+1)^{−σ}` rate for every
    `σ ≥ 0` (Siegel brick S2a) — the sub-one extension of `char_rpow_tail_rate`. -/
lemma char_rpow_tail_rate_gen {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1) {σ : ℝ} (hσ : 0 ≤ σ) (y : ℕ) :
    ∀ z : ℕ, y ≤ z →
    |∑ d ∈ Icc (y + 1) z, charFn q χ d * ((d:ℝ)) ^ (-σ)|
      ≤ 2 * (q:ℝ) * (((y + 1 : ℕ)):ℝ) ^ (-σ) := by
  intro z hz
  set w : ℕ → ℝ := fun d => if d = 0 then 1 else ((d:ℝ)) ^ (-σ) with hw
  have hw0 : ∀ d, 0 ≤ w d := by
    intro d
    rw [hw]
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · simp only [if_neg hd]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hwa : ∀ d, w (d + 1) ≤ w d := by
    intro d
    rw [hw]
    rcases eq_or_ne d 0 with rfl | hd
    · norm_num [Real.one_rpow]
    · simp only [if_neg hd, if_neg (by omega : d + 1 ≠ 0)]
      have hd0 : (0:ℝ) < (d:ℝ) := by
        have : (0:ℕ) < d := by omega
        exact_mod_cast this
      apply Real.rpow_le_rpow_of_nonpos hd0 (by push_cast; linarith)
      linarith
  have hG := charFn_partial_sum_bound hq χ hχ2 hχ1
  have h := abel_tail_general (charFn q χ) ((q:ℝ)) w hG hw0 hwa y z hz
  have hcongr : ∑ d ∈ Icc (y + 1) z, charFn q χ d * w d
      = ∑ d ∈ Icc (y + 1) z, charFn q χ d * ((d:ℝ)) ^ (-σ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [hw]
    simp only [if_neg (by omega : d ≠ 0)]
  rw [hcongr] at h
  have hwy : w (y + 1) = (((y + 1 : ℕ)):ℝ) ^ (-σ) := by
    rw [hw]
    simp only [if_neg (by omega : y + 1 ≠ 0)]
  rw [hwy] at h
  exact h

/-- **The below-one partial-sum rate for `L(σ,χ)`** (Siegel brick S2b): at real
    `σ ∈ (9/10, 1)`, the analytically-continued `L`-value is within
    `2q(y+1)^{−σ}` of every partial sum — the representation the zero-gap
    bridge differences. -/
theorem LFunction_partial_rate_below_one {q : ℕ} [NeZero q] (hq : 1 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1)
    {σ : ℝ} (hσ1 : 9/10 < σ) (hσ2 : σ < 1) (y : ℕ) :
    ‖DirichletCharacter.LFunction χ ((σ:ℂ))
      - ((∑ d ∈ Icc 1 y, charFn q χ d * ((d:ℝ)) ^ (-σ) : ℝ) : ℂ)‖
    ≤ 2 * (q:ℝ) * (((y + 1 : ℕ)):ℝ) ^ (-σ) := by
  have hσ0 : (0:ℝ) < σ := by linarith
  -- the running character sum
  set SFn : ℕ → ℝ := fun n => ∑ m ∈ Icc 1 n, charFn q χ m with hSFn
  have hSFn0 : SFn 0 = 0 := by
    rw [hSFn]
    simp
  have hSb : ∀ n : ℕ, |SFn n| ≤ (q:ℝ) := fun n => charFn_partial_sum_bound hq χ hχ2 hχ1 n
  have hSE : ∀ n : ℕ, 1 ≤ n → |SFn n| ≤ (q:ℝ) * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
    intro n hn
    have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have h1 : (1:ℝ) ≤ ((n:ℝ)) ^ ((3:ℝ)/4) := Real.one_le_rpow hn1r (by norm_num)
    have h2 : (1:ℝ) ≤ 1 + Real.log n := by
      have := Real.log_nonneg hn1r
      linarith
    calc |SFn n| ≤ (q:ℝ) := hSb n
      _ = (q:ℝ) * 1 := (mul_one _).symm
      _ ≤ (q:ℝ) * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
          nlinarith [h1, h2]
  -- the Abel continuation W
  set W : ℂ → ℂ := fun s => ∑' n : ℕ,
      ((SFn n : ℝ) : ℂ) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)) with hW
  -- LFunction = W at σ via the identity theorem
  have hLW : DirichletCharacter.LFunction χ ((σ:ℂ)) = W ((σ:ℂ)) := by
    apply eqOn_slit_halfplane (DirichletCharacter.LFunction χ) W
      (fun s _ _ => (DirichletCharacter.differentiable_LFunction hχ1).differentiableAt)
      (fun s hs _ => eseries_differentiableAt SFn ((q:ℝ)) (Nat.cast_nonneg q) hSFn0 hSE s hs)
      ?_ ((σ:ℂ)) (by rw [Complex.ofReal_re]; exact hσ1) (by
        intro h
        rw [Complex.ofReal_eq_one] at h
        linarith)
    intro s hs
    have hsum : LSeriesSummable (fun n => ((charFn q χ n : ℝ) : ℂ)) s := by
      apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
      intro n _
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact charFn_bound χ hχ2 n
    have hC : ∀ x : ℕ, ‖∑ n ∈ Icc 1 x, ((charFn q χ n : ℝ) : ℂ)‖ ≤ (q:ℝ) * x := by
      intro x
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
      rcases Nat.eq_zero_or_pos x with rfl | hx
      · simp
      · have hx1r : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
        calc |∑ n ∈ Icc 1 x, charFn q χ n| ≤ (q:ℝ) :=
              charFn_partial_sum_bound hq χ hχ2 hχ1 x
          _ ≤ (q:ℝ) * x := by nlinarith [Nat.cast_nonneg (α := ℝ) q]
    have hL : DirichletCharacter.LFunction χ s
        = LSeries (fun n => ((charFn q χ n : ℝ) : ℂ)) s := by
      rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
      exact (LSeries_congr (fun {n} hn => charFn_repr χ hχ2 n) s).symm
    rw [hL, lseries_eq_tsum_abel _ ((q:ℝ)) hC hs hsum, hW]
    apply tsum_congr
    intro n
    rw [hSFn, Complex.ofReal_sum]
  -- the direct partial sums converge to W(σ)
  set D : ℕ → ℝ := fun z => ∑ d ∈ Icc 1 z, charFn q χ d * ((d:ℝ)) ^ (-σ) with hD
  have hterm_cast : ∀ d : ℕ, ((charFn q χ d * ((d:ℝ)) ^ (-σ) : ℝ) : ℂ)
      = ((charFn q χ d : ℝ) : ℂ) * ((d:ℂ)) ^ (-((σ:ℝ):ℂ)) := by
    intro d
    rw [cpow_real_cast d σ]
    push_cast
    ring
  -- summability of the W-terms at σ
  have hWsum : Summable (fun n : ℕ =>
      ((SFn n : ℝ) : ℂ) * (((n:ℂ)) ^ (-((σ:ℝ):ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-((σ:ℝ):ℂ)))) := by
    have hmaj : Summable (fun n : ℕ => (q:ℝ) * (1 / ((n:ℝ)) ^ ((19:ℝ)/10))) :=
      Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr (by norm_num))
    have hg0 : ∀ n : ℕ, 0 ≤ (if n = 0 then (0:ℝ) else
        (q:ℝ) * (1 / ((n:ℝ)) ^ ((19:ℝ)/10))) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · rw [if_pos rfl]
      · rw [if_neg hn]
        positivity
    have hgle : ∀ n : ℕ, (if n = 0 then (0:ℝ) else
        (q:ℝ) * (1 / ((n:ℝ)) ^ ((19:ℝ)/10)))
        ≤ (q:ℝ) * (1 / ((n:ℝ)) ^ ((19:ℝ)/10)) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · rw [if_pos rfl]
        positivity
      · rw [if_neg hn]
    apply Summable.of_norm_bounded (g := fun n : ℕ => if n = 0 then 0 else
      (q:ℝ) * (1 / ((n:ℝ)) ^ ((19:ℝ)/10))) (Summable.of_nonneg_of_le hg0 hgle hmaj)
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hSFn0]
      simp
    · rw [if_neg hn]
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      have hn0 : (0:ℝ) < (n:ℝ) := by linarith
      have hΔ : ((n:ℂ)) ^ (-((σ:ℝ):ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-((σ:ℝ):ℂ))
          = (((((n:ℝ)) ^ (-σ) - (((n + 1 : ℕ)):ℝ) ^ (-σ)) : ℝ) : ℂ) := by
        rw [cpow_real_cast n σ, cpow_real_cast (n + 1) σ]
        push_cast
        ring
      rw [hΔ, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have hΔ0 : (0:ℝ) ≤ ((n:ℝ)) ^ (-σ) - (((n + 1 : ℕ)):ℝ) ^ (-σ) := by
        have : (((n + 1 : ℕ)):ℝ) ^ (-σ) ≤ ((n:ℝ)) ^ (-σ) := by
          apply Real.rpow_le_rpow_of_nonpos hn0 (by push_cast; linarith)
          linarith
        linarith
      have hΔle : ((n:ℝ)) ^ (-σ) - (((n + 1 : ℕ)):ℝ) ^ (-σ) ≤ ((n:ℝ)) ^ (-((19:ℝ)/10)) := by
        calc ((n:ℝ)) ^ (-σ) - (((n + 1 : ℕ)):ℝ) ^ (-σ)
            ≤ σ * ((n:ℝ)) ^ (-σ - 1) := rpow_diff_le n hn1 σ hσ0.le
          _ ≤ 1 * ((n:ℝ)) ^ (-σ - 1) := by
              apply mul_le_mul_of_nonneg_right (by linarith)
                (Real.rpow_nonneg hn0.le _)
          _ = ((n:ℝ)) ^ (-σ - 1) := one_mul _
          _ ≤ ((n:ℝ)) ^ (-((19:ℝ)/10)) := by
              apply Real.rpow_le_rpow_of_exponent_le hn1r
              linarith
      have hone : (1:ℝ) / ((n:ℝ)) ^ ((19:ℝ)/10) = ((n:ℝ)) ^ (-((19:ℝ)/10)) := by
        rw [one_div, ← Real.rpow_neg hn0.le]
      rw [abs_of_nonneg hΔ0, hone]
      exact mul_le_mul (hSb n) hΔle hΔ0 (Nat.cast_nonneg q)
  -- boundary decay
  have hbdry : Tendsto (fun z : ℕ => ((SFn z : ℝ) : ℂ) * ((z:ℂ)) ^ (-((σ:ℝ):ℂ)))
      atTop (nhds 0) := by
    have hbound : ∀ z : ℕ, ‖((SFn z : ℝ) : ℂ) * ((z:ℂ)) ^ (-((σ:ℝ):ℂ))‖
        ≤ (q:ℝ) * ((z:ℝ)) ^ (-σ) := by
      intro z
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, cpow_real_cast z σ,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg z) _)]
      exact mul_le_mul_of_nonneg_right (hSb z) (Real.rpow_nonneg (Nat.cast_nonneg z) _)
    have hg : Tendsto (fun z : ℕ => (q:ℝ) * ((z:ℝ)) ^ (-σ)) atTop (nhds 0) := by
      have h := tendsto_rpow_neg_atTop hσ0
      have hcomp := h.comp tendsto_natCast_atTop_atTop
      have h2 := hcomp.const_mul ((q:ℝ))
      simpa [Function.comp_def] using h2
    exact squeeze_zero_norm hbound hg
  -- the Icc-to-range recount of the W-partials
  have hIcc_range : ∀ z : ℕ, ∑ n ∈ Icc 1 (z - 1),
      ((SFn n : ℝ) : ℂ) * (((n:ℂ)) ^ (-((σ:ℝ):ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-((σ:ℝ):ℂ)))
      = ∑ n ∈ range z,
      ((SFn n : ℝ) : ℂ) * (((n:ℂ)) ^ (-((σ:ℝ):ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-((σ:ℝ):ℂ))) := by
    intro z
    rcases Nat.eq_zero_or_pos z with rfl | hz
    · rfl
    · rw [show range z = insert 0 (Icc 1 (z - 1)) from by
        ext d
        simp only [Finset.mem_insert, Finset.mem_range, Finset.mem_Icc]
        omega, Finset.sum_insert (by
          simp only [Finset.mem_Icc]
          omega)]
      rw [hSFn0]
      simp
  have hsum_shift : Tendsto (fun z : ℕ => ∑ n ∈ Icc 1 (z - 1),
      ((SFn n : ℝ) : ℂ) * (((n:ℂ)) ^ (-((σ:ℝ):ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-((σ:ℝ):ℂ))))
      atTop (nhds (W ((σ:ℂ)))) := by
    have h := hWsum.hasSum.tendsto_sum_nat
    apply h.congr
    intro z
    exact (hIcc_range z).symm
  -- the Abel identity links D to the W-partials
  have habel : ∀ z : ℕ, 1 ≤ z → ((D z : ℝ) : ℂ)
      = ((SFn z : ℝ) : ℂ) * ((z:ℂ)) ^ (-((σ:ℝ):ℂ))
        + ∑ n ∈ Icc 1 (z - 1),
          ((SFn n : ℝ) : ℂ) * (((n:ℂ)) ^ (-((σ:ℝ):ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-((σ:ℝ):ℂ))) := by
    intro z hz
    have h := abel_initial (fun n => ((charFn q χ n : ℝ) : ℂ))
      (fun n => ((n:ℂ)) ^ (-((σ:ℝ):ℂ))) z hz
    have hL : ((D z : ℝ) : ℂ) = ∑ n ∈ Icc 1 z,
        ((charFn q χ n : ℝ) : ℂ) * ((n:ℂ)) ^ (-((σ:ℝ):ℂ)) := by
      rw [hD]
      push_cast [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [← hterm_cast d]
      push_cast
      ring
    have hA : ∀ x : ℕ, ∑ m ∈ Icc 1 x, ((charFn q χ m : ℝ) : ℂ) = ((SFn x : ℝ) : ℂ) := by
      intro x
      rw [hSFn, Complex.ofReal_sum]
    rw [hL, h, hA z]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [hA n]
  -- D converges to W(σ)
  have hDW : Tendsto (fun z : ℕ => ((D z : ℝ) : ℂ)) atTop (nhds (W ((σ:ℂ)))) := by
    have h := hbdry.add hsum_shift
    rw [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with z hz
    exact (habel z hz).symm
  -- the tail rate transfers to the limit
  have hrate : ∀ z : ℕ, y ≤ z →
      ‖((D z : ℝ) : ℂ) - ((D y : ℝ) : ℂ)‖ ≤ 2 * (q:ℝ) * (((y + 1 : ℕ)):ℝ) ^ (-σ) := by
    intro z hz
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hsplit : D z - D y = ∑ d ∈ Icc (y + 1) z, charFn q χ d * ((d:ℝ)) ^ (-σ) := by
      rw [hD]
      simp only
      rw [show Icc 1 z = Icc 1 y ∪ Icc (y + 1) z from by
        ext d
        simp only [Finset.mem_union, Finset.mem_Icc]
        omega, Finset.sum_union (by
          rw [Finset.disjoint_left]
          intro d hd hd2
          rw [Finset.mem_Icc] at hd hd2
          omega)]
      ring
    rw [hsplit]
    exact char_rpow_tail_rate_gen hq χ hχ2 hχ1 hσ0.le y z hz
  have hfinal : ‖W ((σ:ℂ)) - ((D y : ℝ) : ℂ)‖ ≤ 2 * (q:ℝ) * (((y + 1 : ℕ)):ℝ) ^ (-σ) := by
    have h2 : Tendsto (fun z : ℕ => ‖((D z : ℝ) : ℂ) - ((D y : ℝ) : ℂ)‖) atTop
        (nhds ‖W ((σ:ℂ)) - ((D y : ℝ) : ℂ)‖) := (hDW.sub tendsto_const_nhds).norm
    apply le_of_tendsto h2
    filter_upwards [eventually_ge_atTop y] with z hz
    exact hrate z hz
  rw [hLW]
  exact hfinal

/-- **The head difference across the window** (Siegel brick S2c): moving the
    exponent from `β` to `1` across a window with `N^{1−β} ≤ 2` costs only
    `2(1−β)(1+log N)²` on partial sums of a quadratic character. -/
lemma char_head_diff_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    (N : ℕ) (hN : 1 ≤ N) {β : ℝ} (hβ1 : 0 < β) (hβ2 : β < 1)
    (hN2 : ((N:ℝ)) ^ (1 - β) ≤ 2) :
    |∑ d ∈ Icc 1 N, charFn q χ d / d - ∑ d ∈ Icc 1 N, charFn q χ d * ((d:ℝ)) ^ (-β)|
    ≤ 2 * (1 - β) * (1 + Real.log N) ^ 2 := by
  have hNr : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlogN : (0:ℝ) ≤ Real.log N := Real.log_nonneg hNr
  -- per-term bound
  have hterm : ∀ d : ℕ, d ∈ Icc 1 N →
      |charFn q χ d / d - charFn q χ d * ((d:ℝ)) ^ (-β)|
      ≤ 2 * (1 - β) * (Real.log d / d) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd1r : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd.1
    have hd0 : (0:ℝ) < (d:ℝ) := by linarith
    have hlogd : (0:ℝ) ≤ Real.log d := Real.log_nonneg hd1r
    -- factor: 1/d − d^{−β} = −d^{−1}(d^{1−β} − 1)
    have hfac : charFn q χ d / d - charFn q χ d * ((d:ℝ)) ^ (-β)
        = -(charFn q χ d * (((d:ℝ)) ^ (1 - β) - 1) / d) := by
      have hrw : ((d:ℝ)) ^ (-β) = ((d:ℝ)) ^ (1 - β) / d := by
        rw [eq_div_iff (ne_of_gt hd0)]
        calc ((d:ℝ)) ^ (-β) * (d:ℝ) = ((d:ℝ)) ^ (-β) * ((d:ℝ)) ^ (1:ℝ) := by
              rw [Real.rpow_one]
          _ = ((d:ℝ)) ^ (-β + 1) := (Real.rpow_add hd0 _ _).symm
          _ = ((d:ℝ)) ^ (1 - β) := by ring_nf
      rw [hrw]
      field_simp
      ring
    rw [hfac, abs_neg, abs_div, Nat.abs_cast, abs_mul]
    -- d^{1−β} − 1 ≤ 2(1−β)log d
    have hexp : ((d:ℝ)) ^ (1 - β) - 1 ≤ 2 * (1 - β) * Real.log d := by
      have h1β : (0:ℝ) ≤ 1 - β := by linarith
      have hx0 : (0:ℝ) ≤ (1 - β) * Real.log d := mul_nonneg h1β hlogd
      have hrpow : ((d:ℝ)) ^ (1 - β) = Real.exp ((1 - β) * Real.log d) := by
        rw [Real.rpow_def_of_pos hd0]
        ring_nf
      have hEM : Real.exp ((1 - β) * Real.log d) - 1
          ≤ ((1 - β) * Real.log d) * Real.exp ((1 - β) * Real.log d) := by
        set x : ℝ := (1 - β) * Real.log d with hx
        have h1 := Real.add_one_le_exp (-x)
        have h2 : (0:ℝ) < Real.exp x := Real.exp_pos _
        have h3 : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
        rw [h3] at h1
        have h4 : (-x + 1) * Real.exp x ≤ 1 := by
          calc (-x + 1) * Real.exp x ≤ (Real.exp x)⁻¹ * Real.exp x := by
                apply mul_le_mul_of_nonneg_right h1 h2.le
            _ = 1 := inv_mul_cancel₀ (ne_of_gt h2)

        nlinarith [h4]
      have hd2 : ((d:ℝ)) ^ (1 - β) ≤ 2 := by
        calc ((d:ℝ)) ^ (1 - β) ≤ ((N:ℝ)) ^ (1 - β) := by
              apply Real.rpow_le_rpow hd0.le _ h1β
              exact_mod_cast hd.2
          _ ≤ 2 := hN2
      calc ((d:ℝ)) ^ (1 - β) - 1
          = Real.exp ((1 - β) * Real.log d) - 1 := by rw [hrpow]
        _ ≤ ((1 - β) * Real.log d) * Real.exp ((1 - β) * Real.log d) := hEM
        _ = ((1 - β) * Real.log d) * ((d:ℝ)) ^ (1 - β) := by rw [hrpow]
        _ ≤ ((1 - β) * Real.log d) * 2 := by
            apply mul_le_mul_of_nonneg_left hd2 hx0
        _ = 2 * (1 - β) * Real.log d := by ring
    have hnn : (0:ℝ) ≤ ((d:ℝ)) ^ (1 - β) - 1 := by
      have : (1:ℝ) ≤ ((d:ℝ)) ^ (1 - β) := Real.one_le_rpow hd1r (by linarith)
      linarith
    calc |charFn q χ d| * |((d:ℝ)) ^ (1 - β) - 1| / (d:ℝ)
        ≤ 1 * (2 * (1 - β) * Real.log d) / (d:ℝ) := by
          apply div_le_div_of_nonneg_right _ hd0.le
          apply mul_le_mul (charFn_bound χ hχ2 d) _ (abs_nonneg _) zero_le_one
          rw [abs_of_nonneg hnn]
          exact hexp
      _ = 2 * (1 - β) * (Real.log d / d) := by ring
  -- sum the per-term bounds
  have hsum : ∑ d ∈ Icc 1 N, Real.log d / d ≤ (1 + Real.log N) ^ 2 := by
    calc ∑ d ∈ Icc 1 N, Real.log d / d
        ≤ ∑ d ∈ Icc 1 N, Real.log N * (1 / d) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          have hd0 : (0:ℝ) < (d:ℝ) := by
            have : (0:ℕ) < d := by omega
            exact_mod_cast this
          have hlog_le : Real.log d ≤ Real.log N := by
            apply Real.log_le_log hd0
            exact_mod_cast hd.2
          rw [mul_one_div]
          apply div_le_div_of_nonneg_right hlog_le hd0.le
      _ = Real.log N * ∑ d ∈ Icc 1 N, (1:ℝ) / d := by rw [Finset.mul_sum]
      _ ≤ Real.log N * (1 + Real.log N) := by
          apply mul_le_mul_of_nonneg_left (sum_one_div_le_log N hN) hlogN
      _ ≤ (1 + Real.log N) ^ 2 := by nlinarith [hlogN]
  calc |∑ d ∈ Icc 1 N, charFn q χ d / d - ∑ d ∈ Icc 1 N, charFn q χ d * ((d:ℝ)) ^ (-β)|
      = |∑ d ∈ Icc 1 N, (charFn q χ d / d - charFn q χ d * ((d:ℝ)) ^ (-β))| := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ d ∈ Icc 1 N, |charFn q χ d / d - charFn q χ d * ((d:ℝ)) ^ (-β)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 N, 2 * (1 - β) * (Real.log d / d) := Finset.sum_le_sum hterm
    _ = 2 * (1 - β) * ∑ d ∈ Icc 1 N, Real.log d / d := by rw [Finset.mul_sum]
    _ ≤ 2 * (1 - β) * (1 + Real.log N) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hsum
        nlinarith [hβ2]

/-- **THE ZERO-GAP BRIDGE** (Siegel brick S2d): a real zero `β` of `L(·,χ)` inside
    the window `(1−β)·log q ≤ 1/10` forces the `L(1,χ)`-limit small:
    `|L₁| ≤ 2(1−β)(1+3log q)² + 4q^{−17/10}` — so a big `L(1,χ)` pushes zeros away. -/
theorem zero_gap_bridge {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1)
    (L₁ : ℝ)
    (hr : ∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, charFn q χ d / d| ≤ 2 * (q:ℝ) / (y + 1))
    {β : ℝ} (hβ2 : β < 1) (hβw : (1 - β) * Real.log q ≤ 1/10)
    (hzero : DirichletCharacter.LFunction χ ((β:ℂ)) = 0) :
    |L₁| ≤ 2 * (1 - β) * (1 + 3 * Real.log q) ^ 2 + 4 * ((q:ℝ)) ^ (-(17:ℝ)/10) := by
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0:ℝ) < (q:ℝ) := by
    have : (0:ℕ) < q := by omega
    exact_mod_cast this
  have hq3r : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  -- log q > 1
  have hlogq1 : (1:ℝ) < Real.log q := by
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
      _ ≤ Real.log q := Real.log_le_log (by norm_num) hq3r
  have hβ910 : (9:ℝ)/10 < β := by
    have h1 : 1 - β ≤ (1/10) / Real.log q := by
      rw [le_div_iff₀ (by linarith)]
      linarith [hβw]
    have h2 : (1/10 : ℝ) / Real.log q < 1/10 := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith [hlogq1]
    linarith
  have hβ0 : (0:ℝ) < β := by linarith
  set N : ℕ := q ^ 3 with hN
  have hN1 : 1 ≤ N := Nat.one_le_pow 3 q (by omega)
  have hNr : ((N:ℕ):ℝ) = ((q:ℝ)) ^ (3:ℕ) := by
    rw [hN]
    push_cast
    ring
  have hlogN : Real.log N = 3 * Real.log q := by
    rw [hNr, Real.log_pow]
    push_cast
    ring
  -- N^{1−β} ≤ 2
  have hN2 : ((N:ℝ)) ^ (1 - β) ≤ 2 := by
    have hN0 : (0:ℝ) < (N:ℝ) := by
      rw [hNr]
      positivity
    rw [Real.rpow_def_of_pos hN0]
    calc Real.exp (Real.log ((N:ℝ)) * (1 - β)) ≤ Real.exp (3/10) := by
          apply Real.exp_le_exp.mpr
          rw [hlogN]
          nlinarith [hβw]
      _ ≤ 2 := by
          have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
          calc Real.exp (3/10) ≤ Real.exp (Real.log 2) := by
                apply Real.exp_le_exp.mpr
                linarith
            _ = 2 := Real.exp_log (by norm_num)
  set D1 : ℝ := ∑ d ∈ Icc 1 N, charFn q χ d / d with hD1
  set Dβ : ℝ := ∑ d ∈ Icc 1 N, charFn q χ d * ((d:ℝ)) ^ (-β) with hDβ
  -- piece (a): |L₁ − D_N(1)| ≤ 2q^{−17/10}
  have ha : |L₁ - D1| ≤ 2 * ((q:ℝ)) ^ (-(17:ℝ)/10) := by
    calc |L₁ - D1| ≤ 2 * (q:ℝ) / ((N:ℝ) + 1) := hr N
      _ ≤ 2 * (q:ℝ) / ((q:ℝ)) ^ (3:ℕ) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          rw [hNr]
          linarith
      _ = 2 * ((q:ℝ)) ^ (-(2:ℝ)) := by
          rw [show (-(2:ℝ)) = -(((2:ℕ)):ℝ) from by norm_num, Real.rpow_neg hq0.le,
            Real.rpow_natCast]
          field_simp
      _ ≤ 2 * ((q:ℝ)) ^ (-(17:ℝ)/10) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.rpow_le_rpow_of_exponent_le (by linarith)
          norm_num
  -- piece (b): the head difference
  have hb : |D1 - Dβ| ≤ 2 * (1 - β) * (1 + 3 * Real.log q) ^ 2 := by
    have h := char_head_diff_bound χ hχ2 N hN1 hβ0 hβ2 hN2
    rw [hlogN] at h
    exact h
  -- piece (c): |D_N(β)| ≤ 2q^{−17/10} at the zero
  have hc : |Dβ| ≤ 2 * ((q:ℝ)) ^ (-(17:ℝ)/10) := by
    have h1 := LFunction_partial_rate_below_one hq1 χ hχ2 hχ1 hβ910 hβ2 N
    rw [hzero, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs] at h1
    have hN0 : (0:ℝ) < (N:ℝ) := by
      rw [hNr]
      positivity
    have h2 : (((N + 1 : ℕ)):ℝ) ^ (-β) ≤ ((N:ℝ)) ^ (-β) := by
      apply Real.rpow_le_rpow_of_nonpos hN0 (by push_cast; linarith)
      linarith
    have hq1r : (1:ℝ) ≤ (q:ℝ) := by linarith
    have h4 : ((N:ℝ)) ^ (-β) = ((q:ℝ)) ^ ((3:ℝ) * (-β)) := by
      rw [hNr, ← Real.rpow_natCast (q:ℝ) 3, ← Real.rpow_mul hq0.le]
      congr 1
    have h5 : (q:ℝ) * ((q:ℝ)) ^ ((3:ℝ) * (-β)) = ((q:ℝ)) ^ (1 + (3:ℝ) * (-β)) := by
      rw [Real.rpow_add hq0, Real.rpow_one]
    have h6 : ((q:ℝ)) ^ (1 + (3:ℝ) * (-β)) ≤ ((q:ℝ)) ^ (-(17:ℝ)/10) := by
      apply Real.rpow_le_rpow_of_exponent_le hq1r
      nlinarith [hβ910]
    calc |Dβ| ≤ 2 * (q:ℝ) * (((N + 1 : ℕ)):ℝ) ^ (-β) := h1
      _ ≤ 2 * (q:ℝ) * ((N:ℝ)) ^ (-β) := by
          apply mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * ((q:ℝ) * ((q:ℝ)) ^ ((3:ℝ) * (-β))) := by
          rw [h4]
          ring
      _ = 2 * ((q:ℝ)) ^ (1 + (3:ℝ) * (-β)) := by rw [h5]
      _ ≤ 2 * ((q:ℝ)) ^ (-(17:ℝ)/10) := by
          apply mul_le_mul_of_nonneg_left h6 (by norm_num)
  -- triangle assembly
  have h1 := abs_add_le (L₁ - D1) (D1 - Dβ)
  have e1 : (L₁ - D1) + (D1 - Dβ) = L₁ - Dβ := by ring
  rw [e1] at h1
  have h2 := abs_add_le (L₁ - Dβ) Dβ
  have e2 : (L₁ - Dβ) + Dβ = L₁ := by ring
  rw [e2] at h2
  linarith [h1, h2, ha, hb, hc]

/-- **The explicit-C E-package** (Siegel brick S3-pre-a): `quad_E_package` with the
    constant exposed — `C = 30(1+q₁)(1+B) + 36 + 3|L₁Lk|`, ready for the
    polynomial-in-`q` bound the dichotomy needs. -/
theorem quad_E_package_explicit (g₁ g₂ : ℕ → ℝ) (q₁ B L₁ Lk : ℝ)
    (h1b : ∀ n, |g₁ n| ≤ 1) (h2b : ∀ n, |g₂ n| ≤ 1)
    (hL₁ : ∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, g₁ d / d| ≤ 2 * q₁ / (y + 1))
    (hq₁ : 0 ≤ q₁)
    (hH : ∀ M : ℕ, 1 ≤ M →
      |∑ n ∈ Icc 1 M, (toArith (fun _ => (1:ℝ)) * toArith g₁) n - L₁ * M|
        ≤ (1 + 4 * q₁) * (Real.sqrt M + 1))
    (hKb : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (toArith g₂ * toArith (fun m => g₁ m * g₂ m)) n|
        ≤ B * (Real.sqrt t + 1))
    (hLk : ∀ y : ℕ, 1 ≤ y →
      |Lk - ∑ d ∈ Icc 1 y, (toArith g₂ * toArith (fun m => g₁ m * g₂ m)) d / d|
        ≤ 7 * B / Real.sqrt y) :
    ∀ n : ℕ, 1 ≤ n →
      |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
          * toArith (fun k => g₁ k * g₂ k)) m - L₁ * Lk * n|
        ≤ (30 * (1 + q₁) * (1 + B) + 36 + 3 * |L₁ * Lk|)
          * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
  have hB0 : 0 ≤ B := by
    have h0 := hKb 0
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, abs_zero,
      Nat.cast_zero, Real.sqrt_zero, zero_add, mul_one] at h0
    exact h0
  intro n hn
  have hn0 : (0:ℝ) < (n:ℝ) := by
    have : (0:ℕ) < n := hn
    exact_mod_cast this
  have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have htge1 : (1:ℝ) ≤ ((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n) := by
    have h1 : (1:ℝ) ≤ ((n:ℝ)) ^ ((3:ℝ)/4) := Real.one_le_rpow hn1r (by norm_num)
    have h2 : (1:ℝ) ≤ 1 + Real.log n := by
      have := Real.log_nonneg hn1r
      linarith
    nlinarith [h1, h2]
  have ht0 : (0:ℝ) ≤ ((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n) := by linarith
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · -- n ∈ {1, 2, 3}: cube bound
    have hA : |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun k => g₁ k * g₂ k)) m| ≤ 36 := by
      calc |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
            * toArith (fun k => g₁ k * g₂ k)) m|
          ≤ ∑ m ∈ Icc 1 n, |(toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
            * toArith (fun k => g₁ k * g₂ k)) m| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Icc 1 n, ((m:ℝ)) ^ (3:ℕ) :=
            Finset.sum_le_sum (fun m _ => quad_value_le_cube g₁ g₂ h1b h2b m)
        _ ≤ ∑ m ∈ Icc (1:ℕ) 3, ((m:ℝ)) ^ (3:ℕ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro m hm
              rw [Finset.mem_Icc] at hm ⊢
              omega
            · intro m _ _
              positivity
        _ = 36 := by
            rw [show (Icc (1:ℕ) 3 : Finset ℕ) = {1, 2, 3} by decide]
            norm_num [Finset.sum_insert, Finset.mem_insert, Finset.sum_singleton]
    have h3n : (n:ℝ) ≤ 3 := by
      have : n ≤ 3 := by omega
      exact_mod_cast this
    have hlam : |L₁ * Lk| * (n:ℝ) ≤ 3 * |L₁ * Lk| := by
      nlinarith [abs_nonneg (L₁ * Lk), h3n]
    have htri : |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun k => g₁ k * g₂ k)) m - L₁ * Lk * n|
        ≤ |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
            * toArith (fun k => g₁ k * g₂ k)) m| + |L₁ * Lk * (n:ℝ)| := by
      have h := abs_add_le (∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁
          * toArith g₂ * toArith (fun k => g₁ k * g₂ k)) m) (-(L₁ * Lk * (n:ℝ)))
      rw [abs_neg, ← sub_eq_add_neg] at h
      exact h
    have habsmul : |L₁ * Lk * (n:ℝ)| = |L₁ * Lk| * (n:ℝ) := by
      rw [abs_mul, Nat.abs_cast]
    calc |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
          * toArith (fun k => g₁ k * g₂ k)) m - L₁ * Lk * n|
        ≤ 36 + 3 * |L₁ * Lk| := by
          rw [habsmul] at htri
          linarith [htri, hA, hlam]
      _ = (36 + 3 * |L₁ * Lk|) * 1 := (mul_one _).symm
      _ ≤ (36 + 3 * |L₁ * Lk|) * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
          apply mul_le_mul_of_nonneg_left htge1 (by positivity)
      _ ≤ (30 * (1 + q₁) * (1 + B) + 36 + 3 * |L₁ * Lk|)
            * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
          apply mul_le_mul_of_nonneg_right _ ht0
          nlinarith [hq₁, hB0]
  · -- n ≥ 4: the hyperbola asymptotic
    have hmain := quad_coeff_asymptotic g₁ g₂ q₁ B L₁ Lk h1b h2b hL₁ hq₁ hH hKb hLk n h4
    have hconv : Real.sqrt n * Real.sqrt (Real.sqrt n) = ((n:ℝ)) ^ ((3:ℝ)/4) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
      norm_num
    rw [hconv] at hmain
    calc |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
          * toArith (fun k => g₁ k * g₂ k)) m - L₁ * Lk * n|
        ≤ 30 * (1 + q₁) * (1 + B) * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := hmain
      _ ≤ (30 * (1 + q₁) * (1 + B) + 36 + 3 * |L₁ * Lk|)
            * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
          apply mul_le_mul_of_nonneg_right _ ht0
          nlinarith [abs_nonneg (L₁ * Lk)]

/-- **The bounded character quad system** (Siegel brick S3-pre-b):
    `quad_system_for_chars` with the constant polynomially controlled:
    `C ≤ 1000(1+q₁)²(1+q₂)²` — the shape the dichotomy's `x`-choice requires. -/
theorem quad_system_for_chars_bounded {q₁ q₂ : ℕ} (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂)
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1) :
    ∃ L₁ Lk C : ℝ,
      (∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, charFn q₁ χ₁ d / d| ≤ 2 * (q₁:ℝ) / (y + 1))
      ∧ (∀ y : ℕ, 1 ≤ y →
          |Lk - ∑ d ∈ Icc 1 y, (toArith (charFn q₂ χ₂)
              * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d / d|
            ≤ 7 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) / Real.sqrt y)
      ∧ 0 ≤ C
      ∧ C ≤ 1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2
      ∧ ∀ n : ℕ, 1 ≤ n →
        |∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
            * toArith (charFn q₂ χ₂)
            * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m - L₁ * Lk * n|
          ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
  have h1b := fun n => charFn_bound χ₁ hχ₁2 n
  have h2b := fun n => charFn_bound χ₂ hχ₂2 n
  have hG₁ := charFn_partial_sum_bound hq₁ χ₁ hχ₁2 hχ₁1
  have hG₂ := charFn_partial_sum_bound hq₂ χ₂ hχ₂2 hχ₂1
  obtain ⟨L₁, hL₁⟩ := log_mean_exists (charFn q₁ χ₁) ((q₁:ℝ)) hG₁
  have hH : ∀ M : ℕ, 1 ≤ M →
      |∑ n ∈ Icc 1 M, (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)) n - L₁ * M|
        ≤ (1 + 4 * (q₁:ℝ)) * (Real.sqrt M + 1) := by
    intro M hM
    have hcomm : toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
        = toArith (charFn q₁ χ₁) * toArith (fun _ => (1:ℝ)) := mul_comm _ _
    rw [hcomm]
    exact divisor_char_asymptotic (charFn q₁ χ₁) ((q₁:ℝ)) L₁ h1b hG₁ hL₁ M hM
  have hχ₃2 : ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
      * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ^ 2 = 1 := by
    rw [mul_pow, ← map_pow, ← map_pow, hχ₁2, hχ₂2, map_one, map_one, mul_one]
  have hq₁₂ : 1 ≤ q₁ * q₂ :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hG₃ := charFn_partial_sum_bound hq₁₂ _ hχ₃2 hχ₃1
  have h12b : ∀ n, |charFn q₁ χ₁ n * charFn q₂ χ₂ n| ≤ 1 := by
    intro n
    rw [abs_mul]
    calc |charFn q₁ χ₁ n| * |charFn q₂ χ₂ n| ≤ 1 * 1 :=
        mul_le_mul (h1b n) (h2b n) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hK2 : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (charFn q₁ χ₁ n * charFn q₂ χ₂ n)|
      ≤ (q₁:ℝ) * (q₂:ℝ) := by
    intro t
    have heq : ∑ n ∈ Icc 1 t, (charFn q₁ χ₁ n * charFn q₂ χ₂ n)
        = ∑ n ∈ Icc 1 t, charFn (q₁ * q₂)
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) n :=
      Finset.sum_congr rfl (fun n _ => (charFn_mul_char χ₁ χ₂ hχ₁2 hχ₂2 n).symm)
    rw [heq]
    have h := hG₃ t
    push_cast at h
    exact h
  have hKb : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (toArith (charFn q₂ χ₂)
      * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) n|
      ≤ (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) * (Real.sqrt t + 1) :=
    fun t => bounded_conv_sqrt_bound (charFn q₂ χ₂)
      (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m) ((q₂:ℝ)) ((q₁:ℝ) * (q₂:ℝ))
      h2b h12b hG₂ hK2 t
  obtain ⟨Lk, hLk⟩ := sqrt_mean_exists
    (fun d => (toArith (charFn q₂ χ₂)
      * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d)
    (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) hKb
  have hE := quad_E_package_explicit (charFn q₁ χ₁) (charFn q₂ χ₂)
    ((q₁:ℝ)) (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) L₁ Lk h1b h2b hL₁
    (by positivity) hH hKb hLk
  refine ⟨L₁, Lk, 30 * (1 + (q₁:ℝ)) * (1 + (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ))) + 36
    + 3 * |L₁ * Lk|, hL₁, hLk, by positivity, ?_, hE⟩
  -- the polynomial bound
  have ha1 : (1:ℝ) ≤ (q₁:ℝ) := by exact_mod_cast hq₁
  have hb1 : (1:ℝ) ≤ (q₂:ℝ) := by exact_mod_cast hq₂
  have hL1u : |L₁| ≤ 3 + Real.log q₁ :=
    rate_limit_upper_log (charFn q₁ χ₁) q₁ hq₁ L₁ h1b hL₁
  have hLku : |Lk| ≤ 7 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) + 1 :=
    sqrt_rate_limit_upper (charFn q₂ χ₂)
      (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)
      (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) Lk h2b h12b hLk
  have hlogq : Real.log q₁ ≤ (q₁:ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (q₁:ℝ) by linarith)
    linarith
  have hprod : |L₁ * Lk| ≤ (3 + (q₁:ℝ)) * (7 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) + 1) := by
    rw [abs_mul]
    apply mul_le_mul _ hLku (abs_nonneg _) (by linarith)
    calc |L₁| ≤ 3 + Real.log q₁ := hL1u
      _ ≤ 3 + (q₁:ℝ) := by linarith
  set a : ℝ := (q₁:ℝ) with hadef
  set b : ℝ := (q₂:ℝ) with hbdef
  have hab : (1:ℝ) ≤ a * b := by nlinarith
  nlinarith [hprod, ha1, hb1, hab, sq_nonneg (a - b), sq_nonneg (a + b),
    sq_nonneg ((a + 1) * (b + 1)), mul_pos (show (0:ℝ) < a + 1 by linarith)
      (show (0:ℝ) < b + 1 by linarith),
    mul_nonneg (mul_nonneg (show (0:ℝ) ≤ a by linarith) (show (0:ℝ) ≤ b by linarith))
      (show (0:ℝ) ≤ a by linarith),
    mul_nonneg (mul_nonneg (show (0:ℝ) ≤ a by linarith) (show (0:ℝ) ≤ b by linarith))
      (show (0:ℝ) ≤ b by linarith),
    sq_nonneg (a * b - 1), sq_nonneg (a * b + 1)]

/-- **The bounded λ lower bound at characters** (Siegel brick S3a):
    `siegel_lambda_lower_for_chars` with `C ≤ 1000(1+q₁)²(1+q₂)²` carried along. -/
theorem siegel_lambda_lower_for_chars_bounded {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1)
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1)
    (hzero : DirichletCharacter.LFunction χ₁ ((β:ℂ)) = 0) :
    ∃ L₁ Lk C : ℝ, 0 ≤ L₁ * Lk ∧ 0 ≤ C
      ∧ C ≤ 1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2
      ∧ (∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, charFn q₁ χ₁ d / d| ≤ 2 * (q₁:ℝ) / (y + 1))
      ∧ (∀ y : ℕ, 1 ≤ y →
          |Lk - ∑ d ∈ Icc 1 y, (toArith (charFn q₂ χ₂)
              * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d / d|
            ≤ 7 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) / Real.sqrt y)
      ∧ ∀ x : ℕ, 2 ≤ x → ((820 * (C + 1)) ^ (40:ℕ) : ℝ) ≤ (x:ℝ) →
          1 - β ≤ 26 * (L₁ * Lk) * ((x:ℝ)) ^ (1 - β) := by
  have hq₁ : 1 ≤ q₁ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)
  have hq₂ : 1 ≤ q₂ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₂)
  obtain ⟨L₁, Lk, C, hr1, hr2, hC0, hCB, hEsys⟩ :=
    quad_system_for_chars_bounded hq₁ hq₂ χ₁ χ₂ hχ₁2 hχ₂2 hχ₁1 hχ₂1 hχ₃1
  obtain ⟨ha0, ha1⟩ := quad_conv_nonneg (charFn q₁ χ₁) (charFn q₂ χ₂)
    (charFn_mul χ₁ hχ₁2) (charFn_mul χ₂ hχ₂2)
    (charFn_one χ₁) (charFn_one χ₂)
    (charFn_values χ₁ hχ₁2) (charFn_values χ₂ hχ₂2)
  have h1b := fun n => charFn_bound χ₁ hχ₁2 n
  have h2b := fun n => charFn_bound χ₂ hχ₂2 n
  -- the E-function and its properties
  have hA0 : ∀ n : ℕ, 0 ≤ ∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ))
      * toArith (charFn q₁ χ₁) * toArith (charFn q₂ χ₂)
      * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m :=
    fun n => Finset.sum_nonneg (fun m _ => ha0 m)
  have hlam : 0 ≤ L₁ * Lk := by
    apply lam_nonneg (fun n => ∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ))
        * toArith (charFn q₁ χ₁) * toArith (charFn q₂ χ₂)
        * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m)
      (L₁ * Lk) C hC0 hA0
    intro n hn
    exact hEsys n hn
  refine ⟨L₁, Lk, C, hlam, hC0, hCB, hr1, hr2, ?_⟩
  intro x hx hxC
  apply siegel_lambda_lower
    (fun n => (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
      * toArith (charFn q₂ χ₂)
      * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) n)
    (L₁ * Lk)
    (fun n => (∑ m ∈ Icc 1 n, (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
      * toArith (charFn q₂ χ₂)
      * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m) - L₁ * Lk * n)
    C ha0 ha1 hlam
    (fun n => by ring)
    hC0
    (by
      show (∑ m ∈ Icc 1 0, (toArith (fun _ => (1:ℝ)) * toArith (charFn q₁ χ₁)
        * toArith (charFn q₂ χ₂)
        * toArith (fun k => charFn q₁ χ₁ k * charFn q₂ χ₂ k)) m) - L₁ * Lk * (0:ℕ) = 0
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, Nat.cast_zero, mul_zero,
        sub_zero])
    (fun n hn => hEsys n hn)
    (fun s hs => quad_LSeriesSummable (charFn q₁ χ₁) (charFn q₂ χ₂) h1b h2b hs)
    (fun w => riemannZeta w * DirichletCharacter.LFunction χ₁ w
      * DirichletCharacter.LFunction χ₂ w
      * DirichletCharacter.LFunction
          ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
            * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) w)
    (fun s _ hs1 => quad_P_differentiableAt χ₁ χ₂ hχ₁1 hχ₂1 hχ₃1 s hs1)
    (fun s hs => quad_P_identity χ₁ χ₂ hχ₁2 hχ₂2 hs)
    hβ1 hβ2
    (by
      show riemannZeta ((β:ℂ)) * DirichletCharacter.LFunction χ₁ ((β:ℂ))
        * DirichletCharacter.LFunction χ₂ ((β:ℂ))
        * DirichletCharacter.LFunction
            ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
              * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ((β:ℂ)) = 0
      rw [hzero, mul_zero, zero_mul, zero_mul])
    x hx hxC

/-- **The λ lower bound with the concrete truncation** (Siegel brick S3b): with
    `M := 2(820(1000(1+q₁)²(1+q₂)²+1))^{40}`, a vanishing `L(β,χ₁)` at real
    `β ∈ (9/10,1)` forces `1−β ≤ 26·λ·M^{1−β}` — every quantity closed-form in
    the moduli. -/
theorem siegel_lambda_lower_concrete {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1)
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1)
    (hzero : DirichletCharacter.LFunction χ₁ ((β:ℂ)) = 0) :
    ∃ L₁ Lk : ℝ, 0 ≤ L₁ * Lk
      ∧ (∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, charFn q₁ χ₁ d / d| ≤ 2 * (q₁:ℝ) / (y + 1))
      ∧ (∀ y : ℕ, 1 ≤ y →
          |Lk - ∑ d ∈ Icc 1 y, (toArith (charFn q₂ χ₂)
              * toArith (fun m => charFn q₁ χ₁ m * charFn q₂ χ₂ m)) d / d|
            ≤ 7 * (2 * (q₂:ℝ) + (q₁:ℝ) * (q₂:ℝ)) / Real.sqrt y)
      ∧ 1 - β ≤ 26 * (L₁ * Lk)
          * ((2 * (820 * (1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 + 1))
              ^ ((40:ℝ)))) ^ (1 - β) := by
  obtain ⟨L₁, Lk, C, hlam, hC0, hCB, hr1, hr2, hmain⟩ :=
    siegel_lambda_lower_for_chars_bounded χ₁ χ₂ hχ₁2 hχ₂2 hχ₁1 hχ₂1 hχ₃1 hβ1 hβ2 hzero
  obtain ⟨CQ, hCQ⟩ : ∃ CQ : ℝ,
      CQ = 1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have hq1r : (1:ℝ) ≤ (q₁:ℝ) := by
    have : (1:ℕ) ≤ q₁ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)
    exact_mod_cast this
  have hq2r : (1:ℝ) ≤ (q₂:ℝ) := by
    have : (1:ℕ) ≤ q₂ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₂)
    exact_mod_cast this
  have hCQ4 : (4000:ℝ) ≤ CQ := by
    rw [hCQ]
    have h3 : (4:ℝ) ≤ ((q₁:ℝ) + 1) ^ 2 := by nlinarith [hq1r]
    have h4 : (4:ℝ) ≤ ((q₂:ℝ) + 1) ^ 2 := by nlinarith [hq2r]
    nlinarith [h3, h4]
  have hCB' : C ≤ CQ := by
    rw [hCQ]
    exact hCB
  have hbase1 : (1:ℝ) ≤ 820 * (CQ + 1) := by nlinarith [hCQ4]
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = (820 * (CQ + 1)) ^ ((40:ℝ)) := ⟨_, rfl⟩
  have hX4 : (4:ℝ) ≤ X := by
    rw [hXdef]
    calc (4:ℝ) ≤ 820 * (CQ + 1) := by nlinarith [hCQ4]
      _ = (820 * (CQ + 1)) ^ ((1:ℝ)) := (Real.rpow_one _).symm
      _ ≤ (820 * (CQ + 1)) ^ ((40:ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hbase1 (by norm_num)
  obtain ⟨x, hxdef⟩ : ∃ x : ℕ, x = Nat.ceil X + 2 := ⟨_, rfl⟩
  have hx2 : 2 ≤ x := by
    rw [hxdef]
    omega
  have hxge : X ≤ (x:ℝ) := by
    rw [hxdef]
    push_cast
    linarith [Nat.le_ceil X]
  have hxM : (x:ℝ) ≤ 2 * X := by
    rw [hxdef]
    push_cast
    have hceil := Nat.ceil_lt_add_one (show (0:ℝ) ≤ X by linarith)
    linarith [hX4]
  have hxC : ((820 * (C + 1)) ^ (40:ℕ) : ℝ) ≤ (x:ℝ) := by
    have h1 : ((820 * (C + 1)) ^ (40:ℕ) : ℝ) ≤ X := by
      rw [hXdef, show ((820 * (C + 1)) ^ (40:ℕ) : ℝ)
          = (820 * (C + 1)) ^ (((40:ℕ)):ℝ) from (Real.rpow_natCast _ 40).symm]
      rw [show (((40:ℕ)):ℝ) = (40:ℝ) from by norm_num]
      exact Real.rpow_le_rpow (by positivity) (by linarith [hCB']) (by norm_num)
    linarith
  have hstep := hmain x hx2 hxC
  have hβ0 : (0:ℝ) ≤ 1 - β := by linarith
  have hxpos : (0:ℝ) < (x:ℝ) := by
    have h1 : (0:ℕ) < x := by omega
    exact_mod_cast h1
  have hrpow : ((x:ℝ)) ^ (1 - β) ≤ ((2 * X : ℝ)) ^ (1 - β) :=
    Real.rpow_le_rpow hxpos.le hxM hβ0
  refine ⟨L₁, Lk, hlam, hr1, hr2, ?_⟩
  have hfinal : 1 - β ≤ 26 * (L₁ * Lk) * ((2 * X : ℝ)) ^ (1 - β) := by
    calc 1 - β ≤ 26 * (L₁ * Lk) * ((x:ℝ)) ^ (1 - β) := hstep
      _ ≤ 26 * (L₁ * Lk) * ((2 * X : ℝ)) ^ (1 - β) := by
          apply mul_le_mul_of_nonneg_left hrpow
          nlinarith [hlam]
  rw [hXdef, hCQ] at hfinal
  exact hfinal

/-- **The `L(1,χ₂)` lower bound at an exceptional zero** (Siegel brick S3c-a):
    a zero `β` of `L(·,χ₁)` in `(9/10,1)` forces, for every companion `χ₂`,
    `|ℓ₂| ≥ (1−β) / (26·M^{1−β}·(3+log q₁)(3+log q₁q₂))` where `ℓ₂` is the real
    value of `L(1,χ₂)` with its Abel rate — the quantity the zero-gap bridge eats. -/
theorem L_one_chi2_lower {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1)
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1)
    (hzero : DirichletCharacter.LFunction χ₁ ((β:ℂ)) = 0) :
    ∃ ℓ₂ : ℝ,
      (∀ y : ℕ, |ℓ₂ - ∑ d ∈ Icc 1 y, charFn q₂ χ₂ d / d| ≤ 2 * (q₂:ℝ) / (y + 1))
      ∧ DirichletCharacter.LFunction χ₂ 1 = ((ℓ₂ : ℝ) : ℂ)
      ∧ (1 - β) / (26 * ((2 * (820 * (1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 + 1))
              ^ ((40:ℝ)))) ^ (1 - β)
            * (3 + Real.log q₁) * (3 + Real.log (q₁ * q₂ : ℕ)))
          ≤ |ℓ₂| := by
  have hq₁ : 1 ≤ q₁ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)
  have hq₂ : 1 ≤ q₂ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₂)
  have hq₁₂ : 1 ≤ q₁ * q₂ :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  haveI : NeZero (q₁ * q₂) := ⟨by omega⟩
  -- the engine
  obtain ⟨L₁, Lk, hlam, hr1, hr2, hmain⟩ :=
    siegel_lambda_lower_concrete χ₁ χ₂ hχ₁2 hχ₂2 hχ₁1 hχ₂1 hχ₃1 hβ1 hβ2 hzero
  -- fold the polynomial base and the tower into opaque atoms BEFORE any tactic
  obtain ⟨P, hP⟩ : ∃ P : ℝ,
      P = 1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 + 1 := ⟨_, rfl⟩
  rw [← hP] at hmain ⊢
  obtain ⟨Mv, hMv⟩ : ∃ Mv : ℝ,
      Mv = ((2 * (820 * P) ^ ((40:ℝ)))) ^ (1 - β) := ⟨_, rfl⟩
  rw [← hMv] at hmain ⊢
  have hP0 : (0:ℝ) < P := by
    rw [hP]
    positivity
  have hMv0 : (0:ℝ) < Mv := by
    rw [hMv]
    have h2 : (0:ℝ) < (820 * P) ^ ((40:ℝ)) :=
      Real.rpow_pos_of_pos (by linarith) _
    exact Real.rpow_pos_of_pos (by linarith) _
  -- the χ₂ and χ₃ values with their rates
  obtain ⟨ℓ₂, hrℓ₂⟩ := log_mean_exists (charFn q₂ χ₂) ((q₂:ℝ))
    (charFn_partial_sum_bound hq₂ χ₂ hχ₂2 hχ₂1)
  have hχ₃2 : ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
      * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) ^ 2 = 1 := by
    rw [mul_pow, ← map_pow, ← map_pow, hχ₁2, hχ₂2, map_one, map_one, mul_one]
  obtain ⟨L₃, hrL₃⟩ := log_mean_exists
    (charFn (q₁ * q₂) ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
      * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂))) (((q₁ * q₂ : ℕ)):ℝ)
    (charFn_partial_sum_bound hq₁₂ _ hχ₃2 hχ₃1)
  -- identifications at s = 1
  have hI2 : DirichletCharacter.LFunction χ₂ 1 = ((ℓ₂ : ℝ) : ℂ) :=
    L1_eq_LFunction_one hq₂ χ₂ hχ₂2 hχ₂1 ℓ₂ hrℓ₂
  have hI3 : DirichletCharacter.LFunction
      ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) 1
      = ((L₃ : ℝ) : ℂ) :=
    L1_eq_LFunction_one hq₁₂ _ hχ₃2 hχ₃1 L₃ hrL₃
  have hIk : DirichletCharacter.LFunction χ₂ 1
      * DirichletCharacter.LFunction
          ((DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
            * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂)) 1
      = ((Lk : ℝ) : ℂ) :=
    Lk_eq_LFunction_pair_one hq₁ hq₂ χ₁ χ₂ hχ₁2 hχ₂2 hχ₁1 hχ₂1 hχ₃1 Lk hr2
  have hLkprod : Lk = ℓ₂ * L₃ := by
    have h1 : ((Lk : ℝ) : ℂ) = ((ℓ₂ * L₃ : ℝ) : ℂ) := by
      rw [← hIk, hI2, hI3]
      push_cast
      ring
    exact_mod_cast h1
  have hL₁u : |L₁| ≤ 3 + Real.log q₁ :=
    rate_limit_upper_log (charFn q₁ χ₁) q₁ hq₁ L₁ (fun n => charFn_bound χ₁ hχ₁2 n) hr1
  have hL₃u : |L₃| ≤ 3 + Real.log ((q₁ * q₂ : ℕ)) :=
    rate_limit_upper_log _ (q₁ * q₂) hq₁₂ L₃ (fun n => charFn_bound _ hχ₃2 n) hrL₃
  have hβ0 : (0:ℝ) < 1 - β := by linarith
  have hq₁r : (1:ℝ) ≤ (q₁:ℝ) := by exact_mod_cast hq₁
  have hq₁₂r : (1:ℝ) ≤ ((q₁ * q₂ : ℕ):ℝ) := by exact_mod_cast hq₁₂
  have hlog₁ : (0:ℝ) ≤ Real.log q₁ := Real.log_nonneg hq₁r
  have hlog₃ : (0:ℝ) ≤ Real.log ((q₁ * q₂ : ℕ)) := Real.log_nonneg hq₁₂r
  have hden₁ : (0:ℝ) < 3 + Real.log q₁ := by linarith
  have hden₃ : (0:ℝ) < 3 + Real.log ((q₁ * q₂ : ℕ)) := by linarith
  have hlampos : (0:ℝ) < L₁ * Lk := by
    by_contra hcon
    push_neg at hcon
    have h1 : 26 * (L₁ * Lk) * Mv ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ hMv0.le
      nlinarith [hcon]
    linarith [hmain, hβ0]
  refine ⟨ℓ₂, hrℓ₂, hI2, ?_⟩
  have hLk_abs : |Lk| = |ℓ₂| * |L₃| := by
    rw [hLkprod, abs_mul]
  have hlam_le2 : L₁ * Lk ≤ (3 + Real.log q₁) * (3 + Real.log ((q₁ * q₂ : ℕ))) * |ℓ₂| := by
    calc L₁ * Lk ≤ |L₁ * Lk| := le_abs_self _
      _ = |L₁| * |Lk| := abs_mul _ _
      _ ≤ (3 + Real.log q₁) * |Lk| := by
          apply mul_le_mul_of_nonneg_right hL₁u (abs_nonneg _)
      _ = (3 + Real.log q₁) * (|ℓ₂| * |L₃|) := by rw [hLk_abs]
      _ ≤ (3 + Real.log q₁) * (|ℓ₂| * (3 + Real.log ((q₁ * q₂ : ℕ)))) := by
          apply mul_le_mul_of_nonneg_left _ hden₁.le
          apply mul_le_mul_of_nonneg_left hL₃u (abs_nonneg _)
      _ = (3 + Real.log q₁) * (3 + Real.log ((q₁ * q₂ : ℕ))) * |ℓ₂| := by ring
  have hdenpos : (0:ℝ) < 26 * Mv * (3 + Real.log q₁) * (3 + Real.log ((q₁ * q₂ : ℕ))) := by
    have h1 : (0:ℝ) < 26 * Mv := by linarith
    exact mul_pos (mul_pos h1 hden₁) hden₃
  rw [div_le_iff₀ hdenpos]
  have h26Mv : (0:ℝ) ≤ 26 * Mv := by linarith
  calc 1 - β ≤ 26 * (L₁ * Lk) * Mv := hmain
    _ = L₁ * Lk * (26 * Mv) := by ring
    _ ≤ ((3 + Real.log q₁) * (3 + Real.log ((q₁ * q₂ : ℕ))) * |ℓ₂|) * (26 * Mv) := by
        apply mul_le_mul_of_nonneg_right hlam_le2 h26Mv
    _ = |ℓ₂| * (26 * Mv * (3 + Real.log q₁) * (3 + Real.log ((q₁ * q₂ : ℕ)))) := by
        ring

/-- **The two-zero inequality** (Siegel brick S3c-b): an exceptional zero `β₁` of
    `χ₁` and any windowed zero `β₂` of a companion `χ₂` squeeze `|L(1,χ₂)|` from
    both sides — the inequality the dichotomy solves for `1−β₂`. -/
theorem chi2_zero_gap {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] (hq₂3 : 3 ≤ q₂)
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hχ₃1 : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) ≠ 1)
    {β₁ : ℝ} (hβ₁1 : 9/10 < β₁) (hβ₁2 : β₁ < 1)
    (hzero₁ : DirichletCharacter.LFunction χ₁ ((β₁:ℂ)) = 0)
    {β₂ : ℝ} (hβ₂2 : β₂ < 1) (hβ₂w : (1 - β₂) * Real.log q₂ ≤ 1/10)
    (hzero₂ : DirichletCharacter.LFunction χ₂ ((β₂:ℂ)) = 0) :
    (1 - β₁) / (26 * ((2 * (820 * (1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 + 1))
            ^ ((40:ℝ)))) ^ (1 - β₁)
          * (3 + Real.log q₁) * (3 + Real.log (q₁ * q₂ : ℕ)))
      ≤ 2 * (1 - β₂) * (1 + 3 * Real.log q₂) ^ 2 + 4 * ((q₂:ℝ)) ^ (-(17:ℝ)/10) := by
  obtain ⟨ℓ₂, hr, hI, hlow⟩ :=
    L_one_chi2_lower χ₁ χ₂ hχ₁2 hχ₂2 hχ₁1 hχ₂1 hχ₃1 hβ₁1 hβ₁2 hzero₁
  have hup := zero_gap_bridge hq₂3 χ₂ hχ₂2 hχ₂1 ℓ₂ hr hβ₂2 hβ₂w hzero₂
  linarith [hlow, hup]

/-- **The fixed-character gap** (Siegel brick S3c-c): a FIXED nontrivial `χ` has a
    positive zero-free interval below `1` — pure continuity from `L(1,χ) ≠ 0`. -/
theorem fixed_char_gap {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ β : ℝ, 1 - δ ≤ β → β < 1 →
      DirichletCharacter.LFunction χ ((β:ℂ)) ≠ 0 := by
  have hcont : ContinuousAt (DirichletCharacter.LFunction χ) 1 :=
    (DirichletCharacter.differentiable_LFunction hχ1).continuous.continuousAt
  have hne : DirichletCharacter.LFunction χ 1 ≠ 0 :=
    DirichletCharacter.LFunction_apply_one_ne_zero hχ1
  have hev : ∀ᶠ s in nhds (1:ℂ), DirichletCharacter.LFunction χ s ≠ 0 :=
    hcont.eventually_ne hne
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε0, hball⟩ := hev
  refine ⟨ε / 2, by linarith, ?_⟩
  intro β hβ1 hβ2
  apply hball
  rw [Complex.dist_eq, show ((β:ℂ)) - 1 = (((β - 1 : ℝ)):ℂ) from by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith

/-- **Zero transfer when the product trivializes** (Siegel brick S3c-g): if
    `χ₁χ₂ = 1` at level `q₁q₂` then a real zero of `χ₂` in `(0,1)` is a zero of
    `χ₁` — the Euler factors of `changeLevel` never vanish on `(0,1)`. -/
theorem zero_transfer_of_product_trivial {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁2 : χ₁ ^ 2 = 1) (hχ₂2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (htriv : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) = 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ2 : β < 1)
    (hzero : DirichletCharacter.LFunction χ₂ ((β:ℂ)) = 0) :
    DirichletCharacter.LFunction χ₁ ((β:ℂ)) = 0 := by
  haveI : NeZero (q₁ * q₂) := ⟨Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩
  set cl₁ := DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ with hcl₁
  set cl₂ := DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂ with hcl₂
  -- cl₂ = cl₁ by pure monoid algebra
  have h1 : cl₁ * cl₁ = 1 := by
    have h2 : cl₁ ^ 2 = 1 := by
      rw [hcl₁, ← map_pow, hχ₁2, map_one]
    rw [← pow_two]
    exact h2
  have hcl : cl₂ = cl₁ := by
    calc cl₂ = 1 * cl₂ := (one_mul _).symm
      _ = (cl₁ * cl₁) * cl₂ := by rw [h1]
      _ = cl₁ * (cl₁ * cl₂) := mul_assoc _ _ _
      _ = cl₁ * 1 := by rw [htriv]
      _ = cl₁ := mul_one _
  -- β is not 1
  have hβne : ((β:ℂ)) ≠ 1 := by
    intro h
    rw [Complex.ofReal_eq_one] at h
    linarith
  -- the Euler factors never vanish on (0,1)
  have hfac : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 →
      ∀ p ∈ (q₁ * q₂).primeFactors, (1 : ℂ) - χ ((p : ZMod q)) * ((p:ℂ)) ^ (-((β:ℝ):ℂ)) ≠ 0 := by
    intro q χ hχ2 p hp hzero'
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp1r : (1:ℝ) < (p:ℝ) := by
      have h : (1:ℕ) < p := hp2
      exact_mod_cast h
    have hz : (1:ℂ) = χ ((p : ZMod q)) * ((p:ℂ)) ^ (-((β:ℝ):ℂ)) := sub_eq_zero.mp hzero'
    have hnorm : (1:ℝ) = ‖χ ((p : ZMod q))‖ * ‖((p:ℂ)) ^ (-((β:ℝ):ℂ))‖ := by
      calc (1:ℝ) = ‖(1:ℂ)‖ := norm_one.symm
        _ = ‖χ ((p : ZMod q)) * ((p:ℂ)) ^ (-((β:ℝ):ℂ))‖ := by rw [← hz]
        _ = ‖χ ((p : ZMod q))‖ * ‖((p:ℂ)) ^ (-((β:ℝ):ℂ))‖ := norm_mul _ _
    have hχn : ‖χ ((p : ZMod q))‖ ≤ 1 := by
      rcases real_char_repr χ hχ2 ((p : ZMod q)) with h | h | h <;> rw [h] <;> norm_num
    have hpn : ‖((p:ℂ)) ^ (-((β:ℝ):ℂ))‖ = ((p:ℝ)) ^ (-β) := by
      rw [cpow_real_cast p β, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    have hlt : ((p:ℝ)) ^ (-β) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1r (by linarith)
    have hle : ‖χ ((p : ZMod q))‖ * ‖((p:ℂ)) ^ (-((β:ℝ):ℂ))‖
        ≤ ‖((p:ℂ)) ^ (-((β:ℝ):ℂ))‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hχn
    rw [hpn] at hle hnorm
    linarith [hnorm.le, hnorm.ge, hle, hlt]
  -- transfer through the changeLevel factorizations
  have hL2big : DirichletCharacter.LFunction cl₂ ((β:ℂ))
      = DirichletCharacter.LFunction χ₂ ((β:ℂ))
        * ∏ p ∈ (q₁ * q₂).primeFactors,
            (1 - χ₂ ((p : ZMod q₂)) * ((p:ℂ)) ^ (-((β:ℝ):ℂ))) :=
    DirichletCharacter.LFunction_changeLevel (dvd_mul_left q₂ q₁) χ₂ (Or.inr hβne)
  have hL1big : DirichletCharacter.LFunction cl₁ ((β:ℂ))
      = DirichletCharacter.LFunction χ₁ ((β:ℂ))
        * ∏ p ∈ (q₁ * q₂).primeFactors,
            (1 - χ₁ ((p : ZMod q₁)) * ((p:ℂ)) ^ (-((β:ℝ):ℂ))) :=
    DirichletCharacter.LFunction_changeLevel (dvd_mul_right q₁ q₂) χ₁ (Or.inr hβne)
  have hz2 : DirichletCharacter.LFunction cl₂ ((β:ℂ)) = 0 := by
    rw [hL2big, hzero, zero_mul]
  rw [hcl, hL1big] at hz2
  rcases mul_eq_zero.mp hz2 with h | h
  · exact h
  · exfalso
    have hne : ∏ p ∈ (q₁ * q₂).primeFactors,
        ((1:ℂ) - χ₁ ((p : ZMod q₁)) * ((p:ℂ)) ^ (-((β:ℝ):ℂ))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun p hp => hfac q₁ χ₁ hχ₁2 p hp)
    exact hne h

/-- **The dichotomy gap estimate** (Siegel brick S3c-e): with the exceptional zero
    in the `ε/320`-window, the whole denominator of `chi2_zero_gap` is at most
    `K(ε,q₁)·q₂^{ε/2}` — all `q₂`-growth tamed to an arbitrarily small power. -/
theorem dichotomy_gap_estimate (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1/100)
    (q₁ : ℕ) (hq₁ : 1 ≤ q₁) {β₁ : ℝ} (hβw : 1 - β₁ ≤ ε / 320) (hβpos : 0 ≤ 1 - β₁) :
    ∃ K : ℝ, 0 < K ∧ ∀ q₂ : ℕ, 1 ≤ q₂ →
      26 * ((2 * (820 * (1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 + 1))
          ^ ((40:ℝ)))) ^ (1 - β₁)
        * (3 + Real.log q₁) * (3 + Real.log ((q₁ * q₂ : ℕ)))
      ≤ K * ((q₂:ℝ)) ^ (ε / 2) := by
  have hq₁r : (1:ℝ) ≤ (q₁:ℝ) := by exact_mod_cast hq₁
  have hA1 : (2:ℝ) ≤ (q₁:ℝ) + 1 := by linarith
  have hlogq₁ : (0:ℝ) ≤ Real.log q₁ := Real.log_nonneg hq₁r
  refine ⟨(260 / ε) * Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
    * (3 + Real.log q₁) ^ 2, by positivity, ?_⟩
  intro q₂ hq₂
  have hq₂r : (1:ℝ) ≤ (q₂:ℝ) := by exact_mod_cast hq₂
  have hq₂0 : (0:ℝ) < (q₂:ℝ) := by linarith
  have hB1 : (2:ℝ) ≤ (q₂:ℝ) + 1 := by linarith
  have hlogq₂ : (0:ℝ) ≤ Real.log q₂ := Real.log_nonneg hq₂r
  -- name the pieces
  obtain ⟨P, hP⟩ : ∃ P : ℝ,
      P = 1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 + 1 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ((2 * (820 * P) ^ ((40:ℝ)))) ^ (1 - β₁) := ⟨_, rfl⟩
  rw [← hP, ← hT]
  have hP1 : (1:ℝ) ≤ P := by
    rw [hP]
    have h0 : (0:ℝ) ≤ 1000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 := by positivity
    linarith
  have hP0 : (0:ℝ) < P := by linarith
  have h820P : (0:ℝ) < 820 * P := by linarith
  have hinner0 : (0:ℝ) < (820 * P) ^ ((40:ℝ)) := Real.rpow_pos_of_pos h820P _
  have hbase0 : (0:ℝ) < 2 * (820 * P) ^ ((40:ℝ)) := by linarith
  -- log P ≤ log 2000 + 2 log A + 2 log B ≤ 2000 + 2 log A + 2 log B
  have hlogP : Real.log P ≤ 2000 + 2 * Real.log ((q₁:ℝ) + 1) + 2 * Real.log ((q₂:ℝ) + 1) := by
    have h1 : P ≤ 2000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2 := by
      rw [hP]
      have hA2 : (4:ℝ) ≤ ((q₁:ℝ) + 1) ^ 2 := by nlinarith [hA1]
      have hB2 : (4:ℝ) ≤ ((q₂:ℝ) + 1) ^ 2 := by nlinarith [hB1]
      nlinarith [hA2, hB2]
    have h2 : Real.log P ≤ Real.log (2000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2) :=
      Real.log_le_log hP0 h1
    have h3 : Real.log (2000 * ((q₁:ℝ) + 1) ^ 2 * ((q₂:ℝ) + 1) ^ 2)
        = Real.log 2000 + 2 * Real.log ((q₁:ℝ) + 1) + 2 * Real.log ((q₂:ℝ) + 1) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
      push_cast
      ring
    have h4 : Real.log 2000 ≤ 2000 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2000 by norm_num)
      linarith
    linarith
  -- log T ≤ (1−β₁)(112802 + 80 log A) + (1−β₁)·80·log B
  have hlogT : Real.log T ≤ (112802 + 80 * Real.log ((q₁:ℝ) + 1))
      + (ε / 4) * Real.log ((q₂:ℝ) + 1) := by
    rw [hT, Real.log_rpow hbase0]
    have h1 : Real.log (2 * (820 * P) ^ ((40:ℝ)))
        = Real.log 2 + 40 * Real.log (820 * P) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hinner0), Real.log_rpow h820P]
    have h2 : Real.log (820 * P) = Real.log 820 + Real.log P := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hP0)]
    have h3 : Real.log 820 ≤ 820 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 820 by norm_num)
      linarith
    have h4 : Real.log 2 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      linarith
    have hlogB0 : (0:ℝ) ≤ Real.log ((q₂:ℝ) + 1) := Real.log_nonneg (by linarith)
    have hlogA0 : (0:ℝ) ≤ Real.log ((q₁:ℝ) + 1) := Real.log_nonneg (by linarith)
    have h5 : Real.log (2 * (820 * P) ^ ((40:ℝ)))
        ≤ 112802 + 80 * Real.log ((q₁:ℝ) + 1) + 80 * Real.log ((q₂:ℝ) + 1) := by
      rw [h1, h2]
      linarith [hlogP]
    have h6 : (1 - β₁) * Real.log (2 * (820 * P) ^ ((40:ℝ)))
        ≤ 1 * (112802 + 80 * Real.log ((q₁:ℝ) + 1))
          + (1 - β₁) * (80 * Real.log ((q₂:ℝ) + 1)) := by
      have h7 : (1 - β₁) * Real.log (2 * (820 * P) ^ ((40:ℝ)))
          ≤ (1 - β₁) * (112802 + 80 * Real.log ((q₁:ℝ) + 1)
            + 80 * Real.log ((q₂:ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h5 hβpos
      have h8 : (1 - β₁) ≤ 1 := by
        have : (0:ℝ) < ε / 320 := by linarith
        linarith [hβw, hε1]
      nlinarith [h7, h8, hlogA0, hlogB0, hβpos]
    have h9 : (1 - β₁) * (80 * Real.log ((q₂:ℝ) + 1))
        ≤ (ε / 4) * Real.log ((q₂:ℝ) + 1) := by
      have : (1 - β₁) * 80 ≤ ε / 4 := by linarith [hβw]
      nlinarith [hlogB0, this, hβpos]
    linarith [h6, h9]
  -- T ≤ K₁ · (q₂+1)^{ε/4}
  have hT0 : (0:ℝ) < T := by
    rw [hT]
    exact Real.rpow_pos_of_pos hbase0 _
  have hTle : T ≤ Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
      * ((q₂:ℝ) + 1) ^ (ε / 4) := by
    have h1 : T = Real.exp (Real.log T) := (Real.exp_log hT0).symm
    rw [h1]
    have h2 : ((q₂:ℝ) + 1) ^ (ε / 4)
        = Real.exp ((ε / 4) * Real.log ((q₂:ℝ) + 1)) := by
      rw [Real.rpow_def_of_pos (by linarith), mul_comm]
    rw [h2, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hlogT
  -- (q₂+1)^{ε/4} ≤ 2·q₂^{ε/4}
  have hBpow : ((q₂:ℝ) + 1) ^ (ε / 4) ≤ 2 * ((q₂:ℝ)) ^ (ε / 4) := by
    calc ((q₂:ℝ) + 1) ^ (ε / 4) ≤ (2 * (q₂:ℝ)) ^ (ε / 4) := by
          apply Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
      _ = (2:ℝ) ^ (ε / 4) * ((q₂:ℝ)) ^ (ε / 4) :=
          Real.mul_rpow (by norm_num) hq₂0.le
      _ ≤ 2 * ((q₂:ℝ)) ^ (ε / 4) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hq₂0.le _)
          calc (2:ℝ) ^ (ε / 4) ≤ (2:ℝ) ^ ((1:ℝ)) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := Real.rpow_one 2
  -- 3 + log(q₁q₂) ≤ (3+log q₁)·(5/ε)·q₂^{ε/4}
  have hlogsplit : Real.log ((q₁ * q₂ : ℕ)) = Real.log q₁ + Real.log q₂ := by
    push_cast
    rw [Real.log_mul (by linarith) (by linarith)]
  have hlogq₂' : Real.log q₂ ≤ (4 / ε) * ((q₂:ℝ)) ^ (ε / 4) := by
    have h1 : Real.log q₂ ≤ ((q₂:ℝ)) ^ (ε / 4) / (ε / 4) :=
      Real.log_le_rpow_div hq₂0.le (by linarith)
    have h2 : ((q₂:ℝ)) ^ (ε / 4) / (ε / 4) = (4 / ε) * ((q₂:ℝ)) ^ (ε / 4) := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  have hpow1 : (1:ℝ) ≤ ((q₂:ℝ)) ^ (ε / 4) := Real.one_le_rpow hq₂r (by linarith)
  have hfac : 3 + Real.log ((q₁ * q₂ : ℕ))
      ≤ (3 + Real.log q₁) * ((5 / ε) * ((q₂:ℝ)) ^ (ε / 4)) := by
    rw [hlogsplit, ← add_assoc]
    have h1 : 3 + Real.log q₁ + Real.log q₂
        ≤ (3 + Real.log q₁) * (1 + (4 / ε) * ((q₂:ℝ)) ^ (ε / 4)) := by
      have h2 : (1:ℝ) ≤ 3 + Real.log q₁ := by linarith
      nlinarith [hlogq₂', h2, hlogq₂]
    have h3 : (1:ℝ) + (4 / ε) * ((q₂:ℝ)) ^ (ε / 4) ≤ (5 / ε) * ((q₂:ℝ)) ^ (ε / 4) := by
      have h4 : (1:ℝ) ≤ (1 / ε) * ((q₂:ℝ)) ^ (ε / 4) := by
        have h5 : (1:ℝ) ≤ 1 / ε := by
          rw [le_div_iff₀ hε0]
          linarith
        nlinarith [hpow1, h5]
      have h6 : (4 / ε) * ((q₂:ℝ)) ^ (ε / 4) + (1 / ε) * ((q₂:ℝ)) ^ (ε / 4)
          = (5 / ε) * ((q₂:ℝ)) ^ (ε / 4) := by ring
      linarith
    have h7 : (0:ℝ) ≤ 3 + Real.log q₁ := by linarith
    calc 3 + Real.log q₁ + Real.log q₂
        ≤ (3 + Real.log q₁) * (1 + (4 / ε) * ((q₂:ℝ)) ^ (ε / 4)) := h1
      _ ≤ (3 + Real.log q₁) * ((5 / ε) * ((q₂:ℝ)) ^ (ε / 4)) :=
          mul_le_mul_of_nonneg_left h3 h7
  -- assemble
  have hpowmul : ((q₂:ℝ)) ^ (ε / 4) * ((q₂:ℝ)) ^ (ε / 4) = ((q₂:ℝ)) ^ (ε / 2) := by
    rw [← Real.rpow_add hq₂0]
    congr 1
    ring
  have hden₁ : (0:ℝ) < 3 + Real.log q₁ := by linarith
  have hK₁0 : (0:ℝ) < Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1)) := Real.exp_pos _
  calc 26 * T * (3 + Real.log q₁) * (3 + Real.log ((q₁ * q₂ : ℕ)))
      ≤ 26 * (Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
          * (2 * ((q₂:ℝ)) ^ (ε / 4))) * (3 + Real.log q₁)
        * ((3 + Real.log q₁) * ((5 / ε) * ((q₂:ℝ)) ^ (ε / 4))) := by
        have hT2 : T ≤ Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
            * (2 * ((q₂:ℝ)) ^ (ε / 4)) := by
          calc T ≤ Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
              * ((q₂:ℝ) + 1) ^ (ε / 4) := hTle
            _ ≤ Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
                * (2 * ((q₂:ℝ)) ^ (ε / 4)) := by
                apply mul_le_mul_of_nonneg_left hBpow hK₁0.le
        have h30 : (0:ℝ) ≤ 3 + Real.log ((q₁ * q₂ : ℕ)) := by
          have := Real.log_nonneg (show (1:ℝ) ≤ ((q₁ * q₂ : ℕ):ℝ) from by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
          linarith
        have hfac0 : (0:ℝ) ≤ (3 + Real.log q₁) * ((5 / ε) * ((q₂:ℝ)) ^ (ε / 4)) := by
          positivity
        calc 26 * T * (3 + Real.log q₁) * (3 + Real.log ((q₁ * q₂ : ℕ)))
            ≤ 26 * T * (3 + Real.log q₁)
              * ((3 + Real.log q₁) * ((5 / ε) * ((q₂:ℝ)) ^ (ε / 4))) := by
              apply mul_le_mul_of_nonneg_left hfac
              positivity
          _ ≤ 26 * (Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
                * (2 * ((q₂:ℝ)) ^ (ε / 4))) * (3 + Real.log q₁)
              * ((3 + Real.log q₁) * ((5 / ε) * ((q₂:ℝ)) ^ (ε / 4))) := by
              apply mul_le_mul_of_nonneg_right _ hfac0
              apply mul_le_mul_of_nonneg_right _ hden₁.le
              apply mul_le_mul_of_nonneg_left hT2 (by norm_num)
    _ = ((260 / ε) * Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
          * (3 + Real.log q₁) ^ 2) * (((q₂:ℝ)) ^ (ε / 4) * ((q₂:ℝ)) ^ (ε / 4)) := by
        ring
    _ = ((260 / ε) * Real.exp (112802 + 80 * Real.log ((q₁:ℝ) + 1))
          * (3 + Real.log q₁) ^ 2) * ((q₂:ℝ)) ^ (ε / 2) := by
        rw [hpowmul]

/-- **The small-modulus gap** (Siegel brick S3c-f): below any threshold `Q₀` there
    are finitely many characters, so a single `c > 0` clears a zero-free interval
    below `1` for all of them at once. -/
theorem small_q_gap (Q₀ : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q → q < Q₀ →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ β : ℝ, 1 - c ≤ β → β < 1 →
        DirichletCharacter.LFunction χ ((β:ℂ)) ≠ 0 := by
  induction Q₀ with
  | zero =>
    exact ⟨1, one_pos, fun q _ _ hq0 => absurd hq0 (by omega)⟩
  | succ Q ih =>
    obtain ⟨c', hc'0, hc'⟩ := ih
    rcases Nat.lt_or_ge Q 3 with hQ3 | hQ3
    · -- the new modulus Q is below 3: nothing new to cover
      refine ⟨c', hc'0, ?_⟩
      intro q _ hq3 hqlt χ hχ1 β hβ1 hβ2
      have hqQ : q < Q := by omega
      exact hc' q hq3 hqQ χ hχ1 β hβ1 hβ2
    · -- take the min over the finitely many characters mod Q
      haveI : NeZero Q := ⟨by omega⟩
      haveI : Finite (DirichletCharacter ℂ Q) :=
        inferInstanceAs (Finite (MulChar (ZMod Q) ℂ))
      haveI := Fintype.ofFinite (DirichletCharacter ℂ Q)
      have hF : ∀ χ : DirichletCharacter ℂ Q, ∃ δ : ℝ, 0 < δ ∧
          (χ ≠ 1 → ∀ β : ℝ, 1 - δ ≤ β → β < 1 →
            DirichletCharacter.LFunction χ ((β:ℂ)) ≠ 0) := by
        intro χ
        by_cases h : χ = 1
        · exact ⟨1, one_pos, fun h1 => absurd h h1⟩
        · obtain ⟨δ, hδ0, hδ⟩ := fixed_char_gap χ h
          exact ⟨δ, hδ0, fun _ => hδ⟩
      choose δf hδf0 hδf using hF
      have hne : (Finset.univ : Finset (DirichletCharacter ℂ Q)).Nonempty :=
        ⟨1, Finset.mem_univ 1⟩
      refine ⟨min c' (Finset.univ.inf' hne δf), ?_, ?_⟩
      · apply lt_min hc'0
        rw [Finset.lt_inf'_iff]
        exact fun χ _ => hδf0 χ
      · intro q _ hq3 hqlt χ hχ1 β hβ1 hβ2
        rcases Nat.lt_or_ge q Q with h | h
        · apply hc' q hq3 h χ hχ1 β _ hβ2
          have := min_le_left c' (Finset.univ.inf' hne δf)
          linarith
        · have hqeq : q = Q := by omega
          subst hqeq
          apply hδf χ hχ1 β _ hβ2
          have h1 := Finset.inf'_le δf (Finset.mem_univ χ)
          have h2 := min_le_right c' (Finset.univ.inf' hne δf)
          linarith

/-- **SIEGEL'S THEOREM (auxiliary form, `ε ≤ 1/100`)** (Siegel brick S3c-h). -/
theorem siegel_zero_free_aux (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1/100) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ^ 2 = 1 → χ ≠ 1 →
      ∀ β : ℝ, β < 1 → DirichletCharacter.LFunction χ ((β:ℂ)) = 0 →
      β ≤ 1 - c * ((q:ℝ)) ^ (-ε) := by
  by_cases hex : ∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁),
      3 ≤ q₁ ∧ χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ ∃ β₁ : ℝ, 9/10 < β₁ ∧ β₁ < 1 ∧
        1 - β₁ ≤ ε / 320 ∧ DirichletCharacter.LFunction χ₁ ((β₁:ℂ)) = 0
  case neg =>
    -- no exceptional zero: the window itself is zero-free
    refine ⟨min (1/10) (ε / 320), by positivity, ?_⟩
    intro q _ hq3 χ hχ2 hχ1 β hβ2 hzero
    by_contra hcon
    push_neg at hcon
    have hq1r : (1:ℝ) ≤ (q:ℝ) := by
      have : (1:ℕ) ≤ q := by omega
      exact_mod_cast this
    have hqe : ((q:ℝ)) ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hq1r (by linarith)
    have hc1 : min (1/10) (ε / 320) * ((q:ℝ)) ^ (-ε) ≤ min (1/10) (ε / 320) := by
      have h0 : (0:ℝ) ≤ min (1/10) (ε / 320) := by positivity
      nlinarith [hqe, h0]
    apply hex
    refine ⟨q, ⟨by omega⟩, χ, hq3, hχ2, hχ1, β, ?_, hβ2, ?_, hzero⟩
    · have := min_le_left (1/10 : ℝ) (ε / 320)
      linarith
    · have := min_le_right (1/10 : ℝ) (ε / 320)
      linarith
  case pos =>
    obtain ⟨q₁, i₁, χ₁, hq₁3, hχ₁2, hχ₁1, β₁, hβ₁910, hβ₁lt, hβ₁win, hzero₁⟩ := hex
    haveI := i₁
    have hβ₁pos : (0:ℝ) < 1 - β₁ := by linarith
    obtain ⟨K, hK0, hKest⟩ :=
      dichotomy_gap_estimate ε hε0 hε1 q₁ (by omega) hβ₁win (by linarith)
    obtain ⟨δ₁, hδ₁0, hδ₁⟩ := fixed_char_gap χ₁ hχ₁1
    have hp0 : (0:ℝ) < (17:ℝ)/10 - ε/2 := by linarith
    obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀ : ℕ,
        Q₀ = Nat.ceil ((8 * K / (1 - β₁)) ^ ((((17:ℝ)/10 - ε/2))⁻¹)) + 1 := ⟨_, rfl⟩
    obtain ⟨cs, hcs0, hcs⟩ := small_q_gap Q₀
    obtain ⟨cc, hcc⟩ : ∃ cc : ℝ, cc = (1 - β₁) * ε ^ 2 / (676 * K) := ⟨_, rfl⟩
    have hcc0 : (0:ℝ) < cc := by
      rw [hcc]
      positivity
    refine ⟨min (min (1/10) (ε / 10)) (min cs (min cc δ₁)), by positivity, ?_⟩
    intro q _ hq3 χ hχ2 hχ1 β hβ2 hzero
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min (min (1/10) (ε / 10)) (min cs (min cc δ₁)) := ⟨_, rfl⟩
    rw [← hc]
    have hc0 : (0:ℝ) < c := by
      rw [hc]
      positivity
    have hq1r : (1:ℝ) ≤ (q:ℝ) := by
      have : (1:ℕ) ≤ q := by omega
      exact_mod_cast this
    have hq3r : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq3
    have hqe0 : (0:ℝ) < ((q:ℝ)) ^ (-ε) := Real.rpow_pos_of_pos (by linarith) _
    have hqe1 : ((q:ℝ)) ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hq1r (by linarith)
    have hlogq : (1:ℝ) < Real.log q := by
      have he : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9
        linarith
      calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
        _ ≤ Real.log q := Real.log_le_log (by norm_num) hq3r
    -- generic closer: from 1 − β ≥ c_br and c ≤ c_br
    have hclose_const : ∀ cbr : ℝ, c ≤ cbr → 1 - β ≥ cbr → β ≤ 1 - c * ((q:ℝ)) ^ (-ε) := by
      intro cbr hle hge
      have h1 : c * ((q:ℝ)) ^ (-ε) ≤ cbr := by
        calc c * ((q:ℝ)) ^ (-ε) ≤ c * 1 := by
              apply mul_le_mul_of_nonneg_left hqe1 hc0.le
          _ = c := mul_one c
          _ ≤ cbr := hle
      linarith
    have hclose_rpow : ∀ cbr : ℝ, 0 ≤ cbr → c ≤ cbr →
        1 - β ≥ cbr * ((q:ℝ)) ^ (-ε) → β ≤ 1 - c * ((q:ℝ)) ^ (-ε) := by
      intro cbr h0 hle hge
      have h1 : c * ((q:ℝ)) ^ (-ε) ≤ cbr * ((q:ℝ)) ^ (-ε) :=
        mul_le_mul_of_nonneg_right hle hqe0.le
      linarith
    -- branch: β ≤ 9/10
    by_cases hb : β ≤ 9/10
    · apply hclose_const (1/10)
      · rw [hc]
        exact le_trans (min_le_left _ _) (min_le_left _ _)
      · linarith
    push_neg at hb
    have hβ0 : (0:ℝ) < β := by linarith
    -- branch: outside the window
    by_cases hwin : (1 - β) * Real.log q ≤ 1/10
    swap
    · push_neg at hwin
      apply hclose_rpow (ε / 10) (by linarith) _ _
      · rw [hc]
        exact le_trans (min_le_left _ _) (min_le_right _ _)
      · have h1 : 1 / (10 * Real.log q) < 1 - β := by
          rw [div_lt_iff₀ (by linarith)]
          linarith [hwin]
        have h2 : Real.log q ≤ ((q:ℝ)) ^ ε / ε :=
          Real.log_le_rpow_div (by linarith) hε0
        have h3 : (ε / 10) * ((q:ℝ)) ^ (-ε) ≤ 1 / (10 * Real.log q) := by
          have h4 : ((q:ℝ)) ^ (-ε) * ((q:ℝ)) ^ ε = 1 := by
            rw [← Real.rpow_add (by linarith : (0:ℝ) < (q:ℝ))]
            simp
          have h5 : Real.log q * ε ≤ ((q:ℝ)) ^ ε := by
            rw [← le_div_iff₀ hε0]
            exact h2
          rw [le_div_iff₀ (by linarith : (0:ℝ) < 10 * Real.log q)]
          have h6 : ε / 10 * ((q:ℝ)) ^ (-ε) * (10 * Real.log q)
              = (Real.log q * ε) * ((q:ℝ)) ^ (-ε) := by ring
          rw [h6]
          calc (Real.log q * ε) * ((q:ℝ)) ^ (-ε)
              ≤ ((q:ℝ)) ^ ε * ((q:ℝ)) ^ (-ε) :=
                mul_le_mul_of_nonneg_right h5 hqe0.le
            _ = 1 := by rw [mul_comm]; exact h4
        linarith
    -- in the window: split on the product character
    by_cases hprod : (DirichletCharacter.changeLevel (dvd_mul_right q₁ q) χ₁)
        * (DirichletCharacter.changeLevel (dvd_mul_left q q₁) χ) = 1
    · -- product trivial: transfer the zero to χ₁ and use its fixed gap
      have hz1 := zero_transfer_of_product_trivial χ₁ χ hχ₁2 hχ2 hχ₁1 hχ1 hprod
        hβ0 hβ2 hzero
      apply hclose_const δ₁
      · rw [hc]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
      · by_contra hcon2
        push_neg at hcon2
        exact hδ₁ β (by linarith) hβ2 hz1
    · by_cases hbig : Q₀ ≤ q
      swap
      · -- small q: the finite-min constant
        push_neg at hbig
        apply hclose_const cs
        · rw [hc]
          exact le_trans (min_le_right _ _) (min_le_left _ _)
        · by_contra hcon2
          push_neg at hcon2
          exact hcs q hq3 hbig χ hχ1 β (by linarith) hβ2 hzero
      · -- THE MAIN CHAIN
        have hgap := chi2_zero_gap (q₂ := q) hq3 χ₁ χ hχ₁2 hχ2 hχ₁1 hχ1 hprod
          hβ₁910 hβ₁lt hzero₁ hβ2 hwin hzero
        have hKq := hKest q (by omega)
        obtain ⟨BIG, hBIG⟩ : ∃ B : ℝ, B = 26 * ((2 * (820 * (1000 * ((q₁:ℝ) + 1) ^ 2
            * ((q:ℝ) + 1) ^ 2 + 1)) ^ ((40:ℝ)))) ^ (1 - β₁)
            * (3 + Real.log q₁) * (3 + Real.log (q₁ * q : ℕ)) := ⟨_, rfl⟩
        rw [← hBIG] at hgap hKq
        have hBIG0 : (0:ℝ) < BIG := by
          rw [hBIG]
          obtain ⟨P, hP⟩ : ∃ P : ℝ,
              P = 1000 * ((q₁:ℝ) + 1) ^ 2 * ((q:ℝ) + 1) ^ 2 + 1 := ⟨_, rfl⟩
          rw [← hP]
          have hP0 : (0:ℝ) < P := by
            rw [hP]
            positivity
          have h1 : (0:ℝ) < (820 * P) ^ ((40:ℝ)) :=
            Real.rpow_pos_of_pos (by linarith) _
          have h2 : (0:ℝ) < ((2 * (820 * P) ^ ((40:ℝ)))) ^ (1 - β₁) :=
            Real.rpow_pos_of_pos (by linarith) _
          have h3 : (0:ℝ) < 3 + Real.log q₁ := by
            have := Real.log_nonneg (show (1:ℝ) ≤ (q₁:ℝ) from by
              exact_mod_cast (show (1:ℕ) ≤ q₁ from by omega))
            linarith
          have h4 : (0:ℝ) < 3 + Real.log ((q₁ * q : ℕ)) := by
            have h5 : (1:ℕ) ≤ q₁ * q :=
              Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
            have := Real.log_nonneg (show (1:ℝ) ≤ ((q₁ * q : ℕ):ℝ) from by
              exact_mod_cast h5)
            linarith
          have h26 : (0:ℝ) < (26:ℝ) := by norm_num
          exact mul_pos (mul_pos (mul_pos h26 h2) h3) h4
        have hqpos : (0:ℝ) < (q:ℝ) := by linarith
        have hthresh : 4 * ((q:ℝ)) ^ (-(17:ℝ)/10)
            ≤ (1 - β₁) / (2 * K * ((q:ℝ)) ^ (ε/2)) := by
          have hR0 : (0:ℝ) < 8 * K / (1 - β₁) := by positivity
          have hq_ge : (8 * K / (1 - β₁)) ^ ((((17:ℝ)/10 - ε/2))⁻¹) ≤ (q:ℝ) := by
            have h1 : (Q₀:ℝ) ≤ (q:ℝ) := by exact_mod_cast hbig
            rw [hQ₀] at h1
            push_cast at h1
            linarith [Nat.le_ceil ((8 * K / (1 - β₁)) ^ ((((17:ℝ)/10 - ε/2))⁻¹))]
          have h2 : 8 * K / (1 - β₁) ≤ ((q:ℝ)) ^ ((17:ℝ)/10 - ε/2) := by
            calc 8 * K / (1 - β₁)
                = ((8 * K / (1 - β₁)) ^ ((((17:ℝ)/10 - ε/2))⁻¹)) ^ ((17:ℝ)/10 - ε/2) := by
                  rw [← Real.rpow_mul hR0.le, inv_mul_cancel₀ (ne_of_gt hp0),
                    Real.rpow_one]
              _ ≤ ((q:ℝ)) ^ ((17:ℝ)/10 - ε/2) :=
                  Real.rpow_le_rpow (Real.rpow_nonneg hR0.le _) hq_ge hp0.le
          have h3 : ((q:ℝ)) ^ ((17:ℝ)/10 - ε/2)
              = ((q:ℝ)) ^ ((17:ℝ)/10) * ((q:ℝ)) ^ (-(ε/2)) := by
            rw [← Real.rpow_add hqpos]
            congr 1
          have hc17 : ((q:ℝ)) ^ (-(17:ℝ)/10) * ((q:ℝ)) ^ ((17:ℝ)/10) = 1 := by
            rw [← Real.rpow_add hqpos]
            norm_num
          have hce2 : ((q:ℝ)) ^ (-(ε/2)) * ((q:ℝ)) ^ (ε/2) = 1 := by
            rw [← Real.rpow_add hqpos]
            simp
          rw [le_div_iff₀ (by positivity)]
          rw [div_le_iff₀ hβ₁pos, h3] at h2
          have h4 := mul_le_mul_of_nonneg_right h2
            (show (0:ℝ) ≤ ((q:ℝ)) ^ (-(17:ℝ)/10) * ((q:ℝ)) ^ (ε/2) by positivity)
          have h5 : ((q:ℝ)) ^ ((17:ℝ)/10) * ((q:ℝ)) ^ (-(ε/2)) * (1 - β₁)
              * (((q:ℝ)) ^ (-(17:ℝ)/10) * ((q:ℝ)) ^ (ε/2))
              = (1 - β₁) * ((((q:ℝ)) ^ (-(17:ℝ)/10) * ((q:ℝ)) ^ ((17:ℝ)/10))
                * (((q:ℝ)) ^ (-(ε/2)) * ((q:ℝ)) ^ (ε/2))) := by ring
          rw [h5, hc17, hce2] at h4
          have h6 : 8 * K * (((q:ℝ)) ^ (-(17:ℝ)/10) * ((q:ℝ)) ^ (ε/2))
              = 4 * ((q:ℝ)) ^ (-(17:ℝ)/10) * (2 * K * ((q:ℝ)) ^ (ε/2)) := by ring
          rw [h6] at h4
          simpa using h4
        have hchain : (1 - β₁) / (K * ((q:ℝ)) ^ (ε/2))
            ≤ 2 * (1 - β) * (1 + 3 * Real.log q) ^ 2 + 4 * ((q:ℝ)) ^ (-(17:ℝ)/10) := by
          calc (1 - β₁) / (K * ((q:ℝ)) ^ (ε/2)) ≤ (1 - β₁) / BIG :=
              div_le_div_of_nonneg_left hβ₁pos.le hBIG0 hKq
            _ ≤ _ := hgap
        have hhalf : (1 - β₁) / (K * ((q:ℝ)) ^ (ε/2))
            = 2 * ((1 - β₁) / (2 * K * ((q:ℝ)) ^ (ε/2))) := by
          field_simp
        have hmain2 : (1 - β₁) / (2 * K * ((q:ℝ)) ^ (ε/2))
            ≤ 2 * (1 - β) * (1 + 3 * Real.log q) ^ 2 := by
          linarith [hchain, hthresh, hhalf.le, hhalf.ge]
        have hlog2 : (1 + 3 * Real.log q) ^ 2 ≤ (169 / ε ^ 2) * ((q:ℝ)) ^ (ε/2) := by
          have h1 : Real.log q ≤ ((q:ℝ)) ^ (ε/4) / (ε/4) :=
            Real.log_le_rpow_div hqpos.le (by linarith)
          have hp1 : (1:ℝ) ≤ ((q:ℝ)) ^ (ε/4) := Real.one_le_rpow hq1r (by linarith)
          have h2 : 1 + 3 * Real.log q ≤ (13 / ε) * ((q:ℝ)) ^ (ε/4) := by
            have h1' : Real.log q * (ε/4) ≤ ((q:ℝ)) ^ (ε/4) := by
              rwa [← le_div_iff₀ (by linarith : (0:ℝ) < ε/4)]
            rw [div_mul_eq_mul_div, le_div_iff₀ hε0]
            nlinarith [h1', hp1, hε1, hε0]
          have h7 : (0:ℝ) ≤ 1 + 3 * Real.log q := by
            have := Real.log_nonneg hq1r
            linarith
          calc (1 + 3 * Real.log q) ^ 2 ≤ ((13 / ε) * ((q:ℝ)) ^ (ε/4)) ^ 2 := by
                nlinarith [h2, h7]
            _ = (169 / ε ^ 2) * (((q:ℝ)) ^ (ε/4) * ((q:ℝ)) ^ (ε/4)) := by ring
            _ = (169 / ε ^ 2) * ((q:ℝ)) ^ (ε/2) := by
                rw [← Real.rpow_add hqpos]
                congr 2
                ring
        apply hclose_rpow cc hcc0.le _ _
        · rw [hc]
          exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
        · have hq2 : (0:ℝ) < ((q:ℝ)) ^ (ε/2) := Real.rpow_pos_of_pos hqpos _
          have h1 : (1 - β₁) / (2 * K * ((q:ℝ)) ^ (ε/2))
              ≤ 2 * (1 - β) * ((169 / ε ^ 2) * ((q:ℝ)) ^ (ε/2)) := by
            calc (1 - β₁) / (2 * K * ((q:ℝ)) ^ (ε/2))
                ≤ 2 * (1 - β) * (1 + 3 * Real.log q) ^ 2 := hmain2
              _ ≤ 2 * (1 - β) * ((169 / ε ^ 2) * ((q:ℝ)) ^ (ε/2)) := by
                  apply mul_le_mul_of_nonneg_left hlog2 (by linarith)
          have hqeq : ((q:ℝ)) ^ (ε/2) * ((q:ℝ)) ^ (ε/2) = ((q:ℝ)) ^ ε := by
            rw [← Real.rpow_add hqpos]
            congr 1
            ring
          have hqinv : ((q:ℝ)) ^ (-ε) * ((q:ℝ)) ^ ε = 1 := by
            rw [← Real.rpow_add hqpos]
            simp
          rw [div_le_iff₀ (by positivity)] at h1
          have h2 : 2 * (1 - β) * ((169 / ε ^ 2) * ((q:ℝ)) ^ (ε/2))
              * (2 * K * ((q:ℝ)) ^ (ε/2))
              = (676 * K / ε ^ 2) * (1 - β) * (((q:ℝ)) ^ (ε/2) * ((q:ℝ)) ^ (ε/2)) := by
            ring
          rw [h2, hqeq] at h1
          have h3 := mul_le_mul_of_nonneg_right h1
            (show (0:ℝ) ≤ (ε ^ 2 / (676 * K)) * ((q:ℝ)) ^ (-ε) by positivity)
          have h4 : (676 * K / ε ^ 2) * (1 - β) * ((q:ℝ)) ^ ε
              * ((ε ^ 2 / (676 * K)) * ((q:ℝ)) ^ (-ε))
              = (1 - β) * (((q:ℝ)) ^ (-ε) * ((q:ℝ)) ^ ε)
                * ((676 * K / ε ^ 2) * (ε ^ 2 / (676 * K))) := by ring
          have h5 : (676 * K / ε ^ 2) * (ε ^ 2 / (676 * K)) = 1 := by
            field_simp
          rw [h4, hqinv, h5, mul_one, mul_one] at h3
          have h6 : (1 - β₁) * ((ε ^ 2 / (676 * K)) * ((q:ℝ)) ^ (-ε))
              = ((1 - β₁) * ε ^ 2 / (676 * K)) * ((q:ℝ)) ^ (-ε) := by ring
          rw [h6] at h3
          rw [hcc]
          linarith [h3]

/-- **SIEGEL'S THEOREM** (Siegel brick S3c-h, final form): for every `ε > 0` there
    is `c(ε) > 0` (ineffective) with: every real zero `β < 1` of every quadratic
    nontrivial Dirichlet character mod `q ≥ 3` satisfies `β ≤ 1 − c·q^{−ε}`. -/
theorem siegel_zero_free (ε : ℝ) (hε0 : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ^ 2 = 1 → χ ≠ 1 →
      ∀ β : ℝ, β < 1 → DirichletCharacter.LFunction χ ((β:ℂ)) = 0 →
      β ≤ 1 - c * ((q:ℝ)) ^ (-ε) := by
  rcases le_or_gt ε (1/100) with hε1 | hε1
  · exact siegel_zero_free_aux ε hε0 hε1
  · obtain ⟨c, hc0, hc⟩ := siegel_zero_free_aux (1/100) (by norm_num) (le_refl _)
    refine ⟨c, hc0, ?_⟩
    intro q _ hq3 χ hχ2 hχ1 β hβ2 hzero
    have h1 := hc q hq3 χ hχ2 hχ1 β hβ2 hzero
    have hq1r : (1:ℝ) ≤ (q:ℝ) := by
      have : (1:ℕ) ≤ q := by omega
      exact_mod_cast this
    have h2 : ((q:ℝ)) ^ (-ε) ≤ ((q:ℝ)) ^ (-(1/100:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1r (by linarith)
    have h3 : c * ((q:ℝ)) ^ (-ε) ≤ c * ((q:ℝ)) ^ (-(1/100:ℝ)) :=
      mul_le_mul_of_nonneg_left h2 hc0.le
    linarith [h1, h3]

end Principia.Common.SW
