/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.ExplicitSpine
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

set_option autoImplicit false

/-!
# `EF.LeftLD` as a spine of four named sub-links (composition PROVED)

**`leftLD_of_links : LDFE → DigammaLine → VM32 → KInt → EF.LeftLD`**, by application only after
three PROVED facts. `EF.LeftLD` (survey EF6–7) is
`∫_ℝ |L'/L(−1/2 + iτ, χ)|²/|−1/2 + iτ|² dτ ≤ 2π(log q + 8)²` for every primitive `χ` mod `q`.

## The route (asymmetric functional equation, not the survey's symmetric one)

With `s = −1/2 + iτ` and `z = 1 − s = 3/2 − iτ` (`sR`), the log-derivative of
`L(s, χ) = q^{1/2 − s} ε(χ) Γ_ℂ(1 − s) T(s) L(1 − s, χ̄)` (`T = sin(πs/2)` for even `χ`,
`cos(πs/2)` for odd; `Γ_ℝ(1 − s + κ)/Γ_ℝ(s + κ) = Γ_ℂ(1 − s) T(s)`) is
`L'/L(s, χ) = −log q + log 2π − ψ(z) + (π/2)U(s) − L'/L(z, χ̄)` (LINK `LDFE`), with
`U = cot(πs/2)` or `−tan(πs/2)`, of modulus exactly `1` on `Re s = −1/2` (`ufac_norm`, PROVED:
`|cos(−π/4 + iy)| = |sin(−π/4 + iy)|`). Then
`|L'/L(s) + log q| ≤ |log 2π − log z| + |ψ(z) − log z| + π/2 + |L'/L(z, χ̄)| ≤ K(τ)` with
`K = |log 2π − log z| + π/2 + 1/2 + 7/4` (`Kfun`), using
* LINK `DigammaLine`: `|ψ(z) − log z| ≤ 1/2` on `Re z = 3/2` (true sup `0.3699` at `τ = 0`; from
  `ψ(z) − log z = −∑_n (1/w − log(1 + 1/w))`, `w = n + z`, each term `≤ 1/(2|w|²)`, and
  `∑ 1/(n + 3/2)² ≤ ∑(1/(n+1) − 1/(n+2)) = 1`; needs the digamma series, PNT+ `DigammaSeries`);
* LINK `VM32`: `∑Λ(n)n^{−3/2} ≤ 7/4` (true value `1.5052`; `= (∑ log n·n^{−3/2})/ζ(3/2)` with
  `ζ(3/2) ≥ 1 + √2` and `∑ log n·n^{−3/2} ≤ log 2/2^{3/2} + √2(log 2 + 2)`, i.e. `≤ 1.68`); it gives
  `|L'/L(3/2 − iτ, χ)| ≤ 7/4` for EVERY `χ` (`vmBound_of_vm32`, PROVED);
* LINK `KInt`: `∫ K(τ)²/|s|² dτ ≤ 2π·8²` — a pure real-variable numerical statement; mpmath gives
  `√(∫K²/|s|²/2π) = 5.30` against the `8` required (integral ratio `0.44`).
Minkowski in `L²(dτ/|s|²)` with `∫ dτ/|s|² = 2π` (`lint_c_div_sL`, PROVED) finishes:
`‖L'/L/s‖₂ ≤ log q·√(2π) + 8√(2π)`.

## Findings

* **F-L1. The survey's constant is very loose.** With the exact digamma and `∑Λn^{−3/2}`,
  `√(∫|L'/L + log q|²/|s|²/2π) ≤ 4.80` (asymmetric form, triangle inequality on `U`) and
  `≤ 3.94` (symmetric form), against the survey's `7.573` and the stated `8`. The slack is what
  lets every sub-link be crude: `1/2` for the digamma (true `0.37`), `7/4` for `VM32` (true
  `1.505`).
* **F-L2. The phases of `(π/2)U` and `−i·arg z` cancel as `|τ| → ∞`** (both tend to `∓iπ/2`); the
  triangle inequality used in `Kfun` forgoes this, costing `≈ 0.9` in the final constant.
* No falsification: all four sub-links are true as stated (numerics in `scratchpad/agld/`:
  `n3.py` checks `LDFE` to `10⁻²⁵` for characters mod 3, 4 (odd), 5 (even, odd complex)).
-/

namespace Principia.Common.TernaryGoldbach.AG

open MeasureTheory Set Filter Topology Principia.Common.Goldbach
open Principia.Common.TernaryGoldbach Principia.Common.TernaryGoldbach.EF
open scoped ENNReal ArithmeticFunction

/-! ## (1) Objects -/

/-- `z = 1 − s = 3/2 − iτ` for `s = sL τ`. -/
noncomputable def sR (τ : ℝ) : ℂ := 3 / 2 - τ * Complex.I

theorem one_sub_sL (τ : ℝ) : 1 - sL τ = sR τ := by
  unfold sL sR
  ring

theorem sR_re (τ : ℝ) : (sR τ).re = 3 / 2 := by
  simp [sR]

open Classical in
/-- **The trigonometric factor** `U = cot(πs/2)` (even `χ`) or `−tan(πs/2)` (odd `χ`). -/
noncomputable def Ufac {q : ℕ} (χ : DirichletCharacter ℂ q) (τ : ℝ) : ℂ :=
  if χ.Even then Complex.cot (Real.pi * sL τ / 2) else -Complex.tan (Real.pi * sL τ / 2)

/-- **The majorant** `K(τ) = |log 2π − log z| + π/2 + 1/2 + 7/4`. -/
noncomputable def Kfun (τ : ℝ) : ℝ :=
  ‖(Real.log (2 * Real.pi) : ℂ) - Complex.log (sR τ)‖ + Real.pi / 2 + 1 / 2 + 7 / 4

/-! ## (2) The named sub-links -/

/-- **LINK [LDFE] — the functional equation, log-derivative form** on `Re s = −1/2`:
`L'/L(s, χ) = −log q + log 2π − ψ(1 − s) + (π/2)U(s) − L'/L(1 − s, χ̄)` for primitive `χ`
(Mathlib `IsPrimitive.completedLFunction_one_sub`, `LFunction_eq_completed_div_gammaFactor`,
`Gammaℝ_div_Gammaℝ_one_sub`; `ψ = Complex.digamma = logDeriv Γ`). -/
def LDFE : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ τ : ℝ,
    LD χ (sL τ) = -(Real.log q : ℂ) + (Real.log (2 * Real.pi) : ℂ) - Complex.digamma (sR τ) +
      ((Real.pi / 2 : ℝ) : ℂ) * Ufac χ τ - LD χ⁻¹ (sR τ)

/-- **LINK [DigammaLine]** — `|ψ(z) − log z| ≤ 1/2` on `Re z = 3/2`. -/
def DigammaLine : Prop :=
  ∀ τ : ℝ, ‖Complex.digamma (sR τ) - Complex.log (sR τ)‖ ≤ 1 / 2

/-- **LINK [VM32]** — `∑ Λ(n) n^{−3/2} ≤ 7/4`. -/
def VM32 : Prop :=
  ∑' n : ℕ, Λ n / (n : ℝ) ^ (3 / 2 : ℝ) ≤ 7 / 4

/-- **LINK [KInt]** — `∫ K(τ)²/|−1/2 + iτ|² dτ ≤ 2π·8²` (pure real analysis). -/
def KInt : Prop :=
  ∫⁻ τ : ℝ, ENNReal.ofReal ((Kfun τ / ‖sL τ‖) ^ 2) ≤ ENNReal.ofReal (2 * Real.pi * 8 ^ 2)

/-! ## (3) `|U| = 1` on `Re s = −1/2` (PROVED) -/

/-- `πs/2 = −π/4 + i(πτ/2)`. -/
theorem pi_sL_div_two (τ : ℝ) : (Real.pi : ℂ) * sL τ / 2 =
    ((-(Real.pi / 4) : ℝ) : ℂ) + ((Real.pi * τ / 2 : ℝ) : ℂ) * Complex.I := by
  unfold sL
  push_cast
  ring

/-- **`|cos(πs/2)| = |sin(πs/2)| ≠ 0`** on `Re s = −1/2`. -/
theorem cos_sin_sL (τ : ℝ) :
    ‖Complex.cos (Real.pi * sL τ / 2)‖ = ‖Complex.sin (Real.pi * sL τ / 2)‖ ∧
      Complex.sin (Real.pi * sL τ / 2) ≠ 0 ∧ Complex.cos (Real.pi * sL τ / 2) ≠ 0 := by
  have hc : Real.cos (-(Real.pi / 4)) = Real.sqrt 2 / 2 := by
    rw [Real.cos_neg, Real.cos_pi_div_four]
  have hs : Real.sin (-(Real.pi / 4)) = -(Real.sqrt 2 / 2) := by
    rw [Real.sin_neg, Real.sin_pi_div_four]
  have hcos : Complex.cos (Real.pi * sL τ / 2) =
      ((Real.sqrt 2 / 2 * Real.cosh (Real.pi * τ / 2) : ℝ) : ℂ) +
        ((Real.sqrt 2 / 2 * Real.sinh (Real.pi * τ / 2) : ℝ) : ℂ) * Complex.I := by
    rw [pi_sL_div_two, Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, hc, hs]
    push_cast
    ring
  have hsin : Complex.sin (Real.pi * sL τ / 2) =
      ((-(Real.sqrt 2 / 2) * Real.cosh (Real.pi * τ / 2) : ℝ) : ℂ) +
        ((Real.sqrt 2 / 2 * Real.sinh (Real.pi * τ / 2) : ℝ) : ℂ) * Complex.I := by
    rw [pi_sL_div_two, Complex.sin_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, hc, hs]
    push_cast
    ring
  have hch : 0 < Real.cosh (Real.pi * τ / 2) := Real.cosh_pos _
  have h2 : 0 < Real.sqrt 2 := by positivity
  have hpos : 0 < (Real.sqrt 2 / 2 * Real.cosh (Real.pi * τ / 2)) ^ 2 +
      (Real.sqrt 2 / 2 * Real.sinh (Real.pi * τ / 2)) ^ 2 := by
    have h3 : 0 < Real.sqrt 2 / 2 * Real.cosh (Real.pi * τ / 2) := by positivity
    nlinarith [sq_nonneg (Real.sqrt 2 / 2 * Real.sinh (Real.pi * τ / 2))]
  have hpos' : 0 < (-(Real.sqrt 2 / 2) * Real.cosh (Real.pi * τ / 2)) ^ 2 +
      (Real.sqrt 2 / 2 * Real.sinh (Real.pi * τ / 2)) ^ 2 := by
    have e : (-(Real.sqrt 2 / 2) * Real.cosh (Real.pi * τ / 2)) ^ 2 =
        (Real.sqrt 2 / 2 * Real.cosh (Real.pi * τ / 2)) ^ 2 := by ring
    rw [e]
    exact hpos
  refine ⟨?_, ?_, ?_⟩
  · rw [hcos, hsin, Complex.norm_add_mul_I, Complex.norm_add_mul_I]
    congr 1
    ring
  · intro h0
    have := congrArg norm h0
    rw [hsin, Complex.norm_add_mul_I, norm_zero, Real.sqrt_eq_zero hpos'.le] at this
    linarith
  · intro h0
    have := congrArg norm h0
    rw [hcos, Complex.norm_add_mul_I, norm_zero, Real.sqrt_eq_zero hpos.le] at this
    linarith

/-- **`|U| = 1`.** -/
theorem ufac_norm {q : ℕ} (χ : DirichletCharacter ℂ q) (τ : ℝ) : ‖Ufac χ τ‖ = 1 := by
  obtain ⟨he, hs, hc⟩ := cos_sin_sL τ
  unfold Ufac
  split_ifs
  · rw [Complex.cot_eq_cos_div_sin, norm_div, he, div_self (norm_ne_zero_iff.mpr hs)]
  · rw [norm_neg, Complex.tan_eq_sin_div_cos, norm_div, he, div_self (norm_ne_zero_iff.mpr hs)]

/-! ## (4) `VM32` bounds `L'/L` on `Re s = 3/2` for every character (PROVED) -/

/-- **`|L'/L(3/2 − iτ, χ)| ≤ 7/4`** for every `χ` (the Dirichlet series and `VM32`). -/
theorem vmBound_of_vm32 (h : VM32) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (τ : ℝ) :
    ‖LD χ (sR τ)‖ ≤ 7 / 4 := by
  have h1 : 1 < (sR τ).re := by rw [sR_re]; norm_num
  rw [← norm_neg, neg_LD_eq_tsum χ h1]
  refine (tsum_of_norm_bounded (summable_vM (σ := 3 / 2) (by norm_num)).hasSum
    fun n => ?_).trans h
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hcast : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; ring
    rw [norm_div, norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn0, sR_re,
      Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hχ := DirichletCharacter.norm_le_one χ (n : ZMod q)
    have hp : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
    rw [div_le_div_iff_of_pos_right hp]
    calc ‖χ (n : ZMod q)‖ * Λ n ≤ 1 * Λ n :=
          mul_le_mul_of_nonneg_right hχ ArithmeticFunction.vonMangoldt_nonneg
      _ = Λ n := one_mul _

/-! ## (5) `∫ dτ/|s|² = 2π` (PROVED) -/

/-- `|−1/2 + iτ|² = 1/4 + τ²`. -/
theorem norm_sL_sq (τ : ℝ) : ‖sL τ‖ ^ 2 = 1 / 4 + τ ^ 2 := by
  have e : sL τ = ((-(1 / 2) : ℝ) : ℂ) + (τ : ℂ) * Complex.I := by
    unfold sL
    push_cast
    ring
  rw [e, Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
  ring

/-- **`∫ (c/|s|)² dτ = 2πc²`.** -/
theorem lint_c_div_sL (c : ℝ) :
    ∫⁻ τ : ℝ, ENNReal.ofReal ((c / ‖sL τ‖) ^ 2) = ENNReal.ofReal (2 * Real.pi * c ^ 2) := by
  have hpt : ∀ τ : ℝ, (c / ‖sL τ‖) ^ 2 = 4 * c ^ 2 * (1 + (2 * τ) ^ 2)⁻¹ := by
    intro τ
    rw [div_pow, norm_sL_sq]
    field_simp
    ring
  simp_rw [hpt]
  have hint : Integrable fun τ : ℝ => 4 * c ^ 2 * (1 + (2 * τ) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun τ => by positivity),
    integral_const_mul]
  congr 1
  have h2 := Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) 2
  rw [h2, integral_univ_inv_one_add_sq, smul_eq_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
  ring

/-! ## (6) The composition (PROVED) -/

/-- `Kfun` is measurable. -/
theorem measurable_Kfun : Measurable Kfun := by
  have hR : Measurable sR := by unfold sR; fun_prop
  unfold Kfun
  exact (((measurable_const.sub (Complex.measurable_log.comp hR)).norm.add_const _).add_const
    _).add_const _

/-- **The pointwise bound** `|L'/L(s)| ≤ log q + K(τ)` from `LDFE`, `DigammaLine`, `VM32`. -/
theorem ld_le_Kfun (hFE : LDFE) (hDG : DigammaLine) (hVM : VM32) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (τ : ℝ) :
    ‖LD χ (sL τ)‖ ≤ Real.log q + Kfun τ := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  rw [hFE q χ hχ τ]
  set A : ℂ := (Real.log (2 * Real.pi) : ℂ) - Complex.log (sR τ) with hA
  set B : ℂ := Complex.log (sR τ) - Complex.digamma (sR τ) with hB
  set C : ℂ := ((Real.pi / 2 : ℝ) : ℂ) * Ufac χ τ with hC
  set D : ℂ := LD χ⁻¹ (sR τ) with hD
  have e : -(Real.log q : ℂ) + (Real.log (2 * Real.pi) : ℂ) - Complex.digamma (sR τ) +
      ((Real.pi / 2 : ℝ) : ℂ) * Ufac χ τ - LD χ⁻¹ (sR τ) = -(Real.log q : ℂ) + A + B + C - D := by
    rw [hA, hB, hC, hD]
    ring
  rw [e]
  have hBn : ‖B‖ ≤ 1 / 2 := by rw [hB, norm_sub_rev]; exact hDG τ
  have hCn : ‖C‖ = Real.pi / 2 := by
    rw [hC, norm_mul, ufac_norm, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hDn : ‖D‖ ≤ 7 / 4 := vmBound_of_vm32 hVM χ⁻¹ τ
  have hqn : ‖-(Real.log q : ℂ)‖ = Real.log q := by
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg hlq]
  have t1 := norm_sub_le (-(Real.log q : ℂ) + A + B + C) D
  have t2 := norm_add_le (-(Real.log q : ℂ) + A + B) C
  have t3 := norm_add_le (-(Real.log q : ℂ) + A) B
  have t4 := norm_add_le (-(Real.log q : ℂ)) A
  unfold Kfun
  rw [← hA]
  linarith

/-- **`EF.LeftLD` from the four sub-links** (Minkowski in `L²(dτ/|s|²)`). -/
theorem leftLD_of_links (hFE : LDFE) (hDG : DigammaLine) (hVM : VM32) (hK : KInt) :
    LeftLD := by
  intro q _ χ hχ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hpi : 0 < 2 * Real.pi := by positivity
  have hK0 : ∀ τ, 0 ≤ Kfun τ := fun τ => by unfold Kfun; positivity
  set f : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal (Real.log q / ‖sL τ‖) with hf
  set g : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal (Kfun τ / ‖sL τ‖) with hg
  have hfm : AEMeasurable f volume :=
    (measurable_const.div measurable_sL.norm).ennreal_ofReal.aemeasurable
  have hgm : AEMeasurable g volume :=
    (measurable_Kfun.div measurable_sL.norm).ennreal_ofReal.aemeasurable
  have hpt : ∀ τ : ℝ, ENNReal.ofReal ((‖LD χ (sL τ)‖ / ‖sL τ‖) ^ 2) ≤ (f + g) τ ^ (2 : ℝ) := by
    intro τ
    have hs : 0 < ‖sL τ‖ := norm_pos_iff.mpr (sL_ne_zero τ)
    simp only [Pi.add_apply, hf, hg]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_add (div_nonneg hlq hs.le) (div_nonneg (hK0 τ) hs.le),
      ← ENNReal.ofReal_pow (add_nonneg (div_nonneg hlq hs.le) (div_nonneg (hK0 τ) hs.le))]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ 2)
    rw [← add_div]
    exact div_le_div_of_nonneg_right (ld_le_Kfun hFE hDG hVM hχ τ) hs.le
  have hmk := ENNReal.lintegral_Lp_add_le hfm hgm (show (1 : ℝ) ≤ 2 by norm_num)
  have e2 : ∀ (u : ℝ → ℝ), (∀ τ, 0 ≤ u τ) →
      (fun τ => ENNReal.ofReal (u τ) ^ (2 : ℝ)) = fun τ => ENNReal.ofReal (u τ ^ 2) := by
    intro u hu
    funext τ
    rw [ENNReal.rpow_two, ENNReal.ofReal_pow (hu τ)]
  have hfnn : ∀ τ, 0 ≤ Real.log q / ‖sL τ‖ := fun τ => div_nonneg hlq (norm_nonneg _)
  have hgnn : ∀ τ, 0 ≤ Kfun τ / ‖sL τ‖ := fun τ => div_nonneg (hK0 τ) (norm_nonneg _)
  rw [show (fun τ => f τ ^ (2 : ℝ)) = fun τ => ENNReal.ofReal ((Real.log q / ‖sL τ‖) ^ 2) from
      e2 _ hfnn,
    show (fun τ => g τ ^ (2 : ℝ)) = fun τ => ENNReal.ofReal ((Kfun τ / ‖sL τ‖) ^ 2) from
      e2 _ hgnn, lint_c_div_sL] at hmk
  have hK' := ENNReal.rpow_le_rpow hK (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have k1 : 2 * Real.pi * Real.log q ^ 2 = (Real.sqrt (2 * Real.pi) * Real.log q) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hpi.le]
  have k2 : 2 * Real.pi * 8 ^ 2 = (Real.sqrt (2 * Real.pi) * 8) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hpi.le]
  rw [k2, ofReal_sq_rpow_half (by positivity)] at hK'
  rw [k1, ofReal_sq_rpow_half (by positivity)] at hmk
  have hsum := hmk.trans (add_le_add le_rfl hK')
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hsum
  have h3 := le_sq_of_rpow_half_le hsum
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two] at h3
  have k3 : (Real.sqrt (2 * Real.pi) * Real.log q + Real.sqrt (2 * Real.pi) * 8) ^ 2 =
      2 * Real.pi * (Real.log q + 8) ^ 2 := by
    rw [← mul_add, mul_pow, Real.sq_sqrt hpi.le]
  rw [k3] at h3
  exact (lintegral_mono hpt).trans h3

end Principia.Common.TernaryGoldbach.AG
