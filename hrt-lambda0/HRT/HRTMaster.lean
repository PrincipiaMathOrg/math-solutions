/-
# HRT / Heil–Speegle — the assembly module

The campaign's four files were written as independent Mathlib-only modules, which is why
`HRTResonant.fromCoeffs` duplicates `ZakPeriodization.ofCoeffs`: nothing could import anything.
This module is the fix.  It composes

* `ZakTransform`      — the Zak fibration, the fibre equation, the symbol/quadratic identity
* `BirkhoffErgodic`   — the pointwise ergodic theorem and the coboundary mean lemma
* `HRTResonantFibre`  — the counting/Jensen endgame and the ILR-free capstone

Build:  `lake build HRTMaster`   (build the MODULE, never the library target).

**STATUS: BUILDS.**  Verified with `lake build HRTMaster` → `Build completed successfully`,
after `ZakTransform`, `BirkhoffErgodic` and `HRTResonantFibre` each built as modules.  Freeing the
machine meant stopping the Lean daemon outright for the duration — it holds 3–4 GB, and it was the
thing competing with `lake`.
-/

import ZakTransform
import BirkhoffErgodic
import HRTResonantFibre

open MeasureTheory Complex Real AddCircle

namespace HRTMaster

/-! ## The first genuinely cross-module theorem

Everything below needs two modules at once, so none of it could be stated before this file built.

`ZakPeriodization.norm_symbol_eq_norm_quadratic` says the Zak fibre symbol and the counting
machinery's quadratic are the same object at `z = e^{2πit}`.
`HRTResonant.quadratic_fibre_mean_eq_circleAverage` says the `t`-integral of that quadratic is a
circle average.  Chaining them expresses the mean of `log‖symbol‖` — the quantity the DYNAMICAL
side produces — as the Mahler measure the JENSEN side consumes. -/

/-- **The symbol's fibre mean is a Mahler measure.**  Joins the Zak side to the Jensen side. -/
theorem symbol_mean_eq_circleAverage (A B C : ℂ) (θ : ℝ) :
    (∫ t in (0 : ℝ)..1, Real.log ‖ZakPeriodization.symbol A B C θ t‖)
      = circleAverage (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z
          + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))‖) 0 1 := by
  have hrw : ∀ t : ℝ, Real.log ‖ZakPeriodization.symbol A B C θ t‖
      = Real.log ‖C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2
          + A * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
          + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))‖ := by
    intro t
    rw [ZakPeriodization.norm_symbol_eq_norm_quadratic]
  rw [intervalIntegral.integral_congr (fun t _ => hrw t)]
  exact HRTResonant.quadratic_fibre_mean_eq_circleAverage A B C _

/-- **The live set is finite, from the mean of the SYMBOL.**  The Zak-native form: a caller supplies
the mean of `log‖symbol‖` over each live fibre — which is what the cocycle plus Birkhoff produce —
and finiteness comes out, with no ILR and no manual change of variables. -/
theorem live_set_not_infinite_of_symbol_mean
    (A B C D : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hDC : ‖D‖ ≠ ‖C‖) (hDB : ‖D‖ ≠ ‖B‖)
    (Θ : Set ℝ)
    (hmean : ∀ θ ∈ Θ, (∫ t in (0 : ℝ)..1, Real.log ‖ZakPeriodization.symbol A B C θ t‖)
      = Real.log ‖D‖) :
    ¬ ((fun θ : ℝ => Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))) '' Θ).Infinite := by
  refine HRTResonant.live_set_not_infinite_of_mean A B C D hA hB hC hD hDC hDB _ ?_ ?_
  · rintro w ⟨θ, _, rfl⟩
    exact ZakPeriodization.norm_fibre_param θ
  · rintro w ⟨θ, hθ, rfl⟩
    rw [← symbol_mean_eq_circleAverage]
    exact hmean θ hθ

/-! ## The three-point chain, joined

The same join on the LINEAR side.  `ZakPeriodization.symbol_linear` collapses the symbol at `C = 0`
to `A + B e^{-2πi(t+θ)}`, and `HRTResonant.linear_coeff_constraint_of_fibre_mean` turns the mean of
its log into a constraint on the coefficients.  Composed, a three-point dependence's fibre mean
pins `max ‖A‖ ‖B‖ = ‖D‖` — a condition on the DEPENDENCE, not on the fibre. -/

/-- **A three-point symbol mean pins the coefficients.** -/
theorem threePoint_coeff_constraint_of_symbol_mean (A B D : ℂ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0) (θ : ℝ)
    (hmean : (∫ t in (0 : ℝ)..1, Real.log ‖ZakPeriodization.symbol A B 0 θ t‖)
      = Real.log ‖D‖) :
    max ‖A‖ ‖B‖ = ‖D‖ := by
  have hrw : ∀ t : ℝ, Real.log ‖ZakPeriodization.symbol A B 0 θ t‖
      = Real.log ‖B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t + θ : ℝ) : ℂ))) + A‖ := by
    intro t
    rw [ZakPeriodization.symbol_linear]
    congr 2
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hrw t)] at hmean
  exact HRTResonant.linear_coeff_constraint_of_fibre_mean A B D hA hB hD θ hmean

/-- Contrapositive: coefficients violating the constraint admit no such fibre mean, hence no
dependence producing it. -/
theorem no_threePoint_dependence_of_symbol_mean (A B D : ℂ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0) (θ : ℝ) (hne : max ‖A‖ ‖B‖ ≠ ‖D‖) :
    ¬ ((∫ t in (0 : ℝ)..1, Real.log ‖ZakPeriodization.symbol A B 0 θ t‖) = Real.log ‖D‖) :=
  fun hmean => hne (threePoint_coeff_constraint_of_symbol_mean A B D hA hB hD θ hmean)

/-- **The degree condition, from the symbol mean, with no ILR.**  The four-point counterpart:
`rootCount = 1` straight from the quantity the Zak/Birkhoff side produces. -/
theorem rootCount_eq_one_of_symbol_mean (A B C D : ℂ) (θ : ℝ) (ζ₁ ζ₂ : ℂ)
    (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hDC : ‖D‖ ≠ ‖C‖) (hDB : ‖D‖ ≠ ‖B‖)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z
        + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))
      = C * (z - ζ₁) * (z - ζ₂))
    (h1 : ‖ζ₁‖ ≠ 1) (h2 : ‖ζ₂‖ ≠ 1)
    (hmean : (∫ t in (0 : ℝ)..1, Real.log ‖ZakPeriodization.symbol A B C θ t‖)
      = Real.log ‖D‖) :
    HRTResonant.rootCount ζ₁ ζ₂ = 1 := by
  rw [symbol_mean_eq_circleAverage] at hmean
  exact HRTResonant.rootCount_eq_one_of_mean A B C D _ ζ₁ ζ₂ hB hC hD
    (ZakPeriodization.norm_fibre_param θ) hDC hDB hfac h1 h2 hmean


/-! ## The two halves meet

`ZakPeriodization.cocycle_circle_abs` supplies exactly the multiplicative cocycle that
`integral_log_eq_of_modulus_cocycle` consumes, on `AddCircle 1` where Haar is a probability measure
and translation is measure-preserving.  The conclusion is the MEAN CONDITION — the hypothesis every
Jensen-side theorem in this development has been waiting for. -/

/-- **The mean condition, derived from the Zak cocycle by the pointwise ergodic theorem.** -/
theorem mean_of_zak_cocycle (g : ℝ → ℂ) (A B C D : ℂ) (a θ : ℝ) (hD : 0 < ‖D‖)
    (hR : MeasurePreserving
      (fun x : AddCircle (1 : ℝ) => x - ((a : ℝ) : AddCircle (1 : ℝ)))
      (haarAddCircle : Measure (AddCircle (1 : ℝ))) haarAddCircle)
    (hGmeas : Measurable (ZakPeriodization.fibreCircle g θ))
    (hPmeas : Measurable (ZakPeriodization.symbolCircle A B C θ))
    (hGne : ∀ᵐ x ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))),
      ZakPeriodization.fibreCircle g θ x ≠ 0)
    (hPne : ∀ᵐ x ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))),
      ZakPeriodization.symbolCircle A B C θ x ≠ 0)
    (hcoc : ∀ t : ℝ, ‖ZakPeriodization.symbol A B C θ t‖ * ‖ZakPeriodization.zakFibre g θ t‖
      = ‖D‖ * ‖ZakPeriodization.zakFibre g θ (t - a)‖)
    (hint : Integrable (fun x => Real.log |ZakPeriodization.symbolCircle A B C θ x|)
      (haarAddCircle : Measure (AddCircle (1 : ℝ)))) :
    (∫ x, Real.log |ZakPeriodization.symbolCircle A B C θ x|
      ∂(haarAddCircle : Measure (AddCircle (1 : ℝ)))) = Real.log ‖D‖ :=
  integral_log_eq_of_modulus_cocycle hR hD hGmeas hPmeas hGne hPne
    (Filter.Eventually.of_forall
      (ZakPeriodization.cocycle_circle_abs g A B C D a θ hcoc)) hint

/-! ## The full chain

Everything above composes.  From a Zak cocycle — the raw output of a time–frequency dependence —
these produce a statement about the DEPENDENCE COEFFICIENTS, passing through the pointwise ergodic
theorem, the descent to the circle, the change of variables, and Jensen's formula, with no ILR and
no spectral theory anywhere in the path. -/

/-- **THE THREE-POINT CHAIN, END TO END.**  Zak cocycle ⟹ `max ‖A‖ ‖B‖ = ‖D‖`. -/
theorem threePoint_constraint_of_cocycle (g : ℝ → ℂ) (A B D : ℂ) (a θ : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0)
    (hR : MeasurePreserving
      (fun x : AddCircle (1 : ℝ) => x - ((a : ℝ) : AddCircle (1 : ℝ)))
      (haarAddCircle : Measure (AddCircle (1 : ℝ))) haarAddCircle)
    (hGmeas : Measurable (ZakPeriodization.fibreCircle g θ))
    (hPmeas : Measurable (ZakPeriodization.symbolCircle A B 0 θ))
    (hGne : ∀ᵐ x ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))),
      ZakPeriodization.fibreCircle g θ x ≠ 0)
    (hPne : ∀ᵐ x ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))),
      ZakPeriodization.symbolCircle A B 0 θ x ≠ 0)
    (hcoc : ∀ t : ℝ, ‖ZakPeriodization.symbol A B 0 θ t‖ * ‖ZakPeriodization.zakFibre g θ t‖
      = ‖D‖ * ‖ZakPeriodization.zakFibre g θ (t - a)‖)
    (hint : Integrable (fun x => Real.log |ZakPeriodization.symbolCircle A B 0 θ x|)
      (haarAddCircle : Measure (AddCircle (1 : ℝ)))) :
    max ‖A‖ ‖B‖ = ‖D‖ := by
  have hmean := mean_of_zak_cocycle g A B 0 D a θ (norm_pos_iff.mpr hD)
    hR hGmeas hPmeas hGne hPne hcoc hint
  rw [ZakPeriodization.symbol_mean_circle_eq_interval] at hmean
  exact threePoint_coeff_constraint_of_symbol_mean A B D hA hB hD θ hmean

/-- **THE FOUR-POINT CHAIN, END TO END.**  Zak cocycle ⟹ `rootCount = 1`, the degree condition,
with no Iwanik–Lemańczyk–Rudolph input. -/
theorem rootCount_of_cocycle (g : ℝ → ℂ) (A B C D : ℂ) (a θ : ℝ) (ζ₁ ζ₂ : ℂ)
    (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hDC : ‖D‖ ≠ ‖C‖) (hDB : ‖D‖ ≠ ‖B‖)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z
        + B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)))
      = C * (z - ζ₁) * (z - ζ₂))
    (h1 : ‖ζ₁‖ ≠ 1) (h2 : ‖ζ₂‖ ≠ 1)
    (hR : MeasurePreserving
      (fun x : AddCircle (1 : ℝ) => x - ((a : ℝ) : AddCircle (1 : ℝ)))
      (haarAddCircle : Measure (AddCircle (1 : ℝ))) haarAddCircle)
    (hGmeas : Measurable (ZakPeriodization.fibreCircle g θ))
    (hPmeas : Measurable (ZakPeriodization.symbolCircle A B C θ))
    (hGne : ∀ᵐ x ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))),
      ZakPeriodization.fibreCircle g θ x ≠ 0)
    (hPne : ∀ᵐ x ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))),
      ZakPeriodization.symbolCircle A B C θ x ≠ 0)
    (hcoc : ∀ t : ℝ, ‖ZakPeriodization.symbol A B C θ t‖ * ‖ZakPeriodization.zakFibre g θ t‖
      = ‖D‖ * ‖ZakPeriodization.zakFibre g θ (t - a)‖)
    (hint : Integrable (fun x => Real.log |ZakPeriodization.symbolCircle A B C θ x|)
      (haarAddCircle : Measure (AddCircle (1 : ℝ)))) :
    HRTResonant.rootCount ζ₁ ζ₂ = 1 := by
  have hmean := mean_of_zak_cocycle g A B C D a θ (norm_pos_iff.mpr hD)
    hR hGmeas hPmeas hGne hPne hcoc hint
  rw [ZakPeriodization.symbol_mean_circle_eq_interval] at hmean
  exact rootCount_eq_one_of_symbol_mean A B C D θ ζ₁ ζ₂ hB hC hD hDC hDB hfac h1 h2 hmean

end HRTMaster

/-! ## Acceptance gate -/

#print axioms HRTMaster.symbol_mean_eq_circleAverage
#print axioms HRTMaster.live_set_not_infinite_of_symbol_mean
#print axioms HRTMaster.threePoint_coeff_constraint_of_symbol_mean
#print axioms HRTMaster.no_threePoint_dependence_of_symbol_mean
#print axioms HRTMaster.rootCount_eq_one_of_symbol_mean
#print axioms HRTMaster.mean_of_zak_cocycle
#print axioms HRTMaster.threePoint_constraint_of_cocycle
#print axioms HRTMaster.rootCount_of_cocycle
