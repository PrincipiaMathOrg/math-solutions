/-
STATEMENT MODULE — definitions only, no theorems, no proofs.

This file holds every project-specific definition the trusted statement in
`Challenge.lean` rests on. Together with Mathlib it is the entire audit surface: read
this file and `Challenge.lean` and you have read everything you must trust.

The definitions are byte-for-byte those of the certified development file
(`HRTLambda0/Endgame.lean` proves the theorems about them).

READ `ZakReduction` CAREFULLY — it is the honesty-critical definition. It packages, as a
single named HYPOTHESIS on the window `g`, everything the paper establishes before its
endgame (the Zak-transform reduction, the WLOG that all four coefficients are nonzero,
the fibre dichotomy producing a live interval, the degree identity at `j = 0`, and
Jensen's formula on the fibre). None of that is proved in this repository. The theorem
in `Challenge.lean` is CONDITIONAL on it, and that conditionality is the honest content
of this solution folder.

Palomar requires `Challenge.lean` to import nothing but Mathlib (and Lean core, Tau Ceti,
CSLib), so `Challenge.lean` carries a verbatim copy of these definitions instead of
importing this module. Keep the two in sync; Comparator fails when they differ.
-/
import Mathlib
set_option autoImplicit false

namespace HRTLambda0

open Complex

/-- The time–frequency translate `x ↦ e^{2πi b x} g(x - a)`. -/
noncomputable def tfTranslate (a b : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => Complex.exp (2 * Real.pi * Complex.I * b * x) * g (x - a)

/-- The four translates indexed by `{(0,0), (1,0), (0,1), (α, α + j)}`. -/
noncomputable def configTranslates (α : ℝ) (j : ℤ) (g : ℝ → ℂ) : Fin 4 → (ℝ → ℂ)
  | 0 => tfTranslate 0 0 g
  | 1 => tfTranslate 1 0 g
  | 2 => tfTranslate 0 1 g
  | 3 => tfTranslate α (α + j) g

/-- The four translates at `Λ₀ = {(0,0), (1,0), (0,1), (√2,√2)}`: the case
`α = √2`, `j = 0` of `configTranslates`. -/
noncomputable def lambda0Translates (g : ℝ → ℂ) : Fin 4 → (ℝ → ℂ) :=
  configTranslates (Real.sqrt 2) 0 g

/-- The conclusion of the paper's main theorem, as a Lean statement: the four
translates at `Λ₀` are linearly independent over `ℂ`. -/
def Lambda0Independent (g : ℝ → ℂ) : Prop :=
  LinearIndependent ℂ (lambda0Translates g)

/-- The analytic reduction carried out in the paper's §Reduction, §The fibre
dichotomy and §The degree identity, together with Jensen's formula on the fibre,
stated as a hypothesis on the window `g`. **This is an UNPROVED hypothesis in this
repository**, not a theorem — see the module docstring. -/
def ZakReduction (g : ℝ → ℂ) : Prop :=
  ¬ Lambda0Independent g →
    ∃ (c₁ c₂ c₃ c₄ : ℂ) (a b : ℝ) (zin zout : ℝ → ℂ),
      c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ c₃ ≠ 0 ∧ c₄ ≠ 0 ∧ a < b ∧ b - a < 1 ∧
      (∀ c ∈ Set.Icc a b, zin c + zout c = -c₁ / c₃) ∧
      (∀ c ∈ Set.Icc a b, zin c * zout c =
        (c₂ / c₃) * Complex.exp (-(2 * Real.pi * Complex.I * c))) ∧
      (∀ c ∈ Set.Icc a b, ‖zout c‖ = ‖c₄‖ / ‖c₃‖)

end HRTLambda0
