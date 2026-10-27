/-
TRUSTED CHALLENGE FILE — the statement, without proof.

This file is the audit surface, together with Mathlib. Comparator
(github.com/leanprover/comparator) checks that the corresponding declaration in
`Solution.lean` proves EXACTLY this statement, using no axioms beyond the permitted list
in `comparator/all.json`:
  • `lambda0_independent_of_reduction` — [propext, Quot.sound, Classical.choice].

The `sorry` below is deliberate and is the only `sorry` in this directory.

IMPORT CLOSURE: Mathlib only, as Palomar's Challenge policy requires. The definitions
in the first namespace block below are a verbatim copy of `HRTLambda0/Statement.lean`, the
module the development and `Solution.lean` import; Comparator checks that the two
copies agree declaration by declaration, so a drift between them fails the check.

WHAT THE STATEMENT SAYS, in words — read it CAREFULLY, because the honesty of this
solution folder lives in the hypothesis:

  lambda0_independent_of_reduction
      IF the window `g` satisfies `ZakReduction g` — the paper's analytic reduction
      (Zak transform, fibre dichotomy, degree identity, Jensen's formula on the fibre),
      packaged as a single named HYPOTHESIS that is NOT proved in this repository —
      THEN the four time–frequency translates of `g` at
      `Λ₀ = {(0,0), (1,0), (0,1), (√2,√2)}` are linearly independent over `ℂ`.

This is a CONDITIONAL result. The HRT conjecture at `Λ₀` (Heil 2006, Conjecture 9.2(a);
Heil–Speegle, Conjecture 2) is NOT claimed unconditionally here. What is machine-checked
is the paper's endgame: that the reduction SUFFICES.
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

namespace HRTLambda0.Statement

/-- **HRT at `Λ₀`, conditional on the analytic reduction** (the paper's endgame). -/
theorem lambda0_independent_of_reduction {g : ℝ → ℂ}
    (h : HRTLambda0.ZakReduction g) : HRTLambda0.Lambda0Independent g := by
  sorry

end HRTLambda0.Statement
