/-
SOLUTION FILE — the same statement as `Challenge.lean`, proved.

The proof is a direct term assignment from the development
(`HRTLambda0.lambda0_independent_of_reduction` in `HRTLambda0/Endgame.lean`). A term
assignment forces Lean to check that the development's statement and the trusted
statement in `Challenge.lean` are DEFINITIONALLY EQUAL — there is no transport lemma
doing hidden work.

The `#print axioms` line is a redundant local audit; Comparator performs the
authoritative check of the footprint against `Challenge.lean`. Expected footprint:
  • lambda0_independent_of_reduction : [propext, Classical.choice, Quot.sound]
-/
import HRTLambda0
set_option autoImplicit false

namespace HRTLambda0.Statement

/-- **HRT at `Λ₀`, conditional on the analytic reduction** (the paper's endgame). -/
theorem lambda0_independent_of_reduction {g : ℝ → ℂ}
    (h : HRTLambda0.ZakReduction g) : HRTLambda0.Lambda0Independent g :=
  _root_.HRTLambda0.lambda0_independent_of_reduction h

#print axioms lambda0_independent_of_reduction

end HRTLambda0.Statement
