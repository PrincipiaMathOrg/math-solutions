/-
SOLUTION FILE — the same two statements as `Challenge.lean`, proved.

Each proof is a direct term assignment from the development (`Erdos361.Core`). A term
assignment forces Lean to check that the development's statement and the trusted statement
in `Challenge.lean` are DEFINITIONALLY EQUAL — which, since the development imports
`Erdos361.Statement`, is immediate. There is no transport lemma doing hidden work.

The `#print axioms` lines are a redundant local audit; Comparator performs the authoritative
check of the footprints against `Challenge.lean`. Expected footprints:
  • erdos361_cge1      : [propext, Classical.choice, Quot.sound]
  • erdos361_irregular : [propext, Classical.choice, Quot.sound]
-/
import Erdos361
import Erdos361.Statement
set_option autoImplicit false

namespace Erdos361.Statement
open Filter Topology
open scoped Pointwise

/-- **Erdős #361, regular range.** -/
theorem erdos361_cge1 (M n : ℕ) (hn : 1 ≤ n) (hM : n ≤ M) :
    F M n = M - (n + 1) / 2 :=
  Erdos361.erdos361_cge1 M n hn hM

/-- **Erdős #361, irregularity (c ∈ (0,1)).** -/
theorem erdos361_irregular (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ¬ ∃ L : ℝ, Tendsto (fun n : ℕ => (Fc c n : ℝ) / n) atTop (nhds L) :=
  Erdos361.erdos361_irregular c hc0 hc1

/-- **Erdős #361, Part 1 — Basile's Problem 7.1.** Proved by direct term assignment from the
development's `Erdos361BasileMaster.basile71_fully_unconditional` (the fully unconditional form, with
Freiman `3k-3` discharged by the in-project `Erdos361Freiman.freiman_3k3`); the trusted `Avoids` here
and the development's `Avoids` are definitionally equal, so Lean checks the two statements agree. -/
theorem basile71_unconditional (ε : ℝ) (hε : 0 < ε) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E →
      (1 / 3 + ε) * E ≤ (A.card : ℝ) →
      ∀ t : ℕ, 2 * E < t → t < 3 * E → 2 ∣ t → ¬ 3 ∣ t → ¬ Avoids A t :=
  Erdos361BasileMaster.basile71_fully_unconditional ε hε

#print axioms erdos361_cge1
#print axioms erdos361_irregular
#print axioms basile71_unconditional

end Erdos361.Statement
