/-
TRUSTED CHALLENGE FILE — the statements, without proofs.

This file is the audit surface. Comparator (github.com/leanprover/comparator) checks that
the corresponding declarations in `Solution.lean` prove EXACTLY these statements, using no
axioms beyond the permitted list in `comparator/*.json`:
  • `erdos361_cge1`      — [propext, Quot.sound, Classical.choice]  (axiom-free).
  • `erdos361_irregular` — [propext, Quot.sound, Classical.choice]  (axiom-free). Alon 1987
    Thm 1.1, formerly postulated, is now PROVED in `Erdos361/Core.lean` (general-h Dias da
    Silva–Hamidoune from Mathlib's Combinatorial Nullstellensatz, on the subsequence n = 2p).

The `sorry`s below are deliberate and are the only `sorry`s in the repository.

IMPORT CLOSURE: Mathlib only, as Palomar's Challenge policy requires. The definitions
in the first namespace block below are a verbatim copy of `Erdos361/Statement.lean`, the
module the development and `Solution.lean` import; Comparator checks that the two
copies agree declaration by declaration, so a drift between them fails the check.

WHAT EACH STATEMENT SAYS, in words:

  erdos361_cge1      For 1 ≤ n ≤ M, the max cardinality of a subset of [1,M] with no subset
                     summing to n equals M − ⌈n/2⌉ (here `(n+1)/2` = ⌈n/2⌉ in ℕ). Hence for
                     c ≥ 1, f_c(n)/n → c − 1/2: the regular range.

  erdos361_irregular Erdős–Graham irregularity. For every real c ∈ (0,1) the sequence
                     f_c(n)/n = F ⌊cn⌋ n / n does NOT converge.
-/
import Mathlib
set_option autoImplicit false

namespace Erdos361.Statement
open Finset
open scoped Classical
def Avoids (A : Finset ℕ) (n : ℕ) : Prop := ∀ B ⊆ A, B.sum id = n → B = ∅
noncomputable def Avoiders (M n : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 M).powerset.filter (fun A => Avoids A n)
noncomputable def F (M n : ℕ) : ℕ := (Avoiders M n).sup Finset.card
noncomputable def Fc (c : ℝ) (n : ℕ) : ℕ := F ⌊c * n⌋₊ n
end Erdos361.Statement

namespace Erdos361.Statement
open Filter Topology
open scoped Pointwise

/-- **Erdős #361, regular range.** For `1 ≤ n ≤ M`, `F M n = M − ⌈n/2⌉`. -/
theorem erdos361_cge1 (M n : ℕ) (hn : 1 ≤ n) (hM : n ≤ M) :
    F M n = M - (n + 1) / 2 := by
  sorry

/-- **Erdős #361, irregularity (c ∈ (0,1)).** `f_c(n)/n` does not converge. -/
theorem erdos361_irregular (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ¬ ∃ L : ℝ, Tendsto (fun n : ℕ => (Fc c n : ℝ) / n) atTop (nhds L) := by
  sorry

/-- **Erdős #361, Part 1 — Basile's Problem 7.1 (snd = 3 linear case).** For every `ε > 0` there is an
`E₀` such that for all `E ≥ E₀`, every `A ⊆ [1,E]` of density `≥ 1/3 + ε` represents every even
`t ∈ (2E, 3E)` with `3 ∤ t` (i.e. `¬ Avoids A t`). **Fully unconditional and axiom-free** — no cited
hypothesis: Freiman's `3k-3` theorem (`|B+B| ≥ min{L,2|B|-3}+|B|`), which earlier revisions carried as
the hypothesis `hFreiman`, is now **proved from scratch** in `Erdos361/BasileFreiman.lean`
(`Erdos361Freiman.freiman_3k3`, Nathanson's Kneser-free induction, no Mathlib port exists). Alon's
Prop 2.5 good core and the located covering are likewise *proved* in-development (`good_core_exists`,
`hLev_covering`), the latter avoiding Lev 1997 entirely. -/
theorem basile71_unconditional (ε : ℝ) (hε : 0 < ε) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E →
      (1 / 3 + ε) * E ≤ (A.card : ℝ) →
      ∀ t : ℕ, 2 * E < t → t < 3 * E → 2 ∣ t → ¬ 3 ∣ t → ¬ Avoids A t := by
  sorry

end Erdos361.Statement
