import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Logic.Relation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# MathDB #335493 — Li–Liu Conjecture 4.6 is FALSE

Write-up: `mathdb-open-problems/problems/335493/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-28 from the
third hundred, see `THIRD100-ENROLMENT.md`).
Source: F. Li and S. Liu, *On exchange spectra of valued quivers and cluster algebras*, Pure Appl.
Math. Q. **16** (2020) 1533–1561 (arXiv:1703.02225v1), **Conjecture 4.6**: any two quivers in one
mutation class with the same exchange spectrum can be connected by mutations at sinks and sources,
after allowing an initial quiver isomorphism.

**The counterexample is the write-up's own**, on three vertices:

`1 --3--> 2`,  `2 --4--> 3`,  `3 --6--> 1`,  i.e. `B = !![0, 3, -6; -3, 0, 4; 6, -4, 0]`.

`conjecture_4_6_false` carries **no hypotheses**.

## Why the refutation needs no bound on the length of the mutation sequence

The conjecture quantifies over *arbitrarily long* sequences of sink/source mutations, which sounds
like an induction. It is not one. **Every vertex of `B` has both an incoming and an outgoing arrow,
and that property is invariant under relabelling**, so no quiver isomorphic to `B` admits even a
*first* allowed mutation (`no_step_of_iso`). The reachability relation therefore collapses:
`Relation.ReflTransGen Step R _` with no step available forces the empty sequence
(`reachable_eq_of_iso`, by `ReflTransGen.cases_head`), so the target would have to *be* `R` — and
`R` is isomorphic to `B` while the target is `Bᵒᵖ = -B`, which is not (`not_quiverIso_B_negB`).
Three finite checks and one collapse; no induction on sequence length anywhere.

## The three finite facts, all `decide`

* `mutAt 1 B = -B` — mutating at the middle vertex gives the **opposite** quiver, so both lie in one
  mutation class. `mutAt` is the literature's formula, `/ 2` and all:
  `b'ᵢⱼ = -bᵢⱼ` on row/column `k`, else `bᵢⱼ + (|bᵢₖ|bₖⱼ + bᵢₖ|bₖⱼ|)/2`. **The integer division
  reduces in the kernel**, so no division-free reformulation was needed — worth recording, since
  `Rat` division does *not* (see #338791).
* `¬ QuiverIso B (-B)` — none of the six vertex permutations carries `B` to `-B`.
* `∀ i, (∃ j, 0 < B i j) ∧ (∃ j, B i j < 0)` — no sinks, no sources.

## The spectrum, and what the verifier added

`charAt A l = det(l·I − A)` is `l³ + 61l` for both `B` and `-B`, so the exchange spectra agree.
`charAt_skew` proves the *general* fact behind it — for any skew `3 × 3` with entries `a, b, c` the
polynomial is `l³ + (a² + b² + c²)l` — which is the verifier's independent second route and explains
*why* `B` and `-B` are cospectral: the polynomial sees only the three multiplicities, which negation
does not change. `61 = 3² + 4² + 6²`.

## 215 check — the distinctness of `3, 4, 6` is load-bearing, and the verifier shows it

The write-up says only *"The three such numbers are distinct, so each of the three underlying edges
must map to itself"*. It does not say what goes wrong otherwise, so a reader cannot tell whether
distinctness is essential or incidental. It is essential: `verify_335493.py` checks that the
**all-ones 3-cycle `!![0,1,-1; -1,0,1; 1,-1,0]` *is* isomorphic to its own opposite**, via each of
the three transpositions. With equal multiplicities the whole argument collapses, so the example's
choice of `3, 4, 6` is the substance of the second paragraph rather than decoration.

Also checked and holding: loops and oriented `2`-cycles are absent (`B` is skew with zero diagonal);
mutation is an involution at each vertex, so "same mutation class" is symmetric as the source
intends; and the source's definition permits multiple arrows, which this example needs.
-/

namespace Principia.MathDB.P335493

open Matrix

/-- Exchange matrices on three vertices. -/
abbrev Ex := Matrix (Fin 3) (Fin 3) ℤ

/-- **Matrix mutation**, exactly the literature's formula including the `/ 2`. -/
def mutAt (k : Fin 3) (A : Ex) : Ex :=
  Matrix.of fun i j =>
    if i = k ∨ j = k then -A i j
    else A i j + (|A i k| * A k j + A i k * |A k j|) / 2

/-- The write-up's quiver: `1 --3--> 2`, `2 --4--> 3`, `3 --6--> 1`. -/
def B : Ex := !![0, 3, -6; -3, 0, 4; 6, -4, 0]

/-- `B` is skew with zero diagonal: no loops and no oriented `2`-cycles. -/
theorem B_skew : Bᵀ = -B := by decide

theorem B_diag_zero : ∀ i, B i i = 0 := by decide

/-- **Mutating at the middle vertex gives the opposite quiver**, so `B` and `-B` lie in one
mutation class. -/
theorem mutAt_one_B : mutAt 1 B = -B := by decide

/-- Mutation is an involution, so "same mutation class" is symmetric. -/
theorem mutAt_involutive_B : ∀ k : Fin 3, mutAt k (mutAt k B) = B := by decide

/-! ### The exchange spectrum -/

/-- `det(l · I − A)`, the characteristic value at `l`. -/
def charAt (A : Ex) (l : ℤ) : ℤ :=
  (Matrix.of fun i j => (if i = j then l else 0) - A i j).det

/-- The general skew `3 × 3` characteristic polynomial: it sees only `a, b, c` through their
squares, which is exactly why negating the quiver cannot change the spectrum. -/
theorem charAt_skew (a b c l : ℤ) :
    charAt !![0, a, b; -a, 0, c; -b, -c, 0] l = l ^ 3 + (a ^ 2 + b ^ 2 + c ^ 2) * l := by
  simp [charAt, Matrix.det_fin_three]
  ring

theorem charAt_B (l : ℤ) : charAt B l = l ^ 3 + 61 * l := by
  have h : B = !![0, 3, -6; -3, 0, 4; -(-6), -4, 0] := by decide
  rw [h, charAt_skew]
  ring

theorem charAt_negB (l : ℤ) : charAt (-B) l = l ^ 3 + 61 * l := by
  have h : -B = !![0, -3, 6; -(-3), 0, -4; -6, -(-4), 0] := by decide
  rw [h, charAt_skew]
  ring

/-- **The two quivers are cospectral.** -/
theorem cospectral (l : ℤ) : charAt B l = charAt (-B) l := by
  rw [charAt_B, charAt_negB]

/-! ### Quiver isomorphism -/

/-- A quiver isomorphism is a relabelling of the vertices. -/
def QuiverIso (A A' : Ex) : Prop := ∃ σ : Equiv.Perm (Fin 3), ∀ i j, A' (σ i) (σ j) = A i j

instance instDecidableQuiverIso (A A' : Ex) : Decidable (QuiverIso A A') := by
  unfold QuiverIso; infer_instance

/-- **`B` is NOT isomorphic to its opposite.** None of the six relabellings works — and the reason
is that the three arrow multiplicities `3, 4, 6` are pairwise distinct; see the module header. -/
theorem not_quiverIso_B_negB : ¬ QuiverIso B (-B) := by decide

/-- POSITIVE CONTROL: the test is not vacuous — the identity is a self-isomorphism. -/
theorem quiverIso_B_self : QuiverIso B B := by decide

/-! ### Sinks, sources, and the collapse of the reachability relation -/

/-- A sink has no outgoing arrows. -/
def IsSink (A : Ex) (i : Fin 3) : Prop := ∀ j, A i j ≤ 0

/-- A source has no incoming arrows. -/
def IsSource (A : Ex) (i : Fin 3) : Prop := ∀ j, 0 ≤ A i j

/-- Every vertex of `B` has an outgoing arrow. -/
theorem B_out : ∀ i : Fin 3, ∃ j, 0 < B i j := by decide

/-- Every vertex of `B` has an incoming arrow. -/
theorem B_in : ∀ i : Fin 3, ∃ j, B i j < 0 := by decide

theorem not_isSink_of_quiverIso {R : Ex} (h : QuiverIso B R) (i : Fin 3) : ¬ IsSink R i := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨j, hj⟩ := B_out (σ.symm i)
  intro hsink
  have hR : R (σ (σ.symm i)) (σ j) = B (σ.symm i) j := hσ _ _
  rw [Equiv.apply_symm_apply] at hR
  have := hsink (σ j)
  rw [hR] at this
  exact absurd hj (not_lt.mpr this)

theorem not_isSource_of_quiverIso {R : Ex} (h : QuiverIso B R) (i : Fin 3) : ¬ IsSource R i := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨j, hj⟩ := B_in (σ.symm i)
  intro hsrc
  have hR : R (σ (σ.symm i)) (σ j) = B (σ.symm i) j := hσ _ _
  rw [Equiv.apply_symm_apply] at hR
  have := hsrc (σ j)
  rw [hR] at this
  exact absurd hj (not_lt.mpr this)

/-- One allowed move: a mutation at a sink or a source. -/
def Step (A A' : Ex) : Prop := ∃ k, (IsSink A k ∨ IsSource A k) ∧ A' = mutAt k A

/-- **No quiver isomorphic to `B` admits even a first allowed move.** This is what removes the
induction on sequence length. -/
theorem no_step_of_quiverIso {R : Ex} (h : QuiverIso B R) : ∀ A', ¬ Step R A' := by
  rintro A' ⟨k, hk, -⟩
  rcases hk with hk | hk
  · exact not_isSink_of_quiverIso h k hk
  · exact not_isSource_of_quiverIso h k hk

/-- **The reachability relation collapses**: with no step available, the only sequence is empty. -/
theorem reachable_eq_of_quiverIso {R A : Ex} (h : QuiverIso B R)
    (hr : Relation.ReflTransGen Step R A) : R = A := by
  rcases hr.cases_head with h0 | ⟨c, hc, -⟩
  · exact h0
  · exact absurd hc (no_step_of_quiverIso h c)

/-! ## The refutation, assembled -/

/-- **LI–LIU CONJECTURE 4.6 IS FALSE.** `B` and its opposite lie in one mutation class (a single
mutation at vertex `2` connects them) and are cospectral, yet no quiver isomorphic to `B` reaches
`-B` by mutations at sinks and sources — not by any sequence, of any length. -/
theorem conjecture_4_6_false :
    (∃ k : Fin 3, mutAt k B = -B)
      ∧ (∀ l : ℤ, charAt B l = charAt (-B) l)
      ∧ ¬ ∃ R : Ex, QuiverIso B R ∧ Relation.ReflTransGen Step R (-B) := by
  refine ⟨⟨1, mutAt_one_B⟩, cospectral, ?_⟩
  rintro ⟨R, hiso, hreach⟩
  have hRB : R = -B := reachable_eq_of_quiverIso hiso hreach
  rw [hRB] at hiso
  exact not_quiverIso_B_negB hiso

end Principia.MathDB.P335493
