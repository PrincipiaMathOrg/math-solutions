/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# MathDB #332161 — the Schur–Brauer version of van der Waerden's theorem for semimodules is FALSE

MathDB open problem #332161, from Xiongping Dai, *"Grünwald version of van der Waerden's theorem
for semi-modules"*, [arXiv:1512.08695](https://arxiv.org/abs/1512.08695), Conjecture 3.26:

> Let `G = B₁ ∪ ⋯ ∪ B_q` be a finite partition of a semimodule `(G, +)` over a semiring
> `(R, +, ·)`.  For a subset `F ⊆ R` write `Fb = {f b : f ∈ F}`.  **One of the sets `B_j` has the
> property that, for every finite subset `F` of `R`, there are elements `a ∈ G` and `b ∈ B_j` with
> `b ≠ o` such that `a + F b ⊆ B_j`.**

The claim is false, and the counterexample is two elements wide: take `R = G = 𝔽₂` with `G` the
regular module, split into the singletons `{0}` and `{1}`, and take `F = {0, 1}`.  The cell `{0}`
holds no permitted `b ≠ 0` at all; in the cell `{1}` the only candidate is `b = 1`, and then
`a + F b = {a, a + 1} = 𝔽₂ ⊄ {1}` for either `a`.  One finite set defeats both cells.

Campaign source: `mathdb-open-problems/problems/332161/` in the collaborator repository
`antoshashakov/Principia-Math-In-Progress` (solution, proof skeleton, literature audit and a
finite `certificate.json` checked by `verify_counterexample.py`).  This file replaces that
certificate's finite search by a kernel-checked proof.

## What is certified here

Everything.  There is no hypothesis, no `sorry`, and no analytic input: the file proves an
unconditional negation, and the acceptance gate is the axiom footprint
`[propext, Classical.choice, Quot.sound]`.

## Why the statement is formalized twice

`SchurBrauerSource` transcribes the source's own axiom list — a bundled `SourceSemiring` and
`SourceSemimodule`, no Mathlib typeclass in sight — because the conjecture quantifies over *that*
class, and a refutation must land on the statement as posed.

`SchurBrauerModule` is the same sentence over Mathlib's `Semiring`/`Module`.  That is a **strictly
smaller** class of structures (Mathlib additionally demands scalar associativity `(r * t) • g =
r • (t • g)` and `r • 0 = 0`), so `SchurBrauerSource → SchurBrauerModule` — `module_of_source`
below — and refuting the Mathlib version is therefore the *stronger* of the two results.  The
witness `ZMod 2` is in fact a field, so the refutation survives every strengthening of the
algebraic hypotheses the source could plausibly have intended.  The partition hypothesis is
strengthened in the same direction: `IsFinitePartition` demands cells that are nonempty, pairwise
disjoint and covering, which makes the conjecture weaker and the refutation stronger again.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Principia.MathDB.P332161

/-! ### The source's algebra, transcribed

Dai's definitions: a semiring is an abelian additive semigroup with zero, an associative
multiplicative semigroup with unit and absorbing zero, and both distributive laws; a left
semimodule is an abelian additive semigroup with zero carrying an action satisfying the four
displayed identities.  Neither definition asks for cancellation, negatives, commutativity of
multiplication, scalar associativity, or infinitude. -/

/-- A semiring in the source's sense. -/
structure SourceSemiring (R : Type) where
  add : R → R → R
  mul : R → R → R
  zero : R
  one : R
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  add_zero : ∀ a, add a zero = a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  zero_mul : ∀ a, mul zero a = zero
  mul_zero : ∀ a, mul a zero = zero
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)

/-- A left semimodule over `S` in the source's sense; `zero` is the source's `o`. -/
structure SourceSemimodule (R M : Type) (S : SourceSemiring R) where
  add : M → M → M
  zero : M
  smul : R → M → M
  add_assoc : ∀ g h k, add (add g h) k = add g (add h k)
  add_comm : ∀ g h, add g h = add h g
  add_zero : ∀ g, add g zero = g
  add_smul : ∀ r t g, smul (S.add r t) g = add (smul r g) (smul t g)
  smul_add : ∀ r g h, smul r (add g h) = add (smul r g) (smul r h)
  one_smul : ∀ g, smul S.one g = g
  zero_smul : ∀ g, smul S.zero g = zero

/-- A finite partition into `q` cells: nonempty, pairwise disjoint, covering. -/
structure IsFinitePartition {M : Type} {q : ℕ} (B : Fin q → Set M) : Prop where
  nonempty : ∀ j, (B j).Nonempty
  disjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j)
  cover : ∀ x, ∃ j, x ∈ B j

/-! ### The conjecture -/

/-- **MathDB #332161, as posed** — over the source's own semiring/semimodule axioms. -/
def SchurBrauerSource : Prop :=
  ∀ (R M : Type) (S : SourceSemiring R) (N : SourceSemimodule R M S)
    (q : ℕ) (B : Fin q → Set M), IsFinitePartition B →
    ∃ j, ∀ F : Finset R, ∃ a b : M,
      b ∈ B j ∧ b ≠ N.zero ∧ ∀ f ∈ F, N.add a (N.smul f b) ∈ B j

/-- The same sentence over Mathlib's `Semiring`/`Module`, i.e. over a **smaller** class of
structures.  This is the version actually refuted below. -/
def SchurBrauerModule : Prop :=
  ∀ (R M : Type) [Semiring R] [AddCommMonoid M] [Module R M]
    (q : ℕ) (B : Fin q → Set M), IsFinitePartition B →
    ∃ j, ∀ F : Finset R, ∃ a b : M,
      b ∈ B j ∧ b ≠ 0 ∧ ∀ f ∈ F, a + f • b ∈ B j

/-! ### Every Mathlib module is a source semimodule -/

/-- A Mathlib `Semiring` satisfies the source's semiring axioms. -/
def ofSemiring (R : Type) [Semiring R] : SourceSemiring R where
  add := (· + ·)
  mul := (· * ·)
  zero := 0
  one := 1
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := mul_add
  right_distrib := add_mul

/-- A Mathlib `Module` satisfies the source's semimodule axioms. -/
def ofModule (R M : Type) [Semiring R] [AddCommMonoid M] [Module R M] :
    SourceSemimodule R M (ofSemiring R) where
  add := (· + ·)
  zero := 0
  smul := (· • ·)
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  add_smul := add_smul
  smul_add := smul_add
  one_smul := fun g => one_smul R g
  zero_smul := fun g => zero_smul R g

/-- The conjecture over the source's class implies the conjecture over Mathlib's, because the
latter class is contained in the former. -/
theorem module_of_source (h : SchurBrauerSource) : SchurBrauerModule :=
  fun R M _ _ _ q B hB => h R M (ofSemiring R) (ofModule R M) q B hB

/-! ### The counterexample: the regular `𝔽₂`-module, split into singletons -/

/-- The two colour classes `B₁ = {0}`, `B₂ = {1}` of `𝔽₂`. -/
def cells : Fin 2 → Set (ZMod 2) := ![{0}, {1}]

theorem cells_isFinitePartition : IsFinitePartition cells where
  nonempty j := by fin_cases j <;> exact ⟨_, rfl⟩
  disjoint i j hij := by
    fin_cases i <;> fin_cases j <;> simp_all [cells]
  cover x := by
    have hx : x = 0 ∨ x = 1 := by revert x; decide
    rcases hx with h | h
    · exact ⟨0, by simp [cells, h]⟩
    · exact ⟨1, by simp [cells, h]⟩

/-! ### The refutation -/

/-- **MathDB #332161 is false**, already over Mathlib's `Semiring`/`Module`: the single finite set
`F = {0, 1} ⊆ 𝔽₂` defeats both cells of the singleton partition of the regular `𝔽₂`-module. -/
theorem not_schurBrauerModule : ¬ SchurBrauerModule := by
  intro h
  obtain ⟨j, hj⟩ := h (ZMod 2) (ZMod 2) 2 cells cells_isFinitePartition
  obtain ⟨a, b, hb, hb0, hF⟩ := hj Finset.univ
  -- `f = 0` puts `a` itself into the cell; `f = 1` puts `a + b` into it.
  have h0 : a ∈ cells j := by simpa using hF 0 (Finset.mem_univ _)
  have h1 : a + b ∈ cells j := by simpa using hF 1 (Finset.mem_univ _)
  fin_cases j
  · -- the cell `{0}` contains no permitted `b`
    simp [cells] at hb
    exact hb0 hb
  · -- the cell `{1}` forces `b = 1`, `a = 1` and `a + b = 1`, i.e. `0 = 1` in `𝔽₂`
    simp [cells] at hb h0 h1
    subst hb
    subst h0
    exact absurd h1 (by decide)

/-- **MathDB #332161, as posed, is false.** -/
theorem not_schurBrauerSource : ¬ SchurBrauerSource :=
  fun h => not_schurBrauerModule (module_of_source h)

end Principia.MathDB.P332161
