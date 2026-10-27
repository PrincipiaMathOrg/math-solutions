/-
TRUSTED STATEMENT LAYER — Erdős Problem #361.

Import closure: Mathlib only. Contains ONLY definitions — NO axioms. (Alon 1987 Thm 1.1,
formerly postulated here, is now PROVED axiom-free in `Erdos361/Core.lean` via general-h
Dias da Silva–Hamidoune from Mathlib's Combinatorial Nullstellensatz.) This file +
`Challenge.lean` are the entire audit surface: read them and you have read everything you
must trust.

The definitions are verbatim copies of the development's (`Erdos361/Core.lean`, namespace
`Erdos361`, which imports this file); `Solution.lean` proves each headline theorem by direct
term assignment, forcing Lean to check the two agree.

Palomar requires `Challenge.lean` to import nothing but Mathlib (and Lean core, Tau Ceti,
CSLib), so `Challenge.lean` carries a verbatim copy of these definitions instead of
importing this module. Keep the two in sync; Comparator fails when they differ.
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
