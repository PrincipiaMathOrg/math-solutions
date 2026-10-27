import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Enumerators the KERNEL computes

Campaign-agnostic. These are structurally recursive replacements for the library's enumeration
functions, written so that `decide` can evaluate them.

**Why they exist.** `List.permutations` does **not** kernel-reduce: a `decide` over it fails with
reduction *"stuck at `Nat.beq`"*, and the error names the outermost `Decidable` instance rather
than the function that actually got stuck. It is the same trap as `Nat.xor` routing through
`Nat.bitwise` — a library function that is perfectly computable and that the kernel nevertheless
will not unfold. `perms` below recurses structurally and evaluates in seconds on inputs of size
six (720 permutations).

The rule the whole family instantiates: **before a `decide`, ask of every library function in the
term whether the KERNEL computes it, not whether it is computable.**

`Principia/MathDB/Problem381794.lean` predates this file and carries its own copy of `insertAll`
and `perms`; migrating it is a separate change, deliberately not made here, because it would move
a banked row's declaration count for no mathematical gain.
-/

namespace Principia.Common.ListEnum

variable {α : Type*}

/-- Insert `x` at every position of `l`, giving `l.length + 1` lists. -/
def insertAll (x : α) : List α → List (List α)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertAll x ys).map (fun l => y :: l)

/-- All permutations of `l`, by structural recursion — the kernel-computable replacement for
`List.permutations`. -/
def perms : List α → List (List α)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap (fun p => insertAll x p)

/-- Prepend each of `vals` to each list of `l`. -/
def extendBy (vals : List α) (l : List (List α)) : List (List α) :=
  l.flatMap fun t => vals.map fun v => v :: t

/-- All `n`-tuples drawn from `vals`, as lists of length `n`. -/
def tuples (vals : List α) : ℕ → List (List α)
  | 0 => [[]]
  | n + 1 => extendBy vals (tuples vals n)

/-! ## Counting -/

theorem length_insertAll (x : α) (l : List α) : (insertAll x l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
      simp only [insertAll, List.length_cons, List.length_map, ih]

theorem length_tuples (vals : List α) (n : ℕ) :
    (tuples vals n).length = vals.length ^ n := by
  induction n with
  | zero => simp [tuples]
  | succ k ih =>
      simp only [tuples, extendBy, List.length_flatMap, List.length_map]
      rw [List.map_const', List.sum_const_nat, ih]
      ring

/-- Every permutation produced has the same length as the input. -/
theorem length_mem_insertAll (x : α) (l p : List α) (hp : p ∈ insertAll x l) :
    p.length = l.length + 1 := by
  induction l generalizing p with
  | nil =>
      simp only [insertAll, List.mem_singleton] at hp
      subst hp
      rfl
  | cons y ys ih =>
      simp only [insertAll, List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨q, hq, rfl⟩
      · simp
      · simp only [List.length_cons, ih q hq]

theorem length_mem_perms (l p : List α) (hp : p ∈ perms l) : p.length = l.length := by
  induction l generalizing p with
  | nil =>
      simp only [perms, List.mem_singleton] at hp
      subst hp
      rfl
  | cons x xs ih =>
      simp only [perms, List.mem_flatMap] at hp
      obtain ⟨q, hq, hp⟩ := hp
      rw [length_mem_insertAll x q p hp, ih q hq]
      simp

theorem length_perms (l : List α) : (perms l).length = Nat.factorial l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [perms, List.length_flatMap]
      have hconst : ∀ q ∈ perms xs, (insertAll x q).length = xs.length + 1 := by
        intro q hq
        rw [length_insertAll, length_mem_perms xs q hq]
      rw [List.map_congr_left hconst, List.map_const', List.sum_const_nat, ih]
      simp [Nat.factorial_succ, Nat.mul_comm]

end Principia.Common.ListEnum
