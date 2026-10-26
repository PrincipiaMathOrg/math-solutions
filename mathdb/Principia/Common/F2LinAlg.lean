import Mathlib.Data.List.Basic

set_option autoImplicit false

/-!
# Linear algebra over `𝔽₂`, in the representation the KERNEL computes

Campaign-agnostic. A vector over `𝔽₂` is a `List Bool` and addition is `List.zipWith xor`.

**The representation is the whole engineering decision.** The obvious encoding of an `𝔽₂` vector is
an `ℕ` bitmask with `Nat.xor`, and it **cannot be used** in a `decide` proof: `Nat.xor` routes
through `Nat.bitwise`, which is well-founded recursion with none of the GMP acceleration the kernel
gives `Nat.add/sub/mul/div/mod/beq/ble`, so a kernel evaluation over bitmasks crawls or sticks.
`List Bool` with `List.zipWith xor` is structural throughout and reduces in seconds. Nothing here
uses `native_decide`, which would add `ofReduceBool` and be refused by the campaign gate — so a
proof that "needs" it needs a different representation, which is what this file is.

Elimination is the same routine in every consumer: walk the columns, take a pivot row, clear the
column from the others. `rank` is that routine with the pivot rows discarded; a consumer needing
the reduced rows themselves (an inverse, say) keeps them in a second list and eliminates each new
pivot from **both**, because eliminating only from the remaining rows leaves the finished ones
unreduced and silently breaks the inverse.

`Principia/MathDB/Problem380333.lean` predates this file and carries its own copy of `rank`
alongside a Gauss–Jordan inverse; migrating it is a separate change, deliberately not made here,
because it would move a verified row's declaration count for no mathematical gain.
-/

namespace Principia.Common.F2

/-- A vector over `𝔽₂`: `true` is 1, `false` is 0. -/
abbrev Row := List Bool

/-- Addition over `𝔽₂`, which is also subtraction. -/
def add (u v : Row) : Row := List.zipWith xor u v

/-- Elimination over the listed columns, counting pivots. -/
def rankAux : List ℕ → List Row → ℕ
  | [], _ => 0
  | (b :: bs), rows =>
      match rows.find? (fun r => r.getD b false) with
      | none => rankAux bs rows
      | some p =>
          1 + rankAux bs ((rows.filter (fun r => r ≠ p)).map
            (fun r => if r.getD b false then add r p else r))

/-- The `𝔽₂`-rank of a list of rows of width `w`. -/
def rank (w : ℕ) (rows : List Row) : ℕ := rankAux (List.range w) rows

/-- The zero vector of width `w`. -/
def zeroRow (w : ℕ) : Row := List.replicate w false

/-- Every `𝔽₂`-combination of `gens`, as a list of `2 ^ gens.length` rows of width `w`. -/
def span (w : ℕ) : List Row → List Row
  | [] => [zeroRow w]
  | g :: gs => (span w gs).flatMap (fun u => [u, add u g])

end Principia.Common.F2
