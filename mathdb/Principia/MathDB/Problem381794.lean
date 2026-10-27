import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
-- `decide` enumerates the 720 permutations of a six-element list; the default recursion depth is
-- reached while unfolding `List.permutations`.
set_option maxRecDepth 100000

/-!
# MathDB #381794 — Brenti–Sentinelli Conjecture 6.3

Write-up: `mathdb-open-problems/problems/381794/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-30).

The conjecture: the convex hull `P_m` of the **Wachs permutations** in `S_{2m}` is *simple* for
every `m ≥ 1`. The write-up proves more — `P_m` is affinely isomorphic to `Π_m × C_m`, the
ordinary `(m−1)`-dimensional permutahedron times an `m`-cube — so it has dimension `2m−1`,
`2ᵐ m!` vertices and `(2m−1) 2^{m−1} m!` edges.

## What this module proves

**The affine isomorphism, in full generality.** `T` sends `x` to
`y_i = (x_{2i−1} + x_{2i} + 1)/4` and `z_i = x_{2i} − x_{2i−1}`, and the write-up displays an
inverse. `Tinv_left` and `Tinv_right` prove the two composites are the identity — coordinatewise,
for arbitrary rationals, by `ring`. This is the write-up's whole geometric content and it is
unconditional.

**The block characterisation, computationally.** `isWachs` is the source's own condition
`|w⁻¹(i) − w⁻¹(i*)| ≤ 1`; `fromBlocks` arranges the `m` value-pairs `{2j−1, 2j}` in a chosen
order with a chosen orientation each. `wachs_eq_blocks_two` and `wachs_eq_blocks_three` prove by
kernel evaluation that the two descriptions agree **as sets**, for `m = 2` and `m = 3`, and
`wachs_card_*` that the count is `2ᵐ m!`.

**The counting arithmetic, in full generality.** `dimension_eq` (`(m−1) + m = 2m−1`) and
`edge_count` (`2·((2m−1)·2^{m−1}·m!) = 2ᵐ·m!·(2m−1)`, the handshake identity with no division).

## What is absent, established by grep before this paragraph was written

* **No polytope theory.** Mathlib has no notion of a polytope's vertices, edges or *simplicity* —
  no `IsSimplePolytope`, no face lattice — and no `permutahedron`. So "`P_m` is simple" cannot be
  stated, let alone proved; what is provable is the affine isomorphism that reduces it to two
  standard facts.
* **But `convexHull_prod` DOES exist** (`Mathlib/Analysis/Convex/Combination.lean`), so the step
  `conv(A × B) = conv(A) × conv(B)` — one of the write-up's three ingredients — is already
  available and is *not* part of the residue.

## Residue

The block lemma for **general** `m` (the write-up's induction on position pairs: `|w⁻¹(i) −
w⁻¹(i*)| ≤ 1` with distinct positions forces consecutiveness, then position 1 must pair with
position 2 and one strips the first block). It is elementary and index-heavy; the `m ≤ 3` cases
here are kernel-checked rather than assumed. Transport of the hull along `T`, and simplicity
itself, wait on the absent polytope theory.
-/

namespace Principia.MathDB.P381794

/-! ## The affine map, and it is an isomorphism -/

/-- `y_i = (x_{2i−1} + x_{2i} + 1)/4`. -/
def yOf (a b : ℚ) : ℚ := (a + b + 1) / 4

/-- `z_i = x_{2i} − x_{2i−1}`. -/
def zOf (a b : ℚ) : ℚ := b - a

/-- The write-up's displayed inverse, odd coordinate. -/
def xOdd (y z : ℚ) : ℚ := 2 * y - 1 / 2 - z / 2

/-- The write-up's displayed inverse, even coordinate. -/
def xEven (y z : ℚ) : ℚ := 2 * y - 1 / 2 + z / 2

/-- **`T⁻¹ ∘ T = id`**, coordinatewise and for arbitrary rationals. -/
theorem Tinv_left (a b : ℚ) :
    xOdd (yOf a b) (zOf a b) = a ∧ xEven (yOf a b) (zOf a b) = b := by
  refine ⟨?_, ?_⟩
  · simp only [xOdd, yOf, zOf]; ring
  · simp only [xEven, yOf, zOf]; ring

/-- **`T ∘ T⁻¹ = id`**, coordinatewise and for arbitrary rationals. -/
theorem Tinv_right (y z : ℚ) :
    yOf (xOdd y z) (xEven y z) = y ∧ zOf (xOdd y z) (xEven y z) = z := by
  refine ⟨?_, ?_⟩
  · simp only [yOf, xOdd, xEven]; ring
  · simp only [zOf, xOdd, xEven]; ring

/-- The pair sum and difference that make `T` affine: `x_{2i−1} + x_{2i} = 4y_i − 1` and
`x_{2i} − x_{2i−1} = z_i`. -/
theorem affine_coords (y z : ℚ) :
    xOdd y z + xEven y z = 4 * y - 1 ∧ xEven y z - xOdd y z = z := by
  refine ⟨?_, ?_⟩
  · simp only [xOdd, xEven]; ring
  · simp only [xOdd, xEven]; ring

/-! ## The Wachs condition and the block construction -/

/-- `i* = i+1` for odd `i`, `i−1` for even `i`. -/
def star (i : ℕ) : ℕ := if i % 2 = 1 then i + 1 else i - 1

theorem star_involutive (i : ℕ) (hi : 1 ≤ i) : star (star i) = i := by
  simp only [star]
  split_ifs <;> omega

/-- One-based position of the value `v` in the one-line word `w`. -/
def posOf (w : List ℕ) (v : ℕ) : ℕ := w.idxOf v + 1

/-- The source's condition, `|w⁻¹(i) − w⁻¹(i*)| ≤ 1` for every `i` in `[2m−1]`. -/
def isWachs (w : List ℕ) : Bool :=
  (List.range (w.length - 1)).all fun t =>
    let i := t + 1
    decide (posOf w i ≤ posOf w (star i) + 1) && decide (posOf w (star i) ≤ posOf w i + 1)

/-- Arrange the value pairs `{2j−1, 2j}` in the given order, each with the given orientation. -/
def fromBlocks (order : List ℕ) (orient : List Bool) : List ℕ :=
  (order.zip orient).flatMap fun p =>
    if p.2 then [2 * p.1 + 2, 2 * p.1 + 1] else [2 * p.1 + 1, 2 * p.1 + 2]

/-- All `2ᵐ` orientation vectors. -/
def allOrients : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allOrients n).flatMap fun e => [false :: e, true :: e]

/-- Insert `x` at every position of a list. -/
def insertAll (x : ℕ) : List ℕ → List (List ℕ)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertAll x ys).map (fun l => y :: l)

/-- All permutations of a list, by STRUCTURAL recursion.

`List.permutations` is not usable here: `decide` gets stuck on it, reduction stopping at
`Nat.beq`. It is the same trap as `Nat.xor` -- the obvious library function is not the one the
kernel computes -- and the fix is the same, namely an encoding that recurses structurally. -/
def perms : List ℕ → List (List ℕ)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap (fun p => insertAll x p)

/-- Every word built from blocks, for a given `m`. -/
def blockWords (m : ℕ) : List (List ℕ) :=
  (perms (List.range m)).flatMap fun o => (allOrients m).map fun e => fromBlocks o e

/-- Every permutation of `1, …, 2m`. -/
def allWords (m : ℕ) : List (List ℕ) := perms ((List.range (2 * m)).map (· + 1))

/-! ### `m = 2` -/

theorem wachs_card_two : ((allWords 2).filter isWachs).length = 8 := by decide

theorem blocks_card_two : (blockWords 2).dedup.length = 8 := by decide

/-- **The two descriptions agree as sets** at `m = 2`. -/
theorem wachs_eq_blocks_two :
    ((allWords 2).filter isWachs).all (fun w => (blockWords 2).contains w)
      && (blockWords 2).all (fun w => ((allWords 2).filter isWachs).contains w) = true := by
  decide

/-! ### `m = 3` -/

theorem wachs_card_three : ((allWords 3).filter isWachs).length = 48 := by decide

theorem blocks_card_three : (blockWords 3).dedup.length = 48 := by decide

/-- **The two descriptions agree as sets** at `m = 3`. -/
theorem wachs_eq_blocks_three :
    ((allWords 3).filter isWachs).all (fun w => (blockWords 3).contains w)
      && (blockWords 3).all (fun w => ((allWords 3).filter isWachs).contains w) = true := by
  decide

/-- The Wachs set is a **proper** subset: 16 of the 24 permutations in `S₄` fail the condition. -/
theorem wachs_proper_two : ((allWords 2).filter (fun w => !isWachs w)).length = 16 := by decide

/-! ## The counting arithmetic -/

/-- `2ᵐ · m!` — the vertex count, as the block description gives it. -/
def vertexCount (m : ℕ) : ℕ := 2 ^ m * Nat.factorial m

theorem vertexCount_two : vertexCount 2 = 8 := by decide

theorem vertexCount_three : vertexCount 3 = 48 := by decide

/-- `dim(Π_m × C_m) = (m−1) + m = 2m−1`. -/
theorem dimension_eq (m : ℕ) (hm : 1 ≤ m) : (m - 1) + m = 2 * m - 1 := by omega

/-- **The handshake identity**, stated without division: a `(2m−1)`-regular graph on `2ᵐ m!`
vertices has `(2m−1) 2^{m−1} m!` edges. -/
theorem edge_count (m : ℕ) (hm : 1 ≤ m) :
    2 * ((2 * m - 1) * 2 ^ (m - 1) * Nat.factorial m)
      = vertexCount m * (2 * m - 1) := by
  simp only [vertexCount]
  have hp : 2 * 2 ^ (m - 1) = 2 ^ m := by
    rw [← pow_succ']
    congr 1
    omega
  calc 2 * ((2 * m - 1) * 2 ^ (m - 1) * Nat.factorial m)
      = (2 * 2 ^ (m - 1)) * (Nat.factorial m * (2 * m - 1)) := by ring
    _ = 2 ^ m * (Nat.factorial m * (2 * m - 1)) := by rw [hp]
    _ = 2 ^ m * Nat.factorial m * (2 * m - 1) := by ring

end Principia.MathDB.P381794
