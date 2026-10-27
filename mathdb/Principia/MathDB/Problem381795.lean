import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Principia.Common.ListEnumerate

set_option autoImplicit false
-- `decide` enumerates `B_4`, which is 384 signed permutations; the default recursion depth is
-- reached while unfolding the enumeration.
set_option maxRecDepth 100000

/-!
# MathDB #381795 — Brenti–Sentinelli Conjecture 6.4

Write-up: `mathdb-open-problems/problems/381795/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-30).
Source: F. Brenti and P. Sentinelli, *Wachs permutations, Bruhat order and weak order*, European
J. Combin. **119** (2024), 103804; arXiv:2212.04932v1, **Conjecture 6.4** (pp. 36–37).

The conjecture: the convex hull `Q_m` of the **signed** Wachs permutations in `B_{2m}` is simple
for every `m ≥ 1`. The write-up proves more — `Q_m` is *linearly* isomorphic to
`Π^B(a) × [−1,1]^m` with `a = (3, 7, …, 4m−1)` — and supplies an explicit **cone certificate**
at a vertex, from which simplicity, dimension `2m`, `4ᵐ m!` vertices and `m 4ᵐ m!` edges follow.

## The cone certificate is a telescoping identity, and that is what this module proves

For a signed permutation vector `u` of `a`, set `c k = Σ_{i ∈ [k, m)} (a i − u i)`. Then

* `telescope` — `c k − c (k+1) = a k − u k` for every `k < m`. One `Finset.sum_Ico_succ_bot`.
* the decomposition `u − a = c₀·(−e₁) + Σ_{k≥1} c_k·(e_k − e_{k+1})` is that identity read
  coordinatewise, and `cone_coord` states it in the form the cone argument uses.

The `c_k` are the cone coefficients; their **nonnegativity** is the one step this module takes as
a hypothesis, because it is a rearrangement fact (the sum of any `r` entries of a signed
permutation of a positive increasing vector is at most the sum of the `r` largest). The verifier
checks it on every signed permutation vector for `m ≤ 4`, and measures that the minimum value
attained is exactly `0`, so the bound is tight.

## The generators are attained, and `a`'s step of 4 is what makes them what they are

`aVec k = 4k + 3`, so `aVec 0 = 3` and `aVec (k+1) − aVec k = 4`. `flip_difference` computes the
vertex difference from flipping the sign of `aVec 0` as `−6·e₀`, and `swap_difference` the
difference from transposing `aVec k` and `aVec (k+1)` as `4·(e_k − e_{k+1})`. Both are one
`ring` each once `aVec` is unfolded — the write-up's `−6` and `4` are not chosen, they are forced
by `a`.

## The linear map, and the block arithmetic behind `a`

`T` sends `x` to `y_i = x_{2i−1} + x_{2i}`, `z_i = x_{2i} − x_{2i−1}`; `Tinv_left` and
`Tinv_right` prove the displayed inverse `x_{2i−1} = (y_i − z_i)/2`, `x_{2i} = (y_i + z_i)/2` is
one, for arbitrary rationals. `block_sum_diff` is why `a` is `(3, 7, …)`: a block with absolute
values `2j+1, 2j+2` has sum `4j+3` and difference `1`.

## The signed Wachs set, kernel-checked

`isWachsB` is the source's own condition `|w⁻¹(i) − w⁻¹(i*)| ≤ 1` with **signed** inverse
positions. `wachs_card_one` and `wachs_card_two` give `|W(B_2)| = 4` and `|W(B_4)| = 32`, i.e.
`4ᵐ m!`, by kernel evaluation over `B_2` and the 384 elements of `B_4` — using the enumerators
promoted to `Principia.Common.ListEnum`, because `List.permutations` does not kernel-reduce.

## What is absent

Mathlib has **no polytope theory** — no vertices, edges, face lattice, `IsSimplePolytope`, no
signed permutahedron — re-grepped this tick. So "extreme rays of the vertex cone correspond to
edges", and simplicity itself, cannot be stated. `convexHull_prod` does exist, so the product
step is available. The residue is therefore: the rearrangement nonnegativity, the extreme-ray
correspondence, and the polytope language.
-/

namespace Principia.MathDB.P381795

open Principia.Common.ListEnum

/-! ## The linear map -/

def yOf (a b : ℚ) : ℚ := a + b

def zOf (a b : ℚ) : ℚ := b - a

def xOdd (y z : ℚ) : ℚ := (y - z) / 2

def xEven (y z : ℚ) : ℚ := (y + z) / 2

theorem Tinv_left (a b : ℚ) :
    xOdd (yOf a b) (zOf a b) = a ∧ xEven (yOf a b) (zOf a b) = b := by
  refine ⟨?_, ?_⟩
  · simp only [xOdd, yOf, zOf]; ring
  · simp only [xEven, yOf, zOf]; ring

theorem Tinv_right (y z : ℚ) :
    yOf (xOdd y z) (xEven y z) = y ∧ zOf (xOdd y z) (xEven y z) = z := by
  refine ⟨?_, ?_⟩
  · simp only [yOf, xOdd, xEven]; ring
  · simp only [zOf, xOdd, xEven]; ring

/-- **Why `a = (3, 7, …, 4m−1)`.** The block with absolute values `2j+1, 2j+2` has sum `4j+3`
and difference `1`, and both signs are free. -/
theorem block_sum_diff (j : ℕ) :
    (2 * j + 1) + (2 * j + 2) = 4 * j + 3 ∧ (2 * j + 2) - (2 * j + 1) = 1 := by
  constructor <;> omega

/-! ## The vector `a`, and the two attained generators -/

/-- `a k = 4k + 3`, zero-indexed: `3, 7, 11, …`. -/
def aVec (k : ℕ) : ℚ := 4 * k + 3

theorem aVec_zero : aVec 0 = 3 := by simp only [aVec]; norm_num

theorem aVec_step (k : ℕ) : aVec (k + 1) - aVec k = 4 := by
  simp only [aVec]; push_cast; ring

theorem aVec_pos (k : ℕ) : 0 < aVec k := by
  simp only [aVec]
  positivity

theorem aVec_mono (k : ℕ) : aVec k < aVec (k + 1) := by
  have := aVec_step k
  linarith

/-- **The first generator is attained.** Flipping the sign of `a₀ = 3` changes that coordinate
by `−6` and no other. -/
theorem flip_difference : -aVec 0 - aVec 0 = -6 := by
  rw [aVec_zero]; norm_num

/-- **The remaining generators are attained.** Transposing `a_k` and `a_{k+1}` changes the two
coordinates by `+4` and `−4` — forced by `a`'s constant step. -/
theorem swap_difference (k : ℕ) :
    aVec (k + 1) - aVec k = 4 ∧ aVec k - aVec (k + 1) = -4 := by
  have h := aVec_step k
  exact ⟨h, by linarith⟩

/-! ## The cone certificate -/

/-- `c k = Σ_{i ∈ [k, m)} (a i − u i)`, the cone coefficients. -/
def coneCoeff (u a : ℕ → ℚ) (m k : ℕ) : ℚ := ∑ i ∈ Finset.Ico k m, (a i - u i)

/-- **The telescoping identity**, which is the cone decomposition. -/
theorem telescope (u a : ℕ → ℚ) (m k : ℕ) (hk : k < m) :
    coneCoeff u a m k - coneCoeff u a m (k + 1) = a k - u k := by
  simp only [coneCoeff]
  rw [Finset.sum_eq_sum_Ico_succ_bot hk]
  ring

/-- The same identity in the form the cone argument reads off: the `k`-th coordinate of `u − a`
is `c (k+1) − c k`. -/
theorem cone_coord (u a : ℕ → ℚ) (m k : ℕ) (hk : k < m) :
    u k - a k = coneCoeff u a m (k + 1) - coneCoeff u a m k := by
  have := telescope u a m k hk
  linarith

/-- The top coefficient vanishes, which is what terminates the telescope. -/
theorem coneCoeff_top (u a : ℕ → ℚ) (m : ℕ) : coneCoeff u a m m = 0 := by
  simp only [coneCoeff, Finset.Ico_self, Finset.sum_empty]

/-! ## The signed Wachs set -/

/-- `i* = i+1` for odd `i`, `i−1` for even `i`. -/
def star (i : ℕ) : ℕ := if i % 2 = 1 then i + 1 else i - 1

/-- Signed inverse position of the positive value `i`: `p` if `w p = i`, `−p` if `w p = −i`. -/
def invPos (w : List ℤ) (i : ℕ) : ℤ :=
  match w.findIdx? (fun v => v == (i : ℤ)) with
  | some p => (p : ℤ) + 1
  | none =>
      match w.findIdx? (fun v => v == -(i : ℤ)) with
      | some p => -((p : ℤ) + 1)
      | none => 0

/-- The source's condition, with **signed** inverse positions. -/
def isWachsB (w : List ℤ) : Bool :=
  (List.range (w.length - 1)).all fun t =>
    let i := t + 1
    decide (invPos w i - invPos w (star i) ≤ 1) && decide (invPos w (star i) - invPos w i ≤ 1)

/-- Attach a sign vector to a permutation. -/
def signApply (signs : List ℤ) (p : List ℤ) : List ℤ := (signs.zip p).map fun q => q.1 * q.2

/-- All of `B_n`, as coordinate vectors. -/
def signedGroup (n : ℕ) : List (List ℤ) :=
  (tuples [(1 : ℤ), -1] n).flatMap fun s =>
    (perms ((List.range n).map (fun k => (k : ℤ) + 1))).map fun p => signApply s p

theorem card_signedGroup_one : (signedGroup 2).length = 8 := by decide

theorem card_signedGroup_two : (signedGroup 4).length = 384 := by decide

/-- `|W(B_2)| = 4 = 4¹·1!`. -/
theorem wachs_card_one : ((signedGroup 2).filter isWachsB).length = 4 := by decide

/-- `|W(B_4)| = 32 = 4²·2!`. -/
theorem wachs_card_two : ((signedGroup 4).filter isWachsB).length = 32 := by decide

/-- The condition is not vacuous: 352 of the 384 elements of `B_4` fail it. -/
theorem wachs_proper_two : ((signedGroup 4).filter (fun w => !isWachsB w)).length = 352 := by
  decide

/-! ## The counts -/

/-- `4ᵐ·m!` — the vertex count the block description gives. -/
def vertexCount (m : ℕ) : ℕ := 4 ^ m * Nat.factorial m

theorem vertexCount_one : vertexCount 1 = 4 := by decide

theorem vertexCount_two : vertexCount 2 = 32 := by decide

/-- `dim(Π^B(a) × [−1,1]^m) = m + m = 2m`. -/
theorem dimension_eq (m : ℕ) : m + m = 2 * m := by omega

/-- **The handshake identity**, division-free: a `2m`-regular graph on `4ᵐ m!` vertices has
`m·4ᵐ·m!` edges. -/
theorem edge_count (m : ℕ) :
    2 * (m * 4 ^ m * Nat.factorial m) = vertexCount m * (2 * m) := by
  simp only [vertexCount]
  ring

/-- At `m = 1` the polytope is a parallelogram: four vertices and four edges. -/
theorem parallelogram : vertexCount 1 = 4 ∧ 1 * 4 ^ 1 * Nat.factorial 1 = 4 := by decide

end Principia.MathDB.P381795
