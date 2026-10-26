import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
-- every count below is closed by kernel evaluation over `List Bool`; the default recursion
-- depth is reached while unfolding the 256-element `sublists` enumeration.
set_option maxRecDepth 100000

/-!
# MathDB #380333 — Genest's Conjecture 1.7.17 is FALSE

Write-up: `mathdb-open-problems/problems/380333/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-30; one of
the nine solutions added upstream when the branch moved to `93ea328d`).
Source: Genest, **Conjecture 1.7.17** (p. 41): for a bicolored graph without isolated vertices or
twins, its parity class is in bijection with its complementation sets.

**The counterexample is the 3-dimensional cube with all vertices black.** It is connected, has no
twins and no isolated vertices, has exactly **56** complementation sets, and exactly **28** graphs
in its parity class — so no bijection can exist.

## Why this is a finite computation, and how it is made one

For an all-black graph every parity step is an adjacent black pair, so the whole question lives
over `𝔽₂`: the write-up's Lemma says the complementation sets are exactly the `S` for which the
principal submatrix `A[S]` is **nonsingular**. That turns clause one into "count the subsets of an
8-element set whose principal submatrix has full rank over `𝔽₂`" — 256 rank computations on
matrices of size at most `8`.

**The representation is the whole engineering decision.** The obvious encoding is `ℕ` bitmasks
with `xor`, and it is the wrong one: `Nat.xor` goes through `Nat.bitwise`, which is defined by
well-founded recursion and has no kernel GMP acceleration, so `decide` would either crawl or get
stuck. `List Bool` with `List.zipWith xor` is structural throughout and kernel-reduces, and
`List.sublists` enumerates the 256 subsets the same way. Every count below is therefore closed by
`decide` with no `native_decide` anywhere — which matters, because `native_decide` would add
`ofReduceBool` to the footprint and the campaign's gate refuses it.

## What this module proves

* `cube` — the adjacency matrix, and `cube_symm` / `cube_irrefl` confirming it really is a graph.
* `noIsolated`, `noTwins`, `connected` — the three hypotheses Genest's conjecture imposes, all
  checked rather than assumed.
* `compSets` and `compCount` — **exactly 56** complementation sets, by the nonsingularity
  criterion. The size distribution `1, 12, 30, 12, 1` is recorded too: every one has even size,
  which is forced because a symmetric matrix with zero diagonal over `𝔽₂` has even rank.

## THE CONJECTURE IS REFUTED -- `conjecture_1_7_17_false`

Stage 2 closed the second count. `conjecture_1_7_17_false` is the refutation: the all-black
3-cube is admissible -- connected, twin-free, isolated-free, all proved above -- yet its **56**
complementation sets map onto only **28** graphs, so no bijection between the two sets can exist.

* `inv2` -- inversion over `F2` by Gauss-Jordan on augmented `List Bool` rows. `gjAux` carries the
  finished pivot rows separately and eliminates each new pivot from **both** lists, so the rows it
  returns really are in reduced echelon form; `inv2` then reads the inverse off by matching each
  `take k` against a unit vector, which also detects singularity.
* `pivotGraph` -- the principal pivot transform `A * S`, with blocks `P` inverse, `P` inverse `Q`,
  `Q` transpose `P` inverse and `R + Q` transpose `P` inverse `Q`, written back in the original
  vertex order.
* `pivot_empty` -- the identity check: the empty complementation set returns the original cube.
  This is the cheapest possible guard against an index-order mistake in the reassembly, and it is
  the same check the verifier runs first.
* `parityClass` and `parityCount` -- exactly **28** graphs, and `parityClass_graphs` confirms every
  image is again a graph (symmetric, zero diagonal).

Nothing in this file is hypothetical, and `native_decide` appears nowhere.

-/

namespace Principia.MathDB.P380333

/-- A row of an `𝔽₂` adjacency matrix. -/
abbrev Row : Type := List Bool

/-- The 3-cube: vertices `0..7` as bit patterns, adjacent when they differ in one coordinate. -/
def cube : List Row :=
  [[false, true, true, false, true, false, false, false],
   [true, false, false, true, false, true, false, false],
   [true, false, false, true, false, false, true, false],
   [false, true, true, false, false, false, false, true],
   [true, false, false, false, false, true, true, false],
   [false, true, false, false, true, false, false, true],
   [false, false, true, false, true, false, false, true],
   [false, false, false, true, false, true, true, false]]

/-- Entry `(i, j)` of the adjacency matrix. -/
def adj (i j : ℕ) : Bool := ((cube.getD i []).getD j false)

/-- It is a graph: symmetric. -/
theorem cube_symm : ∀ i ∈ List.range 8, ∀ j ∈ List.range 8, adj i j = adj j i := by decide

/-- It is a graph: no loops. -/
theorem cube_irrefl : ∀ i ∈ List.range 8, adj i i = false := by decide

/-- Every vertex has degree 3, so in particular none is isolated. -/
theorem noIsolated : ∀ i ∈ List.range 8, ((cube.getD i []).count true) = 3 := by decide

/-- The open neighbourhood of `i`. -/
def openNbhd (i : ℕ) : Row := cube.getD i []

/-- The closed neighbourhood of `i`, as a row with the diagonal set. -/
def closedNbhd (i : ℕ) : Row :=
  (List.range 8).map (fun j => adj i j || decide (i = j))

/-- No twins: distinct vertices have distinct open AND distinct closed neighbourhoods. -/
theorem noTwins : ∀ i ∈ List.range 8, ∀ j ∈ List.range 8, i ≠ j →
    openNbhd i ≠ openNbhd j ∧ closedNbhd i ≠ closedNbhd j := by decide

/-! ### Connectivity, by explicit reachability -/

/-- One breadth-first expansion step: add every neighbour of a vertex already reached. -/
def expand (reached : List ℕ) : List ℕ :=
  (List.range 8).filter (fun j => reached.contains j || reached.any (fun i => adj i j))

/-- Iterate the expansion `n` times from `{0}`. -/
def reach : ℕ → List ℕ
  | 0 => [0]
  | (n + 1) => expand (reach n)

/-- The cube is connected: three expansions from vertex `0` reach all eight vertices. -/
theorem connected : reach 3 = List.range 8 := by decide

/-! ### The complementation sets -/

/-- The rows of the principal submatrix `A[S]`, each compressed to the positions of `S`. -/
def subRows (S : List ℕ) : List Row := S.map (fun i => S.map (fun j => adj i j))

/-- Rank over `𝔽₂`, eliminating on the listed column positions. Structural in the column list,
so it kernel-reduces. -/
def rank2Aux : List ℕ → List Row → ℕ
  | [], _ => 0
  | (b :: bs), rows =>
      match rows.find? (fun r => r.getD b false) with
      | none => rank2Aux bs rows
      | some p =>
          1 + rank2Aux bs ((rows.filter (fun r => r ≠ p)).map
            (fun r => if r.getD b false then List.zipWith xor r p else r))

/-- Rank over `𝔽₂` of a square block of side `rows.length`. -/
def rank2 (rows : List Row) : ℕ := rank2Aux (List.range rows.length) rows

/-- The write-up's criterion: `S` is a complementation set exactly when `A[S]` is nonsingular,
the empty matrix counting as nonsingular. -/
def isComp (S : List ℕ) : Bool := rank2 (subRows S) == S.length

/-- All 256 subsets of the vertex set. -/
def allSubsets : List (List ℕ) := (List.range 8).sublists

theorem allSubsets_card : allSubsets.length = 256 := by decide

/-- The complementation sets of the all-black 3-cube. -/
def compSets : List (List ℕ) := allSubsets.filter isComp

/-- **Clause one of the counterexample: exactly 56 complementation sets.** -/
theorem compCount : compSets.length = 56 := by decide

/-- Every complementation set has even size — forced, since a symmetric matrix with zero diagonal
over `𝔽₂` has even rank. The distribution is `1, 12, 30, 12, 1`. -/
theorem compSizes :
    (compSets.filter (fun S => S.length == 0)).length = 1 ∧
      (compSets.filter (fun S => S.length == 2)).length = 12 ∧
      (compSets.filter (fun S => S.length == 4)).length = 30 ∧
      (compSets.filter (fun S => S.length == 6)).length = 12 ∧
      (compSets.filter (fun S => S.length == 8)).length = 1 := by decide

/-- No complementation set has odd size. -/
theorem compSizes_even : ∀ S ∈ compSets, S.length % 2 = 0 := by decide

/-! ## Stage 2: the principal pivot transform and the parity class

Same representation as stage 1 -- `List Bool` rows, structural throughout, closed by
`decide` with no `native_decide`. Gauss-Jordan over `F2` inverts the pivot block. -/

/-- The complement of `S` inside the vertex set. -/
def vcompl (S : List ℕ) : List ℕ := (List.range 8).filter (fun j => !S.contains j)

def zeroRow (w : ℕ) : Row := List.replicate w false

def unitRow (k i : ℕ) : Row := (List.range k).map (fun j => decide (i = j))

def idRows (k : ℕ) : List Row := (List.range k).map (unitRow k)

/-- `[rows | I]`, the augmented system Gauss–Jordan inverts. -/
def augment (rows : List Row) : List Row :=
  List.zipWith (fun r e => r ++ e) rows (idRows rows.length)

/-- Gauss–Jordan over `𝔽₂`: `done` holds the rows already carrying a pivot, and each new pivot is
eliminated from **both** lists, so the finished rows really are in reduced echelon form. -/
def gjAux : List ℕ → List Row → List Row → List Row
  | [], done, rest => done ++ rest
  | (c :: cs), done, rest =>
      match rest.find? (fun r => r.getD c false) with
      | none => gjAux cs done rest
      | some p =>
          gjAux cs
            ((done.map (fun r => if r.getD c false then List.zipWith xor r p else r)) ++ [p])
            ((rest.filter (fun r => r ≠ p)).map
              (fun r => if r.getD c false then List.zipWith xor r p else r))

/-- The inverse over `𝔽₂`, or `none` when singular. -/
def inv2 (rows : List Row) : Option (List Row) :=
  let k := rows.length
  let red := gjAux (List.range k) [] (augment rows)
  let out := (List.range k).map (fun i =>
    match red.find? (fun r => r.take k = unitRow k i) with
    | none => ([] : Row)
    | some r => r.drop k)
  if out.all (fun r => r.length == k) then some out else none

/-- XOR together the rows of `Y` selected by the `true` entries of `r`. -/
def rowCombine : Row → List Row → Row → Row
  | [], _, acc => acc
  | (_ :: _), [], acc => acc
  | (b :: bs), (y :: ys), acc => rowCombine bs ys (if b then List.zipWith xor acc y else acc)

/-- Matrix product over `𝔽₂`; `w` is the width of the result. -/
def mul2 (X Y : List Row) (w : ℕ) : List Row := X.map (fun r => rowCombine r Y (zeroRow w))

/-- The block of the adjacency matrix with rows indexed by `I` and columns by `J`. -/
def block (I J : List ℕ) : List Row := I.map (fun i => J.map (fun j => adj i j))

/-- The principal pivot transform `A ∗ S`, written back in the original vertex order. -/
def pivotGraph (S : List ℕ) : List Row :=
  let Sc := vcompl S
  let k := S.length
  let m := Sc.length
  match inv2 (block S S) with
  | none => cube
  | some Pi =>
      let Q := block S Sc
      let Qt := block Sc S
      let R := block Sc Sc
      let TR := mul2 Pi Q m
      let BL := mul2 Qt Pi k
      let BR := List.zipWith (fun r s => List.zipWith xor r s) R (mul2 BL Q m)
      (List.range 8).map (fun i =>
        (List.range 8).map (fun j =>
          if S.contains i then
            (if S.contains j then ((Pi.getD (S.idxOf i) []).getD (S.idxOf j) false)
             else ((TR.getD (S.idxOf i) []).getD (Sc.idxOf j) false))
          else
            (if S.contains j then ((BL.getD (Sc.idxOf i) []).getD (S.idxOf j) false)
             else ((BR.getD (Sc.idxOf i) []).getD (Sc.idxOf j) false))))

/-- **Identity check**: the empty complementation set returns the original cube. -/
theorem pivot_empty : pivotGraph [] = cube := by decide

/-- The parity class of the all-black 3-cube. -/
def parityClass : List (List Row) := (compSets.map pivotGraph).dedup

/-- **Clause two of the counterexample: exactly 28 graphs in the parity class.** -/
theorem parityCount : parityClass.length = 28 := by decide

/-- **Genest's Conjecture 1.7.17 is false.** The all-black 3-cube is admissible — connected,
twin-free, isolated-free — yet its 56 complementation sets map onto only 28 graphs, so no
bijection between the two sets exists. -/
theorem conjecture_1_7_17_false : compSets.length ≠ parityClass.length := by decide

/-- Every image is again a graph: symmetric with zero diagonal. -/
theorem parityClass_graphs :
    ∀ g ∈ parityClass, (∀ i ∈ List.range 8, ∀ j ∈ List.range 8,
      (g.getD i []).getD j false = (g.getD j []).getD i false) ∧
      (∀ i ∈ List.range 8, (g.getD i []).getD i false = false) := by decide
end Principia.MathDB.P380333
