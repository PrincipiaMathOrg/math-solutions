import Mathlib.Data.List.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

set_option autoImplicit false
-- every count below is closed by kernel evaluation on `List (ℤ × ℤ × ℤ)`; the default recursion
-- depth is reached while unfolding the 1024-element `sublists` enumeration of the ten cubes.
set_option maxRecDepth 100000

/-!
# MathDB #380444 — Kurz's recursive structure conjecture is FALSE

Write-up: `mathdb-open-problems/problems/380444/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-30).
Source: S. Kurz, *Convex hulls of polyominoes*, Beiträge zur Algebra und Geometrie **49** (2008),
125–136, **Conjecture 1** (p. 135); arXiv:math/0702786v1.

The conjecture: an extremal `d`-dimensional polyomino contains a subpolyomino `P'` of thickness
one in some coordinate direction, whose projection retains all other bounding-box side lengths.

The counterexample: ten unit cubes with bounding box `(4,4,4)` and convex-hull volume `28` — the
maximum for ten cubes in dimension three, by Kurz's own Theorem 4 — with **no** such `P'`.

## A finding that makes the counterexample simpler than the write-up's argument

The write-up rules `P'` out by counting: every coordinate layer holds at most six cubes, and a
facet-connected planar polyomino with side lengths `r, s` needs at least `r + s - 1 = 7` cells.
A verifier control written to confirm that connectivity is load-bearing **failed**, and in the
direction that strengthens the result: **not one subset of a single layer spans `4 × 4` even
without connectivity.** The reason is in `layer_never_full` — *no coordinate layer of `P` even has
a projected bounding box of* `(4,4)`; the layers measure `(4,3)`, `(1,2)`, `(1,4)`, `(4,1)` and so
on. So for this example the planar cell-count lemma is **not needed at all**: the refutation is a
bounding-box fact, not a counting one. `no_thin` proves the stronger statement over all 1024
subsets and `no_eligible` reads the conjecture's own (connected) form off it.

## What is a hypothesis and what is proved

`volume_is_28` is a **spine**: the two genuinely geometric inputs — the Minkowski identity
`conv P = K + [0,1]³` and the extrusion (Steiner) formula relating the volume of `K + [0,1]³` to
`Vol K`, the three projected areas and the three widths — are **named hypotheses**, because
Mathlib has no computation of the volume of a specific convex hull in `ℝ³` and stating one is a
project rather than a tick. Everything else is proved here: the facet certificate for `K` is
**derived** by scanning all triples of its vertices rather than read off the write-up's table, the
projected hulls are confirmed to contain every projected cube, the shoelace areas are computed,
and Kurz's bound is evaluated. The verifier closes the gap numerically, including an independent
exact convex-hull computation on the 44 distinct cube corners which returns 20 vertices, 37 edges,
19 facets and volume 28.
-/

namespace Principia.MathDB.P380444

/-! ## The polyomino -/

abbrev Cell := ℤ × ℤ × ℤ

abbrev Vec := ℤ × ℤ × ℤ

/-- The ten lower corners, in the write-up's growth order. -/
def cells : List Cell :=
  [(0, 0, 0), (1, 0, 0), (1, 0, -1), (1, -1, -1), (-1, 0, 0),
   (1, -2, -1), (2, 0, 0), (1, -1, -2), (2, 0, 1), (1, -3, -1)]

/-- `growthNeighbour[j]` is the index of the earlier cube that cube `j` shares a facet with. -/
def growthNeighbour : List ℕ := [0, 0, 1, 2, 0, 3, 1, 3, 6, 5]

def coord : ℕ → Cell → ℤ
  | 0, c => c.1
  | 1, c => c.2.1
  | _, c => c.2.2

def sub3 (p q : Cell) : Vec := (p.1 - q.1, p.2.1 - q.2.1, p.2.2 - q.2.2)

def dot3 (u v : Vec) : ℤ := u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

def cross3 (u v : Vec) : Vec :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1, u.2.2 * v.1 - u.1 * v.2.2, u.1 * v.2.1 - u.2.1 * v.1)

/-- Two cubes share a facet exactly when their lower corners differ by one standard basis
vector, up to sign. -/
def adjacent (p q : Cell) : Bool :=
  ([(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)] : List Vec).contains
    (sub3 p q)

/-- The bounding-box side length in direction `i`: one more than the width. -/
def sideLen (i : ℕ) : List Cell → ℤ
  | [] => 0
  | c :: cs =>
      (cs.foldl (fun a q => max a (coord i q)) (coord i c))
        - (cs.foldl (fun a q => min a (coord i q)) (coord i c)) + 1

def sideSum (s : List Cell) : ℤ := sideLen 0 s + sideLen 1 s + sideLen 2 s

theorem cells_distinct : cells.dedup.length = 10 := by decide

/-- Each cube after the first shares a facet with the listed earlier one, so `P` really is a
polyomino. -/
theorem growth_facet_connected :
    ((List.range 9).all fun k =>
      adjacent (cells.getD (k + 1) (0, 0, 0))
        (cells.getD (growthNeighbour.getD (k + 1) 0) (0, 0, 0))) = true := by
  decide

theorem box_sides : (sideLen 0 cells, sideLen 1 cells, sideLen 2 cells) = (4, 4, 4) := by decide

/-- Every added cube increases exactly one bounding-box side length, which is what forces the
source's growth parameters `v_i` to vanish: `n = 1 + Σ(l_i - 1) + Σ v_i` with `n = 10` and
`Σ(l_i - 1) = 9`. -/
theorem growth_increments :
    ((List.range 9).all fun k =>
      sideSum (cells.take (k + 2)) - sideSum (cells.take (k + 1)) == 1) = true := by
  decide

theorem v_parameters_vanish : (10 : ℤ) = 1 + (4 - 1) + (4 - 1) + (4 - 1) := by decide

/-! ## The refutation

A subpolyomino `P'` of thickness one in direction `i` lies in a single coordinate layer, and
condition (ii) asks its projection to retain **both** other bounding-box side lengths, here `4`
and `4`. `thin` is exactly that condition, with connectivity deliberately left out. -/

def thickness1 (i : ℕ) (s : List Cell) : Bool := ((s.map (coord i)).dedup).length == 1

def thin (s : List Cell) : Bool :=
  (thickness1 0 s && sideLen 1 s == 4 && sideLen 2 s == 4)
    || (thickness1 1 s && sideLen 0 s == 4 && sideLen 2 s == 4)
    || (thickness1 2 s && sideLen 0 s == 4 && sideLen 1 s == 4)

def expandOnce (all seen : List Cell) : List Cell :=
  seen ++ all.filter (fun q => !seen.contains q && seen.any (fun p => adjacent p q))

def reachFrom : ℕ → List Cell → List Cell → List Cell
  | 0, _, seen => seen
  | n + 1, all, seen => reachFrom n all (expandOnce all seen)

def connected (s : List Cell) : Bool :=
  match s with
  | [] => false
  | c :: _ => (reachFrom s.length s [c]).length == s.length

/-- Conditions (i) and (ii) of the conjecture, in full: a nonempty facet-connected subpolyomino
of thickness one retaining both other side lengths. -/
def eligible (s : List Cell) : Bool := !s.isEmpty && connected s && thin s

/-- **The strong form.** No subset of the ten cubes — connected or not — has thickness one while
retaining both other side lengths. -/
theorem no_thin : (cells.sublists.all fun s => !thin s) = true := by decide

/-- The conjecture's own form follows at once, because `eligible` is `thin` conjoined with more.
Connectivity is never used, which is the finding recorded in the header. -/
theorem no_eligible : (cells.sublists.all fun s => !eligible s) = true := by
  have h := no_thin
  simp only [List.all_eq_true] at h ⊢
  intro s hs
  have ht : thin s = false := by simpa using h s hs
  simp [eligible, ht]

/-! ## Why: the layers themselves are too small

Not "too few cells" but "too small a box" — every coordinate layer fails at least one of the two
remaining side lengths. -/

def layerValues (i : ℕ) : List ℤ := (cells.map (coord i)).dedup

def layerOf (i : ℕ) (v : ℤ) : List Cell := cells.filter (fun c => coord i c == v)

def otherSides : ℕ → List Cell → ℤ × ℤ
  | 0, s => (sideLen 1 s, sideLen 2 s)
  | 1, s => (sideLen 0 s, sideLen 2 s)
  | _, s => (sideLen 0 s, sideLen 1 s)

/-- **No coordinate layer of `P` has a projected bounding box of `(4,4)`.** This is what makes
the counterexample work, and it is strictly stronger than the write-up's cell count. -/
theorem layer_never_full :
    (([0, 1, 2] : List ℕ).all fun i =>
      (layerValues i).all fun v => decide (otherSides i (layerOf i v) ≠ (4, 4))) = true := by
  decide

def layerCounts (i : ℕ) (vs : List ℤ) : List ℕ := vs.map fun v => (layerOf i v).length

theorem layer_counts_x : layerCounts 0 [-1, 0, 1, 2] = [1, 1, 6, 2] := by decide

theorem layer_counts_y : layerCounts 1 [-3, -2, -1, 0] = [1, 1, 2, 6] := by decide

theorem layer_counts_z : layerCounts 2 [-2, -1, 0, 1] = [1, 4, 4, 1] := by decide

theorem layer_values_exhaustive :
    (layerValues 0).dedup.length = 4 ∧ (layerValues 1).dedup.length = 4
      ∧ (layerValues 2).dedup.length = 4 := by
  decide

/-! ## The hull `K` of the ten lower corners, with a DERIVED facet certificate -/

def Kverts : List Cell := [(-1, 0, 0), (1, 0, -1), (1, -1, -2), (1, -3, -1), (2, 0, 0), (2, 0, 1)]

/-- The write-up's table of outward normals and offsets. It is checked against `supporting`
below, not trusted. -/
def facetTable : List (Vec × ℤ) :=
  [((-5, -2, -4), 5), ((-3, -5, 9), 3), ((-1, 2, -2), 1), ((0, 1, 0), 0),
   ((1, 1, -1), 2), ((3, -1, 0), 6), ((5, -1, -2), 10)]

def primitive (u : Vec) (b : ℤ) : Vec × ℤ :=
  let g : ℤ := (Int.gcd (Int.gcd u.1 u.2.1) u.2.2 : ℕ)
  if g = 0 then (u, b) else ((u.1 / g, u.2.1 / g, u.2.2 / g), b / g)

/-- Every supporting plane of `conv Kverts`, found by scanning all triples of vertices. -/
def supporting (l : List Cell) : List (Vec × ℤ) :=
  (l.flatMap fun a => l.flatMap fun b => l.filterMap fun c =>
    let u := cross3 (sub3 b a) (sub3 c a)
    if u = (0, 0, 0) then none
    else
      let t := dot3 u a
      if l.all (fun p => decide (dot3 u p ≤ t)) then some (primitive u t)
      else if l.all (fun p => decide (t ≤ dot3 u p)) then
        some (primitive (-u.1, -u.2.1, -u.2.2) (-t))
      else none).dedup

/-- **The facet table is complete and correct**, derived rather than transcribed. -/
theorem facets_derived :
    (supporting Kverts).length = 7
      ∧ ((supporting Kverts).all fun f => facetTable.contains f) = true
      ∧ (facetTable.all fun f => (supporting Kverts).contains f) = true := by
  decide

theorem facets_support_verts :
    (Kverts.all fun p => facetTable.all fun f => decide (dot3 f.1 p ≤ f.2)) = true := by decide

/-- Every lower corner lies in `K`, so `K` really is their hull. -/
theorem cells_in_K :
    (cells.all fun p => facetTable.all fun f => decide (dot3 f.1 p ≤ f.2)) = true := by decide

def onSegment (p q r : Cell) : Bool :=
  (cross3 (sub3 p q) (sub3 r q) == (0, 0, 0))
    && decide (0 ≤ dot3 (sub3 p q) (sub3 r q))
    && decide (dot3 (sub3 p q) (sub3 r q) ≤ dot3 (sub3 r q) (sub3 r q))

/-- The four lower corners that are not vertices lie on segment `AE` or segment `BD`. -/
theorem others_on_segments :
    ((cells.filter fun c => !Kverts.contains c).all fun p =>
      onSegment p (-1, 0, 0) (2, 0, 0) || onSegment p (1, 0, -1) (1, -3, -1)) = true := by
  decide

/-- The origin lies on `AE`, hence in `K`, which is what makes the pyramid decomposition of the
volume valid. -/
theorem origin_in_K : onSegment (0, 0, 0) (-1, 0, 0) (2, 0, 0) = true := by decide

/-- The oriented facet contributions sum to `27`, so `Vol K = 27/6 = 9/2`. -/
theorem facet_offsets_sum : (facetTable.map Prod.snd).sum = 27 := by decide

theorem volK_value : (27 : ℚ) / 6 = 9 / 2 := by norm_num

/-! ## The three projections -/

def proj : ℕ → Cell → ℤ × ℤ
  | 0, c => (c.2.1, c.2.2)
  | 1, c => (c.1, c.2.2)
  | _, c => (c.1, c.2.1)

def leftOf (e : (ℤ × ℤ) × (ℤ × ℤ)) (p : ℤ × ℤ) : Bool :=
  decide (0 ≤ (e.2.1 - e.1.1) * (p.2 - e.1.2) - (e.2.2 - e.1.2) * (p.1 - e.1.1))

def inHull (poly : List (ℤ × ℤ)) (p : ℤ × ℤ) : Bool :=
  (poly.zip (poly.rotate 1)).all fun e => leftOf e p

def shoelace2Aux (first : ℤ × ℤ) : List (ℤ × ℤ) → ℤ
  | [] => 0
  | [q] => q.1 * first.2 - first.1 * q.2
  | q :: r :: rest => (q.1 * r.2 - r.1 * q.2) + shoelace2Aux first (r :: rest)

/-- Twice the signed area of a cyclically ordered polygon. -/
def shoelace2 : List (ℤ × ℤ) → ℤ
  | [] => 0
  | p :: ps => shoelace2Aux p (p :: ps)

def polyXY : List (ℤ × ℤ) := [(-1, 0), (1, -3), (2, 0)]

def polyXZ : List (ℤ × ℤ) := [(-1, 0), (1, -2), (2, 0), (2, 1)]

def polyYZ : List (ℤ × ℤ) := [(-3, -1), (-1, -2), (0, -1), (0, 1)]

/-- Each listed polygon really does contain every projected cube, so it is the projected hull. -/
theorem projections_contain_cells :
    (cells.all fun c => inHull polyXY (proj 2 c))
      && (cells.all fun c => inHull polyXZ (proj 1 c))
      && (cells.all fun c => inHull polyYZ (proj 0 c)) = true := by
  decide

/-- All three projected hulls have area `9/2`. -/
theorem projection_areas :
    shoelace2 polyXY = 9 ∧ shoelace2 polyXZ = 9 ∧ shoelace2 polyYZ = 9 := by decide

/-- Every coordinate width of `K` is `3`. -/
theorem widths :
    (sideLen 0 cells - 1, sideLen 1 cells - 1, sideLen 2 cells - 1) = (3, 3, 3) := by decide

/-! ## Extremality -/

/-- Kurz's upper bound (Theorem 4 of the source) at `d = 3`, `n = 10`, where all three floor
values `⌊(n-2+i)/d⌋` equal `3`. -/
def kurzBound10 : ℚ := 1 + 3 * 3 + 3 * (3 * 3) / 2 + 3 * 3 * 3 / 6

theorem kurz_bound_eq : kurzBound10 = 28 := by
  unfold kurzBound10
  norm_num

/-- **The volume, as a spine.** `hSteiner` is the extrusion formula for `Vol(K + [0,1]³)` — the
one genuinely geometric input, stated as a hypothesis because Mathlib has no computation of the
volume of a specific convex hull in `ℝ³`. Every other quantity is the value proved above. -/
theorem volume_is_28 (volConvP volK aXY aXZ aYZ wX wY wZ : ℚ)
    (hSteiner : volConvP = volK + aXY + aXZ + aYZ + wX + wY + wZ + 1)
    (hK : volK = 9 / 2) (hxy : aXY = 9 / 2) (hxz : aXZ = 9 / 2) (hyz : aYZ = 9 / 2)
    (hwX : wX = 3) (hwY : wY = 3) (hwZ : wZ = 3) :
    volConvP = 28 := by
  subst hSteiner hK hxy hxz hyz hwX hwY hwZ
  norm_num

/-- **Kurz's Conjecture 1 is false.** The ten-cube polyomino `P` is extremal — its convex-hull
volume attains Kurz's own upper bound for ten cubes — its bounding box is `(4,4,4)`, and **no**
subset of its cubes, connected or not, has thickness one in a coordinate direction while
retaining both other bounding-box side lengths. -/
theorem conjecture_1_false (volConvP : ℚ) (hvol : volConvP = 28) :
    cells.dedup.length = 10
      ∧ (sideLen 0 cells, sideLen 1 cells, sideLen 2 cells) = (4, 4, 4)
      ∧ volConvP = kurzBound10
      ∧ (cells.sublists.all fun s => !thin s) = true
      ∧ (cells.sublists.all fun s => !eligible s) = true := by
  refine ⟨cells_distinct, box_sides, ?_, no_thin, no_eligible⟩
  rw [hvol, kurz_bound_eq]

end Principia.MathDB.P380444
