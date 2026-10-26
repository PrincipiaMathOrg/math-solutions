/-
Copyright (c) 2026 Principia. All rights reserved.
Released under Apache 2.0.
-/
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Group.Nat.Even

/-!
# Distance parity in a bipartite graph

Mathlib has `SimpleGraph.IsBipartiteWith` with a workable API, and `SimpleGraph.dist` with another
— but **not the fact that ties them together**.  Checked against the pinned tree on 2026-08-22:
nothing in `Combinatorics/SimpleGraph/` relates distance to the bipartition, so "the distance
between two vertices of a bipartite graph is even exactly when they lie in the same part" has to be
proved here.

The content is entirely in `even_length_iff`, an induction on a walk.  `IsBipartiteWith` is a
two-field structure — `disjoint` and `mem_of_adj` — and those two fields say precisely that **every
edge flips side membership**.  So each `cons` flips the parity of the length *and* the truth of
`u ∈ s ↔ v ∈ s`, and the biconditional between the two is preserved.  Passing to `dist` is then one
application of `Reachable.exists_walk_length_eq_dist`.

Note what is *not* assumed.  `s ∪ t` need not cover the vertex set — that is Mathlib's convention
for `IsBipartiteWith`, and this file inherits it rather than strengthening the hypothesis.  And the
graph need not be connected: reachability is a hypothesis on the statements that need it, not a
blanket assumption, which keeps the results usable on a component of a larger graph.

Campaign-agnostic: nothing here mentions distance matrices, spectra, or any extremal problem.
-/

set_option autoImplicit false

namespace Principia.Common

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {s t : Set V}

/-- **Every edge flips side membership.**  This is the whole content of `IsBipartiteWith` for what
follows: `mem_of_adj` puts the endpoints on opposite sides, and `disjoint` stops a vertex from
being on both. -/
theorem not_iff_mem_of_adj (h : G.IsBipartiteWith s t) {u v : V} (hadj : G.Adj u v) :
    ¬ (u ∈ s ↔ v ∈ s) := by
  rcases h.mem_of_adj hadj with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hvs : v ∉ s := Set.disjoint_right.mp h.disjoint hv
    exact fun hiff => hvs (hiff.mp hu)
  · have hus : u ∉ s := Set.disjoint_right.mp h.disjoint hu
    exact fun hiff => hus (hiff.mpr hv)

/-- **A walk's length is even exactly when its endpoints lie on the same side.**  Each `cons` flips
the parity and, by `not_iff_mem_of_adj`, also flips the membership biconditional; the step is then
propositional. -/
theorem even_length_iff (h : G.IsBipartiteWith s t) {u v : V} (w : G.Walk u v) :
    Even w.length ↔ (u ∈ s ↔ v ∈ s) := by
  induction w with
  | nil => simp
  | cons hadj p ih =>
    have hflip := not_iff_mem_of_adj h hadj
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ih]
    tauto

/-- **The distance is even exactly when the endpoints share a side.** -/
theorem even_dist_iff (h : G.IsBipartiteWith s t) {u v : V} (hr : G.Reachable u v) :
    Even (G.dist u v) ↔ (u ∈ s ↔ v ∈ s) := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  rw [← hp]
  exact even_length_iff h p

/-- **Two distinct vertices of the same side are at distance at least `2`.**  The distance is even
and nonzero, and there is no even number strictly between `0` and `2`.  This is the bound behind
`X ≥ a(a-1)` and `Y ≥ b(b-1)` in the extremal literature. -/
theorem two_le_dist_of_same (h : G.IsBipartiteWith s t) {u v : V} (hr : G.Reachable u v)
    (hne : u ≠ v) (hu : u ∈ s) (hv : v ∈ s) : 2 ≤ G.dist u v := by
  have heven : Even (G.dist u v) := (even_dist_iff h hr).mpr ⟨fun _ => hv, fun _ => hu⟩
  have hpos : 0 < G.dist u v := hr.pos_dist_of_ne hne
  obtain ⟨k, hk⟩ := heven
  omega

/-- **Vertices on opposite sides are at odd distance.**  This is the bound behind `Z ≥ ab`, and
the source's step from a missing cross edge to a distance of at least `3`. -/
theorem not_even_dist_of_cross (h : G.IsBipartiteWith s t) {u v : V} (hr : G.Reachable u v)
    (hu : u ∈ s) (hv : v ∈ t) : ¬ Even (G.dist u v) := by
  intro heven
  have hiff := (even_dist_iff h hr).mp heven
  exact (Set.disjoint_right.mp h.disjoint hv) (hiff.mp hu)

/-- **A cross pair that is not an edge is at distance at least `3`.**  Odd, and not `1` because
distance `1` is adjacency.  This is the source's inequality `Z ≥ ab + 2` for a noncomplete
bipartite graph. -/
theorem three_le_dist_of_cross_nonadj (h : G.IsBipartiteWith s t) {u v : V} (hr : G.Reachable u v)
    (hu : u ∈ s) (hv : v ∈ t) (hne : u ≠ v) (hnadj : ¬ G.Adj u v) : 3 ≤ G.dist u v := by
  -- `one_lt_dist_of_ne_of_not_adj` is already in Mathlib; reproving it via `dist_eq_one_iff_adj`
  -- would be redundant.
  have hodd := not_even_dist_of_cross h hr hu hv
  have h1 := hr.one_lt_dist_of_ne_of_not_adj hne hnadj
  rcases Nat.even_or_odd (G.dist u v) with he | ⟨k, hk⟩
  · exact absurd he hodd
  · omega

end Principia.Common
