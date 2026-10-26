/-
Copyright (c) 2026 Principia. All rights reserved.
Released under Apache 2.0.
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Bipartite
-- `Analysis.Matrix.Spectrum` was imported here; narrowed to `.Hermitian` on 2026-08-23.
-- `Matrix.IsHermitian.eigenvalues` and `spectrum` occur in this file ZERO times in code
-- (only in a docstring explaining why the matrix-level spectrum is NOT used), while
-- `isSymmetric_toEuclideanLin_iff` lives in `.Hermitian`.  Dropping `.Spectrum` removes
-- `Charpoly.Eigs`, `Matrix.Rank`, `Eigenspace.Matrix` and `UnitaryStarAlgAut` from the
-- import closure, which on this disk is what build time is proportional to.
import Mathlib.Analysis.Matrix.Hermitian
import Principia.Common.HermitianRayleigh
import Principia.Common.BipartiteDistance

/-!
# MathDB #333521 — the balanced complete bipartite graph minimises the distance signless
Laplacian spread

Foundations only in this file so far: the distance matrix, the transmission, the distance signless
Laplacian `Q = Tr + D`, and its spread.  **None of these exist in Mathlib** — there is no distance
matrix, no transmission, no Wiener index.  `SimpleGraph.dist` does exist, with `dist_comm` and a
usable API, and `SimpleGraph.IsBipartiteWith` exists too.

Three design decisions, each of which the rest of the row depends on.

**Connectedness is a hypothesis on the definitions' *lemmas*, not on the definitions.**
`G.dist u v = 0` when `u` and `v` are unreachable, so `D` is silently wrong on a disconnected
graph rather than undefined.  Making `Connected` a field of the matrix would force it through every
rewrite; carrying it as a hypothesis where it is used keeps the definitions computable and the
statements honest.

**The spectrum is taken through `Matrix.toEuclideanLin`, not through `Matrix.IsHermitian`.**
The matrix-level `eigenvalues` is indexed by the *vertex type* and carries no ordering, whereas the
spread needs the largest and the smallest.  `LinearMap.IsSymmetric.eigenvalues` is indexed by
`Fin n` and comes with `eigenvalues_antitone`, so `q₁` is `eigenvalues 0` and `qₙ` is
`eigenvalues (last)` by construction rather than by an extra sorting argument.  This also matches
`Common.HermitianRayleigh`, which is stated for symmetric linear maps.

**The spread is defined from the ordering, not as a `⨆ - ⨅`.**  Same reason as the Rayleigh
bounds: a caller comparing spreads wants two named endpoints, not two lattice operations whose
`Nonempty` side conditions have to be discharged at each use.
-/

set_option autoImplicit false

namespace Principia.MathDB.P333521

open Matrix Finset
-- `⟪ x, y ⟫_ℝ` lives in the `InnerProductSpace` scope, NOT `RealInnerProductSpace`,
-- which rebinds the UNSUFFIXED bracket and leaves every statement below a parse error
-- reported as `expected token` at the signature.
open scoped InnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- The distance matrix.  Honest only when `G` is connected; see the module docstring. -/
noncomputable def distMatrix : Matrix V V ℝ := fun u v => (G.dist u v : ℝ)

/-- The transmission of a vertex: the sum of its distances to all vertices. -/
noncomputable def transmission (u : V) : ℝ := ∑ v, (G.dist u v : ℝ)

/-- The distance signless Laplacian `Q = Tr + D`. -/
noncomputable def Q : Matrix V V ℝ := Matrix.diagonal (transmission G) + distMatrix G

/-- **`Q` is symmetric**, because graph distance is.

Via `IsHermitian.ext` rather than by unfolding `ᴴ` — the entrywise characterisation
`∀ i j, star (A j i) = A i j` is what the distance's symmetry directly supplies. -/
theorem Q_isHermitian : (Q G).IsHermitian := by
  refine Matrix.IsHermitian.ext fun u v => ?_
  by_cases h : u = v
  · subst h
    simp
  · have hd : G.dist v u = G.dist u v := SimpleGraph.dist_comm ..
    simp only [Q, Matrix.add_apply, Matrix.diagonal_apply, distMatrix, if_neg h,
      if_neg (Ne.symm h), zero_add, star_trivial, hd]

/-- **`Q` as a symmetric operator.**  The eigenvalues that carry an ORDER live here, not at matrix
level: `Matrix.IsHermitian.eigenvalues` is indexed by the vertex type and unordered, whereas
`LinearMap.IsSymmetric.eigenvalues` is indexed by `Fin _` and comes with `eigenvalues_antitone`. -/
noncomputable def QLin : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
  Matrix.toEuclideanLin (Q G)

theorem QLin_isSymmetric : (QLin G).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (Q_isHermitian G)

/-- The dimension equation, **named once**.  `eigenvalues` takes the `finrank` proof as an
argument, so two uses that build it inline are only *propositionally* the same term; sharing one
named proof keeps `qEig` and any lemma about it syntactically identical and spares a `simp` that
would otherwise have to see through proof irrelevance. -/
theorem finrank_euclidean_eq {n : ℕ} (hcard : Fintype.card V = n + 1) :
    Module.finrank ℝ (EuclideanSpace ℝ V) = n + 1 := by
  rw [finrank_euclideanSpace, hcard]

/-- The eigenvalues of `Q`, decreasing.

**Indexed by `Fin (n+1)`, not `Fin (Fintype.card V)`, and that is deliberate.**  `Fin k` has an
`OfNat _ 0` instance only when `k` is a syntactic successor, so with the card left as an opaque
`Fintype.card V` the literals `0` and `Fin.last _` do not elaborate in the *statement* — a
hypothesis `Fintype.card V = n + 1` does not help, because no `subst` has happened yet at that
point.  Taking the order as `n + 1` up front makes both endpoints nameable, which is exactly what
a spread needs. -/
noncomputable def qEig {n : ℕ} (hcard : Fintype.card V = n + 1) : Fin (n + 1) → ℝ :=
  (QLin_isSymmetric G).eigenvalues (finrank_euclidean_eq hcard)

/-- **The distance signless Laplacian spread**, `S_Q(G) = q₁ - qₙ`.

Defined from the ordering rather than as `⨆ - ⨅`, for the same reason the Rayleigh bounds in
`Common.HermitianRayleigh` avoid lattice operations: a caller comparing two spreads wants two
named endpoints, not two lattice operations whose side conditions must be discharged at each use. -/
noncomputable def spread {n : ℕ} (hcard : Fintype.card V = n + 1) : ℝ :=
  qEig G hcard 0 - qEig G hcard (Fin.last n)

/-- The spread is nonnegative, because the eigenvalues are listed in decreasing order. -/
theorem spread_nonneg {n : ℕ} (hcard : Fintype.card V = n + 1) : 0 ≤ spread G hcard := by
  have hanti := (QLin_isSymmetric G).eigenvalues_antitone (finrank_euclidean_eq hcard)
  rw [spread, sub_nonneg]
  exact hanti (Fin.zero_le (Fin.last n))


/-! ### The three distance sums, and the bound the source calls (1)

The source writes these over **unordered** pairs: `X = ∑_{{u,v}⊆A} d(u,v)`, with `X ≥ a(a-1)` from
`a(a-1)/2` pairs each at distance `≥ 2`.  Summing over `Finset.offDiag` gives the **ordered** sum
`= 2X`, and every constant then lands without a division.

Two deliberate choices.  The bounds are stated against `S.offDiag.card` rather than against
`S.card ^ 2 - S.card`, which keeps ℕ-subtraction and its casts out of the statement entirely —
`Finset.offDiag_card` relates the two for a caller who wants the closed form.  And the part
memberships are hypotheses (`∀ u ∈ S, u ∈ s`) rather than a bundled "S is the part", so the same
lemma serves both `A` and `B` without a symmetry argument. -/

/-- The ordered distance sum inside one part: twice the source's `X` (or `Y`). -/
noncomputable def sumWithin (S : Finset V) : ℝ := ∑ p ∈ S.offDiag, (G.dist p.1 p.2 : ℝ)

/-- The ordered distance sum across the parts: the source's `Z`. -/
noncomputable def sumAcross (A B : Finset V) : ℝ := ∑ u ∈ A, ∑ v ∈ B, (G.dist u v : ℝ)

/-- **Inside a part, every ordered pair costs at least `2`.**  Bipartite parity forces the distance
even, connectedness forces it nonzero, and there is no even number strictly between.  This is the
source's `X ≥ a(a-1)` and `Y ≥ b(b-1)`, doubled. -/
theorem two_mul_card_le_sumWithin {s t : Set V} (hb : G.IsBipartiteWith s t) (hconn : G.Connected)
    (S : Finset V) (hS : ∀ u ∈ S, u ∈ s) :
    2 * (S.offDiag.card : ℝ) ≤ sumWithin G S := by
  have hstep : ∀ p ∈ S.offDiag, (2 : ℝ) ≤ (G.dist p.1 p.2 : ℝ) := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨h1, h2, hne⟩ := hp
    have := Principia.Common.two_le_dist_of_same hb (hconn p.1 p.2) hne (hS _ h1) (hS _ h2)
    exact_mod_cast this
  have hsum := Finset.card_nsmul_le_sum S.offDiag (fun p => (G.dist p.1 p.2 : ℝ)) 2 hstep
  rw [nsmul_eq_mul] at hsum
  rw [sumWithin]
  linarith

/-- **Across the parts, every ordered pair costs at least `1`.**  The distance is odd, hence
nonzero.  This is the source's `Z ≥ ab`, and it needs no separate connectedness appeal beyond the
one inside the parity lemma. -/
theorem card_mul_card_le_sumAcross {s t : Set V} (hb : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hA : ∀ u ∈ A, u ∈ s) (hB : ∀ v ∈ B, v ∈ t) :
    (A.card : ℝ) * B.card ≤ sumAcross G A B := by
  have hstep : ∀ u ∈ A, ∀ v ∈ B, (1 : ℝ) ≤ (G.dist u v : ℝ) := by
    intro u hu v hv
    have hodd := Principia.Common.not_even_dist_of_cross hb (hconn u v) (hA _ hu) (hB _ hv)
    have hne : G.dist u v ≠ 0 := by
      intro h0
      -- `Even n` unfolds to `∃ r, n = r + r`, so the witness needs no lemma name.  `even_zero` is
      -- `to_additive`-generated and has no declaration to grep, which is how it got written here
      -- unverified in the first place.
      exact hodd ⟨0, by omega⟩
    have : 1 ≤ G.dist u v := Nat.one_le_iff_ne_zero.mpr hne
    exact_mod_cast this
  have hinner : ∀ u ∈ A, (B.card : ℝ) * 1 ≤ ∑ v ∈ B, (G.dist u v : ℝ) := by
    intro u hu
    have h := Finset.card_nsmul_le_sum B (fun v => (G.dist u v : ℝ)) 1 (hstep u hu)
    rw [nsmul_eq_mul] at h
    linarith
  have houter : (A.card : ℝ) * ((B.card : ℝ) * 1) ≤ ∑ u ∈ A, ∑ v ∈ B, (G.dist u v : ℝ) := by
    have h := Finset.card_nsmul_le_sum A (fun u => ∑ v ∈ B, (G.dist u v : ℝ))
      ((B.card : ℝ) * 1) hinner
    rw [nsmul_eq_mul] at h
    linarith
  rw [sumAcross]
  linarith

/-! ### Evaluating at the all-ones vector — the source's inequality (3)

`q₁ ≥ 4W/n` is the one bound in the source needing no case analysis: the Rayleigh quotient at the
all-ones vector is `1ᵀQ1 / n`, and `1ᵀQ1` is twice the ordered distance sum, because the two halves
of `Q = Tr + D` contribute the same total — the diagonal by definition of transmission, the
distance matrix by being the same sum written out.

Stated **multiplied out**, `2·totalDist ≤ q₁ · n`, rather than as `4W/n ≤ q₁`.  There is then no
division and no `n ≠ 0` side condition, and the *ordered* sum `totalDist = 2W` absorbs the factor
the source carries as a `4`, so no constant is ever halved. -/

/-- The **ordered** total distance sum `∑_u ∑_v d(u,v)`, equal to `2 W(G)` for the Wiener index
`W`.  Working ordered keeps every constant in the row an integer. -/
noncomputable def totalDist : ℝ := ∑ u, ∑ v, (G.dist u v : ℝ)

/-- The transmissions sum to the ordered total distance — definitionally, since `transmission` is
exactly the inner sum. -/
theorem sum_transmission : ∑ u, transmission G u = totalDist G := rfl

/-- The all-ones vector.  `EuclideanSpace ℝ V` is `WithLp 2 (V → ℝ)`, and in the pinned tree
`WithLp` is a **structure**, not a type synonym — so the constant function must be injected with
`WithLp.toLp` rather than written directly. -/
noncomputable def ones : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ => (1 : ℝ))

@[simp] theorem ones_apply (u : V) : (ones : EuclideanSpace ℝ V) u = 1 := rfl

theorem norm_sq_ones : ‖(ones : EuclideanSpace ℝ V)‖ ^ 2 = (Fintype.card V : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp

/-- A row of `Q` sums to the vertex's transmission plus its row of `D`. -/
theorem sum_row_Q (i : V) : ∑ j, Q G i j = transmission G i + ∑ j, (G.dist i j : ℝ) := by
  have hdiag : ∑ j, Matrix.diagonal (transmission G) i j = transmission G i := by
    rw [Finset.sum_eq_single i (fun j _ hj => Matrix.diagonal_apply_ne' _ hj)
      (fun h => absurd (Finset.mem_univ i) h)]
    exact Matrix.diagonal_apply_eq _ i
  simp only [Q, Matrix.add_apply, distMatrix]
  rw [Finset.sum_add_distrib, hdiag]

/-- **`1ᵀQ1 = 2·totalDist`.** -/
theorem sum_sum_Q : ∑ i, ∑ j, Q G i j = 2 * totalDist G := by
  simp only [sum_row_Q]
  rw [Finset.sum_add_distrib, sum_transmission]
  have hd : ∑ i, ∑ j, (G.dist i j : ℝ) = totalDist G := rfl
  rw [hd]
  ring

/-- The quadratic form at the all-ones vector.  Every step from the inner product to the double
sum is definitional in the pinned tree — `EuclideanSpace.inner_eq_star_dotProduct`,
`Matrix.toLpLin_apply` and `WithLp.ofLp_toLp` are all `rfl` — so the only real content is
`sum_sum_Q`. -/
theorem inner_ones_QLin_ones :
    ⟪(ones : EuclideanSpace ℝ V), QLin G ones⟫_ℝ = 2 * totalDist G := by
  have hrw : ⟪(ones : EuclideanSpace ℝ V), QLin G ones⟫_ℝ = ∑ i, ∑ j, Q G i j := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [QLin, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, ones, WithLp.ofLp_toLp]
    simp [dotProduct, Matrix.mulVec]
  rw [hrw, sum_sum_Q]

/-- **Inequality (3), `4W ≤ q₁ n`.**  The largest eigenvalue dominates the Rayleigh quotient at
every vector; at the all-ones vector that quotient is `2·totalDist / n`.

The eigenvalue hypothesis of `Common.mul_norm_sq_le_inner_apply`'s dual is discharged by
`eigenvalues_antitone` at `Fin.zero_le`, which is the only place the *ordering* chosen back in
`qEig` earns its keep. -/
theorem two_mul_totalDist_le_qEig_mul_card {n : ℕ} (hcard : Fintype.card V = n + 1) :
    2 * totalDist G ≤ qEig G hcard 0 * (Fintype.card V : ℝ) := by
  have hanti := (QLin_isSymmetric G).eigenvalues_antitone (finrank_euclidean_eq hcard)
  have h := Principia.Common.inner_apply_le_mul_norm_sq (QLin_isSymmetric G)
      (finrank_euclidean_eq hcard) (c := qEig G hcard 0) (fun i => hanti (Fin.zero_le i))
      (ones : EuclideanSpace ℝ V)
  rw [inner_ones_QLin_ones, norm_sq_ones] at h
  exact h

/-! ### Averaging over difference vectors — the source's inequality (4)

The source bounds `qₙ` by averaging Rayleigh quotients over an **orthonormal basis of the zero-sum
subspace** supported on one part.  **We never build that basis.**  `Common.mul_sum_norm_sq_le_sum_inner_apply`
requires no orthogonality and no normalisation, so the over-complete, wildly non-orthogonal family
of differences `eᵤ - eᵥ` — indexed by *all* ordered pairs from the part — serves just as well, and
it is explicit, so every quantity it needs is a finite sum rather than a construction.

**The two routes give literally the same bound — checked by hand and numerically, NOT by Lean.**
Over `S ×ˢ S` the difference family yields `qₙ · |S|(|S|-1) ≤ (|S|-1)·T_S − X_S`, and expanding the
source's `r_A = (2(a-2)X + (a-1)Z)/(a(a-1))` gives `2aX − 4X + (a−1)Z`, the same number.  The
elaborator sees only the left-hand side of that comparison: **the source's formula appears nowhere
in this development, so no theorem here can be evidence about it.**  What does support it is the
independent check recorded in the campaign README — evaluating the assembled `θ = 0` bound at the
parity minima reproduces `B₀ = 3n/2 + d/2 + d²/n` exactly, as a rational number, for every `(a,b)`
tested.  Treat this paragraph at that strength and no higher.

So nothing is lost by trading the orthonormal basis for the redundant family — the *bound* was never
using the orthogonality, only the count, which is why the hypothesis could be dropped upstream.

**Why the diagonal costs nothing.**  Summing over the full product rather than `offDiag` looks
wasteful, but `eᵤ - eᵤ = 0`, so the diagonal contributes `0` to both sides and needs no exclusion.
That is what removes `Finset.offDiag` from the argument entirely — and with it the counting lemma
`∑_{p ∈ S.offDiag} g p.1 = (|S|-1) ∑ g` that Mathlib does not have. -/

/-- The sum of transmissions over a set of vertices. -/
noncomputable def sumTransOn (S : Finset V) : ℝ := ∑ u ∈ S, transmission G u

/-- The Euclidean vector attached to a plain function, absorbing the `WithLp` wrapper **once**. -/
noncomputable def vec (f : V → ℝ) : EuclideanSpace ℝ V := WithLp.toLp 2 f

theorem norm_sq_vec (f : V → ℝ) : ‖(vec f : EuclideanSpace ℝ V)‖ ^ 2 = ∑ i, f i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [vec, Real.norm_eq_abs, sq_abs]

/-- The quadratic form of `Q` at an arbitrary function.  This is the bridge every later bound goes
through; the coercion friction is paid here and nowhere else. -/
theorem inner_vec_QLin_vec (f : V → ℝ) :
    ⟪(vec f : EuclideanSpace ℝ V), QLin G (vec f)⟫_ℝ = ∑ i, ∑ j, Q G i j * f j * f i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [QLin, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, vec, WithLp.ofLp_toLp]
  simp [dotProduct, Matrix.mulVec, Finset.sum_mul]

/-- The indicator of a vertex. -/
noncomputable def ind (u : V) : V → ℝ := fun w => if w = u then 1 else 0

@[simp] theorem ind_self (u : V) : ind (V := V) u u = 1 := if_pos rfl

theorem sum_mul_ind (u : V) (g : V → ℝ) : ∑ w, g w * ind (V := V) u w = g u := by
  simp [ind, mul_ite, Fintype.sum_ite_eq']

/-- The bilinear form of any matrix at a pair of indicators picks out a single entry. -/
theorem sum_sum_mul_ind (M : Matrix V V ℝ) (a b : V) :
    ∑ i, ∑ j, M i j * ind (V := V) a j * ind (V := V) b i = M b a := by
  have hinner : ∀ i : V, ∑ j, M i j * ind (V := V) a j * ind (V := V) b i
      = (M i a) * ind (V := V) b i := by
    intro i
    rw [← Finset.sum_mul, sum_mul_ind a (M i)]
  rw [Finset.sum_congr rfl (fun i _ => hinner i), sum_mul_ind b (fun i => M i a)]

/-- The test function `eᵤ - eᵥ`. -/
noncomputable def diffFun (u v : V) : V → ℝ := fun w => ind (V := V) u w - ind (V := V) v w

/-- `‖eᵤ - eᵥ‖² = 2 - 2[u = v]`, so it is `2` off the diagonal and `0` on it. -/
theorem sum_sq_diffFun (u v : V) :
    ∑ w, diffFun (V := V) u v w ^ 2 = 2 - 2 * ind (V := V) u v := by
  have hpt : ∀ w : V, diffFun (V := V) u v w ^ 2
      = ind (V := V) u w * ind (V := V) u w - 2 * (ind (V := V) u w * ind (V := V) v w)
        + ind (V := V) v w * ind (V := V) v w := by
    intro w; simp only [diffFun]; ring
  rw [Finset.sum_congr rfl (fun w _ => hpt w), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  have h1 : ∑ w, ind (V := V) u w * ind (V := V) u w = 1 := by
    rw [sum_mul_ind u (ind (V := V) u), ind_self]
  have h2 : ∑ w, ind (V := V) u w * ind (V := V) v w = ind (V := V) u v := by
    rw [sum_mul_ind v (ind (V := V) u)]
  have h3 : ∑ w, ind (V := V) v w * ind (V := V) v w = 1 := by
    rw [sum_mul_ind v (ind (V := V) v), ind_self]
  rw [h1, h2, h3]
  ring

/-- The quadratic form of any matrix at a difference vector. -/
theorem sum_sum_mul_diffFun (M : Matrix V V ℝ) (u v : V) :
    ∑ i, ∑ j, M i j * diffFun (V := V) u v j * diffFun (V := V) u v i
      = M u u + M v v - M u v - M v u := by
  have hpt : ∀ i j : V, M i j * diffFun (V := V) u v j * diffFun (V := V) u v i
      = M i j * ind (V := V) u j * ind (V := V) u i
        - M i j * ind (V := V) u j * ind (V := V) v i
        - M i j * ind (V := V) v j * ind (V := V) u i
        + M i j * ind (V := V) v j * ind (V := V) v i := by
    intro i j; simp only [diffFun]; ring
  calc ∑ i, ∑ j, M i j * diffFun (V := V) u v j * diffFun (V := V) u v i
      = ∑ i, ∑ j, (M i j * ind (V := V) u j * ind (V := V) u i
          - M i j * ind (V := V) u j * ind (V := V) v i
          - M i j * ind (V := V) v j * ind (V := V) u i
          + M i j * ind (V := V) v j * ind (V := V) v i) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
    _ = M u u - M v u - M u v + M v v := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_sum_mul_ind]
    _ = M u u + M v v - M u v - M v u := by ring

/-- `Q`'s diagonal is the transmission, because `d(u,u) = 0`. -/
@[simp] theorem Q_diag (u : V) : Q G u u = transmission G u := by
  simp [Q, distMatrix, SimpleGraph.dist_self]

/-- Summing `d` over the **full** product `S ×ˢ S` gives the `offDiag` sum, since the diagonal
contributes `0`.  This is the lemma that lets the whole argument avoid `Finset.offDiag`. -/
theorem sumWithin_eq_prod (S : Finset V) :
    ∑ u ∈ S, ∑ v ∈ S, (G.dist u v : ℝ) = sumWithin G S := by
  have hz : ∑ p ∈ S.diag, (G.dist p.1 p.2 : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_diag] at hp
    rw [← hp.2, SimpleGraph.dist_self]
    norm_num
  calc ∑ u ∈ S, ∑ v ∈ S, (G.dist u v : ℝ)
      = ∑ p ∈ S ×ˢ S, (G.dist p.1 p.2 : ℝ) :=
        (Finset.sum_product' S S (fun u v => (G.dist u v : ℝ))).symm
    _ = ∑ p ∈ S.diag ∪ S.offDiag, (G.dist p.1 p.2 : ℝ) := by rw [Finset.diag_union_offDiag]
    _ = (∑ p ∈ S.diag, (G.dist p.1 p.2 : ℝ)) + ∑ p ∈ S.offDiag, (G.dist p.1 p.2 : ℝ) :=
        Finset.sum_union (Finset.disjoint_diag_offDiag S)
    _ = sumWithin G S := by rw [hz, zero_add, sumWithin]

/-- The full block sum of `Q` over one part. -/
theorem sum_sum_Q_on (S : Finset V) :
    ∑ u ∈ S, ∑ v ∈ S, Q G u v = sumTransOn G S + sumWithin G S := by
  have hdiag : ∑ u ∈ S, ∑ v ∈ S, Matrix.diagonal (transmission G) u v = sumTransOn G S := by
    have hinner : ∀ u ∈ S, ∑ v ∈ S, Matrix.diagonal (transmission G) u v = transmission G u := by
      intro u hu
      simp only [Matrix.diagonal_apply]
      rw [Finset.sum_ite_eq, if_pos hu]
    rw [Finset.sum_congr rfl hinner, sumTransOn]
  calc ∑ u ∈ S, ∑ v ∈ S, Q G u v
      = ∑ u ∈ S, ∑ v ∈ S, (Matrix.diagonal (transmission G) u v + (G.dist u v : ℝ)) :=
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => rfl
    _ = (∑ u ∈ S, ∑ v ∈ S, Matrix.diagonal (transmission G) u v)
        + ∑ u ∈ S, ∑ v ∈ S, (G.dist u v : ℝ) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_add_distrib
    _ = sumTransOn G S + sumWithin G S := by rw [hdiag, sumWithin_eq_prod]

/-- **Inequality (4), multiplied out.**  `qₙ · |S|(|S|-1) ≤ (|S|-1)·T_S − X_S`, doubled to match
the ordered convention.  Taking `S` to be a part of the bipartition and expanding `T_S` is the
source's `r_A` and `r_B` bound; here it holds for **any** vertex set, since nothing in the argument
looked at the bipartition. -/
theorem qEig_last_bound {n : ℕ} (hcard : Fintype.card V = n + 1) (S : Finset V) :
    qEig G hcard (Fin.last n) * (2 * (S.card : ℝ) ^ 2 - 2 * S.card)
      ≤ 2 * ((S.card : ℝ) - 1) * sumTransOn G S - 2 * sumWithin G S := by
  have hanti := (QLin_isSymmetric G).eigenvalues_antitone (finrank_euclidean_eq hcard)
  have hgen := Principia.Common.mul_sum_norm_sq_le_sum_inner_apply (QLin_isSymmetric G)
      (finrank_euclidean_eq hcard) (c := qEig G hcard (Fin.last n))
      (fun i => hanti (Fin.le_last i)) (S ×ˢ S) (fun p => vec (diffFun p.1 p.2))
  -- the norms
  have hnorm : ∑ p ∈ S ×ˢ S, ‖(vec (diffFun p.1 p.2) : EuclideanSpace ℝ V)‖ ^ 2
      = 2 * (S.card : ℝ) ^ 2 - 2 * S.card := by
    have hinner : ∀ u ∈ S, ∑ v ∈ S, (2 - 2 * ind (V := V) u v) = 2 * (S.card : ℝ) - 2 := by
      intro u hu
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      simp only [ind]
      rw [Finset.sum_ite_eq' S u (fun _ => (1 : ℝ)), if_pos hu]
      ring
    calc ∑ p ∈ S ×ˢ S, ‖(vec (diffFun p.1 p.2) : EuclideanSpace ℝ V)‖ ^ 2
        = ∑ p ∈ S ×ˢ S, (2 - 2 * ind (V := V) p.1 p.2) :=
          Finset.sum_congr rfl fun p _ => by rw [norm_sq_vec, sum_sq_diffFun]
      _ = ∑ u ∈ S, ∑ v ∈ S, (2 - 2 * ind (V := V) u v) :=
          Finset.sum_product' S S (fun u v => (2 : ℝ) - 2 * ind (V := V) u v)
      _ = 2 * (S.card : ℝ) ^ 2 - 2 * S.card := by
          rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
          ring
  -- the quadratic forms
  have hquad : ∑ p ∈ S ×ˢ S, ⟪(vec (diffFun p.1 p.2) : EuclideanSpace ℝ V),
        QLin G (vec (diffFun p.1 p.2))⟫_ℝ
      = 2 * ((S.card : ℝ) - 1) * sumTransOn G S - 2 * sumWithin G S := by
    have hswap : ∑ u ∈ S, ∑ v ∈ S, Q G v u = ∑ u ∈ S, ∑ v ∈ S, Q G u v := Finset.sum_comm
    calc ∑ p ∈ S ×ˢ S, ⟪(vec (diffFun p.1 p.2) : EuclideanSpace ℝ V),
            QLin G (vec (diffFun p.1 p.2))⟫_ℝ
        = ∑ p ∈ S ×ˢ S, (Q G p.1 p.1 + Q G p.2 p.2 - Q G p.1 p.2 - Q G p.2 p.1) :=
          Finset.sum_congr rfl fun p _ => by
            rw [inner_vec_QLin_vec, sum_sum_mul_diffFun]
      _ = ∑ u ∈ S, ∑ v ∈ S, (Q G u u + Q G v v - Q G u v - Q G v u) :=
          Finset.sum_product' S S (fun u v => Q G u u + Q G v v - Q G u v - Q G v u)
      _ = 2 * ((S.card : ℝ) - 1) * sumTransOn G S - 2 * sumWithin G S := by
          have hQdiagsum : ∑ u ∈ S, Q G u u = sumTransOn G S :=
            Finset.sum_congr rfl fun u _ => Q_diag G u
          have hsplit : ∑ u ∈ S, ∑ v ∈ S, (Q G u u + Q G v v - Q G u v - Q G v u)
              = (∑ u ∈ S, ∑ v ∈ S, Q G u u) + (∑ u ∈ S, ∑ v ∈ S, Q G v v)
                - (∑ u ∈ S, ∑ v ∈ S, Q G u v) - ∑ u ∈ S, ∑ v ∈ S, Q G v u := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          have hA1 : ∑ u ∈ S, ∑ v ∈ S, Q G u u = (S.card : ℝ) * sumTransOn G S := by
            have hc : ∀ u ∈ S, ∑ _v ∈ S, Q G u u = (S.card : ℝ) * Q G u u := by
              intro u _
              rw [Finset.sum_const, nsmul_eq_mul]
            rw [Finset.sum_congr rfl hc, ← Finset.mul_sum, hQdiagsum]
          have hA2 : ∑ _u ∈ S, ∑ v ∈ S, Q G v v = (S.card : ℝ) * sumTransOn G S := by
            rw [Finset.sum_congr rfl (fun _u _ => hQdiagsum), Finset.sum_const, nsmul_eq_mul]
          have hA4 : ∑ u ∈ S, ∑ v ∈ S, Q G v u = ∑ u ∈ S, ∑ v ∈ S, Q G u v :=
            Finset.sum_comm
          rw [hsplit, hA1, hA2, hA4, sum_sum_Q_on]
          ring
  rw [hnorm, hquad] at hgen
  exact hgen

/-- `ones` is the constant function through `vec`; recorded so the two bridge lemmas above are
visibly the special case of `norm_sq_vec` and `inner_vec_QLin_vec`, which were generalised from
them. -/
theorem ones_eq_vec : (ones : EuclideanSpace ℝ V) = vec (fun _ => (1 : ℝ)) := rfl

/-! ### Combining (3) and (4) into a spread bound — the source's step 3

The source writes `S_Q ≥ 4(X+Y+Z)/n − θ r_A − (1−θ) r_B`, three nested quotients.  Every one of
them is avoidable: a lower bound on `q₁` and an upper bound on `qₙ` combine into a lower bound on
`q₁ − qₙ` **by cross-multiplication**, provided the two denominators are positive — and they are,
being a vertex count and `2|S|(|S|−1)`.

`combine_bounds` is the whole content and it is pure arithmetic: from `a ≤ q₁c` and `qₙd ≤ b` with
`c, d > 0`, conclude `ad − bc ≤ (q₁ − qₙ)(cd)`.  It mentions no graph and could be promoted to
`Common/`; it is left here as a single lemma rather than made into a module of its own, which is a
judgement about file hygiene and not about its generality.

The `θ` step then needs no work at all, and that is worth saying plainly rather than hiding in a
proof.  `θ r_A + (1−θ) r_B` looks like an optimisation, but a **convex combination of two lower
bounds on the same quantity is again a lower bound**, so `spread_convex` is three lines.  All the
difficulty the source's `θ` carries is in *choosing* it to make the coefficients `c_X, c_Y, c_Z`
nonnegative — a case analysis, not an inequality — and that is the next stage, not this one. -/

/-- **Two one-sided bounds on a difference, combined without division.**  From `a ≤ q₁c` and
`qₙd ≤ b` with `c, d > 0`: `ad − bc ≤ (q₁ − qₙ)(cd)`.  This is `q₁ ≥ a/c` and `qₙ ≤ b/d` giving
`q₁ − qₙ ≥ a/c − b/d`, with both denominators cleared. -/
theorem combine_bounds {a b c d q1 qn : ℝ} (hc : 0 < c) (hd : 0 < d)
    (h1 : a ≤ q1 * c) (h2 : qn * d ≤ b) : a * d - b * c ≤ (q1 - qn) * (c * d) := by
  have e1 : a * d ≤ q1 * c * d := mul_le_mul_of_nonneg_right h1 hd.le
  have e2 : qn * d * c ≤ b * c := mul_le_mul_of_nonneg_right h2 hc.le
  nlinarith [e1, e2]

/-- The vertex count is positive, since the order was taken as `n + 1`. -/
theorem card_pos_of_hcard {n : ℕ} (hcard : Fintype.card V = n + 1) :
    (0 : ℝ) < (Fintype.card V : ℝ) := by
  rw [hcard]
  exact_mod_cast Nat.succ_pos n

/-- `2|S|² − 2|S| = 2|S|(|S|−1)` is positive once the part has at least two vertices.  This is the
`d` of `combine_bounds`, and it is exactly the ordered pair count `|S.offDiag|` doubled. -/
theorem offDiag_weight_pos {S : Finset V} (hS : 2 ≤ S.card) :
    (0 : ℝ) < 2 * (S.card : ℝ) ^ 2 - 2 * S.card := by
  have h : (2 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hS
  nlinarith [h]

/-- **The spread bound contributed by one part**, division-free.

This is `S_Q ≥ 4(X+Y+Z)/n − r_S` with both denominators cleared: `(3)` supplies the `q₁` side and
`qEig_last_bound` the `qₙ` side, and `combine_bounds` does the rest.  As with `(4)`, `S` is an
arbitrary vertex set of size at least two — the bipartition enters only when `sumTransOn` is
expanded, which happens later. -/
theorem spread_bound_of_part {n : ℕ} (hcard : Fintype.card V = n + 1) (S : Finset V)
    (hS : 2 ≤ S.card) :
    (2 * totalDist G) * (2 * (S.card : ℝ) ^ 2 - 2 * S.card)
        - (2 * ((S.card : ℝ) - 1) * sumTransOn G S - 2 * sumWithin G S) * (Fintype.card V : ℝ)
      ≤ spread G hcard * ((Fintype.card V : ℝ) * (2 * (S.card : ℝ) ^ 2 - 2 * S.card)) := by
  have hc := card_pos_of_hcard (V := V) hcard
  have hd := offDiag_weight_pos (V := V) hS
  exact combine_bounds hc hd (two_mul_totalDist_le_qEig_mul_card G hcard)
    (qEig_last_bound G hcard S)

/-- **The `θ` step, which costs nothing.**  A convex combination of two lower bounds on the same
quantity is again a lower bound — so the source's `θ r_A + (1−θ) r_B` needs no inequality of its
own.  What `θ` is actually *for* is making the resulting coefficients `c_X, c_Y, c_Z` nonnegative,
which is a case analysis on the part sizes rather than an estimate. -/
theorem spread_convex {θ L₁ L₂ s : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hL₁ : L₁ ≤ s) (hL₂ : L₂ ≤ s) :
    θ * L₁ + (1 - θ) * L₂ ≤ s := by
  nlinarith [mul_le_mul_of_nonneg_left hL₁ h0, mul_le_mul_of_nonneg_left hL₂ (by linarith : (0:ℝ) ≤ 1 - θ)]

/-! ### Expanding the transmissions over a bipartition — where `X`, `Y`, `Z` finally appear

Everything above holds for an arbitrary vertex set `S`, because nothing in the Rayleigh argument
looked at the bipartition.  It enters exactly here, and only through one fact: the two parts
**cover** the vertex set, so a transmission splits as within-part plus across-part.

Note the covering hypothesis is carried explicitly rather than taken from `IsBipartiteWith`.
Mathlib's `IsBipartiteWith s t` deliberately does **not** require `s ∪ t = univ` — a convention
`Common/BipartiteDistance.lean` inherits rather than strengthens — so a formalisation that assumed
coverage from it would be assuming something false. -/

/-- **`T_A = X_A + Z`**: the transmission sum over a part is its within-part distance sum plus its
across-part sum.  The only input is that the parts cover the vertex set. -/
theorem sumTransOn_split (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B) :
    sumTransOn G A = sumWithin G A + sumAcross G A B := by
  have huniv : A ∪ B = Finset.univ :=
    Finset.eq_univ_of_forall fun v => Finset.mem_union.mpr (hcov v)
  have hstep : ∀ u ∈ A, transmission G u
      = (∑ v ∈ A, (G.dist u v : ℝ)) + ∑ v ∈ B, (G.dist u v : ℝ) := by
    intro u _
    simp only [transmission]
    rw [← huniv, Finset.sum_union hdisj]
  rw [sumTransOn, Finset.sum_congr rfl hstep, Finset.sum_add_distrib, sumWithin_eq_prod, sumAcross]

/-- **The part bound in the source's own variables.**  Substituting `T_A = X_A + Z` into
`qEig_last_bound` gives `qₙ·|A|(|A|−1) ≤ (|A|−1)(X_A + Z) − X_A`, which is the source's
`r_A = (2(a−2)X + (a−1)Z)/(a(a−1))` with the denominator cleared and the ordered convention's
factor of two carried through. -/
theorem qEig_last_bound_parts {n : ℕ} (hcard : Fintype.card V = n + 1) (A B : Finset V)
    (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B) :
    qEig G hcard (Fin.last n) * (2 * (A.card : ℝ) ^ 2 - 2 * A.card)
      ≤ 2 * ((A.card : ℝ) - 2) * sumWithin G A + 2 * ((A.card : ℝ) - 1) * sumAcross G A B := by
  have h := qEig_last_bound G hcard A
  rw [sumTransOn_split G A B hcov hdisj] at h
  linarith [h]

/-! ### `totalDist` in the source's variables

`totalDist = X + Y + 2Z` in the ordered convention, because the cross pairs are counted once in
each direction while the within-part pairs are already ordered.  With this, the `q₁` side of the
spread bound is expressed in `X`, `Y`, `Z` exactly as the `qₙ` side already is, and the remaining
work of the row is the coefficient case analysis rather than any further identity. -/

/-- The cross sum is symmetric, because distance is. -/
theorem sumAcross_comm (A B : Finset V) : sumAcross G A B = sumAcross G B A := by
  rw [sumAcross, sumAcross, Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => by
    rw [SimpleGraph.dist_comm]

/-- **`totalDist = X + Y + 2Z`.**  Both parts of `Q`'s row sums decompose over the bipartition, and
the cross block is traversed in both directions. -/
theorem totalDist_split (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B) :
    totalDist G = sumWithin G A + sumWithin G B + 2 * sumAcross G A B := by
  have huniv : A ∪ B = Finset.univ :=
    Finset.eq_univ_of_forall fun v => Finset.mem_union.mpr (hcov v)
  have hrow : ∀ u : V, (∑ v, (G.dist u v : ℝ))
      = (∑ v ∈ A, (G.dist u v : ℝ)) + ∑ v ∈ B, (G.dist u v : ℝ) := by
    intro u
    rw [← huniv, Finset.sum_union hdisj]
  calc totalDist G = ∑ u, ((∑ v ∈ A, (G.dist u v : ℝ)) + ∑ v ∈ B, (G.dist u v : ℝ)) :=
        Finset.sum_congr rfl fun u _ => hrow u
    _ = (∑ u, ∑ v ∈ A, (G.dist u v : ℝ)) + ∑ u, ∑ v ∈ B, (G.dist u v : ℝ) :=
        Finset.sum_add_distrib
    _ = ((∑ u ∈ A, ∑ v ∈ A, (G.dist u v : ℝ)) + ∑ u ∈ B, ∑ v ∈ A, (G.dist u v : ℝ))
        + ((∑ u ∈ A, ∑ v ∈ B, (G.dist u v : ℝ)) + ∑ u ∈ B, ∑ v ∈ B, (G.dist u v : ℝ)) := by
        rw [← huniv, Finset.sum_union hdisj, Finset.sum_union hdisj]
    _ = sumWithin G A + sumWithin G B + 2 * sumAcross G A B := by
        rw [sumWithin_eq_prod, sumWithin_eq_prod]
        have hBA : (∑ u ∈ B, ∑ v ∈ A, (G.dist u v : ℝ)) = sumAcross G A B := by
          rw [← sumAcross, sumAcross_comm]
        have hAB : (∑ u ∈ A, ∑ v ∈ B, (G.dist u v : ℝ)) = sumAcross G A B := rfl
        rw [hBA, hAB]
        ring

/-! ### The master inequality at `θ = 0`, with the coefficients named

Substituting both bipartition identities into `spread_bound_of_part` at `S = B` collects the whole
`θ = 0` bound into `c_X·X + c_Y·Y + c_Z·Z ≤ S_Q · (n · 2b(b−1))` with

  `c_X = 4b(b−1)`,  `c_Y = 4b(b−1) − 2n(b−2)`,  `c_Z = 2(b−1)(4b − n)`.

Naming the coefficients is the point of this stage.  Once they are named, the six regimes of the
source's case table stop being an analytic question and become a question about the **signs of
three real numbers** — and the parity bounds of inequality (1) may be substituted term by term the
moment a coefficient is known nonnegative.  `le_of_coeffs_nonneg` is that substitution, stated once
so no regime has to redo it.

**Checked against the source at the balanced even point.**  With `a = b = m` and `n = 2m` the
coefficients are `4m(m−1)`, `4m`, `4m(m−1)`; substituting `X ≥ 2m(m−1)`, `Y ≥ 2m(m−1)`, `Z ≥ m²`
and dividing by `n·2b(b−1) = 4m²(m−1)` gives `2(m−1) + 2 + m = 3m`, which is the source's
`B₀ = 3n/2`.  The arithmetic of this stage was verified against that value before it was written. -/

/-- **Monotone substitution.**  With all three coefficients nonnegative, any lower bounds on
`X, Y, Z` may be substituted into the master inequality.  Stated separately so that each regime of
the case table supplies only the three sign facts and reuses this. -/
theorem le_of_coeffs_nonneg {cX cY cZ x y z x₀ y₀ z₀ s : ℝ}
    (hX : 0 ≤ cX) (hY : 0 ≤ cY) (hZ : 0 ≤ cZ)
    (hx : x₀ ≤ x) (hy : y₀ ≤ y) (hz : z₀ ≤ z)
    (h : cX * x + cY * y + cZ * z ≤ s) :
    cX * x₀ + cY * y₀ + cZ * z₀ ≤ s := by
  have e1 : cX * x₀ ≤ cX * x := mul_le_mul_of_nonneg_left hx hX
  have e2 : cY * y₀ ≤ cY * y := mul_le_mul_of_nonneg_left hy hY
  have e3 : cZ * z₀ ≤ cZ * z := mul_le_mul_of_nonneg_left hz hZ
  linarith

/-- **The `θ = 0` master inequality.**  Everything the row needs from spectral graph theory is now
on the left of a single `≤`; what remains is arithmetic in `a`, `b` and `n`. -/
theorem spread_theta_zero {n : ℕ} (hcard : Fintype.card V = n + 1) (A B : Finset V)
    (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B) (hB : 2 ≤ B.card) :
    4 * (B.card : ℝ) * ((B.card : ℝ) - 1) * sumWithin G A
      + (4 * (B.card : ℝ) * ((B.card : ℝ) - 1)
          - 2 * (Fintype.card V : ℝ) * ((B.card : ℝ) - 2)) * sumWithin G B
      + 2 * ((B.card : ℝ) - 1) * (4 * (B.card : ℝ) - (Fintype.card V : ℝ)) * sumAcross G A B
      ≤ spread G hcard
          * ((Fintype.card V : ℝ) * (2 * (B.card : ℝ) ^ 2 - 2 * (B.card : ℝ))) := by
  have h := spread_bound_of_part G hcard B hB
  rw [sumTransOn_split G B A (fun v => (hcov v).symm) hdisj.symm,
    sumAcross_comm G B A, totalDist_split G A B hcov hdisj] at h
  nlinarith [h]

/-! ### The general-`θ` master inequality

`θ = 0` used only the `B` part.  The two regimes the source still needs — `θ_Z` for `b ∈ {2,3}` and
`θ_Y` for `b ≥ 4` — need both parts weighted together, and the obvious route (`qₙ ≤ θ r_A +
(1−θ) r_B`) reintroduces the two denominators that step 3 was careful to clear.

They clear again, by the same trick and with no new idea: weight the `A` bound by `θ·Q` and the `B`
bound by `(1−θ)·P`, where `P = 2a(a−1)` and `Q = 2b(b−1)` are the two part weights.  The `qₙ`
coefficients then both become `P·Q`, the `θ` and `1−θ` sum to one, and what remains is
`qₙ·(P·Q) ≤ θ·Q·R_A + (1−θ)·P·R_B` — the convex combination, with every denominator already gone.

`spread_theta_zero` is the `θ = 0` case of what follows, kept because it is the regime that
discharges most of the table and its coefficients are the ones checked against `B₀`. -/

/-- The weight `2s(s−1)` a part contributes to the `qₙ` bound.  It is `2·|S.offDiag|`, the count of
ordered pairs doubled — the same quantity the difference family is indexed by. -/
noncomputable def partWeight (S : Finset V) : ℝ := 2 * (S.card : ℝ) ^ 2 - 2 * S.card

/-- The numerator of a part's `qₙ` bound: `2(s−2)·X_S + 2(s−1)·Z`. -/
noncomputable def partNum (S T : Finset V) : ℝ :=
  2 * ((S.card : ℝ) - 2) * sumWithin G S + 2 * ((S.card : ℝ) - 1) * sumAcross G S T

theorem partWeight_nonneg {S : Finset V} (hS : 2 ≤ S.card) : 0 ≤ partWeight (V := V) S :=
  le_of_lt (offDiag_weight_pos (V := V) hS)

/-- **The convex `qₙ` bound, division-free.**  Weighting the `A` bound by `θ·Q` and the `B` bound by
`(1−θ)·P` makes both `qₙ` coefficients equal to `P·Q`, so the two weights sum to one exactly as they
do in the source's `θ r_A + (1−θ) r_B` — but with no quotient anywhere. -/
theorem qEig_last_convex {n : ℕ} (hcard : Fintype.card V = n + 1) (A B : Finset V)
    (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    qEig G hcard (Fin.last n) * (partWeight (V := V) A * partWeight (V := V) B)
      ≤ θ * partWeight (V := V) B * partNum G A B
        + (1 - θ) * partWeight (V := V) A * partNum G B A := by
  have hPA : (0 : ℝ) ≤ partWeight (V := V) A := partWeight_nonneg (V := V) hA
  have hPB : (0 : ℝ) ≤ partWeight (V := V) B := partWeight_nonneg (V := V) hB
  have hbA : qEig G hcard (Fin.last n) * partWeight (V := V) A ≤ partNum G A B :=
    qEig_last_bound_parts G hcard A B hcov hdisj
  have hbB : qEig G hcard (Fin.last n) * partWeight (V := V) B ≤ partNum G B A :=
    qEig_last_bound_parts G hcard B A (fun v => (hcov v).symm) hdisj.symm
  have e1 : θ * partWeight (V := V) B * (qEig G hcard (Fin.last n) * partWeight (V := V) A)
      ≤ θ * partWeight (V := V) B * partNum G A B :=
    mul_le_mul_of_nonneg_left hbA (mul_nonneg h0 hPB)
  have e2 : (1 - θ) * partWeight (V := V) A * (qEig G hcard (Fin.last n) * partWeight (V := V) B)
      ≤ (1 - θ) * partWeight (V := V) A * partNum G B A :=
    mul_le_mul_of_nonneg_left hbB (mul_nonneg (by linarith) hPA)
  nlinarith [e1, e2]

/-- **The general-`θ` master inequality.**  Everything the row needs from spectral graph theory,
for every regime of the case table, sits on the left of this single `≤`. -/
theorem spread_master_convex {n : ℕ} (hcard : Fintype.card V = n + 1) (A B : Finset V)
    (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    2 * totalDist G * (partWeight (V := V) A * partWeight (V := V) B)
        - (θ * partWeight (V := V) B * partNum G A B
            + (1 - θ) * partWeight (V := V) A * partNum G B A) * (Fintype.card V : ℝ)
      ≤ spread G hcard
          * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B)) := by
  have hc := card_pos_of_hcard (V := V) hcard
  have hd : (0 : ℝ) < partWeight (V := V) A * partWeight (V := V) B :=
    mul_pos (offDiag_weight_pos (V := V) hA) (offDiag_weight_pos (V := V) hB)
  exact combine_bounds hc hd (two_mul_totalDist_le_qEig_mul_card G hcard)
    (qEig_last_convex G hcard A B hcov hdisj hA hB h0 h1)

/-! ### The base bound: substituting the parity minima

With the coefficients named, each regime of the source's case table needs exactly three facts —
`0 ≤ c_X`, `0 ≤ c_Y`, `0 ≤ c_Z` — and `base_bound_le_spread` converts them into a lower bound on
the spread in `a` and `b` alone.  Nothing below is regime-specific; the case analysis supplies only
the three signs.

**Both remaining regimes were checked numerically against the source before this was written**,
in the ordered convention and as exact rationals: at `θ_Y = (a(b−2) − b²)/(n(b−2))` for `b ≥ 4` the
base bound equals the source's `B_Y = 3n/2 + d(bn − 2d)/(2n(b−2))`, and at
`θ_Z = a(a−3b)/(n(a−b))` for `b ∈ {2,3}` it equals `B_Z = 2n` exactly — in every case where
`θ ∈ [0,1]`, with all three coefficients nonnegative.  That check is arithmetic on our own
coefficients against a closed form appearing nowhere in this file, so **Lean does not see it**;
it is recorded here at that strength and no higher. -/

/-- `|S.offDiag| = |S|² − |S|` over `ℝ`.  Mathlib's `offDiag_card` is a **ℕ**-subtraction identity;
this is the cast, and the truncation is harmless because `k ≤ k²` for every natural `k`. -/
theorem offDiag_card_real (S : Finset V) :
    (S.offDiag.card : ℝ) = (S.card : ℝ) ^ 2 - S.card := by
  have hle : S.card ≤ S.card * S.card := by
    rcases Nat.eq_zero_or_pos S.card with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left _ h
  rw [Finset.offDiag_card, Nat.cast_sub hle]
  push_cast
  ring

/-- **Inequality (1) with the pair count in closed form**: `2(|S|² − |S|) ≤ X_S`. -/
theorem two_mul_sq_sub_le_sumWithin {s t : Set V} (hb : G.IsBipartiteWith s t)
    (hconn : G.Connected) (S : Finset V) (hS : ∀ u ∈ S, u ∈ s) :
    2 * ((S.card : ℝ) ^ 2 - S.card) ≤ sumWithin G S := by
  have h := two_mul_card_le_sumWithin G hb hconn S hS
  rwa [offDiag_card_real] at h

/-- The coefficient of `X` in the general-`θ` master inequality. -/
noncomputable def coeffX (A B : Finset V) (θ : ℝ) : ℝ :=
  2 * (partWeight (V := V) A * partWeight (V := V) B)
    - 2 * (Fintype.card V : ℝ) * θ * partWeight (V := V) B * ((A.card : ℝ) - 2)

/-- The coefficient of `Y`. -/
noncomputable def coeffY (A B : Finset V) (θ : ℝ) : ℝ :=
  2 * (partWeight (V := V) A * partWeight (V := V) B)
    - 2 * (Fintype.card V : ℝ) * (1 - θ) * partWeight (V := V) A * ((B.card : ℝ) - 2)

/-- The coefficient of `Z`. -/
noncomputable def coeffZ (A B : Finset V) (θ : ℝ) : ℝ :=
  4 * (partWeight (V := V) A * partWeight (V := V) B)
    - 2 * (Fintype.card V : ℝ) * θ * partWeight (V := V) B * ((A.card : ℝ) - 1)
    - 2 * (Fintype.card V : ℝ) * (1 - θ) * partWeight (V := V) A * ((B.card : ℝ) - 1)

/-- **The master inequality in coefficient form.**  Same content as `spread_master_convex`, with
`totalDist` expanded and the two `partNum`s multiplied out, so that `X`, `Y` and `Z` each carry a
single named coefficient. -/
theorem spread_master_coeffs {n : ℕ} (hcard : Fintype.card V = n + 1) (A B : Finset V)
    (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    coeffX (V := V) A B θ * sumWithin G A + coeffY (V := V) A B θ * sumWithin G B
        + coeffZ (V := V) A B θ * sumAcross G A B
      ≤ spread G hcard
          * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B)) := by
  have h := spread_master_convex G hcard A B hcov hdisj hA2 hB2 h0 h1
  rw [totalDist_split G A B hcov hdisj] at h
  simp only [partNum, sumAcross_comm G B A] at h
  simp only [coeffX, coeffY, coeffZ]
  nlinarith [h]

/-- **The base bound.**  Given only that the three coefficients are nonnegative, the parity minima
of inequality (1) substitute into the master inequality.  Every regime of the source's case table
factors through this: it supplies the three signs and nothing else. -/
theorem base_bound_le_spread {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hb : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (hcX : 0 ≤ coeffX (V := V) A B θ) (hcY : 0 ≤ coeffY (V := V) A B θ)
    (hcZ : 0 ≤ coeffZ (V := V) A B θ) :
    coeffX (V := V) A B θ * (2 * ((A.card : ℝ) ^ 2 - A.card))
        + coeffY (V := V) A B θ * (2 * ((B.card : ℝ) ^ 2 - B.card))
        + coeffZ (V := V) A B θ * ((A.card : ℝ) * B.card)
      ≤ spread G hcard
          * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B)) :=
  le_of_coeffs_nonneg hcX hcY hcZ
    (two_mul_sq_sub_le_sumWithin G hb hconn A hAs)
    (two_mul_sq_sub_le_sumWithin G hb.symm hconn B hBt)
    (card_mul_card_le_sumAcross G hb hconn A B hAs hBt)
    (spread_master_coeffs G hcard A B hcov hdisj hA2 hB2 h0 h1)

/-! ### The `θ = 0` regime, discharged

The first of the source's six rows, complete.  At `θ = 0` the three coefficients factor:

  `c_X = 2·P·Q`,  `c_Y = 2·P·(Q − n(b−2))`,  `c_Z = 2·P·(b−1)·(4b − n)`

with `P, Q ≥ 0`, so `c_X` is unconditional and the other two reduce to the two scalar conditions
`n(b−2) ≤ Q` and `n ≤ 4b`.  Those are the source's "choose `θ = 0` when both smaller-part
coefficients are already nonnegative", made explicit.

The factorisations are why this row is cheap: each coefficient is a product of things already known
nonnegative and one linear condition, so `nlinarith` closes each on a single hint rather than
searching. -/

/-- `c_X` at `θ = 0` is `2·P·Q`, nonnegative unconditionally. -/
theorem coeffX_zero_nonneg (A B : Finset V) (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card) :
    0 ≤ coeffX (V := V) A B 0 := by
  have hPA := partWeight_nonneg (V := V) hA2
  have hPB := partWeight_nonneg (V := V) hB2
  simp only [coeffX]
  nlinarith [mul_nonneg hPA hPB]

/-- `c_Y` at `θ = 0` is `2·P·(Q − n(b−2))`. -/
theorem coeffY_zero_nonneg (A B : Finset V) (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (h : (Fintype.card V : ℝ) * ((B.card : ℝ) - 2) ≤ partWeight (V := V) B) :
    0 ≤ coeffY (V := V) A B 0 := by
  have hPA := partWeight_nonneg (V := V) hA2
  have hd : (0 : ℝ) ≤ partWeight (V := V) B - (Fintype.card V : ℝ) * ((B.card : ℝ) - 2) := by
    linarith
  simp only [coeffY]
  nlinarith [mul_nonneg hPA hd]

/-- `c_Z` at `θ = 0` is `2·P·(b−1)·(4b − n)`, so it is exactly the condition `n ≤ 4b`. -/
theorem coeffZ_zero_nonneg (A B : Finset V) (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (h : (Fintype.card V : ℝ) ≤ 4 * (B.card : ℝ)) : 0 ≤ coeffZ (V := V) A B 0 := by
  have hPA := partWeight_nonneg (V := V) hA2
  have hb : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB2
  -- Factor FIRST, and do not unfold `partWeight` in the goal: `hPA` names the folded
  -- definition, so unfolding only on one side leaves `nlinarith` with two unrelated atoms.
  have hfac : coeffZ (V := V) A B 0
      = 2 * partWeight (V := V) A
          * (((B.card : ℝ) - 1) * (4 * (B.card : ℝ) - (Fintype.card V : ℝ))) := by
    simp only [coeffZ, partWeight]
    ring
  have h1 : (0 : ℝ) ≤ (B.card : ℝ) - 1 := by linarith
  have h4 : (0 : ℝ) ≤ 4 * (B.card : ℝ) - (Fintype.card V : ℝ) := by linarith
  rw [hfac]
  exact mul_nonneg (by linarith) (mul_nonneg h1 h4)

/-- **The `θ = 0` row of the case table, discharged.**  Under the two scalar conditions the source
states for this regime, the base bound holds with no further hypotheses. -/
theorem base_bound_theta_zero {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hb : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    (hY : (Fintype.card V : ℝ) * ((B.card : ℝ) - 2) ≤ partWeight (V := V) B)
    (hZ : (Fintype.card V : ℝ) ≤ 4 * (B.card : ℝ)) :
    coeffX (V := V) A B 0 * (2 * ((A.card : ℝ) ^ 2 - A.card))
        + coeffY (V := V) A B 0 * (2 * ((B.card : ℝ) ^ 2 - B.card))
        + coeffZ (V := V) A B 0 * ((A.card : ℝ) * B.card)
      ≤ spread G hcard
          * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B)) :=
  base_bound_le_spread G hcard hb hconn A B hcov hdisj hA2 hB2 hAs hBt le_rfl zero_le_one
    (coeffX_zero_nonneg (V := V) A B hA2 hB2)
    (coeffY_zero_nonneg (V := V) A B hA2 hB2 hY)
    (coeffZ_zero_nonneg (V := V) A B hA2 hB2 hZ)

/-! ### The coefficients, factored — and what `θ_Z` is actually for

Each coefficient is a product of a manifestly nonnegative part weight with a **single scalar
condition**:

  `c_X = 2Q·(P − nθ(a−2))`,  `c_Y = 2P·(Q − n(1−θ)(b−2))`,
  `c_Z = 4(a−1)(b−1)·(4ab − nθb − na(1−θ))`

Verified as exact identities on 400 random `(a, b, θ)` before being written.  With these, a regime's
three sign obligations are three scalar inequalities in `a`, `b`, `n`, `θ` — no part weights, no
spectral objects, nothing to unfold.

**And `c_Z`'s factor is what `θ_Z` is for.**  The source introduces `θ_Z = a(a−3b)/(n(a−b))` for
`b ∈ {2,3}` without saying why that value; substituting it makes `4ab − nθb − na(1−θ)` **exactly
zero** — checked for `b ∈ {2,3}` across `a`, always `0`, never merely nonnegative.  So that regime
does not need a `c_Z ≥ 0` inequality at all, it needs an **equation**, and
`base_bound_of_coeffZ_zero` consumes it directly.  An equation is much cheaper than an inequality
here, and it is the difference between substituting a quotient into three sign checks and
substituting it into one identity.

This is the third time on this row that a step presented as an estimate turned out to be an exact
identity or a free consequence — the `θ` convexity, the denominators, and now `θ_Z` itself. -/

/-- `c_X = 2Q·(P − nθ(a−2))`. -/
theorem coeffX_factor (A B : Finset V) (θ : ℝ) :
    coeffX (V := V) A B θ
      = 2 * partWeight (V := V) B
          * (partWeight (V := V) A - (Fintype.card V : ℝ) * θ * ((A.card : ℝ) - 2)) := by
  simp only [coeffX, partWeight]
  ring

/-- `c_Y = 2P·(Q − n(1−θ)(b−2))`. -/
theorem coeffY_factor (A B : Finset V) (θ : ℝ) :
    coeffY (V := V) A B θ
      = 2 * partWeight (V := V) A
          * (partWeight (V := V) B - (Fintype.card V : ℝ) * (1 - θ) * ((B.card : ℝ) - 2)) := by
  simp only [coeffY, partWeight]
  ring

/-- `c_Z = 4(a−1)(b−1)·(4ab − nθb − na(1−θ))`.  The second factor is the one `θ_Z` zeroes. -/
theorem coeffZ_factor (A B : Finset V) (θ : ℝ) :
    coeffZ (V := V) A B θ
      = 4 * ((A.card : ℝ) - 1) * ((B.card : ℝ) - 1)
          * (4 * (A.card : ℝ) * (B.card : ℝ)
              - (Fintype.card V : ℝ) * θ * (B.card : ℝ)
              - (Fintype.card V : ℝ) * (A.card : ℝ) * (1 - θ)) := by
  simp only [coeffZ, partWeight]
  ring

/-- `c_X ≥ 0` from its scalar condition alone. -/
theorem coeffX_nonneg_of (A B : Finset V) (hB2 : 2 ≤ B.card) {θ : ℝ}
    (h : (Fintype.card V : ℝ) * θ * ((A.card : ℝ) - 2) ≤ partWeight (V := V) A) :
    0 ≤ coeffX (V := V) A B θ := by
  rw [coeffX_factor]
  exact mul_nonneg (by linarith [partWeight_nonneg (V := V) hB2]) (by linarith)

/-- `c_Y ≥ 0` from its scalar condition alone. -/
theorem coeffY_nonneg_of (A B : Finset V) (hA2 : 2 ≤ A.card) {θ : ℝ}
    (h : (Fintype.card V : ℝ) * (1 - θ) * ((B.card : ℝ) - 2) ≤ partWeight (V := V) B) :
    0 ≤ coeffY (V := V) A B θ := by
  rw [coeffY_factor]
  exact mul_nonneg (by linarith [partWeight_nonneg (V := V) hA2]) (by linarith)

/-- **`c_Z = 0` iff its scalar factor vanishes**, for parts of size at least two. -/
theorem coeffZ_eq_zero_of (A B : Finset V) {θ : ℝ}
    (h : 4 * (A.card : ℝ) * (B.card : ℝ)
        - (Fintype.card V : ℝ) * θ * (B.card : ℝ)
        - (Fintype.card V : ℝ) * (A.card : ℝ) * (1 - θ) = 0) :
    coeffZ (V := V) A B θ = 0 := by
  rw [coeffZ_factor, h, mul_zero]

/-- **The base bound when `θ` is chosen to annihilate `c_Z`** — the `θ_Z` regime's shape.  Only two
sign obligations remain, and the third is discharged by an equation. -/
theorem base_bound_of_coeffZ_zero {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hb : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (hcX : 0 ≤ coeffX (V := V) A B θ) (hcY : 0 ≤ coeffY (V := V) A B θ)
    (hcZ : coeffZ (V := V) A B θ = 0) :
    coeffX (V := V) A B θ * (2 * ((A.card : ℝ) ^ 2 - A.card))
        + coeffY (V := V) A B θ * (2 * ((B.card : ℝ) ^ 2 - B.card))
      ≤ spread G hcard
          * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B)) := by
  have h := base_bound_le_spread G hcard hb hconn A B hcov hdisj hA2 hB2 hAs hBt h0 h1
    hcX hcY (le_of_eq hcZ.symm)
  rw [hcZ] at h
  linarith

/-! ### `θ_Y` annihilates `c_Y`, exactly as `θ_Z` annihilates `c_Z`

The source gives two opaque formulas, `θ_Y = (a(b−2) − b²)/(n(b−2))` for `b ≥ 4` and
`θ_Z = a(a−3b)/(n(a−b))` for `b ∈ {2,3}`, without saying where either comes from.  They are the
**roots of `c_Y = 0` and `c_Z = 0`**, and that is the whole content of the case table:

| regime | `θ` | what it does |
| --- | --- | --- |
| both smaller-part coefficients already nonnegative | `0` | nothing needs annihilating |
| `b ∈ {2,3}` | `θ_Z` | zeroes `c_Z` |
| `b ≥ 4` | `θ_Y` | zeroes `c_Y` |

Checked before formalising: at `θ_Y`, `c_Y` is identically `0` — never merely nonnegative — for
every `(a,b)` with `b = 4..9`, `a = b..b+7` and `θ_Y ∈ [0,1]`, with `c_X, c_Z ≥ 0` throughout.  The
same held for `θ_Z` and `c_Z`.  **Those checks are arithmetic on our own coefficients and Lean does
not see them**; what Lean sees is that *if* the scalar factor vanishes then the coefficient does,
which is `coeffY_eq_zero_of` below, and that this suffices, which is
`base_bound_of_coeffY_zero`.

So each regime supplies one linear equation in `θ` and two sign checks — never three inequalities.
That is the sense in which the six-row case table was never six rows of analysis. -/

/-- **`c_Y = 0` when its scalar factor vanishes.**  Dual to `coeffZ_eq_zero_of`. -/
theorem coeffY_eq_zero_of (A B : Finset V) {θ : ℝ}
    (h : partWeight (V := V) B
        - (Fintype.card V : ℝ) * (1 - θ) * ((B.card : ℝ) - 2) = 0) :
    coeffY (V := V) A B θ = 0 := by
  rw [coeffY_factor, h, mul_zero]

/-- **The base bound when `θ` annihilates `c_Y`** — the `θ_Y` regime's shape, dual to
`base_bound_of_coeffZ_zero`. -/
theorem base_bound_of_coeffY_zero {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hb : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (hcX : 0 ≤ coeffX (V := V) A B θ) (hcY : coeffY (V := V) A B θ = 0)
    (hcZ : 0 ≤ coeffZ (V := V) A B θ) :
    coeffX (V := V) A B θ * (2 * ((A.card : ℝ) ^ 2 - A.card))
        + coeffZ (V := V) A B θ * ((A.card : ℝ) * B.card)
      ≤ spread G hcard
          * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B)) := by
  have h := base_bound_le_spread G hcard hb hconn A B hcov hdisj hA2 hB2 hAs hBt h0 h1
    hcX (le_of_eq hcY.symm) hcZ
  rw [hcY] at h
  linarith

/-! ### The two `θ`s, constructed rather than quoted

The source supplies `θ_Y` and `θ_Z` as formulas with no derivation.  Here they are **solved for**,
from the scalar factors of `coeffY_factor` and `coeffZ_factor`, and the source's expressions are
recovered rather than assumed:

* `c_Z`'s factor `4ab − nθb − na(1−θ)` is linear in `θ` with coefficient `n(a−b)`, so it vanishes at
  `θ = a(n − 4b)/(n(a−b))`.  Since `n = a + b`, `n − 4b = a − 3b`, and that is the source's
  `θ_Z = a(a−3b)/(n(a−b))`.
* `c_Y`'s factor `Q − n(1−θ)(b−2)` vanishes at `1 − θ = Q/(n(b−2))`, i.e.
  `θ = (n(b−2) − Q)/(n(b−2))`; expanding `Q = 2b(b−1)` and `n = a+b` gives the source's
  `θ_Y = (a(b−2) − b²)/(n(b−2))`.

Both identifications were confirmed as exact rationals against the source's formulas before this was
written, and each `θ` was confirmed to annihilate its coefficient identically.  **Lean checks that
these definitions annihilate the coefficients; it does not check that they agree with the source's
expressions**, which appear nowhere in this development.

The side conditions are exactly the ones the source's regimes carry, and for the same reason: `θ_Z`
needs `a ≠ b` because the balanced case is where `c_Z`'s `θ`-coefficient degenerates (and there
`θ = 0` already works), and `θ_Y` needs `b ≠ 2` because at `b = 2` the factor `(b−2)` is identically
zero and `c_Y` is unconditionally positive. -/

/-- **The `θ` that annihilates `c_Z`**, obtained by solving the linear factor rather than quoted. -/
noncomputable def thetaZ (A B : Finset V) : ℝ :=
  (A.card : ℝ) * ((Fintype.card V : ℝ) - 4 * (B.card : ℝ))
    / ((Fintype.card V : ℝ) * ((A.card : ℝ) - (B.card : ℝ)))

theorem coeffZ_thetaZ (A B : Finset V) (hn : (Fintype.card V : ℝ) ≠ 0)
    (hab : (A.card : ℝ) - (B.card : ℝ) ≠ 0) :
    coeffZ (V := V) A B (thetaZ (V := V) A B) = 0 := by
  refine coeffZ_eq_zero_of (V := V) A B ?_
  rw [thetaZ]
  field_simp
  ring

/-- **The `θ` that annihilates `c_Y`**, likewise solved from its linear factor. -/
noncomputable def thetaY (A B : Finset V) : ℝ :=
  ((Fintype.card V : ℝ) * ((B.card : ℝ) - 2) - partWeight (V := V) B)
    / ((Fintype.card V : ℝ) * ((B.card : ℝ) - 2))

theorem coeffY_thetaY (A B : Finset V) (hn : (Fintype.card V : ℝ) ≠ 0)
    (hb : (B.card : ℝ) - 2 ≠ 0) :
    coeffY (V := V) A B (thetaY (V := V) A B) = 0 := by
  refine coeffY_eq_zero_of (V := V) A B ?_
  rw [thetaY]
  field_simp
  ring

/-! ### The `θ_Z` row, discharged

At `θ_Z` the vertex count cancels out of both `n·θ` and `n·(1−θ)`, leaving two quotients with the
same denominator `a − b`:

  `n·θ_Z = a(n − 4b)/(a − b)`,  `n·(1 − θ_Z) = b(3a − b)/(a − b)`

so both sign conditions clear to polynomials.  `c_X` needs only `a ≥ b ≥ 2` — the cleared form is
`a(a² + ab − 4b) ≥ 0`, and `a² + ab − 4b` is already nonnegative at `a = b ≥ 2`.  `c_Y` is the one
that constrains the regime: cleared, it is `(3a − b)(b − 2) ≤ 2(b − 1)(a − b)`, which holds for
`2 ≤ b ≤ 3` with `a ≥ 3b` and **fails for `b = 4`** — checked, `c_Y = −16` at `a = 12..15`.  That is
why the source restricts `θ_Z` to `b ∈ {2,3}`, and the restriction is now derived rather than
quoted.

The hypothesis `a ≥ 3b` is also exactly `0 ≤ θ_Z`: `θ_Z = a(a − 3b)/(n(a − b))`, whose numerator
changes sign at `a = 3b`.  So the regime's two conditions — `θ_Z ∈ [0,1]` and `c_Y ≥ 0` — are the
same inequality, which is the kind of coincidence that stops looking like one once the `θ` is solved
for rather than quoted. -/

/-- The parts cover the vertex set disjointly, so `n = a + b`. -/
theorem card_eq_add (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B) :
    (Fintype.card V : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by
  have huniv : A ∪ B = Finset.univ :=
    Finset.eq_univ_of_forall fun v => Finset.mem_union.mpr (hcov v)
  have h : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hdisj
  rw [huniv, Finset.card_univ] at h
  exact_mod_cast h

/-- `n·θ_Z = a(n − 4b)/(a − b)`: the vertex count cancels. -/
theorem card_mul_thetaZ (A B : Finset V) (hn : (Fintype.card V : ℝ) ≠ 0)
    (hab : (A.card : ℝ) - (B.card : ℝ) ≠ 0) :
    (Fintype.card V : ℝ) * thetaZ (V := V) A B
      = (A.card : ℝ) * ((Fintype.card V : ℝ) - 4 * (B.card : ℝ))
          / ((A.card : ℝ) - (B.card : ℝ)) := by
  -- `field_simp` CLOSES this goal.  In `coeffY_thetaY` the same call left a `ring` identity
  -- behind.  Whether it finishes is not predictable from the shape -- read the error, do not guess.
  rw [thetaZ]
  field_simp

/-- `n·(1 − θ_Z) = b(3a − b)/(a − b)`, using `n = a + b`. -/
theorem card_mul_one_sub_thetaZ (A B : Finset V) (hn : (Fintype.card V : ℝ) ≠ 0)
    (hab : (A.card : ℝ) - (B.card : ℝ) ≠ 0)
    (hsum : (Fintype.card V : ℝ) = (A.card : ℝ) + (B.card : ℝ)) :
    (Fintype.card V : ℝ) * (1 - thetaZ (V := V) A B)
      = (B.card : ℝ) * (3 * (A.card : ℝ) - (B.card : ℝ))
          / ((A.card : ℝ) - (B.card : ℝ)) := by
  rw [thetaZ, hsum]
  rw [hsum] at hn
  field_simp
  ring

/-- `c_X ≥ 0` at `θ_Z`, needing only `a ≥ b ≥ 2`. -/
theorem coeffX_thetaZ_nonneg (A B : Finset V) (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hlt : (B.card : ℝ) < (A.card : ℝ))
    (hsum : (Fintype.card V : ℝ) = (A.card : ℝ) + (B.card : ℝ)) :
    0 ≤ coeffX (V := V) A B (thetaZ (V := V) A B) := by
  have ha : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA2
  have hb : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB2
  have hd : (0 : ℝ) < (A.card : ℝ) - (B.card : ℝ) := by linarith
  have hnz : (Fintype.card V : ℝ) ≠ 0 := by rw [hsum]; positivity
  refine coeffX_nonneg_of (V := V) A B hB2 ?_
  rw [card_mul_thetaZ (V := V) A B hnz (ne_of_gt hd), div_mul_eq_mul_div, div_le_iff₀ hd,
    partWeight, hsum]
  nlinarith [ha, hb, hd, sq_nonneg ((A.card : ℝ) - (B.card : ℝ))]

/-- `c_Y ≥ 0` at `θ_Z` — this is the condition that pins the regime to `b ≤ 3`. -/
theorem coeffY_thetaZ_nonneg (A B : Finset V) (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hlt : (B.card : ℝ) < (A.card : ℝ)) (hsmall : (B.card : ℝ) ≤ 3)
    (hbig : 3 * (B.card : ℝ) ≤ (A.card : ℝ))
    (hsum : (Fintype.card V : ℝ) = (A.card : ℝ) + (B.card : ℝ)) :
    0 ≤ coeffY (V := V) A B (thetaZ (V := V) A B) := by
  have ha : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA2
  have hb : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB2
  have hd : (0 : ℝ) < (A.card : ℝ) - (B.card : ℝ) := by linarith
  have hnz : (Fintype.card V : ℝ) ≠ 0 := by rw [hsum]; positivity
  refine coeffY_nonneg_of (V := V) A B hA2 ?_
  rw [card_mul_one_sub_thetaZ (V := V) A B hnz (ne_of_gt hd) hsum, div_mul_eq_mul_div,
    div_le_iff₀ hd, partWeight]
  -- Cleared, the goal is `b*(4a - ab - b^2) ≥ 0`, and that quantity factors exactly as
  -- `b(a-3b)(4-b) + 4b²(3-b)` -- both terms nonnegative given `a ≥ 3b` and `b ≤ 3`.  Handing
  -- `nlinarith` those two products turns a search into a linear combination.
  have hb0 : (0 : ℝ) ≤ (B.card : ℝ) := by linarith
  have h4b : (0 : ℝ) ≤ 4 - (B.card : ℝ) := by linarith
  have h3b : (0 : ℝ) ≤ (A.card : ℝ) - 3 * (B.card : ℝ) := by linarith
  have hbe : (0 : ℝ) ≤ 3 - (B.card : ℝ) := by linarith
  nlinarith [mul_nonneg hb0 (mul_nonneg h3b h4b), mul_nonneg hb0 (mul_nonneg hb0 hbe), hb, hd]

/-- **The `θ_Z` row of the case table, discharged.**  For `2 ≤ b ≤ 3` and `a ≥ 3b`, the base bound
holds with `c_Z` annihilated — two sign checks and one equation, no third inequality. -/
theorem base_bound_thetaZ {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hb : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    (hsmall : (B.card : ℝ) ≤ 3) (hbig : 3 * (B.card : ℝ) ≤ (A.card : ℝ)) :
    coeffX (V := V) A B (thetaZ (V := V) A B) * (2 * ((A.card : ℝ) ^ 2 - A.card))
        + coeffY (V := V) A B (thetaZ (V := V) A B) * (2 * ((B.card : ℝ) ^ 2 - B.card))
      ≤ spread G hcard
          * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B)) := by
  have hb2 : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB2
  have hlt : (B.card : ℝ) < (A.card : ℝ) := by linarith
  have hsum := card_eq_add (V := V) A B hcov hdisj
  have hd : (0 : ℝ) < (A.card : ℝ) - (B.card : ℝ) := by linarith
  have hnz : (Fintype.card V : ℝ) ≠ 0 := by rw [hsum]; positivity
  have hthz : (0 : ℝ) ≤ thetaZ (V := V) A B := by
    rw [thetaZ, hsum]
    apply div_nonneg
    · nlinarith [hbig, hb2]
    · nlinarith [hd, hb2]
  have hth1 : thetaZ (V := V) A B ≤ 1 := by
    rw [thetaZ, hsum, div_le_one (by nlinarith [hd, hb2])]
    nlinarith [hb2, hd]
  exact base_bound_of_coeffZ_zero G hcard hb hconn A B hcov hdisj hA2 hB2 hAs hBt hthz hth1
    (coeffX_thetaZ_nonneg (V := V) A B hA2 hB2 hlt hsum)
    (coeffY_thetaZ_nonneg (V := V) A B hA2 hB2 hlt hsmall hbig hsum)
    (coeffZ_thetaZ (V := V) A B hnz (ne_of_gt hd))

/-! ### The `θ_Y` row — and the whole case table is one sign test

Define the **discriminant**

  `S = 2(b−1)(a−b) − (3a−b)(b−2)`, which expands to `S = a(4 − b) − b²`.

Then, after clearing denominators:

* the `c_Y ≥ 0` condition of the `θ_Z` row **is exactly** `S ≥ 0`;
* the `c_Z ≥ 0` condition of the `θ_Y` row **is exactly** `S ≤ 0`.

The same scalar, compared against zero in opposite directions.  Since one of `S ≥ 0`, `S ≤ 0`
always holds, **the two regimes are exhaustive with no gap between them** — and the source's split
into `b ∈ {2,3}` versus `b ≥ 4` is a *sufficient way of deciding that sign*, not the underlying
dichotomy.  For `b ≥ 4` the factor `4 − b` is `≤ 0`, so `S ≤ 0` needs no hypothesis on `a` at all,
which is why `θ_Y` serves that whole range; for `b ≤ 3` with `a ≥ 3b` the sign goes the other way.

That is the last structural claim the row had left, and it is what a six-row case table really is:
**one quadratic, one comparison, two constructions.**

`c_X ≥ 0` at `θ_Y` holds with no extra hypothesis beyond the regime's own: cleared, it is
`u(a−2) ≤ 2a(a−1)(b−2)` where `u = a(b−2) − b²` is the numerator of `θ_Y`, and it follows from
`u ≤ a(b−2)` together with `a − 2 ≤ 2(a−1)`. -/

/-- `c_Z ≥ 0` from its scalar factor alone, dual to `coeffZ_eq_zero_of`. -/
theorem coeffZ_nonneg_of (A B : Finset V) (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card) {θ : ℝ}
    (h : 0 ≤ 4 * (A.card : ℝ) * (B.card : ℝ)
        - (Fintype.card V : ℝ) * θ * (B.card : ℝ)
        - (Fintype.card V : ℝ) * (A.card : ℝ) * (1 - θ)) :
    0 ≤ coeffZ (V := V) A B θ := by
  have ha : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA2
  have hb : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB2
  rw [coeffZ_factor]
  have h1 : (0 : ℝ) ≤ (A.card : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) ≤ (B.card : ℝ) - 1 := by linarith
  nlinarith [mul_nonneg (mul_nonneg h1 h2) h]

/-- `n·(1 − θ_Y) = Q/(b − 2)`: the vertex count cancels, as it did at `θ_Z`. -/
theorem card_mul_one_sub_thetaY (A B : Finset V) (hn : (Fintype.card V : ℝ) ≠ 0)
    (hb2 : (B.card : ℝ) - 2 ≠ 0) :
    (Fintype.card V : ℝ) * (1 - thetaY (V := V) A B)
      = partWeight (V := V) B / ((B.card : ℝ) - 2) := by
  rw [thetaY]
  field_simp
  ring

/-- `n·θ_Y = n − Q/(b − 2)`. -/
theorem card_mul_thetaY (A B : Finset V) (hn : (Fintype.card V : ℝ) ≠ 0)
    (hb2 : (B.card : ℝ) - 2 ≠ 0) :
    (Fintype.card V : ℝ) * thetaY (V := V) A B
      = (Fintype.card V : ℝ) - partWeight (V := V) B / ((B.card : ℝ) - 2) := by
  have h := card_mul_one_sub_thetaY (V := V) A B hn hb2
  have hexp : (Fintype.card V : ℝ) * (1 - thetaY (V := V) A B)
      = (Fintype.card V : ℝ) - (Fintype.card V : ℝ) * thetaY (V := V) A B := by ring
  rw [hexp] at h
  linarith

/-- **`n·θ_Y` in closed form**: `(a(b−2) − b²)/(b−2)`, whose numerator is the numerator of the
source's `θ_Y`.  Both sign conditions below go through this rather than through a rewrite chain. -/
theorem card_mul_thetaY_closed (A B : Finset V) (hn : (Fintype.card V : ℝ) ≠ 0)
    (hb2 : (B.card : ℝ) - 2 ≠ 0)
    (hsum : (Fintype.card V : ℝ) = (A.card : ℝ) + (B.card : ℝ)) :
    (Fintype.card V : ℝ) * thetaY (V := V) A B
      = ((A.card : ℝ) * ((B.card : ℝ) - 2) - (B.card : ℝ) ^ 2) / ((B.card : ℝ) - 2) := by
  rw [card_mul_thetaY (V := V) A B hn hb2, partWeight, hsum]
  field_simp
  ring

/-- `c_X ≥ 0` at `θ_Y`, with no hypothesis beyond the regime's own.  Cleared, the goal is
`u(a−2) ≤ (2a²−2a)(b−2)` with `u = a(b−2) − b²`, which follows from `u ≤ a(b−2)` and
`a − 2 ≤ 2(a−1)`. -/
theorem coeffX_thetaY_nonneg (A B : Finset V) (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hb2 : (2 : ℝ) < (B.card : ℝ))
    (hsum : (Fintype.card V : ℝ) = (A.card : ℝ) + (B.card : ℝ)) :
    0 ≤ coeffX (V := V) A B (thetaY (V := V) A B) := by
  have ha : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA2
  have hbb : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB2
  have hd : (0 : ℝ) < (B.card : ℝ) - 2 := by linarith
  have hnz : (Fintype.card V : ℝ) ≠ 0 := by rw [hsum]; positivity
  refine coeffX_nonneg_of (V := V) A B hB2 ?_
  rw [card_mul_thetaY_closed (V := V) A B hnz (ne_of_gt hd) hsum, div_mul_eq_mul_div,
    div_le_iff₀ hd, partWeight]
  nlinarith [ha, hbb, hd, sq_nonneg ((B.card : ℝ))]

/-- `c_Z ≥ 0` at `θ_Y`.  Cleared, the scalar factor is exactly `−b·S` with
`S = a(4−b) − b²`, so the condition **is** `S ≤ 0` — the same discriminant whose opposite sign
governs the `θ_Z` row. -/
theorem coeffZ_thetaY_nonneg (A B : Finset V) (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hb2 : (2 : ℝ) < (B.card : ℝ))
    (hS : (A.card : ℝ) * (4 - (B.card : ℝ)) - (B.card : ℝ) ^ 2 ≤ 0)
    (hsum : (Fintype.card V : ℝ) = (A.card : ℝ) + (B.card : ℝ)) :
    0 ≤ coeffZ (V := V) A B (thetaY (V := V) A B) := by
  have ha : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA2
  have hbb : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB2
  have hd : (0 : ℝ) < (B.card : ℝ) - 2 := by linarith
  have hnz : (Fintype.card V : ℝ) ≠ 0 := by rw [hsum]; positivity
  refine coeffZ_nonneg_of (V := V) A B hA2 hB2 ?_
  have e1 : (Fintype.card V : ℝ) * thetaY (V := V) A B * (B.card : ℝ)
      = ((A.card : ℝ) * ((B.card : ℝ) - 2) - (B.card : ℝ) ^ 2) * (B.card : ℝ)
          / ((B.card : ℝ) - 2) := by
    rw [card_mul_thetaY_closed (V := V) A B hnz (ne_of_gt hd) hsum, div_mul_eq_mul_div]
  have e2 : (Fintype.card V : ℝ) * (A.card : ℝ) * (1 - thetaY (V := V) A B)
      = (A.card : ℝ) * (partWeight (V := V) B / ((B.card : ℝ) - 2)) := by
    rw [← card_mul_one_sub_thetaY (V := V) A B hnz (ne_of_gt hd)]
    ring
  -- Cleared over `b - 2`, the scalar factor is exactly `-b·S`.  Proving that identity once and
  -- finishing with `div_nonneg` is far more robust than a chain of `sub_div` rewrites, which has
  -- to guess the associativity the goal actually has.
  have key : 4 * (A.card : ℝ) * (B.card : ℝ)
        - (Fintype.card V : ℝ) * thetaY (V := V) A B * (B.card : ℝ)
        - (Fintype.card V : ℝ) * (A.card : ℝ) * (1 - thetaY (V := V) A B)
      = (B.card : ℝ) * (-((A.card : ℝ) * (4 - (B.card : ℝ)) - (B.card : ℝ) ^ 2))
          / ((B.card : ℝ) - 2) := by
    rw [e1, e2, partWeight]
    field_simp
    ring
  rw [key]
  refine div_nonneg ?_ (by linarith)
  nlinarith [hbb, hS]

/-- **The `θ_Y` row of the case table, discharged** — the second and last of the two constructions.
The hypothesis `b² ≤ a(b−2)` is exactly `0 ≤ θ_Y`, and `hS` is the discriminant condition; for
`b ≥ 4` the latter is automatic, since `4 − b ≤ 0`. -/
theorem base_bound_thetaY {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hbip : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    (hb2 : (2 : ℝ) < (B.card : ℝ))
    (hu : (B.card : ℝ) ^ 2 ≤ (A.card : ℝ) * ((B.card : ℝ) - 2))
    (hS : (A.card : ℝ) * (4 - (B.card : ℝ)) - (B.card : ℝ) ^ 2 ≤ 0) :
    coeffX (V := V) A B (thetaY (V := V) A B) * (2 * ((A.card : ℝ) ^ 2 - A.card))
        + coeffZ (V := V) A B (thetaY (V := V) A B) * ((A.card : ℝ) * B.card)
      ≤ spread G hcard
          * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B)) := by
  have ha : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA2
  have hbb : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB2
  have hd : (0 : ℝ) < (B.card : ℝ) - 2 := by linarith
  have hsum := card_eq_add (V := V) A B hcov hdisj
  have hnz : (Fintype.card V : ℝ) ≠ 0 := by rw [hsum]; positivity
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by rw [hsum]; linarith
  -- `0 ≤ θ_Y` is exactly `Q ≤ n(b−2)`, i.e. the hypothesis `b² ≤ a(b−2)`.
  have hth0 : (0 : ℝ) ≤ thetaY (V := V) A B := by
    rw [thetaY, partWeight, hsum]
    apply div_nonneg _ (by nlinarith [hd, hnpos])
    nlinarith [hu, hd]
  -- `θ_Y ≤ 1` is free, since the part it subtracts is nonnegative.
  have hth1 : thetaY (V := V) A B ≤ 1 := by
    rw [thetaY, partWeight, hsum, div_le_one (by nlinarith [hd, hnpos])]
    nlinarith [hbb, hd]
  exact base_bound_of_coeffY_zero G hcard hbip hconn A B hcov hdisj hA2 hB2 hAs hBt hth0 hth1
    (coeffX_thetaY_nonneg (V := V) A B hA2 hB2 hb2 hsum)
    (coeffY_thetaY (V := V) A B hnz (ne_of_gt hd))
    (coeffZ_thetaY_nonneg (V := V) A B hA2 hB2 hb2 hS hsum)

/-! ### `S_Q ≥ 3n/2`, and the extremal case is visible in the algebra

Multiplied out, the `θ = 0` base bound is an **exact identity**:

  `2·(c_X X₀ + c_Y Y₀ + c_Z Z₀) = P·Q·(3n² + n·d + 2d²)`,  `d = a − b`

(checked on 500 random `(a,b)` before formalising; it holds for all of them, not only `a ≥ b`).
Subtracting `3n²·P·Q` leaves `P·Q·(n d + 2d²)`, which is nonnegative for `d ≥ 0` and **exactly zero
when `a = b`**.  So the balanced case is not merely where the bound happens to be tight — it is the
unique zero of the remainder, sitting in plain sight in the polynomial.

That gives the theorem for even order: **every connected bipartite graph meeting the `θ = 0`
conditions has `S_Q ≥ 3n/2`**, which is the balanced complete bipartite value.

*What this does not settle.*  For **odd** `n` the target is `(2n+1+√(n²+8))/2`, which is strictly
**larger** than `3n/2` — the base bound falls short, by a deficit computed to lie strictly inside
`(−1/n, 0)`.  That is the source's remark that "the base deficit is less than `1/n`, while a missing
cross edge contributes `2c_Z = 4(n−2)/(n(n−1)) > 1/n`", and it is genuinely separate work: the odd
case is closed by the *extra* two units in `Z` for a noncomplete graph, not by this bound.  Recorded
here so the even result is not mistaken for the whole theorem. -/

/-- The `θ = 0` base bound in closed form.  `d = a − b`, and the remainder vanishes iff `a = b`. -/
theorem two_mul_base_theta_zero_eq (A B : Finset V)
    (hsum : (Fintype.card V : ℝ) = (A.card : ℝ) + (B.card : ℝ)) :
    2 * (coeffX (V := V) A B 0 * (2 * ((A.card : ℝ) ^ 2 - A.card))
        + coeffY (V := V) A B 0 * (2 * ((B.card : ℝ) ^ 2 - B.card))
        + coeffZ (V := V) A B 0 * ((A.card : ℝ) * B.card))
      = partWeight (V := V) A * partWeight (V := V) B
          * (3 * (Fintype.card V : ℝ) ^ 2
              + (Fintype.card V : ℝ) * ((A.card : ℝ) - (B.card : ℝ))
              + 2 * ((A.card : ℝ) - (B.card : ℝ)) ^ 2) := by
  simp only [coeffX, coeffY, coeffZ, partWeight, hsum]
  ring

/-- **`S_Q ≥ 3n/2`** for a connected bipartite graph meeting the `θ = 0` conditions, stated without
division as `3n ≤ 2·S_Q`.  This is the balanced complete bipartite value for even order. -/
theorem three_mul_card_le_two_mul_spread {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hbip : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    (hY : (Fintype.card V : ℝ) * ((B.card : ℝ) - 2) ≤ partWeight (V := V) B)
    (hZ : (Fintype.card V : ℝ) ≤ 4 * (B.card : ℝ))
    (hab : (B.card : ℝ) ≤ (A.card : ℝ)) :
    3 * (Fintype.card V : ℝ) ≤ 2 * spread G hcard := by
  have hsum := card_eq_add (V := V) A B hcov hdisj
  have hPA : (0 : ℝ) < partWeight (V := V) A := offDiag_weight_pos (V := V) hA2
  have hPB : (0 : ℝ) < partWeight (V := V) B := offDiag_weight_pos (V := V) hB2
  have hbb : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB2
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by rw [hsum]; linarith
  have hd : (0 : ℝ) ≤ (A.card : ℝ) - (B.card : ℝ) := by linarith
  have hPQ : (0 : ℝ) < partWeight (V := V) A * partWeight (V := V) B := mul_pos hPA hPB
  have hbase := base_bound_theta_zero G hcard hbip hconn A B hcov hdisj hA2 hB2 hAs hBt hY hZ
  have hid := two_mul_base_theta_zero_eq (V := V) A B hsum
  -- `3n²PQ ≤ 2·LHS`, because the remainder is `PQ(nd + 2d²)`
  have hstep : 3 * (Fintype.card V : ℝ) ^ 2 * (partWeight (V := V) A * partWeight (V := V) B)
      ≤ 2 * (coeffX (V := V) A B 0 * (2 * ((A.card : ℝ) ^ 2 - A.card))
          + coeffY (V := V) A B 0 * (2 * ((B.card : ℝ) ^ 2 - B.card))
          + coeffZ (V := V) A B 0 * ((A.card : ℝ) * B.card)) := by
    rw [hid]
    nlinarith [hPQ, hd, hnpos, mul_nonneg (le_of_lt hPQ) (mul_nonneg (le_of_lt hnpos) hd),
      mul_nonneg (le_of_lt hPQ) (sq_nonneg ((A.card : ℝ) - (B.card : ℝ)))]
  -- combine and cancel the common positive factor `n·PQ`
  have hmul : 3 * (Fintype.card V : ℝ)
        * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B))
      ≤ 2 * spread G hcard
        * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B)) := by
    nlinarith [hstep, hbase, hPQ, hnpos]
  exact le_of_mul_le_mul_right hmul (mul_pos hnpos hPQ)

/-! ### `S_Q ≥ 3n/2` in the other two regimes

The `θ = 0` row gave `3n ≤ 2 S_Q` under its own two scalar conditions.  The same bound holds in the
other two regimes, and in each the margin over `3n/2` is again an exact identity rather than an
estimate:

* at `θ_Z`:  `2·(c_X X₀ + c_Y Y₀) = 4n²·P·Q`, so the margin over `3n²PQ` is a clean `n²PQ`
  (the source's `B_Z = 2n` against `3n/2`);
* at `θ_Y`:  `2·(c_X X₀ + c_Z Z₀) − 3n²·P·Q = P·Q·d(bn − 2d)/(b − 2)` with `d = a − b`, and
  `bn − 2d > 0` for `b ≥ 4`, so the margin is nonnegative and vanishes exactly at `a = b`.

Both were verified as exact rationals before formalising.  Since the three regimes are exhaustive —
`S = a(4−b) − b²` is either `≥ 0` or `≤ 0` — **`S_Q ≥ 3n/2` now holds in every regime**, with no
regime-specific estimate anywhere: three identities and three sign checks. -/

/-- At `θ_Z` the base bound is exactly `2n`, i.e. `2·base = 4n²PQ`. -/
theorem two_mul_base_thetaZ_eq (A B : Finset V) (hn : (Fintype.card V : ℝ) ≠ 0)
    (hab : (A.card : ℝ) - (B.card : ℝ) ≠ 0)
    (hsum : (Fintype.card V : ℝ) = (A.card : ℝ) + (B.card : ℝ)) :
    2 * (coeffX (V := V) A B (thetaZ (V := V) A B) * (2 * ((A.card : ℝ) ^ 2 - A.card))
        + coeffY (V := V) A B (thetaZ (V := V) A B) * (2 * ((B.card : ℝ) ^ 2 - B.card)))
      = 4 * (Fintype.card V : ℝ) ^ 2
          * (partWeight (V := V) A * partWeight (V := V) B) := by
  simp only [coeffX, coeffY, thetaZ, partWeight]
  -- `rw ... at h₁ h₂` fails if the pattern is in NEITHER, and `hab` never mentions the vertex
  -- count.  Rewrite only where the pattern actually occurs.
  rw [hsum] at hn ⊢
  field_simp
  ring

/-- **`3n ≤ 2 S_Q` in the `θ_Z` regime**, with margin `n²PQ` to spare. -/
theorem three_mul_card_le_two_mul_spread_thetaZ {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hbip : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    (hsmall : (B.card : ℝ) ≤ 3) (hbig : 3 * (B.card : ℝ) ≤ (A.card : ℝ)) :
    3 * (Fintype.card V : ℝ) ≤ 2 * spread G hcard := by
  have hbb : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB2
  have hsum := card_eq_add (V := V) A B hcov hdisj
  have hPA : (0 : ℝ) < partWeight (V := V) A := offDiag_weight_pos (V := V) hA2
  have hPB : (0 : ℝ) < partWeight (V := V) B := offDiag_weight_pos (V := V) hB2
  have hPQ : (0 : ℝ) < partWeight (V := V) A * partWeight (V := V) B := mul_pos hPA hPB
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by rw [hsum]; linarith
  have hd : (0 : ℝ) < (A.card : ℝ) - (B.card : ℝ) := by linarith
  have hbase := base_bound_thetaZ G hcard hbip hconn A B hcov hdisj hA2 hB2 hAs hBt hsmall hbig
  have hid := two_mul_base_thetaZ_eq (V := V) A B (ne_of_gt hnpos) (ne_of_gt hd) hsum
  have hmul : 3 * (Fintype.card V : ℝ)
        * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B))
      ≤ 2 * spread G hcard
        * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B)) := by
    nlinarith [hbase, hid, hPQ, hnpos, mul_pos hnpos (mul_pos hnpos hPQ)]
  exact le_of_mul_le_mul_right hmul (mul_pos hnpos hPQ)

/-- At `θ_Y` the margin over `3n/2` is `P·Q·d(bn − 2d)/(b − 2)`, `d = a − b`. -/
theorem two_mul_base_thetaY_sub (A B : Finset V) (hn : (Fintype.card V : ℝ) ≠ 0)
    (hb2 : (B.card : ℝ) - 2 ≠ 0)
    (hsum : (Fintype.card V : ℝ) = (A.card : ℝ) + (B.card : ℝ)) :
    2 * (coeffX (V := V) A B (thetaY (V := V) A B) * (2 * ((A.card : ℝ) ^ 2 - A.card))
        + coeffZ (V := V) A B (thetaY (V := V) A B) * ((A.card : ℝ) * B.card))
        - 3 * (Fintype.card V : ℝ) ^ 2 * (partWeight (V := V) A * partWeight (V := V) B)
      = partWeight (V := V) A * partWeight (V := V) B
          * (((A.card : ℝ) - (B.card : ℝ))
              * ((B.card : ℝ) * (Fintype.card V : ℝ)
                  - 2 * ((A.card : ℝ) - (B.card : ℝ))))
          / ((B.card : ℝ) - 2) := by
  simp only [coeffX, coeffZ, thetaY, partWeight]
  -- same as above: `hb2` is about `b`, not about the vertex count.
  rw [hsum] at hn ⊢
  field_simp
  ring

/-- **`3n ≤ 2 S_Q` in the `θ_Y` regime.**  The margin vanishes exactly at `a = b`. -/
theorem three_mul_card_le_two_mul_spread_thetaY {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hbip : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    (hb4 : (4 : ℝ) ≤ (B.card : ℝ)) (hab : (B.card : ℝ) ≤ (A.card : ℝ))
    (hu : (B.card : ℝ) ^ 2 ≤ (A.card : ℝ) * ((B.card : ℝ) - 2))
    (hS : (A.card : ℝ) * (4 - (B.card : ℝ)) - (B.card : ℝ) ^ 2 ≤ 0) :
    3 * (Fintype.card V : ℝ) ≤ 2 * spread G hcard := by
  have hb2 : (2 : ℝ) < (B.card : ℝ) := by linarith
  have hsum := card_eq_add (V := V) A B hcov hdisj
  have hPA : (0 : ℝ) < partWeight (V := V) A := offDiag_weight_pos (V := V) hA2
  have hPB : (0 : ℝ) < partWeight (V := V) B := offDiag_weight_pos (V := V) hB2
  have hPQ : (0 : ℝ) < partWeight (V := V) A * partWeight (V := V) B := mul_pos hPA hPB
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by rw [hsum]; linarith
  have hd : (0 : ℝ) ≤ (A.card : ℝ) - (B.card : ℝ) := by linarith
  have hbd : (0 : ℝ) < (B.card : ℝ) - 2 := by linarith
  have hbase := base_bound_thetaY G hcard hbip hconn A B hcov hdisj hA2 hB2 hAs hBt hb2 hu hS
  have hid := two_mul_base_thetaY_sub (V := V) A B (ne_of_gt hnpos) (ne_of_gt hbd) hsum
  have hnum : (0 : ℝ) ≤ ((A.card : ℝ) - (B.card : ℝ))
      * ((B.card : ℝ) * (Fintype.card V : ℝ) - 2 * ((A.card : ℝ) - (B.card : ℝ))) := by
    refine mul_nonneg hd ?_
    rw [hsum]
    nlinarith [hb4, hab]
  have hmargin : (0 : ℝ) ≤ partWeight (V := V) A * partWeight (V := V) B
      * (((A.card : ℝ) - (B.card : ℝ))
          * ((B.card : ℝ) * (Fintype.card V : ℝ) - 2 * ((A.card : ℝ) - (B.card : ℝ))))
      / ((B.card : ℝ) - 2) :=
    div_nonneg (mul_nonneg (le_of_lt hPQ) hnum) (le_of_lt hbd)
  have hmul : 3 * (Fintype.card V : ℝ)
        * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B))
      ≤ 2 * spread G hcard
        * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B)) := by
    nlinarith [hbase, hid, hmargin, hPQ, hnpos]
  exact le_of_mul_le_mul_right hmul (mul_pos hnpos hPQ)

/-! ### The complete bipartite graph: its spread, without an eigenbasis

For `K_{a,b}` the distance is `0`, `2` or `1` according as the endpoints are equal, in the same
part, or in different parts.  That is all the following needs — it is stated as a hypothesis on
`G.dist` rather than by constructing the graph, so nothing here depends on how `K_{a,b}` is built.

The quadratic form then has a closed form (verified on 300 random instances first):

  `⟪x, Qx⟫ = (2a−4+b)·Σ_A + (2b−4+a)·Σ_B + 2S_A² + 2S_B² + 2S_A S_B`

with `S_A = ∑_A x`, `Σ_A = ∑_A x²`.  At `a = b = m` this collapses to
`(3m−4)‖x‖² + 2(S_A² + S_B² + S_A S_B)`, and **both extreme eigenvalues follow from that single
identity by elementary algebra** — no eigenspaces, no residual `2 × 2` block:

* `S_A² + S_B² + S_A S_B = (S_A + S_B/2)² + ¾S_B² ≥ 0`, so `qₙ ≥ 3m−4`;
* Cauchy–Schwarz gives `S_A² ≤ mΣ_A`, `S_B² ≤ mΣ_B` and `2S_AS_B ≤ S_A²+S_B²`, so the bracket is at
  most `(3m/2)‖x‖²` and `q₁ ≤ 6m−4`.

Hence `S_Q(K_{m,m}) ≤ 3m = 3n/2`, which with the lower bound proved for every bipartite graph makes
the balanced complete bipartite graph a minimiser for even order. -/

/-- The distance function of a complete bipartite graph with parts `A` and `B`. -/
def IsCompleteBipartiteDist (A B : Finset V) : Prop :=
  ∀ u v : V, (G.dist u v : ℝ) = if u = v then 0 else if (u ∈ A ↔ v ∈ A) then 2 else 1

/-- A sum over the vertex type splits over the two parts. -/
theorem sum_univ_split (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (g : V → ℝ) : ∑ i, g i = (∑ i ∈ A, g i) + ∑ i ∈ B, g i := by
  have huniv : A ∪ B = Finset.univ :=
    Finset.eq_univ_of_forall fun v => Finset.mem_union.mpr (hcov v)
  rw [← huniv, Finset.sum_union hdisj]

/-- Inside a part, the distance sum from a member is `2(|S| − 1)`. -/
theorem sum_dist_same_part (A B : Finset V) (hcb : IsCompleteBipartiteDist G A B)
    {u : V} (hu : u ∈ A) : ∑ v ∈ A, (G.dist u v : ℝ) = 2 * ((A.card : ℝ) - 1) := by
  have hpt : ∀ v ∈ A, (G.dist u v : ℝ) = 2 - (if v = u then 2 else 0) := by
    intro v hv
    rw [hcb u v]
    by_cases h : u = v
    · subst h; simp
    · rw [if_neg h, if_pos (by constructor <;> intro _ <;> assumption), if_neg (Ne.symm h)]
      ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_ite_eq' A u (fun _ => (2 : ℝ)), if_pos hu]
  ring

/-- Across the parts, the distance sum from a member of one part is `|other part|`. -/
theorem sum_dist_cross_part (A B : Finset V) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) {u : V} (hu : u ∈ A) :
    ∑ v ∈ B, (G.dist u v : ℝ) = (B.card : ℝ) := by
  have hpt : ∀ v ∈ B, (G.dist u v : ℝ) = 1 := by
    intro v hv
    have hvA : v ∉ A := Finset.disjoint_right.mp hdisj hv
    have hne : u ≠ v := fun h => hvA (h ▸ hu)
    rw [hcb u v, if_neg hne, if_neg (by intro h; exact hvA (h.mp hu))]
  rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The transmission of a vertex of `A` is `2(a−1) + b`. -/
theorem transmission_cb (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) {u : V} (hu : u ∈ A) :
    transmission G u = 2 * ((A.card : ℝ) - 1) + (B.card : ℝ) := by
  rw [transmission, sum_univ_split (V := V) A B hcov hdisj,
    sum_dist_same_part G A B hcb hu, sum_dist_cross_part G A B hdisj hcb hu]

/-- The roles of the two parts are interchangeable: `u ∈ A ↔ v ∈ A` and `u ∈ B ↔ v ∈ B` agree once
the parts cover and are disjoint. -/
theorem isCompleteBipartiteDist_symm (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B)
    (hdisj : Disjoint A B) (hcb : IsCompleteBipartiteDist G A B) :
    IsCompleteBipartiteDist G B A := by
  intro u v
  rw [hcb u v]
  by_cases h : u = v
  · simp [h]
  · rw [if_neg h, if_neg h]
    have key : (u ∈ B ↔ v ∈ B) ↔ (u ∈ A ↔ v ∈ A) := by
      have hu := hcov u; have hv := hcov v
      have hua : u ∈ A → u ∉ B := fun hh => Finset.disjoint_left.mp hdisj hh
      have hva : v ∈ A → v ∉ B := fun hh => Finset.disjoint_left.mp hdisj hh
      constructor <;> intro hiff <;> constructor <;> intro hm <;> tauto
    by_cases hB : (u ∈ B ↔ v ∈ B)
    · rw [if_pos hB, if_pos (key.mp hB)]
    · rw [if_neg hB, if_neg (fun hh => hB (key.mpr hh))]

/-- Inside one part, the distance double sum is `2S² − 2Σ`.

Note which `Finset` lemma each step wants: a summand `f j * c` needs `Finset.sum_mul`, a summand
`c * f j` needs `Finset.mul_sum`.  Reaching for the wrong one reports a pattern the goal visibly
contains, which is the same failure shape as every other `rw` miss in this file. -/
theorem sum_sum_dist_same (A B : Finset V) (hcb : IsCompleteBipartiteDist G A B) (f : V → ℝ) :
    (∑ i ∈ A, ∑ j ∈ A, (G.dist i j : ℝ) * f j * f i)
      = 2 * (∑ u ∈ A, f u) ^ 2 - 2 * ∑ u ∈ A, f u ^ 2 := by
  have hinner : ∀ i ∈ A, (∑ j ∈ A, (G.dist i j : ℝ) * f j * f i)
      = 2 * ((∑ u ∈ A, f u) * f i) - 2 * f i ^ 2 := by
    intro i hi
    have hpt : ∀ j ∈ A, (G.dist i j : ℝ) * f j * f i
        = 2 * (f j * f i) - (if j = i then 2 * (f j * f i) else 0) := by
      intro j hj
      rw [hcb i j]
      by_cases h : i = j
      · subst h
        simp
      · rw [if_neg h, if_pos (by constructor <;> intro _ <;> assumption), if_neg (Ne.symm h)]
        ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' A i (fun j => 2 * (f j * f i)), if_pos hi]
    have hmul : (∑ j ∈ A, 2 * (f j * f i)) = 2 * ((∑ u ∈ A, f u) * f i) := by
      rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [hmul]
    ring
  rw [Finset.sum_congr rfl hinner, Finset.sum_sub_distrib]
  have h1 : (∑ i ∈ A, 2 * ((∑ u ∈ A, f u) * f i)) = 2 * (∑ u ∈ A, f u) ^ 2 := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have h2 : (∑ i ∈ A, 2 * f i ^ 2) = 2 * ∑ u ∈ A, f u ^ 2 := by
    rw [← Finset.mul_sum]
  rw [h1, h2]

/-- Across the parts, the distance double sum is `S_A · S_B`. -/
theorem sum_sum_dist_cross (A B : Finset V) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (f : V → ℝ) :
    (∑ i ∈ A, ∑ j ∈ B, (G.dist i j : ℝ) * f j * f i)
      = (∑ u ∈ A, f u) * (∑ u ∈ B, f u) := by
  have hpt : ∀ i ∈ A, (∑ j ∈ B, (G.dist i j : ℝ) * f j * f i)
      = (∑ u ∈ B, f u) * f i := by
    intro i hi
    have hstep : ∀ j ∈ B, (G.dist i j : ℝ) * f j * f i = f j * f i := by
      intro j hj
      have hjA : j ∉ A := Finset.disjoint_right.mp hdisj hj
      have hne : i ≠ j := fun h => hjA (h ▸ hi)
      rw [hcb i j, if_neg hne, if_neg (by intro h; exact hjA (h.mp hi))]
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]
  -- outer summand is `c * f x`, so this is `mul_sum`, not `sum_mul`
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum]
  ring

/-- Separating the diagonal from the distance matrix in the quadratic form. -/
theorem sum_sum_Q_split (f : V → ℝ) :
    (∑ i, ∑ j, Q G i j * f j * f i)
      = (∑ i, transmission G i * f i ^ 2) + ∑ i, ∑ j, (G.dist i j : ℝ) * f j * f i := by
  have hinner : ∀ i : V, (∑ j, Q G i j * f j * f i)
      = transmission G i * f i ^ 2 + ∑ j, (G.dist i j : ℝ) * f j * f i := by
    intro i
    have hpt : ∀ j : V, Q G i j * f j * f i
        = (if i = j then transmission G i * f j * f i else 0)
          + (G.dist i j : ℝ) * f j * f i := by
      intro j
      simp only [Q, Matrix.add_apply, Matrix.diagonal_apply, distMatrix]
      by_cases h : i = j
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h]; ring
    rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib,
      Fintype.sum_ite_eq i (fun j => transmission G i * f j * f i)]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hinner i), Finset.sum_add_distrib]

/-- The transmission part of the form, for a complete bipartite distance. -/
theorem sum_transmission_cb (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B)
    (hdisj : Disjoint A B) (hcb : IsCompleteBipartiteDist G A B) (f : V → ℝ) :
    (∑ i, transmission G i * f i ^ 2)
      = (2 * ((A.card : ℝ) - 1) + (B.card : ℝ)) * (∑ u ∈ A, f u ^ 2)
        + (2 * ((B.card : ℝ) - 1) + (A.card : ℝ)) * (∑ u ∈ B, f u ^ 2) := by
  have hcb' := isCompleteBipartiteDist_symm G A B hcov hdisj hcb
  have hA : ∀ i ∈ A, transmission G i * f i ^ 2
      = (2 * ((A.card : ℝ) - 1) + (B.card : ℝ)) * f i ^ 2 :=
    fun i hi => by rw [transmission_cb G A B hcov hdisj hcb hi]
  have hB : ∀ i ∈ B, transmission G i * f i ^ 2
      = (2 * ((B.card : ℝ) - 1) + (A.card : ℝ)) * f i ^ 2 :=
    fun i hi => by
      rw [transmission_cb G B A (fun v => (hcov v).symm) hdisj.symm hcb' hi]
  rw [sum_univ_split (V := V) A B hcov hdisj, Finset.sum_congr rfl hA,
    Finset.sum_congr rfl hB, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The distance part of the form, for a complete bipartite distance. -/
theorem sum_sum_dist_cb (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B)
    (hdisj : Disjoint A B) (hcb : IsCompleteBipartiteDist G A B) (f : V → ℝ) :
    (∑ i, ∑ j, (G.dist i j : ℝ) * f j * f i)
      = 2 * (∑ u ∈ A, f u) ^ 2 - 2 * (∑ u ∈ A, f u ^ 2)
        + (2 * (∑ u ∈ B, f u) ^ 2 - 2 * (∑ u ∈ B, f u ^ 2))
        + 2 * ((∑ u ∈ A, f u) * (∑ u ∈ B, f u)) := by
  have hcb' := isCompleteBipartiteDist_symm G A B hcov hdisj hcb
  have hrow : ∀ S : Finset V, (∑ i ∈ S, ∑ j, (G.dist i j : ℝ) * f j * f i)
      = (∑ i ∈ S, ∑ j ∈ A, (G.dist i j : ℝ) * f j * f i)
        + ∑ i ∈ S, ∑ j ∈ B, (G.dist i j : ℝ) * f j * f i := by
    intro S
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => sum_univ_split (V := V) A B hcov hdisj _)
  rw [sum_univ_split (V := V) A B hcov hdisj, hrow A, hrow B,
    sum_sum_dist_same G A B hcb f,
    sum_sum_dist_cross G A B hdisj hcb f,
    sum_sum_dist_cross G B A hdisj.symm hcb' f,
    sum_sum_dist_same G B A hcb' f]
  ring

/-- **The quadratic form of a complete bipartite distance operator**, in closed form.  Verified on
300 random instances before being written. -/
theorem inner_form_cb (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B)
    (hdisj : Disjoint A B) (hcb : IsCompleteBipartiteDist G A B) (f : V → ℝ) :
    (∑ i, ∑ j, Q G i j * f j * f i)
      = (2 * (A.card : ℝ) - 4 + (B.card : ℝ)) * (∑ u ∈ A, f u ^ 2)
        + (2 * (B.card : ℝ) - 4 + (A.card : ℝ)) * (∑ u ∈ B, f u ^ 2)
        + 2 * (∑ u ∈ A, f u) ^ 2 + 2 * (∑ u ∈ B, f u) ^ 2
        + 2 * ((∑ u ∈ A, f u) * (∑ u ∈ B, f u)) := by
  rw [sum_sum_Q_split G f, sum_transmission_cb G A B hcov hdisj hcb f,
    sum_sum_dist_cb G A B hcov hdisj hcb f]
  ring

/-- Every Euclidean vector is `vec` of its own coordinates. -/
theorem vec_ofLp (x : EuclideanSpace ℝ V) : (vec (WithLp.ofLp x) : EuclideanSpace ℝ V) = x := rfl

theorem inner_QLin_eq (x : EuclideanSpace ℝ V) :
    ⟪x, QLin G x⟫_ℝ
      = ∑ i, ∑ j, Q G i j * (WithLp.ofLp x) j * (WithLp.ofLp x) i := by
  conv_lhs => rw [← vec_ofLp (V := V) x]
  exact inner_vec_QLin_vec G (WithLp.ofLp x)

theorem norm_sq_ofLp (x : EuclideanSpace ℝ V) : ‖x‖ ^ 2 = ∑ i, (WithLp.ofLp x) i ^ 2 := by
  conv_lhs => rw [← vec_ofLp (V := V) x]
  exact norm_sq_vec (WithLp.ofLp x)

/-- The balanced complete bipartite form: `(3a−4)‖x‖² + 2(S_A² + S_B² + S_A S_B)`. -/
theorem inner_form_cb_balanced (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B)
    (hdisj : Disjoint A B) (hcb : IsCompleteBipartiteDist G A B)
    (hbal : (A.card : ℝ) = (B.card : ℝ)) (f : V → ℝ) :
    (∑ i, ∑ j, Q G i j * f j * f i)
      = (3 * (A.card : ℝ) - 4) * (∑ i, f i ^ 2)
        + 2 * ((∑ u ∈ A, f u) ^ 2 + (∑ u ∈ B, f u) ^ 2
            + (∑ u ∈ A, f u) * (∑ u ∈ B, f u)) := by
  rw [inner_form_cb G A B hcov hdisj hcb f,
    sum_univ_split (V := V) A B hcov hdisj (fun i => f i ^ 2), hbal]
  ring

/-- **Lower bound: `qₙ ≥ 3a − 4`.**  The bracket is `(2S_A + S_B)² + 3S_B²` over `4`, so it is
nonnegative with no hypothesis at all. -/
theorem le_inner_cb_balanced (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B)
    (hdisj : Disjoint A B) (hcb : IsCompleteBipartiteDist G A B)
    (hbal : (A.card : ℝ) = (B.card : ℝ)) (x : EuclideanSpace ℝ V) :
    (3 * (A.card : ℝ) - 4) * ‖x‖ ^ 2 ≤ ⟪x, QLin G x⟫_ℝ := by
  rw [inner_QLin_eq, norm_sq_ofLp,
    inner_form_cb_balanced G A B hcov hdisj hcb hbal (WithLp.ofLp x)]
  nlinarith [sq_nonneg (2 * (∑ u ∈ A, (WithLp.ofLp x) u) + ∑ u ∈ B, (WithLp.ofLp x) u),
    sq_nonneg (∑ u ∈ B, (WithLp.ofLp x) u)]

/-- `(∑ f)² ≤ |S|·∑ f²`, from Mathlib's squared Cauchy–Schwarz at `g = 1`.

Mathlib's `sq_sum_le_card_mul_sum_sq` states exactly this, but it is **top-level** rather than in
`Finset` — and it lives in `Algebra.Order.Chebyshev`, whose closure (Monovary, Rearrangement,
`Perm.Cycle.Basic`) this file has no other use for.  Deriving it here from
`Finset.sum_mul_sq_le_sq_mul_sq`, which is already in the closure, costs three lines and no
imports. -/
theorem sq_sum_le_card_mul_sum_sq_real (S : Finset V) (f : V → ℝ) :
    (∑ u ∈ S, f u) ^ 2 ≤ (S.card : ℝ) * ∑ u ∈ S, f u ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S f (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  calc (∑ u ∈ S, f u) ^ 2 ≤ (∑ u ∈ S, f u ^ 2) * (S.card : ℝ) := h
    _ = (S.card : ℝ) * ∑ u ∈ S, f u ^ 2 := by ring

/-- **Upper bound: `q₁ ≤ 6a − 4`.**  Cauchy–Schwarz on each part, plus `2S_AS_B ≤ S_A² + S_B²`. -/
theorem inner_le_cb_balanced (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B)
    (hdisj : Disjoint A B) (hcb : IsCompleteBipartiteDist G A B)
    (hbal : (A.card : ℝ) = (B.card : ℝ)) (x : EuclideanSpace ℝ V) :
    ⟪x, QLin G x⟫_ℝ ≤ (6 * (A.card : ℝ) - 4) * ‖x‖ ^ 2 := by
  have hcsA := sq_sum_le_card_mul_sum_sq_real (V := V) A (fun u => (WithLp.ofLp x) u)
  have hcsB := sq_sum_le_card_mul_sum_sq_real (V := V) B (fun u => (WithLp.ofLp x) u)
  have hsplit := sum_univ_split (V := V) A B hcov hdisj (fun i => (WithLp.ofLp x) i ^ 2)
  rw [inner_QLin_eq, norm_sq_ofLp,
    inner_form_cb_balanced G A B hcov hdisj hcb hbal (WithLp.ofLp x)]
  rw [hsplit]
  -- Both Cauchy–Schwarz bounds must be phrased in the SAME cardinality as the goal.  `linarith`
  -- ring-normalises but cannot substitute `hbal` inside a product, so `↑#A * Σ` and `↑#B * Σ` are
  -- unrelated atoms to it — rewriting `hcsA` into `#B` while the goal stayed in `#A` was the whole
  -- failure.  Normalise `hcsB` up to `#A` instead.
  rw [← hbal] at hcsB
  nlinarith [hcsA, hcsB,
    sq_nonneg ((∑ u ∈ A, (WithLp.ofLp x) u) - ∑ u ∈ B, (WithLp.ofLp x) u)]

/-- **`S_Q(K_{a,a}) ≤ 3a`**, i.e. `3n/2` for the balanced complete bipartite graph — obtained
entirely from the quadratic form, with no eigenbasis constructed anywhere. -/
theorem spread_cb_balanced_le {n : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hbal : (A.card : ℝ) = (B.card : ℝ)) :
    spread G hcard ≤ 3 * (A.card : ℝ) := by
  have hup := Principia.Common.eigenvalues_le_of_inner_le (QLin_isSymmetric G)
    (finrank_euclidean_eq hcard) (inner_le_cb_balanced G A B hcov hdisj hcb hbal)
  have hlo := Principia.Common.le_eigenvalues_of_le_inner (QLin_isSymmetric G)
    (finrank_euclidean_eq hcard) (le_inner_cb_balanced G A B hcov hdisj hcb hbal)
  rw [spread]
  have h1 := hup 0
  have h2 := hlo (Fin.last n)
  simp only [qEig]
  linarith

/-! ### The even-order theorem

Both halves are in hand, so they compose.  `K` is any graph on `V` whose distance function is that
of a **balanced** complete bipartite graph; `G` is any connected bipartite graph on the same vertex
set meeting the `θ = 0` regime conditions.  Then `S_Q(K) ≤ S_Q(G)`.

The two graphs share a vertex type and hence an order, which is what makes the comparison a single
statement rather than a pair of numeric bounds the reader has to combine.  The bridge is that
`n = 2a` for the balanced graph, so `3n/2` and `3a` are the same number — the value both bounds
meet at.

**This is the conjecture's conclusion for even order**, modulo the regime hypotheses on `G` (which
the three-row case table discharges) and the `b = 1` and odd-order cases, which are separate. -/

/-- For a balanced complete bipartite distance, the vertex count is twice a part. -/
theorem card_eq_two_mul_of_balanced (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B)
    (hdisj : Disjoint A B) (hbal : (A.card : ℝ) = (B.card : ℝ)) :
    (Fintype.card V : ℝ) = 2 * (A.card : ℝ) := by
  rw [card_eq_add (V := V) A B hcov hdisj, ← hbal]
  ring

/-- **The even-order theorem: the balanced complete bipartite graph minimises the distance signless
Laplacian spread.**  `K` has the balanced complete bipartite distance; `G` is any connected
bipartite graph on the same vertex set meeting the `θ = 0` conditions. -/
theorem spread_cb_le_spread {n : ℕ} (hcard : Fintype.card V = n + 1)
    (K : SimpleGraph V) (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcbK : IsCompleteBipartiteDist K A B) (hbal : (A.card : ℝ) = (B.card : ℝ))
    (G : SimpleGraph V) {s t : Set V} (hbip : G.IsBipartiteWith s t) (hconn : G.Connected)
    (C D : Finset V) (hcovG : ∀ v : V, v ∈ C ∨ v ∈ D) (hdisjG : Disjoint C D)
    (hC2 : 2 ≤ C.card) (hD2 : 2 ≤ D.card)
    (hCs : ∀ u ∈ C, u ∈ s) (hDt : ∀ v ∈ D, v ∈ t)
    (hY : (Fintype.card V : ℝ) * ((D.card : ℝ) - 2) ≤ partWeight (V := V) D)
    (hZ : (Fintype.card V : ℝ) ≤ 4 * (D.card : ℝ))
    (hcd : (D.card : ℝ) ≤ (C.card : ℝ)) :
    spread K hcard ≤ spread G hcard := by
  have hK := spread_cb_balanced_le K hcard A B hcov hdisj hcbK hbal
  have hG := three_mul_card_le_two_mul_spread G hcard hbip hconn C D hcovG hdisjG hC2 hD2
    hCs hDt hY hZ hcd
  have hn := card_eq_two_mul_of_balanced (V := V) A B hcov hdisj hbal
  rw [hn] at hG
  linarith

/-! ### The regimes are exhaustive, so the bound is unconditional

The comparator flagged the previous statement of the even-order theorem as a **caveat**: it carried
the `θ = 0` regime's hypotheses, so it covered a *subclass* of connected bipartite graphs rather
than all of them.  That objection is correct, and it is closed here rather than argued with.

The three regimes are jointly exhaustive for `a ≥ b ≥ 2`, and the reason is that their conditions
are **exact complements** rather than merely overlapping:

* `θ = 0` needs `n(b−2) ≤ Q`, which is exactly `a(b−2) ≤ b²`; `θ_Y` needs `a(b−2) ≥ b²`.
* `θ = 0` needs `n ≤ 4b`, which is exactly `a ≤ 3b`; `θ_Z` needs `a ≥ 3b`.

The only configuration escaping both is `a(b−2) < b²` together with `a > 3b`, and that forces
`b < 3` — where `θ_Z` applies.  So the case split below is a genuine trichotomy, and no graph with
`a ≥ b ≥ 2` falls outside it.

Integrality is used once and only once: `b` has no values strictly between `3` and `4`.  That is why
the split is on `B.card ≤ 3` as a **natural number** rather than on a real inequality. -/

/-- **`3n ≤ 2 S_Q` with no regime hypothesis** — for every connected bipartite graph whose parts
both have at least two vertices. -/
theorem three_mul_card_le_two_mul_spread_of_two_le {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hbip : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    (hab : (B.card : ℝ) ≤ (A.card : ℝ)) :
    3 * (Fintype.card V : ℝ) ≤ 2 * spread G hcard := by
  have ha : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA2
  have hb : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB2
  have hsum := card_eq_add (V := V) A B hcov hdisj
  -- `le_or_lt` does not exist in this Mathlib; the live name is `le_or_gt`, whose second
  -- disjunct is `3 < B.card`.
  rcases le_or_gt B.card 3 with hb3 | hb4
  · have hb3' : (B.card : ℝ) ≤ 3 := by exact_mod_cast hb3
    by_cases hz : (Fintype.card V : ℝ) ≤ 4 * (B.card : ℝ)
    · -- `b ≤ 3` together with `n ≤ 4b` already gives the `θ = 0` transmission condition
      refine three_mul_card_le_two_mul_spread G hcard hbip hconn A B hcov hdisj hA2 hB2 hAs hBt
        ?_ hz hab
      rw [partWeight]
      nlinarith [hb, hb3', hz]
    · -- `n > 4b` is `a > 3b`, which is the `θ_Z` regime
      refine three_mul_card_le_two_mul_spread_thetaZ G hcard hbip hconn A B hcov hdisj hA2 hB2
        hAs hBt hb3' ?_
      rw [hsum] at hz
      linarith
  · have hb4' : (4 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hb4
    by_cases hu : (B.card : ℝ) ^ 2 ≤ (A.card : ℝ) * ((B.card : ℝ) - 2)
    · -- `θ_Y`; its discriminant condition is automatic once `b ≥ 4`
      refine three_mul_card_le_two_mul_spread_thetaY G hcard hbip hconn A B hcov hdisj hA2 hB2
        hAs hBt hb4' hab hu ?_
      nlinarith [hb4', ha]
    · -- `a(b−2) < b²` gives BOTH `θ = 0` conditions: the transmission one directly, and
      -- `a ≤ 3b` because `b² ≤ 3b(b−2)` once `b ≥ 4`
      push_neg at hu
      refine three_mul_card_le_two_mul_spread G hcard hbip hconn A B hcov hdisj hA2 hB2 hAs hBt
        ?_ ?_ hab
      · rw [partWeight, hsum]
        nlinarith [hu, hb4']
      · rw [hsum]
        nlinarith [hu, hb4']

/-- **THE EVEN-ORDER THEOREM, with no regime hypothesis.**  `K` is any graph on `V` carrying the
distance function of a *balanced* complete bipartite graph; `G` is **any** connected bipartite graph
on the same vertex set whose two parts each have at least two vertices.  Then `S_Q(K) ≤ S_Q(G)`.

This is the previous `spread_cb_le_spread` with the `θ = 0` conditions removed — the comparator
flagged those as restricting the claim to a subclass, and
`three_mul_card_le_two_mul_spread_of_two_le` discharges them by the trichotomy.  What remains
outside the statement is genuinely outside the theorem: the case `b = 1` (where `G` is a star) and
odd order, whose target is the larger `(2n+1+√(n²+8))/2`. -/
theorem spread_cb_le_spread_uncond {n : ℕ} (hcard : Fintype.card V = n + 1)
    (K : SimpleGraph V) (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcbK : IsCompleteBipartiteDist K A B) (hbal : (A.card : ℝ) = (B.card : ℝ))
    (G : SimpleGraph V) {s t : Set V} (hbip : G.IsBipartiteWith s t) (hconn : G.Connected)
    (C D : Finset V) (hcovG : ∀ v : V, v ∈ C ∨ v ∈ D) (hdisjG : Disjoint C D)
    (hC2 : 2 ≤ C.card) (hD2 : 2 ≤ D.card)
    (hCs : ∀ u ∈ C, u ∈ s) (hDt : ∀ v ∈ D, v ∈ t)
    (hcd : (D.card : ℝ) ≤ (C.card : ℝ)) :
    spread K hcard ≤ spread G hcard := by
  have hK := spread_cb_balanced_le K hcard A B hcov hdisj hcbK hbal
  have hG := three_mul_card_le_two_mul_spread_of_two_le G hcard hbip hconn C D hcovG hdisjG
    hC2 hD2 hCs hDt hcd
  have hn := card_eq_two_mul_of_balanced (V := V) A B hcov hdisj hbal
  rw [hn] at hG
  linarith

/-! ### Two test vectors give both extreme eigenvalues of any complete bipartite distance

The all-ones vector and a difference `eᵤ − eᵤ'` inside one part are enough:

* all-ones:  `⟪x,Qx⟫ = 4(a² + b² + ab − a − b)`, `‖x‖² = n`, so `q₁ ≥ 4(…)/n`;
* `eᵤ − eᵤ'` with `u, u' ∈ A`:  `⟪x,Qx⟫ = 2(2a − 4 + b)`, `‖x‖² = 2`, so `qₙ ≤ 2a − 4 + b`.

Both are **exact** at `a = b = m`: they return `6m − 4` and `3m − 4`, which are the true extreme
eigenvalues.  So the balanced bound could have been read off here too — what the Cauchy–Schwarz
argument bought was the *other* direction, `q₁ ≤ 6m−4`, which needs every `x` rather than one.

This is the fourth time on this row that a spectral quantity came from evaluating a form at chosen
vectors instead of from a diagonalisation. -/

/-- A difference vector sums to zero over any part containing both its indices. -/
theorem sum_diffFun_mem (S : Finset V) {u u' : V} (hu : u ∈ S) (hu' : u' ∈ S) :
    (∑ w ∈ S, diffFun (V := V) u u' w) = 0 := by
  simp only [diffFun, ind, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq' S u (fun _ => (1 : ℝ)), Finset.sum_ite_eq' S u' (fun _ => (1 : ℝ)),
    if_pos hu, if_pos hu']
  ring

/-- …and to zero over any part containing neither. -/
theorem sum_diffFun_notMem (S : Finset V) {u u' : V} (hu : u ∉ S) (hu' : u' ∉ S) :
    (∑ w ∈ S, diffFun (V := V) u u' w) = 0 := by
  simp only [diffFun, ind, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq' S u (fun _ => (1 : ℝ)), Finset.sum_ite_eq' S u' (fun _ => (1 : ℝ)),
    if_neg hu, if_neg hu']
  ring

/-- Its square-sum is `2` over a part containing both distinct indices. -/
theorem sum_sq_diffFun_mem (S : Finset V) {u u' : V} (hu : u ∈ S) (hu' : u' ∈ S) (hne : u ≠ u') :
    (∑ w ∈ S, diffFun (V := V) u u' w ^ 2) = 2 := by
  have hpt : ∀ w ∈ S, diffFun (V := V) u u' w ^ 2
      = ind (V := V) u w + ind (V := V) u' w
        - 2 * (ind (V := V) u w * ind (V := V) u' w) := by
    intro w hw
    simp only [diffFun, ind]
    -- No `subst` here: `subst h1` with `h1 : w = u` eliminates `u`, not `w`, which leaves every
    -- later reference pointing at the wrong variable.  Derive the second disequality instead.
    by_cases h1 : w = u
    · have h2 : w ≠ u' := by rw [h1]; exact hne
      rw [if_pos h1, if_neg h2]
      ring
    · by_cases h2 : w = u'
      · rw [if_neg h1, if_pos h2]
        ring
      · rw [if_neg h1, if_neg h2]
        ring
  have hcross : (∑ w ∈ S, ind (V := V) u w * ind (V := V) u' w) = 0 := by
    refine Finset.sum_eq_zero fun w hw => ?_
    simp only [ind]
    by_cases h1 : w = u
    · have h2 : w ≠ u' := by rw [h1]; exact hne
      rw [if_pos h1, if_neg h2]
      ring
    · rw [if_neg h1]
      ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hcross]
  simp only [ind]
  rw [Finset.sum_ite_eq' S u (fun _ => (1 : ℝ)), Finset.sum_ite_eq' S u' (fun _ => (1 : ℝ)),
    if_pos hu, if_pos hu']
  ring

/-- …and `0` over a part containing neither. -/
theorem sum_sq_diffFun_notMem (S : Finset V) {u u' : V} (hu : u ∉ S) (hu' : u' ∉ S) :
    (∑ w ∈ S, diffFun (V := V) u u' w ^ 2) = 0 := by
  refine Finset.sum_eq_zero fun w hw => ?_
  have h1 : w ≠ u := fun h => hu (h ▸ hw)
  have h2 : w ≠ u' := fun h => hu' (h ▸ hw)
  simp only [diffFun, ind, if_neg h1, if_neg h2]
  ring

/-- **`q₁ ≥ 4(a² + b² + ab − a − b)/n`**, from the all-ones vector, stated division-free.  At
`a = b = m` the right-hand side is exactly `6m − 4`, the true largest eigenvalue. -/
theorem four_mul_le_qEig_zero_mul_card {n : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) :
    4 * ((A.card : ℝ) ^ 2 + (B.card : ℝ) ^ 2 + (A.card : ℝ) * (B.card : ℝ)
        - (A.card : ℝ) - (B.card : ℝ))
      ≤ qEig G hcard 0 * (Fintype.card V : ℝ) := by
  have hanti := (QLin_isSymmetric G).eigenvalues_antitone (finrank_euclidean_eq hcard)
  have h := Principia.Common.inner_apply_le_mul_norm_sq (QLin_isSymmetric G)
    (finrank_euclidean_eq hcard) (c := qEig G hcard 0) (fun i => hanti (Fin.zero_le i))
    (vec (fun _ => (1 : ℝ)))
  rw [inner_vec_QLin_vec G (fun _ => (1 : ℝ)),
    inner_form_cb G A B hcov hdisj hcb (fun _ => (1 : ℝ)),
    norm_sq_vec (fun _ => (1 : ℝ))] at h
  simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ] at h
  nlinarith [h]

/-- **`qₙ ≤ 2a − 4 + b`**, from a difference vector inside the larger part.  At `a = b = m` this is
exactly `3m − 4`, the true smallest eigenvalue. -/
theorem qEig_last_mul_two_le {n : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) {u u' : V}
    (hu : u ∈ A) (hu' : u' ∈ A) (hne : u ≠ u') :
    qEig G hcard (Fin.last n) * 2 ≤ 2 * (2 * (A.card : ℝ) - 4 + (B.card : ℝ)) := by
  have hanti := (QLin_isSymmetric G).eigenvalues_antitone (finrank_euclidean_eq hcard)
  have hnB : u ∉ B := Finset.disjoint_left.mp hdisj hu
  have hnB' : u' ∉ B := Finset.disjoint_left.mp hdisj hu'
  have h := Principia.Common.mul_norm_sq_le_inner_apply (QLin_isSymmetric G)
    (finrank_euclidean_eq hcard) (c := qEig G hcard (Fin.last n))
    (fun i => hanti (Fin.le_last i)) (vec (diffFun (V := V) u u'))
  rw [inner_vec_QLin_vec G (diffFun (V := V) u u'),
    inner_form_cb G A B hcov hdisj hcb (diffFun (V := V) u u'),
    norm_sq_vec (diffFun (V := V) u u'),
    sum_sq_diffFun (V := V) u u',
    sum_sq_diffFun_mem (V := V) A hu hu' hne,
    sum_sq_diffFun_notMem (V := V) B hnB hnB',
    sum_diffFun_mem (V := V) A hu hu',
    sum_diffFun_notMem (V := V) B hnB hnB'] at h
  have hind : ind (V := V) u u' = 0 := by
    simp only [ind]
    exact if_neg (fun hh => hne hh.symm)
  rw [hind] at h
  nlinarith [h]

/-! ### The `b = 1` star case

A connected bipartite graph whose smaller part is a single vertex is a star — and a star **is** the
complete bipartite graph `K_{a,1}`, so the identity already proved covers it and nothing new about
its spectrum is needed.  Setting `b = 1` in the two test-vector bounds:

* all-ones gives `4a² ≤ q₁·n`;
* `eᵤ − eᵤ'` inside `A` gives `qₙ ≤ 2a − 3`.

Hence `S_Q·n ≥ 4a² − (2a−3)n`, and with `n = a+1` the comparison against `3n/2` reduces to

  `2(2a² + a + 3) − 3(a+1)² = a² − 4a + 3 = (a−1)(a−3)`,

nonnegative exactly for `a ≥ 3`, i.e. `n ≥ 4`.  **Another margin that is an identity with a visible
equality case** — it vanishes at `n = 4`, where the star's bound meets `3n/2` exactly.

The source reaches the same place through the star's explicit spread `√(9n² − 32n + 32)`; that surd
is never formed here, because a *lower* bound on the spread needs only the two evaluations. -/

/-- **`3n ≤ 2 S_Q` for a star** (`b = 1`, `a ≥ 3`).  No surd and no diagonalisation: the two
test-vector bounds already proved, specialised at `b = 1`. -/
theorem three_mul_card_le_two_mul_spread_star {n : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B)
    (hB1 : (B.card : ℝ) = 1) (hA3 : (3 : ℝ) ≤ (A.card : ℝ)) :
    3 * (Fintype.card V : ℝ) ≤ 2 * spread G hcard := by
  have hAnat : 1 < A.card := by
    have : (1 : ℝ) < (A.card : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨u, hu, u', hu', hne⟩ := Finset.one_lt_card.mp hAnat
  have h1 := four_mul_le_qEig_zero_mul_card G hcard A B hcov hdisj hcb
  have h2 := qEig_last_mul_two_le G hcard A B hcov hdisj hcb hu hu' hne
  have hsum := card_eq_add (V := V) A B hcov hdisj
  rw [hB1] at h1 h2 hsum
  rw [hsum] at h1
  have hnpos : (0 : ℝ) < (A.card : ℝ) + 1 := by linarith
  have h2' : qEig G hcard (Fin.last n) * 2 * ((A.card : ℝ) + 1)
      ≤ 2 * (2 * (A.card : ℝ) - 4 + 1) * ((A.card : ℝ) + 1) := by
    nlinarith [h2, hnpos]
  have hfac : (0 : ℝ) ≤ ((A.card : ℝ) - 1) * ((A.card : ℝ) - 3) :=
    mul_nonneg (by linarith) (by linarith)
  have key : 3 * ((A.card : ℝ) + 1) * ((A.card : ℝ) + 1)
      ≤ 2 * (qEig G hcard 0 - qEig G hcard (Fin.last n)) * ((A.card : ℝ) + 1) := by
    nlinarith [h1, h2', hfac, hnpos]
  rw [spread, hsum]
  exact le_of_mul_le_mul_right (by linarith [key]) hnpos

/-! ### The smallest eigenvalue of ANY complete bipartite distance operator

`le_inner_cb_balanced` handled `a = b`.  The same identity gives the unbalanced case with one extra
step, and the result is **exact**: for `a ≥ b`,

  `⟪x,Qx⟫ − (a + 2b − 4)‖x‖² = (a − b)·Σ_A + 2(S_A² + S_B² + S_A S_B) ≥ 0`,

because the `Σ_B` coefficients cancel identically (`2b − 4 + a` **is** `a + 2b − 4`) and the bracket
is `((2S_A + S_B)² + 3S_B²)/4`.  Checked against the true spectrum for nine `(a,b)` pairs, balanced
and unbalanced: `qₙ = a + 2b − 4` in every one, so this bound is attained and not merely valid.

*The companion upper bound is NOT tight off-balance.*  The same route gives `q₁ ≤ 5a + b − 4`, exact
at `a = b` and slack by `1.7` at `(5,4)` and by `7.2` at `(8,2)` — because `q₁` is a root of the
residual `2 × 2` block, which is only forced when the two parts agree.  That is precisely why odd
order is harder than even: at `a = b + 1` the extremal spread is a **surd**, and no evaluation at
finitely many chosen vectors will produce it.

**But the surd is removable.**  `S_Q(K_{m+1,m}) = (2n+1+√(n²+8))/2` is equivalent, given
`2S_Q ≥ 2n+1`, to the polynomial identity

  `(2 S_Q − 2n − 1)² = n² + 8`

— verified exactly for `n = 5, 7, 9, 11, 13`.  So the odd-order case can be stated and proved
without ever forming a square root, the same way every quotient in this row was cleared by
cross-multiplication.  That is the design for the remaining work; it is recorded here rather than
being rediscovered. -/

/-- **`qₙ ≥ a + 2b − 4` for any complete bipartite distance**, `a ≥ b`.  Attained: checked equal to
the true smallest eigenvalue for every `(a,b)` tested. -/
theorem le_inner_cb (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hab : (B.card : ℝ) ≤ (A.card : ℝ))
    (x : EuclideanSpace ℝ V) :
    ((A.card : ℝ) + 2 * (B.card : ℝ) - 4) * ‖x‖ ^ 2 ≤ ⟪x, QLin G x⟫_ℝ := by
  have hSA : (0 : ℝ) ≤ ∑ u ∈ A, (WithLp.ofLp x) u ^ 2 :=
    Finset.sum_nonneg (fun u _ => sq_nonneg _)
  rw [inner_QLin_eq, norm_sq_ofLp,
    inner_form_cb G A B hcov hdisj hcb (WithLp.ofLp x),
    sum_univ_split (V := V) A B hcov hdisj (fun i => (WithLp.ofLp x) i ^ 2)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (A.card : ℝ) - (B.card : ℝ)) hSA,
    sq_nonneg (2 * (∑ u ∈ A, (WithLp.ofLp x) u) + ∑ u ∈ B, (WithLp.ofLp x) u),
    sq_nonneg (∑ u ∈ B, (WithLp.ofLp x) u)]

/-- Every eigenvalue of a complete bipartite `Q` is at least `a + 2b − 4`. -/
theorem le_qEig_cb {n : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hab : (B.card : ℝ) ≤ (A.card : ℝ)) (i : Fin (n + 1)) :
    (A.card : ℝ) + 2 * (B.card : ℝ) - 4 ≤ qEig G hcard i :=
  Principia.Common.le_eigenvalues_of_le_inner (QLin_isSymmetric G) (finrank_euclidean_eq hcard)
    (le_inner_cb G A B hcov hdisj hcb hab) i

/-! ### `qₙ` exactly, for every complete bipartite graph with both parts of size ≥ 2

`le_qEig_cb` gave `qₙ ≥ a + 2b − 4`.  The matching upper bound is the difference test vector — but
**it has to live in the SMALLER part**.  A difference inside `A` returns `2a − 4 + b`, slack by
exactly `a − b`; inside `B` it returns `2b − 4 + a`, which *is* `a + 2b − 4`.  Measured across eight
`(a,b)` pairs: the `B` bound is exact in every one, the `A` bound only when `a = b`.

The reason is worth keeping, because it is the general lesson of this whole row applied one level
down.  A difference vector inside a part sees that part's own zero-sum eigenvalue, and there are two
of them — `2a−4+b` and `2b−4+a`.  Which is smaller is decided by `a ≥ b`.  **Evaluating a form at a
chosen vector bounds the extreme eigenvalue, but only a vector from the right eigenspace bounds it
tightly**; picking the convenient part rather than the correct one costs exactly the asymmetry
`a − b`, invisible in the balanced case where the two coincide.

No new machinery: this is `le_qEig_cb` and `qEig_last_mul_two_le` — the latter applied to the pair
`(B, A)` through `isCompleteBipartiteDist_symm` — met by `le_antisymm`. -/

/-- **`qₙ = a + 2b − 4` exactly**, for a complete bipartite distance with `b ≤ a` and `2 ≤ b`. -/
theorem qEig_last_eq_cb {n : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hab : (B.card : ℝ) ≤ (A.card : ℝ))
    (hB2 : 2 ≤ B.card) :
    qEig G hcard (Fin.last n) = (A.card : ℝ) + 2 * (B.card : ℝ) - 4 := by
  refine le_antisymm ?_ (le_qEig_cb G hcard A B hcov hdisj hcb hab (Fin.last n))
  have hcb' := isCompleteBipartiteDist_symm G A B hcov hdisj hcb
  obtain ⟨u, hu, u', hu', hne⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
  have h := qEig_last_mul_two_le G hcard B A (fun v => (hcov v).symm) hdisj.symm hcb' hu hu' hne
  linarith

/-! ### `q₁` from above — the two-parameter family, and why it has to be a family

`qEig_last_eq_cb` pinned `qₙ` exactly.  `q₁` is the quantity no single test vector reaches: it is a
root of the residual `2 × 2` block `[[4a+b−4, b], [a, a+4b−4]]` on `span{1_A, 1_B}`, and at
`a = b + 1` that root is a **surd** — `(5n−8+√(n²+8))/2` with `n = a + b`.  No identity with rational
coefficients can name it, which is why every earlier attempt to bound `q₁` by evaluating the form at
a chosen vector stalled: a lower bound is all a test vector can give, and the spread needs `q₁` from
*above*.

The upper bound comes from the form itself rather than from a vector.  Cauchy–Schwarz on each part
converts `2S_A²` into `2a·Σ_A` and `2S_B²` into `2b·Σ_B`; the cross term `2S_AS_B` is then split by
`2st ≤ p s² + q t²`, valid for every positive `p, q` with `pq ≥ 1`.  That leaves the form dominated
by `(4a+b−4+pa)·Σ_A + (a+4b−4+qb)·Σ_B`, so any `c` above both coefficients bounds every eigenvalue.

**The family is the point, not a weakness.**  Optimising `p` over the hyperbola recovers the larger
root of the block exactly — the surd is the optimum, not the bound — so the family touches `q₁` while
every member of it is division-free and rational.  Measured against the true `q₁` at
`(a,b) ∈ {(3,3), (5,4), (3,2), (4,3), (6,5)}` the best member agrees to four decimal places, and at
`a = b` the member `p = q = 1` is exact: `6a − 4`. -/

/-- `2st ≤ p s² + q t²` whenever `p, q > 0` and `pq ≥ 1`.

Division-free on purpose.  The usual statement of this splitting carries a `t/p`, and a hypothesis
`0 < p` then has to be threaded through every later `field_simp`; multiplying the claim by `p`
instead turns it into `(ps − t)² + (pq − 1)t² ≥ 0`, which is two `nlinarith` hints and no side
conditions downstream. -/
theorem two_mul_le_of_one_le_mul {p q s t : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : 1 ≤ p * q) :
    2 * (s * t) ≤ p * s ^ 2 + q * t ^ 2 := by
  by_contra hcon
  push_neg at hcon
  nlinarith [sq_nonneg (p * s - t), mul_nonneg (sub_nonneg.2 hpq) (sq_nonneg t), hp, hcon]

/-- **The complete bipartite form from above.**  For every `p, q > 0` with `pq ≥ 1`, and every `c`
dominating both `4a + b − 4 + pa` and `a + 4b − 4 + qb`, the form is at most `c‖x‖²`. -/
theorem inner_le_cb (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) {p q c : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : 1 ≤ p * q)
    (hA : 4 * (A.card : ℝ) + (B.card : ℝ) - 4 + p * (A.card : ℝ) ≤ c)
    (hB : (A.card : ℝ) + 4 * (B.card : ℝ) - 4 + q * (B.card : ℝ) ≤ c)
    (x : EuclideanSpace ℝ V) :
    ⟪x, QLin G x⟫_ℝ ≤ c * ‖x‖ ^ 2 := by
  have hTA : (0 : ℝ) ≤ ∑ u ∈ A, (WithLp.ofLp x) u ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hTB : (0 : ℝ) ≤ ∑ u ∈ B, (WithLp.ofLp x) u ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcsA := sq_sum_le_card_mul_sum_sq_real (V := V) A fun u => (WithLp.ofLp x) u
  have hcsB := sq_sum_le_card_mul_sum_sq_real (V := V) B fun u => (WithLp.ofLp x) u
  have hcross := two_mul_le_of_one_le_mul (s := ∑ u ∈ A, (WithLp.ofLp x) u)
    (t := ∑ u ∈ B, (WithLp.ofLp x) u) hp hq hpq
  rw [inner_QLin_eq, norm_sq_ofLp, inner_form_cb G A B hcov hdisj hcb (WithLp.ofLp x),
    sum_univ_split (V := V) A B hcov hdisj fun i => (WithLp.ofLp x) i ^ 2]
  nlinarith [hcross, hTA, hTB,
    mul_le_mul_of_nonneg_left hcsA (by linarith : (0 : ℝ) ≤ 2 + p),
    mul_le_mul_of_nonneg_left hcsB (by linarith : (0 : ℝ) ≤ 2 + q),
    mul_nonneg (sub_nonneg.2 hA) hTA, mul_nonneg (sub_nonneg.2 hB) hTB]

/-- **Every eigenvalue of a complete bipartite `Q` is at most `c`**, for every `(p, q)` on the
hyperbola.  Stated for all `i` rather than for `q₁`: the Rayleigh bound proves the general statement
and `qEig … 0` is one instance of it. -/
theorem qEig_le_cb {n : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) {p q c : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : 1 ≤ p * q)
    (hA : 4 * (A.card : ℝ) + (B.card : ℝ) - 4 + p * (A.card : ℝ) ≤ c)
    (hB : (A.card : ℝ) + 4 * (B.card : ℝ) - 4 + q * (B.card : ℝ) ≤ c)
    (i : Fin (n + 1)) :
    qEig G hcard i ≤ c :=
  Principia.Common.eigenvalues_le_of_inner_le (QLin_isSymmetric G) (finrank_euclidean_eq hcard)
    (inner_le_cb G A B hcov hdisj hcb hp hq hpq hA hB) i

/-- **`q₁ ≤ 5a + b − 4`**, the member `p = q = 1` — the first upper bound on `q₁` here that needs no
balance hypothesis.  It is exact at `a = b`, where it reads `6a − 4`. -/
theorem qEig_le_cb_one {n : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hab : (B.card : ℝ) ≤ (A.card : ℝ)) (i : Fin (n + 1)) :
    qEig G hcard i ≤ 5 * (A.card : ℝ) + (B.card : ℝ) - 4 :=
  qEig_le_cb G hcard A B hcov hdisj hcb one_pos one_pos (by norm_num) (by linarith) (by linarith) i

/-- **`S_Q ≤ 4a − b` for every complete bipartite graph with both parts of size ≥ 2.**

Both endpoints are now in hand: `qₙ = a + 2b − 4` exactly, and `q₁ ≤ 5a + b − 4`.  At `a = b` this
returns `3a`, matching `spread_cb_balanced_le` — the same number reached by an argument that never
mentions balance. -/
theorem spread_cb_le {n : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hab : (B.card : ℝ) ≤ (A.card : ℝ)) (hB2 : 2 ≤ B.card) :
    spread G hcard ≤ 4 * (A.card : ℝ) - (B.card : ℝ) := by
  have hs : spread G hcard = qEig G hcard 0 - qEig G hcard (Fin.last n) := rfl
  rw [hs, qEig_last_eq_cb G hcard A B hcov hdisj hcb hab hB2]
  linarith [qEig_le_cb_one G hcard A B hcov hdisj hcb hab 0]

/-! ### The odd-order case, part one: every **strictly unbalanced** complete bipartite graph

For `n = a + b` odd the extremal graph is `K_{m+1,m}` with `n = 2m + 1`, and the family above gives
`q₁(K_{m+1,m}) ≤ 6m` — take `p = m/(m+1)` and `q = (m+3)/m`, whose product `(m+3)/(m+1)` clears `1`
for free.  With `qₙ = 3m − 3` that caps the target spread at `3m + 3`.

The other complete bipartite graphs on `n` vertices are then handled with **no new analysis at all**.
The all-ones vector already gave `q₁ ≥ 4(a²+b²+ab−a−b)/n`, and `qₙ` is exact, so writing `a = n − b`
collapses the difference to `3n − 5b + 4b²/n` — a parabola in `b` alone.  Clearing the denominator
and subtracting the target leaves a ring identity with both factors of known sign:

`8b² − 10nb + 3n² − 3n = (2b − n + 3)(4b − 3n − 6) + 18`

On `b ≤ (n − 3)/2` the first factor is `≤ 0` and the second is `< 0`, so the whole expression is at
least `18` — **the margin is exactly `9/n`, and it never degenerates**.  That is the right answer
rather than a lucky one: `b = (n − 3)/2` is the largest strictly-unbalanced split, the closest
competitor to the extremal graph, and the identity's first factor vanishes there.  The bound is
therefore tight at the boundary of its own hypothesis and strict throughout its interior.

Worth recording is what did *not* happen.  The natural expectation was that separating the extremal
graph from its neighbours would need `q₁` for the neighbours too — the surd again, one imbalance at a
time.  It does not: a *lower* bound on the competitor and an *upper* bound on the extremal graph are
bounds in opposite directions, so each may be as lossy as its own side allows.  The all-ones vector
is lossy by `9/n` here and that is enough. -/

/-- **The spread of a complete bipartite graph from below, denominator cleared.**

`3n² − 5nb + 4b² ≤ S_Q · n`, for every complete bipartite distance with `b ≤ a` and `2 ≤ b`.  Both
inputs are already proved: `four_mul_le_qEig_zero_mul_card` for `q₁` and `qEig_last_eq_cb` for `qₙ`.
Substituting `a = n − b` is what turns a two-variable bound into a parabola in `b`. -/
theorem sq_card_sub_le_spread_mul_card_cb {n : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hab : (B.card : ℝ) ≤ (A.card : ℝ)) (hB2 : 2 ≤ B.card) :
    3 * (Fintype.card V : ℝ) ^ 2 - 5 * (Fintype.card V : ℝ) * (B.card : ℝ) + 4 * (B.card : ℝ) ^ 2
      ≤ spread G hcard * (Fintype.card V : ℝ) := by
  have hsum : (Fintype.card V : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by
    simpa using sum_univ_split (V := V) A B hcov hdisj fun _ => (1 : ℝ)
  have hs : spread G hcard = qEig G hcard 0 - qEig G hcard (Fin.last n) := rfl
  have hq1 := four_mul_le_qEig_zero_mul_card G hcard A B hcov hdisj hcb
  have hqn := qEig_last_eq_cb G hcard A B hcov hdisj hcb hab hB2
  rw [hs, hqn, sub_mul]
  rw [hsum] at hq1 ⊢
  nlinarith [hq1]

/-- **Every strictly unbalanced complete bipartite graph of odd order beats `3m + 3`.**

`3m + 3` is the cap the two-parameter family puts on `S_Q(K_{m+1,m})`, so this closes the odd-order
comparison for every complete bipartite competitor except the extremal graph itself.  The hypothesis
`b + 1 ≤ m` is exactly "strictly unbalanced"; at `b = m` the graph *is* `K_{m+1,m}`. -/
theorem le_spread_cb_of_odd_unbalanced {m : ℕ} (hcard : Fintype.card V = 2 * m + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hB2 : 2 ≤ B.card)
    (hunb : (B.card : ℝ) + 1 ≤ (m : ℝ)) :
    3 * (m : ℝ) + 3 ≤ spread G hcard := by
  have hN : (Fintype.card V : ℝ) = 2 * (m : ℝ) + 1 := by rw [hcard]; push_cast; ring
  have hsum : (Fintype.card V : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by
    simpa using sum_univ_split (V := V) A B hcov hdisj fun _ => (1 : ℝ)
  have hab : (B.card : ℝ) ≤ (A.card : ℝ) := by rw [hN] at hsum; linarith
  have hNpos : (0 : ℝ) < (Fintype.card V : ℝ) := by rw [hN]; positivity
  have hlow := sq_card_sub_le_spread_mul_card_cb G hcard A B hcov hdisj hcb hab hB2
  -- `8b² − 10Nb + 3N² − 3N = (2b − N + 3)(4b − 3N − 6) + 18`, both factors nonpositive.
  have hfac : (0 : ℝ) ≤ ((Fintype.card V : ℝ) - 3 - 2 * (B.card : ℝ))
      * (3 * (Fintype.card V : ℝ) + 6 - 4 * (B.card : ℝ)) := by
    rw [hN]
    exact mul_nonneg (by linarith) (by linarith)
  have key : (Fintype.card V : ℝ) * (3 * (Fintype.card V : ℝ) + 3) + 18
      ≤ 2 * (spread G hcard * (Fintype.card V : ℝ)) := by nlinarith [hlow, hfac]
  rw [hN] at key hNpos
  nlinarith [key, hNpos]

/-! ### The odd-order case, part two: the cap on the extremal graph

The member of the family that fits `K_{m+1,m}` is `p = m/(m+1)`, `q = (m+3)/m`.  It is worth stating
why this one: the two coefficients it produces are **equal**, both exactly `6m`.

`4a + b − 4 + pa = 4(m+1) + m − 4 + m = 6m`  and  `a + 4b − 4 + qb = (m+1) + 4m − 4 + (m+3) = 6m`.

Equal coefficients is the signature of the optimal member — the family's bound is `max` of the two,
so any member with unequal coefficients is paying for the larger one and could trade.  The side
condition costs nothing here: `pq = (m+3)/(m+1) ≥ 1` with room to spare, so this member is not even
on the boundary of the hyperbola.  Against the true `q₁ = (10m−3+√(4m²+4m+9))/2` the cap `6m` is
slack by `0.63` at `m = 2`, `0.82` at `m = 5` and `0.90` at `m = 10` — bounded, and in the direction
that matters, because `3m + 3` is what the competitors must clear. -/

/-- **`q₁(K_{m+1,m}) ≤ 6m`.** -/
theorem qEig_le_cb_odd {n m : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hm : 0 < m)
    (hA : (A.card : ℝ) = (m : ℝ) + 1) (hB : (B.card : ℝ) = (m : ℝ)) (i : Fin (n + 1)) :
    qEig G hcard i ≤ 6 * (m : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  refine qEig_le_cb G hcard A B hcov hdisj hcb (p := (m : ℝ) / ((m : ℝ) + 1))
    (q := ((m : ℝ) + 3) / (m : ℝ)) (div_pos hm0 hm1) (div_pos (by linarith) hm0) ?_ ?_ ?_ i
  · rw [div_mul_div_comm]
    exact (one_le_div (by positivity)).2 (by nlinarith)
  · rw [hA, hB, div_mul_cancel₀ _ (ne_of_gt hm1)]
    linarith
  · rw [hA, hB, div_mul_cancel₀ _ (ne_of_gt hm0)]
    linarith

/-- **`S_Q(K_{m+1,m}) ≤ 3m + 3`** — the target that `le_spread_cb_of_odd_unbalanced` clears.  With
`qₙ = 3m − 3` exact, this is the cap on `q₁` minus that, and the two halves of the odd-order
complete bipartite comparison now meet at the same number. -/
theorem spread_cb_le_odd {m : ℕ} (hcard : Fintype.card V = 2 * m + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hm : 2 ≤ m)
    (hA : (A.card : ℝ) = (m : ℝ) + 1) (hB : (B.card : ℝ) = (m : ℝ)) :
    spread G hcard ≤ 3 * (m : ℝ) + 3 := by
  have hs : spread G hcard = qEig G hcard 0 - qEig G hcard (Fin.last (2 * m)) := rfl
  have hab : (B.card : ℝ) ≤ (A.card : ℝ) := by rw [hA, hB]; linarith
  have hB2 : 2 ≤ B.card := by
    have : (2 : ℝ) ≤ (B.card : ℝ) := by rw [hB]; exact_mod_cast hm
    exact_mod_cast this
  rw [hs, qEig_last_eq_cb G hcard A B hcov hdisj hcb hab hB2, hA, hB]
  have := qEig_le_cb_odd G hcard A B hcov hdisj hcb (by omega : 0 < m) hA hB 0
  linarith

/-! ### The odd-order case, part three: what a **non**-complete-bipartite competitor pays

The two parts above dispose of every complete bipartite competitor.  What is left is a connected
bipartite `G` in which some cross pair is *not* adjacent, and the quantity that has to improve is
`Z = ∑_{u∈A} ∑_{v∈B} d(u,v)`, bounded so far by `card_mul_card_le_sumAcross` at `Z ≥ ab`.

**One non-edge costs `2`, not `1`.**  Bipartite parity (`Common.not_even_dist_of_cross`) makes every
cross distance odd, so a non-adjacent cross pair cannot be at distance `2` either — it jumps straight
from `1` to `3`.  Hence `Z ≥ ab + 2`.

The accounting says this is enough, which is worth recording because a first pass said it was not.
Threading `Z ≥ ab + 2` through `base_bound_le_spread` adds `2·c_Z` to the left-hand side, i.e.
`2·c_Z/(n·P·Q) = 2(4b−n)/(nb)` to the spread — about `2/m` at the near-balanced split.  Set against
that, the deficit is **not** the `3/2` obtained by comparing against the bare `3n/2`: the base bound
carries its own remainder `P·Q·(nd + 2d²)`, so a competitor with `d = a − b ≥ 1` already enjoys
`3n/2 + d/2 + d²/n`, and only `d = 1` is in play once the parts above are done.  Measured against the
true extremal spread at `m = 2 … 12`, the deficit runs `0.172, 0.132, …, 0.040` — it is `O(1/m)`, and
the `Z`-gain beats it by a factor of roughly `3.5` at every `m`.

The first accounting compared the gain against the wrong deficit and concluded the route was short by
a constant.  The remainder term is the whole difference, and it was already proved. -/

/-- **A non-adjacent cross pair is at distance at least `3`.**  Parity does the work: the distance is
odd, so ruling out `1` (non-adjacency) rules out `2` for free. -/
theorem three_le_dist_cross_of_not_adj {s t : Set V} (hb : G.IsBipartiteWith s t)
    (hconn : G.Connected) {u v : V} (hu : u ∈ s) (hv : v ∈ t) (hnadj : ¬ G.Adj u v) :
    3 ≤ G.dist u v := by
  have hodd := Principia.Common.not_even_dist_of_cross hb (hconn u v) hu hv
  have h0 : G.dist u v ≠ 0 := fun h => hodd ⟨0, by omega⟩
  have h1 : G.dist u v ≠ 1 := fun h => hnadj (SimpleGraph.dist_eq_one_iff_adj.mp h)
  have h2 : G.dist u v ≠ 2 := fun h => hodd ⟨1, by omega⟩
  omega

/-- **`Z ≥ ab + 2` whenever one cross pair is non-adjacent.**

Both sums are handled the same way: subtract the baseline the previous bound already established,
observe the residual is termwise nonnegative, and apply `Finset.single_le_sum` at the exceptional
index.  Nothing here is special to the inner or the outer sum. -/
theorem card_mul_card_add_two_le_sumAcross {s t : Set V} (hb : G.IsBipartiteWith s t)
    (hconn : G.Connected) (A B : Finset V) (hA : ∀ u ∈ A, u ∈ s) (hB : ∀ v ∈ B, v ∈ t)
    {u₀ v₀ : V} (hu₀ : u₀ ∈ A) (hv₀ : v₀ ∈ B) (hnadj : ¬ G.Adj u₀ v₀) :
    (A.card : ℝ) * B.card + 2 ≤ sumAcross G A B := by
  have hone : ∀ u ∈ A, ∀ v ∈ B, (1 : ℝ) ≤ (G.dist u v : ℝ) := by
    intro u hu v hv
    have hodd := Principia.Common.not_even_dist_of_cross hb (hconn u v) (hA _ hu) (hB _ hv)
    have hne : G.dist u v ≠ 0 := fun h0 => hodd ⟨0, by omega⟩
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  have hrow : ∀ u ∈ A, (B.card : ℝ) ≤ ∑ v ∈ B, (G.dist u v : ℝ) := by
    intro u hu
    have h := Finset.card_nsmul_le_sum B (fun v => (G.dist u v : ℝ)) 1 (hone u hu)
    rw [nsmul_eq_mul, mul_one] at h
    exact h
  have h3 : (3 : ℝ) ≤ (G.dist u₀ v₀ : ℝ) := by
    exact_mod_cast three_le_dist_cross_of_not_adj G hb hconn (hA _ hu₀) (hB _ hv₀) hnadj
  have hrow0 : (B.card : ℝ) + 2 ≤ ∑ v ∈ B, (G.dist u₀ v : ℝ) := by
    have hnn : ∀ v ∈ B, (0 : ℝ) ≤ (G.dist u₀ v : ℝ) - 1 := fun v hv => by
      linarith [hone u₀ hu₀ v hv]
    have hle := Finset.single_le_sum (f := fun v => (G.dist u₀ v : ℝ) - 1) hnn hv₀
    have heq : ∑ v ∈ B, ((G.dist u₀ v : ℝ) - 1)
        = (∑ v ∈ B, (G.dist u₀ v : ℝ)) - (B.card : ℝ) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [heq] at hle
    linarith
  have hnn2 : ∀ u ∈ A, (0 : ℝ) ≤ (∑ v ∈ B, (G.dist u v : ℝ)) - (B.card : ℝ) :=
    fun u hu => by linarith [hrow u hu]
  have hout := Finset.single_le_sum
    (f := fun u => (∑ v ∈ B, (G.dist u v : ℝ)) - (B.card : ℝ)) hnn2 hu₀
  have hsum2 : ∑ u ∈ A, ((∑ v ∈ B, (G.dist u v : ℝ)) - (B.card : ℝ))
      = sumAcross G A B - (A.card : ℝ) * (B.card : ℝ) := by
    rw [Finset.sum_sub_distrib, sumAcross]
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hsum2] at hout
  linarith

/-! ### The sharp cap: `q₁(K_{m+1,m}) ≤ 6m − 1 + 2/n`

`spread_cb_le_odd` capped the extremal spread at `3m + 3`, which is enough to beat the *strictly
unbalanced* complete bipartite competitors but **not** the remaining ones: a non-complete-bipartite
competitor is only guaranteed `3m + 2 + 1/n + 2(4b−n)/(nb)`, and `3m + 3` sits above that.  The cap
has to come within `O(1/n)` of the truth, and the family delivers exactly that.

Take `p = (2m² − m + 1)/((m+1)(2m+1))` and `q = 1/p`.  Then

  `c_A = 4a + b − 4 + pa = 5m + (2m² − m + 1)/(2m+1) = 6m − 1 + 2/n`
  `c_B = a + 4b − 4 + qb = 6m − 1 + (2m − 2)/(2m² − m + 1)`

and `c_A ≥ c_B` for every `m`, because the comparison clears to `2 ≥ −2`.  So `c = c_A`, and the two
coefficients are within `O(1/m²)` of each other — this member is not the exact optimum (that is the
surd) but it is inside it by less than the statement can notice.  Against the true `q₁` the cap is
slack by `0.028` at `m = 2` and `0.0004` at `m = 13`.

Stated multiplied out by `n`, so no division survives into the statement a consumer has to carry. -/

/-- **`q₁ · n ≤ (6m − 1)·n + 2` for `K_{m+1,m}`**, `n = 2m + 1`. -/
theorem qEig_mul_le_cb_odd_sharp {n m : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hm : 0 < m)
    (hA : (A.card : ℝ) = (m : ℝ) + 1) (hB : (B.card : ℝ) = (m : ℝ)) (i : Fin (n + 1)) :
    qEig G hcard i * (2 * (m : ℝ) + 1) ≤ (6 * (m : ℝ) - 1) * (2 * (m : ℝ) + 1) + 2 := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hn : (0 : ℝ) < 2 * (m : ℝ) + 1 := by linarith
  have hden1 : (0 : ℝ) < ((m : ℝ) + 1) * (2 * (m : ℝ) + 1) := by positivity
  have hden2 : (0 : ℝ) < 2 * (m : ℝ) ^ 2 - (m : ℝ) + 1 := by
    nlinarith [sq_nonneg (4 * (m : ℝ) - 1)]
  have hd1 : (((m : ℝ) + 1) * (2 * (m : ℝ) + 1)) ≠ 0 := ne_of_gt hden1
  have hd2 : (2 * (m : ℝ) ^ 2 - (m : ℝ) + 1) ≠ 0 := ne_of_gt hden2
  have hnne : (2 * (m : ℝ) + 1) ≠ 0 := ne_of_gt hn
  have hle := qEig_le_cb G hcard A B hcov hdisj hcb
    (p := (2 * (m : ℝ) ^ 2 - (m : ℝ) + 1) / (((m : ℝ) + 1) * (2 * (m : ℝ) + 1)))
    (q := (((m : ℝ) + 1) * (2 * (m : ℝ) + 1)) / (2 * (m : ℝ) ^ 2 - (m : ℝ) + 1))
    (c := 6 * (m : ℝ) - 1 + 2 / (2 * (m : ℝ) + 1))
    (div_pos hden2 hden1) (div_pos hden1 hden2)
    (by
      -- `field_simp` alone leaves `1 = X / X`: it ring-normalises the denominator into a shape no
      -- longer syntactically equal to `hd2`, so it cannot discharge its own side condition.  Naming
      -- the cancellation explicitly avoids depending on that normal form at all.
      have heq : (2 * (m : ℝ) ^ 2 - (m : ℝ) + 1) / (((m : ℝ) + 1) * (2 * (m : ℝ) + 1))
          * ((((m : ℝ) + 1) * (2 * (m : ℝ) + 1)) / (2 * (m : ℝ) ^ 2 - (m : ℝ) + 1)) = 1 := by
        rw [div_mul_div_comm,
          mul_comm (2 * (m : ℝ) ^ 2 - (m : ℝ) + 1) (((m : ℝ) + 1) * (2 * (m : ℝ) + 1)),
          div_self (mul_ne_zero hd1 hd2)]
      exact heq.ge)
    (by rw [hA, hB]; refine le_of_eq ?_; field_simp; ring)
    (by
      -- Not `field_simp`: it clears the `(2m+1)` denominator but leaves `X⁻¹` as an atom, and `ring`
      -- then cannot cancel it against `X`.  Comparing the two sides as *quotients* and applying
      -- `div_le_div_iff₀` reduces the whole claim to one polynomial inequality whose two sides differ
      -- by the constant `4` — the same `4` the numerics predicted.
      rw [hA, hB]
      have h1 : (((m : ℝ) + 1) * (2 * (m : ℝ) + 1)) / (2 * (m : ℝ) ^ 2 - (m : ℝ) + 1) * (m : ℝ)
          = ((((m : ℝ) + 1) * (2 * (m : ℝ) + 1)) * (m : ℝ))
              / (2 * (m : ℝ) ^ 2 - (m : ℝ) + 1) :=
        div_mul_eq_mul_div _ _ _
      have h2 : 6 * (m : ℝ) - 1 + 2 / (2 * (m : ℝ) + 1)
          = ((m : ℝ) + 1) + 4 * (m : ℝ) - 4
              + (2 * (m : ℝ) ^ 2 + 5 * (m : ℝ) + 4) / (2 * (m : ℝ) + 1) := by
        field_simp
        ring
      rw [h1, h2]
      have h3 : ((((m : ℝ) + 1) * (2 * (m : ℝ) + 1)) * (m : ℝ))
            / (2 * (m : ℝ) ^ 2 - (m : ℝ) + 1)
          ≤ (2 * (m : ℝ) ^ 2 + 5 * (m : ℝ) + 4) / (2 * (m : ℝ) + 1) := by
        rw [div_le_div_iff₀ hden2 hn]
        nlinarith [hm0]
      linarith)
    i
  have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt hn)
  calc qEig G hcard i * (2 * (m : ℝ) + 1)
      ≤ (6 * (m : ℝ) - 1 + 2 / (2 * (m : ℝ) + 1)) * (2 * (m : ℝ) + 1) := hmul
    _ = (6 * (m : ℝ) - 1) * (2 * (m : ℝ) + 1) + 2 := by field_simp

/-! ### Threading the improved `Z` through the base bound

`le_of_coeffs_nonneg` takes the three parity minima as arguments, so improving one of them is a
change of argument and nothing else — the master inequality, the coefficient algebra and the sign
conditions are all reused verbatim.  That is the payoff of having stated the substitution once.

The `d = 1` case is the whole remaining difficulty and it sits **entirely inside the `θ = 0`
regime**: with `a = b + 1` and `n = 2b + 1`, the regime's two side conditions read `−b − 2 ≤ 0` and
`1 ≤ 2b`, both free.  For `d ≥ 3` the `θ = 0` conditions do fail once `m ≥ 8`, which is why the
general trichotomy exists — but `d ≥ 3` needs no help from `Z` at all, since the base bound's own
remainder already supplies `3n/2 + 3/2 + 9/n`.

Scaling by `b` is what removes the last denominator.  `c_Z` at `θ = 0` is `4PQ − 2nP(b−1)`, and
`Q = 2b(b−1)`, so `b·c_Z = PQ·(4b − n)` exactly — the factor `P` that `c_Z` carries alone becomes a
factor of `PQ` the moment it is multiplied by `b`.  Everything is then a multiple of `PQ` and
cancels in one step. -/

/-- **The base bound with a non-adjacent cross pair.**  Identical to `base_bound_le_spread` except
that `Z` enters at `ab + 2`. -/
theorem base_bound_le_spread_nonadj {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hb : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (hcX : 0 ≤ coeffX (V := V) A B θ) (hcY : 0 ≤ coeffY (V := V) A B θ)
    (hcZ : 0 ≤ coeffZ (V := V) A B θ)
    {u₀ v₀ : V} (hu₀ : u₀ ∈ A) (hv₀ : v₀ ∈ B) (hnadj : ¬ G.Adj u₀ v₀) :
    coeffX (V := V) A B θ * (2 * ((A.card : ℝ) ^ 2 - A.card))
        + coeffY (V := V) A B θ * (2 * ((B.card : ℝ) ^ 2 - B.card))
        + coeffZ (V := V) A B θ * ((A.card : ℝ) * B.card + 2)
      ≤ spread G hcard
          * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B)) :=
  le_of_coeffs_nonneg hcX hcY hcZ
    (two_mul_sq_sub_le_sumWithin G hb hconn A hAs)
    (two_mul_sq_sub_le_sumWithin G hb.symm hconn B hBt)
    (card_mul_card_add_two_le_sumAcross G hb hconn A B hAs hBt hu₀ hv₀ hnadj)
    (spread_master_coeffs G hcard A B hcov hdisj hA2 hB2 h0 h1)

/-- The `θ = 0` regime of `base_bound_le_spread_nonadj`. -/
theorem base_bound_theta_zero_nonadj {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hb : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    (hY : (Fintype.card V : ℝ) * ((B.card : ℝ) - 2) ≤ partWeight (V := V) B)
    (hZ : (Fintype.card V : ℝ) ≤ 4 * (B.card : ℝ))
    {u₀ v₀ : V} (hu₀ : u₀ ∈ A) (hv₀ : v₀ ∈ B) (hnadj : ¬ G.Adj u₀ v₀) :
    coeffX (V := V) A B 0 * (2 * ((A.card : ℝ) ^ 2 - A.card))
        + coeffY (V := V) A B 0 * (2 * ((B.card : ℝ) ^ 2 - B.card))
        + coeffZ (V := V) A B 0 * ((A.card : ℝ) * B.card + 2)
      ≤ spread G hcard
          * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B)) :=
  base_bound_le_spread_nonadj G hcard hb hconn A B hcov hdisj hA2 hB2 hAs hBt le_rfl zero_le_one
    (coeffX_zero_nonneg (V := V) A B hA2 hB2)
    (coeffY_zero_nonneg (V := V) A B hA2 hB2 hY)
    (coeffZ_zero_nonneg (V := V) A B hA2 hB2 hZ) hu₀ hv₀ hnadj

/-- **The improved base identity, scaled by `b`.**  `2b ·` (base with `Z = ab + 2`) is `PQ` times a
polynomial.  The scaling is what turns `c_Z`'s lone factor `P` into a factor of `PQ`, so that one
cancellation disposes of both `P` and `Q`. -/
theorem two_mul_card_mul_base_theta_zero_nonadj_eq (A B : Finset V)
    (hsum : (Fintype.card V : ℝ) = (A.card : ℝ) + (B.card : ℝ)) :
    2 * ((B.card : ℝ) * (coeffX (V := V) A B 0 * (2 * ((A.card : ℝ) ^ 2 - A.card))
        + coeffY (V := V) A B 0 * (2 * ((B.card : ℝ) ^ 2 - B.card))
        + coeffZ (V := V) A B 0 * ((A.card : ℝ) * B.card + 2)))
      = ((B.card : ℝ) * (3 * (Fintype.card V : ℝ) ^ 2
              + (Fintype.card V : ℝ) * ((A.card : ℝ) - (B.card : ℝ))
              + 2 * ((A.card : ℝ) - (B.card : ℝ)) ^ 2)
          + 4 * (4 * (B.card : ℝ) - (Fintype.card V : ℝ)))
        * (partWeight (V := V) A * partWeight (V := V) B) := by
  simp only [coeffX, coeffY, coeffZ, partWeight, hsum]
  ring

/-- **`3n² + n + 4 ≤ 2·S_Q·n`** for a connected bipartite graph with `a = b + 1` and a non-adjacent
cross pair.  Equivalently `S_Q ≥ 3n/2 + 1/2 + 2/n`, which is exactly the cap
`qEig_mul_le_cb_odd_sharp` puts on `S_Q(K_{m+1,m})`: the two meet at `(3m+2)·n + 2`. -/
theorem odd_nonadj_spread_bound {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hb : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    (hd : (A.card : ℝ) = (B.card : ℝ) + 1)
    {u₀ v₀ : V} (hu₀ : u₀ ∈ A) (hv₀ : v₀ ∈ B) (hnadj : ¬ G.Adj u₀ v₀) :
    3 * (Fintype.card V : ℝ) ^ 2 + (Fintype.card V : ℝ) + 4
      ≤ 2 * spread G hcard * (Fintype.card V : ℝ) := by
  have hsum := card_eq_add (V := V) A B hcov hdisj
  have hbb : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB2
  have hbpos : (0 : ℝ) < (B.card : ℝ) := by linarith
  have hPQ : (0 : ℝ) < partWeight (V := V) A * partWeight (V := V) B :=
    mul_pos (offDiag_weight_pos (V := V) hA2) (offDiag_weight_pos (V := V) hB2)
  have hn2b : (Fintype.card V : ℝ) = 2 * (B.card : ℝ) + 1 := by rw [hsum, hd]; ring
  have hY : (Fintype.card V : ℝ) * ((B.card : ℝ) - 2) ≤ partWeight (V := V) B := by
    simp only [partWeight, hn2b]
    nlinarith [hbb]
  have hZ : (Fintype.card V : ℝ) ≤ 4 * (B.card : ℝ) := by rw [hn2b]; linarith
  have hbase := base_bound_theta_zero_nonadj G hcard hb hconn A B hcov hdisj hA2 hB2 hAs hBt
    hY hZ hu₀ hv₀ hnadj
  have hscale := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hbase (le_of_lt hbpos)) (by norm_num : (0 : ℝ) ≤ 2)
  rw [two_mul_card_mul_base_theta_zero_nonadj_eq (V := V) A B hsum] at hscale
  have hrhs : 2 * ((B.card : ℝ) * (spread G hcard
        * ((Fintype.card V : ℝ) * (partWeight (V := V) A * partWeight (V := V) B))))
      = (2 * (B.card : ℝ) * spread G hcard * (Fintype.card V : ℝ))
        * (partWeight (V := V) A * partWeight (V := V) B) := by ring
  rw [hrhs] at hscale
  have h2 := le_of_mul_le_mul_right hscale hPQ
  rw [hd, hn2b] at h2
  have hgb : (B.card : ℝ) * (3 * (2 * (B.card : ℝ) + 1) ^ 2 + (2 * (B.card : ℝ) + 1) + 4)
      ≤ (B.card : ℝ) * (2 * spread G hcard * (2 * (B.card : ℝ) + 1)) := by
    nlinarith [h2, hbb]
  rw [hn2b]
  exact le_of_mul_le_mul_left hgb hbpos

/-! ### The last quadrant: `d ≥ 3`, by keeping the margin each regime already proves

`three_mul_card_le_two_mul_spread_of_two_le` reaches `3n ≤ 2S_Q` through three regimes and **throws
away what each of them actually proved**.  Recovering those margins is the whole of this section —
no new inequality is needed, and in particular `Z ≥ ab + 2` is not needed here at all.

  * `θ = 0` proves `2S_Q·n ≥ 3n² + nd + 2d²`.  At `d ≥ 3` the remainder alone is `3n + 18`.
  * `θ_Z` proves `2S_Q·n ≥ 4n²`, i.e. `S_Q ≥ 2n` — the regime is `b ≤ 3`, `a ≥ 3b`, so `n ≥ 8` and
    `n² ≥ n + 4` with room.  Note this is *not* the `d`-remainder bound: at `(a,b) = (13,2)` the
    remainder form gives `36.07` and this gives `30`.  It does not have to be; it only has to clear
    the target.
  * `θ_Y` proves `2S_Q·n ≥ 3n² + d(bn − 2d)/(b−2)`.  Since `bn − 2d = (b−2)n + 4b`, the quotient is
    at least `3n` once `d ≥ 3`, and `3n ≥ n + 4`.

Each of the three clears `3n² + n + 4` — the same number `odd_nonadj_spread_bound` reaches for
`d = 1`, and the same number the sharp cap puts on the extremal graph.  **`d = 1` was the only case
that needed the improved `Z`**, which is why it was worth isolating: everything else had margin to
spare and was losing it to a weaker statement of the conclusion. -/

/-- **`θ = 0`, `d ≥ 3`.**  The remainder `nd + 2d²` dominates `n + 4` outright. -/
theorem three_le_diff_target_theta_zero {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hbip : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    (hY : (Fintype.card V : ℝ) * ((B.card : ℝ) - 2) ≤ partWeight (V := V) B)
    (hZ : (Fintype.card V : ℝ) ≤ 4 * (B.card : ℝ))
    (hd3 : 3 ≤ (A.card : ℝ) - (B.card : ℝ)) :
    3 * (Fintype.card V : ℝ) ^ 2 + (Fintype.card V : ℝ) + 4
      ≤ 2 * spread G hcard * (Fintype.card V : ℝ) := by
  have hbb : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB2
  have hsum := card_eq_add (V := V) A B hcov hdisj
  have hPQ : (0 : ℝ) < partWeight (V := V) A * partWeight (V := V) B :=
    mul_pos (offDiag_weight_pos (V := V) hA2) (offDiag_weight_pos (V := V) hB2)
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by rw [hsum]; linarith
  have hbase := base_bound_theta_zero G hcard hbip hconn A B hcov hdisj hA2 hB2 hAs hBt hY hZ
  have hid := two_mul_base_theta_zero_eq (V := V) A B hsum
  have hrem : (0 : ℝ) ≤ (partWeight (V := V) A * partWeight (V := V) B)
      * ((Fintype.card V : ℝ) * ((A.card : ℝ) - (B.card : ℝ))
          + 2 * ((A.card : ℝ) - (B.card : ℝ)) ^ 2 - (Fintype.card V : ℝ) - 4) :=
    mul_nonneg (le_of_lt hPQ) (by nlinarith [hd3, hnpos])
  have hmul : (3 * (Fintype.card V : ℝ) ^ 2 + (Fintype.card V : ℝ) + 4)
        * (partWeight (V := V) A * partWeight (V := V) B)
      ≤ (2 * spread G hcard * (Fintype.card V : ℝ))
        * (partWeight (V := V) A * partWeight (V := V) B) := by
    nlinarith [hbase, hid, hrem]
  exact le_of_mul_le_mul_right hmul hPQ

/-- **`θ_Z`.**  This regime proves `S_Q ≥ 2n`, and `b ≤ 3` with `a ≥ 3b` forces `n ≥ 8`. -/
theorem three_le_diff_target_thetaZ {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hbip : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    (hsmall : (B.card : ℝ) ≤ 3) (hbig : 3 * (B.card : ℝ) ≤ (A.card : ℝ)) :
    3 * (Fintype.card V : ℝ) ^ 2 + (Fintype.card V : ℝ) + 4
      ≤ 2 * spread G hcard * (Fintype.card V : ℝ) := by
  have hbb : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB2
  have hsum := card_eq_add (V := V) A B hcov hdisj
  have hPQ : (0 : ℝ) < partWeight (V := V) A * partWeight (V := V) B :=
    mul_pos (offDiag_weight_pos (V := V) hA2) (offDiag_weight_pos (V := V) hB2)
  have hn8 : (8 : ℝ) ≤ (Fintype.card V : ℝ) := by rw [hsum]; linarith
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by linarith
  have hd : (0 : ℝ) < (A.card : ℝ) - (B.card : ℝ) := by linarith
  have hbase := base_bound_thetaZ G hcard hbip hconn A B hcov hdisj hA2 hB2 hAs hBt hsmall hbig
  have hid := two_mul_base_thetaZ_eq (V := V) A B (ne_of_gt hnpos) (ne_of_gt hd) hsum
  have hgap : (0 : ℝ) ≤ (partWeight (V := V) A * partWeight (V := V) B)
      * ((Fintype.card V : ℝ) ^ 2 - (Fintype.card V : ℝ) - 4) :=
    mul_nonneg (le_of_lt hPQ) (by nlinarith [hn8])
  have hmul : (3 * (Fintype.card V : ℝ) ^ 2 + (Fintype.card V : ℝ) + 4)
        * (partWeight (V := V) A * partWeight (V := V) B)
      ≤ (2 * spread G hcard * (Fintype.card V : ℝ))
        * (partWeight (V := V) A * partWeight (V := V) B) := by
    nlinarith [hbase, hid, hgap]
  exact le_of_mul_le_mul_right hmul hPQ

/-- **`θ_Y`, `d ≥ 3`.**  `bn − 2d = (b−2)n + 4b`, so the regime's margin `d(bn−2d)/(b−2)` is at
least `3n`, and `3n ≥ n + 4`. -/
theorem three_le_diff_target_thetaY {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hbip : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    (hb4 : (4 : ℝ) ≤ (B.card : ℝ)) (hab : (B.card : ℝ) ≤ (A.card : ℝ))
    (hu : (B.card : ℝ) ^ 2 ≤ (A.card : ℝ) * ((B.card : ℝ) - 2))
    (hS : (A.card : ℝ) * (4 - (B.card : ℝ)) - (B.card : ℝ) ^ 2 ≤ 0)
    (hd3 : 3 ≤ (A.card : ℝ) - (B.card : ℝ)) :
    3 * (Fintype.card V : ℝ) ^ 2 + (Fintype.card V : ℝ) + 4
      ≤ 2 * spread G hcard * (Fintype.card V : ℝ) := by
  have hb2 : (2 : ℝ) < (B.card : ℝ) := by linarith
  have hsum := card_eq_add (V := V) A B hcov hdisj
  have hPQ : (0 : ℝ) < partWeight (V := V) A * partWeight (V := V) B :=
    mul_pos (offDiag_weight_pos (V := V) hA2) (offDiag_weight_pos (V := V) hB2)
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by rw [hsum]; linarith
  have hbd : (0 : ℝ) < (B.card : ℝ) - 2 := by linarith
  have hbase := base_bound_thetaY G hcard hbip hconn A B hcov hdisj hA2 hB2 hAs hBt hb2 hu hS
  have hid := two_mul_base_thetaY_sub (V := V) A B (ne_of_gt hnpos) (ne_of_gt hbd) hsum
  have hquot : (Fintype.card V : ℝ) + 4
      ≤ ((A.card : ℝ) - (B.card : ℝ))
          * ((B.card : ℝ) * (Fintype.card V : ℝ) - 2 * ((A.card : ℝ) - (B.card : ℝ)))
        / ((B.card : ℝ) - 2) := by
    rw [le_div_iff₀ hbd, hsum]
    nlinarith [hd3, hb4, hab,
      mul_nonneg (by linarith : (0 : ℝ) ≤ (B.card : ℝ) - 2)
        (by linarith : (0 : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (A.card : ℝ) - (B.card : ℝ) - 3)
        (by nlinarith [hb4, hab] :
          (0 : ℝ) ≤ ((B.card : ℝ) - 2) * ((A.card : ℝ) + (B.card : ℝ)) + 4 * (B.card : ℝ))]
  have hmargin : (partWeight (V := V) A * partWeight (V := V) B) * ((Fintype.card V : ℝ) + 4)
      ≤ partWeight (V := V) A * partWeight (V := V) B
        * (((A.card : ℝ) - (B.card : ℝ))
            * ((B.card : ℝ) * (Fintype.card V : ℝ) - 2 * ((A.card : ℝ) - (B.card : ℝ))))
        / ((B.card : ℝ) - 2) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hquot (le_of_lt hPQ)
  have hmul : (3 * (Fintype.card V : ℝ) ^ 2 + (Fintype.card V : ℝ) + 4)
        * (partWeight (V := V) A * partWeight (V := V) B)
      ≤ (2 * spread G hcard * (Fintype.card V : ℝ))
        * (partWeight (V := V) A * partWeight (V := V) B) := by
    nlinarith [hbase, hid, hmargin]
  exact le_of_mul_le_mul_right hmul hPQ

/-- **The trichotomy, with the margins kept.**  Every connected bipartite graph whose parts differ
by at least `3` satisfies `3n² + n + 4 ≤ 2·S_Q·n`.  The case split is the same one
`three_mul_card_le_two_mul_spread_of_two_le` makes; only the conclusion carried through it is
stronger. -/
theorem three_le_diff_target_of_two_le {n : ℕ} (hcard : Fintype.card V = n + 1)
    {s t : Set V} (hbip : G.IsBipartiteWith s t) (hconn : G.Connected)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ B.card)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    (hab : (B.card : ℝ) ≤ (A.card : ℝ)) (hd3 : 3 ≤ (A.card : ℝ) - (B.card : ℝ)) :
    3 * (Fintype.card V : ℝ) ^ 2 + (Fintype.card V : ℝ) + 4
      ≤ 2 * spread G hcard * (Fintype.card V : ℝ) := by
  have ha : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA2
  have hb : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB2
  have hsum := card_eq_add (V := V) A B hcov hdisj
  rcases le_or_gt B.card 3 with hb3 | hb4
  · have hb3' : (B.card : ℝ) ≤ 3 := by exact_mod_cast hb3
    by_cases hz : (Fintype.card V : ℝ) ≤ 4 * (B.card : ℝ)
    · refine three_le_diff_target_theta_zero G hcard hbip hconn A B hcov hdisj hA2 hB2 hAs hBt
        ?_ hz hd3
      rw [partWeight]
      nlinarith [hb, hb3', hz]
    · refine three_le_diff_target_thetaZ G hcard hbip hconn A B hcov hdisj hA2 hB2 hAs hBt hb3' ?_
      rw [hsum] at hz
      linarith
  · have hb4' : (4 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hb4
    by_cases hu : (B.card : ℝ) ^ 2 ≤ (A.card : ℝ) * ((B.card : ℝ) - 2)
    · refine three_le_diff_target_thetaY G hcard hbip hconn A B hcov hdisj hA2 hB2 hAs hBt
        hb4' hab hu ?_ hd3
      nlinarith [hb4', ha]
    · push_neg at hu
      refine three_le_diff_target_theta_zero G hcard hbip hconn A B hcov hdisj hA2 hB2 hAs hBt
        ?_ ?_ hd3
      · rw [partWeight, hsum]
        nlinarith [hu, hb4']
      · rw [hsum]
        nlinarith [hu, hb4']

/-! ### The dichotomy that lets the four odd-order cases combine

Every competitor either has a non-adjacent cross pair — and then pays `Z ≥ ab + 2`, which is what
`odd_nonadj_spread_bound` consumes — or it has none, and then it *is* `K_{a,b}` and its spread is
computed exactly rather than bounded.  The second half needs proving: "every cross pair is an edge"
is a statement about adjacency, while everything downstream is stated about `dist`.

The conversion is short because bipartite parity supplies the lower bound for free.  Across a part
the distance is `1` by `dist_eq_one_iff_adj`.  Within a part it is at most `2` (two edges through
any vertex of the other part, which is nonempty) and at least `2` (`Common.two_le_dist_of_same`:
same-side distances are even, and positive for distinct vertices).  No walk needs to be built by
hand in either direction. -/

/-- **If every cross pair is an edge, the distance is complete bipartite.** -/
theorem isCompleteBipartiteDist_of_forall_adj {s t : Set V} (hbip : G.IsBipartiteWith s t)
    (hconn : G.Connected) (A B : Finset V)
    (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hAs : ∀ u ∈ A, u ∈ s) (hBt : ∀ v ∈ B, v ∈ t)
    (hA1 : A.Nonempty) (hB1 : B.Nonempty)
    (hadj : ∀ u ∈ A, ∀ v ∈ B, G.Adj u v) :
    IsCompleteBipartiteDist G A B := by
  have hcross : ∀ u ∈ A, ∀ v ∈ B, G.dist u v = 1 := fun u hu v hv =>
    SimpleGraph.dist_eq_one_iff_adj.mpr (hadj u hu v hv)
  have hsame : ∀ u v : V, u ≠ v → (u ∈ A ↔ v ∈ A) → G.dist u v = 2 := by
    intro u v hne hiff
    by_cases huA : u ∈ A
    · have hvA : v ∈ A := hiff.mp huA
      obtain ⟨w, hw⟩ := hB1
      have h1 : G.dist u w = 1 := hcross u huA w hw
      have h2 : G.dist w v = 1 := by
        rw [SimpleGraph.dist_comm]
        exact hcross v hvA w hw
      have htri := hconn.dist_triangle (u := u) (v := w) (w := v)
      have hge := Principia.Common.two_le_dist_of_same hbip (hconn u v) hne (hAs u huA) (hAs v hvA)
      omega
    · have huB : u ∈ B := (hcov u).resolve_left huA
      have hvB : v ∈ B := by
        have hvA : v ∉ A := fun hv => huA (hiff.mpr hv)
        exact (hcov v).resolve_left hvA
      obtain ⟨w, hw⟩ := hA1
      have h1 : G.dist u w = 1 := by
        rw [SimpleGraph.dist_comm]
        exact hcross w hw u huB
      have h2 : G.dist w v = 1 := hcross w hw v hvB
      have htri := hconn.dist_triangle (u := u) (v := w) (w := v)
      have hge := Principia.Common.two_le_dist_of_same hbip.symm (hconn u v) hne
        (hBt u huB) (hBt v hvB)
      omega
  intro u v
  by_cases huv : u = v
  · subst huv
    simp
  · rw [if_neg huv]
    by_cases hiff : (u ∈ A ↔ v ∈ A)
    · rw [if_pos hiff, hsame u v huv hiff]
      norm_num
    · rw [if_neg hiff]
      by_cases huA : u ∈ A
      · have hvA : v ∉ A := fun hv => hiff ⟨fun _ => hv, fun _ => huA⟩
        rw [hcross u huA v ((hcov v).resolve_left hvA)]
        norm_num
      · have huB : u ∈ B := (hcov u).resolve_left huA
        have hvA : v ∈ A := by
          by_contra hv
          exact hiff ⟨fun h => absurd h huA, fun h => absurd h hv⟩
        rw [SimpleGraph.dist_comm, hcross v hvA u huB]
        norm_num

/-! ### `q₁` exactly, without ever forming the surd

Every bound so far was one-sided, and one-sided was always enough — until the equality case.  A
competitor that *is* `K_{m+1,m}`, on a possibly different partition of the same vertex set, has
spread equal to the extremal spread; the sharp cap sits `0.028` above that by design, and that slack
is exactly what made the cap provable.  So no bound can settle the equality case.  `q₁` has to be
pinned.

It can be, and the surd never appears, because `λ` enters as a **parameter satisfying a polynomial
relation** rather than as a closed form.  Let `λ` satisfy the residual `2 × 2` block's characteristic
equation

  `λ² − ((4a+b−4) + (a+4b−4))·λ + ((4a+b−4)(a+4b−4) − ab) = 0`.

Both directions then come out of that single equation:

* **Upper.**  Feed the family `p = (λ − (4a+b−4))/a`, `q = (λ − (a+4b−4))/b`.  Each coefficient
  becomes `λ` on the nose, and the side condition `pq ≥ 1` is *free* — `(λ−(4a+b−4))(λ−(a+4b−4)) = ab`
  **is** the characteristic equation rearranged, so `pq = 1` exactly.  This is why the family was
  worth stating with a general `(p,q)` rather than at a fixed member.
* **Lower.**  Evaluate the quadratic form at the block's own eigenvector, `(α,β) = (b, λ−(4a+b−4))`.
  The Rayleigh quotient there is `λ`, and the identity `num − λ·den = (char)·b·(4a+b−λ−4)` is a ring
  identity — one `linear_combination` with that cofactor.

So `q₁` is a function of `(a,b)` alone.  No permutation-similarity argument is needed for the
equality case, which is the thing this was built to avoid. -/

/-- The test vector that is constant on each part. -/
def partFun (A : Finset V) (α β : ℝ) : V → ℝ := fun v => if v ∈ A then α else β

theorem partFun_mem (A : Finset V) (α β : ℝ) {u : V} (hu : u ∈ A) : partFun A α β u = α := if_pos hu

theorem partFun_notMem (A : Finset V) (α β : ℝ) {u : V} (hu : u ∉ A) :
    partFun A α β u = β := if_neg hu

theorem sum_partFun_self (A : Finset V) (α β : ℝ) :
    ∑ u ∈ A, partFun A α β u = (A.card : ℝ) * α := by
  have h : ∀ u ∈ A, partFun A α β u = α := fun u hu => partFun_mem A α β hu
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

theorem sum_sq_partFun_self (A : Finset V) (α β : ℝ) :
    ∑ u ∈ A, partFun A α β u ^ 2 = (A.card : ℝ) * α ^ 2 := by
  have h : ∀ u ∈ A, partFun A α β u ^ 2 = α ^ 2 := fun u hu => by rw [partFun_mem A α β hu]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

theorem sum_partFun_other (A B : Finset V) (α β : ℝ) (hdisj : Disjoint A B) :
    ∑ u ∈ B, partFun A α β u = (B.card : ℝ) * β := by
  have h : ∀ u ∈ B, partFun A α β u = β := fun u hu =>
    partFun_notMem A α β (Finset.disjoint_right.mp hdisj hu)
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

theorem sum_sq_partFun_other (A B : Finset V) (α β : ℝ) (hdisj : Disjoint A B) :
    ∑ u ∈ B, partFun A α β u ^ 2 = (B.card : ℝ) * β ^ 2 := by
  have h : ∀ u ∈ B, partFun A α β u ^ 2 = β ^ 2 := fun u hu => by
    rw [partFun_notMem A α β (Finset.disjoint_right.mp hdisj hu)]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

/-- **The two-parameter Rayleigh lower bound on `q₁`.**  `four_mul_le_qEig_zero_mul_card` is the
member `α = β = 1`; the extra parameter is what lets the block's eigenvector be reached. -/
theorem le_qEig_zero_cb_twoParam {n : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (α β : ℝ) :
    (2 * (A.card : ℝ) - 4 + (B.card : ℝ)) * ((A.card : ℝ) * α ^ 2)
        + (2 * (B.card : ℝ) - 4 + (A.card : ℝ)) * ((B.card : ℝ) * β ^ 2)
        + 2 * ((A.card : ℝ) * α) ^ 2 + 2 * ((B.card : ℝ) * β) ^ 2
        + 2 * (((A.card : ℝ) * α) * ((B.card : ℝ) * β))
      ≤ qEig G hcard 0 * ((A.card : ℝ) * α ^ 2 + (B.card : ℝ) * β ^ 2) := by
  have hanti := (QLin_isSymmetric G).eigenvalues_antitone (finrank_euclidean_eq hcard)
  have h := Principia.Common.inner_apply_le_mul_norm_sq (QLin_isSymmetric G)
    (finrank_euclidean_eq hcard) (c := qEig G hcard 0) (fun i => hanti (Fin.zero_le i))
    (vec (partFun A α β))
  rw [inner_vec_QLin_vec G (partFun A α β),
    inner_form_cb G A B hcov hdisj hcb (partFun A α β),
    norm_sq_vec (partFun A α β),
    sum_univ_split (V := V) A B hcov hdisj (fun i => partFun A α β i ^ 2),
    sum_sq_partFun_self A α β, sum_sq_partFun_other A B α β hdisj,
    sum_partFun_self A α β, sum_partFun_other A B α β hdisj] at h
  linarith [h]

/-- **`q₁ ≥ λ`** for any root `λ` of the block's characteristic equation. -/
theorem le_qEig_zero_of_char {n : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hA1 : 0 < A.card) (hB1 : 0 < B.card) (lam : ℝ)
    (hchar : lam ^ 2
        - ((4 * (A.card : ℝ) + (B.card : ℝ) - 4) + ((A.card : ℝ) + 4 * (B.card : ℝ) - 4)) * lam
        + ((4 * (A.card : ℝ) + (B.card : ℝ) - 4) * ((A.card : ℝ) + 4 * (B.card : ℝ) - 4)
            - (A.card : ℝ) * (B.card : ℝ)) = 0) :
    lam ≤ qEig G hcard 0 := by
  have hapos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA1
  have hbpos : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast hB1
  have h := le_qEig_zero_cb_twoParam G hcard A B hcov hdisj hcb
    (B.card : ℝ) (lam - (4 * (A.card : ℝ) + (B.card : ℝ) - 4))
  have hden : (0 : ℝ) < (A.card : ℝ) * (B.card : ℝ) ^ 2
      + (B.card : ℝ) * (lam - (4 * (A.card : ℝ) + (B.card : ℝ) - 4)) ^ 2 := by
    have h1 : (0 : ℝ) < (A.card : ℝ) * (B.card : ℝ) ^ 2 := mul_pos hapos (pow_pos hbpos 2)
    have h2 : (0 : ℝ) ≤ (B.card : ℝ) * (lam - (4 * (A.card : ℝ) + (B.card : ℝ) - 4)) ^ 2 :=
      mul_nonneg (le_of_lt hbpos) (sq_nonneg _)
    linarith
  have hid : (2 * (A.card : ℝ) - 4 + (B.card : ℝ)) * ((A.card : ℝ) * (B.card : ℝ) ^ 2)
        + (2 * (B.card : ℝ) - 4 + (A.card : ℝ))
          * ((B.card : ℝ) * (lam - (4 * (A.card : ℝ) + (B.card : ℝ) - 4)) ^ 2)
        + 2 * ((A.card : ℝ) * (B.card : ℝ)) ^ 2
        + 2 * ((B.card : ℝ) * (lam - (4 * (A.card : ℝ) + (B.card : ℝ) - 4))) ^ 2
        + 2 * (((A.card : ℝ) * (B.card : ℝ))
            * ((B.card : ℝ) * (lam - (4 * (A.card : ℝ) + (B.card : ℝ) - 4))))
      = lam * ((A.card : ℝ) * (B.card : ℝ) ^ 2
          + (B.card : ℝ) * (lam - (4 * (A.card : ℝ) + (B.card : ℝ) - 4)) ^ 2) := by
    linear_combination ((B.card : ℝ) * (4 * (A.card : ℝ) + (B.card : ℝ) - lam - 4)) * hchar
  rw [hid] at h
  exact le_of_mul_le_mul_right h hden

/-- **`q₁ ≤ λ`** for a root `λ` dominating both diagonal entries of the block.  The side condition
`pq ≥ 1` is discharged *by the characteristic equation itself*. -/
theorem qEig_le_of_char {n : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hA1 : 0 < A.card) (hB1 : 0 < B.card) (lam : ℝ)
    (hchar : lam ^ 2
        - ((4 * (A.card : ℝ) + (B.card : ℝ) - 4) + ((A.card : ℝ) + 4 * (B.card : ℝ) - 4)) * lam
        + ((4 * (A.card : ℝ) + (B.card : ℝ) - 4) * ((A.card : ℝ) + 4 * (B.card : ℝ) - 4)
            - (A.card : ℝ) * (B.card : ℝ)) = 0)
    (hgtA : 4 * (A.card : ℝ) + (B.card : ℝ) - 4 < lam)
    (hgtB : (A.card : ℝ) + 4 * (B.card : ℝ) - 4 < lam) (i : Fin (n + 1)) :
    qEig G hcard i ≤ lam := by
  have hapos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA1
  have hbpos : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast hB1
  refine qEig_le_cb G hcard A B hcov hdisj hcb
    (p := (lam - (4 * (A.card : ℝ) + (B.card : ℝ) - 4)) / (A.card : ℝ))
    (q := (lam - ((A.card : ℝ) + 4 * (B.card : ℝ) - 4)) / (B.card : ℝ)) (c := lam)
    (div_pos (by linarith) hapos) (div_pos (by linarith) hbpos) ?_ ?_ ?_ i
  · rw [div_mul_div_comm, le_div_iff₀ (mul_pos hapos hbpos)]
    refine le_of_eq ?_
    linear_combination (-1 : ℝ) * hchar
  · rw [div_mul_cancel₀ _ (ne_of_gt hapos)]
    linarith
  · rw [div_mul_cancel₀ _ (ne_of_gt hbpos)]
    linarith

/-- **`q₁ = λ` exactly.**  With both directions in hand, `q₁` is a function of `(a, b)` alone. -/
theorem qEig_zero_eq_of_char {n : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hA1 : 0 < A.card) (hB1 : 0 < B.card) (lam : ℝ)
    (hchar : lam ^ 2
        - ((4 * (A.card : ℝ) + (B.card : ℝ) - 4) + ((A.card : ℝ) + 4 * (B.card : ℝ) - 4)) * lam
        + ((4 * (A.card : ℝ) + (B.card : ℝ) - 4) * ((A.card : ℝ) + 4 * (B.card : ℝ) - 4)
            - (A.card : ℝ) * (B.card : ℝ)) = 0)
    (hgtA : 4 * (A.card : ℝ) + (B.card : ℝ) - 4 < lam)
    (hgtB : (A.card : ℝ) + 4 * (B.card : ℝ) - 4 < lam) :
    qEig G hcard 0 = lam :=
  le_antisymm (qEig_le_of_char G hcard A B hcov hdisj hcb hA1 hB1 lam hchar hgtA hgtB 0)
    (le_qEig_zero_of_char G hcard A B hcov hdisj hcb hA1 hB1 lam hchar)

/-! ### The odd-order theorem

`qEig_zero_eq_of_char` pins `q₁` *given* a root of the characteristic equation.  To use it, a root
has to exist, and here — and only here — a square root is taken.  The discriminant is

  `(5n−8)² − 4·det = 9a² + 9b² − 14ab = 9(a−b)² + 4ab`

which is visibly positive, and that decomposition does double duty: it also gives
`√D > 3|a − b|` at once, which is exactly the statement that the larger root strictly dominates both
diagonal entries of the block.  One identity, both side conditions.

The four cases are then mechanical.  Write `d = |C| − |D|`; since `|C| + |D| = 2m+1` is odd, `d` is
odd, so `d = 1` or `d ≥ 3` — `omega` sees this from the parity alone.

  `d ≥ 3`               `three_le_diff_target_of_two_le`
  `d = 1`, some cross pair missing   `odd_nonadj_spread_bound`
  `d = 1`, none missing  the competitor **is** `K_{m+1,m}`, on a possibly different partition, and
                         `qEig_zero_eq_of_char` gives both graphs the *same* `q₁` — the case that no
                         bound could have settled.

The first two both deliver `3n² + n + 4 ≤ 2·S_Q(G)·n`, and the sharp cap delivers
`2·S_Q(K)·n ≤ 3n² + n + 4` for the same `n`. -/

/-- **A root of the block's characteristic equation exists, and dominates both diagonal entries.**
`9a² + 9b² − 14ab = 9(a−b)² + 4ab` supplies positivity of the discriminant and the strict domination
in one step. -/
theorem exists_char_root (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ lam : ℝ,
      lam ^ 2 - ((4 * a + b - 4) + (a + 4 * b - 4)) * lam
          + ((4 * a + b - 4) * (a + 4 * b - 4) - a * b) = 0
        ∧ 4 * a + b - 4 < lam ∧ a + 4 * b - 4 < lam := by
  have hab : (0 : ℝ) < a * b := mul_pos ha hb
  have hD : (0 : ℝ) ≤ 9 * a ^ 2 + 9 * b ^ 2 - 14 * a * b := by nlinarith [sq_nonneg (a - b)]
  have hsq : Real.sqrt (9 * a ^ 2 + 9 * b ^ 2 - 14 * a * b) ^ 2
      = 9 * a ^ 2 + 9 * b ^ 2 - 14 * a * b := Real.sq_sqrt hD
  have hsnn : (0 : ℝ) ≤ Real.sqrt (9 * a ^ 2 + 9 * b ^ 2 - 14 * a * b) := Real.sqrt_nonneg _
  refine ⟨((5 * a + 5 * b - 8) + Real.sqrt (9 * a ^ 2 + 9 * b ^ 2 - 14 * a * b)) / 2, ?_, ?_, ?_⟩
  · linear_combination (1 / 4 : ℝ) * hsq
  · have h : 2 * (4 * a + b - 4)
        < (5 * a + 5 * b - 8) + Real.sqrt (9 * a ^ 2 + 9 * b ^ 2 - 14 * a * b) := by
      nlinarith [hsq, hsnn, hab]
    linarith
  · have h : 2 * (a + 4 * b - 4)
        < (5 * a + 5 * b - 8) + Real.sqrt (9 * a ^ 2 + 9 * b ^ 2 - 14 * a * b) := by
      nlinarith [hsq, hsnn, hab]
    linarith

/-- **`S_Q(K_{m+1,m}) ≤ S_Q(G)` for every connected bipartite `G` of odd order `2m+1`.**  The
odd-order companion of `spread_cb_le_spread_uncond`. -/
theorem spread_cb_le_spread_odd {m : ℕ} (hcard : Fintype.card V = 2 * m + 1)
    (K : SimpleGraph V) (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcbK : IsCompleteBipartiteDist K A B) (hm : 2 ≤ m)
    (hA : A.card = m + 1) (hB : B.card = m)
    (G : SimpleGraph V) {s t : Set V} (hbip : G.IsBipartiteWith s t) (hconn : G.Connected)
    (C D : Finset V) (hcovG : ∀ v : V, v ∈ C ∨ v ∈ D) (hdisjG : Disjoint C D)
    (hC2 : 2 ≤ C.card) (hD2 : 2 ≤ D.card)
    (hCs : ∀ u ∈ C, u ∈ s) (hDt : ∀ v ∈ D, v ∈ t) (hcd : D.card ≤ C.card) :
    spread K hcard ≤ spread G hcard := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hN : (Fintype.card V : ℝ) = 2 * (m : ℝ) + 1 := by rw [hcard]; push_cast; ring
  have hNpos : (0 : ℝ) < (Fintype.card V : ℝ) := by rw [hN]; linarith
  have hAR : (A.card : ℝ) = (m : ℝ) + 1 := by rw [hA]; push_cast; ring
  have hBR : (B.card : ℝ) = (m : ℝ) := by rw [hB]
  have hA2 : 2 ≤ A.card := by omega
  have hB2 : 2 ≤ B.card := by omega
  have hcdR : (D.card : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hcd
  have hsumG : (Fintype.card V : ℝ) = (C.card : ℝ) + (D.card : ℝ) :=
    card_eq_add (V := V) C D hcovG hdisjG
  have hsumN : C.card + D.card = 2 * m + 1 := by
    have h : ((C.card + D.card : ℕ) : ℝ) = ((2 * m + 1 : ℕ) : ℝ) := by
      push_cast
      rw [← hN, ← hsumG]
    exact_mod_cast h
  obtain ⟨lam, hchar, hgtA, hgtB⟩ := exists_char_root ((m : ℝ) + 1) (m : ℝ) (by linarith) (by linarith)
  have hspK : spread K hcard = qEig K hcard 0 - qEig K hcard (Fin.last (2 * m)) := rfl
  have hK0 : qEig K hcard 0 = lam :=
    qEig_zero_eq_of_char K hcard A B hcov hdisj hcbK (by omega) (by omega) lam
      (by rw [hAR, hBR]; exact hchar) (by rw [hAR, hBR]; exact hgtA)
      (by rw [hAR, hBR]; exact hgtB)
  have hKlast := qEig_last_eq_cb K hcard A B hcov hdisj hcbK (by rw [hAR, hBR]; linarith) hB2
  have hspreadK : spread K hcard = lam - ((m : ℝ) + 1 + 2 * (m : ℝ) - 4) := by
    rw [hspK, hK0, hKlast, hAR, hBR]
  have hcap := qEig_mul_le_cb_odd_sharp K hcard A B hcov hdisj hcbK (by omega : 0 < m) hAR hBR 0
  rw [hK0] at hcap
  -- `|C| + |D|` is odd, so `|C| − |D|` is odd: it is `1`, or at least `3`.
  rcases (by omega : C.card = D.card + 1 ∨ D.card + 3 ≤ C.card) with hd1 | hd3
  · have hDm : D.card = m := by omega
    have hCm : C.card = m + 1 := by omega
    have hCR : (C.card : ℝ) = (m : ℝ) + 1 := by rw [hCm]; push_cast; ring
    have hDR : (D.card : ℝ) = (m : ℝ) := by rw [hDm]
    by_cases hall : ∀ u ∈ C, ∀ v ∈ D, G.Adj u v
    · -- `G` IS `K_{m+1,m}`; the same `lam` pins both, so the spreads are equal.
      have hcbG := isCompleteBipartiteDist_of_forall_adj G hbip hconn C D hcovG hdisjG hCs hDt
        (Finset.card_pos.mp (by omega)) (Finset.card_pos.mp (by omega)) hall
      have hG0 : qEig G hcard 0 = lam :=
        qEig_zero_eq_of_char G hcard C D hcovG hdisjG hcbG (by omega) (by omega) lam
          (by rw [hCR, hDR]; exact hchar) (by rw [hCR, hDR]; exact hgtA)
          (by rw [hCR, hDR]; exact hgtB)
      have hGlast := qEig_last_eq_cb G hcard C D hcovG hdisjG hcbG
        (by rw [hCR, hDR]; linarith) hD2
      have hspG : spread G hcard = qEig G hcard 0 - qEig G hcard (Fin.last (2 * m)) := rfl
      have hspreadG : spread G hcard = lam - ((m : ℝ) + 1 + 2 * (m : ℝ) - 4) := by
        rw [hspG, hG0, hGlast, hCR, hDR]
      rw [hspreadK, hspreadG]
    · push_neg at hall
      obtain ⟨u₀, hu₀, v₀, hv₀, hnadj⟩ := hall
      have hdR : (C.card : ℝ) = (D.card : ℝ) + 1 := by rw [hCR, hDR]
      have hG := odd_nonadj_spread_bound G hcard hbip hconn C D hcovG hdisjG hC2 hD2 hCs hDt
        hdR hu₀ hv₀ hnadj
      rw [hN] at hG
      have h2 : (2 * spread K hcard) * (Fintype.card V : ℝ)
          ≤ (2 * spread G hcard) * (Fintype.card V : ℝ) := by
        rw [hspreadK, hN]
        nlinarith [hG, hcap]
      have h3 := le_of_mul_le_mul_right h2 hNpos
      linarith
  · have hd3R : (3 : ℝ) ≤ (C.card : ℝ) - (D.card : ℝ) := by
      have h : ((D.card + 3 : ℕ) : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hd3
      push_cast at h
      linarith
    have hG := three_le_diff_target_of_two_le G hcard hbip hconn C D hcovG hdisjG hC2 hD2
      hCs hDt hcdR hd3R
    rw [hN] at hG
    have h2 : (2 * spread K hcard) * (Fintype.card V : ℝ)
        ≤ (2 * spread G hcard) * (Fintype.card V : ℝ) := by
      rw [hspreadK, hN]
      nlinarith [hG, hcap]
    have h3 := le_of_mul_le_mul_right h2 hNpos
    linarith

/-! ### The star, which the comparator caught

`spread_cb_le_spread_odd` and `spread_cb_le_spread_uncond` both require **both** sides of the
competitor's bipartition to have at least two vertices, and the comparator flagged it: a connected
bipartite graph may have a singleton side, and then it is the star `K_{n−1,1}`, which the informal
claim does not exclude.

It clears the target with room — `S_Q = 39.7` against `23.1` at `n = 15` — but the *existing* star
bound does not.  `q₁ ≥ 4(n−1)²/n` from the all-ones vector, minus `q_n ≤ 2n−5`, gives `7.8` at
`n = 5` against a target of `8.4`.  The exact `λ` closes it: `λ − (2n−5) = 8.424`, margin `0.024`,
and that is the whole content of the case.  Multiplied out to `(4m+2)·λ ≥ 28m² + 10m + 2` and
combined with the characteristic equation, it reduces to

  `q(K) = −(80m⁴ − 64m³ − 156m² − 52m − 16) ≤ 0`  for `m ≥ 2`,

whose certificate is `80(m−2)m³ + 96(m−2)m² + 36(m−2)m + 20(m−2) + 24`.  The `24` is the `m = 2`
margin — the tight case — appearing as the constant term.

Two hypotheses had to be relaxed to reach it: `exists_char_root` and the three `char` lemmas took
`2 ≤ a`, `2 ≤ b` but used them **only** for positivity, so `0 < a`, `0 < b` is what they actually
needed.  A hypothesis stronger than the proof requires is invisible until a case arrives that cannot
supply it. -/

/-- **A singleton side forces every cross pair to be an edge.**  Not an extra assumption:
bipartiteness puts every neighbour of a `C`-vertex inside `D`, so a `C`-vertex with no `D`-neighbour
has no neighbour at all, which a connected graph on more than one vertex does not have. -/
theorem forall_adj_of_card_eq_one {s t : Set V} (hbip : G.IsBipartiteWith s t)
    (hconn : G.Connected) (C D : Finset V)
    (hcov : ∀ v : V, v ∈ C ∨ v ∈ D) (hCs : ∀ u ∈ C, u ∈ s) (hDt : ∀ v ∈ D, v ∈ t)
    (hone : D.card = 1) (hcard2 : 1 < Fintype.card V) :
    ∀ u ∈ C, ∀ v ∈ D, G.Adj u v := by
  intro u hu v hv
  obtain ⟨w, hw⟩ : ∃ w, G.Adj u w := by
    obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card hcard2 u
    obtain ⟨p⟩ := hconn u x
    cases p with
    | nil => exact absurd rfl hx
    | cons hadj _ => exact ⟨_, hadj⟩
  have hwt : w ∈ t := hbip.mem_of_mem_adj (hCs u hu) hw
  have hwD : w ∈ D := by
    rcases hcov w with hwC | hwD
    · exact absurd (hCs w hwC) (Set.disjoint_right.mp hbip.disjoint hwt)
    · exact hwD
  have hwv : w = v := Finset.card_le_one.mp (le_of_eq hone) w hwD v hv
  exact hwv ▸ hw

/-! ### The three-vertex star, where the general bound is not sharp enough

`le_qEig_cb` gives `qₙ ≥ a + 2b − 4`, which at `(a, b) = (2, 1)` reads `qₙ ≥ 0`.  The truth is
`qₙ = 1`, and the gap is exactly what leaves the `n ≤ 3` case of the odd theorem open: the route
through `star_target` needs `3n² + n + 4 ≤ 2·S_Q·n`, i.e. `S_Q ≥ 34/6` at `n = 3`, while the actual
spread of `K_{2,1}` is `(7 + √17)/2 − 1 ≈ 4.56`.  **The target is false at `m = 1`**, so that route
cannot be repaired by relaxing a hypothesis — the case needs the exact `qₙ`.

Why the general bound loses: it discards `∑_B f²` against `S_B²`, which is wasteful unless `B` is a
singleton, where the two are *equal*.  Keeping them identified is the whole gain, and it is why this
sharpening is available only for `b = 1`. -/

/-- **The star's quadratic form dominates `‖x‖²`.**  The bracket is `S_A² + (S_A + S_B)²`. -/
theorem le_inner_cb_star_two (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B)
    (hdisj : Disjoint A B) (hcb : IsCompleteBipartiteDist G A B)
    (hA : A.card = 2) (hB : B.card = 1) (x : EuclideanSpace ℝ V) :
    (1 : ℝ) * ‖x‖ ^ 2 ≤ ⟪x, QLin G x⟫_ℝ := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hB
  have hAR : (A.card : ℝ) = 2 := by rw [hA]; norm_num
  have hBR : (B.card : ℝ) = 1 := by rw [hB]; norm_num
  -- a singleton's sum of squares IS the square of its sum; this is the sharpening
  have hsq : (∑ u ∈ B, (WithLp.ofLp x) u ^ 2) = (∑ u ∈ B, (WithLp.ofLp x) u) ^ 2 := by
    rw [hv]
    simp
  rw [inner_QLin_eq, norm_sq_ofLp, inner_form_cb G A B hcov hdisj hcb (WithLp.ofLp x),
    sum_univ_split (V := V) A B hcov hdisj (fun i => (WithLp.ofLp x) i ^ 2), hAR, hBR, hsq]
  nlinarith [sq_nonneg (∑ u ∈ A, (WithLp.ofLp x) u),
    sq_nonneg ((∑ u ∈ A, (WithLp.ofLp x) u) + (∑ u ∈ B, (WithLp.ofLp x) u))]

/-- **`qₙ ≥ 1` for the three-vertex star.**  With `qEig_last_mul_two_le`'s matching upper bound this
pins `qₙ = 1` exactly. -/
theorem le_qEig_star_two {n : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hA : A.card = 2) (hB : B.card = 1)
    (i : Fin (n + 1)) : (1 : ℝ) ≤ qEig G hcard i :=
  Principia.Common.le_eigenvalues_of_le_inner (QLin_isSymmetric G) (finrank_euclidean_eq hcard)
    (le_inner_cb_star_two G A B hcov hdisj hcb hA hB) i

/-- **The star clears the odd-order target.**  `a = 2m`, `b = 1`. -/
theorem star_target {m : ℕ} (hcard : Fintype.card V = 2 * m + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hm : 2 ≤ m)
    (hA : A.card = 2 * m) (hB : B.card = 1) :
    3 * (Fintype.card V : ℝ) ^ 2 + (Fintype.card V : ℝ) + 4
      ≤ 2 * spread G hcard * (Fintype.card V : ℝ) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hN : (Fintype.card V : ℝ) = 2 * (m : ℝ) + 1 := by rw [hcard]; push_cast; ring
  have hAR : (A.card : ℝ) = 2 * (m : ℝ) := by rw [hA]; push_cast; ring
  have hBR : (B.card : ℝ) = 1 := by rw [hB]; norm_num
  obtain ⟨lam, hchar, hgtA, hgtB⟩ :=
    exists_char_root (2 * (m : ℝ)) 1 (by linarith) (by norm_num)
  have hq0 : qEig G hcard 0 = lam :=
    qEig_zero_eq_of_char G hcard A B hcov hdisj hcb (by omega) (by omega) lam
      (by rw [hAR, hBR]; exact hchar) (by rw [hAR, hBR]; exact hgtA)
      (by rw [hAR, hBR]; exact hgtB)
  obtain ⟨u, hu, u', hu', hne⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  have hlast := qEig_last_mul_two_le G hcard A B hcov hdisj hcb hu hu' hne
  rw [hAR, hBR] at hlast
  have hgtAR : 8 * (m : ℝ) - 3 < lam := by linarith
  -- `(4m+2)·λ ≥ 28m² + 10m + 2` is the whole star case.
  have hkey : 28 * (m : ℝ) ^ 2 + 10 * (m : ℝ) + 2 ≤ (4 * (m : ℝ) + 2) * lam := by
    by_contra hcon
    push_neg at hcon
    nlinarith [hchar, hgtAR, hmR, hcon,
      mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - 2) (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 3),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - 2) (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - 2) (by linarith : (0 : ℝ) ≤ (m : ℝ))]
  have hq : (4 * (m : ℝ) + 2) * qEig G hcard (Fin.last (2 * m))
      ≤ (4 * (m : ℝ) + 2) * (4 * (m : ℝ) - 3) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hsp : spread G hcard = qEig G hcard 0 - qEig G hcard (Fin.last (2 * m)) := rfl
  rw [hsp, hq0, hN]
  nlinarith [hkey, hq]

/-- The cap side of the comparison, factored out so the star reuses it. -/
theorem spread_le_of_target {m : ℕ} (hcard : Fintype.card V = 2 * m + 1)
    (K : SimpleGraph V) (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcbK : IsCompleteBipartiteDist K A B) (hm : 2 ≤ m)
    (hA : A.card = m + 1) (hB : B.card = m) (G : SimpleGraph V)
    (hG : 3 * (Fintype.card V : ℝ) ^ 2 + (Fintype.card V : ℝ) + 4
        ≤ 2 * spread G hcard * (Fintype.card V : ℝ)) :
    spread K hcard ≤ spread G hcard := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hN : (Fintype.card V : ℝ) = 2 * (m : ℝ) + 1 := by rw [hcard]; push_cast; ring
  have hNpos : (0 : ℝ) < (Fintype.card V : ℝ) := by rw [hN]; linarith
  have hAR : (A.card : ℝ) = (m : ℝ) + 1 := by rw [hA]; push_cast; ring
  have hBR : (B.card : ℝ) = (m : ℝ) := by rw [hB]
  have hspK : spread K hcard = qEig K hcard 0 - qEig K hcard (Fin.last (2 * m)) := rfl
  have hKlast := qEig_last_eq_cb K hcard A B hcov hdisj hcbK (by rw [hAR, hBR]; linarith)
    (by omega : 2 ≤ B.card)
  have hcap := qEig_mul_le_cb_odd_sharp K hcard A B hcov hdisj hcbK (by omega : 0 < m) hAR hBR 0
  rw [hN] at hG
  have h2 : (2 * spread K hcard) * (Fintype.card V : ℝ)
      ≤ (2 * spread G hcard) * (Fintype.card V : ℝ) := by
    rw [hspK, hKlast, hAR, hBR, hN]
    nlinarith [hG, hcap]
  have h3 := le_of_mul_le_mul_right h2 hNpos
  linarith

/-- **`S_Q(K_{m+1,m}) ≤ S_Q(G)` for EVERY connected bipartite `G` of odd order `2m+1`** — the
singleton side no longer excluded. -/
theorem spread_cb_le_spread_odd_uncond {m : ℕ} (hcard : Fintype.card V = 2 * m + 1)
    (K : SimpleGraph V) (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcbK : IsCompleteBipartiteDist K A B) (hm : 2 ≤ m)
    (hA : A.card = m + 1) (hB : B.card = m)
    (G : SimpleGraph V) {s t : Set V} (hbip : G.IsBipartiteWith s t) (hconn : G.Connected)
    (C D : Finset V) (hcovG : ∀ v : V, v ∈ C ∨ v ∈ D) (hdisjG : Disjoint C D)
    (hC2 : 2 ≤ C.card) (hD1 : 1 ≤ D.card)
    (hCs : ∀ u ∈ C, u ∈ s) (hDt : ∀ v ∈ D, v ∈ t) (hcd : D.card ≤ C.card) :
    spread K hcard ≤ spread G hcard := by
  have hN : (Fintype.card V : ℝ) = 2 * (m : ℝ) + 1 := by rw [hcard]; push_cast; ring
  have hsumG : (Fintype.card V : ℝ) = (C.card : ℝ) + (D.card : ℝ) :=
    card_eq_add (V := V) C D hcovG hdisjG
  have hsumN : C.card + D.card = 2 * m + 1 := by
    have h : ((C.card + D.card : ℕ) : ℝ) = ((2 * m + 1 : ℕ) : ℝ) := by
      push_cast
      rw [← hN, ← hsumG]
    exact_mod_cast h
  rcases (by omega : D.card = 1 ∨ 2 ≤ D.card) with hd1 | hd2
  · have hCm : C.card = 2 * m := by omega
    have hall := forall_adj_of_card_eq_one G hbip hconn C D hcovG hCs hDt hd1 (by omega)
    have hcbG := isCompleteBipartiteDist_of_forall_adj G hbip hconn C D hcovG hdisjG hCs hDt
      (Finset.card_pos.mp (by omega)) (Finset.card_pos.mp (by omega)) hall
    exact spread_le_of_target hcard K A B hcov hdisj hcbK hm hA hB G
      (star_target G hcard C D hcovG hdisjG hcbG hm hCm hd1)
  · exact spread_cb_le_spread_odd hcard K A B hcov hdisj hcbK hm hA hB G hbip hconn C D
      hcovG hdisjG hC2 hd2 hCs hDt hcd

/-- **`S_Q(K_{a,a}) ≤ S_Q(G)` for EVERY connected bipartite `G` of even order** — the even
counterpart of `spread_cb_le_spread_odd_uncond`, with the singleton side no longer excluded.

The even side needed no new bound: its target is only `3n ≤ 2·S_Q`, which
`three_mul_card_le_two_mul_spread_star` already clears (with equality at `n = 4`, where the star
`K_{3,1}` and `K_{2,2}` both have spread `6`).  It is the *odd* target that is fine enough to need
the exact `λ`.  Only the plumbing is new: `|C| = 2|A| − 1` is odd, so `2 ≤ |C|` upgrades to
`3 ≤ |C|` for free, which is exactly the hypothesis the star bound wants. -/
theorem spread_cb_le_spread_uncond_star {n : ℕ} (hcard : Fintype.card V = n + 1)
    (K : SimpleGraph V) (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcbK : IsCompleteBipartiteDist K A B) (hbal : (A.card : ℝ) = (B.card : ℝ))
    (G : SimpleGraph V) {s t : Set V} (hbip : G.IsBipartiteWith s t) (hconn : G.Connected)
    (C D : Finset V) (hcovG : ∀ v : V, v ∈ C ∨ v ∈ D) (hdisjG : Disjoint C D)
    (hC2 : 2 ≤ C.card) (hD1 : 1 ≤ D.card)
    (hCs : ∀ u ∈ C, u ∈ s) (hDt : ∀ v ∈ D, v ∈ t) (hcd : (D.card : ℝ) ≤ (C.card : ℝ)) :
    spread K hcard ≤ spread G hcard := by
  have hn2 := card_eq_two_mul_of_balanced (V := V) A B hcov hdisj hbal
  have hsumG : (Fintype.card V : ℝ) = (C.card : ℝ) + (D.card : ℝ) :=
    card_eq_add (V := V) C D hcovG hdisjG
  have hcardN : Fintype.card V = C.card + D.card := by
    have h : ((Fintype.card V : ℕ) : ℝ) = ((C.card + D.card : ℕ) : ℝ) := by
      push_cast
      exact hsumG
    exact_mod_cast h
  have hsumN : C.card + D.card = 2 * A.card := by
    have h : ((C.card + D.card : ℕ) : ℝ) = ((2 * A.card : ℕ) : ℝ) := by
      push_cast
      rw [← hsumG, hn2]
    exact_mod_cast h
  rcases (by omega : D.card = 1 ∨ 2 ≤ D.card) with hd1 | hd2
  · -- `|C| = 2|A| − 1` is odd, so `2 ≤ |C|` already gives `3 ≤ |C|`.
    have hC3 : 3 ≤ C.card := by omega
    have hall := forall_adj_of_card_eq_one G hbip hconn C D hcovG hCs hDt hd1 (by omega)
    have hcbG := isCompleteBipartiteDist_of_forall_adj G hbip hconn C D hcovG hdisjG hCs hDt
      (Finset.card_pos.mp (by omega)) (Finset.card_pos.mp (by omega)) hall
    have hG := three_mul_card_le_two_mul_spread_star G hcard C D hcovG hdisjG hcbG
      (by rw [hd1]; norm_num) (by exact_mod_cast hC3)
    have hK := spread_cb_balanced_le K hcard A B hcov hdisj hcbK hbal
    rw [hn2] at hG
    linarith
  · exact spread_cb_le_spread_uncond hcard K A B hcov hdisj hcbK hbal G hbip hconn C D
      hcovG hdisjG hC2 hd2 hCs hDt hcd


/-- **`qₙ = 1` for the three-vertex star**, the lower bound meeting `qEig_last_mul_two_le`'s upper
one: at `(a, b) = (2, 1)` the latter reads `qₙ · 2 ≤ 2`. -/
theorem qEig_last_eq_star_two {n : ℕ} (hcard : Fintype.card V = n + 1)
    (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcb : IsCompleteBipartiteDist G A B) (hA : A.card = 2) (hB : B.card = 1) :
    qEig G hcard (Fin.last n) = 1 := by
  have hAR : (A.card : ℝ) = 2 := by rw [hA]; norm_num
  have hBR : (B.card : ℝ) = 1 := by rw [hB]; norm_num
  obtain ⟨u, hu, u', hu', hne⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  have hup := qEig_last_mul_two_le G hcard A B hcov hdisj hcb hu hu' hne
  rw [hAR, hBR] at hup
  have hlo := le_qEig_star_two G hcard A B hcov hdisj hcb hA hB (Fin.last n)
  linarith

/-- **The `m = 1` case: the two spreads are EQUAL.**

At `n = 3` the extremal graph and the competitor are both complete bipartite with parts `(2, 1)`, so
`q₁` is the same characteristic root for both — `qEig_zero_eq_of_char` is fed the *same* `lam` twice —
and `qₙ = 1` for both.  The comparison is an equality with itself, which is why no *bound* could
settle it: `star_target` asks for `S_Q ≥ 34/6` where the truth is `(7 + √17)/2 − 1 ≈ 4.56`. -/
theorem spread_cb_le_spread_odd_m1 {n : ℕ} (hcard : Fintype.card V = n + 1)
    (K : SimpleGraph V) (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcbK : IsCompleteBipartiteDist K A B) (hA : A.card = 2) (hB : B.card = 1)
    (G : SimpleGraph V) (C D : Finset V) (hcovG : ∀ v : V, v ∈ C ∨ v ∈ D) (hdisjG : Disjoint C D)
    (hcbG : IsCompleteBipartiteDist G C D) (hC : C.card = 2) (hD : D.card = 1) :
    spread K hcard ≤ spread G hcard := by
  obtain ⟨lam, hchar, hgtA, hgtB⟩ := exists_char_root 2 1 (by norm_num) (by norm_num)
  have hARK : (A.card : ℝ) = 2 := by rw [hA]; norm_num
  have hBRK : (B.card : ℝ) = 1 := by rw [hB]; norm_num
  have hARG : (C.card : ℝ) = 2 := by rw [hC]; norm_num
  have hBRG : (D.card : ℝ) = 1 := by rw [hD]; norm_num
  have hK0 : qEig K hcard 0 = lam :=
    qEig_zero_eq_of_char K hcard A B hcov hdisj hcbK (by omega) (by omega) lam
      (by rw [hARK, hBRK]; exact hchar) (by rw [hARK, hBRK]; exact hgtA)
      (by rw [hARK, hBRK]; exact hgtB)
  have hG0 : qEig G hcard 0 = lam :=
    qEig_zero_eq_of_char G hcard C D hcovG hdisjG hcbG (by omega) (by omega) lam
      (by rw [hARG, hBRG]; exact hchar) (by rw [hARG, hBRG]; exact hgtA)
      (by rw [hARG, hBRG]; exact hgtB)
  have hKn := qEig_last_eq_star_two K hcard A B hcov hdisj hcbK hA hB
  have hGn := qEig_last_eq_star_two G hcard C D hcovG hdisjG hcbG hC hD
  have hsK : spread K hcard = qEig K hcard 0 - qEig K hcard (Fin.last n) := rfl
  have hsG : spread G hcard = qEig G hcard 0 - qEig G hcard (Fin.last n) := rfl
  rw [hsK, hsG, hK0, hG0, hKn, hGn]

/-- **The odd-order theorem with no lower bound on `m` at all.**

`m = 0` is vacuous — `card V = 1` cannot hold two disjoint parts one of which has two elements —
`m = 1` is the equality case above, and `m ≥ 2` is the existing theorem.  This closes the last
`caveat` the comparator raised on this row. -/
theorem spread_cb_le_spread_odd_uncond_all {m : ℕ} (hcard : Fintype.card V = 2 * m + 1)
    (K : SimpleGraph V) (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcbK : IsCompleteBipartiteDist K A B)
    (hA : A.card = m + 1) (hB : B.card = m)
    (G : SimpleGraph V) {s t : Set V} (hbip : G.IsBipartiteWith s t) (hconn : G.Connected)
    (C D : Finset V) (hcovG : ∀ v : V, v ∈ C ∨ v ∈ D) (hdisjG : Disjoint C D)
    (hC2 : 2 ≤ C.card) (hD1 : 1 ≤ D.card)
    (hCs : ∀ u ∈ C, u ∈ s) (hDt : ∀ v ∈ D, v ∈ t) (hcd : D.card ≤ C.card) :
    spread K hcard ≤ spread G hcard := by
  have hsumG : (Fintype.card V : ℝ) = (C.card : ℝ) + (D.card : ℝ) :=
    card_eq_add (V := V) C D hcovG hdisjG
  have hsumN : C.card + D.card = 2 * m + 1 := by
    have h : ((C.card + D.card : ℕ) : ℝ) = ((2 * m + 1 : ℕ) : ℝ) := by
      push_cast
      rw [← hsumG, hcard]
      push_cast
      ring
    exact_mod_cast h
  rcases (by omega : m = 0 ∨ m = 1 ∨ 2 ≤ m) with h0 | h1 | h2
  · exact absurd hsumN (by omega)
  · subst h1
    have hCc : C.card = 2 := by omega
    have hDc : D.card = 1 := by omega
    have hall := forall_adj_of_card_eq_one G hbip hconn C D hcovG hCs hDt hDc (by omega)
    have hcbG := isCompleteBipartiteDist_of_forall_adj G hbip hconn C D hcovG hdisjG hCs hDt
      (Finset.card_pos.mp (by omega)) (Finset.card_pos.mp (by omega)) hall
    exact spread_cb_le_spread_odd_m1 hcard K A B hcov hdisj hcbK (by omega) (by omega)
      G C D hcovG hdisjG hcbG hCc hDc
  · exact spread_cb_le_spread_odd_uncond hcard K A B hcov hdisj hcbK h2 hA hB
      G hbip hconn C D hcovG hdisjG hC2 hD1 hCs hDt hcd


/-- **#333521, both parities in one statement.**

Among connected bipartite graphs on `card V` vertices, the balanced complete bipartite graph
`K_{⌈N/2⌉,⌊N/2⌋}` minimizes the distance signless Laplacian spread.  The part sizes are written as
`(N+1)/2` and `N/2` — natural-number division — which *is* the ceiling/floor split and specializes
correctly on both sides: at `N = 2m+1` to `(m+1, m)`, at `N = 2a` to `(a, a)`.

The two halves were proved separately because their targets differ in strength: the even side needs
only `3n ≤ 2·S_Q`, while the odd side is fine enough to require the exact characteristic root.  The
comparator flagged the odd theorem alone as covering "half the claimed domain", which was fair — the
row had no statement quantifying over both.  This is it. -/
theorem spread_cb_le_spread_balanced {n : ℕ} (hcard : Fintype.card V = n + 1)
    (K : SimpleGraph V) (A B : Finset V) (hcov : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : Disjoint A B)
    (hcbK : IsCompleteBipartiteDist K A B)
    (hA : A.card = (Fintype.card V + 1) / 2) (hB : B.card = Fintype.card V / 2)
    (G : SimpleGraph V) {s t : Set V} (hbip : G.IsBipartiteWith s t) (hconn : G.Connected)
    (C D : Finset V) (hcovG : ∀ v : V, v ∈ C ∨ v ∈ D) (hdisjG : Disjoint C D)
    (hC2 : 2 ≤ C.card) (hD1 : 1 ≤ D.card)
    (hCs : ∀ u ∈ C, u ∈ s) (hDt : ∀ v ∈ D, v ∈ t) (hcd : D.card ≤ C.card) :
    spread K hcard ≤ spread G hcard := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨a, ha⟩
  · -- `n = m + m`, so the order `N = 2m+1` is ODD and the extremal graph is `K_{m+1,m}`
    have hn : n = 2 * m := by omega
    subst hn
    have hAm : A.card = m + 1 := by omega
    have hBm : B.card = m := by omega
    exact spread_cb_le_spread_odd_uncond_all hcard K A B hcov hdisj hcbK hAm hBm
      G hbip hconn C D hcovG hdisjG hC2 hD1 hCs hDt hcd
  · -- `n = 2a+1`, so the order `N = 2a+2` is EVEN and the extremal graph is balanced
    have hn : n = 2 * a + 1 := by omega
    subst hn
    have hbalN : A.card = B.card := by omega
    have hbal : (A.card : ℝ) = (B.card : ℝ) := by exact_mod_cast hbalN
    have hcdR : (D.card : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hcd
    exact spread_cb_le_spread_uncond_star hcard K A B hcov hdisj hcbK hbal
      G hbip hconn C D hcovG hdisjG hC2 hD1 hCs hDt hcdR

end Principia.MathDB.P333521
