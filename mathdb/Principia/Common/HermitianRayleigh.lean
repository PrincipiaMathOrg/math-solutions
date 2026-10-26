/-
Copyright (c) 2026 Principia. All rights reserved.
Released under Apache 2.0.
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Rayleigh bounds from the eigenvalues of a symmetric operator

Mathlib proves the spectral theorem for symmetric operators and supplies an orthonormal
eigenvector basis, and separately develops the Rayleigh quotient with `⨆`/`⨅` over the whole
space for a `ContinuousLinearMap` — but the two never meet.  Checked against the pinned tree on
2026-08-22, there is **no** statement anywhere in Mathlib of the form "the least eigenvalue is at
most `⟪x, T x⟫ / ‖x‖²`": `Analysis/Matrix/Spectrum.lean` and
`Analysis/InnerProductSpace/Spectrum.lean` give diagonalisation without any inequality, and
`Analysis/InnerProductSpace/Rayleigh.lean` gives an inequality with no link to `eigenvalues`.
Grepping `eigenvalues` against `dotProduct|inner|mulVec|rayleigh|quadratic` across all of Mathlib
returns only `IsPositive.nonneg_eigenvalues` and singular-value material.

This file supplies the bridge.  The bounds are stated against **any** uniform bound on the
eigenvalues rather than as an `⨅`/`⨆`, because a caller normally has a specific candidate for the
extreme eigenvalue, and that form needs no `Nonempty` hypothesis and composes without extracting a
witness from an infimum.

Everything rests on one expansion, `inner_apply_eq_sum`: in the eigenbasis the quadratic form is
`∑ λᵢ tᵢ²` with `tᵢ = ⟪bᵢ, x⟫`, while `‖x‖² = ∑ tᵢ²`.  Both bounds are then termwise, since
`tᵢ² ≥ 0`.  Note this is exactly why the hypothesis needs no ordering on the eigenvalues: the
comparison happens coefficient by coefficient.

Campaign-agnostic: nothing here mentions graphs, distances, or any particular operator.
-/

set_option autoImplicit false

namespace Principia.Common

open Finset
-- `⟪ x, y ⟫_ℝ` lives in the `InnerProductSpace` scope.  `RealInnerProductSpace` rebinds the
-- UNSUFFIXED bracket to ℝ and does not provide the suffixed form — opening it instead makes every
-- statement below a parse error, reported as "unexpected identifier" at the signature.
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {T : E →ₗ[ℝ] E} {n : ℕ}

/-- **The quadratic form, diagonalised.**  In the eigenbasis, `⟪x, T x⟫ = ∑ λᵢ ⟪bᵢ, x⟫²`. -/
theorem inner_apply_eq_sum (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = n) (x : E) :
    ⟪x, T x⟫_ℝ
      = ∑ i, hT.eigenvalues hn i * ⟪hT.eigenvectorBasis hn i, x⟫_ℝ ^ 2 := by
  rw [← OrthonormalBasis.sum_inner_mul_inner (hT.eigenvectorBasis hn) x (T x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ⟪hT.eigenvectorBasis hn i, T x⟫_ℝ
      = hT.eigenvalues hn i * ⟪hT.eigenvectorBasis hn i, x⟫_ℝ := by
    -- `apply_eigenvectorBasis` states the scalar coerced into the field; at the reals that
    -- coercion is `RCLike.ofReal`, the identity but not syntactically so, which leaves
    -- `↑λ * … = λ * …`.  `norm_cast` closes exactly that.
    rw [← hT (hT.eigenvectorBasis hn i) x, hT.apply_eigenvectorBasis hn i, real_inner_smul_left]
    norm_cast
  rw [h1, real_inner_comm x (hT.eigenvectorBasis hn i)]
  ring

/-- **Parseval, in the same coordinates.**  `‖x‖² = ∑ ⟪bᵢ, x⟫²`. -/
theorem norm_sq_eq_sum (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = n) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ⟪hT.eigenvectorBasis hn i, x⟫_ℝ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq,
    ← OrthonormalBasis.sum_inner_mul_inner (hT.eigenvectorBasis hn) x x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm x (hT.eigenvectorBasis hn i)]
  ring

/-- **Lower Rayleigh bound.**  If every eigenvalue is at least `c`, the quadratic form dominates
`c‖x‖²`.  Taking `c` to be the least eigenvalue gives `qₙ ≤ ⟪x, T x⟫` for every unit `x`. -/
theorem mul_norm_sq_le_inner_apply (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = n) {c : ℝ}
    (h : ∀ i, c ≤ hT.eigenvalues hn i) (x : E) : c * ‖x‖ ^ 2 ≤ ⟪x, T x⟫_ℝ := by
  rw [inner_apply_eq_sum hT hn x, norm_sq_eq_sum hT hn x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (sq_nonneg _)

/-- **Upper Rayleigh bound.**  Dual to the above; taking `c` to be the greatest eigenvalue gives
`⟪x, T x⟫ ≤ q₁` for every unit `x`, which is the form that bounds `q₁` from below by evaluating at
a convenient vector. -/
theorem inner_apply_le_mul_norm_sq (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = n) {c : ℝ}
    (h : ∀ i, hT.eigenvalues hn i ≤ c) (x : E) : ⟪x, T x⟫_ℝ ≤ c * ‖x‖ ^ 2 := by
  rw [inner_apply_eq_sum hT hn x, norm_sq_eq_sum hT hn x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (sq_nonneg _)

/-- **The general summed form: no normalisation at all.**  If every eigenvalue is at least `c`,
then `c * ∑ ‖vⱼ‖²` is at most `∑ ⟪vⱼ, T vⱼ⟫` over any finite family of vectors whatsoever.

This is `mul_norm_sq_le_inner_apply` summed, and `mul_card_le_sum_inner_apply` below is now derived
from it rather than proved separately.  Dropping the unit-vector hypothesis is not cosmetic: a
caller testing against differences `eᵤ - eᵥ` would otherwise divide each by `√2`, carrying an
irrational scalar and its `≠ 0` side conditions through an argument that never needed them.  Here
`∑ ‖vⱼ‖²` is simply computed, and it comes out an integer. -/
theorem mul_sum_norm_sq_le_sum_inner_apply (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = n)
    {c : ℝ} (h : ∀ i, c ≤ hT.eigenvalues hn i) {ι : Type*} (t : Finset ι) (v : ι → E) :
    c * ∑ j ∈ t, ‖v j‖ ^ 2 ≤ ∑ j ∈ t, ⟪v j, T (v j)⟫_ℝ := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => mul_norm_sq_le_inner_apply hT hn h (v j)

/-- **The summed form, which is what a subspace bound actually needs.**  If every eigenvalue is at
least `c`, then `c * |t|` is at most the total of `⟪vⱼ, T vⱼ⟫` over any finite family of unit
vectors.

Two deliberate choices.  It is stated **summed rather than averaged**, so there is no division and
no `Nonempty` hypothesis — on the empty family both sides are `0` — and a caller who wants the
average divides.  And **orthogonality is not required**, only that each vector is a unit vector,
which is strictly weaker than the Courant–Fischer hypotheses usually quoted for this step.

The reason orthogonality drops out is worth stating, because it is what transfers: the expansion
makes the comparison *termwise*, so each test vector is bounded independently and then summed, and
summing preserves a uniform bound regardless of any relation between the things summed.
Courant–Fischer needs orthogonality because it computes an exact min-max; a one-sided bound does
not. -/
theorem mul_card_le_sum_inner_apply (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = n) {c : ℝ}
    (h : ∀ i, c ≤ hT.eigenvalues hn i) {ι : Type*} (t : Finset ι)
    (v : ι → E) (hv : ∀ j ∈ t, ‖v j‖ = 1) :
    c * t.card ≤ ∑ j ∈ t, ⟪v j, T (v j)⟫_ℝ := by
  have hone : ∀ j ∈ t, ‖v j‖ ^ 2 = 1 := fun j hj => by rw [hv j hj, one_pow]
  have hsum : ∑ j ∈ t, ‖v j‖ ^ 2 = (t.card : ℝ) := by
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hgen := mul_sum_norm_sq_le_sum_inner_apply hT hn h t v
  rwa [hsum] at hgen

/-! ### The converse direction: a quadratic-form bound IS an eigenvalue bound

The two bounds above go from eigenvalues to the quadratic form.  The converse is what a caller
needs when the eigenvalues are the *unknown*: to bound an extreme eigenvalue of a specific operator,
it is far cheaper to bound `⟪x, T x⟫` uniformly than to exhibit an eigenbasis.

Both directions are one line each from `apply_eigenvectorBasis`, because an eigenvector of unit
norm turns the quadratic form into the eigenvalue itself.  Together with the pair above they say
that `⨆ᵢ λᵢ` and `⨅ᵢ λᵢ` are *exactly* the extremes of the Rayleigh quotient — but stated as four
implications rather than two suprema, so no `Nonempty` hypothesis and no witness extraction is ever
needed.

**Why this matters more than the convenience.**  Computing the extreme eigenvalues of a structured
matrix normally means diagonalising it — for a complete bipartite distance operator, exhibiting the
zero-sum eigenspaces of each part and then diagonalising a residual `2 × 2` block.  With these
lemmas the same information follows from two inequalities on `⟪x, T x⟫`, which are polynomial
identities in the coordinates of `x`.  That is the same trade that removed the orthonormal basis
from the `qₙ` bound: **a one-sided bound never needs the basis that an exact diagonalisation does.** -/

/-- **A uniform upper bound on the quadratic form bounds every eigenvalue.**  Converse of
`inner_apply_le_mul_norm_sq`. -/
theorem eigenvalues_le_of_inner_le (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = n) {c : ℝ}
    (h : ∀ x, ⟪x, T x⟫_ℝ ≤ c * ‖x‖ ^ 2) (i : Fin n) : hT.eigenvalues hn i ≤ c := by
  have hnorm : ‖hT.eigenvectorBasis hn i‖ = 1 := (hT.eigenvectorBasis hn).orthonormal.1 i
  have hi := h (hT.eigenvectorBasis hn i)
  rw [hT.apply_eigenvectorBasis hn i, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hnorm] at hi
  norm_num at hi
  exact_mod_cast hi

/-- **A uniform lower bound on the quadratic form bounds every eigenvalue below.**  Converse of
`mul_norm_sq_le_inner_apply`. -/
theorem le_eigenvalues_of_le_inner (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = n) {c : ℝ}
    (h : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, T x⟫_ℝ) (i : Fin n) : c ≤ hT.eigenvalues hn i := by
  have hnorm : ‖hT.eigenvectorBasis hn i‖ = 1 := (hT.eigenvectorBasis hn).orthonormal.1 i
  have hi := h (hT.eigenvectorBasis hn i)
  rw [hT.apply_eigenvectorBasis hn i, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hnorm] at hi
  norm_num at hi
  exact_mod_cast hi

end Principia.Common
