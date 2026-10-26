import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# MathDB #364187 -- monotonicity of the signature of a mixed graph matrix

Write-up `mathdb-open-problems/problems/364187/solution.tex`,
*Monotonicity of the signature of a mixed graph matrix*, 22 September 2026.
Source: R. Bonetto and H. Jardon Kojakhmetov, *On the Eigenvalues of Graphs with Mixed
Algebraic Structure*, arXiv:2408.00487v1 (2024), Definition 3 and **Conjecture 1**; retained
as Conjecture 3.1.1 in R. Bonetto, *Oscillations and diffusion in dynamic networks models*,
University of Groningen PhD thesis (2025).

Conjecture 1 concerns a simple graph `F` whose edges are split between spanning subgraphs
`G` and `H`, and the pencil `M(eps) = L_G + eps * A_H` for `eps > 0`: its signature is
claimed to be decreasing.  The write-up proves the general statement announced immediately
after the conjecture in the source -- for real symmetric `A >= 0` and `B`, the inertia of
`A + tB` is monotone in `t > 0`.

**What is proved.**  `sigPos_anti`, `sigNeg_mono` and `sig_anti` are that general theorem,
for quadratic forms on any finite-dimensional real vector space (which contains the
symmetric-matrix case).  `conj1` and `conj1_counts` are Conjecture 1 itself, for the
Laplacian-plus-adjacency pencil of an arbitrary pair of graphs on one vertex set.  Nothing is
assumed: every declaration is unconditional.

**The proof needs no normalization.**  The write-up divides by the parameter and compares
`N(u) - N(v) = (1/u - 1/v) A >= 0`.  That step is unnecessary once the argument is run on
the subspaces directly: if `A + vB` is positive definite on `V`, then for `0 < u < v`

  `v * (A + uB)(x) = (v - u) * A(x) + u * (A + vB)(x) > 0`,

a nonnegative term plus a positive one, so `A + uB` is positive definite on the SAME `V`
(`posDef_of_lt`).  The negative side is even shorter: `A + uB < 0` and `A >= 0` force
`B(x) < 0`, and then `(v - u) B(x) < 0` pushes `A + vB` further down (`negDef_of_lt`).
Maximizing over `V` gives the two count inequalities.

**Why Mathlib's `sigPos` is the right object.**  `QuadraticForm.sigPos Q` is *defined* as the
maximal `finrank` of a subspace on which `Q` is positive definite -- which is exactly the
characterization the source's own Lemma establishes and then uses for the whole proof.  So
the two inertia counts here are the variational ones, and `sig = sigPos - sigNeg`.  Their
identification with the multiplicities of the positive and negative eigenvalues is Sylvester's
law of inertia; Mathlib carries its uniqueness half
(`QuadraticForm.sigPos_of_equiv_weightedSumSquares`), but the bridge from
`Matrix.IsHermitian.spectral_theorem` to a weighted sum of squares is not built here, so this
module never mentions an eigenvalue.  That identification is classical and is the source's
own first sentence, not a step of its argument.

**Generality beyond the source.**  The source's `G` and `H` partition the edges of a common
`F`.  That hypothesis is never used: `conj1` quantifies over every pair of graphs on the
vertex set, so the source's family is contained in it.  Likewise `sig_anti` holds on any
finite-dimensional real space, not only `V -> R`.

Values checked first in `Campaigns/MathDB-Formalization/verify_364187.py`, which computes
inertia EXACTLY (real-rooted characteristic polynomials make Descartes' rule an equality, so
no floating point enters): the general pencil on random rational instances, every `(F, G, H)`
partition on at most four vertices (759 of them), a counterexample showing the hypothesis
`A >= 0` is load-bearing, and a case where the inertia is constant -- the source's
"decreasing" means nonincreasing.
-/

namespace Principia.MathDB.P364187

open QuadraticMap QuadraticForm

variable {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]

/-- The pencil `M(t) = A + t B`, as a quadratic form. -/
def pen (QA QB : QuadraticForm ℝ M) (t : ℝ) : QuadraticForm ℝ M := QA + t • QB

omit [FiniteDimensional ℝ M] in
@[simp] theorem pen_apply (QA QB : QuadraticForm ℝ M) (t : ℝ) (x : M) :
    pen QA QB t x = QA x + t * QB x := by
  simp [pen]

omit [FiniteDimensional ℝ M] in
/-- Positive-definiteness on a subspace descends from the larger parameter to the
smaller one.  This is the whole content: `A + uB = (1 - u/v) A + (u/v)(A + vB)`, a sum of
a nonnegative term and a positive one. -/
theorem posDef_of_lt (QA QB : QuadraticForm ℝ M) (hA : ∀ x, 0 ≤ QA x)
    {V : Submodule ℝ M} {u v : ℝ} (hu : 0 < u) (huv : u < v)
    (h : ((pen QA QB v).restrict V).PosDef) :
    ((pen QA QB u).restrict V).PosDef := by
  intro x hx
  have hv : 0 < QA (x : M) + v * QB (x : M) := by
    have := h x hx
    simpa using this
  have hAx : 0 ≤ QA (x : M) := hA _
  have hvpos : 0 < v := lt_trans hu huv
  have hkey : 0 < v * (QA (x : M) + u * QB (x : M)) := by nlinarith
  have : 0 < QA (x : M) + u * QB (x : M) := by nlinarith
  simpa using this

omit [FiniteDimensional ℝ M] in
/-- Negative-definiteness on a subspace ascends from the smaller parameter to the larger. -/
theorem negDef_of_lt (QA QB : QuadraticForm ℝ M) (hA : ∀ x, 0 ≤ QA x)
    {V : Submodule ℝ M} {u v : ℝ} (hu : 0 < u) (huv : u < v)
    (h : ((-pen QA QB u).restrict V).PosDef) :
    ((-pen QA QB v).restrict V).PosDef := by
  intro x hx
  have hu' : QA (x : M) + u * QB (x : M) < 0 := by
    have := h x hx
    simp only [restrict_apply, QuadraticMap.neg_apply, pen_apply] at this
    linarith
  have hAx : 0 ≤ QA (x : M) := hA _
  have hb : QB (x : M) < 0 := by nlinarith
  have hprod : (v - u) * QB (x : M) < 0 := mul_neg_of_pos_of_neg (by linarith) hb
  have : QA (x : M) + v * QB (x : M) < 0 := by nlinarith
  simp only [restrict_apply, QuadraticMap.neg_apply, pen_apply]
  linarith

/-- **The positive inertia count is nonincreasing in the parameter.** -/
theorem sigPos_anti (QA QB : QuadraticForm ℝ M) (hA : ∀ x, 0 ≤ QA x) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    sigPos (pen QA QB v) ≤ sigPos (pen QA QB u) := by
  obtain ⟨V, hrank, hpd⟩ := exists_finrank_eq_sigPos_and_posDef (pen QA QB v)
  rw [← hrank]
  exact le_sigPos_of_posDef _ (posDef_of_lt QA QB hA hu huv hpd)

/-- **The negative inertia count is nondecreasing in the parameter.** -/
theorem sigNeg_mono (QA QB : QuadraticForm ℝ M) (hA : ∀ x, 0 ≤ QA x) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    sigNeg (pen QA QB u) ≤ sigNeg (pen QA QB v) := by
  obtain ⟨V, hrank, hnd⟩ := exists_finrank_eq_sigNeg_and_negDef (pen QA QB u)
  rw [← hrank]
  exact le_sigNeg_of_negDef _ (negDef_of_lt QA QB hA hu huv hnd)

/-- The signature `s(Q) = n_+(Q) - n_-(Q)`. -/
noncomputable def sig (Q : QuadraticForm ℝ M) : ℤ := (sigPos Q : ℤ) - (sigNeg Q : ℤ)

/-- **The source's Conjecture 1, in the generality of its own Theorem.** -/
theorem sig_anti (QA QB : QuadraticForm ℝ M) (hA : ∀ x, 0 ≤ QA x) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    sig (pen QA QB v) ≤ sig (pen QA QB u) := by
  have h1 := sigPos_anti QA QB hA hu huv
  have h2 := sigNeg_mono QA QB hA hu huv
  simp only [sig]
  omega

/-! ### The source's Conjecture 1: a graph Laplacian against an adjacency matrix

Definition 3 of the source splits the edges of a simple graph `F` between spanning subgraphs
`G` and `H` and sets `M(eps) = L_G + eps * A_H`.  The partition hypothesis is never used
below -- the statement holds for EVERY pair `(G, H)` on the same vertex set, which contains
the source's family. -/

variable {V : Type*} [Fintype V] [DecidableEq V]

open SimpleGraph Matrix

/-- The Laplacian quadratic form is nonnegative: it is a sum of squares. -/
theorem lap_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
    0 ≤ (G.lapMatrix ℝ).toQuadraticForm' x := by
  rw [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    SimpleGraph.lapMatrix_toLinearMap₂']
  positivity

/-- The source's pencil `M(eps) = L_G + eps * A_H`. -/
noncomputable def gpen (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (eps : ℝ) : QuadraticForm ℝ (V → ℝ) :=
  pen (G.lapMatrix ℝ).toQuadraticForm' (H.adjMatrix ℝ).toQuadraticForm' eps

/-- **Conjecture 1 (Bonetto--Jardon Kojakhmetov), proved.**  The signature of
`M(eps) = L_G + eps A_H` is nonincreasing on `eps > 0`. -/
theorem conj1 (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    sig (gpen G H v) ≤ sig (gpen G H u) :=
  sig_anti _ _ (lap_nonneg G) hu huv

/-- The stable dimension `n_+` is nonincreasing, and the unstable dimension `n_-` of the
gradient system `q' = -M(eps) q` is nondecreasing. -/
theorem conj1_counts (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    sigPos (gpen G H v) ≤ sigPos (gpen G H u) ∧
      sigNeg (gpen G H u) ≤ sigNeg (gpen G H v) :=
  ⟨sigPos_anti _ _ (lap_nonneg G) hu huv, sigNeg_mono _ _ (lap_nonneg G) hu huv⟩

end Principia.MathDB.P364187
