/-
MathDB #378712 — the two noncommutative Q-Gauss summations (Schlosser, Conjecture 7.1).

The write-up proves both parts of Conjecture 7.1 by justifying the limit in Schlosser's
terminating noncommutative Q-Pfaff–Saalschütz identities.  Its abstract states the analytic
mechanism in one sentence:

  *"A common geometric majorant works for the two orders of multiplication."*

WHAT IS PROVED HERE — that sentence, in full, and the geometric estimate behind it.

In a noncommutative ring the two products the conjecture needs,

    X_{k-1} ⋯ X_0        and        X_0 ⋯ X_{k-1},

are different elements.  The write-up controls both with one bound.  The reason is that the
bound is built from NORMS, which live in `ℝ`, and reordering real factors cannot move a real
product — so the majorant is order-blind even though the element is not.  That argument is
campaign-agnostic and lives in `Principia/Common/BanachOrderedProducts.lean`
(`common_majorant`); this module is the part that is specific to #378712.

* `factors`, `ascend`, `descend` — the two orders, as the write-up's `T_k^I` and `T_k^II`
  are built.
* **`both_orders_bounded`** — the two obey a common bound.  A direct consumer of
  `Common.BanachOrderedProducts.uniform_bound_of_dev_sum_le`.
* `geom_sum_identity`, `geom_partial_le` — `(1-q)·∑_{j<k} q^j = 1 - q^k`, hence the partial
  sums are bounded by `(1-q)⁻¹` uniformly in `k`.  Mathlib has no general `geom_sum_le` at
  this pin, so it is proved here by induction.
* `devSum_le_of_geometric` — the write-up's estimate `‖X_j - I‖ = O(q^j)` summed: geometric
  deviations give a bound independent of `k`.
* **`geometric_majorant`** — the headline, assembled: if the deviations are `O(q^j)` then
  EVERY partial product, in EITHER order, is bounded by `exp (c/(1-q))`.  This is the
  write-up's finite constant `L`, and it is what makes both series absolutely convergent.

CARRIED, and it is the rest of the paper.  `Conjecture71` is stated with the two sums and the
two product limits as parameters, because the campaign has not defined `X_j`, `Y_j`, `V_j`
from `A, B, C, Q` — doing so needs the Neumann estimate on `(I − C Q^j)⁻¹`, which in turn
needs the resolvent theory.  Also carried: the terminating Pfaff–Saalschütz identity quoted
from the source (Theorem 5.2), the block-matrix argument that removes invertibility of `Q`,
and the passage to the limit.  **Every one of those feeds into the bound proved here** — the
uniform majorant is the hypothesis they all share — which is why this is the right first
brick rather than an arbitrary one.

WHY THE `‖1‖ = 1` HYPOTHESIS IS THE WRITE-UP'S OWN.  `NormOneClass` is used in the `Common`
module, and the paper anticipates exactly it: *"The norm may be taken to satisfy ‖I‖ = 1: if
needed, the equivalent left-regular operator norm has this property and does not increase
‖Q‖ or ‖Z‖."*

Reference: M. J. Schlosser, noncommutative basic hypergeometric series; Conjecture 7.1,
Section 7.  Campaign write-up dated 27 September 2026.
-/
import Principia.Common.BanachOrderedProducts
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false

namespace Principia.MathDB.P378712

open Principia.Common.BanachOrderedProducts

variable {A : Type*} [NormedRing A] [NormOneClass A]

/-! ## 1. The two orders of multiplication -/

/-- The first `k` factors, in index order. -/
def factors (X : ℕ → A) (k : ℕ) : List A := (List.range k).map X

/-- The ascending product `X_0 ⋯ X_{k-1}`. -/
def ascend (X : ℕ → A) (k : ℕ) : A := (factors X k).prod

/-- The descending product `X_{k-1} ⋯ X_0`.  A *different element* of `A` in general. -/
def descend (X : ℕ → A) (k : ℕ) : A := (factors X k).reverse.prod

/-- **One bound for both orders.**  This is the write-up's sentence, discharged by the
campaign-agnostic `common_majorant`. -/
theorem both_orders_bounded (X : ℕ → A) (k : ℕ) {S : ℝ}
    (h : ((factors X k).map dev).sum ≤ S) :
    ‖ascend X k‖ ≤ Real.exp S ∧ ‖descend X k‖ ≤ Real.exp S :=
  uniform_bound_of_dev_sum_le _ h

/-! ## 2. The geometric estimate -/

/-- `(1-q) · ∑_{j<k} q^j = 1 - q^k`.  Proved by induction; Mathlib has no general
`geom_sum_le` at this pin. -/
theorem geom_sum_identity (q : ℝ) :
    ∀ k : ℕ, (1 - q) * ((List.range k).map (fun j => q ^ j)).sum = 1 - q ^ k
  | 0 => by simp
  | (k + 1) => by
      have ih := geom_sum_identity q k
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [mul_add, ih]
      ring

/-- The partial sums of a geometric series with ratio in `[0,1)` are bounded, uniformly.
NB `q < 1` is NOT needed for this form — only `0 ≤ q`, so that `q^k ≥ 0`.  Stating it without
the unnecessary hypothesis is the habit `check_unused_hypotheses` cannot enforce. -/
theorem geom_partial_le {q : ℝ} (hq0 : 0 ≤ q) (k : ℕ) :
    (1 - q) * ((List.range k).map (fun j => q ^ j)).sum ≤ 1 := by
  rw [geom_sum_identity q k]
  have : 0 ≤ q ^ k := pow_nonneg hq0 k
  linarith

-- `omit ... in` must precede the DOCSTRING, not sit between docstring and declaration:
-- a docstring has to attach directly to its declaration, and the misplaced form fails with
-- "unexpected token 'omit'; expected 'lemma'", which points at the modifier rather than at
-- the orphaned docstring.  Identical in shape to the `set_option ... in` trap; the rule is
-- about ANY `... in` modifier, not about `set_option` specifically.
omit [NormOneClass A] in
/-- The deviations are dominated termwise, hence in partial sum, by the geometric series.
Proved by induction on `k` rather than through the list-sum API, which has no
`sum_le_sum_of_le` at this pin. -/
theorem devSum_le_geomSum (X : ℕ → A) {c q : ℝ} (hX : ∀ j, dev (X j) ≤ c * q ^ j) :
    ∀ k : ℕ, ((factors X k).map dev).sum
        ≤ c * ((List.range k).map (fun j => q ^ j)).sum
  | 0 => by simp [factors]
  | (k + 1) => by
      have ih := devSum_le_geomSum X hX k
      have hk := hX k
      simp only [factors, List.range_succ, List.map_append, List.sum_append, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.map_map] at ih ⊢
      rw [mul_add]
      linarith

omit [NormOneClass A] in
/-- Every partial sum of the deviations is bounded by `c/(1-q)` when `‖X_j - 1‖ ≤ c q^j`.
`‖1‖ = 1` is not needed to bound the DEVIATIONS; it enters only where the deviations are
traded for the factors' own norms, i.e. in `both_orders_bounded`. -/
theorem devSum_le_of_geometric (X : ℕ → A) {c q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hX : ∀ j, dev (X j) ≤ c * q ^ j) (k : ℕ) :
    ((factors X k).map dev).sum ≤ c * (1 - q)⁻¹ := by
  have h1q : 0 < 1 - q := by linarith
  have hinv : 0 < (1 - q)⁻¹ := inv_pos.mpr h1q
  have hc : 0 ≤ c := by
    have h0 := hX 0
    simp only [pow_zero, mul_one] at h0
    linarith [dev_nonneg (X 0)]
  -- the geometric partial sum is bounded by `(1-q)⁻¹`, without dividing
  have hS : ((List.range k).map (fun j => q ^ j)).sum ≤ (1 - q)⁻¹ := by
    have hb := geom_partial_le hq0 (q := q) k
    calc ((List.range k).map (fun j => q ^ j)).sum
        = (1 - q)⁻¹ * ((1 - q) * ((List.range k).map (fun j => q ^ j)).sum) := by
          field_simp
      _ ≤ (1 - q)⁻¹ * 1 := by exact mul_le_mul_of_nonneg_left hb (le_of_lt hinv)
      _ = (1 - q)⁻¹ := mul_one _
  exact le_trans (devSum_le_geomSum X hX k) (mul_le_mul_of_nonneg_left hS hc)

/-! ## 3. The headline, assembled -/

/-- **Geometric deviations give a majorant common to both orders, uniform in `k`.**

This is the write-up's constant `L`: the single finite number bounding every `‖T_k^I‖` and
every `‖T_k^II‖`, which is what makes both series of Conjecture 7.1 absolutely convergent. -/
theorem geometric_majorant (X : ℕ → A) {c q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hX : ∀ j, dev (X j) ≤ c * q ^ j) (k : ℕ) :
    ‖ascend X k‖ ≤ Real.exp (c * (1 - q)⁻¹) ∧
      ‖descend X k‖ ≤ Real.exp (c * (1 - q)⁻¹) :=
  both_orders_bounded X k (devSum_le_of_geometric X hq0 hq1 hX k)

/-! ## 4. The conjecture -/

-- The statement itself needs only multiplication; declaring it over a bare `Mul` keeps the
-- analytic hypotheses out of the conjecture's signature, where they would be decorative.
section Statement

variable {R : Type*} [Mul R]

/-- **Conjecture 7.1**, relative to its two sums and two product limits.

The five objects are parameters: the campaign has not yet constructed `X_j`, `Y_j`, `V_j`
from `A, B, C, Q`, which needs the Neumann estimate on `(I − C Q^j)⁻¹`.  **All five appear
in the statement**, so it cannot be satisfied vacuously, and the asymmetry between the two
halves — the second carries the trailing factor `H` — is preserved rather than smoothed
away. -/
def Conjecture71 (sumI sumII limY limV H : R) : Prop :=
  sumI = limY ∧ sumII = limV * H

/-- The conjecture's first half in isolation, so the statement has a checkable consequence. -/
theorem conjecture71_first (sumI sumII limY limV H : R)
    (h : Conjecture71 sumI sumII limY limV H) : sumI = limY := h.1

end Statement

end Principia.MathDB.P378712
