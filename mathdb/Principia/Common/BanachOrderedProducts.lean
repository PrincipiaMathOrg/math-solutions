/-
Ordered products in a Banach algebra: ONE majorant for BOTH orders of multiplication.

This module is CAMPAIGN-AGNOSTIC.  It mentions no basic hypergeometric series, no q-shifted
factorials and no specific identity; it is about finite products in a normed ring and nothing
else, so it lives in `Common/` where the next campaign can find it.

WHY IT EXISTS.  The write-up for MathDB #378712 (the two noncommutative Q-Gauss summations,
Schlosser's Conjecture 7.1) states its own analytic mechanism in a single sentence of the
abstract:

  *"A common geometric majorant works for the two orders of multiplication."*

That sentence is the load-bearing analytic content of the whole paper, and it is not about
q-series at all.  In a noncommutative ring the two products

    X_{k-1} * ... * X_0        and        X_0 * ... * X_{k-1}

are different elements, and the paper needs both to be controlled at once.  The reason one
bound serves both is that the majorant is a product of NORMS, and norms live in the reals,
which are commutative -- so reordering the factors cannot change the bound even though it
changes the element.  Formalising that turns the paper's sentence into `common_majorant`.

WHAT IS PROVED
* `norm_listProd_le_prod_one_add` -- `‖l.prod‖ ≤ ∏ (1 + ‖eᵢ - 1‖)`, the deviation form.  The
  deviations, not the norms themselves, are what the paper sums.
* `prod_one_add_le_exp_sum` -- `∏ (1 + aᵢ) ≤ exp (∑ aᵢ)` for nonnegative `aᵢ`.  This is what
  converts a *summability* hypothesis into a *uniform bound on all finite products*, which is
  exactly the step the paper takes to produce its constant `L`.
* `norm_listProd_le_exp` -- the two combined: `‖l.prod‖ ≤ exp (∑ ‖eᵢ - 1‖)`.
* **`common_majorant`** -- the headline: the ascending and descending products of the *same*
  factors obey the *same* bound.  Stated with `max` so the single shared majorant is visible
  in the statement rather than left to the reader.

WHY THE `NormOneClass` HYPOTHESIS IS NOT AN IMPOSITION.  `‖1‖ = 1` is used twice (once for the
empty product, once in `‖e‖ ≤ 1 + ‖e - 1‖`).  The write-up anticipates precisely this: *"The
norm may be taken to satisfy ‖I‖ = 1: if needed, the equivalent left-regular operator norm has
this property and does not increase ‖Q‖ or ‖Z‖."*  So the Lean hypothesis and the paper's
remark are the same remark.

NOT PROVED HERE, and it is the rest of the paper: that the specific factors `X_j`, `Y_j`, `V_j`
have summable deviations (that is a Neumann-series estimate on `(I - C Q^j)⁻¹`), the
terminating Pfaff--Saalschütz identity that is quoted from the source, the block-matrix
argument removing invertibility of `Q`, and the passage to the limit.  This module supplies the
one ingredient those all feed into: once deviations are summable, every finite product in
either order is uniformly bounded.
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false

namespace Principia.Common.BanachOrderedProducts

open List

-- `dev` and its nonnegativity need only the ring structure; `‖1‖ = 1` enters one step later,
-- so they are declared before `NormOneClass` is in scope rather than carrying it unused.
variable {A : Type*} [NormedRing A]

/-- The deviation of a factor from the identity.  The paper's estimates are all of the form
`‖X_j - I‖ = O(q^j)`, i.e. they bound this quantity and not `‖X_j‖`. -/
noncomputable def dev (a : A) : ℝ := ‖a - 1‖

theorem dev_nonneg (a : A) : 0 ≤ dev a := norm_nonneg _

variable [NormOneClass A]

/-- `‖a‖ ≤ 1 + ‖a - 1‖`.  The triangle inequality applied to `a = 1 + (a - 1)`; this is the
only place the size of a factor is traded for the size of its deviation. -/
theorem norm_le_one_add_dev (a : A) : ‖a‖ ≤ 1 + dev a := by
  -- NB `ring` does NOT apply: a `NormedRing` need not be commutative, and `ring` reports
  -- "made no progress".  This is an additive-group identity, so `abel` is the right tactic.
  have h : a = 1 + (a - 1) := by abel
  calc ‖a‖ = ‖(1 : A) + (a - 1)‖ := by rw [← h]
    _ ≤ ‖(1 : A)‖ + ‖a - 1‖ := norm_add_le _ _
    _ = 1 + dev a := by rw [norm_one]; rfl

/-- **The deviation bound on an ordered product.**  Proved by induction on the list, so it is
insensitive to how the factors are ordered -- which is what makes `common_majorant` available. -/
theorem norm_listProd_le_prod_one_add :
    ∀ l : List A, ‖l.prod‖ ≤ (l.map (fun a => 1 + dev a)).prod
  | [] => by simp
  | a :: t => by
      have ih := norm_listProd_le_prod_one_add t
      have h1 : ‖(a :: t).prod‖ ≤ ‖a‖ * ‖t.prod‖ := by
        rw [List.prod_cons]; exact norm_mul_le _ _
      have hb : (0 : ℝ) ≤ (t.map (fun x => 1 + dev x)).prod :=
        List.prod_nonneg (by
          intro x hx
          simp only [List.mem_map] at hx
          obtain ⟨y, _, rfl⟩ := hx
          linarith [dev_nonneg y])
      calc ‖(a :: t).prod‖ ≤ ‖a‖ * ‖t.prod‖ := h1
        _ ≤ (1 + dev a) * (t.map (fun x => 1 + dev x)).prod := by
            apply mul_le_mul (norm_le_one_add_dev a) ih (norm_nonneg _)
            linarith [dev_nonneg a]
        _ = ((a :: t).map (fun x => 1 + dev x)).prod := by rw [List.map_cons, List.prod_cons]

/-- **`∏ (1 + aᵢ) ≤ exp (∑ aᵢ)` for nonnegative `aᵢ`.**  This is the step that turns a
*summability* hypothesis into a bound valid for *every* finite product at once, which is how
the write-up's constant `L` is finite. -/
theorem prod_one_add_le_exp_sum :
    ∀ (l : List ℝ), (∀ x ∈ l, 0 ≤ x) → (l.map (fun x => 1 + x)).prod ≤ Real.exp l.sum
  | [], _ => by simp
  | a :: t, h => by
      have ha : 0 ≤ a := h a (by simp)
      have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => h x (by simp [hx])
      have ih := prod_one_add_le_exp_sum t ht
      have hpos : (0 : ℝ) ≤ (t.map (fun x => 1 + x)).prod :=
        List.prod_nonneg (by
          intro x hx
          simp only [List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          linarith [ht y hy])
      have hexp : 1 + a ≤ Real.exp a := by
        have := Real.add_one_le_exp a
        linarith
      calc ((a :: t).map (fun x => 1 + x)).prod
          = (1 + a) * (t.map (fun x => 1 + x)).prod := by rw [List.map_cons, List.prod_cons]
        _ ≤ Real.exp a * Real.exp t.sum := by
            apply mul_le_mul hexp ih hpos (le_of_lt (Real.exp_pos a))
        _ = Real.exp (a :: t).sum := by rw [← Real.exp_add, List.sum_cons]

/-- `‖l.prod‖ ≤ exp (∑ ‖eᵢ - 1‖)`: summable deviations bound the product. -/
theorem norm_listProd_le_exp (l : List A) :
    ‖l.prod‖ ≤ Real.exp ((l.map dev).sum) := by
  refine (norm_listProd_le_prod_one_add l).trans ?_
  have h := prod_one_add_le_exp_sum (l.map dev) (by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact dev_nonneg y)
  -- state the map-composition explicitly rather than trusting `simpa` to normalise both
  -- sides the same way; the bare `simpa` version failed with a post-simplification mismatch
  have hmm : (l.map dev).map (fun x => 1 + x) = l.map (fun a => 1 + dev a) := by
    rw [List.map_map]; rfl
  rw [hmm] at h
  exact h

/-- **THE HEADLINE — a common majorant for the two orders of multiplication.**

`l.prod` and `l.reverse.prod` are different elements of `A` whenever `A` is noncommutative, yet
a single bound covers both.  The reason is visible in the proof and is the whole point: the
majorant is a sum of *norms*, and `List.sum_reverse` holds in `ℝ` because `ℝ` is commutative.
Reordering the factors permutes the summands of the bound and therefore does not move it. -/
theorem common_majorant (l : List A) :
    max ‖l.prod‖ ‖l.reverse.prod‖ ≤ Real.exp ((l.map dev).sum) := by
  refine max_le (norm_listProd_le_exp l) ?_
  have h := norm_listProd_le_exp l.reverse
  simpa [List.map_reverse, List.sum_reverse] using h

/-- The same statement in the form the write-up uses it: a single constant bounding every
ascending and descending partial product, given a bound on the total deviation. -/
theorem uniform_bound_of_dev_sum_le {S : ℝ} (l : List A) (h : (l.map dev).sum ≤ S) :
    ‖l.prod‖ ≤ Real.exp S ∧ ‖l.reverse.prod‖ ≤ Real.exp S := by
  have hb := common_majorant l
  have hm : Real.exp ((l.map dev).sum) ≤ Real.exp S := Real.exp_le_exp.mpr h
  exact ⟨le_trans (le_trans (le_max_left _ _) hb) hm,
         le_trans (le_trans (le_max_right _ _) hb) hm⟩

end Principia.Common.BanachOrderedProducts
