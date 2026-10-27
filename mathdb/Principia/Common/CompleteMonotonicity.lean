import Mathlib

set_option autoImplicit false

/-!
# Complete monotonicity, and its bridge to Mathlib's `AbsolutelyMonotoneOn`

Mathlib has `AbsolutelyMonotoneOn` (every iterated derivative nonnegative,
`Mathlib/Analysis/Calculus/AbsolutelyMonotone.lean`, 122 lines) and **no** predicate for the
reflected notion: `f` is *completely monotone* on `s` when `(-1)^n f^(n) >= 0` on `s`.  That is the
side the literature on Mills ratios, Bessel quotients and Laplace transforms is stated on, and it is
what a MathDB refutation of a complete-monotonicity conjecture has to contradict.

Nothing here mentions any campaign's objects.

**Why the predicate carries `ContDiffOn`.**  `iteratedDerivWithin` is junk-valued off the domain of
differentiability, and its junk value is `0`, which satisfies every sign condition.  Without the
smoothness conjunct the predicate would be satisfied by functions that have no derivatives at all,
and a refutation of it would prove nothing.

**Why the bridge is stated for OPEN `s`.**  `AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg`
needs `UniqueDiffOn`, and the reflection needs `-s` to satisfy it too; `UniqueDiffOn` has no
`neg` lemma, while `IsOpen` does and gives `UniqueDiffOn` for free.  Every conjecture this is aimed
at is stated on `(0, +inf)`, so the restriction costs nothing.
-/

namespace Principia.Common

open Set
open scoped ContDiff Pointwise

variable {f : ℝ → ℝ} {s : Set ℝ}

/-- `f` is **completely monotone on `s`**: it is `C^inf` there and `(-1)^n f^(n) >= 0` for every
`n`.  The `ContDiffOn` conjunct is load-bearing -- see the module docstring. -/
def CompletelyMonotoneOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ContDiffOn ℝ ∞ f s ∧ ∀ n : ℕ, ∀ x ∈ s, 0 ≤ (-1 : ℝ) ^ n * iteratedDerivWithin n f s x

/-- On an open set the `within` derivative in the definition is the plain one. -/
theorem CompletelyMonotoneOn.iteratedDeriv_nonneg (hf : CompletelyMonotoneOn f s) (hs : IsOpen s)
    (n : ℕ) {x : ℝ} (hx : x ∈ s) : 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n f x := by
  have h := hf.2 n x hx
  rwa [iteratedDerivWithin_of_isOpen hs hx] at h

/-- **The refutation criterion.**  One point and one order at which `(-1)^n f^(n)` is negative
refutes complete monotonicity.  Note there is no smoothness hypothesis: the predicate carries its
own. -/
theorem not_completelyMonotoneOn_of_iteratedDeriv_lt (hs : IsOpen s) {n : ℕ} {x : ℝ} (hx : x ∈ s)
    (h : (-1 : ℝ) ^ n * iteratedDeriv n f x < 0) : ¬ CompletelyMonotoneOn f s :=
  fun hf => absurd (hf.iteratedDeriv_nonneg hs n hx) (not_le.mpr h)

/-- The sufficient condition, phrased with the plain iterated derivative. -/
theorem completelyMonotoneOn_of_isOpen (hs : IsOpen s) (hcont : ContDiffOn ℝ ∞ f s)
    (h : ∀ n : ℕ, ∀ x ∈ s, 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n f x) : CompletelyMonotoneOn f s :=
  ⟨hcont, fun n x hx => by rw [iteratedDerivWithin_of_isOpen hs hx]; exact h n x hx⟩

/-- A completely monotone function is nonnegative (the `n = 0` instance). -/
theorem CompletelyMonotoneOn.nonneg (hf : CompletelyMonotoneOn f s) {x : ℝ} (hx : x ∈ s) :
    0 ≤ f x := by
  have h := hf.2 0 x hx
  simpa using h

/-- Reflection is a smooth change of variable. -/
theorem contDiffOn_comp_neg (hcont : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (fun x : ℝ => f (-x)) (-s) :=
  hcont.comp contDiff_neg.contDiffOn (fun _ hy => by simpa using hy)

/-- **The bridge.**  Complete monotonicity on `s` is absolute monotonicity of the reflection on
`-s`, so Mathlib's development transfers in both directions. -/
theorem completelyMonotoneOn_iff_absolutelyMonotoneOn_neg (hs : IsOpen s) :
    CompletelyMonotoneOn f s ↔ AbsolutelyMonotoneOn (fun x : ℝ => f (-x)) (-s) := by
  have hns : IsOpen (-s) := hs.neg
  have hmem : ∀ {y : ℝ}, y ∈ -s → -y ∈ s := fun hy => by simpa using hy
  rw [AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg hns.uniqueDiffOn]
  constructor
  · intro hf
    refine ⟨contDiffOn_comp_neg hf.1, fun n y hy => ?_⟩
    rw [iteratedDerivWithin_of_isOpen hns hy, iteratedDeriv_comp_neg, smul_eq_mul]
    exact hf.iteratedDeriv_nonneg hs n (hmem hy)
  · rintro ⟨hcont, hnn⟩
    have hback : ContDiffOn ℝ ∞ (fun x : ℝ => f (- -x)) (- -s) := contDiffOn_comp_neg hcont
    simp only [neg_neg] at hback
    refine ⟨hback, fun n x hx => ?_⟩
    have hx' : -x ∈ -s := by simpa using hx
    have h := hnn n (-x) hx'
    rw [iteratedDerivWithin_of_isOpen hns hx', iteratedDeriv_comp_neg, smul_eq_mul, neg_neg] at h
    rwa [iteratedDerivWithin_of_isOpen hs hx]

end Principia.Common
