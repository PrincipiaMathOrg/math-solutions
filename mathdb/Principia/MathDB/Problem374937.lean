import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# MathDB 374937 — stable CSM positivity fails at the empty partition

Write-up: `mathdb-open-problems/problems/374937/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`, "Failure of stable CSM positivity at
the empty partition".  It refutes **Conjecture 6.7** of G. Bérczi and L. M. Fehér,
*Positivity in classical enumerative geometry*, arXiv:2605.25271v1, §6.2, pp. 26–27.

## The conjecture and the witness

For a partition `λ` with all parts `≥ 2`, put `c = |λ| - ℓ(λ)` and write the equivariant
CSM class of the **open** coincident-root stratum `Y_λ(d)` in the Schur basis with
coefficients `C_{λ,f,i}(d)`.  With `C̃ = (-1)^(f-c) C`, Conjecture 6.7 requires every
coefficient `γⱼ` in

  `C̃_{λ,f,i}(y + |λ| + 2(f-c)) = ∑ⱼ γⱼ · binom y j`

to be **nonnegative** (and the sequence log-concave).

The witness is the **empty partition**, `f = 1`, `i = 0`.  It has no parts, so it
vacuously has all parts `≥ 2`, and the source discusses it explicitly just before the
conjecture.  Then `|λ| = ℓ(λ) = c = 0`, the sign is `(-1)¹ = -1`, and the prescribed shift
is `y + 0 + 2(1-0) = y + 2`, i.e. `d = y + 2`.  `index_data_admissible` records all of
this, so the witness is checked against the conjecture's **hypotheses**, not only its
conclusion.

## What is carried, and what is proved

**Carried**: the single value `C_{∅,1,0}(d) = d(3-d)/2` (`Cco`).  This is the write-up's
equivariant-geometry computation — `c₁(V_d) = d(d+1)/2·(a+b)` minus the discriminant class
`[D_d] = d(d-1)·(a+b)`, using normalisation and additivity of equivariant CSM classes.
Mathlib has no CSM classes, no equivariant Chern classes and no coincident-root strata, so
this cannot be proved here.  `Campaigns/MathDB-Formalization/verify_374937.py`
re-derives it from those two stated inputs, so a transcription slip surfaces there.

**Proved**: everything downstream.  `Ctilde_expansion` confirms the write-up's displayed
expansion `-binom y 0 + binom y 1 + binom y 2`, `Ctilde_zero` extracts `C̃(0) = -1` from
it, and `not_positive` shows **no** nonnegative expansion of any length can exist.

## The argument

`binom 0 j` is `1` at `j = 0` and `0` for every `j ≥ 1`, because the product
`∏_{k<j} (y - k)` contains the factor `y` itself.  So the value at `y = 0` of ANY
nonnegative binomial expansion is a sum of nonnegative terms, hence `≥ 0`.  But
`C̃(0) = -1`.  That is the whole refutation — it needs neither uniqueness of the binomial
expansion nor any bound on its length, and it is the short route the write-up itself
offers ("evaluation at `y = 0` already forces its constant binomial coefficient to be
`-1`").

## Scope (the 215 check)

* This refutes the conjecture **as universally formulated**.  It is *not* a refutation of
  the conjecture restricted to `λ ≠ ∅`, which remains open — the write-up says so, and
  `not_positive` is stated only about the empty-partition polynomial.
* The object is the **open** stratum `Y_∅(d)` (squarefree forms), whose closure is all of
  `V_d`.  No claim about classes of closures is made or used.
* Only the positivity half is addressed; log-concavity is not, and does not need to be —
  one failed requirement refutes the conjunction.
-/

namespace Principia.MathDB.P374937

open Finset Nat

/-! ## The binomial basis -/

/-- `binom y j = y(y-1)⋯(y-j+1)/j!`, the basis Conjecture 6.7 expands in. -/
noncomputable def binom (y : ℝ) (j : ℕ) : ℝ := (∏ k ∈ range j, (y - k)) / (j ! : ℝ)

theorem binom_zero (y : ℝ) : binom y 0 = 1 := by
  simp [binom]

theorem binom_one (y : ℝ) : binom y 1 = y := by
  simp [binom]

theorem binom_two (y : ℝ) : binom y 2 = y * (y - 1) / 2 := by
  simp [binom, Finset.prod_range_succ]

/-- The factor `y` in the product is what makes every higher basis element vanish at `0`. -/
theorem binom_zero_of_pos {j : ℕ} (hj : 0 < j) : binom 0 j = 0 := by
  rw [binom, Finset.prod_eq_zero (Finset.mem_range.mpr hj) (by norm_num), zero_div]

theorem binom_zero_nonneg (j : ℕ) : 0 ≤ binom (0 : ℝ) j := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · rw [hj, binom_zero]; norm_num
  · rw [binom_zero_of_pos hj]

/-! ## The positivity requirement -/

/-- The positivity half of Conjecture 6.7 for a single shifted coefficient polynomial:
it admits a binomial expansion with all coefficients nonnegative.  No bound on the length
is assumed, so refuting this refutes the conjecture's requirement a fortiori. -/
def HasNonnegBinomialExpansion (P : ℝ → ℝ) : Prop :=
  ∃ (N : ℕ) (γ : ℕ → ℝ), (∀ j, 0 ≤ γ j) ∧ ∀ y : ℝ, P y = ∑ j ∈ range N, γ j * binom y j

/-- A nonnegative binomial expansion is nonnegative at `0`, whatever its length. -/
theorem nonneg_at_zero {P : ℝ → ℝ} (h : HasNonnegBinomialExpansion P) : 0 ≤ P 0 := by
  obtain ⟨N, γ, hγ, heq⟩ := h
  rw [heq 0]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hγ j) (binom_zero_nonneg j)

/-! ## The empty-partition coefficient -/

/-- `C_{∅,1,0}(d) = d(3-d)/2`.  **Carried** from the write-up: `c₁(V_d) - [D_d]`. -/
noncomputable def Cco (d : ℝ) : ℝ := d * (3 - d) / 2

/-- The conjecture's signed, shifted polynomial at `λ = ∅`, `f = 1`, `i = 0`: the sign is
`(-1)^(f-c) = -1` and the shift is `d = y + 2`. -/
noncomputable def Ctilde (y : ℝ) : ℝ := -(Cco (y + 2))

theorem Ctilde_eq (y : ℝ) : Ctilde y = (y + 2) * (y - 1) / 2 := by
  unfold Ctilde Cco; ring

/-- The write-up's displayed expansion, verified. -/
theorem Ctilde_expansion (y : ℝ) :
    Ctilde y = (-1) * binom y 0 + 1 * binom y 1 + 1 * binom y 2 := by
  rw [binom_zero, binom_one, binom_two, Ctilde_eq]; ring

/-- `γ₀ = -1`, read off by evaluating the expansion at `y = 0`. -/
theorem Ctilde_zero : Ctilde 0 = -1 := by
  rw [Ctilde_expansion, binom_zero, binom_zero_of_pos (by norm_num),
    binom_zero_of_pos (by norm_num)]
  ring

/-- **Conjecture 6.7's positivity requirement fails at the empty partition.** -/
theorem not_positive : ¬ HasNonnegBinomialExpansion Ctilde := by
  intro h
  have h0 := nonneg_at_zero h
  rw [Ctilde_zero] at h0
  norm_num at h0

/-! ## The witness satisfies the conjecture's own hypotheses -/

/-- `λ = ∅`, `f = 1`, `i = 0`: all parts are `≥ 2` (vacuously), `c = |λ| - ℓ(λ) = 0`,
`f ≥ c`, `i ≤ ⌊f/2⌋`, and the prescribed shift `|λ| + 2(f-c)` is `2`. -/
theorem index_data_admissible :
    (∀ p ∈ ([] : List ℕ), 2 ≤ p) ∧ ([] : List ℕ).sum = 0 ∧ ([] : List ℕ).length = 0 ∧
      (0 : ℕ) ≤ 1 ∧ (0 : ℕ) ≤ 1 / 2 ∧ ([] : List ℕ).sum + 2 * (1 - 0) = 2 := by
  refine ⟨by simp, rfl, rfl, by norm_num, by norm_num, by norm_num⟩

end Principia.MathDB.P374937
