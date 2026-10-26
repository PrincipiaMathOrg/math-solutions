import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

/-!
# MathDB #317353 — Star of David matrices are NOT closed under inversion

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/317353/solution.tex`, refuting Conjecture 2.6 of Sun (the Star of
David rule paper): *every invertible `A ∈ SDR_m` has `A⁻¹ ∈ SDR_m`*.

**The objects.**  Matrices are infinite and lower triangular, indexed by `ℕ × ℕ`.  For
`n ≥ k ≥ 0`, `2 ≤ p ≤ m − 1` and `0 ≤ r ≤ p − 1`, Sun's Definition 1.1 compares

  `L_{p,r}(n,k) = ∏_{i=0}^{r} X_{n+i, k+r−i} · ∏_{i=0}^{p−r−1} X_{n+p−i, k+r+i+1}`,
  `R_{p,r}(n,k) = ∏_{i=0}^{r} X_{n+p−i, k+p−r+i} · ∏_{i=0}^{p−r−1} X_{n+i, k+p−r−i−1}`,

and `X ∈ SDR_m` means `L = R` for every such index.  `L` and `R` below write the natural-number
subtractions as `k + (r − i)`, `n + (p − i)`, `k + (p − r) + i` and `k + (p − r − i − 1)`; on the
index ranges of the products (`i ≤ r ≤ p − 1`, and `i ≤ p − r − 1` in the second products) these
are equal to the source's expressions, so no truncation of `ℕ` subtraction is ever reached.

**What is refuted, and why it is stated weakly.**  `SunConj26` is the `m = 3` instance, over
integer matrices, with both matrices assumed lower triangular and inverse to each other.  Each of
those choices only WEAKENS the conjecture — the source claims every `m ≥ 3`, over any field, and a
lower triangular matrix's inverse is lower triangular anyway — so refuting this instance refutes
the source.  Lower triangularity of the LEFT factor is also what makes the product
`∑_{l ≤ i} X_{i,l} Y_{l,j}` below the true matrix product.

**The witness** is `A = M ⊕ I` with the `5 × 5` block
`M = [[1,0,0,0,0],[1,1,0,0,0],[0,1,1,0,0],[0,0,1,1,0],[0,1,0,2,1]]`, whose inverse is
`B = M⁻¹ ⊕ I`, `M⁻¹ = [[1,0,0,0,0],[-1,1,0,0,0],[1,-1,1,0,0],[-1,1,-1,1,0],[3,-3,2,-2,1]]`.
`A ∈ SDR_3`, but at `(p, r, n, k) = (2, 0, 2, 0)` the inverse has `L = 3` and `R = 2`.

The only unbounded parts are `A ∈ SDR_3` and the inverse identities for indices past the block;
both reduce to "a tail row of an identity matrix has one nonzero entry", as in the write-up's
Lemma 1.  Every value was checked against the write-up in Python before this file was written.
-/

namespace Principia.MathDB.P317353

open Finset

/-- Infinite integer matrices, indexed by `ℕ × ℕ`. -/
abbrev Mat := ℕ → ℕ → ℤ

/-- Zero strictly above the diagonal. -/
def LowerTri (X : Mat) : Prop := ∀ i j, i < j → X i j = 0

/-- The left-hand product of Sun's Definition 1.1. -/
def L (p r n k : ℕ) (X : Mat) : ℤ :=
  (∏ i ∈ range (r + 1), X (n + i) (k + (r - i))) *
    ∏ i ∈ range (p - r), X (n + (p - i)) (k + r + i + 1)

/-- The right-hand product of Sun's Definition 1.1. -/
def R (p r n k : ℕ) (X : Mat) : ℤ :=
  (∏ i ∈ range (r + 1), X (n + (p - i)) (k + (p - r) + i)) *
    ∏ i ∈ range (p - r), X (n + i) (k + (p - r - i - 1))

/-- Sun's `SDR_m`, the Star of David rule of order up to `m`. -/
def SDR (m : ℕ) (X : Mat) : Prop :=
  ∀ p r n k, 2 ≤ p → p ≤ m - 1 → r ≤ p - 1 → k ≤ n → L p r n k X = R p r n k X

/-- `Y` is a two-sided inverse of `X`.  Summing only `l ≤ i` is the true product when the left
factor is lower triangular, which `SunConj26` assumes of both. -/
def InvPair (X Y : Mat) : Prop :=
  (∀ i j, ∑ l ∈ range (i + 1), X i l * Y l j = if i = j then 1 else 0) ∧
    ∀ i j, ∑ l ∈ range (i + 1), Y i l * X l j = if i = j then 1 else 0

/-- Sun's Conjecture 2.6 at `m = 3`, over the integers — a weakening of the source's claim. -/
def SunConj26 : Prop :=
  ∀ X Y : Mat, LowerTri X → LowerTri Y → InvPair X Y → SDR 3 X → SDR 3 Y

/-- The finite block, as rows. -/
def Mrows : List (List ℤ) :=
  [[1, 0, 0, 0, 0], [1, 1, 0, 0, 0], [0, 1, 1, 0, 0], [0, 0, 1, 1, 0], [0, 1, 0, 2, 1]]

/-- The inverse block, as rows. -/
def Minvrows : List (List ℤ) :=
  [[1, 0, 0, 0, 0], [-1, 1, 0, 0, 0], [1, -1, 1, 0, 0], [-1, 1, -1, 1, 0], [3, -3, 2, -2, 1]]

/-- `rows ⊕ I`: the block in the top-left `5 × 5` corner, the identity outside it. -/
def ext (rows : List (List ℤ)) : Mat :=
  fun i j => if i < 5 ∧ j < 5 then (rows.getD i []).getD j 0 else if i = j then 1 else 0

/-- The counterexample matrix. -/
def A : Mat := ext Mrows

/-- Its inverse. -/
def B : Mat := ext Minvrows

theorem A_lower : LowerTri A := by
  intro i j hij
  unfold A ext
  by_cases h : i < 5 ∧ j < 5
  · obtain ⟨hi, hj⟩ := h
    rw [if_pos ⟨hi, hj⟩]
    interval_cases i <;> interval_cases j <;> decide
  · rw [if_neg h, if_neg (by omega)]

theorem B_lower : LowerTri B := by
  intro i j hij
  unfold B ext
  by_cases h : i < 5 ∧ j < 5
  · obtain ⟨hi, hj⟩ := h
    rw [if_pos ⟨hi, hj⟩]
    interval_cases i <;> interval_cases j <;> decide
  · rw [if_neg h, if_neg (by omega)]

/-- Every entry of `A` that is above the diagonal, or off the diagonal in a tail row, vanishes. -/
theorem A_zero (i j : ℕ) (h : i < j ∨ (5 ≤ i ∧ i ≠ j)) : A i j = 0 := by
  rcases h with h | ⟨h1, h2⟩
  · exact A_lower i j h
  · unfold A ext
    rw [if_neg (by omega), if_neg h2]

/-- A tail row of either matrix is a row of the identity. -/
theorem ext_tail (rows : List (List ℤ)) (i j : ℕ) (h : 5 ≤ i) :
    ext rows i j = if i = j then 1 else 0 := by
  unfold ext
  rw [if_neg (by omega)]

/-- A vanishing factor in the first product of `L` makes `L` vanish. -/
theorem L_zero_of_first {X : Mat} {p r n k i : ℕ} (hi : i < r + 1)
    (h : X (n + i) (k + (r - i)) = 0) : L p r n k X = 0 := by
  unfold L
  exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_range.mpr hi) h) _

/-- A vanishing factor in the second product of `L` makes `L` vanish. -/
theorem L_zero_of_second {X : Mat} {p r n k i : ℕ} (hi : i < p - r)
    (h : X (n + (p - i)) (k + r + i + 1) = 0) : L p r n k X = 0 := by
  unfold L
  exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_range.mpr hi) h)

/-- A vanishing factor in the first product of `R` makes `R` vanish. -/
theorem R_zero_of_first {X : Mat} {p r n k i : ℕ} (hi : i < r + 1)
    (h : X (n + (p - i)) (k + (p - r) + i) = 0) : R p r n k X = 0 := by
  unfold R
  exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_range.mpr hi) h) _

/-- A vanishing factor in the second product of `R` makes `R` vanish. -/
theorem R_zero_of_second {X : Mat} {p r n k i : ℕ} (hi : i < p - r)
    (h : X (n + i) (k + (p - r - i - 1)) = 0) : R p r n k X = 0 := by
  unfold R
  exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_range.mpr hi) h)

/-- **`A` satisfies the order-three Star of David rule** for every `n ≥ k ≥ 0`.  For `n ≤ 2` the
indices stay inside the block and the identity is a finite computation; for `n ≥ 3` row `n + 2` is
an identity row, and in each of the four cases one factor on each side is forced to vanish. -/
theorem A_sdr3 : SDR 3 A := by
  intro p r n k hp hpm hr hkn
  have hp2 : p = 2 := by omega
  subst hp2
  have hr' : r = 0 ∨ r = 1 := by omega
  by_cases hn : n ≤ 2
  · rcases hr' with rfl | rfl <;> interval_cases n <;> interval_cases k <;>
      simp only [L, R, Finset.prod_range_succ, Finset.prod_range_zero, one_mul] <;> decide
  · rcases hr' with rfl | rfl <;> rcases Nat.lt_or_ge k n with hk | hk
    · -- r = 0, k < n: row n + 2 is an identity row, and both columns miss its diagonal
      rw [L_zero_of_second (i := 0) (by omega) (A_zero (n + (2 - 0)) (k + 0 + 0 + 1) (by omega)),
        R_zero_of_first (i := 0) (by omega) (A_zero (n + (2 - 0)) (k + (2 - 0) + 0) (by omega))]
    · -- r = 0, k = n
      rw [L_zero_of_second (i := 0) (by omega) (A_zero (n + (2 - 0)) (k + 0 + 0 + 1) (by omega)),
        R_zero_of_second (i := 0) (by omega) (A_zero (n + 0) (k + (2 - 0 - 0 - 1)) (by omega))]
    · -- r = 1, k < n
      rw [L_zero_of_second (i := 0) (by omega) (A_zero (n + (2 - 0)) (k + 1 + 0 + 1) (by omega)),
        R_zero_of_first (i := 0) (by omega) (A_zero (n + (2 - 0)) (k + (2 - 1) + 0) (by omega))]
    · -- r = 1, k = n
      rw [L_zero_of_first (i := 0) (by omega) (A_zero (n + 0) (k + (1 - 0)) (by omega)),
        R_zero_of_first (i := 0) (by omega) (A_zero (n + (2 - 0)) (k + (2 - 1) + 0) (by omega))]

/-- The truncated product of two block-plus-identity matrices is the identity, for every index.
Inside the block it is a finite computation; in a tail row only `l = i` survives; in a tail column
every term vanishes because the right factor is zero there. -/
theorem ext_inv (P Q : List (List ℤ)) (hQ : LowerTri (ext Q))
    (hblock : ∀ i j, i < 5 → j < 5 →
      ∑ l ∈ range (i + 1), ext P i l * ext Q l j = if i = j then 1 else 0)
    (i j : ℕ) :
    ∑ l ∈ range (i + 1), ext P i l * ext Q l j = if i = j then 1 else 0 := by
  by_cases hi : i < 5
  · by_cases hj : j < 5
    · exact hblock i j hi hj
    · rw [if_neg (by omega)]
      refine Finset.sum_eq_zero (fun l hl => ?_)
      have hl' : l < j := by
        have := Finset.mem_range.mp hl
        omega
      rw [hQ l j hl', mul_zero]
  · rw [Finset.sum_eq_single i]
    · rw [ext_tail P i i (by omega), if_pos rfl, one_mul, ext_tail Q i j (by omega)]
    · intro l _ hli
      rw [ext_tail P i l (by omega), if_neg (Ne.symm hli), zero_mul]
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by omega)) hmem

theorem A_B_inv : InvPair A B := by
  refine ⟨ext_inv Mrows Minvrows B_lower ?_, ext_inv Minvrows Mrows A_lower ?_⟩
  · intro i j hi hj
    interval_cases i <;> interval_cases j <;>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] <;> decide
  · intro i j hi hj
    interval_cases i <;> interval_cases j <;>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] <;> decide

/-- At `(p, r, n, k) = (2, 0, 2, 0)` the inverse has `L = B₂₀ B₄₁ B₃₂ = 1·(−3)·(−1) = 3`. -/
theorem B_L : L 2 0 2 0 B = 3 := by
  simp only [L, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  decide

/-- … and `R = B₄₂ B₂₁ B₃₀ = 2·(−1)·(−1) = 2`. -/
theorem B_R : R 2 0 2 0 B = 2 := by
  simp only [R, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  decide

theorem B_not_sdr3 : ¬ SDR 3 B := by
  intro h
  have := h 2 0 2 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [B_L, B_R] at this
  norm_num at this

/-- **MathDB #317353: Sun's Conjecture 2.6 is false** — already at `m = 3`, over the integers. -/
theorem not_sunConj26 : ¬ SunConj26 := fun h =>
  B_not_sdr3 (h A B A_lower B_lower A_B_inv A_sdr3)

end Principia.MathDB.P317353
