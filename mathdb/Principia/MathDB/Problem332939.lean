import Mathlib

/-!
# MathDB #332939 — Lin's additive majorization conjecture fails for `p = 4` in dimension three

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/332939/solution.tex`, refuting Conjecture 4.3 of M. Lin: for positive
semidefinite `A, B` and every `p > 0`, `λ(A² + |BA|^p) ≻ λ(A² + |AB|^p)` (majorization of the
decreasingly ordered eigenvalues), where `|Z| = (Z*Z)^{1/2}`.

**What is refuted, and why it is stated weakly.**  Majorization includes equal traces, so it forces
`λ₁ + λ₂` of the left matrix to dominate that of the right, hence `λ_min(L) ≤ λ_min(R)`.  That is
equivalent to: for every `c`, `L − cI ≻ 0` implies `R − cI ≻ 0`.  `LminConj` states only this
consequence, only for real `3 × 3` matrices, and only at `p = 4`, where `|X|⁴ = (XᴴX)²` exactly
(`absPow4`).  Each restriction weakens the statement, so refuting it refutes the conjecture.

**The witness (the write-up's).**  `A = diag(1, 2, 20)`, `B = M/5` with
`M = [[6, −1, 1], [−1, 2, 1], [1, 1, 1]]`.  Then `L − (142/25)I` is positive definite (its `LDLᵀ`
pivots `2623/125, 4042206/8196875, 3046358174/50527575` are positive; `TL_posDef` uses the
corresponding sum of squares), while `vᵀ(R − (142/25)I)v = −73/625` for `v = (1, −1, 0)`.  All
matrices and certificates were checked in SymPy.
-/

namespace Principia.MathDB.P332939

open Matrix

/-- `|X|⁴ = (XᴴX)²`. -/
noncomputable def absPow4 (X : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (Xᴴ * X) ^ 2

/-- The consequence `λ_min(A² + |BA|⁴) ≤ λ_min(A² + |AB|⁴)` of Conjecture 4.3 at `p = 4`. -/
def LminConj : Prop :=
  ∀ A B : Matrix (Fin 3) (Fin 3) ℝ, A.PosSemidef → B.PosSemidef → ∀ c : ℝ,
    (A ^ 2 + absPow4 (B * A) - c • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef →
      (A ^ 2 + absPow4 (A * B) - c • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef

/-- `A = diag(1, 2, 20)`. -/
def A : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 2, 0; 0, 0, 20]

/-- `B = M/5`. -/
noncomputable def B : Matrix (Fin 3) (Fin 3) ℝ :=
  !![6 / 5, -1 / 5, 1 / 5; -1 / 5, 2 / 5, 1 / 5; 1 / 5, 1 / 5, 1 / 5]

/-- `L − (142/25)I`, entrywise. -/
noncomputable def TL : Matrix (Fin 3) (Fin 3) ℝ :=
  !![13115 / 625, 8732 / 625, 147440 / 625; 8732 / 625, 6122 / 625, 96240 / 625;
    147440 / 625, 96240 / 625, 1707250 / 625]

/-- `R − (142/25)I`, entrywise. -/
noncomputable def TR : Matrix (Fin 3) (Fin 3) ℝ :=
  !![501275 / 625, 494416 / 625, 496792 / 625; 494416 / 625, 487484 / 625, 489726 / 625;
    496792 / 625, 489726 / 625, 737728 / 625]

theorem L_eq : A ^ 2 + absPow4 (B * A) - (142 / 25 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) = TL := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, B, TL, absPow4, sq, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.conjTranspose_apply] <;> norm_num

theorem R_eq : A ^ 2 + absPow4 (A * B) - (142 / 25 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) = TR := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, B, TR, absPow4, sq, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.conjTranspose_apply] <;> norm_num

theorem ne_zero_cases (x : Fin 3 → ℝ) (hx : x ≠ 0) : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
  by_contra h
  push_neg at h
  apply hx
  funext i
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem A_psd : A.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · unfold Matrix.IsHermitian
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A]
  · simp only [A, dotProduct, mulVec, Fin.sum_univ_three, star_trivial]
    simp
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

theorem B_psd : B.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · unfold Matrix.IsHermitian
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B]
  · have hq : star x ⬝ᵥ (B *ᵥ x) = (1 / 5) * (6 * (x 0 - x 1 / 6 + x 2 / 6) ^ 2
        + 11 / 6 * (x 1 + 7 / 11 * x 2) ^ 2 + 1 / 11 * x 2 ^ 2) := by
      simp [B, dotProduct, mulVec, Fin.sum_univ_three]
      ring
    rw [hq]
    positivity

theorem TL_posDef : TL.PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · unfold Matrix.IsHermitian
    ext i j
    fin_cases i <;> fin_cases j <;> simp [TL]
  · have hq : star x ⬝ᵥ (TL *ᵥ x) = 2623 / 125 * (x 0 + 8732 / 13115 * x 1 + 29488 / 2623 * x 2) ^ 2
        + 4042206 / 8196875 * (x 1 - 12629240 / 2021103 * x 2) ^ 2
        + 3046358174 / 50527575 * x 2 ^ 2 := by
      simp [TL, dotProduct, mulVec, Fin.sum_univ_three]
      ring
    rw [hq]
    by_contra hle
    push_neg at hle
    have s1 := sq_nonneg (x 0 + 8732 / 13115 * x 1 + 29488 / 2623 * x 2)
    have s2 := sq_nonneg (x 1 - 12629240 / 2021103 * x 2)
    have s3 := sq_nonneg (x 2)
    have h2 : x 2 = 0 := by
      have : x 2 ^ 2 = 0 := by nlinarith
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    have h1 : x 1 = 0 := by
      have : (x 1 - 12629240 / 2021103 * x 2) ^ 2 = 0 := by nlinarith
      have := pow_eq_zero_iff two_ne_zero |>.1 this
      rw [h2] at this
      linarith
    have h0 : x 0 = 0 := by
      have : (x 0 + 8732 / 13115 * x 1 + 29488 / 2623 * x 2) ^ 2 = 0 := by nlinarith
      have := pow_eq_zero_iff two_ne_zero |>.1 this
      rw [h1, h2] at this
      linarith
    rcases ne_zero_cases x hx with h | h | h
    · exact h h0
    · exact h h1
    · exact h h2

/-- **MathDB #332939: Lin's Conjecture 4.3 is false** (already its `λ_min` consequence at `p = 4`,
for real `3 × 3` matrices). -/
theorem not_lminConj : ¬ LminConj := by
  intro h
  have hR := h A B A_psd B_psd (142 / 25) (by rw [L_eq]; exact TL_posDef)
  rw [R_eq] at hR
  have hv : (![1, -1, 0] : Fin 3 → ℝ) ≠ 0 := fun hv => by
    have := congrFun hv 0
    simp at this
  have := hR.dotProduct_mulVec_pos hv
  simp [TR, dotProduct, mulVec, Fin.sum_univ_three] at this
  norm_num at this

end Principia.MathDB.P332939
