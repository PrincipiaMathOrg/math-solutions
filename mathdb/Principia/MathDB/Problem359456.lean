import Mathlib

/-!
# MathDB #359456 — the Rico–Życzkowski nonlinear measurement monotone fails

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/359456/solution.tex`, refuting Conjecture 1 of Rico and Życzkowski:
for a blockwise probability vector `P = (P₁, …, Pₙ)` of positive semidefinite `d × d` matrices
summing to `I` and a blockwise bistochastic `B` (positive semidefinite blocks, every block row and
column summing to `I`), put `Qᵢ = ∑ⱼ Pⱼ^{1/2} Bᵢⱼ Pⱼ^{1/2}`.  Then for every ordering of the `Qᵢ`
some ordering of the `Pᵢ` satisfies
`‖∑_{i ≤ k} (Pᵢ − I/n)‖₂ ≥ ‖∑_{i ≤ k} (Qᵢ − I/n)‖₂` for all `1 ≤ k ≤ n`.

**What is refuted.**  `RZConj` is the conjecture for complex `3 × 3` blocks and `n = 3` only (a
restriction, hence weaker), with `P^{1/2}` Mathlib's `CFC.sqrt` for the matrix order and the
Hilbert–Schmidt norm compared through its square `re tr(XᴴX)` (norms are nonnegative, so this is
equivalent).

**The witness (the write-up's).**  `Pⱼ = diag(pⱼ)/12` with `pⱼ` having `10` in place `j` and `1`
elsewhere, and `Bᵢⱼ = P_{i+j}` (indices mod 3).  `sqrt_diag` computes the square roots, so
`Q₀ = (17/24) I` (`Q0_eq`).  For the identity ordering of the `Q`, the `k = 1` inequality needs some
`Pⱼ` with `‖Pⱼ − I/3‖² ≥ ‖Q₀ − I/3‖²`, but the left side is `3/8 = 24/64` for every `j` and the
right side is `27/64`.  All values were checked in exact rational arithmetic.
-/

namespace Principia.MathDB.P359456

open Matrix Finset
open scoped MatrixOrder ComplexOrder

/-- Complex `3 × 3` matrices. -/
abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ

/-- A blockwise probability vector: positive semidefinite blocks summing to `I`. -/
def IsProbVec (P : Fin 3 → M3) : Prop := (∀ j, (P j).PosSemidef) ∧ ∑ j, P j = 1

/-- A blockwise bistochastic matrix. -/
def IsBistoch (B : Fin 3 → Fin 3 → M3) : Prop :=
  (∀ i j, (B i j).PosSemidef) ∧ (∀ i, ∑ j, B i j = 1) ∧ ∀ j, ∑ i, B i j = 1

/-- The sequential product `Qᵢ = ∑ⱼ Pⱼ^{1/2} Bᵢⱼ Pⱼ^{1/2}`. -/
noncomputable def seqProd (B : Fin 3 → Fin 3 → M3) (P : Fin 3 → M3) (i : Fin 3) : M3 :=
  ∑ j, CFC.sqrt (P j) * B i j * CFC.sqrt (P j)

/-- The squared Hilbert–Schmidt norm `re tr(XᴴX)`. -/
noncomputable def hs2 (X : M3) : ℝ := (Xᴴ * X).trace.re

/-- `∑_{i < k} (X_{σ i} − I/3)`. -/
noncomputable def psum (X : Fin 3 → M3) (σ : Equiv.Perm (Fin 3)) (k : ℕ) : M3 :=
  ∑ i ∈ univ.filter (fun i : Fin 3 => (i : ℕ) < k), (X (σ i) - (1 / 3 : ℂ) • 1)

/-- Conjecture 1 of Rico–Życzkowski for `n = d = 3`. -/
def RZConj : Prop :=
  ∀ P B, IsProbVec P → IsBistoch B → ∀ τ : Equiv.Perm (Fin 3), ∃ σ : Equiv.Perm (Fin 3),
    ∀ k : ℕ, 1 ≤ k → k ≤ 3 → hs2 (psum (seqProd B P) τ k) ≤ hs2 (psum P σ k)

/-- The diagonal of `Pⱼ`. -/
noncomputable def pv (j : Fin 3) : Fin 3 → ℝ := fun i => if i = j then 10 / 12 else 1 / 12

/-- `Pⱼ = diag(pⱼ)`. -/
noncomputable def P (j : Fin 3) : M3 := diagonal fun i => ((pv j i : ℝ) : ℂ)

/-- `Bᵢⱼ = P_{i+j}`. -/
noncomputable def B (i j : Fin 3) : M3 := P (i + j)

theorem pv_nonneg (j i : Fin 3) : 0 ≤ pv j i := by
  unfold pv
  split_ifs <;> norm_num

theorem diag_psd (v : Fin 3 → ℝ) (hv : ∀ i, 0 ≤ v i) :
    (diagonal fun i => ((v i : ℝ) : ℂ)).PosSemidef :=
  posSemidef_diagonal_iff.2 fun i => Complex.zero_le_real.2 (hv i)

theorem sqrt_diag (v : Fin 3 → ℝ) (hv : ∀ i, 0 ≤ v i) :
    CFC.sqrt (diagonal fun i => ((v i : ℝ) : ℂ))
      = diagonal fun i => ((Real.sqrt (v i) : ℝ) : ℂ) := by
  rw [CFC.sqrt_eq_iff _ _ (nonneg_iff_posSemidef.2 (diag_psd v hv))
    (nonneg_iff_posSemidef.2 (diag_psd _ fun i => Real.sqrt_nonneg _)), diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hv i)]

theorem sandwich (v w : Fin 3 → ℝ) (hv : ∀ i, 0 ≤ v i) :
    diagonal (fun i => ((Real.sqrt (v i) : ℝ) : ℂ)) * diagonal (fun i => ((w i : ℝ) : ℂ))
      * diagonal (fun i => ((Real.sqrt (v i) : ℝ) : ℂ))
      = diagonal fun i => ((v i * w i : ℝ) : ℂ) := by
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [mul_right_comm, ← Complex.ofReal_mul, Real.mul_self_sqrt (hv i), Complex.ofReal_mul]

theorem sum_P : ∑ j, P j = 1 := by
  rw [Fin.sum_univ_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [P, pv, diagonal] <;> norm_num

theorem P_prob : IsProbVec P :=
  ⟨fun j => diag_psd (pv j) (pv_nonneg j), sum_P⟩

theorem B_bistoch : IsBistoch B := by
  refine ⟨fun i j => diag_psd (pv (i + j)) (pv_nonneg (i + j)), fun i => ?_, fun j => ?_⟩
  · simp only [B]
    rw [show (∑ j, P (i + j)) = ∑ j, P j from Equiv.sum_comp (Equiv.addLeft i) P, sum_P]
  · simp only [B]
    rw [show (∑ i, P (i + j)) = ∑ i, P i from Equiv.sum_comp (Equiv.addRight j) P, sum_P]

theorem Q0_eq : seqProd B P 0 = diagonal fun _ => ((17 / 24 : ℝ) : ℂ) := by
  unfold seqProd
  rw [Fin.sum_univ_three]
  simp only [B, zero_add]
  unfold P
  rw [sqrt_diag (pv 0) (pv_nonneg 0), sqrt_diag (pv 1) (pv_nonneg 1),
    sqrt_diag (pv 2) (pv_nonneg 2), sandwich (pv 0) (pv 0) (pv_nonneg 0),
    sandwich (pv 1) (pv 1) (pv_nonneg 1), sandwich (pv 2) (pv 2) (pv_nonneg 2)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pv, diagonal] <;> norm_num

theorem diag_sub (v : Fin 3 → ℝ) :
    diagonal (fun i => ((v i : ℝ) : ℂ)) - (1 / 3 : ℂ) • 1
      = diagonal fun i => ((v i - 1 / 3 : ℝ) : ℂ) := by
  ext a b
  rcases eq_or_ne a b with rfl | hab
  · simp
  · simp [hab]

theorem hs2_diag (v : Fin 3 → ℝ) : hs2 (diagonal fun i => ((v i : ℝ) : ℂ)) = ∑ i, v i ^ 2 := by
  simp [hs2, diagonal_conjTranspose, diagonal_mul_diagonal, Fin.sum_univ_three, sq]
  try ring

theorem hs_P (j : Fin 3) : hs2 (P j - (1 / 3 : ℂ) • 1) = 3 / 8 := by
  rw [P, diag_sub, hs2_diag]
  fin_cases j <;> simp [pv, Fin.sum_univ_three] <;> norm_num

theorem hs_Q0 : hs2 (seqProd B P 0 - (1 / 3 : ℂ) • 1) = 27 / 64 := by
  rw [Q0_eq, diag_sub, hs2_diag]
  norm_num [Fin.sum_univ_three]

theorem psum_one (X : Fin 3 → M3) (σ : Equiv.Perm (Fin 3)) :
    psum X σ 1 = X (σ 0) - (1 / 3 : ℂ) • 1 := by
  have hf : univ.filter (fun i : Fin 3 => (i : ℕ) < 1) = {0} := by decide
  rw [psum, hf, sum_singleton]

/-- **MathDB #359456: Conjecture 1 of Rico–Życzkowski is false** (already for `n = d = 3`). -/
theorem not_rzConj : ¬ RZConj := by
  intro h
  obtain ⟨σ, hσ⟩ := h P B P_prob B_bistoch 1
  have h1 := hσ 1 le_rfl (by norm_num)
  rw [psum_one, psum_one, Equiv.Perm.one_apply, hs_Q0, hs_P] at h1
  norm_num at h1

end Principia.MathDB.P359456
