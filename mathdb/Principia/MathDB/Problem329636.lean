import Mathlib

/-!
# MathDB #329636 — the squared Diaz–Metcalf inequality for positive linear maps fails

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/329636/solution.tex`, refuting Conjecture 2.16 of Moslehian and Fu:
for every unital positive linear map `Φ` and positive definite `A, B` with `m₁² I ≤ A ≤ M₁² I`,
`m₂² I ≤ B ≤ M₂² I`, both a squared Pólya–Szegö inequality and the squared Diaz–Metcalf inequality
`((M₂m₂)/(M₁m₁) Φ(A) + Φ(B))² ≤ (M₂/m₁ + m₂/M₁)² Φ(A#B)²` hold, where
`A#B = A^{1/2}(A^{-1/2}BA^{-1/2})^{1/2}A^{1/2}`.

**What is refuted.**  `DMConj` is the Diaz–Metcalf half alone (the conjecture asserts both halves),
for `3 × 3` complex matrices and only the maps `Φ(X) = VᴴXV` with `VᴴV = I`, `V ∈ ℂ^{3×2}` (unital
completely positive, hence unital positive), with `A^{1/2} = CFC.sqrt A`, `A^{-1/2}` its inverse,
and `≤` the Loewner order (`open scoped MatrixOrder`).  Each restriction weakens the statement.

**The witness (the write-up's).**  `A = diag(1, 9/4, 4)`, `B = I`, `m₁ = 1`, `M₁ = 2`,
`m₂ = M₂ = 1`, `V = (1/3)[[2, 1], [1, 2], [2, −2]]`.  Then `A#B = diag(1, 3/2, 2)` (`gm_eq`),
`R = Φ(A#B) = [[3/2, −1/3], [−1/3, 5/3]]`, `S = Φ(A)/2 + I = [[161/72, −19/36], [−19/36, 22/9]]`,
and `vᴴ((9/4)R² − S²)v = −113/5184` for `v = (3, −1)`.  All values were checked in SymPy.

**Absent:** the write-up's counterexample to the Pólya–Szegö half (an irrational geometric mean).
-/

namespace Principia.MathDB.P329636

open Matrix
open scoped MatrixOrder ComplexOrder

/-- Complex `3 × 3` matrices. -/
abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ

/-- The geometric mean `A#B = A^{1/2}(A^{-1/2}BA^{-1/2})^{1/2}A^{1/2}`. -/
noncomputable def gm (A B : M3) : M3 :=
  CFC.sqrt A * CFC.sqrt ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹) * CFC.sqrt A

/-- The squared Diaz–Metcalf half of Conjecture 2.16, for `Φ(X) = VᴴXV` with `VᴴV = I`. -/
def DMConj : Prop :=
  ∀ (A B : M3) (m₁ M₁ m₂ M₂ : ℝ), 0 < m₁ → m₁ ≤ M₁ → 0 < m₂ → m₂ ≤ M₂ →
    A.PosDef → B.PosDef →
    ((m₁ ^ 2 : ℝ) : ℂ) • (1 : M3) ≤ A → A ≤ ((M₁ ^ 2 : ℝ) : ℂ) • (1 : M3) →
    ((m₂ ^ 2 : ℝ) : ℂ) • (1 : M3) ≤ B → B ≤ ((M₂ ^ 2 : ℝ) : ℂ) • (1 : M3) →
    ∀ V : Matrix (Fin 3) (Fin 2) ℂ, Vᴴ * V = 1 →
      (((M₂ * m₂ / (M₁ * m₁) : ℝ) : ℂ) • (Vᴴ * A * V) + Vᴴ * B * V) ^ 2
        ≤ (((M₂ / m₁ + m₂ / M₁) ^ 2 : ℝ) : ℂ) • (Vᴴ * gm A B * V) ^ 2

/-- The diagonal of `A`. -/
noncomputable def av : Fin 3 → ℝ := ![1, 9 / 4, 4]

/-- The diagonal of `A^{1/2}` (and of `A#I`). -/
noncomputable def gv : Fin 3 → ℝ := ![1, 3 / 2, 2]

/-- `A = diag(1, 9/4, 4)`. -/
noncomputable def A : M3 := diagonal fun i => ((av i : ℝ) : ℂ)

/-- `V = (1/3)[[2, 1], [1, 2], [2, −2]]`. -/
noncomputable def V : Matrix (Fin 3) (Fin 2) ℂ :=
  (!![2 / 3, 1 / 3; 1 / 3, 2 / 3; 2 / 3, -2 / 3] : Matrix (Fin 3) (Fin 2) ℝ).map fun x => (x : ℂ)

theorem gv_pos (i : Fin 3) : 0 < gv i := by
  fin_cases i <;> simp [gv] <;> norm_num

theorem av_pos (i : Fin 3) : 0 < av i := by
  fin_cases i <;> simp [av] <;> norm_num

theorem diag_psd (v : Fin 3 → ℝ) (hv : ∀ i, 0 ≤ v i) :
    (diagonal fun i => ((v i : ℝ) : ℂ)).PosSemidef :=
  posSemidef_diagonal_iff.2 fun i => Complex.zero_le_real.2 (hv i)

theorem sqrt_diag (v w : Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i) (hvw : ∀ i, w i * w i = v i) :
    CFC.sqrt (diagonal fun i => ((v i : ℝ) : ℂ)) = diagonal fun i => ((w i : ℝ) : ℂ) := by
  have hv : ∀ i, 0 ≤ v i := fun i => hvw i ▸ mul_nonneg (hw i) (hw i)
  rw [CFC.sqrt_eq_iff _ _ (nonneg_iff_posSemidef.2 (diag_psd v hv))
    (nonneg_iff_posSemidef.2 (diag_psd w hw)), diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Complex.ofReal_mul, hvw i]

theorem inv_diag (w : Fin 3 → ℝ) (hw : ∀ i, w i ≠ 0) :
    (diagonal fun i => ((w i : ℝ) : ℂ))⁻¹ = diagonal fun i => (((w i)⁻¹ : ℝ) : ℂ) := by
  apply Matrix.inv_eq_left_inv
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hw i), Complex.ofReal_one]

theorem gm_eq : gm A 1 = diagonal fun i => ((gv i : ℝ) : ℂ) := by
  have hsq : CFC.sqrt A = diagonal fun i => ((gv i : ℝ) : ℂ) :=
    sqrt_diag av gv (fun i => (gv_pos i).le) fun i => by
      fin_cases i <;> simp [gv, av] <;> norm_num
  unfold gm
  rw [hsq, inv_diag gv fun i => (gv_pos i).ne', Matrix.mul_one, diagonal_mul_diagonal]
  simp only [← Complex.ofReal_mul]
  rw [sqrt_diag (fun i => (gv i)⁻¹ * (gv i)⁻¹) (fun i => (gv i)⁻¹)
    (fun i => (inv_pos.2 (gv_pos i)).le) fun i => rfl, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, mul_inv_cancel₀ (gv_pos i).ne', one_mul]

theorem V_isometry : Vᴴ * V = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [V, Matrix.mul_apply, Fin.sum_univ_three, conjTranspose_apply] <;> norm_num

theorem scal_one (r : ℝ) : ((r : ℝ) : ℂ) • (1 : M3) = diagonal fun _ => ((r : ℝ) : ℂ) := by
  ext a b
  rcases eq_or_ne a b with rfl | hab
  · simp
  · simp [hab]

theorem diag_le (u v : Fin 3 → ℝ) (h : ∀ i, u i ≤ v i) :
    diagonal (fun i => ((u i : ℝ) : ℂ)) ≤ diagonal fun i => ((v i : ℝ) : ℂ) := by
  rw [le_iff, diagonal_sub]
  have e : (fun i => ((v i : ℝ) : ℂ) - ((u i : ℝ) : ℂ)) = fun i => ((v i - u i : ℝ) : ℂ) := by
    funext i
    push_cast
    ring
  rw [e]
  exact diag_psd _ fun i => sub_nonneg.2 (h i)

theorem A_posDef : A.PosDef :=
  posDef_diagonal_iff.2 fun i => Complex.zero_lt_real.2 (av_pos i)

theorem R_eq : Vᴴ * gm A 1 * V = !![3 / 2, -1 / 3; -1 / 3, 5 / 3] := by
  rw [gm_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [V, gv, Matrix.mul_apply, Fin.sum_univ_three, conjTranspose_apply, diagonal] <;> norm_num

theorem S_eq : (((1 * 1 / (2 * 1) : ℝ) : ℂ) • (Vᴴ * A * V) + Vᴴ * (1 : M3) * V
      : Matrix (Fin 2) (Fin 2) ℂ) = !![161 / 72, -19 / 36; -19 / 36, 22 / 9] := by
  rw [Matrix.mul_one, V_isometry]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [V, A, av, Matrix.mul_apply, Fin.sum_univ_three, conjTranspose_apply, diagonal] <;>
    norm_num

/-- **MathDB #329636: the squared Diaz–Metcalf half of Conjecture 2.16 is false.** -/
theorem not_dmConj : ¬ DMConj := by
  intro h
  have hA1 : ((1 ^ 2 : ℝ) : ℂ) • (1 : M3) ≤ A := by
    rw [scal_one, A]
    exact diag_le _ _ fun i => by
      fin_cases i <;> simp [av] <;> norm_num
  have hA2 : A ≤ ((2 ^ 2 : ℝ) : ℂ) • (1 : M3) := by
    rw [scal_one, A]
    exact diag_le _ _ fun i => by
      fin_cases i <;> simp [av] <;> norm_num
  have hB : ((1 ^ 2 : ℝ) : ℂ) • (1 : M3) ≤ 1 := le_of_eq (by simp)
  have hB' : (1 : M3) ≤ ((1 ^ 2 : ℝ) : ℂ) • (1 : M3) := le_of_eq (by simp)
  have hle := h A 1 1 2 1 1 one_pos (by norm_num) one_pos le_rfl A_posDef PosDef.one
    hA1 hA2 hB hB' V V_isometry
  rw [S_eq, R_eq, le_iff] at hle
  have hv := hle.dotProduct_mulVec_nonneg ![3, -1]
  have hval : star (![3, -1] : Fin 2 → ℂ) ⬝ᵥ
      (((((1 / 1 + 1 / 2) ^ 2 : ℝ) : ℂ)
          • (!![3 / 2, -1 / 3; -1 / 3, 5 / 3] : Matrix (Fin 2) (Fin 2) ℂ) ^ 2
          - (!![161 / 72, -19 / 36; -19 / 36, 22 / 9] : Matrix (Fin 2) (Fin 2) ℂ) ^ 2)
        *ᵥ ![3, -1]) = ((-113 / 5184 : ℝ) : ℂ) := by
    norm_num [sq, Matrix.mul_apply, Fin.sum_univ_two, dotProduct, mulVec, map_ofNat]
  rw [hval] at hv
  have := Complex.zero_le_real.1 hv
  norm_num at this

end Principia.MathDB.P329636
