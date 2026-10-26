import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic

/-!
# MathDB #336488 — a strictly positive premagic matrix that is NOT diagonalizable

Write-up: `mathdb-open-problems/problems/336488/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (added 2026-09-27; this row
was not in the campaign table until 2026-09-28, see the README's scope block).
Source: K. Teknomo, *Premagic and Ideal Flow Matrices*, **Conjecture 7.2** — every premagic
matrix is diagonalizable and has a full set of independent eigenvectors.  A matrix is
*premagic* when its vector of row sums equals its vector of column sums (Definition 4.3).

**The conjecture is FALSE, and this file refutes it with no carried hypothesis.**  The witness
is the write-up's own matrix

`M = !![4, 4, 1; 2, 2, 5; 3, 3, 3]`,

strictly positive, with every row sum and every column sum equal to `9`.  `Mf K` is the same
matrix read in an arbitrary field, which is where the `ℝ` and `ℂ` statements come from.

## The certificate is TWO matrix identities, and that is the whole proof

The write-up refutes the conjecture by exhibiting a basis `B = (j u v)` with `det B = 6`, the
similarity `M B = B J` for an explicit Jordan form, the characteristic polynomial `x²(x − 9)`,
and both eigenspaces.  **None of that is needed.**  The identities

`M ^ 3 = 9 • M ^ 2`   and   `M ^ 2 ≠ 9 • M`

are by themselves incompatible with diagonalizability: for a diagonal matrix the first forces
`d ^ 2 * (d − 9) = 0` entrywise, hence `d = 0` or `d = 9`, hence `d ^ 2 = 9 * d`, hence the
second must fail.  So `sq_eq_smul_of_cube_eq_smul_sq` carries the entire argument and mentions
no eigenvalue, no eigenvector, no characteristic polynomial and no Jordan form.  (The
write-up's own route was checked independently in
`Campaigns/MathDB-Formalization/verify_336488.py`: `det B = 6` and `M B = B J` both hold, so
this is a *lighter* proof of a correct claim, not a correction of a wrong one.)

`sq_eq_smul_of_cube_eq_smul_sq`, `pow_mul_eq` and the two cancellation lemmas assert nothing
about premagic matrices and are **`Common/` promotion candidates**; they are kept here for now
so that this row lands behind a single gate.

## What the write-up claims, clause by clause

Its Theorem is clause (1).  Its Proposition adds three more.  **All four are proved here**,
which is the whole of the write-up's mathematical content:

1. `M` is premagic and not diagonalizable, **over any field with `(9 : K) ≠ 0` and in
   particular over `ℝ` and `ℂ`** — `M_premagic`, `M_not_diagonalizable` over `ℚ`, and then
   `Mf_premagic`, `Mf_not_diagonalizable`, `Mf_not_diagonalizable_real`,
   `Mf_not_diagonalizable_complex`, packaged as `conjecture_7_2_false_real` and
   `conjecture_7_2_false_complex`. **Proved.**  The field version is not decoration: **a rational
   counterexample is not automatically a real one**, since a rational matrix can fail to be similar
   to a *rational* diagonal matrix and still be diagonalizable over `ℝ`.  Teknomo's matrices are
   real and the write-up says *"even over `ℂ`"*, so the `ℚ`-only statement would have claimed less
   than the row does.
2. `M / 9` is strictly positive doubly stochastic and not diagonalizable —
   `Mds_doublyStochastic`, `Mds_pos`, `Mds_not_diagonalizable`. **Proved.**
3. for every `t > 0`, `M + t • 1` is strictly positive, premagic, has determinant
   `(9 + t) * t ^ 2` (hence is invertible) and is not diagonalizable — `Mshift_pos`,
   `Mshift_premagic`, `Mshift_det`, `Mshift_not_diagonalizable`. **Proved.**
4. *"No real premagic matrix of order less than three is defective."*  **Proved, in both halves.**
   `premagic_two_isSymm` is the write-up's own argument — premagic on a `2 × 2` reads
   `a + b = a + c`, so `b = c` — and `isSymm_two_diagonalizable` does the remaining step **by hand
   with an explicit eigenbasis** rather than through the spectral theorem: eigenvalues
   `((a + c) ± s) / 2` with `s = √((a − c)² + 4b²)`, eigenvectors `(λ − c, b)`, and `det = b · s`,
   nonzero because `b ≠ 0` in the branch where the matrix is not already diagonal and `s > 0`
   there.  `premagic_two_diagonalizable` and `premagic_one_diagonalizable` are the two orders
   below three.  Mathlib's `Matrix.IsHermitian.spectral_theorem` would also do it, but it lives in
   `Mathlib.Analysis.Matrix.Spectrum` and is stated through `conjStarAlgAut` and
   `RCLike.ofReal ∘ eigenvalues`, so using it would have cost both a bridge and the whole
   inner-product-space import closure; the explicit route needs only `Real.sqrt`.

## Why `Diagonalizable` avoids inverses

`Diagonalizable A` is `∃ P d, IsUnit P.det ∧ A * P = P * diagonal d`.  Stating similarity
multiplicatively keeps `Matrix.inv` — whose `Ring.inverse`-based definition carries a side
condition at every use — out of every proof below; all that is ever needed is cancellation of
an invertible factor, from `Matrix.invertibleOfIsUnitDet` with `mul_invOf_self`.
-/

namespace Principia.MathDB.P336488

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix is **premagic** when its vector of row sums equals its vector of column sums;
Teknomo's Definition 4.3, `A 1 = Aᵀ 1`. -/
def Premagic {R : Type*} [Semiring R] (A : Matrix n n R) : Prop :=
  A *ᵥ (fun _ => (1 : R)) = Aᵀ *ᵥ (fun _ => (1 : R))

/-- `A` is **diagonalizable** when it is similar to a diagonal matrix, stated multiplicatively
so that no matrix inverse occurs. -/
def Diagonalizable {R : Type*} [CommRing R] (A : Matrix n n R) : Prop :=
  ∃ (P : Matrix n n R) (d : n → R), IsUnit P.det ∧ A * P = P * diagonal d

/-! ### Cancelling an invertible factor -/

/-- Left-cancel an invertible matrix. -/
theorem mul_left_cancel_of_isUnit_det {R : Type*} [CommRing R] {A B P : Matrix n n R}
    (hP : IsUnit P.det) (h : P * A = P * B) : A = B := by
  haveI := invertibleOfIsUnitDet P hP
  calc A = ⅟ P * (P * A) := by rw [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]
    _ = ⅟ P * (P * B) := by rw [h]
    _ = B := by rw [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]

/-- Right-cancel an invertible matrix. -/
theorem mul_right_cancel_of_isUnit_det {R : Type*} [CommRing R] {A B P : Matrix n n R}
    (hP : IsUnit P.det) (h : A * P = B * P) : A = B := by
  haveI := invertibleOfIsUnitDet P hP
  calc A = A * P * ⅟ P := by rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]
    _ = B * P * ⅟ P := by rw [h]
    _ = B := by rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]

/-! ### The engine: a diagonalizable matrix cannot carry a repeated root at the top -/

/-- A similarity transports through powers, kept in `diagonal (…)` form throughout. -/
theorem pow_mul_eq {R : Type*} [CommRing R] {A P : Matrix n n R} {d : n → R}
    (h : A * P = P * diagonal d) (k : ℕ) : A ^ k * P = P * diagonal (d ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc A ^ (k + 1) * P = A ^ k * (A * P) := by rw [pow_succ, Matrix.mul_assoc]
      _ = A ^ k * P * diagonal d := by rw [h, ← Matrix.mul_assoc]
      _ = P * diagonal (d ^ k) * diagonal d := by rw [ih]
      _ = P * (diagonal (d ^ k) * diagonal d) := by rw [Matrix.mul_assoc]
      _ = P * diagonal (d ^ (k + 1)) := by
          -- `diagonal_mul_diagonal` returns the LAMBDA form `fun i => d i ^ k * d i`, which is
          -- only definitionally the Pi-product, so `rw`'s closing `rfl` does not see it.
          rw [diagonal_mul_diagonal]
          have hfun : (fun i => (d ^ k) i * d i) = d ^ (k + 1) := by
            funext i
            simp [pow_succ]
          rw [hfun]

/-- **THE WHOLE ARGUMENT.**  A diagonalizable matrix satisfying `A ^ 3 = c • A ^ 2` already
satisfies `A ^ 2 = c • A`.  Contrapositive: a matrix with the cube identity and *without* the
square identity is not diagonalizable — no eigenvalue, eigenvector, characteristic polynomial
or Jordan form anywhere in the statement or the proof. -/
theorem sq_eq_smul_of_cube_eq_smul_sq {K : Type*} [Field K] {A : Matrix n n K} {c : K}
    (hd : Diagonalizable A) (h3 : A ^ 3 = c • A ^ 2) : A ^ 2 = c • A := by
  obtain ⟨P, d, hP, hAP⟩ := hd
  have h2 : A ^ 2 * P = P * diagonal (d ^ 2) := pow_mul_eq hAP 2
  -- Step 1: push the cube identity onto the diagonal.
  have hcube : P * diagonal (d ^ 3) = P * diagonal (c • d ^ 2) := by
    calc P * diagonal (d ^ 3) = A ^ 3 * P := (pow_mul_eq hAP 3).symm
      _ = (c • A ^ 2) * P := by rw [h3]
      _ = c • (A ^ 2 * P) := by rw [Matrix.smul_mul]
      _ = c • (P * diagonal (d ^ 2)) := by rw [h2]
      _ = P * (c • diagonal (d ^ 2)) := by rw [Matrix.mul_smul]
      _ = P * diagonal (c • d ^ 2) := by rw [diagonal_smul]
  have hfun : d ^ 3 = c • d ^ 2 :=
    diagonal_injective (mul_left_cancel_of_isUnit_det hP hcube)
  -- Step 2: entrywise, `d i ^ 2 * (d i - c) = 0`, so `d i ^ 2 = c * d i`.
  have hpt : ∀ i, d i ^ 2 = c * d i := by
    intro i
    have h3i : d i ^ 3 = c * d i ^ 2 := by
      have := congrFun hfun i
      simpa [Pi.pow_apply, Pi.smul_apply, smul_eq_mul] using this
    have hfac : d i ^ 2 * (d i - c) = 0 := by linear_combination h3i
    rcases mul_eq_zero.mp hfac with h0 | h0
    · have hz : d i = 0 := by simpa using h0
      simp [hz]
    · have hc : d i = c := by
        have := sub_eq_zero.mp h0
        exact this
      rw [hc]; ring
  -- Step 3: push the square identity back onto `A`.
  have hsq : (diagonal (d ^ 2) : Matrix n n K) = diagonal (c • d) :=
    congrArg diagonal (funext fun i => by
      simpa [Pi.pow_apply, Pi.smul_apply, smul_eq_mul] using hpt i)
  refine mul_right_cancel_of_isUnit_det (P := P) hP ?_
  calc A ^ 2 * P = P * diagonal (d ^ 2) := h2
    _ = P * diagonal (c • d) := by rw [hsq]
    _ = P * (c • diagonal d) := by rw [diagonal_smul]
    _ = c • (P * diagonal d) := by rw [Matrix.mul_smul]
    _ = c • (A * P) := by rw [hAP]
    _ = (c • A) * P := by rw [Matrix.smul_mul]

/-- The contrapositive, packaged: the two identities refute diagonalizability. -/
theorem not_diagonalizable_of_cube_of_ne {K : Type*} [Field K] {A : Matrix n n K} {c : K}
    (h3 : A ^ 3 = c • A ^ 2) (hne : A ^ 2 ≠ c • A) : ¬ Diagonalizable A :=
  fun hd => hne (sq_eq_smul_of_cube_eq_smul_sq hd h3)

/-! ### Closure properties, for the Proposition's clauses (2) and (3) -/

/-- A scalar multiple of a diagonalizable matrix is diagonalizable. -/
theorem Diagonalizable.smul {R : Type*} [CommRing R] {A : Matrix n n R} (c : R)
    (h : Diagonalizable A) : Diagonalizable (c • A) := by
  obtain ⟨P, d, hP, hAP⟩ := h
  refine ⟨P, c • d, hP, ?_⟩
  rw [Matrix.smul_mul, hAP, diagonal_smul, Matrix.mul_smul]

/-- A scalar multiple of the identity is central. -/
theorem smul_one_mul_comm {R : Type*} [CommRing R] (t : R) (P : Matrix n n R) :
    (t • (1 : Matrix n n R)) * P = P * (t • (1 : Matrix n n R)) := by
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

omit [Fintype n] in
/-- `t • 1` is the diagonal matrix with constant entry `t`. -/
theorem smul_one_eq_diagonal {R : Type*} [CommRing R] (t : R) :
    (t • (1 : Matrix n n R)) = diagonal (fun _ => t) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h, diagonal_apply_ne _ h]

/-- Subtracting a scalar multiple of the identity preserves diagonalizability. -/
theorem Diagonalizable.sub_smul_one {R : Type*} [CommRing R] {A : Matrix n n R} (t : R)
    (h : Diagonalizable A) : Diagonalizable (A - t • (1 : Matrix n n R)) := by
  obtain ⟨P, d, hP, hAP⟩ := h
  refine ⟨P, d - fun _ => t, hP, ?_⟩
  have hsub : (diagonal (d - fun _ => t) : Matrix n n R)
      = diagonal d - diagonal (fun _ => t) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [diagonal_apply_ne _ hij]
  calc (A - t • (1 : Matrix n n R)) * P = A * P - (t • (1 : Matrix n n R)) * P := by
        rw [Matrix.sub_mul]
    _ = P * diagonal d - P * (t • (1 : Matrix n n R)) := by rw [hAP, smul_one_mul_comm]
    _ = P * diagonal d - P * diagonal (fun _ => t) := by rw [smul_one_eq_diagonal]
    _ = P * (diagonal d - diagonal (fun _ => t)) := by rw [Matrix.mul_sub]
    _ = P * diagonal (d - fun _ => t) := by rw [hsub]

/-! ## The witness -/

/-- The write-up's counterexample: strictly positive, every row and column sum `9`. -/
def M : Matrix (Fin 3) (Fin 3) ℚ := !![4, 4, 1; 2, 2, 5; 3, 3, 3]

theorem M_pos : ∀ i j, 0 < M i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [M]

/-- Every row sum is `9`. -/
theorem M_rowSums : M *ᵥ (fun _ => (1 : ℚ)) = fun _ => 9 := by
  funext i
  fin_cases i <;>
    simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num

/-- Every column sum is `9`. -/
theorem M_colSums : Mᵀ *ᵥ (fun _ => (1 : ℚ)) = fun _ => 9 := by
  funext i
  fin_cases i <;>
    simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply] <;> norm_num

/-- Clause (1), first half: `M` is premagic — the row sums and the column sums are both `9`. -/
theorem M_premagic : Premagic M := by
  rw [Premagic, M_rowSums, M_colSums]

/-- `M ^ 2` is `27` times the all-ones matrix — the computation behind both identities. -/
theorem M_sq : M ^ 2 = !![27, 27, 27; 27, 27, 27; 27, 27, 27] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-- The cube identity. -/
theorem M_cube : M ^ 3 = (9 : ℚ) • M ^ 2 := by
  have h : M ^ 3 = M * M ^ 2 := by rw [← pow_succ']
  rw [h, M_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-- **THE DEFECT.**  The square identity FAILS — which a diagonalizable matrix satisfying the
cube identity could not do. -/
theorem M_sq_ne : M ^ 2 ≠ (9 : ℚ) • M := by
  intro h
  have h00 : (M ^ 2) 0 0 = ((9 : ℚ) • M) 0 0 := by rw [h]
  rw [M_sq] at h00
  norm_num [M] at h00

/-- **CLAUSE (1): Teknomo's Conjecture 7.2 is false.** -/
theorem M_not_diagonalizable : ¬ Diagonalizable M :=
  not_diagonalizable_of_cube_of_ne M_cube M_sq_ne

/-- The refutation, packaged: a strictly positive premagic matrix that is not similar to any
diagonal matrix.

**Exactly what this refutes.**  Conjecture 7.2 asserts two things, *diagonalizable* and *has a
full set of independent eigenvectors*.  What is refuted here is the first, in the form
`Diagonalizable` above — similarity to a diagonal matrix.  The two assertions are the same
statement, because the columns of `P` are exactly an eigenbasis, **but that equivalence is not
formalised in this file**, so the honest reading of this theorem is the similarity one. -/
theorem conjecture_7_2_false :
    ∃ A : Matrix (Fin 3) (Fin 3) ℚ, Premagic A ∧ (∀ i j, 0 < A i j) ∧ ¬ Diagonalizable A :=
  ⟨M, M_premagic, M_pos, M_not_diagonalizable⟩

/-! ## The same witness over ANY field, which is what *"even over `ℂ`"* requires

Everything above is over `ℚ`, and **a counterexample to the rational statement is not by itself a
counterexample to the real one** — a rational matrix can fail to be similar to a *rational* diagonal
matrix and still be diagonalizable over `ℝ`.  Teknomo's matrices are real, and the write-up's
Theorem says *"not diagonalizable, even over `ℂ`"*.  So the witness is re-read over an arbitrary
field: the two identities are numeral arithmetic and hold in every commutative ring, and the only
thing the refutation needs of the field is `(9 : K) ≠ 0`, i.e. characteristic other than `3`. -/

/-- The witness with its entries read in an arbitrary field. -/
def Mf (K : Type*) [Field K] : Matrix (Fin 3) (Fin 3) K := !![4, 4, 1; 2, 2, 5; 3, 3, 3]

theorem Mf_sq (K : Type*) [Field K] :
    (Mf K) ^ 2 = !![27, 27, 27; 27, 27, 27; 27, 27, 27] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mf, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem Mf_cube (K : Type*) [Field K] : (Mf K) ^ 3 = (9 : K) • (Mf K) ^ 2 := by
  have h : (Mf K) ^ 3 = Mf K * (Mf K) ^ 2 := by rw [← pow_succ']
  rw [h, Mf_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mf, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-- The defect survives in any field where `9 ≠ 0`: the `(0,0)` entry would force `27 = 36`. -/
theorem Mf_sq_ne (K : Type*) [Field K] (h9 : (9 : K) ≠ 0) :
    (Mf K) ^ 2 ≠ (9 : K) • Mf K := by
  intro h
  have h00 : ((Mf K) ^ 2) 0 0 = ((9 : K) • Mf K) 0 0 := by rw [h]
  rw [Mf_sq] at h00
  -- `suffices` rather than `simp … at h00`: the flexible-tactic linter is right that a `simp`
  -- rewriting a hypothesis leaves the next step depending on a shape nobody stated.
  have h27 : (27 : K) = 9 * 4 := by
    simpa [Mf] using h00
  exact h9 (by linear_combination -h27)

/-- **THE REFUTATION OVER ANY FIELD OF CHARACTERISTIC OTHER THAN THREE.** -/
theorem Mf_not_diagonalizable (K : Type*) [Field K] (h9 : (9 : K) ≠ 0) :
    ¬ Diagonalizable (Mf K) :=
  not_diagonalizable_of_cube_of_ne (Mf_cube K) (Mf_sq_ne K h9)

/-- Over `ℝ`, which is the case Teknomo's ideal-flow setting is about. -/
theorem Mf_not_diagonalizable_real : ¬ Diagonalizable (Mf ℝ) :=
  Mf_not_diagonalizable ℝ (by norm_num)

/-- And over `ℂ`, which is the write-up's *"even over `ℂ`"*. -/
theorem Mf_not_diagonalizable_complex : ¬ Diagonalizable (Mf ℂ) :=
  Mf_not_diagonalizable ℂ (by norm_num)

/-- `Mf` is premagic over any field. -/
theorem Mf_premagic (K : Type*) [Field K] : Premagic (Mf K) := by
  funext i
  fin_cases i <;>
    simp [Mf, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.transpose_apply] <;> norm_num

/-- **CLAUSE (1) IN THE FORM THE WRITE-UP STATES IT**: a premagic matrix over `ℝ`, strictly
positive, that is not diagonalizable — and the same over `ℂ`. -/
theorem conjecture_7_2_false_real :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, Premagic A ∧ (∀ i j, 0 < A i j) ∧ ¬ Diagonalizable A := by
  refine ⟨Mf ℝ, Mf_premagic ℝ, ?_, Mf_not_diagonalizable_real⟩
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Mf]

theorem conjecture_7_2_false_complex :
    ∃ A : Matrix (Fin 3) (Fin 3) ℂ, Premagic A ∧ ¬ Diagonalizable A :=
  ⟨Mf ℂ, Mf_premagic ℂ, Mf_not_diagonalizable_complex⟩

/-! ## Clause (2): the doubly stochastic scaling -/

/-- `M / 9`. -/
def Mds : Matrix (Fin 3) (Fin 3) ℚ := (9 : ℚ)⁻¹ • M

theorem Mds_pos : ∀ i j, 0 < Mds i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Mds, M]

/-- Every row sum and every column sum of `M / 9` is `1`: it is doubly stochastic. -/
theorem Mds_doublyStochastic :
    Mds *ᵥ (fun _ => (1 : ℚ)) = (fun _ => 1) ∧ Mdsᵀ *ᵥ (fun _ => (1 : ℚ)) = (fun _ => 1) := by
  refine ⟨?_, ?_⟩
  · rw [Mds, Matrix.smul_mulVec, M_rowSums]
    funext i
    norm_num
  · rw [Mds, Matrix.transpose_smul, Matrix.smul_mulVec, M_colSums]
    funext i
    norm_num

theorem Mds_not_diagonalizable : ¬ Diagonalizable Mds := by
  intro h
  have h9 : Diagonalizable ((9 : ℚ) • Mds) := h.smul 9
  have : (9 : ℚ) • Mds = M := by
    rw [Mds, smul_smul]
    norm_num
  rw [this] at h9
  exact M_not_diagonalizable h9

/-! ## Clause (3): the invertible shifts -/

/-- `M + t • 1`. -/
def Mshift (t : ℚ) : Matrix (Fin 3) (Fin 3) ℚ := M + t • (1 : Matrix (Fin 3) (Fin 3) ℚ)

theorem Mshift_pos {t : ℚ} (ht : 0 < t) : ∀ i j, 0 < Mshift t i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Mshift, M] <;> linarith

theorem Mshift_premagic (t : ℚ) : Premagic (Mshift t) := by
  rw [Premagic, Mshift, Matrix.add_mulVec, M_rowSums, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.add_mulVec, M_colSums]

/-- The determinant is `(9 + t) * t ^ 2`, so every positive shift is invertible. -/
theorem Mshift_det (t : ℚ) : (Mshift t).det = (9 + t) * t ^ 2 := by
  rw [Matrix.det_fin_three]
  simp [Mshift, M]
  ring

theorem Mshift_not_diagonalizable (t : ℚ) : ¬ Diagonalizable (Mshift t) := by
  intro h
  have h' : Diagonalizable (Mshift t - t • (1 : Matrix (Fin 3) (Fin 3) ℚ)) := h.sub_smul_one t
  rw [Mshift, add_sub_cancel_right] at h'
  exact M_not_diagonalizable h'

/-! ## Clause (4), elementary half: order two forces symmetry

The write-up's own argument: premagic on a `2 × 2` matrix reads `a + b = a + c`, so `b = c`.
The remaining step — real symmetric implies diagonalizable — is the spectral theorem and is NOT
formalised here; see the module header. -/

/-- A premagic `2 × 2` matrix is symmetric. -/
theorem premagic_two_isSymm {R : Type*} [CommRing R] {A : Matrix (Fin 2) (Fin 2) R}
    (h : Premagic A) : A.IsSymm := by
  have h0 : A 0 0 + A 0 1 = A 0 0 + A 1 0 := by
    have := congrFun h 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply] using this
  have hoff : A 0 1 = A 1 0 := add_left_cancel h0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, hoff]

/-- A real symmetric `2 × 2` matrix is diagonalizable, **with an explicit eigenbasis** rather than
through the spectral theorem: the eigenvalues are `((a + c) ± s) / 2` with
`s = √((a − c)² + 4b²)`, the eigenvectors are `(λ − c, b)`, and `det = b * s ≠ 0` because `b ≠ 0`
and `s > 0`.  Doing it by hand keeps the analysis import closure down to `Real.sqrt`. -/
theorem isSymm_two_diagonalizable {A : Matrix (Fin 2) (Fin 2) ℝ} (h : A.IsSymm) :
    Diagonalizable A := by
  have hsym : A 1 0 = A 0 1 := by
    have := congrFun (congrFun h 0) 1
    simpa [Matrix.transpose_apply] using this
  set a := A 0 0 with ha
  set b := A 0 1 with hb
  set c := A 1 1 with hc
  by_cases hb0 : b = 0
  · -- Already diagonal.
    refine ⟨1, fun i => A i i, by simp, ?_⟩
    rw [Matrix.mul_one, Matrix.one_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hsym, hb0, ← hb]
  · -- Two distinct eigenvalues, with explicit eigenvectors.
    have hpos : (0 : ℝ) < (a - c) ^ 2 + 4 * b ^ 2 := by positivity
    set s := Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2) with hs_def
    have hs2 : s ^ 2 = (a - c) ^ 2 + 4 * b ^ 2 := Real.sq_sqrt (le_of_lt hpos)
    have hspos : 0 < s := Real.sqrt_pos.mpr hpos
    set l1 := ((a + c) + s) / 2 with hl1
    set l2 := ((a + c) - s) / 2 with hl2
    have hchar1 : l1 ^ 2 - (a + c) * l1 + (a * c - b ^ 2) = 0 := by
      rw [hl1]; linear_combination hs2 / 4
    have hchar2 : l2 ^ 2 - (a + c) * l2 + (a * c - b ^ 2) = 0 := by
      rw [hl2]; linear_combination hs2 / 4
    have hdiff : l1 - l2 = s := by rw [hl1, hl2]; ring
    refine ⟨!![l1 - c, l2 - c; b, b], fun i => if i = 0 then l1 else l2, ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      have hdet : (l1 - c) * b - (l2 - c) * b = b * s := by rw [← hdiff]; ring
      rw [hdet]
      exact isUnit_iff_ne_zero.mpr (by positivity)
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, diagonal_apply, hsym, ← ha, ← hb, ← hc]
      · linear_combination hchar1 - hs2 / 2
      · linear_combination hchar2 - hs2 / 2
      · ring
      · ring

/-- **CLAUSE (4).**  No premagic matrix of order two is defective — the write-up's minimal-order
assertion at the only order where it has content. -/
theorem premagic_two_diagonalizable {A : Matrix (Fin 2) (Fin 2) ℝ} (h : Premagic A) :
    Diagonalizable A :=
  isSymm_two_diagonalizable (premagic_two_isSymm h)

/-- Order one is immediate, which completes *"no real premagic matrix of order less than three is
defective"* together with `premagic_two_diagonalizable`. -/
theorem premagic_one_diagonalizable (A : Matrix (Fin 1) (Fin 1) ℝ) : Diagonalizable A := by
  refine ⟨1, fun i => A i i, by simp, ?_⟩
  rw [Matrix.mul_one, Matrix.one_mul]
  ext i j
  fin_cases i
  fin_cases j
  simp

end Principia.MathDB.P336488
