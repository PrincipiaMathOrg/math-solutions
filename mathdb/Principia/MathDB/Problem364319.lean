import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# MathDB #364319 — Nikseresht–Namazi–Beygi Khormaei Conjecture 2

Write-up: `mathdb-open-problems/problems/364319/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-28 from the
third hundred, see `THIRD100-ENROLMENT.md`).
Source: Nikseresht, Namazi and Beygi Khormaei, **Conjecture 2** (p. 18): if `−1` is an eigenvalue of
`PM` for every permutation matrix `P`, then the entries of `M` sum to `−k`. The source proves the
nonsymmetric case only when `(k−1)! ≠ 0` in `F`; the write-up proves the **stronger** row-or-column
classification over *every* field, with no characteristic restriction.

**The write-up's theorem.** For every `M ∈ F^{k×k}` the following are equivalent:

1. `−1` is an eigenvalue of `PM` for every permutation matrix `P`;
2. `M + P` is singular for every permutation matrix `P`;
3. `M · 1 = −1` **or** `1ᵀ · M = −1ᵀ`.

and either of the first two forces `∑ᵢⱼ Mᵢⱼ = −k`.

## What is proved here, and what is the residue

**PROVED, over an arbitrary field and with no characteristic hypothesis:**

* `eigenNegOne_iff_singularTranslates` — **(1) ⟺ (2)**, which is the observation `1 + PM = P(M
+ P⁻¹)`
  together with the fact that inversion permutes the permutation matrices. `det P = sign σ` is a
  unit in every field, so no characteristic enters.
* `singularTranslates_of_rowOrColSums` — **(3) ⟹ (2)**, and with the equivalence also **(3) ⟹ (1)**.
  Every permutation fixes `1` on both sides, so the row-sum hypothesis puts `1` in the kernel of
  `M + P` and the column-sum hypothesis puts it in the kernel of the transpose.
* `entrySum_of_rowOrColSums` — the conjecture's own conclusion `∑ᵢⱼ Mᵢⱼ = −k` from (3), by summing
  the row sums or the column sums. **This is the clause the source conjectures**, so with (3) in
  hand the conjecture follows; what remains is only that (2) *implies* (3).
* `permMatrix_swap_eq` — the transposition identity `T_{ij} = 1 − u uᵀ` with `u = eᵢ − eⱼ`. **This
  is the step that makes the write-up's argument characteristic-free**, and it is the one a reader
  should most want checked: it holds in characteristic two as well, where `u uᵀ` has zero diagonal
  contributions cancelling differently. Proved entrywise, with no division.

**RESIDUE — (2) ⟹ (3), i.e. exactly two named facts.** Both are stated in the write-up and neither
needs theory Mathlib lacks:

1. *the rank-one update lemma*: if `u ∉ range A` and `v ∉ range Aᵀ` then
   `rank (A + u vᵀ) = rank A + 1`. The write-up's proof picks `x ∈ ker A` with `vᵀ x ≠ 0`, which is
   the statement that `range Aᵀ` is the annihilator of `ker A`. Mathlib has that as
   `LinearMap.range_dualMap_eq_dualAnnihilator_ker` (over a field), but it is phrased for
   `Module.Dual`, so the work is translating between `Matrix.mulVec`/`dotProduct` and dual maps —
   friction, not mathematics. `Matrix.rank_transpose` is available for the dimension bookkeeping.
2. *the two-subspace covering lemma*: if every `eᵢ − eⱼ` lies in `C ∪ R` for subspaces `C`, `R`,
   then `H ⊆ C` or `H ⊆ R`, where `H = {x : 1ᵀx = 0}`. The write-up's proof is self-contained: pick
   `e_a − e_b ∉ C`, note that for each `i` at least one of `eᵢ − e_a`, `eᵢ − e_b` is outside `C`
   (their difference is `e_b − e_a ∉ C`), and translate by `e_a − e_b ∈ R`.

With those, the main argument is the write-up's maximal-rank step: choose `P₀` maximising
`rank (M + P₀)`, set `A = P₀⁻¹M + 1`, and use `permMatrix_swap_eq` to see `rank (A − u uᵀ) ≤
rank A`,
so no `u = eᵢ − eⱼ` can avoid both `range A` and `range Aᵀ`.

## 215 check

* **The source's hypothesis is about eigenvalues of `PM`, not of `M + P`**, and those are different
  statements until `1 + PM = P(M + P⁻¹)` is checked — which is why (1) ⟺ (2) is proved here rather
  than assumed as a restatement.
* **The write-up proves strictly more than the conjecture**: the conjecture asks only for the entry
  sum, while (3) is a classification. `entrySum_of_rowOrColSums` records the conjecture's own
  conclusion separately, so a reader can see which clause is the source's and which is the
  strengthening.
* No step below divides by `k`, by a factorial, or by `2`, and `1` is a nonzero vector even when the
  characteristic divides `k` — the hypothesis `0 < k` is carried explicitly where it is needed and
  nowhere else.
-/

namespace Principia.MathDB.P364319

open Matrix Equiv

variable {k : ℕ} {F : Type*} [Field F]

/-- The all-ones vector. -/
def ones (k : ℕ) (F : Type*) [Field F] : Fin k → F := fun _ => 1

theorem ones_ne_zero (hk : 0 < k) : ones k F ≠ 0 := by
  intro h
  have h0 := congrFun h ⟨0, hk⟩
  simp [ones] at h0

/-! ### The three conditions -/

/-- (1) `−1` is an eigenvalue of `P M` for every permutation matrix `P`. -/
def EigenNegOne (M : Matrix (Fin k) (Fin k) F) : Prop :=
  ∀ σ : Perm (Fin k), (σ.permMatrix F * M + 1).det = 0

/-- (2) `M + P` is singular for every permutation matrix `P`. -/
def SingularTranslates (M : Matrix (Fin k) (Fin k) F) : Prop :=
  ∀ σ : Perm (Fin k), (M + σ.permMatrix F).det = 0

/-- (3) all row sums are `−1`, or all column sums are `−1`. -/
def RowOrColSums (M : Matrix (Fin k) (Fin k) F) : Prop :=
  M.mulVec (ones k F) = -ones k F ∨ Matrix.vecMul (ones k F) M = -ones k F

/-! ### Permutation matrices: invertibility and the fixed vector -/

theorem permMatrix_mul_inv (σ : Perm (Fin k)) :
    σ.permMatrix F * σ⁻¹.permMatrix F = 1 := by
  -- `Matrix.permMatrix_mul` is an ANTI-homomorphism: `(σ * τ).permMatrix = τ.permMatrix *
  -- σ.permMatrix`.  So the product we want comes from `σ⁻¹ * σ`, not `σ * σ⁻¹`.
  rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

/-- A permutation matrix is nonsingular over every field — no characteristic enters, because the
proof uses only `P P⁻¹ = 1`, not the sign. -/
theorem permMatrix_det_ne_zero (σ : Perm (Fin k)) : (σ.permMatrix F).det ≠ 0 := by
  intro hz
  have hd := congrArg Matrix.det (permMatrix_mul_inv (F := F) σ)
  rw [Matrix.det_mul, hz, zero_mul, Matrix.det_one] at hd
  exact zero_ne_one hd

theorem permMatrix_mulVec_ones (σ : Perm (Fin k)) :
    (σ.permMatrix F).mulVec (ones k F) = ones k F := by
  ext i
  simp [Matrix.permMatrix_mulVec, ones]

theorem ones_vecMul_permMatrix (σ : Perm (Fin k)) :
    Matrix.vecMul (ones k F) (σ.permMatrix F) = ones k F := by
  ext j
  rw [Matrix.vecMul, dotProduct]
  rw [Finset.sum_eq_single (σ.symm j)]
  · simp [ones, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  · intro i _ hne
    have hsi : σ i ≠ j := fun hj => hne (by rw [← hj]; simp)
    simp [ones, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, hsi]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-! ### (1) ⟺ (2) -/

/-- `1 + P M = P (M + P⁻¹)`, the identity behind the equivalence. -/
theorem permMatrix_mul_add_one (M : Matrix (Fin k) (Fin k) F) (σ : Perm (Fin k)) :
    σ.permMatrix F * M + 1 = σ.permMatrix F * (M + σ⁻¹.permMatrix F) := by
  rw [Matrix.mul_add, permMatrix_mul_inv]

/-- **(1) ⟺ (2).** The source's hypothesis is about eigenvalues of `P M`; the write-up's is about
singularity of `M + P`. They are the same statement only after this identity, so it is proved
rather than assumed. -/
theorem eigenNegOne_iff_singularTranslates (M : Matrix (Fin k) (Fin k) F) :
    EigenNegOne M ↔ SingularTranslates M := by
  constructor
  · intro h σ
    have h1 := h σ⁻¹
    rw [permMatrix_mul_add_one, Matrix.det_mul, inv_inv] at h1
    exact (mul_eq_zero.mp h1).resolve_left (permMatrix_det_ne_zero _)
  · intro h σ
    rw [permMatrix_mul_add_one, Matrix.det_mul, h σ⁻¹, mul_zero]

/-! ### (3) ⟹ (2), and the conjecture's own conclusion -/

/-- **(3) ⟹ (2).** Every permutation fixes `1` on both sides, so a row-sum hypothesis puts `1` in
the kernel of `M + P` and a column-sum hypothesis puts it in the kernel of the transpose. -/
theorem singularTranslates_of_rowOrColSums (hk : 0 < k) {M : Matrix (Fin k) (Fin k) F}
    (h : RowOrColSums M) : SingularTranslates M := by
  intro σ
  rcases h with hrow | hcol
  · have hker : (M + σ.permMatrix F).mulVec (ones k F) = 0 := by
      rw [Matrix.add_mulVec, hrow, permMatrix_mulVec_ones]
      ext i
      simp
    exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨ones k F, ones_ne_zero hk, hker⟩
  · have hker : Matrix.vecMul (ones k F) (M + σ.permMatrix F) = 0 := by
      rw [Matrix.vecMul_add, hcol, ones_vecMul_permMatrix]
      ext i
      simp
    have h2 : ((M + σ.permMatrix F)ᵀ).mulVec (ones k F) = 0 := by
      rw [← Matrix.vecMul_transpose]
      simpa using hker
    have h3 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨ones k F, ones_ne_zero hk, h2⟩
    rwa [Matrix.det_transpose] at h3

/-- **(3) ⟹ (1)**, by the equivalence. -/
theorem eigenNegOne_of_rowOrColSums (hk : 0 < k) {M : Matrix (Fin k) (Fin k) F}
    (h : RowOrColSums M) : EigenNegOne M :=
  (eigenNegOne_iff_singularTranslates M).mpr (singularTranslates_of_rowOrColSums hk h)

/-- **THE CONJECTURE'S OWN CONCLUSION** follows from (3): the entries sum to `−k`. This is the
clause the source conjectures; the classification (3) is the write-up's strengthening. -/
theorem entrySum_of_rowOrColSums {M : Matrix (Fin k) (Fin k) F} (h : RowOrColSums M) :
    ∑ i, ∑ j, M i j = -(k : F) := by
  rcases h with hrow | hcol
  · have hrowsum : ∀ i, ∑ j, M i j = -1 := by
      intro i
      have hi := congrFun hrow i
      simpa [Matrix.mulVec, dotProduct, ones] using hi
    rw [Finset.sum_congr rfl fun i _ => hrowsum i]
    simp
  · have hcolsum : ∀ j, ∑ i, M i j = -1 := by
      intro j
      have hj := congrFun hcol j
      simpa [Matrix.vecMul, dotProduct, ones] using hj
    rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => hcolsum j]
    simp

/-! ### The transposition identity — the step that makes the argument characteristic-free -/

/-- `T_{ij} = 1 − u uᵀ` with `u = eᵢ − eⱼ`. This holds in **every** characteristic, including two,
and it is what lets the write-up's maximal-rank argument drop the source's `(k−1)! ≠ 0`
restriction. -/
theorem permMatrix_swap_eq {i j : Fin k} (hij : i ≠ j) :
    (Equiv.swap i j).permMatrix F
      = 1 - Matrix.vecMulVec (Pi.single i (1 : F) - Pi.single j (1 : F))
            (Pi.single i (1 : F) - Pi.single j (1 : F)) := by
  ext a b
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.sub_apply,
    Pi.single_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  by_cases ha : a = i
  · subst ha
    by_cases hb : b = a
    · subst hb; simp [Equiv.swap_apply_left, hij, Ne.symm hij]
    · by_cases hb' : b = j
      · subst hb'; simp [Equiv.swap_apply_left, hij, Ne.symm hij]
      · simp [Equiv.swap_apply_left, hb, hb', Ne.symm hb, Ne.symm hb']
  · by_cases ha' : a = j
    · subst ha'
      by_cases hb : b = i
      · subst hb; simp [Equiv.swap_apply_right, hij, Ne.symm hij]
      · by_cases hb' : b = a
        · subst hb'; simp [Equiv.swap_apply_right, hij, Ne.symm hij]
        · simp [Equiv.swap_apply_right, hb, hb', Ne.symm hb, Ne.symm hb']
    · have hswap : Equiv.swap i j a = a := Equiv.swap_apply_of_ne_of_ne ha ha'
      simp [hswap, ha, ha']

/-! ## The residue: `(2) ⟹ (3)`

Recorded as a work-list when this row was first banked. The only friction was Mathlib-shaped:
`range Aᵀ` is the orthogonal complement of `ker A`, which Mathlib has as a **dimension** fact about
bilinear forms (`LinearMap.BilinForm.finrank_orthogonal`) rather than as a statement about matrices,
so the work is to name the standard dot-product form and count. -/

open Module in
/-- The standard dot-product form on `Fin k → F`, as a bilinear form, so that Mathlib's
orthogonal-complement dimension theory applies. -/
noncomputable def dotForm (k : ℕ) (F : Type*) [Field F] :
    LinearMap.BilinForm F (Fin k → F) := Matrix.toBilin' (1 : Matrix (Fin k) (Fin k) F)

theorem dotForm_apply (x y : Fin k → F) : dotForm k F x y = dotProduct x y := by
  simp [dotForm, Matrix.toBilin'_apply']

theorem dotForm_nondegenerate : (dotForm k F).Nondegenerate := by
  have h1 : (1 : Matrix (Fin k) (Fin k) F).Nondegenerate := by
    rw [Matrix.nondegenerate_iff_det_ne_zero]
    simp
  exact h1.toBilin'

/-- The row space sits inside the orthogonal complement of the kernel — the easy half. -/
theorem range_transpose_le_orthogonal_ker (A : Matrix (Fin k) (Fin k) F) :
    LinearMap.range (Matrix.mulVecLin Aᵀ)
      ≤ (dotForm k F).orthogonal (LinearMap.ker (Matrix.mulVecLin A)) := by
  rintro v ⟨w, rfl⟩ x hx
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
  change dotForm k F _ _ = 0
  rw [dotForm_apply]
  simp only [Matrix.mulVecLin_apply]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hx, zero_dotProduct]

/-- **THE DUALITY LEMMA.** `range Aᵀ` *is* the orthogonal complement of `ker A`. Proved by the easy
inclusion plus a dimension count: both sides have dimension `rank A`, one by
`Matrix.rank_transpose` and the other by `finrank_orthogonal` and rank–nullity. -/
theorem range_transpose_eq_orthogonal_ker (A : Matrix (Fin k) (Fin k) F) :
    LinearMap.range (Matrix.mulVecLin Aᵀ)
      = (dotForm k F).orthogonal (LinearMap.ker (Matrix.mulVecLin A)) := by
  refine Submodule.eq_of_le_of_finrank_le (range_transpose_le_orthogonal_ker A) ?_
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin A)
  have horth := LinearMap.BilinForm.finrank_orthogonal (B := dotForm k F) dotForm_nondegenerate
    (LinearMap.ker (Matrix.mulVecLin A))
  have hdim : Module.finrank F (Fin k → F) = k := by simp
  -- `Matrix.rank X` is BY DEFINITION `finrank (range X.mulVecLin)`, but it is a plain `def`, so
  -- `rw [← Matrix.rank]` has no equation lemma to use; state the transpose fact as a `finrank`
  -- equality instead and let the definitional unfolding happen in the `have`.
  have htr : Module.finrank F (LinearMap.range (Matrix.mulVecLin Aᵀ))
      = Module.finrank F (LinearMap.range (Matrix.mulVecLin A)) := Matrix.rank_transpose A
  rw [htr, horth, hdim]
  omega

/-- What the duality lemma is for: a vector off the row space pairs nontrivially with the kernel. -/
theorem exists_mem_ker_dotProduct_ne_zero {A : Matrix (Fin k) (Fin k) F} {v : Fin k → F}
    (hv : v ∉ LinearMap.range (Matrix.mulVecLin Aᵀ)) :
    ∃ x, A.mulVec x = 0 ∧ dotProduct v x ≠ 0 := by
  rw [range_transpose_eq_orthogonal_ker] at hv
  by_contra hcon
  push Not at hcon
  refine hv ?_
  intro x hx
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
  change dotForm k F _ _ = 0
  rw [dotForm_apply, dotProduct_comm]
  exact hcon x hx

/-! ### The rank-one update, in kernel form

The write-up states a rank identity; the kernel version is shorter and needs no case analysis:
`(A − u uᵀ) x = 0` forces `A x = (u ⬝ᵥ x) • u`, so if `u ∉ range A` then `u ⬝ᵥ x = 0` and
`A x = 0`. -/

theorem vecMulVec_mulVec (u v x : Fin k → F) :
    (Matrix.vecMulVec u v).mulVec x = (dotProduct v x) • u := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.mul_sum, mul_comm,
    mul_left_comm]

theorem ker_sub_vecMulVec_le {A : Matrix (Fin k) (Fin k) F} {u : Fin k → F}
    (hu : u ∉ LinearMap.range (Matrix.mulVecLin A)) :
    LinearMap.ker (Matrix.mulVecLin (A - Matrix.vecMulVec u u))
      ≤ LinearMap.ker (Matrix.mulVecLin A) := by
  intro x hx
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
    vecMulVec_mulVec, sub_eq_zero] at hx
  -- `A x = (u ⬝ᵥ x) • u`; if the scalar were nonzero, `u ∈ range A`
  have hzero : dotProduct u x = 0 := by
    by_contra hne
    refine hu ⟨(dotProduct u x)⁻¹ • x, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_smul, hx, smul_smul,
      inv_mul_cancel₀ hne, one_smul]
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  rw [hx, hzero, zero_smul]

/-- **THE STRICT RANK INCREASE.** If `u` avoids both the column space and the row space, then
subtracting `u uᵀ` strictly raises the rank — which is what contradicts maximality. -/
theorem rank_lt_rank_sub_vecMulVec {A : Matrix (Fin k) (Fin k) F} {u : Fin k → F}
    (hcol : u ∉ LinearMap.range (Matrix.mulVecLin A))
    (hrow : u ∉ LinearMap.range (Matrix.mulVecLin Aᵀ)) :
    A.rank < (A - Matrix.vecMulVec u u).rank := by
  obtain ⟨x, hxker, hxdot⟩ := exists_mem_ker_dotProduct_ne_zero hrow
  have hlt : LinearMap.ker (Matrix.mulVecLin (A - Matrix.vecMulVec u u))
      < LinearMap.ker (Matrix.mulVecLin A) := by
    refine lt_of_le_of_ne (ker_sub_vecMulVec_le hcol) ?_
    intro heq
    have hx : x ∈ LinearMap.ker (Matrix.mulVecLin A) := by
      simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hxker
    rw [← heq] at hx
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
      vecMulVec_mulVec, sub_eq_zero] at hx
    rw [hxker] at hx
    -- `0 = (u ⬝ᵥ x) • u`, and `u ≠ 0` because `u ∉ range A` while `0 ∈ range A`
    have hune : u ≠ 0 := by
      intro h
      exact hcol (by rw [h]; exact Submodule.zero_mem _)
    have := hx.symm
    rcases smul_eq_zero.mp this with h | h
    · exact hxdot h
    · exact hune h
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin A)
  have h2 := LinearMap.finrank_range_add_finrank_ker
    (Matrix.mulVecLin (A - Matrix.vecMulVec u u))
  have h3 : Module.finrank F (LinearMap.ker (Matrix.mulVecLin (A - Matrix.vecMulVec u u)))
      < Module.finrank F (LinearMap.ker (Matrix.mulVecLin A)) :=
    Submodule.finrank_lt_finrank_of_lt hlt
  -- `omega` treats `A.rank` and `finrank (range A.mulVecLin)` as TWO atoms even though they are
  -- definitionally equal, so the goal has to be put in the same shape as the hypotheses first.
  change Module.finrank F (LinearMap.range (Matrix.mulVecLin A))
      < Module.finrank F (LinearMap.range (Matrix.mulVecLin (A - Matrix.vecMulVec u u)))
  omega

/-! ### The two-subspace covering lemma

The write-up's second lemma, and the only part of the residue with no Mathlib friction: if every
difference `eᵢ − eⱼ` lies in `C ∪ R`, then all of `H = {x : ∑ xᵢ = 0}` lies in one of them. -/

/-- The sum-of-coordinates functional. -/
def sumLin (k : ℕ) (F : Type*) [Field F] : (Fin k → F) →ₗ[F] F where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

/-- `H = {x : ∑ xᵢ = 0}`, the hyperplane the covering lemma lands in. -/
def Hsub (k : ℕ) (F : Type*) [Field F] : Submodule F (Fin k → F) := LinearMap.ker (sumLin k F)

theorem mem_Hsub {x : Fin k → F} : x ∈ Hsub k F ↔ ∑ i, x i = 0 := Iff.rfl

theorem sum_smul_single (x : Fin k → F) : ∑ i, x i • (Pi.single i (1 : F)) = x := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- The differences `eᵢ − e_a` span `H`: a vector of zero coordinate sum is their combination. -/
theorem eq_sum_smul_diff {x : Fin k → F} (hx : ∑ i, x i = 0) (a : Fin k) :
    x = ∑ i, x i • (Pi.single i (1 : F) - Pi.single a (1 : F)) := by
  have hstep : ∀ i : Fin k, x i • (Pi.single i (1 : F) - Pi.single a (1 : F))
      = x i • Pi.single i (1 : F) - x i • Pi.single a (1 : F) := fun i => smul_sub _ _ _
  rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_sub_distrib, sum_smul_single,
    ← Finset.sum_smul, hx, zero_smul, sub_zero]

/-- **THE COVERING LEMMA.** A union of two subspaces containing every `eᵢ − eⱼ` contains `H` in one
of them. -/
theorem covering {C R : Submodule F (Fin k → F)} (hk : 0 < k)
    (h : ∀ i j : Fin k, (Pi.single i (1 : F) - Pi.single j (1 : F)) ∈ C ∨
      (Pi.single i (1 : F) - Pi.single j (1 : F)) ∈ R) :
    Hsub k F ≤ C ∨ Hsub k F ≤ R := by
  by_cases hall : ∀ i j : Fin k, (Pi.single i (1 : F) - Pi.single j (1 : F)) ∈ C
  · left
    intro x hx
    rw [eq_sum_smul_diff (mem_Hsub.mp hx) (⟨0, hk⟩ : Fin k)]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hall i ⟨0, hk⟩)
  · right
    push Not at hall
    obtain ⟨a, b, hab⟩ := hall
    have habR : (Pi.single a (1 : F) - Pi.single b (1 : F)) ∈ R := (h a b).resolve_left hab
    have key : ∀ i : Fin k, (Pi.single i (1 : F) - Pi.single a (1 : F)) ∈ R := by
      intro i
      by_cases hia : (Pi.single i (1 : F) - Pi.single a (1 : F)) ∈ C
      · -- then `eᵢ − e_b ∉ C`, or else `e_a − e_b` would be in `C`
        have hib : (Pi.single i (1 : F) - Pi.single b (1 : F)) ∉ C := by
          intro hibC
          refine hab ?_
          have hd : (Pi.single a (1 : F) - Pi.single b (1 : F) : Fin k → F)
              = (Pi.single i (1 : F) - Pi.single b (1 : F))
                - (Pi.single i (1 : F) - Pi.single a (1 : F)) := by
            abel
          rw [hd]
          exact Submodule.sub_mem _ hibC hia
        have hibR := (h i b).resolve_left hib
        have hd : (Pi.single i (1 : F) - Pi.single a (1 : F) : Fin k → F)
            = (Pi.single i (1 : F) - Pi.single b (1 : F))
              - (Pi.single a (1 : F) - Pi.single b (1 : F)) := by
          abel
        rw [hd]
        exact Submodule.sub_mem _ hibR habR
      · exact (h i a).resolve_left hia
    intro x hx
    rw [eq_sum_smul_diff (mem_Hsub.mp hx) a]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (key i)

/-! ### `dim H = k − 1` -/

theorem sumLin_surjective (hk : 0 < k) : Function.Surjective (sumLin k F) := by
  intro c
  refine ⟨Pi.single (⟨0, hk⟩ : Fin k) c, ?_⟩
  simp [sumLin, Pi.single_apply, Finset.sum_ite_eq']

theorem finrank_Hsub (hk : 0 < k) : Module.finrank F (Hsub k F) = k - 1 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (sumLin k F)
  rw [LinearMap.range_eq_top.mpr (sumLin_surjective (F := F) hk)] at h1
  have h2 : Module.finrank F (⊤ : Submodule F F) = 1 := by simp
  have h3 : Module.finrank F (Fin k → F) = k := by simp
  rw [h2, h3] at h1
  change 1 + Module.finrank F (Hsub k F) = k at h1
  omega

/-! ### The assembly -/

theorem permMatrix_inv_mul (σ : Perm (Fin k)) :
    σ⁻¹.permMatrix F * σ.permMatrix F = 1 := by
  rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

theorem permMatrix_isUnit_det (σ : Perm (Fin k)) : IsUnit (σ.permMatrix F).det :=
  isUnit_iff_ne_zero.mpr (permMatrix_det_ne_zero σ)

/-- **(2) ⟹ (3).** The write-up's maximal-rank argument. -/
theorem rowOrColSums_of_singularTranslates (hk : 0 < k) {M : Matrix (Fin k) (Fin k) F}
    (h : SingularTranslates M) : RowOrColSums M := by
  obtain ⟨σ₀, hmax⟩ := Finite.exists_max fun σ : Perm (Fin k) => (M + σ.permMatrix F).rank
  set A : Matrix (Fin k) (Fin k) F := σ₀⁻¹.permMatrix F * M + 1 with hAdef
  -- `P₀ A = M + P₀`, so `rank A = rank (M + P₀)`
  have hPA : σ₀.permMatrix F * A = M + σ₀.permMatrix F := by
    rw [hAdef, Matrix.mul_add, ← Matrix.mul_assoc, permMatrix_mul_inv, Matrix.one_mul,
      Matrix.mul_one]
  have hrankA : A.rank = (M + σ₀.permMatrix F).rank := by
    rw [← hPA, Matrix.rank_mul_eq_right_of_isUnit_det _ _ (permMatrix_isUnit_det σ₀)]
  -- every difference meets the column space or the row space
  have hdiff : ∀ i j : Fin k, (Pi.single i (1 : F) - Pi.single j (1 : F))
      ∈ LinearMap.range (Matrix.mulVecLin A) ∨
      (Pi.single i (1 : F) - Pi.single j (1 : F)) ∈ LinearMap.range (Matrix.mulVecLin Aᵀ) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      left
      simp only [sub_self]
      exact Submodule.zero_mem _
    by_contra hcon
    push Not at hcon
    obtain ⟨hc, hr⟩ := hcon
    have hlt := rank_lt_rank_sub_vecMulVec hc hr
    -- but `A − u uᵀ = P₀⁻¹ (M + P₀ T_{ij})`, whose rank is bounded by maximality
    have hT : A - Matrix.vecMulVec (Pi.single i (1 : F) - Pi.single j (1 : F))
        (Pi.single i (1 : F) - Pi.single j (1 : F))
        = σ₀⁻¹.permMatrix F * (M + σ₀.permMatrix F * (Equiv.swap i j).permMatrix F) := by
      rw [permMatrix_swap_eq hij, hAdef]
      rw [Matrix.mul_add, ← Matrix.mul_assoc, permMatrix_inv_mul, Matrix.one_mul]
      abel
    have hrank2 : (A - Matrix.vecMulVec (Pi.single i (1 : F) - Pi.single j (1 : F))
        (Pi.single i (1 : F) - Pi.single j (1 : F))).rank
        = (M + σ₀.permMatrix F * (Equiv.swap i j).permMatrix F).rank := by
      rw [hT, Matrix.rank_mul_eq_right_of_isUnit_det _ _ (permMatrix_isUnit_det σ₀⁻¹)]
    have hperm : σ₀.permMatrix F * (Equiv.swap i j).permMatrix F
        = (Equiv.swap i j * σ₀).permMatrix F := (Matrix.permMatrix_mul _ _).symm
    rw [hperm] at hrank2
    have := hmax (Equiv.swap i j * σ₀)
    omega
  -- the covering lemma, then the dimension squeeze
  have hArank : A.rank < k := by
    rw [hrankA]
    obtain ⟨v, hvne, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (h σ₀)
    have hkerne : Module.finrank F
        (LinearMap.ker (Matrix.mulVecLin (M + σ₀.permMatrix F))) ≠ 0 := by
      intro h0
      have hbot := Submodule.finrank_eq_zero.mp h0
      have hmem : v ∈ LinearMap.ker (Matrix.mulVecLin (M + σ₀.permMatrix F)) := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        exact hv0
      rw [hbot, Submodule.mem_bot] at hmem
      exact hvne hmem
    have h1 := LinearMap.finrank_range_add_finrank_ker
      (Matrix.mulVecLin (M + σ₀.permMatrix F))
    have h3 : Module.finrank F (Fin k → F) = k := by simp
    rw [h3] at h1
    change Module.finrank F (LinearMap.range (Matrix.mulVecLin (M + σ₀.permMatrix F)))
      + Module.finrank F (LinearMap.ker (Matrix.mulVecLin (M + σ₀.permMatrix F))) = k at h1
    change Module.finrank F
      (LinearMap.range (Matrix.mulVecLin (M + σ₀.permMatrix F))) < k
    omega
  rcases covering hk hdiff with hC | hR
  · -- `H ≤ range A` and `range A` proper, so `range A = H`, i.e. `1ᵀA = 0`
    right
    have hEq : LinearMap.range (Matrix.mulVecLin A) = Hsub k F := by
      refine (Submodule.eq_of_le_of_finrank_le hC ?_).symm
      rw [finrank_Hsub hk]
      change A.rank ≤ k - 1
      omega
    -- so every column sum of `A` vanishes
    have hcol : Matrix.vecMul (ones k F) A = 0 := by
      ext j
      have hmem : Matrix.mulVecLin A (Pi.single j (1 : F)) ∈ Hsub k F := by
        rw [← hEq]; exact LinearMap.mem_range_self _ _
      rw [mem_Hsub] at hmem
      simpa [Matrix.vecMul, dotProduct, ones, Matrix.mulVecLin_apply, Matrix.mulVec,
        Pi.single_apply, Finset.sum_ite_eq', mul_comm] using hmem
    rw [hAdef] at hcol
    rw [Matrix.vecMul_add, Matrix.vecMul_one, ← Matrix.vecMul_vecMul,
      ones_vecMul_permMatrix] at hcol
    exact eq_neg_of_add_eq_zero_left hcol
  · -- `H ≤ range Aᵀ`, symmetrically `A · 1 = 0`
    left
    have hEq : LinearMap.range (Matrix.mulVecLin Aᵀ) = Hsub k F := by
      refine (Submodule.eq_of_le_of_finrank_le hR ?_).symm
      rw [finrank_Hsub hk]
      have htr : Module.finrank F (LinearMap.range (Matrix.mulVecLin Aᵀ))
          = Module.finrank F (LinearMap.range (Matrix.mulVecLin A)) := Matrix.rank_transpose A
      rw [htr]
      change A.rank ≤ k - 1
      omega
    have hrow : A.mulVec (ones k F) = 0 := by
      ext i
      have hmem : Matrix.mulVecLin Aᵀ (Pi.single i (1 : F)) ∈ Hsub k F := by
        rw [← hEq]; exact LinearMap.mem_range_self _ _
      rw [mem_Hsub] at hmem
      simpa [Matrix.mulVec, dotProduct, ones, Matrix.mulVecLin_apply, Matrix.transpose_apply,
        Pi.single_apply, Finset.sum_ite_eq', mul_comm] using hmem
    rw [hAdef, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at hrow
    have hneg : Matrix.mulVec (σ₀⁻¹.permMatrix F) (M.mulVec (ones k F)) = -ones k F :=
      eq_neg_of_add_eq_zero_left hrow
    have happ := congrArg (fun w => Matrix.mulVec (σ₀.permMatrix F) w) hneg
    simp only [Matrix.mulVec_neg, permMatrix_mulVec_ones] at happ
    rw [Matrix.mulVec_mulVec, permMatrix_mul_inv, Matrix.one_mulVec] at happ
    exact happ

/-! ## The write-up's theorem, complete -/

/-- **NIKSERESHT–NAMAZI–BEYGI KHORMAEI CONJECTURE 2, AND THE WRITE-UP'S STRONGER CLASSIFICATION.**
Over every field and in every characteristic: `−1` is an eigenvalue of `PM` for every permutation
matrix `P` **iff** `M + P` is always singular **iff** all row sums are `−1` or all column sums are
`−1`; and then the entries sum to `−k`, which is the source's own conjecture. -/
theorem conjecture_2 (hk : 0 < k) (M : Matrix (Fin k) (Fin k) F) :
    (EigenNegOne M ↔ SingularTranslates M) ∧ (SingularTranslates M ↔ RowOrColSums M) ∧
      (EigenNegOne M → ∑ i, ∑ j, M i j = -(k : F)) := by
  refine ⟨eigenNegOne_iff_singularTranslates M, ⟨?_, singularTranslates_of_rowOrColSums hk⟩, ?_⟩
  · exact rowOrColSums_of_singularTranslates hk
  · intro hE
    exact entrySum_of_rowOrColSums (rowOrColSums_of_singularTranslates hk
      ((eigenNegOne_iff_singularTranslates M).mp hE))

end Principia.MathDB.P364319
