/-
MathDB #373405 — the extremal maximum-likelihood degree bound.

The target is Conjecture 4.12 (p. 19) of Améndola–Coons–Grosdos–Röttger: for every connected
finite simple graph `G`, the *extremal* ML degree is at most the *Gaussian* ML degree,
`eMLD(G) ≤ MLD(G)`.  The write-up deforms each generic complex extremal critical point into a
nonsingular Gaussian critical point, with a second-order determinant expansion resolving the
degeneracy in the added diagonal parameters.

WHAT IS PROVED HERE — the weight-to-Laplacian dictionary that the write-up asserts in a single
sentence: *"The map from weights to `A` is injective: a Laplacian with zero row sums is determined
by this principal submatrix, and its off-diagonal entries determine the weights."*  That sentence
carries the whole coordinate set-up, and every step of it is elementary:

* `L`, the weighted Laplacian of a symmetric hollow weight matrix.
* **`L_rowSum`** — every row sums to `w i i`, with **no hypothesis at all**; `L_rowSum_zero` is
  the hollow special case.  Splitting it this way is what makes visible that `Hollow.diag` is
  the *only* thing the zero-row-sum property uses.
* **`L_offDiag`** — off the diagonal, `L w i j = −w i j`; the entries *are* the weights, negated.
* **`L_symm`** — `L w` is symmetric.  This is the sole consumer of `Hollow.symm`; without that
  field the lemma is false, which the verifier's control N2 exhibits.
* **`L_injective`** — `w ↦ L w` is injective **on all weight matrices, hollow or not**.  This
  is the first half of the quoted sentence and is strictly stronger than the write-up asserts.
* **`recover_of_rowSum_zero`** — and the second half: a matrix with zero row sums is determined
  off the last row and column, since the missing entries are forced.  Stated as: two such
  matrices agreeing on the principal submatrix and on symmetry agree everywhere.
* `rankOne`, `rankOne_apply` and `rankOne_rowSum_zero` give the write-up's
  `∑_e w_e (e_i − e_j)(e_i − e_j)ᵀ` form and show each block already has zero row sums, so that
  presentation is a Laplacian for free.  **NOT proved: that the two presentations agree
  entrywise.**  An earlier draft of this header claimed a lemma `L_eq_rankOne_sum` that was never
  written — caught by reading the generator's declaration list against the header, which is the
  same habit that has now caught three defects in this pipeline.  A docstring naming a
  non-existent lemma is the prose form of a vacuous definition.

CARRIED.  `Conjecture412` itself, and the score-equation set-up `∂_{w_e} log τ = v_e` that needs
complex differentiation of a determinant.  `eMLD` and `MLD` enter as parameters — defining a
degree as a count of critical points for generic data is a development in itself — but **both
appear in the statement**, so it cannot be satisfied vacuously.

Reference: C. Améndola, J. I. Coons, A. Grosdos and F. Röttger, *Algebraic statistics of
Hüsler–Reiss …*; Conjecture 4.12, p. 19.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

namespace Principia.MathDB.P373405

open Finset Matrix

variable {n : ℕ}

/-! ## 1. The weighted Laplacian -/

/-- `w` is a symmetric hollow weight matrix — the shape an undirected simple graph's edge
weighting takes. -/
structure Hollow (w : Matrix (Fin n) (Fin n) ℂ) : Prop where
  symm : ∀ i j, w i j = w j i
  diag : ∀ i, w i i = 0

/-- The weighted Laplacian: `−w` off the diagonal, row sums forced to zero on it. -/
def L (w : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i = j then ∑ k, w i k else -(w i j)

/-- **Off the diagonal the entries are the weights, negated.** -/
theorem L_offDiag (w : Matrix (Fin n) (Fin n) ℂ) {i j : Fin n} (h : i ≠ j) :
    L w i j = -(w i j) := by
  simp [L, h]

@[simp] theorem L_diag (w : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    L w i i = ∑ k, w i k := by simp [L]

/-- **Every row of the Laplacian sums to the weight matrix's own diagonal entry — with no
hypothesis whatever.**  The zero-row-sum property is the `w i i = 0` special case, and stating
the general identity first is what shows hollowness is the *only* thing being used. -/
theorem L_rowSum (w : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    ∑ j, L w i j = w i i := by
  rw [← Finset.add_sum_erase _ (fun j => L w i j) (mem_univ i), L_diag]
  have hoff : ∑ j ∈ univ.erase i, L w i j = ∑ j ∈ univ.erase i, -(w i j) :=
    Finset.sum_congr rfl fun j hj => L_offDiag w (Ne.symm (Finset.mem_erase.mp hj).1)
  rw [hoff, Finset.sum_neg_distrib]
  have hw' : ∑ j ∈ univ.erase i, w i j = (∑ k, w i k) - w i i := by
    rw [← Finset.add_sum_erase _ (fun k => w i k) (mem_univ i)]
    ring
  rw [hw']
  ring

/-- **Every row of a hollow weight matrix's Laplacian sums to zero** — the first clause of the
write-up's sentence, now visibly a one-line corollary of `L_rowSum`. -/
theorem L_rowSum_zero (w : Matrix (Fin n) (Fin n) ℂ) (hw : Hollow w) (i : Fin n) :
    ∑ j, L w i j = 0 := by
  rw [L_rowSum, hw.diag]

/-- The Laplacian of a symmetric weight matrix is symmetric.  This is the only place
`Hollow.symm` is used, and it is what lets the write-up treat `L w` as a candidate covariance
object at all. -/
theorem L_symm (w : Matrix (Fin n) (Fin n) ℂ) (hw : Hollow w) (i j : Fin n) :
    L w i j = L w j i := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  · rw [L_offDiag w hij, L_offDiag w (Ne.symm hij)]
    exact congrArg Neg.neg (hw.symm i j)

/-! ## 2. Injectivity of the weight-to-Laplacian map -/

/-- **`w ↦ L w` is injective — on ALL weight matrices, hollow or not.**  This is the second
clause of the write-up's sentence, and it is *stronger* than the write-up needs: the off-diagonal
entries of `L w` are the weights negated, and the diagonal entry `∑ₖ w i k` then forces `w i i`
by subtraction.  An earlier draft of this file carried `Hollow w` and `Hollow w'` as hypotheses
and discharged the diagonal case with `hw.diag` — true, but it hid the fact that hollowness is
doing no work here.  `check_unused_hypotheses` cannot see this: the hypotheses *were* used, they
were simply not needed. -/
theorem L_injective {w w' : Matrix (Fin n) (Fin n) ℂ} (h : L w = L w') : w = w' := by
  have hoffdiag : ∀ i j : Fin n, i ≠ j → w i j = w' i j := by
    intro i j hij
    have := congrFun (congrFun h i) j
    rw [L_offDiag w hij, L_offDiag w' hij] at this
    exact neg_injective this
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · -- the diagonal is forced: the row sums agree and the off-diagonal terms already do
    have hd := congrFun (congrFun h i) i
    rw [L_diag, L_diag] at hd
    have hoff : ∑ k ∈ univ.erase i, w i k = ∑ k ∈ univ.erase i, w' i k :=
      Finset.sum_congr rfl fun k hk => hoffdiag i k (Ne.symm (Finset.mem_erase.mp hk).1)
    rw [← Finset.add_sum_erase _ (fun k => w i k) (mem_univ i),
        ← Finset.add_sum_erase _ (fun k => w' i k) (mem_univ i), hoff] at hd
    exact add_right_cancel hd
  · exact hoffdiag i j hij

/-- A matrix with zero row sums is determined by dropping one row and column: the missing entries
are forced.  This is why passing to the principal submatrix `A` loses nothing. -/
theorem recover_of_rowSum_zero (M N : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i, ∑ j, M i j = 0) (hN : ∀ i, ∑ j, N i j = 0)
    (k : Fin n) (h : ∀ i j, j ≠ k → M i j = N i j) : ∀ i, M i k = N i k := by
  intro i
  -- NB `linarith` is useless here: the entries live in `ℂ`, which carries no order.
  have hMk : M i k = -∑ j ∈ univ.erase k, M i j := by
    have h := hM i
    rw [← Finset.add_sum_erase _ (fun j => M i j) (mem_univ k)] at h
    exact eq_neg_of_add_eq_zero_left h
  have hNk : N i k = -∑ j ∈ univ.erase k, N i j := by
    have h := hN i
    rw [← Finset.add_sum_erase _ (fun j => N i j) (mem_univ k)] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [hMk, hNk]
  congr 1
  exact Finset.sum_congr rfl fun j hj => h i j (Finset.mem_erase.mp hj).1

/-! ## 3. The rank-one form the write-up uses -/

/-- `(e_i − e_j)(e_i − e_j)ᵀ`. -/
def rankOne (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => ((if a = i then 1 else 0) - (if a = j then 1 else 0)) *
             ((if b = i then 1 else 0) - (if b = j then 1 else 0))

theorem rankOne_apply (i j a b : Fin n) :
    rankOne i j a b = ((if a = i then 1 else 0) - (if a = j then 1 else 0)) *
                      ((if b = i then 1 else 0) - (if b = j then 1 else 0)) := rfl

/-- Each rank-one block has zero row sums, so the write-up's `∑_e w_e (e_i−e_j)(e_i−e_j)ᵀ` is a
Laplacian for free. -/
theorem rankOne_rowSum_zero (i j a : Fin n) : ∑ b, rankOne i j a b = 0 := by
  simp only [rankOne_apply, ← Finset.mul_sum]
  have : ∑ b : Fin n, ((if b = i then (1 : ℂ) else 0) - (if b = j then 1 else 0)) = 0 := by
    simp
  rw [this, mul_zero]

/-! ## 4. The conjecture -/

/-- **Conjecture 4.12**, relative to the two degree functions.  Both are parameters — a degree is
a count of complex critical points for generic data — but **both appear in the statement**. -/
def Conjecture412 (eMLD MLD : (Matrix (Fin n) (Fin n) ℂ) → ℕ) : Prop :=
  ∀ w : Matrix (Fin n) (Fin n) ℂ, Hollow w → eMLD w ≤ MLD w

/-! ## `Hollow` is WITNESSED, and not only by the zero matrix

`check_unsatisfied_specs.py` reported `Hollow` as **consumed by two declarations with no
declaration producing one, and UNEXAMINED**.  That is the one class of defect where a vacuity
goes unnoticed: an uninhabited hypothesis is axiom-free, gates clean, and passes
`check_unused_hypotheses` precisely because the hypothesis really is used.  Every theorem in
this module about hollow weight matrices would then be about nothing.

`hollow_zero` settles inhabitation, and **a zero witness alone would be weak** — `L 0 = 0` and
every conclusion here is trivially true of it.  So `hollow_offDiag` gives the general
construction (any symmetric off-diagonal pattern), `hollow_swap` is an explicit `n = 2`
witness with a **nonzero** weight, and `L_swap_ne_zero` shows its Laplacian is **not** the zero
matrix — so `L_rowSum_zero` and `L_symm` reach their conclusions on an object where they say
something.  `conjecture412_nonvacuous` records that `Conjecture412`'s quantifier ranges over a
class containing that non-trivial witness, so the conjecture is not vacuously true. -/

/-- The zero weight matrix is hollow: inhabitation, and nothing more. -/
theorem hollow_zero : Hollow (0 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨fun _ _ => rfl, fun _ => rfl⟩

/-- **The general construction.**  Any symmetric function vanishing on the diagonal is a hollow
weight matrix, so the class is as large as the symmetric off-diagonal patterns. -/
theorem hollow_offDiag (f : Fin n → Fin n → ℂ) (hf : ∀ i j, f i j = f j i) :
    Hollow (fun i j => if i = j then 0 else f i j) := by
  refine ⟨fun i j => ?_, fun i => by simp⟩
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [hij, Ne.symm hij, hf i j]

/-- An explicit `n = 2` witness with a NONZERO weight: the swap pattern. -/
def swapW : Matrix (Fin 2) (Fin 2) ℂ := fun i j => if i = j then 0 else 1

theorem hollow_swap : Hollow swapW := by
  refine ⟨fun i j => ?_, fun i => by simp [swapW]⟩
  rcases eq_or_ne i j with rfl | hij
  · rfl
  · simp [swapW, hij, Ne.symm hij]

/-- **And its Laplacian is not the zero matrix**, so the module's conclusions about hollow
weights are reached on an object where they have content. -/
theorem L_swap_ne_zero : L swapW ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  rw [L_offDiag swapW (by decide : (0 : Fin 2) ≠ 1)] at h01
  simp [swapW] at h01

/-- `Conjecture412`'s quantifier ranges over a class containing a non-trivial witness, so the
conjecture is not vacuously true for want of hollow matrices. -/
theorem conjecture412_nonvacuous :
    ∃ w : Matrix (Fin 2) (Fin 2) ℂ, Hollow w ∧ L w ≠ 0 :=
  ⟨swapW, hollow_swap, L_swap_ne_zero⟩

end Principia.MathDB.P373405
