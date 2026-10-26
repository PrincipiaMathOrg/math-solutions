import Mathlib

/-!
# MathDB #405093 — sign and factorization tools for the interlacing argument

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/405093/solution.tex`, Lemmas on the interlacing family `A_a` and on
`Q_n`.  Two root-level facts the interlacing induction uses, stated for arbitrary real data:

* `prod_sign`: if exactly the first `j` of `r₀, …, r_{n−1}` lie below `x` (and the rest above),
  then `(−1)^{n−j} ∏ᵢ (x − rᵢ) > 0`;
* `factor_of_roots`: a real polynomial of degree `n` with `n` distinct roots `rᵢ` equals its leading
  coefficient times `∏ᵢ (X − rᵢ)`.

The interlacing lemma is the consumer.
-/

namespace Principia.MathDB.P405093

open Finset Polynomial

/-- The sign of `∏ (x − rᵢ)` when exactly the first `j` roots lie below `x`. -/
theorem prod_sign : ∀ (n : ℕ) (r : Fin n → ℝ) (x : ℝ) (j : ℕ), j ≤ n →
    (∀ i : Fin n, (i : ℕ) < j → r i < x) → (∀ i : Fin n, j ≤ (i : ℕ) → x < r i) →
    0 < (-1 : ℝ) ^ (n - j) * ∏ i, (x - r i) := by
  intro n
  induction n with
  | zero =>
    intro r x j hj _ _
    have : j = 0 := by omega
    subst this
    simp
  | succ n ih =>
    intro r x j hj hlo hhi
    rw [Fin.prod_univ_castSucc]
    rcases Nat.lt_or_ge n j with hnj | hnj
    · -- `j = n + 1`: every root lies below `x`
      have hj' : j = n + 1 := by omega
      subst hj'
      have hP := ih (fun i => r i.castSucc) x n le_rfl
        (fun i hi => hlo i.castSucc (by simp only [Fin.coe_castSucc]; omega))
        (fun i hi => by have := i.isLt; omega)
      have hlast : r (Fin.last n) < x := hlo (Fin.last n) (by simp)
      simp only [Nat.sub_self, pow_zero, one_mul] at hP ⊢
      exact mul_pos hP (by linarith)
    · have hP := ih (fun i => r i.castSucc) x j hnj (fun i hi => hlo i.castSucc (by simpa using hi))
        (fun i hi => hhi i.castSucc (by simpa using hi))
      have hlast : x < r (Fin.last n) := hhi (Fin.last n) (by simp; omega)
      rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ]
      have : (-1 : ℝ) ^ (n - j) * (-1) * ((∏ i : Fin n, (x - r i.castSucc)) * (x - r (Fin.last n)))
          = ((-1 : ℝ) ^ (n - j) * ∏ i : Fin n, (x - r i.castSucc)) * (r (Fin.last n) - x) := by
        ring
      rw [this]
      exact mul_pos hP (by linarith)

/-- A real polynomial of degree `n` with `n` distinct roots is `lc · ∏ (X − rᵢ)`. -/
theorem factor_of_roots (p : ℝ[X]) (n : ℕ) (hdeg : p.natDegree = n) (hp : p ≠ 0)
    (r : Fin n → ℝ) (hr : Function.Injective r) (hroot : ∀ i, p.eval (r i) = 0) :
    p = C p.leadingCoeff * ∏ i, (X - C (r i)) := by
  have hsub : (univ.image r).val ≤ p.roots := by
    rw [Multiset.le_iff_subset (univ.image r).nodup]
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.1 (show x ∈ univ.image r from hx)
    exact (mem_roots hp).2 (hroot i)
  have hcard : Multiset.card (univ.image r).val = n := by
    rw [Finset.card_val, card_image_of_injective _ hr, card_univ, Fintype.card_fin]
  have heq : (univ.image r).val = p.roots :=
    Multiset.eq_of_le_of_card_le hsub (by rw [hcard, ← hdeg]; exact card_roots' p)
  have hroots : Multiset.card p.roots = p.natDegree := by rw [← heq, hcard, hdeg]
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hroots]
  rw [← heq]
  congr 1
  exact Finset.prod_image (f := fun a => X - C a) (fun i _ j _ h => hr h)

end Principia.MathDB.P405093
