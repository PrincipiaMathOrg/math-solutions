import Mathlib

/-!
# MathDB #347481 — the largest entry of the inverse geometric Vandermonde matrix is diagonal

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/347481/solution.tex`, proving Conjecture 11 of Sanna, Shallit and
Zhang: for `b > 1`, `V = (b^{ij})_{0 ≤ i,j < n}` and `C = V⁻¹`, for all sufficiently large `n` the
maximum `M_b(n) = max_{i,j} |c_{ij}|` equals `|c_{ii}|` for some `i ≤ n₀ = ⌈log_b(1 + b⁻¹)⌉`.

`ssz_conj` proves this for **every** `n ≥ 1` (which implies the conjecture).  The argument is the
write-up's:

* `V_posDef`: `xᵀVx = ∑ₖ (log b)ᵏ/k! · (∑ᵢ xᵢ iᵏ)²`, and some moment with `k < n` is nonzero because
  the Vandermonde matrix on the nodes `0, …, n−1` is invertible.  So `C` is positive definite and
  `entry_le` gives `|c_{pq}| ≤ max(c_{pp}, c_{qq})` from a `2 × 2` principal minor.
* `col_eq`: column `j` of `C` is the coefficient vector of the Lagrange polynomial
  `∏_{h ≠ j} (X − bʰ) / ∏_{h ≠ j} (bʲ − bʰ)`, so `|c_{ij}| = [Xⁱ] ∏_{h ≠ j} (X + bʰ) / |π_j|`.
* `Q_coeff_mono` (the numerators decrease in `j`) and `piv_mono` (`|π_j| ≤ |π_{j+1}|` once
  `bʲ ≥ 1 + b⁻¹`, i.e. `j ≥ n₀`) give `step`: `|c_{i,j+1}| ≤ |c_{ij}|` for `j ≥ n₀`.

**Absent:** the write-up's strict statements (no off-diagonal entry attains `M_b(n)`, strict
decrease of the diagonal after `n₀`) and Tasks 2 onward.
-/

namespace Principia.MathDB.P347481

open Finset Polynomial Matrix

/-- `V = (b^{ij})_{0 ≤ i,j < n}`. -/
def V (b : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => b ^ ((i : ℕ) * (j : ℕ))

/-- `n₀ = ⌈log_b(1 + b⁻¹)⌉`. -/
noncomputable def n0 (b : ℝ) : ℕ := ⌈Real.logb b (1 + b⁻¹)⌉₊

/-- Conjecture 11 of Sanna–Shallit–Zhang, for every `n ≥ 1`: the largest `|c_{kl}|` of `V⁻¹` is a
diagonal entry `|c_{ii}|` with `i ≤ n₀`. -/
def SSZConj : Prop :=
  ∀ b : ℝ, 1 < b → ∀ n : ℕ, 1 ≤ n → ∃ i : Fin n, (i : ℕ) ≤ n0 b ∧
    ∀ k l : Fin n, |(V b n)⁻¹ k l| ≤ |(V b n)⁻¹ i i|

/-- `P_j = ∏_{h < n, h ≠ j} (X − bʰ)`. -/
noncomputable def P (b : ℝ) (n j : ℕ) : ℝ[X] := ∏ h ∈ (range n).erase j, (X - C (b ^ h))

/-- `Q_j = ∏_{h < n, h ≠ j} (X + bʰ)`. -/
noncomputable def Q (b : ℝ) (n j : ℕ) : ℝ[X] := ∏ h ∈ (range n).erase j, (X + C (b ^ h))

/-- `π_j = ∏_{h < n, h ≠ j} (bʲ − bʰ)`. -/
noncomputable def piv (b : ℝ) (n j : ℕ) : ℝ := ∏ h ∈ (range n).erase j, (b ^ j - b ^ h)

theorem n0_spec (b : ℝ) (hb : 1 < b) (j : ℕ) (hj : n0 b ≤ j) : 1 + b⁻¹ ≤ b ^ j := by
  have hpos : 0 < 1 + b⁻¹ := by
    have := inv_pos.2 (show (0 : ℝ) < b by linarith)
    linarith
  have h1 : Real.logb b (1 + b⁻¹) ≤ j := Nat.ceil_le.1 hj
  rw [Real.logb_le_iff_le_rpow hb hpos, Real.rpow_natCast] at h1
  exact h1

theorem V_posDef (b : ℝ) (hb : 1 < b) (n : ℕ) : (V b n).PosDef := by
  have hb0 : 0 < b := by linarith
  have hs : 0 < Real.log b := Real.log_pos hb
  have hexp : ∀ y : ℝ, HasSum (fun k : ℕ => y ^ k / (k.factorial : ℝ)) (Real.exp y) := fun y => by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp y
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · unfold Matrix.IsHermitian
    ext i j
    simp [V, mul_comm]
  · have hq : star x ⬝ᵥ (V b n *ᵥ x) = ∑ i : Fin n, ∑ j : Fin n,
        x i * (Real.exp (((i : ℕ) : ℝ) * ((j : ℕ) : ℝ) * Real.log b) * x j) := by
      simp only [dotProduct, mulVec, V, of_apply, Pi.star_apply, star_trivial, Finset.mul_sum]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hb0]
      push_cast
      rw [mul_comm (Real.log b)]
    have h : HasSum (fun k : ℕ => ∑ i : Fin n, ∑ j : Fin n,
        x i * ((((i : ℕ) : ℝ) * ((j : ℕ) : ℝ) * Real.log b) ^ k / (k.factorial : ℝ) * x j))
        (∑ i : Fin n, ∑ j : Fin n,
          x i * (Real.exp (((i : ℕ) : ℝ) * ((j : ℕ) : ℝ) * Real.log b) * x j)) :=
      hasSum_sum fun i _ => hasSum_sum fun j _ =>
        ((hexp (((i : ℕ) : ℝ) * ((j : ℕ) : ℝ) * Real.log b)).mul_right (x j)).mul_left (x i)
    have hsum : HasSum (fun k : ℕ => Real.log b ^ k / (k.factorial : ℝ) *
        (∑ i : Fin n, x i * ((i : ℕ) : ℝ) ^ k) ^ 2) (star x ⬝ᵥ (V b n *ᵥ x)) := by
      rw [hq]
      convert h using 1
      funext k
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine sum_congr rfl fun j _ => ?_
      ring
    obtain ⟨k, hk⟩ : ∃ k : Fin n, ∑ i : Fin n, x i * ((i : ℕ) : ℝ) ^ (k : ℕ) ≠ 0 := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      apply hx
      have hdet : (Matrix.vandermonde (fun i : Fin n => ((i : ℕ) : ℝ)))ᵀ.det ≠ 0 := by
        rw [det_transpose, det_vandermonde_ne_zero_iff]
        intro a c hac
        exact Fin.ext (by simpa using hac)
      refine eq_zero_of_mulVec_eq_zero hdet ?_
      funext k
      simp only [mulVec, dotProduct, transpose_apply, vandermonde_apply, Pi.zero_apply]
      simpa [mul_comm] using hall k
    have hpos : 0 < Real.log b ^ (k : ℕ) / ((k : ℕ).factorial : ℝ) *
        (∑ i : Fin n, x i * ((i : ℕ) : ℝ) ^ (k : ℕ)) ^ 2 :=
      mul_pos (div_pos (pow_pos hs _) (Nat.cast_pos.2 (Nat.factorial_pos _)))
        (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hk)))
    exact lt_of_lt_of_le hpos (le_hasSum hsum (k : ℕ) fun k' _ =>
      mul_nonneg (div_nonneg (pow_nonneg hs.le _) (Nat.cast_nonneg _)) (sq_nonneg _))

theorem entry_le (b : ℝ) (hb : 1 < b) (n : ℕ) (p q : Fin n) :
    |(V b n)⁻¹ p q| ≤ max ((V b n)⁻¹ p p) ((V b n)⁻¹ q q) := by
  have hC := (V_posDef b hb n).inv
  have hsym : (V b n)⁻¹ q p = (V b n)⁻¹ p q := by
    have := hC.isHermitian.apply p q
    simpa using this
  have hdet := (hC.posSemidef.submatrix ![p, q]).det_nonneg
  simp only [det_fin_two, submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  rw [hsym] at hdet
  have hp : 0 < (V b n)⁻¹ p p := hC.diag_pos
  have hq : 0 < (V b n)⁻¹ q q := hC.diag_pos
  by_contra hc
  rw [not_le] at hc
  have hu : (V b n)⁻¹ p p < |(V b n)⁻¹ p q| := lt_of_le_of_lt (le_max_left _ _) hc
  have hw : (V b n)⁻¹ q q < |(V b n)⁻¹ p q| := lt_of_le_of_lt (le_max_right _ _) hc
  nlinarith [sq_abs ((V b n)⁻¹ p q), abs_nonneg ((V b n)⁻¹ p q), mul_lt_mul'' hu hw hp.le hq.le]

theorem P_natDegree (b : ℝ) (n j : ℕ) (hj : j < n) : (P b n j).natDegree < n := by
  unfold P
  refine lt_of_le_of_lt (natDegree_prod_le _ _) ?_
  simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one,
    card_erase_of_mem (mem_range.2 hj), card_range]
  omega

theorem piv_ne_zero (b : ℝ) (hb : 1 < b) (n j : ℕ) : piv b n j ≠ 0 := by
  unfold piv
  refine prod_ne_zero_iff.2 fun h hh => sub_ne_zero.2 fun he => ?_
  have hjh : j = h := (pow_right_strictMono₀ hb).injective he
  simp only [mem_erase] at hh
  exact hh.1 hjh.symm

/-- Column `j` of `V⁻¹` is the coefficient vector of the Lagrange polynomial at `bʲ`. -/
theorem col_eq (b : ℝ) (hb : 1 < b) (n : ℕ) (i j : Fin n) :
    (V b n)⁻¹ i j = (P b n j).coeff i / piv b n j := by
  have hdet : IsUnit (V b n).det := isUnit_iff_ne_zero.2 (V_posDef b hb n).det_pos.ne'
  let w : Fin n → ℝ := fun i => (P b n j).coeff i / piv b n j
  have hw : V b n *ᵥ w = Pi.single j 1 := by
    funext k
    have hsum : (V b n *ᵥ w) k = (P b n j).eval (b ^ (k : ℕ)) / piv b n j := by
      rw [eval_eq_sum_range' (P_natDegree b n j j.isLt), ← Fin.sum_univ_eq_sum_range,
        Finset.sum_div]
      simp only [mulVec, dotProduct, V, of_apply, w]
      refine sum_congr rfl fun i _ => ?_
      rw [pow_mul]
      ring
    rw [hsum]
    unfold P
    rw [eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    by_cases hkj : k = j
    · subst hkj
      rw [Pi.single_eq_same]
      exact div_self (piv_ne_zero b hb n k)
    · rw [Pi.single_eq_of_ne hkj, Finset.prod_eq_zero (i := (k : ℕ))
        (mem_erase.2 ⟨fun h => hkj (Fin.ext h), mem_range.2 k.isLt⟩) (sub_self _), zero_div]
  have h2 := congrArg (fun u => (V b n)⁻¹ *ᵥ u) hw
  simp only [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec, mulVec_single_one] at h2
  have h3 := congrFun h2 i
  simpa [w, Matrix.col_apply] using h3.symm

theorem coeff_prod_sub (b : ℝ) (s : Finset ℕ) :
    ∀ i : ℕ, (∏ h ∈ s, (X - C (b ^ h))).coeff i
      = (-1) ^ (#s + i) * (∏ h ∈ s, (X + C (b ^ h))).coeff i := by
  induction s using Finset.induction_on with
  | empty =>
    intro i
    rcases i with _ | i <;> simp [coeff_one]
  | insert a s ha ih =>
    intro i
    rw [prod_insert ha, prod_insert ha, card_insert_of_notMem ha]
    rcases i with _ | i
    · simp only [mul_coeff_zero, coeff_sub, coeff_add, coeff_X_zero, coeff_C_zero, ih 0]
      ring
    · simp only [sub_mul, add_mul, coeff_sub, coeff_add, coeff_X_mul, coeff_C_mul, ih i,
        ih (i + 1)]
      ring

theorem coeff_prod_add_nonneg (b : ℝ) (hb : 0 ≤ b) (s : Finset ℕ) :
    ∀ i : ℕ, 0 ≤ (∏ h ∈ s, (X + C (b ^ h))).coeff i := by
  induction s using Finset.induction_on with
  | empty =>
    intro i
    rcases i with _ | i <;> simp [coeff_one]
  | insert a s ha ih =>
    intro i
    have hfa : 0 ≤ b ^ a := pow_nonneg hb a
    rw [prod_insert ha]
    rcases i with _ | i
    · simp only [mul_coeff_zero, coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
      exact mul_nonneg hfa (ih 0)
    · simp only [add_mul, coeff_add, coeff_X_mul, coeff_C_mul]
      exact add_nonneg (ih i) (mul_nonneg hfa (ih (i + 1)))

/-- `|c_{ij}| = [Xⁱ] Q_j / |π_j|`. -/
theorem col_abs (b : ℝ) (hb : 1 < b) (n : ℕ) (i j : Fin n) :
    |(V b n)⁻¹ i j| = (Q b n j).coeff i / |piv b n j| := by
  rw [col_eq b hb n i j, abs_div]
  unfold P Q
  rw [coeff_prod_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (coeff_prod_add_nonneg b (by linarith) _ _)]

/-- The numerators decrease: `[Xⁱ] Q_{j+1} ≤ [Xⁱ] Q_j`. -/
theorem Q_coeff_mono (b : ℝ) (hb : 1 < b) (n j i : ℕ) (hj : j + 1 < n) :
    (Q b n (j + 1)).coeff i ≤ (Q b n j).coeff i := by
  have h1 := Finset.mul_prod_erase ((range n).erase j) (fun h => X + C (b ^ h)) (a := j + 1)
    (by simp only [mem_erase, mem_range]; omega)
  have h2 := Finset.mul_prod_erase ((range n).erase (j + 1)) (fun h => X + C (b ^ h)) (a := j)
    (by simp only [mem_erase, mem_range]; omega)
  rw [Finset.erase_right_comm] at h2
  beta_reduce at h1 h2
  have hdiff : Q b n j - Q b n (j + 1) = C (b ^ (j + 1) - b ^ j) *
      ∏ h ∈ ((range n).erase j).erase (j + 1), (X + C (b ^ h)) := by
    unfold Q
    rw [← h1, ← h2, C_sub]
    ring
  have hc := congrArg (fun p => p.coeff i) hdiff
  simp only [coeff_sub, coeff_C_mul] at hc
  have hnn := coeff_prod_add_nonneg b (by linarith) (((range n).erase j).erase (j + 1)) i
  have hpow : b ^ j ≤ b ^ (j + 1) := pow_le_pow_right₀ hb.le (by omega)
  nlinarith [mul_nonneg (sub_nonneg.2 hpow) hnn]

theorem abs_piv (b : ℝ) (hb : 1 < b) (n j : ℕ) (hj : j < n) :
    |piv b n j| = (∏ h ∈ range j, (b ^ j - b ^ h))
      * ∏ d ∈ range (n - (j + 1)), (b ^ (j + 1 + d) - b ^ j) := by
  have hS : (range n).erase j = range j ∪ Ico (j + 1) n := by
    ext x
    simp only [mem_erase, mem_range, mem_union, mem_Ico]
    constructor <;> intro h <;> omega
  have hD : Disjoint (range j) (Ico (j + 1) n) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [mem_range, mem_Ico] at h1 h2
    omega
  unfold piv
  rw [Finset.abs_prod, hS, prod_union hD, prod_Ico_eq_prod_range]
  congr 1
  · refine prod_congr rfl fun h hh => abs_of_nonneg (sub_nonneg.2 (pow_le_pow_right₀ hb.le ?_))
    simp only [mem_range] at hh
    omega
  · refine prod_congr rfl fun d _ => ?_
    rw [abs_sub_comm]
    exact abs_of_nonneg (sub_nonneg.2 (pow_le_pow_right₀ hb.le (by omega)))

/-- `|π_j| ≤ |π_{j+1}|` once `bʲ ≥ 1 + b⁻¹` (here `n = j + 2 + r`). -/
theorem piv_mono (b : ℝ) (hb : 1 < b) (j r : ℕ) (hj : 1 + b⁻¹ ≤ b ^ j) :
    |piv b (j + 2 + r) j| ≤ |piv b (j + 2 + r) (j + 1)| := by
  have hb0 : 0 < b := by linarith
  have hA : ∏ h ∈ range (j + 1), (b ^ (j + 1) - b ^ h)
      = b ^ j * (b ^ (j + 1) - 1) * ∏ h ∈ range j, (b ^ j - b ^ h) := by
    rw [prod_range_succ', pow_zero]
    have e : ∏ h ∈ range j, (b ^ (j + 1) - b ^ (h + 1)) = ∏ h ∈ range j, (b * (b ^ j - b ^ h)) :=
      prod_congr rfl fun h _ => by ring
    rw [e, prod_mul_distrib, prod_const, card_range]
    ring
  have hB : ∏ d ∈ range (r + 1), (b ^ (j + 1 + d) - b ^ j)
      = (∏ d ∈ range r, (b ^ (j + 1 + d) - b ^ j)) * (b ^ (j + 1 + r) - b ^ j) :=
    prod_range_succ _ _
  have hB' : ∏ d ∈ range r, (b ^ (j + 1 + 1 + d) - b ^ (j + 1))
      = b ^ r * ∏ d ∈ range r, (b ^ (j + 1 + d) - b ^ j) := by
    have e : ∀ d : ℕ, b ^ (j + 1 + 1 + d) - b ^ (j + 1) = b * (b ^ (j + 1 + d) - b ^ j) :=
      fun d => by ring
    rw [prod_congr rfl fun d _ => e d, prod_mul_distrib, prod_const, card_range]
  have hA0 : 0 ≤ ∏ h ∈ range j, (b ^ j - b ^ h) :=
    prod_nonneg fun h hh => sub_nonneg.2 (pow_le_pow_right₀ hb.le
      (by simp only [mem_range] at hh; omega))
  have hG0 : 0 ≤ ∏ d ∈ range r, (b ^ (j + 1 + d) - b ^ j) :=
    prod_nonneg fun d _ => sub_nonneg.2 (pow_le_pow_right₀ hb.le (by omega))
  have hub : b + 1 ≤ b ^ j * b := by
    have h := mul_le_mul_of_nonneg_right hj hb0.le
    rwa [add_mul, inv_mul_cancel₀ hb0.ne', one_mul] at h
  have hu : 0 < b ^ j := pow_pos hb0 j
  have hw : 1 ≤ b ^ r := one_le_pow₀ hb.le
  have key : b ^ (j + 1 + r) - b ^ j ≤ b ^ j * (b ^ (j + 1) - 1) * b ^ r := by
    have e1 : b ^ (j + 1 + r) = b ^ j * b * b ^ r := by ring
    have e2 : b ^ (j + 1) = b ^ j * b := by ring
    rw [e1, e2]
    nlinarith [mul_nonneg (mul_nonneg hu.le (by linarith : (0 : ℝ) ≤ b ^ r)) (sub_nonneg.2 hub)]
  rw [abs_piv b hb (j + 2 + r) j (by omega),
    abs_piv b hb (j + 2 + r) (j + 1) (by omega),
    show j + 2 + r - (j + 1) = r + 1 by omega, show j + 2 + r - (j + 1 + 1) = r by omega,
    hA, hB, hB']
  generalize (∏ h ∈ range j, (b ^ j - b ^ h)) = A at hA0 ⊢
  generalize (∏ d ∈ range r, (b ^ (j + 1 + d) - b ^ j)) = G at hG0 ⊢
  calc A * (G * (b ^ (j + 1 + r) - b ^ j))
      = (A * G) * (b ^ (j + 1 + r) - b ^ j) := by ring
    _ ≤ (A * G) * (b ^ j * (b ^ (j + 1) - 1) * b ^ r) :=
      mul_le_mul_of_nonneg_left key (mul_nonneg hA0 hG0)
    _ = b ^ j * (b ^ (j + 1) - 1) * A * (b ^ r * G) := by ring

/-- `|c_{i,j+1}| ≤ |c_{ij}|` for `j ≥ n₀`. -/
theorem step (b : ℝ) (hb : 1 < b) (n j : ℕ) (hj : n0 b ≤ j) (hj1 : j + 1 < n) (r : Fin n) :
    |(V b n)⁻¹ r ⟨j + 1, hj1⟩| ≤ |(V b n)⁻¹ r ⟨j, by omega⟩| := by
  have hpow : 1 + b⁻¹ ≤ b ^ j := n0_spec b hb j hj
  rw [col_abs b hb n r ⟨j + 1, hj1⟩, col_abs b hb n r ⟨j, by omega⟩]
  obtain ⟨s, rfl⟩ : ∃ s, n = j + 2 + s := ⟨n - (j + 2), by omega⟩
  exact div_le_div₀ (coeff_prod_add_nonneg b (by linarith) ((range (j + 2 + s)).erase j) r)
    (Q_coeff_mono b hb (j + 2 + s) j r (by omega)) (abs_pos.2 (piv_ne_zero b hb (j + 2 + s) j))
    (piv_mono b hb j s hpow)

/-- Every column index can be capped at `n₀` without decreasing `|c|`. -/
theorem cap (b : ℝ) (hb : 1 < b) (n : ℕ) (r l : Fin n) :
    ∃ l' : Fin n, (l' : ℕ) ≤ n0 b ∧ |(V b n)⁻¹ r l| ≤ |(V b n)⁻¹ r l'| := by
  by_cases hl : (l : ℕ) ≤ n0 b
  · exact ⟨l, hl, le_rfl⟩
  · rw [not_le] at hl
    have hn0 : n0 b < n := hl.trans l.isLt
    refine ⟨⟨n0 b, hn0⟩, le_rfl, ?_⟩
    have key : ∀ d : ℕ, ∀ h : n0 b + d < n,
        |(V b n)⁻¹ r ⟨n0 b + d, h⟩| ≤ |(V b n)⁻¹ r ⟨n0 b, hn0⟩| := by
      intro d
      induction d with
      | zero => intro h; exact le_rfl
      | succ d ih =>
        intro h
        exact (step b hb n (n0 b + d) (Nat.le_add_right _ _) h r).trans (ih (by omega))
    obtain ⟨d, hd⟩ : ∃ d, (l : ℕ) = n0 b + d := ⟨l - n0 b, by omega⟩
    have hl' : l = ⟨n0 b + d, hd ▸ l.isLt⟩ := Fin.ext hd
    rw [hl']
    exact key d _

/-- **MathDB #347481 (Sanna–Shallit–Zhang, Conjecture 11), for every `n ≥ 1`.** -/
theorem ssz_conj : SSZConj := by
  intro b hb n hn
  have hC := (V_posDef b hb n).inv
  let S : Finset (Fin n) := (univ : Finset (Fin n)).filter fun i => (i : ℕ) ≤ n0 b
  have hS : S.Nonempty := ⟨⟨0, hn⟩, by simp [S]⟩
  obtain ⟨i, hiS, himax⟩ := S.exists_max_image (fun i => (V b n)⁻¹ i i) hS
  refine ⟨i, (mem_filter.1 hiS).2, fun k l => ?_⟩
  rw [abs_of_pos (hC.diag_pos (i := i))]
  obtain ⟨l', hl', h1⟩ := cap b hb n k l
  obtain ⟨k', hk', h2⟩ := cap b hb n l' k
  have hsym : (V b n)⁻¹ k l' = (V b n)⁻¹ l' k := by
    have := hC.isHermitian.apply l' k
    simpa using this
  calc |(V b n)⁻¹ k l| ≤ |(V b n)⁻¹ k l'| := h1
    _ = |(V b n)⁻¹ l' k| := by rw [hsym]
    _ ≤ |(V b n)⁻¹ l' k'| := h2
    _ ≤ max ((V b n)⁻¹ l' l') ((V b n)⁻¹ k' k') := entry_le b hb n l' k'
    _ ≤ (V b n)⁻¹ i i := max_le (himax l' (mem_filter.2 ⟨mem_univ _, hl'⟩))
        (himax k' (mem_filter.2 ⟨mem_univ _, hk'⟩))

end Principia.MathDB.P347481
