import Principia.MathDB.Problem405093Alt

/-!
# MathDB #405093 — `Q_n = A_{n−1}A_{n+1} + A_n²` has only real negative zeros

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/405093/solution.tex`, Lemma "sum" with `α = β = 1`, for `n = m + 2`.
With the zeros `r₀ < ⋯ < r_m < 0` of `A_{m+2}` (`interlace m`), `Q(rᵢ) < 0` by the recurrence,
and between consecutive `rᵢ` the polynomial `A_{m+1}` changes sign, so it has a zero `cᵢ` there,
where `Q(cᵢ) = A_{m+2}(cᵢ)² > 0`; also `Q(0) = 2`.  The `2m + 2` points
`r₀ < c₀ < r₁ < ⋯ < c_{m−1} < r_m < 0` alternate in sign, so `alt_real_rooted` gives
`card roots = natDegree = 2m + 2` with all zeros negative (`Q_real_rooted`).  Checked in SymPy for
`m ≤ 4`.  The log-concavity theorem is the consumer.
-/

namespace Principia.MathDB.P405093

open Finset Polynomial

/-- `Q = A_{m+1} A_{m+3} + A_{m+2}²`. -/
noncomputable def Q (m : ℕ) : ℝ[X] := A (m + 1) * A (m + 1 + 1 + 1) + A (m + 1 + 1) ^ 2

theorem coeff_Q_top (m : ℕ) : (Q m).coeff (2 * m + 2)
    = (A (m + 1)).leadingCoeff * (A (m + 1 + 1 + 1)).leadingCoeff
      + (A (m + 1 + 1)).leadingCoeff ^ 2 := by
  unfold Q
  rw [coeff_add, sq, sq]
  have e1 : 2 * m + 2 = (A (m + 1)).natDegree + (A (m + 1 + 1 + 1)).natDegree := by
    rw [natDegree_A, natDegree_A]
    ring
  have e2 : 2 * m + 2 = (A (m + 1 + 1)).natDegree + (A (m + 1 + 1)).natDegree := by
    rw [natDegree_A]
    ring
  rw [show (A (m + 1) * A (m + 1 + 1 + 1)).coeff (2 * m + 2)
      = (A (m + 1)).leadingCoeff * (A (m + 1 + 1 + 1)).leadingCoeff by
    rw [e1]; exact coeff_mul_degree_add_degree _ _]
  rw [show (A (m + 1 + 1) * A (m + 1 + 1)).coeff (2 * m + 2)
      = (A (m + 1 + 1)).leadingCoeff * (A (m + 1 + 1)).leadingCoeff by
    rw [e2]; exact coeff_mul_degree_add_degree _ _]

theorem coeff_Q_top_pos (m : ℕ) : 0 < (Q m).coeff (2 * m + 2) := by
  rw [coeff_Q_top]
  have := leadingCoeff_A_pos m
  have := leadingCoeff_A_pos (m + 1 + 1)
  have := leadingCoeff_A_pos (m + 1)
  positivity

theorem natDegree_Q (m : ℕ) : (Q m).natDegree = 2 * m + 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero _ (coeff_Q_top_pos m).ne'
  unfold Q
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans ?_
    rw [natDegree_A, natDegree_A]
    omega
  · refine natDegree_pow_le.trans ?_
    rw [natDegree_A]
    omega

theorem leadingCoeff_Q_pos (m : ℕ) : 0 < (Q m).leadingCoeff := by
  rw [leadingCoeff, natDegree_Q]
  exact coeff_Q_top_pos m

theorem eval_Q (m : ℕ) (x : ℝ) : (Q m).eval x
    = (A (m + 1)).eval x * (A (m + 1 + 1 + 1)).eval x + (A (m + 1 + 1)).eval x ^ 2 := by
  simp [Q, eval_add, eval_mul, eval_pow]

/-- **`Q` has `2m + 2` real zeros, all negative.** -/
theorem Q_real_rooted (m : ℕ) :
    Multiset.card (Q m).roots = (Q m).natDegree ∧ ∀ x ∈ (Q m).roots, x < 0 := by
  obtain ⟨r, hmono, hneg, hroot, hsign⟩ := interlace m
  have hfac := factor_of_roots (A (m + 1 + 1)) (m + 1) (natDegree_A _) (A_ne_zero _) r
    hmono.injective hroot
  -- `Q < 0` at the zeros of `A_{m+2}`
  have hQr : ∀ i, (Q m).eval (r i) < 0 := by
    intro i
    have hrec := eval_A_rec m (r i)
    rw [hroot i, mul_zero, zero_sub] at hrec
    have hs := hsign i
    have hA1 : (A (m + 1)).eval (r i) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hs
      exact lt_irrefl 0 hs
    rw [eval_Q, hroot i]
    have hpos : 0 < (A (m + 1)).eval (r i) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hA1))
    have h3 : (0 : ℝ) < (m : ℝ) + 3 := by positivity
    have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have key : ((m : ℝ) + 3) * ((A (m + 1)).eval (r i) * (A (m + 1 + 1 + 1)).eval (r i) + 0 ^ 2)
        = -(((m : ℝ) + 1) * (A (m + 1)).eval (r i) ^ 2) := by
      linear_combination ((A (m + 1)).eval (r i)) * hrec
    have hneg' : ((m : ℝ) + 3)
        * ((A (m + 1)).eval (r i) * (A (m + 1 + 1 + 1)).eval (r i) + 0 ^ 2) < 0 := by
      rw [key]
      have := mul_pos h1 hpos
      linarith
    exact neg_of_mul_neg_right hneg' h3.le
  -- a zero of `A_{m+1}` between consecutive zeros of `A_{m+2}`
  have hex : ∀ i : Fin m, ∃ c, r i.castSucc < c ∧ c < r i.succ ∧ (A (m + 1)).eval c = 0 := by
    intro i
    refine exists_root_between _ (hmono Fin.castSucc_lt_succ) ?_
    have s1 := hsign i.castSucc
    have s2 := hsign i.succ
    simp only [Fin.coe_castSucc, Fin.val_succ] at s1 s2
    rw [show m - (i : ℕ) = (m - ((i : ℕ) + 1)) + 1 by omega, pow_succ] at s1
    have hp2 : (0 : ℝ) < ((-1 : ℝ) ^ (m - ((i : ℕ) + 1))) ^ 2 := by positivity
    nlinarith [mul_pos s1 s2]
  choose c hc1 hc2 hc3 using hex
  have hQc : ∀ i, 0 < (Q m).eval (c i) := by
    intro i
    rw [eval_Q, hc3 i, zero_mul, zero_add]
    have hne : (A (m + 1 + 1)).eval (c i) ≠ 0 := by
      rw [hfac, eval_mul, eval_C, eval_prod]
      simp only [eval_sub, eval_X, eval_C]
      have hps := prod_sign (m + 1) r (c i) ((i : ℕ) + 1) (by omega)
        (fun j hj => by
          have : r j ≤ r i.castSucc := hmono.monotone (Fin.le_iff_val_le_val.2 (by simp; omega))
          linarith [hc1 i])
        (fun j hj => by
          have : r i.succ ≤ r j := hmono.monotone (Fin.le_iff_val_le_val.2 (by simp; omega))
          linarith [hc2 i])
      have hlc := leadingCoeff_A_pos (m + 1)
      intro h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hlc.ne'
      · rw [h, mul_zero] at hps
        exact lt_irrefl 0 hps
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  have hQ0 : (Q m).eval 0 = 2 := by
    rw [eval_Q, eval_A_zero, eval_A_zero, eval_A_zero]
    norm_num
  -- the alternating points
  let rr : ℕ → ℝ := fun i => if h : i < m + 1 then r ⟨i, h⟩ else 0
  let cc : ℕ → ℝ := fun i => if h : i < m then c ⟨i, h⟩ else 0
  let p : Fin (2 * m + 1 + 1) → ℝ := fun k =>
    if (k : ℕ) % 2 = 0 then rr ((k : ℕ) / 2) else if (k : ℕ) / 2 < m then cc ((k : ℕ) / 2) else 0
  have hp : StrictMono p := by
    refine Fin.strictMono_iff_lt_succ.2 fun k => ?_
    simp only [p, Fin.coe_castSucc, Fin.val_succ]
    have hk := k.isLt
    rcases Nat.even_or_odd' (k : ℕ) with ⟨i, hi | hi⟩
    · have e1 : (2 * i) % 2 = 0 := by omega
      have e2 : (2 * i) / 2 = i := by omega
      have e3 : (2 * i + 1) % 2 = 1 := by omega
      have e4 : (2 * i + 1) / 2 = i := by omega
      rw [hi]
      simp only [e1, e2, e3, e4, if_true, one_ne_zero, if_false]
      simp only [rr, cc, dif_pos (show i < m + 1 by omega)]
      split_ifs with h
      · exact hc1 ⟨i, h⟩
      · exact hneg _
    · have e1 : (2 * i + 1) % 2 = 1 := by omega
      have e2 : (2 * i + 1) / 2 = i := by omega
      have e3 : (2 * i + 1 + 1) % 2 = 0 := by omega
      have e4 : (2 * i + 1 + 1) / 2 = i + 1 := by omega
      rw [hi]
      simp only [e1, e2, e3, e4, if_true, one_ne_zero, if_false]
      rw [if_pos (show i < m by omega)]
      simp only [rr, cc, dif_pos (show i < m by omega), dif_pos (show i + 1 < m + 1 by omega)]
      exact hc2 ⟨i, by omega⟩
  have hsgn : ∀ k : Fin (2 * m + 1 + 1),
      0 < (-1 : ℝ) ^ (2 * m + 1 - (k : ℕ)) * (Q m).eval (p k) := by
    intro k
    simp only [p]
    rcases Nat.even_or_odd' (k : ℕ) with ⟨i, hi | hi⟩
    · have hk := k.isLt
      rw [hi, if_pos (by omega), show 2 * i / 2 = i by omega,
        Odd.neg_one_pow ⟨m - i, by omega⟩]
      simp only [rr, dif_pos (show i < m + 1 by omega)]
      linarith [hQr ⟨i, by omega⟩]
    · have hk := k.isLt
      rw [hi, if_neg (by omega), show (2 * i + 1) / 2 = i by omega,
        Even.neg_one_pow ⟨m - i, by omega⟩, one_mul]
      split_ifs with h
      · simp only [cc, dif_pos h]
        exact hQc _
      · rw [hQ0]
        norm_num
  have hdeg : (Q m).natDegree = 2 * m + 1 + 1 := by rw [natDegree_Q]
  obtain ⟨hcard, hlt⟩ := alt_real_rooted (Q m) (2 * m + 1) hdeg (leadingCoeff_Q_pos m) p hp hsgn
  refine ⟨hcard, fun x hx => ?_⟩
  have := hlt x hx
  have hlast : p (Fin.last (2 * m + 1)) = 0 := by
    simp only [p, Fin.val_last]
    rw [if_neg (by omega), if_neg (by omega)]
  linarith

end Principia.MathDB.P405093
