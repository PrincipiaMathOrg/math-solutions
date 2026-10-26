import Principia.MathDB.Problem405093A
import Principia.MathDB.Problem405093Roots

/-!
# MathDB #405093 — interlacing of the zeros of `A_a`

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/405093/solution.tex`, Lemma "family".  `interlace n` is the
write-up's induction, for `a = n + 2`: `A_a` has `a − 1` strictly increasing negative zeros `rᵢ`,
and `A_{a−1}` alternates in sign on them, `(−1)^{n−i} A_{a−1}(rᵢ) > 0`.

The step follows the write-up (recurrence (5) gives `A_{a+1}(rᵢ) = −((a−1)/(a+1)) A_{a−1}(rᵢ)`,
the intermediate value theorem gives a zero in each `(rᵢ, rᵢ₊₁)` and in `(r_last, 0)`), except for
the leftmost zero: instead of the behaviour at `−∞`, `A_{a+1}` is divided by the `a − 1` zeros
found, the quotient is linear with positive slope, and its value at `r₀` places its zero below
`r₀`.  The sign clause for the new zeros comes from `A_a = lc · ∏ (X − rᵢ)` (`factor_of_roots`) and
`prod_sign`.  The roots of `A_a` were computed in SymPy for `a ≤ 5`.  The real-rootedness of
`Q_n` is the consumer.
-/

namespace Principia.MathDB.P405093

open Finset Polynomial

theorem natDegree_A (n : ℕ) : (A (n + 1)).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [coeff_A, Nat.choose_eq_zero_of_lt (by exact_mod_cast hm), Nat.cast_zero, zero_div]
  · rw [coeff_A, Nat.choose_self]
    positivity

theorem leadingCoeff_A_pos (n : ℕ) : 0 < (A (n + 1)).leadingCoeff := by
  rw [leadingCoeff, natDegree_A, coeff_A, Nat.choose_self]
  positivity

theorem A_ne_zero (n : ℕ) : A (n + 1) ≠ 0 := fun h => by
  have := leadingCoeff_A_pos n
  rw [h, leadingCoeff_zero] at this
  exact lt_irrefl 0 this

/-- The recurrence (5) evaluated at a point. -/
theorem eval_A_rec (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 3) * (A (n + 1 + 1 + 1)).eval x
      = (2 * ((n : ℝ) + 2) + x) * (A (n + 1 + 1)).eval x - ((n : ℝ) + 1) * (A (n + 1)).eval x := by
  have h := congrArg (eval x) (A_rec n)
  simpa [eval_mul, eval_sub, eval_add, eval_C, eval_X] using h

/-- A zero of `p` strictly between two points where `p` has opposite signs. -/
theorem exists_root_between (p : ℝ[X]) {a b : ℝ} (hab : a < b)
    (h : p.eval a * p.eval b < 0) : ∃ c, a < c ∧ c < b ∧ p.eval c = 0 := by
  have hc : ContinuousOn (fun x => p.eval x) (Set.Icc a b) := p.continuous.continuousOn
  rcases lt_or_gt_of_ne (show p.eval a ≠ 0 by rintro h0; simp [h0] at h) with ha | ha
  · have hb : 0 < p.eval b := by nlinarith
    obtain ⟨c, hc', hcv⟩ := intermediate_value_Ioo hab.le hc ⟨ha, hb⟩
    exact ⟨c, hc'.1, hc'.2, hcv⟩
  · have hb : p.eval b < 0 := by nlinarith
    obtain ⟨c, hc', hcv⟩ := intermediate_value_Ioo' hab.le hc ⟨hb, ha⟩
    exact ⟨c, hc'.1, hc'.2, hcv⟩

/-- **The interlacing lemma** for `a = n + 2`. -/
theorem interlace : ∀ n : ℕ, ∃ r : Fin (n + 1) → ℝ, StrictMono r ∧ (∀ i, r i < 0) ∧
    (∀ i, (A (n + 1 + 1)).eval (r i) = 0) ∧
    (∀ i : Fin (n + 1), 0 < (-1 : ℝ) ^ (n - (i : ℕ)) * (A (n + 1)).eval (r i)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun _ => -2, fun i j h => absurd h (by omega), fun _ => by norm_num, fun _ => ?_,
      fun _ => ?_⟩
    · rw [eval_eq_sum_range' (n := 2) (by rw [natDegree_A]; norm_num)]
      simp [coeff_A, Finset.sum_range_succ, Nat.factorial]
      norm_num
    · rw [eval_eq_sum_range' (n := 1) (by rw [natDegree_A]; norm_num)]
      simp [coeff_A, Nat.factorial]
  | succ n ih =>
    obtain ⟨r, hmono, hneg, hroot, hsign⟩ := ih
    -- signs of `A_{n+3}` at the old zeros and at `0`
    have hval : ∀ i : Fin (n + 1),
        0 < (-1 : ℝ) ^ (n + 1 - (i : ℕ)) * (A (n + 1 + 1 + 1)).eval (r i) := by
      intro i
      have hrec := eval_A_rec n (r i)
      rw [hroot i, mul_zero, zero_sub] at hrec
      have hs := hsign i
      rw [show n + 1 - (i : ℕ) = (n - (i : ℕ)) + 1 by omega, pow_succ]
      have h3 : (0 : ℝ) < (n : ℝ) + 3 := by positivity
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have key : ((n : ℝ) + 3) * ((-1 : ℝ) ^ (n - (i : ℕ)) * -1 * (A (n + 1 + 1 + 1)).eval (r i))
          = ((n : ℝ) + 1) * ((-1 : ℝ) ^ (n - (i : ℕ)) * (A (n + 1)).eval (r i)) := by
        linear_combination (-(-1 : ℝ) ^ (n - (i : ℕ))) * hrec
      have hm := mul_pos h1 hs
      rw [← key] at hm
      exact pos_of_mul_pos_right hm h3.le
    have h0 : (A (n + 1 + 1 + 1)).eval 0 = 1 := eval_A_zero _
    -- the endpoints of the `n + 1` intervals
    let hi : Fin (n + 1) → ℝ := fun j => if h : (j : ℕ) + 1 < n + 1 then r ⟨j + 1, h⟩ else 0
    have hlohi : ∀ j : Fin (n + 1), r j < hi j := by
      intro j
      simp only [hi]
      split_ifs with h
      · exact hmono (show j < ⟨j + 1, h⟩ from Fin.mk_lt_mk.2 (by simp))
      · exact hneg j
    have hopp : ∀ j : Fin (n + 1),
        (A (n + 1 + 1 + 1)).eval (r j) * (A (n + 1 + 1 + 1)).eval (hi j) < 0 := by
      intro j
      simp only [hi]
      split_ifs with h
      · have s1 := hval j
        have s2 := hval ⟨j + 1, h⟩
        simp only at s2
        rw [show n + 1 - (j : ℕ) = (n - (j : ℕ)) + 1 by omega] at s1
        rw [show n + 1 - ((j : ℕ) + 1) = n - (j : ℕ) by omega] at s2
        rw [pow_succ] at s1
        have hp : (0 : ℝ) < ((-1 : ℝ) ^ (n - (j : ℕ))) ^ 2 := by positivity
        nlinarith [mul_pos s1 s2]
      · have hj : (j : ℕ) = n := by omega
        have s1 := hval j
        rw [show n + 1 - (j : ℕ) = 1 by omega, pow_one] at s1
        rw [h0, mul_one]
        linarith
    have hex : ∀ j : Fin (n + 1), ∃ c, r j < c ∧ c < hi j ∧ (A (n + 1 + 1 + 1)).eval c = 0 :=
      fun j => exists_root_between _ (hlohi j) (hopp j)
    choose s hs1 hs2 hs3 using hex
    -- `s` is strictly increasing
    have hsmono : StrictMono s := by
      apply Fin.strictMono_iff_lt_succ.2
      intro j
      have h1 := hs2 j.castSucc
      have h2 := hs1 j.succ
      simp only [hi, Fin.coe_castSucc] at h1
      rw [dif_pos (by omega)] at h1
      have : r ⟨(j : ℕ) + 1, by omega⟩ = r j.succ := rfl
      linarith
    -- divide `A_{n+3}` by `∏ (X − sⱼ)`
    have hAne := A_ne_zero (n + 1 + 1)
    have hdvd : (∏ j, (X - C (s j))) ∣ A (n + 1 + 1 + 1) := by
      have hle : (univ.image s).val ≤ (A (n + 1 + 1 + 1)).roots := by
        rw [Multiset.le_iff_subset (univ.image s).nodup]
        intro x hx
        obtain ⟨j, _, rfl⟩ := mem_image.1 (show x ∈ univ.image s from hx)
        exact (mem_roots hAne).2 (hs3 j)
      have := (Multiset.prod_X_sub_C_dvd_iff_le_roots hAne _).2 hle
      rwa [← Finset.prod_image (f := fun a => X - C a) (fun i _ j _ h => hsmono.injective h)]
    obtain ⟨q, hq⟩ := hdvd
    have hPmonic : (∏ j, (X - C (s j))).Monic := monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
    have hPdeg : (∏ j, (X - C (s j))).natDegree = n + 1 := by
      rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
      simp
    have hqne : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hAne hq
    have hqdeg : q.natDegree = 1 := by
      have := congrArg natDegree hq
      rw [natDegree_A, hPmonic.natDegree_mul' hqne, hPdeg] at this
      omega
    have hqlead : q.leadingCoeff = (A (n + 1 + 1 + 1)).leadingCoeff := by
      rw [hq, leadingCoeff_mul, hPmonic.leadingCoeff, one_mul]
    have hq1 : 0 < q.coeff 1 := by
      have := leadingCoeff_A_pos (n + 1 + 1)
      rwa [← hqlead, leadingCoeff, hqdeg] at this
    have hqform := eq_X_add_C_of_natDegree_le_one hqdeg.le
    -- the value of `q` at `r₀` is positive
    have hr0 := hval 0
    have hP0 : 0 < (-1 : ℝ) ^ (n + 1 - 0) * ∏ j, (r 0 - s j) := by
      refine prod_sign (n + 1) s (r 0) 0 (by omega) (fun i hik => absurd hik (by omega))
        fun i _ => ?_
      have := hs1 i
      have hmono0 : r 0 ≤ r i := hmono.monotone (Fin.zero_le _)
      linarith
    have hAr0 : (A (n + 1 + 1 + 1)).eval (r 0) = (∏ j, (r 0 - s j)) * q.eval (r 0) := by
      conv_lhs => rw [hq]
      rw [eval_mul, eval_prod]
      simp [eval_sub, eval_X, eval_C]
    have hqr0 : 0 < q.eval (r 0) := by
      rw [hAr0] at hr0
      have e : (-1 : ℝ) ^ (n + 1 - ((0 : Fin (n + 1)) : ℕ))
          * ((∏ j, (r 0 - s j)) * q.eval (r 0))
          = ((-1 : ℝ) ^ (n + 1 - 0) * ∏ j, (r 0 - s j)) * q.eval (r 0) := by
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]
        ring
      rw [e] at hr0
      exact pos_of_mul_pos_right hr0 hP0.le
    -- the leftmost zero `t`
    set t := -q.coeff 0 / q.coeff 1 with ht
    have hqt : q.eval t = 0 := by
      rw [hqform]
      simp only [eval_add, eval_mul, eval_C, eval_X, ht]
      field_simp
      ring
    have htr0 : t < r 0 := by
      have hq0 : q.eval (r 0) = q.coeff 1 * r 0 + q.coeff 0 := by
        rw [hqform]
        simp
      rw [hq0] at hqr0
      rw [ht, div_lt_iff₀ hq1]
      linarith
    have hAt : (A (n + 1 + 1 + 1)).eval t = 0 := by
      rw [hq, eval_mul, hqt, mul_zero]
    -- the new zero list
    refine ⟨Fin.cons t s, ?_, ?_, ?_, ?_⟩
    · refine Fin.strictMono_iff_lt_succ.2 fun j => ?_
      refine Fin.cases ?_ (fun k => ?_) j
      · show t < s 0
        have := hs1 0
        linarith
      · show s k.castSucc < s k.succ
        exact hsmono Fin.castSucc_lt_succ
    · refine Fin.cases ?_ (fun k => ?_)
      · simp only [Fin.cons_zero]
        linarith [hneg 0]
      · simp only [Fin.cons_succ]
        have h1 := hs2 k
        simp only [hi] at h1
        split_ifs at h1 with h
        · linarith [hneg ⟨k + 1, h⟩]
        · exact h1
    · refine Fin.cases ?_ (fun k => ?_)
      · simpa using hAt
      · simpa using hs3 k
    · -- signs of `A_{n+2}` on the new zeros, from its factorization over the old zeros
      have hfac := factor_of_roots (A (n + 1 + 1)) (n + 1) (natDegree_A _) (A_ne_zero _) r
        hmono.injective hroot
      have hlc := leadingCoeff_A_pos (n + 1)
      refine Fin.cases ?_ (fun k => ?_)
      · simp only [Fin.cons_zero, Fin.val_zero]
        rw [hfac, eval_mul, eval_C, eval_prod]
        simp only [eval_sub, eval_X, eval_C]
        have := prod_sign (n + 1) r t 0 (by omega) (fun i hik => absurd hik (by omega))
          fun i _ => by
          have : r 0 ≤ r i := hmono.monotone (Fin.zero_le _)
          linarith
        rw [Nat.sub_zero] at this ⊢
        rw [mul_left_comm]
        exact mul_pos hlc this
      · simp only [Fin.cons_succ, Fin.val_succ]
        rw [hfac, eval_mul, eval_C, eval_prod]
        simp only [eval_sub, eval_X, eval_C]
        have := prod_sign (n + 1) r (s k) ((k : ℕ) + 1) (by omega)
          (fun i hik => by
            have : r i ≤ r k := hmono.monotone (Fin.mk_le_mk.2 (by omega))
            linarith [hs1 k])
          (fun i hik => by
            have h2 := hs2 k
            simp only [hi] at h2
            rw [dif_pos (by omega)] at h2
            have : r ⟨(k : ℕ) + 1, by omega⟩ ≤ r i := hmono.monotone (Fin.mk_le_mk.2 (by omega))
            linarith)
        rw [mul_left_comm]
        exact mul_pos hlc this

end Principia.MathDB.P405093
