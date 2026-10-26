import Principia.MathDB.Problem405093Interlace

/-!
# MathDB #405093 — real-rootedness from sign alternation

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/405093/solution.tex`, Lemma "sum" (the zeros of `Q_n`).  The
write-up counts `2n − 2` sign-change intervals of `Q_n`, using the sign of `Q_n` near `−∞` for the
leftmost one.  `alt_real_rooted` packages the counting for any real polynomial: if `P` has degree
`N + 1`, positive leading coefficient, and strictly increasing points `p₀ < ⋯ < p_N` with
`(−1)^{N−k} P(p_k) > 0`, then all `N + 1` zeros of `P` are real (`card roots = natDegree`) and lie
below `p_N`.  As in `interlace`, the leftmost zero comes from the linear quotient of `P` by the `N`
zeros found between the points, not from the behaviour at `−∞`.  The real-rootedness of `Q_n` is
the consumer.
-/

namespace Principia.MathDB.P405093

open Finset Polynomial

/-- **Real-rootedness from `N + 1` alternating signs** for a polynomial of degree `N + 1`. -/
theorem alt_real_rooted (P : ℝ[X]) (N : ℕ) (hdeg : P.natDegree = N + 1)
    (hlead : 0 < P.leadingCoeff) (p : Fin (N + 1) → ℝ) (hp : StrictMono p)
    (hsign : ∀ k : Fin (N + 1), 0 < (-1 : ℝ) ^ (N - (k : ℕ)) * P.eval (p k)) :
    Multiset.card P.roots = P.natDegree ∧ ∀ x ∈ P.roots, x < p (Fin.last N) := by
  have hPne : P ≠ 0 := fun h => by rw [h, leadingCoeff_zero] at hlead; exact lt_irrefl 0 hlead
  -- a zero between consecutive points
  have hex : ∀ k : Fin N, ∃ c, p k.castSucc < c ∧ c < p k.succ ∧ P.eval c = 0 := by
    intro k
    refine exists_root_between P (hp Fin.castSucc_lt_succ) ?_
    have s1 := hsign k.castSucc
    have s2 := hsign k.succ
    simp only [Fin.coe_castSucc, Fin.val_succ] at s1 s2
    rw [show N - (k : ℕ) = (N - ((k : ℕ) + 1)) + 1 by omega, pow_succ] at s1
    have hp2 : (0 : ℝ) < ((-1 : ℝ) ^ (N - ((k : ℕ) + 1))) ^ 2 := by positivity
    nlinarith [mul_pos s1 s2]
  choose s hs1 hs2 hs3 using hex
  have hsmono : StrictMono s := by
    intro i j hij
    have h1 := hs2 i
    have h2 := hs1 j
    have : p i.succ ≤ p j.castSucc :=
      hp.monotone (Fin.le_iff_val_le_val.2 (by simp; exact Fin.lt_iff_val_lt_val.1 hij))
    linarith
  -- divide by the zeros found
  have hdvd : (∏ j, (X - C (s j))) ∣ P := by
    have hle : (univ.image s).val ≤ P.roots := by
      rw [Multiset.le_iff_subset (univ.image s).nodup]
      intro x hx
      obtain ⟨j, _, rfl⟩ := mem_image.1 (show x ∈ univ.image s from hx)
      exact (mem_roots hPne).2 (hs3 j)
    have := (Multiset.prod_X_sub_C_dvd_iff_le_roots hPne _).2 hle
    rwa [← Finset.prod_image (f := fun a => X - C a) (fun i _ j _ h => hsmono.injective h)]
  obtain ⟨q, hq⟩ := hdvd
  have hPmonic : (∏ j, (X - C (s j))).Monic := monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
  have hPdeg : (∏ j, (X - C (s j))).natDegree = N := by
    rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
    simp
  have hqne : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hPne hq
  have hqdeg : q.natDegree = 1 := by
    have := congrArg natDegree hq
    rw [hdeg, hPmonic.natDegree_mul' hqne, hPdeg] at this
    omega
  have hq1 : 0 < q.coeff 1 := by
    have hql : q.leadingCoeff = P.leadingCoeff := by
      rw [hq, leadingCoeff_mul, hPmonic.leadingCoeff, one_mul]
    rwa [← hql, leadingCoeff, hqdeg] at hlead
  have hqform := eq_X_add_C_of_natDegree_le_one hqdeg.le
  -- `q(p₀) > 0`
  have hs0 := hsign 0
  have hprod : 0 < (-1 : ℝ) ^ (N - 0) * ∏ j, (p 0 - s j) := by
    refine prod_sign N s (p 0) 0 (by omega) (fun i hik => absurd hik (by omega)) fun i _ => ?_
    have := hs1 i
    have : p 0 ≤ p i.castSucc := hp.monotone (Fin.zero_le _)
    linarith
  have hP0 : P.eval (p 0) = (∏ j, (p 0 - s j)) * q.eval (p 0) := by
    conv_lhs => rw [hq]
    rw [eval_mul, eval_prod]
    simp [eval_sub, eval_X, eval_C]
  have hqp0 : 0 < q.eval (p 0) := by
    rw [hP0] at hs0
    have e : (-1 : ℝ) ^ (N - ((0 : Fin (N + 1)) : ℕ)) * ((∏ j, (p 0 - s j)) * q.eval (p 0))
        = ((-1 : ℝ) ^ (N - 0) * ∏ j, (p 0 - s j)) * q.eval (p 0) := by
      simp only [Fin.val_zero]
      ring
    rw [e] at hs0
    exact pos_of_mul_pos_right hs0 hprod.le
  -- the leftmost zero
  set t := -q.coeff 0 / q.coeff 1 with ht
  have hqt : q.eval t = 0 := by
    rw [hqform]
    simp only [eval_add, eval_mul, eval_C, eval_X, ht]
    field_simp
    ring
  have htp0 : t < p 0 := by
    have hq0 : q.eval (p 0) = q.coeff 1 * p 0 + q.coeff 0 := by
      rw [hqform]
      simp
    rw [hq0] at hqp0
    rw [ht, div_lt_iff₀ hq1]
    linarith
  have hPt : P.eval t = 0 := by rw [hq, eval_mul, hqt, mul_zero]
  -- the `N + 1` zeros `t, s₀, …`
  let z : Fin (N + 1) → ℝ := Fin.cons t s
  have hzmono : StrictMono z := by
    intro a b hab
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact absurd hab (lt_irrefl _)
      | succ b' =>
        show t < s b'
        have h1 := hs1 b'
        have h2 : p 0 ≤ p b'.castSucc := hp.monotone (Fin.zero_le _)
        linarith
    | succ a' =>
      induction b using Fin.cases with
      | zero => exact absurd hab (Fin.not_lt_zero _)
      | succ b' =>
        show s a' < s b'
        exact hsmono (Fin.succ_lt_succ_iff.1 hab)
  have hzroot : ∀ k, P.eval (z k) = 0 := by
    refine Fin.cases ?_ (fun k => ?_)
    · simpa [z] using hPt
    · simpa [z] using hs3 k
  have hfac := factor_of_roots P (N + 1) hdeg hPne z hzmono.injective hzroot
  have hroots : Multiset.card P.roots = P.natDegree := by
    have hsub : (univ.image z).val ≤ P.roots := by
      rw [Multiset.le_iff_subset (univ.image z).nodup]
      intro x hx
      obtain ⟨j, _, rfl⟩ := mem_image.1 (show x ∈ univ.image z from hx)
      exact (mem_roots hPne).2 (hzroot j)
    have hc : Multiset.card (univ.image z).val = N + 1 := by
      rw [Finset.card_val, card_image_of_injective _ hzmono.injective, card_univ, Fintype.card_fin]
    have := Multiset.card_le_card hsub
    have := card_roots' P
    omega
  refine ⟨hroots, fun x hx => ?_⟩
  have hx0 : P.eval x = 0 := (mem_roots hPne).1 hx
  rw [hfac, eval_mul, eval_C, eval_prod] at hx0
  rcases mul_eq_zero.1 hx0 with h | h
  · exact absurd h (ne_of_gt hlead)
  obtain ⟨k, _, hk⟩ := Finset.prod_eq_zero_iff.1 h
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hk
  rw [hk]
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [z, Fin.cons_zero]
    have : p 0 ≤ p (Fin.last N) := hp.monotone (Fin.zero_le _)
    linarith
  · simp only [z, Fin.cons_succ]
    have := hs2 j
    have : p j.succ ≤ p (Fin.last N) := hp.monotone (Fin.le_last _)
    linarith

end Principia.MathDB.P405093
