/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIYuttoSpine

set_option autoImplicit false

/-!
# `M2Y.ConvK` PROVED — `μ(r)1_{(r,k)=1}/σ(r) = (aK(k,·) ⋆ μ/id)(r)`

The three functions `F = μ·1_{(·,k)=1}/σ`, `A = aK(k,·)`, `M = μ/id` are multiplicative, so the
convolution identity `A ⋆ M = F` is checked on prime powers `p^i`
(`A(p^j) = p^{-j}` if `p | k`, `p^{-j}/(p+1)` if `p ∤ k`; `M(p) = −1/p`, `M(p^e) = 0` for `e ≥ 2`):
`A(p^{m+1}) − A(p^m)/p` is `0` except `−1/(p+1)` at `m = 0`, `p ∤ k`. Summing over `r ≤ y` with
Mathlib's `sum_Ioc_mul_eq_sum_sum` and `⌊y/a⌋ = ⌊⌊y⌋/a⌋` gives `M2Y.ConvK`.

```
 isMult_F, isMult_A, isMult_M     multiplicativity
 F_pp, A_pp, M_pp                 values at p^i
 conv_eq : fA k * fM = fF k        (k ≥ 1)                                       PROVED
 convK : M2Y.ConvK                                                                PROVED
```
-/

namespace Principia.Common.TernaryGoldbach.M2YC

open Finset ArithmeticFunction

/-- `F(r) = μ(r)1_{(r,k)=1}/σ(r)`. -/
noncomputable def fF (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun r => if Nat.Coprime r k then M2Y.mu r / M2Y.sg r else 0, by simp [M2Y.mu]⟩

/-- `A(a) = aK(k, a)`. -/
noncomputable def fA (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun a => M2Y.aK k a, by simp [M2Y.aK]⟩

/-- `M(b) = μ(b)/b`. -/
noncomputable def fM : ArithmeticFunction ℝ :=
  ⟨fun b => M2Y.mu b / b, by simp⟩

theorem fF_apply (k r : ℕ) :
    fF k r = if Nat.Coprime r k then M2Y.mu r / M2Y.sg r else 0 := rfl

theorem fA_apply (k a : ℕ) : fA k a = M2Y.aK k a := rfl

theorem fM_apply (b : ℕ) : fM b = M2Y.mu b / b := rfl

theorem mu_mul (m n : ℕ) (h : Nat.Coprime m n) : M2Y.mu (m * n) = M2Y.mu m * M2Y.mu n := by
  unfold M2Y.mu
  rw [isMultiplicative_moebius.map_mul_of_coprime h]
  push_cast
  ring

theorem sg_mul (m n : ℕ) (h : Nat.Coprime m n) : M2Y.sg (m * n) = M2Y.sg m * M2Y.sg n := by
  unfold M2Y.sg
  rw [isMultiplicative_sigma.map_mul_of_coprime h]
  push_cast
  ring

theorem isMult_M : fM.IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [fM_apply, M2Y.mu], fun {m n} _ _ h => ?_⟩
  rw [fM_apply, fM_apply, fM_apply, mu_mul m n h]
  push_cast
  rw [mul_div_mul_comm]

theorem isMult_F (k : ℕ) : (fF k).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [fF_apply, M2Y.mu, M2Y.sg], fun {m n} _ _ h => ?_⟩
  rw [fF_apply, fF_apply, fF_apply]
  by_cases hm : Nat.Coprime m k <;> by_cases hn : Nat.Coprime n k
  · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩), if_pos hm, if_pos hn, mu_mul m n h,
      sg_mul m n h, mul_div_mul_comm]
  · rw [if_neg (fun h' => hn (Nat.coprime_mul_iff_left.mp h').2), if_neg hn, mul_zero]
  · rw [if_neg (fun h' => hm (Nat.coprime_mul_iff_left.mp h').1), if_neg hm, zero_mul]
  · rw [if_neg (fun h' => hm (Nat.coprime_mul_iff_left.mp h').1), if_neg hm, zero_mul]

theorem isMult_A (k : ℕ) : (fA k).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [fA_apply, M2Y.aK], fun {m n} _ _ h => ?_⟩
  rw [fA_apply, fA_apply, fA_apply]
  unfold M2Y.aK
  rw [Nat.Coprime.primeFactors_mul h, Finset.filter_union,
    Finset.prod_union (Finset.disjoint_filter_filter h.disjoint_primeFactors)]
  push_cast
  rw [div_mul_div_comm, one_mul]
  ring

/-- `M(p^e)`. -/
theorem M_pp (p e : ℕ) (hp : p.Prime) :
    fM (p ^ e) = if e = 0 then 1 else if e = 1 then -1 / (p : ℝ) else 0 := by
  rw [fM_apply]
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    simp [M2Y.mu]
  · rw [if_neg he.ne']
    unfold M2Y.mu
    rw [moebius_apply_prime_pow hp he.ne']
    split_ifs with h1
    · subst h1
      simp
    · simp

/-- `A(p^j)`. -/
theorem A_pp (k p j : ℕ) (hp : p.Prime) :
    fA k (p ^ j) =
      if j = 0 then 1 else 1 / ((p : ℝ) ^ j * (if p ∣ k then 1 else (p : ℝ) + 1)) := by
  rw [fA_apply]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp [M2Y.aK]
  · rw [if_neg hj.ne']
    unfold M2Y.aK
    rw [Nat.primeFactors_prime_pow hj.ne' hp]
    push_cast
    congr 2
    split_ifs with h
    · rw [Finset.filter_singleton, if_neg (not_not.mpr h), Finset.prod_empty]
    · rw [Finset.filter_singleton, if_pos h, Finset.prod_singleton]

/-- `F(p^i)`. -/
theorem F_pp (k p i : ℕ) (hp : p.Prime) :
    fF k (p ^ i) =
      if i = 0 then 1 else if i = 1 ∧ ¬ p ∣ k then -1 / ((p : ℝ) + 1) else 0 := by
  rw [fF_apply]
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    simp [M2Y.mu, M2Y.sg]
  · rw [if_neg hi.ne']
    by_cases hk : p ∣ k
    · have hnc : ¬ Nat.Coprime (p ^ i) k := by
        intro hc
        have h1 : p ∣ Nat.gcd (p ^ i) k := Nat.dvd_gcd (dvd_pow_self p hi.ne') hk
        rw [hc] at h1
        exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
      rw [if_neg hnc, if_neg (fun h => h.2 hk)]
    · have hc : Nat.Coprime (p ^ i) k :=
        Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp).2 hk)
      rw [if_pos hc]
      unfold M2Y.mu M2Y.sg
      rw [moebius_apply_prime_pow hp hi.ne']
      by_cases h1 : i = 1
      · subst h1
        rw [if_pos rfl, if_pos ⟨rfl, hk⟩, sigma_one_apply_prime_pow hp]
        simp [Finset.sum_range_succ]
        ring
      · rw [if_neg h1, if_neg (fun h => h1 h.1)]
        simp

/-- **`A ⋆ M = F`.** -/
theorem conv_eq (k : ℕ) : fA k * fM = fF k := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ ((isMult_A k).mul isMult_M) _ (isMult_F k)]
  intro p i hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => fA k a * fM b),
    Nat.sum_divisors_prime_pow hp]
  have hdiv : ∀ j ∈ range (i + 1), p ^ i / p ^ j = p ^ (i - j) := fun j hj =>
    Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hp.pos
  rw [Finset.sum_congr rfl fun j hj => by rw [hdiv j hj]]
  rw [F_pp k p i hp]
  rcases i with _ | m
  · simp [(isMult_A k).map_one, isMult_M.map_one]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hz : ∑ j ∈ range m, fA k (p ^ j) * fM (p ^ (m + 1 - j)) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      rw [M_pp p _ hp, if_neg (by omega), if_neg (by omega), mul_zero]
    rw [hz, zero_add, Nat.sub_self, show m + 1 - m = 1 by omega, M_pp p 1 hp, M_pp p 0 hp,
      A_pp k p (m + 1) hp, A_pp k p m hp]
    simp only [if_true, one_ne_zero, if_false, Nat.add_one_ne_zero, mul_one]
    by_cases hk : p ∣ k
    · simp only [hk, if_true, not_true_eq_false, and_false, if_false, mul_one]
      rcases m with _ | m
      · simp
        field_simp
        ring
      · simp only [Nat.add_one_ne_zero, if_false]
        field_simp
        ring
    · simp only [hk, if_false, not_false_eq_true, and_true]
      rcases m with _ | m
      · simp
        field_simp
        ring
      · simp only [Nat.add_one_ne_zero, if_false, add_eq_right]
        field_simp
        ring

theorem Icc_one_eq (N : ℕ) : Icc 1 N = Ioc 0 N := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- **`M2Y.ConvK`, PROVED.** -/
theorem convK : M2Y.ConvK := by
  intro k _ y hy
  unfold M2Y.hY
  have h1 : ∑ r ∈ Icc 1 ⌊y⌋₊, (if Nat.Coprime r k then M2Y.mu r / M2Y.sg r else 0) =
      ∑ r ∈ Ioc 0 ⌊y⌋₊, (fA k * fM) r := by
    rw [conv_eq, Icc_one_eq]
    rfl
  rw [h1, sum_Ioc_mul_eq_sum_sum, ← Icc_one_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [fA_apply]
  congr 1
  unfold HC.mertF
  rw [Nat.floor_div_natCast, ← Icc_one_eq]
  rfl

end Principia.Common.TernaryGoldbach.M2YC
