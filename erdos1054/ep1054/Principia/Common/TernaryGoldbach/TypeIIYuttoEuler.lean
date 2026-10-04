/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIYuttoSpine

set_option autoImplicit false

/-!
# Finite Euler-product tools for the `lem:yutto` links

Campaign-agnostic facts about nonnegative multiplicative functions, used by the four
Euler-product links of `M2Y` (`KSumH`, `KSumQ`, `DSumH`, `DSumQ`):

```
 euler_le      ∑_{n ≤ N} F(n) ≤ ∏_{p ≤ N} ∑_{j ≤ N} F(p^j)    (F ≥ 0 multiplicative, F(1) = 1)
 mult_le       f ≤ g pointwise if f(p^k) ≤ g(p^k)             (f ≥ 0, f, g multiplicative)
 inv_sqrt_step 1/(n√n) ≤ 1/√(n−2) − 1/√n                     (n ≥ 3)
 odd_tail      ∑_{i < J} 1/((M+2i)√(M+2i)) ≤ 1/√(M−2)
 exp_le_inv    e^t ≤ 1/(1 − t)                                (t < 1)
 prod_primes_le ∏_{p ∈ P odd}(1 + x_p) ≤ ∏_{p ∈ L}(1 + u_p)/(1 − C/√(M−2))
               (explicit small primes `L`, tail `x_p ≤ C/(p√p)` for `p ≥ M`)
```
-/

namespace Principia.Common.TernaryGoldbach.M2YE

open Finset

/-! ## (1) The finite Euler product -/

/-- The inductive step's set: `n ≤ N` with all prime factors in `P`. -/
theorem euler_key (F : ℕ → ℝ) (h0 : ∀ n, 0 ≤ F n) (h1 : F 1 = 1)
    (hm : ∀ m n, m ≠ 0 → n ≠ 0 → Nat.Coprime m n → F (m * n) = F m * F n) (N : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ n ∈ (Icc 1 N).filter (fun n => n.primeFactors ⊆ P), F n ≤
      ∏ p ∈ P, ∑ j ∈ range (N + 1), F (p ^ j) := by
  induction P using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    have hsub : (Icc 1 N).filter (fun n => n.primeFactors ⊆ (∅ : Finset ℕ)) ⊆ {1} := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.subset_empty,
        Nat.primeFactors_eq_empty] at hn
      simp only [Finset.mem_singleton]
      omega
    calc ∑ n ∈ (Icc 1 N).filter (fun n => n.primeFactors ⊆ (∅ : Finset ℕ)), F n
        ≤ ∑ n ∈ ({1} : Finset ℕ), F n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => h0 n
      _ = 1 := by rw [Finset.sum_singleton, h1]
  | insert p P hpP ih =>
    have hp : p.Prime := hP p (Finset.mem_insert_self p P)
    have ih' := ih fun q hq => hP q (Finset.mem_insert_of_mem hq)
    set S := (Icc 1 N).filter (fun n => n.primeFactors ⊆ P) with hS
    have hsub : (Icc 1 N).filter (fun n => n.primeFactors ⊆ insert p P) ⊆
        (range (N + 1) ×ˢ S).image (fun x : ℕ × ℕ => p ^ x.1 * x.2) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnN⟩, hnP⟩ := hn
      have hn0 : n ≠ 0 := by omega
      rw [Finset.mem_image]
      refine ⟨(n.factorization p, n / p ^ n.factorization p), ?_,
        Nat.ordProj_mul_ordCompl_eq_self n p⟩
      have hpj : p ^ n.factorization p ≤ n := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p)
      have hm0 := Nat.ordCompl_pos p hn0
      simp only [Finset.mem_product, Finset.mem_range, hS, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨?_, ⟨by omega, le_trans (Nat.div_le_self _ _) hnN⟩, ?_⟩
      · have := Nat.lt_pow_self hp.one_lt (n := n.factorization p)
        omega
      · intro q hq
        have hqp : q ≠ p := by
          rintro rfl
          exact Nat.not_dvd_ordCompl hp hn0 (Nat.dvd_of_mem_primeFactors hq)
        have hqn : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr
          ⟨Nat.prime_of_mem_primeFactors hq,
            dvd_trans (Nat.dvd_of_mem_primeFactors hq) (Nat.ordCompl_dvd n p), hn0⟩
        rcases Finset.mem_insert.mp (hnP hqn) with h | h
        · exact absurd h hqp
        · exact h
    have hcop : ∀ j m, m ∈ S → F (p ^ j * m) = F (p ^ j) * F m := by
      intro j m hmS
      simp only [hS, Finset.mem_filter, Finset.mem_Icc] at hmS
      have hm0 : m ≠ 0 := by omega
      have hpm : ¬ p ∣ m := fun h =>
        hpP (hmS.2 (Nat.mem_primeFactors.mpr ⟨hp, h, hm0⟩))
      exact hm _ _ (pow_ne_zero _ hp.ne_zero) hm0
        (Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm))
    have hL0 : 0 ≤ ∑ j ∈ range (N + 1), F (p ^ j) := Finset.sum_nonneg fun j _ => h0 _
    rw [Finset.prod_insert hpP]
    calc ∑ n ∈ (Icc 1 N).filter (fun n => n.primeFactors ⊆ insert p P), F n
        ≤ ∑ n ∈ (range (N + 1) ×ˢ S).image (fun x : ℕ × ℕ => p ^ x.1 * x.2), F n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => h0 n
      _ ≤ ∑ x ∈ range (N + 1) ×ˢ S, F (p ^ x.1 * x.2) :=
          Finset.sum_image_le_of_nonneg fun n _ => h0 n
      _ = ∑ x ∈ range (N + 1) ×ˢ S, F (p ^ x.1) * F x.2 :=
          Finset.sum_congr rfl fun x hx => hcop x.1 x.2 (Finset.mem_product.mp hx).2
      _ = (∑ j ∈ range (N + 1), F (p ^ j)) * ∑ m ∈ S, F m := by
          rw [Finset.sum_product, Finset.sum_mul_sum]
      _ ≤ (∑ j ∈ range (N + 1), F (p ^ j)) * ∏ q ∈ P, ∑ j ∈ range (N + 1), F (q ^ j) :=
          mul_le_mul_of_nonneg_left ih' hL0

/-- **The finite Euler product**: `∑_{n ≤ N} F(n) ≤ ∏_{p ≤ N} ∑_{j ≤ N} F(p^j)`. -/
theorem euler_le (F : ℕ → ℝ) (h0 : ∀ n, 0 ≤ F n) (h1 : F 1 = 1)
    (hm : ∀ m n, m ≠ 0 → n ≠ 0 → Nat.Coprime m n → F (m * n) = F m * F n) (N : ℕ) :
    ∑ n ∈ Icc 1 N, F n ≤
      ∏ p ∈ (range (N + 1)).filter Nat.Prime, ∑ j ∈ range (N + 1), F (p ^ j) := by
  have h := euler_key F h0 h1 hm N ((range (N + 1)).filter Nat.Prime)
    (fun p hp => (Finset.mem_filter.mp hp).2)
  have e : (Icc 1 N).filter (fun n => n.primeFactors ⊆ (range (N + 1)).filter Nat.Prime) =
      Icc 1 N := by
    refine Finset.filter_true_of_mem fun n hn q hq => ?_
    have hn' := Finset.mem_Icc.mp hn
    have hq' := Nat.le_of_mem_primeFactors hq
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.prime_of_mem_primeFactors hq⟩
  rwa [e] at h

/-! ## (2) Domination through prime powers -/

/-- **`f ≤ g` from prime powers** for multiplicative `f ≥ 0` and `g`. -/
theorem mult_le (f g : ArithmeticFunction ℝ) (hf : f.IsMultiplicative)
    (hg : g.IsMultiplicative) (hf0 : ∀ n, 0 ≤ f n)
    (hpp : ∀ p k : ℕ, p.Prime → 1 ≤ k → f (p ^ k) ≤ g (p ^ k)) (n : ℕ) : f n ≤ g n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization f hf hn,
    ArithmeticFunction.IsMultiplicative.multiplicative_factorization g hg hn]
  unfold Finsupp.prod
  refine Finset.prod_le_prod (fun p _ => hf0 _) fun p hp => ?_
  rw [Nat.support_factorization] at hp
  exact hpp p _ (Nat.prime_of_mem_primeFactors hp)
    (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization])))

/-! ## (3) The odd tail `∑ n^{-3/2}` -/

/-- `1/(n√n) ≤ 1/√(n−2) − 1/√n` for `n ≥ 3`. -/
theorem inv_sqrt_step (n : ℝ) (hn : 3 ≤ n) :
    1 / (n * Real.sqrt n) ≤ 1 / Real.sqrt (n - 2) - 1 / Real.sqrt n := by
  have ha := Real.sqrt_pos.2 (show (0 : ℝ) < n - 2 by linarith)
  have hb := Real.sqrt_pos.2 (show (0 : ℝ) < n by linarith)
  have ha2 := Real.sq_sqrt (show (0 : ℝ) ≤ n - 2 by linarith)
  have hb2 := Real.sq_sqrt (show (0 : ℝ) ≤ n by linarith)
  have hab : Real.sqrt (n - 2) ≤ Real.sqrt n := Real.sqrt_le_sqrt (by linarith)
  set a := Real.sqrt (n - 2)
  set b := Real.sqrt n
  have hn' : n = b ^ 2 := hb2.symm
  rw [hn', div_sub_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have hba : b - a = 2 / (a + b) := by
    rw [eq_div_iff (by positivity)]
    nlinarith
  have key : 1 * (a * b) ≤ (1 * b - a * 1) * (b ^ 2 * b) := by
    have : (1 * b - a * 1) * (b ^ 2 * b) = 2 * b ^ 3 / (a + b) := by
      rw [show 1 * b - a * 1 = b - a by ring, hba]
      field_simp
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hab ha.le, mul_le_mul_of_nonneg_left hab hb.le]
  linarith

/-- **`∑_{i < J} 1/((M+2i)√(M+2i)) ≤ 1/√(M−2)`** for `M ≥ 3`. -/
theorem odd_tail (M J : ℕ) (hM : 3 ≤ M) :
    ∑ i ∈ range J, 1 / (((M : ℝ) + 2 * i) * Real.sqrt ((M : ℝ) + 2 * i)) ≤
      1 / Real.sqrt ((M : ℝ) - 2) := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  set g : ℕ → ℝ := fun i => 1 / Real.sqrt ((M : ℝ) + 2 * i - 2) with hg
  have h1 : ∀ i ∈ range J, 1 / (((M : ℝ) + 2 * i) * Real.sqrt ((M : ℝ) + 2 * i)) ≤
      g i - g (i + 1) := by
    intro i _
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have h := inv_sqrt_step ((M : ℝ) + 2 * i) (by linarith)
    simp only [hg]
    push_cast
    have e : (M : ℝ) + 2 * (i + 1) - 2 = (M : ℝ) + 2 * i := by ring
    rw [e]
    exact h
  have h2 := Finset.sum_le_sum h1
  rw [Finset.sum_range_sub'] at h2
  have hgJ : 0 ≤ g J := by simp only [hg]; positivity
  have hg0 : g 0 = 1 / Real.sqrt ((M : ℝ) - 2) := by simp [hg]
  linarith

/-- `e^t ≤ 1/(1 − t)` for `t < 1`. -/
theorem exp_le_inv (t : ℝ) (ht : t < 1) : Real.exp t ≤ 1 / (1 - t) := by
  have h := Real.add_one_le_exp (-t)
  have hpos := Real.exp_pos (-t)
  rw [le_div_iff₀ (by linarith)]
  have e : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos t]

/-! ## (4) Products over primes -/

/-- **`∏_{p ∈ P, p ≠ 2}(1 + x_p)` from explicit small primes and an `n^{-3/2}` tail.** -/
theorem prod_primes_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x u : ℕ → ℝ) (L : Finset ℕ)
    (M : ℕ) (hM : 3 ≤ M) (hMo : M % 2 = 1) (C : ℝ)
    (hx0 : ∀ p ∈ P, 0 ≤ x p)
    (hL : ∀ p ∈ P, p ≠ 2 → p < M → p ∈ L)
    (hu : ∀ p ∈ L, 0 ≤ u p)
    (hxu : ∀ p ∈ P, p ≠ 2 → p < M → x p ≤ u p)
    (hC : ∀ p ∈ P, M ≤ p → x p ≤ C / ((p : ℝ) * Real.sqrt p))
    (hC0 : 0 ≤ C) (ht : C / Real.sqrt ((M : ℝ) - 2) < 1) :
    ∏ p ∈ P.filter (· ≠ 2), (1 + x p) ≤
      (∏ p ∈ L, (1 + u p)) / (1 - C / Real.sqrt ((M : ℝ) - 2)) := by
  set T := C / Real.sqrt ((M : ℝ) - 2) with hT
  set A := (P.filter (· ≠ 2)).filter (· < M) with hA
  set B := (P.filter (· ≠ 2)).filter (fun p => ¬ p < M) with hB
  rw [← Finset.prod_filter_mul_prod_filter_not (P.filter (· ≠ 2)) (· < M)]
  have hAL : ∏ p ∈ A, (1 + x p) ≤ ∏ p ∈ L, (1 + u p) := by
    have hsub : A ⊆ L := fun p hp => by
      simp only [hA, Finset.mem_filter] at hp
      exact hL p hp.1.1 hp.1.2 hp.2
    calc ∏ p ∈ A, (1 + x p) ≤ ∏ p ∈ A, (1 + u p) := by
          refine Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_
          · simp only [hA, Finset.mem_filter] at hp
            linarith [hx0 p hp.1.1]
          · simp only [hA, Finset.mem_filter] at hp
            linarith [hxu p hp.1.1 hp.1.2 hp.2]
      _ ≤ ∏ p ∈ L, (1 + u p) :=
          Finset.prod_le_prod_of_subset_of_one_le hsub
            (fun p hp => by linarith [hu p (hsub hp)]) fun p hp _ => by linarith [hu p hp]
  have hB1 : ∏ p ∈ B, (1 + x p) ≤ Real.exp (∑ p ∈ B, x p) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) fun p _ => ?_
    · simp only [hB, Finset.mem_filter] at hp
      linarith [hx0 p hp.1.1]
    · linarith [Real.add_one_le_exp (x p)]
  have hBsum : ∑ p ∈ B, x p ≤ T := by
    have hstep : ∑ p ∈ B, x p ≤ ∑ p ∈ B, C / ((p : ℝ) * Real.sqrt p) :=
      Finset.sum_le_sum fun p hp => by
        simp only [hB, Finset.mem_filter, not_lt] at hp
        exact hC p hp.1.1 hp.2
    set J := B.sup id + 1 with hJ
    have hsub : B ⊆ (range J).image (fun i => M + 2 * i) := by
      intro p hp
      have hp' := hp
      simp only [hB, Finset.mem_filter, not_lt] at hp'
      obtain ⟨⟨hpP, hp2⟩, hpM⟩ := hp'
      have hodd : p % 2 = 1 := by
        rcases (hP p hpP).eq_two_or_odd with h | h
        · exact absurd h hp2
        · exact h
      have hle : p ≤ B.sup id := Finset.le_sup (f := id) hp
      rw [Finset.mem_image]
      refine ⟨(p - M) / 2, Finset.mem_range.mpr (by omega), by omega⟩
    have hinj : Set.InjOn (fun i => M + 2 * i) (range J : Set ℕ) := by
      intro i _ j _ h
      simp only at h
      omega
    calc ∑ p ∈ B, x p ≤ ∑ p ∈ B, C / ((p : ℝ) * Real.sqrt p) := hstep
      _ ≤ ∑ p ∈ (range J).image (fun i => M + 2 * i), C / ((p : ℝ) * Real.sqrt p) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
      _ = ∑ i ∈ range J, C / (((M + 2 * i : ℕ) : ℝ) * Real.sqrt ((M + 2 * i : ℕ) : ℝ)) :=
          Finset.sum_image hinj
      _ = C * ∑ i ∈ range J, 1 / (((M : ℝ) + 2 * i) * Real.sqrt ((M : ℝ) + 2 * i)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          push_cast
          ring
      _ ≤ C * (1 / Real.sqrt ((M : ℝ) - 2)) :=
          mul_le_mul_of_nonneg_left (odd_tail M J hM) hC0
      _ = T := by rw [hT]; ring
  have hB2 : ∏ p ∈ B, (1 + x p) ≤ 1 / (1 - T) :=
    hB1.trans ((Real.exp_le_exp.mpr hBsum).trans (exp_le_inv T ht))
  have hA0 : 0 ≤ ∏ p ∈ A, (1 + x p) := Finset.prod_nonneg fun p hp => by
    simp only [hA, Finset.mem_filter] at hp
    linarith [hx0 p hp.1.1]
  have hL0 : 0 ≤ ∏ p ∈ L, (1 + u p) := Finset.prod_nonneg fun p hp => by linarith [hu p hp]
  calc (∏ p ∈ A, (1 + x p)) * ∏ p ∈ B, (1 + x p)
      ≤ (∏ p ∈ L, (1 + u p)) * (1 / (1 - T)) := mul_le_mul hAL hB2
        (Finset.prod_nonneg fun p hp => by
          simp only [hB, Finset.mem_filter] at hp
          linarith [hx0 p hp.1.1]) hL0
    _ = (∏ p ∈ L, (1 + u p)) / (1 - T) := by ring

end Principia.Common.TernaryGoldbach.M2YE
