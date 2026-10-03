/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.LucaPomerance.MertensAP
import Principia.Common.LucaPomerance.Lemma21Algebra
import Principia.Common.HalberstamRichertPollack

set_option autoImplicit false

/-!
# `ω_p(n)` is rarely small, uniformly in `p ≤ log log N`

`ω_p(n) = #{q prime : q ∥ n, p ∣ q + 1}` (`Lemma21Algebra.omegaP`).

* `omegaP_mul`, `omegaP_prime`: `ω_p` is additive on coprime arguments, and `ω_p(q) = [p ∣ q+1]`.
* `card_omegaP_le_exp` (Pollack's mean-value bound applied to the multiplicative
  `n ↦ z^{ω_p(n)}`, `0 < z ≤ 1`): `#{n ≤ N : ω_p(n) ≤ j} ≤ C N e^{−(1−z) S_p(N)} / z^j`, where
  `S_p(N) = ∑_{q ≤ N prime, p ∣ q+1} 1/q` (`Sp`).
* `Sp_lower`: **the sharp constant** — `S_p(N) ≥ log log N/(p−1) − K` for every prime
  `p ≤ log log N`, from `mertens_AP_primes` at `B = 1` (class `−1 mod p`, cut `T = max(T₀, e^p)`).
-/

namespace Principia.Common.LucaPomerance.LP21

open Finset Real ArithmeticFunction Filter

theorem omegaP_one (p : ℕ) : omegaP p 1 = 0 := by simp [omegaP]

theorem omegaP_zero (p : ℕ) : omegaP p 0 = 0 := by simp [omegaP]

theorem omegaP_prime (p : ℕ) {q : ℕ} (hq : q.Prime) :
    omegaP p q = if p ∣ q + 1 then 1 else 0 := by
  unfold omegaP
  rw [hq.primeFactors, Finset.filter_singleton]
  by_cases h : p ∣ q + 1
  · simp [h, hq.factorization_self]
  · simp [h]

theorem omegaP_mul (p : ℕ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) :
    omegaP p (m * n) = omegaP p m + omegaP p n := by
  classical
  unfold omegaP
  have hdisj := Nat.Coprime.disjoint_primeFactors hmn
  rw [Nat.primeFactors_mul hm hn, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
  congr 1
  · refine congrArg Finset.card (Finset.filter_congr fun q hq => ?_)
    have hzn : n.factorization q = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
      exact Finset.disjoint_left.mp hdisj hq
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply, hzn, add_zero]
  · refine congrArg Finset.card (Finset.filter_congr fun q hq => ?_)
    have hzm : m.factorization q = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
      exact Finset.disjoint_right.mp hdisj hq
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply, hzm, zero_add]

/-- `S_p(N) = ∑_{q ≤ N prime, p ∣ q+1} 1/q`. -/
noncomputable def Sp (p N : ℕ) : ℝ :=
  ∑ q ∈ (Nat.primesLE N).filter (fun q => p ∣ q + 1), (1 : ℝ) / q

theorem Sp_nonneg (p N : ℕ) : 0 ≤ Sp p N := by
  unfold Sp
  exact Finset.sum_nonneg fun q _ => by positivity

theorem exponent_eq (p N : ℕ) (z : ℝ) :
    ∑ q ∈ Nat.primesLE N, (z ^ omegaP p q - 1) / (q : ℝ) = -(1 - z) * Sp p N := by
  classical
  unfold Sp
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [omegaP_prime p (Nat.prime_of_mem_primesLE hq)]
  split_ifs <;> ring

/-- **Pollack's bound for `z^{ω_p}`.** -/
theorem pollack_omegaP :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (z : ℝ), 0 ≤ z → z ≤ 1 → ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Finset.Icc 1 N, z ^ omegaP p n ≤ C * N * Real.exp (-(1 - z) * Sp p N) := by
  obtain ⟨C, hC, hpol⟩ := Principia.Common.HalberstamRichert.pollack_mean_value_nat
  refine ⟨C, hC, fun p z hz0 hz1 N hN => ?_⟩
  have h := hpol (fun n => z ^ omegaP p n) (by simp [omegaP_one]) ?_ ?_ N hN
  · rw [exponent_eq] at h
    exact h
  · intro m n hmn
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have hn1 : n = 1 := Nat.coprime_zero_left n |>.mp hmn
      subst hn1
      simp [omegaP_one]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hm1 : m = 1 := Nat.coprime_zero_right m |>.mp hmn
      subst hm1
      simp [omegaP_one]
    rw [omegaP_mul p hm.ne' hn.ne' hmn, pow_add]
  · intro q k _ _
    exact ⟨pow_nonneg hz0 _, pow_le_one₀ hz0 hz1⟩

/-- `#{n ≤ N : ω_p(n) ≤ j} ≤ C N e^{−(1−z) S_p(N)} / z^j` for `0 < z ≤ 1`. -/
theorem card_omegaP_le_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (z : ℝ), 0 < z → z ≤ 1 → ∀ j N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter (fun n => omegaP p n ≤ j)).card : ℝ) ≤
        C * N * Real.exp (-(1 - z) * Sp p N) / z ^ j := by
  obtain ⟨C, hC, hpol⟩ := pollack_omegaP
  refine ⟨C, hC, fun p z hz0 hz1 j N hN => ?_⟩
  have hzj : 0 < z ^ j := pow_pos hz0 j
  rw [le_div_iff₀ hzj]
  have h1 : (((Finset.Icc 1 N).filter (fun n => omegaP p n ≤ j)).card : ℝ) * z ^ j =
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => omegaP p n ≤ j), z ^ j := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => omegaP p n ≤ j), z ^ j ≤
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => omegaP p n ≤ j), z ^ omegaP p n := by
    refine Finset.sum_le_sum fun n hn => ?_
    exact pow_le_pow_of_le_one hz0.le hz1 (Finset.mem_filter.mp hn).2
  have h3 : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => omegaP p n ≤ j), z ^ omegaP p n ≤
      ∑ n ∈ Finset.Icc 1 N, z ^ omegaP p n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => pow_nonneg hz0.le _)
  linarith [hpol p z hz0.le hz1 N hN]

/-- For a prime `q` and a prime `p`: `(−1 : ZMod p) = q ↔ p ∣ q + 1`. -/
theorem neg_one_eq_cast_iff (p q : ℕ) : (-1 : ZMod p) = (q : ZMod p) ↔ p ∣ q + 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, eq_comm, ← sub_eq_zero,
    sub_neg_eq_add]

/-- **`S_p(N) ≥ log log N/(p−1) − K`, uniformly in primes `p ≤ log log N`.** -/
theorem Sp_lower :
    ∃ K : ℝ, 0 < K ∧ ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ p : ℕ, p.Prime →
      (p : ℝ) ≤ Real.log (Real.log N) → Real.log (Real.log N) / ((p : ℝ) - 1) - K ≤ Sp p N := by
  obtain ⟨K, hK, T₀, hT₀3, hmap⟩ := mertens_AP_primes 1 le_rfl
  refine ⟨|Real.log (Real.log T₀)| + 2 * K + 2, by positivity, T₀, ?_⟩
  intro N hN p hp hpL
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hN3 : 3 ≤ N := le_trans hT₀3 hN
  have hN0 : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  have hlogN : 1 ≤ Real.log N := one_le_log_of_three_le hN3
  -- the cut `T`
  set T := max T₀ ⌈Real.exp p⌉₊ with hTdef
  have hT₀T : T₀ ≤ T := le_max_left _ _
  have hT3 : 3 ≤ T := le_trans hT₀3 hT₀T
  have hexpN : Real.exp p ≤ N := by
    calc Real.exp p ≤ Real.exp (Real.log (Real.log N)) := Real.exp_le_exp.mpr hpL
      _ = Real.log N := Real.exp_log (by linarith)
      _ ≤ N := by
          have := Real.log_le_sub_one_of_pos hN0
          linarith
  have hTN : T ≤ N := max_le hN (Nat.ceil_le.mpr hexpN)
  have hpT : (p : ℝ) ≤ Real.log T ^ 1 := by
    rw [pow_one]
    have hceil : Real.exp p ≤ (T : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right T₀ ⌈Real.exp p⌉₊)
    calc (p : ℝ) = Real.log (Real.exp p) := (Real.log_exp _).symm
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos _) hceil
  have hunit : IsUnit (-1 : ZMod p) := isUnit_one.neg
  have h := (hmap p (-1 : ZMod p) hunit T N hT₀T hTN hpT).2
  -- the AP prime sum is part of `S_p(N)`
  have hsub : ∑ q ∈ (Finset.Ioc T N).filter (fun q : ℕ => q.Prime ∧ (-1 : ZMod p) = ((q : ZMod p))),
      (1 : ℝ) / q ≤ Sp p N := by
    unfold Sp
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_Ioc] at hq
      rw [Finset.mem_filter, Nat.mem_primesLE]
      exact ⟨⟨hq.1.2, hq.2.1⟩, (neg_one_eq_cast_iff p q).mp hq.2.2⟩
    · intro q _ _
      positivity
  -- `φ(p) = p − 1`
  have hφ : ((p.totient : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  rw [hφ] at h
  have hp1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  -- `log log T ≤ |log log T₀| + log (p + 1)`
  have hlogp1 : 0 ≤ Real.log ((p : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hLT : Real.log (Real.log T) ≤ |Real.log (Real.log T₀)| + Real.log ((p : ℝ) + 1) := by
    rcases le_total T₀ ⌈Real.exp p⌉₊ with hle | hle
    · have hT : T = ⌈Real.exp p⌉₊ := max_eq_right hle
      have hTup : (T : ℝ) ≤ Real.exp ((p : ℝ) + 1) := by
        rw [hT]
        have h1 := (Nat.ceil_lt_add_one (Real.exp_pos (p : ℝ)).le).le
        have h2 : Real.exp (p : ℝ) + 1 ≤ Real.exp ((p : ℝ) + 1) := by
          rw [Real.exp_add]
          have he : (2 : ℝ) ≤ Real.exp 1 := by
            have := Real.add_one_le_exp (1 : ℝ)
            linarith
          have hep : (1 : ℝ) ≤ Real.exp p := Real.one_le_exp (by positivity)
          nlinarith
        linarith
      have hT0 : (0 : ℝ) < T := by
        have : (3 : ℝ) ≤ T := by exact_mod_cast hT3
        linarith
      have hlogT : 1 ≤ Real.log T := one_le_log_of_three_le hT3
      have h3 : Real.log T ≤ (p : ℝ) + 1 := by
        calc Real.log T ≤ Real.log (Real.exp ((p : ℝ) + 1)) := Real.log_le_log hT0 hTup
          _ = (p : ℝ) + 1 := Real.log_exp _
      have h4 : Real.log (Real.log T) ≤ Real.log ((p : ℝ) + 1) :=
        Real.log_le_log (by linarith) h3
      have := abs_nonneg (Real.log (Real.log T₀))
      linarith
    · have hT : T = T₀ := max_eq_left hle
      rw [hT]
      have := le_abs_self (Real.log (Real.log T₀))
      linarith
  have hlogp : Real.log ((p : ℝ) + 1) / ((p : ℝ) - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (p : ℝ) + 1 by positivity)
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hA : (|Real.log (Real.log T₀)| + K) / ((p : ℝ) - 1) ≤ |Real.log (Real.log T₀)| + K :=
    div_le_self (by positivity) hp1
  have hmain : Real.log (Real.log N) / ((p : ℝ) - 1) -
      (|Real.log (Real.log T₀)| + 2 * K + 2) ≤
      (Real.log (Real.log N) - Real.log (Real.log T) - K) / ((p : ℝ) - 1) - K := by
    have e : (Real.log (Real.log N) - Real.log (Real.log T) - K) / ((p : ℝ) - 1) =
        Real.log (Real.log N) / ((p : ℝ) - 1) - Real.log (Real.log T) / ((p : ℝ) - 1) -
          K / ((p : ℝ) - 1) := by ring
    have h5 : Real.log (Real.log T) / ((p : ℝ) - 1) + K / ((p : ℝ) - 1) ≤
        (|Real.log (Real.log T₀)| + K) / ((p : ℝ) - 1) +
          Real.log ((p : ℝ) + 1) / ((p : ℝ) - 1) := by
      rw [← add_div, ← add_div]
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    rw [e]
    linarith
  linarith

end Principia.Common.LucaPomerance.LP21
