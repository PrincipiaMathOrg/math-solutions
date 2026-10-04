/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIYuttoKSum

set_option autoImplicit false

/-!
# `M2Y.DSumH` and `M2Y.DSumQ` PROVED — the `d`-sums

*`DSumQ`*: the summand `f(d) = 1_{d odd}μ²(d)√d/σ(d)²∏_{p|d}ρ_Q(p)²` is multiplicative,
supported on odd squarefree `d`, so `M2YE.euler_le` gives
`∑_{d ≤ N} f(d) ≤ ∏_{3 ≤ p ≤ N}(1 + f(p))`, `f(p) = √p·ρ_Q(p)²/(p+1)²`; small primes explicitly and the tail `f(p) ≤ 1.08/(p√p)`:
`≤ 1.6923/(1 − 0.1086) ≤ 1.899 ≤ 2.4`.

*`DSumH`*: the summand `H(d) = 1_{d odd}μ²(d)·d/σ(d)²·∏ρ_H(p)²` has `H(p) = h_p/p`,
`h_p = (pρ_H(p)/(p+1))² ≥ 1`. With `E(e) = 1_{e odd}μ²(e)/e·∏_{p|e}(h_p − 1)` and
`Z(b) = 1_{b odd}μ²(b)/b`, `H ≤ E ⋆ Z` (`M2YE.mult_le`: equality at odd primes, `H = 0` at higher
powers and at `2`), so `∑_{d ≤ N} H ≤ (∑_{e ≤ N} E)(∑_{b ≤ N} 1/b) ≤ 2.74·(1 + log N)`
(`E`'s Euler product: `2.0590/(1 − 0.2483)`; harmonic bound from Mathlib) `≤ 8 + 4 log x`.

```
 dSumQ : M2Y.DSumQ                                                              PROVED
 dSumH : M2Y.DSumH                                                              PROVED
```
-/

namespace Principia.Common.TernaryGoldbach.M2YD

open Finset ArithmeticFunction

/-! ## (1) Multiplicativity helpers -/

theorem mu_sq_mul (m n : ℕ) (h : Nat.Coprime m n) :
    M2Y.mu (m * n) ^ 2 = M2Y.mu m ^ 2 * M2Y.mu n ^ 2 := by
  rw [M2YC.mu_mul m n h]
  ring

theorem pf_mul (φ : ℕ → ℝ) (m n : ℕ) (h : Nat.Coprime m n) :
    ∏ p ∈ (m * n).primeFactors, φ p = (∏ p ∈ m.primeFactors, φ p) * ∏ p ∈ n.primeFactors, φ p := by
  rw [Nat.Coprime.primeFactors_mul h, Finset.prod_union h.disjoint_primeFactors]

theorem ite_mul (g : ℕ → ℝ) (m n : ℕ) (hg : g (m * n) = g m * g n) :
    (if Nat.Coprime (m * n) 2 then g (m * n) else 0) =
      (if Nat.Coprime m 2 then g m else 0) * (if Nat.Coprime n 2 then g n else 0) := by
  by_cases h1 : Nat.Coprime m 2 <;> by_cases h2 : Nat.Coprime n 2
  · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨h1, h2⟩), if_pos h1, if_pos h2, hg]
  · rw [if_neg (fun h => h2 (Nat.coprime_mul_iff_left.mp h).2), if_neg h2, mul_zero]
  · rw [if_neg (fun h => h1 (Nat.coprime_mul_iff_left.mp h).1), if_neg h1, zero_mul]
  · rw [if_neg (fun h => h1 (Nat.coprime_mul_iff_left.mp h).1), if_neg h1, zero_mul]

theorem sg_prime (p : ℕ) (hp : p.Prime) : M2Y.sg p = (p : ℝ) + 1 := by
  unfold M2Y.sg
  have h := sigma_one_apply_prime_pow (i := 1) hp
  rw [pow_one] at h
  rw [h]
  simp [Finset.sum_range_succ]
  ring

theorem mu_sq_prime (p : ℕ) (hp : p.Prime) : M2Y.mu p ^ 2 = 1 := by
  unfold M2Y.mu
  rw [moebius_apply_prime hp]
  norm_num

theorem mu_pow_zero (p j : ℕ) (hp : p.Prime) (hj : 2 ≤ j) : M2Y.mu (p ^ j) = 0 := by
  unfold M2Y.mu
  rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
  simp

theorem odd_of_prime (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) : Nat.Coprime p 2 :=
  (Nat.coprime_primes hp Nat.prime_two).mpr h2

/-- **Local factor for a function vanishing at `p^j`, `j ≥ 2`.** -/
theorem loc2 (F : ℕ → ℝ) (p N : ℕ) (h1 : F 1 = 1) (hz : ∀ j, 2 ≤ j → F (p ^ j) = 0)
    (hp0 : 0 ≤ F p) : ∑ j ∈ range (N + 1), F (p ^ j) ≤ 1 + F p := by
  rcases N with _ | M
  · simp [h1, hp0]
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hz' : ∑ j ∈ range M, F (p ^ (j + 1 + 1)) = 0 :=
      Finset.sum_eq_zero fun j _ => hz _ (by omega)
    rw [hz']
    simp only [zero_add, pow_one, pow_zero, h1]
    linarith

/-- **`∏_{p ≤ N}(1 + F(p))` with `F(2) = 0` is the odd product.** -/
theorem prod_drop_two (F : ℕ → ℝ) (P : Finset ℕ) (h2 : F 2 = 0) :
    ∏ p ∈ P, (1 + F p) = ∏ p ∈ P.filter (· ≠ 2), (1 + F p) := by
  rw [← Finset.prod_filter_mul_prod_filter_not P (· ≠ 2)]
  have e : ∏ p ∈ P.filter (fun p => ¬ p ≠ 2), (1 + F p) = 1 :=
    Finset.prod_eq_one fun p hp => by
      have : p = 2 := not_not.mp (Finset.mem_filter.mp hp).2
      rw [this, h2, add_zero]
  rw [e, mul_one]

/-- `ρ(p, q) = (p+1)/((p+1)(1 − q) + q)` is monotone in `q ∈ [0, 1)`. -/
theorem rho_mono (p : ℕ) (q1 q2 : ℝ) (h12 : q1 ≤ q2) (h2 : q2 < 1) :
    M2YK.rho p q1 ≤ M2YK.rho p q2 := by
  unfold M2YK.rho
  have hp := Nat.cast_nonneg (α := ℝ) p
  have hd1 : 0 < ((p : ℝ) + 1) * (1 - q1) + q1 := by nlinarith
  have hd2 : 0 < ((p : ℝ) + 1) * (1 - q2) + q2 := by nlinarith
  have hD : ((p : ℝ) + 1) * (1 - q2) + q2 ≤ ((p : ℝ) + 1) * (1 - q1) + q1 := by
    nlinarith [mul_le_mul_of_nonneg_left h12 hp]
  rw [div_le_div_iff₀ hd1 hd2]
  nlinarith [mul_le_mul_of_nonneg_left hD (show (0 : ℝ) ≤ (p : ℝ) + 1 by positivity)]

theorem rho_nonneg (p : ℕ) (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) : 0 ≤ M2YK.rho p q :=
  le_trans zero_le_one (M2YK.rho_ge_one p q h0 h1)

/-! ## (2) `DSumQ` -/

/-- The `DSumQ` summand without the parity indicator. -/
noncomputable def gQ (d : ℕ) : ℝ :=
  M2Y.mu d ^ 2 * Real.sqrt d / M2Y.sg d ^ 2 * ∏ p ∈ d.primeFactors, M2Y.rhoQ p ^ 2

theorem gQ_mul (m n : ℕ) (h : Nat.Coprime m n) : gQ (m * n) = gQ m * gQ n := by
  unfold gQ
  rw [mu_sq_mul m n h, M2YC.sg_mul m n h, pf_mul _ m n h, M2YK.sqrt_w_mul]
  ring

theorem gQ_nonneg (d : ℕ) : 0 ≤ gQ d := by
  unfold gQ
  have : 0 ≤ ∏ p ∈ d.primeFactors, M2Y.rhoQ p ^ 2 := Finset.prod_nonneg fun p _ => sq_nonneg _
  positivity

/-- `ρ_Q(p) = ρ(p, qq p)`. -/
theorem rhoQ_eq (p : ℕ) : M2Y.rhoQ p = M2YK.rho p (M2Y.qq p) := rfl

/-- The tail of `DSumQ`: `√p·ρ_Q(p)²/(p+1)² ≤ 1.08/(p√p)` for `p ≥ 101`. -/
theorem tailQ (p : ℕ) (hM : 101 ≤ p) :
    Real.sqrt p * M2YK.rho p (M2Y.qq p) ^ 2 / ((p : ℝ) + 1) ^ 2 ≤
      1.08 / ((p : ℝ) * Real.sqrt p) := by
  have hp0 : (101 : ℝ) ≤ p := by exact_mod_cast hM
  have hsq : 10 ≤ Real.sqrt (p : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
  have hrt : 3 ≤ Real.sqrt (Real.sqrt (p : ℝ)) := Real.le_sqrt_of_sq_le (by linarith)
  have hq1 : M2Y.qq p ≤ 1 / 30 := by
    unfold M2Y.qq
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hq0 : 0 ≤ M2Y.qq p := by unfold M2Y.qq; positivity
  have hrho : M2YK.rho p (M2Y.qq p) / ((p : ℝ) + 1) ≤ 1 / ((p : ℝ) * (29 / 30)) := by
    unfold M2YK.rho
    have hD : (p : ℝ) * (29 / 30) ≤ ((p : ℝ) + 1) * (1 - M2Y.qq p) + M2Y.qq p := by nlinarith
    rw [div_div, div_le_div_iff₀ (mul_pos (by nlinarith) (by positivity)) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hD (show (0 : ℝ) ≤ (p : ℝ) + 1 by positivity)]
  have hr0 : 0 ≤ M2YK.rho p (M2Y.qq p) / ((p : ℝ) + 1) :=
    div_nonneg (rho_nonneg p _ hq0 (by linarith)) (by positivity)
  have e : Real.sqrt p * M2YK.rho p (M2Y.qq p) ^ 2 / ((p : ℝ) + 1) ^ 2 =
      Real.sqrt p * (M2YK.rho p (M2Y.qq p) / ((p : ℝ) + 1)) ^ 2 := by rw [div_pow]; ring
  rw [e]
  have h2 : (M2YK.rho p (M2Y.qq p) / ((p : ℝ) + 1)) ^ 2 ≤ (1 / ((p : ℝ) * (29 / 30))) ^ 2 :=
    pow_le_pow_left₀ hr0 hrho 2
  set a := Real.sqrt (p : ℝ) with ha
  have haa : a * a = p := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have ha0 : 0 < a := by linarith
  calc a * (M2YK.rho p (M2Y.qq p) / ((p : ℝ) + 1)) ^ 2
      ≤ a * (1 / ((p : ℝ) * (29 / 30))) ^ 2 := mul_le_mul_of_nonneg_left h2 ha0.le
    _ ≤ 1.08 / ((p : ℝ) * a) := by
      rw [← haa]
      field_simp
      nlinarith

/-- Small primes of `DSumQ`: `√p·ρ_Q(p)²/(p+1)² ≤ ⌈1000√p⌉/1000·ρ(p, q̄)²/(p+1)²`. -/
theorem smallQ (p : ℕ) (hm : p ∈ M2YK.smallP) :
    Real.sqrt p * M2YK.rho p (M2Y.qq p) ^ 2 / ((p : ℝ) + 1) ^ 2 ≤
      ((Nat.sqrt (p * 1000000) + 1 : ℕ) : ℝ) / 1000 *
        M2YK.rho p (1 / (M2YK.sL p * M2YK.tL p)) ^ 2 / ((p : ℝ) + 1) ^ 2 := by
  have hs1 : 1 < M2YK.sL p * M2YK.tL p := by
    simp only [M2YK.smallP, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [M2YK.sL, M2YK.tL]
      norm_num
  have hq0 : 0 ≤ M2Y.qq p := by unfold M2Y.qq; positivity
  have hqb' : M2Y.qq p ≤ 1 / (M2YK.sL p * M2YK.tL p) := by
    unfold M2Y.qq
    have ht0 : 0 ≤ M2YK.tL p := by unfold M2YK.tL; positivity
    exact one_div_le_one_div_of_le (by linarith)
      (mul_le_mul (M2YK.sL_le p) (M2YK.tL_le p) ht0 (Real.sqrt_nonneg _))
  have hqb1 : 1 / (M2YK.sL p * M2YK.tL p) < 1 := by
    rw [div_lt_one (by linarith)]
    exact hs1
  have hr := rho_mono p _ _ hqb' hqb1
  have hr0 := rho_nonneg p _ hq0 (lt_of_le_of_lt hqb' hqb1)
  have hsU : Real.sqrt (p : ℝ) ≤ ((Nat.sqrt (p * 1000000) + 1 : ℕ) : ℝ) / 1000 := by
    rw [Real.sqrt_le_left (by positivity)]
    have h := Nat.lt_succ_sqrt' (p * 1000000)
    have h' : ((p * 1000000 : ℕ) : ℝ) < ((Nat.sqrt (p * 1000000) + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast h
    push_cast at h' ⊢
    nlinarith
  have hp1 : (0 : ℝ) < ((p : ℝ) + 1) ^ 2 := by positivity
  rw [div_le_div_iff_of_pos_right hp1]
  exact mul_le_mul hsU (pow_le_pow_left₀ hr0 hr 2) (sq_nonneg _) (by positivity)

/-- **`M2Y.DSumQ`, PROVED.** -/
theorem dSumQ : M2Y.DSumQ := by
  intro N
  set F : ℕ → ℝ := fun d => if Nat.Coprime d 2 then gQ d else 0 with hF
  have hF0 : ∀ n, 0 ≤ F n := fun n => by
    simp only [hF]
    split_ifs
    · exact gQ_nonneg n
    · exact le_rfl
  have hF1 : F 1 = 1 := by simp [hF, gQ, M2Y.mu, M2Y.sg]
  have hFm : ∀ m n, m ≠ 0 → n ≠ 0 → Nat.Coprime m n → F (m * n) = F m * F n :=
    fun m n _ _ h => ite_mul gQ m n (gQ_mul m n h)
  have h1 := M2YE.euler_le F hF0 hF1 hFm N
  set P := (range (N + 1)).filter Nat.Prime with hP
  have hloc : ∀ p ∈ P, ∑ j ∈ range (N + 1), F (p ^ j) ≤ 1 + F p := fun p hp =>
    loc2 F p N hF1 (fun j hj => by
      simp only [hF]
      split_ifs
      · unfold gQ
        rw [mu_pow_zero p j (Finset.mem_filter.mp hp).2 hj]
        simp
      · rfl) (hF0 p)
  have h2 := Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun j _ => hF0 _) hloc
  have hF2 : F 2 = 0 := by simp [hF]
  rw [prod_drop_two F P hF2] at h2
  have hFp : ∀ p, p.Prime → p ≠ 2 →
      F p = Real.sqrt p * M2YK.rho p (M2Y.qq p) ^ 2 / ((p : ℝ) + 1) ^ 2 := fun p hp h2 => by
    simp only [hF, if_pos (odd_of_prime p hp h2), gQ, mu_sq_prime p hp, sg_prime p hp,
      Nat.Prime.primeFactors hp, Finset.prod_singleton, rhoQ_eq]
    ring
  have hT : (1.08 : ℝ) / Real.sqrt ((101 : ℕ) - 2 : ℝ) ≤ 0.10856 := by
    have := M2YK.sqrt_99_ge
    norm_num
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hpp := M2YE.prod_primes_le P (fun p hp => (Finset.mem_filter.mp hp).2) F
    (fun p => ((Nat.sqrt (p * 1000000) + 1 : ℕ) : ℝ) / 1000 *
      M2YK.rho p (1 / (M2YK.sL p * M2YK.tL p)) ^ 2 / ((p : ℝ) + 1) ^ 2)
    M2YK.smallP 101 (by norm_num) (by norm_num) 1.08
    (fun p _ => hF0 p)
    (fun p hp h2 h => M2YK.mem_smallP p (Finset.mem_filter.mp hp).2 h2 h)
    (fun p _ => by positivity)
    (fun p hp h2 h => by
      have hpr := (Finset.mem_filter.mp hp).2
      rw [hFp p hpr h2]
      exact smallQ p (M2YK.mem_smallP p hpr h2 h))
    (fun p hp hM => by
      rw [hFp p (Finset.mem_filter.mp hp).2 (by omega)]
      exact tailQ p hM)
    (by norm_num) (by linarith)
  have hsmall : ∏ p ∈ M2YK.smallP, (1 + ((Nat.sqrt (p * 1000000) + 1 : ℕ) : ℝ) / 1000 *
      M2YK.rho p (1 / (M2YK.sL p * M2YK.tL p)) ^ 2 / ((p : ℝ) + 1) ^ 2) ≤ 1.6923 := by
    simp only [M2YK.smallP, M2YK.sL, M2YK.tL, M2YK.rho]
    norm_num [Finset.prod_insert, Finset.prod_singleton]
  have hT0 : 0 ≤ (1.08 : ℝ) / Real.sqrt ((101 : ℕ) - 2 : ℝ) := by positivity
  have h3 : (∏ p ∈ M2YK.smallP, (1 + ((Nat.sqrt (p * 1000000) + 1 : ℕ) : ℝ) / 1000 *
      M2YK.rho p (1 / (M2YK.sL p * M2YK.tL p)) ^ 2 / ((p : ℝ) + 1) ^ 2)) /
      (1 - (1.08 : ℝ) / Real.sqrt ((101 : ℕ) - 2 : ℝ)) ≤ 2.4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hsumF : ∑ d ∈ Icc 1 N, F d = ∑ d ∈ Icc 1 N, (if Nat.Coprime d 2 then
      M2Y.mu d ^ 2 * Real.sqrt d / M2Y.sg d ^ 2 * ∏ p ∈ d.primeFactors, M2Y.rhoQ p ^ 2
      else 0) := rfl
  rw [← hsumF]
  linarith

/-! ## (3) `DSumH` -/

/-- `ε_p = (pρ_H(p)/(p+1))² − 1`. -/
noncomputable def epsH (p : ℕ) : ℝ := ((p : ℝ) * M2Y.rhoH p / ((p : ℝ) + 1)) ^ 2 - 1

/-- The `DSumH` summand without the parity indicator. -/
noncomputable def gH (d : ℕ) : ℝ :=
  M2Y.mu d ^ 2 * (d : ℝ) / M2Y.sg d ^ 2 * ∏ p ∈ d.primeFactors, M2Y.rhoH p ^ 2

/-- `E` without the parity indicator. -/
noncomputable def gE (e : ℕ) : ℝ := M2Y.mu e ^ 2 / (e : ℝ) * ∏ p ∈ e.primeFactors, epsH p

/-- `Z` without the parity indicator. -/
noncomputable def gZ (b : ℕ) : ℝ := M2Y.mu b ^ 2 / (b : ℝ)

theorem gH_mul (m n : ℕ) (h : Nat.Coprime m n) : gH (m * n) = gH m * gH n := by
  unfold gH
  rw [mu_sq_mul m n h, M2YC.sg_mul m n h, pf_mul _ m n h]
  push_cast
  ring

theorem gE_mul (m n : ℕ) (h : Nat.Coprime m n) : gE (m * n) = gE m * gE n := by
  unfold gE
  rw [mu_sq_mul m n h, pf_mul _ m n h]
  push_cast
  ring

theorem gZ_mul (m n : ℕ) (h : Nat.Coprime m n) : gZ (m * n) = gZ m * gZ n := by
  unfold gZ
  rw [mu_sq_mul m n h]
  push_cast
  ring

/-- `ρ_H(p) = ρ(p, 1/√p)`. -/
theorem rhoH_eq (p : ℕ) : M2Y.rhoH p = M2YK.rho p (1 / Real.sqrt p) := rfl

theorem epsH_nonneg (p : ℕ) (hp : 1 ≤ p) : 0 ≤ epsH p := by
  unfold epsH
  rw [rhoH_eq]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hs : 1 ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.mpr hp1
  have hss : Real.sqrt (p : ℝ) * Real.sqrt p = p := Real.mul_self_sqrt (by linarith)
  have hq0 : 0 ≤ 1 / Real.sqrt (p : ℝ) := by positivity
  have hq1 : 1 / Real.sqrt (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hs
  unfold M2YK.rho
  have hD : 0 < ((p : ℝ) + 1) * (1 - 1 / Real.sqrt p) + 1 / Real.sqrt p := by nlinarith
  have hpq : (p : ℝ) * (1 / Real.sqrt p) = Real.sqrt p := by
    field_simp
    linarith
  have hge : 1 ≤ (p : ℝ) * (((p : ℝ) + 1) /
      (((p : ℝ) + 1) * (1 - 1 / Real.sqrt p) + 1 / Real.sqrt p)) / ((p : ℝ) + 1) := by
    rw [mul_div_assoc', div_div, le_div_iff₀ (by positivity)]
    nlinarith
  nlinarith

/-- The convolution of two nonnegative functions is nonnegative. -/
theorem conv_nonneg (f g : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n)
    (n : ℕ) : 0 ≤ (f * g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hf _) (hg _)

/-- The tail of `DSumH`: `ε_p/p ≤ 2.47/(p√p)` for `p ≥ 101`. -/
theorem tailH (p : ℕ) (hM : 101 ≤ p) :
    epsH p / p ≤ 2.47 / ((p : ℝ) * Real.sqrt p) := by
  have hp0 : (101 : ℝ) ≤ p := by exact_mod_cast hM
  have hsq : 10 ≤ Real.sqrt (p : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
  have haa : Real.sqrt (p : ℝ) * Real.sqrt p = p := Real.mul_self_sqrt (Nat.cast_nonneg _)
  set a := Real.sqrt (p : ℝ) with ha
  have ha0 : 0 < a := by linarith
  have hpa : (p : ℝ) = a ^ 2 := by rw [sq]; exact haa.symm
  have hD : 0 < a ^ 2 - a + 1 := by nlinarith
  have hDen : ((p : ℝ) + 1) * (1 - 1 / a) + 1 / a = a ^ 2 - a + 1 := by
    rw [hpa]
    field_simp
    ring
  have hval : (p : ℝ) * M2Y.rhoH p / ((p : ℝ) + 1) = a ^ 2 / (a ^ 2 - a + 1) := by
    rw [rhoH_eq]
    unfold M2YK.rho
    rw [← ha, hDen]
    have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    field_simp
    rw [hpa]
  unfold epsH
  rw [hval, hpa]
  rw [div_pow, div_sub_one (by positivity), div_div, div_le_div_iff₀ (by positivity)
    (by positivity)]
  have h10 : (0 : ℝ) ≤ a - 10 := by linarith
  nlinarith [mul_nonneg (mul_nonneg ha0.le ha0.le) (mul_nonneg ha0.le h10),
    mul_nonneg (mul_nonneg ha0.le ha0.le) (mul_nonneg ha0.le ha0.le),
    mul_nonneg (mul_nonneg (mul_nonneg ha0.le ha0.le) (mul_nonneg ha0.le ha0.le)) h10]

/-- Small primes of `DSumH`. -/
theorem smallH (p : ℕ) (hm : p ∈ M2YK.smallP) :
    epsH p / p ≤ (((p : ℝ) * M2YK.rho p (1 / M2YK.sL p) / ((p : ℝ) + 1)) ^ 2 - 1) / p := by
  have hs1 : 1 < M2YK.sL p := by
    simp only [M2YK.smallP, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [M2YK.sL]
      norm_num
  have h2 : (0 : ℝ) < Real.sqrt p := by linarith [M2YK.sL_le p]
  have hp0 : (0 : ℝ) < p := Real.sqrt_pos.mp h2
  have hq : 1 / Real.sqrt (p : ℝ) ≤ 1 / M2YK.sL p :=
    one_div_le_one_div_of_le (by linarith) (M2YK.sL_le p)
  have hqb1 : 1 / M2YK.sL p < 1 := by rw [div_lt_one (by linarith)]; exact hs1
  have hr := rho_mono p _ _ hq hqb1
  have hr0 := rho_nonneg p (1 / Real.sqrt (p : ℝ)) (by positivity) (lt_of_le_of_lt hq hqb1)
  unfold epsH
  rw [rhoH_eq]
  apply div_le_div_of_nonneg_right _ hp0.le
  have h1 : (p : ℝ) * M2YK.rho p (1 / Real.sqrt p) / ((p : ℝ) + 1) ≤
      (p : ℝ) * M2YK.rho p (1 / M2YK.sL p) / ((p : ℝ) + 1) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr hp0.le) (by positivity)
  have h0 : 0 ≤ (p : ℝ) * M2YK.rho p (1 / Real.sqrt p) / ((p : ℝ) + 1) := by positivity
  nlinarith [pow_le_pow_left₀ h0 h1 2]

/-- The parity-restricted function `1_{n odd}·g(n)` as an arithmetic function. -/
noncomputable def oddF (g : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun d => if Nat.Coprime d 2 then g d else 0, by simp⟩

theorem oddF_apply (g : ℕ → ℝ) (n : ℕ) : oddF g n = if Nat.Coprime n 2 then g n else 0 := rfl

theorem oddF_mult (g : ℕ → ℝ) (hg1 : g 1 = 1)
    (hgm : ∀ m n, Nat.Coprime m n → g (m * n) = g m * g n) : (oddF g).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [oddF_apply, hg1], fun {m n} _ _ h => ?_⟩
  simp only [oddF_apply]
  exact ite_mul g m n (hgm m n h)

theorem oddF_nonneg (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ oddF g n := by
  rw [oddF_apply]
  split_ifs
  · exact hg n
  · exact le_rfl

theorem gH_nonneg (n : ℕ) : 0 ≤ gH n := by
  unfold gH
  have : 0 ≤ ∏ p ∈ n.primeFactors, M2Y.rhoH p ^ 2 := Finset.prod_nonneg fun p _ => sq_nonneg _
  positivity

theorem gE_nonneg (n : ℕ) : 0 ≤ gE n := by
  unfold gE
  have : 0 ≤ ∏ p ∈ n.primeFactors, epsH p := Finset.prod_nonneg fun p hp =>
    epsH_nonneg p (Nat.prime_of_mem_primeFactors hp).one_lt.le
  positivity

theorem gZ_nonneg (n : ℕ) : 0 ≤ gZ n := by
  unfold gZ
  positivity

/-- **`H ≤ E ⋆ Z`.** -/
theorem dom_HEZ (n : ℕ) : oddF gH n ≤ (oddF gE * oddF gZ) n := by
  have hE0 := oddF_nonneg gE gE_nonneg
  have hZ0 := oddF_nonneg gZ gZ_nonneg
  refine M2YE.mult_le (oddF gH) (oddF gE * oddF gZ)
    (oddF_mult gH (by simp [gH, M2Y.mu, M2Y.sg]) gH_mul)
    ((oddF_mult gE (by simp [gE, M2Y.mu]) gE_mul).mul
      (oddF_mult gZ (by simp [gZ, M2Y.mu]) gZ_mul))
    (oddF_nonneg gH gH_nonneg) (fun p k hp hk => ?_) n
  by_cases h2 : p = 2
  · subst h2
    have : oddF gH (2 ^ k) = 0 := by
      rw [oddF_apply, if_neg]
      intro h
      have := Nat.Coprime.coprime_dvd_left (dvd_pow_self 2 (by omega)) h
      norm_num at this
    rw [this]
    exact conv_nonneg _ _ hE0 hZ0 _
  by_cases hk2 : 2 ≤ k
  · have : oddF gH (p ^ k) = 0 := by
      rw [oddF_apply]
      split_ifs
      · unfold gH
        rw [mu_pow_zero p k hp hk2]
        simp
      · rfl
    rw [this]
    exact conv_nonneg _ _ hE0 hZ0 _
  have hk1 : k = 1 := by omega
  subst hk1
  rw [pow_one, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => oddF gE a * oddF gZ b), Nat.Prime.sum_divisors hp,
    Nat.div_self hp.pos, Nat.div_one]
  have ho := odd_of_prime p hp h2
  have h1 : Nat.Coprime 1 2 := Nat.coprime_one_left 2
  simp only [oddF_apply, if_pos ho, if_pos h1, gH, gE, gZ, mu_sq_prime p hp, sg_prime p hp,
    Nat.Prime.primeFactors hp, Finset.prod_singleton, Nat.primeFactors_one, Finset.prod_empty]
  have hm1 : M2Y.mu 1 = 1 := by simp [M2Y.mu]
  rw [hm1]
  unfold epsH
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  apply le_of_eq
  field_simp
  ring

/-- `∑_{e ≤ N} E(e) ≤ 2.74`. -/
theorem sumE_le (N : ℕ) : ∑ e ∈ Icc 1 N, oddF gE e ≤ 2.74 := by
  have hE0 := oddF_nonneg gE gE_nonneg
  have hmE := oddF_mult gE (by simp [gE, M2Y.mu]) gE_mul
  set F : ℕ → ℝ := fun e => oddF gE e with hF
  have h1 := M2YE.euler_le F hE0 hmE.map_one (fun m n _ _ h => hmE.map_mul_of_coprime h) N
  set P := (range (N + 1)).filter Nat.Prime with hP
  have hloc : ∀ p ∈ P, ∑ j ∈ range (N + 1), F (p ^ j) ≤ 1 + F p := fun p hp =>
    loc2 F p N hmE.map_one (fun j hj => by
      simp only [hF, oddF_apply]
      split_ifs
      · unfold gE
        rw [mu_pow_zero p j (Finset.mem_filter.mp hp).2 hj]
        simp
      · rfl) (hE0 p)
  have h2 := Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun j _ => hE0 _) hloc
  have hF2 : F 2 = 0 := by simp [hF, oddF_apply]
  rw [prod_drop_two F P hF2] at h2
  have hFp : ∀ p, p.Prime → p ≠ 2 → F p = epsH p / p := fun p hp h2 => by
    simp only [hF, oddF_apply, if_pos (odd_of_prime p hp h2), gE, mu_sq_prime p hp,
      Nat.Prime.primeFactors hp, Finset.prod_singleton]
    ring
  have hT : (2.47 : ℝ) / Real.sqrt ((101 : ℕ) - 2 : ℝ) ≤ 0.24828 := by
    have := M2YK.sqrt_99_ge
    norm_num
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hpp := M2YE.prod_primes_le P (fun p hp => (Finset.mem_filter.mp hp).2) F
    (fun p => (((p : ℝ) * M2YK.rho p (1 / M2YK.sL p) / ((p : ℝ) + 1)) ^ 2 - 1) / p)
    M2YK.smallP 101 (by norm_num) (by norm_num) 2.47
    (fun p _ => hE0 p)
    (fun p hp h2 h => M2YK.mem_smallP p (Finset.mem_filter.mp hp).2 h2 h)
    (fun p hp => by
      have hpr : p.Prime := by
        simp only [M2YK.smallP, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
      have h2 : p ≠ 2 := by
        simp only [M2YK.smallP, Finset.mem_insert, Finset.mem_singleton] at hp
        omega
      have := smallH p hp
      rw [← hFp p hpr h2] at this
      exact le_trans (hE0 p) this)
    (fun p hp h2 h => by
      have hpr := (Finset.mem_filter.mp hp).2
      rw [hFp p hpr h2]
      exact smallH p (M2YK.mem_smallP p hpr h2 h))
    (fun p hp hM => by
      rw [hFp p (Finset.mem_filter.mp hp).2 (by omega)]
      exact tailH p hM)
    (by norm_num) (by linarith)
  have hsmall : ∏ p ∈ M2YK.smallP,
      (1 + (((p : ℝ) * M2YK.rho p (1 / M2YK.sL p) / ((p : ℝ) + 1)) ^ 2 - 1) / p) ≤ 2.0590 := by
    simp only [M2YK.smallP, M2YK.sL, M2YK.rho]
    norm_num [Finset.prod_insert, Finset.prod_singleton]
  have hT0 : 0 ≤ (2.47 : ℝ) / Real.sqrt ((101 : ℕ) - 2 : ℝ) := by positivity
  have h3 : (∏ p ∈ M2YK.smallP,
      (1 + (((p : ℝ) * M2YK.rho p (1 / M2YK.sL p) / ((p : ℝ) + 1)) ^ 2 - 1) / p)) /
      (1 - (2.47 : ℝ) / Real.sqrt ((101 : ℕ) - 2 : ℝ)) ≤ 2.74 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

/-- `∑_{b ≤ N} Z(b) ≤ 1 + log N`. -/
theorem sumZ_le (N : ℕ) : ∑ b ∈ Icc 1 N, oddF gZ b ≤ 1 + Real.log N := by
  have hh := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at hh
  push_cast at hh
  refine le_trans (Finset.sum_le_sum fun b hb => ?_) hh
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (Finset.mem_Icc.mp hb).1
  rw [oddF_apply]
  split_ifs
  · unfold gZ
    have hm1 : M2Y.mu b ^ 2 ≤ 1 := by
      unfold M2Y.mu
      have h := ArithmeticFunction.abs_moebius_le_one (n := b)
      rcases abs_le.mp h with ⟨h1, h2⟩
      generalize (ArithmeticFunction.moebius b : ℤ) = m at h1 h2 ⊢
      interval_cases m <;> norm_num
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right hm1 (by linarith)
  · positivity

/-- **`M2Y.DSumH`, PROVED.** -/
theorem dSumH : M2Y.DSumH := by
  intro x hx
  set N := ⌊x⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hE0 := oddF_nonneg gE gE_nonneg
  have hZ0 := oddF_nonneg gZ gZ_nonneg
  have hswap : ∑ d ∈ Icc 1 N, oddF gH d ≤
      (∑ e ∈ Icc 1 N, oddF gE e) * ∑ b ∈ Icc 1 N, oddF gZ b := by
    calc ∑ d ∈ Icc 1 N, oddF gH d ≤ ∑ d ∈ Icc 1 N, (oddF gE * oddF gZ) d :=
          Finset.sum_le_sum fun d _ => dom_HEZ d
      _ = ∑ e ∈ Icc 1 N, oddF gE e * ∑ b ∈ Icc 1 (N / e), oddF gZ b := by
          rw [M2YC.Icc_one_eq, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [M2YC.Icc_one_eq]
      _ ≤ ∑ e ∈ Icc 1 N, oddF gE e * ∑ b ∈ Icc 1 N, oddF gZ b := by
          refine Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left ?_ (hE0 e)
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => ?_) fun b _ _ => hZ0 b
          simp only [Finset.mem_Icc] at hb ⊢
          exact ⟨hb.1, le_trans hb.2 (Nat.div_le_self N e)⟩
      _ = (∑ e ∈ Icc 1 N, oddF gE e) * ∑ b ∈ Icc 1 N, oddF gZ b := by rw [Finset.sum_mul]
  have hlog : Real.log N ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast hN1) (Nat.floor_le (by linarith))
  have hZ : ∑ b ∈ Icc 1 N, oddF gZ b ≤ 1 + Real.log x := by linarith [sumZ_le N]
  have hsum : ∑ d ∈ Icc 1 N, oddF gH d = ∑ d ∈ Icc 1 N, (if Nat.Coprime d 2 then
      M2Y.mu d ^ 2 * (d : ℝ) / M2Y.sg d ^ 2 * ∏ p ∈ d.primeFactors, M2Y.rhoH p ^ 2 else 0) :=
    rfl
  rw [← hsum]
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hZ0' : 0 ≤ ∑ b ∈ Icc 1 N, oddF gZ b := Finset.sum_nonneg fun b _ => hZ0 b
  calc ∑ d ∈ Icc 1 N, oddF gH d ≤ (∑ e ∈ Icc 1 N, oddF gE e) * ∑ b ∈ Icc 1 N, oddF gZ b :=
        hswap
    _ ≤ 2.74 * (1 + Real.log x) := mul_le_mul (sumE_le N) hZ hZ0' (by norm_num)
    _ ≤ 8 + 4 * Real.log x := by nlinarith

end Principia.Common.TernaryGoldbach.M2YD
