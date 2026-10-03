/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Principia.Common.Sieve.AuxResults

set_option autoImplicit false

/-!
# The sum of proper divisors along `n = m p` (Luca–Pomerance, Pollack)

Elementary facts about `s(n) = σ(n) − n` shared by the Luca–Pomerance Lemma 2.2 and Pollack
Theorem 1.4 modules of this directory:

* `aliq_mul_prime`: for a prime `p ∤ m`, `s(m p) = p s(m) + σ(m)` (the linear form in `p` that
  both source proofs sieve);
* `modEq_of_dvd`, `gcd_dvd_of_dvd`, `gcd_dvd_self_of_dvd`: every solution `P` of `Q ∣ P s + c`
  lies in one class modulo `Q / gcd(Q, s)`, and `gcd(Q, s(m)) ∣ m` once a solution exists — the
  refinement (after Pollack's Lemma 2.7) that removes Luca–Pomerance's appeal to their Lemma 2.1(2);
* `mul_totient_div_ge`: `g φ(q²/g) ≥ q(q−1)` for `g ∣ q²`, `q` prime;
* `sum_multiples_div_le`: `∑_{m ≤ Z, d ∣ m} d/m ≤ 1 + log Z`;
* `sum_Ioc_inv_mul_pred`: `∑_{K < j ≤ M} 1/(j(j−1)) = 1/K − 1/M`.

Everything is in Mathlib's vocabulary (`ArithmeticFunction.sigma 1`), so it is campaign-agnostic.
-/

namespace Principia.Common.LucaPomerance.Aliquot

open Finset

/-- `s(n) = σ(n) − n`, the sum of the proper divisors (truncated subtraction; `σ(n) ≥ n`). -/
abbrev aliq (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n - n

theorem le_sigma (n : ℕ) : n ≤ ArithmeticFunction.sigma 1 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [ArithmeticFunction.sigma_one_apply]
    exact Finset.single_le_sum (f := fun d : ℕ => d) (fun d _ => Nat.zero_le d)
      (Nat.mem_divisors_self n hn.ne')

theorem sigma_prime {p : ℕ} (hp : p.Prime) : ArithmeticFunction.sigma 1 p = p + 1 := by
  rw [ArithmeticFunction.sigma_one_apply, hp.divisors,
    Finset.sum_pair (Ne.symm hp.one_lt.ne')]
  ring

/-- `σ(m p) = σ(m) (p + 1)` for a prime `p ∤ m`. -/
theorem sigma_mul_prime {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    ArithmeticFunction.sigma 1 (m * p) = ArithmeticFunction.sigma 1 m * (p + 1) := by
  have hcop : Nat.Coprime m p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_prime hp]

/-- **`s(m p) = p s(m) + σ(m)`** for a prime `p ∤ m`. -/
theorem aliq_mul_prime {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    aliq (m * p) = p * aliq m + ArithmeticFunction.sigma 1 m := by
  unfold aliq
  rw [sigma_mul_prime hp hpm]
  obtain ⟨t, ht⟩ : ∃ t, ArithmeticFunction.sigma 1 m = m + t :=
    ⟨_, (Nat.add_sub_of_le (le_sigma m)).symm⟩
  rw [ht, Nat.add_sub_cancel_left]
  have e : (m + t) * (p + 1) = m * p + (p * t + (m + t)) := by ring
  rw [e, Nat.add_sub_cancel_left]

/-- All solutions `P` of `Q ∣ P s + c` lie in one residue class modulo `Q / gcd(Q, s)`. -/
theorem modEq_of_dvd {Q s c P₁ P₂ : ℕ} (hQ : 0 < Q) (h₁ : Q ∣ P₁ * s + c)
    (h₂ : Q ∣ P₂ * s + c) : P₁ ≡ P₂ [MOD Q / Nat.gcd Q s] := by
  apply Nat.ModEq.cancel_right_div_gcd hQ
  have e1 : P₁ * s + c ≡ 0 [MOD Q] := Nat.modEq_zero_iff_dvd.2 h₁
  have e2 : P₂ * s + c ≡ 0 [MOD Q] := Nat.modEq_zero_iff_dvd.2 h₂
  exact Nat.ModEq.add_right_cancel' c (e1.trans e2.symm)

/-- If `Q ∣ P s + c` then `gcd(Q, s) ∣ c`. -/
theorem gcd_dvd_of_dvd {Q s c P : ℕ} (h : Q ∣ P * s + c) : Nat.gcd Q s ∣ c := by
  have h1 : Nat.gcd Q s ∣ P * s + c := (Nat.gcd_dvd_left Q s).trans h
  have h2 : Nat.gcd Q s ∣ P * s := Dvd.dvd.mul_left (Nat.gcd_dvd_right Q s) P
  exact (Nat.dvd_add_right h2).1 h1

/-- If `Q ∣ P s(m) + σ(m)` then `gcd(Q, s(m)) ∣ m`. -/
theorem gcd_dvd_self_of_dvd {Q m P : ℕ} (h : Q ∣ P * aliq m + ArithmeticFunction.sigma 1 m) :
    Nat.gcd Q (aliq m) ∣ m := by
  have h1 : Nat.gcd Q (aliq m) ∣ ArithmeticFunction.sigma 1 m := gcd_dvd_of_dvd h
  have h2 : Nat.gcd Q (aliq m) ∣ aliq m := Nat.gcd_dvd_right _ _
  have h3 := Nat.dvd_sub h1 h2
  unfold aliq at h3
  rwa [Nat.sub_sub_self (le_sigma m)] at h3

/-- `g φ(q²/g) ≥ q (q − 1)` for every divisor `g` of `q²`, `q` prime. -/
theorem mul_totient_div_ge {q g : ℕ} (hq : q.Prime) (hg : g ∣ q ^ 2) :
    q * (q - 1) ≤ g * (q ^ 2 / g).totient := by
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hq).1 hg
  have hq0 : 0 < q := hq.pos
  interval_cases i
  · rw [pow_zero, Nat.div_one, one_mul, Nat.totient_prime_pow hq (by norm_num)]
    simp
  · rw [pow_one, show q ^ 2 = q * q by ring, Nat.mul_div_cancel _ hq0, Nat.totient_prime hq]
  · rw [Nat.div_self (pow_pos hq0 2), Nat.totient_one, mul_one, sq]
    exact Nat.mul_le_mul_left q (Nat.sub_le q 1)

/-- `∑_{m ≤ Z, d ∣ m} d/m ≤ 1 + log Z`. -/
theorem sum_multiples_div_le (d Z : ℕ) (hd : 1 ≤ d) (hZ : 1 ≤ Z) :
    ∑ m ∈ (Icc 1 Z).filter (d ∣ ·), (d : ℝ) / m ≤ 1 + Real.log Z := by
  have hd0 : 0 < d := hd
  have himage : (Icc 1 Z).filter (d ∣ ·) = (Icc 1 (Z / d)).image (d * ·) := by
    ext m
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨j, rfl⟩⟩
      refine ⟨j, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp at h1
        · exact hj
      · exact (Nat.le_div_iff_mul_le hd0).2 (by rw [mul_comm]; exact h2)
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right d j⟩
      · exact Nat.mul_le_mul hd h1
      · have := (Nat.le_div_iff_mul_le hd0).1 h2
        rw [mul_comm]
        exact this
  rw [himage, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd0 h)]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
  calc ∑ j ∈ Icc 1 (Z / d), (d : ℝ) / ((d * j : ℕ) : ℝ)
      = ∑ j ∈ Icc 1 (Z / d), (j : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro j _
        push_cast
        rw [div_mul_eq_div_div, div_self hdR, one_div]
    _ ≤ ∑ j ∈ Icc 1 Z, (j : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (Nat.div_le_self _ _))
          (fun _ _ _ => by positivity)
    _ ≤ 1 + Real.log Z := Aux.sum_inv_le_log Z hZ

/-- Telescoping: `∑_{K < j ≤ M} 1/(j (j − 1)) = 1/K − 1/M` for `1 ≤ K ≤ M`. -/
theorem sum_Ioc_inv_mul_pred (K : ℕ) (hK : 1 ≤ K) :
    ∀ M : ℕ, K ≤ M →
      ∑ j ∈ Ioc K M, (1 : ℝ) / ((j : ℝ) * ((j : ℝ) - 1)) = 1 / (K : ℝ) - 1 / (M : ℝ) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hKM ih =>
    rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hKM, Finset.sum_insert (by simp), ih]
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (hK.trans hKM)
    have hM0 : (M : ℝ) ≠ 0 := by linarith
    have hM10 : (M : ℝ) + 1 ≠ 0 := by linarith
    push_cast
    rw [show (M : ℝ) + 1 - 1 = M by ring]
    field_simp
    ring

/-- `∑_{K < j ≤ M} 1/(j (j − 1)) ≤ 1/K`. -/
theorem sum_Ioc_inv_mul_pred_le (K M : ℕ) (hK : 1 ≤ K) :
    ∑ j ∈ Ioc K M, (1 : ℝ) / ((j : ℝ) * ((j : ℝ) - 1)) ≤ 1 / (K : ℝ) := by
  rcases le_or_gt K M with h | h
  · rw [sum_Ioc_inv_mul_pred K hK M h]
    have : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    positivity

end Principia.Common.LucaPomerance.Aliquot
