/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Davenport.Truncation
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Rat.BigOperators

set_option autoImplicit false

/-!
# Davenport's theorem, part 2: `σ(n)/n` does not concentrate (continuity of the law)

**Theorem** (`eventually_card_abund_near_le`). For every real `c` and every `η > 0` there is
`δ > 0` such that `#{1 ≤ n ≤ X : |σ(n)/n − c| ≤ δ} ≤ η X` for all large `X`.

This is exactly what makes Davenport's limiting distribution function of `σ(n)/n` continuous.
The proof is elementary and uses only the divergence of `∑ 1/p` (Mathlib's
`not_summable_one_div_on_primes`). Fix `y < z` and the primes `P = (y, z]`, `M = ∏_{p ∈ P} p`.
An integer `n` with `|h(n) − c| ≤ δ` (`h = σ(n)/n`) falls in one of three classes:

1. `gcd(n, M) = 1`: at most `X φ(M)/M + M = X ∏_{p ∈ P} (1 − 1/p) + M`, and the product is
   `≤ 1/(1 + ∑_{p ∈ P} 1/p)`, as small as we like once `z` is large (`card_coprime_le`,
   `totient_div_prod_eq`, `prod_one_sub_inv_le`, `exists_sum_prime_recip_ge`);
2. `p² ∣ n` for some `p ∈ P`: at most `X ∑_{p > y} 1/p² ≤ 2X/(y+1)` (`card_sq_dvd_le`);
3. `p ∥ n` for some `p ∈ P`: write `n = p m` with `p ∤ m`, so `h(n) = (1 + 1/p) h(m)`. For fixed
   `m` two primes `p < p' ≤ z` give values differing by `(1/p − 1/p') h(m) ≥ 1/z²`, so when
   `2δz² < 1` at most one of them lies within `δ` of `c`. Hence `n ↦ m = n/p` is at most
   one-to-one into `[1, X/(y+1)]`, and the class has at most `X/(y+1)` elements
   (`prime_eq_of_abund_close`, `card_exact_near_le`).

Choosing `y ≍ 1/η`, then `z` with `∑_{y < p ≤ z} 1/p ≥ 4/η`, then `δ = 1/(4(z² + 1))` gives the
theorem. This avoids the Erdős–Wintner/Lévy concentration machinery entirely.
-/

namespace Principia.Common.Davenport

open Finset Filter

/-- `σ(p) = p + 1`. -/
theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : ArithmeticFunction.sigma 1 p = p + 1 := by
  rw [ArithmeticFunction.sigma_one_apply, hp.divisors,
    Finset.sum_pair (Ne.symm hp.one_lt.ne')]
  ring

/-- `h(p m) = (1 + 1/p) h(m)` for a prime `p ∤ m`. -/
theorem abund_prime_mul {p m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    abund (p * m) = (1 + 1 / (p : ℝ)) * abund m := by
  have hm : m ≠ 0 := by
    rintro rfl
    exact hpm (dvd_zero p)
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  have hmul : ArithmeticFunction.sigma 1 (p * m) =
      ArithmeticFunction.sigma 1 p * ArithmeticFunction.sigma 1 m :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e : ((p : ℝ) + 1) / p = 1 + 1 / (p : ℝ) := by rw [add_div, div_self hp0]
  unfold abund
  rw [hmul, sigma_one_prime hp]
  push_cast
  rw [← e, div_mul_div_comm]

/-- **Spacing.** For a fixed `m`, two primes `p₁, p₂ ≤ z` not dividing `m` whose values
`h(p_i m)` both lie within `δ` of `c` coincide, provided `2 δ z² < 1`. -/
theorem prime_eq_of_abund_close {p₁ p₂ m z : ℕ} {c δ : ℝ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime)
    (h₁ : ¬ p₁ ∣ m) (h₂ : ¬ p₂ ∣ m) (hz₁ : p₁ ≤ z) (hz₂ : p₂ ≤ z)
    (hδ : 2 * δ * (z : ℝ) ^ 2 < 1)
    (hc₁ : |abund (p₁ * m) - c| ≤ δ) (hc₂ : |abund (p₂ * m) - c| ≤ δ) : p₁ = p₂ := by
  have key : ∀ {q₁ q₂ : ℕ}, q₁.Prime → q₂.Prime → ¬ q₁ ∣ m → ¬ q₂ ∣ m → q₁ ≤ z → q₂ ≤ z →
      |abund (q₁ * m) - c| ≤ δ → |abund (q₂ * m) - c| ≤ δ → ¬ q₁ < q₂ := by
    intro q₁ q₂ hq₁ hq₂ hn₁ hn₂ hqz₁ hqz₂ hd₁ hd₂ hlt
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        exact absurd (dvd_zero q₁) hn₁
      · exact h
    have hA := one_le_abund hm
    rw [abund_prime_mul hq₁ hn₁] at hd₁
    rw [abund_prime_mul hq₂ hn₂] at hd₂
    have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hd₁
    have r₁ : (0 : ℝ) < q₁ := by exact_mod_cast hq₁.pos
    have r₂ : (0 : ℝ) < q₂ := by exact_mod_cast hq₂.pos
    have r₁' : (q₁ : ℝ) ≠ 0 := r₁.ne'
    have r₂' : (q₂ : ℝ) ≠ 0 := r₂.ne'
    have hlt' : (q₁ : ℝ) + 1 ≤ q₂ := by exact_mod_cast hlt
    have hz₁' : (q₁ : ℝ) ≤ z := by exact_mod_cast hqz₁
    have hz₂' : (q₂ : ℝ) ≤ z := by exact_mod_cast hqz₂
    have hdiff : (1 / (q₁ : ℝ) - 1 / q₂) * abund m ≤ 2 * δ := by
      have e : (1 + 1 / (q₁ : ℝ)) * abund m - (1 + 1 / q₂) * abund m =
          (1 / (q₁ : ℝ) - 1 / q₂) * abund m := by ring
      have a₁ := abs_sub_le_iff.1 hd₁
      have a₂ := abs_sub_le_iff.1 hd₂
      linarith
    have e2 : (1 / (q₁ : ℝ) - 1 / q₂) * abund m * (q₁ * q₂) = (q₂ - q₁) * abund m := by
      calc (1 / (q₁ : ℝ) - 1 / q₂) * abund m * (q₁ * q₂)
          = abund m * (q₂ * ((q₁ : ℝ) * (1 / q₁)) - q₁ * ((q₂ : ℝ) * (1 / q₂))) := by ring
        _ = (q₂ - q₁) * abund m := by
          rw [mul_one_div_cancel r₁', mul_one_div_cancel r₂']
          ring
    have h3 : ((q₂ : ℝ) - q₁) * abund m ≤ 2 * δ * (q₁ * q₂) := by
      rw [← e2]
      exact mul_le_mul_of_nonneg_right hdiff (by positivity)
    have h4 : (q₁ : ℝ) * q₂ ≤ (z : ℝ) ^ 2 := by
      rw [sq]
      exact mul_le_mul hz₁' hz₂' r₂.le (le_trans r₁.le hz₁')
    have h5 : 2 * δ * ((q₁ : ℝ) * q₂) ≤ 2 * δ * (z : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left h4 (by linarith)
    have hd : (1 : ℝ) ≤ (q₂ : ℝ) - q₁ := by linarith
    have h6 : (1 : ℝ) ≤ ((q₂ : ℝ) - q₁) * abund m :=
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ((q₂ : ℝ) - q₁) * abund m := mul_le_mul hd hA zero_le_one (by linarith)
    linarith
  rcases lt_trichotomy p₁ p₂ with h | h | h
  · exact absurd h (key hp₁ hp₂ h₁ h₂ hz₁ hz₂ hc₁ hc₂)
  · exact h
  · exact absurd h (key hp₂ hp₁ h₂ h₁ hz₂ hz₁ hc₂ hc₁)

/-- **Class 3.** The `n ≤ X` within `δ` of `c` that have a prime factor `p ∈ P ⊆ (y, z]` exactly
dividing them number at most `X/(y+1)`, provided `2 δ z² < 1`. -/
theorem card_exact_near_le (y z X : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ y < p ∧ p ≤ z) (c δ : ℝ) (hδ : 2 * δ * (z : ℝ) ^ 2 < 1) :
    (((Icc 1 X).filter (fun n => |abund n - c| ≤ δ ∧
        ∃ p ∈ P, p ∣ n ∧ ¬ p ^ 2 ∣ n)).card : ℝ) ≤ (X : ℝ) / (y + 1) := by
  have hcard : ((Icc 1 X).filter (fun n => |abund n - c| ≤ δ ∧
        ∃ p ∈ P, p ∣ n ∧ ¬ p ^ 2 ∣ n)).card ≤ (Icc 1 (X / (y + 1))).card := by
    apply Finset.card_le_card_of_forall_subsingleton
      (fun n m => ∃ p ∈ P, n = p * m ∧ ¬ p ∣ m)
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨h1, hX⟩, _, p, hp, hpn, hp2⟩ := hn
      obtain ⟨hpp, hyp, _⟩ := hP p hp
      have hppos : 0 < p := hpp.pos
      refine ⟨n / p, ?_, p, hp, (Nat.mul_div_cancel' hpn).symm, ?_⟩
      · rw [Finset.mem_Icc]
        constructor
        · exact Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hppos
        · rw [Nat.le_div_iff_mul_le (by omega)]
          calc n / p * (y + 1) ≤ n / p * p := Nat.mul_le_mul_left _ (by omega)
            _ = n := Nat.div_mul_cancel hpn
            _ ≤ X := hX
      · intro hdvd
        apply hp2
        have h' : p * p ∣ p * (n / p) := Nat.mul_dvd_mul_left p hdvd
        rw [Nat.mul_div_cancel' hpn, ← sq] at h'
        exact h'
    · intro m _ n₁ hn₁ n₂ hn₂
      simp only [Set.mem_setOf_eq, Finset.mem_filter] at hn₁ hn₂
      obtain ⟨⟨_, hc₁, _⟩, p₁, hp₁, e₁, hd₁⟩ := hn₁
      obtain ⟨⟨_, hc₂, _⟩, p₂, hp₂, e₂, hd₂⟩ := hn₂
      obtain ⟨hpp₁, _, hz₁⟩ := hP p₁ hp₁
      obtain ⟨hpp₂, _, hz₂⟩ := hP p₂ hp₂
      subst e₁ e₂
      have hpeq := prime_eq_of_abund_close hpp₁ hpp₂ hd₁ hd₂ hz₁ hz₂ hδ hc₁ hc₂
      rw [hpeq]
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
  calc (((Icc 1 X).filter (fun n => |abund n - c| ≤ δ ∧
        ∃ p ∈ P, p ∣ n ∧ ¬ p ^ 2 ∣ n)).card : ℝ) ≤ ((X / (y + 1) : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ (X : ℝ) / ((y + 1 : ℕ) : ℝ) := Nat.cast_div_le
    _ = (X : ℝ) / (y + 1) := by rw [Nat.cast_add, Nat.cast_one]

/-- **Class 2.** `#{n ≤ X : p² ∣ n for some p ∈ P} ≤ 2X/(y+1)` when `P ⊆ (y, z]`. -/
theorem card_sq_dvd_le (y z X : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, y < p ∧ p ≤ z) :
    (((Icc 1 X).filter (fun n => ∃ p ∈ P, p ^ 2 ∣ n)).card : ℝ) ≤ X * (2 / (y + 1)) := by
  have hsub : (Icc 1 X).filter (fun n => ∃ p ∈ P, p ^ 2 ∣ n) ⊆
      P.biUnion (fun p => (Icc 1 X).filter (fun n => p ^ 2 ∣ n)) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hn1, p, hp, hd⟩ := hn
    rw [Finset.mem_biUnion]
    exact ⟨p, hp, Finset.mem_filter.2 ⟨hn1, hd⟩⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hIcc : (Icc 1 X) = Ioc 0 X := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have h2 : ∀ p ∈ P, ((((Icc 1 X).filter (fun n => p ^ 2 ∣ n)).card : ℕ) : ℝ) ≤
      X * ((p : ℝ) ^ 2)⁻¹ := by
    intro p _
    rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div X (p ^ 2)]
    calc ((X / p ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) / ((p ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
      _ = X * ((p : ℝ) ^ 2)⁻¹ := by rw [Nat.cast_pow, div_eq_mul_inv]
  have hPsub : P ⊆ Ioo y (z + 1) := by
    intro p hp
    have := hP p hp
    rw [Finset.mem_Ioo]
    omega
  calc (((Icc 1 X).filter (fun n => ∃ p ∈ P, p ^ 2 ∣ n)).card : ℝ)
      ≤ ∑ p ∈ P, ((((Icc 1 X).filter (fun n => p ^ 2 ∣ n)).card : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ ≤ ∑ p ∈ P, (X : ℝ) * ((p : ℝ) ^ 2)⁻¹ := Finset.sum_le_sum h2
    _ = X * ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ X * ∑ p ∈ Ioo y (z + 1), ((p : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hPsub (fun _ _ _ => by positivity))
          (Nat.cast_nonneg X)
    _ ≤ X * (2 / (y + 1)) :=
        mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le y (z + 1)) (Nat.cast_nonneg X)

/-- **Class 1, count.** `#{n ≤ X : gcd(M, n) = 1} ≤ X φ(M)/M + M`. -/
theorem card_coprime_le (M X : ℕ) (hM : M ≠ 0) :
    (((Icc 1 X).filter (fun n => M.Coprime n)).card : ℝ) ≤ X * ((M.totient : ℝ) / M) + M := by
  have h := Nat.Ico_filter_coprime_le 1 X hM
  have hIco : Ico 1 (1 + X) = Icc 1 X := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hIco] at h
  have hφ : (M.totient : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
  have hdiv : ((X / M : ℕ) : ℝ) ≤ (X : ℝ) / M := Nat.cast_div_le
  have hmul := mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg (M.totient))
  calc (((Icc 1 X).filter (fun n => M.Coprime n)).card : ℝ)
      ≤ ((M.totient * (X / M + 1) : ℕ) : ℝ) := by exact_mod_cast h
    _ = (M.totient : ℝ) * ((X / M : ℕ) : ℝ) + M.totient := by push_cast; ring
    _ ≤ (M.totient : ℝ) * ((X : ℝ) / M) + M := by linarith
    _ = X * ((M.totient : ℝ) / M) + M := by ring

/-- **Class 1, density.** For a finset `P` of primes, `φ(∏ P)/∏ P = ∏_{p ∈ P} (1 − 1/p)`. -/
theorem totient_div_prod_eq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ((∏ p ∈ P, p).totient : ℝ) / ((∏ p ∈ P, p : ℕ) : ℝ) = ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
  have h := Nat.totient_eq_mul_prod_factors (∏ p ∈ P, p)
  rw [Nat.primeFactors_prod hP] at h
  have hM : ((∏ p ∈ P, p : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.2 fun p hp => (hP p hp).ne_zero
  rw [div_eq_iff hM]
  have h2 := congrArg (fun q : ℚ => (q : ℝ)) h
  push_cast at h2 ⊢
  simp only [one_div] at h2 ⊢
  linear_combination h2

/-- `∏_{p ∈ P} (1 − 1/p) ≤ 1/(1 + ∑_{p ∈ P} 1/p)` (from `1 − x ≤ e^{−x}` and `e^S ≥ 1 + S`). -/
theorem prod_one_sub_inv_le (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) :
    ∏ p ∈ P, (1 - 1 / (p : ℝ)) ≤ 1 / (1 + ∑ p ∈ P, 1 / (p : ℝ)) := by
  have h1 : ∏ p ∈ P, (1 - 1 / (p : ℝ)) ≤ ∏ p ∈ P, Real.exp (-(1 / (p : ℝ))) := by
    apply Finset.prod_le_prod
    · intro p hp
      have h1p : (1 : ℝ) ≤ p := by exact_mod_cast hP p hp
      rw [sub_nonneg, div_le_one (by linarith)]
      exact h1p
    · intro p _
      have := Real.add_one_le_exp (-(1 / (p : ℝ)))
      linarith
  rw [← Real.exp_sum, Finset.sum_neg_distrib] at h1
  have hS : 0 ≤ ∑ p ∈ P, 1 / (p : ℝ) := Finset.sum_nonneg fun p _ => by positivity
  have h2 : Real.exp (-(∑ p ∈ P, 1 / (p : ℝ))) ≤ 1 / (1 + ∑ p ∈ P, 1 / (p : ℝ)) := by
    rw [Real.exp_neg, ← one_div]
    have := Real.add_one_le_exp (∑ p ∈ P, 1 / (p : ℝ))
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  exact h1.trans h2

/-- **Divergence of `∑ 1/p`, tail form.** For every `y` and `B` there is `z ≥ y` with
`∑_{y < p ≤ z} 1/p ≥ B`. -/
theorem exists_sum_prime_recip_ge (y : ℕ) (B : ℝ) :
    ∃ z : ℕ, y ≤ z ∧ B ≤ ∑ p ∈ (Ioc y z).filter Nat.Prime, 1 / (p : ℝ) := by
  have hf0 : ∀ n, 0 ≤ Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n :=
    fun n => Set.indicator_nonneg (fun m _ => by change (0 : ℝ) ≤ 1 / (m : ℝ); positivity) n
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf0).1 not_summable_one_div_on_primes
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hdiv.eventually_ge_atTop
    (B + ∑ i ∈ range (y + 1), Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i))
  refine ⟨max N y, le_max_right _ _, ?_⟩
  have h1 := hN (max N y + 1) (by omega)
  have h2 := Finset.sum_range_add_sum_Ico
    (Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n))
    (show y + 1 ≤ max N y + 1 by omega)
  have h3 : ∑ i ∈ Ico (y + 1) (max N y + 1),
      Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i =
      ∑ p ∈ (Ioc y (max N y)).filter Nat.Prime, 1 / (p : ℝ) := by
    have hI : Ico (y + 1) (max N y + 1) = Ioc y (max N y) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    rw [hI, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : Nat.Prime i
    · rw [if_pos hi, Set.indicator_of_mem (show i ∈ {p : ℕ | p.Prime} from hi)]
    · rw [if_neg hi, Set.indicator_of_notMem (show i ∉ {p : ℕ | p.Prime} from hi)]
  linarith

/-- **Davenport's continuity, count form: `σ(n)/n` does not concentrate.** For every `c` and
`η > 0` there is `δ > 0` with `#{1 ≤ n ≤ X : |σ(n)/n − c| ≤ δ} ≤ η X` for all large `X`. -/
theorem eventually_card_abund_near_le (c : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℕ in atTop,
      (((Icc 1 X).filter (fun n => |abund n - c| ≤ δ)).card : ℝ) ≤ η * X := by
  obtain ⟨y, hy⟩ := exists_nat_gt (12 / η)
  obtain ⟨z, _, hS⟩ := exists_sum_prime_recip_ge y (4 / η)
  obtain ⟨P, hPdef⟩ : ∃ P : Finset ℕ, P = (Ioc y z).filter Nat.Prime := ⟨_, rfl⟩
  rw [← hPdef] at hS
  have hPmem : ∀ p ∈ P, p.Prime ∧ y < p ∧ p ≤ z := by
    intro p hp
    rw [hPdef, Finset.mem_filter, Finset.mem_Ioc] at hp
    exact ⟨hp.2, hp.1.1, hp.1.2⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = ∏ p ∈ P, p := ⟨_, rfl⟩
  have hM0 : M ≠ 0 := by
    rw [hMdef]
    exact Finset.prod_ne_zero_iff.2 fun p hp => (hPmem p hp).1.ne_zero
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / (4 * ((z : ℝ) ^ 2 + 1)) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    rw [hδdef]
    positivity
  have hδz : 2 * δ * (z : ℝ) ^ 2 < 1 := by
    have hz2 : (0 : ℝ) ≤ (z : ℝ) ^ 2 := by positivity
    have hden : (0 : ℝ) < 4 * ((z : ℝ) ^ 2 + 1) := by positivity
    have e : 2 * δ * (z : ℝ) ^ 2 = (2 * (z : ℝ) ^ 2) / (4 * ((z : ℝ) ^ 2 + 1)) := by
      rw [hδdef]
      ring
    rw [e, div_lt_one hden]
    linarith
  -- the three density constants
  have hratio : (M.totient : ℝ) / M ≤ η / 4 := by
    rw [hMdef, totient_div_prod_eq P (fun p hp => (hPmem p hp).1)]
    have hS0 : 0 ≤ ∑ p ∈ P, 1 / (p : ℝ) := Finset.sum_nonneg fun p _ => by positivity
    refine (prod_one_sub_inv_le P (fun p hp => (hPmem p hp).1.one_lt.le)).trans ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have h4 : 4 ≤ (∑ p ∈ P, 1 / (p : ℝ)) * η := (div_le_iff₀ hη).1 hS
    nlinarith
  have hy' : 1 / ((y : ℝ) + 1) ≤ η / 12 := by
    have hy1 : (0 : ℝ) < (y : ℝ) + 1 := by positivity
    rw [div_le_div_iff₀ hy1 (by norm_num)]
    have h12 : 12 < (y : ℝ) * η := (div_lt_iff₀ hη).1 hy
    nlinarith
  refine ⟨δ, hδpos, ?_⟩
  filter_upwards [eventually_ge_atTop ⌈2 * (M : ℝ) / η⌉₊] with X hX
  have hX0 : 2 * (M : ℝ) / η ≤ X := le_trans (Nat.le_ceil _) (by exact_mod_cast hX)
  have hMX : 2 * (M : ℝ) ≤ X * η := (div_le_iff₀ hη).1 hX0
  -- the decomposition into the three classes
  have hsub : (Icc 1 X).filter (fun n => |abund n - c| ≤ δ) ⊆
      ((Icc 1 X).filter (fun n => M.Coprime n) ∪
        (Icc 1 X).filter (fun n => ∃ p ∈ P, p ^ 2 ∣ n)) ∪
        (Icc 1 X).filter (fun n => |abund n - c| ≤ δ ∧ ∃ p ∈ P, p ∣ n ∧ ¬ p ^ 2 ∣ n) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hcop : M.Coprime n
    · exact Or.inl (Or.inl ⟨hn.1, hcop⟩)
    · have hex : ∃ p ∈ P, p ∣ n := by
        rw [hMdef, Nat.coprime_prod_left_iff] at hcop
        push Not at hcop
        obtain ⟨p, hp, hpn⟩ := hcop
        refine ⟨p, hp, ?_⟩
        by_contra hnd
        exact hpn ((Nat.Prime.coprime_iff_not_dvd (hPmem p hp).1).2 hnd)
      obtain ⟨p, hp, hpn⟩ := hex
      by_cases hp2 : p ^ 2 ∣ n
      · exact Or.inl (Or.inr ⟨hn.1, p, hp, hp2⟩)
      · exact Or.inr ⟨hn.1, hn.2, p, hp, hpn, hp2⟩
  have hcard := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hcardR : (((Icc 1 X).filter (fun n => |abund n - c| ≤ δ)).card : ℝ) ≤
      (((Icc 1 X).filter (fun n => M.Coprime n)).card : ℝ) +
      (((Icc 1 X).filter (fun n => ∃ p ∈ P, p ^ 2 ∣ n)).card : ℝ) +
      (((Icc 1 X).filter
        (fun n => |abund n - c| ≤ δ ∧ ∃ p ∈ P, p ∣ n ∧ ¬ p ^ 2 ∣ n)).card : ℝ) := by
    exact_mod_cast hcard
  have h1 := card_coprime_le M X hM0
  have h2 := card_sq_dvd_le y z X P (fun p hp => (hPmem p hp).2)
  have h3 := card_exact_near_le y z X P hPmem c δ hδz
  have hX0' : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have k1 : (X : ℝ) * ((M.totient : ℝ) / M) ≤ X * (η / 4) :=
    mul_le_mul_of_nonneg_left hratio hX0'
  have k2 : (X : ℝ) * (2 / ((y : ℝ) + 1)) ≤ X * (2 * (η / 12)) := by
    apply mul_le_mul_of_nonneg_left _ hX0'
    have : 2 / ((y : ℝ) + 1) = 2 * (1 / ((y : ℝ) + 1)) := by ring
    rw [this]
    linarith
  have k3 : (X : ℝ) / ((y : ℝ) + 1) ≤ X * (η / 12) := by
    have : (X : ℝ) / ((y : ℝ) + 1) = X * (1 / ((y : ℝ) + 1)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hy' hX0'
  linarith

end Principia.Common.Davenport
