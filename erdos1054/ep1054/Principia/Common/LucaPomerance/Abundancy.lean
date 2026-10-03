/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.LucaPomerance.Basic
import Principia.Common.Davenport.Concentration
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false

/-!
# The abundancy of `s(n)` against that of `n`

The structural half of the weak Pollack Theorem 1.4 (`Pollack14.lean`):

**`abund_aliq_le`.** If `p^k ∣ σ(n)` and `p^k ∤ n` for every prime `p ≤ w`, then
`h(s(n)) ≤ h(n) · exp(2 ∑_{p ∣ s(n), p > w} 1/p)`, where `h(N) = σ(N)/N`
(`Common.Davenport.abund`).

Proof: for `p ≤ w`, `v_p(n) < k ≤ v_p(σ(n))` forces `v_p(s(n)) = v_p(n)`
(`factorization_aliq_eq`). Write `h(N) = ∏_{p ∣ N} σ(p^{v_p N})/p^{v_p N}` (`abund_eq_prod`); the
factors of `h(s(n))` at primes `≤ w` are factors of `h(n)` (each factor is `≥ 1`), and those at
primes `p > w` are `≤ 1 + 2/p ≤ e^{2/p}` (`ppRatio_le`).
-/

namespace Principia.Common.LucaPomerance.Pollack14

open Principia.Common.LucaPomerance.Aliquot

open Finset
open Principia.Common.Davenport (abund one_le_abund abund_nonneg)

/-- `σ(p^a)/p^a`. -/
noncomputable def ppRatio (p a : ℕ) : ℝ :=
  (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) / ((p : ℝ) ^ a)

/-- `h(N) = ∏_{p ∣ N} σ(p^{v_p N})/p^{v_p N}`. -/
theorem abund_eq_prod {N : ℕ} (hN : N ≠ 0) :
    abund N = ∏ p ∈ N.primeFactors, ppRatio p (N.factorization p) := by
  unfold abund ppRatio
  have h1 : (ArithmeticFunction.sigma 1 N : ℝ) =
      ∏ p ∈ N.primeFactors, (ArithmeticFunction.sigma 1 (p ^ N.factorization p) : ℝ) := by
    rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
      ArithmeticFunction.isMultiplicative_sigma hN, Finsupp.prod, Nat.support_factorization,
      Nat.cast_prod]
  have h2 : (N : ℝ) = ∏ p ∈ N.primeFactors, ((p : ℝ) ^ N.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN]
    rw [Finsupp.prod, Nat.support_factorization, Nat.cast_prod]
    push_cast
    rfl
  rw [h1, h2, Finset.prod_div_distrib]

theorem one_le_ppRatio {p : ℕ} (hp : p.Prime) (a : ℕ) : 1 ≤ ppRatio p a := by
  unfold ppRatio
  have hpa : (0 : ℝ) < (p : ℝ) ^ a := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  rw [le_div_iff₀ hpa, one_mul]
  have := le_sigma (p ^ a)
  exact_mod_cast this

/-- `σ(p^a)/p^a < p/(p − 1) ≤ 1 + 2/p`. -/
theorem ppRatio_le {p : ℕ} (hp : p.Prime) (a : ℕ) : ppRatio p a ≤ 1 + 2 / (p : ℝ) := by
  unfold ppRatio
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hpa : (0 : ℝ) < (p : ℝ) ^ a := by positivity
  rw [div_le_iff₀ hpa]
  have hgeom : (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) * ((p : ℝ) - 1) =
      (p : ℝ) ^ (a + 1) - 1 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
    push_cast
    exact geom_sum_mul (p : ℝ) (a + 1)
  have hkey : (p : ℝ) ^ (a + 1) - 1 ≤ ((1 + 2 / (p : ℝ)) * (p : ℝ) ^ a) * ((p : ℝ) - 1) := by
    have e : ((1 + 2 / (p : ℝ)) * (p : ℝ) ^ a) * ((p : ℝ) - 1) =
        (p : ℝ) ^ a * (((p : ℝ) - 1) * ((p : ℝ) + 2) / p) := by
      field_simp
    rw [e, pow_succ]
    have h3 : (p : ℝ) ≤ ((p : ℝ) - 1) * ((p : ℝ) + 2) / p := by
      rw [le_div_iff₀ hp0]
      nlinarith
    nlinarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [← hgeom] at hkey
  exact le_of_mul_le_mul_right hkey hp1

/-- `σ(n) ≥ n + 1` for `n ≥ 2`, so `s(n) ≥ 1`. -/
theorem one_le_aliq {n : ℕ} (hn : 2 ≤ n) : 1 ≤ aliq n := by
  have h : n + 1 ≤ ArithmeticFunction.sigma 1 n := by
    rw [ArithmeticFunction.sigma_one_apply]
    have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
      intro d hd
      rw [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · exact Nat.one_mem_divisors.2 (by omega)
      · exact Nat.mem_divisors_self _ (by omega)
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun d : ℕ => d) hsub
      (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_pair (by omega)] at this
    omega
  unfold aliq
  omega

/-- `v_p(s(n)) = v_p(n)` when `p^k ∣ σ(n)` and `p^k ∤ n`. -/
theorem factorization_aliq_eq {n p k : ℕ} (hn : 2 ≤ n) (hp : p.Prime)
    (hσ : p ^ k ∣ ArithmeticFunction.sigma 1 n) (hnk : ¬ p ^ k ∣ n) :
    (aliq n).factorization p = n.factorization p := by
  have hn0 : n ≠ 0 := by omega
  have hs0 : aliq n ≠ 0 := by have := one_le_aliq hn; omega
  set a := n.factorization p with ha
  have hak : a < k := by
    by_contra h
    push Not at h
    exact hnk ((hp.pow_dvd_iff_le_factorization hn0).2 h)
  have hpa_n : p ^ a ∣ n := (hp.pow_dvd_iff_le_factorization hn0).2 le_rfl
  have hpa_σ : p ^ a ∣ ArithmeticFunction.sigma 1 n :=
    (pow_dvd_pow p hak.le).trans hσ
  have hpa_s : p ^ a ∣ aliq n := Nat.dvd_sub hpa_σ hpa_n
  have hge : a ≤ (aliq n).factorization p := (hp.pow_dvd_iff_le_factorization hs0).1 hpa_s
  have hlt : (aliq n).factorization p < a + 1 := by
    by_contra h
    push Not at h
    have h1 : p ^ (a + 1) ∣ aliq n := (hp.pow_dvd_iff_le_factorization hs0).2 h
    have h2 : p ^ (a + 1) ∣ ArithmeticFunction.sigma 1 n := (pow_dvd_pow p hak).trans hσ
    have h3 := Nat.dvd_sub h2 h1
    unfold aliq at h3
    rw [Nat.sub_sub_self (le_sigma n)] at h3
    have := (hp.pow_dvd_iff_le_factorization hn0).1 h3
    omega
  omega

/-- A product of factors `≥ 1` over a larger set is larger. -/
theorem prod_le_prod_of_subset_of_one_le' {s t : Finset ℕ} (h : s ⊆ t) (f : ℕ → ℝ)
    (hf : ∀ i ∈ t, 1 ≤ f i) : ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  rw [← Finset.prod_sdiff h]
  have h1 : 1 ≤ ∏ i ∈ t \ s, f i := by
    have := Finset.prod_le_prod (s := t \ s) (f := fun _ => (1 : ℝ)) (g := f)
      (fun _ _ => zero_le_one) (fun i hi => hf i (Finset.mem_sdiff.1 hi).1)
    simpa using this
  have h0 : 0 ≤ ∏ i ∈ s, f i :=
    Finset.prod_nonneg (fun i hi => le_trans zero_le_one (hf i (h hi)))
  nlinarith

/-- **The abundancy of `s(n)`.** If `p^k ∣ σ(n)` and `p^k ∤ n` for every prime `p ≤ w`, then
`h(s(n)) ≤ h(n) · exp(2 ∑_{p ∣ s(n), p > w} 1/p)`. -/
theorem abund_aliq_le {n w k : ℕ} (hn : 2 ≤ n)
    (hσ : ∀ p, p.Prime → p ≤ w → p ^ k ∣ ArithmeticFunction.sigma 1 n)
    (hnk : ∀ p, p.Prime → p ≤ w → ¬ p ^ k ∣ n) :
    abund (aliq n) ≤
      abund n * Real.exp (2 * ∑ p ∈ (aliq n).primeFactors.filter (w < ·), (1 : ℝ) / p) := by
  have hn0 : n ≠ 0 := by omega
  have hs0 : aliq n ≠ 0 := by have := one_le_aliq hn; omega
  set s := aliq n with hs
  rw [abund_eq_prod hs0, ← Finset.prod_filter_mul_prod_filter_not s.primeFactors (· ≤ w)]
  have hfilt : s.primeFactors.filter (fun p => ¬ p ≤ w) = s.primeFactors.filter (w < ·) :=
    Finset.filter_congr (fun p _ => not_le)
  rw [hfilt]
  -- small primes: the factors are those of `h(n)`
  have hA : ∏ p ∈ s.primeFactors.filter (· ≤ w), ppRatio p (s.factorization p) ≤ abund n := by
    have hcongr : ∏ p ∈ s.primeFactors.filter (· ≤ w), ppRatio p (s.factorization p) =
        ∏ p ∈ s.primeFactors.filter (· ≤ w), ppRatio p (n.factorization p) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      obtain ⟨hps, hpw⟩ := Finset.mem_filter.1 hp
      have hpp := Nat.prime_of_mem_primeFactors hps
      rw [hs, factorization_aliq_eq hn hpp (hσ p hpp hpw) (hnk p hpp hpw)]
    rw [hcongr, abund_eq_prod hn0]
    apply prod_le_prod_of_subset_of_one_le'
    · intro p hp
      obtain ⟨hps, hpw⟩ := Finset.mem_filter.1 hp
      have hpp := Nat.prime_of_mem_primeFactors hps
      have hv : s.factorization p ≠ 0 := by
        rw [← Finsupp.mem_support_iff, Nat.support_factorization]
        exact hps
      rw [hs, factorization_aliq_eq hn hpp (hσ p hpp hpw) (hnk p hpp hpw)] at hv
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      exact hv
    · intro p hp
      exact one_le_ppRatio (Nat.prime_of_mem_primeFactors hp) _
  -- large primes: each factor is at most `e^{2/p}`
  have hB : ∏ p ∈ s.primeFactors.filter (w < ·), ppRatio p (s.factorization p) ≤
      Real.exp (2 * ∑ p ∈ s.primeFactors.filter (w < ·), (1 : ℝ) / p) := by
    rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      exact le_trans zero_le_one
        (one_le_ppRatio (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1) _)
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1
      calc ppRatio p (s.factorization p) ≤ 1 + 2 / (p : ℝ) := ppRatio_le hpp _
        _ ≤ Real.exp (2 * (1 / (p : ℝ))) := by
          have := Real.add_one_le_exp (2 * (1 / (p : ℝ)))
          rw [mul_one_div] at this ⊢
          linarith
  have hB0 : 0 ≤ ∏ p ∈ s.primeFactors.filter (w < ·), ppRatio p (s.factorization p) :=
    Finset.prod_nonneg fun p hp =>
      le_trans zero_le_one
        (one_le_ppRatio (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1) _)
  exact mul_le_mul hA hB hB0 (abund_nonneg n)

end Principia.Common.LucaPomerance.Pollack14
