/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

/-!
# Luca–Pomerance Lemma 2.1: the algebraic part

Pure divisibility, no density input. With `σ = σ₁`, `g = gcd(n, σ(n))`, `s = σ(n) − n`:

* `iii_of_i`, `iv_of_i`: if `v_p(n) < v_p(σ(n))` for every prime `p ≤ y`, then every prime
  `p ≤ y` divides `σ(n)/g`, and every prime factor of `s/g` exceeds `y`. (LP's own proof of their
  part (4) opens with exactly this reduction.)
* `smooth_gcd_of_forall`: `g` is `y`-smooth as soon as no prime `r > y` divides both `n` and
  `σ(n)`.
* `omegaP p n = #{q ∥ n prime : p ∣ q + 1}` and `pow_omegaP_dvd_sigma`: `p^{ω_p(n)} ∣ σ(n)`,
  hence `omegaP_le_factorization_of_fail`: if `v_p(σ(n)) ≤ v_p(n)` then `ω_p(n) ≤ v_p(n)`.
* `exists_prime_pow_of_dvd_sigma`: a prime `r ∣ σ(n)` divides `σ(q^{v_q(n)})` for some `q ∣ n`;
  `sigma_prime_pow_lt`: `σ(q^k) < q^{k+1}`.
-/

namespace Principia.Common.LucaPomerance.LP21

open Finset ArithmeticFunction

/-- `n ≤ σ(n)` for `n ≠ 0`. -/
theorem le_sigma_one {n : ℕ} (hn : n ≠ 0) : n ≤ sigma 1 n := by
  rw [sigma_one_apply]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le i) (Nat.mem_divisors_self n hn)

/-- **(i) ⟹ (iii).** -/
theorem iii_of_i (n : ℕ) (y : ℝ)
    (hi : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y → n.factorization p < (sigma 1 n).factorization p) :
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y → p ∣ sigma 1 n / Nat.gcd n (sigma 1 n) := by
  intro p hp hpy
  have h := hi p hp hpy
  have hn : n ≠ 0 := by
    rintro rfl
    simp at h
  have hσ : sigma 1 n ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  set a := n.factorization p
  have hpa : p ^ (a + 1) ∣ sigma 1 n := (hp.pow_dvd_iff_le_factorization hσ).mpr h
  by_contra hnd
  have hcop : Nat.Coprime (p ^ (a + 1)) (sigma 1 n / Nat.gcd n (sigma 1 n)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
  have hsplit : sigma 1 n = sigma 1 n / Nat.gcd n (sigma 1 n) * Nat.gcd n (sigma 1 n) :=
    (Nat.div_mul_cancel (Nat.gcd_dvd_right n (sigma 1 n))).symm
  have hg : p ^ (a + 1) ∣ Nat.gcd n (sigma 1 n) := by
    rw [hsplit] at hpa
    exact hcop.dvd_of_dvd_mul_left hpa
  exact Nat.pow_succ_factorization_not_dvd hn hp (hg.trans (Nat.gcd_dvd_left n _))

/-- **(i) ⟹ (iv).** -/
theorem iv_of_i (n : ℕ) (y : ℝ)
    (hi : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y → n.factorization p < (sigma 1 n).factorization p) :
    ∀ p ∈ ((sigma 1 n - n) / Nat.gcd n (sigma 1 n)).primeFactors, y < (p : ℝ) := by
  intro p hpmem
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  have hpd : p ∣ (sigma 1 n - n) / Nat.gcd n (sigma 1 n) := Nat.dvd_of_mem_primeFactors hpmem
  by_contra hpy'
  have hpy : (p : ℝ) ≤ y := not_lt.mp hpy'
  have h := hi p hp hpy
  have hn : n ≠ 0 := by
    rintro rfl
    simp at h
  have hσ : sigma 1 n ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  set a := n.factorization p
  set σn := sigma 1 n
  set g := Nat.gcd n σn
  have hpa1 : p ^ (a + 1) ∣ σn := (hp.pow_dvd_iff_le_factorization hσ).mpr h
  have hpa_n : p ^ a ∣ n := Nat.ordProj_dvd n p
  have hpa_σ : p ^ a ∣ σn := (pow_dvd_pow p (Nat.le_succ a)).trans hpa1
  have hpa_g : p ^ a ∣ g := Nat.dvd_gcd hpa_n hpa_σ
  have hgs : g ∣ σn - n := Nat.dvd_sub (Nat.gcd_dvd_right n σn) (Nat.gcd_dvd_left n σn)
  have hs : σn - n = (σn - n) / g * g := (Nat.div_mul_cancel hgs).symm
  have hps : p ^ (a + 1) ∣ σn - n := by
    rw [hs, pow_succ, mul_comm (p ^ a) p]
    exact Nat.mul_dvd_mul hpd hpa_g
  have hle : n ≤ σn := le_sigma_one hn
  have hsub : σn - (σn - n) = n := Nat.sub_sub_self hle
  have hpn : p ^ (a + 1) ∣ n := by
    rw [← hsub]
    exact Nat.dvd_sub hpa1 hps
  exact Nat.pow_succ_factorization_not_dvd hn hp hpn

/-- **(ii) from the absence of a large common prime.** -/
theorem smooth_gcd_of_forall (n : ℕ) (y : ℝ)
    (h : ∀ r : ℕ, r.Prime → y < (r : ℝ) → r ∣ n → ¬ r ∣ sigma 1 n) :
    ∀ r ∈ (Nat.gcd n (sigma 1 n)).primeFactors, (r : ℝ) ≤ y := by
  intro r hr
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  have hrd : r ∣ Nat.gcd n (sigma 1 n) := Nat.dvd_of_mem_primeFactors hr
  by_contra hlt'
  have hlt : y < (r : ℝ) := not_le.mp hlt'
  exact h r hrp hlt (hrd.trans (Nat.gcd_dvd_left _ _)) (hrd.trans (Nat.gcd_dvd_right _ _))

/-! ## `ω_p(n)` and `p^{ω_p(n)} ∣ σ(n)` -/

/-- `ω_p(n) = #{q prime : q ∥ n, p ∣ q + 1}`. -/
def omegaP (p n : ℕ) : ℕ :=
  (n.primeFactors.filter (fun q => p ∣ q + 1 ∧ n.factorization q = 1)).card

/-- `σ(n) = ∏_{q ∣ n} σ(q^{v_q(n)})`. -/
theorem sigma_eq_prod (n : ℕ) (hn : n ≠ 0) :
    sigma 1 n = ∏ q ∈ n.primeFactors, sigma 1 (q ^ n.factorization q) := by
  rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hn, Finsupp.prod,
    Nat.support_factorization]

theorem sigma_one_prime {q : ℕ} (hq : q.Prime) : sigma 1 q = q + 1 := by
  have h := sigma_one_apply_prime_pow (i := 1) hq
  rw [pow_one] at h
  rw [h, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, add_comm]

theorem pow_omegaP_dvd_sigma (p n : ℕ) (hn : n ≠ 0) : p ^ omegaP p n ∣ sigma 1 n := by
  classical
  set S := n.primeFactors.filter (fun q => p ∣ q + 1 ∧ n.factorization q = 1)
  have h1 : p ^ S.card = ∏ _q ∈ S, p := by rw [Finset.prod_const]
  have h2 : ∏ _q ∈ S, p ∣ ∏ q ∈ S, sigma 1 (q ^ n.factorization q) := by
    apply Finset.prod_dvd_prod_of_dvd
    intro q hq
    rw [Finset.mem_filter] at hq
    rw [hq.2.2, pow_one, sigma_one_prime (Nat.prime_of_mem_primeFactors hq.1)]
    exact hq.2.1
  have h3 : ∏ q ∈ S, sigma 1 (q ^ n.factorization q) ∣
      ∏ q ∈ n.primeFactors, sigma 1 (q ^ n.factorization q) :=
    Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  unfold omegaP
  rw [sigma_eq_prod n hn, h1]
  exact h2.trans h3

/-- If `(i)` fails at `p` (`v_p(σ(n)) ≤ v_p(n)`), then `ω_p(n) ≤ v_p(n)`. -/
theorem omegaP_le_factorization_of_fail {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hfail : (sigma 1 n).factorization p ≤ n.factorization p) :
    omegaP p n ≤ n.factorization p := by
  have hσ : sigma 1 n ≠ 0 := by
    have := le_sigma_one hn
    omega
  have h := (hp.pow_dvd_iff_le_factorization hσ).mp (pow_omegaP_dvd_sigma p n hn)
  omega

/-! ## Prime divisors of `σ(n)` -/

/-- A prime dividing `σ(n)` divides `σ(q^{v_q(n)})` for some prime `q ∣ n`. -/
theorem exists_prime_pow_of_dvd_sigma {n r : ℕ} (hn : n ≠ 0) (hr : r.Prime)
    (hrd : r ∣ sigma 1 n) :
    ∃ q ∈ n.primeFactors, r ∣ sigma 1 (q ^ n.factorization q) := by
  rw [sigma_eq_prod n hn] at hrd
  exact (Prime.dvd_finsetProd_iff hr.prime _).mp hrd

/-- `σ(q^k) < q^{k+1}` for `q ≥ 2`. -/
theorem sigma_prime_pow_lt {q : ℕ} (hq : q.Prime) (k : ℕ) : sigma 1 (q ^ k) < q ^ (k + 1) := by
  rw [sigma_one_apply_prime_pow hq]
  exact Nat.geomSum_lt hq.two_le (fun i hi => Finset.mem_range.mp hi)

end Principia.Common.LucaPomerance.LP21
