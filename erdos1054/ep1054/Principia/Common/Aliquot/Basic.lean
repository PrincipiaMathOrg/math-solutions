/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.LucaPomerance.Abundancy
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false

/-!
# Elementary facts about `s(n) = σ(n) − n` for the Chen–Zhao argument

* `sigma_mul_le`: `σ(a) b ≤ σ(a b)` (the divisors `d b`, `d ∣ a`, are divisors of `a b`);
* `aliq_mul_le`: `s(g) m ≤ s(g m)`;
* `le_aliq_of_dvd`: a proper divisor of `n` is at most `s(n)`;
* `le_two_mul_aliq`: `n ≤ 2 s(n)` for even `n ≥ 2` (`n/2` is a proper divisor);
* `exists_sq_of_sigma_odd`: an odd `n` with `σ(n)` odd is a square;
* `aliq_sq_prime`: `s(p²) = p + 1`;  `cube_le_sq_aliq_sq`: `k³ ≤ s(k²)²` for composite `k`;
* `gcd_aliq_eq`: if `v_p(n) < v_p(σ(n))` for every prime `p ∣ Q`, then
  `gcd(s(n), Q) = gcd(n, Q)` — the congruence behind Chen–Zhao's `s(m) ≡ −m (mod 2M)`.

Everything is stated with Mathlib's `ArithmeticFunction.sigma 1` and the library's `aliq`, so it
is campaign-agnostic.
-/

namespace Principia.Common.Aliquot

open Finset
open Principia.Common.LucaPomerance.Aliquot (aliq le_sigma)

theorem aliq_one : aliq 1 = 0 := by
  simp [aliq]

/-- `σ(n) = s(n) + n`. -/
theorem sigma_eq_aliq_add (n : ℕ) : ArithmeticFunction.sigma 1 n = aliq n + n := by
  unfold aliq
  have := le_sigma n
  omega

/-- `σ(a) · b ≤ σ(a b)`. -/
theorem sigma_mul_le (a b : ℕ) (hb : 0 < b) :
    ArithmeticFunction.sigma 1 a * b ≤ ArithmeticFunction.sigma 1 (a * b) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rw [ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply, Finset.sum_mul]
  have hinj : Set.InjOn (fun d : ℕ => d * b) (a.divisors : Set ℕ) :=
    fun x _ y _ h => Nat.eq_of_mul_eq_mul_right hb h
  rw [← Finset.sum_image (f := fun d : ℕ => d) hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    rw [Nat.mem_divisors] at hd ⊢
    exact ⟨Nat.mul_dvd_mul_right hd.1 b, Nat.mul_ne_zero hd.2 hb.ne'⟩
  · intro _ _ _
    exact Nat.zero_le _

/-- `s(g) · m ≤ s(g m)`. -/
theorem aliq_mul_le (g m : ℕ) (hm : 0 < m) : aliq g * m ≤ aliq (g * m) := by
  unfold aliq
  rw [Nat.sub_mul]
  exact Nat.sub_le_sub_right (sigma_mul_le g m hm) _

/-- A proper divisor of `n` is at most `s(n)`. -/
theorem le_aliq_of_dvd {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) (hdn : d < n) : d ≤ aliq n := by
  have h : d + n ≤ ArithmeticFunction.sigma 1 n := by
    rw [ArithmeticFunction.sigma_one_apply]
    have hsub : ({d, n} : Finset ℕ) ⊆ n.divisors := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Nat.mem_divisors.2 ⟨hd, hn.ne'⟩
      · exact Nat.mem_divisors_self _ hn.ne'
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun x : ℕ => x) hsub
      (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_pair hdn.ne] at this
    exact this
  unfold aliq
  omega

/-- `n ≤ 2 s(n)` for even `n ≥ 2`. -/
theorem le_two_mul_aliq {n : ℕ} (hn : 2 ≤ n) (he : 2 ∣ n) : n ≤ 2 * aliq n := by
  have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
  have h := le_aliq_of_dvd (by omega) (Nat.div_dvd_of_dvd he) hlt
  have h2 : 2 * (n / 2) = n := Nat.mul_div_cancel' he
  omega

/-- For odd `p`, `∑_{j ≤ k} p^j ≡ k + 1 (mod 2)`. -/
theorem sum_range_pow_mod_two {p : ℕ} (hp : p % 2 = 1) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), p ^ j) % 2 = (k + 1) % 2 := by
  rw [Finset.sum_nat_mod,
    Finset.sum_congr rfl (fun j _ => by rw [Nat.pow_mod, hp, one_pow])]
  simp

/-- **An odd `n` with `σ(n)` odd is a square.** (Every prime factor is odd, and
`σ(p^a) ≡ a + 1 (mod 2)`, so every exponent is even.) -/
theorem exists_sq_of_sigma_odd {n : ℕ} (hn : n ≠ 0) (hodd : ¬ 2 ∣ n)
    (hσ : Odd (ArithmeticFunction.sigma 1 n)) : ∃ k, n = k ^ 2 := by
  have hev : ∀ p ∈ n.primeFactors, Even (n.factorization p) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := fun h => hodd (h ▸ Nat.dvd_of_mem_primeFactors hp)
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hpp.odd_of_ne_two hp2)
    have hdvd : ArithmeticFunction.sigma 1 (p ^ n.factorization p) ∣
        ArithmeticFunction.sigma 1 n := by
      conv_rhs => rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn,
        Finsupp.prod]
      exact Finset.dvd_prod_of_mem (fun q => ArithmeticFunction.sigma 1 (q ^ n.factorization q))
        (by rw [Nat.support_factorization]; exact hp)
    have hfac : Odd (ArithmeticFunction.sigma 1 (p ^ n.factorization p)) := by
      obtain ⟨c, hc⟩ := hdvd
      have h := hσ
      rw [hc, Nat.odd_mul] at h
      exact h.1
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hpp, Nat.odd_iff,
      sum_range_pow_mod_two hpodd] at hfac
    rw [Nat.even_iff]
    omega
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  rw [← Finset.prod_pow]
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn, Finsupp.prod,
    Nat.support_factorization]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  rw [← pow_mul, Nat.div_mul_cancel (hev p hp).two_dvd]

/-- `s(p²) = p + 1` for a prime `p`. -/
theorem aliq_sq_prime {p : ℕ} (hp : p.Prime) : aliq (p ^ 2) = p + 1 := by
  unfold aliq
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
  omega

/-- `k³ ≤ s(k²)²` for composite `k ≥ 2`: with `a = minFac k`, `b = k/a ≥ a`, the proper divisor
`k b` of `k²` satisfies `(k b)² ≥ k² · a b = k³`. -/
theorem cube_le_sq_aliq_sq {k : ℕ} (hk : 2 ≤ k) (hnp : ¬ k.Prime) :
    k ^ 3 ≤ aliq (k ^ 2) ^ 2 := by
  set a := k.minFac with ha
  have hk0 : 0 < k := by omega
  have ha2 : 2 ≤ a := (Nat.minFac_prime (by omega)).two_le
  have hadvd : a ∣ k := Nat.minFac_dvd k
  have hsq : a ^ 2 ≤ k := Nat.minFac_sq_le_self hk0 hnp
  set b := k / a with hb
  have hab : a * b = k := Nat.mul_div_cancel' hadvd
  have hab' : a ≤ b := by
    by_contra h
    push Not at h
    have : a * b < a * a := Nat.mul_lt_mul_of_pos_left h (by omega)
    nlinarith
  have hbk : b < k := by
    rw [← hab]
    nlinarith
  have hdvd : k * b ∣ k ^ 2 := by
    rw [sq]
    exact Nat.mul_dvd_mul_left k (Dvd.intro_left a hab)
  have hlt : k * b < k ^ 2 := by
    rw [sq]
    exact Nat.mul_lt_mul_of_pos_left hbk hk0
  have hle : k * b ≤ aliq (k ^ 2) := le_aliq_of_dvd (by positivity) hdvd hlt
  have hbb : k ≤ b * b := by
    rw [← hab]
    exact Nat.mul_le_mul_right b hab'
  calc k ^ 3 = k ^ 2 * k := by ring
    _ ≤ k ^ 2 * (b * b) := Nat.mul_le_mul_left _ hbb
    _ = (k * b) ^ 2 := by ring
    _ ≤ aliq (k ^ 2) ^ 2 := Nat.pow_le_pow_left hle 2

/-- **`gcd(s(n), Q) = gcd(n, Q)`** when `v_p(n) < v_p(σ(n))` for every prime `p ∣ Q`. -/
theorem gcd_aliq_eq {n Q : ℕ} (hn : 2 ≤ n) (hQ : 0 < Q)
    (h : ∀ p : ℕ, p.Prime → p ∣ Q →
      n.factorization p < (ArithmeticFunction.sigma 1 n).factorization p) :
    Nat.gcd (aliq n) Q = Nat.gcd n Q := by
  have hn0 : n ≠ 0 := by omega
  have hs0 : aliq n ≠ 0 := by
    have := Principia.Common.LucaPomerance.Pollack14.one_le_aliq hn
    omega
  have hσ0 : ArithmeticFunction.sigma 1 n ≠ 0 := by
    have := le_sigma n
    omega
  apply Nat.eq_of_factorization_eq (Nat.gcd_pos_of_pos_right _ hQ).ne'
    (Nat.gcd_pos_of_pos_right _ hQ).ne'
  intro p
  rw [Nat.factorization_gcd hs0 hQ.ne', Nat.factorization_gcd hn0 hQ.ne', Finsupp.inf_apply,
    Finsupp.inf_apply]
  by_cases hp : p.Prime
  · by_cases hpQ : p ∣ Q
    · have hlt := h p hp hpQ
      have hdσ : p ^ (n.factorization p + 1) ∣ ArithmeticFunction.sigma 1 n :=
        (hp.pow_dvd_iff_le_factorization hσ0).2 hlt
      have hnd : ¬ p ^ (n.factorization p + 1) ∣ n := Nat.pow_succ_factorization_not_dvd hn0 hp
      rw [Principia.Common.LucaPomerance.Pollack14.factorization_aliq_eq hn hp hdσ hnd]
    · rw [Nat.factorization_eq_zero_of_not_dvd hpQ]
      simp
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

end Principia.Common.Aliquot
