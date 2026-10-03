/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Sieve.BrunTitchmarshAP
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

/-!
# Luca–Pomerance, Lemma 2.5: large primes of `σ(n)` have reciprocal sum `≤ 1` almost always

**Statement** (`lp_lemma25_density`). Put
`S(n) = ∑_{r ∣ σ(n), r prime, r > (log log n)^2} 1/r`. Then `#{n ≤ X : S(n) > 1} = o(X)`.

Source: F. Luca, C. Pomerance, *The range of the sum-of-proper-divisors function*, Acta Arith.
168 (2015), Lemma 2.5 (via De Koninck–Luca). Nothing here is new mathematics; the proof is the
standard first-moment argument, arranged so that each step is an elementary inequality.

## Route

Fix `X`, put `w = (log X)/2`, `v = log w`, `z = v^2`.

1. **Uniform threshold.** For `√X < n ≤ X` we have `log n > w`, so `(log log n)^2 ≥ z`, hence
   `S(n) ≤ T_z(σ(n))` where `T_z(m) = ∑_{r ∣ m, r > z} 1/r` (`tailRecip`). The `n ≤ √X` cost
   `√X`.
2. **Pointwise decomposition** (`tailRecip_sigma_le`). If no `m ≥ 2` with `m^6 > z` has
   `m^2 ∣ n`, then every prime `r > z` of `σ(n) = ∏ σ(q^a)` divides `σ(q) = q + 1` for some
   `q ∣ n`: a factor `σ(q^a)` with `a ≥ 2` has `σ(q^a) ≤ q^{2a} ≤ m^6 ≤ z` for `m = q^{⌊a/2⌋}`.
   So `T_z(σ(n)) ≤ F_z(n) := ∑_{q ∣ n} T_z(q+1)`.
3. **Squareful exceptions** (`card_squareful_le`): `≤ ∑_{m > k} X/m^2 ≤ 2X/(k+1)` whenever
   `k^6 ≤ z` (Mathlib's `sum_Ioo_inv_sq_le`).
4. **First moment** (`sum_Icc_sum_primeFactors_le`, `sum_tailRecip_div_le`):
   `∑_{n ≤ X} F_z(n) ≤ X ∑_{q ≤ X} T_z(q+1)/q = X ∑_{r > z} (1/r) G(r, X)`, where
   `G(r, X) = ∑_{q ≤ X, q ≡ −1 (r)} 1/q`.
5. **Brun–Titchmarsh in dyadic blocks** (`classRecip_le`): on `(r2^j, r2^{j+1}]`,
   `π(r2^{j+1}; r, −1) ≤ 2008 · r2^{j+1}/((r−1)(j+1) log 2)`
   (`Principia.Common.BrunTitchmarshAP.brun_titchmarsh_ap`), so the block contributes
   `≤ 4016/((r−1)(j+1) log 2)`; summing `j < log₂ X + 1` gives a harmonic number, and the only
   `q ≤ r` is `q = r − 1`. Hence `G(r, X) ≪ (1 + log log X)/r` **with no `log r` loss**, because
   the blocks start at `r` itself.
6. So the mean of `F_z` is `≪ log log X / z ≪ 1/v`, Markov bounds `#{F_z > 1}`, and altogether
   `#{n ≤ X : S(n) > 1}/X ≤ 144583 / v^{1/3} → 0` (`card_lp_div_le`).
-/

namespace Principia.Common.LucaPomerance.Lemma25

open Finset Filter
open scoped Topology

/-! ## Definitions -/

/-- `T_z(m) = ∑_{r ∣ m, r prime, r > z} 1/r`. -/
noncomputable def tailRecip (z : ℝ) (m : ℕ) : ℝ :=
  ∑ r ∈ m.primeFactors.filter (fun r : ℕ => z < (r : ℝ)), (1 : ℝ) / r

/-- The Luca–Pomerance sum `S(n) = ∑_{r ∣ σ(n), r prime, r > (log log n)^2} 1/r`. -/
noncomputable def lpSum (n : ℕ) : ℝ :=
  ∑ r ∈ (ArithmeticFunction.sigma 1 n).primeFactors.filter
      (fun r : ℕ => (Real.log (Real.log (n : ℝ))) ^ 2 < (r : ℝ)), (1 : ℝ) / r

/-- `G(r, N) = ∑_{q ≤ N, q prime, r ∣ q + 1} 1/q`. -/
noncomputable def classRecip (r N : ℕ) : ℝ :=
  ∑ q ∈ (Finset.Iic N).filter (fun q => q.Prime ∧ r ∣ q + 1), (1 : ℝ) / q

theorem tailRecip_nonneg (z : ℝ) (m : ℕ) : 0 ≤ tailRecip z m :=
  Finset.sum_nonneg (fun _ _ => by positivity)

/-! ## Elementary helpers -/

/-- A sum of nonnegative terms over a `biUnion` is at most the sum of the sums. -/
theorem sum_biUnion_le_of_nonneg {ι : Type*} (s : Finset ι)
    (t : ι → Finset ℕ) (f : ℕ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have h := Finset.sum_union_inter (s₁ := t i) (s₂ := s.biUnion t) (f := f)
    have h0 : 0 ≤ ∑ x ∈ t i ∩ s.biUnion t, f x := Finset.sum_nonneg (fun x _ => hf x)
    linarith

/-- `#{1 ≤ n ≤ N : d ∣ n} ≤ N/d`. -/
theorem card_multiples_le (N d : ℕ) :
    ((((Finset.Icc 1 N).filter (fun n => d ∣ n)).card : ℕ) : ℝ) ≤ (N : ℝ) / d := by
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]
  exact Nat.cast_div_le

/-- Markov: `#{n ∈ S : f n > 1} ≤ ∑_{n ∈ S} f n` for `f ≥ 0`. -/
theorem card_filter_one_lt_le (S : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ n ∈ S, 0 ≤ f n) :
    (((S.filter (fun n => 1 < f n)).card : ℕ) : ℝ) ≤ ∑ n ∈ S, f n := by
  calc (((S.filter (fun n => 1 < f n)).card : ℕ) : ℝ)
      = ∑ n ∈ S.filter (fun n => 1 < f n), (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ n ∈ S.filter (fun n => 1 < f n), f n :=
        Finset.sum_le_sum (fun n hn => (Finset.mem_filter.mp hn).2.le)
    _ ≤ ∑ n ∈ S, f n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun n hn _ => hf n hn)

/-- `σ(d) ≤ d^2`. -/
theorem sigma_le_sq (d : ℕ) : ArithmeticFunction.sigma 1 d ≤ d ^ 2 := by
  rw [ArithmeticFunction.sigma_one_apply]
  calc ∑ e ∈ d.divisors, e ≤ ∑ _e ∈ d.divisors, d :=
        Finset.sum_le_sum (fun e he => Nat.divisor_le he)
    _ = d.divisors.card * d := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ d * d := Nat.mul_le_mul_right d (Nat.card_divisors_le_self d)
    _ = d ^ 2 := (sq d).symm

/-- `σ(q) = q + 1` for a prime `q`. -/
theorem sigma_prime (q : ℕ) (hq : q.Prime) : ArithmeticFunction.sigma 1 q = q + 1 := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.Prime.divisors hq, Finset.sum_pair hq.one_lt.ne]
  omega

/-! ## Step 2: the pointwise decomposition -/

/-- **Pointwise decomposition.** If every `m ≥ 2` with `m^2 ∣ n` has `m^6 ≤ z`, then every prime
`r > z` of `σ(n)` divides `q + 1` for a prime `q ∣ n`, so `T_z(σ(n)) ≤ ∑_{q ∣ n} T_z(q + 1)`. -/
theorem tailRecip_sigma_le (n : ℕ) (hn : n ≠ 0) (z : ℝ)
    (hW : ∀ m : ℕ, 2 ≤ m → m ^ 2 ∣ n → ((m : ℝ)) ^ 6 ≤ z) :
    tailRecip z (ArithmeticFunction.sigma 1 n) ≤ ∑ q ∈ n.primeFactors, tailRecip z (q + 1) := by
  classical
  unfold tailRecip
  have hsub : (ArithmeticFunction.sigma 1 n).primeFactors.filter (fun r : ℕ => z < (r : ℝ)) ⊆
      n.primeFactors.biUnion
        (fun q => (q + 1).primeFactors.filter (fun r : ℕ => z < (r : ℝ))) := by
    intro r hr
    rw [Finset.mem_filter, Nat.mem_primeFactors] at hr
    obtain ⟨⟨hrp, hrd, _⟩, hzr⟩ := hr
    have hfac := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
      (ArithmeticFunction.sigma 1) ArithmeticFunction.isMultiplicative_sigma hn
    rw [hfac, Finsupp.prod, Nat.support_factorization] at hrd
    obtain ⟨q, hq, hrq⟩ := (Nat.Prime.prime hrp).exists_mem_finset_dvd hrd
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have ha1 : 0 < n.factorization q :=
      Nat.Prime.factorization_pos_of_dvd hqp hn (Nat.dvd_of_mem_primeFactors hq)
    rw [Finset.mem_biUnion]
    refine ⟨q, hq, ?_⟩
    rw [Finset.mem_filter, Nat.mem_primeFactors]
    refine ⟨⟨hrp, ?_, by omega⟩, hzr⟩
    by_cases ha : n.factorization q = 1
    · rw [ha, pow_one, sigma_prime q hqp] at hrq
      exact hrq
    · exfalso
      have ha2 : 2 ≤ n.factorization q := by omega
      have hm2 : 2 ≤ q ^ (n.factorization q / 2) :=
        calc 2 ≤ q := hqp.two_le
          _ = q ^ 1 := (pow_one q).symm
          _ ≤ q ^ (n.factorization q / 2) := Nat.pow_le_pow_right hqp.pos (by omega)
      have hmdvd : (q ^ (n.factorization q / 2)) ^ 2 ∣ n := by
        rw [← pow_mul]
        exact (Nat.pow_dvd_pow q (by omega)).trans (Nat.ordProj_dvd n q)
      have hmz := hW _ hm2 hmdvd
      have hsig_pos : 0 < ArithmeticFunction.sigma 1 (q ^ n.factorization q) :=
        ArithmeticFunction.sigma_pos 1 _ (pow_ne_zero _ hqp.ne_zero)
      have hr_le : r ≤ ArithmeticFunction.sigma 1 (q ^ n.factorization q) :=
        Nat.le_of_dvd hsig_pos hrq
      have hqa : q ^ n.factorization q ≤ (q ^ (n.factorization q / 2)) ^ 3 := by
        rw [← pow_mul]
        exact Nat.pow_le_pow_right hqp.pos (by omega)
      have hr6 : r ≤ (q ^ (n.factorization q / 2)) ^ 6 :=
        calc r ≤ ArithmeticFunction.sigma 1 (q ^ n.factorization q) := hr_le
          _ ≤ (q ^ n.factorization q) ^ 2 := sigma_le_sq _
          _ ≤ ((q ^ (n.factorization q / 2)) ^ 3) ^ 2 := Nat.pow_le_pow_left hqa 2
          _ = (q ^ (n.factorization q / 2)) ^ 6 := by rw [← pow_mul]
      have hr6' : (r : ℝ) ≤ ((q ^ (n.factorization q / 2) : ℕ) : ℝ) ^ 6 := by
        exact_mod_cast hr6
      linarith
  calc ∑ r ∈ (ArithmeticFunction.sigma 1 n).primeFactors.filter (fun r : ℕ => z < (r : ℝ)),
        (1 : ℝ) / r
      ≤ ∑ r ∈ n.primeFactors.biUnion
          (fun q => (q + 1).primeFactors.filter (fun r : ℕ => z < (r : ℝ))), (1 : ℝ) / r :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ q ∈ n.primeFactors,
          ∑ r ∈ (q + 1).primeFactors.filter (fun r : ℕ => z < (r : ℝ)), (1 : ℝ) / r :=
        sum_biUnion_le_of_nonneg _ _ _ (fun _ => by positivity)

/-! ## Step 3: squareful exceptions -/

open Classical in
/-- **Squareful exceptions.** If `k^6 ≤ z`, then
`#{n ≤ N : m^2 ∣ n for some m ≥ 2 with m^6 > z} ≤ N · 2/(k+1)`. -/
theorem card_squareful_le (N k : ℕ) (z : ℝ) (hk : ((k : ℝ)) ^ 6 ≤ z) :
    ((((Finset.Icc 1 N).filter
        (fun n => ∃ m : ℕ, 2 ≤ m ∧ m ^ 2 ∣ n ∧ z < ((m : ℝ)) ^ 6)).card : ℕ) : ℝ)
      ≤ (N : ℝ) * (2 / ((k : ℝ) + 1)) := by
  classical
  have hsub : (Finset.Icc 1 N).filter
        (fun n => ∃ m : ℕ, 2 ≤ m ∧ m ^ 2 ∣ n ∧ z < ((m : ℝ)) ^ 6) ⊆
      (Finset.Ioo k (N + 1)).biUnion
        (fun m => (Finset.Icc 1 N).filter (fun n => m ^ 2 ∣ n)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, m, hm2, hmd, hmz⟩ := hn
    rw [Finset.mem_biUnion]
    refine ⟨m, ?_, ?_⟩
    · rw [Finset.mem_Ioo]
      constructor
      · by_contra hkm
        have hkm2 : m ≤ k := Nat.le_of_not_lt hkm
        have hkm' : ((m : ℝ)) ^ 6 ≤ ((k : ℝ)) ^ 6 :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast hkm2) 6
        linarith
      · have h1 : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
        have h2 : m ^ 2 ≤ n := Nat.le_of_dvd (by omega) hmd
        omega
    · rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hn1, hnN⟩, hmd⟩
  have hcard := Finset.card_le_card hsub
  have hbu := Finset.card_biUnion_le (s := Finset.Ioo k (N + 1))
    (t := fun m => (Finset.Icc 1 N).filter (fun n => m ^ 2 ∣ n))
  calc ((((Finset.Icc 1 N).filter
        (fun n => ∃ m : ℕ, 2 ≤ m ∧ m ^ 2 ∣ n ∧ z < ((m : ℝ)) ^ 6)).card : ℕ) : ℝ)
      ≤ ∑ m ∈ Finset.Ioo k (N + 1),
          ((((Finset.Icc 1 N).filter (fun n => m ^ 2 ∣ n)).card : ℕ) : ℝ) := by
        exact_mod_cast hcard.trans hbu
    _ ≤ ∑ m ∈ Finset.Ioo k (N + 1), (N : ℝ) * ((m : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum
        intro m _
        have h := card_multiples_le N (m ^ 2)
        push_cast at h
        rw [div_eq_mul_inv] at h
        exact h
    _ = (N : ℝ) * ∑ m ∈ Finset.Ioo k (N + 1), ((m : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (N : ℝ) * (2 / ((k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le k (N + 1)) (by positivity)

/-! ## Step 4: the first moment -/

/-- `∑_{n ≤ N} ∑_{q ∣ n} g(q) ≤ N ∑_{q ≤ N prime} g(q)/q` for `g ≥ 0`. -/
theorem sum_Icc_sum_primeFactors_le (N : ℕ) (g : ℕ → ℝ) (hg : ∀ q, 0 ≤ g q) :
    ∑ n ∈ Finset.Icc 1 N, ∑ q ∈ n.primeFactors, g q ≤
      (N : ℝ) * ∑ q ∈ (Finset.Iic N).filter Nat.Prime, g q / q := by
  classical
  rw [Finset.sum_comm' (t' := (Finset.Iic N).filter Nat.Prime)
    (s' := fun q => (Finset.Icc 1 N).filter (fun n => q ∣ n))]
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q _
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc := card_multiples_le N q
    calc ((((Finset.Icc 1 N).filter (fun n => q ∣ n)).card : ℕ) : ℝ) * g q
        ≤ ((N : ℝ) / q) * g q := mul_le_mul_of_nonneg_right hc (hg q)
      _ = (N : ℝ) * (g q / q) := by ring
  · intro n q
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_Iic, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp, hd, _⟩
      exact ⟨⟨⟨h1, h2⟩, hd⟩, le_trans (Nat.le_of_dvd (by omega) hd) h2, hp⟩
    · rintro ⟨⟨⟨h1, h2⟩, hd⟩, _, hp⟩
      exact ⟨⟨h1, h2⟩, hp, hd, by omega⟩

/-- For `r ≥ 2`, `r ∣ q + 1` means `q ≡ r − 1 (mod r)`. -/
theorem mod_of_dvd_succ {r q : ℕ} (hr : 2 ≤ r) (h : r ∣ q + 1) : q % r = (r - 1) % r := by
  obtain ⟨t, ht⟩ := h
  rcases t with _ | s
  · simp at ht
  · rw [mul_add, mul_one] at ht
    have hq : q = (r - 1) + r * s := by
      generalize r * s = w at ht ⊢
      omega
    rw [hq, Nat.add_mul_mod_self_left]

/-! ## Step 5: Brun–Titchmarsh in dyadic blocks -/

/-- **One dyadic block.** For a prime `r`,
`∑_{r2^j < q ≤ r2^{j+1}, q prime, r ∣ q+1} 1/q ≤ 4016/((r−1)(j+1) log 2)`. -/
theorem block_bound (r : ℕ) (hr : r.Prime) (j : ℕ) :
    ∑ q ∈ (Finset.Ioc (r * 2 ^ j) (r * 2 ^ (j + 1))).filter (fun q => q.Prime ∧ r ∣ q + 1),
        (1 : ℝ) / q
      ≤ 4016 / (((r : ℝ) - 1) * ((j : ℝ) + 1) * Real.log 2) := by
  classical
  have hr2 : 2 ≤ r := hr.two_le
  have hr2R : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  have hr0 : (0 : ℝ) < r := by linarith
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  set x : ℝ := ((r * 2 ^ (j + 1) : ℕ) : ℝ) with hx
  have hxr : (r : ℝ) < x := by
    rw [hx]
    push_cast
    have : (2 : ℝ) ≤ 2 ^ (j + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  have hBT := Principia.Common.BrunTitchmarshAP.brun_titchmarsh_ap r (r - 1) (by omega) x hxr
  have hfloor : ⌊x⌋₊ = r * 2 ^ (j + 1) := by rw [hx, Nat.floor_natCast]
  rw [hfloor] at hBT
  have htot : ((r.totient : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.totient_prime hr]
    push_cast [Nat.one_le_iff_ne_zero.mpr hr.ne_zero]
    ring
  have hxdiv : x / r = 2 ^ (j + 1) := by
    rw [hx]
    push_cast
    field_simp
  have hlogx : Real.log (x / r) = ((j : ℝ) + 1) * Real.log 2 := by
    rw [hxdiv, Real.log_pow]
    push_cast
    ring
  rw [htot, hlogx] at hBT
  have hcard : ((Finset.Ioc (r * 2 ^ j) (r * 2 ^ (j + 1))).filter
      (fun q => q.Prime ∧ r ∣ q + 1)).card ≤
      ((Finset.Iic (r * 2 ^ (j + 1))).filter (fun p => p.Prime ∧ p % r = (r - 1) % r)).card := by
    apply Finset.card_le_card
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hq
    rw [Finset.mem_filter, Finset.mem_Iic]
    exact ⟨hq.1.2, hq.2.1, mod_of_dvd_succ hr2 hq.2.2⟩
  have hterm : ∀ q ∈ (Finset.Ioc (r * 2 ^ j) (r * 2 ^ (j + 1))).filter
      (fun q => q.Prime ∧ r ∣ q + 1), (1 : ℝ) / q ≤ 1 / ((r : ℝ) * 2 ^ j) := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hq
    apply one_div_le_one_div_of_le (by positivity)
    have : r * 2 ^ j ≤ q := hq.1.1.le
    exact_mod_cast this
  calc ∑ q ∈ (Finset.Ioc (r * 2 ^ j) (r * 2 ^ (j + 1))).filter (fun q => q.Prime ∧ r ∣ q + 1),
        (1 : ℝ) / q
      ≤ ∑ q ∈ (Finset.Ioc (r * 2 ^ j) (r * 2 ^ (j + 1))).filter (fun q => q.Prime ∧ r ∣ q + 1),
          (1 : ℝ) / ((r : ℝ) * 2 ^ j) := Finset.sum_le_sum hterm
    _ = (((Finset.Ioc (r * 2 ^ j) (r * 2 ^ (j + 1))).filter
          (fun q => q.Prime ∧ r ∣ q + 1)).card : ℝ) * (1 / ((r : ℝ) * 2 ^ j)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((Finset.Iic (r * 2 ^ (j + 1))).filter
          (fun p => p.Prime ∧ p % r = (r - 1) % r)).card : ℝ) * (1 / ((r : ℝ) * 2 ^ j)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ ≤ 2008 * x / (((r : ℝ) - 1) * (((j : ℝ) + 1) * Real.log 2)) *
          (1 / ((r : ℝ) * 2 ^ j)) := mul_le_mul_of_nonneg_right hBT (by positivity)
    _ = 4016 / (((r : ℝ) - 1) * ((j : ℝ) + 1) * Real.log 2) := by
        rw [hx]
        push_cast
        rw [pow_succ]
        field_simp
        ring

/-- **`J` dyadic blocks.** `∑_{r < q ≤ r2^J, q prime, r ∣ q+1} 1/q ≤
(4016/((r−1) log 2)) · ∑_{j < J} 1/(j+1)`. -/
theorem dyadic_bound (r : ℕ) (hr : r.Prime) (J : ℕ) :
    ∑ q ∈ (Finset.Ioc r (r * 2 ^ J)).filter (fun q => q.Prime ∧ r ∣ q + 1), (1 : ℝ) / q
      ≤ 4016 / (((r : ℝ) - 1) * Real.log 2) *
          ∑ j ∈ Finset.range J, (1 : ℝ) / ((j : ℝ) + 1) := by
  classical
  have hr2R : (2 : ℝ) ≤ r := by exact_mod_cast hr.two_le
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  induction J with
  | zero => simp
  | succ J ih =>
    have hle1 : r ≤ r * 2 ^ J := Nat.le_mul_of_pos_right r (by positivity)
    have hle2 : r * 2 ^ J ≤ r * 2 ^ (J + 1) :=
      Nat.mul_le_mul_left r (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hsplit : Finset.Ioc r (r * 2 ^ (J + 1)) =
        Finset.Ioc r (r * 2 ^ J) ∪ Finset.Ioc (r * 2 ^ J) (r * 2 ^ (J + 1)) :=
      (Finset.Ioc_union_Ioc_eq_Ioc hle1 hle2).symm
    rw [hsplit, Finset.filter_union, Finset.sum_union
      (Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl))]
    rw [Finset.sum_range_succ, mul_add]
    have hb := block_bound r hr J
    have e : 4016 / (((r : ℝ) - 1) * ((J : ℝ) + 1) * Real.log 2) =
        4016 / (((r : ℝ) - 1) * Real.log 2) * (1 / ((J : ℝ) + 1)) := by
      field_simp
    linarith

/-- **The class sum.** For a prime `r`,
`G(r, N) ≤ (2 + 12048 (1 + log(⌊log₂ N⌋ + 1)))/r`. -/
theorem classRecip_le (r N : ℕ) (hr : r.Prime) :
    classRecip r N ≤ (2 + 12048 * (1 + Real.log ((Nat.log 2 N : ℝ) + 1))) / r := by
  classical
  have hr2 : 2 ≤ r := hr.two_le
  have hr2R : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  have hr0 : (0 : ℝ) < r := by linarith
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : (2 : ℝ) / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  set J := Nat.log 2 N + 1 with hJ
  have hNJ : N < r * 2 ^ J := by
    have h1 : N < 2 ^ J := Nat.lt_pow_succ_log_self (by norm_num) N
    have h2 : 2 ^ J ≤ r * 2 ^ J := Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- split into `q ≤ r` (only `q = r - 1`) and `q > r`
  have hsub : (Finset.Iic N).filter (fun q => q.Prime ∧ r ∣ q + 1) ⊆
      ({r - 1} : Finset ℕ) ∪ (Finset.Ioc r (r * 2 ^ J)).filter (fun q => q.Prime ∧ r ∣ q + 1) := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Iic] at hq
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, Finset.mem_Ioc]
    by_cases hqr : q ≤ r
    · left
      have h1 : r ≤ q + 1 := Nat.le_of_dvd (by omega) hq.2.2
      have h2 : q ≠ r := by
        rintro rfl
        have : q ∣ 1 := (Nat.dvd_add_right (dvd_refl q)).mp hq.2.2
        have := Nat.le_of_dvd (by norm_num) this
        omega
      omega
    · right
      exact ⟨⟨by omega, by omega⟩, hq.2⟩
  have hH : ∑ j ∈ Finset.range J, (1 : ℝ) / ((j : ℝ) + 1) ≤
      1 + Real.log ((Nat.log 2 N : ℝ) + 1) := by
    have h := harmonic_le_one_add_log J
    have e : ((harmonic J : ℚ) : ℝ) = ∑ j ∈ Finset.range J, (1 : ℝ) / ((j : ℝ) + 1) := by
      rw [harmonic]
      push_cast
      apply Finset.sum_congr rfl
      intro j _
      rw [one_div]
    rw [e] at h
    rw [hJ] at h
    push_cast at h
    exact h
  have hH0 : 0 ≤ ∑ j ∈ Finset.range J, (1 : ℝ) / ((j : ℝ) + 1) :=
    Finset.sum_nonneg (fun j _ => by positivity)
  have hdy := dyadic_bound r hr J
  have hsingle : ∑ q ∈ ({r - 1} : Finset ℕ), (1 : ℝ) / q = 1 / ((r : ℝ) - 1) := by
    rw [Finset.sum_singleton]
    push_cast [Nat.one_le_iff_ne_zero.mpr hr.ne_zero]
    ring
  have hL0 : 0 ≤ 1 + Real.log ((Nat.log 2 N : ℝ) + 1) := by
    have : 0 ≤ Real.log ((Nat.log 2 N : ℝ) + 1) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg (Nat.log 2 N) : (0 : ℝ) ≤ _)])
    linarith
  unfold classRecip
  calc ∑ q ∈ (Finset.Iic N).filter (fun q => q.Prime ∧ r ∣ q + 1), (1 : ℝ) / q
      ≤ ∑ q ∈ ({r - 1} : Finset ℕ) ∪
          (Finset.Ioc r (r * 2 ^ J)).filter (fun q => q.Prime ∧ r ∣ q + 1), (1 : ℝ) / q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ q ∈ ({r - 1} : Finset ℕ), (1 : ℝ) / q +
          ∑ q ∈ (Finset.Ioc r (r * 2 ^ J)).filter (fun q => q.Prime ∧ r ∣ q + 1), (1 : ℝ) / q := by
        have h := Finset.sum_union_inter (s₁ := ({r - 1} : Finset ℕ))
          (s₂ := (Finset.Ioc r (r * 2 ^ J)).filter (fun q => q.Prime ∧ r ∣ q + 1))
          (f := fun q : ℕ => (1 : ℝ) / q)
        have h0 : 0 ≤ ∑ q ∈ ({r - 1} : Finset ℕ) ∩
            (Finset.Ioc r (r * 2 ^ J)).filter (fun q => q.Prime ∧ r ∣ q + 1), (1 : ℝ) / q :=
          Finset.sum_nonneg (fun _ _ => by positivity)
        linarith
    _ ≤ 1 / ((r : ℝ) - 1) + 4016 / (((r : ℝ) - 1) * Real.log 2) *
          (1 + Real.log ((Nat.log 2 N : ℝ) + 1)) := by
        rw [hsingle]
        have : 4016 / (((r : ℝ) - 1) * Real.log 2) *
            ∑ j ∈ Finset.range J, (1 : ℝ) / ((j : ℝ) + 1) ≤
            4016 / (((r : ℝ) - 1) * Real.log 2) * (1 + Real.log ((Nat.log 2 N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hH (by positivity)
        linarith
    _ ≤ (1 + 6024 * (1 + Real.log ((Nat.log 2 N : ℝ) + 1))) / ((r : ℝ) - 1) := by
        have hc : 4016 / (((r : ℝ) - 1) * Real.log 2) ≤ 6024 / ((r : ℝ) - 1) := by
          rw [div_le_div_iff₀ (by positivity) hr1]
          nlinarith
        have := mul_le_mul_of_nonneg_right hc hL0
        have e1 : (1 + 6024 * (1 + Real.log ((Nat.log 2 N : ℝ) + 1))) / ((r : ℝ) - 1) =
            1 / ((r : ℝ) - 1) + 6024 / ((r : ℝ) - 1) * (1 + Real.log ((Nat.log 2 N : ℝ) + 1)) := by
          field_simp
        linarith
    _ ≤ (2 + 12048 * (1 + Real.log ((Nat.log 2 N : ℝ) + 1))) / r := by
        rw [div_le_div_iff₀ hr1 hr0]
        nlinarith

/-- **Step 4, completed.** For `z > 0`,
`∑_{q ≤ N prime} T_z(q+1)/q ≤ 2 (2 + 12048 (1 + log(⌊log₂ N⌋ + 1)))/z`. -/
theorem sum_tailRecip_div_le (N : ℕ) (z : ℝ) (hz : 0 < z) :
    ∑ q ∈ (Finset.Iic N).filter Nat.Prime, tailRecip z (q + 1) / q ≤
      2 * (2 + 12048 * (1 + Real.log ((Nat.log 2 N : ℝ) + 1))) / z := by
  classical
  set K := 2 + 12048 * (1 + Real.log ((Nat.log 2 N : ℝ) + 1)) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ Real.log ((Nat.log 2 N : ℝ) + 1) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg (Nat.log 2 N) : (0 : ℝ) ≤ _)])
    rw [hK]
    linarith
  set R := (Finset.Iic (N + 1)).filter (fun r : ℕ => r.Prime ∧ z < (r : ℝ)) with hR
  have hswap : ∑ q ∈ (Finset.Iic N).filter Nat.Prime, tailRecip z (q + 1) / q =
      ∑ r ∈ R, (1 : ℝ) / r * classRecip r N := by
    unfold tailRecip classRecip
    simp_rw [Finset.sum_div, Finset.mul_sum]
    rw [Finset.sum_comm' (t' := R)
      (s' := fun r => (Finset.Iic N).filter (fun q => q.Prime ∧ r ∣ q + 1))]
    · apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro q _
      ring
    · intro q r
      simp only [hR, Finset.mem_filter, Finset.mem_Iic, Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨hqN, hq⟩, ⟨hr, hrd, _⟩, hzr⟩
        exact ⟨⟨hqN, hq, hrd⟩, le_trans (Nat.le_of_dvd (by omega) hrd) (by omega), hr, hzr⟩
      · rintro ⟨⟨hqN, hq, hrd⟩, _, hr, hzr⟩
        exact ⟨⟨hqN, hq⟩, ⟨hr, hrd, by omega⟩, hzr⟩
  rw [hswap]
  calc ∑ r ∈ R, (1 : ℝ) / r * classRecip r N
      ≤ ∑ r ∈ R, K * ((r : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum
        intro r hr
        rw [hR, Finset.mem_filter] at hr
        have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.2.1.pos
        have h := classRecip_le r N hr.2.1
        calc (1 : ℝ) / r * classRecip r N ≤ 1 / r * (K / r) :=
              mul_le_mul_of_nonneg_left h (by positivity)
          _ = K * ((r : ℝ) ^ 2)⁻¹ := by field_simp
    _ = K * ∑ r ∈ R, ((r : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ K * ∑ r ∈ Finset.Ioo ⌊z⌋₊ (N + 2), ((r : ℝ) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ hK0
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro r hr
          rw [hR, Finset.mem_filter, Finset.mem_Iic] at hr
          rw [Finset.mem_Ioo]
          refine ⟨?_, by omega⟩
          have h1 : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le hz.le
          have h2 : (⌊z⌋₊ : ℝ) < r := lt_of_le_of_lt h1 hr.2.2
          exact_mod_cast h2
        · intro _ _ _
          positivity
    _ ≤ K * (2 / ((⌊z⌋₊ : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le ⌊z⌋₊ (N + 2)) hK0
    _ ≤ 2 * K / z := by
        have h1 : z < (⌊z⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one z
        have h2 : 2 / ((⌊z⌋₊ : ℝ) + 1) ≤ 2 / z :=
          div_le_div_of_nonneg_left (by norm_num) hz h1.le
        calc K * (2 / ((⌊z⌋₊ : ℝ) + 1)) ≤ K * (2 / z) := mul_le_mul_of_nonneg_left h2 hK0
          _ = 2 * K / z := by ring

/-! ## Steps 1 and 6: the uniform threshold and the assembly -/

/-- From `1 ≤ log((log X)/2)`: `(log X)/2 > 0`, so `X > 0`. -/
theorem half_log_pos (X : ℕ) (hv : 1 ≤ Real.log (Real.log (X : ℝ) / 2)) :
    0 < Real.log (X : ℝ) / 2 := by
  have hw0 : 0 ≤ Real.log (X : ℝ) / 2 := by
    have := Real.log_natCast_nonneg X
    linarith
  rcases hw0.lt_or_eq with h | h
  · exact h
  · rw [← h, Real.log_zero] at hv
    norm_num at hv

/-- **Uniform threshold.** If `v = log((log X)/2) ≥ 1` and `n > ⌊√X⌋`, then
`v^2 ≤ (log log n)^2`. -/
theorem threshold_le (X n : ℕ) (hv : 1 ≤ Real.log (Real.log (X : ℝ) / 2))
    (hn : Nat.sqrt X < n) :
    (Real.log (Real.log (X : ℝ) / 2)) ^ 2 ≤ (Real.log (Real.log (n : ℝ))) ^ 2 := by
  have hw := half_log_pos X hv
  have hX0 : (X : ℝ) ≠ 0 := by
    intro h
    rw [h, Real.log_zero] at hw
    norm_num at hw
  have hXpos : (0 : ℝ) < X := lt_of_le_of_ne (Nat.cast_nonneg X) (Ne.symm hX0)
  have hXn : (X : ℝ) < (n : ℝ) ^ 2 := by
    have h1 : X < (Nat.sqrt X + 1) ^ 2 := Nat.lt_succ_sqrt' X
    have h2 : (Nat.sqrt X + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
    exact_mod_cast lt_of_lt_of_le h1 h2
  have hlog : Real.log (X : ℝ) < 2 * Real.log (n : ℝ) := by
    have := Real.log_lt_log hXpos hXn
    rwa [Real.log_pow] at this
  have hll : Real.log (Real.log (X : ℝ) / 2) ≤ Real.log (Real.log (n : ℝ)) :=
    Real.log_le_log hw (by linarith)
  exact pow_le_pow_left₀ (by linarith) hll 2

open Classical in
/-- **The count.** If `v = log((log X)/2) ≥ 1` and `k^6 ≤ v^2`, then
`#{n ≤ X : S(n) > 1} ≤ ⌊√X⌋ + X · 2/(k+1) + X · 2 (2 + 12048 (1 + log(⌊log₂ X⌋ + 1)))/v^2`. -/
theorem card_lp_le (X k : ℕ) (hv : 1 ≤ Real.log (Real.log (X : ℝ) / 2))
    (hk : ((k : ℝ)) ^ 6 ≤ (Real.log (Real.log (X : ℝ) / 2)) ^ 2) :
    ((((Finset.Icc 1 X).filter (fun n => 1 < lpSum n)).card : ℕ) : ℝ) ≤
      (Nat.sqrt X : ℝ) + (X : ℝ) * (2 / ((k : ℝ) + 1)) +
        (X : ℝ) * (2 * (2 + 12048 * (1 + Real.log ((Nat.log 2 X : ℝ) + 1))) /
          (Real.log (Real.log (X : ℝ) / 2)) ^ 2) := by
  set v := Real.log (Real.log (X : ℝ) / 2) with hv_def
  set z := v ^ 2 with hz_def
  have hz : 0 < z := by
    rw [hz_def]
    nlinarith
  set A := (Finset.Icc 1 X).filter (fun n => n ≤ Nat.sqrt X) with hA
  set B := (Finset.Icc 1 X).filter
    (fun n => ∃ m : ℕ, 2 ≤ m ∧ m ^ 2 ∣ n ∧ z < ((m : ℝ)) ^ 6) with hB
  set C := (Finset.Icc 1 X).filter
    (fun n => 1 < ∑ q ∈ n.primeFactors, tailRecip z (q + 1)) with hC
  have hsub : (Finset.Icc 1 X).filter (fun n => 1 < lpSum n) ⊆ A ∪ B ∪ C := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnI, hS⟩ := hn
    rw [Finset.mem_union, Finset.mem_union]
    by_cases h1 : n ≤ Nat.sqrt X
    · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨hnI, h1⟩))
    by_cases h2 : ∃ m : ℕ, 2 ≤ m ∧ m ^ 2 ∣ n ∧ z < ((m : ℝ)) ^ 6
    · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hnI, h2⟩))
    refine Or.inr (Finset.mem_filter.mpr ⟨hnI, ?_⟩)
    have hn0 : n ≠ 0 := by
      rw [Finset.mem_Icc] at hnI
      omega
    have hthr : z ≤ (Real.log (Real.log (n : ℝ))) ^ 2 := threshold_le X n hv (by omega)
    have h3 : lpSum n ≤ tailRecip z (ArithmeticFunction.sigma 1 n) := by
      unfold lpSum tailRecip
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        rw [Finset.mem_filter] at hr ⊢
        exact ⟨hr.1, lt_of_le_of_lt hthr hr.2⟩
      · intro _ _ _
        positivity
    have h4 := tailRecip_sigma_le n hn0 z (fun m hm hmd => by
      by_contra hc
      exact h2 ⟨m, hm, hmd, lt_of_not_ge hc⟩)
    linarith
  have hcardA : ((A.card : ℕ) : ℝ) ≤ (Nat.sqrt X : ℝ) := by
    have hAs : A ⊆ Finset.Icc 1 (Nat.sqrt X) := by
      intro n hn
      rw [hA, Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_Icc]
      exact ⟨hn.1.1, hn.2⟩
    have h := Finset.card_le_card hAs
    rw [Nat.card_Icc] at h
    exact_mod_cast (le_trans h (by omega))
  have hcardB := card_squareful_le X k z hk
  have hcardC : ((C.card : ℕ) : ℝ) ≤
      (X : ℝ) * (2 * (2 + 12048 * (1 + Real.log ((Nat.log 2 X : ℝ) + 1))) / z) := by
    have hM := card_filter_one_lt_le (Finset.Icc 1 X)
      (fun n => ∑ q ∈ n.primeFactors, tailRecip z (q + 1))
      (fun n _ => Finset.sum_nonneg (fun q _ => tailRecip_nonneg z (q + 1)))
    have hF := sum_Icc_sum_primeFactors_le X (fun q => tailRecip z (q + 1))
      (fun q => tailRecip_nonneg z (q + 1))
    have hD := sum_tailRecip_div_le X z hz
    have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    calc ((C.card : ℕ) : ℝ)
        ≤ ∑ n ∈ Finset.Icc 1 X, ∑ q ∈ n.primeFactors, tailRecip z (q + 1) := hM
      _ ≤ (X : ℝ) * ∑ q ∈ (Finset.Iic X).filter Nat.Prime, tailRecip z (q + 1) / q := hF
      _ ≤ (X : ℝ) * (2 * (2 + 12048 * (1 + Real.log ((Nat.log 2 X : ℝ) + 1))) / z) :=
        mul_le_mul_of_nonneg_left hD hX0
  have hU := Finset.card_le_card hsub
  have hU2 := Finset.card_union_le (A ∪ B) C
  have hU3 := Finset.card_union_le A B
  have hsum : ((((Finset.Icc 1 X).filter (fun n => 1 < lpSum n)).card : ℕ) : ℝ) ≤
      ((A.card : ℕ) : ℝ) + ((B.card : ℕ) : ℝ) + ((C.card : ℕ) : ℝ) := by
    exact_mod_cast le_trans hU (le_trans hU2 (by omega))
  linarith

/-- **The density bound.** If `v = log((log X)/2) ≥ 1`, then
`#{n ≤ X : S(n) > 1}/X ≤ 144583 / v^{1/3}`. -/
theorem card_lp_div_le (X : ℕ) (hv : 1 ≤ Real.log (Real.log (X : ℝ) / 2)) :
    ((((Finset.Icc 1 X).filter (fun n => 1 < lpSum n)).card : ℕ) : ℝ) / X ≤
      144583 / (Real.log (Real.log (X : ℝ) / 2)) ^ ((1 : ℝ) / 3) := by
  set v := Real.log (Real.log (X : ℝ) / 2) with hv_def
  have hw := half_log_pos X hv
  have hX0 : X ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero, Real.log_zero] at hw
    norm_num at hw
  have hXpos : (0 : ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX0
  -- `v ≤ w - 1` and `w ≤ √X - 1`, where `w = (log X)/2 = log √X`
  have hvw : v ≤ Real.log (X : ℝ) / 2 - 1 := Real.log_le_sub_one_of_pos hw
  have hsqrt_pos : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hXpos
  have hwsq : Real.log (X : ℝ) / 2 ≤ Real.sqrt (X : ℝ) - 1 := by
    rw [← Real.log_sqrt hXpos.le]
    exact Real.log_le_sub_one_of_pos hsqrt_pos
  have hw1 : 2 ≤ Real.log (X : ℝ) / 2 := by linarith
  set c := v ^ ((1 : ℝ) / 3) with hc_def
  have hc1 : 1 ≤ c := Real.one_le_rpow hv (by norm_num)
  have hc0 : 0 < c := by linarith
  have hcv : c ≤ v := by
    calc c = v ^ ((1 : ℝ) / 3) := rfl
      _ ≤ v ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hv (by norm_num)
      _ = v := Real.rpow_one v
  set k := ⌊c⌋₊ with hk_def
  have hk6 : ((k : ℝ)) ^ 6 ≤ v ^ 2 := by
    have h1 : (k : ℝ) ≤ c := Nat.floor_le hc0.le
    have h2 : ((k : ℝ)) ^ 6 ≤ c ^ 6 := pow_le_pow_left₀ (by positivity) h1 6
    have h3 : c ^ 6 = v ^ 2 := by
      rw [hc_def, ← Real.rpow_natCast (v ^ ((1 : ℝ) / 3)) 6,
        ← Real.rpow_mul (by linarith)]
      norm_num
    linarith
  have hkc : c < (k : ℝ) + 1 := Nat.lt_floor_add_one c
  have hmain := card_lp_le X k hv hk6
  -- the three pieces, each `≤ const/c`
  have e1 : (Nat.sqrt X : ℝ) * c ≤ X := by
    have h1 : (Nat.sqrt X : ℝ) ≤ Real.sqrt (X : ℝ) := Real.nat_sqrt_le_real_sqrt
    have h2 : c ≤ Real.sqrt (X : ℝ) := by linarith
    calc (Nat.sqrt X : ℝ) * c ≤ Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) :=
          mul_le_mul h1 h2 hc0.le hsqrt_pos.le
      _ = X := Real.mul_self_sqrt (Nat.cast_nonneg X)
  have e2 : 2 / ((k : ℝ) + 1) * c ≤ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  set K := 2 + 12048 * (1 + Real.log ((Nat.log 2 X : ℝ) + 1)) with hK
  have hL : (Nat.log 2 X : ℝ) ≤ 2 * Real.log (X : ℝ) := by
    have h := Nat.pow_log_le_self 2 hX0
    have h' : (2 : ℝ) ^ (Nat.log 2 X) ≤ (X : ℝ) := by exact_mod_cast h
    have h'' := Real.log_le_log (by positivity) h'
    rw [Real.log_pow] at h''
    have hl2 := Real.log_two_gt_d9
    have hl0 : (0 : ℝ) ≤ Nat.log 2 X := Nat.cast_nonneg _
    nlinarith
  have hlogL : Real.log ((Nat.log 2 X : ℝ) + 1) ≤ 4 + v := by
    have h5 : (Nat.log 2 X : ℝ) + 1 ≤ 5 * (Real.log (X : ℝ) / 2) := by linarith
    have h6 := Real.log_le_log (by positivity) h5
    rw [Real.log_mul (by norm_num) hw.ne'] at h6
    have h7 : Real.log 5 ≤ 5 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hK0 : 0 ≤ K := by
    have : 0 ≤ Real.log ((Nat.log 2 X : ℝ) + 1) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg (Nat.log 2 X) : (0 : ℝ) ≤ _)])
    rw [hK]
    linarith
  have hKv : K ≤ 72290 * v := by
    rw [hK]
    linarith
  have e3 : 2 * K / v ^ 2 * c ≤ 144580 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hX0' : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  rw [div_le_div_iff₀ hXpos hc0]
  calc ((((Finset.Icc 1 X).filter (fun n => 1 < lpSum n)).card : ℕ) : ℝ) * c
      ≤ ((Nat.sqrt X : ℝ) + (X : ℝ) * (2 / ((k : ℝ) + 1)) + (X : ℝ) * (2 * K / v ^ 2)) * c :=
        mul_le_mul_of_nonneg_right hmain hc0.le
    _ = (Nat.sqrt X : ℝ) * c + (X : ℝ) * (2 / ((k : ℝ) + 1) * c) +
          (X : ℝ) * (2 * K / v ^ 2 * c) := by ring
    _ ≤ (X : ℝ) + (X : ℝ) * 2 + (X : ℝ) * 144580 :=
        add_le_add (add_le_add e1 (mul_le_mul_of_nonneg_left e2 hX0'))
          (mul_le_mul_of_nonneg_left e3 hX0')
    _ = 144583 * X := by ring

/-- **Luca–Pomerance, Lemma 2.5.** The set of `n` with
`∑_{r ∣ σ(n), r prime, r > (log log n)^2} 1/r > 1` has asymptotic density zero. -/
theorem lp_lemma25_density :
    Tendsto (fun X : ℕ =>
      ((((Finset.Icc 1 X).filter (fun n => 1 < lpSum n)).card : ℕ) : ℝ) / X)
      atTop (𝓝 0) := by
  have hv : Tendsto (fun X : ℕ => Real.log (Real.log (X : ℝ) / 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
        (by norm_num))
  have hc : Tendsto (fun X : ℕ => (Real.log (Real.log (X : ℝ) / 2)) ^ ((1 : ℝ) / 3))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hv
  have hlim : Tendsto
      (fun X : ℕ => (144583 : ℝ) / (Real.log (Real.log (X : ℝ) / 2)) ^ ((1 : ℝ) / 3))
      atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hc
  refine squeeze_zero' (Eventually.of_forall (fun X => by positivity)) ?_ hlim
  filter_upwards [hv.eventually_ge_atTop 1] with X hX
  exact card_lp_div_le X hX

end Principia.Common.LucaPomerance.Lemma25
