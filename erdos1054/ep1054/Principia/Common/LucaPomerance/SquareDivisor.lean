/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.LucaPomerance.Basic
import Principia.Common.Sieve.BrunTitchmarshAP

set_option autoImplicit false

/-!
# Luca–Pomerance Lemma 2.2 in the range `P(n) > n^{7/9}`, `q ≤ n^{10/27}`

Luca–Pomerance (*The range of the sum-of-proper-divisors function*, Acta Arith. 168 (2015),
Lemma 2.2): the `n` with `P(n) > n^{1/2}` and `π² ∣ s(n)` for a prime `π > y(n)` have density `0`.
Here: the range form used by the Erdős-1054 paper, with the threshold `y(n)` replaced by a fixed
level `K` (the density-zero statement follows because `y(n) → ∞`, see the Erdős-1054 bridge).

**Main result** (`card_LP22Bad_le`): for `K ≥ 1` and `log X ≥ 9`,
`#{n ≤ X : n has a prime factor p > n^{7/9} and q² ∣ s(n) for a prime K < q ≤ n^{10/27}}
  ≤ 54216 X / K`.

**Proof.** `n = m p`, `m < n^{2/9}`, `p ∤ m`, `s(n) = p s(m) + σ(m)` (`aliq_mul_prime`). For fixed
`(m, q)` all admissible `p` lie in one class modulo `k = q²/g`, `g = gcd(q², s(m))`, and none exist
unless `g ∣ m` (`modEq_of_dvd`, `gcd_dvd_self_of_dvd`). Brun–Titchmarsh
(`BrunTitchmarshAP.brun_titchmarsh_ap`) with `X/(m k) ≥ X^{1/27}` bounds their number by
`54216 X g/(m q(q−1) log X)`; `∑_{m ≤ X^{2/9}} [g ∣ m] g/m ≤ 3(1 + log X^{2/9}) ≤ log X` and
`∑_{q > K} 1/(q(q−1)) ≤ 1/K` finish.

This avoids Luca–Pomerance's Lemma 2.1(2) (their case `π ∣ s(m)`): the congruence still fixes `p`
modulo `q²/g`, and the factor `g` lost from the modulus is repaid by `g ∣ m`.
-/

namespace Principia.Common.LucaPomerance.LP22

open Principia.Common.LucaPomerance.Aliquot

open Finset

/-- `n` is an exception of level `K` to Luca–Pomerance Lemma 2.2 (range form): `n` has a prime
factor `p > n^{7/9}`, and `q² ∣ s(n)` for some prime `K < q ≤ n^{10/27}`. -/
def LP22Bad (K n : ℕ) : Prop :=
  (∃ p ∈ n.primeFactors, (n : ℝ) ^ ((7 : ℝ) / 9) < p) ∧
    ∃ q : ℕ, q.Prime ∧ K < q ∧ (q : ℝ) ≤ (n : ℝ) ^ ((10 : ℝ) / 27) ∧ q ^ 2 ∣ aliq n

/-- The primes `p ≤ T` with `q² ∣ p s(m) + σ(m)`. -/
noncomputable def solSet (T : ℝ) (m q : ℕ) : Finset ℕ :=
  (Iic ⌊T⌋₊).filter (fun p => p.Prime ∧ q ^ 2 ∣ p * aliq m + ArithmeticFunction.sigma 1 m)

/-- The prime-count bound for one pair `(m, q)`: Brun–Titchmarsh in the class forced modulo
`q² / gcd(q², s(m))`. -/
theorem card_solSet_le {T : ℝ} {m q : ℕ} (hq : q.Prime) (hqT : (q : ℝ) ^ 2 < T) :
    ((solSet T m q).card : ℝ) ≤
      2008 * T / ((q : ℝ) * ((q : ℝ) - 1) * Real.log (T / (q : ℝ) ^ 2)) *
        (if Nat.gcd (q ^ 2) (aliq m) ∣ m then (Nat.gcd (q ^ 2) (aliq m) : ℝ) else 0) := by
  set g := Nat.gcd (q ^ 2) (aliq m) with hg
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hq0 : (0 : ℝ) < q := by linarith
  have hqq : (0 : ℝ) < (q : ℝ) * ((q : ℝ) - 1) := mul_pos hq0 (by linarith)
  have hT0 : 0 < T := lt_of_le_of_lt (by positivity) hqT
  have hTq : 1 < T / (q : ℝ) ^ 2 := by
    rw [one_lt_div (by positivity)]
    exact hqT
  have hlog : 0 < Real.log (T / (q : ℝ) ^ 2) := Real.log_pos hTq
  have hpref : 0 ≤ 2008 * T / ((q : ℝ) * ((q : ℝ) - 1) * Real.log (T / (q : ℝ) ^ 2)) := by
    positivity
  rcases (solSet T m q).eq_empty_or_nonempty with he | ⟨p₀, hp₀⟩
  · rw [he, Finset.card_empty, Nat.cast_zero]
    split_ifs
    · positivity
    · simp
  have hp₀' := (Finset.mem_filter.1 hp₀).2.2
  have hgm : g ∣ m := gcd_dvd_self_of_dvd hp₀'
  rw [if_pos hgm]
  have hQ : 0 < q ^ 2 := pow_pos hq.pos 2
  set k := q ^ 2 / g with hk
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hQ
  have hgq : g ∣ q ^ 2 := Nat.gcd_dvd_left _ _
  have hk1 : 1 ≤ k := Nat.div_pos (Nat.le_of_dvd hQ hgq) hg0
  have hkq : k ≤ q ^ 2 := Nat.div_le_self _ _
  have hkqR : (k : ℝ) ≤ (q : ℝ) ^ 2 := by exact_mod_cast hkq
  have hk0R : (0 : ℝ) < k := by exact_mod_cast hk1
  have hkT : (k : ℝ) < T := lt_of_le_of_lt hkqR hqT
  -- every solution lies in the class of `p₀` modulo `k`
  have hsub : solSet T m q ⊆
      (Iic ⌊T⌋₊).filter (fun p => p.Prime ∧ p % k = p₀ % k) := by
    intro p hp
    obtain ⟨hpT, hpp, hpd⟩ := Finset.mem_filter.1 hp
    exact Finset.mem_filter.2 ⟨hpT, hpp, modEq_of_dvd hQ hpd hp₀'⟩
  have hBT := Principia.Common.BrunTitchmarshAP.brun_titchmarsh_ap k p₀ hk1 T hkT
  have hcard : ((solSet T m q).card : ℝ) ≤
      2008 * T / ((k.totient : ℝ) * Real.log (T / k)) :=
    le_trans (by exact_mod_cast Finset.card_le_card hsub) hBT
  -- `g φ(k) ≥ q (q − 1)` and `log(T/k) ≥ log(T/q²)`
  have htot : (q : ℝ) * ((q : ℝ) - 1) ≤ (g : ℝ) * (k.totient : ℝ) := by
    have h := mul_totient_div_ge hq hgq
    have hq1 : 1 ≤ q := hq.one_lt.le
    have : ((q * (q - 1) : ℕ) : ℝ) ≤ ((g * k.totient : ℕ) : ℝ) := by exact_mod_cast h
    push_cast [Nat.cast_sub hq1] at this
    exact this
  have hlogk : Real.log (T / (q : ℝ) ^ 2) ≤ Real.log (T / k) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_left hT0.le hk0R hkqR)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
  have htot0 : (0 : ℝ) < (k.totient : ℝ) := by
    have : 0 < k.totient := Nat.totient_pos.2 hk1
    exact_mod_cast this
  calc ((solSet T m q).card : ℝ)
      ≤ 2008 * T / ((k.totient : ℝ) * Real.log (T / k)) := hcard
    _ ≤ 2008 * T / (((q : ℝ) * ((q : ℝ) - 1) / g) * Real.log (T / (q : ℝ) ^ 2)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        apply mul_le_mul _ hlogk hlog.le htot0.le
        rw [div_le_iff₀ hgR]
        linarith
    _ = 2008 * T / ((q : ℝ) * ((q : ℝ) - 1) * Real.log (T / (q : ℝ) ^ 2)) * (g : ℝ) := by
        field_simp

/-- The real-exponent bookkeeping: `X^{2/9} (X^{10/27})² X^{1/27} = X`. -/
theorem rpow_split (X : ℝ) (hX : 0 < X) :
    X ^ ((2 : ℝ) / 9) * (X ^ ((10 : ℝ) / 27)) ^ 2 * X ^ ((1 : ℝ) / 27) = X := by
  rw [sq, ← Real.rpow_add hX, ← Real.rpow_add hX, ← Real.rpow_add hX]
  norm_num

/-- The bound for one pair `(m, q)` in the ranges `m ≤ X^{2/9}`, `q ≤ X^{10/27}`. -/
theorem card_solSet_le_range {X : ℝ} (hX : 1 < X) {m q : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hma : (m : ℝ) ≤ X ^ ((2 : ℝ) / 9)) (hqb : (q : ℝ) ≤ X ^ ((10 : ℝ) / 27)) :
    ((solSet (X / m) m q).card : ℝ) ≤
      54216 * X / ((q : ℝ) * ((q : ℝ) - 1) * Real.log X) *
        (if Nat.gcd (q ^ 2) (aliq m) ∣ m then (Nat.gcd (q ^ 2) (aliq m) : ℝ) / m else 0) := by
  have hX0 : 0 < X := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hq0 : (0 : ℝ) < q := by linarith
  have hqq : (0 : ℝ) < (q : ℝ) * ((q : ℝ) - 1) := mul_pos hq0 (by linarith)
  set a := X ^ ((2 : ℝ) / 9) with ha
  set b := X ^ ((10 : ℝ) / 27) with hb
  set c := X ^ ((1 : ℝ) / 27) with hc
  have hsplit : a * b ^ 2 * c = X := rpow_split X hX0
  have ha0 : 0 < a := Real.rpow_pos_of_pos hX0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hX0 _
  have hc1 : 1 < c := Real.one_lt_rpow hX (by norm_num)
  have hq2b : (q : ℝ) ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hq0.le hqb 2
  have hmq : (m : ℝ) * (q : ℝ) ^ 2 ≤ a * b ^ 2 := mul_le_mul hma hq2b (by positivity) ha0.le
  have hmq0 : 0 < (m : ℝ) * (q : ℝ) ^ 2 := by positivity
  -- `X/m / q² ≥ X^{1/27}`
  have hratio : c ≤ X / m / (q : ℝ) ^ 2 := by
    rw [div_div, le_div_iff₀ hmq0]
    calc c * ((m : ℝ) * (q : ℝ) ^ 2) ≤ c * (a * b ^ 2) :=
          mul_le_mul_of_nonneg_left hmq (by linarith)
      _ = X := by rw [← hsplit]; ring
  have hqT : (q : ℝ) ^ 2 < X / m := by
    have h1 : 1 < X / m / (q : ℝ) ^ 2 := lt_of_lt_of_le hc1 hratio
    rwa [one_lt_div (by positivity)] at h1
  have hlogc : Real.log c = Real.log X / 27 := by
    rw [hc, Real.log_rpow hX0]
    ring
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlogT : Real.log X / 27 ≤ Real.log (X / m / (q : ℝ) ^ 2) := by
    rw [← hlogc]
    exact Real.log_le_log (by linarith) hratio
  have h1 := card_solSet_le (m := m) hq hqT
  refine h1.trans ?_
  split_ifs with hgm
  · have hg0 : (0 : ℝ) ≤ (Nat.gcd (q ^ 2) (aliq m) : ℝ) := Nat.cast_nonneg _
    have hden : (q : ℝ) * ((q : ℝ) - 1) * (Real.log X / 27) ≤
        (q : ℝ) * ((q : ℝ) - 1) * Real.log (X / m / (q : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hlogT hqq.le
    calc 2008 * (X / m) / ((q : ℝ) * ((q : ℝ) - 1) * Real.log (X / m / (q : ℝ) ^ 2)) *
          (Nat.gcd (q ^ 2) (aliq m) : ℝ)
        ≤ 2008 * (X / m) / ((q : ℝ) * ((q : ℝ) - 1) * (Real.log X / 27)) *
          (Nat.gcd (q ^ 2) (aliq m) : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hg0
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 54216 * X / ((q : ℝ) * ((q : ℝ) - 1) * Real.log X) *
          ((Nat.gcd (q ^ 2) (aliq m) : ℝ) / m) := by
          field_simp
          ring
  · simp

/-- `[g ∣ m] g/m ≤ 1/m + [q ∣ m] q/m + [q² ∣ m] q²/m` for `g ∣ q²`. -/
theorem ite_div_le {q g m : ℕ} (hq : q.Prime) (hg : g ∣ q ^ 2) :
    (if g ∣ m then (g : ℝ) / m else 0) ≤
      (1 : ℝ) / m + (if q ∣ m then (q : ℝ) / m else 0) +
        (if q ^ 2 ∣ m then ((q ^ 2 : ℕ) : ℝ) / m else 0) := by
  have e1 : (0 : ℝ) ≤ 1 / m := by positivity
  have e2 : (0 : ℝ) ≤ (if q ∣ m then (q : ℝ) / m else 0) := by
    split_ifs
    · positivity
    · exact le_rfl
  have e3 : (0 : ℝ) ≤ (if q ^ 2 ∣ m then ((q ^ 2 : ℕ) : ℝ) / m else 0) := by
    split_ifs
    · positivity
    · exact le_rfl
  by_cases hgm : g ∣ m
  · rw [if_pos hgm]
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hq).1 hg
    interval_cases i
    · simp only [pow_zero, Nat.cast_one]
      linarith
    · rw [pow_one] at hgm ⊢
      rw [if_pos hgm]
      linarith
    · rw [if_pos hgm]
      linarith
  · rw [if_neg hgm]
    linarith

/-- `∑_{m ≤ Z} [g_m ∣ m] g_m/m ≤ 3 (1 + log Z)`, where each `g_m` divides `q²`. -/
theorem sum_ite_div_le {q Z : ℕ} (hq : q.Prime) (hZ : 1 ≤ Z) (g : ℕ → ℕ)
    (hg : ∀ m, g m ∣ q ^ 2) :
    ∑ m ∈ Icc 1 Z, (if g m ∣ m then (g m : ℝ) / m else 0) ≤ 3 * (1 + Real.log Z) := by
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hq21 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
  calc ∑ m ∈ Icc 1 Z, (if g m ∣ m then (g m : ℝ) / m else 0)
      ≤ ∑ m ∈ Icc 1 Z, ((1 : ℝ) / m + (if q ∣ m then (q : ℝ) / m else 0) +
          (if q ^ 2 ∣ m then ((q ^ 2 : ℕ) : ℝ) / m else 0)) :=
        Finset.sum_le_sum fun m _ => ite_div_le hq (hg m)
    _ = ∑ m ∈ (Icc 1 Z).filter (1 ∣ ·), ((1 : ℕ) : ℝ) / m +
          ∑ m ∈ (Icc 1 Z).filter (q ∣ ·), (q : ℝ) / m +
          ∑ m ∈ (Icc 1 Z).filter (q ^ 2 ∣ ·), ((q ^ 2 : ℕ) : ℝ) / m := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter,
          Finset.sum_filter]
        simp
    _ ≤ (1 + Real.log Z) + (1 + Real.log Z) + (1 + Real.log Z) := by
        gcongr
        · exact sum_multiples_div_le 1 Z le_rfl hZ
        · exact sum_multiples_div_le q Z hq1 hZ
        · exact sum_multiples_div_le (q ^ 2) Z hq21 hZ
    _ = 3 * (1 + Real.log Z) := by ring

open Classical in
/-- **Luca–Pomerance Lemma 2.2, range form, at a fixed level `K`.** For `K ≥ 1` and
`X ≥ e⁹`, at most `54216 X / K` integers `n ≤ X` have a prime factor `p > n^{7/9}` and
`q² ∣ s(n)` for some prime `K < q ≤ n^{10/27}`. -/
theorem card_LP22Bad_le (K : ℕ) (hK : 1 ≤ K) (X : ℝ) (hX : Real.exp 9 ≤ X) :
    (((Icc 1 ⌊X⌋₊).filter (LP22Bad K)).card : ℝ) ≤ 54216 * X / K := by
  have hX1 : 1 < X := lt_of_lt_of_le (by have := Real.add_one_le_exp 9; linarith) hX
  have hX0 : 0 < X := by linarith
  have hlogX9 : 9 ≤ Real.log X := by
    have := Real.log_le_log (Real.exp_pos 9) hX
    rwa [Real.log_exp] at this
  have hlogX : 0 < Real.log X := by linarith
  set a := X ^ ((2 : ℝ) / 9) with ha
  set b := X ^ ((10 : ℝ) / 27) with hb
  have ha1 : 1 ≤ a := Real.one_le_rpow hX1.le (by norm_num)
  set Z := ⌊a⌋₊ with hZ
  set Qm := ⌊b⌋₊ with hQm
  have hZ1 : 1 ≤ Z := Nat.le_floor (by exact_mod_cast ha1)
  set Qs := (Ioc K Qm).filter Nat.Prime with hQs
  -- the covering
  have hcover : (Icc 1 ⌊X⌋₊).filter (LP22Bad K) ⊆
      (Icc 1 Z).biUnion (fun m => Qs.biUnion (fun q => (solSet (X / m) m q).image (m * ·))) := by
    intro n hn
    obtain ⟨hnI, ⟨p, hp, hpn⟩, q, hq, hKq, hqn, hqs⟩ := Finset.mem_filter.1 hn
    obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.1 hnI
    have hnXR : (n : ℝ) ≤ X := le_trans (by exact_mod_cast hnX) (Nat.floor_le hX0.le)
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    obtain ⟨hpp, hpdvd, hn0⟩ := Nat.mem_primeFactors.1 hp
    set m := n / p with hm
    have hmp : m * p = n := Nat.div_mul_cancel hpdvd
    have hm0 : m ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hmp
      exact hn0 hmp.symm
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm0
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hmpR : (m : ℝ) * p = n := by exact_mod_cast hmp
    have hsplit : (n : ℝ) ^ ((2 : ℝ) / 9) * (n : ℝ) ^ ((7 : ℝ) / 9) = n := by
      rw [← Real.rpow_add (by linarith)]
      norm_num
    have h29pos : 0 < (n : ℝ) ^ ((2 : ℝ) / 9) := Real.rpow_pos_of_pos (by linarith) _
    have hmlt : (m : ℝ) < (n : ℝ) ^ ((2 : ℝ) / 9) := by
      by_contra hcon
      push Not at hcon
      have : (n : ℝ) < (m : ℝ) * p := by
        calc (n : ℝ) = (n : ℝ) ^ ((2 : ℝ) / 9) * (n : ℝ) ^ ((7 : ℝ) / 9) := hsplit.symm
          _ < (n : ℝ) ^ ((2 : ℝ) / 9) * p := mul_lt_mul_of_pos_left hpn h29pos
          _ ≤ (m : ℝ) * p := mul_le_mul_of_nonneg_right hcon hpR.le
      linarith
    have hma : (m : ℝ) ≤ a :=
      le_trans hmlt.le (Real.rpow_le_rpow (by linarith) hnXR (by norm_num))
    have hmZ : m ≤ Z := Nat.le_floor hma
    have hqb : (q : ℝ) ≤ b := le_trans hqn (Real.rpow_le_rpow (by linarith) hnXR (by norm_num))
    have hqQ : q ≤ Qm := Nat.le_floor hqb
    have hpm : ¬ p ∣ m := by
      intro hdvd
      have hle : p ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
      have hleR : (p : ℝ) ≤ m := by exact_mod_cast hle
      have h27 : (n : ℝ) ^ ((2 : ℝ) / 9) ≤ (n : ℝ) ^ ((7 : ℝ) / 9) :=
        Real.rpow_le_rpow_of_exponent_le hn1R (by norm_num)
      linarith
    have hpX : (p : ℝ) ≤ X / m := by
      rw [le_div_iff₀ hmR]
      linarith
    have hpT : p ≤ ⌊X / m⌋₊ := Nat.le_floor hpX
    have hdiv : q ^ 2 ∣ p * aliq m + ArithmeticFunction.sigma 1 m := by
      rw [← aliq_mul_prime hpp hpm, hmp]
      exact hqs
    rw [Finset.mem_biUnion]
    refine ⟨m, Finset.mem_Icc.2 ⟨hm1, hmZ⟩, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨q, Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨hKq, hqQ⟩, hq⟩, ?_⟩
    rw [Finset.mem_image]
    exact ⟨p, Finset.mem_filter.2 ⟨Finset.mem_Iic.2 hpT, hpp, hdiv⟩, hmp⟩
  -- the per-pair bound, summed
  set W : ℕ → ℝ := fun q => 54216 * X / ((q : ℝ) * ((q : ℝ) - 1) * Real.log X) with hW
  have hcard1 : (((Icc 1 ⌊X⌋₊).filter (LP22Bad K)).card : ℝ) ≤
      ∑ m ∈ Icc 1 Z, ∑ q ∈ Qs, ((solSet (X / m) m q).card : ℝ) := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_biUnion_le (s := Icc 1 Z)
      (t := fun m => Qs.biUnion (fun q => (solSet (X / m) m q).image (m * ·)))
    have h3 : ∀ m ∈ Icc 1 Z, (Qs.biUnion (fun q => (solSet (X / m) m q).image (m * ·))).card ≤
        ∑ q ∈ Qs, (solSet (X / m) m q).card := by
      intro m _
      refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun q _ => ?_)
      exact Finset.card_image_le
    have h4 := h1.trans (h2.trans (Finset.sum_le_sum h3))
    exact_mod_cast h4
  have hterm : ∀ m ∈ Icc 1 Z, ∀ q ∈ Qs, ((solSet (X / m) m q).card : ℝ) ≤
      W q * (if Nat.gcd (q ^ 2) (aliq m) ∣ m then (Nat.gcd (q ^ 2) (aliq m) : ℝ) / m else 0) := by
    intro m hm q hq
    obtain ⟨hm1, hmZ⟩ := Finset.mem_Icc.1 hm
    obtain ⟨hqI, hqp⟩ := Finset.mem_filter.1 hq
    have hma : (m : ℝ) ≤ a := le_trans (by exact_mod_cast hmZ) (Nat.floor_le (by linarith))
    have hqb : (q : ℝ) ≤ b :=
      le_trans (by exact_mod_cast (Finset.mem_Ioc.1 hqI).2)
        (Nat.floor_le (Real.rpow_pos_of_pos hX0 _).le)
    exact card_solSet_le_range hX1 hqp hm1 hma hqb
  have hWnn : ∀ q ∈ Qs, 0 ≤ W q := by
    intro q hq
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_filter.1 hq).2.two_le
    have : 0 < (q : ℝ) * ((q : ℝ) - 1) := mul_pos (by linarith) (by linarith)
    positivity
  have hlogZ : Real.log Z ≤ 2 / 9 * Real.log X := by
    have hZ0 : (0 : ℝ) < Z := by exact_mod_cast hZ1
    calc Real.log Z ≤ Real.log a := Real.log_le_log hZ0 (Nat.floor_le (by linarith))
      _ = 2 / 9 * Real.log X := by rw [ha, Real.log_rpow hX0]
  have hinner : 3 * (1 + Real.log Z) ≤ Real.log X := by linarith
  have hsumq : ∑ q ∈ Qs, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) ≤ 1 / (K : ℝ) := by
    refine le_trans ?_ (sum_Ioc_inv_mul_pred_le K Qm hK)
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro j hj _
    have hj2 : (2 : ℝ) ≤ j := by
      have := (Finset.mem_Ioc.1 hj).1
      exact_mod_cast (show 2 ≤ j by omega)
    have : 0 < (j : ℝ) * ((j : ℝ) - 1) := mul_pos (by linarith) (by linarith)
    positivity
  calc (((Icc 1 ⌊X⌋₊).filter (LP22Bad K)).card : ℝ)
      ≤ ∑ m ∈ Icc 1 Z, ∑ q ∈ Qs, ((solSet (X / m) m q).card : ℝ) := hcard1
    _ ≤ ∑ m ∈ Icc 1 Z, ∑ q ∈ Qs, W q *
          (if Nat.gcd (q ^ 2) (aliq m) ∣ m then (Nat.gcd (q ^ 2) (aliq m) : ℝ) / m else 0) :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun q hq => hterm m hm q hq
    _ = ∑ q ∈ Qs, W q * ∑ m ∈ Icc 1 Z,
          (if Nat.gcd (q ^ 2) (aliq m) ∣ m then (Nat.gcd (q ^ 2) (aliq m) : ℝ) / m else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ q ∈ Qs, W q * Real.log X := by
        refine Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left ?_ (hWnn q hq)
        exact (sum_ite_div_le (Finset.mem_filter.1 hq).2 hZ1 (fun m => Nat.gcd (q ^ 2) (aliq m))
          (fun m => Nat.gcd_dvd_left _ _)).trans hinner
    _ = 54216 * X * ∑ q ∈ Qs, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q hq => ?_
        have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_filter.1 hq).2.two_le
        have : (q : ℝ) * ((q : ℝ) - 1) ≠ 0 := (mul_pos (by linarith) (by linarith)).ne'
        rw [hW]
        field_simp
    _ ≤ 54216 * X * (1 / (K : ℝ)) := mul_le_mul_of_nonneg_left hsumq (by positivity)
    _ = 54216 * X / K := by ring

end Principia.Common.LucaPomerance.LP22
