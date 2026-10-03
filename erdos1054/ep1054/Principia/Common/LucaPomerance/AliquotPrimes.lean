/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.LucaPomerance.Basic
import Principia.Common.LucaPomerance.Smooth
import Principia.Common.Sieve.BrunTitchmarshAP
import Principia.Common.Davenport.Concentration

set_option autoImplicit false

/-!
# `s(n)` rarely has many large prime factors (in reciprocal mass)

`T_w(n) = ∑_{p ∣ s(n), p > w} 1/p` (`bigPrimeRecip`). **Main result**
(`card_bigPrimeRecip_gt_le`): for fixed `u, w ≥ 1`, `δ, η > 0`, and all large `X`,
`#{n ≤ X : T_w(n) > δ} ≤ (4 C_M/u + (2/δ)(1 + 16064 u)/w + η) X`.

This is Erdős's "Lemma 4" of *On asymptotic properties of aliquot sequences* (1976), in the
fixed-parameter form Pollack's §3.1 remark derives from his Lemma 2.8; the proof here follows
Pollack's Lemma 2.7 (Illinois J. Math. 58 (2014)) restricted to **prime** moduli.

**Proof.** Put `v = X^{1/(2u)}`.
* `p > v`: `s(n) ≤ n² ≤ v^{4u}`, so `s(n)` has at most `4u` prime factors `> v`; they contribute
  `≤ 4u/v` (`sum_primeFactors_gt_le`).
* `w < p ≤ v`: for `n` with a prime `P ∥ n`, `P > v²`, write `n = mP`, `s(n) = P s(m) + σ(m)`.
  If `p ∣ s(m)` then `p ∣ m ∣ n`; otherwise `P` lies in one class mod `p`, and Brun–Titchmarsh
  (`X/(mp) ≥ v`) gives `≤ 2008 X/(m (p − 1) log v)` choices. So
  `#{n : p ∣ s(n)} ≤ (1 + 16064 u) X/p` (`card_good_dvd_le`) and Markov bounds the `n` whose sum
  over `w < p ≤ v` exceeds `δ/2` by `(2/δ)(1 + 16064u) X/w`.
* the other `n` are `v²`-smooth (`≤ √X + 4 C_M X/u`, `Smooth.lean`) or divisible by `P²` for a
  prime `P > v²` (`≤ 2X/v²`, `Common.Davenport.card_sq_dvd_le`).
-/

namespace Principia.Common.LucaPomerance.Pollack14

open Principia.Common.LucaPomerance.Aliquot

open Finset

/-- `T_w(n) = ∑_{p ∣ s(n), p > w} 1/p`. -/
noncomputable def bigPrimeRecip (w n : ℕ) : ℝ :=
  ∑ p ∈ (aliq n).primeFactors.filter (w < ·), (1 : ℝ) / p

theorem bigPrimeRecip_nonneg (w n : ℕ) : 0 ≤ bigPrimeRecip w n :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem sigma_le_sq (n : ℕ) : ArithmeticFunction.sigma 1 n ≤ n ^ 2 := by
  rw [ArithmeticFunction.sigma_one_apply]
  calc ∑ d ∈ n.divisors, d ≤ ∑ _d ∈ n.divisors, n :=
        Finset.sum_le_sum fun d hd => Nat.divisor_le hd
    _ = n.divisors.card * n := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n * n := Nat.mul_le_mul_right n (Nat.card_divisors_le_self n)
    _ = n ^ 2 := (sq n).symm

theorem aliq_le_sq (n : ℕ) : aliq n ≤ n ^ 2 :=
  (Nat.sub_le _ _).trans (sigma_le_sq n)

/-- The prime factors `> z` of `s ≤ z^c` have reciprocal sum at most `c/z`. -/
theorem sum_primeFactors_gt_le {s : ℕ} (hs : s ≠ 0) {z : ℝ} (hz : 1 < z) {c : ℕ}
    (hsz : (s : ℝ) ≤ z ^ c) :
    ∑ p ∈ s.primeFactors.filter (fun p : ℕ => z < p), (1 : ℝ) / p ≤ c / z := by
  set F := s.primeFactors.filter (fun p : ℕ => z < p) with hF
  have hprod : ∏ p ∈ F, p ∣ s :=
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd s)
  have hprodle : (∏ p ∈ F, (p : ℝ)) ≤ s := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hs) hprod
    have h' : ((∏ p ∈ F, p : ℕ) : ℝ) ≤ s := by exact_mod_cast this
    rwa [Nat.cast_prod] at h'
  have hzF : z ^ F.card ≤ ∏ p ∈ F, (p : ℝ) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => by linarith) (fun p hp => (Finset.mem_filter.1 hp).2.le)
  have hcard : F.card ≤ c := (pow_le_pow_iff_right₀ hz).1 (hzF.trans (hprodle.trans hsz))
  have hz0 : 0 < z := by linarith
  calc ∑ p ∈ F, (1 : ℝ) / p ≤ ∑ _p ∈ F, (1 : ℝ) / z :=
        Finset.sum_le_sum fun p hp =>
          one_div_le_one_div_of_le hz0 (Finset.mem_filter.1 hp).2.le
    _ = F.card / z := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ c / z := div_le_div_of_nonneg_right (by exact_mod_cast hcard) hz0.le

/-- `n` has a prime factor `P > y` dividing it exactly once. -/
def HasBigExactPrime (y : ℝ) (n : ℕ) : Prop :=
  ∃ P : ℕ, P.Prime ∧ P ∣ n ∧ ¬ P ^ 2 ∣ n ∧ y < (P : ℝ)

/-- The primes `P ≤ X/m`, `P > y`, with `p ∣ P s(m) + σ(m)`. -/
noncomputable def solP (X y : ℝ) (m p : ℕ) : Finset ℕ :=
  (Iic ⌊X / m⌋₊).filter
    (fun P : ℕ => P.Prime ∧ y < (P : ℝ) ∧ p ∣ P * aliq m + ArithmeticFunction.sigma 1 m)

/-- Brun–Titchmarsh for `solP` at a prime modulus `p ∤ s(m)`, `p ≤ v`. -/
theorem card_solP_le {X v : ℝ} (hX : 0 < X) (hv : 1 < v) {m p : ℕ} (hm : 1 ≤ m) (hp : p.Prime)
    (hpv : (p : ℝ) ≤ v) (hpm : ¬ p ∣ aliq m) :
    ((solP X (v ^ 2) m p).card : ℝ) ≤ 2008 * (X / m) / (((p : ℝ) - 1) * Real.log v) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hlogv : 0 < Real.log v := Real.log_pos hv
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hXm : 0 < X / m := div_pos hX hm0
  rcases (solP X (v ^ 2) m p).eq_empty_or_nonempty with he | ⟨P₀, hP₀⟩
  · rw [he, Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨hP₀T, hP₀p, hP₀v, hP₀d⟩ := Finset.mem_filter.1 hP₀
  have hP₀X : (P₀ : ℝ) ≤ X / m :=
    le_trans (by exact_mod_cast Finset.mem_Iic.1 hP₀T) (Nat.floor_le hXm.le)
  have hv2X : v ^ 2 < X / m := lt_of_lt_of_le hP₀v hP₀X
  have hpX : (p : ℝ) < X / m := by nlinarith
  have hgcd : Nat.gcd p (aliq m) = 1 :=
    Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  have hsub : solP X (v ^ 2) m p ⊆
      (Iic ⌊X / m⌋₊).filter (fun P => P.Prime ∧ P % p = P₀ % p) := by
    intro P hP
    obtain ⟨hPT, hPp, _, hPd⟩ := Finset.mem_filter.1 hP
    have h := modEq_of_dvd hp.pos hPd hP₀d
    rw [hgcd, Nat.div_one] at h
    exact Finset.mem_filter.2 ⟨hPT, hPp, h⟩
  have hBT := Principia.Common.BrunTitchmarshAP.brun_titchmarsh_ap p P₀ hp.one_lt.le (X / m) hpX
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one] at hBT
  have hratio : v ≤ X / m / p := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hlog : Real.log v ≤ Real.log (X / m / p) := Real.log_le_log (by linarith) hratio
  calc ((solP X (v ^ 2) m p).card : ℝ)
      ≤ 2008 * (X / m) / (((p : ℝ) - 1) * Real.log (X / m / p)) :=
        le_trans (by exact_mod_cast Finset.card_le_card hsub) hBT
    _ ≤ 2008 * (X / m) / (((p : ℝ) - 1) * Real.log v) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hlog hp1.le)

open Classical in
/-- **Count of `p ∣ s(n)`.** For `X ≥ e`, a prime `p ≤ v = X^{1/(2u)}`: at most
`(1 + 16064 u) X / p` integers `n ≤ X` with a prime `P ∥ n`, `P > v²`, have `p ∣ s(n)`. -/
theorem card_good_dvd_le {X : ℝ} (u : ℕ) (hu : 1 ≤ u) (hXe : Real.exp 1 ≤ X) {p : ℕ}
    (hp : p.Prime) (hpv : (p : ℝ) ≤ X ^ (((2 * u : ℕ) : ℝ)⁻¹)) :
    (((Icc 1 ⌊X⌋₊).filter (fun n =>
        HasBigExactPrime ((X ^ (((2 * u : ℕ) : ℝ)⁻¹)) ^ 2) n ∧ p ∣ aliq n)).card : ℝ) ≤
      (1 + 16064 * u) * X / p := by
  set v := X ^ (((2 * u : ℕ) : ℝ)⁻¹) with hvdef
  have hX1 : 1 < X := lt_of_lt_of_le (by have := Real.add_one_le_exp 1; linarith) hXe
  have hX0 : 0 < X := by linarith
  have hlogX1 : 1 ≤ Real.log X := by
    have := Real.log_le_log (Real.exp_pos 1) hXe
    rwa [Real.log_exp] at this
  have hu2 : (0 : ℝ) < ((2 * u : ℕ) : ℝ) := by
    have : 0 < 2 * u := by omega
    exact_mod_cast this
  have hv1 : 1 < v := Real.one_lt_rpow hX1 (inv_pos.2 hu2)
  have hlogv : Real.log v = Real.log X / ((2 * u : ℕ) : ℝ) := by
    rw [hvdef, Real.log_rpow hX0]
    ring
  have hlogv0 : 0 < Real.log v := Real.log_pos hv1
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  set N := ⌊X⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hNX : (N : ℝ) ≤ X := Nat.floor_le hX0.le
  set Ms := (Icc 1 N).filter (fun m => ¬ p ∣ aliq m) with hMs
  -- the covering
  have hcover : (Icc 1 N).filter (fun n => HasBigExactPrime (v ^ 2) n ∧ p ∣ aliq n) ⊆
      (Icc 1 N).filter (p ∣ ·) ∪ Ms.biUnion (fun m => (solP X (v ^ 2) m p).image (m * ·)) := by
    intro n hn
    obtain ⟨hnI, ⟨P, hPp, hPn, hP2, hvP⟩, hpd⟩ := Finset.mem_filter.1 hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.1 hnI
    set m := n / P with hm
    have hmP : m * P = n := Nat.div_mul_cancel hPn
    have hm0 : m ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hmP
      omega
    have hPm : ¬ P ∣ m := by
      rintro ⟨t, ht⟩
      apply hP2
      exact ⟨t, by rw [← hmP, ht]; ring⟩
    have hal : aliq n = P * aliq m + ArithmeticFunction.sigma 1 m := by
      rw [← hmP]
      exact aliq_mul_prime hPp hPm
    rw [hal] at hpd
    rw [Finset.mem_union]
    by_cases hps : p ∣ aliq m
    · left
      have h1 : Nat.gcd p (aliq m) ∣ m := gcd_dvd_self_of_dvd hpd
      rw [Nat.gcd_eq_left hps] at h1
      exact Finset.mem_filter.2 ⟨hnI, h1.trans (Dvd.intro P hmP)⟩
    · right
      rw [Finset.mem_biUnion]
      have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm0
      have hmN : m ≤ N := le_trans (Nat.le_of_dvd (by omega) (Dvd.intro P hmP)) hnN
      refine ⟨m, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hm1, hmN⟩, hps⟩, ?_⟩
      rw [Finset.mem_image]
      refine ⟨P, Finset.mem_filter.2 ⟨?_, hPp, hvP, hpd⟩, hmP⟩
      apply Finset.mem_Iic.2
      apply Nat.le_floor
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
      rw [le_div_iff₀ hmR]
      have : ((P * m : ℕ) : ℝ) ≤ X := by
        rw [mul_comm, hmP]
        exact le_trans (by exact_mod_cast hnN) hNX
      push_cast at this
      linarith
  -- the multiples of `p`
  have hmult : (((Icc 1 N).filter (p ∣ ·)).card : ℝ) ≤ X / p := by
    have hIcc : (Icc 1 N) = Ioc 0 N := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div N p]
    calc ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
      _ ≤ X / p := div_le_div_of_nonneg_right hNX (by linarith)
  -- the Brun–Titchmarsh part
  have hBTsum : ∑ m ∈ Ms, ((solP X (v ^ 2) m p).card : ℝ) ≤ 16064 * u * X / p := by
    have hterm : ∀ m ∈ Ms, ((solP X (v ^ 2) m p).card : ℝ) ≤
        2008 * X / (((p : ℝ) - 1) * Real.log v) * (1 / (m : ℝ)) := by
      intro m hm
      obtain ⟨hmI, hpm⟩ := Finset.mem_filter.1 hm
      have hm1 := (Finset.mem_Icc.1 hmI).1
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
      have h := card_solP_le hX0 hv1 hm1 hp hpv hpm
      calc ((solP X (v ^ 2) m p).card : ℝ) ≤ 2008 * (X / m) / (((p : ℝ) - 1) * Real.log v) := h
        _ = 2008 * X / (((p : ℝ) - 1) * Real.log v) * (1 / (m : ℝ)) := by
          field_simp
    have hharm : ∑ m ∈ Ms, (1 / (m : ℝ)) ≤ 2 * Real.log X := by
      calc ∑ m ∈ Ms, (1 / (m : ℝ)) ≤ ∑ m ∈ Icc 1 N, (1 / (m : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => by positivity)
        _ = ∑ m ∈ Icc 1 N, (m : ℝ)⁻¹ := by simp only [one_div]
        _ ≤ 1 + Real.log N := Aux.sum_inv_le_log N hN1
        _ ≤ 2 * Real.log X := by
            have : Real.log N ≤ Real.log X :=
              Real.log_le_log (by exact_mod_cast hN1) hNX
            linarith
    have hpref : 0 ≤ 2008 * X / (((p : ℝ) - 1) * Real.log v) := by positivity
    calc ∑ m ∈ Ms, ((solP X (v ^ 2) m p).card : ℝ)
        ≤ ∑ m ∈ Ms, 2008 * X / (((p : ℝ) - 1) * Real.log v) * (1 / (m : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = 2008 * X / (((p : ℝ) - 1) * Real.log v) * ∑ m ∈ Ms, (1 / (m : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ 2008 * X / (((p : ℝ) - 1) * Real.log v) * (2 * Real.log X) :=
          mul_le_mul_of_nonneg_left hharm hpref
      _ = 8032 * u * X / ((p : ℝ) - 1) := by
          rw [hlogv]
          push_cast
          field_simp
          ring
      _ ≤ 16064 * u * X / p := by
          rw [div_le_div_iff₀ hp1 (by linarith)]
          have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg u
          nlinarith [mul_nonneg hu0 hX0.le]
  -- assemble
  have hcard := Finset.card_le_card hcover
  have h1 := hcard.trans (Finset.card_union_le _ _)
  have h2 := Finset.card_biUnion_le (s := Ms)
    (t := fun m => (solP X (v ^ 2) m p).image (m * ·))
  have h3 : ∑ m ∈ Ms, ((solP X (v ^ 2) m p).image (m * ·)).card ≤
      ∑ m ∈ Ms, (solP X (v ^ 2) m p).card :=
    Finset.sum_le_sum fun m _ => Finset.card_image_le
  have htot : (((Icc 1 N).filter (fun n => HasBigExactPrime (v ^ 2) n ∧ p ∣ aliq n)).card : ℝ) ≤
      (((Icc 1 N).filter (p ∣ ·)).card : ℝ) + ∑ m ∈ Ms, ((solP X (v ^ 2) m p).card : ℝ) := by
    have := h1.trans (Nat.add_le_add_left (h2.trans h3) _)
    exact_mod_cast this
  calc (((Icc 1 N).filter (fun n => HasBigExactPrime (v ^ 2) n ∧ p ∣ aliq n)).card : ℝ)
      ≤ X / p + 16064 * u * X / p := htot.trans (add_le_add hmult hBTsum)
    _ = (1 + 16064 * u) * X / p := by ring

/-- `T_w(n) ≤ ∑_{w < p ≤ v, p ∣ s(n)} 1/p + 4u/v` when `n ≤ v^{2u}`. -/
theorem bigPrimeRecip_le {w n u : ℕ} {v : ℝ} (hv : 1 < v) (hn : (n : ℝ) ≤ v ^ (2 * u)) :
    bigPrimeRecip w n ≤
      ∑ p ∈ (Ioc w ⌊v⌋₊).filter Nat.Prime, (if p ∣ aliq n then (1 : ℝ) / p else 0) +
        ((4 * u : ℕ) : ℝ) / v := by
  unfold bigPrimeRecip
  set s := aliq n with hs
  rw [← Finset.sum_filter_add_sum_filter_not (s.primeFactors.filter (w < ·))
    (fun p : ℕ => (p : ℝ) ≤ v)]
  apply add_le_add
  · -- the primes `w < p ≤ v`
    have hsub : (s.primeFactors.filter (w < ·)).filter (fun p : ℕ => (p : ℝ) ≤ v) ⊆
        (Ioc w ⌊v⌋₊).filter Nat.Prime := by
      intro p hp
      obtain ⟨hp1, hpv⟩ := Finset.mem_filter.1 hp
      obtain ⟨hps, hwp⟩ := Finset.mem_filter.1 hp1
      exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨hwp, Nat.le_floor hpv⟩,
        Nat.prime_of_mem_primeFactors hps⟩
    calc ∑ p ∈ (s.primeFactors.filter (w < ·)).filter (fun p : ℕ => (p : ℝ) ≤ v), (1 : ℝ) / p
        = ∑ p ∈ (s.primeFactors.filter (w < ·)).filter (fun p : ℕ => (p : ℝ) ≤ v),
            (if p ∣ s then (1 : ℝ) / p else 0) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          have hps := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1
          rw [if_pos (Nat.dvd_of_mem_primeFactors hps)]
      _ ≤ ∑ p ∈ (Ioc w ⌊v⌋₊).filter Nat.Prime, (if p ∣ s then (1 : ℝ) / p else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by
            split_ifs
            · positivity
            · exact le_rfl)
  · -- the primes `p > v`
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · rw [hs0, Nat.primeFactors_zero]
      simp only [Finset.filter_empty, Finset.sum_empty]
      positivity
    have hsub : (s.primeFactors.filter (w < ·)).filter (fun p : ℕ => ¬ (p : ℝ) ≤ v) ⊆
        s.primeFactors.filter (fun p : ℕ => v < p) := by
      intro p hp
      obtain ⟨hp1, hpv⟩ := Finset.mem_filter.1 hp
      exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hp1).1, lt_of_not_ge hpv⟩
    have hsv : (s : ℝ) ≤ v ^ (4 * u) := by
      have h1 : (s : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast aliq_le_sq n
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      calc (s : ℝ) ≤ (n : ℝ) ^ 2 := h1
        _ ≤ (v ^ (2 * u)) ^ 2 := pow_le_pow_left₀ hn0 hn 2
        _ = v ^ (4 * u) := by rw [← pow_mul]; ring_nf
    calc ∑ p ∈ (s.primeFactors.filter (w < ·)).filter (fun p : ℕ => ¬ (p : ℝ) ≤ v), (1 : ℝ) / p
        ≤ ∑ p ∈ s.primeFactors.filter (fun p : ℕ => v < p), (1 : ℝ) / p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ ((4 * u : ℕ) : ℝ) / v := sum_primeFactors_gt_le hs0.ne' hv hsv


/-- `∑_{w < p ≤ v, p ∣ s(n)} 1/p`. -/
noncomputable def midRecip (w : ℕ) (v : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ (Ioc w ⌊v⌋₊).filter Nat.Prime, (if p ∣ aliq n then (1 : ℝ) / p else 0)

theorem midRecip_nonneg (w : ℕ) (v : ℝ) (n : ℕ) : 0 ≤ midRecip w v n :=
  Finset.sum_nonneg fun p _ => by
    split_ifs
    · positivity
    · exact le_rfl

/-- `∑_{p > w prime} 1/p² ≤ 1/w`. -/
theorem sum_prime_inv_sq_le (w M : ℕ) (hw : 1 ≤ w) :
    ∑ p ∈ (Ioc w M).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) * (p : ℝ)) ≤ 1 / (w : ℝ) := by
  refine le_trans ?_ (sum_Ioc_inv_mul_pred_le w M hw)
  calc ∑ p ∈ (Ioc w M).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) * (p : ℝ))
      ≤ ∑ p ∈ (Ioc w M).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.two_le
        apply one_div_le_one_div_of_le (mul_pos (by linarith) (by linarith))
        nlinarith
    _ ≤ ∑ j ∈ Ioc w M, (1 : ℝ) / ((j : ℝ) * ((j : ℝ) - 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro j hj _
        have hj2 : (2 : ℝ) ≤ j := by
          have := (Finset.mem_Ioc.1 hj).1
          exact_mod_cast (show 2 ≤ j by omega)
        have : 0 < (j : ℝ) * ((j : ℝ) - 1) := mul_pos (by linarith) (by linarith)
        positivity

open Classical in
/-- The total of `midRecip` over the `n ≤ X` with a prime `P ∥ n`, `P > v²`
(`v = X^{1/(2u)}`) is at most `(1 + 16064 u) X / w`. -/
theorem sum_midRecip_good_le {X : ℝ} (u w : ℕ) (hu : 1 ≤ u) (hw : 1 ≤ w)
    (hXe : Real.exp 1 ≤ X) :
    ∑ n ∈ (Icc 1 ⌊X⌋₊).filter (HasBigExactPrime ((X ^ (((2 * u : ℕ) : ℝ)⁻¹)) ^ 2)),
        midRecip w (X ^ (((2 * u : ℕ) : ℝ)⁻¹)) n ≤ (1 + 16064 * u) * X / w := by
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hv0 : 0 ≤ X ^ (((2 * u : ℕ) : ℝ)⁻¹) := (Real.rpow_pos_of_pos hX0 _).le
  have hC : 0 ≤ (1 + 16064 * (u : ℝ)) * X := by positivity
  unfold midRecip
  rw [Finset.sum_comm]
  calc ∑ p ∈ (Ioc w ⌊X ^ (((2 * u : ℕ) : ℝ)⁻¹)⌋₊).filter Nat.Prime,
        ∑ n ∈ (Icc 1 ⌊X⌋₊).filter (HasBigExactPrime ((X ^ (((2 * u : ℕ) : ℝ)⁻¹)) ^ 2)),
          (if p ∣ aliq n then (1 : ℝ) / p else 0)
      ≤ ∑ p ∈ (Ioc w ⌊X ^ (((2 * u : ℕ) : ℝ)⁻¹)⌋₊).filter Nat.Prime,
          (1 + 16064 * u) * X * ((1 : ℝ) / ((p : ℝ) * (p : ℝ))) := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨hpI, hpp⟩ := Finset.mem_filter.1 hp
        have hpv : (p : ℝ) ≤ X ^ (((2 * u : ℕ) : ℝ)⁻¹) :=
          le_trans (by exact_mod_cast (Finset.mem_Ioc.1 hpI).2) (Nat.floor_le hv0)
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_filter]
        have h := card_good_dvd_le u hu hXe hpp hpv
        calc (((Icc 1 ⌊X⌋₊).filter (fun n =>
              HasBigExactPrime ((X ^ (((2 * u : ℕ) : ℝ)⁻¹)) ^ 2) n ∧ p ∣ aliq n)).card : ℝ) *
              (1 / (p : ℝ))
            ≤ (1 + 16064 * u) * X / p * (1 / (p : ℝ)) :=
              mul_le_mul_of_nonneg_right h (by positivity)
          _ = (1 + 16064 * u) * X * ((1 : ℝ) / ((p : ℝ) * (p : ℝ))) := by
              field_simp
    _ = (1 + 16064 * u) * X * ∑ p ∈ (Ioc w ⌊X ^ (((2 * u : ℕ) : ℝ)⁻¹)⌋₊).filter Nat.Prime,
          ((1 : ℝ) / ((p : ℝ) * (p : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ (1 + 16064 * u) * X * (1 / (w : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_prime_inv_sq_le w _ hw) hC
    _ = (1 + 16064 * u) * X / w := by ring

open Classical in
/-- **Markov**: the good `n ≤ X` with `midRecip > δ/2` number at most
`(2/δ)(1 + 16064 u) X / w`. -/
theorem card_midRecip_gt_le {X δ : ℝ} (u w : ℕ) (hu : 1 ≤ u) (hw : 1 ≤ w)
    (hXe : Real.exp 1 ≤ X) (hδ : 0 < δ) :
    ((((Icc 1 ⌊X⌋₊).filter (HasBigExactPrime ((X ^ (((2 * u : ℕ) : ℝ)⁻¹)) ^ 2))).filter
        (fun n => δ / 2 < midRecip w (X ^ (((2 * u : ℕ) : ℝ)⁻¹)) n)).card : ℝ) ≤
      2 / δ * (1 + 16064 * u) / w * X := by
  have hsum := sum_midRecip_good_le u w hu hw hXe (X := X)
  have hmark : ((((Icc 1 ⌊X⌋₊).filter (HasBigExactPrime ((X ^ (((2 * u : ℕ) : ℝ)⁻¹)) ^ 2))).filter
        (fun n => δ / 2 < midRecip w (X ^ (((2 * u : ℕ) : ℝ)⁻¹)) n)).card : ℝ) * (δ / 2) ≤
      ∑ n ∈ (Icc 1 ⌊X⌋₊).filter (HasBigExactPrime ((X ^ (((2 * u : ℕ) : ℝ)⁻¹)) ^ 2)),
        midRecip w (X ^ (((2 * u : ℕ) : ℝ)⁻¹)) n := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine le_trans (Finset.sum_le_sum fun n hn => (Finset.mem_filter.1 hn).2.le) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => midRecip_nonneg _ _ n)
  have h := hmark.trans hsum
  have hδ2 : 0 < δ / 2 := by linarith
  rw [← le_div_iff₀ hδ2] at h
  calc _ ≤ (1 + 16064 * u) * X / w / (δ / 2) := h
    _ = 2 / δ * (1 + 16064 * u) / w * X := by
        field_simp

/-- The `v²`-smooth `n ≤ X = v^{2u}` number at most `X η/4 + 4 C_M X/u`. -/
theorem card_smooth_part_le {X v η : ℝ} (u : ℕ) (hu : 1 ≤ u) (hη : 0 < η) (hX4 : 4 ≤ X)
    (hXη : 16 / η ^ 2 ≤ X) (hv2 : 2 ≤ v) (hvpow : v ^ (2 * u) = X) :
    (((Icc 1 ⌊X⌋₊).filter (fun n : ℕ => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ v ^ 2)).card : ℝ) ≤
      X * (η / 4) + 4 * mertensConst / u * X := by
  have hX0 : 0 < X := by linarith
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have hNX : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX0.le
  have hN4 : 4 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX4)
  have hNhalf : X / 2 ≤ ((⌊X⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one X
    linarith
  have hy : (2 : ℝ) ≤ v ^ 2 := by nlinarith
  have h := card_smooth_le_mertens ⌊X⌋₊ (by omega) (v ^ 2) hy
  have hlogX : Real.log X = (2 * u : ℕ) * Real.log v := by
    rw [← hvpow, Real.log_pow]
  have hlogv2 : Real.log (v ^ 2) = Real.log X / u := by
    rw [Real.log_pow, hlogX]
    push_cast
    field_simp
  have hlogN : Real.log X / 2 ≤ Real.log (⌊X⌋₊ : ℕ) := by
    have h1 : Real.log (X / 2) ≤ Real.log (⌊X⌋₊ : ℕ) := Real.log_le_log (by linarith) hNhalf
    rw [Real.log_div hX0.ne' (by norm_num)] at h1
    have h2 : Real.log 4 ≤ Real.log X := Real.log_le_log (by norm_num) hX4
    have h3 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hsqrt : Real.sqrt (⌊X⌋₊ : ℕ) ≤ X * (η / 4) := by
    have h1 : Real.sqrt (⌊X⌋₊ : ℕ) ≤ Real.sqrt X := Real.sqrt_le_sqrt hNX
    have h2 : 4 / η ≤ Real.sqrt X := by
      rw [show 4 / η = Real.sqrt ((4 / η) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt
      rw [div_pow]
      norm_num
      exact hXη
    have h3 : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
    have h4 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
    have h5 : 1 ≤ Real.sqrt X * (η / 4) := by
      rw [div_le_iff₀ hη] at h2
      linarith
    nlinarith
  have hmain : 2 * ((⌊X⌋₊ : ℕ) : ℝ) * (mertensConst * Real.log (v ^ 2)) /
      Real.log (⌊X⌋₊ : ℕ) ≤ 4 * mertensConst / u * X := by
    rw [hlogv2, div_le_iff₀ (by linarith)]
    have hM := mertensConst_pos
    have e : 4 * mertensConst / u * X * (Real.log X / 2) ≤
        4 * mertensConst / u * X * Real.log (⌊X⌋₊ : ℕ) :=
      mul_le_mul_of_nonneg_left hlogN (by positivity)
    have e2 : 2 * ((⌊X⌋₊ : ℕ) : ℝ) * (mertensConst * (Real.log X / u)) ≤
        4 * mertensConst / u * X * (Real.log X / 2) := by
      have e3 : 2 * ((⌊X⌋₊ : ℕ) : ℝ) * (mertensConst * (Real.log X / u)) =
          (2 * mertensConst * Real.log X / u) * ((⌊X⌋₊ : ℕ) : ℝ) := by ring
      have e4 : 4 * mertensConst / u * X * (Real.log X / 2) =
          (2 * mertensConst * Real.log X / u) * X := by ring
      rw [e3, e4]
      exact mul_le_mul_of_nonneg_left hNX (by positivity)
    linarith
  linarith

/-- The primes in `(⌊v²⌋, N]`. -/
noncomputable def bigPrimes (v : ℝ) (N : ℕ) : Finset ℕ := (Ioc ⌊v ^ 2⌋₊ N).filter Nat.Prime

/-- The `n ≤ X` divisible by `P²` for a prime `P > v²` number at most `X η/2` once
`v ≥ max(2, 4/η)`. -/
theorem card_sq_part_le {X v η : ℝ} (hη : 0 < η) (hX0 : 0 < X) (hv2 : 2 ≤ v)
    (hvη : 4 / η ≤ v) :
    (((Icc 1 ⌊X⌋₊).filter
        (fun n => ∃ P ∈ bigPrimes v ⌊X⌋₊, P ^ 2 ∣ n)).card : ℝ) ≤
      X * (η / 2) := by
  have h := Principia.Common.Davenport.card_sq_dvd_le ⌊v ^ 2⌋₊ ⌊X⌋₊ ⌊X⌋₊
    (bigPrimes v ⌊X⌋₊) (fun P hP => by
      have := Finset.mem_Ioc.1 (Finset.mem_filter.1 hP).1
      exact ⟨this.1, this.2⟩)
  have hNX : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX0.le
  have hfl : v ^ 2 ≤ (⌊v ^ 2⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have hv2η : 4 / η ≤ v ^ 2 := by nlinarith
  have hdiv : (2 : ℝ) / ((⌊v ^ 2⌋₊ : ℝ) + 1) ≤ η / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have := (div_le_iff₀ hη).1 hv2η
    nlinarith
  calc _ ≤ ((⌊X⌋₊ : ℕ) : ℝ) * (2 / ((⌊v ^ 2⌋₊ : ℝ) + 1)) := h
    _ ≤ X * (η / 2) := mul_le_mul hNX hdiv (by positivity) hX0.le

open Classical in
/-- The covering: an `n ≤ X` with `T_w(n) > δ` is `v²`-smooth, or divisible by `P²` for a prime
`P > v²`, or good with `midRecip > δ/2` (when `4u/v ≤ δ/2`). -/
theorem bigPrimeRecip_cover {X δ : ℝ} (u w : ℕ) (hX0 : 0 < X) (hv1 : 1 < X ^ (((2 * u : ℕ) : ℝ)⁻¹))
    (hvpow : (X ^ (((2 * u : ℕ) : ℝ)⁻¹)) ^ (2 * u) = X)
    (htail : ((4 * u : ℕ) : ℝ) / X ^ (((2 * u : ℕ) : ℝ)⁻¹) ≤ δ / 2) :
    (Icc 1 ⌊X⌋₊).filter (fun n => δ < bigPrimeRecip w n) ⊆
      ((Icc 1 ⌊X⌋₊).filter (fun n : ℕ => ∀ p ∈ n.primeFactors,
          ((p : ℕ) : ℝ) ≤ (X ^ (((2 * u : ℕ) : ℝ)⁻¹)) ^ 2) ∪
        (Icc 1 ⌊X⌋₊).filter (fun n => ∃ P ∈ bigPrimes (X ^ (((2 * u : ℕ) : ℝ)⁻¹)) ⌊X⌋₊,
          P ^ 2 ∣ n)) ∪
        ((Icc 1 ⌊X⌋₊).filter (HasBigExactPrime ((X ^ (((2 * u : ℕ) : ℝ)⁻¹)) ^ 2))).filter
          (fun n => δ / 2 < midRecip w (X ^ (((2 * u : ℕ) : ℝ)⁻¹)) n) := by
  set v := X ^ (((2 * u : ℕ) : ℝ)⁻¹) with hvdef
  intro n hn
  obtain ⟨hnI, hnδ⟩ := Finset.mem_filter.1 hn
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.1 hnI
  rw [Finset.mem_union, Finset.mem_union]
  by_cases hgood : HasBigExactPrime (v ^ 2) n
  · right
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hnI, hgood⟩, ?_⟩
    have hnv : (n : ℝ) ≤ v ^ (2 * u) := by
      rw [hvpow]
      exact le_trans (by exact_mod_cast hnN) (Nat.floor_le hX0.le)
    have hle := bigPrimeRecip_le (w := w) hv1 hnv
    have : bigPrimeRecip w n ≤ midRecip w v n + ((4 * u : ℕ) : ℝ) / v := hle
    linarith
  · left
    by_cases hsm : ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ v ^ 2
    · left
      exact Finset.mem_filter.2 ⟨hnI, hsm⟩
    · right
      push Not at hsm
      obtain ⟨P, hP, hvP⟩ := hsm
      have hPp := Nat.prime_of_mem_primeFactors hP
      have hPn := Nat.dvd_of_mem_primeFactors hP
      have hP2 : P ^ 2 ∣ n := by
        by_contra h
        exact hgood ⟨P, hPp, hPn, h, hvP⟩
      refine Finset.mem_filter.2 ⟨hnI, P, Finset.mem_filter.2 ⟨?_, hPp⟩, hP2⟩
      show P ∈ Ioc ⌊v ^ 2⌋₊ ⌊X⌋₊
      refine Finset.mem_Ioc.2 ⟨?_, le_trans (Nat.le_of_dvd (by omega) hPn) hnN⟩
      exact (Nat.floor_lt (by positivity)).2 hvP

open Classical in
/-- **Erdős's Lemma 4, fixed-parameter form.** For `u, w ≥ 1` and `δ, η > 0`, for all large `X`,
`#{n ≤ X : ∑_{p ∣ s(n), p > w} 1/p > δ} ≤ (4 C_M/u + (2/δ)(1 + 16064 u)/w + η) X`. -/
theorem card_bigPrimeRecip_gt_le (u w : ℕ) (hu : 1 ≤ u) (hw : 1 ≤ w) {δ : ℝ} (hδ : 0 < δ)
    {η : ℝ} (hη : 0 < η) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      (((Icc 1 ⌊X⌋₊).filter (fun n => δ < bigPrimeRecip w n)).card : ℝ) ≤
        (4 * mertensConst / u + 2 / δ * (1 + 16064 * u) / w + η) * X := by
  refine ⟨max (max 4 (Real.exp 1))
    (max ((max 2 (max (8 * u / δ) (4 / η))) ^ (2 * u)) (16 / η ^ 2)), fun X hX => ?_⟩
  have hX4 : 4 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXV : (max 2 (max (8 * u / δ) (4 / η))) ^ (2 * u) ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXη : 16 / η ^ 2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hX0 : 0 < X := by linarith
  have h2u : 2 * u ≠ 0 := by omega
  have hV₀0 : 0 ≤ max 2 (max (8 * u / δ) (4 / η)) := le_trans (by norm_num) (le_max_left _ _)
  have hvV : max 2 (max (8 * u / δ) (4 / η)) ≤ X ^ (((2 * u : ℕ) : ℝ)⁻¹) := by
    have h := Real.rpow_le_rpow (by positivity) hXV (inv_nonneg.2 (Nat.cast_nonneg (2 * u)))
    rwa [Real.pow_rpow_inv_natCast hV₀0 h2u] at h
  have hv2 : 2 ≤ X ^ (((2 * u : ℕ) : ℝ)⁻¹) := le_trans (le_max_left _ _) hvV
  have hvδ : 8 * u / δ ≤ X ^ (((2 * u : ℕ) : ℝ)⁻¹) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hvV
  have hvη : 4 / η ≤ X ^ (((2 * u : ℕ) : ℝ)⁻¹) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hvV
  have hvpow : (X ^ (((2 * u : ℕ) : ℝ)⁻¹)) ^ (2 * u) = X := Real.rpow_inv_natCast_pow hX0.le h2u
  have htail : ((4 * u : ℕ) : ℝ) / X ^ (((2 * u : ℕ) : ℝ)⁻¹) ≤ δ / 2 := by
    have h4u : ((4 * u : ℕ) : ℝ) = 4 * (u : ℝ) := by push_cast; ring
    rw [h4u, div_le_iff₀ (by linarith)]
    have := (div_le_iff₀ hδ).1 hvδ
    linarith
  have hcov := bigPrimeRecip_cover u w (δ := δ) hX0 (by linarith) hvpow htail
  have hSm := card_smooth_part_le u hu hη hX4 hXη hv2 hvpow
  have hSq := card_sq_part_le hη hX0 hv2 hvη
  have hGB := card_midRecip_gt_le u w hu hw hXe hδ (X := X)
  have h1 := (Finset.card_le_card hcov).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have h2 : (((Icc 1 ⌊X⌋₊).filter (fun n => δ < bigPrimeRecip w n)).card : ℝ) ≤
      (X * (η / 4) + 4 * mertensConst / u * X) + X * (η / 2) +
        2 / δ * (1 + 16064 * u) / w * X := by
    have h1' : (((Icc 1 ⌊X⌋₊).filter (fun n => δ < bigPrimeRecip w n)).card : ℝ) ≤
        (((Icc 1 ⌊X⌋₊).filter (fun n : ℕ => ∀ p ∈ n.primeFactors,
          ((p : ℕ) : ℝ) ≤ (X ^ (((2 * u : ℕ) : ℝ)⁻¹)) ^ 2)).card : ℝ) +
        (((Icc 1 ⌊X⌋₊).filter (fun n => ∃ P ∈ bigPrimes (X ^ (((2 * u : ℕ) : ℝ)⁻¹)) ⌊X⌋₊,
          P ^ 2 ∣ n)).card : ℝ) +
        ((((Icc 1 ⌊X⌋₊).filter (HasBigExactPrime ((X ^ (((2 * u : ℕ) : ℝ)⁻¹)) ^ 2))).filter
          (fun n => δ / 2 < midRecip w (X ^ (((2 * u : ℕ) : ℝ)⁻¹)) n)).card : ℝ) := by
      exact_mod_cast h1
    linarith
  have hηX : 0 ≤ η * X := by positivity
  have e : (4 * mertensConst / u + 2 / δ * (1 + 16064 * u) / w + η) * X =
      4 * mertensConst / u * X + 2 / δ * (1 + 16064 * u) / w * X + η * X := by ring
  rw [e]
  linarith

end Principia.Common.LucaPomerance.Pollack14
