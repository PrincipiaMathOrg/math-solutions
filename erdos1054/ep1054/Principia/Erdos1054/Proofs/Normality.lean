/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Density
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) — package `Normality`

Proofs of the spine obligations

* `link_Lem_FixedModulusNormality : Spine.Link_Lem_FixedModulusNormality`
  (lem:fixed-modulus-normality, lines 452–480, from `Std_recipPrimesAP_diverges`);
* `link_Lem_SigmaRangeZero : Spine.Link_Lem_SigmaRangeZero`
  (lem:sigma-range-zero, lines 484–498, from `Lem_FixedModulusNormality`);
* `link_Lem_SigmaRate_B2 : Spine.Link_Lem_SigmaRate_B2`
  (lem:sigma-rate, second assertion, line 518 / proof 558–559, from `Std_sigma_odd_iff`);

and of the two inputs

* `input_Std_sigma_odd_iff : Std_sigma_odd_iff` (`σ(n)` odd iff `n` is a square or twice a square);
* `input_Std_totient_sigma : Std_totient_sigma` (`v/φ(v) ≤ ζ(2) σ(v)/v`), via the Euler product
  of `n ↦ n⁻²` over the prime factors of `v` (Mathlib `EulerProduct`) and `∑ 1/n² = π²/6`
  (Mathlib `hasSum_zeta_two`).

## Route of `lem:fixed-modulus-normality`

Ported from the certified master `Erdos1054_3rdMomentProof.lean` (namespace `Represented`:
`forced_sigma_factor`, `sieve_prod_small`, `crt_count_mul`, `density_S_le`, `sigma_avoid`), where
it is proved for a prime modulus. The prime hypothesis there is only used for the divergence of
`∑_{p ≡ −1 (q)} 1/p`, which here is the hypothesis `Std_recipPrimesAP_diverges` of the link, for
every prime power `q`. Steps:

1. `dvd_sigma_of_exact`: `r ≡ −1 (mod q)` prime, `r ∥ n` ⟹ `q ∣ σ(r) ∣ σ(n)`.
2. `hasDens_noExact`: the set of `n` with no `r ∈ 𝒫` exactly dividing `n` is periodic modulo
   `∏ r²` and (Chinese remainder theorem) has density `∏ (1 − 1/r + 1/r²)`.
3. `exists_noExact_prod_le`: the divergence makes that product `≤ ε` for a suitable finite `𝒫`.
4. `densZero_not_dvd_sigma`: hence `{n : q ∤ σ(n)}` has upper density `0`, for every `q` whose
   class `−1` has divergent reciprocal prime sum.
5. `not_dvd_subset` + `densZero_biUnion`: the union bound over the prime-power factors of `V`.
-/

namespace Principia.Erdos1054.Proofs.Normality

open Finset Filter
open scoped Topology

/-! ## 1. Parity of `σ` -/

/-- The geometric sum `∑_{i ≤ k} 2^i` is odd. -/
theorem odd_sum_range_two_pow (k : ℕ) : Odd (∑ i ∈ Finset.range (k + 1), 2 ^ i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    exact ih.add_even ((Nat.even_pow).mpr ⟨even_two, Nat.succ_ne_zero k⟩)

/-- For odd `p`, `∑_{j ≤ k} p^j ≡ k + 1 (mod 2)`. -/
theorem sum_range_pow_mod_two {p : ℕ} (hp : p % 2 = 1) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), p ^ j) % 2 = (k + 1) % 2 := by
  rw [Finset.sum_nat_mod,
    Finset.sum_congr rfl (fun j _ => by rw [Nat.pow_mod, hp, one_pow])]
  simp

/-- If `σ(n)` is odd, every odd prime divides `n` to an even power. -/
theorem even_factorization_of_sigma_odd {n : ℕ} (hn : n ≠ 0)
    (hodd : Odd (ArithmeticFunction.sigma 1 n)) :
    ∀ p ∈ n.primeFactors, p ≠ 2 → Even (n.factorization p) := by
  intro p hp hp2
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hpp.odd_of_ne_two hp2)
  have hdvd : ArithmeticFunction.sigma 1 (p ^ n.factorization p) ∣
      ArithmeticFunction.sigma 1 n := by
    conv_rhs => rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn,
      Finsupp.prod]
    exact Finset.dvd_prod_of_mem (fun q => ArithmeticFunction.sigma 1 (q ^ n.factorization q))
      (by rw [Nat.support_factorization]; exact hp)
  have hfac : Odd (ArithmeticFunction.sigma 1 (p ^ n.factorization p)) := by
    obtain ⟨c, hc⟩ := hdvd
    have h := hodd
    rw [hc, Nat.odd_mul] at h
    exact h.1
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hpp] at hfac
  rw [Nat.odd_iff, sum_range_pow_mod_two hpodd] at hfac
  rw [Nat.even_iff]
  omega

/-- **σ-parity, forward** (ported from the master's `sigma_odd_imp_sq_or_twosq`): if `σ(n)` is odd
then `n` is a square or twice a square. -/
theorem sq_or_twice_sq_of_sigma_odd {d : ℕ} (hd0 : d ≠ 0)
    (hodd : Odd (ArithmeticFunction.sigma 1 d)) : ∃ s, d = s ^ 2 ∨ d = 2 * s ^ 2 := by
  have hev := even_factorization_of_sigma_odd hd0 hodd
  set a := d.factorization 2 with ha
  have hdvd2 : 2 ^ a ∣ d := Nat.ordProj_dvd d 2
  set o := d / 2 ^ a with ho
  have hdeq : d = 2 ^ a * o := (Nat.mul_div_cancel' hdvd2).symm
  have ho0 : o ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hdeq
    exact hd0 hdeq
  have h2a0 : (2 : ℕ) ^ a ≠ 0 := by positivity
  have hod : o ∣ d := ⟨2 ^ a, by rw [hdeq, mul_comm]⟩
  have hoodd : ¬ (2 ∣ o) := Nat.not_dvd_ordCompl Nat.prime_two hd0
  have hfacto : ∀ p, p ≠ 2 → o.factorization p = d.factorization p := by
    intro p hp2
    rw [hdeq, Nat.factorization_mul h2a0 ho0, Finsupp.add_apply, Nat.factorization_pow,
      Finsupp.smul_apply, Nat.Prime.factorization Nat.prime_two, Finsupp.single_apply,
      if_neg (Ne.symm hp2), smul_zero, zero_add]
  have hosq : ∃ s, o = s ^ 2 := by
    refine ⟨∏ p ∈ o.primeFactors, p ^ (o.factorization p / 2), ?_⟩
    rw [← Finset.prod_pow]
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self ho0, Finsupp.prod,
      Nat.support_factorization]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp2 : p ≠ 2 := fun h => hoodd (h ▸ Nat.dvd_of_mem_primeFactors hp)
    have hpd : p ∈ d.primeFactors := Nat.primeFactors_mono hod hd0 hp
    have heven : Even (o.factorization p) := by rw [hfacto p hp2]; exact hev p hpd hp2
    rw [← pow_mul, Nat.div_mul_cancel heven.two_dvd]
  obtain ⟨s, hs⟩ := hosq
  rcases Nat.even_or_odd a with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact ⟨2 ^ b * s, Or.inl (by rw [hdeq, hs, hb]; ring)⟩
  · exact ⟨2 ^ b * s, Or.inr (by rw [hdeq, hs, hb]; ring)⟩

/-- **σ-parity, backward**: if every odd prime divides `n` to an even power, `σ(n)` is odd. -/
theorem sigma_odd_of_even_factorization {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors, p ≠ 2 → Even (n.factorization p)) :
    Odd (ArithmeticFunction.sigma 1 n) := by
  rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn, Finsupp.prod,
    Nat.support_factorization]
  refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one ?_
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hpp]
  by_cases hp2 : p = 2
  · subst hp2
    exact odd_sum_range_two_pow _
  · have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hpp.odd_of_ne_two hp2)
    rw [Nat.odd_iff, sum_range_pow_mod_two hpodd]
    obtain ⟨r, hr⟩ := h p hp hp2
    omega

/-! ## 2. Counting helpers for `cnt` -/

open Classical in
/-- `cnt S X` is at most the size of any finset containing `S ∩ [1, X]`. -/
theorem cnt_le_card_of_subset {S : Set ℕ} {X : ℝ} (T : Finset ℕ)
    (h : ∀ n, 1 ≤ n → n ≤ ⌊X⌋₊ → n ∈ S → n ∈ T) : cnt S X ≤ T.card := by
  unfold cnt
  apply Finset.card_le_card
  intro n hn
  rw [mem_cntFinset] at hn
  exact h n hn.1.1 hn.1.2 hn.2

open Classical in
/-- If every element of `S ∩ [1, X]` is the image under `φ` of an element of `B ∩ [1, X]`, then
`cnt S X ≤ cnt B X`. -/
theorem cnt_le_cnt_of_image {S B : Set ℕ} (φ : ℕ → ℕ) {X : ℝ}
    (h : ∀ N, 1 ≤ N → N ≤ ⌊X⌋₊ → N ∈ S → ∃ n, 1 ≤ n ∧ n ≤ ⌊X⌋₊ ∧ n ∈ B ∧ φ n = N) :
    cnt S X ≤ cnt B X := by
  unfold cnt
  calc ((Finset.Icc 1 ⌊X⌋₊).filter (· ∈ S)).card
      ≤ (((Finset.Icc 1 ⌊X⌋₊).filter (· ∈ B)).image φ).card := by
        apply Finset.card_le_card
        intro N hN
        rw [mem_cntFinset] at hN
        obtain ⟨n, h1, h2, h3, h4⟩ := h N hN.1.1 hN.1.2 hN.2
        rw [Finset.mem_image]
        exact ⟨n, mem_cntFinset.2 ⟨⟨h1, h2⟩, h3⟩, h4⟩
    _ ≤ ((Finset.Icc 1 ⌊X⌋₊).filter (· ∈ B)).card := Finset.card_image_le

/-- `n ≤ σ(n)` for `n ≥ 1`. -/
theorem le_sig {n : ℕ} (hn : n ≠ 0) : n ≤ sig n := by
  show n ≤ ArithmeticFunction.sigma 1 n
  rw [ArithmeticFunction.sigma_one_apply]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le i) (Nat.mem_divisors_self n hn)

/-! ## 3. The forced factor and the exact-division sieve -/

/-- `p % q = q − 1` with `q ≥ 1` means `q ∣ p + 1`. -/
theorem dvd_succ_of_mod_eq {p q : ℕ} (hq : 1 ≤ q) (h : p % q = q - 1) : q ∣ p + 1 := by
  refine ⟨p / q + 1, ?_⟩
  have h1 := Nat.div_add_mod p q
  rw [mul_add, mul_one]
  generalize q * (p / q) = t at h1 ⊢
  generalize p % q = r at h h1
  omega

/-- **Forced σ-factor** (paper line 465; master `forced_sigma_factor`): if the prime `p` divides
`n` exactly once and `q ∣ p + 1`, then `q ∣ σ(p) ∣ σ(n)`. -/
theorem dvd_sigma_of_exact {q p n : ℕ} (hp : p.Prime) (hqp : q ∣ p + 1)
    (hpn : p ∣ n) (hp2n : ¬ p ^ 2 ∣ n) : q ∣ sig n := by
  obtain ⟨m, rfl⟩ := hpn
  have hpm : ¬ p ∣ m := fun h => by
    obtain ⟨k, rfl⟩ := h
    exact hp2n ⟨k, by ring⟩
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
  have hsp : ArithmeticFunction.sigma 1 p = p + 1 := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.Prime.divisors hp,
      Finset.sum_pair hp.one_lt.ne]
    omega
  show q ∣ ArithmeticFunction.sigma 1 (p * m)
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsp]
  exact Dvd.dvd.mul_right hqp _

/-- `NoExact s n`: no `p ∈ s` divides `n` exactly once (`p ∣ n`, `p² ∤ n`). -/
def NoExact (s : Finset ℕ) (n : ℕ) : Prop := ∀ p ∈ s, ¬ (p ∣ n ∧ ¬ p ^ 2 ∣ n)

instance NoExact.decPred (s : Finset ℕ) : DecidablePred (NoExact s) := fun n => by
  unfold NoExact
  infer_instance

/-- The single-prime predicate is periodic with period `p²`. -/
theorem single_periodic (p : ℕ) :
    Function.Periodic (fun n => ¬ (p ∣ n ∧ ¬ p ^ 2 ∣ n)) (p ^ 2) := by
  intro n
  have e1 : p ∣ n + p ^ 2 ↔ p ∣ n := by
    rw [add_comm]
    exact Nat.dvd_add_right (dvd_pow_self p two_ne_zero)
  have e2 : p ^ 2 ∣ n + p ^ 2 ↔ p ^ 2 ∣ n := Nat.dvd_add_self_right
  simp only [e1, e2]

/-- `NoExact s` is periodic modulo `∏_{p ∈ s} p²`. -/
theorem noExact_periodic (s : Finset ℕ) :
    Function.Periodic (NoExact s) (∏ p ∈ s, p ^ 2) := by
  intro n
  simp only [NoExact, eq_iff_iff]
  refine forall_congr' fun p => imp_congr_right fun hp => ?_
  have hpdvd : p ^ 2 ∣ ∏ p ∈ s, p ^ 2 := Finset.dvd_prod_of_mem _ hp
  have e1 : p ∣ n + ∏ p ∈ s, p ^ 2 ↔ p ∣ n := by
    rw [add_comm]
    exact Nat.dvd_add_right (dvd_trans (dvd_pow_self p two_ne_zero) hpdvd)
  have e2 : p ^ 2 ∣ n + ∏ p ∈ s, p ^ 2 ↔ p ^ 2 ∣ n := by
    rw [add_comm]
    exact Nat.dvd_add_right hpdvd
  simp only [e1, e2]

/-- **CRT count is multiplicative over coprime moduli** (master `crt_count_mul`). -/
theorem crt_count_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b)
    (Pa Pb : ℕ → Prop) [DecidablePred Pa] [DecidablePred Pb]
    (hPa : Function.Periodic Pa a) (hPb : Function.Periodic Pb b) :
    (a * b).count (fun n => Pa n ∧ Pb n) = a.count Pa * b.count Pb := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range,
    Nat.count_eq_card_filter_range, ← Finset.card_product, ← Finset.filter_product]
  refine Finset.card_nbij' (fun n => (n % a, n % b))
    (fun x => (Nat.chineseRemainder hab x.1 x.2 : ℕ)) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnlt, hPan, hPbn⟩ := hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨Nat.mod_lt _ (Nat.pos_of_ne_zero ha), Nat.mod_lt _ (Nat.pos_of_ne_zero hb)⟩, ?_, ?_⟩
    · rw [hPa.map_mod_nat]; exact hPan
    · rw [hPb.map_mod_nat]; exact hPbn
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
    obtain ⟨⟨hx1, hx2⟩, hPax, hPbx⟩ := hx
    have hka : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % a = x.1 := by
      have h2 : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % a = x.1 % a :=
        (Nat.chineseRemainder hab x.1 x.2).prop.1
      rwa [Nat.mod_eq_of_lt hx1] at h2
    have hkb : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % b = x.2 := by
      have h2 : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % b = x.2 % b :=
        (Nat.chineseRemainder hab x.1 x.2).prop.2
      rwa [Nat.mod_eq_of_lt hx2] at h2
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.chineseRemainder_lt_mul hab x.1 x.2 ha hb, ?_, ?_⟩
    · rw [← hPa.map_mod_nat, hka]; exact hPax
    · rw [← hPb.map_mod_nat, hkb]; exact hPbx
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnlt, -, -⟩ := hn
    show (Nat.chineseRemainder hab (n % a) (n % b) : ℕ) = n
    have hca : (Nat.chineseRemainder hab (n % a) (n % b) : ℕ) ≡ n [MOD a] :=
      (Nat.chineseRemainder hab (n % a) (n % b)).prop.1.trans (Nat.mod_modEq n a)
    have hcb : (Nat.chineseRemainder hab (n % a) (n % b) : ℕ) ≡ n [MOD b] :=
      (Nat.chineseRemainder hab (n % a) (n % b)).prop.2.trans (Nat.mod_modEq n b)
    have hcab : (Nat.chineseRemainder hab (n % a) (n % b) : ℕ) ≡ n [MOD a * b] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨hca, hcb⟩
    have hclt : (Nat.chineseRemainder hab (n % a) (n % b) : ℕ) < a * b :=
      Nat.chineseRemainder_lt_mul hab (n % a) (n % b) ha hb
    have hmod := Nat.mod_eq_of_modEq hcab hnlt
    rwa [Nat.mod_eq_of_lt hclt] at hmod
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_range] at hx
    obtain ⟨⟨hx1, hx2⟩, -, -⟩ := hx
    have hka : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % a = x.1 := by
      have h2 : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % a = x.1 % a :=
        (Nat.chineseRemainder hab x.1 x.2).prop.1
      rwa [Nat.mod_eq_of_lt hx1] at h2
    have hkb : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % b = x.2 := by
      have h2 : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % b = x.2 % b :=
        (Nat.chineseRemainder hab x.1 x.2).prop.2
      rwa [Nat.mod_eq_of_lt hx2] at h2
    show ((Nat.chineseRemainder hab x.1 x.2 : ℕ) % a,
      (Nat.chineseRemainder hab x.1 x.2 : ℕ) % b) = x
    rw [hka, hkb]

/-- Among `0 ≤ r < p²` exactly `p² − (p − 1)` residues are not exactly divisible by the prime `p`
(master `single_prime_count`). -/
theorem single_count (p : ℕ) (hp : p.Prime) :
    (p ^ 2).count (fun n => ¬ (p ∣ n ∧ ¬ p ^ 2 ∣ n)) = p ^ 2 - (p - 1) := by
  have hp0 : 0 < p := hp.pos
  have hbad : (p ^ 2).count (fun n => p ∣ n ∧ ¬ p ^ 2 ∣ n) = p - 1 := by
    rw [Nat.count_eq_card_filter_range]
    have hset : (Finset.range (p ^ 2)).filter (fun n => p ∣ n ∧ ¬ p ^ 2 ∣ n)
        = (Finset.Ico 1 p).image (fun k => k * p) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_Ico]
      constructor
      · rintro ⟨hnlt, ⟨k, rfl⟩, hns⟩
        refine ⟨k, ⟨?_, ?_⟩, by ring⟩
        · rcases Nat.eq_zero_or_pos k with rfl | hkpos
          · exact absurd (show p ^ 2 ∣ p * 0 from ⟨0, by ring⟩) hns
          · exact hkpos
        · by_contra hge
          push_neg at hge
          have hmul : p * p ≤ p * k := Nat.mul_le_mul (le_refl p) hge
          rw [pow_two] at hnlt
          omega
      · rintro ⟨k, ⟨hk1, hkp⟩, rfl⟩
        refine ⟨?_, ⟨k, by ring⟩, ?_⟩
        · rw [pow_two]
          exact mul_lt_mul_of_pos_right hkp hp0
        · intro hdvd
          rw [pow_two] at hdvd
          have hpk : p ∣ k := (mul_dvd_mul_iff_right hp0.ne').mp hdvd
          have := Nat.le_of_dvd (by omega) hpk
          omega
    rw [hset, Finset.card_image_of_injective _
      (fun x y h => Nat.eq_of_mul_eq_mul_right hp0 h), Nat.card_Ico]
  have hcompl : (p ^ 2).count (fun n => ¬ (p ∣ n ∧ ¬ p ^ 2 ∣ n))
      + (p ^ 2).count (fun n => p ∣ n ∧ ¬ p ^ 2 ∣ n) = p ^ 2 := by
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range, add_comm,
      Finset.card_filter_add_card_filter_not, Finset.card_range]
  omega

/-- **Good-residue count factorizes (CRT)** (master `good_count_eq`). -/
theorem count_noExact (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p ^ 2).count (NoExact s) = ∏ p ∈ s, (p ^ 2 - (p - 1)) := by
  revert hs
  induction s using Finset.induction_on with
  | empty =>
    intro _
    rw [Finset.prod_empty, Finset.prod_empty, Nat.count_eq_card_filter_range,
      Finset.filter_true_of_mem (fun x _ => by simp [NoExact]), Finset.card_range]
  | insert p₀ s hp₀ ih =>
    intro hs
    have hp₀p : p₀.Prime := hs p₀ (Finset.mem_insert_self p₀ s)
    have hsp : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have ha : p₀ ^ 2 ≠ 0 := pow_ne_zero _ hp₀p.ne_zero
    have hb : (∏ p ∈ s, p ^ 2) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hsp p hp).ne_zero
    have hcop : (p₀ ^ 2).Coprime (∏ p ∈ s, p ^ 2) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      have hne : p₀ ≠ p := by
        rintro rfl
        exact hp₀ hp
      exact ((Nat.coprime_primes hp₀p (hsp p hp)).mpr hne).pow 2 2
    rw [Finset.prod_insert hp₀, Finset.prod_insert hp₀]
    have hbridge : (p₀ ^ 2 * ∏ p ∈ s, p ^ 2).count (NoExact (insert p₀ s))
        = (p₀ ^ 2 * ∏ p ∈ s, p ^ 2).count
            (fun n => (fun n => ¬ (p₀ ∣ n ∧ ¬ p₀ ^ 2 ∣ n)) n ∧ NoExact s n) := by
      rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
      exact congrArg Finset.card (Finset.filter_congr (fun n _ => by
        simp only [NoExact, Finset.forall_mem_insert]))
    rw [hbridge, crt_count_mul ha hb hcop (fun n => ¬ (p₀ ∣ n ∧ ¬ p₀ ^ 2 ∣ n)) (NoExact s)
        (single_periodic p₀) (noExact_periodic s), single_count p₀ hp₀p, ih hsp]

/-- **CRT density** of the exact-division sieve: `{n : no p ∈ s divides n exactly once}` has
density `∏_{p ∈ s} (1 − 1/p + 1/p²)` (paper lines 470–475). -/
theorem hasDens_noExact (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    HasDens {n | NoExact s n} (∏ p ∈ s, (1 - ((1 : ℝ) / p - 1 / (p : ℝ) ^ 2))) := by
  have hM0 : 0 < ∏ p ∈ s, p ^ 2 := Finset.prod_pos fun p hp => pow_pos (hs p hp).pos 2
  have hS : ∀ N, N ∈ {n | NoExact s n} ↔ N % (∏ p ∈ s, p ^ 2) ∈ {n | NoExact s n} := by
    intro N
    simp only [Set.mem_setOf_eq]
    rw [(noExact_periodic s).map_mod_nat N]
  have h1 : HasDens {n | NoExact s n}
      (((∏ p ∈ s, p ^ 2).count (NoExact s) : ℝ) / ((∏ p ∈ s, p ^ 2 : ℕ) : ℝ)) := by
    have h := hasDens_of_mem_iff_mod_mem hM0 hS
    convert h using 3
    rw [Nat.count_eq_card_filter_range]
    congr 1
    ext n
    simp only [Finset.mem_filter, Set.mem_setOf_eq]
  have hval : ((∏ p ∈ s, (p ^ 2 - (p - 1)) : ℕ) : ℝ)
      = ((∏ p ∈ s, p ^ 2 : ℕ) : ℝ) * ∏ p ∈ s, (1 - ((1 : ℝ) / p - 1 / (p : ℝ) ^ 2)) := by
    rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hs p hp).ne_zero
    have hle1 : 1 ≤ p := (hs p hp).one_lt.le
    have hle2 : p - 1 ≤ p ^ 2 := le_trans (Nat.sub_le p 1) (by nlinarith)
    rw [Nat.cast_sub hle2, Nat.cast_pow, Nat.cast_sub hle1, Nat.cast_one]
    field_simp
  have hMne : ((∏ p ∈ s, p ^ 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hM0.ne'
  convert h1 using 1
  rw [count_noExact s hs, hval, mul_div_cancel_left₀ _ hMne]

/-- **The sieve product can be made small** (master `sieve_prod_small`), from the divergence of
`∑_{p ≡ −1 (q)} 1/p` in the form of `Std_recipPrimesAP_diverges`. -/
theorem exists_noExact_prod_le (q : ℕ)
    (hdiv : ¬ Summable (fun p : ℕ => if p.Prime ∧ p % q = q - 1 then (1 : ℝ) / p else 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ p % q = q - 1) ∧
      ∏ p ∈ s, (1 - ((1 : ℝ) / p - 1 / (p : ℝ) ^ 2)) ≤ ε := by
  have hterm : ∀ p : ℕ, 0 ≤ (1 : ℝ) / p - 1 / (p : ℝ) ^ 2 := by
    intro p
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
      rw [sub_nonneg]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
  have hf0 : 0 ≤ (fun p : ℕ =>
      if p.Prime ∧ p % q = q - 1 then (1 : ℝ) / p - 1 / (p : ℝ) ^ 2 else 0) := by
    intro p
    dsimp only
    split_ifs
    · exact hterm p
    · exact le_refl 0
  obtain ⟨t, ht⟩ : ∃ t : Finset ℕ, -Real.log ε ≤
      ∑ p ∈ t, (if p.Prime ∧ p % q = q - 1 then (1 : ℝ) / p - 1 / (p : ℝ) ^ 2 else 0) := by
    by_contra hcon
    push_neg at hcon
    have hfs := summable_of_sum_le hf0 (fun u => (hcon u).le)
    have hgs : Summable (fun p : ℕ =>
        if p.Prime ∧ p % q = q - 1 then 1 / (p : ℝ) ^ 2 else 0) := by
      refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
        (Real.summable_one_div_nat_pow.mpr one_lt_two)
      · split_ifs
        · positivity
        · exact le_refl 0
      · split_ifs
        · exact le_refl _
        · positivity
    apply hdiv
    refine (hfs.add hgs).congr (fun p => ?_)
    split_ifs <;> ring
  have hsum : ∑ p ∈ t.filter (fun p => p.Prime ∧ p % q = q - 1),
      ((1 : ℝ) / p - 1 / (p : ℝ) ^ 2) =
      ∑ p ∈ t, (if p.Prime ∧ p % q = q - 1 then (1 : ℝ) / p - 1 / (p : ℝ) ^ 2 else 0) := by
    rw [Finset.sum_filter]
  rw [← hsum] at ht
  refine ⟨t.filter (fun p => p.Prime ∧ p % q = q - 1),
    fun p hp => (Finset.mem_filter.1 hp).2, ?_⟩
  calc ∏ p ∈ t.filter (fun p => p.Prime ∧ p % q = q - 1), (1 - ((1 : ℝ) / p - 1 / (p : ℝ) ^ 2))
      ≤ ∏ p ∈ t.filter (fun p => p.Prime ∧ p % q = q - 1),
          Real.exp (-((1 : ℝ) / p - 1 / (p : ℝ) ^ 2)) := by
        refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => Real.one_sub_le_exp_neg _)
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.1.two_le
        have h1p : (1 : ℝ) / p ≤ 1 := by
          rw [div_le_one (by linarith)]
          linarith
        have h2p : (0 : ℝ) ≤ 1 / (p : ℝ) ^ 2 := by positivity
        linarith
    _ = Real.exp (-∑ p ∈ t.filter (fun p => p.Prime ∧ p % q = q - 1),
          ((1 : ℝ) / p - 1 / (p : ℝ) ^ 2)) := by
        rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
    _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr (by linarith)
    _ = ε := Real.exp_log hε

/-- **`q ∤ σ(n)` is rare** whenever the primes `≡ −1 (mod q)` have divergent reciprocal sum
(paper lines 462–478, master `sigma_avoid`). -/
theorem densZero_not_dvd_sigma (q : ℕ) (hq : 1 ≤ q)
    (hdiv : ¬ Summable (fun p : ℕ => if p.Prime ∧ p % q = q - 1 then (1 : ℝ) / p else 0)) :
    DensZero {n : ℕ | ¬ q ∣ sig n} := by
  have key : ∀ ε : ℝ, 0 < ε → upperDens {n : ℕ | ¬ q ∣ sig n} ≤ ε := by
    intro ε hε
    obtain ⟨s, hsP, hsε⟩ := exists_noExact_prod_le q hdiv hε
    have hsub : {n : ℕ | ¬ q ∣ sig n} ⊆ {n | NoExact s n} := by
      intro n hn p hp hpn
      exact hn (dvd_sigma_of_exact (hsP p hp).1 (dvd_succ_of_mod_eq hq (hsP p hp).2) hpn.1 hpn.2)
    calc upperDens {n : ℕ | ¬ q ∣ sig n} ≤ upperDens {n | NoExact s n} := upperDens_mono hsub
      _ = ∏ p ∈ s, (1 - ((1 : ℝ) / p - 1 / (p : ℝ) ^ 2)) :=
        (hasDens_noExact s (fun p hp => (hsP p hp).1)).upperDens_eq
      _ ≤ ε := hsε
  rw [densZero_iff_upperDens_eq_zero]
  by_contra hne
  have hpos : 0 < upperDens {n : ℕ | ¬ q ∣ sig n} :=
    lt_of_le_of_ne (upperDens_nonneg _) (Ne.symm hne)
  have := key (upperDens {n : ℕ | ¬ q ∣ sig n} / 2) (half_pos hpos)
  linarith

/-- **Union bound** (paper line 479): `V ∤ σ(n)` forces `p^{v_p(V)} ∤ σ(n)` for some `p ∣ V`. -/
theorem not_dvd_subset (V : ℕ) (hV : V ≠ 0) :
    {n : ℕ | ¬ V ∣ sig n} ⊆ ⋃ p ∈ V.primeFactors, {n : ℕ | ¬ p ^ V.factorization p ∣ sig n} := by
  intro n hn
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hn ⊢
  by_contra hcon
  push_neg at hcon
  apply hn
  by_cases hσ : sig n = 0
  · rw [hσ]
    exact dvd_zero V
  rw [← Nat.factorization_prime_le_iff_dvd hV hσ]
  intro p hp
  by_cases hpV : p ∈ V.primeFactors
  · exact (hp.pow_dvd_iff_le_factorization hσ).mp (hcon p hpV)
  · have h0 : V.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact hpV (Nat.mem_primeFactors.2 ⟨hp, hd, hV⟩)
    rw [h0]
    exact Nat.zero_le _

/-! ## 4. `v/φ(v) ≤ ζ(2) σ(v)/v` -/

/-- `σ(p^a) ≥ p^a (1 + 1/p)` for `a ≥ 1`. -/
theorem sigma_prime_pow_ge {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    (p : ℝ) ^ a * (1 + 1 / (p : ℝ)) ≤ (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  have hnat : p ^ m + p ^ (m + 1) ≤ ArithmeticFunction.sigma 1 (p ^ (m + 1)) := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, Finset.sum_range_succ,
      Finset.sum_range_succ]
    exact Nat.add_le_add_right (Nat.le_add_left _ _) _
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e : (p : ℝ) ^ (m + 1) * (1 / (p : ℝ)) = (p : ℝ) ^ m := by
    rw [pow_succ, mul_assoc, mul_one_div, div_self hp0, mul_one]
  calc (p : ℝ) ^ (m + 1) * (1 + 1 / (p : ℝ))
      = (p : ℝ) ^ (m + 1) + (p : ℝ) ^ (m + 1) * (1 / (p : ℝ)) := by ring
    _ = (p : ℝ) ^ m + (p : ℝ) ^ (m + 1) := by rw [e, add_comm]
    _ ≤ (ArithmeticFunction.sigma 1 (p ^ (m + 1)) : ℝ) := by exact_mod_cast hnat

/-- `σ(v) ≥ v ∏_{p ∣ v} (1 + 1/p)`. -/
theorem sigma_ge_prod (v : ℕ) (hv : v ≠ 0) :
    (v : ℝ) * ∏ p ∈ v.primeFactors, (1 + 1 / (p : ℝ)) ≤ (sig v : ℝ) := by
  have hσ : (sig v : ℝ) = ∏ p ∈ v.primeFactors,
      (ArithmeticFunction.sigma 1 (p ^ v.factorization p) : ℝ) := by
    show ((ArithmeticFunction.sigma 1 v : ℕ) : ℝ) = _
    rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hv,
      Finsupp.prod, Nat.support_factorization, Nat.cast_prod]
  have hv' : (v : ℝ) = ∏ p ∈ v.primeFactors, ((p : ℝ) ^ v.factorization p) := by
    have h := Nat.prod_factorization_pow_eq_self hv
    rw [Finsupp.prod, Nat.support_factorization] at h
    exact_mod_cast h.symm
  rw [hσ, hv', ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro p _
    positivity
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact sigma_prime_pow_ge hpp (hpp.factorization_pos_of_dvd hv (Nat.dvd_of_mem_primeFactors hp))

/-- Euler's product for the totient, in `ℝ`: `φ(v) = v ∏_{p ∣ v} (1 − 1/p)`. -/
theorem totient_eq_prod (v : ℕ) :
    (v.totient : ℝ) = (v : ℝ) * ∏ p ∈ v.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors v)
  push_cast at h
  exact h

/-- The completely multiplicative function `n ↦ n⁻²`. -/
noncomputable def invSq : ℕ →* ℝ where
  toFun n := ((n : ℝ) ^ 2)⁻¹
  map_one' := by simp
  map_mul' m n := by
    push_cast
    rw [mul_pow, mul_inv]

/-- **Euler-product bound**: for a finite set `s` of primes, `∏_{p ∈ s} (1 − p⁻²)⁻¹ ≤ π²/6`. -/
theorem prod_inv_one_sub_invSq_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ ≤ Real.pi ^ 2 / 6 := by
  have hlt : ∀ {p : ℕ}, p.Prime → ‖invSq p‖ < 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    show ‖((p : ℝ) ^ 2)⁻¹‖ < 1
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by nlinarith)
  obtain ⟨-, hsum⟩ :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric hlt s
  rw [Finset.filter_true_of_mem hs] at hsum
  have hfun : (fun n : ℕ => invSq n) = (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
    funext n
    show ((n : ℝ) ^ 2)⁻¹ = 1 / (n : ℝ) ^ 2
    rw [one_div]
  have hz : HasSum (fun n : ℕ => invSq n) (Real.pi ^ 2 / 6) := by
    rw [hfun]
    exact hasSum_zeta_two
  have hnn : ∀ n : ℕ, 0 ≤ invSq n := fun n => by
    show (0 : ℝ) ≤ ((n : ℝ) ^ 2)⁻¹
    positivity
  have hle := tsum_comp_le_tsum_of_inj hz.summable hnn
    (Subtype.val_injective : Function.Injective (Subtype.val : Nat.factoredNumbers s → ℕ))
  calc ∏ p ∈ s, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ = ∑' m : Nat.factoredNumbers s, invSq m :=
        hsum.tsum_eq.symm
    _ ≤ ∑' n : ℕ, invSq n := hle
    _ = Real.pi ^ 2 / 6 := hz.tsum_eq

end Principia.Erdos1054.Proofs.Normality

namespace Principia.Erdos1054.Proofs

open Finset Filter
open scoped Topology

/-! ## 5. The obligations -/

/-- **Input `Std_sigma_odd_iff`** (paper lines 558, 2588): `σ(n)` is odd exactly when `n` is a
square or twice a square. -/
theorem input_Std_sigma_odd_iff : Principia.Erdos1054.Std_sigma_odd_iff := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  constructor
  · intro hodd
    obtain ⟨s, hs | hs⟩ := Normality.sq_or_twice_sq_of_sigma_odd hn0 hodd
    · exact Or.inl ⟨s, by rw [hs, sq]⟩
    · exact Or.inr ⟨s, hs⟩
  · rintro (⟨r, hr⟩ | ⟨m, hm⟩)
    · apply Normality.sigma_odd_of_even_factorization hn0
      intro p _ _
      rw [hr, ← sq, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      exact even_two_mul _
    · apply Normality.sigma_odd_of_even_factorization hn0
      intro p _ hp2
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [hm] at hn0
        exact hn0 (by ring)
      rw [hm, Nat.factorization_mul two_ne_zero (pow_ne_zero 2 hm0), Finsupp.add_apply,
        Nat.Prime.factorization Nat.prime_two, Finsupp.single_apply, if_neg (Ne.symm hp2),
        zero_add, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      exact even_two_mul _

/-- **`lem:sigma-rate`, second assertion** (paper line 518, proof lines 558–559):
`B_2(y) ≤ 2 √y`, since every `n` with `σ(n)` odd is `r²` or `2r²` with `1 ≤ r ≤ √y`. -/
theorem link_Lem_SigmaRate_B2 : Principia.Erdos1054.Spine.Link_Lem_SigmaRate_B2 := by
  intro hodd
  refine ⟨2, fun y hy => ?_⟩
  have hy0 : 0 ≤ y := by linarith
  have hcnt : Bq 2 y ≤ ((Finset.Icc 1 (Nat.sqrt ⌊y⌋₊)).image (fun r => r ^ 2) ∪
      (Finset.Icc 1 (Nat.sqrt ⌊y⌋₊)).image (fun r => 2 * r ^ 2)).card := by
    unfold Bq
    apply Normality.cnt_le_card_of_subset
    intro n hn1 hnX hnS
    have hnS' : ¬ 2 ∣ sig n := hnS
    have hodd' : Odd (sig n) := Nat.odd_iff.mpr (by omega)
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    rcases (hodd n hn1).mp hodd' with ⟨r, hr⟩ | ⟨m, hm⟩
    · left
      refine ⟨r, Finset.mem_Icc.2 ⟨?_, ?_⟩, by rw [hr, sq]⟩
      · rcases Nat.eq_zero_or_pos r with h0 | h0
        · rw [h0] at hr
          omega
        · exact h0
      · exact Nat.le_sqrt.2 (by rw [← hr]; exact hnX)
    · right
      refine ⟨m, Finset.mem_Icc.2 ⟨?_, ?_⟩, hm.symm⟩
      · rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0] at hm
          omega
        · exact h0
      · have h2 : 2 * m ^ 2 ≤ ⌊y⌋₊ := by rw [← hm]; exact hnX
        exact Nat.le_sqrt.2 (by nlinarith)
  have hcard : ((Finset.Icc 1 (Nat.sqrt ⌊y⌋₊)).image (fun r => r ^ 2) ∪
      (Finset.Icc 1 (Nat.sqrt ⌊y⌋₊)).image (fun r => 2 * r ^ 2)).card ≤ 2 * Nat.sqrt ⌊y⌋₊ := by
    refine (Finset.card_union_le _ _).trans ?_
    have h1 := Finset.card_image_le (s := Finset.Icc 1 (Nat.sqrt ⌊y⌋₊)) (f := fun r => r ^ 2)
    have h2 := Finset.card_image_le (s := Finset.Icc 1 (Nat.sqrt ⌊y⌋₊))
      (f := fun r => 2 * r ^ 2)
    rw [Nat.card_Icc] at h1 h2
    omega
  have hk : ((Nat.sqrt ⌊y⌋₊ : ℕ) : ℝ) ≤ Real.sqrt y :=
    Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt (Nat.floor_le hy0))
  have hB : (Bq 2 y : ℝ) ≤ 2 * ((Nat.sqrt ⌊y⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast hcnt.trans hcard
  linarith

/-- **`lem:fixed-modulus-normality`** (paper lines 452–480): for every `V ≥ 1`, `V ∣ σ(n)` for
almost all `n`, given the divergence of `∑_{p ≡ −1 (q)} 1/p` for prime powers `q`. -/
theorem link_Lem_FixedModulusNormality :
    Principia.Erdos1054.Spine.Link_Lem_FixedModulusNormality := by
  intro hdiv V hV
  have hV0 : V ≠ 0 := by omega
  refine densZero_subset ?_ (Normality.not_dvd_subset V hV0)
  refine densZero_biUnion V.primeFactors (fun p hp => ?_)
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hk : 0 < V.factorization p :=
    hpp.factorization_pos_of_dvd hV0 (Nat.dvd_of_mem_primeFactors hp)
  have hpow : IsPrimePow (p ^ V.factorization p) := ⟨p, V.factorization p, hpp.prime, hk, rfl⟩
  exact Normality.densZero_not_dvd_sigma _
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hpp.ne_zero)) (hdiv _ hpow)

/-- **`lem:sigma-range-zero`** (paper lines 484–498): `σ(ℕ)` has density zero, since for each
`q ≥ 1` its upper density is at most `1/q`. -/
theorem link_Lem_SigmaRangeZero : Principia.Erdos1054.Spine.Link_Lem_SigmaRangeZero := by
  intro hnorm
  have key : ∀ q : ℕ, 1 ≤ q →
      upperDens {N : ℕ | ∃ n : ℕ, 1 ≤ n ∧ sig n = N} ≤ 1 / (q : ℝ) := by
    intro q hq
    have hB : DensZero {n : ℕ | ¬ q ∣ sig n} := hnorm q hq
    have hT : DensZero {N : ℕ | ∃ n : ℕ, 1 ≤ n ∧ sig n = N ∧ ¬ q ∣ N} := by
      refine squeeze_zero (cnt_div_nonneg _) (fun X => div_le_div_of_nonneg_right ?_
        (Nat.cast_nonneg X)) hB
      have hle : cnt {N : ℕ | ∃ n : ℕ, 1 ≤ n ∧ sig n = N ∧ ¬ q ∣ N} (X : ℝ) ≤
          cnt {n : ℕ | ¬ q ∣ sig n} (X : ℝ) := by
        apply Normality.cnt_le_cnt_of_image sig
        rintro N - hNX ⟨n, hn1, hnN, hq'⟩
        refine ⟨n, hn1, ?_, ?_, hnN⟩
        · have := Normality.le_sig (n := n) (by omega)
          omega
        · show ¬ q ∣ sig n
          rw [hnN]
          exact hq'
      exact_mod_cast hle
    have hsub : {N : ℕ | ∃ n : ℕ, 1 ≤ n ∧ sig n = N} ⊆
        {N : ℕ | q ∣ N} ∪ {N : ℕ | ∃ n : ℕ, 1 ≤ n ∧ sig n = N ∧ ¬ q ∣ N} := by
      rintro N ⟨n, hn1, hnN⟩
      by_cases hqN : q ∣ N
      · exact Or.inl hqN
      · exact Or.inr ⟨n, hn1, hnN, hqN⟩
    calc upperDens {N : ℕ | ∃ n : ℕ, 1 ≤ n ∧ sig n = N}
        ≤ upperDens ({N : ℕ | q ∣ N} ∪ {N : ℕ | ∃ n : ℕ, 1 ≤ n ∧ sig n = N ∧ ¬ q ∣ N}) :=
          upperDens_mono hsub
      _ ≤ upperDens {N : ℕ | q ∣ N} +
            upperDens {N : ℕ | ∃ n : ℕ, 1 ≤ n ∧ sig n = N ∧ ¬ q ∣ N} :=
          upperDens_union_le _ _
      _ = 1 / (q : ℝ) := by
          rw [(hasDens_dvd hq).upperDens_eq, densZero_iff_upperDens_eq_zero.1 hT, add_zero]
  show DensZero {N : ℕ | ∃ n : ℕ, 1 ≤ n ∧ sig n = N}
  rw [densZero_iff_upperDens_eq_zero]
  by_contra hne
  have hpos : 0 < upperDens {N : ℕ | ∃ n : ℕ, 1 ≤ n ∧ sig n = N} :=
    lt_of_le_of_ne (upperDens_nonneg _) (Ne.symm hne)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
  have h := key (k + 1) (by omega)
  push_cast at h
  linarith

/-- **Input `Std_totient_sigma`** (paper lines 1620–1627): `v/φ(v) ≤ ζ(2) σ(v)/v` for `v ≥ 1`,
from `(σ(v)/v)(φ(v)/v) ≥ ∏_{p ∣ v} (1 − p⁻²) ≥ 1/ζ(2)`. -/
theorem input_Std_totient_sigma : Principia.Erdos1054.Std_totient_sigma := by
  intro v hv
  have hv0 : v ≠ 0 := by omega
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hφ : (0 : ℝ) < v.totient := by exact_mod_cast Nat.totient_pos.2 hv
  have hAB : (∏ p ∈ v.primeFactors, (1 + 1 / (p : ℝ))) * ∏ p ∈ v.primeFactors, (1 - (p : ℝ)⁻¹)
      = ∏ p ∈ v.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    ring
  have hPpos : 0 < ∏ p ∈ v.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹) := Finset.prod_pos fun p hp => by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : ((p : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
    linarith
  have hPinv : (∏ p ∈ v.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹))⁻¹ ≤ Real.pi ^ 2 / 6 := by
    have h := Normality.prod_inv_one_sub_invSq_le v.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
    rwa [Finset.prod_inv_distrib] at h
  have hσ := Normality.sigma_ge_prod v hv0
  have hφeq := Normality.totient_eq_prod v
  have h1 : (v : ℝ) * v * ∏ p ∈ v.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹) ≤
      (sig v : ℝ) * v.totient := by
    calc (v : ℝ) * v * ∏ p ∈ v.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)
        = ((v : ℝ) * ∏ p ∈ v.primeFactors, (1 + 1 / (p : ℝ))) * (v.totient : ℝ) := by
          rw [hφeq, ← hAB]
          ring
      _ ≤ (sig v : ℝ) * v.totient := mul_le_mul_of_nonneg_right hσ hφ.le
  have h2 : (v : ℝ) * v ≤ (sig v : ℝ) * v.totient *
      (∏ p ∈ v.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹))⁻¹ := by
    rw [le_mul_inv_iff₀ hPpos]
    exact h1
  have hσφ : 0 ≤ (sig v : ℝ) * v.totient := by positivity
  have h3 : (v : ℝ) * v ≤ Real.pi ^ 2 / 6 * ((sig v : ℝ) * v.totient) := by
    refine h2.trans ?_
    rw [mul_comm (Real.pi ^ 2 / 6)]
    exact mul_le_mul_of_nonneg_left hPinv hσφ
  have hvne : (v : ℝ) ≠ 0 := hvR.ne'
  rw [div_le_iff₀ hφ]
  calc (v : ℝ) = (v : ℝ) * v / v := (mul_div_cancel_right₀ (v : ℝ) hvne).symm
    _ ≤ Real.pi ^ 2 / 6 * ((sig v : ℝ) * v.totient) / v := div_le_div_of_nonneg_right h3 hvR.le
    _ = Real.pi ^ 2 / 6 * ((sig v : ℝ) / v) * v.totient := by ring

end Principia.Erdos1054.Proofs
