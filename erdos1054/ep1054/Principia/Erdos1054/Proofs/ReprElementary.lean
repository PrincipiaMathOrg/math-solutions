/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Interval.Finset.SuccPred

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) §3 — the elementary representability package

Proofs of the elementary leaves and links of `prop:fraiture-finite` (lines 686–823),
`prop:fraiture-tail` (lines 900–953) and the "in particular" clause of
`thm:fraiture-representability` (line 683). Every theorem's type is the spine `Prop` stated by
name; the verifier checks `Comp_Verifier_*`, Dusart (`Cite_Dusart_Thm69`) and the balanced
Goldbach lemma enter only as the link hypotheses the spine names.

## Method

* **Representations via `F`, never via `Finset.sort`.** `prefixSumDivisors` does not reduce for
  `m ≥ 2`, so every membership `N ∈ 𝓡` is produced by `mem_R_iff_exists_F`: for `D ∣ m`, the sum
  of the divisors of `m` up to `D` is represented (`sum_divisors_le_mem_R`). The prime-window,
  three-prime and four-prime prefixes are all instances of one lemma
  (`one_add_sum_mem_R`: primes `J` with top element `D` and all products of two distinct
  elements `> D` give `1 + ∑ J ∈ 𝓡`), and `σ(B) + q ∑_{i ≤ j} d_i(B)` is the sum of the divisors
  of `Bq` up to `q d_j(B)`.
* **No concrete interval is ever unfolded.** The windows `(10⁴, 98 999 987]` and
  `(2·10⁷, 399·10¹²]` appear only as arguments to lemmas proved for variable endpoints or variable
  finsets (a defeq check that meets `Finset.card` of a concrete interval makes the elaborator and
  the kernel evaluate it). The interval-extension inductions run over a variable `n` and are
  instantiated at the literal endpoint only at the end.
* **Bertrand in the large window.** The width `51 000 001 + ∑_{4·10⁷ < p ≤ n} p` stays `≥ n + 1`
  (`large_width`): below `8·10⁷` it is the explicit prime `40 000 003` (`norm_num`), above it the
  Bertrand prime in `(n/2, n]` and strong induction at `n/2`.
* **Real analysis of the tail.** `(log x)² < 16 √x` (from `log s ≤ s − 1` at `s = x^{1/4}`) gives
  `c (log x)² < x` for `x ≥ 10²⁷`, `c ≤ 10¹²`; `log n ≤ log T + n/T − 1` with `log T < 64`
  (from `e > 2.7182818283`) gives `H ≥ 10²⁷` and `H > n/2` in the odd case.
-/

namespace Principia.Erdos1054.Proofs.ReprElementary

open Finset Principia.Erdos1054

/-- The sum of the divisors of `m` up to a divisor `D` is represented. -/
lemma sum_divisors_le_mem_R (m D : ℕ) (hm : 1 ≤ m) (hD : D ∣ m) :
    (∑ x ∈ m.divisors.filter (· ≤ D), x) ∈ R := by
  rw [mem_R_iff_exists_F]
  have hDpos : 0 < D := Nat.pos_of_dvd_of_pos hD hm
  refine ⟨m / D, D, Nat.div_pos (Nat.le_of_dvd hm hD) hDpos, hDpos, ?_⟩
  unfold F
  rw [Nat.div_mul_cancel hD]

/-- For a finite set `J` of primes bounded by `D`, whose products of two distinct elements exceed
`D`, the divisors of `∏ J` up to `D` are `1` and the elements of `J`. -/
lemma divisors_prod_filter (J : Finset ℕ) (hJ : ∀ p ∈ J, p.Prime) (D : ℕ)
    (hmax : ∀ p ∈ J, p ≤ D) (hpair : ∀ p ∈ J, ∀ q ∈ J, p ≠ q → D < p * q) (hD1 : 1 ≤ D) :
    (∏ p ∈ J, p).divisors.filter (· ≤ D) = insert 1 J := by
  have hprodpos : 0 < ∏ p ∈ J, p := Finset.prod_pos (fun p hp => (hJ p hp).pos)
  have hmemJ : ∀ r : ℕ, r.Prime → r ∣ ∏ p ∈ J, p → r ∈ J := by
    intro r hr hdvd
    obtain ⟨j, hj, hrj⟩ := (Prime.dvd_finsetProd_iff hr.prime (fun p : ℕ => p)).1 hdvd
    have hrj' : r = j := (Nat.prime_dvd_prime_iff_eq hr (hJ j hj)).1 hrj
    rw [hrj']
    exact hj
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert]
  constructor
  · rintro ⟨⟨hdvd, _⟩, hdD⟩
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    right
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hprodpos
    have hpPrime : d.minFac.Prime := Nat.minFac_prime hd1
    have hpd : d.minFac ∣ d := Nat.minFac_dvd d
    have hpJ : d.minFac ∈ J := hmemJ _ hpPrime (hpd.trans hdvd)
    by_cases hdp : d = d.minFac
    · rw [hdp]; exact hpJ
    exfalso
    obtain ⟨e, he⟩ := hpd
    have he1 : e ≠ 1 := by
      intro h
      apply hdp
      rw [h, mul_one] at he
      exact he
    have hqPrime : e.minFac.Prime := Nat.minFac_prime he1
    have hqe : e.minFac ∣ e := Nat.minFac_dvd e
    have hpqd : d.minFac * e.minFac ∣ d := by
      have h' : d.minFac * e.minFac ∣ d.minFac * e := Nat.mul_dvd_mul_left _ hqe
      rwa [← he] at h'
    have hed : e ∣ d := Dvd.intro_left _ he.symm
    have hqJ : e.minFac ∈ J := hmemJ _ hqPrime ((hqe.trans hed).trans hdvd)
    by_cases hpq : d.minFac = e.minFac
    · rw [← hpq] at hpqd
      have hpp : d.minFac * d.minFac ∣ ∏ x ∈ J, x := hpqd.trans hdvd
      rw [← Finset.mul_prod_erase J (fun x : ℕ => x) hpJ] at hpp
      have hdiv : d.minFac ∣ ∏ x ∈ J.erase d.minFac, x :=
        Nat.dvd_of_mul_dvd_mul_left hpPrime.pos hpp
      obtain ⟨j, hj, hpj⟩ :=
        (Prime.dvd_finsetProd_iff hpPrime.prime (fun p : ℕ => p)).1 hdiv
      have hjJ : j ∈ J := Finset.mem_of_mem_erase hj
      have hjne : j ≠ d.minFac := Finset.ne_of_mem_erase hj
      exact hjne ((Nat.prime_dvd_prime_iff_eq hpPrime (hJ j hjJ)).1 hpj).symm
    · have hlt := hpair _ hpJ _ hqJ hpq
      have hle : d.minFac * e.minFac ≤ d := Nat.le_of_dvd hdpos hpqd
      omega
  · rintro (rfl | hdJ)
    · exact ⟨⟨one_dvd _, hprodpos.ne'⟩, hD1⟩
    · exact ⟨⟨Finset.dvd_prod_of_mem (fun p : ℕ => p) hdJ, hprodpos.ne'⟩, hmax d hdJ⟩

/-- `1 + ∑ J ∈ 𝓡` for a set of primes `J` with top element `D` and pairwise products `> D`. -/
lemma one_add_sum_mem_R (J : Finset ℕ) (hJ : ∀ p ∈ J, p.Prime) (D : ℕ) (hDJ : D ∈ J)
    (hmax : ∀ p ∈ J, p ≤ D) (hpair : ∀ p ∈ J, ∀ q ∈ J, p ≠ q → D < p * q) :
    1 + ∑ p ∈ J, p ∈ R := by
  have hD1 : 1 ≤ D := (hJ D hDJ).one_lt.le
  have h1J : (1 : ℕ) ∉ J := fun h => Nat.not_prime_one (hJ 1 h)
  have hsum : 1 + ∑ p ∈ J, p = ∑ x ∈ (∏ p ∈ J, p).divisors.filter (· ≤ D), x := by
    rw [divisors_prod_filter J hJ D hmax hpair hD1, Finset.sum_insert h1J]
  rw [hsum]
  exact sum_divisors_le_mem_R _ D (Finset.prod_pos (fun p hp => (hJ p hp).pos))
    (Finset.dvd_prod_of_mem (fun p : ℕ => p) hDJ)

/-- `F e d` as a sum over `[1, d]`. -/
lemma F_eq_sum_Icc (e d : ℕ) (he : 1 ≤ e) (hd : 1 ≤ d) :
    F e d = ∑ x ∈ (Finset.Icc 1 d).filter (· ∣ e * d), x := by
  unfold F
  congr 1
  ext x
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  have hed : e * d ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.mul_pos he hd)
  constructor
  · rintro ⟨⟨hx, _⟩, hxd⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hx (Nat.pos_of_ne_zero hed), hxd⟩, hx⟩
  · rintro ⟨⟨_, hxd⟩, hx⟩
    exact ⟨⟨hx, hed⟩, hxd⟩

/-- `1 + d ≤ F e d` when `d ≥ 2`. -/
lemma one_add_le_F (e d : ℕ) (he : 1 ≤ e) (hd : 2 ≤ d) : 1 + d ≤ F e d := by
  rw [F_eq_sum_Icc e d he (by omega)]
  have hsub : ({1, d} : Finset ℕ) ⊆ (Finset.Icc 1 d).filter (· ∣ e * d) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_rfl, by omega⟩, one_dvd _⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, le_rfl⟩, dvd_mul_left _ _⟩
  have h := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) hsub
  have h1d : (1 : ℕ) ∉ ({d} : Finset ℕ) := by simp; omega
  rw [Finset.sum_insert h1d, Finset.sum_singleton] at h
  exact h

/-- `F e d ∉ {0, 2, 5}` for `e, d ≥ 1`. -/
lemma F_ne_small (e d : ℕ) (he : 1 ≤ e) (hd : 1 ≤ d) :
    F e d ≠ 0 ∧ F e d ≠ 2 ∧ F e d ≠ 5 := by
  by_cases hd5 : 5 ≤ d
  · have := one_add_le_F e d he (by omega)
    omega
  · have hd' : d ≤ 4 := by omega
    rw [F_eq_sum_Icc e d he hd, Finset.sum_filter]
    interval_cases d
    · rw [show Finset.Icc 1 1 = {1} by rfl, Finset.sum_singleton, if_pos (one_dvd _)]
      decide
    · rw [show Finset.Icc 1 2 = {1, 2} by rfl, Finset.sum_insert (by decide),
        Finset.sum_singleton, if_pos (one_dvd _), if_pos (dvd_mul_left 2 e)]
      decide
    · rw [show Finset.Icc 1 3 = {1, 2, 3} by rfl, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton, if_pos (one_dvd _),
        if_pos (dvd_mul_left 3 e)]
      split_ifs <;> decide
    · have h2 : 2 ∣ e * 4 := Dvd.dvd.mul_left (by norm_num) e
      rw [show Finset.Icc 1 4 = {1, 2, 3, 4} by rfl, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
        if_pos (one_dvd _), if_pos h2, if_pos (dvd_mul_left 4 e)]
      split_ifs <;> decide

/-- `(log x)^2 < 16 √x` for `x ≥ 1` (from `log s ≤ s - 1` at `s = x^{1/4}`). -/
lemma log_sq_lt_sqrt (x : ℝ) (hx : 1 ≤ x) : Real.log x ^ 2 < 16 * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hs2 : Real.sqrt (Real.sqrt x) ^ 2 = Real.sqrt x := Real.sq_sqrt hsx
  have hlog : Real.log x = 4 * Real.log (Real.sqrt (Real.sqrt x)) := by
    rw [Real.log_sqrt hsx, Real.log_sqrt hx0]
    ring
  have hs1 : 1 ≤ Real.sqrt (Real.sqrt x) := Real.one_le_sqrt.2 (Real.one_le_sqrt.2 hx)
  have hlogs0 : 0 ≤ Real.log (Real.sqrt (Real.sqrt x)) := Real.log_nonneg hs1
  have hlogs : Real.log (Real.sqrt (Real.sqrt x)) < Real.sqrt (Real.sqrt x) := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.sqrt (Real.sqrt x))
    linarith
  have hsq : Real.log (Real.sqrt (Real.sqrt x)) ^ 2 < Real.sqrt (Real.sqrt x) ^ 2 :=
    pow_lt_pow_left₀ hlogs hlogs0 (by norm_num)
  calc Real.log x ^ 2 = 16 * Real.log (Real.sqrt (Real.sqrt x)) ^ 2 := by rw [hlog]; ring
    _ < 16 * Real.sqrt (Real.sqrt x) ^ 2 := by linarith
    _ = 16 * Real.sqrt x := by rw [hs2]

/-- For `x ≥ 10^27` and `c ≤ 10^12`, `c (log x)^2 < x`. -/
lemma mul_log_sq_lt (x : ℝ) (hx : (10 : ℝ) ^ 27 ≤ x) (c : ℝ)
    (hc : c ≤ 10 ^ 12) : c * Real.log x ^ 2 < x := by
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have hx0 : 0 ≤ x := by linarith
  have h1 := log_sq_lt_sqrt x hx1
  have hsq : (3 * 10 ^ 13 : ℝ) ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num) hx0).2 (le_trans (by norm_num) hx)
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  have hl0 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
  calc c * Real.log x ^ 2 ≤ 10 ^ 12 * Real.log x ^ 2 := mul_le_mul_of_nonneg_right hc hl0
    _ < 10 ^ 12 * (16 * Real.sqrt x) := mul_lt_mul_of_pos_left h1 (by norm_num)
    _ ≤ 3 * 10 ^ 13 * Real.sqrt x := by linarith [Real.sqrt_nonneg x]
    _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg x)
    _ = x := hxx

/-- Three distinct primes with pairwise products above their sum `H` give `1 + H ∈ 𝓡`. -/
lemma tail_three (hT3 : Step_FraitureTailThreePrimes) (p q r H : ℕ) (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hsum : p + q + r = H) (h1 : H < p * q) (h2 : H < p * r) (h3 : H < q * r) :
    1 + H ∈ R := by
  have h2p := hp.two_le
  have h2q := hq.two_le
  have h2r := hr.two_le
  have h1' : H < q * p := by rw [mul_comm]; exact h1
  have h2' : H < r * p := by rw [mul_comm]; exact h2
  have h3' : H < r * q := by rw [mul_comm]; exact h3
  have key : ∀ a b c : ℕ, a.Prime → b.Prime → c.Prime → a < b → b < c → a + b + c = H →
      H < a * b → 1 + H ∈ R := by
    intro a b c ha hb hc hab hbc hs hab'
    have ha2 := ha.two_le
    have hcH : c < H := by omega
    have hmem := hT3 a b c ha hb hc hab hbc (lt_trans hcH hab')
    have e : 1 + H = 1 + a + b + c := by omega
    rw [e]
    exact hmem
  rcases lt_or_gt_of_ne hpq with h | h <;> rcases lt_or_gt_of_ne hpr with h' | h' <;>
    rcases lt_or_gt_of_ne hqr with h'' | h'' <;>
    first
    | exact key p q r hp hq hr (by omega) (by omega) (by omega) h1
    | exact key p r q hp hr hq (by omega) (by omega) (by omega) h2
    | exact key q p r hq hp hr (by omega) (by omega) (by omega) h1'
    | exact key q r p hq hr hp (by omega) (by omega) (by omega) h3
    | exact key r p q hr hp hq (by omega) (by omega) (by omega) h2'
    | exact key r q p hr hq hp (by omega) (by omega) (by omega) h3'

/-- A prime `l` below three distinct primes with sum `H`, with `l · x > H` for each of them,
gives `1 + l + H ∈ 𝓡`. -/
lemma tail_four (hT4 : Step_FraitureTailFourPrimes) (l p q r H : ℕ) (hl : l.Prime)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hlp : l < p) (hlq : l < q) (hlr : l < r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hsum : p + q + r = H) (h1 : H < l * p) (h2 : H < l * q) (h3 : H < l * r) :
    1 + l + H ∈ R := by
  have h2p := hp.two_le
  have h2q := hq.two_le
  have h2r := hr.two_le
  have key : ∀ a b c : ℕ, a.Prime → b.Prime → c.Prime → l < a → a < b → b < c →
      a + b + c = H → H < l * a → 1 + l + H ∈ R := by
    intro a b c ha hb hc hla hab hbc hs hla'
    have ha2 := ha.two_le
    have hcH : c < H := by omega
    have hmem := hT4 l a b c hl ha hb hc hla hab hbc (lt_trans hcH hla')
    have e : 1 + l + H = 1 + l + a + b + c := by omega
    rw [e]
    exact hmem
  rcases lt_or_gt_of_ne hpq with h | h <;> rcases lt_or_gt_of_ne hpr with h' | h' <;>
    rcases lt_or_gt_of_ne hqr with h'' | h'' <;>
    first
    | exact key p q r hp hq hr hlp (by omega) (by omega) (by omega) h1
    | exact key p r q hp hr hq hlp (by omega) (by omega) (by omega) h1
    | exact key q p r hq hp hr hlq (by omega) (by omega) (by omega) h2
    | exact key q r p hq hr hp hlq (by omega) (by omega) (by omega) h2
    | exact key r p q hr hp hq hlr (by omega) (by omega) (by omega) h3
    | exact key r q p hr hq hp hlr (by omega) (by omega) (by omega) h3

/-- `π(b) = π(a) + #{a < p ≤ b prime}` for `a ≤ b`. -/
lemma card_filter_prime_Ioc (a b : ℕ) (hab : a ≤ b) :
    ((Finset.Ioc a b).filter Nat.Prime).card + Nat.primeCounting a = Nat.primeCounting b := by
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hU : Finset.range (b + 1) = Finset.Ioc a b ∪ Finset.range (a + 1) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hD : Disjoint (Finset.Ioc a b) (Finset.range (a + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_range, Finset.mem_Ioc] at hx hx'
    omega
  rw [hU, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hD)]

/-- The first prime after `40 000 000`, used to start the width induction. -/
lemma prime_40000003 : Nat.Prime 40000003 := by norm_num

/-- The certified width stays ahead of the next prime: for `n ≥ 4·10^7`,
`n + 1 ≤ 51 000 001 + ∑_{4·10^7 < p ≤ n} p`. -/
lemma large_width (n : ℕ) (hn : 40000000 ≤ n) :
    n + 1 ≤ 51000001 + ∑ r ∈ (Finset.Ioc 40000000 n).filter Nat.Prime, r := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : n ≤ 51000000
    · omega
    by_cases h2 : n < 80000000
    · have hmem : 40000003 ∈ (Finset.Ioc 40000000 n).filter Nat.Prime := by
        rw [Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨by norm_num, by omega⟩, prime_40000003⟩
      have hle : 40000003 ≤ ∑ r ∈ (Finset.Ioc 40000000 n).filter Nat.Prime, r :=
        Finset.single_le_sum (f := fun r : ℕ => r) (fun i _ => Nat.zero_le i) hmem
      omega
    · obtain ⟨m, hm⟩ : ∃ m, m = n / 2 := ⟨_, rfl⟩
      have hm1 : 40000000 ≤ m := by omega
      have hm2 : m < n := by omega
      have ihm := ih m hm2 hm1
      obtain ⟨q, hq, hmq, hq2m⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
      have hsub : insert q ((Finset.Ioc 40000000 m).filter Nat.Prime) ⊆
          (Finset.Ioc 40000000 n).filter Nat.Prime := by
        intro x hx
        rw [Finset.mem_insert] at hx
        rw [Finset.mem_filter, Finset.mem_Ioc]
        rcases hx with rfl | hx
        · exact ⟨⟨by omega, by omega⟩, hq⟩
        · rw [Finset.mem_filter, Finset.mem_Ioc] at hx
          exact ⟨⟨hx.1.1, by omega⟩, hx.2⟩
      have hnotin : q ∉ (Finset.Ioc 40000000 m).filter Nat.Prime := by
        intro hx
        rw [Finset.mem_filter, Finset.mem_Ioc] at hx
        omega
      have hle : ∑ r ∈ insert q ((Finset.Ioc 40000000 m).filter Nat.Prime), r ≤
          ∑ r ∈ (Finset.Ioc 40000000 n).filter Nat.Prime, r :=
        Finset.sum_le_sum_of_subset hsub
      rw [Finset.sum_insert hnotin] at hle
      omega

/-- `#s · a ≤ ∑_{x ∈ t} x` when `s ⊆ t` and every element of `s` is `≥ a` (stated for variable
finsets, so no concrete interval is ever unfolded). -/
lemma card_mul_le_sum_of_subset (s t : Finset ℕ) (a : ℕ) (hst : s ⊆ t) (h : ∀ x ∈ s, a ≤ x) :
    s.card * a ≤ ∑ x ∈ t, x := by
  have h1 : s.card • a ≤ ∑ x ∈ s, x := Finset.card_nsmul_le_sum s (fun x => x) a h
  have h2 : ∑ x ∈ s, x ≤ ∑ x ∈ t, x := Finset.sum_le_sum_of_subset hst
  rw [smul_eq_mul] at h1
  exact h1.trans h2

/-- `log a > 32` for `a = 199 500 000 000 000` (from `e < 2.7182818286`). -/
lemma lps_log_a : 32 < Real.log 199500000000000 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have he : Real.exp 32 = Real.exp 1 ^ 32 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [he]
  calc Real.exp 1 ^ 32 < (2.7182818286 : ℝ) ^ 32 :=
        pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
    _ < 199500000000000 := by norm_num

/-- `log Y < 34` for `Y = 399 000 000 000 000` (from `e > 2.7182818283`). -/
lemma lps_log_Y : Real.log 399000000000000 < 34 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have he : Real.exp 34 = Real.exp 1 ^ 34 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [he]
  calc (399000000000000 : ℝ) < (2.7182818283 : ℝ) ^ 34 := by norm_num
    _ < Real.exp 1 ^ 34 := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)

/-- Dusart (`Cite_Dusart_Thm69`) at a natural number `n ≥ a`. -/
lemma dusart_at_nat (hD : Cite_Dusart_Thm69) (n : ℕ) (hn : 199500000000000 ≤ n) :
    (n : ℝ) / Real.log n < (Nat.primeCounting n : ℝ) ∧
      (Nat.primeCounting n : ℝ) ≤ (n : ℝ) / Real.log n * (1 + 1.2762 / Real.log n) := by
  have h := hD (n : ℝ) (by exact_mod_cast hn)
  rw [Nat.floor_natCast] at h
  exact h

/-- The paper's rational comparison (lines 810–812). -/
lemma lps_num : (1000000000000000000100000000 : ℝ) <
    (399000000000000 / 34 - 199500000000000 / 32 * (1 + 1.2762 / 32) : ℝ) * 199500000000000 := by
  norm_num

/-- The real-arithmetic core of lines 806–812, over abstract reals. -/
lemma lps_real_core (a Y piA piY c : ℝ) (ha : a = 199500000000000) (hY : Y = 399000000000000)
    (hDa : piA ≤ a / Real.log a * (1 + 1.2762 / Real.log a)) (hDY : Y / Real.log Y < piY)
    (hc : c + piA = piY) : (1000000000000000000100000000 : ℝ) < c * 199500000000000 := by
  subst ha hY
  have hla := lps_log_a
  have hlY := lps_log_Y
  have hlY0 : 0 < Real.log 399000000000000 := Real.log_pos (by norm_num)
  have hpia : piA ≤ 199500000000000 / 32 * (1 + 1.2762 / 32) := by
    refine hDa.trans ?_
    gcongr
  have hpiY : (399000000000000 : ℝ) / 34 < piY := by
    refine lt_trans ?_ hDY
    gcongr
  have hlow : (399000000000000 / 34 - 199500000000000 / 32 * (1 + 1.2762 / 32) : ℝ) < c := by
    linarith
  have hmul := mul_lt_mul_of_pos_right hlow (by norm_num : (0 : ℝ) < 199500000000000)
  exact lt_trans lps_num hmul

end Principia.Erdos1054.Proofs.ReprElementary

namespace Principia.Erdos1054.Proofs

open Finset Principia.Erdos1054 Principia.Erdos1054.Proofs.ReprElementary

theorem leaf_Lem_FraiturePrimeWindow : Principia.Erdos1054.Lem_FraiturePrimeWindow := by
  intro M Y P hM hY hP J hJP hJne
  have hJprime : ∀ p ∈ J, p.Prime := fun p hp => (hP p (hJP hp)).1
  refine one_add_sum_mem_R J hJprime (J.max' hJne) (J.max'_mem hJne)
    (fun p hp => J.le_max' p hp) ?_
  intro p hp q hq _
  have hpM : M < (p : ℝ) := (hP p (hJP hp)).2.1
  have hqM : M < (q : ℝ) := (hP q (hJP hq)).2.1
  have hDY : ((J.max' hJne : ℕ) : ℝ) ≤ Y := (hP _ (hJP (J.max'_mem hJne))).2.2
  have hlt : ((J.max' hJne : ℕ) : ℝ) < (p : ℝ) * q := by
    calc ((J.max' hJne : ℕ) : ℝ) ≤ Y := hDY
      _ < M ^ 2 := hY
      _ = M * M := sq M
      _ < (p : ℝ) * q := mul_lt_mul'' hpM hqM (by linarith) (by linarith)
  exact_mod_cast hlt

theorem leaf_Lem_FraitureExtension : Principia.Erdos1054.Lem_FraitureExtension := by
  intro C U P p hCU _ hcover _ hpP hp N hCN hNU
  by_cases hN : N ≤ U
  · obtain ⟨S, hS, hsum⟩ := hcover N hCN hN
    exact ⟨S, hS.trans (Finset.subset_insert p P), hsum⟩
  · obtain ⟨S, hS, hsum⟩ := hcover (N - p) (by omega) (by omega)
    have hpS : p ∉ S := fun h => hpP (hS h)
    refine ⟨insert p S, Finset.insert_subset_insert p hS, ?_⟩
    rw [Finset.sum_insert hpS, hsum]
    omega

theorem leaf_Step_FraitureSeven : Principia.Erdos1054.Step_FraitureSeven := by
  show IsRep 7 4
  rw [isRep_iff_exists_divisor]
  exact ⟨4, by decide, by decide⟩

theorem leaf_Step_FraitureSmallCases : Principia.Erdos1054.Step_FraitureSmallCases := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [isRep_iff_exists_divisor]; exact ⟨1, by decide, by decide⟩
  · rw [isRep_iff_exists_divisor]; exact ⟨2, by decide, by decide⟩
  · rw [isRep_iff_exists_divisor]; exact ⟨3, by decide, by decide⟩
  · intro h
    obtain ⟨e, d, he, hd, hN⟩ := (mem_R_iff_exists_F 2).1 h
    exact (F_ne_small e d he hd).2.1 hN.symm
  · intro h
    obtain ⟨e, d, he, hd, hN⟩ := (mem_R_iff_exists_F 5).1 h
    exact (F_ne_small e d he hd).2.2 hN.symm
  · intro h
    obtain ⟨e, d, he, hd, hN⟩ := (mem_R_iff_exists_F 0).1 h
    exact (F_ne_small e d he hd).1 hN.symm

theorem leaf_Step_FraitureSmallBq : Principia.Erdos1054.Step_FraitureSmallBq := by
  intro B q j hB1 _ hq hBq hj1 hj
  obtain ⟨d0, hd0, hpref⟩ := prefixSumDivisors_eq_Fdiv B j hj1 hj
  rw [hpref]
  have hd0dvd : d0 ∣ B := Nat.dvd_of_mem_divisors hd0
  have hd0pos : 0 < d0 := Nat.pos_of_mem_divisors hd0
  have hB0 : B ≠ 0 := by omega
  have hkey : (B * q).divisors.filter (· ≤ q * d0) =
      B.divisors ∪ (B.divisors.filter (· ≤ d0)).image (fun t => q * t) := by
    ext x
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨⟨hx, _⟩, hxle⟩
      by_cases hqx : q ∣ x
      · obtain ⟨t, rfl⟩ := hqx
        right
        refine ⟨t, ⟨⟨?_, hB0⟩, ?_⟩, rfl⟩
        · rw [mul_comm B q] at hx
          exact Nat.dvd_of_mul_dvd_mul_left hq.pos hx
        · exact Nat.le_of_mul_le_mul_left hxle hq.pos
      · left
        have hcop : Nat.Coprime x q :=
          Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq).2 hqx)
        exact ⟨hcop.dvd_of_dvd_mul_right hx, hB0⟩
    · rintro (⟨hx, _⟩ | ⟨t, ⟨⟨ht, _⟩, htle⟩, rfl⟩)
      · refine ⟨⟨Dvd.dvd.mul_right hx q, Nat.mul_ne_zero hB0 hq.ne_zero⟩, ?_⟩
        have hxB : x ≤ B := Nat.le_of_dvd (by omega) hx
        have hqd : q ≤ q * d0 := Nat.le_mul_of_pos_right q hd0pos
        omega
      · refine ⟨⟨?_, Nat.mul_ne_zero hB0 hq.ne_zero⟩, Nat.mul_le_mul_left q htle⟩
        rw [mul_comm B q]
        exact Nat.mul_dvd_mul_left q ht
  have hdisj : Disjoint B.divisors ((B.divisors.filter (· ≤ d0)).image (fun t => q * t)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx'
    have htpos : 0 < t := Nat.pos_of_mem_divisors (Finset.mem_filter.1 ht).1
    have hxB : q * t ≤ B := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hx)
    have hqt : q ≤ q * t := Nat.le_mul_of_pos_right q htpos
    omega
  have hinj : Set.InjOn (fun t => q * t) ↑(B.divisors.filter (· ≤ d0)) :=
    fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hq.pos h
  have hsig : sig B = ∑ d ∈ B.divisors, d := ArithmeticFunction.sigma_one_apply B
  have hsum : sig B + q * Fdiv B d0 = ∑ x ∈ (B * q).divisors.filter (· ≤ q * d0), x := by
    rw [hkey, Finset.sum_union hdisj, Finset.sum_image hinj, hsig, Fdiv, Finset.mul_sum]
  rw [hsum]
  exact sum_divisors_le_mem_R (B * q) (q * d0) (Nat.mul_pos (by omega) hq.pos)
    (by rw [mul_comm B q]; exact Nat.mul_dvd_mul_left q hd0dvd)

theorem leaf_Step_FraitureTailThreePrimes : Principia.Erdos1054.Step_FraitureTailThreePrimes := by
  intro p q r hp hq hr hpq hqr hrpq
  have h2p := hp.two_le
  have h2q := hq.two_le
  have h2r := hr.two_le
  have hsum : ∑ x ∈ ({p, q, r} : Finset ℕ), x = p + q + r := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
      Finset.sum_singleton]
    ring
  have e : 1 + p + q + r = 1 + ∑ x ∈ ({p, q, r} : Finset ℕ), x := by
    rw [hsum]
    ring
  rw [e]
  refine one_add_sum_mem_R {p, q, r} ?_ r (by simp) ?_ ?_
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact absurd rfl hxy | nlinarith

theorem leaf_Step_FraitureTailFourPrimes : Principia.Erdos1054.Step_FraitureTailFourPrimes := by
  intro l p q r hl hp hq hr hlp hpq hqr hrlp
  have h2l := hl.two_le
  have h2p := hp.two_le
  have h2q := hq.two_le
  have h2r := hr.two_le
  have hsum : ∑ x ∈ ({l, p, q, r} : Finset ℕ), x = l + p + q + r := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
      Finset.sum_insert (by simp; omega), Finset.sum_singleton]
    ring
  have e : 1 + l + p + q + r = 1 + ∑ x ∈ ({l, p, q, r} : Finset ℕ), x := by
    rw [hsum]
    ring
  rw [e]
  refine one_add_sum_mem_R {l, p, q, r} ?_ r (by simp) ?_ ?_
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hxy | nlinarith

theorem link_Eq_FraitureSmall : Principia.Erdos1054.Spine.Link_Eq_FraitureSmall := by
  intro hBq h7 hComp N hN6 hN
  by_cases h : N = 7
  · subst h
    exact ⟨4, by norm_num, h7⟩
  · obtain ⟨B, q, j, hB1, hB, hq, hBq', hj1, hj, rfl⟩ := hComp N hN6 hN h
    exact hBq B q j hB1 hB hq hBq' hj1 hj

theorem link_Step_FraitureFirstWindowCover :
    Principia.Erdos1054.Spine.Link_Step_FraitureFirstWindowCover := by
  intro hExt hComp
  obtain ⟨_, hbase, hstep, hfinal⟩ := hComp
  have key : ∀ n, 10883 ≤ n → n ≤ 98999987 → ∀ N, 469615 ≤ N →
      N ≤ 480503 + ∑ r ∈ (Finset.Ioc 10883 n).filter Nat.Prime, r →
      N ∈ subsetSums ((Finset.Ioc 10000 n).filter Nat.Prime) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro _ N hN1 hN2
      rw [Finset.Ioc_self, Finset.filter_empty, Finset.sum_empty] at hN2
      exact hbase N hN1 (by omega)
    | succ n hn ih =>
      intro hn1 N hN1 hN2
      have ih' := ih (by omega)
      rw [← Finset.insert_Ioc_right_eq_Ioc_add_one (by omega : 10883 ≤ n),
        Finset.filter_insert] at hN2
      rw [← Finset.insert_Ioc_right_eq_Ioc_add_one (by omega : 10000 ≤ n), Finset.filter_insert]
      by_cases hp : (n + 1).Prime
      · rw [if_pos hp] at hN2 ⊢
        have hnotin : n + 1 ∉ (Finset.Ioc 10883 n).filter Nat.Prime := by simp
        rw [Finset.sum_insert hnotin] at hN2
        have hwidth := hstep (n + 1) hp (by omega) hn1
        rw [Finset.Ioo_add_one_right_eq_Ioc] at hwidth
        exact hExt 469615 (480503 + ∑ r ∈ (Finset.Ioc 10883 n).filter Nat.Prime, r) _ (n + 1)
          (by omega) (fun q hq => (Finset.mem_filter.1 hq).2) ih' hp (by simp) (by omega)
          N hN1 (by omega)
      · rw [if_neg hp] at hN2 ⊢
        exact ih' N hN1 hN2
  intro N hN1 hN2
  exact key 98999987 (by norm_num) le_rfl N hN1 (by rw [hfinal]; exact hN2)

theorem link_Eq_FraitureFirstWindow : Principia.Erdos1054.Spine.Link_Eq_FraitureFirstWindow := by
  intro hCov hPW N hN1 hN2
  obtain ⟨S, hS, hsum⟩ := hCov (N - 1) (by omega) (by omega)
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.sum_empty] at hsum
    omega
  have hmem := hPW 10000 99000000 ((Finset.Ioc 10000 98999987).filter Nat.Prime) (by norm_num)
    (by norm_num) (by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      have hp' : p ≤ 99000000 := by omega
      exact ⟨hp.2, by exact_mod_cast hp.1.1, by exact_mod_cast hp'⟩) S hS hSne
  rw [hsum] at hmem
  have e : N = 1 + (N - 1) := by omega
  rw [e]
  exact hmem

theorem link_Step_FraitureLargeWindowCover :
    Principia.Erdos1054.Spine.Link_Step_FraitureLargeWindowCover := by
  intro hExt hSeed
  have key : ∀ n, 40000000 ≤ n → ∀ N, 105000000 ≤ N →
      N ≤ 156000000 + ∑ r ∈ (Finset.Ioc 40000000 n).filter Nat.Prime, r →
      N ∈ subsetSums ((Finset.Ioc 20000000 n).filter Nat.Prime) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro N hN1 hN2
      rw [Finset.Ioc_self, Finset.filter_empty, Finset.sum_empty] at hN2
      obtain ⟨S, _, hSP, hsum⟩ := hSeed N hN1 (by omega)
      refine ⟨S, ?_, hsum⟩
      intro p hp
      obtain ⟨hpp, h1, h2⟩ := hSP p hp
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨h1, h2.le⟩, hpp⟩
    | succ n hn ih =>
      intro N hN1 hN2
      rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hn, Finset.filter_insert] at hN2
      rw [← Finset.insert_Ioc_right_eq_Ioc_add_one (by omega : 20000000 ≤ n),
        Finset.filter_insert]
      by_cases hp : (n + 1).Prime
      · rw [if_pos hp] at hN2 ⊢
        have hnotin : n + 1 ∉ (Finset.Ioc 40000000 n).filter Nat.Prime := by simp
        rw [Finset.sum_insert hnotin] at hN2
        have hw := large_width n hn
        exact hExt 105000000 (156000000 + ∑ r ∈ (Finset.Ioc 40000000 n).filter Nat.Prime, r) _
          (n + 1) (by omega) (fun q hq => (Finset.mem_filter.1 hq).2) ih hp (by simp)
          (by omega) N hN1 (by omega)
      · rw [if_neg hp] at hN2 ⊢
        exact ih N hN1 hN2
  intro N hN1 hN2
  exact key 399000000000000 (by norm_num) N hN1 hN2

theorem link_Step_FraitureLargePrimeSum :
    Principia.Erdos1054.Spine.Link_Step_FraitureLargePrimeSum := by
  intro hD
  show 10 ^ 27 + 10 ^ 8 < ∑ p ∈ (Finset.Ioc 40000000 399000000000000).filter Nat.Prime, p
  have hA := dusart_at_nat hD 199500000000000 le_rfl
  have hB := dusart_at_nat hD 399000000000000 (by norm_num)
  have hcard := card_filter_prime_Ioc 199500000000000 399000000000000 (by norm_num)
  have hcardR := congrArg (Nat.cast : ℕ → ℝ) hcard
  rw [Nat.cast_add] at hcardR
  have hreal := lps_real_core _ _ _ _ _ (by norm_num) (by norm_num) hA.2 hB.1 hcardR
  have hge := card_mul_le_sum_of_subset ((Finset.Ioc 199500000000000 399000000000000).filter
      Nat.Prime) ((Finset.Ioc 40000000 399000000000000).filter Nat.Prime) 199500000000000
    (by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_Ioc] at hx ⊢
      exact ⟨⟨by omega, hx.1.2⟩, hx.2⟩)
    (by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_Ioc] at hx
      omega)
  have hgeR := (Nat.cast_le (α := ℝ)).2 hge
  rw [Nat.cast_mul, Nat.cast_ofNat] at hgeR
  have hfinR := lt_of_lt_of_le hreal hgeR
  have hfinR' : ((1000000000000000000100000000 : ℕ) : ℝ) <
      ((∑ p ∈ (Finset.Ioc 40000000 399000000000000).filter Nat.Prime, p : ℕ) : ℝ) := by
    rw [Nat.cast_ofNat]
    exact hfinR
  have hlit : (10 : ℕ) ^ 27 + 10 ^ 8 = 1000000000000000000100000000 := by norm_num
  rw [hlit]
  exact Nat.cast_lt.1 hfinR'

theorem link_Eq_FraitureLargeWindow : Principia.Erdos1054.Spine.Link_Eq_FraitureLargeWindow := by
  intro hCov hSum hPW N hN1 hN2
  have hlit : (10 : ℕ) ^ 27 + 10 ^ 8 = 1000000000000000000100000000 := by norm_num
  unfold Principia.Erdos1054.Step_FraitureLargePrimeSum at hSum
  rw [hlit] at hSum hN2
  obtain ⟨S, hS, hsum⟩ := hCov (N - 1) (by omega) (by omega)
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.sum_empty] at hsum
    omega
  have hmem := hPW 20000000 399000000000000
    ((Finset.Ioc 20000000 399000000000000).filter Nat.Prime) (by norm_num)
    (by norm_num) (by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      exact ⟨hp.2, by exact_mod_cast hp.1.1, by exact_mod_cast hp.1.2⟩) S hS hSne
  rw [hsum] at hmem
  have e : N = 1 + (N - 1) := by omega
  rw [e]
  exact hmem

theorem link_Step_FraitureTailEven : Principia.Erdos1054.Spine.Link_Step_FraitureTailEven := by
  intro hBG hT3 n hn hnT
  have hlit : (10 : ℕ) ^ 27 + 10 ^ 8 = 1000000000000000000100000000 := by norm_num
  rw [hlit] at hnT
  obtain ⟨k, hk⟩ := hn
  obtain ⟨H, hH⟩ : ∃ H, H = n - 1 := ⟨_, rfl⟩
  have hHodd : Odd H := ⟨k - 1, by omega⟩
  have hH27 : 10 ^ 27 ≤ H := by
    rw [show (10 : ℕ) ^ 27 = 1000000000000000000000000000 by norm_num]
    omega
  obtain ⟨p, q, r, hp, hq, hr, _, _, _, hpq, hpr, hqr, hsum, hzp, hzq, hzr⟩ :=
    hBG H hHodd hH27
  have hHR : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH27
  have hH0 : (0 : ℝ) < H := lt_of_lt_of_le (by norm_num) hHR
  have hlogH : 0 < Real.log H := Real.log_pos (lt_of_lt_of_le (by norm_num) hHR)
  have hbig := mul_log_sq_lt (H : ℝ) hHR (30000 ^ 2) (by norm_num)
  have hden : 0 < 30000 * Real.log H := by positivity
  obtain ⟨z, hzdef⟩ : ∃ z, z = (H : ℝ) / (30000 * Real.log H) := ⟨_, rfl⟩
  rw [← hzdef] at hzp hzq hzr
  have hz0 : 0 < z := by rw [hzdef]; exact div_pos hH0 hden
  have hzmul : z * (30000 * Real.log H) = H := by
    rw [hzdef]; exact div_mul_cancel₀ _ hden.ne'
  have hsq : (30000 * Real.log H) * (30000 * Real.log H) < (H : ℝ) := by
    have e : (30000 * Real.log H) * (30000 * Real.log H) = 30000 ^ 2 * Real.log H ^ 2 := by
      ring
    rw [e]
    exact hbig
  have hz : (H : ℝ) < z * z := by
    have hcc : 0 < (30000 * Real.log H) * (30000 * Real.log H) := mul_pos hden hden
    have h1 : (H : ℝ) * ((30000 * Real.log H) * (30000 * Real.log H)) <
        (z * (30000 * Real.log H)) * (z * (30000 * Real.log H)) := by
      rw [hzmul]
      exact mul_lt_mul_of_pos_left hsq hH0
    have h2 : (z * (30000 * Real.log H)) * (z * (30000 * Real.log H)) =
        (z * z) * ((30000 * Real.log H) * (30000 * Real.log H)) := by ring
    rw [h2] at h1
    exact lt_of_mul_lt_mul_right h1 hcc.le
  have hpair : ∀ x y : ℕ, z < x → z < y → H < x * y := by
    intro x y hx hy
    have hxy : (H : ℝ) < (x : ℝ) * y := lt_trans hz (mul_lt_mul'' hx hy hz0.le hz0.le)
    exact_mod_cast hxy
  have hmem := tail_three hT3 p q r H hp hq hr hpq hpr hqr hsum (hpair p q hzp hzq)
    (hpair p r hzp hzr) (hpair q r hzq hzr)
  have e : n = 1 + H := by omega
  rw [e]
  exact hmem

theorem link_Step_FraitureTailOdd : Principia.Erdos1054.Spine.Link_Step_FraitureTailOdd := by
  intro hBG hT4 n hn hnT
  have hlit : (10 : ℕ) ^ 27 + 10 ^ 8 = 1000000000000000000100000000 := by norm_num
  rw [hlit] at hnT
  have hnR : (1000000000000000000100000000 : ℝ) ≤ n := by exact_mod_cast hnT
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  have hn27 : (10 : ℝ) ^ 27 ≤ n := le_trans (by norm_num) hnR
  -- `log n > 1`
  have hL1 : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt hn0]
    calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ < n := lt_of_lt_of_le (by norm_num) hnR
  -- `log n ≤ 63 + n / T`, from `log T < 64` and `log (n / T) ≤ n / T - 1`
  have hlogT : Real.log 1000000000000000000100000000 < 64 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have he : Real.exp 64 = Real.exp 1 ^ 64 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    calc (1000000000000000000100000000 : ℝ) < (2.7182818283 : ℝ) ^ 64 := by norm_num
      _ < Real.exp 1 ^ 64 := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have hLup : Real.log n ≤ 63 + n / 1000000000000000000100000000 := by
    have h := Real.log_le_sub_one_of_pos
      (div_pos hn0 (by norm_num : (0 : ℝ) < 1000000000000000000100000000))
    rw [Real.log_div hn0.ne' (by norm_num)] at h
    linarith
  -- Bertrand: an odd prime `ℓ` with `60000 log n < ℓ ≤ 120000 log n`
  have hx0 : (0 : ℝ) ≤ 60000 * Real.log n := by linarith
  have hfl : ⌊60000 * Real.log n⌋₊ ≠ 0 :=
    (Nat.floor_pos.2 (by linarith : (1 : ℝ) ≤ 60000 * Real.log n)).ne'
  obtain ⟨l, hl, hkl, hl2k⟩ := Nat.exists_prime_lt_and_le_two_mul _ hfl
  have hlgt : 60000 * Real.log n < l := by
    have h1 := Nat.lt_floor_add_one (60000 * Real.log n)
    have h2 : (⌊60000 * Real.log n⌋₊ : ℝ) + 1 ≤ l := by exact_mod_cast hkl
    linarith
  have hlle : (l : ℝ) ≤ 120000 * Real.log n := by
    have h1 := Nat.floor_le hx0
    have h2 : (l : ℝ) ≤ 2 * (⌊60000 * Real.log n⌋₊ : ℝ) := by exact_mod_cast hl2k
    linarith
  have hlodd : Odd l := hl.odd_of_ne_two (by
    intro h
    rw [h] at hlgt
    push_cast at hlgt
    linarith)
  -- `H = n - 1 - ℓ`, with `H ≥ 10^27` and `H > n / 2`
  have hHR27 : (1000000000000000000000000000 : ℝ) ≤ (n : ℝ) - 1 - l := by linarith
  have hln : l + 1 ≤ n := by
    have hr : (l : ℝ) + 1 ≤ n := by linarith
    exact_mod_cast hr
  obtain ⟨H, hH⟩ : ∃ H, H = n - 1 - l := ⟨_, rfl⟩
  have hHcast : (H : ℝ) = (n : ℝ) - 1 - l := by
    have h' : H + 1 + l = n := by omega
    have h'' : (H : ℝ) + 1 + l = n := by exact_mod_cast h'
    linarith
  have hH27 : 10 ^ 27 ≤ H := by
    have hr : ((1000000000000000000000000000 : ℕ) : ℝ) ≤ (H : ℝ) := by
      rw [hHcast]; push_cast; linarith
    have hr' : 1000000000000000000000000000 ≤ H := by exact_mod_cast hr
    rw [show (10 : ℕ) ^ 27 = 1000000000000000000000000000 by norm_num]
    exact hr'
  have hHodd : Odd H := by
    obtain ⟨a, ha⟩ := hn
    obtain ⟨b, hb⟩ := hlodd
    exact ⟨a - b - 1, by omega⟩
  have hHhalf : (n : ℝ) < 2 * H := by
    rw [hHcast]
    linarith
  have hHn : (H : ℝ) < n := by
    rw [hHcast]
    linarith
  obtain ⟨p, q, r, hp, hq, hr, _, _, _, hpq, hpr, hqr, hsum, hzp, hzq, hzr⟩ :=
    hBG H hHodd hH27
  have hH1 : (1 : ℝ) < H := by rw [hHcast]; linarith
  have hlogH : 0 < Real.log H := Real.log_pos hH1
  have hlogHn : Real.log H < Real.log n := Real.log_lt_log (by linarith) hHn
  have hden : 0 < 30000 * Real.log H := by positivity
  obtain ⟨z, hzdef⟩ : ∃ z, z = (H : ℝ) / (30000 * Real.log H) := ⟨_, rfl⟩
  rw [← hzdef] at hzp hzq hzr
  have hz0 : 0 < z := by rw [hzdef]; exact div_pos (by linarith) hden
  have hzmul : z * (30000 * Real.log H) = H := by
    rw [hzdef]; exact div_mul_cancel₀ _ hden.ne'
  -- `n / (60000 log n) < z`
  have hzn : (n : ℝ) / (60000 * Real.log n) < z := by
    rw [hzdef, div_lt_div_iff₀ (by positivity) hden]
    have h1 : (n : ℝ) * (30000 * Real.log H) < (2 * H) * (30000 * Real.log H) :=
      mul_lt_mul_of_pos_right hHhalf hden
    have h2 : (2 * (H : ℝ)) * (30000 * Real.log H) < (2 * H) * (30000 * Real.log n) :=
      mul_lt_mul_of_pos_left (by linarith) (by linarith)
    have e : (2 * (H : ℝ)) * (30000 * Real.log n) = (H : ℝ) * (60000 * Real.log n) := by ring
    linarith
  -- `120000 log n < n / (60000 log n)`
  have hbig := mul_log_sq_lt (n : ℝ) hn27 7200000000 (by norm_num)
  have hnL : 120000 * Real.log n < (n : ℝ) / (60000 * Real.log n) := by
    rw [lt_div_iff₀ (by positivity)]
    have e : 120000 * Real.log n * (60000 * Real.log n) = 7200000000 * Real.log n ^ 2 := by
      ring
    rw [e]
    exact hbig
  have hlx : ∀ x : ℕ, z < x → l < x := by
    intro x hx
    have hr : (l : ℝ) < x := by linarith
    exact_mod_cast hr
  have hHx : ∀ x : ℕ, z < x → H < l * x := by
    intro x hx
    have e1 : 0 < ((l : ℝ) - 60000 * Real.log n) * x := mul_pos (by linarith) (by linarith)
    have e2 : 0 < 60000 * Real.log n * ((x : ℝ) - z) := mul_pos (by linarith) (by linarith)
    have e3 : 0 < 60000 * z * (Real.log n - Real.log H) := mul_pos (by linarith) (by linarith)
    have e4 : (l : ℝ) * x = ((l : ℝ) - 60000 * Real.log n) * x +
        60000 * Real.log n * ((x : ℝ) - z) + 60000 * z * (Real.log n - Real.log H) +
        2 * (z * (30000 * Real.log H)) := by ring
    have hlx' : (H : ℝ) < (l : ℝ) * x := by
      rw [e4, hzmul]
      linarith
    exact_mod_cast hlx'
  have hmem := tail_four hT4 l p q r H hl hp hq hr (hlx p hzp) (hlx q hzq) (hlx r hzr) hpq hpr
    hqr hsum (hHx p hzp) (hHx q hzq) (hHx r hzr)
  have e : n = 1 + l + H := by omega
  rw [e]
  exact hmem

theorem link_Prop_FraitureTail : Principia.Erdos1054.Spine.Link_Prop_FraitureTail := by
  intro hE hO n hn
  rcases Nat.even_or_odd n with h | h
  · exact hE n h hn
  · exact hO n h hn

theorem link_Thm_FraitureRepresentability_Ge6 :
    Principia.Erdos1054.Spine.Link_Thm_FraitureRepresentability_Ge6 := by
  intro h N hN
  have h' : R = {N : ℕ | 1 ≤ N ∧ N ≠ 2 ∧ N ≠ 5} := h
  rw [h']
  exact ⟨by omega, by omega, by omega⟩

end Principia.Erdos1054.Proofs
