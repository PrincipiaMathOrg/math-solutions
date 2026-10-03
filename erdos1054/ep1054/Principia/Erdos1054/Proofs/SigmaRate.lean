/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

/-!
# EP1054 `lem:sigma-rate`, odd-prime clause (paper lines 500-557)

Proves `Principia.Erdos1054.Spine.Link_Lem_SigmaRate_OddPrime`:
`Cite_Pollack_Lemma24 → Std_SiegelWalfisz_dyadic → Lem_SigmaRate_OddPrime`.

The proof follows the paper:
* `h_q` (`Principia.Erdos1054.hq`) is multiplicative with values in `{0, 1}` (`hq_isMultiplicative`,
  `hq_nonneg`, `hq_le_one`), and `1_{q ∤ σ(n)} ≤ h_q(n)` (`dvd_sig_of_exists`, `Bq_le_sum_hq`);
* the mean-value bound `[Pollack, Lemma 2.4]` then gives
  `B_q(y) ≪ y exp(−∑_{p ≤ y, p ≡ −1 (q)} 1/p)` (`sum_hq_prime_le`);
* the dyadic Siegel–Walfisz lower bound, summed over the intervals `(e^a 2^k, e^a 2^{k+1}]` with
  `a = C q²` (`piAP_dyadic_le`, `dyadic_sum`), and `∑_{k<K} 1/(a + k log 2) ≥ log((a+K log 2)/a)/log 2`
  (`log_le_harmonic`) give `∑_{p ≤ y, p ≡ −1 (q)} 1/p ≥ (c/(4 log 2)) log log y / q` once
  `q ≤ log log y / log log log y` and `y` is large (`eventually_conditions`).

Witnesses: `c₀ = 1`, `c₁ = c_SW / (4 log 2)`, implied constant `max C_Pollack 0`.
`Lem_SigmaRate` itself is the conjunction the spine assembles (`And.intro`), so no theorem is
stated for it here.
-/

namespace Principia.Erdos1054.Proofs.SigmaRate

open Finset Filter
open Principia.Erdos1054

/-! ## The majorant `h_q` -/

open Classical in
theorem hq_apply (q n : ℕ) : hq q n = if n = 0 then 0 else
    if ∃ p ∈ n.primeFactors, q ∣ p + 1 ∧ n.factorization p = 1 then 0 else 1 := rfl

theorem hq_nonneg (q n : ℕ) : 0 ≤ hq q n := by
  rw [hq_apply]; split_ifs <;> norm_num

theorem hq_le_one (q n : ℕ) : hq q n ≤ 1 := by
  rw [hq_apply]; split_ifs <;> norm_num

theorem hq_prime (q p : ℕ) (hp : p.Prime) : hq q p = if q ∣ p + 1 then 0 else 1 := by
  rw [hq_apply, if_neg hp.ne_zero]
  by_cases h : q ∣ p + 1
  · have hmem : p ∈ p.primeFactors := by
      rw [hp.primeFactors]; exact Finset.mem_singleton_self p
    rw [if_pos h, if_pos ⟨p, hmem, h, hp.factorization_self⟩]
  · rw [if_neg h, if_neg]
    rintro ⟨r, hr, hqr, _⟩
    rw [hp.primeFactors, Finset.mem_singleton] at hr
    exact h (hr ▸ hqr)

theorem hq_isMultiplicative (q : ℕ) : (hq q).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [hq_apply], ?_⟩
  intro m n hm hn hmn
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
  have hdisj := Nat.Coprime.disjoint_primeFactors hmn
  have hzn : ∀ p ∈ m.primeFactors, n.factorization p = 0 := by
    intro p hp
    rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
    exact Finset.disjoint_left.mp hdisj hp
  have hzm : ∀ p ∈ n.primeFactors, m.factorization p = 0 := by
    intro p hp
    rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
    exact Finset.disjoint_right.mp hdisj hp
  have key : (∃ p ∈ (m * n).primeFactors, q ∣ p + 1 ∧ (m * n).factorization p = 1) ↔
      (∃ p ∈ m.primeFactors, q ∣ p + 1 ∧ m.factorization p = 1) ∨
      (∃ p ∈ n.primeFactors, q ∣ p + 1 ∧ n.factorization p = 1) := by
    rw [Nat.primeFactors_mul hm hn, Nat.factorization_mul hm hn]
    constructor
    · rintro ⟨p, hp, hqp, hf⟩
      rw [Finset.mem_union] at hp
      rcases hp with hp | hp
      · left
        refine ⟨p, hp, hqp, ?_⟩
        simpa [hzn p hp] using hf
      · right
        refine ⟨p, hp, hqp, ?_⟩
        simpa [hzm p hp] using hf
    · rintro (⟨p, hp, hqp, hf⟩ | ⟨p, hp, hqp, hf⟩)
      · exact ⟨p, Finset.mem_union_left _ hp, hqp, by simp [hzn p hp, hf]⟩
      · exact ⟨p, Finset.mem_union_right _ hp, hqp, by simp [hzm p hp, hf]⟩
  rw [hq_apply q (m * n), hq_apply q m, hq_apply q n, if_neg hmn0, if_neg hm, if_neg hn]
  by_cases hA : ∃ p ∈ m.primeFactors, q ∣ p + 1 ∧ m.factorization p = 1
  · rw [if_pos (key.2 (Or.inl hA)), if_pos hA, zero_mul]
  · by_cases hB : ∃ p ∈ n.primeFactors, q ∣ p + 1 ∧ n.factorization p = 1
    · rw [if_pos (key.2 (Or.inr hB)), if_pos hB, mul_zero]
    · rw [if_neg (fun h => (key.1 h).elim hA hB), if_neg hA, if_neg hB, mul_one]

/-- If a prime `p ≡ −1 (mod q)` exactly divides `n`, then `q ∣ σ(p) ∣ σ(n)` (paper line 530). -/
theorem dvd_sig_of_exists (q n : ℕ) (hn : n ≠ 0)
    (h : ∃ p ∈ n.primeFactors, q ∣ p + 1 ∧ n.factorization p = 1) : q ∣ sig n := by
  obtain ⟨p, hp, hqp, hf⟩ := h
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hcop : Nat.Coprime (p ^ n.factorization p) (n / p ^ n.factorization p) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hpp hn)
  have hsplit := Nat.ordProj_mul_ordCompl_eq_self n p
  have hsig : sig n = sig (p ^ n.factorization p) * sig (n / p ^ n.factorization p) := by
    show ArithmeticFunction.sigma 1 n = _
    conv_lhs => rw [← hsplit]
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  have h1 : sig p = p + 1 := by
    have h2 := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hpp
    rw [pow_one] at h2
    show ArithmeticFunction.sigma 1 p = p + 1
    rw [h2, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, add_comm]
  rw [hsig, hf, pow_one, h1]
  exact Dvd.dvd.mul_right hqp _

/-- `1_{q ∤ σ(n)} ≤ h_q(n)`, summed: `B_q(y) ≤ ∑_{n ≤ y} h_q(n)` (paper lines 530-535). -/
theorem Bq_le_sum_hq (q : ℕ) (y : ℝ) :
    (Bq q y : ℝ) ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, hq q n := by
  unfold Bq cnt
  rw [Finset.natCast_card_filter]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 : n ≠ 0 := by
    rw [Finset.mem_Icc] at hn; omega
  split_ifs with h
  · have h' : ¬ q ∣ sig n := h
    rw [hq_apply, if_neg hn0, if_neg (fun hex => h' (dvd_sig_of_exists q n hn0 hex))]
  · exact hq_nonneg q n

/-! ## Primes `≡ −1 (mod q)` -/

/-- The weight `1/p` of a prime `p ≡ −1 (mod q)`, in the residue form used by `piAP`. -/
noncomputable def w (q n : ℕ) : ℝ := if n.Prime ∧ n % q = (q - 1) % q then 1 / (n : ℝ) else 0

theorem w_nonneg (q n : ℕ) : 0 ≤ w q n := by
  unfold w
  split_ifs
  · positivity
  · exact le_rfl

theorem dvd_succ_of_mod (q p : ℕ) (hq1 : 1 ≤ q) (h : p % q = (q - 1) % q) : q ∣ p + 1 := by
  have h1 : p + 1 ≡ (q - 1) + 1 [MOD q] := Nat.ModEq.add_right 1 h
  rw [Nat.sub_add_cancel hq1] at h1
  exact (Nat.modEq_zero_iff_dvd).1 (h1.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))

/-- One dyadic interval: `π(2t; q, −1) − π(t; q, −1) ≤ 2t ∑_{t < p ≤ 2t, p ≡ −1} 1/p`. -/
theorem piAP_dyadic_le (q : ℕ) (t : ℝ) (ht : 0 < t) :
    (piAP (2 * t) q (q - 1) : ℝ) - piAP t q (q - 1) ≤
      2 * t * ∑ n ∈ Finset.Ioc ⌊t⌋₊ ⌊2 * t⌋₊, w q n := by
  have hcard : piAP (2 * t) q (q - 1) ≤ piAP t q (q - 1) +
      ((Finset.Ioc ⌊t⌋₊ ⌊2 * t⌋₊).filter (fun p => p.Prime ∧ p % q = (q - 1) % q)).card := by
    unfold piAP
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_union, Finset.mem_Ioc] at hx ⊢
    by_cases hxt : x ≤ ⌊t⌋₊
    · exact Or.inl ⟨hxt, hx.2⟩
    · exact Or.inr ⟨⟨by omega, hx.1⟩, hx.2⟩
  have hsum : (((Finset.Ioc ⌊t⌋₊ ⌊2 * t⌋₊).filter
      (fun p => p.Prime ∧ p % q = (q - 1) % q)).card : ℝ) ≤
      2 * t * ∑ n ∈ Finset.Ioc ⌊t⌋₊ ⌊2 * t⌋₊, w q n := by
    rw [Finset.natCast_card_filter, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Ioc] at hn
    unfold w
    split_ifs with h
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hn2 : (n : ℝ) ≤ 2 * t :=
        le_trans (by exact_mod_cast hn.2) (Nat.floor_le (by positivity))
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      linarith
    · simp
  have hcast : (piAP (2 * t) q (q - 1) : ℝ) ≤ (piAP t q (q - 1) : ℝ) +
      (((Finset.Ioc ⌊t⌋₊ ⌊2 * t⌋₊).filter (fun p => p.Prime ∧ p % q = (q - 1) % q)).card : ℝ) := by
    exact_mod_cast hcard
  linarith

/-- Summing Siegel–Walfisz over the dyadic intervals `(e^a 2^k, e^a 2^{k+1}]`, `k < K`. -/
theorem dyadic_sum (q : ℕ) (hq0 : 0 < q) (a c : ℝ) (ha : 0 < a)
    (hsw : ∀ t : ℝ, Real.exp a ≤ t →
      c * t / ((q : ℝ) * Real.log t) ≤ (piAP (2 * t) q (q - 1) : ℝ) - (piAP t q (q - 1) : ℝ))
    (K : ℕ) :
    ∑ k ∈ Finset.range K, c / (2 * q) * (1 / (a + k * Real.log 2)) ≤
      ∑ n ∈ Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a + K * Real.log 2)⌋₊, w q n := by
  have hb : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq0
  induction K with
  | zero => simp
  | succ K ih =>
    have hden : 0 < a + K * Real.log 2 := by positivity
    have hta : Real.exp a ≤ Real.exp (a + K * Real.log 2) :=
      Real.exp_le_exp.mpr (by nlinarith [hb])
    have h2t : Real.exp (a + ((K + 1 : ℕ) : ℝ) * Real.log 2) =
        2 * Real.exp (a + K * Real.log 2) := by
      rw [show a + ((K + 1 : ℕ) : ℝ) * Real.log 2 = (a + K * Real.log 2) + Real.log 2 by
        push_cast; ring, Real.exp_add, Real.exp_log two_pos, mul_comm]
    have htpos : 0 < Real.exp (a + K * Real.log 2) := Real.exp_pos _
    have hmono1 : ⌊Real.exp a⌋₊ ≤ ⌊Real.exp (a + K * Real.log 2)⌋₊ := Nat.floor_le_floor hta
    have hmono2 : ⌊Real.exp (a + K * Real.log 2)⌋₊ ≤ ⌊2 * Real.exp (a + K * Real.log 2)⌋₊ :=
      Nat.floor_le_floor (by linarith)
    rw [Finset.sum_range_succ, h2t, ← Finset.sum_Ioc_consecutive (w q) hmono1 hmono2]
    have hpiece : c / (2 * q) * (1 / (a + K * Real.log 2)) ≤
        ∑ n ∈ Finset.Ioc ⌊Real.exp (a + K * Real.log 2)⌋₊
          ⌊2 * Real.exp (a + K * Real.log 2)⌋₊, w q n := by
      have h1 := hsw _ hta
      have h2 := piAP_dyadic_le q _ htpos
      rw [Real.log_exp] at h1
      have h3 := le_trans h1 h2
      rw [div_le_iff₀ (by positivity)] at h3
      rw [div_mul_div_comm, mul_one, div_le_iff₀ (by positivity)]
      refine le_of_mul_le_mul_right ?_ htpos
      calc c * Real.exp (a + K * Real.log 2)
          ≤ 2 * Real.exp (a + K * Real.log 2) *
              (∑ n ∈ Finset.Ioc ⌊Real.exp (a + K * Real.log 2)⌋₊
                ⌊2 * Real.exp (a + K * Real.log 2)⌋₊, w q n) *
              ((q : ℝ) * (a + K * Real.log 2)) := h3
        _ = (∑ n ∈ Finset.Ioc ⌊Real.exp (a + K * Real.log 2)⌋₊
                ⌊2 * Real.exp (a + K * Real.log 2)⌋₊, w q n) *
              (2 * q * (a + K * Real.log 2)) * Real.exp (a + K * Real.log 2) := by ring
    linarith [ih]

/-- `∑_{k<K} 1/(a + kb) ≥ (log(a + Kb) − log a)/b`, from `log x ≤ x − 1`. -/
theorem log_le_harmonic (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (K : ℕ) :
    (Real.log (a + K * b) - Real.log a) / b ≤ ∑ k ∈ Finset.range K, 1 / (a + k * b) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hx : 0 < a + K * b := by positivity
    have hy : 0 < a + ((K + 1 : ℕ) : ℝ) * b := by positivity
    have hstep : Real.log (a + ((K + 1 : ℕ) : ℝ) * b) - Real.log (a + K * b) ≤ b / (a + K * b) := by
      rw [← Real.log_div hy.ne' hx.ne']
      have h1 := Real.log_le_sub_one_of_pos (div_pos hy hx)
      have e : (a + ((K + 1 : ℕ) : ℝ) * b) / (a + K * b) - 1 = b / (a + K * b) := by
        rw [div_sub_one hx.ne']
        congr 1
        push_cast
        ring
      linarith
    have hsplit : (Real.log (a + ((K + 1 : ℕ) : ℝ) * b) - Real.log a) / b =
        (Real.log (a + K * b) - Real.log a) / b +
          (Real.log (a + ((K + 1 : ℕ) : ℝ) * b) - Real.log (a + K * b)) / b := by
      ring
    have h2 : (Real.log (a + ((K + 1 : ℕ) : ℝ) * b) - Real.log (a + K * b)) / b ≤
        1 / (a + K * b) := by
      rw [div_le_iff₀ hb]
      calc _ ≤ b / (a + K * b) := hstep
        _ = 1 / (a + K * b) * b := by ring
    rw [hsplit]
    linarith

/-! ## The eventual conditions on `y` -/

theorem eventually_conditions (C : ℝ) : ∀ᶠ y : ℝ in atTop, 1 ≤ y ∧ 2 ≤ Real.log y ∧
    1 ≤ Real.log (Real.log (Real.log y)) ∧
    Real.log 2 + Real.log C + 2 * Real.log (Real.log (Real.log y)) ≤
      Real.log (Real.log y) / 2 := by
  have h1 : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have h2 : Tendsto (fun y => Real.log (Real.log y)) atTop atTop := h1.comp h1
  have h3 : Tendsto (fun y => Real.log (Real.log (Real.log y))) atTop atTop := h1.comp h2
  have hw : ∀ᶠ w : ℝ in atTop, Real.log 2 + Real.log C + 2 * Real.log w ≤ w / 2 := by
    have hlo := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 8 by norm_num)
    filter_upwards [hlo, eventually_ge_atTop (4 * (Real.log 2 + Real.log C)),
      eventually_ge_atTop (0 : ℝ)] with w hw1 hw2 hw3
    simp only [Real.norm_eq_abs, id_eq] at hw1
    rw [abs_of_nonneg hw3] at hw1
    have := le_abs_self (Real.log w)
    linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ), h1.eventually_ge_atTop 2,
    h3.eventually_ge_atTop 1, h2.eventually hw] with y hy1 hy2 hy3 hy4
  exact ⟨hy1, hy2, hy3, hy4⟩

theorem logIt_two (y : ℝ) : logIt 2 y = Real.log (Real.log y) := rfl

theorem logIt_three (y : ℝ) : logIt 3 y = Real.log (Real.log (Real.log y)) := rfl

/-- `∑_{p ≤ N} (h_q(p) − 1)/p ≤ −∑_{p ≤ N, p ≡ −1 (q)} 1/p` (paper lines 537-540). -/
theorem sum_hq_prime_le (q : ℕ) (hq1 : 1 ≤ q) (N : ℕ) :
    ∑ p ∈ (Finset.Iic N).filter Nat.Prime, (hq q p - 1) / (p : ℝ) ≤
      -∑ n ∈ Finset.Iic N, w q n := by
  rw [Finset.sum_filter, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro n _
  unfold w
  by_cases hn : n.Prime
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
    rw [if_pos hn, hq_prime q n hn]
    by_cases hm : n % q = (q - 1) % q
    · rw [if_pos (dvd_succ_of_mod q n hq1 hm), if_pos ⟨hn, hm⟩]
      exact le_of_eq (by ring)
    · rw [if_neg (show ¬ (n.Prime ∧ n % q = (q - 1) % q) from fun h => hm h.2), neg_zero]
      split_ifs
      · exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hn0.le
      · exact le_of_eq (by ring)
  · rw [if_neg hn, if_neg (show ¬ (n.Prime ∧ n % q = (q - 1) % q) from fun h => hn h.1),
      neg_zero]

end Principia.Erdos1054.Proofs.SigmaRate

namespace Principia.Erdos1054.Proofs

open Finset Filter
open Principia.Erdos1054 Principia.Erdos1054.Proofs.SigmaRate

/-- **`lem:sigma-rate`, odd-prime clause** (EP1054.tex lines 508-517, proof 521-557), from the
Halberstam–Richert mean-value bound `[Pollack, Lemma 2.4]` and the dyadic Siegel–Walfisz lower
bound. Witnesses: `c₀ = 1`, `c₁ = c_SW/(4 log 2)`, `C = max C_Pollack 0`. -/
theorem link_Lem_SigmaRate_OddPrime : Principia.Erdos1054.Spine.Link_Lem_SigmaRate_OddPrime := by
  intro hP hSW
  unfold Cite_Pollack_Lemma24 at hP
  unfold Std_SiegelWalfisz_dyadic at hSW
  unfold Lem_SigmaRate_OddPrime
  obtain ⟨CP, hCP⟩ := hP
  obtain ⟨C, hC, c, hc, hsw⟩ := hSW
  obtain ⟨y₀, hy₀⟩ := Filter.eventually_atTop.mp (eventually_conditions C)
  have hb : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hb1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  refine ⟨1, one_pos, c / (4 * Real.log 2), div_pos hc (by linarith), max CP 0, y₀, ?_⟩
  intro y hy q hqp hq3 hqle
  obtain ⟨hy1, hL1, hL3, hmain⟩ := hy₀ y hy
  rw [logIt_two, logIt_three, one_mul] at hqle
  rw [logIt_two]
  have hy0 : 0 < y := by linarith
  have hL1pos : 0 < Real.log y := by linarith
  have hL2pos : 0 < Real.log (Real.log y) := Real.log_pos (by linarith)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqp.pos
  have hqL2 : (q : ℝ) ≤ Real.log (Real.log y) := hqle.trans (div_le_self hL2pos.le hL3)
  -- `a = C q² = log z`, the Siegel–Walfisz threshold (paper line 543)
  have ha : 0 < C * (q : ℝ) ^ 2 := by positivity
  have hloga : Real.log (C * (q : ℝ) ^ 2) ≤
      Real.log C + 2 * Real.log (Real.log (Real.log y)) := by
    rw [Real.log_mul hC.ne' (by positivity), Real.log_pow]
    have := Real.log_le_log hqpos hqL2
    push_cast
    linarith
  have hlogy : Real.log (Real.log y) - Real.log 2 ≤ Real.log (Real.log y - Real.log 2) := by
    have h1 : Real.log (Real.log y / 2) = Real.log (Real.log y) - Real.log 2 :=
      Real.log_div hL1pos.ne' two_ne_zero
    rw [← h1]
    exact Real.log_le_log (by linarith) (by linarith)
  have haL : C * (q : ℝ) ^ 2 ≤ Real.log y - Real.log 2 :=
    (Real.log_le_log_iff ha (by linarith)).mp (by linarith)
  set a := C * (q : ℝ) ^ 2
  -- the number of dyadic intervals between `z = e^a` and `y`
  set K := ⌊(Real.log y - a) / Real.log 2⌋₊
  have hK1 : (K : ℝ) ≤ (Real.log y - a) / Real.log 2 :=
    Nat.floor_le (div_nonneg (by linarith) hb.le)
  have hK2 : (Real.log y - a) / Real.log 2 < K + 1 := Nat.lt_floor_add_one _
  have hKup : a + K * Real.log 2 ≤ Real.log y := by
    have := (le_div_iff₀ hb).mp hK1
    linarith
  have hKlow : Real.log y - Real.log 2 < a + K * Real.log 2 := by
    have := (div_lt_iff₀ hb).mp hK2
    rw [add_mul, one_mul] at this
    linarith
  have htK : ⌊Real.exp (a + K * Real.log 2)⌋₊ ≤ ⌊y⌋₊ := by
    apply Nat.floor_le_floor
    calc Real.exp (a + K * Real.log 2) ≤ Real.exp (Real.log y) := Real.exp_le_exp.mpr hKup
      _ = y := Real.exp_log hy0
  have hS1 : ∑ n ∈ Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a + K * Real.log 2)⌋₊, w q n ≤
      ∑ n ∈ Finset.Iic ⌊y⌋₊, w q n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      rw [Finset.mem_Ioc] at hx
      rw [Finset.mem_Iic]
      omega
    · intro n _ _
      exact w_nonneg q n
  have hS2 := dyadic_sum q hqp.pos a c ha (fun t ht => hsw q hqp hq3 t ht) K
  rw [← Finset.mul_sum] at hS2
  have hS3 := log_le_harmonic a (Real.log 2) ha hb K
  have hlogfinal : Real.log (Real.log y) / 2 ≤
      Real.log (a + K * Real.log 2) - Real.log a := by
    have := Real.log_le_log (by linarith) hKlow.le
    linarith
  have hS : c / (4 * Real.log 2) * Real.log (Real.log y) / q ≤
      ∑ n ∈ Finset.Iic ⌊y⌋₊, w q n := by
    have e : c / (4 * Real.log 2) * Real.log (Real.log y) / q =
        c / (2 * q) * ((Real.log (Real.log y) / 2) / Real.log 2) := by ring
    rw [e]
    calc c / (2 * q) * ((Real.log (Real.log y) / 2) / Real.log 2)
        ≤ c / (2 * q) * ((Real.log (a + K * Real.log 2) - Real.log a) / Real.log 2) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlogfinal hb.le) (by positivity)
      _ ≤ c / (2 * q) * ∑ k ∈ Finset.range K, 1 / (a + k * Real.log 2) :=
          mul_le_mul_of_nonneg_left hS3 (by positivity)
      _ ≤ _ := hS2
      _ ≤ _ := hS1
  have hPol := hCP (hq q) (hq_isMultiplicative q) (hq_nonneg q)
    (fun p k _ _ => hq_le_one q _) y hy1
  have hX := sum_hq_prime_le q (by omega) ⌊y⌋₊
  calc (Bq q y : ℝ) ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, hq q n := Bq_le_sum_hq q y
    _ ≤ CP * y * Real.exp (∑ p ∈ (Finset.Iic ⌊y⌋₊).filter Nat.Prime, (hq q p - 1) / (p : ℝ)) :=
        hPol
    _ ≤ max CP 0 * y *
          Real.exp (∑ p ∈ (Finset.Iic ⌊y⌋₊).filter Nat.Prime, (hq q p - 1) / (p : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left CP 0) hy0.le)
          (Real.exp_pos _).le
    _ ≤ max CP 0 * y * Real.exp (-(c / (4 * Real.log 2) * Real.log (Real.log y) / q)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (le_max_right CP 0) hy0.le)
        exact Real.exp_le_exp.mpr (by linarith)

end Principia.Erdos1054.Proofs
