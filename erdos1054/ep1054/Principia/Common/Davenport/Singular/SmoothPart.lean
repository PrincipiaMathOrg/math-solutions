/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Davenport.Truncation
import Principia.Common.LucaPomerance.Smooth
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

/-!
# The `t`-smooth part of `n`, localisation of `abundTrunc`, and its second moment

`smoothPart t n = ∏_{p ≤ t} p^{v_p(n)}` and `logSmooth t n = ∑_{p ≤ t} v_p(n) log p`, which is
`log (smoothPart t n)` for `n ≠ 0` (`log_smoothPart`).

* **Localisation** (`abundTrunc_eq_smoothPart`): if `n ≠ 0` has no prime factor in `(t, K]`, then
  `abundTrunc K n = abundTrunc K (smoothPart t n)` — every divisor `d ≤ K` of `n` is `t`-smooth.
* **Second moment** (`sum_logSmooth_sq_le`): `∑_{n ≤ X} (logSmooth t n)² ≤ X (S² + 2 S log t)` with
  `S = ∑_{p ≤ t} log p/(p − 1)`, via `v_p(n) = #{i ≤ X : p^i ∣ n}`, `logSmooth t (p^i m) =
  i log p + logSmooth t m` and the first moment `∑_{m ≤ Y} logSmooth t m ≤ Y S` (Legendre).
* **Tail** (`card_smoothPart_gt_le`): `#{n ≤ X : smoothPart t n > t^u} ≤ C_B X / u²`,
  `C_B = C_M² + 2 C_M` with `C_M = Pollack14.mertensConst` (Mertens' first theorem).

The first moment alone gives only `C_M/u`; the square is what the singularity argument needs.
-/

namespace Principia.Common.Davenport.Singular

open Finset Principia.Common.Davenport

/-- The `t`-smooth part `∏_{p ≤ t} p^{v_p(n)}` of `n` (`1` at `n = 0`). -/
noncomputable def smoothPart (t n : ℕ) : ℕ :=
  (n.factorization.filter (· ≤ t)).prod (fun p k => p ^ k)

/-- `∑_{p ≤ t} v_p(n) log p`. -/
noncomputable def logSmooth (t n : ℕ) : ℝ :=
  ∑ p ∈ (Iic t).filter Nat.Prime, ((n.factorization p : ℕ) : ℝ) * Real.log p

/-- `S_t = ∑_{p ≤ t} log p/(p − 1)`. -/
noncomputable def smoothConst (t : ℕ) : ℝ :=
  ∑ p ∈ (Iic t).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)

theorem factorization_smoothPart (t n : ℕ) :
    (smoothPart t n).factorization = n.factorization.filter (· ≤ t) := by
  unfold smoothPart
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  rw [Finsupp.support_filter, Finset.mem_filter] at hp
  exact Nat.prime_of_mem_primeFactors hp.1

theorem smoothPart_ne_zero (t n : ℕ) : smoothPart t n ≠ 0 := by
  unfold smoothPart
  rw [Finsupp.prod]
  refine Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ ?_
  rw [Finsupp.support_filter, Finset.mem_filter] at hp
  exact (Nat.prime_of_mem_primeFactors hp.1).ne_zero

theorem smoothPart_dvd (t : ℕ) {n : ℕ} (hn : n ≠ 0) : smoothPart t n ∣ n := by
  rw [← Nat.factorization_le_iff_dvd (smoothPart_ne_zero t n) hn, factorization_smoothPart]
  intro p
  rw [Finsupp.filter_apply]
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

/-- A `t`-smooth divisor of `n` divides the `t`-smooth part of `n`. -/
theorem dvd_smoothPart (t : ℕ) {n d : ℕ} (hn : n ≠ 0) (hd : d ∣ n)
    (hsm : ∀ p ∈ d.primeFactors, p ≤ t) : d ∣ smoothPart t n := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hn (Nat.eq_zero_of_zero_dvd hd)
  rw [← Nat.factorization_le_iff_dvd hd0 (smoothPart_ne_zero t n), factorization_smoothPart]
  intro p
  rw [Finsupp.filter_apply]
  have hle : d.factorization p ≤ n.factorization p :=
    (Nat.factorization_le_iff_dvd hd0 hn).2 hd p
  split_ifs with hpt
  · exact hle
  · by_contra hne
    have hpos : d.factorization p ≠ 0 := by omega
    have hmem : p ∈ d.primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.2 hpos
    exact hpt (hsm p hmem)

/-- **Localisation.** If `n ≠ 0` has no prime factor in `(t, K]`, the truncation of `σ(n)/n` at
`K` only sees the `t`-smooth part of `n`. -/
theorem abundTrunc_eq_smoothPart (t K : ℕ) {n : ℕ} (hn : n ≠ 0)
    (hgap : ∀ p, p.Prime → p ∣ n → t < p → K < p) :
    abundTrunc K n = abundTrunc K (smoothPart t n) := by
  unfold abundTrunc
  congr 1
  apply Finset.filter_congr
  intro d hd
  rw [Finset.mem_Icc] at hd
  constructor
  · intro hdn
    apply dvd_smoothPart t hn hdn
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hpd' : p ≤ d := Nat.le_of_dvd (by omega) hpd
    by_contra hpt
    push Not at hpt
    have := hgap p hpp (hpd.trans hdn) hpt
    omega
  · intro hda
    exact hda.trans (smoothPart_dvd t hn)

theorem log_smoothPart (t n : ℕ) : Real.log (smoothPart t n) = logSmooth t n := by
  rw [Real.log_nat_eq_sum_factorization, factorization_smoothPart, logSmooth]
  rw [Finsupp.sum_of_support_subset _ (s := (Iic t).filter Nat.Prime)]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter, Finset.mem_Iic] at hp
    rw [Finsupp.filter_apply, if_pos hp.1]
  · intro p hp
    rw [Finsupp.support_filter, Finset.mem_filter] at hp
    exact Finset.mem_filter.2 ⟨Finset.mem_Iic.2 hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
  · intro p _
    simp

theorem logSmooth_nonneg (t n : ℕ) : 0 ≤ logSmooth t n := by
  unfold logSmooth
  refine Finset.sum_nonneg fun p hp => ?_
  have hpp := (Finset.mem_filter.1 hp).2
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le))

theorem logSmooth_mul (t : ℕ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    logSmooth t (m * n) = logSmooth t m + logSmooth t n := by
  unfold logSmooth
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Nat.factorization_mul hm hn, Finsupp.add_apply]
  push_cast
  ring

theorem logSmooth_prime_pow (t : ℕ) {p : ℕ} (hp : p.Prime) (hpt : p ≤ t) (i : ℕ) :
    logSmooth t (p ^ i) = i * Real.log p := by
  unfold logSmooth
  rw [Finset.sum_eq_single p]
  · rw [hp.factorization_pow, Finsupp.single_eq_same]
  · intro q _ hqp
    rw [hp.factorization_pow, Finsupp.single_eq_of_ne hqp]
    simp
  · intro hnot
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_Iic.2 hpt, hp⟩) hnot

/-- **First moment.** `∑_{n ≤ X} logSmooth t n ≤ X S_t`. -/
theorem sum_logSmooth_le (t X : ℕ) :
    ∑ n ∈ Icc 1 X, logSmooth t n ≤ X * smoothConst t := by
  unfold logSmooth smoothConst
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpp := (Finset.mem_filter.1 hp).2
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  rw [← Finset.sum_mul]
  have h := Principia.Common.LucaPomerance.Pollack14.sum_factorization_le X p hpp
  calc (∑ n ∈ Icc 1 X, ((n.factorization p : ℕ) : ℝ)) * Real.log p
      ≤ ((X : ℝ) / ((p : ℝ) - 1)) * Real.log p := mul_le_mul_of_nonneg_right h hlogp
    _ = X * (Real.log p / ((p : ℝ) - 1)) := by ring

/-- `v_p(n) = #{1 ≤ i ≤ X : p^i ∣ n}` for `1 ≤ n ≤ X`. -/
theorem factorization_eq_sum_indicator {p n X : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hnX : n ≤ X) :
    ((n.factorization p : ℕ) : ℝ) = ∑ i ∈ Icc 1 X, if p ^ i ∣ n then (1 : ℝ) else 0 := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hlt : n.factorization p < n := Nat.factorization_lt p (by omega)
  have hset : (Icc 1 X).filter (fun i => p ^ i ∣ n) = Icc 1 (n.factorization p) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [hp.pow_dvd_iff_le_factorization (by omega)]
    omega
  rw [hset, Nat.card_Icc, Nat.add_sub_cancel]

/-- Summing over the multiples of `q` in `[1, X]`. -/
theorem sum_filter_dvd_eq (q X : ℕ) (hq : 0 < q) (f : ℕ → ℝ) :
    ∑ n ∈ (Icc 1 X).filter (q ∣ ·), f n = ∑ m ∈ Icc 1 (X / q), f (q * m) := by
  refine Finset.sum_nbij' (fun n => n / q) (fun m => q * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_Icc]
    obtain ⟨⟨h1, h2⟩, h3⟩ := hn
    exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) h3) hq, Nat.div_le_div_right h2⟩
  · intro m hm
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, Dvd.intro m rfl⟩
    · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    · have := (Nat.le_div_iff_mul_le hq).1 hm.2
      linarith [mul_comm m q]
  · intro n hn
    rw [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m _
    exact Nat.mul_div_cancel_left m hq
  · intro n hn
    rw [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]

/-- `∑_{1 ≤ i ≤ N} r^i ≤ r/(1 − r)`. -/
theorem sum_Icc_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ i ∈ Icc 1 N, r ^ i ≤ r / (1 - r) := by
  have h : Icc 1 N = Ico 1 (N + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [h]
  simpa using geom_sum_Ico_le_of_lt_one (m := 1) (n := N + 1) hr0 hr1

/-- `∑_{1 ≤ i ≤ N} i r^i ≤ r/(1 − r)²`. -/
theorem sum_Icc_mul_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ i ∈ Icc 1 N, (i : ℝ) * r ^ i ≤ r / (1 - r) ^ 2 := by
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
  exact sum_le_hasSum _ (fun i _ => mul_nonneg (Nat.cast_nonneg i) (pow_nonneg hr0 i))
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm)

/-- The inner estimate: `∑_{n ≤ X} v_p(n) logSmooth t n ≤ X (log p · p/(p−1)² + S_t/(p−1))`. -/
theorem sum_factorization_mul_logSmooth_le (t X : ℕ) {p : ℕ} (hp : p.Prime) (hpt : p ≤ t) :
    ∑ n ∈ Icc 1 X, ((n.factorization p : ℕ) : ℝ) * logSmooth t n ≤
      X * (Real.log p * ((p : ℝ) / ((p : ℝ) - 1) ^ 2) + smoothConst t / ((p : ℝ) - 1)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hS : 0 ≤ smoothConst t := by
    unfold smoothConst
    refine Finset.sum_nonneg fun q hq => ?_
    have hqq := (Finset.mem_filter.1 hq).2
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hqq.two_le
    exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  -- expand `v_p(n)` as a sum of indicators and swap
  have hexp : ∑ n ∈ Icc 1 X, ((n.factorization p : ℕ) : ℝ) * logSmooth t n =
      ∑ i ∈ Icc 1 X, ∑ n ∈ (Icc 1 X).filter (p ^ i ∣ ·), logSmooth t n := by
    calc ∑ n ∈ Icc 1 X, ((n.factorization p : ℕ) : ℝ) * logSmooth t n
        = ∑ n ∈ Icc 1 X, ∑ i ∈ Icc 1 X, (if p ^ i ∣ n then logSmooth t n else 0) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [Finset.mem_Icc] at hn
          rw [factorization_eq_sum_indicator hp hn.1 hn.2, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs <;> simp
      _ = ∑ i ∈ Icc 1 X, ∑ n ∈ Icc 1 X, (if p ^ i ∣ n then logSmooth t n else 0) :=
          Finset.sum_comm
      _ = ∑ i ∈ Icc 1 X, ∑ n ∈ (Icc 1 X).filter (p ^ i ∣ ·), logSmooth t n := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_filter]
  rw [hexp]
  -- each inner sum
  have hinner : ∀ i ∈ Icc 1 X, ∑ n ∈ (Icc 1 X).filter (p ^ i ∣ ·), logSmooth t n ≤
      (X : ℝ) * ((1 / (p : ℝ)) ^ i) * (i * Real.log p + smoothConst t) := by
    intro i _
    have hpi : 0 < p ^ i := Nat.pow_pos hp.pos
    rw [sum_filter_dvd_eq (p ^ i) X hpi]
    have hrw : ∀ m ∈ Icc 1 (X / p ^ i),
        logSmooth t (p ^ i * m) = i * Real.log p + logSmooth t m := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      rw [logSmooth_mul t hpi.ne' (by omega), logSmooth_prime_pow t hp hpt]
    rw [Finset.sum_congr rfl hrw, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul]
    have h1 := sum_logSmooth_le t (X / p ^ i)
    have hdiv : ((X / p ^ i : ℕ) : ℝ) ≤ (X : ℝ) * ((1 / (p : ℝ)) ^ i) := by
      have := Nat.cast_div_le (α := ℝ) (m := X) (n := p ^ i)
      rw [Nat.cast_pow] at this
      calc ((X / p ^ i : ℕ) : ℝ) ≤ (X : ℝ) / (p : ℝ) ^ i := this
        _ = (X : ℝ) * ((1 / (p : ℝ)) ^ i) := by rw [one_div_pow, div_eq_mul_one_div]
    have hil : 0 ≤ (i : ℝ) * Real.log p := mul_nonneg (Nat.cast_nonneg i) hlogp
    have h2 := mul_le_mul_of_nonneg_right hdiv hil
    have h3 := mul_le_mul_of_nonneg_right hdiv hS
    nlinarith
  calc ∑ i ∈ Icc 1 X, ∑ n ∈ (Icc 1 X).filter (p ^ i ∣ ·), logSmooth t n
      ≤ ∑ i ∈ Icc 1 X, (X : ℝ) * ((1 / (p : ℝ)) ^ i) * (i * Real.log p + smoothConst t) :=
        Finset.sum_le_sum hinner
    _ = X * (Real.log p * ∑ i ∈ Icc 1 X, (i : ℝ) * (1 / (p : ℝ)) ^ i +
          smoothConst t * ∑ i ∈ Icc 1 X, (1 / (p : ℝ)) ^ i) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ X * (Real.log p * ((p : ℝ) / ((p : ℝ) - 1) ^ 2) + smoothConst t / ((p : ℝ) - 1)) := by
        have hr0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
        have hr1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
        have e1 : (1 / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2 = (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
          field_simp
        have e2 : (1 / (p : ℝ)) / (1 - 1 / (p : ℝ)) = 1 / ((p : ℝ) - 1) := by
          field_simp
        have g1 := sum_Icc_mul_pow_le hr0 hr1 X
        have g2 := sum_Icc_pow_le hr0 hr1 X
        rw [e1] at g1
        rw [e2] at g2
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg X)
        have k1 := mul_le_mul_of_nonneg_left g1 hlogp
        have k2 := mul_le_mul_of_nonneg_left g2 hS
        have e3 : smoothConst t * (1 / ((p : ℝ) - 1)) = smoothConst t / ((p : ℝ) - 1) := by ring
        linarith

/-- **Second moment.** `∑_{n ≤ X} (logSmooth t n)² ≤ X (S_t² + 2 S_t log t)`. -/
theorem sum_logSmooth_sq_le (t X : ℕ) :
    ∑ n ∈ Icc 1 X, (logSmooth t n) ^ 2 ≤
      X * (smoothConst t ^ 2 + 2 * smoothConst t * Real.log t) := by
  have hsq : ∀ n, (logSmooth t n) ^ 2 =
      ∑ p ∈ (Iic t).filter Nat.Prime,
        Real.log p * (((n.factorization p : ℕ) : ℝ) * logSmooth t n) := by
    intro n
    unfold logSmooth
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [Finset.sum_congr rfl fun n _ => hsq n, Finset.sum_comm]
  have hbound : ∀ p ∈ (Iic t).filter Nat.Prime,
      Real.log p * ∑ n ∈ Icc 1 X, ((n.factorization p : ℕ) : ℝ) * logSmooth t n ≤
        X * (2 * Real.log t * (Real.log p / ((p : ℝ) - 1)) +
          smoothConst t * (Real.log p / ((p : ℝ) - 1))) := by
    intro p hp
    obtain ⟨hpt, hpp⟩ := Finset.mem_filter.1 hp
    rw [Finset.mem_Iic] at hpt
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hlogpt : Real.log p ≤ Real.log t :=
      Real.log_le_log (by linarith) (by exact_mod_cast hpt)
    have h := sum_factorization_mul_logSmooth_le t X hpp hpt
    have h' := mul_le_mul_of_nonneg_left h hlogp
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    -- `log p · log p · p/(p−1)² ≤ 2 log t · log p/(p−1)`
    have key : Real.log p * (Real.log p * ((p : ℝ) / ((p : ℝ) - 1) ^ 2)) ≤
        2 * Real.log t * (Real.log p / ((p : ℝ) - 1)) := by
      have hfrac : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
        rw [div_le_iff₀ hp1]
        linarith
      have e : Real.log p * (Real.log p * ((p : ℝ) / ((p : ℝ) - 1) ^ 2)) =
          (Real.log p * ((p : ℝ) / ((p : ℝ) - 1))) * (Real.log p / ((p : ℝ) - 1)) := by
        field_simp
      rw [e]
      have hq : 0 ≤ Real.log p / ((p : ℝ) - 1) := div_nonneg hlogp hp1.le
      apply mul_le_mul_of_nonneg_right _ hq
      calc Real.log p * ((p : ℝ) / ((p : ℝ) - 1)) ≤ Real.log t * 2 :=
            mul_le_mul hlogpt hfrac (div_nonneg (by linarith) hp1.le)
              (le_trans hlogp hlogpt)
        _ = 2 * Real.log t := by ring
    have e2 : Real.log p * (smoothConst t / ((p : ℝ) - 1)) =
        smoothConst t * (Real.log p / ((p : ℝ) - 1)) := by ring
    have hX : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    calc Real.log p * ∑ n ∈ Icc 1 X, ((n.factorization p : ℕ) : ℝ) * logSmooth t n
        ≤ Real.log p * (X * (Real.log p * ((p : ℝ) / ((p : ℝ) - 1) ^ 2) +
            smoothConst t / ((p : ℝ) - 1))) := h'
      _ = X * (Real.log p * (Real.log p * ((p : ℝ) / ((p : ℝ) - 1) ^ 2)) +
            Real.log p * (smoothConst t / ((p : ℝ) - 1))) := by ring
      _ ≤ X * (2 * Real.log t * (Real.log p / ((p : ℝ) - 1)) +
            smoothConst t * (Real.log p / ((p : ℝ) - 1))) := by
          rw [e2]
          exact mul_le_mul_of_nonneg_left (by linarith) hX
  calc ∑ p ∈ (Iic t).filter Nat.Prime, ∑ n ∈ Icc 1 X,
        Real.log p * (((n.factorization p : ℕ) : ℝ) * logSmooth t n)
      = ∑ p ∈ (Iic t).filter Nat.Prime,
          Real.log p * ∑ n ∈ Icc 1 X, ((n.factorization p : ℕ) : ℝ) * logSmooth t n := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ (Iic t).filter Nat.Prime, X * (2 * Real.log t * (Real.log p / ((p : ℝ) - 1)) +
          smoothConst t * (Real.log p / ((p : ℝ) - 1))) := Finset.sum_le_sum hbound
    _ = X * (smoothConst t ^ 2 + 2 * smoothConst t * Real.log t) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        unfold smoothConst
        ring

/-- The constant `C_B = C_M² + 2 C_M` of the smooth-part tail. -/
noncomputable def tailConst : ℝ :=
  Principia.Common.LucaPomerance.Pollack14.mertensConst ^ 2 +
    2 * Principia.Common.LucaPomerance.Pollack14.mertensConst

theorem tailConst_pos : 0 < tailConst := by
  have := Principia.Common.LucaPomerance.Pollack14.mertensConst_pos
  unfold tailConst
  positivity

/-- `S_t ≤ C_M log t` for `t ≥ 2` (Mertens' first theorem). -/
theorem smoothConst_le (t : ℕ) (ht : 2 ≤ t) :
    smoothConst t ≤ Principia.Common.LucaPomerance.Pollack14.mertensConst * Real.log t := by
  have h := Principia.Common.LucaPomerance.Pollack14.sum_log_div_pred_le (t : ℝ)
    (by exact_mod_cast ht)
  rw [Nat.floor_natCast] at h
  exact h

theorem smoothConst_nonneg (t : ℕ) : 0 ≤ smoothConst t := by
  unfold smoothConst
  refine Finset.sum_nonneg fun q hq => ?_
  have hqq := (Finset.mem_filter.1 hq).2
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hqq.two_le
  exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)

/-- **Smooth-part tail.** `#{1 ≤ n ≤ X : logSmooth t n > u log t} ≤ C_B X/u²` for `t ≥ 2`,
`u > 0`. -/
theorem card_logSmooth_gt_le (t X : ℕ) (ht : 2 ≤ t) {u : ℝ} (hu : 0 < u) :
    (((Icc 1 X).filter (fun n => u * Real.log t < logSmooth t n)).card : ℝ) ≤
      tailConst * X / u ^ 2 := by
  have hlogt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  have hc : 0 < u * Real.log t := mul_pos hu hlogt
  have hS0 := smoothConst_nonneg t
  have hS := smoothConst_le t ht
  have hCM := Principia.Common.LucaPomerance.Pollack14.mertensConst_pos
  -- Chebyshev
  have hcheb : (((Icc 1 X).filter (fun n => u * Real.log t < logSmooth t n)).card : ℝ) *
      (u * Real.log t) ^ 2 ≤ ∑ n ∈ Icc 1 X, (logSmooth t n) ^ 2 := by
    calc (((Icc 1 X).filter (fun n => u * Real.log t < logSmooth t n)).card : ℝ) *
          (u * Real.log t) ^ 2
        = ∑ _n ∈ (Icc 1 X).filter (fun n => u * Real.log t < logSmooth t n),
            (u * Real.log t) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ (Icc 1 X).filter (fun n => u * Real.log t < logSmooth t n),
            (logSmooth t n) ^ 2 := by
          refine Finset.sum_le_sum fun n hn => ?_
          have := (Finset.mem_filter.1 hn).2
          exact pow_le_pow_left₀ hc.le this.le 2
      _ ≤ ∑ n ∈ Icc 1 X, (logSmooth t n) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun n _ _ => sq_nonneg _)
  have h2 := sum_logSmooth_sq_le t X
  have h3 : smoothConst t ^ 2 + 2 * smoothConst t * Real.log t ≤ tailConst * Real.log t ^ 2 := by
    unfold tailConst
    have a1 : smoothConst t ^ 2 ≤
        (Principia.Common.LucaPomerance.Pollack14.mertensConst * Real.log t) ^ 2 :=
      pow_le_pow_left₀ hS0 hS 2
    have a2 : 2 * smoothConst t * Real.log t ≤
        2 * (Principia.Common.LucaPomerance.Pollack14.mertensConst * Real.log t) * Real.log t := by
      have := mul_le_mul_of_nonneg_right hS hlogt.le
      linarith
    nlinarith
  have hX : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have h4 : (((Icc 1 X).filter (fun n => u * Real.log t < logSmooth t n)).card : ℝ) *
      (u * Real.log t) ^ 2 ≤ tailConst * X / u ^ 2 * (u * Real.log t) ^ 2 := by
    have e : tailConst * X / u ^ 2 * (u * Real.log t) ^ 2 = X * (tailConst * Real.log t ^ 2) := by
      field_simp
    rw [e]
    calc _ ≤ _ := hcheb
      _ ≤ _ := h2
      _ ≤ X * (tailConst * Real.log t ^ 2) := mul_le_mul_of_nonneg_left h3 hX
  exact le_of_mul_le_mul_right h4 (by positivity)

/-- The tail in terms of the integer: `#{n ≤ X : t^u < smoothPart t n} ≤ C_B X / u²`. -/
theorem card_smoothPart_gt_le (t X u : ℕ) (ht : 2 ≤ t) (hu : 0 < u) :
    (((Icc 1 X).filter (fun n => t ^ u < smoothPart t n)).card : ℝ) ≤
      tailConst * X / (u : ℝ) ^ 2 := by
  have hsub : (Icc 1 X).filter (fun n => t ^ u < smoothPart t n) ⊆
      (Icc 1 X).filter (fun n => (u : ℝ) * Real.log t < logSmooth t n) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨hn.1, ?_⟩
    rw [← log_smoothPart]
    have hlt : ((t ^ u : ℕ) : ℝ) < (smoothPart t n : ℝ) := by exact_mod_cast hn.2
    have hpos : (0 : ℝ) < ((t ^ u : ℕ) : ℝ) := by
      have : 0 < t ^ u := Nat.pow_pos (by omega)
      exact_mod_cast this
    have := Real.log_lt_log hpos hlt
    rwa [Nat.cast_pow, Real.log_pow] at this
  calc (((Icc 1 X).filter (fun n => t ^ u < smoothPart t n)).card : ℝ)
      ≤ (((Icc 1 X).filter (fun n => (u : ℝ) * Real.log t < logSmooth t n)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ tailConst * X / (u : ℝ) ^ 2 := card_logSmooth_gt_le t X ht (by exact_mod_cast hu)

end Principia.Common.Davenport.Singular
