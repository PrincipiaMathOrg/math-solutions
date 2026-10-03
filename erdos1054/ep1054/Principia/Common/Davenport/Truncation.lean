/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false

/-!
# Davenport's theorem, part 1: periodic truncations of `σ(n)/n`

`abund n = σ(n)/n = ∑_{d ∣ n} 1/d` (junk value `0` at `n = 0`). Its truncation

  `abundTrunc K n = ∑_{1 ≤ d ≤ K, d ∣ n} 1/d`

depends on `n` only through `n mod L` for any `L` divisible by `1, …, K` (e.g. `K!`), so its level
sets are periodic and have a natural density. The error `abund n − abundTrunc K n` is
`∑_{d ∣ n, d > K} 1/d ≥ 0`, and its sum over `1 ≤ n ≤ X` is at most `X · 2/(K+1)`
(`∑_{d > K} ⌊X/d⌋/d ≤ X ∑_{d > K} 1/d²`). By Markov's inequality the `n ≤ X` with error `> ε`
number at most `2X / ((K+1) ε)` (`card_tail_gt_le`). At `K = 0` the truncation vanishes and the
same bound reads `#{n ≤ X : σ(n)/n > ε} ≤ 2X/ε` (`card_abund_gt_le`).

Nothing here is specific to any campaign; the Erdős-1054 consumer is
`Principia.Erdos1054.Proofs.InputsDavenport`.
-/

namespace Principia.Common.Davenport

open Finset

/-- The abundancy index `σ(n)/n` (junk value `0` at `n = 0`). -/
noncomputable def abund (n : ℕ) : ℝ := (ArithmeticFunction.sigma 1 n : ℝ) / n

/-- The truncation `∑_{1 ≤ d ≤ K, d ∣ n} 1/d`. At `n = 0` every `d` divides, so this is *not*
`0` there; it is periodic in `n` with any period divisible by `1, …, K`, `n = 0` included. -/
noncomputable def abundTrunc (K n : ℕ) : ℝ := ∑ d ∈ (Icc 1 K).filter (· ∣ n), (1 : ℝ) / d

theorem abund_nonneg (n : ℕ) : 0 ≤ abund n := by
  unfold abund
  positivity

theorem abundTrunc_nonneg (K n : ℕ) : 0 ≤ abundTrunc K n := by
  unfold abundTrunc
  exact Finset.sum_nonneg fun d _ => by positivity

theorem abundTrunc_zero (n : ℕ) : abundTrunc 0 n = 0 := by
  unfold abundTrunc
  rw [Finset.Icc_eq_empty (by norm_num)]
  simp

/-- `σ(n)/n = ∑_{d ∣ n} 1/d`. -/
theorem abund_eq_sum (n : ℕ) (hn : n ≠ 0) : abund n = ∑ d ∈ n.divisors, (1 : ℝ) / d := by
  rw [← Nat.sum_div_divisors n (fun d : ℕ => (1 : ℝ) / (d : ℝ)), abund,
    ArithmeticFunction.sigma_one_apply, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [Nat.cast_div hdn hd0]
  field_simp

/-- `σ(n) ≥ n`, i.e. `σ(n)/n ≥ 1` for `n ≥ 1`. -/
theorem one_le_abund {n : ℕ} (hn : 1 ≤ n) : 1 ≤ abund n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold abund
  rw [le_div_iff₀ hn', one_mul]
  have h : n ≤ ArithmeticFunction.sigma 1 n := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact Finset.single_le_sum (f := fun d : ℕ => d) (fun _ _ => Nat.zero_le _)
      (Nat.mem_divisors_self n (by omega))
  exact_mod_cast h

/-- For `n ≠ 0` the truncation filter is the set of divisors `≤ K`. -/
theorem filter_Icc_dvd_eq (K n : ℕ) (hn : n ≠ 0) :
    (Icc 1 K).filter (· ∣ n) = n.divisors.filter (· ≤ K) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨⟨h3, hn⟩, h2⟩
  · rintro ⟨⟨h3, _⟩, h2⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos h3 (Nat.pos_of_ne_zero hn), h2⟩, h3⟩

/-- The truncation error: `σ(n)/n − ∑_{d ≤ K, d ∣ n} 1/d = ∑_{d ∣ n, d > K} 1/d`. -/
theorem abund_sub_abundTrunc (K n : ℕ) (hn : n ≠ 0) :
    abund n - abundTrunc K n = ∑ d ∈ n.divisors.filter (fun d => ¬ d ≤ K), (1 : ℝ) / d := by
  rw [abund_eq_sum n hn, abundTrunc, filter_Icc_dvd_eq K n hn,
    ← Finset.sum_filter_add_sum_filter_not n.divisors (· ≤ K)]
  ring

theorem abundTrunc_le_abund (K n : ℕ) (hn : n ≠ 0) : abundTrunc K n ≤ abund n := by
  have h := abund_sub_abundTrunc K n hn
  have h0 : 0 ≤ ∑ d ∈ n.divisors.filter (fun d => ¬ d ≤ K), (1 : ℝ) / d :=
    Finset.sum_nonneg fun d _ => by positivity
  linarith

/-- **Periodicity.** If every `1 ≤ d ≤ K` divides `L`, then `abundTrunc K (n + L) = abundTrunc K n`
for every `n` (including `n = 0`). -/
theorem abundTrunc_add_of_dvd (K n L : ℕ) (hL : ∀ d ∈ Icc 1 K, d ∣ L) :
    abundTrunc K (n + L) = abundTrunc K n := by
  unfold abundTrunc
  congr 1
  apply Finset.filter_congr
  intro d hd
  have hdL : L % d = 0 := Nat.mod_eq_zero_of_dvd (hL d hd)
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hdL, add_zero,
    Nat.mod_mod]

/-- The `K!` period: every `1 ≤ d ≤ K` divides `K!`. -/
theorem dvd_factorial_of_mem_Icc (K : ℕ) : ∀ d ∈ Icc 1 K, d ∣ K.factorial := by
  intro d hd
  rw [Finset.mem_Icc] at hd
  exact Nat.dvd_factorial hd.1 hd.2

/-- **The mean of the truncation error.** `∑_{n ≤ X} (σ(n)/n − abundTrunc K n) ≤ X · 2/(K+1)`. -/
theorem sum_tail_le (K X : ℕ) :
    ∑ n ∈ Icc 1 X, (abund n - abundTrunc K n) ≤ X * (2 / (K + 1)) := by
  have h1 : ∑ n ∈ Icc 1 X, (abund n - abundTrunc K n) =
      ∑ n ∈ Icc 1 X, ∑ d ∈ n.divisors.filter (fun d => ¬ d ≤ K), (1 : ℝ) / d :=
    Finset.sum_congr rfl fun n hn => by
      rw [Finset.mem_Icc] at hn
      exact abund_sub_abundTrunc K n (by omega)
  rw [h1, Finset.sum_comm' (t' := (Icc 1 X).filter (fun d => ¬ d ≤ K))
    (s' := fun d => (Icc 1 X).filter (d ∣ ·))]
  · simp only [Finset.sum_const, nsmul_eq_mul]
    have hsub : (Icc 1 X).filter (fun d => ¬ d ≤ K) ⊆ Ioo K (X + 1) := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd
      rw [Finset.mem_Ioo]
      omega
    calc ∑ d ∈ (Icc 1 X).filter (fun d => ¬ d ≤ K),
          ((((Icc 1 X).filter (d ∣ ·)).card : ℕ) : ℝ) * (1 / (d : ℝ))
        ≤ ∑ d ∈ (Icc 1 X).filter (fun d => ¬ d ≤ K), (X : ℝ) * ((d : ℝ) ^ 2)⁻¹ := by
          apply Finset.sum_le_sum
          intro d _
          have hIcc : (Icc 1 X) = Ioc 0 X := by
            ext x
            simp only [Finset.mem_Icc, Finset.mem_Ioc]
            omega
          have hcard : ((Icc 1 X).filter (d ∣ ·)).card = X / d := by
            rw [hIcc]
            exact Nat.Ioc_filter_dvd_card_eq_div X d
          rw [hcard]
          have hle : ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / d := Nat.cast_div_le
          have hd0 : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
          calc ((X / d : ℕ) : ℝ) * (1 / (d : ℝ)) ≤ (X : ℝ) / d * (1 / (d : ℝ)) :=
                mul_le_mul_of_nonneg_right hle hd0
            _ = (X : ℝ) * ((d : ℝ) ^ 2)⁻¹ := by
                rw [div_mul_div_comm, mul_one, ← sq, div_eq_mul_inv]
      _ = (X : ℝ) * ∑ d ∈ (Icc 1 X).filter (fun d => ¬ d ≤ K), ((d : ℝ) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ (X : ℝ) * ∑ d ∈ Ioo K (X + 1), ((d : ℝ) ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg X)
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ (X : ℝ) * (2 / (K + 1)) :=
          mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le K (X + 1)) (Nat.cast_nonneg X)
  · intro n d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, _⟩, h5⟩
      exact ⟨⟨⟨h1, h2⟩, h3⟩, ⟨Nat.pos_of_dvd_of_pos h3 (by omega),
        le_trans (Nat.le_of_dvd (by omega) h3) h2⟩, h5⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, _, h5⟩
      exact ⟨⟨h1, h2⟩, ⟨h3, by omega⟩, h5⟩

/-- **Markov.** `#{1 ≤ n ≤ X : σ(n)/n − abundTrunc K n > ε} ≤ X · (2/(K+1)) / ε`. -/
theorem card_tail_gt_le (K X : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (((Icc 1 X).filter (fun n => ε < abund n - abundTrunc K n)).card : ℝ) ≤
      X * (2 / (K + 1)) / ε := by
  rw [le_div_iff₀ hε]
  calc (((Icc 1 X).filter (fun n => ε < abund n - abundTrunc K n)).card : ℝ) * ε
      = ∑ _n ∈ (Icc 1 X).filter (fun n => ε < abund n - abundTrunc K n), ε := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ (Icc 1 X).filter (fun n => ε < abund n - abundTrunc K n),
          (abund n - abundTrunc K n) :=
        Finset.sum_le_sum fun n hn => (Finset.mem_filter.1 hn).2.le
    _ ≤ ∑ n ∈ Icc 1 X, (abund n - abundTrunc K n) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro n hn _
        rw [Finset.mem_Icc] at hn
        have := abundTrunc_le_abund K n (by omega)
        linarith
    _ ≤ X * (2 / (K + 1)) := sum_tail_le K X

/-- **Markov at `K = 0`.** `#{1 ≤ n ≤ X : σ(n)/n > u} ≤ 2X/u`. -/
theorem card_abund_gt_le (X : ℕ) {u : ℝ} (hu : 0 < u) :
    (((Icc 1 X).filter (fun n => u < abund n)).card : ℝ) ≤ 2 * X / u := by
  have h := card_tail_gt_le 0 X hu
  have hfil : (Icc 1 X).filter (fun n => u < abund n - abundTrunc 0 n) =
      (Icc 1 X).filter (fun n => u < abund n) :=
    Finset.filter_congr fun n _ => by rw [abundTrunc_zero, sub_zero]
  rw [hfil] at h
  calc (((Icc 1 X).filter (fun n => u < abund n)).card : ℝ)
      ≤ X * (2 / ((0 : ℕ) + 1)) / u := h
    _ = 2 * X / u := by push_cast; ring

end Principia.Common.Davenport
