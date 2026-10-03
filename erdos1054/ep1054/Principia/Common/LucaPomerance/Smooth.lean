/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Mertens.Mertens
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

/-!
# A crude upper bound for `y`-smooth numbers

`Ψ(N, y) ≤ √N + 2 N (∑_{p ≤ y} log p/(p−1)) / log N ≤ √N + 2 C_M N log y / log N`
(`card_smooth_le`, `card_smooth_le_mertens`). At `y = N^{1/u}` this is `√N + 2 C_M N / u`: enough
for every "almost all `n` have a large prime factor" argument that tolerates a fixed `u`.

**Proof.** For `y`-smooth `n`, `log n = ∑_{p ≤ y} v_p(n) log p`, so
`∑_{n ≤ N smooth} log n ≤ ∑_{p ≤ y} log p ∑_{n ≤ N} v_p(n) = ∑_{p ≤ y} log p · v_p(N!)
  ≤ N ∑_{p ≤ y} log p/(p − 1)` (Legendre, `Nat.factorization_factorial_le_div_pred`); and
every smooth `n > √N` has `log n > log N / 2`. Mertens' first theorem
(`Mertens.sum_log_prime_div_eq_log`) bounds the prime sum by `C_M log y`.
-/

namespace Principia.Common.LucaPomerance.Pollack14

open Finset

/-- The constant of Mertens' first theorem in the form `∑_{p ≤ y} log p/(p − 1) ≤ C_M log y`. -/
noncomputable def mertensConst : ℝ := 2 + 2 * ((Real.log 4 + 4) / Real.log 2)

theorem mertensConst_pos : 0 < mertensConst := by
  unfold mertensConst
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  positivity

theorem filter_prime_Iic_eq_Ioc' (n : ℕ) :
    (Finset.Iic n).filter Nat.Prime = (Finset.Ioc 0 n).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h2.pos, h1⟩, h2⟩
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨h1, h2⟩

/-- **Mertens' first theorem**: `∑_{p ≤ y} log p/(p − 1) ≤ C_M log y` for `y ≥ 2`. -/
theorem sum_log_div_pred_le (y : ℝ) (hy : 2 ≤ y) :
    ∑ p ∈ (Finset.Iic ⌊y⌋₊).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) ≤
      mertensConst * Real.log y := by
  unfold mertensConst
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hly : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hl4 : 0 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    linarith
  have hM := Mertens.sum_log_prime_div_eq_log (show (1 : ℝ) ≤ y by linarith)
  have hMu := (abs_le.mp hM).2
  rw [filter_prime_Iic_eq_Ioc']
  have hterm : ∀ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime,
      Real.log p / ((p : ℝ) - 1) ≤ 2 * (Real.log p / p) := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    calc Real.log p / ((p : ℝ) - 1) ≤ Real.log p / ((p : ℝ) / 2) :=
          div_le_div_of_nonneg_left hlogp (by linarith) (by linarith)
      _ = 2 * (Real.log p / p) := by ring
  have hkey : Real.log 4 + 4 ≤ ((Real.log 4 + 4) / Real.log 2) * Real.log y := by
    calc Real.log 4 + 4 = ((Real.log 4 + 4) / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ ((Real.log 4 + 4) / Real.log 2) * Real.log y :=
          mul_le_mul_of_nonneg_left hly (div_nonneg hl4 hl2.le)
  calc ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)
      ≤ ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, 2 * (Real.log p / p) :=
        Finset.sum_le_sum hterm
    _ = 2 * ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, Real.log p / p := by
        rw [Finset.mul_sum]
    _ ≤ (2 + 2 * ((Real.log 4 + 4) / Real.log 2)) * Real.log y := by
        nlinarith [hMu, hkey]

/-- `∑_{n ≤ N} v_p(n) = v_p(N!) ≤ N/(p − 1)`. -/
theorem sum_factorization_le (N p : ℕ) (hp : p.Prime) :
    ∑ n ∈ Icc 1 N, ((n.factorization p : ℕ) : ℝ) ≤ (N : ℝ) / ((p : ℝ) - 1) := by
  have hIcc : Icc 1 N = Ico 1 (N + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hfac : (N.factorial).factorization p = ∑ n ∈ Icc 1 N, n.factorization p := by
    rw [← Finset.prod_Ico_id_eq_factorial, ← hIcc,
      Nat.factorization_prod (fun x hx => by have := (Finset.mem_Icc.1 hx).1; omega)]
    simp [Finset.sum_apply]
  have hle := Nat.factorization_factorial_le_div_pred hp N
  have hp1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hcast : (((N / (p - 1) : ℕ)) : ℝ) ≤ (N : ℝ) / ((p : ℝ) - 1) := by
    have h := Nat.cast_div_le (α := ℝ) (m := N) (n := p - 1)
    rwa [Nat.cast_sub hp.one_lt.le, Nat.cast_one] at h
  calc ∑ n ∈ Icc 1 N, ((n.factorization p : ℕ) : ℝ)
      = (((N.factorial).factorization p : ℕ) : ℝ) := by rw [hfac, Nat.cast_sum]
    _ ≤ (((N / (p - 1) : ℕ)) : ℝ) := by exact_mod_cast hle
    _ ≤ (N : ℝ) / ((p : ℝ) - 1) := hcast

/-- `∑_{n ≤ N, n y-smooth} log n ≤ N ∑_{p ≤ y} log p/(p − 1)`. -/
theorem sum_log_smooth_le (N : ℕ) (y : ℝ) :
    ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y), Real.log n ≤
      N * ∑ p ∈ (Iic ⌊y⌋₊).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) := by
  set P := (Iic ⌊y⌋₊).filter Nat.Prime with hP
  set S := (Icc 1 N).filter (fun n : ℕ => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y) with hS
  have hlog : ∀ n ∈ S, Real.log n = ∑ p ∈ P, ((n.factorization p : ℕ) : ℝ) * Real.log p := by
    intro n hn
    obtain ⟨_, hsm⟩ := Finset.mem_filter.1 hn
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    apply Finset.sum_subset
    · intro p hp
      refine Finset.mem_filter.2 ⟨Finset.mem_Iic.2 (Nat.le_floor (hsm p hp)),
        Nat.prime_of_mem_primeFactors hp⟩
    · intro p _ hpn
      have : n.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact hpn
      rw [this, Nat.cast_zero, zero_mul]
  have hSsub : S ⊆ Icc 1 N := Finset.filter_subset _ _
  calc ∑ n ∈ S, Real.log n
      = ∑ n ∈ S, ∑ p ∈ P, ((n.factorization p : ℕ) : ℝ) * Real.log p :=
        Finset.sum_congr rfl hlog
    _ = ∑ p ∈ P, Real.log p * ∑ n ∈ S, ((n.factorization p : ℕ) : ℝ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        ring
    _ ≤ ∑ p ∈ P, Real.log p * ((N : ℝ) / ((p : ℝ) - 1)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpp := (Finset.mem_filter.1 hp).2
        have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
        apply mul_le_mul_of_nonneg_left _ hlogp
        calc ∑ n ∈ S, ((n.factorization p : ℕ) : ℝ)
            ≤ ∑ n ∈ Icc 1 N, ((n.factorization p : ℕ) : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun _ _ _ => Nat.cast_nonneg _)
          _ ≤ (N : ℝ) / ((p : ℝ) - 1) := sum_factorization_le N p hpp
    _ = N * ∑ p ∈ P, Real.log p / ((p : ℝ) - 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring

/-- **`Ψ(N, y) ≤ √N + 2 N (∑_{p ≤ y} log p/(p − 1)) / log N`** for `N ≥ 2`. -/
theorem card_smooth_le (N : ℕ) (hN : 2 ≤ N) (y : ℝ) :
    (((Icc 1 N).filter (fun n : ℕ => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ) ≤
      Real.sqrt N +
        2 * N * (∑ p ∈ (Iic ⌊y⌋₊).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)) / Real.log N := by
  set M := ∑ p ∈ (Iic ⌊y⌋₊).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) with hM
  set S := (Icc 1 N).filter (fun n : ℕ => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y) with hS
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hsq0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  -- pointwise: `log N / 2 ≤ log n + [n ≤ √N] log N / 2`
  have hpt : ∀ n ∈ S, Real.log N / 2 ≤
      Real.log n + (if (n : ℝ) ≤ Real.sqrt N then Real.log N / 2 else 0) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    split_ifs with h
    · linarith
    · push Not at h
      have h1 : Real.log (Real.sqrt N) < Real.log n :=
        Real.log_lt_log (Real.sqrt_pos.2 (by linarith)) h
      rw [Real.log_sqrt (by linarith)] at h1
      linarith
  have hsmall : ((S.filter (fun n : ℕ => (n : ℝ) ≤ Real.sqrt N)).card : ℝ) ≤ Real.sqrt N := by
    have hsub : S.filter (fun n : ℕ => (n : ℝ) ≤ Real.sqrt N) ⊆ Icc 1 ⌊Real.sqrt N⌋₊ := by
      intro n hn
      obtain ⟨hnS, hnq⟩ := Finset.mem_filter.1 hn
      have hn1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 hnS).1).1
      exact Finset.mem_Icc.2 ⟨hn1, Nat.le_floor hnq⟩
    have h1 := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
    calc ((S.filter (fun n : ℕ => (n : ℝ) ≤ Real.sqrt N)).card : ℝ) ≤ (⌊Real.sqrt N⌋₊ : ℝ) := by
          exact_mod_cast h1
      _ ≤ Real.sqrt N := Nat.floor_le hsq0
  have hsum : (S.card : ℝ) * (Real.log N / 2) ≤ N * M + Real.log N / 2 * Real.sqrt N := by
    calc (S.card : ℝ) * (Real.log N / 2) = ∑ n ∈ S, Real.log N / 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ S, (Real.log n + (if (n : ℝ) ≤ Real.sqrt N then Real.log N / 2 else 0)) :=
          Finset.sum_le_sum hpt
      _ = ∑ n ∈ S, Real.log n + Real.log N / 2 *
            ((S.filter (fun n : ℕ => (n : ℝ) ≤ Real.sqrt N)).card : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
            mul_comm]
      _ ≤ N * M + Real.log N / 2 * Real.sqrt N := by
          have h1 := sum_log_smooth_le N y
          have h2 := mul_le_mul_of_nonneg_left hsmall (by linarith : (0 : ℝ) ≤ Real.log N / 2)
          linarith
  have hfinal : (S.card : ℝ) ≤ Real.sqrt N + 2 * N * M / Real.log N := by
    rw [show Real.sqrt N + 2 * N * M / Real.log N =
        (N * M + Real.log N / 2 * Real.sqrt N) / (Real.log N / 2) by field_simp; ring]
    rw [le_div_iff₀ (by linarith)]
    exact hsum
  exact hfinal

/-- `Ψ(N, y) ≤ √N + 2 C_M N log y / log N` for `N ≥ 2`, `y ≥ 2`. -/
theorem card_smooth_le_mertens (N : ℕ) (hN : 2 ≤ N) (y : ℝ) (hy : 2 ≤ y) :
    (((Icc 1 N).filter (fun n : ℕ => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ) ≤
      Real.sqrt N + 2 * N * (mertensConst * Real.log y) / Real.log N := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  refine (card_smooth_le N hN y).trans ?_
  have hM := sum_log_div_pred_le y hy
  have : 2 * (N : ℝ) * (∑ p ∈ (Iic ⌊y⌋₊).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)) ≤
      2 * N * (mertensConst * Real.log y) :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have := div_le_div_of_nonneg_right this hlogN.le
  linarith

end Principia.Common.LucaPomerance.Pollack14
