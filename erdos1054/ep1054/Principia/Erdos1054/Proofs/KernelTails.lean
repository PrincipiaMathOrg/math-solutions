/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Common.Mertens.Mertens
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

/-!
# EP1054 `lem:kernel-tails` (paper lines 1896-1977)

Proves the five non-conjunction obligations of `lem:kernel-tails`:

* `leaf_Eq_RankinKernel : Eq_RankinKernel` (`eq:rankin-kernel`, lines 1929-1938). Rankin's trick
  `1_{L > H} ≤ (L/H)^α` (`rankin_term`), the divisor sum of the multiplicative function
  `τ(n) n^{α-1}` as an Euler product over the prime factors of `Λ(y)` (`sum_divisors_tauPow`), the
  finite geometric bound `∑_{a ≤ k} (a+1) x^a ≤ (1-x)^{-2}` (`sum_succ_mul_pow_le`), and
  `primeFactors Λ(y) ⊆ {p ≤ y}` with every Euler factor `≥ 1` (`primeFactors_lcmUpTo_subset`).
* `leaf_UpperTails_Claim_EulerHigherTerms` (lines 1949-1950). `0 ≤ -log(1-x) - x ≤ x²/(1-x)`
  (`neg_log_one_sub_bounds`), `x_p = p^{α-1} ≤ 2^{-3/4}` and `x_p² ≤ p^{-3/2}`; the constant is
  `2 ∑_n n^{-3/2} / (1 - 2^{-3/4})`.
* `link_Eq_SharpPrimeSum : Std_Mertens2 → Eq_SharpPrimeSum` (lines 1940-1948). The partial summation
  is done by hand: primes are grouped into the unit blocks `z - j - 1 < α log p ≤ z - j`
  (`Finset.sum_fiberwise_of_maps_to`), each block's `∑ log p / p` is bounded by Mertens' first
  theorem (`Mertens.sum_log_prime_div_eq_log`, ported from PNT+ and proved) as `1/α + 2B`
  (`block_log_sum_le`), and `e^u - 1 ≤ u · 4 e^z e^{-j}(j+1)/(1+z)` on block `j`
  (`exp_sub_one_le_block`); the block weights `(j+1)e^{-j}` sum to `(1-e^{-1})^{-2}`. This gives
  `∑_{p ≤ y} (p^α - 1)/p ≤ K e^z/(1+z)` (`sum_rpow_sub_one_le`), and `Std_Mertens2` supplies
  `∑_{p ≤ y} 1/p = log log y + O(1)`. Witnesses: `z₀ = 1`, `C = K + |M| + |C₂|/log 2`.
* `link_Eq_FixedKernelTail` (lines 1952-1963): `α = log₃E/log E`; `fixed_core`.
* `link_Eq_MovingKernelTail` (lines 1965-1976): `α = W/J`; `moving_core`.

`Lem_KernelTails` is the conjunction `Eq_FixedKernelTail ∧ Eq_MovingKernelTail` that the spine
assembles with `And.intro` (`Spine.spine_Lem_KernelTails`); it has no `Link_` and no theorem is
stated for it here.
-/

namespace Principia.Erdos1054.Proofs.KernelTails

open Finset Filter
open Principia.Erdos1054 Principia.Erdos1054.UpperTails

theorem sum_succ_mul_pow_mul_sq (x : ℝ) (k : ℕ) :
    (∑ a ∈ range (k + 1), ((a : ℝ) + 1) * x ^ a) * (1 - x) ^ 2 =
      1 - ((k : ℝ) + 2) * x ^ (k + 1) + ((k : ℝ) + 1) * x ^ (k + 2) := by
  induction k with
  | zero => simp; ring
  | succ k ih =>
    rw [sum_range_succ, add_mul, ih]
    push_cast
    ring

theorem sum_succ_mul_pow_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    ∑ a ∈ range (k + 1), ((a : ℝ) + 1) * x ^ a ≤ ((1 - x) ^ 2)⁻¹ := by
  have h1x : 0 < 1 - x := by linarith
  have hpos : 0 < (1 - x) ^ 2 := by positivity
  rw [inv_eq_one_div, le_div_iff₀ hpos, sum_succ_mul_pow_mul_sq]
  have h1 : 0 ≤ x ^ (k + 1) := pow_nonneg hx0 _
  have h2 : x ^ (k + 2) = x * x ^ (k + 1) := by ring
  have h3 : (0 : ℝ) ≤ ((k : ℝ) + 1) * (1 - x) + 1 := by positivity
  rw [h2]
  nlinarith [mul_nonneg h1 h3]

/-- `τ(n) n^β` as a real arithmetic function. -/
noncomputable def tauPow (β : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => (n.divisors.card : ℝ) * (n : ℝ) ^ β, by simp⟩

theorem tauPow_apply (β : ℝ) (n : ℕ) :
    tauPow β n = (n.divisors.card : ℝ) * (n : ℝ) ^ β := rfl

theorem tauPow_isMultiplicative (β : ℝ) : (tauPow β).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [tauPow_apply]
  · intro m n hmn
    rw [tauPow_apply, tauPow_apply, tauPow_apply, Nat.Coprime.card_divisors_mul hmn,
      Nat.cast_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring

theorem tauPow_prime_pow (β : ℝ) {p : ℕ} (hp : p.Prime) (i : ℕ) :
    tauPow β (p ^ i) = ((i : ℝ) + 1) * ((p : ℝ) ^ β) ^ i := by
  rw [tauPow_apply, ← ArithmeticFunction.sigma_zero_apply,
    ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  push_cast
  rw [← Real.rpow_pow_comm (Nat.cast_nonneg p)]

theorem sum_divisors_tauPow (β : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, tauPow β d =
      ∏ p ∈ n.primeFactors, ∑ i ∈ range (n.factorization p + 1), tauPow β (p ^ i) := by
  have hg : (tauPow β * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)).IsMultiplicative :=
    (tauPow_isMultiplicative β).mul ArithmeticFunction.isMultiplicative_zeta.natCast
  rw [← ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.IsMultiplicative.multiplicative_factorization _ hg hn, Finsupp.prod,
    Nat.support_factorization]
  refine prod_congr rfl fun p hp => ?_
  rw [ArithmeticFunction.coe_mul_zeta_apply,
    Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]

theorem lcmUpTo_dvd_factorial (y : ℝ) : lcmUpTo y ∣ (⌊y⌋₊).factorial := by
  unfold lcmUpTo
  refine Finset.lcm_dvd fun b hb => ?_
  rw [Finset.mem_Icc] at hb
  exact Nat.dvd_factorial hb.1 hb.2

theorem lcmUpTo_ne_zero (y : ℝ) : lcmUpTo y ≠ 0 := by
  intro h
  have h' := lcmUpTo_dvd_factorial y
  rw [h] at h'
  exact Nat.factorial_ne_zero _ (Nat.eq_zero_of_zero_dvd h')

theorem primeFactors_lcmUpTo_subset (y : ℝ) : (lcmUpTo y).primeFactors ⊆ primesLE y := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ (⌊y⌋₊).factorial :=
    (Nat.dvd_of_mem_primeFactors hp).trans (lcmUpTo_dvd_factorial y)
  rw [primesLE, Finset.mem_filter, Finset.mem_Iic]
  exact ⟨hpp.dvd_factorial.1 hdvd, hpp⟩

theorem rankin_term {H α : ℝ} (hH : 0 < H) (hα : 0 ≤ α) {L : ℕ} (hL : H < (L : ℝ)) :
    (L.divisors.card : ℝ) / L ≤ H ^ (-α) * tauPow (α - 1) L := by
  have hL0 : (0 : ℝ) < L := hH.trans hL
  rw [tauPow_apply, Real.rpow_sub_one hL0.ne', Real.rpow_neg hH.le]
  have h1 : H ^ α ≤ (L : ℝ) ^ α := Real.rpow_le_rpow hH.le hL.le hα
  have h2 : 0 < H ^ α := Real.rpow_pos_of_pos hH α
  have h3 : (0 : ℝ) ≤ L.divisors.card := Nat.cast_nonneg _
  have heq : (H ^ α)⁻¹ * ((L.divisors.card : ℝ) * ((L : ℝ) ^ α / L)) =
      ((L.divisors.card : ℝ) / L) * ((L : ℝ) ^ α / H ^ α) := by
    field_simp
  rw [heq]
  exact le_mul_of_one_le_right (div_nonneg h3 hL0.le) ((one_le_div h2).mpr h1)

theorem prime_rpow_bounds {α : ℝ} (hα4 : α ≤ 1 / 4) {p : ℕ} (hp : p.Prime) :
    0 ≤ (p : ℝ) ^ (α - 1) ∧ (p : ℝ) ^ (α - 1) < 1 := by
  refine ⟨Real.rpow_nonneg (Nat.cast_nonneg p) _, ?_⟩
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

theorem rankinKernel : Principia.Erdos1054.Eq_RankinKernel := by
  intro y H hy hH α hα hα4
  have hn : lcmUpTo y ≠ 0 := lcmUpTo_ne_zero y
  have hH0 : 0 < H := by linarith
  have hHa : 0 ≤ H ^ (-α) := Real.rpow_nonneg hH0.le _
  have step1 : Skernel y H ≤ H ^ (-α) * ∑ d ∈ (lcmUpTo y).divisors, tauPow (α - 1) d := by
    unfold Skernel
    rw [Finset.mul_sum]
    calc ∑ L ∈ (lcmUpTo y).divisors.filter (fun L : ℕ => H < (L : ℝ)),
          (L.divisors.card : ℝ) / L
        ≤ ∑ L ∈ (lcmUpTo y).divisors.filter (fun L : ℕ => H < (L : ℝ)),
          H ^ (-α) * tauPow (α - 1) L := by
          refine Finset.sum_le_sum fun L hL => ?_
          rw [Finset.mem_filter] at hL
          exact rankin_term hH0 hα.le hL.2
      _ ≤ ∑ L ∈ (lcmUpTo y).divisors, H ^ (-α) * tauPow (α - 1) L := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro L _ _
          rw [tauPow_apply]
          exact mul_nonneg hHa (mul_nonneg (Nat.cast_nonneg _)
            (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have step2 : ∑ d ∈ (lcmUpTo y).divisors, tauPow (α - 1) d ≤
      ∏ p ∈ primesLE y, ((1 - (p : ℝ) ^ (α - 1)) ^ 2)⁻¹ := by
    rw [sum_divisors_tauPow (α - 1) hn]
    calc ∏ p ∈ (lcmUpTo y).primeFactors,
          ∑ i ∈ range ((lcmUpTo y).factorization p + 1), tauPow (α - 1) (p ^ i)
        ≤ ∏ p ∈ (lcmUpTo y).primeFactors, ((1 - (p : ℝ) ^ (α - 1)) ^ 2)⁻¹ := by
          refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
          · refine Finset.sum_nonneg fun i _ => ?_
            rw [tauPow_prime_pow _ (Nat.prime_of_mem_primeFactors hp)]
            have := (prime_rpow_bounds hα4 (Nat.prime_of_mem_primeFactors hp)).1
            positivity
          · have hpp := Nat.prime_of_mem_primeFactors hp
            have hb := prime_rpow_bounds hα4 hpp
            rw [Finset.sum_congr rfl fun i _ => tauPow_prime_pow (α - 1) hpp i]
            exact sum_succ_mul_pow_le _ hb.1 hb.2 _
      _ ≤ ∏ p ∈ primesLE y, ((1 - (p : ℝ) ^ (α - 1)) ^ 2)⁻¹ := by
          refine Finset.prod_le_prod_of_subset_of_one_le (primeFactors_lcmUpTo_subset y)
            (fun p hp => ?_) (fun p hp _ => ?_)
          · have hb := prime_rpow_bounds hα4 (Nat.prime_of_mem_primeFactors hp)
            positivity
          · have hpp : p.Prime := (Finset.mem_filter.1 hp).2
            have hb := prime_rpow_bounds hα4 hpp
            have h1 : 0 < (1 - (p : ℝ) ^ (α - 1)) ^ 2 := by
              have : 0 < 1 - (p : ℝ) ^ (α - 1) := by linarith
              positivity
            rw [one_le_inv₀ h1]
            nlinarith
  exact step1.trans (mul_le_mul_of_nonneg_left step2 hHa)

/-! ## The higher terms of the Euler product -/

theorem neg_log_one_sub_bounds {x : ℝ} (hx1 : x < 1) :
    0 ≤ -Real.log (1 - x) - x ∧ -Real.log (1 - x) - x ≤ x ^ 2 / (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  constructor
  · have := Real.log_le_sub_one_of_pos hpos
    linarith
  · have h := Real.one_sub_inv_le_log_of_pos hpos
    have heq : (1 - x)⁻¹ - 1 - x = x ^ 2 / (1 - x) := by
      field_simp
      ring
    linarith

theorem eulerHigherTerms : Principia.Erdos1054.UpperTails.Claim_EulerHigherTerms := by
  set c : ℝ := (2 : ℝ) ^ (-(3 : ℝ) / 4) with hc
  have hc1 : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hsum : Summable (fun n : ℕ => ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  set T : ℝ := ∑' n : ℕ, ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ with hT
  have hT0 : 0 ≤ T := tsum_nonneg fun n => by positivity
  refine ⟨2 * T / (1 - c), ?_⟩
  intro y α hy hα hα4
  have hterm : ∀ p ∈ primesLE y,
      0 ≤ -Real.log (1 - (p : ℝ) ^ (α - 1)) - (p : ℝ) ^ (α - 1) ∧
      -Real.log (1 - (p : ℝ) ^ (α - 1)) - (p : ℝ) ^ (α - 1) ≤
        ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹ / (1 - c) := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.1 hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hb := prime_rpow_bounds hα4 hpp
    have hxc : (p : ℝ) ^ (α - 1) ≤ c :=
      (Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)).trans
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
    have hsq : ((p : ℝ) ^ (α - 1)) ^ 2 ≤ ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p), ← Real.rpow_neg (Nat.cast_nonneg p)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
    obtain ⟨h0, h1⟩ := neg_log_one_sub_bounds hb.2
    refine ⟨h0, h1.trans ?_⟩
    calc ((p : ℝ) ^ (α - 1)) ^ 2 / (1 - (p : ℝ) ^ (α - 1))
        ≤ ((p : ℝ) ^ (α - 1)) ^ 2 / (1 - c) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)
      _ ≤ ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹ / (1 - c) :=
          div_le_div_of_nonneg_right hsq (by linarith)
  have hlog : Real.log (∏ p ∈ primesLE y, ((1 - (p : ℝ) ^ (α - 1)) ^ 2)⁻¹) -
      2 * ∑ p ∈ primesLE y, (p : ℝ) ^ (α - 1) =
      2 * ∑ p ∈ primesLE y, (-Real.log (1 - (p : ℝ) ^ (α - 1)) - (p : ℝ) ^ (α - 1)) := by
    rw [Real.log_prod (fun p hp => ?_)]
    · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Real.log_inv, Real.log_pow]
      push_cast
      ring
    · have hb := prime_rpow_bounds hα4 (Finset.mem_filter.1 hp).2
      have : 0 < 1 - (p : ℝ) ^ (α - 1) := by linarith
      positivity
  rw [hlog, abs_le]
  have h0 : 0 ≤ ∑ p ∈ primesLE y, (-Real.log (1 - (p : ℝ) ^ (α - 1)) - (p : ℝ) ^ (α - 1)) :=
    Finset.sum_nonneg fun p hp => (hterm p hp).1
  have h1 : ∑ p ∈ primesLE y, (-Real.log (1 - (p : ℝ) ^ (α - 1)) - (p : ℝ) ^ (α - 1)) ≤
      T / (1 - c) := by
    refine (Finset.sum_le_sum fun p hp => (hterm p hp).2).trans ?_
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (hsum.sum_le_tsum _ fun i _ => by positivity)
      (by linarith)
  have h2 : 0 ≤ T / (1 - c) := div_nonneg hT0 (by linarith)
  rw [mul_div_assoc]
  constructor <;> linarith

/-! ## The sharp prime sum -/

/-- The constant of Mertens' first theorem as ported (`Mertens.sum_log_prime_div_eq_log`). -/
noncomputable def Bm : ℝ := Real.log 4 + 4

theorem Bm_nonneg : 0 ≤ Bm := by
  unfold Bm
  have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  linarith

theorem primesLE_eq_Ioc (x : ℝ) : primesLE x = {p ∈ Ioc 0 ⌊x⌋₊ | p.Prime} := by
  ext p
  simp only [primesLE, Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h2.pos, h1⟩, h2⟩
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨h1, h2⟩

/-- Mertens' first theorem over `primesLE`. -/
theorem mertens1 {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ primesLE x, Real.log p / p - Real.log x| ≤ Bm := by
  rw [primesLE_eq_Ioc]
  exact Mertens.sum_log_prime_div_eq_log hx

theorem log_div_nonneg (p : ℕ) : 0 ≤ Real.log p / p :=
  div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

/-- `∑_{a < p ≤ b} log p / p ≤ log (b/a) + 2B`. -/
theorem block_log_sum_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : 1 ≤ b) :
    ∑ p ∈ (primesLE b).filter (fun p : ℕ => a < (p : ℝ)), Real.log p / p ≤
      Real.log b - Real.log a + 2 * Bm := by
  have hB := Bm_nonneg
  have hb' := abs_le.mp (mertens1 hb)
  by_cases ha1 : 1 ≤ a
  · have ha' := abs_le.mp (mertens1 ha1)
    have hsplit := Finset.sum_filter_add_sum_filter_not (primesLE b)
      (fun p : ℕ => a < (p : ℝ)) (fun p => Real.log p / p)
    have hnot : (primesLE b).filter (fun p : ℕ => ¬ a < (p : ℝ)) = primesLE a := by
      ext p
      simp only [primesLE, Finset.mem_filter, Finset.mem_Iic, not_lt]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨Nat.le_floor h3, h2⟩
      · rintro ⟨h1, h2⟩
        have h3 : (p : ℝ) ≤ a := (Nat.le_floor_iff ha.le).mp h1
        exact ⟨⟨Nat.le_floor (h3.trans hab), h2⟩, h3⟩
    rw [hnot] at hsplit
    linarith
  · have ha1' : a < 1 := not_le.mp ha1
    have hla : Real.log a < 0 := Real.log_neg ha ha1'
    have hsub : ∑ p ∈ (primesLE b).filter (fun p : ℕ => a < (p : ℝ)), Real.log p / p ≤
        ∑ p ∈ primesLE b, Real.log p / p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun p _ _ => log_div_nonneg p
    linarith

theorem exp_mul_one_sub_le {u : ℝ} (hu : 0 ≤ u) : Real.exp u * (1 - u) ≤ 1 + u := by
  have h := Real.add_one_le_exp (-u)
  have h2 : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]
    simp
  have h3 : Real.exp u * (1 - u) ≤ Real.exp u * Real.exp (-u) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos u).le
  linarith

/-- Pointwise block bound: for `0 < u` with `z - j - 1 < u ≤ z - j`,
`e^u - 1 ≤ u · 4 e^z e^{-j} (j+1)/(1+z)`. -/
theorem exp_sub_one_le_block {u z : ℝ} {j : ℕ} (hu : 0 < u) (h1 : z - j - 1 < u)
    (h2 : u ≤ z - j) :
    Real.exp u - 1 ≤ u * (4 * Real.exp z * Real.exp (-1) ^ j * ((j : ℝ) + 1) / (1 + z)) := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hz : 0 < 1 + z := by linarith
  have hA : (Real.exp u - 1) * (1 + u) ≤ 2 * u * Real.exp u := by
    nlinarith [exp_mul_one_sub_le hu.le]
  have hB : Real.exp u ≤ Real.exp z * Real.exp (-1) ^ j := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hC : 1 + z ≤ 2 * ((j : ℝ) + 1) * (1 + u) := by
    nlinarith [mul_nonneg hj (show (0 : ℝ) ≤ z - j by linarith),
      mul_le_mul_of_nonneg_left (show z - j ≤ 1 + u by linarith)
        (show (0 : ℝ) ≤ (j : ℝ) + 1 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ (j : ℝ) + 1 by linarith) hu.le]
  have hE : 0 ≤ Real.exp u - 1 := by
    have := Real.add_one_le_exp u
    linarith
  rw [← mul_div_assoc, le_div_iff₀ hz]
  calc (Real.exp u - 1) * (1 + z) ≤ (Real.exp u - 1) * (2 * ((j : ℝ) + 1) * (1 + u)) :=
        mul_le_mul_of_nonneg_left hC hE
    _ = 2 * ((j : ℝ) + 1) * ((Real.exp u - 1) * (1 + u)) := by ring
    _ ≤ 2 * ((j : ℝ) + 1) * (2 * u * Real.exp u) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ ≤ 2 * ((j : ℝ) + 1) * (2 * u * (Real.exp z * Real.exp (-1) ^ j)) := by gcongr
    _ = u * (4 * Real.exp z * Real.exp (-1) ^ j * ((j : ℝ) + 1)) := by ring

/-- The constant of `sum_rpow_sub_one_le`. -/
noncomputable def KS : ℝ := 4 * (1 + Bm / 2) * ((1 - Real.exp (-1)) ^ 2)⁻¹

theorem KS_nonneg : 0 ≤ KS := by
  unfold KS
  have := Bm_nonneg
  positivity

/-- The partial-summation core of `eq:sharp-prime-sum`:
`∑_{p ≤ y} (p^α - 1)/p ≤ K · e^z/(1+z)` with `z = α log y`, uniformly for `0 < α ≤ 1/4`. -/
theorem sum_rpow_sub_one_le {y α : ℝ} (hy : 1 ≤ y) (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    ∑ p ∈ primesLE y, ((p : ℝ) ^ α - 1) / p ≤
      KS * (Real.exp (α * Real.log y) / (1 + α * Real.log y)) := by
  have hB := Bm_nonneg
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  generalize hzdef : α * Real.log y = z
  have hz0 : 0 ≤ z := by rw [← hzdef]; exact mul_nonneg hα.le hlogy
  have hmaps : ∀ p ∈ primesLE y, ⌊z - α * Real.log p⌋₊ ∈ range (⌊z⌋₊ + 1) := by
    intro p hp
    rw [Finset.mem_range]
    have hpp := (Finset.mem_filter.1 hp).2
    have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
    have : z - α * Real.log p ≤ z := by nlinarith
    exact Nat.lt_succ_of_le (Nat.floor_le_floor this)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ j ∈ range (⌊z⌋₊ + 1),
      ∑ p ∈ (primesLE y).filter (fun p : ℕ => ⌊z - α * Real.log p⌋₊ = j),
        ((p : ℝ) ^ α - 1) / p ≤
      (4 * Real.exp z * Real.exp (-1) ^ j * ((j : ℝ) + 1) / (1 + z)) * (1 + Bm / 2) := by
    intro j hj
    have hjz : (j : ℝ) ≤ z := by
      have h1 : j ≤ ⌊z⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.1 hj)
      exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hz0)
    have hcj : 0 ≤ 4 * Real.exp z * Real.exp (-1) ^ j * ((j : ℝ) + 1) / (1 + z) := by
      positivity
    -- the block `(a, b]`
    have hb1 : 1 ≤ Real.exp ((z - j) / α) := Real.one_le_exp (div_nonneg (by linarith) hα.le)
    have hab : Real.exp ((z - j - 1) / α) ≤ Real.exp ((z - j) / α) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hα.le)
    have hsub : (primesLE y).filter (fun p : ℕ => ⌊z - α * Real.log p⌋₊ = j) ⊆
        (primesLE (Real.exp ((z - j) / α))).filter
          (fun p : ℕ => Real.exp ((z - j - 1) / α) < (p : ℝ)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hp1, hgj⟩ := hp
      have hpp := (Finset.mem_filter.1 hp1).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hpy : (p : ℝ) ≤ y :=
        (Nat.le_floor_iff (by linarith)).mp (Finset.mem_Iic.1 (Finset.mem_filter.1 hp1).1)
      have hlpy : Real.log p ≤ Real.log y := Real.log_le_log hp0 hpy
      have hu : α * Real.log p ≤ z := by
        rw [← hzdef]
        exact mul_le_mul_of_nonneg_left hlpy hα.le
      have hfl1 : (j : ℝ) ≤ z - α * Real.log p := by
        rw [← hgj]
        exact Nat.floor_le (by linarith)
      have hfl2 : z - α * Real.log p < (j : ℝ) + 1 := by
        rw [← hgj]
        exact Nat.lt_floor_add_one _
      rw [Finset.mem_filter, primesLE, Finset.mem_filter, Finset.mem_Iic]
      refine ⟨⟨Nat.le_floor ?_, hpp⟩, ?_⟩
      · rw [← Real.exp_log hp0]
        exact Real.exp_le_exp.mpr ((le_div_iff₀ hα).mpr (by linarith))
      · rw [← Real.exp_log hp0]
        exact Real.exp_lt_exp.mpr ((div_lt_iff₀ hα).mpr (by linarith))
    have hpt : ∀ p ∈ (primesLE y).filter (fun p : ℕ => ⌊z - α * Real.log p⌋₊ = j),
        ((p : ℝ) ^ α - 1) / p ≤
          (4 * Real.exp z * Real.exp (-1) ^ j * ((j : ℝ) + 1) / (1 + z)) * α *
            (Real.log p / p) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hp1, hgj⟩ := hp
      have hpp := (Finset.mem_filter.1 hp1).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
      have hpy : (p : ℝ) ≤ y :=
        (Nat.le_floor_iff (by linarith)).mp (Finset.mem_Iic.1 (Finset.mem_filter.1 hp1).1)
      have hlpy : Real.log p ≤ Real.log y := Real.log_le_log hp0 hpy
      have hu : α * Real.log p ≤ z := by
        rw [← hzdef]
        exact mul_le_mul_of_nonneg_left hlpy hα.le
      have hfl1 : (j : ℝ) ≤ z - α * Real.log p := by
        rw [← hgj]
        exact Nat.floor_le (by linarith)
      have hfl2 : z - α * Real.log p < (j : ℝ) + 1 := by
        rw [← hgj]
        exact Nat.lt_floor_add_one _
      have key := exp_sub_one_le_block (mul_pos hα hlp) (j := j) (z := z)
        (by linarith) (by linarith)
      rw [Real.rpow_def_of_pos hp0, mul_comm (Real.log p) α]
      calc (Real.exp (α * Real.log p) - 1) / p
          ≤ (α * Real.log p *
              (4 * Real.exp z * Real.exp (-1) ^ j * ((j : ℝ) + 1) / (1 + z))) / p :=
            div_le_div_of_nonneg_right key hp0.le
        _ = (4 * Real.exp z * Real.exp (-1) ^ j * ((j : ℝ) + 1) / (1 + z)) * α *
            (Real.log p / p) := by ring
    calc ∑ p ∈ (primesLE y).filter (fun p : ℕ => ⌊z - α * Real.log p⌋₊ = j),
          ((p : ℝ) ^ α - 1) / p
        ≤ ∑ p ∈ (primesLE y).filter (fun p : ℕ => ⌊z - α * Real.log p⌋₊ = j),
          (4 * Real.exp z * Real.exp (-1) ^ j * ((j : ℝ) + 1) / (1 + z)) * α *
            (Real.log p / p) := Finset.sum_le_sum hpt
      _ = (4 * Real.exp z * Real.exp (-1) ^ j * ((j : ℝ) + 1) / (1 + z)) * α *
            ∑ p ∈ (primesLE y).filter (fun p : ℕ => ⌊z - α * Real.log p⌋₊ = j),
              Real.log p / p := by rw [Finset.mul_sum]
      _ ≤ (4 * Real.exp z * Real.exp (-1) ^ j * ((j : ℝ) + 1) / (1 + z)) * α *
            ∑ p ∈ (primesLE (Real.exp ((z - j) / α))).filter
              (fun p : ℕ => Real.exp ((z - j - 1) / α) < (p : ℝ)), Real.log p / p :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => log_div_nonneg p)
            (mul_nonneg hcj hα.le)
      _ ≤ (4 * Real.exp z * Real.exp (-1) ^ j * ((j : ℝ) + 1) / (1 + z)) * α *
            (Real.log (Real.exp ((z - j) / α)) - Real.log (Real.exp ((z - j - 1) / α)) +
              2 * Bm) :=
          mul_le_mul_of_nonneg_left (block_log_sum_le (Real.exp_pos _) hab hb1)
            (mul_nonneg hcj hα.le)
      _ = (4 * Real.exp z * Real.exp (-1) ^ j * ((j : ℝ) + 1) / (1 + z)) *
            (1 + 2 * α * Bm) := by
          rw [Real.log_exp, Real.log_exp]
          field_simp
          ring
      _ ≤ (4 * Real.exp z * Real.exp (-1) ^ j * ((j : ℝ) + 1) / (1 + z)) * (1 + Bm / 2) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hcj
  have hx0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hx1 : Real.exp (-1) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  calc ∑ j ∈ range (⌊z⌋₊ + 1),
        ∑ p ∈ (primesLE y).filter (fun p : ℕ => ⌊z - α * Real.log p⌋₊ = j),
          ((p : ℝ) ^ α - 1) / p
      ≤ ∑ j ∈ range (⌊z⌋₊ + 1),
          (4 * Real.exp z * Real.exp (-1) ^ j * ((j : ℝ) + 1) / (1 + z)) * (1 + Bm / 2) :=
        Finset.sum_le_sum hfib
    _ = (4 * (1 + Bm / 2) * (Real.exp z / (1 + z))) *
          ∑ j ∈ range (⌊z⌋₊ + 1), ((j : ℝ) + 1) * Real.exp (-1) ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ (4 * (1 + Bm / 2) * (Real.exp z / (1 + z))) * ((1 - Real.exp (-1)) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (sum_succ_mul_pow_le _ hx0 hx1 _) (by positivity)
    _ = KS * (Real.exp z / (1 + z)) := by
        unfold KS
        ring

theorem sharpPrimeSum : Principia.Erdos1054.Spine.Link_Eq_SharpPrimeSum := by
  intro hM
  obtain ⟨M, C₂, hM⟩ := hM
  refine ⟨KS + (|M| + |C₂| / Real.log 2), 1, ?_⟩
  intro y α hy hα hα4 hz
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogy : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hmert : |∑ p ∈ primesLE y, (1 : ℝ) / p - Real.log (Real.log y) - M| ≤
      C₂ / Real.log y := hM y hy
  have hC : C₂ / Real.log y ≤ |C₂| / Real.log 2 :=
    (div_le_div_of_nonneg_right (le_abs_self C₂) (hl2.le.trans hlogy)).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hl2 hlogy)
  have hdecomp : ∑ p ∈ primesLE y, (p : ℝ) ^ (α - 1) =
      ∑ p ∈ primesLE y, (1 : ℝ) / p + ∑ p ∈ primesLE y, ((p : ℝ) ^ α - 1) / p := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp0 : (p : ℝ) ≠ 0 := by
      have := (Finset.mem_filter.1 hp).2.pos
      positivity
    rw [Real.rpow_sub_one hp0]
    ring
  have hnonneg : 0 ≤ ∑ p ∈ primesLE y, ((p : ℝ) ^ α - 1) / p := by
    refine Finset.sum_nonneg fun p hp => div_nonneg ?_ (Nat.cast_nonneg _)
    have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt.le
    have := Real.one_le_rpow h1 hα.le
    linarith
  have hupper := sum_rpow_sub_one_le (by linarith : (1 : ℝ) ≤ y) hα hα4
  have hKS := KS_nonneg
  rw [hdecomp]
  generalize hzdef : α * Real.log y = z at hz hupper ⊢
  have hz0 : 0 < z := by linarith
  have hez1 : 1 ≤ Real.exp z / z := by
    rw [one_le_div hz0]
    linarith [Real.add_one_le_exp z]
  have hez2 : Real.exp z / (1 + z) ≤ Real.exp z / z :=
    div_le_div_of_nonneg_left (Real.exp_pos z).le hz0 (by linarith)
  have hm := abs_le.mp hmert
  have hD : 0 ≤ |M| + |C₂| / Real.log 2 := by positivity
  have hDle : |M| + |C₂| / Real.log 2 ≤
      (|M| + |C₂| / Real.log 2) * (Real.exp z / z) := le_mul_of_one_le_right hD hez1
  have hKle : KS * (Real.exp z / (1 + z)) ≤ KS * (Real.exp z / z) :=
    mul_le_mul_of_nonneg_left hez2 hKS
  have hKnn : 0 ≤ KS * (Real.exp z / z) := mul_nonneg hKS (by positivity)
  rw [abs_le]
  constructor
  · nlinarith [neg_abs_le M]
  · nlinarith [le_abs_self M]

theorem eulerProd_pos {y α : ℝ} (hα4 : α ≤ 1 / 4) :
    0 < ∏ p ∈ primesLE y, ((1 - (p : ℝ) ^ (α - 1)) ^ 2)⁻¹ := by
  refine Finset.prod_pos fun p hp => ?_
  have hb := prime_rpow_bounds hα4 (Finset.mem_filter.1 hp).2
  have : 0 < 1 - (p : ℝ) ^ (α - 1) := by linarith
  positivity

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

/-! ## `eq:fixed-kernel-tail` -/

theorem fixed_core (hR : Eq_RankinKernel) {CS z₀ CE : ℝ}
    (hS : ∀ y α : ℝ, 2 ≤ y → 0 < α → α ≤ 1 / 4 → z₀ ≤ α * Real.log y →
      |∑ p ∈ primesLE y, (p : ℝ) ^ (α - 1) - Real.log (Real.log y)| ≤
        CS * (Real.exp (α * Real.log y) / (α * Real.log y)))
    (hE : ∀ y α : ℝ, 2 ≤ y → 0 < α → α ≤ 1 / 4 →
      |Real.log (∏ p ∈ primesLE y, ((1 - (p : ℝ) ^ (α - 1)) ^ 2)⁻¹) -
        2 * ∑ p ∈ primesLE y, (p : ℝ) ^ (α - 1)| ≤ CE)
    {E : ℝ} (hE2 : 2 ≤ E) (hL1 : 1 ≤ Real.log E) (hL2 : 1 ≤ Real.log (Real.log E))
    (hL3 : max z₀ 1 ≤ Real.log (Real.log (Real.log E)))
    (hL21 : Real.log (Real.log E) ≤ Real.log E / 4) :
    Skernel E ((Pfix E : ℝ) / E) ≤ Real.exp (-(logIt 2 E / Real.sqrt (logIt 3 E)) +
      (2 * |CS| + |CE| + 1) * (logIt 2 E / logIt 3 E)) := by
  have e1 : logIt 2 E = Real.log (Real.log E) := rfl
  have e2 : logIt 3 E = Real.log (Real.log (Real.log E)) := rfl
  unfold Pfix
  rw [e1, e2]
  have hE0 : 0 < E := by linarith
  have hE1 : 1 ≤ E := by linarith
  generalize hl1 : Real.log E = L1 at *
  generalize hl2 : Real.log L1 = L2 at *
  generalize hl3 : Real.log L2 = L3 at *
  have hL1p : 0 < L1 := by linarith
  have hL2p : 0 < L2 := by linarith
  have hL3p : 0 < L3 := by linarith [le_max_right z₀ 1]
  have hL3z : z₀ ≤ L3 := (le_max_left z₀ 1).trans hL3
  have hL32 : L3 ≤ L2 := by
    rw [← hl3]
    linarith [Real.log_le_sub_one_of_pos hL2p]
  have hexpL3 : Real.exp L3 = L2 := by rw [← hl3, Real.exp_log hL2p]
  set α := L3 / L1 with hα_def
  have hα0 : 0 < α := div_pos hL3p hL1p
  have hα4 : α ≤ 1 / 4 := by
    rw [hα_def, div_le_iff₀ hL1p]
    linarith
  have hαL1 : α * L1 = L3 := by
    rw [hα_def]
    field_simp
  set r := Real.sqrt L3 with hr_def
  have hr0 : 0 < r := Real.sqrt_pos.mpr hL3p
  set β := (2 + 1 / r) * L2 / L3 with hβ_def
  have hq : 1 ≤ L2 / L3 := by
    rw [one_le_div hL3p]
    exact hL32
  have hβ2 : 2 ≤ β := by
    have h1 : 0 ≤ 1 / r := by positivity
    have h2 : β = (2 + 1 / r) * (L2 / L3) := by
      rw [hβ_def, mul_div_assoc]
    rw [h2]
    nlinarith
  have hαβ : α * β * L1 = 2 * L2 + L2 / r := by
    rw [hα_def, hβ_def]
    field_simp
  set X := E ^ (1 + β) with hX_def
  have hEβ : E ^ (2 : ℝ) ≤ E ^ β := Real.rpow_le_rpow_of_exponent_le hE1 hβ2
  rw [Real.rpow_two] at hEβ
  have hXeq : X = E * E ^ β := by
    rw [hX_def, Real.rpow_add hE0, Real.rpow_one]
  have hEβ4 : 4 ≤ E ^ β := by nlinarith
  have hX2 : 2 ≤ X := by
    rw [hXeq]
    nlinarith
  have hfl : X / 2 ≤ (⌊X⌋₊ : ℝ) := by
    have := Nat.sub_one_lt_floor X
    linarith
  set H := (⌊X⌋₊ : ℝ) / E with hH_def
  have hHlow : E ^ β / 2 ≤ H := by
    rw [hH_def, le_div_iff₀ hE0]
    have hfl' : E * E ^ β / 2 ≤ (⌊X⌋₊ : ℝ) := by
      calc E * E ^ β / 2 = X / 2 := by rw [hXeq]
        _ ≤ (⌊X⌋₊ : ℝ) := hfl
    linarith
  have hH2 : 2 ≤ H := by linarith
  have hH0 : 0 < H := by linarith
  have hlogH : β * L1 - Real.log 2 ≤ Real.log H := by
    have h := Real.log_le_log (by positivity) hHlow
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hE0, hl1] at h
    exact h
  have hRk := hR E H hE2 hH2 α hα0 hα4
  have hP0 := eulerProd_pos (y := E) hα4
  have hEul := (abs_le.mp (hE E α hE2 hα0 hα4)).2
  have hSh := (abs_le.mp (hS E α hE2 hα0 hα4 (by rw [hl1, hαL1]; exact hL3z))).2
  rw [hl1, hl2, hαL1, hexpL3] at hSh
  have hkey : Real.log H * (-α) +
      Real.log (∏ p ∈ primesLE E, ((1 - (p : ℝ) ^ (α - 1)) ^ 2)⁻¹) ≤
      -(L2 / r) + (2 * |CS| + |CE| + 1) * (L2 / L3) := by
    have h1 : α * (β * L1 - Real.log 2) ≤ α * Real.log H :=
      mul_le_mul_of_nonneg_left hlogH hα0.le
    have h2 : CS * (L2 / L3) ≤ |CS| * (L2 / L3) :=
      mul_le_mul_of_nonneg_right (le_abs_self CS) (by positivity)
    have h3 : CE ≤ |CE| := le_abs_self CE
    have h5 : α * Real.log 2 ≤ 1 := by
      have := log_two_le_one
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      nlinarith
    have h6 : |CE| + 1 ≤ (|CE| + 1) * (L2 / L3) :=
      le_mul_of_one_le_right (by positivity) hq
    linarith
  calc Skernel E H ≤ H ^ (-α) * ∏ p ∈ primesLE E, ((1 - (p : ℝ) ^ (α - 1)) ^ 2)⁻¹ := hRk
    _ = Real.exp (Real.log H * (-α) +
          Real.log (∏ p ∈ primesLE E, ((1 - (p : ℝ) ^ (α - 1)) ^ 2)⁻¹)) := by
        rw [Real.rpow_def_of_pos hH0, Real.exp_add, Real.exp_log hP0]
    _ ≤ Real.exp (-(L2 / r) + (2 * |CS| + |CE| + 1) * (L2 / L3)) :=
        Real.exp_le_exp.mpr hkey

theorem log_le_mul_eventually (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x in atTop, Real.log x ≤ c * x := by
  filter_upwards [Real.isLittleO_log_id_atTop.def hc, eventually_ge_atTop 1] with x hx hx1
  simp only [Real.norm_eq_abs, id] at hx
  rwa [abs_of_nonneg (Real.log_nonneg hx1), abs_of_nonneg (by linarith)] at hx

theorem fixedKernelTail : Principia.Erdos1054.Spine.Link_Eq_FixedKernelTail := by
  intro hR hS hE
  obtain ⟨CS, z₀, hS⟩ := hS
  obtain ⟨CE, hE⟩ := hE
  refine ⟨2 * |CS| + |CE| + 1, ?_⟩
  have hT1 : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hT2 : Tendsto (fun E => Real.log (Real.log E)) atTop atTop := hT1.comp hT1
  have hT3 : Tendsto (fun E => Real.log (Real.log (Real.log E))) atTop atTop := hT1.comp hT2
  have hlo : ∀ᶠ x in atTop, Real.log x ≤ x / 4 := by
    filter_upwards [log_le_mul_eventually (1 / 4) (by norm_num)] with x hx
    linarith
  have hev : ∀ᶠ E in atTop, 2 ≤ E ∧ 1 ≤ Real.log E ∧ 1 ≤ Real.log (Real.log E) ∧
      max z₀ 1 ≤ Real.log (Real.log (Real.log E)) ∧ Real.log (Real.log E) ≤ Real.log E / 4 := by
    filter_upwards [eventually_ge_atTop 2, hT1.eventually_ge_atTop 1, hT2.eventually_ge_atTop 1,
      hT3.eventually_ge_atTop (max z₀ 1), hT1.eventually hlo] with E h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨E₀, hE₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨E₀, fun E hE' => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hE₀ E hE'
  exact fixed_core hR hS hE h1 h2 h3 h4 h5

/-! ## `eq:moving-kernel-tail` -/

theorem moving_core (hR : Eq_RankinKernel) {CS z₀ CE : ℝ}
    (hS : ∀ y α : ℝ, 2 ≤ y → 0 < α → α ≤ 1 / 4 → z₀ ≤ α * Real.log y →
      |∑ p ∈ primesLE y, (p : ℝ) ^ (α - 1) - Real.log (Real.log y)| ≤
        CS * (Real.exp (α * Real.log y) / (α * Real.log y)))
    (hE : ∀ y α : ℝ, 2 ≤ y → 0 < α → α ≤ 1 / 4 →
      |Real.log (∏ p ∈ primesLE y, ((1 - (p : ℝ) ^ (α - 1)) ^ 2)⁻¹) -
        2 * ∑ p ∈ primesLE y, (p : ℝ) ^ (α - 1)| ≤ CE)
    {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) {J : ℝ} (hJ1 : 1 ≤ J) (hJC : 4 * C ≤ J)
    (hs1 : 4 ≤ Real.log J) (hs2 : 4 * max z₀ 1 ≤ Real.log J) (hs3 : 64 ≤ ε * Real.log J)
    (hs4 : 32 * |CS| ≤ ε * Real.log J) (hs5 : 8 * |CE| ≤ ε * Real.log J)
    (hs6 : Real.log J ≤ J / 8) (hs7 : 8 * Real.log J ≤ ε * J)
    (hs8 : 8 * |Real.log C| ≤ ε * J) :
    Skernel (Fmov J) (Real.exp J / (C * Wmov J)) ≤ Real.exp (-Wmov J + ε * Wmov J) := by
  have hJ0 : 0 < J := by linarith
  have hlogJ : Real.exp (Real.log J) = J := Real.exp_log hJ0
  generalize hsdef : Real.log J = s at *
  have hs0 : 0 < s := by linarith
  have hW2 : Wmov J ^ 2 = J * s / 2 := by
    unfold Wmov
    rw [← hsdef, Real.sq_sqrt]
    rw [hsdef]
    positivity
  have hW0 : 0 ≤ Wmov J := Real.sqrt_nonneg _
  unfold Fmov
  generalize Wmov J = W at *
  -- `r = e^{s/2} = √J`
  have hr2 : Real.exp (s / 2) ^ 2 = J := by
    rw [sq, ← Real.exp_add, add_halves, hlogJ]
  have hr1 : 1 + s / 2 ≤ Real.exp (s / 2) := by
    have := Real.add_one_le_exp (s / 2)
    linarith
  have hrq : s ^ 2 / 8 ≤ Real.exp (s / 2) := by
    have := Real.quadratic_le_exp_of_nonneg (x := s / 2) (by linarith)
    linarith
  have hJW : J ≤ W ^ 2 := by
    rw [hW2]
    have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ s by linarith) hJ0.le
    linarith
  have hrW : Real.exp (s / 2) ≤ W := by
    have hr0 := (Real.exp_pos (s / 2)).le
    exact (pow_le_pow_iff_left₀ hr0 hW0 (by norm_num : (2 : ℕ) ≠ 0)).mp (by rw [hr2]; exact hJW)
  have hWs : s / 2 ≤ W := by linarith
  have hWpos : 0 < W := by linarith
  have hWJ4 : W ≤ J / 4 := by
    refine (pow_le_pow_iff_left₀ hW0 (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp ?_
    rw [hW2]
    have := mul_le_mul_of_nonneg_left hs6 hJ0.le
    linarith
  have hWJ : W ≤ J := by linarith
  set α := W / J with hα_def
  have hα0 : 0 < α := div_pos hWpos hJ0
  have hα4 : α ≤ 1 / 4 := by
    rw [hα_def, div_le_iff₀ hJ0]
    linarith
  have hαJ : α * J = W := by
    rw [hα_def]
    field_simp
  have hαW : α * W = s / 2 := by
    have h : α * W = W ^ 2 / J := by
      rw [hα_def]
      ring
    rw [h, hW2]
    field_simp
  -- `F = ⌊e^W⌋`
  have heW : 3 ≤ Real.exp W := by
    have := Real.add_one_le_exp W
    linarith
  have hFle : (⌊Real.exp W⌋₊ : ℝ) ≤ Real.exp W := Nat.floor_le (Real.exp_pos W).le
  have hFgt : Real.exp W - 1 < (⌊Real.exp W⌋₊ : ℝ) := Nat.sub_one_lt_floor _
  have hF2 : (2 : ℝ) ≤ (⌊Real.exp W⌋₊ : ℝ) := by linarith
  have hF0 : (0 : ℝ) < (⌊Real.exp W⌋₊ : ℝ) := by linarith
  have hlogF1 : Real.log (⌊Real.exp W⌋₊ : ℝ) ≤ W := by
    have := Real.log_le_log hF0 hFle
    rwa [Real.log_exp] at this
  have hlogF2 : W - Real.log 2 ≤ Real.log (⌊Real.exp W⌋₊ : ℝ) := by
    have h : Real.exp W / 2 ≤ (⌊Real.exp W⌋₊ : ℝ) := by linarith
    have := Real.log_le_log (by positivity) h
    rwa [Real.log_div (Real.exp_pos W).ne' (by norm_num), Real.log_exp] at this
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 := log_two_le_one
  have hz_up : α * Real.log (⌊Real.exp W⌋₊ : ℝ) ≤ s / 2 := by
    rw [← hαW]
    exact mul_le_mul_of_nonneg_left hlogF1 hα0.le
  have hz_lo : s / 4 ≤ α * Real.log (⌊Real.exp W⌋₊ : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hlogF2 hα0.le
    have h2 : α * Real.log 2 ≤ 1 / 4 * 1 := mul_le_mul hα4 hl21 hl2p.le (by norm_num)
    linarith
  have hz0 : 0 < α * Real.log (⌊Real.exp W⌋₊ : ℝ) := by linarith
  -- `H = e^J / (C W)`
  have hCW : 0 < C * W := mul_pos hC hWpos
  have hexpJ : J ^ 2 / 2 ≤ Real.exp J := by
    have := Real.quadratic_le_exp_of_nonneg hJ0.le
    linarith
  have hH2 : 2 ≤ Real.exp J / (C * W) := by
    rw [le_div_iff₀ hCW]
    have h1 : C * W ≤ C * (J / 4) := mul_le_mul_of_nonneg_left hWJ4 hC.le
    have h2 : C * J ≤ J * J := mul_le_mul_of_nonneg_right (by linarith) hJ0.le
    linarith
  have hH0 : 0 < Real.exp J / (C * W) := by linarith
  have hlogH : Real.log (Real.exp J / (C * W)) = J - (Real.log C + Real.log W) := by
    rw [Real.log_div (Real.exp_pos J).ne' hCW.ne', Real.log_exp, Real.log_mul hC.ne' hWpos.ne']
  have hRk := hR (⌊Real.exp W⌋₊ : ℝ) (Real.exp J / (C * W)) hF2 hH2 α hα0 hα4
  have hP0 := eulerProd_pos (y := (⌊Real.exp W⌋₊ : ℝ)) hα4
  have hEul := (abs_le.mp (hE (⌊Real.exp W⌋₊ : ℝ) α hF2 hα0 hα4)).2
  have hSh := (abs_le.mp (hS (⌊Real.exp W⌋₊ : ℝ) α hF2 hα0 hα4
    (by linarith [le_max_left z₀ 1]))).2
  -- (a) the `H` defect
  have hlogW : Real.log W ≤ s := by
    rw [← hsdef]
    exact Real.log_le_log hWpos hWJ
  have ha : α * (Real.log C + Real.log W) ≤ ε * W / 4 := by
    have h : Real.log C + Real.log W ≤ ε * J / 4 := by
      linarith [le_abs_self (Real.log C)]
    calc α * (Real.log C + Real.log W) ≤ α * (ε * J / 4) := mul_le_mul_of_nonneg_left h hα0.le
      _ = ε * (α * J) / 4 := by ring
      _ = ε * W / 4 := by rw [hαJ]
  -- (b) `log log F`
  have hb : 2 * Real.log (Real.log (⌊Real.exp W⌋₊ : ℝ)) ≤ ε * W / 4 := by
    have hlF : 0 < Real.log (⌊Real.exp W⌋₊ : ℝ) := Real.log_pos (by linarith)
    have h1 : Real.log (Real.log (⌊Real.exp W⌋₊ : ℝ)) ≤ Real.log W := Real.log_le_log hlF hlogF1
    have h2 : ε * (s ^ 2 / 8) ≤ ε * W :=
      mul_le_mul_of_nonneg_left (hrq.trans hrW) hε.le
    linarith [mul_nonneg (show 0 ≤ ε * s - 64 by linarith) hs0.le]
  -- (c) the sharp-prime-sum error
  have hc : 2 * (CS * (Real.exp (α * Real.log (⌊Real.exp W⌋₊ : ℝ)) /
      (α * Real.log (⌊Real.exp W⌋₊ : ℝ)))) ≤ ε * W / 4 := by
    have hq : Real.exp (α * Real.log (⌊Real.exp W⌋₊ : ℝ)) /
        (α * Real.log (⌊Real.exp W⌋₊ : ℝ)) ≤ Real.exp (s / 2) / (s / 4) :=
      div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr hz_up) (by positivity) hz_lo
    have hq0 : 0 ≤ Real.exp (α * Real.log (⌊Real.exp W⌋₊ : ℝ)) /
        (α * Real.log (⌊Real.exp W⌋₊ : ℝ)) := div_nonneg (Real.exp_pos _).le hz0.le
    have h1 : CS * (Real.exp (α * Real.log (⌊Real.exp W⌋₊ : ℝ)) /
        (α * Real.log (⌊Real.exp W⌋₊ : ℝ))) ≤ |CS| * (Real.exp (s / 2) / (s / 4)) :=
      (mul_le_mul_of_nonneg_right (le_abs_self CS) hq0).trans
        (mul_le_mul_of_nonneg_left hq (abs_nonneg CS))
    have h2 : |CS| * (Real.exp (s / 2) / (s / 4)) = 4 * |CS| * Real.exp (s / 2) / s := by
      field_simp
    have h3 : 4 * |CS| * Real.exp (s / 2) / s ≤ ε * W / 8 := by
      rw [div_le_iff₀ hs0]
      have hr0 := (Real.exp_pos (s / 2)).le
      linarith [mul_le_mul_of_nonneg_right hs4 hr0,
        mul_le_mul_of_nonneg_left hrW (mul_nonneg hε.le hs0.le)]
    linarith
  -- (d) the Euler-product constant
  have hd : CE ≤ ε * W / 4 := by
    have h := mul_le_mul_of_nonneg_left hWs hε.le
    linarith [le_abs_self CE]
  have hkey : Real.log (Real.exp J / (C * W)) * (-α) +
      Real.log (∏ p ∈ primesLE (⌊Real.exp W⌋₊ : ℝ), ((1 - (p : ℝ) ^ (α - 1)) ^ 2)⁻¹) ≤
      -W + ε * W := by
    rw [hlogH]
    linarith
  calc Skernel (⌊Real.exp W⌋₊ : ℝ) (Real.exp J / (C * W))
      ≤ (Real.exp J / (C * W)) ^ (-α) *
          ∏ p ∈ primesLE (⌊Real.exp W⌋₊ : ℝ), ((1 - (p : ℝ) ^ (α - 1)) ^ 2)⁻¹ := hRk
    _ = Real.exp (Real.log (Real.exp J / (C * W)) * (-α) +
          Real.log (∏ p ∈ primesLE (⌊Real.exp W⌋₊ : ℝ), ((1 - (p : ℝ) ^ (α - 1)) ^ 2)⁻¹)) := by
        rw [Real.rpow_def_of_pos hH0, Real.exp_add, Real.exp_log hP0]
    _ ≤ Real.exp (-W + ε * W) := Real.exp_le_exp.mpr hkey

theorem movingKernelTail : Principia.Erdos1054.Spine.Link_Eq_MovingKernelTail := by
  intro hR hS hE
  obtain ⟨CS, z₀, hS⟩ := hS
  obtain ⟨CE, hE⟩ := hE
  intro C hC ε hε
  have hT : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hm : 0 < min 1 ε / 8 := by positivity
  have hev : ∀ᶠ J in atTop, 1 ≤ J ∧ 4 * C ≤ J ∧ 8 * |Real.log C| / ε ≤ J ∧
      4 ≤ Real.log J ∧ 4 * max z₀ 1 ≤ Real.log J ∧ 64 / ε ≤ Real.log J ∧
      32 * |CS| / ε ≤ Real.log J ∧ 8 * |CE| / ε ≤ Real.log J ∧
      Real.log J ≤ min 1 ε / 8 * J := by
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (4 * C),
      eventually_ge_atTop (8 * |Real.log C| / ε), hT.eventually_ge_atTop 4,
      hT.eventually_ge_atTop (4 * max z₀ 1), hT.eventually_ge_atTop (64 / ε),
      hT.eventually_ge_atTop (32 * |CS| / ε), hT.eventually_ge_atTop (8 * |CE| / ε),
      log_le_mul_eventually (min 1 ε / 8) hm] with J h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  obtain ⟨J₀, hJ₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨J₀, fun J hJ => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hJ₀ J hJ
  have hJ0 : 0 < J := by linarith
  have hm1 : min 1 ε / 8 * J ≤ 1 / 8 * J :=
    mul_le_mul_of_nonneg_right (by linarith [min_le_left 1 ε]) hJ0.le
  have hm2 : min 1 ε / 8 * J ≤ ε / 8 * J :=
    mul_le_mul_of_nonneg_right (by linarith [min_le_right 1 ε]) hJ0.le
  refine moving_core hR hS hE hC hε h1 h2 h4 h5 ?_ ?_ ?_ (by linarith) (by linarith) ?_
  · have := (div_le_iff₀ hε).mp h6
    linarith
  · have := (div_le_iff₀ hε).mp h7
    linarith
  · have := (div_le_iff₀ hε).mp h8
    linarith
  · have := (div_le_iff₀ hε).mp h3
    linarith

end Principia.Erdos1054.Proofs.KernelTails

namespace Principia.Erdos1054.Proofs

/-- `eq:rankin-kernel` (EP1054.tex lines 1929-1938). -/
theorem leaf_Eq_RankinKernel : Principia.Erdos1054.Eq_RankinKernel :=
  KernelTails.rankinKernel

/-- The higher terms of the Euler product are `O(1)` (EP1054.tex lines 1949-1950). -/
theorem leaf_UpperTails_Claim_EulerHigherTerms :
    Principia.Erdos1054.UpperTails.Claim_EulerHigherTerms :=
  KernelTails.eulerHigherTerms

/-- `eq:sharp-prime-sum` from Mertens' second theorem (EP1054.tex lines 1940-1948). -/
theorem link_Eq_SharpPrimeSum : Principia.Erdos1054.Spine.Link_Eq_SharpPrimeSum :=
  KernelTails.sharpPrimeSum

/-- `eq:fixed-kernel-tail` (EP1054.tex lines 1904-1915, 1952-1963). -/
theorem link_Eq_FixedKernelTail : Principia.Erdos1054.Spine.Link_Eq_FixedKernelTail :=
  KernelTails.fixedKernelTail

/-- `eq:moving-kernel-tail` (EP1054.tex lines 1916-1925, 1965-1976). -/
theorem link_Eq_MovingKernelTail : Principia.Erdos1054.Spine.Link_Eq_MovingKernelTail :=
  KernelTails.movingKernelTail

end Principia.Erdos1054.Proofs
