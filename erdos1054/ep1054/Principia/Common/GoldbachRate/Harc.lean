/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Goldbach.Harc

/-!
# Goldbach rate, `Harc`: the major-arc L² error with an explicit `1 / log X` rate

`Principia.Common.Goldbach.Harc.harc_proven` proves the major-arc L² error
`∑_{n∈(X/2,X]} (Re coeffModel − 𝔖(n)·r_{X+1}(n))² ≤ ε X³` for every `ε > 0` and all large `X`.
Every estimate in its proof is explicit in `X` except one: the tail
`∑'_{q>P} μ(q)²/φ(q)^{3/2} → 0` (`tail_pow32_tendsto_zero`), taken from `HasSum.tendsto_sum_nat`
with no rate. This module restates the chain with the rate made explicit:

* `mu_sq_div_totient_rpow_le` — the pointwise majorant `μ²/φ^{3/2} ≤ 2^{9/4} q^{-9/8}` (the bound
  inside `phi_pow32_summable`, stated on its own);
* `tail_pow32_le` (R1) — `∑'_{q>P} μ²/φ^{3/2} ≤ 2^{9/4} ζ(17/16) / P^{1/16}` (Rankin's trick);
* `trunc_leg_rate` (R2) — the truncation leg is `≤ K X³ / log X`;
* `arc_tail_rhs_rate` (R3) — the arc-tail right-hand side is `≤ 65 N³ / log N`;
* `h1_arcTail_rate` (R4) — the arc-tail leg is `≤ 520 X³ / log X`;
* `harc_rate` (R5) — **the major-arc L² error is `≤ K X³ / log X`**.

The proofs copy their donors (`trunc_sub_error`, `arc_tail_rhs_small`, `h1_arcTail`,
`harc_proven`) up to the point where `ε` enters and replace the `ε`-bookkeeping by a fixed
`1 / log`. Nothing in `Principia.Common.Goldbach` is edited. The design study is
`Campaigns/Erdos-1054/THM14-RATE-PLAN.md` §3.
-/

set_option autoImplicit false
open DirichletCharacter Complex PowerSeries ArithmeticFunction Finset Filter Metric MeasureTheory

namespace Principia.Common.GoldbachRate

open Principia.Common.Goldbach
open Principia.Common.Goldbach.MinSum
open Principia.Common.Goldbach.MinorArc
open Principia.Common.Goldbach.MajorArcMainTerm
open scoped ArithmeticFunction

/-! ## R1: an explicit tail for `∑ μ(q)²/φ(q)^{3/2}` -/

/-- **The pointwise majorant behind `phi_pow32_summable`**: `μ(q)²/φ(q)^{3/2} ≤ 2^{9/4}·q^{-9/8}`
for every `q` (from `sqfree_totient_strong`, `φ(q)² ≥ q^{3/2}/8` for squarefree `q`). -/
theorem mu_sq_div_totient_rpow_le (q : ℕ) :
    (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2)
      ≤ (2 : ℝ) ^ ((9 : ℝ) / 4) * (1 / (q : ℝ) ^ ((9 : ℝ) / 8)) := by
  by_cases hsq : Squarefree q
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hsq.ne_zero
    have hφpos : 0 < (Nat.totient q : ℝ) := by
      have := Nat.totient_pos.mpr hqpos; positivity
    have hμ2 : (ArithmeticFunction.moebius q : ℝ) ^ 2 ≤ 1 := by
      have h1 : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      nlinarith [h1, abs_nonneg ((ArithmeticFunction.moebius q : ℤ) : ℝ),
        sq_abs ((ArithmeticFunction.moebius q : ℤ) : ℝ)]
    have hts := sqfree_totient_strong q hsq
    have h8 : (8 : ℝ) ^ ((3 : ℝ) / 4) = (2 : ℝ) ^ ((9 : ℝ) / 4) := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 3,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    have hpow : (q : ℝ) ^ ((9 : ℝ) / 8)
        ≤ (2 : ℝ) ^ ((9 : ℝ) / 4) * (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) := by
      have hφ2 : (Nat.totient q : ℝ) ^ 2 = (Nat.totient q : ℝ) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      have hts' : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 8 * (Nat.totient q : ℝ) ^ (2 : ℝ) := by
        rw [← hφ2]; exact hts
      have hb := Real.rpow_le_rpow (by positivity) hts' (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 4)
      rw [Real.mul_rpow (by norm_num) (by positivity),
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (q : ℝ)),
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (Nat.totient q : ℝ))] at hb
      norm_num at hb
      rw [h8] at hb
      exact hb
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (ArithmeticFunction.moebius q : ℝ) ^ 2 * (q : ℝ) ^ ((9 : ℝ) / 8)
        ≤ 1 * (q : ℝ) ^ ((9 : ℝ) / 8) := mul_le_mul_of_nonneg_right hμ2 (by positivity)
      _ = (q : ℝ) ^ ((9 : ℝ) / 8) := one_mul _
      _ ≤ (2 : ℝ) ^ ((9 : ℝ) / 4) * (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) := hpow
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    have hz : ((0 : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) = 0 := by norm_num
    rw [hz]; positivity

/-- **R1 (`tail_pow32_le`): Rankin's trick on the singular-series tail.** For `P ≥ 1`,
`∑'_{q>P} μ(q)²/φ(q)^{3/2} ≤ 2^{9/4}·ζ(17/16) / P^{1/16}`: for `q > P`,
`q^{-9/8} = q^{-1/16}·q^{-17/16} ≤ P^{-1/16}·q^{-17/16}`, and `∑ q^{-17/16}` converges. -/
theorem tail_pow32_le (P : ℕ) (hP : 0 < P) :
    ∑' q, (if P < q then
        (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) else 0)
      ≤ (2 : ℝ) ^ ((9 : ℝ) / 4) * (∑' q : ℕ, 1 / (q : ℝ) ^ ((17 : ℝ) / 16))
          / (P : ℝ) ^ ((1 : ℝ) / 16) := by
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hP16 : 0 < (P : ℝ) ^ ((1 : ℝ) / 16) := Real.rpow_pos_of_pos hPR _
  have hZs : Summable (fun q : ℕ => 1 / (q : ℝ) ^ ((17 : ℝ) / 16)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hpt : ∀ q : ℕ, (if P < q then
        (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) else 0)
      ≤ (2 : ℝ) ^ ((9 : ℝ) / 4) / (P : ℝ) ^ ((1 : ℝ) / 16)
          * (1 / (q : ℝ) ^ ((17 : ℝ) / 16)) := by
    intro q
    split_ifs with hPq
    · have hq : (0 : ℝ) < q := by exact_mod_cast (lt_trans hP hPq)
      have hsplit : (q : ℝ) ^ ((9 : ℝ) / 8)
          = (q : ℝ) ^ ((1 : ℝ) / 16) * (q : ℝ) ^ ((17 : ℝ) / 16) := by
        rw [← Real.rpow_add hq]; norm_num
      have hPq' : (P : ℝ) ^ ((1 : ℝ) / 16) ≤ (q : ℝ) ^ ((1 : ℝ) / 16) :=
        Real.rpow_le_rpow hPR.le (by exact_mod_cast hPq.le) (by norm_num)
      have hq1 : 0 < (q : ℝ) ^ ((1 : ℝ) / 16) := Real.rpow_pos_of_pos hq _
      have hq17 : 0 < (q : ℝ) ^ ((17 : ℝ) / 16) := Real.rpow_pos_of_pos hq _
      have h2 : (0 : ℝ) < (2 : ℝ) ^ ((9 : ℝ) / 4) := by positivity
      refine (mu_sq_div_totient_rpow_le q).trans ?_
      rw [hsplit]
      calc (2 : ℝ) ^ ((9 : ℝ) / 4)
            * (1 / ((q : ℝ) ^ ((1 : ℝ) / 16) * (q : ℝ) ^ ((17 : ℝ) / 16)))
          = (2 : ℝ) ^ ((9 : ℝ) / 4) / (q : ℝ) ^ ((1 : ℝ) / 16)
            * (1 / (q : ℝ) ^ ((17 : ℝ) / 16)) := by
            field_simp
        _ ≤ (2 : ℝ) ^ ((9 : ℝ) / 4) / (P : ℝ) ^ ((1 : ℝ) / 16)
            * (1 / (q : ℝ) ^ ((17 : ℝ) / 16)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact div_le_div_of_nonneg_left h2.le hP16 hPq'
    · positivity
  have hLs : Summable (fun q : ℕ => if P < q then
      (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) else 0) := by
    refine Summable.of_nonneg_of_le (fun q => ?_) hpt (hZs.mul_left _)
    split_ifs <;> positivity
  calc ∑' q, (if P < q then
        (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) else 0)
      ≤ ∑' q : ℕ, (2 : ℝ) ^ ((9 : ℝ) / 4) / (P : ℝ) ^ ((1 : ℝ) / 16)
          * (1 / (q : ℝ) ^ ((17 : ℝ) / 16)) :=
        Summable.tsum_le_tsum hpt hLs (hZs.mul_left _)
    _ = (2 : ℝ) ^ ((9 : ℝ) / 4) / (P : ℝ) ^ ((1 : ℝ) / 16)
          * ∑' q : ℕ, 1 / (q : ℝ) ^ ((17 : ℝ) / 16) := tsum_mul_left
    _ = (2 : ℝ) ^ ((9 : ℝ) / 4) * (∑' q : ℕ, 1 / (q : ℝ) ^ ((17 : ℝ) / 16))
          / (P : ℝ) ^ ((1 : ℝ) / 16) := by ring

/-! ## Scale facts -/

/-- `log x ≥ 2` once `x ≥ 8` (`3 log 2 > 2`). -/
theorem two_le_log_of_eight_le {x : ℝ} (hx : 8 ≤ x) : 2 ≤ Real.log x := by
  calc (2 : ℝ) ≤ Real.log 8 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        have := Real.log_two_gt_d9; push_cast; linarith
    _ ≤ Real.log x := Real.log_le_log (by norm_num) hx

/-- `L⁸ ≤ ⌊L⁹⌋₊` once `L ≥ 2`: `⌊L⁹⌋₊ > L⁹ − 1 ≥ 2L⁸ − 1 ≥ L⁸`. -/
theorem pow8_le_floor_pow9 {L : ℝ} (hL : 2 ≤ L) : L ^ 8 ≤ (Nat.floor (L ^ 9) : ℝ) := by
  have h := Nat.sub_one_lt_floor (L ^ 9)
  have h8 : (1 : ℝ) ≤ L ^ 8 := one_le_pow₀ (by linarith)
  have h9 : L ^ 9 = L * L ^ 8 := by ring
  have hm : 0 ≤ (L - 2) * L ^ 8 := mul_nonneg (by linarith) (by positivity)
  nlinarith

/-- `L ≤ (P^{1/16})² = P^{1/8}` whenever `L⁸ ≤ P`, `L ≥ 0`. -/
theorem le_sq_rpow_sixteenth {L P : ℝ} (hL : 0 ≤ L) (hLP : L ^ 8 ≤ P) :
    L ≤ (P ^ ((1 : ℝ) / 16)) ^ 2 := by
  have hP : 0 ≤ P := le_trans (by positivity) hLP
  have h1 : (P ^ ((1 : ℝ) / 16)) ^ 2 = P ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_natCast (P ^ ((1 : ℝ) / 16)) 2, ← Real.rpow_mul hP]; norm_num
  have h2 : (L ^ 8) ^ ((1 : ℝ) / 8) = L := by
    rw [← Real.rpow_natCast L 8, ← Real.rpow_mul hL]; norm_num
  rw [h1, ← h2]
  exact Real.rpow_le_rpow (by positivity) hLP (by norm_num)

/-! ## R2: the truncation leg -/

/-- **R2 (`trunc_leg_rate`): the truncation leg of `harc` with a `1 / log X` rate.** With
`P = ⌊(log(X+1))⁹⌋₊`: `∑_{n∈(X/2,X]} ((∑'_{q>P} T(q)) · r_{X+1}(n))² ≤ K X³ / log X`. The donor
`trunc_sub_error` bounds the left side by `(X+1)² · e X · (∑'_{q>P} μ²/φ^{3/2})²`; R1 bounds the
squared tail by `A² / P^{1/8} ≤ A² / log(X+1)`, since `P ≥ (log(X+1))⁸`. -/
theorem trunc_leg_rate :
    ∃ K : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X,
        ((∑' q, (if Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9) < q then Tarithv n q else 0))
          * (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
              (fun p => p.1 + p.2 = n)).card : ℝ)) ^ 2
        ≤ K * (X : ℝ) ^ 3 / Real.log X := by
  set A : ℝ := (2 : ℝ) ^ ((9 : ℝ) / 4) * (∑' q : ℕ, 1 / (q : ℝ) ^ ((17 : ℝ) / 16)) with hAdef
  refine ⟨4 * Real.exp 1 * A ^ 2, 8, fun X hX => ?_⟩
  have hX8 : (8 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hX1R : (1 : ℝ) ≤ X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hXcast : ((X + 1 : ℕ) : ℝ) = (X : ℝ) + 1 := by push_cast; ring
  set L : ℝ := Real.log ((X + 1 : ℕ) : ℝ) with hLdef
  have hL2 : 2 ≤ L := two_le_log_of_eight_le (by rw [hXcast]; linarith)
  have hLX : Real.log X ≤ L := Real.log_le_log hXpos (by rw [hXcast]; linarith)
  set P : ℕ := Nat.floor (L ^ 9) with hPdef
  have hPL : L ^ 8 ≤ (P : ℝ) := pow8_le_floor_pow9 hL2
  have hPposR : (0 : ℝ) < P := lt_of_lt_of_le (by positivity) hPL
  have hPpos : 0 < P := by exact_mod_cast hPposR
  set T : ℝ := ∑' q, (if P < q then
      (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) else 0)
    with hTdef
  have hT0 : 0 ≤ T := tsum_nonneg (fun q => by split_ifs <;> positivity)
  have hP16 : 0 < (P : ℝ) ^ ((1 : ℝ) / 16) := Real.rpow_pos_of_pos hPposR _
  have hTle : T ≤ A / (P : ℝ) ^ ((1 : ℝ) / 16) := tail_pow32_le P hPpos
  have hLsq : L ≤ ((P : ℝ) ^ ((1 : ℝ) / 16)) ^ 2 := le_sq_rpow_sixteenth (by linarith) hPL
  have hT2 : T ^ 2 ≤ A ^ 2 / L := by
    have h1 : T ^ 2 ≤ (A / (P : ℝ) ^ ((1 : ℝ) / 16)) ^ 2 := pow_le_pow_left₀ hT0 hTle 2
    rw [div_pow] at h1
    exact h1.trans (div_le_div_of_nonneg_left (by positivity) (by linarith) hLsq)
  have hrN : ∀ n ∈ Finset.Ioc (X / 2) X,
      ((((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
          (fun p => p.1 + p.2 = n)).card : ℝ)) ^ 2 ≤ ((X : ℝ) + 1) ^ 2 := by
    intro n _
    have h1 := kernel_card_le (X + 1) n
    have h0 : (0 : ℝ) ≤ (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
        (fun p => p.1 + p.2 = n)).card : ℝ) := by positivity
    rw [hXcast] at h1
    exact pow_le_pow_left₀ h0 h1 2
  have hstep : ∑ n ∈ Finset.Ioc (X / 2) X,
      ((∑' q, if P < q then Tarithv n q else 0)
        * (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
            (fun p => p.1 + p.2 = n)).card : ℝ)) ^ 2
      ≤ ((X : ℝ) + 1) ^ 2
        * ∑ n ∈ Finset.Ioc (X / 2) X, (∑' q, if P < q then Tarithv n q else 0) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro n hn
    rw [mul_pow]
    nlinarith [hrN n hn, sq_nonneg (∑' q, if P < q then Tarithv n q else 0)]
  have htail := tarith_tail_l2_le P X
  have hX2 : ((X : ℝ) + 1) ^ 2 ≤ 4 * (X : ℝ) ^ 2 := by nlinarith
  have hAL : A ^ 2 / L ≤ A ^ 2 / Real.log X :=
    div_le_div_of_nonneg_left (by positivity) hlogX hLX
  calc ∑ n ∈ Finset.Ioc (X / 2) X,
      ((∑' q, if P < q then Tarithv n q else 0)
        * (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
            (fun p => p.1 + p.2 = n)).card : ℝ)) ^ 2
      ≤ ((X : ℝ) + 1) ^ 2
        * ∑ n ∈ Finset.Ioc (X / 2) X, (∑' q, if P < q then Tarithv n q else 0) ^ 2 := hstep
    _ ≤ ((X : ℝ) + 1) ^ 2 * (Real.exp 1 * (X : ℝ) * T ^ 2) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ (4 * (X : ℝ) ^ 2) * (Real.exp 1 * (X : ℝ) * (A ^ 2 / Real.log X)) := by
        apply mul_le_mul hX2 _ (by positivity) (by positivity)
        apply mul_le_mul_of_nonneg_left (hT2.trans hAL) (by positivity)
    _ = 4 * Real.exp 1 * A ^ 2 * (X : ℝ) ^ 3 / Real.log X := by ring

/-! ## R3, R4: the arc-tail leg -/

/-- **R3 (`arc_tail_rhs_rate`): the arc-tail right-hand side is `≤ 65 N³ / log N`** at
`P = ⌊(log N)⁹⌋₊`, `Q = N/P`. The donor `arc_tail_rhs_small`'s own algebra: term 1 is
`≤ 64 N³ / √P ≤ 64 N³ / log N` (as `P ≥ (log N)²`), term 2 is `≤ 384 N (log N)⁵⁴ ≤ N² / log N`
(`384 (log N)⁵⁵ ≤ N`, `polylog_le_self`). Rpow-free except for the donor's `P^{5/2} = P³/√P`. -/
theorem arc_tail_rhs_rate :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (((N / Nat.floor ((Real.log N) ^ 9) : ℕ) : ℝ) + 1) ^ 3
          * (8 * ((Nat.floor ((Real.log N) ^ 9) : ℕ) : ℝ) ^ ((5 : ℝ) / 2))
        + 192 * (((N / Nat.floor ((Real.log N) ^ 9) : ℕ) : ℝ) + 1)
          * ((Nat.floor ((Real.log N) ^ 9) : ℕ) : ℝ) ^ 7
      ≤ 65 * (N : ℝ) ^ 3 / Real.log N := by
  obtain ⟨N₁, hN₁⟩ := polylog_le_self 9 1 (by norm_num)
  obtain ⟨N₂, hN₂⟩ := polylog_le_self 55 384 (by norm_num)
  refine ⟨max 8 (max N₁ N₂), fun N hN => ?_⟩
  have hN8 : 8 ≤ N := le_trans (le_max_left _ _) hN
  have hN1' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2' : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN8R : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN8
  have hN0R : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by linarith
  set L : ℝ := Real.log N with hLdef
  have hL2 : 2 ≤ L := two_le_log_of_eight_le hN8R
  have hLpos : 0 < L := by linarith
  set P : ℕ := Nat.floor (L ^ 9) with hPdef
  have hPL8 : L ^ 8 ≤ (P : ℝ) := pow8_le_floor_pow9 hL2
  have hPleL9 : (P : ℝ) ≤ L ^ 9 := Nat.floor_le (by positivity)
  have hL2P : L ^ 2 ≤ (P : ℝ) :=
    le_trans (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ L) (by norm_num)) hPL8
  have hP0R : (0 : ℝ) < (P : ℝ) := lt_of_lt_of_le (by positivity) hL2P
  have hPleN : (P : ℝ) ≤ (N : ℝ) := by
    have := hN₁ N hN1'
    rw [one_mul] at this
    exact hPleL9.trans this
  have hPleNnat : P ≤ N := by exact_mod_cast hPleN
  set Q : ℕ := N / P with hQdef
  have hQP : (Q + 1) * P ≤ 2 * N := by
    have h1 : Q * P ≤ N := Nat.div_mul_le_self N P
    have h2 : (Q + 1) * P = Q * P + P := by ring
    omega
  have hQPR : ((Q : ℝ) + 1) * (P : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hQP
  have hsqrtP0 : 0 < Real.sqrt (P : ℝ) := Real.sqrt_pos.mpr hP0R
  have hsqrtP : L ≤ Real.sqrt (P : ℝ) := by
    have h := Real.sqrt_le_sqrt hL2P
    rwa [Real.sqrt_sq hLpos.le] at h
  -- P^{5/2} = P³/√P
  have hrpow : (P : ℝ) ^ ((5 : ℝ) / 2) = (P : ℝ) ^ 3 / Real.sqrt (P : ℝ) := by
    rw [eq_div_iff (ne_of_gt hsqrtP0), Real.sqrt_eq_rpow, ← Real.rpow_add hP0R]
    rw [show (5 : ℝ) / 2 + 1 / 2 = ((3 : ℕ) : ℝ) by norm_num]
    exact Real.rpow_natCast _ 3
  have hterm1 : ((Q : ℝ) + 1) ^ 3 * (8 * (P : ℝ) ^ ((5 : ℝ) / 2)) ≤ 64 * (N : ℝ) ^ 3 / L := by
    rw [hrpow]
    have hcube : ((Q : ℝ) + 1) ^ 3 * (P : ℝ) ^ 3 ≤ 8 * (N : ℝ) ^ 3 := by
      calc ((Q : ℝ) + 1) ^ 3 * (P : ℝ) ^ 3 = (((Q : ℝ) + 1) * (P : ℝ)) ^ 3 := by ring
        _ ≤ (2 * (N : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) hQPR 3
        _ = 8 * (N : ℝ) ^ 3 := by ring
    calc ((Q : ℝ) + 1) ^ 3 * (8 * ((P : ℝ) ^ 3 / Real.sqrt (P : ℝ)))
        = 8 * (((Q : ℝ) + 1) ^ 3 * (P : ℝ) ^ 3) / Real.sqrt (P : ℝ) := by ring
      _ ≤ 8 * (8 * (N : ℝ) ^ 3) / Real.sqrt (P : ℝ) := by
          apply div_le_div_of_nonneg_right _ hsqrtP0.le
          linarith
      _ ≤ 8 * (8 * (N : ℝ) ^ 3) / L :=
          div_le_div_of_nonneg_left (by positivity) hLpos hsqrtP
      _ = 64 * (N : ℝ) ^ 3 / L := by ring
  have hterm2 : 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 7 ≤ (N : ℝ) ^ 3 / L := by
    have hL55 : 384 * L ^ 55 ≤ (N : ℝ) := hN₂ N hN2'
    have hP6 : (P : ℝ) ^ 6 ≤ (L ^ 9) ^ 6 := pow_le_pow_left₀ (by positivity) hPleL9 6
    have h1 : 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 7 ≤ 384 * (N : ℝ) * L ^ 54 := by
      calc 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 7
          = 192 * ((((Q : ℝ) + 1) * (P : ℝ)) * (P : ℝ) ^ 6) := by ring
        _ ≤ 192 * ((2 * (N : ℝ)) * (L ^ 9) ^ 6) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul hQPR hP6 (by positivity) (by positivity)
        _ = 384 * (N : ℝ) * L ^ 54 := by ring
    rw [le_div_iff₀ hLpos]
    have hNN : (N : ℝ) * (N : ℝ) ≤ (N : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg hN0R.le hN0R.le) (sub_nonneg.2 hN1R)]
    calc 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 7 * L ≤ 384 * (N : ℝ) * L ^ 54 * L :=
          mul_le_mul_of_nonneg_right h1 hLpos.le
      _ = (N : ℝ) * (384 * L ^ 55) := by ring
      _ ≤ (N : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_left hL55 hN0R.le
      _ ≤ (N : ℝ) ^ 3 := hNN
  calc ((Q : ℝ) + 1) ^ 3 * (8 * (P : ℝ) ^ ((5 : ℝ) / 2)) + 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 7
      ≤ 64 * (N : ℝ) ^ 3 / L + (N : ℝ) ^ 3 / L := add_le_add hterm1 hterm2
    _ = 65 * (N : ℝ) ^ 3 / L := by ring

section HabB
open MeasureTheory Finset

/-- **R4 (`h1_arcTail_rate`): the arc-tail leg of `harc` with a `1 / log X` rate.** With
`P = ⌊(log(X+1))⁹⌋₊`, `Q = (X+1)/P`:
`∑_{n∈(X/2,X]} (Re coeffModel(n) − r_{X+1}(n)·Re 𝔖_P^ℂ(n))² ≤ 520 X³ / log X`. The donor
`h1_arcTail` verbatim (Bessel + `psi_sub_phi_L2_total`), with R3 in place of
`arc_tail_rhs_small`. -/
theorem h1_arcTail_rate :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X,
        ((coeffModel (X + 1) (Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9))
            ((X + 1) / Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9)) n).re
          - ((((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
                (fun p => p.1 + p.2 = n)).card : ℝ)
              * (singSeriesC (Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9)) n).re)) ^ 2
        ≤ 520 * (X : ℝ) ^ 3 / Real.log X := by
  obtain ⟨N₀, hN₀⟩ := arc_tail_rhs_rate
  obtain ⟨N₂₇, hN₂₇⟩ := polylog_le_self 27 2 (by norm_num)
  refine ⟨max 3 (max N₀ N₂₇), fun X hX => ?_⟩
  have hX3 : 3 ≤ X := le_trans (le_max_left _ _) hX
  have hXN₀ : N₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXN₂₇ : N₂₇ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  set N : ℕ := X + 1 with hNdef
  have hN0R : (0:ℝ) < (N : ℝ) := by positivity
  set L : ℝ := Real.log N with hLdef
  -- L ≥ 1 from N ≥ 4 > e
  have hL1 : (1:ℝ) ≤ L := by
    rw [hLdef, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    calc Real.exp 1 ≤ 3 :=
          le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
      _ ≤ (N : ℝ) := by
          have h3X : (3:ℝ) ≤ (X : ℝ) := by exact_mod_cast hX3
          rw [hNdef]
          push_cast
          linarith
  set P : ℕ := Nat.floor (L ^ 9) with hPdef
  have hP1R : (1:ℝ) ≤ (P : ℝ) := by
    have h1 : (1:ℝ) ≤ L ^ 9 := one_le_pow₀ hL1
    have hfl : (1:ℕ) ≤ P := by
      rw [hPdef]
      exact Nat.le_floor (by exact_mod_cast h1)
    exact_mod_cast hfl
  have hP1 : 1 ≤ P := by exact_mod_cast hP1R
  have hPleL9 : (P : ℝ) ≤ L ^ 9 := Nat.floor_le (by positivity)
  -- 2P³ ≤ N via polylog 27
  have h2L27 : 2 * L ^ 27 ≤ (N : ℝ) := by
    have := hN₂₇ N (by omega)
    exact this
  have h2P3 : 2 * P ^ 3 ≤ N := by
    have hreal : 2 * (P : ℝ) ^ 3 ≤ (N : ℝ) := by
      have hL927 : (L ^ 9) ^ 3 = L ^ 27 := by ring
      have h1 : (P : ℝ) ^ 3 ≤ (L ^ 9) ^ 3 := pow_le_pow_left₀ (by positivity) hPleL9 3
      rw [hL927] at h1
      linarith
    exact_mod_cast hreal
  set Q : ℕ := N / P with hQdef
  have hQ2 : 2 ≤ Q := by
    rw [hQdef]
    rw [Nat.le_div_iff_mul_le (by omega : 0 < P)]
    have hPP3 : P ≤ P ^ 3 := Nat.le_self_pow (by norm_num) P
    calc 2 * P ≤ 2 * P ^ 3 := Nat.mul_le_mul (le_refl 2) hPP3
      _ ≤ N := h2P3
  have hPQ : 2 * P ^ 2 < Q + 1 := by
    have h1 : 2 * P ^ 2 ≤ Q := by
      rw [hQdef, Nat.le_div_iff_mul_le (by omega : 0 < P)]
      nlinarith [h2P3]
    omega
  -- pointwise real-part bridge, then Ioc ⊆ range N
  have hpt : ∀ n : ℕ,
      ((coeffModel N P Q n).re
        - ((((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℝ)
            * (singSeriesC P n).re)) ^ 2
      ≤ ‖coeffModel N P Q n
          - (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
            * singSeriesC P n‖ ^ 2 := by
    intro n
    set z : ℂ := coeffModel N P Q n
      - (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
        * singSeriesC P n with hzdef
    have hre : (coeffModel N P Q n).re
        - ((((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℝ)
            * (singSeriesC P n).re) = z.re := by
      rw [hzdef, Complex.sub_re]
      congr 1
      rw [show (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
          = ((((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℝ) : ℂ)
        from by push_cast; rfl]
      rw [Complex.re_ofReal_mul]
    rw [hre]
    calc z.re ^ 2 = |z.re| ^ 2 := (sq_abs _).symm
      _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 2
  have hsubset : Finset.Ioc (X / 2) X ⊆ Finset.range N := by
    intro n hn
    rw [Finset.mem_range]
    have := (Finset.mem_Ioc.mp hn).2
    omega
  calc ∑ n ∈ Finset.Ioc (X / 2) X,
      ((coeffModel N P Q n).re
        - ((((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℝ)
            * (singSeriesC P n).re)) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (X / 2) X,
          ‖coeffModel N P Q n
            - (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
              * singSeriesC P n‖ ^ 2 := Finset.sum_le_sum (fun n _ => hpt n)
    _ ≤ ∑ n ∈ Finset.range N,
          ‖coeffModel N P Q n
            - (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
              * singSeriesC P n‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro n _ _
        positivity
    _ ≤ ∫ α in Set.Ioc (0:ℝ) 1, ‖PhiArc N P Q α - PsiIdeal N P α‖ ^ 2 :=
        arcTailError_bessel N P Q N
    _ = ∫ α in Set.Ioc (0:ℝ) 1, ‖PsiIdeal N P α - PhiArc N P Q α‖ ^ 2 := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro α _
        dsimp only
        rw [norm_sub_rev]
    _ ≤ ((Q : ℝ) + 1) ^ 3 * (8 * (P : ℝ) ^ ((5 : ℝ) / 2))
        + 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 7 :=
        psi_sub_phi_L2_total N P Q hP1 hQ2 hPQ
    _ ≤ 65 * (N : ℝ) ^ 3 / L := hN₀ N (by omega)
    _ ≤ 520 * (X : ℝ) ^ 3 / Real.log X := by
        have hX2R : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (show 2 ≤ X by omega)
        have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
        have hNX : (N : ℝ) = (X : ℝ) + 1 := by rw [hNdef]; push_cast; ring
        have hLX : Real.log X ≤ L := Real.log_le_log (by linarith) (by rw [hNX]; linarith)
        have hN2X : (N : ℝ) ≤ 2 * (X : ℝ) := by rw [hNX]; linarith
        have h8 : (N : ℝ) ^ 3 ≤ 8 * (X : ℝ) ^ 3 := by
          calc (N : ℝ) ^ 3 ≤ (2 * (X : ℝ)) ^ 3 :=
              pow_le_pow_left₀ (by positivity) hN2X 3
            _ = 8 * (X : ℝ) ^ 3 := by ring
        calc 65 * (N : ℝ) ^ 3 / L ≤ 65 * (8 * (X : ℝ) ^ 3) / L := by
              apply div_le_div_of_nonneg_right _ (by linarith)
              linarith
          _ ≤ 65 * (8 * (X : ℝ) ^ 3) / Real.log X :=
              div_le_div_of_nonneg_left (by positivity) hlogX hLX
          _ = 520 * (X : ℝ) ^ 3 / Real.log X := by ring

end HabB

/-! ## R5: the major-arc L² error -/

/-- **R5 (`harc_rate`): the major-arc L² error with a `1 / log X` rate.** The statement of
`harc_proven` with `ε X³` replaced by `K X³ / log X`: split through `𝔖_P·r` into the arc-tail leg
(R4) and the truncation leg (R2), by `(a − b)² ≤ 2a² + 2b²` and `𝔖 − 𝔖_P = ∑'_{q>P} T`
(`singSeries_tail'`). -/
theorem harc_rate :
    ∃ K : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X,
        ((coeffModel (X + 1) (Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9))
            ((X + 1) / Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9)) n).re
          - (∑' q, Tarithv n q)
              * (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
                  (fun p => p.1 + p.2 = n)).card : ℝ)) ^ 2
        ≤ K * (X : ℝ) ^ 3 / Real.log X := by
  obtain ⟨X₁, h1⟩ := h1_arcTail_rate
  obtain ⟨K₂, X₂, h2⟩ := trunc_leg_rate
  refine ⟨2 * 520 + 2 * K₂, max X₁ X₂, fun X hX => ?_⟩
  have hX1 := h1 X (le_trans (le_max_left _ _) hX)
  have hX2 := h2 X (le_trans (le_max_right _ _) hX)
  set P : ℕ := Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9) with hPdef
  have hpt : ∀ n ∈ Finset.Ioc (X / 2) X,
      ((coeffModel (X + 1) P ((X + 1) / P) n).re
        - (∑' q, Tarithv n q)
            * (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
                (fun p => p.1 + p.2 = n)).card : ℝ)) ^ 2
      ≤ 2 * ((coeffModel (X + 1) P ((X + 1) / P) n).re
          - ((((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
                (fun p => p.1 + p.2 = n)).card : ℝ) * (singSeriesC P n).re)) ^ 2
        + 2 * ((∑' q, (if P < q then Tarithv n q else 0))
          * (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
              (fun p => p.1 + p.2 = n)).card : ℝ)) ^ 2 := by
    intro n hn
    have hn1 : 1 ≤ n := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    have hs : (singSeriesC P n).re = ∑ q ∈ Finset.Icc 1 P, Tarithv n q := by
      rw [singSeriesC_re]
      exact Finset.sum_congr rfl (fun q _ => by rw [Tarithv_apply])
    rw [hs, singSeries_tail' P n hn1]
    set f : ℝ := (coeffModel (X + 1) P ((X + 1) / P) n).re
    set t : ℝ := ∑' q, Tarithv n q
    set s : ℝ := ∑ q ∈ Finset.Icc 1 P, Tarithv n q
    set c : ℝ := (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
        (fun p => p.1 + p.2 = n)).card : ℝ)
    nlinarith [sq_nonneg ((f - c * s) + (t - s) * c)]
  calc ∑ n ∈ Finset.Ioc (X / 2) X,
      ((coeffModel (X + 1) P ((X + 1) / P) n).re
        - (∑' q, Tarithv n q)
            * (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
                (fun p => p.1 + p.2 = n)).card : ℝ)) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (X / 2) X,
          (2 * ((coeffModel (X + 1) P ((X + 1) / P) n).re
            - ((((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
                  (fun p => p.1 + p.2 = n)).card : ℝ) * (singSeriesC P n).re)) ^ 2
          + 2 * ((∑' q, (if P < q then Tarithv n q else 0))
            * (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
                (fun p => p.1 + p.2 = n)).card : ℝ)) ^ 2) := Finset.sum_le_sum hpt
    _ = 2 * ∑ n ∈ Finset.Ioc (X / 2) X,
          ((coeffModel (X + 1) P ((X + 1) / P) n).re
            - ((((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
                  (fun p => p.1 + p.2 = n)).card : ℝ) * (singSeriesC P n).re)) ^ 2
        + 2 * ∑ n ∈ Finset.Ioc (X / 2) X,
          ((∑' q, (if P < q then Tarithv n q else 0))
            * (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
                (fun p => p.1 + p.2 = n)).card : ℝ)) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * (520 * (X : ℝ) ^ 3 / Real.log X) + 2 * (K₂ * (X : ℝ) ^ 3 / Real.log X) := by
        linarith [hX1, hX2]
    _ = (2 * 520 + 2 * K₂) * (X : ℝ) ^ 3 / Real.log X := by ring

end Principia.Common.GoldbachRate
