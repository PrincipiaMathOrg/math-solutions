/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.LargeQAnalytic
import Principia.Common.TernaryGoldbach.EBoundRS

set_option autoImplicit false

/-!
# The three prime-sum bounds of `prop:espagn`'s tail, from RS62 and Helfgott's small runs

* **`mertBound`** (`ternvin.tex` 3072-3077): `Π_{p≤p₁} p/(p−1) ≤ 1.90516 log p₁` for primes
  `p₁ ≥ 29`: the cited run for `p₁ ≤ 43` (`HC.ProdSmallCited`), RS62 (3.30) beyond
  (`e^γ(1 + 1/log²p₁) ≤ 1.7810727·1.0675 ≤ 1.90516` once `log p₁ ≥ 3.85`).
* **`thetaLower`** (3160-3162): `θ(p₁) ≥ 0.8009p₁` for primes `p₁ ≥ 31`: the cited run below
  `200` (`HC.ThetaSmallCited`), RS62 (3.16) beyond (`1 − 1/log 200 ≥ 0.8076`).
* **`logSumBound`** (3082-3107): `Σ_{p≤x} log(1 + p^{−2/3}) ≤ 0.74914x^{1/3}` for primes
  `x ≥ 29`: the cited run up to `10⁴` (`HC.LogSumCited`); beyond, `log(1 + y) ≤ y ≤
  (log p/log 10⁴)y`, and FINITE Abel summation (`EB.abel_le`) of `log p·p^{−2/3}` against RS62
  (3.32) `θ(n) < 1.01624n` gives `Σ_{10⁴<p≤x} log p·p^{−2/3} ≤ 3.04872x^{1/3} − 2.03248·10^{4/3}`
  (Helfgott's formula with `θ(10⁴) ≥ 0` dropped), then the cited `Σ_{p≤10⁴} ≤ 10.09062`. The
  integral of the printed Abel summation is replaced by telescoping:
  `m^{−2/3} ≤ 3(m^{1/3} − (m−1)^{1/3})` (`rpow_neg_twothirds_le`).
-/

namespace Principia.Common.TernaryGoldbach.LQ

open Principia.Common.TernaryGoldbach.HC (mertProd logSum thetaN)

/-! ## (1) Conversions and numerics -/

/-- `HC.thetaN n = θ(n)`. -/
theorem thetaN_eq (n : ℕ) : thetaN n = Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  rfl

/-- `log 47 ≥ 3.85` (`47 = 2⁶·(1 − 1/4)(1 − 1/48)`). -/
theorem log47_ge : (3.85 : ℝ) ≤ Real.log 47 := by
  have hb1 := (Principia.Erdos1054.Proofs.SmallRatio.log_series_bounds (x := 1 / 4) (by norm_num)
    (by norm_num) 10).2
  have hb2 := (Principia.Erdos1054.Proofs.SmallRatio.log_series_bounds (x := 1 / 48)
    (by norm_num) (by norm_num) 4).2
  have h47 : Real.log 47 = 6 * Real.log 2 - -Real.log (1 - 1 / 4) - -Real.log (1 - 1 / 48) := by
    rw [show (47 : ℝ) = 2 ^ 6 * (1 - 1 / 4) * (1 - 1 / 48) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  have h2 := Real.log_two_gt_d9
  norm_num [Finset.sum_range_succ] at hb1 hb2
  rw [h47]
  norm_num at h2 ⊢
  linarith

/-- `log 200 ≥ 5.2` (`e^{5.2} ≤ 181.4`). -/
theorem log200_ge : (5.2 : ℝ) ≤ Real.log 200 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp 5.2 = Real.exp 5 * Real.exp 0.2 := by rw [← Real.exp_add]; norm_num
  have h2 := exp_le_taylor 0.2 (by norm_num) (by norm_num)
  norm_num at h2
  have h3 : Real.exp 5 ≤ 148.4132 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp 1 ^ 5 ≤ (2.7182818286 : ℝ) ^ 5 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 5
    rw [← Real.exp_nat_mul] at this
    norm_num at this ⊢
    linarith
  rw [h1]
  have := mul_le_mul h3 h2 (Real.exp_pos _).le (by norm_num)
  linarith

/-- `9.2103 ≤ log 10⁴ ≤ 9.2104`. -/
theorem log10k_bounds : (9.2103 : ℝ) ≤ Real.log 10000 ∧ Real.log 10000 ≤ 9.2104 := by
  have e : Real.log 10000 = 4 * Real.log 10 := by
    rw [show (10000 : ℝ) = 10 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring
  have h1 := log_ten_ge
  have h2 := Principia.Erdos1054.Proofs.SmallRatio.log_ten_le
  rw [e]
  constructor <;> linarith

/-! ## (2) `Π p/(p−1)` -/

/-- **`Π_{p≤p₁} p/(p−1) ≤ 1.90516 log p₁`** for primes `p₁ ≥ 29` (`ternvin.tex` 3072-3077). -/
theorem mertBound (h330 : RS62_330) (hps : HC.ProdSmallCited) (p : ℕ) (hp : p.Prime)
    (h29 : 29 ≤ p) : mertProd p ≤ 1.90516 * Real.log p := by
  rcases le_or_gt p 43 with h43 | h43
  · exact (hps p hp h29 h43).le
  have h47 : 47 ≤ p := by
    by_contra h
    push Not at h
    interval_cases p <;> norm_num at hp
  have hr := h330 p h47
  have hL : 3.85 ≤ Real.log p :=
    le_trans log47_ge (Real.log_le_log (by norm_num) (by exact_mod_cast h47))
  have hg := Principia.Erdos1054.Proofs.SmallRatio.exp_gamma_le
  set L := Real.log p with hLdef
  have hL0 : 0 < L := by linarith
  have hfac : 1 + 1 / L ^ 2 ≤ 1.0675 := by
    have : 1 / L ^ 2 ≤ 1 / 3.85 ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hL 2)
    norm_num at this ⊢
    linarith
  have hfac0 : 0 ≤ 1 + 1 / L ^ 2 := by positivity
  have h1 : Real.exp Real.eulerMascheroniConstant * L * (1 + 1 / L ^ 2) ≤ 1.7810727 * L * 1.0675 :=
    mul_le_mul (mul_le_mul_of_nonneg_right hg hL0.le) hfac hfac0 (by positivity)
  linarith

/-! ## (3) `θ` from below -/

/-- **`θ(p₁) ≥ 0.8009p₁`** for primes `p₁ ≥ 31` (`ternvin.tex` 3160-3162). -/
theorem thetaLower (h316 : RS62_316) (hts : HC.ThetaSmallCited) (p : ℕ) (hp : p.Prime)
    (h31 : 31 ≤ p) : 0.8009 * (p : ℝ) ≤ Chebyshev.theta p := by
  rcases lt_or_ge p 200 with h200 | h200
  · rw [← thetaN_eq]
    exact hts p hp h31 h200
  have hpr : (200 : ℝ) ≤ p := by exact_mod_cast h200
  have hr := h316 p hpr
  have hL : 5.2 ≤ Real.log p := le_trans log200_ge (Real.log_le_log (by norm_num) hpr)
  have hL0 : 0 < Real.log p := by linarith
  have h1 : 1 / Real.log p ≤ 1 / 5.2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
  have h2 : 0.8009 * (p : ℝ) ≤ (p : ℝ) * (1 - 1 / Real.log p) := by
    have : (0.8009 : ℝ) ≤ 1 - 1 / Real.log p := by norm_num at h1 ⊢; linarith
    nlinarith
  linarith

/-! ## (4) `Σ log(1 + p^{−2/3})` -/

/-- **`m^{−2/3} ≤ 3(m^{1/3} − (m−1)^{1/3})`** for `m ≥ 1`: with `x = m^{1/3}`, `y = (m−1)^{1/3}`,
`x³ − y³ = 1` and `3x²(x − y) − (x³ − y³) = (x − y)²(2x + y) ≥ 0`. -/
theorem rpow_neg_twothirds_le (m : ℝ) (hm : 1 ≤ m) :
    m ^ (-(2 : ℝ) / 3) ≤ 3 * (m ^ ((1 : ℝ) / 3) - (m - 1) ^ ((1 : ℝ) / 3)) := by
  have hm0 : 0 < m := by linarith
  set x := m ^ ((1 : ℝ) / 3) with hx
  set y := (m - 1) ^ ((1 : ℝ) / 3) with hy
  have hx0 : 0 < x := Real.rpow_pos_of_pos hm0 _
  have hy0 : 0 ≤ y := Real.rpow_nonneg (by linarith) _
  have hx3 : x ^ 3 = m := cube_cbrt hm0.le
  have hy3 : y ^ 3 = m - 1 := cube_cbrt (by linarith)
  have hxy : y ≤ x := Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have hm23 : m ^ (-(2 : ℝ) / 3) = (x ^ 2)⁻¹ := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hm0.le, ← Real.rpow_neg hm0.le]
    norm_num
  rw [hm23, inv_le_iff_one_le_mul₀ (by positivity)]
  have e : x ^ 2 * (3 * (x - y)) - (x ^ 3 - y ^ 3) = (x - y) ^ 2 * (2 * x + y) := by ring
  have h1 : 0 ≤ (x - y) ^ 2 * (2 * x + y) := mul_nonneg (sq_nonneg _) (by linarith)
  have h2 : x ^ 3 - y ^ 3 = 1 := by rw [hx3, hy3]; ring
  linarith

/-- The weighted prime sum `Σ_{10⁴<p≤N} log p·p^{−2/3}`, through Abel summation:
`≤ 1.01624·10^{4/3} + 3.04872(max(N,10⁴)^{1/3} − 10^{4/3})`. -/
theorem weighted_le (h332 : RS62_332) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (if n.Prime ∧ 10000 < n then Real.log n else 0) *
        ((max n 10000 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) ≤
      1.01624 * ((10000 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) +
        3 * 1.01624 * (((max N 10000 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) -
          ((10000 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) := by
  have hmax0 : ∀ n : ℕ, (0 : ℝ) < ((max n 10000 : ℕ) : ℝ) := fun n => by
    have : 10000 ≤ max n 10000 := le_max_right _ _
    exact_mod_cast (by omega : 0 < max n 10000)
  have hfa : ∀ n : ℕ, ((max (n + 1) 10000 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) ≤
      ((max n 10000 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) := fun n =>
    Real.rpow_le_rpow_of_nonpos (hmax0 n) (by exact_mod_cast max_le_max (by omega) le_rfl)
      (by norm_num)
  have hf0 : ∀ n : ℕ, 0 ≤ ((max n 10000 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) := fun n =>
    Real.rpow_nonneg (hmax0 n).le _
  have hC : ∀ N' : ℕ, ∑ n ∈ Finset.range (N' + 1),
      (if n.Prime ∧ 10000 < n then Real.log n else 0) ≤ 1.01624 * ((max N' 10000 : ℕ) : ℝ) := by
    intro N'
    have hle : ∑ n ∈ Finset.range (N' + 1), (if n.Prime ∧ 10000 < n then Real.log n else 0) ≤
        thetaN N' := by
      unfold thetaN
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum fun n _ => ?_
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd h1.1 h2
      · exact Real.log_natCast_nonneg n
      · exact le_rfl
    rcases lt_or_ge N' 10000 with hN | hN
    · have hz : ∑ n ∈ Finset.range (N' + 1),
          (if n.Prime ∧ 10000 < n then Real.log n else 0) = 0 := by
        refine Finset.sum_eq_zero fun n hn => ?_
        have := Finset.mem_range.mp hn
        rw [if_neg]
        omega
      rw [hz]
      exact mul_nonneg (by norm_num) (hmax0 N').le
    · have hth := h332 N' (by exact_mod_cast hN)
      rw [← thetaN_eq] at hth
      have hmx : ((max N' 10000 : ℕ) : ℝ) = N' := by rw [max_eq_left hN]
      rw [hmx]
      linarith
  have hab := EB.abel_le (fun n => if n.Prime ∧ 10000 < n then Real.log n else 0)
    (fun n => ((max n 10000 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3))
    (fun n => 1.01624 * ((max n 10000 : ℕ) : ℝ)) hfa hf0 hC N
  -- the right side of Abel, termwise, telescopes
  have hterm : ∀ n ∈ Finset.range N,
      (1.01624 * ((max (n + 1) 10000 : ℕ) : ℝ) - 1.01624 * ((max n 10000 : ℕ) : ℝ)) *
        ((max (n + 1) 10000 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) ≤
      3 * 1.01624 * (((max (n + 1) 10000 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) -
        ((max n 10000 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) := by
    intro n _
    rcases lt_or_ge n 10000 with hn | hn
    · have e1 : max (n + 1) 10000 = 10000 := max_eq_right (by omega)
      have e2 : max n 10000 = 10000 := max_eq_right (by omega)
      rw [e1, e2, sub_self, sub_self, zero_mul, mul_zero]
    · have e1 : max (n + 1) 10000 = n + 1 := max_eq_left (by omega)
      have e2 : max n 10000 = n := max_eq_left hn
      rw [e1, e2]
      have ht := rpow_neg_twothirds_le ((n + 1 : ℕ) : ℝ)
        (by exact_mod_cast (by omega : 1 ≤ n + 1))
      have hcast : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
      rw [hcast] at ht
      have e3 : 1.01624 * ((n + 1 : ℕ) : ℝ) - 1.01624 * (n : ℝ) = 1.01624 := by push_cast; ring
      rw [e3]
      linarith
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum,
    Finset.sum_range_sub (fun n => ((max n 10000 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) N] at hsum
  have hg0 : 1.01624 * ((max 0 10000 : ℕ) : ℝ) * ((max 0 10000 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) =
      1.01624 * ((10000 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [show max 0 10000 = 10000 from rfl]
    have h10 : (0 : ℝ) < ((10000 : ℕ) : ℝ) := by norm_num
    rw [mul_assoc, ← Real.rpow_one_add' h10.le (by norm_num)]
    norm_num
  rw [hg0] at hab
  have hM0 : ((max 0 10000 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) = ((10000 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [show max 0 10000 = 10000 from rfl]
  rw [hM0] at hsum
  linarith

/-- **`Σ_{p≤x} log(1 + p^{−2/3}) ≤ 0.74914x^{1/3}`** for primes `x ≥ 29` (`ternvin.tex`
3082-3107). -/
theorem logSumBound (h332 : RS62_332) (hls : HC.LogSumCited) (hlt : HC.LogSumTenKCited)
    (p : ℕ) (hp : p.Prime) (h29 : 29 ≤ p) :
    logSum p ≤ 0.74914 * (p : ℝ) ^ ((1 : ℝ) / 3) := by
  rcases le_or_gt p 10000 with hsm | hbig
  · exact hls p hp h29 hsm
  have hpr : (10000 : ℝ) < p := by exact_mod_cast hbig
  obtain ⟨hL1, hL2⟩ := log10k_bounds
  -- split at `10⁴`
  have hsplit : logSum p = logSum 10000 + ∑ n ∈ (Finset.range (p + 1)).filter Nat.Prime,
      (if 10000 < n then Real.log (1 + (n : ℝ) ^ (-(2 : ℝ) / 3)) else 0) := by
    have hlp : logSum p = ∑ n ∈ (Finset.range (p + 1)).filter Nat.Prime,
        Real.log (1 + (n : ℝ) ^ (-(2 : ℝ) / 3)) := rfl
    have e1 : ∑ n ∈ ((Finset.range (p + 1)).filter Nat.Prime).filter (fun n => n ≤ 10000),
        Real.log (1 + (n : ℝ) ^ (-(2 : ℝ) / 3)) = logSum 10000 := by
      unfold logSum
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext n
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨⟨_, hp'⟩, hn⟩
        exact ⟨by omega, hp'⟩
      · rintro ⟨hn, hp'⟩
        exact ⟨⟨by omega, hp'⟩, by omega⟩
    have e2 : ∑ n ∈ ((Finset.range (p + 1)).filter Nat.Prime).filter (fun n => ¬n ≤ 10000),
        Real.log (1 + (n : ℝ) ^ (-(2 : ℝ) / 3)) = ∑ n ∈ (Finset.range (p + 1)).filter Nat.Prime,
          (if 10000 < n then Real.log (1 + (n : ℝ) ^ (-(2 : ℝ) / 3)) else 0) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases h : n ≤ 10000
      · rw [if_neg (not_not.mpr h), if_neg (by omega)]
      · rw [if_pos h, if_pos (by omega)]
    rw [hlp, ← Finset.sum_filter_add_sum_filter_not _ (fun n => n ≤ 10000), e1, e2]
  -- each large term is at most `log n·n^{−2/3}/log 10⁴`
  have hterm : ∀ n ∈ (Finset.range (p + 1)).filter Nat.Prime,
      (if 10000 < n then Real.log (1 + (n : ℝ) ^ (-(2 : ℝ) / 3)) else 0) ≤
        (if n.Prime ∧ 10000 < n then Real.log n else 0) *
          ((max n 10000 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) / Real.log 10000 := by
    intro n hn
    have hnp := (Finset.mem_filter.mp hn).2
    by_cases h : 10000 < n
    · rw [if_pos h, if_pos ⟨hnp, h⟩, max_eq_left h.le]
      have hn0 : (10000 : ℝ) < n := by exact_mod_cast h
      have hy0 : 0 ≤ (n : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
      have h1 : Real.log (1 + (n : ℝ) ^ (-(2 : ℝ) / 3)) ≤ (n : ℝ) ^ (-(2 : ℝ) / 3) := by
        have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + (n : ℝ) ^ (-(2 : ℝ) / 3))
        linarith
      have h2 : Real.log 10000 ≤ Real.log n := Real.log_le_log (by norm_num) hn0.le
      rw [le_div_iff₀ (by linarith)]
      calc Real.log (1 + (n : ℝ) ^ (-(2 : ℝ) / 3)) * Real.log 10000
          ≤ (n : ℝ) ^ (-(2 : ℝ) / 3) * Real.log 10000 :=
            mul_le_mul_of_nonneg_right h1 (by linarith)
        _ ≤ (n : ℝ) ^ (-(2 : ℝ) / 3) * Real.log n := mul_le_mul_of_nonneg_left h2 hy0
        _ = Real.log n * (n : ℝ) ^ (-(2 : ℝ) / 3) := by ring
    · rw [if_neg h, if_neg (fun h' => h h'.2), zero_mul, zero_div]
  have h1 := Finset.sum_le_sum hterm
  rw [← Finset.sum_div] at h1
  have hsub : ∑ n ∈ (Finset.range (p + 1)).filter Nat.Prime,
      (if n.Prime ∧ 10000 < n then Real.log n else 0) * ((max n 10000 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) ≤
        ∑ n ∈ Finset.range (p + 1),
          (if n.Prime ∧ 10000 < n then Real.log n else 0) *
            ((max n 10000 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun n _ _ => ?_
    refine mul_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    split_ifs
    · exact Real.log_natCast_nonneg n
    · exact le_rfl
  have hw := weighted_le h332 p
  rw [max_eq_left hbig.le] at hw
  have hlog0 : 0 < Real.log 10000 := by linarith
  -- numerics: `X = p^{1/3} ≥ 21.544`, `10^{4/3} ≥ 21.544`
  set X := (p : ℝ) ^ ((1 : ℝ) / 3) with hX
  set T := ((10000 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) with hT
  have hT0 : (21.544 : ℝ) ≤ T := le_cbrt (by norm_num) (by norm_num)
  have hTX : T ≤ X := Real.rpow_le_rpow (by norm_num) (by push_cast; linarith) (by norm_num)
  have hW : ∑ n ∈ Finset.range (p + 1),
      (if n.Prime ∧ 10000 < n then Real.log n else 0) * ((max n 10000 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) ≤
        3.04872 * X - 2.03248 * T := by linarith
  have hWpos : 0 ≤ 3.04872 * X - 2.03248 * T := by linarith
  have hdiv : (3.04872 * X - 2.03248 * T) / Real.log 10000 ≤ (3.04872 * X - 2.03248 * T) / 9.2103 :=
    div_le_div_of_nonneg_left hWpos (by norm_num) hL1
  have hA : ∑ n ∈ (Finset.range (p + 1)).filter Nat.Prime,
      (if 10000 < n then Real.log (1 + (n : ℝ) ^ (-(2 : ℝ) / 3)) else 0) ≤
        (3.04872 * X - 2.03248 * T) / 9.2103 := by
    refine le_trans h1 (le_trans ?_ hdiv)
    exact div_le_div_of_nonneg_right (le_trans hsub hW) hlog0.le
  rw [hsplit]
  have hlt' : logSum 10000 ≤ 10.09062 := hlt
  have : (3.04872 * X - 2.03248 * T) / 9.2103 = 3.04872 / 9.2103 * X - 2.03248 / 9.2103 * T := by
    ring
  rw [this] at hA
  norm_num at hA ⊢
  nlinarith

end Principia.Common.TernaryGoldbach.LQ
