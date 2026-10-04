/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIWeightX

set_option autoImplicit false

/-!
# `T2V.WeightX` on `2 < X ≤ 9093/4`, PROVED by fourteen kernel-checked intervals

On `[x₀, x₁]` take `R = n` (a fixed integer). Each term `gX(r)` increases with `X` and with
`W ≥ 117` (`aW ≤ 59/117`), so `∑ gX(r)/φ(r) ≥ ∑ g0(x₀, n, r)/φ(r)`, an exact rational; and
`log(X/2) ≤ log(x₁/2) ≤ k·0.6931471808 + x₁/2^{k+1} − 1` (`log y ≤ y − 1` after removing `2^k`,
Mathlib's `log 2 < 0.6931471808`). Every interval is then one `norm_num` comparison of rationals.

```
 log_le_k        log y ≤ k·0.6931471808 + y/2^k − 1                               PROVED
 gX_ge           g0(x₀, R, r) ≤ gX(W, X, R, r)   (W ≥ 117, X ≥ x₀, rR < 3.5x₀)     PROVED
 interval        one interval from one rational inequality                        PROVED
 num0 … num13    the fourteen rational inequalities (R = 1, 2, 3, 6, 7, 15)        PROVED
 weightX_small   WeightX for 2 < X ≤ 9093/4                                       PROVED
```

The intervals were chosen by `scratchpad/wlb/plan2.py` (smallest margin `0.0155` at
`X ∈ [437/4, 727/4]`); the choice is not a proof step, each inequality is checked here.
No computation is cited.
-/

namespace Principia.Common.TernaryGoldbach.T2V

/-- The weight at the worst `W` (`aW ≤ 59/117`) and a fixed `X₀`. -/
noncomputable def g0 (X R : ℝ) (r : ℕ) : ℝ :=
  (59 / 117 + 3 / 2 * ((r : ℝ) * R / (X - r * R / 3.5)))⁻¹

/-- **`log y ≤ k·0.6931471808 + y/2^k − 1`**. -/
theorem log_le_k (y : ℝ) (hy : 0 < y) (k : ℕ) :
    Real.log y ≤ k * 0.6931471808 + y / 2 ^ k - 1 := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have e : y = 2 ^ k * (y / 2 ^ k) := by field_simp
  have h1 : Real.log y = k * Real.log 2 + Real.log (y / 2 ^ k) := by
    rw [← Real.log_pow, ← Real.log_mul (by positivity) (by positivity), ← e]
  have h3 := Real.log_le_sub_one_of_pos (show 0 < y / 2 ^ k by positivity)
  have h5 : (k : ℝ) * Real.log 2 ≤ k * 0.6931471808 :=
    mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg k)
  rw [h1]
  linarith

/-- **`gX` dominates the frozen weight `g0`**. -/
theorem gX_ge (W X X0 R : ℝ) (r : ℕ) (hW : 117 ≤ W) (hX0 : X0 ≤ X) (hR : 0 ≤ R)
    (hrR : (r : ℝ) * R < 3.5 * X0) : g0 X0 R r ≤ gX W X R r := by
  unfold g0 gX
  rw [show (3.5 : ℝ) = 7 / 2 by norm_num] at hrR ⊢
  have hW0 : 0 < W := by linarith
  have hd0 : 0 < X0 - r * R / (7 / 2) := by linarith
  have hd : 0 < X - r * R / (7 / 2) := by linarith
  have hrR0 : 0 ≤ (r : ℝ) * R := mul_nonneg (Nat.cast_nonneg r) hR
  have ha : (W + 1) / (2 * W) ≤ 59 / 117 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hb : (r : ℝ) * R / (X - r * R / (7 / 2)) ≤ r * R / (X0 - r * R / (7 / 2)) :=
    div_le_div_of_nonneg_left hrR0 hd0 (by linarith)
  have hpos : 0 < (W + 1) / (2 * W) + 3 / 2 * ((r : ℝ) * R / (X - r * R / (7 / 2))) :=
    add_pos_of_pos_of_nonneg (by positivity) (mul_nonneg (by norm_num) (div_nonneg hrR0 hd.le))
  apply inv_anti₀ hpos
  linarith

/-- **One interval** from one rational inequality. -/
theorem interval (x0 x1 : ℝ) (n k : ℕ) (hx0 : 2 ≤ x0) (hn1 : 1 ≤ n) (hnx : (n : ℝ) ≤ x0 / 2)
    (hn2 : (n : ℝ) ^ 2 < 3.5 * x0)
    (hnum : (k : ℝ) * 0.6931471808 + x1 / 2 / 2 ^ k - 1 ≤
      ∑ r ∈ (Finset.Icc 1 n).filter Squarefree, g0 x0 n r / Nat.totient r)
    (W X : ℝ) (hW : 117 ≤ W) (hX0 : x0 ≤ X) (hX1 : X ≤ x1) :
    ∃ R : ℝ, 1 ≤ R ∧ R ≤ X / 2 ∧ R ^ 2 < 3.5 * X ∧
      Real.log (X / 2) ≤ ∑ r ∈ sqS R, gX W X R r / Nat.totient r := by
  have h35 : (3.5 : ℝ) * x0 ≤ 3.5 * X := mul_le_mul_of_nonneg_left hX0 (by norm_num)
  refine ⟨n, by exact_mod_cast hn1, by linarith, lt_of_lt_of_le hn2 h35, ?_⟩
  have hl : Real.log (X / 2) ≤ Real.log (x1 / 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hk := log_le_k (x1 / 2) (by linarith) k
  have hs : sqS (n : ℝ) = (Finset.Icc 1 n).filter Squarefree := by
    unfold sqS
    rw [Nat.floor_natCast]
  rw [hs]
  refine hl.trans (hk.trans (hnum.trans (Finset.sum_le_sum fun r hr => ?_)))
  have hrn : r ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).2
  have hrn' : (r : ℝ) ≤ n := by exact_mod_cast hrn
  have hrR : (r : ℝ) * n < 3.5 * x0 := by
    have : (r : ℝ) * n ≤ (n : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  exact div_le_div_of_nonneg_right (gX_ge W X x0 n r hW hX0 (Nat.cast_nonneg n) hrR)
    (Nat.cast_nonneg _)

/-- Interval 0: `X ∈ [2, 4]`, `R = 1`, `k = 1`. -/
theorem num0 : ((1 : ℕ) : ℝ) * 0.6931471808 + (4 : ℝ) / 2 / 2 ^ 1 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 1).filter Squarefree, g0 (2 : ℝ) ((1 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 1).filter Squarefree = {1} by decide +kernel]
  norm_num [Finset.sum_insert, g0]

/-- Interval 1: `X ∈ [4, 11/2]`, `R = 2`, `k = 1`. -/
theorem num1 : ((1 : ℕ) : ℝ) * 0.6931471808 + (11 / 2 : ℝ) / 2 / 2 ^ 1 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 2).filter Squarefree, g0 (4 : ℝ) ((2 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 2).filter Squarefree = {1, 2} by decide +kernel]
  have t2 : Nat.totient 2 = 1 := by decide
  norm_num [Finset.sum_insert, g0, t2]

/-- Interval 2: `X ∈ [11/2, 8]`, `R = 2`, `k = 2`. -/
theorem num2 : ((2 : ℕ) : ℝ) * 0.6931471808 + (8 : ℝ) / 2 / 2 ^ 2 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 2).filter Squarefree, g0 (11 / 2 : ℝ) ((2 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 2).filter Squarefree = {1, 2} by decide +kernel]
  have t2 : Nat.totient 2 = 1 := by decide
  norm_num [Finset.sum_insert, g0, t2]

/-- Interval 3: `X ∈ [8, 23/2]`, `R = 2`, `k = 3`. -/
theorem num3 : ((3 : ℕ) : ℝ) * 0.6931471808 + (23 / 2 : ℝ) / 2 / 2 ^ 3 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 2).filter Squarefree, g0 (8 : ℝ) ((2 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 2).filter Squarefree = {1, 2} by decide +kernel]
  have t2 : Nat.totient 2 = 1 := by decide
  norm_num [Finset.sum_insert, g0, t2]

/-- Interval 4: `X ∈ [23/2, 35/2]`, `R = 2`, `k = 3`. -/
theorem num4 : ((3 : ℕ) : ℝ) * 0.6931471808 + (35 / 2 : ℝ) / 2 / 2 ^ 3 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 2).filter Squarefree, g0 (23 / 2 : ℝ) ((2 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 2).filter Squarefree = {1, 2} by decide +kernel]
  have t2 : Nat.totient 2 = 1 := by decide
  norm_num [Finset.sum_insert, g0, t2]

/-- Interval 5: `X ∈ [35/2, 105/4]`, `R = 2`, `k = 4`. -/
theorem num5 : ((4 : ℕ) : ℝ) * 0.6931471808 + (105 / 4 : ℝ) / 2 / 2 ^ 4 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 2).filter Squarefree, g0 (35 / 2 : ℝ) ((2 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 2).filter Squarefree = {1, 2} by decide +kernel]
  have t2 : Nat.totient 2 = 1 := by decide
  norm_num [Finset.sum_insert, g0, t2]

/-- Interval 6: `X ∈ [105/4, 41]`, `R = 3`, `k = 4`. -/
theorem num6 : ((4 : ℕ) : ℝ) * 0.6931471808 + (41 : ℝ) / 2 / 2 ^ 4 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 3).filter Squarefree, g0 (105 / 4 : ℝ) ((3 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 3).filter Squarefree = {1, 2, 3} by decide +kernel]
  have t2 : Nat.totient 2 = 1 := by decide
  have t3 : Nat.totient 3 = 2 := by decide
  norm_num [Finset.sum_insert, g0, t2, t3]

/-- Interval 7: `X ∈ [41, 277/4]`, `R = 3`, `k = 5`. -/
theorem num7 : ((5 : ℕ) : ℝ) * 0.6931471808 + (277 / 4 : ℝ) / 2 / 2 ^ 5 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 3).filter Squarefree, g0 (41 : ℝ) ((3 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 3).filter Squarefree = {1, 2, 3} by decide +kernel]
  have t2 : Nat.totient 2 = 1 := by decide
  have t3 : Nat.totient 3 = 2 := by decide
  norm_num [Finset.sum_insert, g0, t2, t3]

/-- Interval 8: `X ∈ [277/4, 437/4]`, `R = 3`, `k = 6`. -/
theorem num8 : ((6 : ℕ) : ℝ) * 0.6931471808 + (437 / 4 : ℝ) / 2 / 2 ^ 6 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 3).filter Squarefree, g0 (277 / 4 : ℝ) ((3 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 3).filter Squarefree = {1, 2, 3} by decide +kernel]
  have t2 : Nat.totient 2 = 1 := by decide
  have t3 : Nat.totient 3 = 2 := by decide
  norm_num [Finset.sum_insert, g0, t2, t3]

/-- Interval 9: `X ∈ [437/4, 727/4]`, `R = 6`, `k = 7`. -/
theorem num9 : ((7 : ℕ) : ℝ) * 0.6931471808 + (727 / 4 : ℝ) / 2 / 2 ^ 7 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 6).filter Squarefree, g0 (437 / 4 : ℝ) ((6 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 6).filter Squarefree = {1, 2, 3, 5, 6} by decide +kernel]
  have t2 : Nat.totient 2 = 1 := by decide
  have t3 : Nat.totient 3 = 2 := by decide
  have t5 : Nat.totient 5 = 4 := by decide
  have t6 : Nat.totient 6 = 2 := by decide
  norm_num [Finset.sum_insert, g0, t2, t3, t5, t6]

/-- Interval 10: `X ∈ [727/4, 331]`, `R = 7`, `k = 7`. -/
theorem num10 : ((7 : ℕ) : ℝ) * 0.6931471808 + (331 : ℝ) / 2 / 2 ^ 7 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 7).filter Squarefree, g0 (727 / 4 : ℝ) ((7 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 7).filter Squarefree = {1, 2, 3, 5, 6, 7} by decide +kernel]
  have t2 : Nat.totient 2 = 1 := by decide
  have t3 : Nat.totient 3 = 2 := by decide
  have t5 : Nat.totient 5 = 4 := by decide
  have t6 : Nat.totient 6 = 2 := by decide
  have t7 : Nat.totient 7 = 6 := by decide
  norm_num [Finset.sum_insert, g0, t2, t3, t5, t6, t7]

/-- Interval 11: `X ∈ [331, 614]`, `R = 7`, `k = 8`. -/
theorem num11 : ((8 : ℕ) : ℝ) * 0.6931471808 + (614 : ℝ) / 2 / 2 ^ 8 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 7).filter Squarefree, g0 (331 : ℝ) ((7 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 7).filter Squarefree = {1, 2, 3, 5, 6, 7} by decide +kernel]
  have t2 : Nat.totient 2 = 1 := by decide
  have t3 : Nat.totient 3 = 2 := by decide
  have t5 : Nat.totient 5 = 4 := by decide
  have t6 : Nat.totient 6 = 2 := by decide
  have t7 : Nat.totient 7 = 6 := by decide
  norm_num [Finset.sum_insert, g0, t2, t3, t5, t6, t7]

/-- Interval 12: `X ∈ [614, 4569/4]`, `R = 15`, `k = 9`. -/
theorem num12 : ((9 : ℕ) : ℝ) * 0.6931471808 + (4569 / 4 : ℝ) / 2 / 2 ^ 9 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 15).filter Squarefree, g0 (614 : ℝ) ((15 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 15).filter Squarefree =
    {1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15} by decide +kernel]
  have t2 : Nat.totient 2 = 1 := by decide
  have t3 : Nat.totient 3 = 2 := by decide
  have t5 : Nat.totient 5 = 4 := by decide
  have t6 : Nat.totient 6 = 2 := by decide
  have t7 : Nat.totient 7 = 6 := by decide
  have t10 : Nat.totient 10 = 4 := by decide
  have t11 : Nat.totient 11 = 10 := by decide
  have t13 : Nat.totient 13 = 12 := by decide
  have t14 : Nat.totient 14 = 6 := by decide
  have t15 : Nat.totient 15 = 8 := by decide
  norm_num [Finset.sum_insert, g0, t2, t3, t5, t6, t7, t10, t11, t13, t14, t15]

/-- Interval 13: `X ∈ [4569/4, 9093/4]`, `R = 15`, `k = 10`. -/
theorem num13 : ((10 : ℕ) : ℝ) * 0.6931471808 + (9093 / 4 : ℝ) / 2 / 2 ^ 10 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 15).filter Squarefree, g0 (4569 / 4 : ℝ) ((15 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 15).filter Squarefree =
    {1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15} by decide +kernel]
  have t2 : Nat.totient 2 = 1 := by decide
  have t3 : Nat.totient 3 = 2 := by decide
  have t5 : Nat.totient 5 = 4 := by decide
  have t6 : Nat.totient 6 = 2 := by decide
  have t7 : Nat.totient 7 = 6 := by decide
  have t10 : Nat.totient 10 = 4 := by decide
  have t11 : Nat.totient 11 = 10 := by decide
  have t13 : Nat.totient 13 = 12 := by decide
  have t14 : Nat.totient 14 = 6 := by decide
  have t15 : Nat.totient 15 = 8 := by decide
  norm_num [Finset.sum_insert, g0, t2, t3, t5, t6, t7, t10, t11, t13, t14, t15]

/-- **`WeightX` on `2 < X ≤ 9093/4`, PROVED** (fourteen intervals, `R ≤ 15`). -/
theorem weightX_small (W X : ℝ) (hW : 117 ≤ W) (hX : 2 < X) (hX1 : X ≤ (9093 / 4 : ℝ)) :
    ∃ R : ℝ, 1 ≤ R ∧ R ≤ X / 2 ∧ R ^ 2 < 3.5 * X ∧
      Real.log (X / 2) ≤ ∑ r ∈ sqS R, gX W X R r / Nat.totient r := by
  rcases le_or_gt X (4 : ℝ) with h0 | h0
  · exact interval (2 : ℝ) (4 : ℝ) 1 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) num0 W X hW (by linarith) h0
  rcases le_or_gt X (11 / 2 : ℝ) with h1 | h1
  · exact interval (4 : ℝ) (11 / 2 : ℝ) 2 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) num1 W X hW (by linarith) h1
  rcases le_or_gt X (8 : ℝ) with h2 | h2
  · exact interval (11 / 2 : ℝ) (8 : ℝ) 2 2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) num2 W X hW (by linarith) h2
  rcases le_or_gt X (23 / 2 : ℝ) with h3 | h3
  · exact interval (8 : ℝ) (23 / 2 : ℝ) 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) num3 W X hW (by linarith) h3
  rcases le_or_gt X (35 / 2 : ℝ) with h4 | h4
  · exact interval (23 / 2 : ℝ) (35 / 2 : ℝ) 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) num4 W X hW (by linarith) h4
  rcases le_or_gt X (105 / 4 : ℝ) with h5 | h5
  · exact interval (35 / 2 : ℝ) (105 / 4 : ℝ) 2 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) num5 W X hW (by linarith) h5
  rcases le_or_gt X (41 : ℝ) with h6 | h6
  · exact interval (105 / 4 : ℝ) (41 : ℝ) 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) num6 W X hW (by linarith) h6
  rcases le_or_gt X (277 / 4 : ℝ) with h7 | h7
  · exact interval (41 : ℝ) (277 / 4 : ℝ) 3 5 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) num7 W X hW (by linarith) h7
  rcases le_or_gt X (437 / 4 : ℝ) with h8 | h8
  · exact interval (277 / 4 : ℝ) (437 / 4 : ℝ) 3 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) num8 W X hW (by linarith) h8
  rcases le_or_gt X (727 / 4 : ℝ) with h9 | h9
  · exact interval (437 / 4 : ℝ) (727 / 4 : ℝ) 6 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) num9 W X hW (by linarith) h9
  rcases le_or_gt X (331 : ℝ) with h10 | h10
  · exact interval (727 / 4 : ℝ) (331 : ℝ) 7 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) num10 W X hW (by linarith) h10
  rcases le_or_gt X (614 : ℝ) with h11 | h11
  · exact interval (331 : ℝ) (614 : ℝ) 7 8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) num11 W X hW (by linarith) h11
  rcases le_or_gt X (4569 / 4 : ℝ) with h12 | h12
  · exact interval (614 : ℝ) (4569 / 4 : ℝ) 15 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) num12 W X hW (by linarith) h12
  exact interval (4569 / 4 : ℝ) (9093 / 4 : ℝ) 15 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) num13 W X hW (by linarith) hX1


end Principia.Common.TernaryGoldbach.T2V
