/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIWeightXSmall

set_option autoImplicit false

/-!
# `T2V.WeightX` on `9093/4 ≤ X ≤ 71252`, PROVED by five more kernel-checked intervals

The same method as `TypeIIWeightXSmall` (`T2V.interval`), with `R = 23, 42, 43, 71, 95`. It
carries `WeightX` up to `X = 71252`, where `R = (7X/23)^{1/2} ≥ 147`, so the large range needs
Montgomery–Vaughan's Lemma 8 only above `R = 100` and no cited computation at all.

```
 numM0 … numM4   five rational inequalities                                      PROVED
 weightX_mid     WeightX for 9093/4 ≤ X ≤ 71252                                   PROVED
```

Intervals chosen by `scratchpad/wlb/plan3.py` (smallest margin `0.0212`); not a proof step.
No computation is cited.
-/

namespace Principia.Common.TernaryGoldbach.T2V

/-- Interval M0: `X ∈ [9093/4, 8641/2]`, `R = 23`, `k = 11`. -/
theorem numM0 : ((11 : ℕ) : ℝ) * 0.6931471808 + (8641 / 2 : ℝ) / 2 / 2 ^ 11 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 23).filter Squarefree, g0 (9093 / 4 : ℝ) ((23 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 23).filter Squarefree =
    {1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23} by decide +kernel]
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
  have t17 : Nat.totient 17 = 16 := by decide
  have t19 : Nat.totient 19 = 18 := by decide
  have t21 : Nat.totient 21 = 12 := by decide
  have t22 : Nat.totient 22 = 10 := by decide
  have t23 : Nat.totient 23 = 22 := by decide
  norm_num [Finset.sum_insert, g0, t2, t3, t5, t6, t7, t10, t11, t13, t14, t15, t17, t19, t21,
    t22, t23]

/-- Interval M1: `X ∈ [8641/2, 33987/4]`, `R = 42`, `k = 12`. -/
theorem numM1 : ((12 : ℕ) : ℝ) * 0.6931471808 + (33987 / 4 : ℝ) / 2 / 2 ^ 12 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 42).filter Squarefree, g0 (8641 / 2 : ℝ) ((42 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 42).filter Squarefree =
    {1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29, 30, 31, 33, 34, 35, 37,
     38, 39, 41, 42} by decide +kernel]
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
  have t17 : Nat.totient 17 = 16 := by decide
  have t19 : Nat.totient 19 = 18 := by decide
  have t21 : Nat.totient 21 = 12 := by decide
  have t22 : Nat.totient 22 = 10 := by decide
  have t23 : Nat.totient 23 = 22 := by decide
  have t26 : Nat.totient 26 = 12 := by decide
  have t29 : Nat.totient 29 = 28 := by decide
  have t30 : Nat.totient 30 = 8 := by decide
  have t31 : Nat.totient 31 = 30 := by decide
  have t33 : Nat.totient 33 = 20 := by decide
  have t34 : Nat.totient 34 = 16 := by decide
  have t35 : Nat.totient 35 = 24 := by decide
  have t37 : Nat.totient 37 = 36 := by decide
  have t38 : Nat.totient 38 = 18 := by decide
  have t39 : Nat.totient 39 = 24 := by decide
  have t41 : Nat.totient 41 = 40 := by decide
  have t42 : Nat.totient 42 = 12 := by decide
  norm_num [Finset.sum_insert, g0, t2, t3, t5, t6, t7, t10, t11, t13, t14, t15, t17, t19, t21,
    t22, t23, t26, t29, t30, t31, t33, t34, t35, t37, t38, t39, t41, t42]

/-- Interval M2: `X ∈ [33987/4, 17760]`, `R = 43`, `k = 13`. -/
theorem numM2 : ((13 : ℕ) : ℝ) * 0.6931471808 + (17760 : ℝ) / 2 / 2 ^ 13 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 43).filter Squarefree, g0 (33987 / 4 : ℝ) ((43 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 43).filter Squarefree =
    {1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29, 30, 31, 33, 34, 35, 37,
     38, 39, 41, 42, 43} by decide +kernel]
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
  have t17 : Nat.totient 17 = 16 := by decide
  have t19 : Nat.totient 19 = 18 := by decide
  have t21 : Nat.totient 21 = 12 := by decide
  have t22 : Nat.totient 22 = 10 := by decide
  have t23 : Nat.totient 23 = 22 := by decide
  have t26 : Nat.totient 26 = 12 := by decide
  have t29 : Nat.totient 29 = 28 := by decide
  have t30 : Nat.totient 30 = 8 := by decide
  have t31 : Nat.totient 31 = 30 := by decide
  have t33 : Nat.totient 33 = 20 := by decide
  have t34 : Nat.totient 34 = 16 := by decide
  have t35 : Nat.totient 35 = 24 := by decide
  have t37 : Nat.totient 37 = 36 := by decide
  have t38 : Nat.totient 38 = 18 := by decide
  have t39 : Nat.totient 39 = 24 := by decide
  have t41 : Nat.totient 41 = 40 := by decide
  have t42 : Nat.totient 42 = 12 := by decide
  have t43 : Nat.totient 43 = 42 := by decide
  norm_num [Finset.sum_insert, g0, t2, t3, t5, t6, t7, t10, t11, t13, t14, t15, t17, t19, t21,
    t22, t23, t26, t29, t30, t31, t33, t34, t35, t37, t38, t39, t41, t42, t43]

/-- Interval M3: `X ∈ [17760, 35603]`, `R = 71`, `k = 14`. -/
theorem numM3 : ((14 : ℕ) : ℝ) * 0.6931471808 + (35603 : ℝ) / 2 / 2 ^ 14 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 71).filter Squarefree, g0 (17760 : ℝ) ((71 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 71).filter Squarefree =
    {1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29, 30, 31, 33, 34, 35, 37,
     38, 39, 41, 42, 43, 46, 47, 51, 53, 55, 57, 58, 59, 61, 62, 65, 66, 67, 69, 70,
     71} by decide +kernel]
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
  have t17 : Nat.totient 17 = 16 := by decide
  have t19 : Nat.totient 19 = 18 := by decide
  have t21 : Nat.totient 21 = 12 := by decide
  have t22 : Nat.totient 22 = 10 := by decide
  have t23 : Nat.totient 23 = 22 := by decide
  have t26 : Nat.totient 26 = 12 := by decide
  have t29 : Nat.totient 29 = 28 := by decide
  have t30 : Nat.totient 30 = 8 := by decide
  have t31 : Nat.totient 31 = 30 := by decide
  have t33 : Nat.totient 33 = 20 := by decide
  have t34 : Nat.totient 34 = 16 := by decide
  have t35 : Nat.totient 35 = 24 := by decide
  have t37 : Nat.totient 37 = 36 := by decide
  have t38 : Nat.totient 38 = 18 := by decide
  have t39 : Nat.totient 39 = 24 := by decide
  have t41 : Nat.totient 41 = 40 := by decide
  have t42 : Nat.totient 42 = 12 := by decide
  have t43 : Nat.totient 43 = 42 := by decide
  have t46 : Nat.totient 46 = 22 := by decide
  have t47 : Nat.totient 47 = 46 := by decide
  have t51 : Nat.totient 51 = 32 := by decide
  have t53 : Nat.totient 53 = 52 := by decide
  have t55 : Nat.totient 55 = 40 := by decide
  have t57 : Nat.totient 57 = 36 := by decide
  have t58 : Nat.totient 58 = 28 := by decide
  have t59 : Nat.totient 59 = 58 := by decide
  have t61 : Nat.totient 61 = 60 := by decide
  have t62 : Nat.totient 62 = 30 := by decide
  have t65 : Nat.totient 65 = 48 := by decide
  have t66 : Nat.totient 66 = 20 := by decide
  have t67 : Nat.totient 67 = 66 := by decide
  have t69 : Nat.totient 69 = 44 := by decide
  have t70 : Nat.totient 70 = 24 := by decide
  have t71 : Nat.totient 71 = 70 := by decide
  norm_num [Finset.sum_insert, g0, t2, t3, t5, t6, t7, t10, t11, t13, t14, t15, t17, t19, t21,
    t22, t23, t26, t29, t30, t31, t33, t34, t35, t37, t38, t39, t41, t42, t43, t46, t47, t51,
    t53, t55, t57, t58, t59, t61, t62, t65, t66, t67, t69, t70, t71]

/-- Interval M4: `X ∈ [35603, 71252]`, `R = 95`, `k = 15`. -/
theorem numM4 : ((15 : ℕ) : ℝ) * 0.6931471808 + (71252 : ℝ) / 2 / 2 ^ 15 - 1 ≤
    ∑ r ∈ (Finset.Icc 1 95).filter Squarefree, g0 (35603 : ℝ) ((95 : ℕ) : ℝ) r /
      Nat.totient r := by
  rw [show (Finset.Icc 1 95).filter Squarefree =
    {1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29, 30, 31, 33, 34, 35, 37,
     38, 39, 41, 42, 43, 46, 47, 51, 53, 55, 57, 58, 59, 61, 62, 65, 66, 67, 69, 70, 71, 73,
     74, 77, 78, 79, 82, 83, 85, 86, 87, 89, 91, 93, 94, 95} by decide +kernel]
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
  have t17 : Nat.totient 17 = 16 := by decide
  have t19 : Nat.totient 19 = 18 := by decide
  have t21 : Nat.totient 21 = 12 := by decide
  have t22 : Nat.totient 22 = 10 := by decide
  have t23 : Nat.totient 23 = 22 := by decide
  have t26 : Nat.totient 26 = 12 := by decide
  have t29 : Nat.totient 29 = 28 := by decide
  have t30 : Nat.totient 30 = 8 := by decide
  have t31 : Nat.totient 31 = 30 := by decide
  have t33 : Nat.totient 33 = 20 := by decide
  have t34 : Nat.totient 34 = 16 := by decide
  have t35 : Nat.totient 35 = 24 := by decide
  have t37 : Nat.totient 37 = 36 := by decide
  have t38 : Nat.totient 38 = 18 := by decide
  have t39 : Nat.totient 39 = 24 := by decide
  have t41 : Nat.totient 41 = 40 := by decide
  have t42 : Nat.totient 42 = 12 := by decide
  have t43 : Nat.totient 43 = 42 := by decide
  have t46 : Nat.totient 46 = 22 := by decide
  have t47 : Nat.totient 47 = 46 := by decide
  have t51 : Nat.totient 51 = 32 := by decide
  have t53 : Nat.totient 53 = 52 := by decide
  have t55 : Nat.totient 55 = 40 := by decide
  have t57 : Nat.totient 57 = 36 := by decide
  have t58 : Nat.totient 58 = 28 := by decide
  have t59 : Nat.totient 59 = 58 := by decide
  have t61 : Nat.totient 61 = 60 := by decide
  have t62 : Nat.totient 62 = 30 := by decide
  have t65 : Nat.totient 65 = 48 := by decide
  have t66 : Nat.totient 66 = 20 := by decide
  have t67 : Nat.totient 67 = 66 := by decide
  have t69 : Nat.totient 69 = 44 := by decide
  have t70 : Nat.totient 70 = 24 := by decide
  have t71 : Nat.totient 71 = 70 := by decide
  have t73 : Nat.totient 73 = 72 := by decide
  have t74 : Nat.totient 74 = 36 := by decide
  have t77 : Nat.totient 77 = 60 := by decide
  have t78 : Nat.totient 78 = 24 := by decide
  have t79 : Nat.totient 79 = 78 := by decide
  have t82 : Nat.totient 82 = 40 := by decide
  have t83 : Nat.totient 83 = 82 := by decide
  have t85 : Nat.totient 85 = 64 := by decide
  have t86 : Nat.totient 86 = 42 := by decide
  have t87 : Nat.totient 87 = 56 := by decide
  have t89 : Nat.totient 89 = 88 := by decide
  have t91 : Nat.totient 91 = 72 := by decide
  have t93 : Nat.totient 93 = 60 := by decide
  have t94 : Nat.totient 94 = 46 := by decide
  have t95 : Nat.totient 95 = 72 := by decide
  norm_num [Finset.sum_insert, g0, t2, t3, t5, t6, t7, t10, t11, t13, t14, t15, t17, t19, t21,
    t22, t23, t26, t29, t30, t31, t33, t34, t35, t37, t38, t39, t41, t42, t43, t46, t47, t51,
    t53, t55, t57, t58, t59, t61, t62, t65, t66, t67, t69, t70, t71, t73, t74, t77, t78, t79,
    t82, t83, t85, t86, t87, t89, t91, t93, t94, t95]

/-- **`WeightX` on `9093/4 ≤ X ≤ 71252`, PROVED** (5 intervals). -/
theorem weightX_mid (W X : ℝ) (hW : 117 ≤ W) (hX : 9093 / 4 ≤ X) (hX1 : X ≤ (71252 : ℝ)) :
    ∃ R : ℝ, 1 ≤ R ∧ R ≤ X / 2 ∧ R ^ 2 < 3.5 * X ∧
      Real.log (X / 2) ≤ ∑ r ∈ sqS R, gX W X R r / Nat.totient r := by
  rcases le_or_gt X (8641 / 2 : ℝ) with h0 | h0
  · exact interval (9093 / 4 : ℝ) (8641 / 2 : ℝ) 23 11 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) numM0 W X hW (by linarith) h0
  rcases le_or_gt X (33987 / 4 : ℝ) with h1 | h1
  · exact interval (8641 / 2 : ℝ) (33987 / 4 : ℝ) 42 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) numM1 W X hW (by linarith) h1
  rcases le_or_gt X (17760 : ℝ) with h2 | h2
  · exact interval (33987 / 4 : ℝ) (17760 : ℝ) 43 13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) numM2 W X hW (by linarith) h2
  rcases le_or_gt X (35603 : ℝ) with h3 | h3
  · exact interval (17760 : ℝ) (35603 : ℝ) 71 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) numM3 W X hW (by linarith) h3
  exact interval (35603 : ℝ) (71252 : ℝ) 95 15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) numM4 W X hW (by linarith) hX1


end Principia.Common.TernaryGoldbach.T2V
