/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIWeightXMid

set_option autoImplicit false

/-!
# `T2V.WeightX` and `T2X.Garn1a` from Montgomery–Vaughan's Lemma 8 above `R = 100`

Above `X = 71252` take `R = (7X/23)^{1/2}` (`≥ 147`), the book's `R = (σW/q)^{1/2}` with
`σ = 7/23`, chosen so that `3σ/(1 − σ/3.5) = 1` exactly. Then for `r ≤ R`,
`(3/2)·rR/(X − rR/3.5) ≤ r/2R ≤ aW·r/R`, so `gX(r) ≥ aW⁻¹(1 + r/R)⁻¹`, and Lemma 8 gives
`∑ ≥ aW⁻¹(log R + 0.25068)`. The book's `+1/2` deficit (`N ≤ (W + 1)/2`, not `W/2`) is the
`aW = (W + 1)/2W` here; it costs `log(X/2)/W ≤ 1.6·10⁻⁴`, against a slack of
`0.50136 − log(23/14) ≥ 0.0049`.

```
 MV8Large        NAMED literature: Montgomery–Vaughan 1973 Lemma 8, as invoked by Helfgott
 weightX_large   WeightX for X ≥ 71252, from MV8Large                             PROVED
 weightX_of_mv8  MV8Large → T2V.WeightX  (with weightX_small, weightX_mid)        PROVED
 weightLB_of_mv8 MV8Large → T2G.WeightLB                                          PROVED
 garn1a_of_mv8   MontgomeryIneq → MVWeighted → MV8Large → T2X.Garn1a              PROVED
```

`HC.MV8SmallCited` is NOT used: the range `R < 100` is covered by the kernel-checked intervals
of `TypeIIWeightXSmall` / `TypeIIWeightXMid`. No computation is cited.
-/

namespace Principia.Common.TernaryGoldbach.T2V

open Principia.Common.TernaryGoldbach.T2G

/-- **NAMED (literature) — Montgomery–Vaughan, Lemma 8 above `100`**, in the form Helfgott
invokes it (`minarcs.tex` 3524-3527, arXiv:1205.5252, proof of `lem:kastor1`): "For `R ≥ 2`,
`∑_{r ≤ R} (1 + r R⁻¹)⁻¹ μ(r)²/φ(r) > log R + 0.25068`; this is true for `R ≥ 100` by
[MR0374060, Lemma 8]" (H. L. Montgomery and R. C. Vaughan, *The large sieve*, Mathematika 20
(1973), 119-134). Only the range `R ≥ 100` is stated. The verbatim text of MV's Lemma 8 has
NOT been checked against this transcription (see the round report). -/
def MV8Large : Prop :=
  ∀ R : ℝ, 100 ≤ R →
    Real.log R + 0.25068 < ∑ r ∈ Finset.Icc 1 ⌊R⌋₊,
      (1 + (r : ℝ) / R)⁻¹ * (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (r.totient : ℝ))

/-- The Lemma-8 sum over square-free `r` only. -/
theorem mv8_sum_eq (R : ℝ) :
    ∑ r ∈ Finset.Icc 1 ⌊R⌋₊,
        (1 + (r : ℝ) / R)⁻¹ * (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (r.totient : ℝ)) =
      ∑ r ∈ sqS R, (1 + (r : ℝ) / R)⁻¹ / Nat.totient r := by
  unfold sqS
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : Squarefree r
  · have hm := ArithmeticFunction.moebius_sq_eq_one_of_squarefree h
    have hm' : ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast hm
    rw [if_pos h, hm']
    ring
  · rw [if_neg h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
    simp

/-- **`WeightX` above `X = 71252`, PROVED** from `MV8Large`. -/
theorem weightX_large (mv8 : MV8Large) (W X : ℝ) (hW : 117 ≤ W) (hX : 71252 ≤ X)
    (hXW : X ≤ W) :
    ∃ R : ℝ, 1 ≤ R ∧ R ≤ X / 2 ∧ R ^ 2 < 3.5 * X ∧
      Real.log (X / 2) ≤ ∑ r ∈ sqS R, gX W X R r / Nat.totient r := by
  have hW0 : 0 < W := by linarith
  have hX0 : 0 < X := by linarith
  set R := Real.sqrt (7 * X / 23) with hRdef
  have hR2 : R ^ 2 = 7 * X / 23 := Real.sq_sqrt (by positivity)
  have hR0 : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hR100 : 100 ≤ R := by
    rw [hRdef, show (100 : ℝ) = Real.sqrt (100 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hRX : R ≤ X / 2 := by nlinarith
  refine ⟨R, by linarith, hRX, by rw [hR2]; norm_num; linarith, ?_⟩
  set aW := (W + 1) / (2 * W) with haW
  have haW0 : 0 < aW := by positivity
  have haW2 : 1 / 2 ≤ aW := by
    rw [haW, div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  -- (A) the term bound `gX(r) ≥ (aW(1 + r/R))⁻¹`
  have hterm : ∀ r ∈ sqS R, (aW * (1 + (r : ℝ) / R))⁻¹ / Nat.totient r ≤
      gX W X R r / Nat.totient r := by
    intro r hr
    have hrI := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hrR : (r : ℝ) ≤ R := le_trans (Nat.cast_le.mpr hrI.2) (Nat.floor_le hR0.le)
    have hrR2 : (r : ℝ) * R ≤ R ^ 2 := by nlinarith
    have hXR : X = 23 / 7 * R ^ 2 := by linarith
    have hden : 21 * X / 23 ≤ X - r * R / 3.5 := by
      rw [show (3.5 : ℝ) = 7 / 2 by norm_num]
      nlinarith
    have hden0 : 0 < 21 * X / 23 := by positivity
    have h1 : (r : ℝ) * R / (X - r * R / 3.5) ≤ r * R / (21 * X / 23) :=
      div_le_div_of_nonneg_left (by positivity) hden0 hden
    have h2 : 3 / 2 * ((r : ℝ) * R / (21 * X / 23)) = r / (2 * R) := by
      rw [hXR]
      field_simp
      ring
    have h3 : (r : ℝ) / (2 * R) ≤ aW * (r / R) := by
      rw [show (r : ℝ) / (2 * R) = 1 / 2 * (r / R) by field_simp]
      exact mul_le_mul_of_nonneg_right haW2 (by positivity)
    have hD : aW + 3 / 2 * ((r : ℝ) * R / (X - r * R / 3.5)) ≤ aW * (1 + r / R) := by
      have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3 / 2)
      nlinarith
    have hDpos : 0 < aW + 3 / 2 * ((r : ℝ) * R / (X - r * R / 3.5)) :=
      add_pos_of_pos_of_nonneg haW0
        (mul_nonneg (by norm_num) (div_nonneg (by positivity) (by linarith)))
    exact div_le_div_of_nonneg_right (inv_anti₀ hDpos hD) (Nat.cast_nonneg _)
  -- (B) Lemma 8
  have h8 := mv8 R hR100
  rw [mv8_sum_eq, show (0.25068 : ℝ) = 6267 / 25000 by norm_num] at h8
  have hsum : ∑ r ∈ sqS R, (aW * (1 + (r : ℝ) / R))⁻¹ / Nat.totient r =
      aW⁻¹ * ∑ r ∈ sqS R, (1 + (r : ℝ) / R)⁻¹ / Nat.totient r := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_inv]
    ring
  -- (C) the logarithms
  set L := Real.log (X / 2) with hL
  have hlogR : Real.log R = (L - Real.log (23 / 14)) / 2 := by
    rw [hRdef, Real.log_sqrt (by positivity), hL, ← Real.log_div (by positivity) (by norm_num)]
    congr 2
    field_simp
    ring
  have hz : Real.log (23 / 14) ≤ 9929 / 20000 := by
    have h7 : Real.log ((23 / 14 : ℝ) ^ 7) = 7 * Real.log (23 / 14) := by
      rw [Real.log_pow]
      norm_num
    have hk := log_le_k ((23 / 14 : ℝ) ^ 7) (by positivity) 5
    rw [h7] at hk
    norm_num at hk
    linarith
  have hLW : L ≤ 157 / 1000000 * W := by
    have hk := log_le_k W hW0 16
    have hLle : L ≤ Real.log W := Real.log_le_log (by positivity) (by linarith)
    norm_num at hk ⊢
    linarith
  have hgoal : aW * L ≤ Real.log R + 6267 / 25000 := by
    have e : aW * L = L / 2 + L / (2 * W) := by
      rw [haW]
      field_simp
    have hq : L / (2 * W) ≤ 157 / 2000000 := by
      rw [div_le_iff₀ (by positivity)]
      norm_num at hLW
      linarith
    rw [e, hlogR]
    linarith
  have hfin : L ≤ aW⁻¹ * (Real.log R + 6267 / 25000) := by
    rw [le_inv_mul_iff₀ haW0]
    exact hgoal
  calc L ≤ aW⁻¹ * (Real.log R + 6267 / 25000) := hfin
    _ ≤ aW⁻¹ * ∑ r ∈ sqS R, (1 + (r : ℝ) / R)⁻¹ / Nat.totient r :=
        mul_le_mul_of_nonneg_left h8.le (inv_nonneg.mpr haW0.le)
    _ = ∑ r ∈ sqS R, (aW * (1 + (r : ℝ) / R))⁻¹ / Nat.totient r := hsum.symm
    _ ≤ _ := Finset.sum_le_sum hterm

/-- **`T2V.WeightX` from `MV8Large`, PROVED** (`weightX_small`, `weightX_mid`,
`weightX_large`). -/
theorem weightX_of_mv8 (mv8 : MV8Large) : WeightX := by
  intro W X hW hX hXW
  rcases le_or_gt X (9093 / 4) with h1 | h1
  · exact weightX_small W X hW hX h1
  rcases le_or_gt X 71252 with h2 | h2
  · exact weightX_mid W X hW h1.le h2
  exact weightX_large mv8 W X hW h2.le hXW

/-- **`T2G.WeightLB` from `MV8Large`, PROVED**. -/
theorem weightLB_of_mv8 (mv8 : MV8Large) : WeightLB :=
  weightLB_of_X (weightX_of_mv8 mv8)

/-- **`T2X.Garn1a` from Montgomery's inequality, the weighted large sieve and MV Lemma 8,
PROVED** — exactly the book's three literature inputs, with no cited computation. -/
theorem garn1a_of_mv8 (mi : T2M.MontgomeryIneq) (mv : MVWeighted) (mv8 : MV8Large) :
    Principia.Common.TernaryGoldbach.T2X.Garn1a :=
  garn1a_of_X mi mv (weightX_of_mv8 mv8)

end Principia.Common.TernaryGoldbach.T2V
