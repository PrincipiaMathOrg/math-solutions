import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

/-!
# MathDB 325512 — the generalized `arcsinh_p` is not concave in `p`

Write-up: `mathdb-open-problems/problems/325512/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`, "Parameter concavity of the
generalized inverse hyperbolic sine".  It refutes **Conjecture 2.4** of Baricz, Bhayo and
Vuorinen, which asserts that for each fixed `0 < x < 1` the function

  `F x p = arcsinh_p x = ∫₀ˣ (1 + tᵖ)^(-1/p) dt`

is strictly concave in `p` on `(0, ∞)`.

## The witness

`x = 1/4`, and the three parameters `p₋ = 1/32`, `p₀ = 1/16`, `p₊ = 3/32`, with `p₀` the
exact midpoint of `p₋` and `p₊`.  The write-up's chain is

  `F (1/4) p₀ < 1/65536 < 1/16384 < (F (1/4) p₋ + F (1/4) p₊)/2`,

which contradicts concavity.  All three parameters are in `(0, ∞)` and `1/4 ∈ (0,1)`, so
the witness satisfies the conjecture's own hypotheses — `conj_hypotheses` records that.

## The two bounds, which are the only analysis here

* **Upper** (`g_le`, `F_le`).  AM-GM gives `1 + tᵖ ≥ 2·t^(p/2)`, and `u ↦ u^(-1/p)` is
  decreasing, so `(1 + tᵖ)^(-1/p) ≤ 2^(-1/p)·t^(-1/2)`.  Integrating,
  `F x p ≤ 2^(-1/p)·2√x`, which at `x = 1/4` is exactly `2^(-1/p)`.
  **The write-up proves this bound strict; this module deliberately proves only the
  non-strict form**, because `F p₀ ≤ 2⁻¹⁶ < 2⁻¹⁴ < avg` already yields `F p₀ < avg`.
  Dropping strictness removes the AM-GM equality-case argument entirely.
* **Lower** (`g_ge`, `F_ge`).  For `0 ≤ t ≤ 1` we have `tᵖ ≤ 1`, so `1 + tᵖ ≤ 2` and
  `(1 + tᵖ)^(-1/p) ≥ 2^(-1/p)`.  Integrating over a length-`x` interval, `F x p ≥ x·2^(-1/p)`.
  At `x = 1/4`, `p = 3/32` this is `(1/4)·2^(-32/3) > (1/4)·2⁻¹¹ = 2⁻¹³`, the inequality
  being nothing but `32/3 < 11`.

Only `F p₋ ≥ 0` is needed from `p₋`.

## Why the majorant forces a restricted comparison

`2^(-1/p)·t^(-1/2)` is **singular at `t = 0`**, where `Real.rpow` returns `0` while the
integrand equals `1`; so the pointwise bound is false at the single point `0` and
`integral_mono_on` over `Icc` does not apply.  The comparison is therefore made on
`Ioc 0 x` via `setIntegral_mono_on`, after `intervalIntegral.integral_of_le`.  The
majorant is still interval-integrable there because `-1/2 > -1`
(`intervalIntegrable_rpow'`).

## Scope (the 215 check)

The write-up distinguishes two versions of the conjecture: the **published** one on
`0 < x < 1` (false — refuted here) and a **narrower** survey version restricted to
`p > 1` (true, and proved in the source's Theorem 3).  All three parameters used here are
below `1`, so **this module says nothing about the `p > 1` statement**; `params_lt_one`
records that explicitly so the scope cannot be misread.  `Conj` is stated as plain
`ConcaveOn`, the weakest reading the witness kills — refuting it refutes the source's
strict form a fortiori.

Python check: `Campaigns/MathDB-Formalization/verify_325512.py`.
-/

namespace Principia.MathDB.P325512

open MeasureTheory intervalIntegral Set

/-- The integrand `(1 + tᵖ)^(-1/p)`. -/
noncomputable def g (p t : ℝ) : ℝ := (1 + t ^ p) ^ (-(1 / p))

/-- `F x p = arcsinh_p x`. -/
noncomputable def F (x p : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, g p t

theorem one_add_rpow_pos (p t : ℝ) (ht : 0 ≤ t) : 0 < 1 + t ^ p := by
  have : 0 ≤ t ^ p := Real.rpow_nonneg ht p
  linarith

theorem g_pos (p t : ℝ) (ht : 0 ≤ t) : 0 < g p t :=
  Real.rpow_pos_of_pos (one_add_rpow_pos p t ht) _

theorem g_continuousOn (p x : ℝ) (hp : 0 < p) : ContinuousOn (g p) (Icc 0 x) := by
  have h1 : ContinuousOn (fun t : ℝ => 1 + t ^ p) (Icc 0 x) :=
    (continuous_const.add (Real.continuous_rpow_const hp.le)).continuousOn
  exact h1.rpow_const fun t ht => Or.inl (one_add_rpow_pos p t ht.1).ne'

theorem g_intervalIntegrable (p x : ℝ) (hp : 0 < p) (hx : 0 ≤ x) :
    IntervalIntegrable (g p) volume 0 x :=
  (g_continuousOn p x hp).intervalIntegrable_of_Icc hx

/-! ## The upper bound -/

/-- AM-GM: `1 + tᵖ ≥ 2·t^(p/2)`, the only inequality behind the upper bound. -/
theorem amgm (p t : ℝ) (ht : 0 ≤ t) : 2 * t ^ (p / 2) ≤ 1 + t ^ p := by
  have hs : (0 : ℝ) ≤ t ^ (p / 2) := Real.rpow_nonneg ht _
  have hsq : t ^ p = (t ^ (p / 2)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (t ^ (p / 2)) 2, ← Real.rpow_mul ht]
    norm_num
  nlinarith [sq_nonneg (t ^ (p / 2) - 1)]

theorem g_le (p t : ℝ) (hp : 0 < p) (ht : 0 < t) :
    g p t ≤ (2 : ℝ) ^ (-(1 / p)) * t ^ (-(1 : ℝ) / 2) := by
  have hbase : 0 < 2 * t ^ (p / 2) := by
    have : 0 < t ^ (p / 2) := Real.rpow_pos_of_pos ht _
    linarith
  have hmono : (1 + t ^ p) ^ (-(1 / p)) ≤ (2 * t ^ (p / 2)) ^ (-(1 / p)) :=
    Real.rpow_le_rpow_of_nonpos hbase (amgm p t ht.le) (neg_nonpos.mpr (by positivity))
  refine hmono.trans_eq ?_
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le]
  congr 1
  field_simp

theorem F_le (x p : ℝ) (hx : 0 < x) (hp : 0 < p) :
    F x p ≤ (2 : ℝ) ^ (-(1 / p)) * (2 * Real.sqrt x) := by
  have hmaj : IntervalIntegrable (fun t : ℝ => (2 : ℝ) ^ (-(1 / p)) * t ^ (-(1 : ℝ) / 2))
      volume 0 x :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  have hval : ∫ t in (0 : ℝ)..x, (2 : ℝ) ^ (-(1 / p)) * t ^ (-(1 : ℝ) / 2)
      = (2 : ℝ) ^ (-(1 / p)) * (2 * Real.sqrt x) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
      Real.sqrt_eq_rpow]
    norm_num
    ring_nf
    tauto
  rw [F, ← hval, intervalIntegral.integral_of_le hx.le,
    intervalIntegral.integral_of_le hx.le]
  refine MeasureTheory.setIntegral_mono_on
    ((g_intervalIntegrable p x hp hx.le).1) (hmaj.1) measurableSet_Ioc fun t ht => ?_
  exact g_le p t hp ht.1

/-! ## The lower bound -/

theorem g_ge (p t : ℝ) (hp : 0 < p) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (2 : ℝ) ^ (-(1 / p)) ≤ g p t := by
  have h1 : t ^ p ≤ 1 := Real.rpow_le_one ht ht1 hp.le
  exact Real.rpow_le_rpow_of_nonpos (one_add_rpow_pos p t ht) (by linarith)
    (neg_nonpos.mpr (by positivity))

theorem F_ge (x p : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (hp : 0 < p) :
    x * (2 : ℝ) ^ (-(1 / p)) ≤ F x p := by
  have hconst : ∫ _t in (0 : ℝ)..x, (2 : ℝ) ^ (-(1 / p)) = x * (2 : ℝ) ^ (-(1 / p)) := by
    rw [intervalIntegral.integral_const]
    simp
  rw [F, ← hconst]
  refine intervalIntegral.integral_mono_on hx.le intervalIntegral.intervalIntegrable_const
    (g_intervalIntegrable p x hp hx.le) fun t ht => ?_
  exact g_ge p t hp ht.1 (le_trans ht.2 hx1)

theorem F_nonneg (x p : ℝ) (hx : 0 < x) : 0 ≤ F x p := by
  rw [F]
  refine intervalIntegral.integral_nonneg hx.le fun t ht => ?_
  exact (g_pos p t ht.1).le

/-! ## The three values -/

theorem F_p_zero : F (1 / 4) (1 / 16) ≤ 1 / 65536 := by
  have h := F_le (1 / 4) (1 / 16) (by norm_num) (by norm_num)
  have hs : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h2 : (2 : ℝ) ^ (-(1 / (1 / 16 : ℝ))) = 1 / 65536 := by
    rw [show -(1 / (1 / 16 : ℝ)) = ((-16 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  rw [hs, h2] at h
  linarith

theorem F_p_plus : 1 / 8192 < F (1 / 4) (3 / 32) := by
  have h := F_ge (1 / 4) (3 / 32) (by norm_num) (by norm_num) (by norm_num)
  have hkey : (2 : ℝ) ^ (-(11 : ℝ)) < (2 : ℝ) ^ (-(1 / (3 / 32 : ℝ))) := by
    refine Real.rpow_lt_rpow_left_iff (by norm_num) |>.mpr ?_
    norm_num
  have h11 : (2 : ℝ) ^ (-(11 : ℝ)) = 1 / 2048 := by
    rw [show -(11 : ℝ) = ((-11 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  rw [h11] at hkey
  linarith

theorem F_p_minus : 0 ≤ F (1 / 4) (1 / 32) := F_nonneg _ _ (by norm_num)

/-! ## The refutation -/

/-- Conjecture 2.4 of Baricz–Bhayo–Vuorinen, in the weakest reading the witness kills:
`p ↦ arcsinh_p x` is concave (not necessarily strictly) on `(0, ∞)`. -/
def Conj (x : ℝ) : Prop := ConcaveOn ℝ (Ioi (0 : ℝ)) (fun p => F x p)

/-- The witness lies inside the conjecture's own hypotheses. -/
theorem conj_hypotheses :
    (0 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) < 1 ∧ (1 / 32 : ℝ) ∈ Ioi (0 : ℝ) ∧
      (1 / 16 : ℝ) ∈ Ioi (0 : ℝ) ∧ (3 / 32 : ℝ) ∈ Ioi (0 : ℝ) ∧
      (1 / 16 : ℝ) = (1 / 2) * (1 / 32) + (1 / 2) * (3 / 32) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- All three parameters are below `1`, so the narrower survey conjecture on `p > 1`
(which the source proves TRUE) is untouched by this refutation. -/
theorem params_lt_one :
    (1 / 32 : ℝ) < 1 ∧ (1 / 16 : ℝ) < 1 ∧ (3 / 32 : ℝ) < 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **Conjecture 2.4 is false at `x = 1/4`.** -/
theorem not_conj : ¬ Conj (1 / 4) := by
  intro h
  have hmid := h.2 (by norm_num : (1 / 32 : ℝ) ∈ Ioi (0 : ℝ))
    (by norm_num : (3 / 32 : ℝ) ∈ Ioi (0 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [show (1 / 2 : ℝ) • (1 / 32 : ℝ) + (1 / 2 : ℝ) • (3 / 32 : ℝ) = 1 / 16 by
    simp only [smul_eq_mul]; norm_num] at hmid
  simp only [smul_eq_mul] at hmid
  have h1 := F_p_zero
  have h2 := F_p_plus
  have h3 := F_p_minus
  linarith

end Principia.MathDB.P325512
