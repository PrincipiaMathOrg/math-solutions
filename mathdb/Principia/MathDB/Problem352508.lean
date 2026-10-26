import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

set_option autoImplicit false

/-!
# MathDB 352508 — a log-convexity proof of the converse binomial inequality

Write-up: `mathdb-open-problems/problems/352508/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`.  It proves **Conjecture 3.2** of
Gerhold and Simon, with the sharp constant: for every positive integer `k`, every real
`α > 2` and `x, y ≥ 0`,

  `2^{α-1} ∑_{j=0}^k Γ(αk+1)/(Γ(αj+1)Γ(α(k-j)+1)) x^{αj} y^{α(k-j)} ≥ (x+y)^{αk}`.

Equivalently, with `p = x/(x+y)` and `S(t) = ∑_j binom(tk,tj) p^{tj}(1-p)^{t(k-j)}`,

  `S(α) ≥ ((1 + (2p-1)^{2k})/2)^{α-1} ≥ 2^{1-α}`.

## Where the content sits

The write-up's analytic work is **log-convexity of `S` on `(0,∞)`**, which rests on the
strict log-convexity of `t ↦ Γ(1+(A+B)t)/(Γ(1+At)Γ(1+Bt))` — proved there from the
trigamma series and a Laplace-integral positivity — plus "a positive finite sum of
log-convex functions is log-convex".  That is carried (`Setup.logConvex`).

Everything that converts log-convexity into the *sharp constant* is proved here:

* `anchor_one` — `S(1) = 1`, the binomial theorem.
* `even_part`, `sum_even_reindex`, `anchor_two` — `S(2) = (1 + (p-q)^{2k})/2`, the
  even-part identity.  `(p+q)^{2k} + (p-q)^{2k}` doubles exactly the even-index terms
  because `2k - i` is even iff `i` is, and the even indices of `range (2k+1)` are
  exactly `{2j : j ≤ k}`.
* `anchor_two_ge` — hence `S(2) ≥ 1/2`, with equality exactly at `p = 1/2`.
* `weights` — for `α > 2`, `2 = ((α-2)/(α-1))·1 + (1/(α-1))·α` with both weights in
  `[0,1]` and summing to `1`.  This is the *only* place `α > 2` is used.
* `three_point` — convexity of `log S` at those weights, together with `S(1) = 1`, gives
  `log S(2) ≤ (1/(α-1)) log S(α)`, i.e. `S(2)^{α-1} ≤ S(α)`.
* `final_bound` — and `S(2) ≥ 1/2` turns that into `2^{1-α} ≤ S(α)`, which is the
  conjecture.

## Scope

`Campaigns/MathDB-Formalization/verify_352508.py` checks both anchors in exact rationals,
the weights, the conclusion and the equality cases — and **audits the carry**, confirming
numerically that `(log S)'' ≥ 0` throughout and is strictly positive for `k ≥ 2`, which is
what the sharp form needs.
-/

namespace Principia.MathDB.P352508

open Finset

/-! ## Anchor one: `S(1) = 1` -/

/-- `∑_j C(k,j) pʲ q^{k-j} = 1` when `p + q = 1`. -/
theorem anchor_one (k : ℕ) {p q : ℝ} (hpq : p + q = 1) :
    ∑ j ∈ range (k + 1), (k.choose j : ℝ) * p ^ j * q ^ (k - j) = 1 := by
  have h := add_pow p q k
  rw [hpq, one_pow] at h
  rw [h]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ## Anchor two: the even part -/

/-- `(p+q)^{2k} + (p-q)^{2k}` doubles exactly the even-index terms. -/
theorem even_part (k : ℕ) (p q : ℝ) :
    (p + q) ^ (2 * k) + (p - q) ^ (2 * k)
      = 2 * ∑ i ∈ range (2 * k + 1),
          (if Even i then (Nat.choose (2 * k) i : ℝ) * p ^ i * q ^ (2 * k - i) else 0) := by
  rw [add_pow, sub_eq_add_neg, add_pow, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hi' : i ≤ 2 * k := by omega
  have hev : Even (2 * k) := ⟨k, by ring⟩
  have hiff : Even (2 * k - i) ↔ Even i := by
    rw [Nat.even_sub hi']
    simp [hev]
  by_cases he : Even i
  · have h2 : Even (2 * k - i) := hiff.mpr he
    rw [if_pos he, h2.neg_pow]
    ring
  · have h2 : ¬ Even (2 * k - i) := fun h => he (hiff.mp h)
    rw [if_neg he, (Nat.not_even_iff_odd.mp h2).neg_pow]
    ring

/-- The even indices of `range (2k+1)` are exactly `{2j : j ≤ k}`. -/
theorem sum_even_reindex (k : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ range (2 * k + 1), (if Even i then f i else 0)
      = ∑ j ∈ range (k + 1), f (2 * j) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun i => i / 2) (fun j => 2 * j) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    rw [Finset.mem_range]
    omega
  · intro a ha
    rw [Finset.mem_range] at ha
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ⟨a, by ring⟩⟩
  · intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨_, hev⟩ := ha
    obtain ⟨m, hm⟩ := hev
    omega
  · intro a _
    omega
  · intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨_, hev⟩ := ha
    obtain ⟨m, hm⟩ := hev
    congr 1
    omega

/-- **`S(2) = (1 + (p-q)^{2k})/2`.** -/
theorem anchor_two (k : ℕ) {p q : ℝ} (hpq : p + q = 1) :
    ∑ j ∈ range (k + 1),
        (Nat.choose (2 * k) (2 * j) : ℝ) * p ^ (2 * j) * q ^ (2 * k - 2 * j)
      = (1 + (p - q) ^ (2 * k)) / 2 := by
  have h := even_part k p q
  rw [hpq, one_pow] at h
  rw [sum_even_reindex k
    (fun i => (Nat.choose (2 * k) i : ℝ) * p ^ i * q ^ (2 * k - i))] at h
  linarith

theorem anchor_two_ge (k : ℕ) (p q : ℝ) : (1 : ℝ) / 2 ≤ (1 + (p - q) ^ (2 * k)) / 2 := by
  have h : (0 : ℝ) ≤ (p - q) ^ (2 * k) := by
    rw [pow_mul]
    positivity
  linarith

/-! ## The convex combination -/

/-- For `α > 2`, `2 = w·1 + (1-w)·α` with `w = (α-2)/(α-1) ∈ [0,1]`.  This is the only
place the hypothesis `α > 2` is used. -/
theorem weights {α : ℝ} (hα : 2 < α) :
    0 ≤ (α - 2) / (α - 1) ∧ (α - 2) / (α - 1) ≤ 1 ∧
      (α - 2) / (α - 1) + 1 / (α - 1) = 1 ∧
      (α - 2) / (α - 1) * 1 + 1 / (α - 1) * α = 2 := by
  have h1 : (0 : ℝ) < α - 1 := by linarith
  refine ⟨div_nonneg (by linarith) h1.le, ?_, ?_, ?_⟩
  · rw [div_le_one h1]; linarith
  · field_simp
    ring
  · field_simp
    ring

/-! ## The three-point step -/

/-- Convexity of `log S` at the weights above, with `S(1) = 1`, gives
`S(2)^{α-1} ≤ S(α)`. -/
theorem three_point {α S2 Sa : ℝ} (hα : 2 < α) (hS2 : 0 < S2) (hSa : 0 < Sa)
    (hconv : Real.log S2
      ≤ (α - 2) / (α - 1) * Real.log 1 + 1 / (α - 1) * Real.log Sa) :
    S2 ^ (α - 1) ≤ Sa := by
  have h1 : (0 : ℝ) < α - 1 := by linarith
  rw [Real.log_one, mul_zero, zero_add] at hconv
  have hmul : (α - 1) * Real.log S2 ≤ Real.log Sa := by
    have := mul_le_mul_of_nonneg_left hconv h1.le
    rw [← mul_assoc] at this
    rw [mul_one_div, div_self h1.ne', one_mul] at this
    exact this
  have hlog : Real.log (S2 ^ (α - 1)) ≤ Real.log Sa := by
    rw [Real.log_rpow hS2]
    exact hmul
  have hpos : 0 < S2 ^ (α - 1) := Real.rpow_pos_of_pos hS2 _
  exact (Real.log_le_log_iff hpos hSa).mp hlog

/-- **The conjecture**: `S(2) ≥ 1/2` upgrades the previous bound to `2^{1-α} ≤ S(α)`. -/
theorem final_bound {α S2 Sa : ℝ} (hα : 2 < α) (hS2 : (1 : ℝ) / 2 ≤ S2)
    (h : S2 ^ (α - 1) ≤ Sa) : (2 : ℝ) ^ (1 - α) ≤ Sa := by
  have h1 : (0 : ℝ) ≤ α - 1 := by linarith
  have hhalf : ((1 : ℝ) / 2) ^ (α - 1) ≤ S2 ^ (α - 1) :=
    Real.rpow_le_rpow (by norm_num) hS2 h1
  have hrw : ((1 : ℝ) / 2) ^ (α - 1) = (2 : ℝ) ^ (1 - α) := by
    rw [one_div, Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [hrw] at hhalf
  linarith

/-! ## The carried analytic input -/

/-- What the gamma-quotient lemma and the log-convexity of a positive finite sum give. -/
structure Setup where
  k : ℕ
  hk : 1 ≤ k
  p : ℝ
  q : ℝ
  hpq : p + q = 1
  /-- `S t = ∑_j binom(tk, tj) p^{tj} q^{t(k-j)}` -/
  S : ℝ → ℝ
  hSpos : ∀ t : ℝ, 0 < t → 0 < S t
  /-- the two anchors, at the integer points where the gamma binomial is the ordinary one -/
  hS1 : S 1 = ∑ j ∈ range (k + 1), (k.choose j : ℝ) * p ^ j * q ^ (k - j)
  hS2 : S 2 = ∑ j ∈ range (k + 1),
    (Nat.choose (2 * k) (2 * j) : ℝ) * p ^ (2 * j) * q ^ (2 * k - 2 * j)
  /-- **CARRIED** (the gamma-quotient lemma plus log-convexity of a positive finite sum):
  `log ∘ S` is convex on `(0, ∞)`, applied at the three points `1`, `2`, `α`. -/
  logConvex : ∀ α : ℝ, 2 < α →
    Real.log (S 2) ≤ (α - 2) / (α - 1) * Real.log (S 1) + 1 / (α - 1) * Real.log (S α)

namespace Setup

variable (T : Setup)

theorem S1_eq : T.S 1 = 1 := by rw [T.hS1, anchor_one T.k T.hpq]

theorem S2_eq : T.S 2 = (1 + (T.p - T.q) ^ (2 * T.k)) / 2 := by
  rw [T.hS2, anchor_two T.k T.hpq]

theorem S2_ge : (1 : ℝ) / 2 ≤ T.S 2 := by
  rw [T.S2_eq]
  exact anchor_two_ge T.k T.p T.q

theorem S2_pos : 0 < T.S 2 := lt_of_lt_of_le (by norm_num) T.S2_ge

/-- **THE REFINEMENT**: `S(α) ≥ S(2)^{α-1}`. -/
theorem refined {α : ℝ} (hα : 2 < α) : T.S 2 ^ (α - 1) ≤ T.S α := by
  have hSa : 0 < T.S α := T.hSpos α (by linarith)
  have hc := T.logConvex α hα
  rw [T.S1_eq] at hc
  exact three_point hα T.S2_pos hSa hc

/-- **GERHOLD–SIMON CONJECTURE 3.2**, with the sharp constant `2^{α-1}`. -/
theorem conjecture {α : ℝ} (hα : 2 < α) : (2 : ℝ) ^ (1 - α) ≤ T.S α :=
  final_bound hα T.S2_ge (T.refined hα)

end Setup

end Principia.MathDB.P352508
