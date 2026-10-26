import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# MathDB 336698 — the gamma-quotient monotonicity conjecture

Write-up: `mathdb-open-problems/problems/336698/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`, "A gamma quotient with strict
logarithmic complete monotonicity".  It resolves **Conjecture 3.14** of Arora and Sahoo,
*Involve* **11**(4) (2018) 625–641, p. 635:

  `Q_a(c) = Γ(c)Γ(c-4) / (Γ(c-a)Γ(c+a-1))` decreases on `c > 4`, for every `0 ≤ a ≤ 1`.

## A different route from the write-up's, on purpose

The write-up proves the stronger statement that `log Q_a` is **completely monotone**, using
the digamma *integral* representation and a convexity argument on `a ↦ e^{at} + e^{(1-a)t}`.
The higher derivatives need **polygamma**, which Mathlib does not have (confirmed on the
2026-09-22 special-function sweep).

But the conjecture is only the **first** derivative, and that is reachable from the digamma
*series*.  With `ψ(u) - ψ(v) = ∑_{k≥0} (1/(k+v) - 1/(k+u))` and
`-d/dc log Q_a = [ψ(c-a) - ψ(c)] + [ψ(c+a-1) - ψ(c-4)]`,

  `-d/dc log Q_a(c) = ∑_{k≥0} f a (k+c)`,
  `f a u = 1/u - 1/(u-a) + 1/(u-4) - 1/(u+a-1)`.

## And `f` is elementary

Pairing the terms the other way,

  `f a u = -a/(u(u-a)) + (a+3)/((u-4)(u+a-1))`,

so on `u > 4`, `-3 ≤ a ≤ 4` — where all four denominators are positive — `f a u > 0` is
equivalent, after clearing denominators, to

  `quad a u = 3u² - 2s·u + 4s > 0`,  `s = a(a-1)`.

`quad a u - 3(u-4)² = (12 - s)(2u - 4)`, and `s = a(a-1) ≤ 12` on `[-3,4]`, so
`quad a u ≥ 3(u-4)² > 0`.  **That is the entire proof** — no polygamma, no integral.

## What is carried

`Setup` carries exactly the digamma series, in the form the argument uses: that
`∑_k f a (k+c)` converges and is `-logQ'(c)`.  That identity is classical (DLMF 5.9) and
absent from Mathlib — `Complex.digamma` exists but the file is 64 lines holding only
`digamma = logDeriv Gamma`, three special values, the functional equation and meromorphy,
with a TODO saying Gauss's integral representation is unproved.

## Scope

The module proves the result for `-3 ≤ a ≤ 4`, strictly wider than the conjecture's
`0 ≤ a ≤ 1`, matching the write-up's range.  `Campaigns/MathDB-Formalization/verify_336698.py`
checks the algebra exactly and confirms numerically that the series really is the
logarithmic derivative — its truncation gap after `N` terms matches the predicted `3/N`,
since `f a u ~ 3/u²`.  That `1/N` convergence is presumably why the write-up reached for
the integral form.
-/

namespace Principia.MathDB.P336698

open Set

/-- One term of the digamma-difference series for `-d/dc log Q_a`. -/
noncomputable def f (a u : ℝ) : ℝ := 1 / u - 1 / (u - a) + 1 / (u - 4) - 1 / (u + a - 1)

/-- The quadratic that decides the sign of `f`. -/
noncomputable def quad (a u : ℝ) : ℝ := 3 * u ^ 2 - 2 * (a * (a - 1)) * u + 4 * (a * (a - 1))

theorem u_pos {u : ℝ} (hu : 4 < u) : 0 < u := by linarith

theorem u_sub_a_pos {a u : ℝ} (ha' : a ≤ 4) (hu : 4 < u) : 0 < u - a := by linarith

theorem u_sub_four_pos {u : ℝ} (hu : 4 < u) : 0 < u - 4 := by linarith

theorem u_add_a_pos {a u : ℝ} (ha : -3 ≤ a) (hu : 4 < u) : 0 < u + a - 1 := by linarith

/-- `s = a(a-1) ≤ 12` on `[-3,4]`, because `(a+3)(a-4) ≤ 0` there. -/
theorem s_le_twelve {a : ℝ} (ha : -3 ≤ a) (ha' : a ≤ 4) : a * (a - 1) ≤ 12 := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a + 3) (by linarith : (0:ℝ) ≤ 4 - a)]

theorem quad_sub {a u : ℝ} : quad a u - 3 * (u - 4) ^ 2 = (12 - a * (a - 1)) * (2 * u - 4) := by
  unfold quad; ring

theorem quad_ge {a u : ℝ} (ha : -3 ≤ a) (ha' : a ≤ 4) (hu : 4 < u) :
    3 * (u - 4) ^ 2 ≤ quad a u := by
  have h := quad_sub (a := a) (u := u)
  have h1 : (0:ℝ) ≤ 12 - a * (a - 1) := by linarith [s_le_twelve ha ha']
  have h2 : (0:ℝ) ≤ 2 * u - 4 := by linarith
  nlinarith [mul_nonneg h1 h2]

theorem quad_pos {a u : ℝ} (ha : -3 ≤ a) (ha' : a ≤ 4) (hu : 4 < u) : 0 < quad a u := by
  have h : (0:ℝ) < 3 * (u - 4) ^ 2 := by positivity
  linarith [quad_ge ha ha' hu]

/-- The pairing that makes `f` elementary. -/
theorem f_eq_div {a u : ℝ} (ha : -3 ≤ a) (ha' : a ≤ 4) (hu : 4 < u) :
    f a u = quad a u / (u * (u - a) * ((u - 4) * (u + a - 1))) := by
  have h0 : u ≠ 0 := (u_pos hu).ne'
  have h1 : u - a ≠ 0 := (u_sub_a_pos ha' hu).ne'
  have h2 : u - 4 ≠ 0 := (u_sub_four_pos hu).ne'
  have h3 : u + a - 1 ≠ 0 := (u_add_a_pos ha hu).ne'
  unfold f quad
  field_simp
  ring

/-- **Every term of the series is strictly positive.** -/
theorem f_pos {a u : ℝ} (ha : -3 ≤ a) (ha' : a ≤ 4) (hu : 4 < u) : 0 < f a u := by
  rw [f_eq_div ha ha' hu]
  have hd : 0 < u * (u - a) * ((u - 4) * (u + a - 1)) :=
    mul_pos (mul_pos (u_pos hu) (u_sub_a_pos ha' hu))
      (mul_pos (u_sub_four_pos hu) (u_add_a_pos ha hu))
  exact div_pos (quad_pos ha ha' hu) hd

/-! ## The carried half -/

/-- The digamma series, in the form the argument uses.  `logQ` is `log Q_a`. -/
structure Setup where
  a : ℝ
  ha : -3 ≤ a
  ha' : a ≤ 4
  logQ : ℝ → ℝ
  /-- `∑_k f a (k+c)` converges for `c > 4`. -/
  hsum : ∀ c : ℝ, 4 < c → Summable (fun k : ℕ => f a (k + c))
  /-- and equals `-logQ'(c)` — the digamma difference formula, DLMF 5.9. -/
  hderiv : ∀ c : ℝ, 4 < c → HasDerivAt logQ (-(∑' k : ℕ, f a (k + c))) c

namespace Setup

variable (S : Setup)

theorem series_pos {c : ℝ} (hc : 4 < c) : 0 < ∑' k : ℕ, f S.a (k + c) := by
  refine (S.hsum c hc).tsum_pos (fun k => ?_) 0 ?_
  · have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    exact (f_pos S.ha S.ha' (by linarith)).le
  · have : ((0 : ℕ) : ℝ) + c = c := by norm_num
    rw [this]
    exact f_pos S.ha S.ha' hc

/-- **`log Q_a` is strictly decreasing on `(4, ∞)`** — the conjecture. -/
theorem logQ_strictAntiOn : StrictAntiOn S.logQ (Ioi 4) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 4) ?_ ?_
  · intro x hx
    exact ((S.hderiv x hx).differentiableAt).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(S.hderiv x hx).deriv]
    simpa using S.series_pos hx

end Setup

/-! ## The conjecture -/

/-- Arora–Sahoo Conjecture 3.14 for `Q_a = exp (log Q_a)`. -/
theorem Q_strictAntiOn (S : Setup) (Q : ℝ → ℝ) (hQ : ∀ c, Q c = Real.exp (S.logQ c)) :
    StrictAntiOn Q (Ioi 4) := by
  intro x hx y hy hxy
  rw [hQ, hQ]
  exact Real.exp_lt_exp.mpr (S.logQ_strictAntiOn hx hy hxy)

/-- The conjecture's own parameter range sits inside the one proved. -/
theorem conj_range_included {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : -3 ≤ a ∧ a ≤ 4 :=
  ⟨by linarith, by linarith⟩

end Principia.MathDB.P336698
