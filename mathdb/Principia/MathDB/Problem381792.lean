/-
MathDB #381792 — high-frequency characteristic roots and diffusive boundary feedback.

The write-up settles Conjecture 2 of Bastin–Coron–Hayat for the scalar transport–diffusion
feedback system: for every `ε > 0` there is `η₁ > 0` with `σ_η > −ε` whenever `0 < η < η₁`.
It does so by proving something stronger and `η`-uniform — that for **every fixed** `η > 0`
there are characteristic roots `s_k = i(2k+1)π + o(1)`, whence `σ_η ≥ 0`.

WHAT IS PROVED HERE.  The write-up's engine is Rouché's theorem on small disks around
`iω_k = i(2k+1)π`, and Rouché needs exactly two quantitative inputs plus one counting fact.
This module proves the elementary ones, and re-derives the write-up's threshold.

* **`conjecture2_of_abscissa_nonneg`** — the write-up's own last step, and the whole
  reduction: `σ_η ≥ 0` for every `η > 0` **implies** Conjecture 2, with `η₁ = 1`.  The
  conjecture's `∀ ε > 0` is discharged by `0 > −ε` and nothing else; the quantifier structure
  is the entire content of that paragraph, and here it is a theorem rather than a sentence.
* **`norm_one_sub_exp_neg_ge`** — the circle estimate `‖1 − e^{−w}‖ ≥ ‖w‖ − ‖w‖²`, which is
  what makes Rouché applicable on `|w| = r`.
* **`exp_neg_odd_pi_eq_neg_one`** — `e^{−i(2k+1)π} = −1`, the identity that turns `F_η = 1`
  into the equation `G_k(w) = 0` the write-up applies Rouché to.
* **`eq_zero_of_one_sub_exp_neg_eq_zero`** — `1 − e^{−w}` has **no zero but `w = 0`** in
  `‖w‖ < 2π`, which is the counting fact Rouché transfers.

**THE THRESHOLD `r < 1/2` IS SLACK, IN BOTH OF THE PLACES THE WRITE-UP USES IT.**  The
write-up bounds the exponential tail by a geometric series, obtaining
`m_r = r(1−2r)/(1−r)`, positive only for `r < 1/2`, and then says *"Since `r < 1/2`, the
latter has exactly one zero"*.  Neither use needs it.

* `mSharp_ge_mWrite` proves `r(1−2r)/(1−r) ≤ r − r²` for `0 ≤ r < 1` — the difference is
  exactly `r³/(1−r) ≥ 0` — so Mathlib's remainder bound `‖eˣ − 1 − x‖ ≤ ‖x‖²` gives a
  **strictly better** constant, positive on the whole of `0 < r < 1`.
* `eq_zero_of_one_sub_exp_neg_eq_zero` gives uniqueness of the zero for any `r < 2π`,
  because the other zeros of `1 − e^{−w}` are the nonzero multiples of `2πi` and the nearest
  has modulus `2π ≈ 6.28`.  The write-up's `1/2` is smaller than that by a factor of `4π`.

`mWrite_eq_zero_at_half` records that the write-up's own constant vanishes exactly at
`r = 1/2`, so the threshold is a real feature of *its* estimate and not a typo — it is the
estimate, not the geometry, that wanted `r < 1/2`.  Nothing downstream is weakened by this:
the write-up only ever needs *some* admissible `r`, and it takes `r = 1/4`.  The point is
that the constant is an artifact, and a reader trying to push `r` up would otherwise think
the obstruction is the zero-counting when it is not.

CARRIED, and it is the analytic bulk.  The characteristic function `F_η` and its factor
`H_η`; the principal square root `z = √(1+4ηs)` and the identity `Re √t = √((|t|+Re t)/2)`
on the upper half-plane; the lower bound `Re z ≥ L_k` and hence `|H_η| ≥ B_k → ∞` on the
disks; and Rouché's theorem itself, which Mathlib does have but which is applied here to a
function this module does not construct.  `Conjecture2` therefore takes the spectral abscissa
as a parameter — **it appears in the statement**, so it cannot be satisfied vacuously, and
`conjecture2_of_abscissa_nonneg` is a genuine implication into it rather than a restatement.

Reference: G. Bastin, J.-M. Coron and A. Hayat, Conjecture 2, §6; campaign write-up dated
2026-09-28.
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log

set_option autoImplicit false

namespace Principia.MathDB.P381792

open Complex Real

/-! ## 1. The two constants, and which one the estimate really gives -/

/-- The write-up's circle constant `m_r = r(1−2r)/(1−r)`, obtained by bounding the
exponential tail with a geometric series. -/
noncomputable def mWrite (r : ℝ) : ℝ := r * (1 - 2 * r) / (1 - r)

/-- The constant Mathlib's remainder bound actually gives. -/
noncomputable def mSharp (r : ℝ) : ℝ := r - r ^ 2

theorem mWrite_pos {r : ℝ} (h0 : 0 < r) (h1 : r < 1 / 2) : 0 < mWrite r := by
  have h1r : 0 < 1 - r := by linarith
  have : 0 < r * (1 - 2 * r) := by nlinarith
  exact div_pos this h1r

/-- **The write-up's constant vanishes exactly at `r = 1/2`** — so `r < 1/2` is a real
feature of that estimate, not a transcription slip. -/
theorem mWrite_eq_zero_at_half : mWrite (1 / 2) = 0 := by
  unfold mWrite; norm_num

theorem mSharp_pos {r : ℝ} (h0 : 0 < r) (h1 : r < 1) : 0 < mSharp r := by
  unfold mSharp; nlinarith

/-- **The sharper constant dominates the write-up's, on the whole of `0 ≤ r < 1`.**  The
difference is exactly `r³/(1−r)`. -/
theorem mSharp_ge_mWrite {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : mWrite r ≤ mSharp r := by
  have h1r : 0 < 1 - r := by linarith
  rw [mWrite, mSharp, div_le_iff₀ h1r]
  nlinarith [pow_nonneg h0 3]

/-! ## 2. The circle estimate that makes Rouché applicable -/

/-- **`‖1 − e^{−w}‖ ≥ ‖w‖ − ‖w‖²`.**  On the circle `‖w‖ = r` this is the write-up's `m_r`
step, with the better constant of §1. -/
theorem norm_one_sub_exp_neg_ge {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖w‖ - ‖w‖ ^ 2 ≤ ‖1 - Complex.exp (-w)‖ := by
  have hn : ‖(-w)‖ ≤ 1 := by simpa using hw
  have hrem : ‖Complex.exp (-w) - 1 - (-w)‖ ≤ ‖(-w)‖ ^ 2 :=
    Complex.norm_exp_sub_one_sub_id_le hn
  have hnw : ‖(-w)‖ = ‖w‖ := by simp
  rw [hnw] at hrem
  have hsym : ‖1 - Complex.exp (-w)‖ = ‖Complex.exp (-w) - 1‖ := by
    rw [← norm_neg]; ring_nf
  rw [hsym]
  -- ‖e^{-w} - 1‖ ≥ ‖-w‖ - ‖(e^{-w} - 1) - (-w)‖
  have hsplit : ‖(-w)‖ - ‖Complex.exp (-w) - 1 - (-w)‖ ≤ ‖Complex.exp (-w) - 1‖ := by
    have := norm_sub_norm_le (Complex.exp (-w) - 1) (-w)
    calc ‖(-w)‖ - ‖Complex.exp (-w) - 1 - (-w)‖
        ≤ ‖(-w)‖ - (‖(-w)‖ - ‖Complex.exp (-w) - 1‖) := by
          have h2 := norm_sub_norm_le (-w) (Complex.exp (-w) - 1)
          have h3 : ‖(-w) - (Complex.exp (-w) - 1)‖ = ‖Complex.exp (-w) - 1 - (-w)‖ := by
            rw [← norm_neg]; ring_nf
          rw [h3] at h2
          linarith
      _ = ‖Complex.exp (-w) - 1‖ := by ring
  rw [hnw] at hsplit
  linarith

/-! ## 3. The identity behind the reduction, and the zero count -/

/-- **`e^{−i(2k+1)π} = −1`.**  This is what turns `F_η(s) = 1` on the disk into the
equation `G_k(w) = 0` that Rouché is applied to. -/
theorem exp_neg_odd_pi_eq_neg_one (k : ℤ) :
    Complex.exp (-(((2 * k + 1 : ℤ) : ℂ) * (Real.pi : ℂ) * Complex.I)) = -1 := by
  -- split off a full period: −(2k+1)πi = (−k)(2πi) + (−πi)
  have hsplit : -(((2 * k + 1 : ℤ) : ℂ) * (Real.pi : ℂ) * Complex.I)
      = ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        + -((Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [hsplit, Complex.exp_add]
  have h1 : Complex.exp (((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 :=
    Complex.exp_eq_one_iff.mpr ⟨-k, rfl⟩
  rw [h1, one_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- **The only zero of `1 − e^{−w}` with `‖w‖ < 2π` is `w = 0`.**  This is the zero-counting
fact Rouché transfers, and it holds for radius up to `2π` — far beyond the write-up's `1/2`. -/
theorem eq_zero_of_one_sub_exp_neg_eq_zero {w : ℂ} (hw : ‖w‖ < 2 * Real.pi)
    (h : 1 - Complex.exp (-w) = 0) : w = 0 := by
  have hexp : Complex.exp (-w) = 1 := by linear_combination -h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  have hw' : w = -(n * (2 * Real.pi * Complex.I)) := by rw [← hn]; ring
  rcases eq_or_ne n 0 with rfl | hn0
  · simpa using hw'
  · exfalso
    have hnorm : ‖w‖ = |(n : ℝ)| * (2 * Real.pi) := by
      rw [hw', norm_neg, norm_mul]
      have h1 : ‖((n : ℂ))‖ = |(n : ℝ)| := by simp
      have h2 : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
        rw [norm_mul, norm_mul]
        simp [abs_of_pos Real.pi_pos]
      rw [h1, h2]
    have hge : (1 : ℝ) ≤ |(n : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
      exact_mod_cast h1
    have hpi : 0 < 2 * Real.pi := by positivity
    nlinarith [hnorm, hge, hw]

/-! ## 4. The conjecture, and the reduction the write-up performs -/

/-- **Conjecture 2** of Bastin–Coron–Hayat, relative to the spectral abscissa `σ`.
`σ` is a parameter because the module does not construct the characteristic function, but
**it appears in the statement**, so the conjecture cannot be satisfied vacuously. -/
def Conjecture2 (σ : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ η₁ > 0, ∀ η, 0 < η → η < η₁ → σ η > -ε

/-- **The write-up's final step: `σ_η ≥ 0` for every `η > 0` implies Conjecture 2.**  The
whole paragraph is this implication, and `η₁ = 1` works because the hypothesis is uniform in
`η`; the `∀ ε > 0` is discharged by `0 > −ε` alone. -/
theorem conjecture2_of_abscissa_nonneg {σ : ℝ → ℝ} (h : ∀ η, 0 < η → 0 ≤ σ η) :
    Conjecture2 σ := by
  intro ε hε
  refine ⟨1, one_pos, fun η hη _ => ?_⟩
  have := h η hη
  linarith

/-- The hypothesis is genuinely needed: a `σ` that dips below every negative level fails the
conjecture, so `conjecture2_of_abscissa_nonneg` is not vacuously about an empty class. -/
theorem not_conjecture2_of_const_neg {c : ℝ} (hc : c < 0) :
    ¬ Conjecture2 (fun _ => c) := by
  intro h
  obtain ⟨η₁, hη₁, hall⟩ := h (-c / 2) (by linarith)
  have := hall (min η₁ 1 / 2) (by positivity) (by
    have : min η₁ 1 ≤ η₁ := min_le_left _ _
    have h1 : (0:ℝ) < min η₁ 1 := by positivity
    linarith)
  simp only at this
  linarith

end Principia.MathDB.P381792
