import Mathlib

set_option maxHeartbeats 1000000

/-!
# MathDB #372858 — Schmidlin's Conjecture 37 (SPINE, one named analytic hypothesis)

Write-up `mathdb-open-problems/problems/372858/solution.tex`,
*A stronger Burnside–Stirling–Gautschi bound*, 12 September 2026, **revised 17 September 2026**.
Source: M. Schmidlin, *On Gautschi & Stirling Identities, Asymptotics and Inequalities for the
Pi (or Gamma) Function*, arXiv:2601.21906v1 (2026), Conjecture 37 (pp. 28–29).

With `Π̂(x,α) = Γ(x+1)(x+1)^α` and `S_{1/2}(y) = √(2π)(y+1/2)^{y+1/2}e^{-y-1/2}`, set
`m̂(x,α) = log(Π̂(x,α)/S_{1/2}(x+α))`.  The conjecture asks to remove the restriction `x ≥ 1`
from the bound `m̂(x,α) < [12(x+α) + 18 - 12e^{1/48}]⁻¹`; the write-up proves the strictly
stronger constant `23/4` on the full domain `x ≥ 0`, `α ≥ 0`.

## Why this module exists, and what it is honest about

The campaign's triage recorded this row as blocked because *"Mathlib has no polygamma
functions"*.  Reading the **revised** write-up refutes that: it states outright that Lemma
`binet` is *"the only special-function estimate needed"*, and digamma and trigamma appear
nowhere in it.  (The superseded 12 September argument did use them.  The triage was written
against the earlier text — a staleness of the *source*, not of our own work.)

So the whole proof is elementary except for one input, and this module is the spine that makes
that precise.  Per the project's spine rule, the gap is a **named hypothesis**, never `sorry`:

* `BinetBound` — Binet's bound on the Stirling remainder, `r(u) < 1/(12u) - 1/(360u³) +
  1/(1260u⁵)` for `u > 0`.  This is the write-up's Lemma 1, proved there from Binet's integral
  `r(u) = 2∫₀^∞ arctan(t/u)/(e^{2πt}-1) dt` (DLMF 5.9.10) together with the moment evaluations
  `∫₀^∞ tʲ/(e^{2πt}-1) dt = j!ζ(j+1)/(2π)^{j+1}`.  **Mathlib has none of this**:
  `Analysis/SpecialFunctions/Stirling.lean` is about the *factorial* sequence at integer
  arguments and carries no continuous log-Gamma remainder, and the campaign owns no Binet
  asset either.  It is the single obligation this row still owes.

Everything else below is proved outright, and the composition is a typing fact: `main_of_binet`
and `main_conj37` are `BinetBound → (the conjecture)`, so no gap can hide in the reassembly.

## What is proved unconditionally

* `log_ge_two_mul_div` — `2t/(2+t) ≤ log(1+t)` for `t ≥ 0`, from Mathlib's odd-power series
  for `log(1+x) - log(1-x)` at `x = t/(2+t)`: the bound *is* that series' first term.
* `phi_nonneg`, `phi_ge` — the write-up's Lemma 2 for `φ(t) = (1+t)log(1+t) - t`.
* `mhat_expand`, `mhat_normalization` — the exact identity `m̂(x,α) = r(u) - u·φ(δ/u)` for
  `u = x+1`, `δ = α - 1/2`, which is what turns the bound into a statement about `r` and `φ`.
* `certP_pos`, `F_pos` — the write-up's exact rational certificate.  Its integer coefficient
  table and all four discriminants were re-checked over the rationals before being written
  here (`Campaigns/MathDB-Formalization/probe_372858_cert.py`); the identity residual is `0`.
* `exp_one_div_48_lt`, `lt_exp_one_div_48`, `const_chain` — `0 < 270/47 < 18 - 12e^{1/48} <
  23/4`, so the constant `23/4` really is stronger than the conjectured one.
-/

namespace Principia.MathDB.P372858

open Real

/-! ### The elementary function `φ` (write-up Lemma 2) -/

/-- The write-up's `φ(t) = (1+t)log(1+t) - t`. -/
noncomputable def phi (t : ℝ) : ℝ := (1 + t) * Real.log (1 + t) - t

/-- `2t/(2+t) ≤ log(1+t)` for `t ≥ 0` — the write-up's `q ≥ 0`.

Proved without derivatives: at `x = t/(2+t)` one has `(1+x)/(1-x) = 1+t`, so Mathlib's series
`log(1+x) - log(1-x) = ∑ₖ 2x^{2k+1}/(2k+1)` applies, every term is nonnegative, and the claim
is exactly its `k = 0` term. -/
theorem log_ge_two_mul_div {t : ℝ} (ht : 0 ≤ t) : 2 * t / (2 + t) ≤ Real.log (1 + t) := by
  have h2t : (0:ℝ) < 2 + t := by linarith
  set x : ℝ := t / (2 + t) with hx_def
  have hx0 : 0 ≤ x := div_nonneg ht h2t.le
  have hx1 : x < 1 := by
    rw [hx_def, div_lt_one h2t]; linarith
  have habs : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have hsum := Real.hasSum_log_sub_log_of_abs_lt_one habs
  -- `(1+x) / (1-x) = 1 + t`, so the series sums to `log (1+t)`.
  have hone_sub : (1 : ℝ) - x = 2 / (2 + t) := by rw [hx_def]; field_simp; ring
  have hone_add : (1 : ℝ) + x = (2 + 2 * t) / (2 + t) := by rw [hx_def]; field_simp; ring
  have hlog : Real.log (1 + x) - Real.log (1 - x) = Real.log (1 + t) := by
    rw [hone_sub, hone_add, Real.log_div (by positivity) h2t.ne',
      Real.log_div (by norm_num) h2t.ne']
    have : (2 : ℝ) + 2 * t = 2 * (1 + t) := by ring
    rw [this, Real.log_mul (by norm_num) (by positivity)]
    ring
  rw [hlog] at hsum
  -- the `k = 0` term is `2x`, and every other term is nonnegative
  have hterm : ∀ k : ℕ, 0 ≤ (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k + 1) := by
    intro k
    have h1 : (0:ℝ) < 2 * (k : ℝ) + 1 := by positivity
    have := pow_nonneg hx0 (2 * k + 1)
    positivity
  have hle := sum_le_hasSum ({0} : Finset ℕ) (fun i _ => hterm i) hsum
  rw [Finset.sum_singleton] at hle
  norm_num at hle
  -- `hle : 2 * x ≤ log (1 + t)`
  have : 2 * t / (2 + t) = 2 * x := by rw [hx_def]; ring
  rw [this]
  linarith [hle]

/-- `φ ≥ 0` on `(-1, ∞)`.  From `log s ≥ 1 - 1/s`, i.e. `s log s ≥ s - 1`. -/
theorem phi_nonneg {t : ℝ} (ht : -1 < t) : 0 ≤ phi t := by
  have hs : (0:ℝ) < 1 + t := by linarith
  -- `log (1/(1+t)) ≤ 1/(1+t) - 1`, i.e. `log (1+t) ≥ 1 - 1/(1+t)`
  have h := Real.log_le_sub_one_of_pos (x := 1 / (1 + t)) (by positivity)
  rw [Real.log_div (by norm_num) hs.ne', Real.log_one] at h
  -- h : 0 - log (1+t) ≤ 1/(1+t) - 1
  have hkey : 1 - 1 / (1 + t) ≤ Real.log (1 + t) := by linarith
  have := mul_le_mul_of_nonneg_left hkey hs.le
  rw [mul_sub, mul_one, mul_one_div, div_self hs.ne'] at this
  unfold phi
  linarith

/-- `t²/(2+t) ≤ φ(t)` for `t ≥ 0` — the write-up's Lemma 2, second half.

Immediate from `log_ge_two_mul_div`: `(1+t)·2t/(2+t) - t = t²/(2+t)`. -/
theorem phi_ge {t : ℝ} (ht : 0 ≤ t) : t ^ 2 / (2 + t) ≤ phi t := by
  have h2t : (0:ℝ) < 2 + t := by linarith
  have h := log_ge_two_mul_div ht
  have hmul : (1 + t) * (2 * t / (2 + t)) ≤ (1 + t) * Real.log (1 + t) :=
    mul_le_mul_of_nonneg_left h (by linarith)
  have hid : (1 + t) * (2 * t / (2 + t)) - t = t ^ 2 / (2 + t) := by
    field_simp; ring
  unfold phi
  linarith [hmul, hid]

/-! ### The Stirling remainder, the target, and the normalization identity -/

/-- The Stirling remainder `r(u) = log Γ(u) - (u - 1/2)log u + u - (1/2)log(2π)`. -/
noncomputable def rem (u : ℝ) : ℝ :=
  Real.log (Real.Gamma u) - (u - 1/2) * Real.log u + u - (1/2) * Real.log (2 * π)

/-- The write-up's Burnside–Stirling function `S_{1/2}(y) = √(2π)(y+1/2)^{y+1/2}e^{-y-1/2}`. -/
noncomputable def SS (y : ℝ) : ℝ :=
  Real.sqrt (2 * π) * (y + 1/2) ^ (y + 1/2) * Real.exp (-y - 1/2)

/-- The write-up's `m̂_{1/2}(x,α) = log(Γ(x+1)(x+1)^α / S_{1/2}(x+α))`, stated literally. -/
noncomputable def mhat (x α : ℝ) : ℝ :=
  Real.log (Real.Gamma (x + 1) * (x + 1) ^ α / SS (x + α))

/-- `SS` is positive on the domain of interest. -/
theorem SS_pos {y : ℝ} (hy : 0 ≤ y) : 0 < SS y := by
  unfold SS
  have h1 : (0:ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have h2 : (0:ℝ) < (y + 1/2) ^ (y + 1/2) := Real.rpow_pos_of_pos (by linarith) _
  have h3 : (0:ℝ) < Real.exp (-y - 1/2) := Real.exp_pos _
  positivity

/-- `log (SS y) = (1/2)log(2π) + (y+1/2)log(y+1/2) - y - 1/2`. -/
theorem log_SS {y : ℝ} (hy : 0 ≤ y) :
    Real.log (SS y)
      = (1/2) * Real.log (2 * π) + (y + 1/2) * Real.log (y + 1/2) - y - 1/2 := by
  have hy2 : (0:ℝ) < y + 1/2 := by linarith
  have h1 : (0:ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have h2 : (0:ℝ) < (y + 1/2) ^ (y + 1/2) := Real.rpow_pos_of_pos hy2 _
  unfold SS
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_mul h1.ne' h2.ne',
    Real.log_exp, Real.log_rpow hy2, Real.log_sqrt (by positivity)]
  ring

/-- `mhat` in expanded logarithmic form. -/
theorem mhat_expand {x α : ℝ} (hx : 0 ≤ x) (hα : 0 ≤ α) :
    mhat x α = Real.log (Real.Gamma (x + 1)) + α * Real.log (x + 1)
      - ((1/2) * Real.log (2 * π) + (x + α + 1/2) * Real.log (x + α + 1/2)
          - (x + α) - 1/2) := by
  have hx1 : (0:ℝ) < x + 1 := by linarith
  have hG : (0:ℝ) < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos hx1
  have hR : (0:ℝ) < (x + 1) ^ α := Real.rpow_pos_of_pos hx1 _
  have hS : (0:ℝ) < SS (x + α) := SS_pos (by linarith)
  unfold mhat
  rw [Real.log_div (by positivity) hS.ne', Real.log_mul hG.ne' hR.ne',
    Real.log_rpow hx1, log_SS (by linarith : (0:ℝ) ≤ x + α)]

/-- The exact normalization identity `m̂(x,α) = r(u) - u·φ(δ/u)` with `u = x+1`, `δ = α - 1/2`.

This is the write-up's equation (normalization), and it is what makes the whole bound a
statement about the Stirling remainder and the elementary `φ`. -/
theorem mhat_normalization {x α : ℝ} (hx : 0 ≤ x) (hα : 0 ≤ α) :
    mhat x α = rem (x + 1) - (x + 1) * phi ((α - 1/2) / (x + 1)) := by
  have hu : (0:ℝ) < x + 1 := by linarith
  have hud : (0:ℝ) < x + α + 1/2 := by linarith
  have hlog : Real.log (1 + (α - 1/2) / (x + 1))
      = Real.log (x + α + 1/2) - Real.log (x + 1) := by
    rw [show (1 : ℝ) + (α - 1/2) / (x + 1) = (x + α + 1/2) / (x + 1) from by
      field_simp; ring]
    exact Real.log_div hud.ne' hu.ne'
  rw [mhat_expand hx hα]
  unfold rem phi
  rw [hlog]
  field_simp
  ring

/-! ### The one analytic input -/

/-- **Binet's bound on the Stirling remainder** — the write-up's Lemma 1, and the single
obligation this row still owes.  Mathlib has neither Binet's integral nor a continuous
log-Gamma remainder, so this enters as a hypothesis rather than a theorem. -/
-- SPEC-CARRY-CHECKED: BinetBound -- 2026-09-26.  Measured absent from Mathlib rather than assumed
-- absent: Abel-Plana summation has zero hits; the five `Binet` hits are Binet-Cauchy and Binet's
-- FIBONACCI formula, none of them about Gamma; and the moment integral is unavailable because
-- Mathlib builds `riemannZeta` from theta/Hurwitz kernels, not the Bose kernel.  This is a genuine
-- open obligation on an uncounted row, not a witness that merely went unwritten.
def BinetBound : Prop :=
  ∀ u : ℝ, 0 < u → rem u < 1 / (12 * u) - 1 / (360 * u ^ 3) + 1 / (1260 * u ^ 5)

/-- The simplified form used in the proof: for `u ≥ 1`, `r(u) < 1/(12u) - 1/(504u³)`.
The difference of the two right-hand sides is `(u²-1)/(1260u⁵) ≥ 0`. -/
theorem binet_simplified (hB : BinetBound) {u : ℝ} (hu : 1 ≤ u) :
    rem u < 1 / (12 * u) - 1 / (504 * u ^ 3) := by
  have hu0 : (0:ℝ) < u := by linarith
  have h := hB u hu0
  have key : (1 / (12 * u) - 1 / (504 * u ^ 3))
      - (1 / (12 * u) - 1 / (360 * u ^ 3) + 1 / (1260 * u ^ 5))
      = (u ^ 2 - 1) / (1260 * u ^ 5) := by
    field_simp
    ring
  have hnn : (0:ℝ) ≤ (u ^ 2 - 1) / (1260 * u ^ 5) := by
    apply div_nonneg _ (by positivity)
    nlinarith
  linarith [key, hnn]

/-! ### The exact rational certificate -/

/-- A positive-definite quadratic: `A > 0` and `4AC - B² > 0` give `Ad² - Bd + C > 0`,
since `4A(Ad² - Bd + C) = (2Ad - B)² + (4AC - B²)`. -/
theorem quad_pos {A B C d : ℝ} (hA : 0 < A) (hdisc : 0 < 4 * A * C - B ^ 2) :
    0 < A * d ^ 2 - B * d + C := by
  nlinarith [sq_nonneg (2 * A * d - B), hA, hdisc]

/-- The write-up's certificate polynomial, in `z = u - 1` and `d`.

The coefficient table is the write-up's, re-verified exactly over the rationals before being
transcribed (see `probe_372858_cert.py`: identity residual `0`, and the four discriminants
`4AⱼCⱼ - Bⱼ²` are `665231`, `20434608`, `51841692`, `16087680`). -/
def certP (z d : ℝ) : ℝ :=
  24192 * d ^ 2 * z ^ 4
    + (24192 * d ^ 3 + 21720 * d ^ 2 - 3847 * d + 178)
    + (72576 * d ^ 3 + 91224 * d ^ 2 - 11868 * d + 442) * z
    + (72576 * d ^ 3 + 141624 * d ^ 2 - 12054 * d + 348) * z ^ 2
    + (24192 * d ^ 3 + 96264 * d ^ 2 - 4032 * d + 84) * z ^ 3

/-- The certificate is strictly positive on the whole unbounded region `z ≥ 0`, `d ≥ 0`. -/
theorem certP_pos {z d : ℝ} (hz : 0 ≤ z) (hd : 0 ≤ d) : 0 < certP z d := by
  have hd3 : (0:ℝ) ≤ d ^ 3 := by positivity
  have q0 : (0:ℝ) < 21720 * d ^ 2 - 3847 * d + 178 :=
    quad_pos (by norm_num) (by norm_num)
  have q1 : (0:ℝ) < 91224 * d ^ 2 - 11868 * d + 442 :=
    quad_pos (by norm_num) (by norm_num)
  have q2 : (0:ℝ) < 141624 * d ^ 2 - 12054 * d + 348 :=
    quad_pos (by norm_num) (by norm_num)
  have q3 : (0:ℝ) < 96264 * d ^ 2 - 4032 * d + 84 :=
    quad_pos (by norm_num) (by norm_num)
  have b0 : (0:ℝ) < 24192 * d ^ 3 + 21720 * d ^ 2 - 3847 * d + 178 := by linarith
  have b1 : (0:ℝ) < 72576 * d ^ 3 + 91224 * d ^ 2 - 11868 * d + 442 := by linarith
  have b2 : (0:ℝ) < 72576 * d ^ 3 + 141624 * d ^ 2 - 12054 * d + 348 := by linarith
  have b3 : (0:ℝ) < 24192 * d ^ 3 + 96264 * d ^ 2 - 4032 * d + 84 := by linarith
  have t1 := mul_nonneg b1.le hz
  have t2 := mul_nonneg b2.le (by positivity : (0:ℝ) ≤ z ^ 2)
  have t3 := mul_nonneg b3.le (by positivity : (0:ℝ) ≤ z ^ 3)
  have t4 : (0:ℝ) ≤ 24192 * d ^ 2 * z ^ 4 := by positivity
  unfold certP
  linarith

/-- The write-up's `F(u,δ) > 0` on `u ≥ 1`, `δ ≥ 0`. -/
theorem F_pos {u d : ℝ} (hu : 1 ≤ u) (hd : 0 ≤ d) :
    0 < 1 / (12 * (u + d) - 1/4) - 1 / (12 * u) + 1 / (504 * u ^ 3)
        + d ^ 2 / (2 * u + d) := by
  have hu0 : (0:ℝ) < u := by linarith
  have h1 : (0:ℝ) < 12 * (u + d) - 1/4 := by linarith
  have h2 : (0:ℝ) < 2 * u + d := by linarith
  have h3 : (0:ℝ) < 48 * u + 48 * d - 1 := by linarith
  have hden : (0:ℝ) < 504 * u ^ 3 * (2 * u + d) * (48 * u + 48 * d - 1) :=
    mul_pos (mul_pos (by positivity) h2) h3
  have hu' : u ≠ 0 := ne_of_gt hu0
  have h2' : (2 * u + d) ≠ 0 := ne_of_gt h2
  have h3' : (48 * u + 48 * d - 1) ≠ 0 := ne_of_gt h3
  -- `field_simp` normalizes this denominator to `-1 + u*48 + d*48` and then no longer
  -- recognizes `h3'` as being about the same term, so it is supplied in that shape too.
  have hrw : 1 / (12 * (u + d) - 1/4) = 4 / (48 * u + 48 * d - 1) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]
    ring
  -- Cancel the denominators ONE TERM AT A TIME.  `field_simp` on the whole product does not
  -- work here: it expands `48u+48d-1` where it sits in a numerator while leaving
  -- `(48u+48d-1)⁻¹` untouched, so the `A * A⁻¹` cancellation never fires and an inverse
  -- survives into `ring`.  Supplying the nonvanishing fact in the normalized shape does not
  -- help, because the obstruction is the missing cancellation, not a missing hypothesis.
  -- Termwise, each product cancels exactly one denominator and `field_simp` is reliable.
  have t1 : (4 / (48 * u + 48 * d - 1))
      * (504 * u ^ 3 * (2 * u + d) * (48 * u + 48 * d - 1))
      = 4 * (504 * u ^ 3 * (2 * u + d)) := by
    field_simp
    -- `field_simp` factors the denominator to `48 * (u + d) - 1` and leaves `a / a = 1`.
    exact div_self (ne_of_gt (by linarith : (0:ℝ) < 48 * (u + d) - 1))
  have t2 : (1 / (12 * u)) * (504 * u ^ 3 * (2 * u + d) * (48 * u + 48 * d - 1))
      = 42 * u ^ 2 * (2 * u + d) * (48 * u + 48 * d - 1) := by
    field_simp; ring
  have t3 : (1 / (504 * u ^ 3)) * (504 * u ^ 3 * (2 * u + d) * (48 * u + 48 * d - 1))
      = (2 * u + d) * (48 * u + 48 * d - 1) := by
    field_simp
  have t4 : (d ^ 2 / (2 * u + d)) * (504 * u ^ 3 * (2 * u + d) * (48 * u + 48 * d - 1))
      = 504 * d ^ 2 * u ^ 3 * (48 * u + 48 * d - 1) := by
    field_simp
  have key : (1 / (12 * (u + d) - 1/4) - 1 / (12 * u) + 1 / (504 * u ^ 3)
        + d ^ 2 / (2 * u + d))
      * (504 * u ^ 3 * (2 * u + d) * (48 * u + 48 * d - 1)) = certP (u - 1) d := by
    rw [hrw]
    have expand : (4 / (48 * u + 48 * d - 1) - 1 / (12 * u) + 1 / (504 * u ^ 3)
          + d ^ 2 / (2 * u + d))
        * (504 * u ^ 3 * (2 * u + d) * (48 * u + 48 * d - 1))
        = (4 / (48 * u + 48 * d - 1))
            * (504 * u ^ 3 * (2 * u + d) * (48 * u + 48 * d - 1))
          - (1 / (12 * u)) * (504 * u ^ 3 * (2 * u + d) * (48 * u + 48 * d - 1))
          + (1 / (504 * u ^ 3)) * (504 * u ^ 3 * (2 * u + d) * (48 * u + 48 * d - 1))
          + (d ^ 2 / (2 * u + d))
            * (504 * u ^ 3 * (2 * u + d) * (48 * u + 48 * d - 1)) := by
      ring
    rw [expand, t1, t2, t3, t4]
    unfold certP
    ring
  have hP : 0 < certP (u - 1) d := certP_pos (by linarith) hd
  have hEq : 1 / (12 * (u + d) - 1/4) - 1 / (12 * u) + 1 / (504 * u ^ 3)
      + d ^ 2 / (2 * u + d)
      = certP (u - 1) d / (504 * u ^ 3 * (2 * u + d) * (48 * u + 48 * d - 1)) := by
    rw [eq_div_iff hden.ne']
    exact key
  rw [hEq]
  exact div_pos hP hden

/-! ### How strong must `BinetBound` be?  The `u⁻³` correction is load-bearing

`binet_simplified` uses Binet only through `r(u) < 1/(12u) - 1/(504u³)`.  It is worth knowing
whether the `u⁻³` term is needed at all, because the *classical* Stirling bound `r(u) < 1/(12u)`
is far more accessible than Binet's integral.  It is needed: replacing `1/(504u³)` by `c/u³` and
evaluating the certificate's `F` at `u = 1`, `δ = 1/10` gives exactly `c - 1/740`, so any
admissible `c` must exceed `1/740` and `c = 0` is refuted outright.

Together with `F_pos` (which proves `c = 1/504` admissible) this pins the obligation between
`1/740` and `1/504`.  A numerical search puts the true threshold at `c ≈ 0.00157886`, attained at
`u = 1`, `δ ≈ 0.0788` — so the write-up's constant carries only about 26% margin and the Binet
input cannot be weakened appreciably.  See `probe_372858_strength.py`. -/

/-- The certificate's `F`, with `1/(504u³)` replaced by `c/u³`, at the witness `u = 1`,
`δ = 1/10`.  The value is exactly `c - 1/740`. -/
theorem witness_value (c : ℝ) :
    1 / (12 * ((1:ℝ) + 1/10) - 1/4) - 1 / (12 * (1:ℝ)) + c / (1:ℝ) ^ 3
        + ((1:ℝ)/10) ^ 2 / (2 * (1:ℝ) + 1/10)
      = c - 1/740 := by
  -- `norm_num` clears the numeric denominators but stops at
  -- `-(19/3108) + c + 1/210 = c - 1/740` with `c` free; `ring` finishes the numeral arithmetic
  -- (`95/15540 - 74/15540 = 21/15540 = 1/740`).
  norm_num
  ring

/-- **The `u⁻³` correction is load-bearing.**  Any constant `c` for which the certificate route
can close must satisfy `1/740 < c`; in particular `c = 0` — i.e. the classical Stirling bound
`r(u) < 1/(12u)`, without Binet — cannot prove this conjecture. -/
theorem needs_cube_correction {c : ℝ}
    (h : 0 < 1 / (12 * ((1 : ℝ) + 1 / 10) - 1 / 4) - 1 / (12 * (1 : ℝ)) + c / (1 : ℝ) ^ 3
            + ((1 : ℝ) / 10) ^ 2 / (2 * (1 : ℝ) + 1 / 10)) :
    1 / 740 < c := by
  rw [witness_value] at h
  linarith

/-! ### The constant `18 - 12e^{1/48}` is weaker than `23/4` -/

theorem lt_exp_one_div_48 : (49:ℝ)/48 < Real.exp (1/48) := by
  have := Real.add_one_lt_exp (x := (1:ℝ)/48) (by norm_num)
  linarith

theorem exp_one_div_48_lt : Real.exp (1/48) < 48/47 := by
  have h1 : (1:ℝ) - 1/48 < Real.exp (-(1/48)) := by
    have := Real.add_one_lt_exp (x := -((1:ℝ)/48)) (by norm_num)
    linarith
  have h2 : Real.exp ((1:ℝ)/48) * Real.exp (-((1:ℝ)/48)) = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos ((1:ℝ)/48), h1, h2]

/-- `0 < 270/47 < 18 - 12e^{1/48} < 23/4`, so `23/4` is the stronger constant. -/
theorem const_chain :
    (0:ℝ) < 270/47 ∧ (270:ℝ)/47 < 18 - 12 * Real.exp (1/48)
      ∧ 18 - 12 * Real.exp (1/48) < (23:ℝ)/4 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · linarith [exp_one_div_48_lt]
  · linarith [lt_exp_one_div_48]

/-! ### The capstone -/

/-- **Conjecture 37, with the stronger constant `23/4`, conditional only on Binet's bound.**

For every `x ≥ 0` and `α ≥ 0` (no upper bound on `α` is needed, as the write-up notes),
`m̂_{1/2}(x,α) < [12(x+α) + 23/4]⁻¹`. -/
theorem main_of_binet (hB : BinetBound) {x α : ℝ} (hx : 0 ≤ x) (hα : 0 ≤ α) :
    mhat x α < 1 / (12 * (x + α) + 23/4) := by
  have hu1 : (1:ℝ) ≤ x + 1 := by linarith
  have hu0 : (0:ℝ) < x + 1 := by linarith
  have hnorm := mhat_normalization hx hα
  have hrem := binet_simplified hB hu1
  have hD : 12 * (x + α) + 23/4 = 12 * ((x + 1) + (α - 1/2)) - 1/4 := by ring
  rcases le_or_gt α ((1:ℝ)/2) with hcase | hcase
  · -- `δ ≤ 0`: `φ ≥ 0` alone suffices
    have ht : (-1:ℝ) < (α - 1/2) / (x + 1) := by
      rw [lt_div_iff₀ hu0]; linarith
    have hphi := phi_nonneg ht
    have hcorr : (0:ℝ) ≤ (x + 1) * phi ((α - 1/2) / (x + 1)) := mul_nonneg hu0.le hphi
    have hsmall : (0:ℝ) < 1 / (504 * (x + 1) ^ 3) := by positivity
    have hstep : mhat x α < 1 / (12 * (x + 1)) := by
      rw [hnorm]; linarith
    have hmono : 1 / (12 * (x + 1)) ≤ 1 / (12 * (x + α) + 23/4) := by
      apply one_div_le_one_div_of_le (by linarith)
      linarith
    linarith
  · -- `δ > 0`: the rational certificate
    have hd0 : (0:ℝ) ≤ α - 1/2 := by linarith
    have ht0 : (0:ℝ) ≤ (α - 1/2) / (x + 1) := div_nonneg hd0 hu0.le
    have hphi := phi_ge ht0
    have hid : (x + 1) * (((α - 1/2) / (x + 1)) ^ 2 / (2 + (α - 1/2) / (x + 1)))
        = (α - 1/2) ^ 2 / (2 * (x + 1) + (α - 1/2)) := by
      have h2 : (0:ℝ) < 2 * (x + 1) + (α - 1/2) := by linarith
      field_simp
    have hcorr : (α - 1/2) ^ 2 / (2 * (x + 1) + (α - 1/2))
        ≤ (x + 1) * phi ((α - 1/2) / (x + 1)) := by
      rw [← hid]
      exact mul_le_mul_of_nonneg_left hphi hu0.le
    have hF := F_pos hu1 hd0
    rw [hnorm, hD]
    linarith

/-- The full statement of the write-up's Theorem, conditional on Binet's bound: the bound holds
with `23/4`, and `23/4` is strictly stronger than the conjectured `18 - 12e^{1/48}`. -/
theorem main_conj37 (hB : BinetBound) {x α : ℝ} (hx : 0 ≤ x) (hα : 0 ≤ α) :
    mhat x α < 1 / (12 * (x + α) + 23/4)
      ∧ 1 / (12 * (x + α) + 23/4)
          < 1 / (12 * (x + α) + (18 - 12 * Real.exp (1/48))) := by
  obtain ⟨c0, c1, c2⟩ := const_chain
  refine ⟨main_of_binet hB hx hα, ?_⟩
  apply one_div_lt_one_div_of_lt (by linarith)
  linarith

end Principia.MathDB.P372858
