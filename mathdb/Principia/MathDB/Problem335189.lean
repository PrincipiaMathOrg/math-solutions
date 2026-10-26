import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# MathDB 335189 — the Redheffer-type lower bound for normalized Bessel ratios is false

Write-up: `mathdb-open-problems/problems/335189/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`, "Counterexamples to the proposed
Redheffer lower bound for a ratio of normalized Bessel functions".  It refutes the **left**
inequality of **Conjecture 1, eq. (3.2)** of Baricz–Mehrez.

## The conjecture

For `ν > -1` let `Jn_ν x = ∑ₖ (-1)ᵏ x^{2k}/(4ᵏ k! (ν+1)ₖ)`, let `j = j_{ν,1}` be the first
positive zero of `J_ν`, `q = j²`, and `R_ν = Jn_{ν+1}/Jn_ν`.  Conjecture 1 asserts, for
`|x| < j`,

  `(q/(q-x²))^{q/[4(ν+1)(ν+2)]} ≤ R_ν x ≤ q/(q-x²)`.

The left inequality fails.

## Why this reduces to a cubic

Both sides equal `1` at `x = 0` and have the **same** `x²` coefficient — `1/[4(ν+1)(ν+2)]`
on each, since `1/[4(ν+1)] - 1/[4(ν+2)]` is exactly that.  So the comparison is decided at
order `x⁴`, by

  `L4 ν q = 1/[8q(ν+1)(ν+2)] + 1/[32(ν+1)²(ν+2)²]`   (the conjectured lower bound)
  `R4 ν   = 1/[16(ν+1)²] - 3/[32(ν+1)(ν+2)] + 1/[32(ν+2)(ν+3)]`   (the ratio).

`L4` is **decreasing in `q`**, so the source's variational bound `q ≤ U ν` gives a valid
lower bound for it, and `key_identity` collapses the whole criterion to a cubic:

  `L4 ν (U ν) - R4 ν = N ν / D ν`,  `N ν = 10ν³ - 225ν² - 1285ν - 1500`,
  `D ν = 480(ν+1)²(ν+2)²(ν+3)(2ν+7)(ν+4) > 0`.

`N 27 = -3390` and `N 28 = 5640`: **the source's threshold `ν ≥ 28` is exactly the sign
change of this cubic**, and `Ncubic_pos` proves `N ν > 0` for every real `ν ≥ 28`.

## What is carried

`Setup` carries two things and no more: the variational bound `q ≤ U ν` on the first
Bessel zero, and the **Taylor step** — that agreement to order `x²` plus a strict gap in
the `x⁴` coefficients makes the lower bound fail for all small nonzero `x`.  Mathlib has
no Bessel functions and no zero bounds for them, and the Taylor step needs the series
division `Jn_{ν+1}/Jn_ν` expanded to fourth order.  Everything else — the cubic reduction,
its positivity, and the monotonicity in `q` that makes the upper bound on `q` the useful
one — is proved.

## Scope, and a finding beyond the write-up

The write-up also refutes the left inequality at the single point `(ν,x) = (30,1)`.  That
half is **not** formalised: it reduces to an exact rational comparison with no `rpow`,
`(6834/6829)^3417 > R_30(1)^9920`, but the margin is `7.704×10⁻¹⁰`, so after the 9920th
power the integers reach ~`2×10⁵` digits.

`Campaigns/MathDB-Formalization/verify_335189.py` also records that **`ν ≥ 28` is an
artefact of the bound `U ν`, not of the mathematics**: evaluated at the true first zero the
`x⁴` gap is already positive at `ν = 20`, and a direct evaluation confirms the lower bound
is violated at `ν = 20, 25, 27`.  A sharper zero bound would widen the range; `gap` below
is stated for an arbitrary `q ≤ U ν`, so it would take that improvement without change.
-/

namespace Principia.MathDB.P335189

/-- The source's variational bound on `j²_{ν,1}`. -/
noncomputable def Ubound (ν : ℝ) : ℝ := 3 * (2 * ν + 7) * (2 * ν + 8) / 10

/-- The `x⁴` coefficient of the conjectured lower bound. -/
noncomputable def L4 (ν q : ℝ) : ℝ :=
  1 / (8 * q * (ν + 1) * (ν + 2)) + 1 / (32 * (ν + 1) ^ 2 * (ν + 2) ^ 2)

/-- The `x⁴` coefficient of `R_ν`. -/
noncomputable def R4 (ν : ℝ) : ℝ :=
  1 / (16 * (ν + 1) ^ 2) - 3 / (32 * (ν + 1) * (ν + 2)) + 1 / (32 * (ν + 2) * (ν + 3))

/-- The numerator of `L4 ν (Ubound ν) - R4 ν`. -/
noncomputable def Ncubic (ν : ℝ) : ℝ := 10 * ν ^ 3 - 225 * ν ^ 2 - 1285 * ν - 1500

/-- Its denominator, positive throughout. -/
noncomputable def Dden (ν : ℝ) : ℝ :=
  480 * (ν + 1) ^ 2 * (ν + 2) ^ 2 * (ν + 3) * (2 * ν + 7) * (ν + 4)

theorem Dden_pos {ν : ℝ} (h : 0 ≤ ν) : 0 < Dden ν := by
  unfold Dden; positivity

theorem Ubound_pos {ν : ℝ} (h : 0 ≤ ν) : 0 < Ubound ν := by
  unfold Ubound; positivity

/-- The whole `x⁴` criterion, at the bound, is one cubic over one positive denominator. -/
theorem key_identity {ν : ℝ} (h : 0 ≤ ν) :
    L4 ν (Ubound ν) - R4 ν = Ncubic ν / Dden ν := by
  have h1 : ν + 1 ≠ 0 := by positivity
  have h2 : ν + 2 ≠ 0 := by positivity
  have h3 : ν + 3 ≠ 0 := by positivity
  have h4 : ν + 4 ≠ 0 := by positivity
  have h5 : 2 * ν + 7 ≠ 0 := by positivity
  have h6 : 2 * ν + 8 ≠ 0 := by positivity
  unfold L4 R4 Ncubic Dden Ubound
  field_simp
  ring

/-- `N ν > 0` for every real `ν ≥ 28`; at `ν = 27` it is `-3390`. -/
theorem Ncubic_pos {ν : ℝ} (h : 28 ≤ ν) : 0 < Ncubic ν := by
  unfold Ncubic
  nlinarith [sq_nonneg (ν - 28), sub_nonneg.2 h,
    mul_nonneg (mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h)) (sub_nonneg.2 h)]

theorem gap_at_bound {ν : ℝ} (h : 28 ≤ ν) : R4 ν < L4 ν (Ubound ν) := by
  have hν : (0 : ℝ) ≤ ν := by linarith
  have hid := key_identity hν
  have hpos : 0 < Ncubic ν / Dden ν := div_pos (Ncubic_pos h) (Dden_pos hν)
  linarith

/-- `L4` decreases in `q`, so an **upper** bound on the zero is what the argument needs. -/
theorem L4_anti {ν q q' : ℝ} (hν : 0 ≤ ν) (hq : 0 < q) (hqq : q ≤ q') :
    L4 ν q' ≤ L4 ν q := by
  unfold L4
  have hb : (0 : ℝ) < 8 * q * (ν + 1) * (ν + 2) := by positivity
  have hle : 8 * q * (ν + 1) * (ν + 2) ≤ 8 * q' * (ν + 1) * (ν + 2) := by nlinarith
  have := one_div_le_one_div_of_le hb hle
  linarith

/-- **The `x⁴` gap, for any `q` below the bound.** -/
theorem gap {ν q : ℝ} (hν : 28 ≤ ν) (hq : 0 < q) (hqU : q ≤ Ubound ν) :
    R4 ν < L4 ν q :=
  lt_of_lt_of_le (gap_at_bound hν) (L4_anti (by linarith) hq hqU)

/-! ## The carried half -/

/-- The two facts taken from the source. -/
structure Setup where
  nu : ℝ
  q : ℝ
  j : ℝ
  hnu : 28 ≤ nu
  hj : 0 < j
  hjq : j ^ 2 = q
  /-- The variational bound on the first Bessel zero. -/
  hqU : q ≤ Ubound nu
  lower : ℝ → ℝ
  ratio : ℝ → ℝ
  /-- The Taylor step: the two sides agree to order `x²`, so a strict gap at order `x⁴`
  makes the conjectured lower bound fail for all small nonzero `x`. -/
  taylor : R4 nu < L4 nu q →
    ∃ ε > (0 : ℝ), ∀ x : ℝ, 0 < |x| → |x| < ε → ratio x < lower x

namespace Setup

variable (S : Setup)

theorem q_pos : 0 < S.q := by rw [← S.hjq]; exact pow_pos S.hj 2

end Setup

/-! ## The refutation -/

/-- Conjecture 1's left inequality, on the punctured disc where it is asserted. -/
def Conj (S : Setup) : Prop := ∀ x : ℝ, 0 < |x| → |x| < S.j → S.lower x ≤ S.ratio x

/-- **The conjectured lower bound is false.** -/
theorem not_conj (S : Setup) : ¬ Conj S := by
  intro hc
  obtain ⟨ε, hε, hfail⟩ := S.taylor (gap S.hnu S.q_pos S.hqU)
  have hm : 0 < min ε S.j := lt_min hε S.hj
  set x : ℝ := min ε S.j / 2 with hxdef
  have hx0 : 0 < x := by rw [hxdef]; linarith
  have hxa : |x| = x := abs_of_pos hx0
  have hxe : |x| < ε := by
    rw [hxa, hxdef]
    have : min ε S.j ≤ ε := min_le_left _ _
    linarith
  have hxj : |x| < S.j := by
    rw [hxa, hxdef]
    have : min ε S.j ≤ S.j := min_le_right _ _
    linarith
  have h1 := hfail x (by rw [hxa]; exact hx0) hxe
  have h2 := hc x (by rw [hxa]; exact hx0) hxj
  linarith

end Principia.MathDB.P335189
