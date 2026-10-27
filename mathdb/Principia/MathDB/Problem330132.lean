/-
MathDB #330132 — a strict strip for Ehrhart roots in dimensions six and seven.

For `d ∈ {6,7}` and a palindromic coefficient vector `h` with `h₀ > 0`, `h₁ ≥ h₀`, `h₂ ≥ h₁`,
`h₃ ≥ h₁`, put `F(z) = ∑_{j=0}^d h_j · C(z+d−j, d)`.  The write-up proves every root of `F`
satisfies `−3 < Re z < 2`, which gives Conjecture 6.4 of the 2015 Hegedűs–Higashitani–Kasprzyk
preprint for Ehrhart polynomials of reflexive polytopes.

WHAT IS PROVED HERE — the two bridges, neither of which needs the determinant expansion.

* **`hyp_of_reflexive`** — the step the write-up disposes of in one sentence (*"the last assertion
  follows from the standard Ehrhart expansion and Hibi's lower bound"*).  The reflexive facts
  (`h` palindromic, `h₀ = h_d = 1`, `h₁ ≥ 1`, `h_j ≥ h₁` for `2 ≤ j ≤ d−1`) imply the theorem's
  four hypotheses, by pure arithmetic.  It needs `4 ≤ d`, which `d ∈ {6,7}` supplies — and that
  dependence is worth making explicit, since `h₃ ≥ h₁` is available only once `3 ≤ d−1`.
* **`strip_iff_abs_lt`** — the write-up's strip is *exactly* the conjecture's bound.  The
  conjecture asks whether a root `−1/2 + u + iv` has `|u| < 5/2`; since `Re z = −1/2 + u`, the
  conditions `−3 < Re z < 2` and `|u| < 5/2` are equivalent.  **So the theorem's claim to be
  "stronger" is entirely about the QUANTIFIER — it drops the conjecture's `u, v ≠ 0` and covers
  real roots too — and not about a tighter strip.**  Stating that distinguishes a genuine
  strengthening from a restatement, which prose alone does not.
* `Palindromic`, `Hyp`, `ReflexiveHStar`, and `binom`/`F` over `ℂ` — the objects, with the
  generalised binomial written as a falling-factorial product so no generalised-binomial theory is
  needed.

CARRIED.  `StripTheorem` itself.  Its proof is an exact determinant expansion whose 112 integer
coefficients the write-up prints in an appendix; reproducing and verifying that inside Lean is a
separate piece of work.  A named hypothesis, never a `sorry`.

Reference: G. Hegedűs, A. Higashitani, A. M. Kasprzyk, *Ehrhart polynomial roots of reflexive
polytopes*, 2015 preprint, Conjecture 6.4 (p. 15); the final article omits the conjecture section
and its p. 5 still leaves the six- and seven-dimensional strip case unproved.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Principia.MathDB.P330132

open Finset

/-! ## 1. The polynomial -/

/-- `C(z, d)` for complex `z`, as a falling-factorial product over `d!`.  Writing it this way
avoids needing any generalised-binomial theory. -/
noncomputable def binom (z : ℂ) (d : ℕ) : ℂ :=
  (∏ i ∈ range d, (z - (i : ℂ))) / (Nat.factorial d : ℂ)

/-- `F(z) = ∑_{j=0}^d h_j · C(z+d−j, d)`. -/
noncomputable def F (h : ℕ → ℤ) (d : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ range (d + 1), (h j : ℂ) * binom (z + (d : ℂ) - (j : ℂ)) d

/-! ## 2. The hypotheses, and the bridge between them -/

/-- `h` is palindromic in degree `d`. -/
def Palindromic (h : ℕ → ℤ) (d : ℕ) : Prop := ∀ j ≤ d, h j = h (d - j)

/-- The write-up's hypotheses on the coefficient vector. -/
structure Hyp (h : ℕ → ℤ) (d : ℕ) : Prop where
  pal : Palindromic h d
  pos : 0 < h 0
  h1 : h 0 ≤ h 1
  h2 : h 1 ≤ h 2
  h3 : h 1 ≤ h 3

/-- The facts about the `h*`-vector of a reflexive polytope, as stated on p. 2 of the final
article: palindromic, `h₀ = h_d = 1`, `h₁ ≥ 1`, and `h_j ≥ h₁` in the middle range.  **No
unimodality is assumed**, matching the write-up. -/
structure ReflexiveHStar (h : ℕ → ℤ) (d : ℕ) : Prop where
  pal : Palindromic h d
  head : h 0 = 1
  tail : h d = 1
  one_le : 1 ≤ h 1
  mid : ∀ j, 2 ≤ j → j ≤ d - 1 → h 1 ≤ h j

/-- **The step the write-up disposes of in one sentence**, proved: the reflexive facts give the
theorem's four hypotheses.  `4 ≤ d` is where the dimension enters — `h₃ ≥ h₁` is available only
once `3 ≤ d − 1`. -/
theorem hyp_of_reflexive (h : ℕ → ℤ) (d : ℕ) (hd : 4 ≤ d) (H : ReflexiveHStar h d) :
    Hyp h d where
  pal := H.pal
  pos := by rw [H.head]; norm_num
  h1 := by rw [H.head]; exact H.one_le
  h2 := H.mid 2 (by norm_num) (by omega)
  h3 := H.mid 3 (by norm_num) (by omega)

/-! ## 3. The strip is exactly the conjecture's bound -/

/-- **The write-up's strip `−3 < Re z < 2` IS the conjecture's `|u| < 5/2`.**  A root is written
`−1/2 + u + iv`, so `Re z = −1/2 + u`.  Hence the theorem's claim to be *stronger* is about the
QUANTIFIER — it drops `u, v ≠ 0` and covers real roots — not about a tighter strip. -/
theorem strip_iff_abs_lt (z : ℂ) (u : ℝ) (hu : z.re = -(1 / 2) + u) :
    (-3 < z.re ∧ z.re < 2) ↔ |u| < 5/2 := by
  rw [hu, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-! ## 4. The theorem and the conjecture -/

/-- **The write-up's Theorem**, carried: for `d ∈ {6,7}` and any coefficient vector satisfying
`Hyp`, every root of `F` lies in the open strip.  Its proof is the exact determinant expansion
with the 112 printed coefficients. -/
def StripTheorem : Prop :=
  ∀ h : ℕ → ℤ, ∀ d : ℕ, (d = 6 ∨ d = 7) → Hyp h d →
    ∀ z : ℂ, F h d z = 0 → -3 < z.re ∧ z.re < 2

/-- **Conjecture 6.4** for reflexive polytopes, in the conjecture's own `|u| < 5/2` form.  That
it follows from `StripTheorem` is `conjecture64_of_strip` below — the two bridges composed. -/
def Conjecture64 : Prop :=
  ∀ h : ℕ → ℤ, ∀ d : ℕ, (d = 6 ∨ d = 7) → ReflexiveHStar h d →
    ∀ z : ℂ, F h d z = 0 → ∀ u : ℝ, z.re = -(1 / 2) + u → |u| < 5/2

/-- **The conjecture follows from the carried theorem**, with no further input: this is
`hyp_of_reflexive` and `strip_iff_abs_lt` composed, so the only remaining obligation is the
determinant expansion. -/
theorem conjecture64_of_strip (H : StripTheorem) : Conjecture64 := by
  intro h d hd R z hz u hu
  have h4 : 4 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  exact (strip_iff_abs_lt z u hu).mp (H h d hd (hyp_of_reflexive h d h4 R) z hz)

end Principia.MathDB.P330132
