import Mathlib

set_option autoImplicit false

/-!
# MathDB #352456 — the polar-parabola centroid locus (SPINE)

Write-up `mathdb-open-problems/problems/352456/solution.tex` on the `mathdb-results` branch
of `antoshashakov/Principia-Math-In-Progress`.
Source: L. Bellio, R. Garcia and D. Reznik, *Parabola-Inscribed Poncelet Polygons Derived
from the Bicentric Family*, KoG **26** (2022) 3–15 (arXiv:2111.00979v3), **Conjecture 5**.

For the parabola `𝒫 : y² + 4fx = 0` and the inner circle `𝒞 : (x+f)² + y² = r²`, a Poncelet
polygon `P` inscribed in `𝒫` and circumscribing `𝒞` has vertices `P_i = (-t_i²/4f, t_i)`.
The *polar* polygon `Q` has as its sides the tangents to `𝒫` at the vertices of `P`, so
`Q_i = (-t_i t_{i+1}/4f, (t_i + t_{i+1})/2)`.  Conjecture 5 asserts that the area centroid
`C₂(Q)` sweeps the line `x = h₂` with

    h₂ = (8f² - r²)/(12f).

## What is proved here, and it is stronger than the source's statement

The shoelace formula gives `(C₂(Q))_x = -S₃₂ / (12f·S₂)` with

    S₂  = ∑ t_i²(t_{i+1} - t_{i-1}),      S₃₂ = ∑ t_i³(t_{i+1}² - t_{i-1}²),

and the tangency of edge `i` to `𝒞` is `g_i = 0`, where

    g_i = (t_i t_{i+1} + 4f²)² - r²(16f² + (t_i + t_{i+1})²).

`centroid_certificate` is the identity, over any commutative ring and for every `N`,

    S₃₂ + (8f² - r²)·S₂ = ∑_i (t_i - t_{i+1})·g_i.                      (cert)

`polar_centroid_x` follows at once: under tangency the right side vanishes, so
`S₃₂ = -(8f² - r²)S₂` and the quotient is `h₂` whenever `S₂ ≠ 0` (i.e. `A(P) ≠ 0`).

**This needs none of the source's machinery** — no flag curve, no elliptic-curve model, no
translation of exact order `N`, no pole/zero divisor count, no Liouville argument, and not
even the Vieta relation.  It is also *stronger* than Conjecture 5's own statement: the
guards `0 < r < f`, primitivity of the family, `N ≥ 3`, and distinctness of the vertices are
all unused.  `(cert)` is an unconditional polynomial identity; only `f ≠ 0` and `S₂ ≠ 0`
enter the final division.

The three "moreover" claims are likewise hypothesis-free and are proved here:
`area_polar` (`A(Q) = -A(P)/2`), `centroid2_y` and `centroid0_y` (the `y`-coordinates of
both centroids are unchanged), each by the same reindexing plus `ring`.

## Why the certificate works

Reindexing `i ↦ i+1` turns both sums into edge sums,

    S₃₂ = ∑_i (t_i - t_{i+1})·t_i²t_{i+1}²,      S₂ = ∑_i (t_i - t_{i+1})·t_i t_{i+1},

so the left side of `(cert)` is `∑_i (t_i - t_{i+1})·[t_i²t_{i+1}² + (8f² - r²)t_i t_{i+1}]`.
The bracket exceeds `g_i` by exactly

    r²(t_i² + t_i t_{i+1} + t_{i+1}²) - 16f²(f² - r²),

and both of those telescope cyclically against `(t_i - t_{i+1})`: the first because
`∑(t_i³ - t_{i+1}³) = 0`, the second because `∑(t_i - t_{i+1}) = 0`.

## What is NOT proved here

* **The vertex-centroid locus `(C₀(Q))_x = h₀`.**  Using Vieta this reduces exactly to
  `∑_i 1/(t_i² - r²)` being constant along a Poncelet orbit, which has NO telescoping
  certificate — a Gröbner test puts it outside the tangency ideal even with the closure
  radius adjoined.  The only known proof is the elliptic-curve argument, and `h₀` has no
  known closed form (it is the write-up's own Task 2).
* **That each locus is a COMPLETE line.**  That needs the real topology of the Poncelet
  family plus an IVT argument; Mathlib has the IVT but no Poncelet family.

Both are recorded, neither is carried as a hypothesis: nothing below depends on them.  So
this row is a SPINE and is NOT counted as fully verified — roughly half of Conjecture 5
(the `h₀` locus and both completeness claims) stays unformalised.

**215 check.**  The source states Conjecture 5 under `0 < r < f`, primitivity, `N ≥ 3` and
distinct vertices.  Every one of those guards is DROPPED here, which is safe in this
direction: the theorem proved is more general than the one conjectured, and `(cert)` is
quantified over all `t`, `f`, `r` with no side conditions at all.  The final statement adds
only `f ≠ 0` and `S₂ ≠ 0`, both of which are forced by the geometry (`S₂ ≠ 0` is
`A(P) ≠ 0`) and both of which are genuinely needed for the division.

Certificate verified first, symbolically over `ℚ[t₁…t_N, f, r]` for `N = 3…9`, in
`Campaigns/MathDB-Formalization/verify_352456.py`.
-/

namespace Principia.MathDB.P352456

open Finset

variable {N : ℕ} [NeZero N]

/-- The tangency defect of the edge from vertex `i` to vertex `i+1`: the chord of `𝒫`
through `t_i` and `t_{i+1}` touches `𝒞` exactly when this vanishes. -/
def tangencyDefect (f r : ℝ) (t : ZMod N → ℝ) (i : ZMod N) : ℝ :=
  (t i * t (i + 1) + 4 * f ^ 2) ^ 2 - r ^ 2 * (16 * f ^ 2 + (t i + t (i + 1)) ^ 2)

/-- `S₂ = ∑ t_i²(t_{i+1} - t_{i-1})`; the signed area of `P` is `-S₂/(8f)`. -/
def S2 (t : ZMod N → ℝ) : ℝ := ∑ i, t i ^ 2 * (t (i + 1) - t (i - 1))

/-- `S₃₂ = ∑ t_i³(t_{i+1}² - t_{i-1}²)`; the area centroid of `Q` has
`x`-coordinate `-S₃₂/(12f·S₂)`. -/
def S32 (t : ZMod N → ℝ) : ℝ := ∑ i, t i ^ 3 * (t (i + 1) ^ 2 - t (i - 1) ^ 2)

/-! ### Reindexing

Every step is the single move `∑_i F(i-1, i) = ∑_i F(i, i+1)`, which on `ZMod N` is
`Fintype.sum_equiv` along `Equiv.addRight 1`. -/

/-- The cyclic shift `i ↦ i + 1` does not change a sum over `ZMod N`. -/
theorem sum_shift (F : ZMod N → ℝ) : ∑ i, F (i + 1) = ∑ i, F i :=
  Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ _ (fun _ => rfl)

/-- `S₂` as a sum over EDGES. -/
theorem S2_edge (t : ZMod N → ℝ) : S2 t = ∑ i, (t i - t (i + 1)) * (t i * t (i + 1)) := by
  have h : ∑ i : ZMod N, t i ^ 2 * t (i - 1) = ∑ i : ZMod N, t (i + 1) ^ 2 * t i := by
    rw [← sum_shift (fun i => t i ^ 2 * t (i - 1))]
    exact Finset.sum_congr rfl (fun i _ => by rw [add_sub_cancel_right])
  simp only [S2, mul_sub]
  rw [Finset.sum_sub_distrib, h, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `S₃₂` as a sum over EDGES. -/
theorem S32_edge (t : ZMod N → ℝ) :
    S32 t = ∑ i, (t i - t (i + 1)) * (t i ^ 2 * t (i + 1) ^ 2) := by
  have h : ∑ i : ZMod N, t i ^ 3 * t (i - 1) ^ 2 = ∑ i : ZMod N, t (i + 1) ^ 3 * t i ^ 2 := by
    rw [← sum_shift (fun i => t i ^ 3 * t (i - 1) ^ 2)]
    exact Finset.sum_congr rfl (fun i _ => by rw [add_sub_cancel_right])
  simp only [S32, mul_sub]
  rw [Finset.sum_sub_distrib, h, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `∑ (t_i - t_{i+1}) · p(t_i, t_{i+1})` telescopes to `0` when `p` is the cyclotomic-style
factor `t_i² + t_i t_{i+1} + t_{i+1}²`, because `(a-b)(a²+ab+b²) = a³ - b³`. -/
theorem telescope_cube (t : ZMod N → ℝ) :
    ∑ i, (t i - t (i + 1)) * (t i ^ 2 + t i * t (i + 1) + t (i + 1) ^ 2) = 0 := by
  have h : ∑ i : ZMod N, (t i ^ 3 - t (i + 1) ^ 3) = 0 := by
    rw [Finset.sum_sub_distrib, sum_shift (fun i => t i ^ 3), sub_self]
  rw [← h]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `∑ (t_i - t_{i+1}) = 0`. -/
theorem telescope_lin (t : ZMod N → ℝ) : ∑ i, (t i - t (i + 1)) = 0 := by
  rw [Finset.sum_sub_distrib, sum_shift (fun i => t i), sub_self]

/-! ### The certificate -/

/-- **The telescoping certificate.**  An unconditional identity: no tangency, no guards,
every `N`.  This is the whole content of the `h₂` half of Conjecture 5. -/
theorem centroid_certificate (f r : ℝ) (t : ZMod N → ℝ) :
    S32 t + (8 * f ^ 2 - r ^ 2) * S2 t
      = ∑ i, (t i - t (i + 1)) * tangencyDefect f r t i := by
  rw [S32_edge, S2_edge, Finset.mul_sum, ← Finset.sum_add_distrib]
  have key : ∀ i : ZMod N,
      (t i - t (i + 1)) * (t i ^ 2 * t (i + 1) ^ 2)
          + (8 * f ^ 2 - r ^ 2) * ((t i - t (i + 1)) * (t i * t (i + 1)))
        = (t i - t (i + 1)) * tangencyDefect f r t i
          + (r ^ 2 * ((t i - t (i + 1)) *
              (t i ^ 2 + t i * t (i + 1) + t (i + 1) ^ 2))
            - 16 * f ^ 2 * (f ^ 2 - r ^ 2) * (t i - t (i + 1))) := by
    intro i
    simp only [tangencyDefect]
    ring
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, telescope_cube,
    telescope_lin]
  ring

/-- **Conjecture 5's constant.**  Under tangency, the area centroid of the polar polygon has
`x`-coordinate `(8f² - r²)/(12f)`, for every `N` and with none of the source's guards. -/
theorem polar_centroid_x (f r : ℝ) (hf : f ≠ 0) (t : ZMod N → ℝ)
    (htan : ∀ i, tangencyDefect f r t i = 0) (hA : S2 t ≠ 0) :
    -S32 t / (12 * f * S2 t) = (8 * f ^ 2 - r ^ 2) / (12 * f) := by
  have hcert := centroid_certificate f r t
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by rw [htan i, mul_zero]),
    Finset.sum_const_zero] at hcert
  have hS32 : S32 t = -((8 * f ^ 2 - r ^ 2) * S2 t) := by linarith
  rw [hS32]
  field_simp

/-! ### The three hypothesis-free "moreover" identities

None of these needs tangency either — they are pure shoelace algebra. -/

/-- `A(Q) = -A(P)/2`.  With `A(P) = -S₂/(8f)` and `A(Q) = S₂/(16f)` this is the statement
that the two shoelace sums agree up to the factor `-1/2`, which holds coefficientwise. -/
theorem area_polar (f : ℝ) (hf : f ≠ 0) (t : ZMod N → ℝ) :
    S2 t / (16 * f) = -(-S2 t / (8 * f)) / 2 := by
  field_simp
  ring

/-- The `y`-coordinate of the AREA centroid is unchanged: the difference is
`∑ t_i²(t_{i+1}² - t_{i-1}²)`, which telescopes. -/
theorem centroid2_y (t : ZMod N → ℝ) :
    ∑ i, t i ^ 2 * (t (i + 1) ^ 2 - t (i - 1) ^ 2) = 0 := by
  have h : ∑ i : ZMod N, t i ^ 2 * t (i - 1) ^ 2 = ∑ i : ZMod N, t (i + 1) ^ 2 * t i ^ 2 := by
    rw [← sum_shift (fun i => t i ^ 2 * t (i - 1) ^ 2)]
    exact Finset.sum_congr rfl (fun i _ => by rw [add_sub_cancel_right])
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib, h, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero (fun i _ => by ring)

/-- The `y`-coordinate of the VERTEX centroid is unchanged: `Q_i` has `y = (t_i+t_{i+1})/2`,
and averaging that over the cycle returns the average of the `t_i`. -/
theorem centroid0_y (t : ZMod N → ℝ) :
    ∑ i, (t i + t (i + 1)) / 2 = ∑ i, t i := by
  rw [← Finset.sum_div, Finset.sum_add_distrib, sum_shift (fun i => t i)]
  ring

/-! ### The hypotheses are inhabited: an exact tangential triangle

Every theorem above is universally quantified over a configuration `t` satisfying tangency with
`S₂ t ≠ 0`, and **nothing above exhibited one** — so nothing above ruled out `polar_centroid_x`
being an empty implication.  No gate can see that: an empty implication is axiom-free, gates clean
and passes `check_unused_hypotheses`, because the hypothesis really is used.

Worse, the easy solutions are exactly the excluded ones.  `S₂` vanishes identically whenever any
two coordinates coincide (checked symbolically), so every symmetric ansatz is degenerate: at
`f = 1`, `t = (-6, 2, 2)` with `r² = 2` satisfies **all three** tangency conditions and still has
`S₂ = 0`.  The area hypothesis is precisely what rules the cheap witnesses out.

**How the witness was found.**  Subtracting two tangency conditions factors exactly:

    g(t₀,t₁) − g(t₁,t₂) = (t₀ − t₂) · [t₁²(t₀+t₂) + 8t₁ − r²(t₀+2t₁+t₂)]

and with `s = t₀+t₁+t₂` the bracket is `−P(t₁)` for `P(x) = x³ − sx² − (8−r²)x + r²s`.  So in a
configuration with distinct coordinates **all three coordinates are roots of one cubic** — the
constraint names the object.  Since `P(tᵢ) = 0` makes the pairwise differences vanish, the three
defects are then all *equal*, so they vanish together.  At `s = 0` the cubic is `x³ − (8−r²)x`,
whose roots are `0, ±√(8−r²)`; that is the witness below, and `r = 2√2 − 2` (inside the source's
own range `0 < r < f`) is what makes it tangential.

**This does not close the row.**  Both residues named above stand: the vertex-centroid locus and
the completeness of the line.  What it does is guarantee the statements already proved are about
something. -/

/-- `√2`, kept as a local abbreviation so the witness arithmetic stays readable. -/
noncomputable def sqrt2 : ℝ := Real.sqrt 2

theorem sqrt2_sq : sqrt2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem sqrt2_pos : 0 < sqrt2 := Real.sqrt_pos.mpr (by norm_num)

theorem sqrt2_gt : 1.4 < sqrt2 := by nlinarith [sqrt2_sq, sqrt2_pos]

/-- The `N = 3` closure radius at `f = 1`: `r = 2√2 − 2 ≈ 0.828`, which satisfies the source's
guard `0 < r < f`. -/
noncomputable def rClose : ℝ := 2 * sqrt2 - 2

theorem rClose_sq : rClose ^ 2 = 12 - 8 * sqrt2 := by
  simp only [rClose]; nlinarith [sqrt2_sq]

/-- The vertex parameter `u = √(8√2 − 4)`, the positive root of the cubic at `s = 0`. -/
noncomputable def uClose : ℝ := Real.sqrt (8 * sqrt2 - 4)

theorem uClose_sq : uClose ^ 2 = 8 * sqrt2 - 4 := Real.sq_sqrt (by nlinarith [sqrt2_gt])

theorem uClose_pos : 0 < uClose := Real.sqrt_pos.mpr (by nlinarith [sqrt2_gt])

/-- The witness triangle `(0, u, −u)`. -/
noncomputable def tClose : ZMod 3 → ℝ := ![0, uClose, -uClose]

theorem tc0 : tClose 0 = 0 := by simp [tClose]
theorem tc1 : tClose 1 = uClose := by simp [tClose]
theorem tc2 : tClose 2 = -uClose := by simp [tClose]

theorem tc3 : tClose 3 = 0 := by
  rw [show (3 : ZMod 3) = 0 from by decide]; exact tc0

/-- Edge `0 → 1` is tangent. -/
theorem tangency_zero : tangencyDefect 1 rClose tClose 0 = 0 := by
  have e : ((0 : ZMod 3) + 1) = 1 := by decide
  simp only [tangencyDefect, e, tc0, tc1, rClose_sq]
  linear_combination (8 * sqrt2 - 12) * uClose_sq + (64 : ℝ) * sqrt2_sq

/-- Edge `1 → 2` is tangent.  This is the edge through `u` and `−u`, where the `u⁴` term appears
and the combination needs the `u² + 8√2 − 12` coefficient. -/
theorem tangency_one : tangencyDefect 1 rClose tClose 1 = 0 := by
  have e : ((1 : ZMod 3) + 1) = 2 := by decide
  simp only [tangencyDefect, e, tc1, tc2, rClose_sq]
  linear_combination (uClose ^ 2 + 8 * sqrt2 - 12) * uClose_sq + (64 : ℝ) * sqrt2_sq

/-- Edge `2 → 0` is tangent. -/
theorem tangency_two : tangencyDefect 1 rClose tClose 2 = 0 := by
  have e : ((2 : ZMod 3) + 1) = 0 := by decide
  simp only [tangencyDefect, e, tc2, tc0, rClose_sq]
  linear_combination (8 * sqrt2 - 12) * uClose_sq + (64 : ℝ) * sqrt2_sq

/-- **All three edges are tangent to `𝒞`.** -/
theorem tangency_tClose : ∀ i, tangencyDefect 1 rClose tClose i = 0 := by
  intro i
  fin_cases i
  · exact tangency_zero
  · exact tangency_one
  · exact tangency_two

/-- `S₂ = −2u³`, so the area is nonzero and the triangle is non-degenerate. -/
theorem S2_tClose : S2 tClose = -2 * uClose ^ 3 := by
  have h : (univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  simp only [S2, h]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [tc0, tc1, tc2, tc3, show ((0 : ZMod 3) + 1) = 1 from by decide,
    show ((0 : ZMod 3) - 1) = 2 from by decide,
    show ((1 : ZMod 3) + 1) = 2 from by decide,
    show ((1 : ZMod 3) - 1) = 0 from by decide,
    show ((2 : ZMod 3) + 1) = 0 from by decide,
    show ((2 : ZMod 3) - 1) = 1 from by decide]
  ring

theorem S2_tClose_ne : S2 tClose ≠ 0 := by
  rw [S2_tClose]
  have h : 0 < uClose ^ 3 := pow_pos uClose_pos 3
  intro hEq
  nlinarith

/-- **`polar_centroid_x`'s hypotheses are inhabited**, so it is not an empty implication. -/
theorem exists_tangential :
    ∃ (r : ℝ) (t : ZMod 3 → ℝ), (∀ i, tangencyDefect 1 r t i = 0) ∧ S2 t ≠ 0 :=
  ⟨rClose, tClose, tangency_tClose, S2_tClose_ne⟩

/-- **Conjecture 5's constant at an explicit triangle, with no hypothesis carried.** -/
theorem centroid_at_witness :
    -S32 tClose / (12 * 1 * S2 tClose) = (8 * (1 : ℝ) ^ 2 - rClose ^ 2) / (12 * 1) :=
  polar_centroid_x 1 rClose one_ne_zero tClose tangency_tClose S2_tClose_ne

/-! ### The whole one-parameter family, not just one triangle

The witness above is one member of something larger, and this section proves it.  Yesterday the
closure equation `R² − 24R + 16 = 0` (with `R = r²`) was recorded in the row as a **lead**, because
it came from reducing the *sum* of the three defects by a hand-rolled symmetric reduction with no
positive control.  It is now a **result**, and the proof needs no root extraction at all:

* `defect_diff` is a **pure ring identity** — differencing two defects factors as
  `(a − c) · (−cubic(b))`.  The antisymmetric factor is the degeneracy locus; the other is the
  cubic every coordinate satisfies.  So on the family the three defects are all *equal*.
* the three defects **sum** to `R² − 24R + 16` by a two-term certificate against the symmetric
  conditions (`hsum` inside `defect_eq_zero_of_family`).
* equal + summing to `3·0` forces each to vanish.

`s` never appears: it *is* `t₀+t₁+t₂`, so `OnFamily` carries only the two remaining symmetric
conditions.  The closure equation constrains `r` **alone**, which is why the family is
one-parameter — and that is exactly the mechanism the source's *"sweeps the line"* claim needs.
It does **not** prove that claim: completeness additionally needs every point of the line to be
attained, which is still a residue of this row. -/

/-- **Differencing two tangency defects is a pure ring identity**, factoring through the cubic. -/
theorem defect_diff (a b c R : ℝ) :
    ((a * b + 4) ^ 2 - R * (16 + (a + b) ^ 2))
        - ((b * c + 4) ^ 2 - R * (16 + (b + c) ^ 2))
      = (a - c) * (-(b ^ 3 - (a + b + c) * b ^ 2 + (R - 8) * b + R * (a + b + c))) := by
  ring

/-- **Every edge defect vanishes on the closure locus** — pure algebra on three reals, with no
root extraction: the pairwise equality (via `defect_diff`) plus the sum certificate. -/
theorem defect_eq_zero_of_family {a b c R : ℝ}
    (h2 : a * b + b * c + c * a = R - 8)
    (h3 : a * b * c = -(R * (a + b + c)))
    (hcl : R ^ 2 - 24 * R + 16 = 0) :
    (a * b + 4) ^ 2 - R * (16 + (a + b) ^ 2) = 0 := by
  have hb : b ^ 3 - (a + b + c) * b ^ 2 + (R - 8) * b + R * (a + b + c) = 0 := by
    linear_combination (-b) * h2 + h3
  have hcc : c ^ 3 - (a + b + c) * c ^ 2 + (R - 8) * c + R * (a + b + c) = 0 := by
    linear_combination (-c) * h2 + h3
  have e1 : ((a * b + 4) ^ 2 - R * (16 + (a + b) ^ 2))
      - ((b * c + 4) ^ 2 - R * (16 + (b + c) ^ 2)) = 0 := by
    linear_combination (-(a - c)) * hb
  have e2 : ((b * c + 4) ^ 2 - R * (16 + (b + c) ^ 2))
      - ((c * a + 4) ^ 2 - R * (16 + (c + a) ^ 2)) = 0 := by
    linear_combination (-(b - a)) * hcc
  have hsum : ((a * b + 4) ^ 2 - R * (16 + (a + b) ^ 2))
      + ((b * c + 4) ^ 2 - R * (16 + (b + c) ^ 2))
      + ((c * a + 4) ^ 2 - R * (16 + (c + a) ^ 2)) = 3 * (R ^ 2 - 24 * R + 16) := by
    linear_combination ((a * b + b * c + c * a) + 3 * R) * h2 + (-2 * (a + b + c)) * h3
  linarith [e1, e2, hsum, hcl]

/-- A triple lies on the closure family for `r`: the two symmetric conditions that make every
coordinate a root of one cubic.  The third Vieta relation is vacuous, since `s` *is* the
coordinate sum. -/
def OnFamily (r : ℝ) (t : ZMod 3 → ℝ) : Prop :=
  t 0 * t 1 + t 1 * t 2 + t 2 * t 0 = r ^ 2 - 8 ∧
    t 0 * t 1 * t 2 = -(r ^ 2 * (t 0 + t 1 + t 2))

/-- The closure equation, on `r` alone — which is what makes the family one-parameter. -/
def ClosureEq (r : ℝ) : Prop := (r ^ 2) ^ 2 - 24 * r ^ 2 + 16 = 0

theorem rClose_closureEq : ClosureEq rClose := by
  simp only [ClosureEq, rClose_sq]
  nlinarith [sqrt2_sq]

/-- **EVERY MEMBER OF THE FAMILY IS TANGENTIAL** at the closure radius. -/
theorem tangency_of_family {r : ℝ} {t : ZMod 3 → ℝ}
    (hf : OnFamily r t) (hcl : ClosureEq r) : ∀ i, tangencyDefect 1 r t i = 0 := by
  obtain ⟨h2, h3⟩ := hf
  rw [ClosureEq] at hcl
  intro i
  fin_cases i
  · simp only [tangencyDefect]
    norm_num
    exact defect_eq_zero_of_family (a := t 0) (b := t 1) (c := t 2) h2 h3 hcl
  · simp only [tangencyDefect]
    norm_num
    exact defect_eq_zero_of_family (a := t 1) (b := t 2) (c := t 0)
      (by linear_combination h2) (by linear_combination h3) hcl
  · simp only [tangencyDefect]
    norm_num
    exact defect_eq_zero_of_family (a := t 2) (b := t 0) (c := t 1)
      (by linear_combination h2) (by linear_combination h3) hcl

/-- The explicit witness is the `s = 0` member of this family. -/
theorem tClose_onFamily : OnFamily rClose tClose := by
  refine ⟨?_, ?_⟩
  · rw [tc0, tc1, tc2, rClose_sq]
    linear_combination -uClose_sq
  · rw [tc0, tc1, tc2]
    ring

/-- `tangency_tClose` re-derived through the general theorem — **two independent proofs of the same
fact**, the direct edge computation and the family route, which is why this is kept. -/
theorem tangency_tClose_via_family : ∀ i, tangencyDefect 1 rClose tClose i = 0 :=
  tangency_of_family tClose_onFamily rClose_closureEq

/-! ### Toward the second residue: non-degeneracy characterised, and the family parameterised

The row's remaining residues are the vertex-centroid locus and the COMPLETENESS of the line.  This
section attacks the second, and stops well short of it.

* `S2_factor` is the Vandermonde-style factorisation `S₂ = −(t₀−t₁)(t₁−t₂)(t₂−t₀)`, a pure `ring`
  identity once the cyclic indices are resolved.  It **upgrades the degeneracy fact to an iff**:
  the earlier note recorded only that `S₂` vanishes when two coordinates coincide; `S2_ne_zero_iff`
  now says the area is nonzero exactly when all three are distinct.
* `exists_onFamily_of_param` makes the family **constructively one-parameter**: fix the third
  coordinate `c`, and the sum and product of the other two are FORCED (`famSum`, `famProd`) by the
  two symmetric conditions, so the triple is the roots of one quadratic.  With
  `tangency_of_family` this yields a tangential triangle for every `c` with `r² ≠ c²` and a
  nonnegative discriminant.

**WHAT THIS IS NOT.**  It is the parameterisation the *sweeps a line* claim needs, not the claim.
Completeness additionally requires (i) that the admissible `c` form a set large enough to reach
every point of the line, and (ii) the centroid's SECOND coordinate as a function of `c` — and the
module still has no point-valued centroid, only the `x`-coordinate identity.  Both residues stand. -/

/-- **`S₂` FACTORS.**  Over `ZMod 3` the shoelace sum is the Vandermonde-style product. -/
theorem S2_factor (t : ZMod 3 → ℝ) :
    S2 t = -((t 0 - t 1) * (t 1 - t 2) * (t 2 - t 0)) := by
  have h : (univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  -- rewrite the INDICES first: `norm_num` renormalises them to `-1` and `3` if it runs first.
  have i01 : ((0 : ZMod 3) + 1) = 1 := by decide
  have i0m : ((0 : ZMod 3) - 1) = 2 := by decide
  have i11 : ((1 : ZMod 3) + 1) = 2 := by decide
  have i1m : ((1 : ZMod 3) - 1) = 0 := by decide
  have i21 : ((2 : ZMod 3) + 1) = 0 := by decide
  have i2m : ((2 : ZMod 3) - 1) = 1 := by decide
  simp only [S2, h]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    i01, i0m, i11, i1m, i21, i2m]
  ring

/-- **The area is nonzero exactly when the three parameters are pairwise distinct** — the
degeneracy fact, now in both directions. -/
theorem S2_ne_zero_iff (t : ZMod 3 → ℝ) :
    S2 t ≠ 0 ↔ t 0 ≠ t 1 ∧ t 1 ≠ t 2 ∧ t 2 ≠ t 0 := by
  rw [S2_factor, neg_ne_zero, mul_ne_zero_iff, mul_ne_zero_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨sub_ne_zero.mp h1, sub_ne_zero.mp h2, sub_ne_zero.mp h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨sub_ne_zero.mpr h1, sub_ne_zero.mpr h2⟩, sub_ne_zero.mpr h3⟩

/-- Family membership on an explicit triple.  This isolates the vector-indexing step, which `rw`
cannot perform because the numerals reach `ZMod 3` by a different `OfNat` path than the one the
goal displays; `show` goes through because the two are definitionally equal. -/
theorem onFamily_of_roots (r a b c : ℝ)
    (h2 : a * b + b * c + c * a = r ^ 2 - 8)
    (h3 : a * b * c = -(r ^ 2 * (a + b + c))) :
    OnFamily r ![a, b, c] := by
  constructor
  · show a * b + b * c + c * a = r ^ 2 - 8
    exact h2
  · show a * b * c = -(r ^ 2 * (a + b + c))
    exact h3

/-- Given the third coordinate `c`, the SUM of the other two is forced. -/
noncomputable def famSum (r c : ℝ) : ℝ := c * (8 - 2 * r ^ 2) / (r ^ 2 - c ^ 2)

/-- ...and then so is their PRODUCT. -/
noncomputable def famProd (r c : ℝ) : ℝ := r ^ 2 - 8 - c * famSum r c

/-- **THE FAMILY IS CONSTRUCTIVELY ONE-PARAMETER.**  For any `c` with `r² ≠ c²` and a nonnegative
discriminant, the triple whose third coordinate is `c` and whose first two are the roots of
`z² − (famSum)·z + famProd` lies on the closure family. -/
theorem exists_onFamily_of_param (r c : ℝ) (hne : r ^ 2 - c ^ 2 ≠ 0)
    (hdisc : 0 ≤ famSum r c ^ 2 - 4 * famProd r c) :
    ∃ t : ZMod 3 → ℝ, OnFamily r t ∧ t 2 = c := by
  set m := famSum r c with hm
  set p := famProd r c with hp
  set d := Real.sqrt (m ^ 2 - 4 * p) with hd
  have hd2 : d ^ 2 = m ^ 2 - 4 * p := Real.sq_sqrt hdisc
  have hP : p + c * m = r ^ 2 - 8 := by rw [hp, famProd]; ring
  have hS : m * (r ^ 2 - c ^ 2) = c * (8 - 2 * r ^ 2) := by
    rw [hm, famSum]; field_simp
  have hpd : p = r ^ 2 - 8 - c * m := by rw [hp, famProd, hm]
  refine ⟨![(m + d) / 2, (m - d) / 2, c], onFamily_of_roots r _ _ c ?_ ?_, by simp⟩
  · have hprod : ((m + d) / 2) * ((m - d) / 2) = p := by
      have he : ((m + d) / 2) * ((m - d) / 2) = (m ^ 2 - d ^ 2) / 4 := by ring
      rw [he, hd2]; ring
    have hsum : (m + d) / 2 + (m - d) / 2 = m := by ring
    calc ((m + d) / 2) * ((m - d) / 2) + ((m - d) / 2) * c + c * ((m + d) / 2)
        = ((m + d) / 2) * ((m - d) / 2) + c * (((m + d) / 2) + ((m - d) / 2)) := by ring
      _ = p + c * m := by rw [hprod, hsum]
      _ = r ^ 2 - 8 := hP
  · have hprod : ((m + d) / 2) * ((m - d) / 2) = p := by
      have he : ((m + d) / 2) * ((m - d) / 2) = (m ^ 2 - d ^ 2) / 4 := by ring
      rw [he, hd2]; ring
    have hsum : (m + d) / 2 + (m - d) / 2 = m := by ring
    calc ((m + d) / 2) * ((m - d) / 2) * c
        = (((m + d) / 2) * ((m - d) / 2)) * c := by ring
      _ = p * c := by rw [hprod]
      _ = -(r ^ 2 * (m + c)) := by rw [hpd]; nlinarith [hS]
      _ = -(r ^ 2 * (((m + d) / 2) + ((m - d) / 2) + c)) := by rw [hsum]

/-! ### At `N = 3` the centroid is elementary, and the family is unconditionally infinite

The polar polygon of a triangle is a triangle, whose area centroid is the AVERAGE OF ITS VERTICES.
With `Qᵢ = (−tᵢtᵢ₊₁/(4f), (tᵢ+tᵢ₊₁)/2)` that makes both coordinates elementary at `f = 1`:

* `x`-coordinate `= −(t₀t₁ + t₁t₂ + t₂t₀)/12`, which on the family is `(8 − r²)/12 = h₂`,
  **constant**;
* `y`-coordinate `= (t₀ + t₁ + t₂)/3 = s/3`, with `s` the coordinate sum.

`S32_eq_e2_mul_S2` is what connects that to the module's own formula: for a triangle
`S₃₂ = e₂ · S₂` identically, so `−S₃₂/(12f·S₂) = −e₂/(12f)`.  `centroid_x_eq_of_e2` is then
**strictly stronger than `polar_centroid_x`** — the constant needs only the second symmetric
condition, not every edge tangent.

`famProd_neg` is the step that makes the family unconditional: on `0 ≤ c < r` with `r² < 4` the
forced product is negative, so the discriminant is automatically positive and
`exists_onFamily_of_lt` needs no hypothesis to supply.  `exists_tangential_of_lt` delivers a
tangential triangle for **every** `c` in `[0, rClose)`.

**WHY THIS STILL DOES NOT CLOSE THE RESIDUE, and the gap is now exact.**  Since `s` is free on the
family, `C_y = s/3` should take every real value, which would make the locus the complete line.
Measured exactly (`verify_352456.py` is not extended to this; the computation is recorded in the
row): the cubic's discriminant at the closure radius is
`(48−32√2)·s⁴ + (7424√2−10368)·s² + (5632√2−6400)`, whose three coefficients are all POSITIVE, so
the cubic has three distinct real roots for every `s`.  Turning that into Lean needs *"a real cubic
with positive discriminant has three real roots"*, and **Mathlib does not have it** — every theorem
in `Mathlib/Algebra/CubicDiscriminant.lean` ASSUMES the roots split and derives Vieta or
discriminant facts from that.  The alternative is an intermediate-value argument on `c ↦ s(c)` over
`[0, r)` together with its blow-up as `c → r⁻`.  Either way the remaining step is named. -/

/-- **`S₃₂ = e₂ · S₂` for a triangle** — a pure `ring` identity. -/
theorem S32_eq_e2_mul_S2 (t : ZMod 3 → ℝ) :
    S32 t = (t 0 * t 1 + t 1 * t 2 + t 2 * t 0) * S2 t := by
  have h : (univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  have i01 : ((0 : ZMod 3) + 1) = 1 := by decide
  have i0m : ((0 : ZMod 3) - 1) = 2 := by decide
  have i11 : ((1 : ZMod 3) + 1) = 2 := by decide
  have i1m : ((1 : ZMod 3) - 1) = 0 := by decide
  have i21 : ((2 : ZMod 3) + 1) = 0 := by decide
  have i2m : ((2 : ZMod 3) - 1) = 1 := by decide
  simp only [S32, S2, h]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    i01, i0m, i11, i1m, i21, i2m]
  ring

/-- **The polar centroid's `x`-coordinate is `(8 − r²)/12` from the SECOND SYMMETRIC CONDITION
ALONE** — strictly stronger than `polar_centroid_x`, which needs every edge tangent. -/
theorem centroid_x_eq_of_e2 (r : ℝ) (t : ZMod 3 → ℝ)
    (he2 : t 0 * t 1 + t 1 * t 2 + t 2 * t 0 = r ^ 2 - 8) (hS : S2 t ≠ 0) :
    -S32 t / (12 * 1 * S2 t) = (8 * (1 : ℝ) ^ 2 - r ^ 2) / (12 * 1) := by
  rw [S32_eq_e2_mul_S2, he2]
  field_simp
  ring

/-- On `[0, r)` the forced product is NEGATIVE, which is what makes the discriminant automatic. -/
theorem famProd_neg (r c : ℝ) (hr : 0 < r) (hr4 : r ^ 2 < 4) (hc0 : 0 ≤ c) (hcr : c < r) :
    famProd r c < 0 := by
  have hden : 0 < r ^ 2 - c ^ 2 := by nlinarith
  have hnum : 0 ≤ c * (8 - 2 * r ^ 2) := by nlinarith
  have hsum : 0 ≤ famSum r c := by
    rw [famSum]
    exact div_nonneg hnum hden.le
  have : 0 ≤ c * famSum r c := mul_nonneg hc0 hsum
  rw [famProd]
  nlinarith

/-- Hence the discriminant hypothesis is DISCHARGED on `[0, r)`. -/
theorem disc_nonneg_of_lt (r c : ℝ) (hr : 0 < r) (hr4 : r ^ 2 < 4) (hc0 : 0 ≤ c) (hcr : c < r) :
    0 ≤ famSum r c ^ 2 - 4 * famProd r c := by
  have h := famProd_neg r c hr hr4 hc0 hcr
  nlinarith [sq_nonneg (famSum r c)]

/-- **AN EXPLICIT INFINITE FAMILY, UNCONDITIONALLY**: for every `c` in `[0, r)` the member with
third coordinate `c` exists, with no discriminant hypothesis to supply. -/
theorem exists_onFamily_of_lt (r c : ℝ) (hr : 0 < r) (hr4 : r ^ 2 < 4)
    (hc0 : 0 ≤ c) (hcr : c < r) :
    ∃ t : ZMod 3 → ℝ, OnFamily r t ∧ t 2 = c :=
  exists_onFamily_of_param r c (by nlinarith) (disc_nonneg_of_lt r c hr hr4 hc0 hcr)

theorem rClose_pos : 0 < rClose := by
  simp only [rClose]
  nlinarith [sqrt2_gt, sqrt2_sq]

theorem rClose_sq_lt_four : rClose ^ 2 < 4 := by
  rw [rClose_sq]
  nlinarith [sqrt2_gt, sqrt2_sq]

/-- **A TANGENTIAL TRIANGLE FOR EVERY `c` IN `[0, rClose)`** — so the family is infinite, and
that is proved rather than inferred from the numerics. -/
theorem exists_tangential_of_lt (c : ℝ) (hc0 : 0 ≤ c) (hcr : c < rClose) :
    ∃ t : ZMod 3 → ℝ, (∀ i, tangencyDefect 1 rClose t i = 0) ∧ t 2 = c := by
  obtain ⟨t, hf, hc⟩ := exists_onFamily_of_lt rClose c rClose_pos rClose_sq_lt_four hc0 hcr
  exact ⟨t, tangency_of_family hf rClose_closureEq, hc⟩

/-- The polar polygon's vertex-centroid `y`-coordinate is the mean of the parameters — the
module's `centroid0_y` specialised to a triangle. -/
theorem centroid_y_eq (t : ZMod 3 → ℝ) :
    (∑ i, (t i + t (i + 1)) / 2) / 3 = (t 0 + t 1 + t 2) / 3 := by
  rw [centroid0_y]
  have h : (univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-! ### The locus is INFINITE — proved, not inferred from the numerics

`exists_tangential_of_lt` gives a triangle for every `c` in `[0, rClose)`, but nothing yet said
those triangles have *different* centroids.  They do: on the family the coordinate sum is
DETERMINED by the third coordinate (`sum_eq_of_onFamily`, derived from the two symmetric conditions
rather than read off the construction), and `c ↦ famSum r c + c` is strictly monotone there — the
whole inequality collapsing to `−r² < c₁c₂`, which is free.  So distinct `c` give distinct
`C_y = s/3`, and `centroidY_infinite` concludes the attained set is infinite.

That is short of the complete line and stays short of it: the gap named above is unchanged.  But it
is the first qualitative fact this row has had about the LOCUS rather than about individual
triangles — the locus is not a finite set of points. -/

/-- **The coordinate sum is DETERMINED by the third coordinate on the family.**  Derived from the
two symmetric conditions, so it applies to any member, not only the constructed one. -/
theorem sum_eq_of_onFamily (r c : ℝ) (t : ZMod 3 → ℝ) (hf : OnFamily r t) (hc : t 2 = c)
    (hne : r ^ 2 - c ^ 2 ≠ 0) : t 0 + t 1 + t 2 = famSum r c + c := by
  obtain ⟨h2, h3⟩ := hf
  rw [hc] at h2 h3
  -- an EQUALITY, so the certificate is a linear combination, not an inequality search:
  -- the goal is `h3 - c * h2`.
  have hm : (t 0 + t 1) * (r ^ 2 - c ^ 2) = c * (8 - 2 * r ^ 2) := by
    linear_combination (-c) * h2 + h3
  have hsum : t 0 + t 1 = famSum r c := by
    rw [famSum, eq_div_iff hne]
    exact hm
  rw [hc, hsum]

/-- **`s(c) = famSum r c + c` is STRICTLY MONOTONE on `[0, r)`**; the inequality collapses to
`−r² < c₁c₂`. -/
theorem famTotal_strictMonoOn (r : ℝ) (hr : 0 < r) (hr4 : r ^ 2 < 4) :
    StrictMonoOn (fun c => famSum r c + c) (Set.Ico 0 r) := by
  intro a ha b hb hab
  simp only [Set.mem_Ico] at ha hb
  obtain ⟨ha0, har⟩ := ha
  obtain ⟨hb0, hbr⟩ := hb
  have hK : 0 < 8 - 2 * r ^ 2 := by nlinarith
  have hDa : 0 < r ^ 2 - a ^ 2 := by nlinarith
  have hDb : 0 < r ^ 2 - b ^ 2 := by nlinarith
  have hfirst : famSum r a ≤ famSum r b := by
    rw [famSum, famSum, div_le_div_iff₀ hDa hDb]
    -- the difference FACTORS; supply the factorisation rather than a search
    have key : b * (8 - 2 * r ^ 2) * (r ^ 2 - a ^ 2) - a * (8 - 2 * r ^ 2) * (r ^ 2 - b ^ 2)
        = (8 - 2 * r ^ 2) * (b - a) * (r ^ 2 + a * b) := by ring
    have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
    have hrab : (0 : ℝ) ≤ r ^ 2 + a * b := by positivity
    have hpos : (0 : ℝ) ≤ (8 - 2 * r ^ 2) * (b - a) * (r ^ 2 + a * b) :=
      mul_nonneg (mul_nonneg hK.le hba.le) hrab
    linarith [key, hpos]
  simp only
  linarith

theorem famTotal_injOn (r : ℝ) (hr : 0 < r) (hr4 : r ^ 2 < 4) :
    Set.InjOn (fun c => famSum r c + c) (Set.Ico 0 r) :=
  (famTotal_strictMonoOn r hr hr4).injOn

/-- **THE ATTAINED CENTROID `y`-COORDINATES ARE INFINITE**, so the locus is not a finite set of
points — the first qualitative fact this row has had about the locus itself. -/
theorem centroidY_infinite :
    {y : ℝ | ∃ t : ZMod 3 → ℝ,
        (∀ i, tangencyDefect 1 rClose t i = 0) ∧ (t 0 + t 1 + t 2) / 3 = y}.Infinite := by
  set f : ℝ → ℝ := fun c => (famSum rClose c + c) / 3 with hf
  have hinj : Set.InjOn f (Set.Ico 0 rClose) := by
    intro a ha b hb hEq
    refine famTotal_injOn rClose rClose_pos rClose_sq_lt_four ha hb ?_
    have h3 : (famSum rClose a + a) / 3 = (famSum rClose b + b) / 3 := hEq
    linarith
  have hsub : f '' (Set.Ico 0 rClose) ⊆
      {y : ℝ | ∃ t : ZMod 3 → ℝ,
        (∀ i, tangencyDefect 1 rClose t i = 0) ∧ (t 0 + t 1 + t 2) / 3 = y} := by
    rintro y ⟨c, hc, rfl⟩
    simp only [Set.mem_Ico] at hc
    obtain ⟨hc0, hcr⟩ := hc
    obtain ⟨t, hfam, hc2⟩ := exists_onFamily_of_lt rClose c rClose_pos rClose_sq_lt_four hc0 hcr
    have hne : rClose ^ 2 - c ^ 2 ≠ 0 := by
      have hlt : c ^ 2 < rClose ^ 2 := by nlinarith [rClose_pos]
      intro h
      nlinarith
    refine ⟨t, tangency_of_family hfam rClose_closureEq, ?_⟩
    rw [sum_eq_of_onFamily rClose c t hfam hc2 hne]
  exact Set.Infinite.mono hsub ((Set.Ico_infinite rClose_pos).image hinj)

/-! ### RESIDUE (ii) IS CLOSED AT `N = 3`: the locus is the COMPLETE line

The previous entry got the locus infinite; this one gets it surjective, which is the whole of
residue (ii) at `N = 3`.  The route avoids the missing cubic-roots fact entirely:

* `onFamily_neg` — negating a triple preserves membership (`e₂` even, `e₃` and `e₁` both odd), so
  the negative half of the line comes free from the positive half;
* `famSum_ge_near` — the endpoint blow-up `famSum r c ≥ (8−2r²)/(4(r−c))` for `r/2 ≤ c < r`, whose
  proof is the factorisation `(8−2r²)(r−c)(3c−r) ≥ 0`;
* `exists_sum_ge` — hence `s(c) = famSum r c + c` is unbounded above, with the explicit choice
  `δ = min(r/2, (8−2r²)/(4(y+1)))`;
* `exists_sum_eq` — the intermediate value theorem on `[0, r−δ]` then attains every `y ≥ 0`;
* `centroidY_surjective` — every real `Y` is a polar-centroid `y`-coordinate.

Together with `centroid_x_eq_of_e2`, which pins the `x`-coordinate at `h₂` for every member, the
locus of polar centroids over the closure family is **exactly the line `x = h₂`**.

**WHAT REMAINS, precisely.**  This is `N = 3` only: the family construction is a triangle
construction, so nothing here speaks to the row's *arbitrary* `N`.  Residue (i), the
vertex-centroid locus `h₀`, is untouched for general `N` — at `N = 3` it coincides with `h₂`
because the two centroids agree for a triangle, but that coincidence is exactly what fails for
`N ≥ 4`, which is where the row's open half lives. -/

/-- **Negating a triple preserves family membership**: `e₂` is even, while `e₃` and `e₁` are both
odd, so `e₃ = −r²e₁` is unchanged. -/
theorem onFamily_neg (r : ℝ) (t : ZMod 3 → ℝ) (h : OnFamily r t) :
    OnFamily r (fun i => -t i) := by
  obtain ⟨h2, h3⟩ := h
  constructor
  · show (-t 0) * (-t 1) + (-t 1) * (-t 2) + (-t 2) * (-t 0) = r ^ 2 - 8
    linear_combination h2
  · show (-t 0) * (-t 1) * (-t 2) = -(r ^ 2 * ((-t 0) + (-t 1) + (-t 2)))
    linear_combination -h3

theorem famSum_zero (r : ℝ) : famSum r 0 = 0 := by simp [famSum]

/-- **The endpoint blow-up.**  For `r/2 ≤ c < r`, `famSum r c ≥ (8−2r²)/(4(r−c))`. -/
theorem famSum_ge_near (r c : ℝ) (hr : 0 < r) (hr4 : r ^ 2 < 4)
    (hc : r / 2 ≤ c) (hcr : c < r) :
    (8 - 2 * r ^ 2) / (4 * (r - c)) ≤ famSum r c := by
  have hK : 0 < 8 - 2 * r ^ 2 := by nlinarith
  have hrc : 0 < r - c := by linarith
  have hden : 0 < r ^ 2 - c ^ 2 := by nlinarith
  rw [famSum, div_le_div_iff₀ (by positivity) hden]
  have key : c * (8 - 2 * r ^ 2) * (4 * (r - c)) - (8 - 2 * r ^ 2) * (r ^ 2 - c ^ 2)
      = (8 - 2 * r ^ 2) * (r - c) * (3 * c - r) := by ring
  have h3c : (0 : ℝ) ≤ 3 * c - r := by linarith
  have hpos : (0 : ℝ) ≤ (8 - 2 * r ^ 2) * (r - c) * (3 * c - r) :=
    mul_nonneg (mul_nonneg hK.le hrc.le) h3c
  linarith [key, hpos]

/-- The total `s(c) = famSum r c + c` is unbounded above on `[r/2, r)`. -/
theorem exists_sum_ge (r y : ℝ) (hr : 0 < r) (hr4 : r ^ 2 < 4) (hy : 0 ≤ y) :
    ∃ b, r / 2 ≤ b ∧ b < r ∧ y ≤ famSum r b + b := by
  have hK : 0 < 8 - 2 * r ^ 2 := by nlinarith
  set d : ℝ := min (r / 2) ((8 - 2 * r ^ 2) / (4 * (y + 1))) with hd
  have hy1 : (0 : ℝ) < y + 1 := by linarith
  have hd0 : 0 < d := lt_min (by linarith) (by positivity)
  have hdr : d ≤ r / 2 := min_le_left _ _
  have hdK : d ≤ (8 - 2 * r ^ 2) / (4 * (y + 1)) := min_le_right _ _
  refine ⟨r - d, by linarith, by linarith, ?_⟩
  have hb2 : r / 2 ≤ r - d := by linarith
  have hbr : r - d < r := by linarith
  have hge := famSum_ge_near r (r - d) hr hr4 hb2 hbr
  have hsimp : r - (r - d) = d := by ring
  rw [hsimp] at hge
  have hkey : y + 1 ≤ (8 - 2 * r ^ 2) / (4 * d) := by
    rw [le_div_iff₀ (by positivity)]
    -- `hdK` is `d ≤ K / (4(y+1))`, i.e. `a ≤ b / c`, so the lemma is `le_div_iff₀` on BOTH sides
    rw [le_div_iff₀ (by positivity)] at hdK
    have hcomm : d * (4 * (y + 1)) = (y + 1) * (4 * d) := by ring
    linarith [hdK, hcomm]
  linarith [hge, hkey, hb2, hr]

/-- **Every nonnegative total is attained**, by the intermediate value theorem. -/
theorem exists_sum_eq (r y : ℝ) (hr : 0 < r) (hr4 : r ^ 2 < 4) (hy : 0 ≤ y) :
    ∃ c, 0 ≤ c ∧ c < r ∧ famSum r c + c = y := by
  obtain ⟨b, hb2, hbr, hbge⟩ := exists_sum_ge r y hr hr4 hy
  have hb0 : (0 : ℝ) ≤ b := by linarith
  have hne : ∀ c ∈ Set.Icc (0 : ℝ) b, r ^ 2 - c ^ 2 ≠ 0 := by
    intro c hc
    simp only [Set.mem_Icc] at hc
    have hlt : c ^ 2 < r ^ 2 := by nlinarith [hc.1, hc.2]
    intro h
    nlinarith
  have hcont : ContinuousOn (fun c => famSum r c + c) (Set.Icc 0 b) := by
    -- unfold the whole FUNCTION first; `simp only [famSum]` cannot reach under the binder here
    have hfun : (fun c => famSum r c + c)
        = fun c => c * (8 - 2 * r ^ 2) / (r ^ 2 - c ^ 2) + c := by
      funext c
      rw [famSum]
    rw [hfun]
    refine ContinuousOn.add ?_ continuousOn_id
    exact ContinuousOn.div (continuous_id.mul continuous_const).continuousOn
      (continuous_const.sub (continuous_pow 2)).continuousOn hne
  have hmem : y ∈ Set.Icc ((fun c => famSum r c + c) 0) ((fun c => famSum r c + c) b) := by
    -- the lambda is NOT beta-reduced in the goal; `show` goes through by defeq
    show y ∈ Set.Icc (famSum r 0 + 0) (famSum r b + b)
    rw [famSum_zero, add_zero]
    exact ⟨hy, hbge⟩
  obtain ⟨c, hcmem, hceq⟩ := intermediate_value_Icc hb0 hcont hmem
  simp only [Set.mem_Icc] at hcmem
  exact ⟨c, hcmem.1, by linarith [hcmem.2], hceq⟩

/-- **EVERY REAL VALUE IS ATTAINED AS A POLAR-CENTROID `y`-COORDINATE.**  With
`centroid_x_eq_of_e2` pinning the `x`-coordinate at `h₂`, the locus of polar centroids over the
closure family is EXACTLY the line `x = h₂` — this row's residue (ii), at `N = 3`. -/
theorem centroidY_surjective (Y : ℝ) :
    ∃ t : ZMod 3 → ℝ, (∀ i, tangencyDefect 1 rClose t i = 0)
      ∧ (t 0 + t 1 + t 2) / 3 = Y := by
  rcases le_or_gt 0 Y with hY | hY
  · obtain ⟨c, hc0, hcr, hceq⟩ :=
      exists_sum_eq rClose (3 * Y) rClose_pos rClose_sq_lt_four (by linarith)
    obtain ⟨t, hfam, hc2⟩ :=
      exists_onFamily_of_lt rClose c rClose_pos rClose_sq_lt_four hc0 hcr
    have hne : rClose ^ 2 - c ^ 2 ≠ 0 := by
      have hlt : c ^ 2 < rClose ^ 2 := by nlinarith [rClose_pos]
      intro h
      nlinarith
    refine ⟨t, tangency_of_family hfam rClose_closureEq, ?_⟩
    rw [sum_eq_of_onFamily rClose c t hfam hc2 hne, hceq]
    ring
  · obtain ⟨c, hc0, hcr, hceq⟩ :=
      exists_sum_eq rClose (3 * (-Y)) rClose_pos rClose_sq_lt_four (by linarith)
    obtain ⟨t, hfam, hc2⟩ :=
      exists_onFamily_of_lt rClose c rClose_pos rClose_sq_lt_four hc0 hcr
    have hne : rClose ^ 2 - c ^ 2 ≠ 0 := by
      have hlt : c ^ 2 < rClose ^ 2 := by nlinarith [rClose_pos]
      intro h
      nlinarith
    have hsum := sum_eq_of_onFamily rClose c t hfam hc2 hne
    rw [hceq] at hsum
    refine ⟨fun i => -t i,
      tangency_of_family (onFamily_neg rClose t hfam) rClose_closureEq, ?_⟩
    show (-t 0 + -t 1 + -t 2) / 3 = Y
    linarith [hsum]

/-! ### RESIDUE (i) IS CLOSED AT `N = 3` TOO, and the two descriptions are equivalent

Two things here.  First the CONVERSE: `onFamily_of_tangency` shows tangency plus distinctness puts
a triangle on the family, so with `tangency_of_family` the two descriptions coincide at `N = 3` and
every family result above is a statement about genuine tangential triangles rather than about a
parameterised set that might be smaller.  The proof is the `defect_diff` factorisation used three
times, then two divisions: `P(t₀) − P(t₁)` over `t₀ − t₁` gives `e₂ = r² − 8` outright, and
`P(t₀) = 0` against the universal identity `t₀³ − e₁t₀² + e₂t₀ − e₃ = 0` gives `e₃ = −r²e₁`.

Second, residue (i).  The row's own reduction is that the vertex-centroid locus amounts to
`∑ᵢ 1/(tᵢ² − r²)` being CONSTANT along the orbit.  At `N = 3` it is, with an explicit value, and
`e₁` cancels twice on the way: `∏(r − tᵢ) = 2r³ − 8r` and `∏(−r − tᵢ) = −2r³ + 8r` are both free of
the coordinate sum, hence so are `∏(tᵢ² − r²) = −4r²(r² − 4)²` and the pairwise sum
`8(r² − 2)(r² − 4)`, and the quotient is `2(2 − r²)/(r²(r² − 4))`.

**WHAT THIS DOES NOT CONTRADICT.**  The row records that a Gröbner test puts this sum OUTSIDE the
TANGENCY ideal even with the closure radius adjoined.  That stands: the certificates here are
against the FAMILY ideal (the two symmetric conditions), which at `N = 3` tangency implies only
together with distinctness — `onFamily_of_tangency` is exactly that implication, and it is where
the extra hypotheses enter.  So the two statements are about different ideals, and both are true.

**STILL `N = 3` ONLY.**  Nothing here touches `N ≥ 4`, where the vertex and area centroids stop
coinciding and the row's open half lives. -/

/-- **THE CONVERSE: tangency plus distinctness puts a triangle ON the family.** -/
theorem onFamily_of_tangency (r : ℝ) (t : ZMod 3 → ℝ)
    (htan : ∀ i, tangencyDefect 1 r t i = 0)
    (h01 : t 0 ≠ t 1) (h12 : t 1 ≠ t 2) (h20 : t 2 ≠ t 0) :
    OnFamily r t := by
  have i01 : ((0 : ZMod 3) + 1) = 1 := by decide
  have i11 : ((1 : ZMod 3) + 1) = 2 := by decide
  have i21 : ((2 : ZMod 3) + 1) = 0 := by decide
  have d0 := htan 0
  have d1 := htan 1
  have d2 := htan 2
  simp only [tangencyDefect, i01] at d0
  simp only [tangencyDefect, i11] at d1
  simp only [tangencyDefect, i21] at d2
  set s : ℝ := t 0 + t 1 + t 2 with hs
  -- middle coordinate `t 1`: from `d0 - d1`, whose antisymmetric factor is `t 0 - t 2`
  have h02 : t 0 - t 2 ≠ 0 := fun h => h20 (by linarith [sub_eq_zero.mp h])
  have hP1 : t 1 ^ 3 - s * t 1 ^ 2 + (r ^ 2 - 8) * t 1 + r ^ 2 * s = 0 := by
    have hfac : (t 0 - t 2) * (t 1 ^ 3 - s * t 1 ^ 2 + (r ^ 2 - 8) * t 1 + r ^ 2 * s) = 0 := by
      rw [hs]; linear_combination -d0 + d1
    exact (mul_eq_zero.mp hfac).resolve_left h02
  -- middle coordinate `t 0`: from `d2 - d0`, whose antisymmetric factor is `t 2 - t 1`
  have h21 : t 2 - t 1 ≠ 0 := fun h => h12 (by linarith [sub_eq_zero.mp h])
  have hP0 : t 0 ^ 3 - s * t 0 ^ 2 + (r ^ 2 - 8) * t 0 + r ^ 2 * s = 0 := by
    have hfac : (t 2 - t 1) * (t 0 ^ 3 - s * t 0 ^ 2 + (r ^ 2 - 8) * t 0 + r ^ 2 * s) = 0 := by
      rw [hs]; linear_combination -d2 + d0
    exact (mul_eq_zero.mp hfac).resolve_left h21
  have h10 : t 0 - t 1 ≠ 0 := fun h => h01 (by linarith [sub_eq_zero.mp h])
  -- `e₂ = r² − 8`, from `P(t₀) − P(t₁)` divided by `t₀ − t₁`
  have he2 : t 0 * t 1 + t 1 * t 2 + t 2 * t 0 = r ^ 2 - 8 := by
    have hfac : (t 0 - t 1)
        * (-(t 0 * t 1 + t 1 * t 2 + t 2 * t 0) + r ^ 2 - 8) = 0 := by
      rw [hs] at hP0 hP1
      linear_combination hP0 - hP1
    have hz := (mul_eq_zero.mp hfac).resolve_left h10
    linarith [hz]
  refine ⟨he2, ?_⟩
  -- `e₃ = −r²e₁`: `P(t₀) = 0` against the universal identity, the `e₂` slack closed by `he2`
  rw [hs] at hP0
  linear_combination hP0 + t 0 * he2

/-- `∏(r − tᵢ) = 2r³ − 8r` on the family — **the coordinate sum cancels**, which is the whole
reason a vertex-centroid constant exists at all. -/
theorem prod_r_sub_eq (r : ℝ) (t : ZMod 3 → ℝ) (h : OnFamily r t) :
    (r - t 0) * (r - t 1) * (r - t 2) = 2 * r ^ 3 - 8 * r := by
  obtain ⟨hc2, hc3⟩ := h
  linear_combination r * hc2 - hc3

/-- The mirror value, also free of the coordinate sum. -/
theorem prod_neg_r_sub_eq (r : ℝ) (t : ZMod 3 → ℝ) (h : OnFamily r t) :
    (-r - t 0) * (-r - t 1) * (-r - t 2) = -2 * r ^ 3 + 8 * r := by
  obtain ⟨hc2, hc3⟩ := h
  linear_combination (-r) * hc2 - hc3

/-- Hence the product of the three `tᵢ² − r²` is a constant of the family. -/
theorem prod_sq_sub_eq (r : ℝ) (t : ZMod 3 → ℝ) (h : OnFamily r t) :
    (t 0 ^ 2 - r ^ 2) * (t 1 ^ 2 - r ^ 2) * (t 2 ^ 2 - r ^ 2)
      = -4 * r ^ 2 * (r ^ 2 - 4) ^ 2 := by
  have hQr := prod_r_sub_eq r t h
  have hQnr := prod_neg_r_sub_eq r t h
  linear_combination ((-r - t 0) * (-r - t 1) * (-r - t 2)) * hQr + (2 * r ^ 3 - 8 * r) * hQnr

/-- ...and so is the sum of the three pairwise products. -/
theorem pairsum_sq_sub_eq (r : ℝ) (t : ZMod 3 → ℝ) (h : OnFamily r t) :
    (t 1 ^ 2 - r ^ 2) * (t 2 ^ 2 - r ^ 2) + (t 0 ^ 2 - r ^ 2) * (t 2 ^ 2 - r ^ 2)
        + (t 0 ^ 2 - r ^ 2) * (t 1 ^ 2 - r ^ 2)
      = 8 * (r ^ 2 - 2) * (r ^ 2 - 4) := by
  obtain ⟨hc2, hc3⟩ := h
  linear_combination ((t 0 * t 1 + t 1 * t 2 + t 2 * t 0) + 5 * r ^ 2 - 8) * hc2
    + (-2 * (t 0 + t 1 + t 2)) * hc3

/-- **THE RECIPROCAL SUM IS A CONSTANT OF THE FAMILY** — which is residue (i)'s content at
`N = 3`, per the row's own reduction of the vertex-centroid locus. -/
theorem reciprocal_sum_eq (r : ℝ) (t : ZMod 3 → ℝ) (h : OnFamily r t)
    (h0 : t 0 ^ 2 - r ^ 2 ≠ 0) (h1 : t 1 ^ 2 - r ^ 2 ≠ 0) (h2 : t 2 ^ 2 - r ^ 2 ≠ 0)
    (hr : r ≠ 0) (hr4 : r ^ 2 - 4 ≠ 0) :
    1 / (t 0 ^ 2 - r ^ 2) + 1 / (t 1 ^ 2 - r ^ 2) + 1 / (t 2 ^ 2 - r ^ 2)
      = 2 * (2 - r ^ 2) / (r ^ 2 * (r ^ 2 - 4)) := by
  have hN := pairsum_sq_sub_eq r t h
  have hP := prod_sq_sub_eq r t h
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  field_simp
  linear_combination (r ^ 2 * (r ^ 2 - 4)) * hN + (2 * (r ^ 2 - 2)) * hP

/-! ### A FIRST STEP INTO `N = 4`: opposite vertices multiply to `−r²`

Everything above is `N = 3`.  The same factorisation that drives that case says something at `N = 4`
as well, and it is worth having because it is the first structural constraint on tangential
quadrilaterals this row has.

`defect_diff_bracket` restates the module's `defect_diff` in the form the argument needs: the middle
coordinate enters only through `b² − r²` and `b`, and the outer two only through their SUM.  At
`N = 4` that makes the four brackets pin `t₀ + t₂` twice over (from `d₀ − d₁` and `d₂ − d₃`) and
`t₁ + t₃` twice over (from `d₁ − d₂` and `d₃ − d₀`).  Eliminating the sum between each pair leaves

    (4 − r²)·(t₃ − t₁)·(t₁t₃ + r²) = 0,

so with `r² ≠ 4` and the diagonals non-degenerate, **`t₁t₃ = −r²` and `t₀t₂ = −r²`**.

**WHY THIS IS NOT THE `N = 4` FAMILY, and why `N = 3` really is special.**  At `N = 3` the three
coordinates are the roots of ONE cubic, because with three cyclic coordinates the local triple sum
appearing in each bracket IS the global coordinate sum.  At `N = 4` the four brackets involve four
DIFFERENT pairs, so no single cubic serves, and what comes out instead is the pair of diagonal
relations above — two equations, not a Vieta description.  Both of the row's residues therefore
remain open for general `N`; what is closed is a constraint, not the locus. -/

/-- `defect_diff` in the form the `N = 4` argument needs: the middle coordinate enters through
`b² − r²` and `b`, the outer two only through their sum. -/
theorem defect_diff_bracket (a b c r : ℝ) :
    ((a * b + 4) ^ 2 - r ^ 2 * (16 + (a + b) ^ 2))
        - ((b * c + 4) ^ 2 - r ^ 2 * (16 + (b + c) ^ 2))
      = (a - c) * ((a + c) * (b ^ 2 - r ^ 2) + 2 * b * (4 - r ^ 2)) := by
  ring

/-- **AT `N = 4`, OPPOSITE VERTICES SATISFY `tᵢ·tᵢ₊₂ = −r²`.** -/
theorem opposite_prod_of_tangency_four (r : ℝ) (t : ZMod 4 → ℝ)
    (htan : ∀ i, tangencyDefect 1 r t i = 0) (hr4 : r ^ 2 - 4 ≠ 0)
    (h02 : t 0 - t 2 ≠ 0) (h13 : t 1 - t 3 ≠ 0) :
    t 1 * t 3 = -r ^ 2 ∧ t 0 * t 2 = -r ^ 2 := by
  have i0 : ((0 : ZMod 4) + 1) = 1 := by decide
  have i1 : ((1 : ZMod 4) + 1) = 2 := by decide
  have i2 : ((2 : ZMod 4) + 1) = 3 := by decide
  have i3 : ((3 : ZMod 4) + 1) = 0 := by decide
  have d0 := htan 0
  have d1 := htan 1
  have d2 := htan 2
  have d3 := htan 3
  simp only [tangencyDefect, i0] at d0
  simp only [tangencyDefect, i1] at d1
  simp only [tangencyDefect, i2] at d2
  simp only [tangencyDefect, i3] at d3
  have h4 : (4 : ℝ) - r ^ 2 ≠ 0 := fun h => hr4 (by linarith)
  have h31 : t 3 - t 1 ≠ 0 := fun h => h13 (by linarith)
  have h20 : t 2 - t 0 ≠ 0 := fun h => h02 (by linarith)
  -- two brackets pin `t 0 + t 2`
  have B012 : (t 0 + t 2) * (t 1 ^ 2 - r ^ 2) = -2 * t 1 * (4 - r ^ 2) := by
    have hfac : (t 0 - t 2)
        * ((t 0 + t 2) * (t 1 ^ 2 - r ^ 2) + 2 * t 1 * (4 - r ^ 2)) = 0 := by
      linear_combination d0 - d1
    have hz := (mul_eq_zero.mp hfac).resolve_left h02
    linarith [hz]
  have B230 : (t 2 + t 0) * (t 3 ^ 2 - r ^ 2) = -2 * t 3 * (4 - r ^ 2) := by
    have hfac : (t 2 - t 0)
        * ((t 2 + t 0) * (t 3 ^ 2 - r ^ 2) + 2 * t 3 * (4 - r ^ 2)) = 0 := by
      linear_combination d2 - d3
    have hz := (mul_eq_zero.mp hfac).resolve_left h20
    linarith [hz]
  -- and two pin `t 1 + t 3`
  have B123 : (t 1 + t 3) * (t 2 ^ 2 - r ^ 2) = -2 * t 2 * (4 - r ^ 2) := by
    have hfac : (t 1 - t 3)
        * ((t 1 + t 3) * (t 2 ^ 2 - r ^ 2) + 2 * t 2 * (4 - r ^ 2)) = 0 := by
      linear_combination d1 - d2
    have hz := (mul_eq_zero.mp hfac).resolve_left h13
    linarith [hz]
  have B301 : (t 3 + t 1) * (t 0 ^ 2 - r ^ 2) = -2 * t 0 * (4 - r ^ 2) := by
    have hfac : (t 3 - t 1)
        * ((t 3 + t 1) * (t 0 ^ 2 - r ^ 2) + 2 * t 0 * (4 - r ^ 2)) = 0 := by
      linear_combination d3 - d0
    have hz := (mul_eq_zero.mp hfac).resolve_left h31
    linarith [hz]
  constructor
  · -- eliminate `t 0 + t 2` between `B012` and `B230`
    have hfac : (-2 * (4 - r ^ 2)) * ((t 3 - t 1) * (t 1 * t 3 + r ^ 2)) = 0 := by
      linear_combination (t 1 ^ 2 - r ^ 2) * B230 - (t 3 ^ 2 - r ^ 2) * B012
    have hne : (-2 : ℝ) * (4 - r ^ 2) ≠ 0 := by
      intro h
      exact h4 (by linarith [h])
    have hz := (mul_eq_zero.mp hfac).resolve_left hne
    have hz2 := (mul_eq_zero.mp hz).resolve_left h31
    linarith [hz2]
  · -- and `t 1 + t 3` between `B123` and `B301`
    have hfac : (-2 * (4 - r ^ 2)) * ((t 0 - t 2) * (t 2 * t 0 + r ^ 2)) = 0 := by
      linear_combination (t 2 ^ 2 - r ^ 2) * B301 - (t 0 ^ 2 - r ^ 2) * B123
    have hne : (-2 : ℝ) * (4 - r ^ 2) ≠ 0 := by
      intro h
      exact h4 (by linarith [h])
    have hz := (mul_eq_zero.mp hfac).resolve_left hne
    have hz2 := (mul_eq_zero.mp hz).resolve_left h02
    linarith [hz2]

/-! ### The `N = 4` CLOSURE CONDITION, in closed form

The diagonal relation above is enough to finish the closure computation for quadrilaterals.
Substituting `t₀t₂ = −r²` into the bracket turns it into `(t₀²−r²)(t₁²−r²) = −2t₀t₁(4−r²)`, and
SUBTRACTING the tangency equation `g(t₀,t₁) = 0` removes every coordinate at once, leaving

    (r²)² + 16r² − 16 = 0,   i.e.   r² = 4√5 − 8 ≈ 0.944,   r ≈ 0.9717,

which is inside the source's own guard `0 < r < f = 1`.  This is the Poncelet closure condition for
quadrilaterals inscribed in the parabola and circumscribing the circle, **derived rather than
assumed** — the `N = 3` analogue was `r² − 24r² + 16`-shaped only after a Vieta reduction that does
not exist here, and this route needs no family description at all.

Note what it does NOT give: a parameterisation.  The condition pins `r`; the remaining freedom is
one equation relating `t₀t₁` and `t₀+t₁`, which is where an `N = 4` family would come from.  Both of
the row's residues stay open for general `N`. -/

/-- **THE `N = 4` CLOSURE CONDITION.**  A tangential quadrilateral with non-degenerate diagonals
forces `(r²)² + 16r² − 16 = 0`. -/
theorem closure_four (r : ℝ) (t : ZMod 4 → ℝ)
    (htan : ∀ i, tangencyDefect 1 r t i = 0) (hr4 : r ^ 2 - 4 ≠ 0)
    (h02 : t 0 - t 2 ≠ 0) (h13 : t 1 - t 3 ≠ 0) :
    (r ^ 2) ^ 2 + 16 * r ^ 2 - 16 = 0 := by
  obtain ⟨-, hprod⟩ := opposite_prod_of_tangency_four r t htan hr4 h02 h13
  have i0 : ((0 : ZMod 4) + 1) = 1 := by decide
  have i1 : ((1 : ZMod 4) + 1) = 2 := by decide
  have d0 := htan 0
  have d1 := htan 1
  simp only [tangencyDefect, i0] at d0
  simp only [tangencyDefect, i1] at d1
  have B012 : (t 0 + t 2) * (t 1 ^ 2 - r ^ 2) = -2 * t 1 * (4 - r ^ 2) := by
    have hfac : (t 0 - t 2)
        * ((t 0 + t 2) * (t 1 ^ 2 - r ^ 2) + 2 * t 1 * (4 - r ^ 2)) = 0 := by
      linear_combination d0 - d1
    have hz := (mul_eq_zero.mp hfac).resolve_left h02
    linarith [hz]
  -- the diagonal relation clears `t 2` out of the bracket
  have hI : (t 0 ^ 2 - r ^ 2) * (t 1 ^ 2 - r ^ 2) = -2 * t 0 * t 1 * (4 - r ^ 2) := by
    linear_combination t 0 * B012 - (t 1 ^ 2 - r ^ 2) * hprod
  -- and subtracting the tangency equation removes every coordinate
  linear_combination hI - d0

/-- The closure radius in closed form: `r² = 4√5 − 8`, so `r ≈ 0.972`, inside the source's guard. -/
theorem closure_four_value (r : ℝ) (hr : 0 < r)
    (h : (r ^ 2) ^ 2 + 16 * r ^ 2 - 16 = 0) :
    r ^ 2 = 4 * Real.sqrt 5 - 8 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : 0 < r ^ 2 := by positivity
  have hsq : (r ^ 2 + 8) ^ 2 = (4 * Real.sqrt 5) ^ 2 := by
    have h80 : (4 * Real.sqrt 5) ^ 2 = 80 := by
      rw [mul_pow]; rw [h5]; norm_num
    rw [h80]; nlinarith [h]
  have hpos1 : 0 < r ^ 2 + 8 := by linarith
  have hpos2 : 0 < 4 * Real.sqrt 5 := by linarith
  -- `a² = b²` with both positive: FACTOR rather than reach for an injectivity lemma
  have hfac : (r ^ 2 + 8 - 4 * Real.sqrt 5) * (r ^ 2 + 8 + 4 * Real.sqrt 5) = 0 := by
    linear_combination hsq
  have hsum : 0 < r ^ 2 + 8 + 4 * Real.sqrt 5 := by linarith
  have hz := (mul_eq_zero.mp hfac).resolve_right (ne_of_gt hsum)
  linarith [hz]

/-! ### The `N = 4` family, and residue (i) closed at `N = 4`

`closure_four` pins `r`; the remaining freedom is one relation between `p = t₀t₁` and
`σ = t₀+t₁`, and `OnFamilyFour` is that relation.  `tangency_four_of_family` is the CONVERSE of
`opposite_prod_of_tangency_four`: at the closure radius the relation is sufficient, so the
tangential quadrilaterals are exactly a one-parameter family, as at `N = 3`.

`cyclic_sum_four` is the payoff, and it is the first result on this row that speaks to the half
that was open.  The polar vertices are `Qᵢ = (-tᵢtᵢ₊₁/(4f), (tᵢ+tᵢ₊₁)/2)`, so the VERTEX centroid's
`x`-coordinate is `-∑tᵢtᵢ₊₁/(4fN)` — and at `N = 4` that cyclic sum is the CONSTANT `2r² - 8`.
The mechanism is a single cancellation: `t₀(t₀+t₂) = t₀² - r²` and `t₁(t₁+t₃) = t₁² - r²` by the
diagonal relations, so `p·∑tᵢtᵢ₊₁ = (t₀²-r²)(t₁²-r²)`, whose excess over `p(2r²-8)` is exactly one
tangency equation plus the closure polynomial.  Hence `vertexCentroidX_four`:

    h₀ = (4 - r²)/(8f)    at `N = 4`

which the source's own Task 2 records as having no known closed form.  At the closure radius
`h₀ = (3-√5)/2 ≈ 0.382` while `h₂ = (4-√5)/3 ≈ 0.588`: the two centroids genuinely separate at
`N = 4`, which is why residue (i) could not be read off the `N = 3` work.

**WHAT IS STILL OPEN.**  This is `N = 4`, not arbitrary `N` — the row claims every `N`, and the
argument here is specific to the cyclic structure that makes `i+2 = i-2`.  And it closes residue
(i) only: residue (ii), that the locus is a COMPLETE line, needs the `y`-coordinate
`(∑tᵢ)/4 = σ(p-r²)/(4p)` to attain every real value along the family, which is untouched. -/

/-- The `N = 4` family relation between `p = t₀t₁` and `σ = t₀+t₁`.  Unlike `OnFamily` this is a
single equation, because at `N = 4` the diagonal relations have already consumed `t₂` and `t₃`. -/
def OnFamilyFour (r t0 t1 : ℝ) : Prop :=
  (t0 * t1) ^ 2 + 8 * (t0 * t1) + (r ^ 2) ^ 2 = r ^ 2 * (t0 + t1) ^ 2

/-- Edge `t₀ → t₁`: the tangency equation IS the family relation minus closure. -/
theorem defect_four_01 (r t0 t1 : ℝ)
    (hcl : (r ^ 2) ^ 2 + 16 * r ^ 2 - 16 = 0) (hfam : OnFamilyFour r t0 t1) :
    (t0 * t1 + 4 * 1 ^ 2) ^ 2 - r ^ 2 * (16 * 1 ^ 2 + (t0 + t1) ^ 2) = 0 := by
  rw [OnFamilyFour] at hfam
  norm_num
  linear_combination hfam - hcl

/-- Edge `t₁ → t₂` with `t₂ = −r²/t₀`. -/
theorem defect_four_12 (r t0 t1 : ℝ) (h0 : t0 ≠ 0)
    (hcl : (r ^ 2) ^ 2 + 16 * r ^ 2 - 16 = 0) (hfam : OnFamilyFour r t0 t1) :
    (t1 * (-r ^ 2 / t0) + 4 * 1 ^ 2) ^ 2
        - r ^ 2 * (16 * 1 ^ 2 + (t1 + -r ^ 2 / t0) ^ 2) = 0 := by
  rw [OnFamilyFour] at hfam
  field_simp
  linear_combination (-r ^ 2) * hfam + (-t0 ^ 2) * hcl

/-- Edge `t₂ → t₃`, the one whose certificate is not a scalar multiple of the others. -/
theorem defect_four_23 (r t0 t1 : ℝ) (h0 : t0 ≠ 0) (h1 : t1 ≠ 0)
    (hcl : (r ^ 2) ^ 2 + 16 * r ^ 2 - 16 = 0) (hfam : OnFamilyFour r t0 t1) :
    ((-r ^ 2 / t0) * (-r ^ 2 / t1) + 4 * 1 ^ 2) ^ 2
        - r ^ 2 * (16 * 1 ^ 2 + ((-r ^ 2 / t0) + -r ^ 2 / t1) ^ 2) = 0 := by
  rw [OnFamilyFour] at hfam
  field_simp
  linear_combination (16 - 16 * r ^ 2) * hfam
    + (r ^ 4 - r ^ 2 * t0 ^ 2 - 2 * r ^ 2 * t0 * t1 - r ^ 2 * t1 ^ 2 + 8 * t0 * t1) * hcl

/-- Edge `t₃ → t₀`. -/
theorem defect_four_30 (r t0 t1 : ℝ) (h1 : t1 ≠ 0)
    (hcl : (r ^ 2) ^ 2 + 16 * r ^ 2 - 16 = 0) (hfam : OnFamilyFour r t0 t1) :
    ((-r ^ 2 / t1) * t0 + 4 * 1 ^ 2) ^ 2
        - r ^ 2 * (16 * 1 ^ 2 + ((-r ^ 2 / t1) + t0) ^ 2) = 0 := by
  rw [OnFamilyFour] at hfam
  field_simp
  linear_combination (-r ^ 2) * hfam + (-t1 ^ 2) * hcl

/-- **THE `N = 4` FAMILY IS TANGENTIAL** — the converse of `opposite_prod_of_tangency_four`.  At
the closure radius, the diagonal relations plus the single family relation are SUFFICIENT for all
four edges to be tangent, so the tangential quadrilaterals are exactly a one-parameter family. -/
theorem tangency_four_of_family (r : ℝ) (t : ZMod 4 → ℝ) (h0 : t 0 ≠ 0) (h1 : t 1 ≠ 0)
    (hd2 : t 2 = -r ^ 2 / t 0) (hd3 : t 3 = -r ^ 2 / t 1)
    (hcl : (r ^ 2) ^ 2 + 16 * r ^ 2 - 16 = 0) (hfam : OnFamilyFour r (t 0) (t 1)) :
    ∀ i, tangencyDefect 1 r t i = 0 := by
  have i0 : ((0 : ZMod 4) + 1) = 1 := by decide
  have i1 : ((1 : ZMod 4) + 1) = 2 := by decide
  have i2 : ((2 : ZMod 4) + 1) = 3 := by decide
  have i3 : ((3 : ZMod 4) + 1) = 0 := by decide
  have e0 : tangencyDefect 1 r t 0 = 0 := by
    simp only [tangencyDefect, i0]
    exact defect_four_01 r (t 0) (t 1) hcl hfam
  have e1 : tangencyDefect 1 r t 1 = 0 := by
    simp only [tangencyDefect, i1, hd2]
    exact defect_four_12 r (t 0) (t 1) h0 hcl hfam
  have e2 : tangencyDefect 1 r t 2 = 0 := by
    simp only [tangencyDefect, i2, hd2, hd3]
    exact defect_four_23 r (t 0) (t 1) h0 h1 hcl hfam
  have e3 : tangencyDefect 1 r t 3 = 0 := by
    simp only [tangencyDefect, i3, hd3]
    exact defect_four_30 r (t 0) (t 1) h1 hcl hfam
  intro i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3

/-- **THE CYCLIC SUM IS CONSTANT AT `N = 4`.**  On any tangential quadrilateral with
non-degenerate diagonals, `∑ᵢ tᵢtᵢ₊₁ = 2r² − 8`.  One cancellation does it: the diagonal relations
give `t₀(t₀+t₂) = t₀²−r²` and `t₁(t₁+t₃) = t₁²−r²`, so `p·∑tᵢtᵢ₊₁ = (t₀²−r²)(t₁²−r²)`, and the
excess of that over `p(2r²−8)` is exactly one tangency equation plus the closure polynomial. -/
theorem cyclic_sum_four (r : ℝ) (t : ZMod 4 → ℝ)
    (htan : ∀ i, tangencyDefect 1 r t i = 0) (hr0 : r ≠ 0) (hr4 : r ^ 2 - 4 ≠ 0)
    (h02 : t 0 - t 2 ≠ 0) (h13 : t 1 - t 3 ≠ 0) :
    t 0 * t 1 + t 1 * t 2 + t 2 * t 3 + t 3 * t 0 = 2 * r ^ 2 - 8 := by
  obtain ⟨h13p, h02p⟩ := opposite_prod_of_tangency_four r t htan hr4 h02 h13
  have hcl := closure_four r t htan hr4 h02 h13
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr0
  have ht0 : t 0 ≠ 0 := by
    intro h; rw [h, zero_mul] at h02p; exact hr2 (by linarith)
  have ht1 : t 1 ≠ 0 := by
    intro h; rw [h, zero_mul] at h13p; exact hr2 (by linarith)
  have i0 : ((0 : ZMod 4) + 1) = 1 := by decide
  have d0 := htan 0
  simp only [tangencyDefect, i0] at d0
  have key : t 0 * t 1 * (t 0 * t 1 + t 1 * t 2 + t 2 * t 3 + t 3 * t 0)
      = t 0 * t 1 * (2 * r ^ 2 - 8) := by
    linear_combination d0 + hcl + (t 0 ^ 2 + t 0 * t 2) * h13p + (t 1 ^ 2 - r ^ 2) * h02p
  exact mul_left_cancel₀ (mul_ne_zero ht0 ht1) key

/-- **`h₀` AT `N = 4`, IN CLOSED FORM — RESIDUE (i) CLOSED AT `N = 4`.**  The polar vertex `Qᵢ`
has `x = -tᵢtᵢ₊₁/(4f)`, so the vertex centroid's `x`-coordinate is the constant `(4−r²)/(8f)`.
The source's Task 2 records `h₀` as having no known closed form; at `N = 4` it has one, and it is
NOT `h₂` — at the closure radius `h₀ = (3−√5)/2 ≈ 0.382` against `h₂ = (4−√5)/3 ≈ 0.588`. -/
theorem vertexCentroidX_four (r : ℝ) (t : ZMod 4 → ℝ)
    (htan : ∀ i, tangencyDefect 1 r t i = 0) (hr0 : r ≠ 0) (hr4 : r ^ 2 - 4 ≠ 0)
    (h02 : t 0 - t 2 ≠ 0) (h13 : t 1 - t 3 ≠ 0) :
    (∑ i, -(t i * t (i + 1)) / 4) / 4 = (4 - r ^ 2) / 8 := by
  have hE := cyclic_sum_four r t htan hr0 hr4 h02 h13
  have hu : (univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have i0 : ((0 : ZMod 4) + 1) = 1 := by decide
  have i1 : ((1 : ZMod 4) + 1) = 2 := by decide
  have i2 : ((2 : ZMod 4) + 1) = 3 := by decide
  have i3 : ((3 : ZMod 4) + 1) = 0 := by decide
  rw [i0, i1, i2, i3]
  linarith [hE]

/-! ### The `N = 4` hypotheses are inhabited — one quadrilateral for every `p > 0`

`closure_four`, `cyclic_sum_four` and `vertexCentroidX_four` are all universally quantified over a
tangential quadrilateral, and **nothing above exhibits one**, so nothing above rules out their
being empty implications.  This is the `N = 3` situation exactly (see `tangency_tClose`), rebuilt
at `N = 4`, and no gate can see it: an empty implication is axiom-free, gates clean, and satisfies
`check_unused_hypotheses` because the hypothesis really is used.

The construction is the family of the previous section run forwards.  Fix `p > 0`, let `σ` be the
coordinate sum the family relation forces, and take `t₀, t₁` to be the roots of `x² - σx + p`.
**There is no admissibility condition**, which is what makes this a family rather than a witness:

    σ² - 4p = (p² + (8 - 4r²)p + r⁴)/r²

and `r² = 4√5 - 8 < 2` at the closure radius, so every coefficient is positive and the
discriminant is positive for **every** `p > 0`.  (Both roots of that quadratic in `p` are
negative — `-4` and `≈ -0.2229` — which is the same statement.)  Non-degeneracy is free too:
`tᵢ - tᵢ₊₂ = (tᵢ² + r²)/tᵢ`, never zero for `r > 0`.

`vertexCentroidX_at_four_witness` is the point of it all: the `h₀` value at an actual
quadrilateral, with **no hypothesis carried**. -/

noncomputable def sqrt5 : ℝ := Real.sqrt 5

theorem sqrt5_sq : sqrt5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem sqrt5_pos : 0 < sqrt5 := Real.sqrt_pos.mpr (by norm_num)

theorem sqrt5_gt : (2 : ℝ) < sqrt5 := by nlinarith [sqrt5_sq, sqrt5_pos]

theorem sqrt5_lt : sqrt5 < 5 / 2 := by nlinarith [sqrt5_sq, sqrt5_pos]

/-- The `N = 4` closure radius `r = √(4√5 − 8) ≈ 0.9717`, inside the source's guard `0 < r < 1`. -/
noncomputable def rFour : ℝ := Real.sqrt (4 * sqrt5 - 8)

theorem rFour_sq : rFour ^ 2 = 4 * sqrt5 - 8 := Real.sq_sqrt (by nlinarith [sqrt5_gt])

theorem rFour_pos : 0 < rFour := Real.sqrt_pos.mpr (by nlinarith [sqrt5_gt])

theorem rFour_sq_pos : 0 < rFour ^ 2 := by rw [rFour_sq]; nlinarith [sqrt5_gt]

/-- `r² < 2` is the inequality the whole construction rests on: it is what makes `8 − 4r²`
positive, hence the discriminant positive for every `p > 0`. -/
theorem rFour_sq_lt_two : rFour ^ 2 < 2 := by rw [rFour_sq]; nlinarith [sqrt5_lt]

theorem rFour_closure : (rFour ^ 2) ^ 2 + 16 * rFour ^ 2 - 16 = 0 := by
  rw [rFour_sq]; linear_combination 16 * sqrt5_sq

theorem rFour_sq_sub_four_ne : rFour ^ 2 - 4 ≠ 0 := by
  have := rFour_sq_lt_two; intro h; linarith

/-- The coordinate sum the family relation forces at parameter `p`. -/
noncomputable def sigFour (p : ℝ) : ℝ :=
  Real.sqrt ((p ^ 2 + 8 * p + (rFour ^ 2) ^ 2) / rFour ^ 2)

theorem sigFour_sq (p : ℝ) (hp : 0 < p) :
    sigFour p ^ 2 = (p ^ 2 + 8 * p + (rFour ^ 2) ^ 2) / rFour ^ 2 :=
  Real.sq_sqrt (div_nonneg (by nlinarith [sq_nonneg p, sq_nonneg (rFour ^ 2)])
    (le_of_lt rFour_sq_pos))

theorem sigFour_pos (p : ℝ) (hp : 0 < p) : 0 < sigFour p :=
  Real.sqrt_pos.mpr (div_pos (by nlinarith [sq_nonneg p, sq_nonneg (rFour ^ 2), rFour_sq_pos])
    rFour_sq_pos)

/-- **NO ADMISSIBILITY CONDITION AT ALL.**  `σ² − 4p = (p² + (8−4r²)p + r⁴)/r²`, and `r² < 2`, so
every coefficient is positive and the discriminant is positive for every `p > 0`. -/
theorem sigFour_disc_pos (p : ℝ) (hp : 0 < p) : 0 < sigFour p ^ 2 - 4 * p := by
  rw [sigFour_sq p hp, sub_pos, lt_div_iff₀ rFour_sq_pos]
  nlinarith [mul_pos hp (sub_pos.mpr rFour_sq_lt_two), sq_nonneg p, sq_nonneg (rFour ^ 2)]

noncomputable def tFour0 (p : ℝ) : ℝ := (sigFour p + Real.sqrt (sigFour p ^ 2 - 4 * p)) / 2
noncomputable def tFour1 (p : ℝ) : ℝ := (sigFour p - Real.sqrt (sigFour p ^ 2 - 4 * p)) / 2

theorem tFour_sum (p : ℝ) : tFour0 p + tFour1 p = sigFour p := by
  simp only [tFour0, tFour1]; ring

theorem tFour_prod (p : ℝ) (hp : 0 < p) : tFour0 p * tFour1 p = p := by
  have hd : Real.sqrt (sigFour p ^ 2 - 4 * p) ^ 2 = sigFour p ^ 2 - 4 * p :=
    Real.sq_sqrt (le_of_lt (sigFour_disc_pos p hp))
  simp only [tFour0, tFour1]
  linear_combination (-(1 : ℝ) / 4) * hd

theorem tFour1_pos (p : ℝ) (hp : 0 < p) : 0 < tFour1 p := by
  have hd : Real.sqrt (sigFour p ^ 2 - 4 * p) ^ 2 = sigFour p ^ 2 - 4 * p :=
    Real.sq_sqrt (le_of_lt (sigFour_disc_pos p hp))
  have hdn : 0 ≤ Real.sqrt (sigFour p ^ 2 - 4 * p) := Real.sqrt_nonneg _
  have hs := sigFour_pos p hp
  have hlt : Real.sqrt (sigFour p ^ 2 - 4 * p) < sigFour p := by nlinarith [hd, hdn, hs, hp]
  simp only [tFour1]; linarith

theorem tFour0_pos (p : ℝ) (hp : 0 < p) : 0 < tFour0 p := by
  have h1 := tFour1_pos p hp
  have hdn : 0 ≤ Real.sqrt (sigFour p ^ 2 - 4 * p) := Real.sqrt_nonneg _
  simp only [tFour0, tFour1] at *
  linarith

theorem onFamilyFour_tFour (p : ℝ) (hp : 0 < p) :
    OnFamilyFour rFour (tFour0 p) (tFour1 p) := by
  have hne : rFour ≠ 0 := ne_of_gt rFour_pos
  rw [OnFamilyFour, tFour_sum, tFour_prod p hp, sigFour_sq p hp]
  field_simp

/-- The quadrilateral at parameter `p`.  The type sits in the `def` signature: written inline in
an application position, `![...]` elaborates as `Fin 4 → ℝ` and will not unify with `ZMod 4 → ℝ`. -/
noncomputable def tFour (p : ℝ) : ZMod 4 → ℝ :=
  ![tFour0 p, tFour1 p, -rFour ^ 2 / tFour0 p, -rFour ^ 2 / tFour1 p]

theorem tf0 (p : ℝ) : tFour p 0 = tFour0 p := by simp [tFour]
theorem tf1 (p : ℝ) : tFour p 1 = tFour1 p := by simp [tFour]
theorem tf2 (p : ℝ) : tFour p 2 = -rFour ^ 2 / tFour0 p := by simp [tFour]
theorem tf3 (p : ℝ) : tFour p 3 = -rFour ^ 2 / tFour1 p := by simp [tFour]

/-- **THE `N = 4` TANGENCY HYPOTHESES ARE INHABITED — ONE QUADRILATERAL FOR EVERY `p > 0`.** -/
theorem tangency_tFour (p : ℝ) (hp : 0 < p) :
    ∀ i, tangencyDefect 1 rFour (tFour p) i = 0 := by
  refine tangency_four_of_family rFour (tFour p) ?_ ?_ ?_ ?_ rFour_closure ?_
  · rw [tf0]; exact ne_of_gt (tFour0_pos p hp)
  · rw [tf1]; exact ne_of_gt (tFour1_pos p hp)
  · rw [tf2, tf0]
  · rw [tf3, tf1]
  · rw [tf0, tf1]; exact onFamilyFour_tFour p hp

/-- Non-degeneracy is free at `N = 4`: `t₀ − t₂ = (t₀² + r²)/t₀`, never zero for `r > 0`. -/
theorem tFour_nondeg0 (p : ℝ) (hp : 0 < p) : tFour p 0 - tFour p 2 ≠ 0 := by
  rw [tf0, tf2]
  have hq : 0 < rFour ^ 2 / tFour0 p := div_pos rFour_sq_pos (tFour0_pos p hp)
  have h : 0 < tFour0 p - -rFour ^ 2 / tFour0 p := by
    rw [neg_div, sub_neg_eq_add]; linarith [tFour0_pos p hp]
  exact ne_of_gt h

theorem tFour_nondeg1 (p : ℝ) (hp : 0 < p) : tFour p 1 - tFour p 3 ≠ 0 := by
  rw [tf1, tf3]
  have hq : 0 < rFour ^ 2 / tFour1 p := div_pos rFour_sq_pos (tFour1_pos p hp)
  have h : 0 < tFour1 p - -rFour ^ 2 / tFour1 p := by
    rw [neg_div, sub_neg_eq_add]; linarith [tFour1_pos p hp]
  exact ne_of_gt h

/-- **A TANGENTIAL QUADRILATERAL EXISTS**, so the `N = 4` theorems above are not empty
implications. -/
theorem exists_tangential_four :
    ∃ (r : ℝ) (t : ZMod 4 → ℝ), 0 < r ∧ (∀ i, tangencyDefect 1 r t i = 0) ∧
      t 0 - t 2 ≠ 0 ∧ t 1 - t 3 ≠ 0 :=
  ⟨rFour, tFour 1, rFour_pos, tangency_tFour 1 one_pos,
    tFour_nondeg0 1 one_pos, tFour_nondeg1 1 one_pos⟩

/-- **`h₀` AT AN ACTUAL QUADRILATERAL, WITH NO HYPOTHESIS CARRIED** — the `N = 4` analogue of
`centroid_at_witness`. -/
theorem vertexCentroidX_at_four_witness :
    (∑ i, -(tFour 1 i * tFour 1 (i + 1)) / 4) / 4 = (4 - rFour ^ 2) / 8 :=
  vertexCentroidX_four rFour (tFour 1) (tangency_tFour 1 one_pos) (ne_of_gt rFour_pos)
    rFour_sq_sub_four_ne (tFour_nondeg0 1 one_pos) (tFour_nondeg1 1 one_pos)

/-! ### Residue (ii) at `N = 4`: the vertex-centroid locus is the COMPLETE line

`vertexCentroidX_four` pins the `x`-coordinate at `h₀` and `tangency_tFour` supplies a
quadrilateral for every `p > 0`, but nothing yet says those quadrilaterals have *different*
centroids, let alone that the `y`-coordinate reaches every real value.  It does.

By the module's own `centroid0_y` the `y`-coordinate is `(∑tᵢ)/4`, and `sum_tFour` evaluates that
on the family: `-r²/t₀ - r²/t₁ = -r²σ/p`, so `∑tᵢ = σ(p - r²)/p`.  Two explicit tails bracket it,
both free:

* `σ ≥ r` always (`sigFour_ge`, from `σ² ≥ r⁴/r² = r²`), and `(p-r²)/(4p) ≤ -r²/(8p)` for
  `p ≤ r²/2`, so `y ≤ -r³/(8p)` — unbounded **below** (`centYFour_le_near`);
* `σr ≥ p` (`sigFour_ge_mul`, from `(σr)² = p² + 8p + r⁴ ≥ p²`), and `(p-r²)/(4p) ≥ 1/8` for
  `p ≥ 2r²`, so `y ≥ p/(8r)` — unbounded **above** (`centYFour_ge_far`).

`d = min(r²/2, r³/(8(|Y|+1)))` and `q = max(2r², 8r(|Y|+1))` make the two choices explicit, and
`d ≤ r²/2 < 2r² ≤ q` means the interval is never empty.  The intermediate value theorem then gives
`centYFour_surjective`, and with `vertexCentroidX_four` the locus is **exactly** the line `x = h₀`.

**WHICH LOCUS.**  The row has two, and this is the **vertex**-centroid one.  Conjecture 5's own
object — the **area**-centroid line `x = h₂` — is not settled at `N = 4`: `centroid2_y` says the
area centroid's `y`-coordinate is *unchanged* from `P`'s, not what it is, and at `N ≥ 4` the area
centroid is not the vertex average.  At `N = 3` the two coincide, which is why
`centroidY_surjective` settled both there and why nothing here inherits it.  This is `N = 4`
only: the chain rests on
the diagonal relations, which exist because `i+2 = i-2` in `ZMod 4`. -/

/-- The vertex centroid's `y`-coordinate at parameter `p`. -/
noncomputable def centYFour (p : ℝ) : ℝ := sigFour p * (p - rFour ^ 2) / (4 * p)

/-- The algebra behind `sum_tFour`, stated abstractly so `p` and `σ` can be eliminated without
rewriting inside `tFour0 p` itself — `← tFour_prod` would rewrite the `p` in `tFour0 p` too. -/
theorem centY_algebra (a b S P R : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hP : P ≠ 0)
    (hS : a + b = S) (hprod : a * b = P) :
    (a + (b + (-R / a + -R / b))) / 4 = S * (P - R) / (4 * P) := by
  subst hS
  subst hprod
  field_simp
  ring

/-- The vertex-centroid `y`-coordinate on the family is `σ(p − r²)/(4p)`. -/
theorem sum_tFour (p : ℝ) (hp : 0 < p) :
    (∑ i, (tFour p i + tFour p (i + 1)) / 2) / 4 = centYFour p := by
  rw [centroid0_y]
  have hu : (univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, tf0, tf1, tf2, tf3, centYFour]
  exact centY_algebra (tFour0 p) (tFour1 p) (sigFour p) p (rFour ^ 2)
    (ne_of_gt (tFour0_pos p hp)) (ne_of_gt (tFour1_pos p hp)) (ne_of_gt hp)
    (tFour_sum p) (tFour_prod p hp)

/-- `σ ≥ r`, from `σ² ≥ r⁴/r² = r²`. -/
theorem sigFour_ge (p : ℝ) (hp : 0 < p) : rFour ≤ sigFour p := by
  have hsq : rFour ^ 2 ≤ sigFour p ^ 2 := by
    rw [sigFour_sq p hp, le_div_iff₀ rFour_sq_pos]
    nlinarith [hp, sq_nonneg p]
  nlinarith [hsq, sigFour_pos p hp, rFour_pos]

/-- `(σr)² = p² + 8p + r⁴`.  Stated multiplicatively on purpose: with `p / rFour` the final
`nlinarith` in `centYFour_ge_far` must reason about `rFour⁻¹ * rFour` and fails. -/
theorem sigFour_mul_sq (p : ℝ) (hp : 0 < p) :
    (sigFour p * rFour) ^ 2 = p ^ 2 + 8 * p + (rFour ^ 2) ^ 2 := by
  have hne : rFour ≠ 0 := ne_of_gt rFour_pos
  rw [mul_pow, sigFour_sq p hp]
  field_simp

/-- `σr ≥ p`, from `(σr)² = p² + 8p + r⁴ ≥ p²`. -/
theorem sigFour_ge_mul (p : ℝ) (hp : 0 < p) : p ≤ sigFour p * rFour := by
  have hsq := sigFour_mul_sq p hp
  have hpos : 0 < sigFour p * rFour := mul_pos (sigFour_pos p hp) rFour_pos
  nlinarith [hsq, hpos, hp, sq_nonneg (rFour ^ 2)]

/-- The lower tail: `y ≤ -r³/(8p)` for `0 < p ≤ r²/2`, so the centroid is unbounded below. -/
theorem centYFour_le_near (p : ℝ) (hp : 0 < p) (hle : p ≤ rFour ^ 2 / 2) :
    centYFour p ≤ -(rFour ^ 3) / (8 * p) := by
  have hr := rFour_pos
  have hneg : p - rFour ^ 2 ≤ 0 := by nlinarith [rFour_sq_pos]
  have h1 : sigFour p * (p - rFour ^ 2) ≤ rFour * (p - rFour ^ 2) :=
    mul_le_mul_of_nonpos_right (sigFour_ge p hp) hneg
  have h2 : rFour * (p - rFour ^ 2) ≤ rFour * (-(rFour ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hr)
  have h3 : sigFour p * (p - rFour ^ 2) ≤ -(rFour ^ 3) / 2 := by nlinarith [h1, h2]
  rw [centYFour, div_le_div_iff₀ (by positivity : (0:ℝ) < 4 * p) (by positivity : (0:ℝ) < 8 * p)]
  nlinarith [h3, hp]

/-- The upper tail: `y ≥ p/(8r)` for `p ≥ 2r²`, so the centroid is unbounded above. -/
theorem centYFour_ge_far (p : ℝ) (hp : 2 * rFour ^ 2 ≤ p) :
    p / (8 * rFour) ≤ centYFour p := by
  have hr := rFour_pos
  have hRpos := rFour_sq_pos
  have hp0 : 0 < p := by nlinarith
  have hhalf : p / 2 ≤ p - rFour ^ 2 := by linarith
  have hspos := sigFour_pos p hp0
  have hsr := sigFour_ge_mul p hp0
  have hstep : p ^ 2 / 2 ≤ sigFour p * (p - rFour ^ 2) * rFour := by
    have h2 : sigFour p * (p / 2) * rFour ≤ sigFour p * (p - rFour ^ 2) * rFour :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhalf (le_of_lt hspos))
        (le_of_lt hr)
    have h3 : p * (p / 2) ≤ sigFour p * rFour * (p / 2) :=
      mul_le_mul_of_nonneg_right hsr (by positivity)
    nlinarith [h2, h3]
  rw [centYFour, div_le_div_iff₀ (by positivity : (0:ℝ) < 8 * rFour)
    (by positivity : (0:ℝ) < 4 * p)]
  nlinarith [hstep, hp0]

theorem exists_centYFour_le (Y : ℝ) :
    ∃ p, 0 < p ∧ p ≤ rFour ^ 2 / 2 ∧ centYFour p ≤ Y := by
  have hr := rFour_pos
  have hRpos := rFour_sq_pos
  set d : ℝ := min (rFour ^ 2 / 2) (rFour ^ 3 / (8 * (|Y| + 1))) with hd
  have hYpos : (0:ℝ) < |Y| + 1 := by positivity
  have hd0 : 0 < d := lt_min (by positivity) (by positivity)
  have hdle : d ≤ rFour ^ 2 / 2 := min_le_left _ _
  refine ⟨d, hd0, hdle, ?_⟩
  have hbound := centYFour_le_near d hd0 hdle
  have hd2 : d ≤ rFour ^ 3 / (8 * (|Y| + 1)) := min_le_right _ _
  have hstep : -(rFour ^ 3) / (8 * d) ≤ -(|Y| + 1) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 8 * d)]
    have : d * (8 * (|Y| + 1)) ≤ rFour ^ 3 := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 8 * (|Y| + 1))] at hd2
      linarith
    nlinarith [this]
  have : -(|Y| + 1) ≤ Y := by cases abs_cases Y with
    | inl h => linarith [h.1]
    | inr h => linarith [h.1]
  linarith [hbound, hstep, this]

theorem exists_centYFour_ge (Y : ℝ) :
    ∃ p, 0 < p ∧ 2 * rFour ^ 2 ≤ p ∧ Y ≤ centYFour p := by
  have hr := rFour_pos
  have hRpos := rFour_sq_pos
  set q : ℝ := max (2 * rFour ^ 2) (8 * rFour * (|Y| + 1)) with hq
  have hYpos : (0:ℝ) < |Y| + 1 := by positivity
  have hqge : 2 * rFour ^ 2 ≤ q := le_max_left _ _
  have hq0 : 0 < q := by nlinarith [hqge]
  refine ⟨q, hq0, hqge, ?_⟩
  have hbound := centYFour_ge_far q hqge
  have hq2 : 8 * rFour * (|Y| + 1) ≤ q := le_max_right _ _
  have hstep : |Y| + 1 ≤ q / (8 * rFour) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 8 * rFour)]
    nlinarith [hq2]
  have : Y ≤ |Y| + 1 := by cases abs_cases Y with
    | inl h => linarith [h.1]
    | inr h => linarith [h.1]
  linarith [hbound, hstep, this]

theorem centYFour_continuousOn (a b : ℝ) (ha : 0 < a) :
    ContinuousOn centYFour (Set.Icc a b) := by
  have hc : Continuous fun p : ℝ =>
      Real.sqrt ((p ^ 2 + 8 * p + (rFour ^ 2) ^ 2) / rFour ^ 2) :=
    Real.continuous_sqrt.comp (by fun_prop)
  have hs : ContinuousOn sigFour (Set.Icc a b) := by
    have : sigFour = fun p : ℝ => Real.sqrt ((p ^ 2 + 8 * p + (rFour ^ 2) ^ 2) / rFour ^ 2) := by
      funext p; rw [sigFour]
    rw [this]; exact hc.continuousOn
  apply ContinuousOn.div (hs.mul (by fun_prop)) (by fun_prop)
  intro x hx
  have : 0 < x := lt_of_lt_of_le ha hx.1
  positivity

/-- **RESIDUE (ii) AT `N = 4`, FOR THE VERTEX-CENTROID LOCUS: EVERY REAL VALUE IS ATTAINED.**
With `vertexCentroidX_four` this makes the locus exactly the line `x = h₀`. -/
theorem centYFour_surjective (Y : ℝ) :
    ∃ p, 0 < p ∧ (∀ i, tangencyDefect 1 rFour (tFour p) i = 0) ∧ centYFour p = Y := by
  obtain ⟨p1, hp1, hp1le, hY1⟩ := exists_centYFour_le Y
  obtain ⟨p2, hp2, hp2ge, hY2⟩ := exists_centYFour_ge Y
  have hRpos := rFour_sq_pos
  have hlt : p1 ≤ p2 := by linarith
  have hsub := intermediate_value_Icc hlt (centYFour_continuousOn p1 p2 hp1)
  have hmem : Y ∈ Set.Icc (centYFour p1) (centYFour p2) := ⟨hY1, hY2⟩
  obtain ⟨p, hpmem, hpval⟩ := hsub hmem
  have hppos : 0 < p := lt_of_lt_of_le hp1 hpmem.1
  exact ⟨p, hppos, tangency_tFour p hppos, hpval⟩

/-! ### General `N`: the Poncelet recurrence, and the sum companion of `S₂`

Everything above is `N = 3` or `N = 4`.  `defect_diff_bracket` was proved as a pure `ring` identity
and then used only at `N = 4`, by hand, four times — but applied to two CONSECUTIVE defects at
arbitrary `N` it gives a general fact, and the `N = 3` cubic and the `N = 4` diagonal relations are
both consequences of it rather than two coincidences:

    (tᵢ + tᵢ₊₂)(tᵢ₊₁² − r²) = −2tᵢ₊₁(4 − r²)      for every `i`,

i.e. a tangential `N`-gon is exactly an `N`-periodic orbit of
`tᵢ₊₂ = −2tᵢ₊₁(4−r²)/(tᵢ₊₁² − r²) − tᵢ`.  Summing it and reindexing `i+1 ↦ j` pins a symmetric
function that `S₂` does not see: `S₂ = ∑tᵢ²(tᵢ₊₁ − tᵢ₋₁)` is the shoelace DIFFERENCE and is free (it
is the area, and `S2_factor` makes it a Vandermonde product), while under tangency the corresponding
SUM is determined.

**WHAT THIS IS NOT.**  It is general-`N` *structure*, not the conjecture.  It does not pin the
closure radius at general `N` and it does not give `h₀`.  Recorded alongside it, because it bears on
residue (i): the banked cyclic sums `r² − 8` at `N = 3` and `2r² − 8` at `N = 4` fit `(N−2)r² − 8`,
and **that extrapolation is false** — solving for the closure radius from the recurrence and
computing the cyclic sum on the convex orbit gives `−5.7629` at `N = 5` against a predicted
`−5.0286`, and it misses at every `N` from 5 to 9.  It holds at exactly the two values it was read
off, which any two-parameter family would fit.  The sums instead decrease toward `−4√2`, so
`h₀ ~ √2/N`.  See `verify_352456.py` section (L).  A structural fact from the same computation: the
convex closure radii increase in `N` and accumulate at `r² = 1`
(`0.6863, 0.9443, 0.99046, 0.998366, 0.99972, 0.999952, 0.999992` for `N = 3…9`), which is why the
source states Conjecture 5 under `0 < r < f`: the family exhausts that range. -/

omit [NeZero N] in
/-- **THE PONCELET RECURRENCE, AT EVERY `N`** — the first general-`N` consequence of tangency on
this row.  No `NeZero N` is needed: this is a statement about two consecutive defects, not a sum
over the cycle. -/
theorem poncelet_recurrence (r : ℝ) (t : ZMod N → ℝ)
    (htan : ∀ i, tangencyDefect 1 r t i = 0) (i : ZMod N) (hne : t i - t (i + 2) ≠ 0) :
    (t i + t (i + 2)) * (t (i + 1) ^ 2 - r ^ 2) = -2 * t (i + 1) * (4 - r ^ 2) := by
  have d0 := htan i
  have d1 := htan (i + 1)
  simp only [tangencyDefect] at d0 d1
  have hidx : i + 1 + 1 = i + 2 := by ring
  rw [hidx] at d1
  have hfac : (t i - t (i + 2)) *
      ((t i + t (i + 2)) * (t (i + 1) ^ 2 - r ^ 2) + 2 * t (i + 1) * (4 - r ^ 2)) = 0 := by
    linear_combination d0 - d1
  have hz := (mul_eq_zero.mp hfac).resolve_left hne
  linarith [hz]

/-- Summing the recurrence over the cycle. -/
theorem poncelet_sum (r : ℝ) (t : ZMod N → ℝ)
    (htan : ∀ i, tangencyDefect 1 r t i = 0) (hnd : ∀ i, t i - t (i + 2) ≠ 0) :
    ∑ i, (t i + t (i + 2)) * (t (i + 1) ^ 2 - r ^ 2) = -2 * (4 - r ^ 2) * ∑ i, t i := by
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    poncelet_recurrence r t htan i (hnd i))]
  have hr : ∀ i : ZMod N,
      -2 * t (i + 1) * (4 - r ^ 2) = (-2 * (4 - r ^ 2)) * t (i + 1) := fun i => by ring
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hr i), ← Finset.mul_sum, sum_shift t]

/-- `∑ tᵢ₋₁ = ∑ tᵢ`, the backwards companion of `sum_shift`. -/
theorem sum_shift_back (F : ZMod N → ℝ) : ∑ i, F (i - 1) = ∑ i, F i := by
  have h := sum_shift (fun j : ZMod N => F (j - 1))
  have hidx : ∀ i : ZMod N, F (i + 1 - 1) = F i := by
    intro i; congr 1; ring
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hidx i)] at h
  exact h.symm

/-- **THE SUM COMPANION OF `S₂`.**  `S₂ = ∑ tᵢ²(tᵢ₊₁ − tᵢ₋₁)` is the shoelace DIFFERENCE and is
free; under tangency the corresponding SUM is pinned to `(4r² − 8)∑tᵢ`. -/
theorem poncelet_sum_identity (r : ℝ) (t : ZMod N → ℝ)
    (htan : ∀ i, tangencyDefect 1 r t i = 0) (hnd : ∀ i, t i - t (i + 2) ≠ 0) :
    ∑ i, t i ^ 2 * (t (i - 1) + t (i + 1)) = (4 * r ^ 2 - 8) * ∑ i, t i := by
  have hps := poncelet_sum r t htan hnd
  have hG := sum_shift (fun j : ZMod N => (t (j - 1) + t (j + 1)) * (t j ^ 2 - r ^ 2))
  have hidx : ∀ i : ZMod N,
      (t (i + 1 - 1) + t (i + 1 + 1)) * (t (i + 1) ^ 2 - r ^ 2)
        = (t i + t (i + 2)) * (t (i + 1) ^ 2 - r ^ 2) := by
    intro i
    have e1 : i + 1 - 1 = i := by ring
    have e2 : i + 1 + 1 = i + 2 := by ring
    rw [e1, e2]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hidx i), hps] at hG
  have hsplit : ∑ i : ZMod N, (t (i - 1) + t (i + 1)) * (t i ^ 2 - r ^ 2)
      = (∑ i, t i ^ 2 * (t (i - 1) + t (i + 1)))
        - r ^ 2 * ∑ i, (t (i - 1) + t (i + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have htwo : ∑ i : ZMod N, (t (i - 1) + t (i + 1)) = 2 * ∑ i, t i := by
    rw [Finset.sum_add_distrib, sum_shift_back t, sum_shift t]
    ring
  rw [hsplit, htwo] at hG
  linarith [hG]

/-! ### `h₀` AT `N = 3`: RESIDUE (i) CLOSED THERE TOO, AND THE TWO LOCI COINCIDE

`vertexCentroidX_four` closed residue (i) at `N = 4`.  At `N = 3` the closed form was sitting
inside `OnFamily`'s own first conjunct: that conjunct **is** the Vieta relation
`∑ᵢ tᵢtᵢ₊₁ = r² − 8`, so the vertex-centroid abscissa is `(8 − r²)/12` with no dependence on the
family parameter `s`.  That is residue (i)'s content at `N = 3`, and it is the reason the numerical
survey found `h₀` identical across every orbit at a given level.

The pay-off is `centroids_coincide_three`.  The module asserted in prose that the vertex and area
centroids *"stop coinciding"* at `N ≥ 4`; nothing proved they coincide at `N = 3`.  They do, because
`h₂ = (8f² − r²)/(12f)` is `(8 − r²)/12` at `f = 1` — exactly `h₀`.  The coincidence is not a
triviality: at `N = 4` the constant is `(4 − r²)/8`, a different function of `r²`.

`N ≥ 5` is untouched, and so is residue (ii) (completeness of the locus as a full line). -/

/-- **`h₀` AT `N = 3`, IN CLOSED FORM.**  Straight off the family's first Vieta conjunct: the
cyclic sum is `r² − 8`, so the vertex centroid's abscissa is `(8 − r²)/12`, independent of `s`. -/
theorem vertexCentroidX_three_of_onFamily (r : ℝ) (t : ZMod 3 → ℝ) (hf : OnFamily r t) :
    (∑ i, -(t i * t (i + 1)) / 4) / 3 = (8 - r ^ 2) / 12 := by
  have hE := hf.1
  have hu : (univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have i0 : ((0 : ZMod 3) + 1) = 1 := by decide
  have i1 : ((1 : ZMod 3) + 1) = 2 := by decide
  have i2 : ((2 : ZMod 3) + 1) = 0 := by decide
  rw [i0, i1, i2]
  linarith [hE]

/-- The tangency form, matching `vertexCentroidX_four`'s shape.  Distinctness enters exactly where
it always does at `N = 3`, through `onFamily_of_tangency`. -/
theorem vertexCentroidX_three (r : ℝ) (t : ZMod 3 → ℝ)
    (htan : ∀ i, tangencyDefect 1 r t i = 0)
    (h01 : t 0 ≠ t 1) (h12 : t 1 ≠ t 2) (h20 : t 2 ≠ t 0) :
    (∑ i, -(t i * t (i + 1)) / 4) / 3 = (8 - r ^ 2) / 12 :=
  vertexCentroidX_three_of_onFamily r t (onFamily_of_tangency r t htan h01 h12 h20)

/-- `h₀` at the explicit witness triangle, where it is `(2√2 − 1)/3`. -/
theorem vertexCentroidX_at_three_witness :
    (∑ i, -(tClose i * tClose (i + 1)) / 4) / 3 = (8 - rClose ^ 2) / 12 :=
  vertexCentroidX_three_of_onFamily rClose tClose tClose_onFamily

/-- **THE TWO CENTROID LOCI COINCIDE AT `N = 3`** — a claim this module previously made only in a
comment.  At `N = 4` they do not: `h₀ = (4 − r²)/8` against `h₂ = (8 − r²)/12`. -/
theorem centroids_coincide_three (r : ℝ) (t : ZMod 3 → ℝ)
    (htan : ∀ i, tangencyDefect 1 r t i = 0) (hA : S2 t ≠ 0)
    (h01 : t 0 ≠ t 1) (h12 : t 1 ≠ t 2) (h20 : t 2 ≠ t 0) :
    -S32 t / (12 * 1 * S2 t) = (∑ i, -(t i * t (i + 1)) / 4) / 3 := by
  rw [vertexCentroidX_three r t htan h01 h12 h20,
    polar_centroid_x 1 r one_ne_zero t htan hA]
  norm_num

/-! ### RESIDUE (i) IS CLOSED AT `N = 4` — and the constraint above is what closes it

The `N = 4` section concludes with *"what is closed is a constraint, not the locus"*.  That
undersells it.  Residue (i)'s content, by this row's own reduction, is that
`∑_i 1/(t_i² − r²)` is a **constant of the family**; and the constraint
`t_i · t_{i+2} = −r²` delivers exactly that, because of an algebraic accident that needs no
Poncelet theory at all:

    a·b = −r²   ⟹   1/(a² − r²) + 1/(b² − r²) = −1/r²,

**independent of `a`**.  So at `N = 4` the two diagonal pairs each contribute `−1/r²` and the
whole reciprocal sum is `−2/r²` — constant, with no free parameter surviving.  The `N = 3`
value is `2(2 − r²)/(r²(r² − 4))` (`reciprocal_sum_eq`); the two differ, as they should, since
the constant is per-`N`.

**What this changes, stated precisely.**  Residue (i) is now closed at `N = 3` *and* `N = 4`.
It remains open for general `N`, because `opposite_prod_of_tangency_four` is genuinely a
four-gon fact — at `N ≥ 5` the brackets pair up differently and no analogue is available here.
So the row stays a SPINE.  What has gone is the *reason* the `N = 4` work was filed as a
by-product: the constraint was the locus, one lemma away. -/

/-- **The pairing accident.**  If `a·b = −r²` then the two reciprocal terms sum to `−1/r²`
with `a` cancelling out entirely.  Nothing here is about Poncelet polygons; it is why the
diagonal constraint closes residue (i) at `N = 4`. -/
theorem recip_pair_of_prod_eq (a b r : ℝ) (hab : a * b = -r ^ 2) (hr : r ≠ 0)
    (ha : a ^ 2 - r ^ 2 ≠ 0) (hb : b ^ 2 - r ^ 2 ≠ 0) :
    1 / (a ^ 2 - r ^ 2) + 1 / (b ^ 2 - r ^ 2) = -1 / r ^ 2 := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  field_simp
  linear_combination (a * b - r ^ 2) * hab

/-- **THE RECIPROCAL SUM IS A CONSTANT OF THE FAMILY AT `N = 4`, equal to `−2/r²`** — residue
(i), closed at the second value of `N`, straight off `opposite_prod_of_tangency_four`, which
until now nothing in this module consumed. -/
theorem reciprocal_sum_four (r : ℝ) (t : ZMod 4 → ℝ)
    (htan : ∀ i, tangencyDefect 1 r t i = 0) (hr : r ≠ 0) (hr4 : r ^ 2 - 4 ≠ 0)
    (h02 : t 0 - t 2 ≠ 0) (h13 : t 1 - t 3 ≠ 0)
    (d0 : t 0 ^ 2 - r ^ 2 ≠ 0) (d1 : t 1 ^ 2 - r ^ 2 ≠ 0)
    (d2 : t 2 ^ 2 - r ^ 2 ≠ 0) (d3 : t 3 ^ 2 - r ^ 2 ≠ 0) :
    1 / (t 0 ^ 2 - r ^ 2) + 1 / (t 1 ^ 2 - r ^ 2)
      + 1 / (t 2 ^ 2 - r ^ 2) + 1 / (t 3 ^ 2 - r ^ 2) = -2 / r ^ 2 := by
  obtain ⟨h13p, h02p⟩ := opposite_prod_of_tangency_four r t htan hr4 h02 h13
  have e02 := recip_pair_of_prod_eq (t 0) (t 2) r h02p hr d0 d2
  have e13 := recip_pair_of_prod_eq (t 1) (t 3) r h13p hr d1 d3
  -- NB do NOT `field_simp` here: the four reciprocals are already ATOMS, so the goal is
  -- linear in them and `linarith` closes it directly.  Clearing denominators first destroys
  -- that structure and `linarith` then fails.  Only the constant needs splitting.
  have hsplit : (-1 : ℝ) / r ^ 2 + -1 / r ^ 2 = -2 / r ^ 2 := by
    field_simp
    norm_num
  linarith [e02, e13, hsplit]

end Principia.MathDB.P352456
