import Mathlib

set_option autoImplicit false

/-!
# MathDB #363173 — the `L_α` resultant-mean comparison (SPINE)

Write-up `mathdb-open-problems/problems/363173/solution.tex` on the `mathdb-results` branch
of `antoshashakov/Principia-Math-In-Progress`.
Source: L. Mihoković and M. Raïssouli, *Results on comparison and sub/super-stabilizability
of some new means*, arXiv:2405.13618v2; Appl. Anal. Discrete Math. **20** (2026) 1–23,
**Conjecture 4.2** (= Conjecture 32, p. 20).

For `0 < |α| < 1/2`, with `r = √(1 + 16α² − 16α⁴)`, `p = ±r` and `q = (1−p)/2 − 2α²`, the
conjecture asserts the strict comparison `L_α < R(B_p, L_α, B_q)` on both power-mean
branches.

## The whole transcendental content is ONE inequality

The write-up proves the comparison from strict concavity of `Φ_t(u) = √u·coth(t√u)`, which
it derives from the DLMF 4.36.3 partial-fraction expansion of `coth`, with termwise
differentiation justified by uniform convergence on compacts.  **None of that is needed.**

* The parameter `t` is spurious: `Φ_t(u) = (1/t)·K(t²u)`, so concavity for every `t` is
  concavity of the single `t`-free `K`.
* Concavity of `K` is exactly `D(z) > 0` for `z > 0`, where
  `D(z) = cosh z·sinh²z + z·sinh z − 2z²·cosh z`.
* `Real.cosh_three_mul` and `Real.sinh_sq` turn `4D` into

      E(z) = cosh 3z − cosh z − 8z²·cosh z + 4z·sinh z,

  and `E > 0` on `(0,∞)` is the entire transcendental content of the row.

**`E` has a sixth-order tangency at `0`** — every derivative through the fifth vanishes
there, and `E(1/1000) ≈ 7.1·10⁻¹⁹` — which is why no `nlinarith` on a truncated polynomial
can see it.  What works is the sixth derivative: with `c = cosh z ≥ 1`, `z ≤ sinh z` and
`z² ≤ sinh²z = c²−1`,

    E⁽⁶⁾(z) ≥ 2908c³ − 92c² − 2396c + 92 = 512 + (c−1)(2908c² + 2816c + 420) ≥ 512,

a cubic that `nlinarith` closes outright, and six `strictMonoOn_of_deriv_pos` steps from `0`
carry it back to `E`.  No series, no uniform convergence, no DLMF, no `tsum`.

## The derivative ladder is uniform, which is what makes this short

Every derivative of `E` has one of two shapes,

    Ev a b c z = a·z·sinh z + (−8z² + b)·cosh z + c·cosh 3z,
    Od a b c z = a·z·cosh z + (−8z² + b)·sinh z + c·sinh 3z,

and differentiating maps `Ev a b c ↦ Od (a−16) (a+b) (3c)` and `Od a b c ↦ Ev (a−16) (a+b) (3c)`
— the *same* coefficient rule both ways.  So two lemmas cover all six steps:

    E   = Ev   4   (−1)   1        E⁽³⁾ = Od (−44) (−37)  27
    E'  = Od (−12)   3     3       E⁽⁴⁾ = Ev (−60) (−81)  81
    E'' = Ev (−28)  (−9)   9       E⁽⁵⁾ = Od (−76) (−141) 243
                                    E⁽⁶⁾ = Ev (−92) (−217) 729

`Ev a b c 0 = b + c` and `Od a b c 0 = 0`, so the six vanishing conditions are arithmetic:
`−1+1 = −9+9 = −81+81 = 0`, while `−217+729 = 512` is exactly the sixth-derivative value.

## What is NOT proved here

The substitution `T = v'·W` and the rectangle-increment step.  They are carried as named
hypotheses, so this row is a SPINE and is NOT counted as fully verified.  Neither is
blocked: the rectangle step needs no Fubini — two `strictAntiOn_of_deriv_neg` calls replace
the write-up's double integral — and the `p`-th-root reversal is
`Real.rpow_lt_rpow_of_neg`, which exists.

*No longer carried* (see §"The bridge", below): strict concavity of `K` — and of `Φ_t` for
every `t > 0` — is now PROVED from `D_pos`, and the parameter identities (`r² + κ² + 2κ = 4`
and the two convex-combination identities for `C²`) were proved earlier.

**One half of the source's Lemma is still absent, deliberately recorded.**  The write-up's
concavity lemma asserts that `Φ_t` is strictly INCREASING as well as strictly concave, and
it uses the increasing half downstream (§"From concavity to the resultant mean").  Only the
concavity half is formalised here.

**215 check.**  `α = 0` and `|α| = 1/2` are EQUALITY cases, not strict, and `α = 0` is the
already-published logarithmic-mean example that precedes the conjecture in the source.  The
Lean therefore states `0 < |α| < 1/2` exactly as the write-up's Theorem 1 does, and NOT the
printed conjecture's wider range — refuting or proving on the wider range would be a
different claim.  `Real.coth` does not exist in Mathlib (grepped); everything here is stated
with `cosh`/`sinh` directly, where every identity needed is present.

Chain verified first, symbolically: `4D − E = 0` identically; `E⁽ᵏ⁾(0) = 0` for `k ≤ 5` and
`E⁽⁶⁾(0) = 512`; the closed form of `E⁽⁶⁾`; and the cubic lower bound with minimum `512` at
`c = 1`.
-/

namespace Principia.MathDB.P363173

open Real

/-! ### The two shapes, and the single coefficient rule -/

/-- Even-index shape: `a·z·sinh z + (−8z² + b)·cosh z + c·cosh 3z`. -/
noncomputable def Ev (a b c z : ℝ) : ℝ :=
  a * z * sinh z + (-8 * z ^ 2 + b) * cosh z + c * cosh (3 * z)

/-- Odd-index shape: `a·z·cosh z + (−8z² + b)·sinh z + c·sinh 3z`. -/
noncomputable def Od (a b c z : ℝ) : ℝ :=
  a * z * cosh z + (-8 * z ^ 2 + b) * sinh z + c * sinh (3 * z)

theorem hasDerivAt_lin (a z : ℝ) : HasDerivAt (fun w : ℝ => a * w) a z := by
  have h := (hasDerivAt_id z).const_mul a
  exact h.congr_deriv (by ring)

theorem hasDerivAt_cosh3 (z : ℝ) :
    HasDerivAt (fun w : ℝ => cosh (3 * w)) (3 * sinh (3 * z)) z := by
  have h := (Real.hasDerivAt_cosh (3 * z)).comp z (hasDerivAt_lin 3 z)
  simp only [Function.comp_def] at h
  exact h.congr_deriv (by ring)

theorem hasDerivAt_sinh3 (z : ℝ) :
    HasDerivAt (fun w : ℝ => sinh (3 * w)) (3 * cosh (3 * z)) z := by
  have h := (Real.hasDerivAt_sinh (3 * z)).comp z (hasDerivAt_lin 3 z)
  simp only [Function.comp_def] at h
  exact h.congr_deriv (by ring)

theorem hasDerivAt_quad (b z : ℝ) :
    HasDerivAt (fun w : ℝ => -8 * w ^ 2 + b) (-16 * z) z := by
  have h := ((hasDerivAt_pow 2 z).const_mul (-8 : ℝ)).add_const b
  exact h.congr_deriv (by push_cast; ring)

/-- **The coefficient rule, even → odd.** -/
theorem hasDerivAt_Ev (a b c z : ℝ) :
    HasDerivAt (Ev a b c) (Od (a - 16) (a + b) (3 * c) z) z := by
  have h1 : HasDerivAt (fun w : ℝ => a * w * sinh w)
      (a * sinh z + a * z * cosh z) z :=
    ((hasDerivAt_lin a z).mul (Real.hasDerivAt_sinh z)).congr_deriv (by ring)
  have h2 : HasDerivAt (fun w : ℝ => (-8 * w ^ 2 + b) * cosh w)
      (-16 * z * cosh z + (-8 * z ^ 2 + b) * sinh z) z :=
    ((hasDerivAt_quad b z).mul (Real.hasDerivAt_cosh z)).congr_deriv (by ring)
  have h3 : HasDerivAt (fun w : ℝ => c * cosh (3 * w)) (c * (3 * sinh (3 * z))) z :=
    (hasDerivAt_cosh3 z).const_mul c
  exact ((h1.add h2).add h3).congr_deriv (by simp only [Od]; ring)

/-- **The coefficient rule, odd → even.**  The same rule. -/
theorem hasDerivAt_Od (a b c z : ℝ) :
    HasDerivAt (Od a b c) (Ev (a - 16) (a + b) (3 * c) z) z := by
  have h1 : HasDerivAt (fun w : ℝ => a * w * cosh w)
      (a * cosh z + a * z * sinh z) z :=
    ((hasDerivAt_lin a z).mul (Real.hasDerivAt_cosh z)).congr_deriv (by ring)
  have h2 : HasDerivAt (fun w : ℝ => (-8 * w ^ 2 + b) * sinh w)
      (-16 * z * sinh z + (-8 * z ^ 2 + b) * cosh z) z :=
    ((hasDerivAt_quad b z).mul (Real.hasDerivAt_sinh z)).congr_deriv (by ring)
  have h3 : HasDerivAt (fun w : ℝ => c * sinh (3 * w)) (c * (3 * cosh (3 * z))) z :=
    (hasDerivAt_sinh3 z).const_mul c
  exact ((h1.add h2).add h3).congr_deriv (by simp only [Ev]; ring)

theorem Ev_zero (a b c : ℝ) : Ev a b c 0 = b + c := by
  simp [Ev]

theorem Od_zero (a b c : ℝ) : Od a b c 0 = 0 := by
  simp [Od]

/-! ### The bottom of the ladder: the sixth derivative -/

/-- **`E⁽⁶⁾ ≥ 512`.**  With `c = cosh z`, `cosh 3z = 4c³ − 3c`, `z ≤ sinh z` and
`z² ≤ sinh²z = c² − 1`, the sixth derivative dominates
`2908c³ − 92c² − 2396c + 92 = 512 + (c−1)(2908c² + 2816c + 420)`. -/
theorem E6_ge {z : ℝ} (hz : 0 ≤ z) : 512 ≤ Ev (-92) (-217) 729 z := by
  have hc : 1 ≤ cosh z := one_le_cosh z
  have hs0 : 0 ≤ sinh z := sinh_nonneg_iff.mpr hz
  have hs : z ≤ sinh z := self_le_sinh_iff.mpr hz
  have hsq : sinh z ^ 2 = cosh z ^ 2 - 1 := by
    have := Real.cosh_sq_sub_sinh_sq z
    linarith
  have h3 : cosh (3 * z) = 4 * cosh z ^ 3 - 3 * cosh z := Real.cosh_three_mul z
  have hzs : z * sinh z ≤ sinh z ^ 2 := by nlinarith
  have hz2 : z ^ 2 ≤ sinh z ^ 2 := by nlinarith
  have hcube : 0 ≤ (cosh z - 1) * (2908 * cosh z ^ 2 + 2816 * cosh z + 420) := by
    apply mul_nonneg (by linarith)
    nlinarith
  simp only [Ev, h3]
  nlinarith [hzs, hz2, hsq, hc, hcube, mul_nonneg (sub_nonneg.mpr hc) hs0]

/-! ### Climbing the ladder -/

/-- If `f 0 = 0` and `f' > 0` on `(0,∞)`, then `f > 0` on `(0,∞)`. -/
theorem pos_of_deriv_pos {f g : ℝ → ℝ} (hd : ∀ z, HasDerivAt f (g z) z) (h0 : f 0 = 0)
    (hg : ∀ z, 0 < z → 0 < g z) {z : ℝ} (hz : 0 < z) : 0 < f z := by
  have hmono : StrictMonoOn f (Set.Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
    · exact fun x _ => ((hd x).differentiableAt).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      exact hg x hx
  have h := hmono Set.self_mem_Ici (Set.mem_Ici.mpr (le_of_lt hz)) hz
  rw [h0] at h
  exact h

theorem E5_pos {z : ℝ} (hz : 0 < z) : 0 < Od (-76) (-141) 243 z := by
  refine pos_of_deriv_pos (g := Ev (-92) (-217) 729) (fun w => ?_) (Od_zero _ _ _)
    (fun w hw => by linarith [E6_ge (le_of_lt hw)]) hz
  have := hasDerivAt_Od (-76 : ℝ) (-141) 243 w
  norm_num at this
  exact this

theorem E4_pos {z : ℝ} (hz : 0 < z) : 0 < Ev (-60) (-81) 81 z := by
  refine pos_of_deriv_pos (g := Od (-76) (-141) 243) (fun w => ?_)
    (by rw [Ev_zero]; norm_num) (fun _ hw => E5_pos hw) hz
  have := hasDerivAt_Ev (-60 : ℝ) (-81) 81 w
  norm_num at this
  exact this

theorem E3_pos {z : ℝ} (hz : 0 < z) : 0 < Od (-44) (-37) 27 z := by
  refine pos_of_deriv_pos (g := Ev (-60) (-81) 81) (fun w => ?_) (Od_zero _ _ _)
    (fun _ hw => E4_pos hw) hz
  have := hasDerivAt_Od (-44 : ℝ) (-37) 27 w
  norm_num at this
  exact this

theorem E2_pos {z : ℝ} (hz : 0 < z) : 0 < Ev (-28) (-9) 9 z := by
  refine pos_of_deriv_pos (g := Od (-44) (-37) 27) (fun w => ?_)
    (by rw [Ev_zero]; norm_num) (fun _ hw => E3_pos hw) hz
  have := hasDerivAt_Ev (-28 : ℝ) (-9) 9 w
  norm_num at this
  exact this

theorem E1_pos {z : ℝ} (hz : 0 < z) : 0 < Od (-12) 3 3 z := by
  refine pos_of_deriv_pos (g := Ev (-28) (-9) 9) (fun w => ?_) (Od_zero _ _ _)
    (fun _ hw => E2_pos hw) hz
  have := hasDerivAt_Od (-12 : ℝ) 3 3 w
  norm_num at this
  exact this

/-- **The transcendental content of the row.**
`E(z) = cosh 3z − cosh z − 8z²·cosh z + 4z·sinh z > 0` for `z > 0`. -/
theorem E_pos {z : ℝ} (hz : 0 < z) : 0 < Ev 4 (-1) 1 z := by
  refine pos_of_deriv_pos (g := Od (-12) 3 3) (fun w => ?_)
    (by rw [Ev_zero]; norm_num) (fun _ hw => E1_pos hw) hz
  have := hasDerivAt_Ev (4 : ℝ) (-1) 1 w
  norm_num at this
  exact this

/-- **`D > 0`**, the form the concavity argument consumes: `4D = E`. -/
theorem D_pos {z : ℝ} (hz : 0 < z) :
    0 < cosh z * sinh z ^ 2 + z * sinh z - 2 * z ^ 2 * cosh z := by
  have h := E_pos hz
  have h3 : cosh (3 * z) = 4 * cosh z ^ 3 - 3 * cosh z := Real.cosh_three_mul z
  have hsq : sinh z ^ 2 = cosh z ^ 2 - 1 := by
    have hc := Real.cosh_sq_sub_sinh_sq z
    linarith
  have key : Ev 4 (-1) 1 z
      = 4 * (cosh z * sinh z ^ 2 + z * sinh z - 2 * z ^ 2 * cosh z) := by
    simp only [Ev, h3, hsq]
    ring
  rw [key] at h
  linarith


/-! ### From `D > 0` to the comparison: the seam, and the parameter algebra

`D_pos` is the transcendental content, but on its own nothing consumes it.  The carried
step is therefore stated so that `D_pos` is its INPUT: `ConcaveOfD` says that the sign
condition yields strict concavity of the write-up's `Φ`.  Everything downstream of the
concavity — the parameter identities and the inequality `W < 0` they produce — is proved. -/

/-- The carried passage from the sign condition to strict concavity.  Its hypothesis is
exactly `D_pos`, so `concave_Phi` discharges it. -/
def ConcaveOfD (Phi : ℝ → ℝ) : Prop :=
  (∀ z : ℝ, 0 < z → 0 < cosh z * sinh z ^ 2 + z * sinh z - 2 * z ^ 2 * cosh z) →
    StrictConcaveOn ℝ (Set.Ioi 0) Phi

/-- **`D_pos` is consumed here.** -/
theorem concave_Phi {Phi : ℝ → ℝ} (h : ConcaveOfD Phi) :
    StrictConcaveOn ℝ (Set.Ioi 0) Phi :=
  h (fun _ hz => D_pos hz)

/-! #### The parameter identities

With `κ = 1 - 4α²` and `r² = 1 + 16α² - 16α⁴`, every identity the transfer needs is a
ring identity modulo `r²`; each is `linear_combination (1/8) * hr` after substituting `κ`. -/

/-- `r² + κ² + 2κ = 4`. -/
theorem param_identity {al r kap : ℝ} (hk : kap = 1 - 4 * al ^ 2)
    (hr : r ^ 2 = 1 + 16 * al ^ 2 - 16 * al ^ 4) : r ^ 2 + kap ^ 2 + 2 * kap = 4 := by
  subst hk
  linear_combination hr

/-- Branch `p = +r`, where `q = (κ-r)/2 < 0` and `C = (r-κ)/4`:
`2C² = (r+1)B² - (r-1)A²` with `A = 1/2`, `B = α`. -/
theorem convex_plus {al r kap : ℝ} (hk : kap = 1 - 4 * al ^ 2)
    (hr : r ^ 2 = 1 + 16 * al ^ 2 - 16 * al ^ 4) :
    2 * ((r - kap) / 4) ^ 2 = (r + 1) * al ^ 2 - (r - 1) * (1 / 2 : ℝ) ^ 2 := by
  subst hk
  linear_combination (1 / 8 : ℝ) * hr

/-- Branch `p = -r`, where `q = (κ+r)/2 > 0` and `C = (κ+r)/4`:
`2C² = (r+1)A² - (r-1)B²`.  **The same certificate closes both branches.** -/
theorem convex_minus {al r kap : ℝ} (hk : kap = 1 - 4 * al ^ 2)
    (hr : r ^ 2 = 1 + 16 * al ^ 2 - 16 * al ^ 4) :
    2 * ((kap + r) / 4) ^ 2 = (r + 1) * (1 / 2 : ℝ) ^ 2 - (r - 1) * al ^ 2 := by
  subst hk
  linear_combination (1 / 8 : ℝ) * hr

/-- `1 < r < 2` on the conjecture's range `0 < |α| < 1/2`.  Both endpoints are OPEN, and
that is not cosmetic: at `α = 0` and `|α| = 1/2` the comparison becomes an EQUALITY. -/
theorem r_bounds {al r : ℝ} (h0 : 0 < al) (h1 : al < 1 / 2) (hrpos : 0 < r)
    (hr : r ^ 2 = 1 + 16 * al ^ 2 - 16 * al ^ 4) : 1 < r ∧ r < 2 := by
  have hsq : 0 < al ^ 2 := by positivity
  have ha2 : al ^ 2 < 1 / 4 := by nlinarith
  -- `r² - 1 = 16α²(1-α²) > 0` and `4 - r² = (1-4α²)(3-4α²) > 0`
  have h1lt : 1 < r ^ 2 := by rw [hr]; nlinarith
  have hlt4 : r ^ 2 < 4 := by rw [hr]; nlinarith
  exact ⟨by nlinarith, by nlinarith⟩

/-! #### `W < 0`, the inequality the transfer consumes -/

/-- Strict concavity at a strict convex combination, in the form both branches need. -/
theorem concave_comb {Phi : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Set.Ioi 0) Phi)
    {u v w lam : ℝ} (hu : u ∈ Set.Ioi (0 : ℝ)) (hw : w ∈ Set.Ioi (0 : ℝ)) (hne : w ≠ u)
    (hl0 : 0 < lam) (hl1 : lam < 1) (hv : v = lam * w + (1 - lam) * u) :
    lam * Phi w + (1 - lam) * Phi u < Phi v := by
  have h := hconc.2 hw hu hne hl0 (by linarith : (0 : ℝ) < 1 - lam) (by ring)
  simp only [smul_eq_mul] at h
  rw [hv]
  exact h

/-- **`W < 0` on the `p = +r` branch.**  `B² = λC² + (1-λ)A²` with `λ = 2/(r+1) ∈ (0,1)`,
so strict concavity gives `(r+1)Φ(B²) > 2Φ(C²) + (r-1)Φ(A²)`. -/
theorem W_neg {Phi : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Set.Ioi 0) Phi)
    {r A2 B2 C2 : ℝ} (hA : A2 ∈ Set.Ioi (0 : ℝ)) (hC : C2 ∈ Set.Ioi (0 : ℝ))
    (hne : C2 ≠ A2) (hr1 : 1 < r) (hr2 : r < 2)
    (hcomb : B2 = (2 / (r + 1)) * C2 + (1 - 2 / (r + 1)) * A2) :
    (r - 1) * Phi A2 - (r + 1) * Phi B2 + 2 * Phi C2 < 0 := by
  have hrp : (0 : ℝ) < r + 1 := by linarith
  have hl0 : 0 < 2 / (r + 1) := by positivity
  have hl1 : 2 / (r + 1) < 1 := by
    rw [div_lt_one hrp]; linarith
  have h := concave_comb hconc hA hC hne hl0 hl1 hcomb
  have hkey : (r + 1) * ((2 / (r + 1)) * Phi C2 + (1 - 2 / (r + 1)) * Phi A2)
      = 2 * Phi C2 + (r - 1) * Phi A2 := by
    field_simp
    ring
  have h2 : 2 * Phi C2 + (r - 1) * Phi A2 < (r + 1) * Phi B2 := by
    rw [← hkey]
    exact mul_lt_mul_of_pos_left h hrp
  linarith

/-! ### The bridge: from `D > 0` to strict concavity, with no second derivative

`ConcaveOfD` was carried over an ARBITRARY `Φ`, which is unprovable as stated — closing it
means naming the write-up's actual `Φ` and proving its concavity.  The parameter `t` is
spurious (`Φ_t(u) = √u·coth(t√u) = (1/t)·K(t²u)`), so only

    `K(u) = √u · coth(√u) = g(√u)`,  `g(z) = z·cosh z / sinh z`

matters.  The obvious route — `strictConcaveOn_of_deriv2_neg` — needs `K''`, i.e. two
derivative chains through `√`.  **One suffices.**  Write `K' (u) = h(√u)` with

    `h(z) = (cosh z·sinh z − z) / (2z·sinh² z)`,

then `StrictAntiOn (deriv K)` follows from `StrictAntiOn h` because `√` is strictly
monotone, and `StrictAntiOn.strictConcaveOn_of_deriv` finishes.  So the only derivative
computed twice is `h'`, in the `z` variable, where

    `h'(z) = −D(z) / (2z²·sinh³ z)`  —  **exactly `D_pos`'s numerator**, with a manifestly
positive denominator.  Checked numerically first in `verify_363173_concavity.py`. -/

section Bridge

open Set

theorem sinh_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < sinh z := by
  have h := Real.sinh_lt_sinh.mpr hz
  simpa using h

/-- `g(z) = z·cosh z / sinh z`, the write-up's `Φ` in the `z = √u` variable. -/
noncomputable def gfun (z : ℝ) : ℝ := z * cosh z / sinh z

/-- `K(u) = g(√u) = √u·coth(√u)`: the write-up's `Φ` with the spurious `t` removed. -/
noncomputable def Kfun (u : ℝ) : ℝ := gfun (Real.sqrt u)

/-- `h(z) = (cosh z·sinh z − z)/(2z·sinh² z)`, which is `K'` read in the `z` variable. -/
noncomputable def hfun (z : ℝ) : ℝ := (cosh z * sinh z - z) / (2 * z * sinh z ^ 2)

/-- `g'(z) = (cosh z·sinh z − z)/sinh² z`.  The `z·(sinh² − cosh²)` released by the product
rule is `−z`, which is where the `−z` in the numerator comes from. -/
theorem hasDerivAt_gfun {z : ℝ} (hz : 0 < z) :
    HasDerivAt gfun ((cosh z * sinh z - z) / sinh z ^ 2) z := by
  have hs : sinh z ≠ 0 := ne_of_gt (sinh_pos_of_pos hz)
  have hnum : HasDerivAt (fun w : ℝ => w * cosh w) (1 * cosh z + z * sinh z) z :=
    (hasDerivAt_id z).mul (Real.hasDerivAt_cosh z)
  have hden : HasDerivAt sinh (cosh z) z := Real.hasDerivAt_sinh z
  have h := hnum.div hden hs
  refine h.congr_deriv ?_
  have hpy : cosh z ^ 2 - sinh z ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq z
  field_simp
  nlinarith [hpy]

/-- `K' (u) = h(√u)`: one chain rule through `√`, and the `1/(2√u)` is exactly the `2z` in
`h`'s denominator. -/
theorem hasDerivAt_Kfun {u : ℝ} (hu : 0 < u) :
    HasDerivAt Kfun (hfun (Real.sqrt u)) u := by
  have hsq : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hs : sinh (Real.sqrt u) ≠ 0 := ne_of_gt (sinh_pos_of_pos hsq)
  have h1 := hasDerivAt_gfun hsq
  have h2 : HasDerivAt (fun x : ℝ => Real.sqrt x) (1 / (2 * Real.sqrt u)) u :=
    Real.hasDerivAt_sqrt (ne_of_gt hu)
  have h := h1.comp u h2
  refine h.congr_deriv ?_
  rw [hfun]
  field_simp

/-- `h'(z) = −D(z)/(2z²·sinh³ z)`.  The numerator is `D` on the nose: expanding the quotient
rule and replacing `cosh²` by `1 + sinh²` collapses everything to `−2·sinh z·D(z)`. -/
theorem hasDerivAt_hfun {z : ℝ} (hz : 0 < z) :
    HasDerivAt hfun
      (-(cosh z * sinh z ^ 2 + z * sinh z - 2 * z ^ 2 * cosh z)
        / (2 * z ^ 2 * sinh z ^ 3)) z := by
  have hsp : 0 < sinh z := sinh_pos_of_pos hz
  have hs : sinh z ≠ 0 := ne_of_gt hsp
  have hzne : z ≠ 0 := ne_of_gt hz
  have hpy : cosh z ^ 2 - sinh z ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq z
  have hnum : HasDerivAt (fun w : ℝ => cosh w * sinh w - w)
      (sinh z * sinh z + cosh z * cosh z - 1) z :=
    (((Real.hasDerivAt_cosh z).mul (Real.hasDerivAt_sinh z)).sub (hasDerivAt_id z))
  -- kill `cosh²` in the numerator BEFORE the quotient rule, so one `hpy` closes the rest
  have hval : sinh z * sinh z + cosh z * cosh z - 1 = 2 * sinh z ^ 2 := by
    linear_combination hpy
  rw [hval] at hnum
  -- `.pow 2` would hand back the POINT-FREE `sinh ^ 2`; the `mul` route keeps the shape
  have hb : HasDerivAt (fun w : ℝ => sinh w ^ 2) (2 * sinh z * cosh z) z := by
    have he : (fun w : ℝ => sinh w ^ 2) = fun w : ℝ => sinh w * sinh w := by
      funext w; ring
    rw [he]
    exact ((Real.hasDerivAt_sinh z).mul (Real.hasDerivAt_sinh z)).congr_deriv (by ring)
  have ha : HasDerivAt (fun w : ℝ => 2 * w) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℝ)
  have hden : HasDerivAt (fun w : ℝ => 2 * w * sinh w ^ 2)
      (2 * sinh z ^ 2 + 2 * z * (2 * sinh z * cosh z)) z :=
    (ha.mul hb).congr_deriv (by ring)
  have hdne : 2 * z * sinh z ^ 2 ≠ 0 := by positivity
  have h := hnum.div hden hdne
  refine h.congr_deriv ?_
  field_simp
  linear_combination (-2 * z * sinh z) * hpy

/-- `h` is strictly decreasing on `(0,∞)` — this is where `D_pos` is consumed. -/
theorem hfun_strictAntiOn : StrictAntiOn hfun (Ioi (0 : ℝ)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
  · intro z hz
    have hzp : 0 < z := hz
    exact ((hasDerivAt_hfun hzp).continuousAt).continuousWithinAt
  · intro z hz
    rw [interior_Ioi] at hz
    have hzp : 0 < z := hz
    rw [(hasDerivAt_hfun hzp).deriv]
    have hsp : 0 < sinh z := sinh_pos_of_pos hzp
    have hD := D_pos hzp
    have hden : 0 < 2 * z ^ 2 * sinh z ^ 3 := by positivity
    exact div_neg_of_neg_of_pos (by linarith) hden

/-- `K` is strictly concave on `(0,∞)`.  `deriv K` is `h ∘ √`, and `√` is strictly monotone,
so antitonicity transfers; `StrictAntiOn.strictConcaveOn_of_deriv` then applies with no
second derivative anywhere. -/
theorem Kfun_strictConcaveOn : StrictConcaveOn ℝ (Ioi (0 : ℝ)) Kfun := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0) ?_ ?_
  · intro u hu
    have hup : 0 < u := hu
    exact ((hasDerivAt_Kfun hup).continuousAt).continuousWithinAt
  · rw [interior_Ioi]
    intro a ha b hb hab
    have hap : 0 < a := ha
    have hbp : 0 < b := hb
    rw [(hasDerivAt_Kfun hap).deriv, (hasDerivAt_Kfun hbp).deriv]
    refine hfun_strictAntiOn (Real.sqrt_pos.mpr hap) (Real.sqrt_pos.mpr hbp) ?_
    exact Real.sqrt_lt_sqrt (le_of_lt hap) hab

/-- **`ConcaveOfD` IS DISCHARGED at the write-up's own `Φ`.**  The carried link asserted the
passage from the sign condition to concavity for an arbitrary `Φ`; here it is proved for the
`Φ` the write-up actually uses, so nothing about it is assumed any more. -/
theorem concaveOfD_Kfun : ConcaveOfD Kfun := fun _ => Kfun_strictConcaveOn

/-- The concavity, now unconditional. -/
theorem Kfun_concave : StrictConcaveOn ℝ (Ioi (0 : ℝ)) Kfun :=
  concave_Phi concaveOfD_Kfun

/-- **`W < 0` for the write-up's own `Φ`, with nothing assumed.**  `W_neg` was stated for an
abstract strictly concave `Φ`; `Kfun_concave` supplies that for the `Φ` the conjecture is
actually about, so the whole ladder — `E6_ge` through `E_pos`, `D_pos`, the derivative
computation and the antitonicity transfer — is load-bearing here. -/
theorem W_neg_Kfun {r A2 B2 C2 : ℝ} (hA : A2 ∈ Set.Ioi (0 : ℝ))
    (hC : C2 ∈ Set.Ioi (0 : ℝ)) (hne : C2 ≠ A2) (hr1 : 1 < r) (hr2 : r < 2)
    (hcomb : B2 = (2 / (r + 1)) * C2 + (1 - 2 / (r + 1)) * A2) :
    (r - 1) * Kfun A2 - (r + 1) * Kfun B2 + 2 * Kfun C2 < 0 :=
  W_neg Kfun_concave hA hC hne hr1 hr2 hcomb

/-- The write-up's `Φ_t(u) = √u·coth(t√u)`, with the parameter restored. -/
noncomputable def Phifun (t u : ℝ) : ℝ :=
  Real.sqrt u * cosh (t * Real.sqrt u) / sinh (t * Real.sqrt u)

/-- **The parameter is a scaling, not new content**: `Φ_t(u) = (1/t)·K(t²u)`. -/
theorem Phifun_eq_Kfun {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    Phifun t u = Kfun (t ^ 2 * u) / t := by
  have h1 : Real.sqrt (t ^ 2 * u) = t * Real.sqrt u := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt ht)]
  have hs : sinh (t * Real.sqrt u) ≠ 0 :=
    ne_of_gt (sinh_pos_of_pos (by positivity))
  rw [Phifun, Kfun, gfun, h1]
  field_simp

/-- **Strict concavity of `Φ_t` for EVERY `t > 0`** — the concavity half of the write-up's
Lemma as it is actually stated, not just the `t = 1` case.  Concavity is not preserved by
reparametrisation in general, but `u ↦ t²u` is LINEAR and `1/t > 0`, so it is here. -/
theorem Phifun_strictConcaveOn {t : ℝ} (ht : 0 < t) :
    StrictConcaveOn ℝ (Set.Ioi (0 : ℝ)) (Phifun t) := by
  refine ⟨convex_Ioi 0, fun x hx y hy hne a b ha hb hab => ?_⟩
  have hx0 : (0 : ℝ) < x := hx
  have hy0 : (0 : ℝ) < y := hy
  have hcx : t ^ 2 * x ∈ Set.Ioi (0 : ℝ) := by
    simp only [Set.mem_Ioi]; positivity
  have hcy : t ^ 2 * y ∈ Set.Ioi (0 : ℝ) := by
    simp only [Set.mem_Ioi]; positivity
  have htne : (t : ℝ) ≠ 0 := ne_of_gt ht
  have hcne : t ^ 2 * x ≠ t ^ 2 * y := by
    intro h
    exact hne (by
      have h2 : (t : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 htne
      exact mul_left_cancel₀ h2 h)
  have hK := Kfun_strictConcaveOn.2 hcx hcy hcne ha hb hab
  simp only [smul_eq_mul] at hK ⊢
  have hcomb : a * (t ^ 2 * x) + b * (t ^ 2 * y) = t ^ 2 * (a * x + b * y) := by ring
  rw [hcomb] at hK
  have hmem : (0 : ℝ) < a * x + b * y := by positivity
  rw [Phifun_eq_Kfun ht hx0, Phifun_eq_Kfun ht hy0, Phifun_eq_Kfun ht hmem]
  have hstep : a * (Kfun (t ^ 2 * x) / t) + b * (Kfun (t ^ 2 * y) / t)
      = (a * Kfun (t ^ 2 * x) + b * Kfun (t ^ 2 * y)) / t := by ring
  rw [hstep, div_lt_div_iff_of_pos_right ht]
  exact hK

/-- **`W < 0` for the write-up's `Φ_t`, every `t > 0`, nothing assumed.** -/
theorem W_neg_Phifun {t : ℝ} (ht : 0 < t) {r A2 B2 C2 : ℝ}
    (hA : A2 ∈ Set.Ioi (0 : ℝ)) (hC : C2 ∈ Set.Ioi (0 : ℝ)) (hne : C2 ≠ A2)
    (hr1 : 1 < r) (hr2 : r < 2)
    (hcomb : B2 = (2 / (r + 1)) * C2 + (1 - 2 / (r + 1)) * A2) :
    (r - 1) * Phifun t A2 - (r + 1) * Phifun t B2 + 2 * Phifun t C2 < 0 :=
  W_neg (Phifun_strictConcaveOn ht) hA hC hne hr1 hr2 hcomb

end Bridge

/-! ### The substitution `T = v'·W` — one of the two remaining steps

The row recorded two unformalised steps: *"the substitution `T = v'·W`"* and *"the rectangle
increment"*.  This section does the first, and it is the one that makes `W_neg_Phifun` — and
with it the whole `D_pos` ladder — CONSUMED rather than terminal.

With `f_c(t) = c·coth(ct)`:

* `f_c' = c² − f_c²` (`hasDerivAt_fc`) — the quotient rule and `cosh² − sinh² = 1`;
* `v' = f_{1/2} − f_α` (`hasDerivAt_vfun`) — `v` is a log of a quotient of `sinh`s, so this is
  three derivatives and a `field_simp`;
* hence `v'' = κ/4 − (f_A + f_B)·v'` with `κ/4 = 1/4 − α²` (`hasDerivAt_vp`);
* and `T := v'' + p(v')² + q·coth(qt/2)·v' − κ/4 = v'·W` by `ring` (`T_eq`), since
  `q·coth(qt/2) = 2f_C`.

**`T` is not a new object.**  That is the content of `T_eq`: the write-up's `T` is `v'` times
exactly the quantity the concavity lemma bounds, which is why the transfer needs no new analysis.

`v' > 0` is the INCREASING half of the write-up's concavity lemma, and it was not formalised
either: `hfun_pos` (the numerator is `sinh(2z)/2 − z > 0`) gives `Kfun_strictMonoOn`, and
`Phifun_strictMonoOn` carries it through the `t`-scaling.  `T_neg` and `T_neg_minus` are the two
parameter branches, `p = +r` and `p = −r`; they differ only in which of `A²`, `B²` is the
interpolated point, and `W_neg_Phifun` is stated for an arbitrary convex combination, so one
lemma serves both.

**What is still missing**: the rectangle increment — `H(a,c) + H(c,b) − H(a,b) < 0` from
`H_ab < 0`.  It needs `h'' − sh' = phT` and two `strictAntiOn_of_deriv_neg` calls (no Fubini:
the double integral is a composition of two one-variable monotonicity statements).  It is
UNFORMALISED, not assumed; the module still has no `Prop` parameter. -/

section Transfer

open Set

/-! ### The substitution `T = v'·W`

The write-up's transfer step.  `v(t) = log(2α·sinh(t/2)/sinh(αt))` has `v' = f_A − f_B` with
`f_c(t) = c·coth(ct)`, and `f_c' = c² − f_c²`, so

    `v'' = κ/4 − (f_A + f_B)·v'`,  `κ/4 = 1/4 − α²`,

whence `T := v'' + p(v')² + q·coth(qt/2)·v' − κ/4` collapses, by `ring` alone, to `v'·W`.  Since
`W < 0` is `W_neg_Phifun` and `v' > 0` is the INCREASING half of the concavity lemma, `T < 0`.
-/

/-- `h > 0` on `(0,∞)`: the numerator is `sinh(2z)/2 − z`, and `sinh w > w` for `w > 0`. -/
theorem hfun_pos {z : ℝ} (hz : 0 < z) : 0 < hfun z := by
  have hsp : 0 < sinh z := sinh_pos_of_pos hz
  have h2 : (2 : ℝ) * z < sinh (2 * z) := Real.self_lt_sinh_iff.mpr (by linarith)
  have hd : sinh (2 * z) = 2 * sinh z * cosh z := Real.sinh_two_mul z
  have hnum : 0 < cosh z * sinh z - z := by
    rw [hd] at h2
    nlinarith [h2]
  have hden : 0 < 2 * z * sinh z ^ 2 := by positivity
  exact div_pos hnum hden

/-- `K` is strictly increasing on `(0,∞)` — the increasing half of the write-up's concavity
lemma, which `v' > 0` consumes. -/
theorem Kfun_strictMonoOn : StrictMonoOn Kfun (Ioi (0 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro u hu
    have hup : 0 < u := hu
    exact ((hasDerivAt_Kfun hup).continuousAt).continuousWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    have hup : 0 < u := hu
    rw [(hasDerivAt_Kfun hup).deriv]
    exact hfun_pos (Real.sqrt_pos.mpr hup)

theorem Phifun_strictMonoOn {t : ℝ} (ht : 0 < t) :
    StrictMonoOn (Phifun t) (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := hx
  have hy0 : (0 : ℝ) < y := hy
  rw [Phifun_eq_Kfun ht hx0, Phifun_eq_Kfun ht hy0, div_lt_div_iff_of_pos_right ht]
  refine Kfun_strictMonoOn (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity) ?_
  exact mul_lt_mul_of_pos_left hxy (by positivity)

/-- `f_c(t) = c·coth(ct)`, the write-up's `f_c`. -/
noncomputable def fc (c t : ℝ) : ℝ := c * cosh (c * t) / sinh (c * t)

theorem fc_eq_Phifun {c t : ℝ} (hc : 0 < c) : fc c t = Phifun t (c ^ 2) := by
  have hsq : Real.sqrt (c ^ 2) = c := Real.sqrt_sq (le_of_lt hc)
  rw [fc, Phifun, hsq, mul_comm t c]

/-- **`f_c' = c² − f_c²`.**  The product/quotient rule plus `cosh² − sinh² = 1`. -/
theorem hasDerivAt_fc {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (fc c) (c ^ 2 - fc c t ^ 2) t := by
  have hct : 0 < c * t := by positivity
  have hs : sinh (c * t) ≠ 0 := ne_of_gt (sinh_pos_of_pos hct)
  have hlin : HasDerivAt (fun s : ℝ => c * s) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  have hnum : HasDerivAt (fun s : ℝ => c * cosh (c * s)) (c * (sinh (c * t) * c)) t :=
    ((Real.hasDerivAt_cosh (c * t)).comp t hlin).const_mul c
  have hden : HasDerivAt (fun s : ℝ => sinh (c * s)) (cosh (c * t) * c) t :=
    (Real.hasDerivAt_sinh (c * t)).comp t hlin
  have h := hnum.div hden hs
  refine h.congr_deriv ?_
  simp only [fc]
  field_simp

/-- `v' = f_A − f_B > 0` for `0 < α < 1/2`: the increasing half of the concavity lemma. -/
theorem fc_lt_fc {b c t : ℝ} (hb : 0 < b) (hbc : b < c) (ht : 0 < t) : fc b t < fc c t := by
  have hc : 0 < c := lt_trans hb hbc
  rw [fc_eq_Phifun hb, fc_eq_Phifun hc]
  refine Phifun_strictMonoOn ht (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity) ?_
  nlinarith [hb, hbc]

/-- The write-up's `v(t) = log(2α·sinh(t/2)/sinh(αt))`. -/
noncomputable def vfun (al t : ℝ) : ℝ := Real.log (2 * al * sinh (t / 2) / sinh (al * t))

/-- **`v' = f_{1/2} − f_α`.** -/
theorem hasDerivAt_vfun {al t : ℝ} (hal : 0 < al) (ht : 0 < t) :
    HasDerivAt (vfun al) (fc (1 / 2) t - fc al t) t := by
  have hs2 : (0 : ℝ) < sinh (t / 2) := sinh_pos_of_pos (by positivity)
  have hsa : (0 : ℝ) < sinh (al * t) := sinh_pos_of_pos (by positivity)
  have d1 : HasDerivAt (fun s : ℝ => sinh (s / 2)) (cosh (t / 2) * (1 / 2)) t := by
    have hlin : HasDerivAt (fun s : ℝ => s / 2) (1 / 2 : ℝ) t := by
      simpa using (hasDerivAt_id t).div_const 2
    exact (Real.hasDerivAt_sinh (t / 2)).comp t hlin
  have d2 : HasDerivAt (fun s : ℝ => sinh (al * s)) (cosh (al * t) * al) t := by
    have hlin : HasDerivAt (fun s : ℝ => al * s) al t := by
      simpa using (hasDerivAt_id t).const_mul al
    exact (Real.hasDerivAt_sinh (al * t)).comp t hlin
  have l1 := d1.log (ne_of_gt hs2)
  have l2 := d2.log (ne_of_gt hsa)
  have hF : HasDerivAt
      (fun s : ℝ => Real.log (2 * al) + Real.log (sinh (s / 2)) - Real.log (sinh (al * s)))
      (fc (1 / 2) t - fc al t) t := by
    refine (((hasDerivAt_const t (Real.log (2 * al))).add l1).sub l2).congr_deriv ?_
    have e1 : (1 / 2 : ℝ) * t = t / 2 := by ring
    simp only [fc, e1]
    field_simp
    ring
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  have hs0 : (0 : ℝ) < s := hs
  have h1 : (0 : ℝ) < sinh (s / 2) := sinh_pos_of_pos (by positivity)
  have h2 : (0 : ℝ) < sinh (al * s) := sinh_pos_of_pos (by positivity)
  rw [vfun, Real.log_div (by positivity) (ne_of_gt h2),
    Real.log_mul (by positivity) (ne_of_gt h1)]

/-- **`v'' = κ/4 − (f_A + f_B)·v'` with `κ/4 = 1/4 − α²`.** -/
theorem hasDerivAt_vp {al t : ℝ} (hal : 0 < al) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => fc (1 / 2) s - fc al s)
      ((1 / 4 - al ^ 2) - (fc (1 / 2) t + fc al t) * (fc (1 / 2) t - fc al t)) t := by
  refine (((hasDerivAt_fc (by norm_num) ht).sub (hasDerivAt_fc hal ht))).congr_deriv ?_
  ring

/-- **The substitution, `T = v'·W`.**  Pure algebra once `v''` is in hand — which is the whole
point: the write-up's `T` is not a new object, it is `v'` times the quantity the concavity
lemma bounds. -/
theorem T_eq (al t p C2 : ℝ) :
    ((1 / 4 - al ^ 2) - (fc (1 / 2) t + fc al t) * (fc (1 / 2) t - fc al t))
        + p * (fc (1 / 2) t - fc al t) ^ 2
        + 2 * C2 * (fc (1 / 2) t - fc al t) - (1 / 4 - al ^ 2)
      = (fc (1 / 2) t - fc al t)
          * ((p - 1) * fc (1 / 2) t - (p + 1) * fc al t + 2 * C2) := by
  ring

/-- **`T < 0`.**  `v' > 0` by the increasing half of the concavity lemma, `W < 0` by
`W_neg_Phifun`; the substitution multiplies them. -/
theorem T_neg {al t r C : ℝ} (hal : 0 < al) (hal2 : al < 1 / 2) (ht : 0 < t) (hC : 0 < C)
    (hne : C ^ 2 ≠ (1 / 2 : ℝ) ^ 2) (hr1 : 1 < r) (hr2 : r < 2)
    (hcomb : al ^ 2 = (2 / (r + 1)) * C ^ 2 + (1 - 2 / (r + 1)) * (1 / 2 : ℝ) ^ 2) :
    ((1 / 4 - al ^ 2) - (fc (1 / 2) t + fc al t) * (fc (1 / 2) t - fc al t))
        + r * (fc (1 / 2) t - fc al t) ^ 2
        + 2 * fc C t * (fc (1 / 2) t - fc al t) - (1 / 4 - al ^ 2) < 0 := by
  have hvp : 0 < fc (1 / 2) t - fc al t := by
    have := fc_lt_fc hal hal2 ht
    linarith
  have hW : (r - 1) * fc (1 / 2) t - (r + 1) * fc al t + 2 * fc C t < 0 := by
    have hA : ((1 / 2 : ℝ)) ^ 2 ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; norm_num
    have hCm : (C : ℝ) ^ 2 ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; positivity
    have h := W_neg_Phifun ht hA hCm hne hr1 hr2 hcomb
    rw [fc_eq_Phifun (by norm_num : (0:ℝ) < 1 / 2), fc_eq_Phifun hal, fc_eq_Phifun hC]
    exact h
  rw [T_eq al t r (fc C t)]
  exact mul_neg_of_pos_of_neg hvp hW

/-- **`T < 0` on the other branch, `p = -r`.**  The identical argument with `A²` and `B²`
exchanged: `convex_minus` makes `A²` the interpolated point, and `W_neg_Phifun` is stated for an
arbitrary convex combination, so one lemma covers both branches. -/
theorem T_neg_minus {al t r C : ℝ} (hal : 0 < al) (hal2 : al < 1 / 2) (ht : 0 < t) (hC : 0 < C)
    (hne : C ^ 2 ≠ al ^ 2) (hr1 : 1 < r) (hr2 : r < 2)
    (hcomb : (1 / 2 : ℝ) ^ 2 = (2 / (r + 1)) * C ^ 2 + (1 - 2 / (r + 1)) * al ^ 2) :
    ((1 / 4 - al ^ 2) - (fc (1 / 2) t + fc al t) * (fc (1 / 2) t - fc al t))
        + (-r) * (fc (1 / 2) t - fc al t) ^ 2
        + 2 * fc C t * (fc (1 / 2) t - fc al t) - (1 / 4 - al ^ 2) < 0 := by
  have hvp : 0 < fc (1 / 2) t - fc al t := by
    have := fc_lt_fc hal hal2 ht
    linarith
  have hW : (-r - 1) * fc (1 / 2) t - (-r + 1) * fc al t + 2 * fc C t < 0 := by
    have hB : (al : ℝ) ^ 2 ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; positivity
    have hCm : (C : ℝ) ^ 2 ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; positivity
    have h := W_neg_Phifun ht hB hCm hne hr1 hr2 hcomb
    rw [fc_eq_Phifun (by norm_num : (0:ℝ) < 1 / 2), fc_eq_Phifun hal, fc_eq_Phifun hC]
    linarith [h]
  rw [T_eq al t (-r) (fc C t)]
  exact mul_neg_of_pos_of_neg hvp hW

end Transfer

/-! ### The ODE `h'' = s·h' + p·h·T`, and the sign of `p·h·T`

The analytic core of the last remaining step.  In the write-up's variables
`H(a,b) = a^s·h(t)` with `t = log(b/a)` and `s = p + q`,

    `h(t) = e^{st/2}·2sinh(qt/2)·e^{pv(t)}`,   `H_ab = −(a^s/(ab))·p·h·T`,

so the sign of the mixed partial IS the sign of `p·h·T`, and that sign is what the rectangle
increment consumes.  Both halves are here.

**`hasDerivAt_hLd` is the ODE**, and the whole of the parameter relation `κ = p + 2q` is spent
in one place: writing `h = e^u·S` with `u = st/2 + pv` and `S = 2sinh(qt/2)`,

    `h'' − s·h' = e^u[ S·(p²v'² − s²/4 + p·v'' + q²/4) + 2p·v'·S' ]`,

and substituting `v'' = κ/4 − (f_A+f_B)v'` makes the constant bracket
`(q² − s² + pκ)/4` vanish **identically** — it is `(q² − (p+q)² + p(p+2q))/4 = 0`.  That is
the only appearance of `α` or of the relation; everything else is the product rule and
`S'' = (q²/4)·S`.  It is also why `Tval` carries no `κ/4`: the term cancels against the one in
the write-up's definition of `T`, which `Tval_eq` records.

**`phT_pos` is the sign.**  `h` has the sign of `q` (the exponential is positive and
`sinh(qt/2)` carries the sign), `pq < 0` on both parameter branches, and `T < 0` — so `p·h < 0`
and `p·h·T > 0`, hence `H_ab < 0`.

`fc_neg` (`f_c` is even in `c`) is what lets the `p = +r` branch, where `q < 0`, use lemmas
stated for a positive half-parameter; `Tval_neg` and `Tval_neg_minus` are the two branches.

**What is still missing**: only the change of variables and the two monotonicity calls —
`H(a,b) = a^s·h(log(b/a))`, the mixed partial in the `(a,b)` coordinates, and then
`φ(u) = H(u,b) − H(u,c)` strictly decreasing on `[a,c]` because `v ↦ H_a(u,v)` is strictly
decreasing on `[c,b]`.  No Fubini and no integral: the write-up's double integral is a
composition of two one-variable monotonicity statements. -/

section Ode

open Set

/-! ### The ODE `h'' − s·h' = p·h·T`

The analytic core of the rectangle increment.  In the write-up's variables `H(a,b) = a^s·h(t)`
with `t = log(b/a)`, `s = p + q`, and

    `h(t) = e^{st/2}·2sinh(qt/2)·e^{pv(t)}`,

and `H_ab = −(a^s/(ab))·p·h·T`, so the sign of the mixed partial is the sign of `p·h·T`.
-/

/-- `u(t) = st/2 + p·v(t)`, the exponent of `h`. -/
noncomputable def uexp (al p q t : ℝ) : ℝ := (p + q) * t / 2 + p * vfun al t

/-- `S(t) = 2 sinh(qt/2)`, the factor of `h` carrying the sign of `q`. -/
noncomputable def sfac (q t : ℝ) : ℝ := 2 * sinh (q / 2 * t)

/-- `h(t) = e^{u(t)}·S(t)`. -/
noncomputable def hL (al p q t : ℝ) : ℝ := Real.exp (uexp al p q t) * sfac q t

/-- `h'(t)`, written out. -/
noncomputable def hLd (al p q t : ℝ) : ℝ :=
  Real.exp (uexp al p q t)
    * (((p + q) / 2 + p * (fc (1 / 2) t - fc al t)) * sfac q t + q * cosh (q / 2 * t))

/-- The write-up's `T`, after `v'' = κ/4 − (f_A+f_B)v'` has been substituted: the `κ/4` cancels
against the `−κ/4` in `T`'s definition, so `T` is homogeneous of degree one in `v'`. -/
noncomputable def Tval (al p q t : ℝ) : ℝ :=
  p * (fc (1 / 2) t - fc al t) ^ 2 - (fc (1 / 2) t + fc al t) * (fc (1 / 2) t - fc al t)
    + 2 * fc (q / 2) t * (fc (1 / 2) t - fc al t)

/-- `f_c` is even in `c`, which is what lets `q < 0` use the `q > 0` lemmas. -/
theorem fc_neg (c t : ℝ) : fc (-c) t = fc c t := by
  have h : (-c) * t = -(c * t) := by ring
  simp only [fc, h, Real.cosh_neg, Real.sinh_neg, neg_mul, neg_div_neg_eq]

theorem hasDerivAt_uexp {al p q t : ℝ} (hal : 0 < al) (ht : 0 < t) :
    HasDerivAt (uexp al p q) ((p + q) / 2 + p * (fc (1 / 2) t - fc al t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (p + q) * s / 2) ((p + q) / 2) t := by
    simpa using ((hasDerivAt_id t).const_mul (p + q)).div_const 2
  have h2 := (hasDerivAt_vfun hal ht).const_mul p
  exact h1.add h2

theorem hasDerivAt_sfac (q t : ℝ) : HasDerivAt (sfac q) (q * cosh (q / 2 * t)) t := by
  have hlin : HasDerivAt (fun s : ℝ => q / 2 * s) (q / 2) t := by
    simpa using (hasDerivAt_id t).const_mul (q / 2)
  have h := ((Real.hasDerivAt_sinh (q / 2 * t)).comp t hlin).const_mul (2 : ℝ)
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_hL {al p q t : ℝ} (hal : 0 < al) (ht : 0 < t) :
    HasDerivAt (hL al p q) (hLd al p q t) t := by
  have h := ((hasDerivAt_uexp (p := p) (q := q) hal ht).exp).mul (hasDerivAt_sfac q t)
  refine h.congr_deriv ?_
  simp only [hLd, sfac]
  ring

/-- **The ODE.**  `h'' = s·h' + p·h·T`.

The constant term is where the parameter relation `κ = p + 2q` is spent: the bracket
`(q² − s² + pκ)/4` vanishes identically, and it is the ONLY place either `α` or the relation
appears.  Everything else is the product rule and `S'' = (q²/4)·S`. -/
theorem hasDerivAt_hLd {al p q t : ℝ} (hal : 0 < al) (ht : 0 < t) (hq : q ≠ 0)
    (hk : p + 2 * q = 1 - 4 * al ^ 2) :
    HasDerivAt (hLd al p q)
      ((p + q) * hLd al p q t + p * hL al p q t * Tval al p q t) t := by
  have hqt : q / 2 * t ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact hq (by linarith [h1])
    · exact (ne_of_gt ht) h2
  have hsne : sinh (q / 2 * t) ≠ 0 := by
    intro h
    exact hqt (Real.sinh_eq_zero.mp h)
  -- the bracket `B` and its derivative
  have hB : HasDerivAt
      (fun s : ℝ => ((p + q) / 2 + p * (fc (1 / 2) s - fc al s)) * sfac q s
        + q * cosh (q / 2 * s))
      ((p * ((1 / 4 - al ^ 2) - (fc (1 / 2) t + fc al t) * (fc (1 / 2) t - fc al t)))
          * sfac q t
        + ((p + q) / 2 + p * (fc (1 / 2) t - fc al t)) * (q * cosh (q / 2 * t))
        + q * (sinh (q / 2 * t) * (q / 2))) t := by
    have d1 : HasDerivAt (fun s : ℝ => (p + q) / 2 + p * (fc (1 / 2) s - fc al s))
        (p * ((1 / 4 - al ^ 2) - (fc (1 / 2) t + fc al t) * (fc (1 / 2) t - fc al t))) t := by
      have h2 := (hasDerivAt_const t ((p + q) / 2)).add ((hasDerivAt_vp hal ht).const_mul p)
      refine h2.congr_deriv ?_
      ring
    have d2 := hasDerivAt_sfac q t
    have hlin : HasDerivAt (fun s : ℝ => q / 2 * s) (q / 2) t := by
      simpa using (hasDerivAt_id t).const_mul (q / 2)
    have d3 : HasDerivAt (fun s : ℝ => q * cosh (q / 2 * s)) (q * (sinh (q / 2 * t) * (q / 2))) t :=
      ((Real.hasDerivAt_cosh (q / 2 * t)).comp t hlin).const_mul q
    exact (d1.mul d2).add d3
  have h := ((hasDerivAt_uexp (p := p) (q := q) hal ht).exp).mul hB
  refine h.congr_deriv ?_
  have hkap : (1 : ℝ) / 4 - al ^ 2 = (p + 2 * q) / 4 := by linarith
  simp only [hLd, hL, Tval, sfac, fc, hkap]
  field_simp
  ring

/-- `h` has the sign of `q`, so `p·h·T > 0` when `pq < 0` and `T < 0`.  This is the sign of the
mixed partial `H_ab`, and it is what the rectangle increment consumes. -/
theorem phT_pos {al p q t : ℝ} (ht : 0 < t) (hpq : p * q < 0)
    (hT : Tval al p q t < 0) : 0 < p * hL al p q t * Tval al p q t := by
  have hexp : 0 < Real.exp (uexp al p q t) := Real.exp_pos _
  have hph : p * hL al p q t < 0 := by
    rcases lt_or_gt_of_ne (fun h : q = 0 => by simp [h] at hpq) with hqn | hqp
    · have hp : 0 < p := by nlinarith [hpq, hqn]
      have hs : sinh (q / 2 * t) < 0 := Real.sinh_neg_iff.mpr (by nlinarith [hqn, ht])
      have : hL al p q t < 0 := by
        simp only [hL, sfac]
        nlinarith [hexp, hs]
      nlinarith [hp, this]
    · have hp : p < 0 := by nlinarith [hpq, hqp]
      have hs : 0 < sinh (q / 2 * t) := Real.sinh_pos_iff.mpr (by positivity)
      have : 0 < hL al p q t := by
        simp only [hL, sfac]
        positivity
      nlinarith [hp, this]
  exact mul_pos_of_neg_of_neg hph hT

/-- `Tval` is the `T` of `T_neg`: the two `κ/4` terms cancel. -/
theorem Tval_eq (al p q t : ℝ) :
    Tval al p q t
      = ((1 / 4 - al ^ 2) - (fc (1 / 2) t + fc al t) * (fc (1 / 2) t - fc al t))
          + p * (fc (1 / 2) t - fc al t) ^ 2
          + 2 * fc (q / 2) t * (fc (1 / 2) t - fc al t) - (1 / 4 - al ^ 2) := by
  simp only [Tval]
  ring

/-- **`T < 0` on the `p = +r` branch**, where `q < 0`.  `fc_neg` is what lets the positive-`C`
lemma be applied to a negative half-parameter. -/
theorem Tval_neg {al t r q : ℝ} (hal : 0 < al) (hal2 : al < 1 / 2) (ht : 0 < t) (hq : q < 0)
    (hne : (q / 2) ^ 2 ≠ (1 / 2 : ℝ) ^ 2) (hr1 : 1 < r) (hr2 : r < 2)
    (hcomb : al ^ 2 = (2 / (r + 1)) * (q / 2) ^ 2 + (1 - 2 / (r + 1)) * (1 / 2 : ℝ) ^ 2) :
    Tval al r q t < 0 := by
  have hCpos : (0 : ℝ) < -(q / 2) := by linarith
  have hsq : (-(q / 2)) ^ 2 = (q / 2) ^ 2 := neg_sq _
  have h := T_neg hal hal2 ht hCpos (by rw [hsq]; exact hne) hr1 hr2 (by rw [hsq]; exact hcomb)
  rw [fc_neg] at h
  rw [Tval_eq]
  exact h

/-- **`T < 0` on the `p = −r` branch**, where `q > 0`. -/
theorem Tval_neg_minus {al t r q : ℝ} (hal : 0 < al) (hal2 : al < 1 / 2) (ht : 0 < t)
    (hq : 0 < q) (hne : (q / 2) ^ 2 ≠ al ^ 2) (hr1 : 1 < r) (hr2 : r < 2)
    (hcomb : (1 / 2 : ℝ) ^ 2 = (2 / (r + 1)) * (q / 2) ^ 2 + (1 - 2 / (r + 1)) * al ^ 2) :
    Tval al (-r) q t < 0 := by
  have h := T_neg_minus hal hal2 ht (by linarith : (0 : ℝ) < q / 2) hne hr1 hr2 hcomb
  rw [Tval_eq]
  exact h

end Ode

/-! ### The change of variables `H(a,b) = a^s·h(t)`

`Lal` is the source's mean **verbatim** — `L_α(a,b) = 2α·a^α·b^α·(b−a)/(b^{2α} − a^{2α})` — so
everything below is about the object the conjecture is about, not about a reformulation.  `Hfun`
is the write-up's `H(a,b) = (b^q − a^q)·L_α(a,b)^p`.

**`Hfun_exp` is the step where every `a` leaves the problem.**  With `b = a·e^t`,

    `L_α(a,b) = a·e^{t/2}·e^{v(t)}`   (`Lal_exp`),
    `H(a,b)    = a^{p+q}·h(t)`        (`Hfun_exp`),

so the two-variable problem becomes the one-variable `h` whose ODE is already proved.  Both
factorisations run through one small identity used twice, `e^x − 1 = e^{x/2}·2sinh(x/2)`
(`exp_sub_one_eq`) — for `b^q − a^q` and for `b − a`.  No sign condition on `p` or `q` is needed:
`Real.rpow` handles a negative exponent on a positive base, and `sinh` carries the sign.

`Hfun_eq` restates it for `0 < a < b` with `t = log(b/a)`, which is the form the rectangle
consumes, and `hasDerivAt_Hfun_fst` is `∂_a H = a^{s−1}(s·h(t) − h'(t))`.

**What remains is two steps.**  Differentiate `∂_a H` in its SECOND variable — which by the ODE is
`−a^{s−1}·p·h·T/v`, negative by `phT_pos` — and then two `strictAntiOn_of_deriv_neg` calls:
`v ↦ ∂_a H(u,v)` strictly decreasing on `[c,b]`, hence `φ(u) = H(u,b) − H(u,c)` strictly
decreasing on `[a,c]`, hence `φ(c) < φ(a)`, which with `H(c,c) = 0` is the rectangle increment
`H(a,c) + H(c,b) < H(a,b)`. -/

section ChangeOfVariables

open Set

/-! ### The change of variables `H(a,b) = a^s·h(t)`

`H(a,b) := (b^q − a^q)·L_α(a,b)^p`, and with `b = a·e^t` the whole `a`-dependence factors out as
`a^{p+q}`.  That is the write-up's `H(a,b) = a^s h(t)`, and it is what turns the mixed partial
into the one-variable ODE already proved.
-/

/-- `e^x − 1 = e^{x/2}·2sinh(x/2)`.  Used twice, for `b^q − a^q` and for `b − a`. -/
theorem exp_sub_one_eq (x : ℝ) : Real.exp x - 1 = Real.exp (x / 2) * (2 * sinh (x / 2)) := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  field_simp
  nlinarith [h1, h2]

/-- The source's mean `L_α(a,b) = 2α·a^α·b^α·(b−a)/(b^{2α} − a^{2α})`. -/
noncomputable def Lal (al a b : ℝ) : ℝ :=
  2 * al * a ^ al * b ^ al * (b - a) / (b ^ (2 * al) - a ^ (2 * al))

/-- **The change of variables for `L_α`**: with `b = a·e^t`,
`L_α(a,b) = a·e^{t/2}·e^{v(t)}`, where `v` is the write-up's `log(2α·sinh(t/2)/sinh(αt))`. -/
theorem Lal_exp {al a t : ℝ} (hal : 0 < al) (ha : 0 < a) (ht : 0 < t) :
    Lal al a (a * Real.exp t) = a * Real.exp (t / 2) * Real.exp (vfun al t) := by
  have hst : (0 : ℝ) < sinh (t / 2) := sinh_pos_of_pos (by positivity)
  have hsa : (0 : ℝ) < sinh (al * t) := sinh_pos_of_pos (by positivity)
  have hv : Real.exp (vfun al t) = 2 * al * sinh (t / 2) / sinh (al * t) := by
    rw [vfun, Real.exp_log (by positivity)]
  have h1 : (a * Real.exp t) ^ al = a ^ al * Real.exp (al * t) := by
    rw [Real.mul_rpow (le_of_lt ha) (le_of_lt (Real.exp_pos t)), ← Real.exp_mul, mul_comm t al]
  have h2 : (a * Real.exp t) ^ (2 * al) = a ^ (2 * al) * Real.exp (2 * al * t) := by
    rw [Real.mul_rpow (le_of_lt ha) (le_of_lt (Real.exp_pos t)), ← Real.exp_mul, mul_comm t (2 * al)]
  have haa : a ^ al * a ^ al = a ^ (2 * al) := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  have e1 : a * Real.exp t - a = a * (Real.exp (t / 2) * (2 * sinh (t / 2))) := by
    rw [← exp_sub_one_eq t]
    ring
  have e2 : Real.exp (2 * al * t) - 1 = Real.exp (al * t) * (2 * sinh (al * t)) := by
    have h := exp_sub_one_eq (2 * al * t)
    have hh : 2 * al * t / 2 = al * t := by ring
    rw [hh] at h
    exact h
  have hane : a ^ (2 * al) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha _)
  have heane : Real.exp (al * t) ≠ 0 := ne_of_gt (Real.exp_pos _)
  rw [Lal, h1, h2, hv, e1]
  rw [show a ^ (2 * al) * Real.exp (2 * al * t) - a ^ (2 * al)
      = a ^ (2 * al) * (Real.exp (2 * al * t) - 1) by ring, e2]
  rw [show 2 * al * a ^ al * (a ^ al * Real.exp (al * t))
      = 2 * al * (a ^ al * a ^ al) * Real.exp (al * t) by ring, haa]
  field_simp

theorem Lal_pos {al a t : ℝ} (hal : 0 < al) (ha : 0 < a) (ht : 0 < t) :
    0 < Lal al a (a * Real.exp t) := by
  rw [Lal_exp hal ha ht]
  positivity

/-- `H(a,b) = (b^q − a^q)·L_α(a,b)^p`, the write-up's `H`. -/
noncomputable def Hfun (al p q a b : ℝ) : ℝ := (b ^ q - a ^ q) * Lal al a b ^ p

/-- **The write-up's factorisation `H(a,b) = a^s·h(t)`, `s = p + q`.**  Every `a` leaves the
problem here: what is left is the one-variable `h` whose ODE is already proved. -/
theorem Hfun_exp {al p q a t : ℝ} (hal : 0 < al) (ha : 0 < a) (ht : 0 < t) :
    Hfun al p q a (a * Real.exp t) = a ^ (p + q) * hL al p q t := by
  have hL0 : (0 : ℝ) < Lal al a (a * Real.exp t) := Lal_pos hal ha ht
  have hq : (a * Real.exp t) ^ q - a ^ q
      = a ^ q * (Real.exp (q * t / 2) * (2 * sinh (q * t / 2))) := by
    rw [Real.mul_rpow (le_of_lt ha) (le_of_lt (Real.exp_pos t)), ← Real.exp_mul,
      mul_comm t q]
    rw [show a ^ q * Real.exp (q * t) - a ^ q = a ^ q * (Real.exp (q * t) - 1) by ring,
      exp_sub_one_eq (q * t)]
  have hp : Lal al a (a * Real.exp t) ^ p
      = a ^ p * Real.exp (p * t / 2 + p * vfun al t) := by
    rw [Lal_exp hal ha ht]
    rw [show a * Real.exp (t / 2) * Real.exp (vfun al t)
        = a * (Real.exp (t / 2) * Real.exp (vfun al t)) by ring]
    rw [Real.mul_rpow (le_of_lt ha) (by positivity), ← Real.exp_add, ← Real.exp_mul]
    congr 1
    ring
  rw [Hfun, hq, hp, hL, uexp, sfac]
  rw [show a ^ q * (Real.exp (q * t / 2) * (2 * sinh (q * t / 2)))
        * (a ^ p * Real.exp (p * t / 2 + p * vfun al t))
      = (a ^ q * a ^ p) * (Real.exp (q * t / 2) * Real.exp (p * t / 2 + p * vfun al t))
        * (2 * sinh (q * t / 2)) by ring]
  rw [← Real.rpow_add ha, ← Real.exp_add,
    show q + p = p + q from by ring,
    show q * t / 2 + (p * t / 2 + p * vfun al t) = (p + q) * t / 2 + p * vfun al t from by ring,
    show q / 2 * t = q * t / 2 from by ring]
  ring

/-- `H(a,b) = a^s·h(log(b/a))`, in the `0 < a < b` form the rectangle uses. -/
theorem Hfun_eq {al p q a b : ℝ} (hal : 0 < al) (ha : 0 < a) (hab : a < b) :
    Hfun al p q a b = a ^ (p + q) * hL al p q (Real.log (b / a)) := by
  have hb : (0 : ℝ) < b := lt_trans ha hab
  have hba1 : (1 : ℝ) < b / a := by
    rw [lt_div_iff₀ ha]
    linarith
  have ht : 0 < Real.log (b / a) := Real.log_pos hba1
  have hba : b = a * Real.exp (Real.log (b / a)) := by
    rw [Real.exp_log (by positivity)]
    field_simp
  have key := Hfun_exp (al := al) (p := p) (q := q) (a := a) (t := Real.log (b / a)) hal ha ht
  rw [← hba] at key
  exact key

/-- `∂_a H(a,b) = a^{s−1}·(s·h(t) − h'(t))`, the partial the rectangle differentiates in its
second variable. -/
theorem hasDerivAt_Hfun_fst {al p q a b : ℝ} (hal : 0 < al) (ha : 0 < a) (hab : a < b) :
    HasDerivAt (fun u => Hfun al p q u b)
      (a ^ (p + q - 1) * ((p + q) * hL al p q (Real.log (b / a))
        - hLd al p q (Real.log (b / a)))) a := by
  have hb : (0 : ℝ) < b := lt_trans ha hab
  have ht : 0 < Real.log (b / a) := Real.log_pos (by rw [lt_div_iff₀ ha]; linarith)
  have hlog : HasDerivAt (fun u : ℝ => Real.log (b / u)) (-a⁻¹) a := by
    have h1 : HasDerivAt (fun u : ℝ => Real.log b - Real.log u) (-a⁻¹) a :=
      ((hasDerivAt_const a (Real.log b)).sub (Real.hasDerivAt_log (ne_of_gt ha))).congr_deriv
        (by ring)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ha] with u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [Real.log_div (ne_of_gt hb) (ne_of_gt hu0)]
  have hcomp : HasDerivAt (fun u : ℝ => hL al p q (Real.log (b / u)))
      (hLd al p q (Real.log (b / a)) * (-a⁻¹)) a := by
    simpa [Function.comp_def] using
      (hasDerivAt_hL (al := al) (p := p) (q := q) hal ht).comp a hlog
  have hpow : HasDerivAt (fun u : ℝ => u ^ (p + q)) ((p + q) * a ^ (p + q - 1)) a :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ha))
  have hFeq : HasDerivAt (fun u : ℝ => Hfun al p q u b)
      ((p + q) * a ^ (p + q - 1) * hL al p q (Real.log (b / a))
        + a ^ (p + q) * (hLd al p q (Real.log (b / a)) * (-a⁻¹))) a := by
    refine (hpow.mul hcomp).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ha hab] with u hu
    exact Hfun_eq hal hu.1 hu.2
  refine hFeq.congr_deriv ?_
  have hsub : a ^ (p + q - 1) = a ^ (p + q) * a⁻¹ := by
    rw [Real.rpow_sub ha, Real.rpow_one]
    field_simp
  rw [hsub]
  ring

end ChangeOfVariables

/-! ### The corner: `h` is right-continuous at `0`

The previous section's change of variables exposed an obstruction the plan had not recorded.
The rectangle increment compares `φ(u) = H(u,b) − H(u,c)` at `u = a` and at `u = c`, and at
`u = c` the second term is `H(c,c)`, which sits at `t = log(c/c) = 0`.  The VALUE there is
already right by computation — `sfac q 0 = 2sinh 0 = 0`, so `hL_zero` gives `h(0) = 0 = H(c,c)`
— but `h` is NOT differentiable at `0`, because `v(t) = log(2α·sinh(t/2)/sinh(αt))` needs
`t > 0`.  So the endpoint needs CONTINUITY rather than a derivative, and that is one limit.

**The limit is two copies of `sinh x / x → 1`.**  For `t ≠ 0`,

    `2α·sinh(t/2)/sinh(αt) = (sinh(t/2)/(t/2)) / (sinh(αt)/(αt))`,

so the `2α` cancels between the two factors and the ratio tends to `1`; hence `v → 0`,
`e^{u} → 1`, and `h = e^{u}·S → 1·0 = 0`.  `tendsto_sinh_div_self` is the slope of `sinh` at
`0` read through `hasDerivAt_iff_tendsto_slope` — Mathlib has no `sinh x / x` limit of its own
(grepped), and the derivative is the cheapest route to it.

`continuousWithinAt_hL_zero` is the closed obstruction, in the `Ici 0` form the rectangle's
`ContinuousOn` obligation consumes.

**What remains is the two monotonicity calls themselves**: `v ↦ ∂_a H(u,v)` strictly decreasing
on `[c,b]` (its derivative is `−a^{s−1}·p·h·T/v`, negative by `phT_pos`), hence
`φ(u) = H(u,b) − H(u,c)` strictly decreasing on `[a,c]`, hence `φ(c) < φ(a)`, which with
`H(c,c) = 0` is the rectangle increment.  Then the `B_q` split and the `p`-th root give
`L_α < R`. -/

section Corner

open Set Filter Topology

/-! ### The corner: `h` is right-continuous at `0`

The rectangle increment compares `φ(u) = H(u,b) − H(u,c)` at `u = a` and at `u = c`, and at
`u = c` the second term is `H(c,c)`, sitting at `t = log(c/c) = 0`.  The VALUE is already right
by computation — `sfac q 0 = 2sinh 0 = 0`, so `hL … 0 = 0` — but `h` is not differentiable
there, because `v(t) = log(2α·sinh(t/2)/sinh(αt))` needs `t > 0`.  So the endpoint needs
CONTINUITY, and that is the single limit `2α·sinh(t/2)/sinh(αt) → 1`, which is two copies of
`sinh x / x → 1` cancelling the `2α`.
-/

/-- `sinh x / x → 1` as `x → 0`: it is the slope of `sinh` at `0`.  Mathlib has no lemma of its
own for this ratio, and the derivative is the cheapest route to it. -/
theorem tendsto_sinh_div_self :
    Tendsto (fun x : ℝ => sinh x / x) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have h := Real.hasDerivAt_sinh 0
  rw [hasDerivAt_iff_tendsto_slope, Real.cosh_zero] at h
  refine Filter.Tendsto.congr (fun x => ?_) h
  rw [slope_def_field]
  simp [Real.sinh_zero]

theorem tendsto_half_nhdsWithin :
    Tendsto (fun t : ℝ => t / 2) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hc : Continuous (fun t : ℝ => t / 2) := continuous_id.div_const 2
    have h : Tendsto (fun t : ℝ => t / 2) (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) / 2)) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    exact ne_of_gt (by positivity)

theorem tendsto_mul_nhdsWithin {al : ℝ} (hal : 0 < al) :
    Tendsto (fun t : ℝ => al * t) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hc : Continuous (fun t : ℝ => al * t) := continuous_const.mul continuous_id
    have h : Tendsto (fun t : ℝ => al * t) (𝓝[>] (0 : ℝ)) (𝓝 (al * (0 : ℝ))) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    exact ne_of_gt (by positivity)

/-- **`v(t) → 0` as `t → 0⁺`.**  The `2α` cancels between the two `sinh x / x` factors:
`2α·sinh(t/2)/sinh(αt) = (sinh(t/2)/(t/2)) / (sinh(αt)/(αt))`. -/
theorem tendsto_vfun_zero {al : ℝ} (hal : 0 < al) :
    Tendsto (vfun al) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hA : Tendsto (fun t : ℝ => sinh (t / 2) / (t / 2)) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    tendsto_sinh_div_self.comp tendsto_half_nhdsWithin
  have hB : Tendsto (fun t : ℝ => sinh (al * t) / (al * t)) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    tendsto_sinh_div_self.comp (tendsto_mul_nhdsWithin hal)
  have hdiv : Tendsto (fun t : ℝ => sinh (t / 2) / (t / 2) / (sinh (al * t) / (al * t)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := hA.div hB one_ne_zero
    simpa [Pi.div_def] using h
  have hlog : Tendsto
      (fun t : ℝ => Real.log (sinh (t / 2) / (t / 2) / (sinh (al * t) / (al * t))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hdiv
    simpa [Real.log_one, Function.comp_def] using h
  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have h1 : sinh (al * t) ≠ 0 := ne_of_gt (sinh_pos_of_pos (by positivity))
  have h2 : sinh (t / 2) ≠ 0 := ne_of_gt (sinh_pos_of_pos (by positivity))
  have h3 : (t : ℝ) ≠ 0 := ne_of_gt ht0
  have h4 : (al : ℝ) ≠ 0 := ne_of_gt hal
  rw [vfun]
  congr 1
  field_simp

/-- The corner VALUE, by computation: `sfac q 0 = 2sinh 0 = 0`. -/
theorem hL_zero (al p q : ℝ) : hL al p q 0 = 0 := by
  simp [hL, sfac]

/-- **`h(t) → 0` as `t → 0⁺`.** -/
theorem tendsto_hL_zero {al p q : ℝ} (hal : 0 < al) :
    Tendsto (hL al p q) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hu : Tendsto (uexp al p q) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (p + q) * t / 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous (fun t : ℝ => (p + q) * t / 2) :=
        (continuous_const.mul continuous_id).div_const 2
      have h : Tendsto (fun t : ℝ => (p + q) * t / 2) (𝓝[>] (0 : ℝ))
          (𝓝 ((p + q) * (0 : ℝ) / 2)) := (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using h
    have h2 : Tendsto (fun t : ℝ => p * vfun al t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (tendsto_vfun_zero hal).const_mul p
      simpa using h
    have h3 : Tendsto (fun t : ℝ => (p + q) * t / 2 + p * vfun al t) (𝓝[>] (0 : ℝ))
        (𝓝 0) := by simpa using h1.add h2
    exact Filter.Tendsto.congr (fun t => rfl) h3
  have hexp : Tendsto (fun t : ℝ => Real.exp (uexp al p q t)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := (Real.continuous_exp.tendsto 0).comp hu
    simpa [Function.comp_def] using h
  have hs : Tendsto (sfac q) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous (sfac q) := by
      show Continuous (fun t : ℝ => 2 * sinh (q / 2 * t))
      exact continuous_const.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))
    have h : Tendsto (sfac q) (𝓝[>] (0 : ℝ)) (𝓝 (sfac q 0)) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa [sfac] using h
  have h0 : Tendsto (fun t : ℝ => Real.exp (uexp al p q t) * sfac q t) (𝓝[>] (0 : ℝ))
      (𝓝 0) := by simpa using hexp.mul hs
  exact Filter.Tendsto.congr (fun t => rfl) h0

/-- **The corner is closed**: `h` is right-continuous at `0`, in the `Ici 0` form a
`ContinuousOn` obligation consumes. -/
theorem continuousWithinAt_hL_zero {al p q : ℝ} (hal : 0 < al) :
    ContinuousWithinAt (hL al p q) (Ici (0 : ℝ)) 0 := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  unfold ContinuousWithinAt
  rw [hL_zero]
  exact tendsto_hL_zero hal

end Corner

/-! ### The rectangle increment, with no integral anywhere

The write-up writes this step as

    `H(a,c) + H(c,b) − H(a,b) = ∫_a^c ∫_c^b H_ab(u,v) dv du < 0`,

and a formalisation that took that literally would owe Fubini, integrability and a sign under
the integral.  **It is a composition of two one-variable monotonicity statements**, and that is
all that is used here:

* `HA_strictAntiOn` — `v ↦ ∂_a H(u,v)` is strictly decreasing on `(u,∞)`, because its
  derivative is `−u^{s−1}·p·h·T/v` (`hasDerivAt_HA_snd`, the ODE) and `p·h·T > 0`
  (`phT_pos`).  So `∂_a H(u,b) < ∂_a H(u,c)` whenever `c < b`;
* hence `φ(u) = H(u,b) − H(u,c)` has negative derivative on `(a,c)` and is strictly decreasing
  on `[a,c]`, so `φ(c) < φ(a)`, which with `H(c,c) = 0` is the increment.

**The closed interval is why the previous pass's corner lemma exists.**  `φ` must be continuous
at `u = c`, where the second term is `H(c,c)` and the chart degenerates;
`continuousOn_Hfun_fst` carries `continuousWithinAt_hL_zero` through `u ↦ log(c/u)` and
`u ↦ u^s`, and `Hfun_eq_le` extends the change of variables ONTO the diagonal, where both sides
are `0`.  Without those the monotonicity would hold only on the open interval and the endpoint
comparison — which is the whole statement — would be unavailable.

**What remains is the write-up's last paragraph, and it is algebra rather than analysis**: put
`c = B_q(a,b)`, so `c^q − a^q = b^q − c^q = (b^q − a^q)/2`; divide the increment by
`b^q − a^q`, whose sign is that of `q`; and take the `p`-th root, whose direction reverses
because `pq < 0`.  Both parameter branches then give `L_α < R(B_p, L_α, B_q)`. -/

section Rectangle

open Set Filter Topology

/-! ### The rectangle increment

`H(a,c) + H(c,b) < H(a,b)` for `a < c < b`, which is the write-up's
`∫_a^c ∫_c^b H_ab < 0` without any integral: the double integral is a composition of two
one-variable monotonicity statements.
-/

/-- The change of variables, extended to the diagonal.  At `a = b` both sides are `0`:
`b^q − a^q` vanishes on the left and `h(log 1) = h(0) = 0` on the right. -/
theorem Hfun_eq_le {al p q a b : ℝ} (hal : 0 < al) (ha : 0 < a) (hab : a ≤ b) :
    Hfun al p q a b = a ^ (p + q) * hL al p q (Real.log (b / a)) := by
  rcases eq_or_lt_of_le hab with rfl | h
  · simp [Hfun, div_self (ne_of_gt ha), Real.log_one, hL_zero]
  · exact Hfun_eq hal ha h

/-- `h` is continuous on `[0,∞)`: at `0` by the corner, elsewhere by its derivative. -/
theorem continuousOn_hL {al p q : ℝ} (hal : 0 < al) :
    ContinuousOn (hL al p q) (Ici (0 : ℝ)) := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h]
    exact continuousWithinAt_hL_zero hal
  · exact ((hasDerivAt_hL hal h).continuousAt).continuousWithinAt

/-- `u ↦ H(u,b)` is continuous on `(0,b]` — INCLUDING the diagonal endpoint `u = b`, which is
where the corner lemma is spent. -/
theorem continuousOn_Hfun_fst {al p q b : ℝ} (hal : 0 < al) (hb : 0 < b) :
    ContinuousOn (fun u => Hfun al p q u b) (Ioc 0 b) := by
  have hEq : ∀ u ∈ Ioc (0 : ℝ) b, Hfun al p q u b = u ^ (p + q) * hL al p q (Real.log (b / u)) :=
    fun u hu => Hfun_eq_le hal hu.1 hu.2
  refine ContinuousOn.congr ?_ hEq
  have h1 : ContinuousOn (fun u : ℝ => u ^ (p + q)) (Ioc 0 b) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu.1
    exact ((Real.hasDerivAt_rpow_const
      (p := p + q) (Or.inl (ne_of_gt hu0))).continuousAt).continuousWithinAt
  have h2 : ContinuousOn (fun u : ℝ => Real.log (b / u)) (Ioc 0 b) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hdiv : ContinuousAt (fun w : ℝ => b / w) u :=
      (continuous_const.continuousAt).div continuousAt_id (ne_of_gt hu0)
    have hne : b / u ≠ 0 := ne_of_gt (by positivity)
    exact ((Real.continuousAt_log hne).comp hdiv).continuousWithinAt
  have hmap : MapsTo (fun u : ℝ => Real.log (b / u)) (Ioc 0 b) (Ici (0 : ℝ)) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have h1le : (1 : ℝ) ≤ b / u := (one_le_div hu0).mpr hu.2
    exact Real.log_nonneg h1le
  exact h1.mul ((continuousOn_hL hal).comp h2 hmap)

/-- `∂_a H(a,v)`, read as a function of the SECOND variable. -/
noncomputable def HA (al p q a v : ℝ) : ℝ :=
  a ^ (p + q - 1) * ((p + q) * hL al p q (Real.log (v / a)) - hLd al p q (Real.log (v / a)))

/-- `∂_v ∂_a H = −a^{s−1}·p·h·T/v`.  The ODE is where `h''` disappears. -/
theorem hasDerivAt_HA_snd {al p q a v : ℝ} (hal : 0 < al) (ha : 0 < a) (hav : a < v)
    (hq : q ≠ 0) (hk : p + 2 * q = 1 - 4 * al ^ 2) :
    HasDerivAt (HA al p q a)
      (-(a ^ (p + q - 1)
        * (p * hL al p q (Real.log (v / a)) * Tval al p q (Real.log (v / a))) / v)) v := by
  have hv : (0 : ℝ) < v := lt_trans ha hav
  have ht : 0 < Real.log (v / a) := Real.log_pos (by rw [lt_div_iff₀ ha]; linarith)
  have hlog : HasDerivAt (fun w : ℝ => Real.log (w / a)) v⁻¹ v := by
    have h1 : HasDerivAt (fun w : ℝ => Real.log w - Real.log a) v⁻¹ v :=
      ((Real.hasDerivAt_log (ne_of_gt hv)).sub (hasDerivAt_const v (Real.log a))).congr_deriv
        (by ring)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hv] with w hw
    have hw0 : (0 : ℝ) < w := hw
    rw [Real.log_div (ne_of_gt hw0) (ne_of_gt ha)]
  have hhL : HasDerivAt (fun w : ℝ => hL al p q (Real.log (w / a)))
      (hLd al p q (Real.log (v / a)) * v⁻¹) v := by
    simpa [Function.comp_def] using
      (hasDerivAt_hL (al := al) (p := p) (q := q) hal ht).comp v hlog
  have hhLd : HasDerivAt (fun w : ℝ => hLd al p q (Real.log (w / a)))
      (((p + q) * hLd al p q (Real.log (v / a))
        + p * hL al p q (Real.log (v / a)) * Tval al p q (Real.log (v / a))) * v⁻¹) v := by
    simpa [Function.comp_def] using
      (hasDerivAt_hLd (al := al) (p := p) (q := q) hal ht hq hk).comp v hlog
  have h := ((hhL.const_mul (p + q)).sub hhLd).const_mul (a ^ (p + q - 1))
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **`v ↦ ∂_a H(u,v)` is strictly decreasing** — the first monotonicity call, and the place
`phT_pos` is consumed. -/
theorem HA_strictAntiOn {al p q a : ℝ} (hal : 0 < al) (ha : 0 < a) (hq : q ≠ 0)
    (hk : p + 2 * q = 1 - 4 * al ^ 2) (hpq : p * q < 0)
    (hT : ∀ t : ℝ, 0 < t → Tval al p q t < 0) :
    StrictAntiOn (HA al p q a) (Ioi a) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi a) ?_ ?_
  · intro v hv
    have hav : a < v := hv
    exact ((hasDerivAt_HA_snd hal ha hav hq hk).continuousAt).continuousWithinAt
  · intro v hv
    rw [interior_Ioi] at hv
    have hav : a < v := hv
    have hv0 : (0 : ℝ) < v := lt_trans ha hav
    have ht : 0 < Real.log (v / a) := Real.log_pos (by rw [lt_div_iff₀ ha]; linarith)
    rw [(hasDerivAt_HA_snd hal ha hav hq hk).deriv]
    have hpos := phT_pos ht hpq (hT _ ht)
    have hpow : (0 : ℝ) < a ^ (p + q - 1) := Real.rpow_pos_of_pos ha _
    have hfrac : 0 < a ^ (p + q - 1)
        * (p * hL al p q (Real.log (v / a)) * Tval al p q (Real.log (v / a))) / v :=
      div_pos (mul_pos hpow hpos) hv0
    linarith

/-- **The rectangle increment.**  `φ(u) = H(u,b) − H(u,c)` is strictly decreasing on `[a,c]`
because `v ↦ ∂_a H(u,v)` is strictly decreasing on `[c,b]`, and `H(c,c) = 0`. -/
theorem rectangle {al p q a c b : ℝ} (hal : 0 < al) (ha : 0 < a) (hac : a < c) (hcb : c < b)
    (hq : q ≠ 0) (hk : p + 2 * q = 1 - 4 * al ^ 2) (hpq : p * q < 0)
    (hT : ∀ t : ℝ, 0 < t → Tval al p q t < 0) :
    Hfun al p q a c + Hfun al p q c b < Hfun al p q a b := by
  have hc0 : (0 : ℝ) < c := lt_trans ha hac
  have hb0 : (0 : ℝ) < b := lt_trans hc0 hcb
  have hcc : Hfun al p q c c = 0 := by simp [Hfun]
  have hphiCont : ContinuousOn (fun u => Hfun al p q u b - Hfun al p q u c) (Icc a c) := by
    have hsub1 : Icc a c ⊆ Ioc (0 : ℝ) b := fun u hu =>
      ⟨lt_of_lt_of_le ha hu.1, le_trans hu.2 (le_of_lt hcb)⟩
    have hsub2 : Icc a c ⊆ Ioc (0 : ℝ) c := fun u hu => ⟨lt_of_lt_of_le ha hu.1, hu.2⟩
    exact ((continuousOn_Hfun_fst hal hb0).mono hsub1).sub
      ((continuousOn_Hfun_fst hal hc0).mono hsub2)
  have hanti : StrictAntiOn (fun u => Hfun al p q u b - Hfun al p q u c) (Icc a c) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc a c) hphiCont ?_
    intro u hu
    rw [interior_Icc] at hu
    have hu0 : (0 : ℝ) < u := lt_trans ha hu.1
    have huc : u < c := hu.2
    have hub : u < b := lt_trans huc hcb
    have hd : HasDerivAt (fun w => Hfun al p q w b - Hfun al p q w c)
        (HA al p q u b - HA al p q u c) u :=
      (hasDerivAt_Hfun_fst hal hu0 hub).sub (hasDerivAt_Hfun_fst hal hu0 huc)
    rw [hd.deriv]
    have hmono := HA_strictAntiOn hal hu0 hq hk hpq hT (show c ∈ Ioi u from huc)
      (show b ∈ Ioi u from hub) hcb
    linarith
  have hlt := hanti (left_mem_Icc.mpr (le_of_lt hac)) (right_mem_Icc.mpr (le_of_lt hac)) hac
  simp only [hcc, sub_zero] at hlt
  linarith

end Rectangle

/-! ### From the rectangle to the conjecture's inequality

`Bmean` is the source's power mean `B_r(a,b) = ((a^r + b^r)/2)^{1/r}` and `Rres` its resultant
mean `R(B_p, L_α, B_q)(a,b) = B_p(L_α(a, B_q(a,b)), L_α(B_q(a,b), b))`, both verbatim.

`Lal_lt_Rres` is the conjecture's inequality.  Given the rectangle increment there is no analysis
left — the whole step is `rpow` bookkeeping in three moves:

* `Bmean_rpow`: `B_r(a,b)^r = (a^r + b^r)/2`, since `(X^{1/r})^r = X`.  With `c = B_q(a,b)` this
  gives `c^q − a^q = b^q − c^q = (b^q − a^q)/2`, so the increment becomes
  `(b^q − a^q)·((X^p + Y^p)/2) < (b^q − a^q)·L^p`;
* `Bmean_lt`: the power mean is STRICTLY between its arguments, which is what licenses the
  rectangle at `a < c < b`.  It splits on the sign of `q` — for `q < 0` both `x ↦ x^q` and
  `x ↦ x^{1/q}` reverse, and the two reversals cancel;
* the division by `b^q − a^q`, whose sign is the sign of `q`, and the `p`-th root, whose
  direction reverses because `p` has the opposite sign.  **The two reversals cancel again**, so
  both parameter branches land on `L_α < R` — which is why the source can state one inequality
  for `p = ±r`.

`Real.rpow_lt_rpow_iff_of_neg` carries every negative-exponent step, in both directions.

**What remains is the parameter bookkeeping only**: derive `p ≠ 0`, `q ≠ 0`,
`p + 2q = 1 − 4α²`, `pq < 0` and `∀ t > 0, T < 0` from the source's
`r = √(1 + 16α² − 16α⁴)`, `p = ±r`, `q = (1−p)/2 − 2α²`.  The module already has
`r_bounds` (`1 < r < 2`), `param_identity`, `convex_plus`/`convex_minus` and
`Tval_neg`/`Tval_neg_minus` for exactly that. -/

section Conclusion

open Set

/-! ### From the rectangle to the conjecture's inequality

Put `c = B_q(a,b)`, so `c^q − a^q = b^q − c^q = (b^q − a^q)/2`; divide the rectangle increment by
`b^q − a^q`, whose sign is the sign of `q`; and take the `p`-th root, whose direction reverses
because `pq < 0`.  Both parameter branches give `L_α < R`.
-/

/-- `B_r(a,b) = ((a^r + b^r)/2)^{1/r}`, the source's power mean. -/
noncomputable def Bmean (r a b : ℝ) : ℝ := ((a ^ r + b ^ r) / 2) ^ (1 / r)

theorem Bmean_pos {r a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < Bmean r a b :=
  Real.rpow_pos_of_pos (by positivity) _

theorem Bmean_rpow {r a b : ℝ} (hr : r ≠ 0) (ha : 0 < a) (hb : 0 < b) :
    Bmean r a b ^ r = (a ^ r + b ^ r) / 2 := by
  have h : (0 : ℝ) < (a ^ r + b ^ r) / 2 := by positivity
  rw [Bmean, ← Real.rpow_mul (le_of_lt h), one_div_mul_cancel hr, Real.rpow_one]

/-- `L_α(a,b) > 0` for `0 < a < b`. -/
theorem Lal_pos_of_lt {al a b : ℝ} (hal : 0 < al) (ha : 0 < a) (hab : a < b) :
    0 < Lal al a b := by
  have hb : (0 : ℝ) < b := lt_trans ha hab
  have ht : 0 < Real.log (b / a) := Real.log_pos (by rw [lt_div_iff₀ ha]; linarith)
  have hba : b = a * Real.exp (Real.log (b / a)) := by
    rw [Real.exp_log (by positivity)]
    field_simp
  have h := Lal_pos hal ha ht
  rw [← hba] at h
  exact h

/-- **The power mean is strictly between its arguments**, for either sign of `q`. -/
theorem Bmean_lt {q a b : ℝ} (hq : q ≠ 0) (ha : 0 < a) (hab : a < b) :
    a < Bmean q a b ∧ Bmean q a b < b := by
  have hb : (0 : ℝ) < b := lt_trans ha hab
  have hpa : (0 : ℝ) < a ^ q := Real.rpow_pos_of_pos ha q
  have hpb : (0 : ℝ) < b ^ q := Real.rpow_pos_of_pos hb q
  have hM : (0 : ℝ) < (a ^ q + b ^ q) / 2 := by positivity
  have hia : ((a ^ q) ^ (1 / q) : ℝ) = a := by
    rw [← Real.rpow_mul (le_of_lt ha), mul_one_div_cancel hq, Real.rpow_one]
  have hib : ((b ^ q) ^ (1 / q) : ℝ) = b := by
    rw [← Real.rpow_mul (le_of_lt hb), mul_one_div_cancel hq, Real.rpow_one]
  simp only [Bmean]
  rcases lt_or_gt_of_ne hq with hqn | hqp
  · have hqi : 1 / q < 0 := div_neg_of_pos_of_neg one_pos hqn
    have hba : b ^ q < a ^ q := (Real.rpow_lt_rpow_iff_of_neg hb ha hqn).mpr hab
    refine ⟨?_, ?_⟩
    · have h := (Real.rpow_lt_rpow_iff_of_neg hpa hM hqi).mpr (by linarith)
      rw [hia] at h
      exact h
    · have h := (Real.rpow_lt_rpow_iff_of_neg hM hpb hqi).mpr (by linarith)
      rw [hib] at h
      exact h
  · have hqi : (0 : ℝ) < 1 / q := div_pos one_pos hqp
    have hba : a ^ q < b ^ q := Real.rpow_lt_rpow (le_of_lt ha) hab hqp
    refine ⟨?_, ?_⟩
    · have h := Real.rpow_lt_rpow (le_of_lt hpa)
        (by linarith : a ^ q < (a ^ q + b ^ q) / 2) hqi
      rw [hia] at h
      exact h
    · have h := Real.rpow_lt_rpow (le_of_lt hM)
        (by linarith : (a ^ q + b ^ q) / 2 < b ^ q) hqi
      rw [hib] at h
      exact h

/-- The source's resultant mean `R(B_p, L_α, B_q)(a,b)`. -/
noncomputable def Rres (al p q a b : ℝ) : ℝ :=
  Bmean p (Lal al a (Bmean q a b)) (Lal al (Bmean q a b) b)

/-- **`L_α(a,b) < R(B_p, L_α, B_q)(a,b)`** on the nondegenerate range, under the write-up's
parameter relations.  This is the conjecture's inequality; what is left is only to derive the
relations from the source's `r`, `p`, `q`. -/
theorem Lal_lt_Rres {al p q a b : ℝ} (hal : 0 < al) (ha : 0 < a) (hab : a < b)
    (hp : p ≠ 0) (hq : q ≠ 0) (hk : p + 2 * q = 1 - 4 * al ^ 2) (hpq : p * q < 0)
    (hT : ∀ t : ℝ, 0 < t → Tval al p q t < 0) :
    Lal al a b < Rres al p q a b := by
  have hb : (0 : ℝ) < b := lt_trans ha hab
  obtain ⟨hac, hcb⟩ := Bmean_lt hq ha hab
  have hc0 : (0 : ℝ) < Bmean q a b := lt_trans ha hac
  have hX : (0 : ℝ) < Lal al a (Bmean q a b) := Lal_pos_of_lt hal ha hac
  have hY : (0 : ℝ) < Lal al (Bmean q a b) b := Lal_pos_of_lt hal hc0 hcb
  have hL : (0 : ℝ) < Lal al a b := Lal_pos_of_lt hal ha hab
  have hrect := rectangle hal ha hac hcb hq hk hpq hT
  have hcq : Bmean q a b ^ q = (a ^ q + b ^ q) / 2 := Bmean_rpow hq ha hb
  have hd1 : Bmean q a b ^ q - a ^ q = (b ^ q - a ^ q) / 2 := by rw [hcq]; ring
  have hd2 : b ^ q - Bmean q a b ^ q = (b ^ q - a ^ q) / 2 := by rw [hcq]; ring
  simp only [Hfun, hd1, hd2] at hrect
  have heq : (b ^ q - a ^ q) / 2 * Lal al a (Bmean q a b) ^ p
        + (b ^ q - a ^ q) / 2 * Lal al (Bmean q a b) b ^ p
      = (b ^ q - a ^ q)
        * ((Lal al a (Bmean q a b) ^ p + Lal al (Bmean q a b) b ^ p) / 2) := by ring
  rw [heq] at hrect
  have hBp : Bmean p (Lal al a (Bmean q a b)) (Lal al (Bmean q a b) b) ^ p
      = (Lal al a (Bmean q a b) ^ p + Lal al (Bmean q a b) b ^ p) / 2 := Bmean_rpow hp hX hY
  have hBpos : (0 : ℝ) < Bmean p (Lal al a (Bmean q a b)) (Lal al (Bmean q a b) b) :=
    Bmean_pos hX hY
  have hpa : (0 : ℝ) < a ^ q := Real.rpow_pos_of_pos ha q
  have hpb : (0 : ℝ) < b ^ q := Real.rpow_pos_of_pos hb q
  rw [Rres]
  rcases lt_or_gt_of_ne hq with hqn | hqp
  · -- `q < 0`, so `b^q < a^q` and `p > 0`
    have hba : b ^ q < a ^ q := (Real.rpow_lt_rpow_iff_of_neg hb ha hqn).mpr hab
    have hDpos : (0 : ℝ) < -(b ^ q - a ^ q) := by linarith
    have hppos : 0 < p := by nlinarith [hpq]
    have h2 : -(b ^ q - a ^ q) * Lal al a b ^ p
        < -(b ^ q - a ^ q)
          * ((Lal al a (Bmean q a b) ^ p + Lal al (Bmean q a b) b ^ p) / 2) := by
      linarith [hrect]
    have hstep := lt_of_mul_lt_mul_left h2 (le_of_lt hDpos)
    by_contra hcon
    push_neg at hcon
    have hle := Real.rpow_le_rpow (le_of_lt hBpos) hcon (le_of_lt hppos)
    rw [hBp] at hle
    linarith
  · -- `q > 0`, so `a^q < b^q` and `p < 0`
    have hba : a ^ q < b ^ q := Real.rpow_lt_rpow (le_of_lt ha) hab hqp
    have hD : (0 : ℝ) < b ^ q - a ^ q := by linarith
    have hpneg : p < 0 := by nlinarith [hpq]
    have hstep := lt_of_mul_lt_mul_left hrect (le_of_lt hD)
    rw [← hBp] at hstep
    exact (Real.rpow_lt_rpow_iff_of_neg hBpos hL hpneg).mp hstep

end Conclusion

/-! ### The source's parameters, and the conjecture

`r = √(1 + 16α² − 16α⁴)`, `p = ±r`, `q = (1−p)/2 − 2α²`.  Everything `Lal_lt_Rres`
assumes is derived here, so `conjecture_4_2` carries only the source's own hypotheses:
`0 < α < 1/2`, `0 < a < b`, and the three parameter definitions.

Most of it is immediate — `p + 2q = 1 − 4α²` is the definition of `q`, `pq < 0` is the sign of
`r`, and `hcomb_plus`/`hcomb_minus` are `convex_plus`/`convex_minus` divided by `r + 1`.  **One
step is not**, and it is worth naming because the obvious bound fails.

`Tval_neg_minus` needs `C² ≠ A²` on the `p = −r` branch, i.e. `q ≠ 2α`.  The crude bound
`r > 1` gives only `q > 1 − 2α²`, which does NOT beat `2α` once `α > (√3−1)/2 ≈ 0.366`, so
the full relation `r² = 1 + 16α² − 16α⁴` is required.  Squaring `r > 4α + 4α² − 1` and
subtracting collapses everything to

    `8α(1 + α)(1 − 4α²) > 0`,

which is exactly the open range `0 < α < 1/2` — and the two sides MEET at `α = 1/2`, which is
the conjecture's excluded equality case.  So the range hypothesis is not a convenience: the
argument's last inequality degenerates precisely where the source says the comparison becomes an
equality. -/

section Parameters

open Set

/-! ### The source's parameters, and the conjecture

`r = √(1 + 16α² − 16α⁴)`, `p = ±r`, `q = (1−p)/2 − 2α²`.  Everything `Lal_lt_Rres` assumes is
derived here.
-/

theorem radicand_pos {al : ℝ} (hal : 0 < al) (hal2 : al < 1 / 2) :
    (0 : ℝ) < 1 + 16 * al ^ 2 - 16 * al ^ 4 := by
  have h1 : al ^ 2 < 1 / 4 := by nlinarith
  nlinarith [sq_nonneg al, mul_pos (mul_pos hal hal) (mul_pos hal hal)]

/-- The `p = +r` branch's convex-combination relation, in the shape `Tval_neg` consumes. -/
theorem hcomb_plus {al r q : ℝ} (hr : r ^ 2 = 1 + 16 * al ^ 2 - 16 * al ^ 4)
    (hq : q = (1 - r) / 2 - 2 * al ^ 2) (hr1 : 1 < r) :
    al ^ 2 = (2 / (r + 1)) * (q / 2) ^ 2 + (1 - 2 / (r + 1)) * (1 / 2 : ℝ) ^ 2 := by
  have hrp : (0 : ℝ) < r + 1 := by linarith
  have hcp := convex_plus (al := al) (r := r) (kap := 1 - 4 * al ^ 2) rfl hr
  have hqe : (q / 2) ^ 2 = ((r - (1 - 4 * al ^ 2)) / 4) ^ 2 := by rw [hq]; ring
  have key : (r + 1) * al ^ 2 = 2 * (q / 2) ^ 2 + (r - 1) * (1 / 2 : ℝ) ^ 2 := by
    rw [hqe]; linarith [hcp]
  have hgoal : (2 / (r + 1)) * (q / 2) ^ 2 + (1 - 2 / (r + 1)) * (1 / 2 : ℝ) ^ 2
      = (2 * (q / 2) ^ 2 + (r - 1) * (1 / 2 : ℝ) ^ 2) / (r + 1) := by
    field_simp
    ring
  rw [hgoal, ← key]
  field_simp

/-- The `p = −r` branch's convex-combination relation, in the shape `Tval_neg_minus` consumes. -/
theorem hcomb_minus {al r q : ℝ} (hr : r ^ 2 = 1 + 16 * al ^ 2 - 16 * al ^ 4)
    (hq : q = (1 + r) / 2 - 2 * al ^ 2) (hr1 : 1 < r) :
    (1 / 2 : ℝ) ^ 2 = (2 / (r + 1)) * (q / 2) ^ 2 + (1 - 2 / (r + 1)) * al ^ 2 := by
  have hrp : (0 : ℝ) < r + 1 := by linarith
  have hcm := convex_minus (al := al) (r := r) (kap := 1 - 4 * al ^ 2) rfl hr
  have hqe : (q / 2) ^ 2 = ((1 - 4 * al ^ 2 + r) / 4) ^ 2 := by rw [hq]; ring
  have key : (r + 1) * (1 / 2 : ℝ) ^ 2 = 2 * (q / 2) ^ 2 + (r - 1) * al ^ 2 := by
    rw [hqe]; linarith [hcm]
  have hgoal : (2 / (r + 1)) * (q / 2) ^ 2 + (1 - 2 / (r + 1)) * al ^ 2
      = (2 * (q / 2) ^ 2 + (r - 1) * al ^ 2) / (r + 1) := by
    field_simp
    ring
  rw [hgoal, ← key]
  field_simp

/-- **`q > 2α` on the `p = −r` branch**, which is what makes `C² ≠ A²` there.

The crude bound `r > 1` is NOT enough: it gives only `q > 1 − 2α²`, which fails to beat `2α`
for `α > (√3−1)/2`.  The full relation `r² = 1 + 16α² − 16α⁴` is needed, and after squaring
`r > 4α + 4α² − 1` the comparison collapses to `8α(1+α)(1 − 4α²) > 0` — exactly the open range,
with the two sides MEETING at `α = 1/2`, the conjecture's excluded equality case. -/
theorem q_gt_two_al {al r q : ℝ} (hal : 0 < al) (hal2 : al < 1 / 2) (hrpos : 0 < r)
    (hr : r ^ 2 = 1 + 16 * al ^ 2 - 16 * al ^ 4) (hq : q = (1 + r) / 2 - 2 * al ^ 2) :
    2 * al < q := by
  have hkey : 4 * al + 4 * al ^ 2 - 1 < r := by
    rcases le_or_gt (4 * al + 4 * al ^ 2 - 1) 0 with h | h
    · linarith
    · have h1 : (0 : ℝ) < 1 - 4 * al ^ 2 := by nlinarith
      have hsq : (4 * al + 4 * al ^ 2 - 1) ^ 2 < r ^ 2 := by
        rw [hr]
        nlinarith [mul_pos hal h1, mul_pos (mul_pos hal hal) h1]
      by_contra hcon
      push_neg at hcon
      nlinarith [hsq, hcon, hrpos, h, mul_self_le_mul_self (le_of_lt hrpos) hcon]
  rw [hq]
  linarith

/-- **Mihoković–Raïssouli Conjecture 4.2 (Conjecture 32 of the published article)** on the
nondegenerate range `0 < α < 1/2`, for both power-mean branches `p = ±r`. -/
theorem conjecture_4_2 {al a b r p q : ℝ} (hal : 0 < al) (hal2 : al < 1 / 2)
    (ha : 0 < a) (hab : a < b)
    (hrdef : r = Real.sqrt (1 + 16 * al ^ 2 - 16 * al ^ 4))
    (hpdef : p = r ∨ p = -r) (hqdef : q = (1 - p) / 2 - 2 * al ^ 2) :
    Lal al a b < Rres al p q a b := by
  have hrad : (0 : ℝ) < 1 + 16 * al ^ 2 - 16 * al ^ 4 := radicand_pos hal hal2
  have hr : r ^ 2 = 1 + 16 * al ^ 2 - 16 * al ^ 4 := by
    rw [hrdef]; exact Real.sq_sqrt (le_of_lt hrad)
  have hrpos : 0 < r := by rw [hrdef]; exact Real.sqrt_pos.mpr hrad
  obtain ⟨hr1, hr2⟩ := r_bounds hal hal2 hrpos hr
  have hal4 : al ^ 2 < 1 / 4 := by nlinarith
  rcases hpdef with hp | hp
  · have hqv : q = (1 - r) / 2 - 2 * al ^ 2 := by rw [hqdef, hp]
    have hqneg : q < 0 := by rw [hqv]; nlinarith
    have hq1 : q ^ 2 < 1 := by rw [hqv]; nlinarith
    have hne : (q / 2) ^ 2 ≠ (1 / 2 : ℝ) ^ 2 := by
      intro h
      nlinarith [h, hq1]
    have hcomb := hcomb_plus hr hqv hr1
    rw [hp]
    refine Lal_lt_Rres hal ha hab (ne_of_gt hrpos) (ne_of_lt hqneg) ?_ ?_ ?_
    · rw [hqv]; ring
    · exact mul_neg_of_pos_of_neg hrpos hqneg
    · intro t ht
      exact Tval_neg hal hal2 ht hqneg hne hr1 hr2 hcomb
  · have hqv : q = (1 + r) / 2 - 2 * al ^ 2 := by rw [hqdef, hp]; ring
    have hqpos : 0 < q := by rw [hqv]; nlinarith
    have h2al : 2 * al < q := q_gt_two_al hal hal2 hrpos hr hqv
    have hne : (q / 2) ^ 2 ≠ al ^ 2 := by
      intro h
      nlinarith [h, h2al, hal]
    have hcomb := hcomb_minus hr hqv hr1
    rw [hp]
    refine Lal_lt_Rres hal ha hab (neg_ne_zero.mpr (ne_of_gt hrpos)) (ne_of_gt hqpos) ?_ ?_ ?_
    · rw [hqv]; ring
    · exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hrpos) hqpos
    · intro t ht
      exact Tval_neg_minus hal hal2 ht hqpos hne hr1 hr2 hcomb

end Parameters

end Principia.MathDB.P363173
