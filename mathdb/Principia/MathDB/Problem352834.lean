import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

set_option autoImplicit false

/-!
# MathDB 352834 — the sine-angle invariant of harmonic polygons

Write-up: `mathdb-open-problems/problems/352834/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`, "The sine-angle invariant of
harmonic polygons".  It proves **Conjecture 2** of R. Alves Garcia, D. Reznik and
P. Roitman, *New Properties of Harmonic Polygons*, J. Geometry and Graphics **26**(2)
(2022) 217–236, stated on p. 228, for every number of sides.

## The statement

A convex harmonic `N`-gon is parametrised, up to a fixed similarity, by

  `P_j = O + R e^{iγ} w_j`,  `w_j = (z_j - d)/(1 - d z_j)`,  `z_j = e^{i(t + jβ)}`,

with `β = 2π/N`, `R > 0`, `-1 < d < 1`, and only `t` varying.  With
`D_m = 1 - 2d²cos(mβ) + d⁴`, `S = ∑ sin(2θ_j)`, `A` the area and `Q = ∑ s_j²`:

  `S/A = -2 sin(2β) D₁ / (R² sin β D₂)`,
  `S/Q = -(1-d²) sin(2β) D₁ / (2R²(1+d²)(1-cos β) D₂)`,

both **independent of `t`**.

## Which piece is the write-up's own

Its stated key point is that the correlation sums `T_m = ∑_j conj(w_j) w_{j+m}` for
different steps `m` share a single phase factor, `T_m = N(1 + C_m H(t))`.  The proof of
that rests on one rational identity, and **that identity is what this module proves**:

  `(1 - dz)(vz - d) = (z - d)(1 - dvz) + C·((z - d) + d(1 - dvz))`   whenever
  `(1 - d²v)·C = (1 - d²)(v - 1)`.

Cleared of denominators it needs no nonvanishing hypotheses at all and is one
`linear_combination z * hC` — the difference of the two sides is exactly `z` times the
defining equation of `C`.  `corr_quotient` recovers the write-up's quotient form.

## What is carried

* the **root-of-unity evaluation** `∑_j 1/(1 - dvz_j)` etc., i.e. that `T_m` has the
  stated closed form (`Setup.hT`), together with the defining equation of `C_m`
  (`Setup.hC`);
* the **geometry**: `S = -Im T₂` (inscribed-angle theorem), `A = (R²/2) Im T₁`
  (shoelace) and `Q = 2R²(N - Re T₁)` (`Setup.hS`, `hA`, `hQ`);
* positivity of `H(t)` (`Setup.hH`).

## What is proved

* `corr_cleared` / `corr_quotient` — the rational identity above.
* `conj_w_mul` — that `conj(w_j) w_{j+m}` really is the quotient the identity is about,
  for `‖z‖ = 1` and real `d`.
* `C_eq` — the closed form `C_m = (1-d⁴)(cos mβ - 1)/D_m + i(1-d²)² sin(mβ)/D_m`,
  obtained from `Setup.hC` by **uniqueness**: `1 - d²v ≠ 0` because `‖d²v‖ = d² < 1`.
* `Dm_pos` — `D_m = (1-d²)² + 2d²(1 - cos mβ) > 0`, which is why every denominator below
  is nonzero.
* `CcIm_pos`, `CcRe_neg` — the sign facts the write-up needs for "division is therefore
  legitimate", and which fix the sign of the answer.
* `ratio_SA`, `ratio_SQ` — the theorem, and `ratio_SA_indep`, `ratio_SQ_indep` — that
  both are independent of `t`, which is half of what Conjecture 2 asserts.
* `S_eq_zero_of_square` — the `N = 4` case the theorem singles out, where `sin 2β = 0`
  and `S = 0`; the zero comes from `Im C₂ = 0`, with no division by the numerator.

`Campaigns/MathDB-Formalization/verify_352834.py` checks all of the above numerically on
actual polygons, including the three carried geometric identifications and the constancy
of `S/A` along each family.
-/

namespace Principia.MathDB.P352834

open Complex

/-! ## The point on the unit circle -/

/-- `v = c + s·i`.  Kept in terms of ABSTRACT `c`, `s` with `c² + s² = 1`, so that the
algebra below never meets `Real.cos`/`Real.sin` — `push_cast` rewrites `↑(Real.cos θ)` to
`Complex.cos ↑θ` and derails every subsequent `field_simp`. -/
noncomputable def vcs (c s : ℝ) : ℂ := (c : ℂ) + (s : ℂ) * I

theorem vcs_re (c s : ℝ) : (vcs c s).re = c := by simp [vcs]

theorem vcs_im (c s : ℝ) : (vcs c s).im = s := by simp [vcs]

theorem vcs_normSq {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) : Complex.normSq (vcs c s) = 1 := by
  rw [Complex.normSq_apply, vcs_re, vcs_im]
  nlinarith [hcs]

theorem vcs_norm {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) : ‖vcs c s‖ = 1 := by
  rw [← Real.sqrt_one, ← vcs_normSq hcs, Complex.norm_def]

/-- `v θ = e^{iθ}`. -/
noncomputable def vv (θ : ℝ) : ℂ := vcs (Real.cos θ) (Real.sin θ)

theorem pythag (θ : ℝ) : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem vv_norm (θ : ℝ) : ‖vv θ‖ = 1 := vcs_norm (pythag θ)

/-! ## `D_m` and its positivity -/

/-- `D_m = 1 - 2d²cos(mβ) + d⁴`. -/
noncomputable def Dm (c d : ℝ) : ℝ := 1 - 2 * d ^ 2 * c + d ^ 4

/-- The form that makes the positivity obvious. -/
theorem Dm_eq (c d : ℝ) : Dm c d = (1 - d ^ 2) ^ 2 + 2 * d ^ 2 * (1 - c) := by
  unfold Dm; ring

theorem Dm_pos {c d : ℝ} (hd : |d| < 1) (hc : c ≤ 1) : 0 < Dm c d := by
  have hd2 : d ^ 2 < 1 := by
    have := abs_lt.mp hd
    nlinarith [this.1, this.2]
  have h1 : 0 < (1 - d ^ 2) ^ 2 := by positivity
  have h2 : 0 ≤ 2 * d ^ 2 * (1 - c) := by nlinarith [sq_nonneg d]
  rw [Dm_eq]; linarith

theorem Dm_ne_zero {c d : ℝ} (hd : |d| < 1) (hc : c ≤ 1) : Dm c d ≠ 0 :=
  (Dm_pos hd hc).ne'

/-! ## The rational identity — the crux of the write-up's Lemma 1 -/

/-- **The identity, cleared of denominators.**  The difference of the two sides is
exactly `z` times the defining equation of `C`, so no nonvanishing hypothesis is needed
and the proof is a single `linear_combination`. -/
theorem corr_cleared (z d v C : ℂ) (hC : (1 - d ^ 2 * v) * C = (1 - d ^ 2) * (v - 1)) :
    (1 - d * z) * (v * z - d)
      = (z - d) * (1 - d * v * z) + C * ((z - d) + d * (1 - d * v * z)) := by
  linear_combination (-z) * hC

/-- …and the quotient form in which the write-up states it. -/
theorem corr_quotient (z d v C : ℂ) (hC : (1 - d ^ 2 * v) * C = (1 - d ^ 2) * (v - 1))
    (h1 : z - d ≠ 0) (h2 : 1 - d * v * z ≠ 0) :
    (1 - d * z) * (v * z - d) / ((z - d) * (1 - d * v * z))
      = 1 + C * (1 / (1 - d * v * z) + d / (z - d)) := by
  have e : 1 + C * (1 / (1 - d * v * z) + d / (z - d))
      = ((z - d) * (1 - d * v * z) + C * ((z - d) + d * (1 - d * v * z)))
        / ((z - d) * (1 - d * v * z)) := by
    field_simp
  rw [e, ← corr_cleared z d v C hC]

/-! ## The correlation this identity is about -/

/-- `w z d = (z - d)/(1 - dz)`, the Möbius map of the parametrisation. -/
noncomputable def w (z : ℂ) (d : ℝ) : ℂ := (z - d) / (1 - d * z)

/-- For `‖z‖ = 1` and real `d`, `conj (w z d) = (1 - dz)/(z - d)`. -/
theorem conj_w {z : ℂ} {d : ℝ} (hz : ‖z‖ = 1) (h2 : z - d ≠ 0) :
    (starRingEnd ℂ) (w z d) = (1 - d * z) / (z - d) := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz
  have hcz : (starRingEnd ℂ) z = z⁻¹ := (Complex.inv_eq_conj hz).symm
  have hzi : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
  simp only [w, map_div₀, map_sub, map_mul, map_one, Complex.conj_ofReal, hcz]
  rw [div_eq_div_iff ?hne h2]
  · field_simp
  · intro h
    apply h2
    linear_combination z * h + (d : ℂ) * hzi

/-- **The correlation is the quotient the identity is about.** -/
theorem conj_w_mul {z v : ℂ} {d : ℝ} (hz : ‖z‖ = 1) (h2 : z - d ≠ 0) :
    (starRingEnd ℂ) (w z d) * w (v * z) d
      = (1 - d * z) * (v * z - d) / ((z - d) * (1 - d * v * z)) := by
  rw [conj_w hz h2, w, div_mul_div_comm]
  congr 2
  ring

/-! ## The closed form of `C_m`, by uniqueness -/

/-- `Re C_m = (1-d⁴)(cos mβ - 1)/D_m`. -/
noncomputable def CcRe (c d : ℝ) : ℝ := (1 - d ^ 4) * (c - 1) / Dm c d

/-- `Im C_m = (1-d²)² sin(mβ)/D_m`. -/
noncomputable def CcIm (c s d : ℝ) : ℝ := (1 - d ^ 2) ^ 2 * s / Dm c d

/-- `1 - d²v ≠ 0` for `v` on the unit circle, because its distance from `1` is `d² < 1`. -/
theorem one_sub_ne_zero {c s d : ℝ} (hd : |d| < 1) (hcs : c ^ 2 + s ^ 2 = 1) :
    (1 : ℂ) - (d : ℂ) ^ 2 * vcs c s ≠ 0 := by
  have hd2 : d ^ 2 < 1 := by
    have := abs_lt.mp hd
    nlinarith [this.1, this.2]
  intro h
  have h1 : (d : ℂ) ^ 2 * vcs c s = 1 := by linear_combination -h
  have h2 : ‖(d : ℂ) ^ 2 * vcs c s‖ = 1 := by rw [h1]; simp
  rw [norm_mul, vcs_norm hcs, mul_one, norm_pow, Complex.norm_real, Real.norm_eq_abs] at h2
  nlinarith [abs_nonneg d, sq_abs d]

/-- `CcRe` and `CcIm` cleared of their common denominator. -/
theorem CcRe_mul_Dm {c d : ℝ} (hD : Dm c d ≠ 0) :
    CcRe c d * Dm c d = (1 - d ^ 4) * (c - 1) := by
  unfold CcRe; field_simp

theorem CcIm_mul_Dm {c s d : ℝ} (hD : Dm c d ≠ 0) :
    CcIm c s d * Dm c d = (1 - d ^ 2) ^ 2 * s := by
  unfold CcIm; field_simp

/-- The closed form satisfies the defining equation.  Multiplying through by `D_m` turns
it into a polynomial identity whose only input is `c² + s² = 1`; the residual is exactly
`d²(1-d²)²(c²+s²-1)`. -/
theorem Cc_spec {c s d : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hD : Dm c d ≠ 0) :
    (1 - (d : ℂ) ^ 2 * vcs c s) * ((CcRe c d : ℂ) + (CcIm c s d : ℂ) * I)
      = (1 - (d : ℂ) ^ 2) * (vcs c s - 1) := by
  have hDC : ((Dm c d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD
  have hpy : ((c : ℂ)) ^ 2 + ((s : ℂ)) ^ 2 = 1 := by exact_mod_cast hcs
  have hDdef : ((Dm c d : ℝ) : ℂ) = 1 - 2 * (d : ℂ) ^ 2 * (c : ℂ) + (d : ℂ) ^ 4 := by
    unfold Dm; push_cast; ring
  have e1 : ((CcRe c d : ℝ) : ℂ) * ((Dm c d : ℝ) : ℂ)
      = (1 - (d : ℂ) ^ 4) * ((c : ℂ) - 1) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (CcRe_mul_Dm (c := c) (d := d) hD)
  have e2 : ((CcIm c s d : ℝ) : ℂ) * ((Dm c d : ℝ) : ℂ)
      = (1 - (d : ℂ) ^ 2) ^ 2 * (s : ℂ) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (CcIm_mul_Dm (c := c) (s := s) (d := d) hD)
  refine mul_right_cancel₀ hDC ?_
  have expand : (1 - (d : ℂ) ^ 2 * vcs c s) * ((CcRe c d : ℂ) + (CcIm c s d : ℂ) * I)
        * ((Dm c d : ℝ) : ℂ)
      = (1 - (d : ℂ) ^ 2 * vcs c s)
        * (((CcRe c d : ℂ) * ((Dm c d : ℝ) : ℂ))
           + ((CcIm c s d : ℂ) * ((Dm c d : ℝ) : ℂ)) * I) := by ring
  rw [expand, e1, e2, hDdef]
  unfold vcs
  linear_combination ((d : ℂ) ^ 2 * (1 - (d : ℂ) ^ 2) ^ 2) * hpy
    - ((d : ℂ) ^ 2 * (s : ℂ) ^ 2 * (1 - (d : ℂ) ^ 2) ^ 2) * Complex.I_sq

/-- **`C_m` is determined**: anything satisfying the defining equation is the closed form. -/
theorem C_eq {c s d : ℝ} (hd : |d| < 1) (hcs : c ^ 2 + s ^ 2 = 1) (hD : Dm c d ≠ 0) {C : ℂ}
    (hC : (1 - (d : ℂ) ^ 2 * vcs c s) * C = (1 - (d : ℂ) ^ 2) * (vcs c s - 1)) :
    C = (CcRe c d : ℂ) + (CcIm c s d : ℂ) * I :=
  mul_left_cancel₀ (one_sub_ne_zero hd hcs) (hC.trans (Cc_spec hcs hD).symm)

theorem C_re {c s d : ℝ} (hd : |d| < 1) (hcs : c ^ 2 + s ^ 2 = 1) (hD : Dm c d ≠ 0) {C : ℂ}
    (hC : (1 - (d : ℂ) ^ 2 * vcs c s) * C = (1 - (d : ℂ) ^ 2) * (vcs c s - 1)) :
    C.re = CcRe c d := by rw [C_eq hd hcs hD hC]; simp

theorem C_im {c s d : ℝ} (hd : |d| < 1) (hcs : c ^ 2 + s ^ 2 = 1) (hD : Dm c d ≠ 0) {C : ℂ}
    (hC : (1 - (d : ℂ) ^ 2 * vcs c s) * C = (1 - (d : ℂ) ^ 2) * (vcs c s - 1)) :
    C.im = CcIm c s d := by rw [C_eq hd hcs hD hC]; simp

/-! ## The sign facts that make the division legitimate -/

theorem CcIm_pos {c s d : ℝ} (hd : |d| < 1) (hc : c ≤ 1) (hs : 0 < s) :
    0 < CcIm c s d := by
  have hd2 : d ^ 2 < 1 := by
    have := abs_lt.mp hd
    nlinarith [this.1, this.2]
  have hnum : 0 < (1 - d ^ 2) ^ 2 * s := by positivity
  exact div_pos hnum (Dm_pos hd hc)

theorem CcRe_neg {c d : ℝ} (hd : |d| < 1) (hc : c < 1) : CcRe c d < 0 := by
  have hd2 : d ^ 2 < 1 := by
    have := abs_lt.mp hd
    nlinarith [this.1, this.2]
  have h4 : 0 < 1 - d ^ 4 := by nlinarith [sq_nonneg (d ^ 2)]
  have hnum : (1 - d ^ 4) * (c - 1) < 0 := mul_neg_of_pos_of_neg h4 (by linarith)
  exact div_neg_of_neg_of_pos hnum (Dm_pos hd hc.le)

/-! ## The carried inputs -/

/-- The root-of-unity evaluation and the three geometric identifications. -/
structure Setup where
  /-- number of sides -/
  N : ℕ
  hN : 3 ≤ N
  /-- the family parameter `-1 < d < 1` -/
  d : ℝ
  hd : |d| < 1
  /-- the scale -/
  R : ℝ
  hR : 0 < R
  /-- `b = 2π/N`, the angular step -/
  b : ℝ
  hb : b = 2 * Real.pi / N
  /-- the correlation sums `T_m(t) = ∑_j conj(w_j) w_{j+m}` -/
  T : ℕ → ℝ → ℂ
  /-- the phase factors `C_m` -/
  C : ℕ → ℂ
  /-- **CARRIED**: `(1 - d² e^{imb}) C_m = (1 - d²)(e^{imb} - 1)`. -/
  hC : ∀ m : ℕ, (1 - (d : ℂ) ^ 2 * vv (m * b)) * C m
    = (1 - (d : ℂ) ^ 2) * (vv (m * b) - 1)
  /-- `H(t) = (1-d^{2N})/(1 - 2d^N cos Nt + d^{2N})` -/
  H : ℝ → ℝ
  hH : ∀ t, 0 < H t
  /-- **CARRIED** (root-of-unity sums): `T_m = N(1 + C_m H(t))`. -/
  hT : ∀ (m : ℕ) (t : ℝ), T m t = (N : ℂ) * (1 + C m * (H t : ℂ))
  /-- `S(t) = ∑_j sin(2θ_j)` -/
  Ssum : ℝ → ℝ
  /-- `A(t)`, the area -/
  Area : ℝ → ℝ
  /-- `Q(t) = ∑_j s_j²` -/
  Qsum : ℝ → ℝ
  /-- **CARRIED** (inscribed-angle theorem): `S = -Im T₂`. -/
  hS : ∀ t, Ssum t = -(T 2 t).im
  /-- **CARRIED** (shoelace formula): `A = (R²/2) Im T₁`. -/
  hA : ∀ t, Area t = R ^ 2 / 2 * (T 1 t).im
  /-- **CARRIED** (each `‖w_j‖ = 1`): `Q = 2R²(N - Re T₁)`. -/
  hQ : ∀ t, Qsum t = 2 * R ^ 2 * ((N : ℝ) - (T 1 t).re)

namespace Setup

variable (P : Setup)

theorem N_pos : 0 < (P.N : ℝ) := by
  have hN := P.hN
  have h : 0 < P.N := by omega
  exact_mod_cast h

/-- `0 < b ≤ 2π/3 < π`, so `sin b > 0` and `cos b < 1`. -/
theorem b_pos : 0 < P.b := by
  rw [P.hb]
  exact div_pos (by positivity) P.N_pos

theorem b_lt_pi : P.b < Real.pi := by
  rw [P.hb]
  have h3 : (3 : ℝ) ≤ (P.N : ℝ) := by exact_mod_cast P.hN
  rw [div_lt_iff₀ P.N_pos]
  nlinarith [Real.pi_pos]

theorem sin_b_pos : 0 < Real.sin P.b :=
  Real.sin_pos_of_pos_of_lt_pi P.b_pos P.b_lt_pi

theorem cos_b_lt_one : Real.cos P.b < 1 := by
  rcases lt_or_eq_of_le (Real.cos_le_one P.b) with h | h
  · exact h
  · exfalso
    have hp := pythag P.b
    have hs : Real.sin P.b = 0 := by nlinarith
    linarith [P.sin_b_pos]

theorem d_sq_lt_one : P.d ^ 2 < 1 := by
  have h := abs_lt.mp P.hd
  nlinarith [h.1, h.2]

/-! ### The two phase factors in closed form -/

theorem C_one_im : (P.C 1).im = CcIm (Real.cos P.b) (Real.sin P.b) P.d := by
  have h : ((1 : ℕ) : ℝ) * P.b = P.b := by push_cast; ring
  have hC := P.hC 1
  rw [h, vv] at hC
  exact C_im P.hd (pythag P.b) (Dm_ne_zero P.hd (Real.cos_le_one _)) hC

theorem C_one_re : (P.C 1).re = CcRe (Real.cos P.b) P.d := by
  have h : ((1 : ℕ) : ℝ) * P.b = P.b := by push_cast; ring
  have hC := P.hC 1
  rw [h, vv] at hC
  exact C_re P.hd (pythag P.b) (Dm_ne_zero P.hd (Real.cos_le_one _)) hC

theorem C_two_im :
    (P.C 2).im = CcIm (Real.cos (2 * P.b)) (Real.sin (2 * P.b)) P.d := by
  have h : ((2 : ℕ) : ℝ) * P.b = 2 * P.b := by push_cast; ring
  have hC := P.hC 2
  rw [h, vv] at hC
  exact C_im P.hd (pythag (2 * P.b)) (Dm_ne_zero P.hd (Real.cos_le_one _)) hC

/-! ### The three quantities in closed form -/

theorem S_eq (t : ℝ) :
    P.Ssum t
      = -((P.N : ℝ) * P.H t * CcIm (Real.cos (2 * P.b)) (Real.sin (2 * P.b)) P.d) := by
  rw [P.hS, P.hT, ← P.C_two_im]
  simp [Complex.add_im, Complex.mul_im]
  ring

theorem A_eq (t : ℝ) :
    P.Area t = (P.N : ℝ) * P.R ^ 2 / 2 * P.H t
      * CcIm (Real.cos P.b) (Real.sin P.b) P.d := by
  rw [P.hA, P.hT, ← P.C_one_im]
  simp [Complex.add_im, Complex.mul_im]
  ring

theorem Q_eq (t : ℝ) :
    P.Qsum t = -(2 * (P.N : ℝ) * P.R ^ 2 * P.H t * CcRe (Real.cos P.b) P.d) := by
  rw [P.hQ, P.hT, ← P.C_one_re]
  simp [Complex.add_re, Complex.mul_re]
  ring

/-! ### Nonvanishing, so the ratios are defined -/

theorem Area_pos (t : ℝ) : 0 < P.Area t := by
  rw [P.A_eq t]
  have h1 : 0 < CcIm (Real.cos P.b) (Real.sin P.b) P.d :=
    CcIm_pos P.hd (Real.cos_le_one _) P.sin_b_pos
  have h2 := P.hH t
  have h3 := P.N_pos
  have h4 : 0 < P.R ^ 2 := pow_pos P.hR 2
  positivity

theorem Qsum_pos (t : ℝ) : 0 < P.Qsum t := by
  rw [P.Q_eq t]
  have h1 : CcRe (Real.cos P.b) P.d < 0 := CcRe_neg P.hd P.cos_b_lt_one
  have h2 := P.hH t
  have h3 := P.N_pos
  have h4 : 0 < P.R ^ 2 := pow_pos P.hR 2
  have h5 : 0 < 2 * (P.N : ℝ) * P.R ^ 2 * P.H t := by positivity
  have e : -(2 * (P.N : ℝ) * P.R ^ 2 * P.H t * CcRe (Real.cos P.b) P.d)
      = (2 * (P.N : ℝ) * P.R ^ 2 * P.H t) * (-CcRe (Real.cos P.b) P.d) := by ring
  rw [e]
  exact mul_pos h5 (by linarith)

/-! ### The theorem -/

/-- **Conjecture 2, first form**: `S/A = -2 sin(2b) D₁ / (R² sin b D₂)`. -/
theorem ratio_SA (t : ℝ) :
    P.Ssum t / P.Area t
      = -(2 * Real.sin (2 * P.b) * Dm (Real.cos P.b) P.d)
        / (P.R ^ 2 * Real.sin P.b * Dm (Real.cos (2 * P.b)) P.d) := by
  have hD1 : Dm (Real.cos P.b) P.d ≠ 0 := Dm_ne_zero P.hd (Real.cos_le_one _)
  have hD2 : Dm (Real.cos (2 * P.b)) P.d ≠ 0 := Dm_ne_zero P.hd (Real.cos_le_one _)
  have hs : Real.sin P.b ≠ 0 := P.sin_b_pos.ne'
  have hR2 : P.R ^ 2 ≠ 0 := pow_ne_zero 2 P.hR.ne'
  have hRne : P.R ≠ 0 := P.hR.ne'
  have hN : (P.N : ℝ) ≠ 0 := P.N_pos.ne'
  have hH := (P.hH t).ne'
  rw [div_eq_iff (P.Area_pos t).ne', P.S_eq t, P.A_eq t]
  unfold CcIm
  field_simp

/-- **Conjecture 2, second form**:
`S/Q = -(1-d²) sin(2b) D₁ / (2R²(1+d²)(1-cos b) D₂)`. -/
theorem ratio_SQ (t : ℝ) :
    P.Ssum t / P.Qsum t
      = -((1 - P.d ^ 2) * Real.sin (2 * P.b) * Dm (Real.cos P.b) P.d)
        / (2 * P.R ^ 2 * (1 + P.d ^ 2) * (1 - Real.cos P.b)
            * Dm (Real.cos (2 * P.b)) P.d) := by
  have hD1 : Dm (Real.cos P.b) P.d ≠ 0 := Dm_ne_zero P.hd (Real.cos_le_one _)
  have hD2 : Dm (Real.cos (2 * P.b)) P.d ≠ 0 := Dm_ne_zero P.hd (Real.cos_le_one _)
  have hR2 : P.R ^ 2 ≠ 0 := pow_ne_zero 2 P.hR.ne'
  have hRne : P.R ≠ 0 := P.hR.ne'
  have hN : (P.N : ℝ) ≠ 0 := P.N_pos.ne'
  have hH := (P.hH t).ne'
  have hdd := P.d_sq_lt_one
  have hone : (1 : ℝ) - P.d ^ 2 ≠ 0 := by intro h; nlinarith
  have hplus : (1 : ℝ) + P.d ^ 2 ≠ 0 := by nlinarith [sq_nonneg P.d]
  have hcb := P.cos_b_lt_one
  have hcos : (1 : ℝ) - Real.cos P.b ≠ 0 := by intro h; linarith
  rw [div_eq_iff (P.Qsum_pos t).ne', P.S_eq t, P.Q_eq t]
  unfold CcIm CcRe
  field_simp
  ring

/-- **Both ratios are independent of `t`** — the other half of Conjecture 2. -/
theorem ratio_SA_indep (t1 t2 : ℝ) : P.Ssum t1 / P.Area t1 = P.Ssum t2 / P.Area t2 := by
  rw [P.ratio_SA t1, P.ratio_SA t2]

theorem ratio_SQ_indep (t1 t2 : ℝ) : P.Ssum t1 / P.Qsum t1 = P.Ssum t2 / P.Qsum t2 := by
  rw [P.ratio_SQ t1, P.ratio_SQ t2]

/-- **The `N = 4` case the theorem singles out.**  There `2b = π`, so `sin(2b) = 0` and
`S = 0` — and the zero arrives through `Im C₂ = 0`, with no division by the numerator. -/
theorem S_eq_zero_of_square (h4 : P.N = 4) (t : ℝ) : P.Ssum t = 0 := by
  have hb : P.b = Real.pi / 2 := by
    rw [P.hb, h4]; push_cast; ring
  have h2b : 2 * P.b = Real.pi := by rw [hb]; ring
  rw [P.S_eq t, h2b, Real.sin_pi]
  unfold CcIm
  simp

end Setup

end Principia.MathDB.P352834
