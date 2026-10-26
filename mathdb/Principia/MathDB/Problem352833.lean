import Principia.MathDB.Problem352834
import Mathlib.Tactic

set_option autoImplicit false

/-!
# MathDB 352833 — the reciprocal areas of the lateral harmonic polygons

Write-up: `mathdb-open-problems/problems/352833/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`.  It proves **Conjecture 1** of
R. Alves Garcia, D. Reznik and P. Roitman, J. Geometry and Graphics **26**(2) (2022)
217–236, p. 228, for every **odd** number of sides.

For the convex Poncelet family between an ellipse of semiaxes `a ≥ b > 0` and its
concentric homothetic outer ellipse, let `A₊` and `A₋` be the areas of the two polar
polygons taken about the foci in circles of radius `ρ`.  With `c = √(a²-b²)`,
`d = c/(a+b) ∈ [0,1)`, `R = ρ²a/b²` and `ϑ = 2π/N`:

  `1/A₊ + 1/A₋ = 4(1 - 2d²cos ϑ + d⁴)/(N R²(1-d²)² sin ϑ) · (1 + d^{2N})/(1 - d^{2N})`,

**independent of the polygon's phase `t`**.

## This is the sibling of #352834, and reuses its machinery

The write-up for #352834 says so itself: "the root-of-unity correlation method extends
the area calculation in our immediately preceding note for MathDB 352833".  This module
therefore **imports** `Principia.MathDB.Problem352834` and reuses `Dm`, `CcIm`,
`corr_cleared` and `Cc_spec` rather than restating them.  What is new here is:

* `mobius_identity` — the row's own algebra.  With `e = c/a = 2d/(1+d²)` and
  `f = b/a = (1-d²)/(1+d²)`, the pole of the side line, recentred at `O_±` and rescaled
  by `R`, is **exactly** `(z - d)/(1 - dz)` with `z = e^{iu}`; and for the other focus
  the same formula holds with `d` replaced by `-d`, **with the same `R` and the same
  phase `t`**.  That last point is what lets the two areas be compared at all.
* `one_sub_e_mul_pos` — the recentring denominator `1 - e·cos u` equals
  `|1 - dz|²/(1+d²) > 0`, so no pole is at infinity.
* `Dm_neg`, `CcIm_neg` — `D` and `Im C` are **even** in `d`, since they involve only
  `d²` and `d⁴`.
* `B_neg_denom` and `inv_add_inv` — **the phase cancellation**.  For odd `N`,
  `(-d)^N = -d^N`, so `A₊ = K/(1 - 2d^N cos Nt + d^{2N})` and
  `A₋ = K/(1 + 2d^N cos Nt + d^{2N})` with the *same* `K`; adding the reciprocals kills
  `cos Nt` and leaves `2(1 + d^{2N})/K`.
* `Setup.invariant` — the theorem, and `Setup.phase_independent` — that it does not
  depend on `t`, which is the conjecture's actual assertion.

## The oddness is load-bearing

`(-d)^N = -d^N` only for odd `N`; for even `N` the two denominators coincide and nothing
cancels.  `Campaigns/MathDB-Formalization/verify_352833.py` confirms this is not a
technicality: for `N = 4, 6, 8` the same sum varies with the phase by up to 385%.

## What is carried

`Setup` carries the geometry and the root-of-unity evaluation: that `A_± = R² B_N(±d, t)`
where `B_N` is the area formula of the write-up's Lemma, whose rational-identity core is
the imported `corr_cleared`.  The Python check verifies that formula against a direct
shoelace computation of the actual polar polygons.
-/

namespace Principia.MathDB.P352833

open Complex Principia.MathDB.P352834

/-! ## `D` and `Im C` are even in `d` -/

theorem Dm_neg (c d : ℝ) : Dm c (-d) = Dm c d := by
  unfold Dm; ring

theorem CcIm_neg (c s d : ℝ) : CcIm c s (-d) = CcIm c s d := by
  unfold CcIm; rw [Dm_neg]; ring_nf

/-! ## The Möbius identity for the poles -/

/-- `(1 + d²)² - (2dC)² = (1 - d²)² + 4d²(1 - C²)`: the factorisation that makes the
recentring denominator's positivity a two-line argument. -/
theorem prod_denoms (d C : ℝ) :
    (1 + d ^ 2 - 2 * d * C) * (1 + d ^ 2 + 2 * d * C)
      = (1 - d ^ 2) ^ 2 + 4 * d ^ 2 * (1 - C ^ 2) := by
  ring

/-- **The recentring denominator is positive**: it is `|1 - dz|²`, and `|dz| = |d| < 1`. -/
theorem denom_sq_pos {d C S : ℝ} (hd : |d| < 1) (hcs : C ^ 2 + S ^ 2 = 1) :
    0 < 1 + d ^ 2 - 2 * d * C := by
  have habs := abs_lt.mp hd
  have hdsq : d ^ 2 < 1 := by nlinarith [habs.1, habs.2]
  have hC : C ^ 2 ≤ 1 := by nlinarith [sq_nonneg S]
  have hprod : 0 < (1 + d ^ 2 - 2 * d * C) * (1 + d ^ 2 + 2 * d * C) := by
    rw [prod_denoms]
    nlinarith [sq_nonneg (1 - d ^ 2), sq_nonneg d, hC, hdsq]
  nlinarith [hprod, sq_nonneg d]

/-- **THE MÖBIUS IDENTITY, CLEARED OF DENOMINATORS.**  Multiplying the write-up's
`(mobius)` through by `(1 + d²)` and by both denominators leaves a polynomial identity
whose only inputs are `C² + S² = 1` and `I² = -1`.  Writing `z = C + Si`, both sides are
`(z - d)²(1 - dz)/z`. -/
theorem mobius_cleared (d C S : ℝ) (hcs : C ^ 2 + S ^ 2 = 1) :
    (((1 + (d : ℂ) ^ 2) * (C : ℂ) - 2 * (d : ℂ))
        + ((1 - (d : ℂ) ^ 2) * (S : ℂ)) * I)
        * (1 - (d : ℂ) * ((C : ℂ) + (S : ℂ) * I))
      = ((C : ℂ) + (S : ℂ) * I - (d : ℂ))
        * ((1 + (d : ℂ) ^ 2) - 2 * (d : ℂ) * (C : ℂ)) := by
  have hpy : ((C : ℂ)) ^ 2 + ((S : ℂ)) ^ 2 = 1 := by exact_mod_cast hcs
  linear_combination ((d : ℂ) * (1 - (d : ℂ) ^ 2)) * hpy
    - ((d : ℂ) * (1 - (d : ℂ) ^ 2) * (S : ℂ) ^ 2) * Complex.I_sq

theorem one_sub_dz_ne {d C S : ℝ} (hd : |d| < 1) (hcs : C ^ 2 + S ^ 2 = 1) :
    (1 : ℂ) - (d : ℂ) * ((C : ℂ) + (S : ℂ) * I) ≠ 0 := by
  have habs := abs_lt.mp hd
  have hdsq : d ^ 2 < 1 := by nlinarith [habs.1, habs.2]
  intro h
  have h1 : (1 : ℝ) - d * C = 0 := by
    have := congrArg Complex.re h
    simpa using this
  have h2 : d * S = 0 := by
    have := congrArg Complex.im h
    simpa using this
  rcases mul_eq_zero.mp h2 with hd0 | hs0
  · rw [hd0] at h1; norm_num at h1
  · have hC2 : C ^ 2 = 1 := by rw [hs0] at hcs; nlinarith
    nlinarith [h1, hC2, hdsq, sq_nonneg (d - C), sq_nonneg (d + C)]

/-- ...and in the quotient form the write-up displays.  The pole, recentred at `O_±` and
rescaled by `R`, is exactly `(z - d)/(1 - dz)`. -/
theorem mobius_quotient {d C S : ℝ} (hd : |d| < 1) (hcs : C ^ 2 + S ^ 2 = 1) :
    (((1 + (d : ℂ) ^ 2) * (C : ℂ) - 2 * (d : ℂ))
        + ((1 - (d : ℂ) ^ 2) * (S : ℂ)) * I)
        / ((1 + (d : ℂ) ^ 2) - 2 * (d : ℂ) * (C : ℂ))
      = ((C : ℂ) + (S : ℂ) * I - (d : ℂ))
        / (1 - (d : ℂ) * ((C : ℂ) + (S : ℂ) * I)) := by
  have hE : ((1 + (d : ℂ) ^ 2) - 2 * (d : ℂ) * (C : ℂ)) ≠ 0 := by
    have h := denom_sq_pos hd hcs
    have : (((1 + d ^ 2 - 2 * d * C : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h.ne'
    push_cast at this
    convert this using 1
  rw [div_eq_div_iff hE (one_sub_dz_ne hd hcs)]
  exact mobius_cleared d C S hcs

/-! ## The area formula and the phase cancellation -/

/-- `B N q c s k = (N/2)·Im C·(1 - q^{2N})/(1 - 2q^N k + q^{2N})`, with `k = cos(Nt)`. -/
noncomputable def B (N : ℕ) (q c s k : ℝ) : ℝ :=
  (N : ℝ) / 2 * CcIm c s q * ((1 - q ^ (2 * N)) / (1 - 2 * q ^ N * k + q ^ (2 * N)))

theorem neg_pow_two_mul (q : ℝ) (N : ℕ) : (-q) ^ (2 * N) = q ^ (2 * N) := by
  rw [pow_mul, pow_mul, neg_sq]

/-- For odd `N`, the two denominators differ only in the sign of the `cos Nt` term. -/
theorem B_neg_denom (N : ℕ) (hN : Odd N) (q c s k : ℝ) :
    B N (-q) c s k
      = (N : ℝ) / 2 * CcIm c s q
        * ((1 - q ^ (2 * N)) / (1 + 2 * q ^ N * k + q ^ (2 * N))) := by
  unfold B
  rw [CcIm_neg, neg_pow_two_mul, hN.neg_pow]
  ring_nf

/-- **The phase cancels.**  `1/A₊ + 1/A₋ = 2(1 + q^{2N})/K`, with `K` free of `k`. -/
theorem inv_add_inv {N : ℕ} (hN : Odd N) {q c s k : ℝ}
    (hK : (N : ℝ) / 2 * CcIm c s q * (1 - q ^ (2 * N)) ≠ 0)
    (hp : 1 - 2 * q ^ N * k + q ^ (2 * N) ≠ 0)
    (hm : 1 + 2 * q ^ N * k + q ^ (2 * N) ≠ 0) :
    1 / B N q c s k + 1 / B N (-q) c s k
      = 2 * (1 + q ^ (2 * N)) / ((N : ℝ) / 2 * CcIm c s q * (1 - q ^ (2 * N))) := by
  rw [B_neg_denom N hN, B]
  field_simp [hK, hp, hm]
  ring

/-! ## The carried geometry, and the theorem -/

/-- What the Poncelet/polar analysis and the root-of-unity evaluation supply. -/
structure Setup where
  /-- number of sides -/
  N : ℕ
  hN : Odd N
  hN3 : 3 ≤ N
  /-- the eccentricity parameter `d = c/(a+b)` -/
  d : ℝ
  hd0 : 0 < d
  hd : |d| < 1
  /-- the scale `R = ρ²a/b²` -/
  R : ℝ
  hR : 0 < R
  /-- `cos ϑ`, `sin ϑ` for `ϑ = 2π/N`, and `cos(Nt)` -/
  cth : ℝ
  sth : ℝ
  kt : ℝ
  hpy : cth ^ 2 + sth ^ 2 = 1
  hcth : cth < 1
  hsth : 0 < sth
  hkt : |kt| ≤ 1
  /-- the two polar areas -/
  Ap : ℝ
  Am : ℝ
  /-- **CARRIED** (the polar geometry, the Möbius normalisation, and the area lemma):
  `A_± = R²·B_N(±d, t)`. -/
  hAp : Ap = R ^ 2 * B N d cth sth kt
  hAm : Am = R ^ 2 * B N (-d) cth sth kt

namespace Setup

variable (S : Setup)

theorem d_sq_lt_one : S.d ^ 2 < 1 := by
  have h := abs_lt.mp S.hd
  nlinarith [h.1, h.2]

theorem d_lt_one : S.d < 1 := by
  have h := abs_lt.mp S.hd
  exact h.2

theorem N_pos : 0 < (S.N : ℝ) := by
  have h3 := S.hN3
  have h : 0 < S.N := by omega
  exact_mod_cast h

theorem pow_sq (m : ℕ) : S.d ^ (2 * m) = (S.d ^ m) ^ 2 := by
  rw [mul_comm, pow_mul]

theorem pow_lt_one' : S.d ^ (2 * S.N) < 1 := by
  have h3 := S.hN3
  exact pow_lt_one₀ S.hd0.le S.d_lt_one (by omega)

theorem CcIm_pos' : 0 < CcIm S.cth S.sth S.d :=
  CcIm_pos S.hd (le_of_lt S.hcth) S.hsth

theorem one_sub_pow_pos : 0 < 1 - S.d ^ (2 * S.N) := by
  linarith [S.pow_lt_one']

theorem K_pos : 0 < (S.N : ℝ) / 2 * CcIm S.cth S.sth S.d * (1 - S.d ^ (2 * S.N)) := by
  have h1 := S.N_pos
  have h2 := S.CcIm_pos'
  have h3 := S.one_sub_pow_pos
  positivity

theorem pow_N_lt_one : S.d ^ S.N < 1 := by
  have h3 := S.hN3
  exact pow_lt_one₀ S.hd0.le S.d_lt_one (by omega)

/-- `1 - 2uk + u² = (1-u)² + 2u(1-k)`, so both denominators are positive. -/
theorem denom_pos_plus : 0 < 1 - 2 * S.d ^ S.N * S.kt + S.d ^ (2 * S.N) := by
  have hdN : 0 < S.d ^ S.N := pow_pos S.hd0 S.N
  have hu := S.pow_N_lt_one
  have hk := abs_le.mp S.hkt
  have hsq := S.pow_sq S.N
  have hid : 1 - 2 * S.d ^ S.N * S.kt + S.d ^ (2 * S.N)
      = (1 - S.d ^ S.N) ^ 2 + 2 * S.d ^ S.N * (1 - S.kt) := by rw [hsq]; ring
  rw [hid]
  have h1 : 0 < (1 - S.d ^ S.N) ^ 2 := by positivity
  have h2 : 0 ≤ 2 * S.d ^ S.N * (1 - S.kt) := by nlinarith [hk.2, hdN]
  linarith

theorem denom_pos_minus : 0 < 1 + 2 * S.d ^ S.N * S.kt + S.d ^ (2 * S.N) := by
  have hdN : 0 < S.d ^ S.N := pow_pos S.hd0 S.N
  have hu := S.pow_N_lt_one
  have hk := abs_le.mp S.hkt
  have hsq := S.pow_sq S.N
  have hid : 1 + 2 * S.d ^ S.N * S.kt + S.d ^ (2 * S.N)
      = (1 - S.d ^ S.N) ^ 2 + 2 * S.d ^ S.N * (1 + S.kt) := by rw [hsq]; ring
  rw [hid]
  have h1 : 0 < (1 - S.d ^ S.N) ^ 2 := by positivity
  have h2 : 0 ≤ 2 * S.d ^ S.N * (1 + S.kt) := by nlinarith [hk.1, hdN]
  linarith

theorem B_pos_plus : 0 < B S.N S.d S.cth S.sth S.kt := by
  unfold B
  have h1 := S.N_pos
  have h2 := S.CcIm_pos'
  have h3 := S.one_sub_pow_pos
  have h4 := S.denom_pos_plus
  positivity

theorem B_pos_minus : 0 < B S.N (-S.d) S.cth S.sth S.kt := by
  rw [B_neg_denom S.N S.hN]
  have h1 := S.N_pos
  have h2 := S.CcIm_pos'
  have h3 := S.one_sub_pow_pos
  have h4 := S.denom_pos_minus
  positivity

/-- **CONJECTURE 1**: the sum of the reciprocal areas, with the phase gone. -/
theorem inv_sum :
    1 / S.Ap + 1 / S.Am
      = 2 * (1 + S.d ^ (2 * S.N))
        / (S.R ^ 2 * ((S.N : ℝ) / 2 * CcIm S.cth S.sth S.d
            * (1 - S.d ^ (2 * S.N)))) := by
  have hR2 : (S.R : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 S.hR.ne'
  have hBp := S.B_pos_plus.ne'
  have hBm := S.B_pos_minus.ne'
  have hB := inv_add_inv S.hN S.K_pos.ne' S.denom_pos_plus.ne' S.denom_pos_minus.ne'
  rw [S.hAp, S.hAm]
  have hsplit : 1 / (S.R ^ 2 * B S.N S.d S.cth S.sth S.kt)
      + 1 / (S.R ^ 2 * B S.N (-S.d) S.cth S.sth S.kt)
      = (1 / S.R ^ 2) * (1 / B S.N S.d S.cth S.sth S.kt
          + 1 / B S.N (-S.d) S.cth S.sth S.kt) := by
    field_simp
  rw [hsplit, hB]
  field_simp

/-- and in the write-up's displayed form. -/
theorem invariant :
    1 / S.Ap + 1 / S.Am
      = 4 * Dm S.cth S.d * (1 + S.d ^ (2 * S.N))
        / ((S.N : ℝ) * S.R ^ 2 * (1 - S.d ^ 2) ^ 2 * S.sth
            * (1 - S.d ^ (2 * S.N))) := by
  rw [S.inv_sum]
  have hD : Dm S.cth S.d ≠ 0 := Dm_ne_zero S.hd (le_of_lt S.hcth)
  have hR2 : (S.R : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 S.hR.ne'
  have hN := S.N_pos.ne'
  have hs := S.hsth.ne'
  have hdd := S.d_sq_lt_one
  have hone : (1 : ℝ) - S.d ^ 2 ≠ 0 := by intro h; linarith
  have hpow := S.one_sub_pow_pos.ne'
  unfold CcIm
  field_simp
  ring

/-- **The conjecture's actual assertion**: the invariant does not depend on the phase.
Two members of the family with the same `d`, `R` and `ϑ` but different `cos(Nt)` have the
same reciprocal-area sum. -/
theorem phase_independent (S' : Setup) (hN : S'.N = S.N) (hd : S'.d = S.d)
    (hR : S'.R = S.R) (hc : S'.cth = S.cth) (hs : S'.sth = S.sth) :
    1 / S'.Ap + 1 / S'.Am = 1 / S.Ap + 1 / S.Am := by
  rw [S'.inv_sum, S.inv_sum, hN, hd, hR, hc, hs]

end Setup

end Principia.MathDB.P352833
