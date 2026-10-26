import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# MathDB #365004 -- a fourth Poncelet family with stationary orthocenter (PROVED)

Write-up `mathdb-open-problems/problems/365004/solution.tex`,
*A fourth configuration with stationary orthocenter*, 21 September 2026
(duplicate formulation 372155).
Source: R. Garcia, M. Helman and D. Reznik, **Conjecture 1**, p. 6: a Poncelet triangle
family can have a stationary orthocenter only in the focal-X_4, MacBeath, or Dual
configurations.

The counterexample is the nested, noncircular pair

  `E : x^2/4 + y^2 = 1`,   `K : (x - 31/20)^2/(4/25) + y^2/(63/1600) = 1`,

whose Poncelet triangles all have orthocenter `H = (31/16, 0)` and are all acute.  Writing
`f = 4/5`, `g = 3/4`, `s = f+g = 31/20`, `p = fg = 3/5`, the vertices are `Z(a), Z(b), Z(c)`
with `Z(z) = (3z + z^{-1})/2` and `a, b, c` the unit-circle roots of
`P_lambda(z) = z^3 - (s+p lambda) z^2 + (p+s lambda) z - lambda`.

**What is proved here** is the algebraic core, the part that is neither classical nor
imported:

* `V_on_ellipse` -- `Z` carries the unit circle onto `E`;
* `brk_eq_zero` -- the write-up's bracket vanishes, **from Vieta alone**; the unit-circle
  condition is not used, which is a sharper statement than the write-up's own derivation;
* `altitude_factor` -- the factored expansion, a pure ring identity in `a, b, c` with no
  hypothesis at all beyond nonvanishing;
* `altitude` and `perp` -- hence `H = (31/16, 0)` lies on every altitude: in real
  coordinates `(H - A)` is perpendicular to `(B - C)`, and `Family` is symmetric in its
  three arguments so the same holds at the other two vertices.  **This is the stationary
  orthocenter, which is the whole point of the counterexample.**
* `tangency_scale` -- the write-up's tangency step, that the chord condition is exactly
  `1600` times the Vieta pair relation.

**The row's named gap is CLOSED (2026-09-23).**  `Family` -- that `a, b, c` lie on the unit
circle and satisfy the two Vieta relations of `P_lambda` -- used to be carried, on the
grounds that the write-up's Section 1 proves it by the argument principle for the
degree-three Blaschke product `B(z) = z(z-f)(z-g)/((1-fz)(1-gz))`, and Mathlib has neither
finite Blaschke products nor a winding-number argument in this form.  That was the wrong
reading of what the STATEMENT needs.  Two elementary facts replace the whole apparatus:

* `root_normSq_eq_one` -- `P_lambda` factors as `z(z-f)(z-g) - lambda(1-fz)(1-gz)`, and the
  modulus identity `|1-az|^2 - |z-a|^2 = (1-a^2)(1-|z|^2)` (here `normSq_sub_identity`) makes
  every factor on the left strictly smaller than its partner on the right inside the disc
  and strictly larger outside.  So a root can only have `|z| = 1`.  No winding number.
* `cubic_vieta` -- a monic complex cubic splits, from the fundamental theorem of algebra for
  one root plus the quadratic formula for the cofactor.  Campaign-agnostic.

Together: `family_exists` produces a `Family` with `abc = lambda` for EVERY `lambda` of
modulus one, so nothing in this module is conditional on an unproved hypothesis.
`family_nonempty` additionally exhibits the explicit member at `lambda = 1`, whose roots are
`1` and `(23 ± i sqrt 1071)/40` (`23^2 + 1071 = 1600`).

**The SECOND of the two remaining links is now closed (2026-09-24), and it had been MISPRICED
here.**  This header used to say that stating "`(E, K)` is none of the three configurations of
Conjecture 1" needs definitions of the focal-X_4, MacBeath and Dual families "which are not in
Mathlib".  The write-up's Section 4 supplies them: it distinguishes the three families by their
Euclidean conic configurations -- outer conic a circle, inner conic a circle, the two conics
concentric -- citing [special, Sections 3--4] for that identification.  **A definition the source
supplies is not a Mathlib gap.**  `section_four` is Section 4 in full, and it spends the three
facts this module had already proved without saying what they were for (`Eset_not_circle`,
`Kset_not_circle`, `not_concentric`) plus `H_not_focus` and `H_mem_KsetInterior`.  The three
predicates are TRANSCRIBED from the cited source, not derived: the projective definitions and
their equivalence with these Euclidean conditions are not formalised.

**THE CONTINUITY ARGUMENT IS GONE, REPLACED BY A DIRECT ONE (2026-09-25).**  The write-up closes
Section 2 with *"a tangent line cannot cross the centre of a nondegenerate ellipse; continuity
preserves the interior side"* -- it obtains the containment of the caustic by deforming along the
family.  Nothing here deforms anything.  The containment follows from one elementary fact about
chords: **a line through two points of the unit circle meets the OPEN disc only STRICTLY BETWEEN
them** (`chord_param_mem_disc`, via the identity `|a + s(b-a)|^2 - 1 = s(s-1)|b-a|^2`).  Since the
caustic is strictly inside the disc (`K0set_inside_unit_disc`, largest squared distance
`1521/1600`), a side that supports the caustic touches it short of the far vertex, and
`vertex_le_of_touch` then puts the near vertex on the caustic's side -- by linear arithmetic, for
ONE triangle, with no family and no limit.  `K0set_subset_triangle` assembles the three sides into
containment by barycentric coordinates, `sdet_of_lineTD` being the bridge that reads the sign of a
signed area as the side of a line.

`family_pair_tangency` supplies the other half that was missing: `tangency_scale` was a ring
identity with nothing tying it to a family member, and eliminating `c` from the two `Family`
relations produces exactly its expression -- unconditionally, because multiplying rather than
dividing avoids needing `ab != 5/3`.

**ALL THREE ARE NOW INSTANTIATED (2026-09-25), AND SO IS THE TRANSPORT TO THE PHYSICAL PLANE.**
(i) The supporting branch is chosen by picking the right SQUARE ROOT of `ab`, not by rotating the
angle: `-u` negates both `cos th = Re u` and `d` at once, so `side_data` case-splits on the branch
and calls `side_data_aux` either way.  (ii) `sdet_ne_zero_of_circle` -- three distinct points of a
circle are not collinear -- reuses the chord identity already here, since collinearity writes
`C = A + t(B-A)` and `|A + t(B-A)|^2 - 1 = t(t-1)|B-A|^2` forces `t = 0` or `t = 1`.  (iii) The
complex-to-real passage is `tangency_eq_of_pair_rel`, and it is ONE `linear_combination`: with
`q = 2du` and `r = u^2` the pair relation equals `u^2` times four times the squared tangency
condition, the only input being `u^2 + 1 = 2(Re u)u`.  `caustic_inside_family_triangle` composes
them.

**The physical plane costs nothing extra.**  Section 1 of the write-up says *"apply `(x,y)=(2X,Y)`
to the unit circle; the inverse image of `K` is `K_0`"* -- so the transport is AFFINE, and
`Z_eq_affine` is why: on the unit circle `z^{-1} = conj z`, so `Z(z) = (3z + z^{-1})/2` is exactly
`(2 Re z, Im z)`.  `mem_Kset_iff_halved` is an IDENTITY rather than an implication, because
`(X/2 - 31/40)^2/(1/25)` and `(X - 31/20)^2/(4/25)` are the same expression.  Hence
`Kset_side_touch` (the write-up's *"and its affine image touches `K`"*) and
`Kset_inside_family_triangle`.

**BOTH FAMILY-LEVEL ITEMS ARE NOW PROVED, AND NEITHER NEEDED THE WINDING ARGUMENT (2026-09-25).**
This paragraph used to list them as the reason the row was not counted; `counterexample` at the
foot of the file now assembles the whole refutation and the module carries nothing.

**(a) Distinctness.**  The write-up derives it from the Blaschke product's *"strictly positive
argument derivative"* together with its *"total argument change `6 pi`"*.  The second is a winding
statement and is exactly what `root_normSq_eq_one` and `cubic_vieta` were built to avoid -- but
**only the first is needed, and it is a rational identity.**  A repeated root makes the Wronskian
`W = N' D - N D'` vanish, and `blaschke_wronskian` puts `W` in the closed form
`Pf Pg + z(1-f^2) Pg + z(1-g^2) Pf` with `Pf = (z-f)(1-fz)`.  On the circle `Pf = z |z-f|^2`
(`mul_conj_line`), so `W = z^2 * (|z-f|^2|z-g|^2 + (9/25)|z-g|^2 + (7/16)|z-f|^2)`, a strictly
positive real times `z^2`.  **Pointwise and algebraic: no argument principle, no total argument
change, no winding number.**

**(b) Fullness.**  Given `z` on the circle, `lambda = N(z)/D(z)` works.  The denominator is nonzero
for a reason needing no estimate: `1 - (4/5)z = 0` would force `z = 5/4`, whose `normSq` is `25/16`.
`normSq lambda = 1` because `normSq N = normSq D` on the circle (`normSq_one_sub_mul`, a one-line
consequence of `mul_conj_line`), `z` is then a root of `P_lambda` by construction, and the three
roots of a monic cubic are its Vieta triple, so `z` is one of them.

**What `counterexample` says.**  `E` and `K` carry a Poncelet triangle family -- full,
nondegenerate, inscribed in `E`, circumscribing `K` -- every member of which has its orthocenter
at the SAME point `(31/16, 0)`, and the pair is in none of the three configurations.  The side
clause is stated for the pair `(a, b)` inside a `forall a b c, Family a b c -> ...`, which is not
a weakening: `Family` is rotation-symmetric, so the rotated family supplies the other two sides.

**Honest about the transcription.**  Section 4's three predicates are taken from the cited source,
not derived here; the projective definitions of the three families and their equivalence with these
Euclidean conditions are not formalised.  That is a citation, not a gap in the argument, and it is
the same status the row has recorded since 2026-09-24.

**Upstream status.**  The collaborator's own state for this problem is
`full-proof-source-audit-pending`, and their write-up assigns itself zero new credit pending
inspection of the journal final; it credits the general orthocenter-locus semiaxis formula
to the prior source.  Nothing certified here depends on that audit.

Values checked first in `Campaigns/MathDB-Formalization/verify_365004.py`.
-/

namespace Principia.MathDB.P365004

open Complex

variable {a b c z : ℂ}

/-- The write-up's vertex map `Z(z) = (3z + z⁻¹)/2`, carrying the unit circle onto the
ellipse `E : x²/4 + y² = 1`. -/
noncomputable def V (z : ℂ) : ℂ := (3 * z + z⁻¹) / 2

/-- Its conjugate on the unit circle. -/
noncomputable def W (z : ℂ) : ℂ := (3 * z⁻¹ + z) / 2

theorem conj_V (hz : (starRingEnd ℂ) z = z⁻¹) : (starRingEnd ℂ) (V z) = W z := by
  rw [V, W, map_div₀, map_add, map_mul, map_inv₀, hz, inv_inv]
  simp [map_ofNat]

theorem normSq_eq_one (hz0 : z ≠ 0) (hz : (starRingEnd ℂ) z = z⁻¹) : normSq z = 1 := by
  have h := Complex.mul_conj z
  rw [hz, mul_inv_cancel₀ hz0] at h
  exact_mod_cast h.symm

theorem V_re (hz : (starRingEnd ℂ) z = z⁻¹) : (V z).re = 2 * z.re := by
  have h : V z = (3 * z + (starRingEnd ℂ) z) / 2 := by rw [V, hz]
  rw [h]
  simp
  ring

theorem V_im (hz : (starRingEnd ℂ) z = z⁻¹) : (V z).im = z.im := by
  have h : V z = (3 * z + (starRingEnd ℂ) z) / 2 := by rw [V, hz]
  rw [h]
  simp
  ring

/-- **The vertices lie on `E`.** -/
theorem V_on_ellipse (hz0 : z ≠ 0) (hz : (starRingEnd ℂ) z = z⁻¹) :
    (V z).re ^ 2 / 4 + (V z).im ^ 2 = 1 := by
  have hn := normSq_eq_one hz0 hz
  rw [Complex.normSq_apply] at hn
  rw [V_re hz, V_im hz]
  linear_combination hn

/-- The Vieta data of the write-up's cubic `P_λ(z) = z³ - (s+pλ)z² + (p+sλ)z - λ` at
`λ = abc`, with `s = f+g = 31/20` and `p = fg = 3/5` for `f = 4/5`, `g = 3/4`, together
with the three vertices lying on the unit circle. -/
structure Family (a b c : ℂ) : Prop where
  ne_a : a ≠ 0
  ne_b : b ≠ 0
  ne_c : c ≠ 0
  ua : (starRingEnd ℂ) a = a⁻¹
  ub : (starRingEnd ℂ) b = b⁻¹
  uc : (starRingEnd ℂ) c = c⁻¹
  sum : a + b + c = 31 / 20 + (3 / 5) * (a * b * c)
  pair : a * b + b * c + c * a = 3 / 5 + (31 / 20) * (a * b * c)

/-- The write-up's bracket, with `A = 3/2`, `D = 1/2`, `h = 31/16`. -/
noncomputable def brk (a L s1 s2 : ℂ) : ℂ :=
  ((1 / 2) * L - (3 / 2) * a) * (31 / 16) + ((3 / 2) * L - (1 / 2) * a) * (31 / 16)
    - 2 * (3 / 2) * (1 / 2) * L * a + (5 / 2) * s1 * a - (5 / 2) * s2
    + 2 * (3 / 2) * (1 / 2)

/-- **The bracket vanishes**, from Vieta alone -- the unit-circle condition is not used. -/
theorem brk_eq_zero (h : Family a b c) :
    brk a (a * b * c) (a + b + c) (a * b + b * c + c * a) = 0 := by
  rw [brk]
  linear_combination ((5 : ℂ) / 2 * a) * h.sum - ((5 : ℂ) / 2) * h.pair

/-- The write-up's factored expansion.  Pure algebra: no hypothesis on `a, b, c` beyond
their being nonzero. -/
theorem altitude_factor (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ((31 : ℂ) / 16 - V a) * (W b - W c) + ((31 : ℂ) / 16 - W a) * (V b - V c)
      = ((b - c) / (a * b * c)) * brk a (a * b * c) (a + b + c) (a * b + b * c + c * a) := by
  rw [V, V, V, W, W, W, brk]
  field_simp
  ring

/-- **The altitude identity**: the fixed point `h = 31/16` lies on every altitude. -/
theorem altitude (h : Family a b c) :
    ((31 : ℂ) / 16 - V a) * (W b - W c) + ((31 : ℂ) / 16 - W a) * (V b - V c) = 0 := by
  rw [altitude_factor h.ne_a h.ne_b h.ne_c, brk_eq_zero h, mul_zero]

theorem re_mul_conj (u v : ℂ) : (u * (starRingEnd ℂ) v).re = u.re * v.re + u.im * v.im := by
  simp [Complex.mul_re]

theorem re_conj_mul (u v : ℂ) : ((starRingEnd ℂ) u * v).re = u.re * v.re + u.im * v.im := by
  simp [Complex.mul_re]

/-- **`H = (31/16, 0)` is the orthocenter**: `(H - A) ⟂ (B - C)`, in real coordinates.
`Family` is symmetric in its three arguments, so the same holds at the other two vertices. -/
theorem perp (h : Family a b c) :
    ((31 : ℂ) / 16 - V a).re * (V b - V c).re + ((31 : ℂ) / 16 - V a).im * (V b - V c).im
      = 0 := by
  have hconj : (starRingEnd ℂ) (V b - V c) = W b - W c := by
    rw [map_sub, conj_V h.ub, conj_V h.uc]
  have hA : (starRingEnd ℂ) ((31 : ℂ) / 16 - V a) = (31 : ℂ) / 16 - W a := by
    rw [map_sub, conj_V h.ua, map_div₀]
    simp [map_ofNat]
  have key := altitude h
  rw [← hconj, ← hA] at key
  have hre := congrArg Complex.re key
  simp only [Complex.add_re, Complex.zero_re, re_mul_conj, re_conj_mul] at hre
  linarith

/-- The write-up's tangency step: the chord condition is exactly `1600` times the pair
relation coming from Vieta.  A ring identity in `q = a+b` and `r = ab`. -/
theorem tangency_scale (q r : ℂ) :
    1600 * q ^ 2 - 2480 * q * (r + 1) + 897 * (r + 1) ^ 2 + 63 * (r - 1) ^ 2
      = 1600 * (q ^ 2 - (31 / 20) * (1 + r) * q + (3 / 5) * (1 + r ^ 2)
          + (417 / 400) * r) := by
  ring

/-! ### The roots really are on the unit circle — elementarily

The row's note named its gap as "Mathlib has no finite Blaschke products and no
winding-number argument in this form".  That gap is not needed.  The write-up's cubic
factors EXACTLY, with no restriction to the circle,

  `P_λ(z) = z(z-f)(z-g) - λ(1-fz)(1-gz)`,

and for real `0 < a < 1` one has the four-line identity

  `normSq (1 - a z) - normSq (z - a) = (1 - a²)(1 - normSq z)`.

So inside the disc every factor `|z-a|` is strictly smaller than `|1-az|`, and `|z| < 1`
as well, making `|z(z-f)(z-g)| < |λ(1-fz)(1-gz)|`; outside, every inequality reverses.
Hence a root can only have `normSq z = 1`. -/

/-- The Blaschke modulus identity, by coordinates. -/
theorem normSq_sub_identity (a : ℝ) (w : ℂ) :
    normSq (1 - (a : ℂ) * w) - normSq (w - (a : ℂ))
      = (1 - a ^ 2) * (1 - normSq w) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem normSq_lt (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (w : ℂ) (hw : normSq w < 1) :
    normSq (w - (a : ℂ)) < normSq (1 - (a : ℂ) * w) := by
  have h := normSq_sub_identity a w
  have ha2 : 0 < 1 - a ^ 2 := by nlinarith
  have hpos : 0 < (1 - a ^ 2) * (1 - normSq w) := mul_pos ha2 (by linarith)
  linarith

theorem normSq_gt (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (w : ℂ) (hw : 1 < normSq w) :
    normSq (1 - (a : ℂ) * w) < normSq (w - (a : ℂ)) := by
  have h := normSq_sub_identity a w
  have ha2 : 0 < 1 - a ^ 2 := by nlinarith
  have hneg : (1 - a ^ 2) * (1 - normSq w) < 0 :=
    mul_neg_of_pos_of_neg ha2 (by linarith)
  linarith

/-- **Every root of `P_λ` lies on the unit circle**, for every `λ` of modulus one.  The
write-up's Blaschke/winding argument is not needed. -/
theorem root_normSq_eq_one (lam w : ℂ) (hlam : normSq lam = 1)
    (hroot : w * (w - ((4 : ℝ) / 5 : ℝ)) * (w - ((3 : ℝ) / 4 : ℝ))
      = lam * ((1 - ((4 : ℝ) / 5 : ℝ) * w) * (1 - ((3 : ℝ) / 4 : ℝ) * w))) :
    normSq w = 1 := by
  have hkey := congrArg normSq hroot
  simp only [map_mul, hlam, one_mul] at hkey
  have p1 : 0 ≤ normSq (w - ((4 : ℝ) / 5 : ℝ)) := normSq_nonneg _
  have p2 : 0 ≤ normSq (w - ((3 : ℝ) / 4 : ℝ)) := normSq_nonneg _
  have p3 : 0 ≤ normSq w := normSq_nonneg _
  rcases lt_trichotomy (normSq w) 1 with h | h | h
  · exfalso
    have h1 := normSq_lt (4 / 5) (by norm_num) (by norm_num) w h
    have h2 := normSq_lt (3 / 4) (by norm_num) (by norm_num) w h
    have q1 : 0 < normSq (1 - ((4 : ℝ) / 5 : ℝ) * w) := lt_of_le_of_lt p1 h1
    have hn : normSq (w - ((4 : ℝ) / 5 : ℝ)) * normSq (w - ((3 : ℝ) / 4 : ℝ))
        < normSq (1 - ((4 : ℝ) / 5 : ℝ) * w) * normSq (1 - ((3 : ℝ) / 4 : ℝ) * w) :=
      mul_lt_mul' (le_of_lt h1) h2 p2 q1
    have hp : 0 ≤ normSq (w - ((4 : ℝ) / 5 : ℝ)) * normSq (w - ((3 : ℝ) / 4 : ℝ)) :=
      mul_nonneg p1 p2
    have hmul : normSq w * (normSq (w - ((4 : ℝ) / 5 : ℝ))
          * normSq (w - ((3 : ℝ) / 4 : ℝ)))
        ≤ 1 * (normSq (w - ((4 : ℝ) / 5 : ℝ)) * normSq (w - ((3 : ℝ) / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_right (le_of_lt h) hp
    nlinarith [hkey, hn, hmul]
  · exact h
  · exfalso
    have h1 := normSq_gt (4 / 5) (by norm_num) (by norm_num) w h
    have h2 := normSq_gt (3 / 4) (by norm_num) (by norm_num) w h
    have q1 : 0 < normSq (w - ((4 : ℝ) / 5 : ℝ)) :=
      lt_of_le_of_lt (normSq_nonneg _) h1
    have hn : normSq (1 - ((4 : ℝ) / 5 : ℝ) * w) * normSq (1 - ((3 : ℝ) / 4 : ℝ) * w)
        < normSq (w - ((4 : ℝ) / 5 : ℝ)) * normSq (w - ((3 : ℝ) / 4 : ℝ)) :=
      mul_lt_mul' (le_of_lt h1) h2 (normSq_nonneg _) q1
    have hp : 0 ≤ normSq (w - ((4 : ℝ) / 5 : ℝ)) * normSq (w - ((3 : ℝ) / 4 : ℝ)) :=
      mul_nonneg p1 p2
    have hmul : 1 * (normSq (w - ((4 : ℝ) / 5 : ℝ))
          * normSq (w - ((3 : ℝ) / 4 : ℝ)))
        ≤ normSq w * (normSq (w - ((4 : ℝ) / 5 : ℝ))
          * normSq (w - ((3 : ℝ) / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_right (le_of_lt h) hp
    nlinarith [hkey, hn, hmul]

/-! ### `Family` is not vacuous — an explicit member at `λ = 1`

At `λ = 1` the cubic is `z³ - (43/20)z² + (43/20)z - 1`, which has `z = 1` as a root and
factors as `(z-1)(z² - (23/20)z + 1)`.  The remaining roots are `(23 ± i√1071)/40`, and
`23² + 1071 = 1600`, so both lie on the unit circle.  Exhibiting them rules out the one way
the theorems above could be empty. -/

noncomputable def r1071 : ℝ := Real.sqrt 1071

theorem r1071_sq : r1071 ^ 2 = 1071 := Real.sq_sqrt (by norm_num)

noncomputable def bWit : ℂ := ⟨23 / 40, r1071 / 40⟩
noncomputable def cWit : ℂ := ⟨23 / 40, -(r1071 / 40)⟩

theorem conj_eq_inv_of_normSq_one {z : ℂ} (h : normSq z = 1) :
    (starRingEnd ℂ) z = z⁻¹ := by
  rw [Complex.inv_def, h]
  simp

theorem normSq_bWit : normSq bWit = 1 := by
  simp only [Complex.normSq_apply, bWit]
  nlinarith [r1071_sq]

theorem normSq_cWit : normSq cWit = 1 := by
  simp only [Complex.normSq_apply, cWit]
  nlinarith [r1071_sq]

theorem bc_eq_one : bWit * cWit = 1 := by
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, bWit, cWit, Complex.one_re, Complex.one_im] <;>
    nlinarith [r1071_sq]

theorem b_add_c : bWit + cWit = 23 / 20 := by
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, bWit, cWit] <;> ring

/-- **`Family` has a member**, so `altitude` and `perp` are not vacuous. -/
theorem family_nonempty : Family 1 bWit cWit := by
  have hb : bWit ≠ 0 := by
    intro h
    have : normSq bWit = 0 := by rw [h]; simp
    rw [normSq_bWit] at this
    norm_num at this
  have hc : cWit ≠ 0 := by
    intro h
    have : normSq cWit = 0 := by rw [h]; simp
    rw [normSq_cWit] at this
    norm_num at this
  refine ⟨one_ne_zero, hb, hc, by simp, conj_eq_inv_of_normSq_one normSq_bWit,
    conj_eq_inv_of_normSq_one normSq_cWit, ?_, ?_⟩
  · linear_combination b_add_c - ((3 : ℂ) / 5) * bc_eq_one
  · linear_combination b_add_c - ((11 : ℂ) / 20) * bc_eq_one


/-! ### `Family` EXISTS FOR EVERY `λ` — the carried hypothesis is discharged

The write-up obtains the three unit-circle roots from the argument principle for the
Blaschke product `B(z) = z(z-f)(z-g)/((1-fz)(1-gz))`.  None of that is needed.  A monic
complex cubic splits by the fundamental theorem of algebra plus the quadratic formula
(`cubic_vieta`); its three roots satisfy the two Vieta relations by construction; and
`root_normSq_eq_one` puts every one of them on the unit circle.  So `Family` is not a
hypothesis at all — `family_exists` produces a member for every `λ` of modulus one. -/

/-- **Every monic complex cubic splits**, in the Vieta sense.  Elementary: one root from
the fundamental theorem of algebra, the other two from the quadratic formula applied to the
cofactor `z² + (B₂+a)z + (B₁ + aB₂ + a²)`.  Campaign-agnostic. -/
theorem cubic_vieta (B2 B1 B0 : ℂ) :
    ∃ a b c : ℂ, a + b + c = -B2 ∧ a * b + b * c + c * a = B1 ∧ a * b * c = -B0 := by
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a ^ 3 + B2 * a ^ 2 + B1 * a + B0 = 0 := by
    have hdeg : (Polynomial.X ^ 3 + Polynomial.C B2 * Polynomial.X ^ 2
        + Polynomial.C B1 * Polynomial.X + Polynomial.C B0 : Polynomial ℂ).degree = 3 := by
      compute_degree!
    obtain ⟨z, hz⟩ := Complex.exists_root
      (f := Polynomial.X ^ 3 + Polynomial.C B2 * Polynomial.X ^ 2
        + Polynomial.C B1 * Polynomial.X + Polynomial.C B0)
      (by rw [hdeg]; norm_num)
    exact ⟨z, by simpa [Polynomial.IsRoot] using hz⟩
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = (B2 + a) ^ 2 - 4 * (B1 + a * B2 + a ^ 2) :=
    IsAlgClosed.exists_pow_nat_eq _ (by norm_num)
  refine ⟨a, (-(B2 + a) + s) / 2, (-(B2 + a) - s) / 2, by ring, ?_, ?_⟩
  · linear_combination (-1 / 4 : ℂ) * hs
  · linear_combination (-a / 4 : ℂ) * hs + ha

/-- A number satisfying the Vieta relations is a root of the corresponding cubic. -/
theorem root_of_vieta {B2 B1 B0 a b c : ℂ} (h1 : a + b + c = -B2)
    (h2 : a * b + b * c + c * a = B1) (h3 : a * b * c = -B0) :
    a ^ 3 + B2 * a ^ 2 + B1 * a + B0 = 0 := by
  linear_combination a ^ 2 * h1 - a * h2 + h3

/-- The write-up's factorisation `P_λ(z) = z(z-f)(z-g) - λ(1-fz)(1-gz)`, `f = 4/5`,
`g = 3/4`.  A ring identity. -/
theorem P_factor (lam z : ℂ) :
    z ^ 3 + (-(31 / 20 + (3 / 5) * lam)) * z ^ 2 + (3 / 5 + (31 / 20) * lam) * z + (-lam)
      = z * (z - ((4 : ℝ) / 5 : ℝ)) * (z - ((3 : ℝ) / 4 : ℝ))
        - lam * ((1 - ((4 : ℝ) / 5 : ℝ) * z) * (1 - ((3 : ℝ) / 4 : ℝ) * z)) := by
  push_cast
  ring

/-- **The carried hypothesis is discharged.**  For every `λ` on the unit circle there are
`a, b, c` forming a `Family` with `abc = λ`.  No Blaschke product, no winding number. -/
theorem family_exists (lam : ℂ) (hlam : normSq lam = 1) :
    ∃ a b c : ℂ, Family a b c ∧ a * b * c = lam := by
  obtain ⟨a, b, c, h1, h2, h3⟩ :=
    cubic_vieta (-(31 / 20 + (3 / 5) * lam)) (3 / 5 + (31 / 20) * lam) (-lam)
  have habc : a * b * c = lam := by rw [h3]; ring
  have key : ∀ w : ℂ, w ^ 3 + (-(31 / 20 + (3 / 5) * lam)) * w ^ 2
      + (3 / 5 + (31 / 20) * lam) * w + (-lam) = 0 → normSq w = 1 := by
    intro w hw
    refine root_normSq_eq_one lam w hlam ?_
    have hp := P_factor lam w
    rw [hw] at hp
    linear_combination -hp
  have ra : normSq a = 1 := key a (root_of_vieta h1 h2 h3)
  have rb : normSq b = 1 :=
    key b (root_of_vieta (a := b) (b := c) (c := a)
      (by linear_combination h1) (by linear_combination h2) (by linear_combination h3))
  have rc : normSq c = 1 :=
    key c (root_of_vieta (a := c) (b := a) (c := b)
      (by linear_combination h1) (by linear_combination h2) (by linear_combination h3))
  have na : a ≠ 0 := by intro h; rw [h] at ra; simp at ra
  have nb : b ≠ 0 := by intro h; rw [h] at rb; simp at rb
  have nc : c ≠ 0 := by intro h; rw [h] at rc; simp at rc
  refine ⟨a, b, c, ⟨na, nb, nc, conj_eq_inv_of_normSq_one ra,
    conj_eq_inv_of_normSq_one rb, conj_eq_inv_of_normSq_one rc, ?_, ?_⟩, habc⟩
  · linear_combination h1 - ((3 : ℂ) / 5) * habc
  · linear_combination h2 - ((31 : ℂ) / 20) * habc

/-! ### Section 1's nesting, and Section 4's exclusion of the three configurations

The row's remaining gap was recorded as *"that `(E,K)` is none of the three configurations,
which would need definitions of focal-`X₄`, MacBeath and Dual families"*.  Reading Section 4
settles what that costs.  **The write-up excludes each family by a EUCLIDEAN CONDITION ON THE
CONIC PAIR ALONE** — MacBeath needs the outer conic to be a circle, focal-`X₄` needs the inner
conic to be a circle, Dual needs the two to be concentric — and each of those is a property of
`E` and `K` and nothing else.  So the exclusion is formalisable today, and what stays cited is
only the correspondence *family ↔ condition*, which is the DEFINITION given in
[special, §§3–4].

**What is deliberately NOT done: defining `IsMacBeath` to mean "the outer conic is a circle".**
That would make the exclusion true by definition and prove nothing.  The three theorems below
are about the explicit conic pair — `E` is not a circle, `K` is not a circle, and they have no
common centre — with the correspondence left visibly as a citation.  `Eset_center_unique` is
what makes the concentricity statement airtight rather than a statement about one chosen
centre.

Section 1's nesting was also unformalised and is one inequality: with `v = cos t` the caustic's
squared distance to the origin is `(v² + 496v + 1024)/1600`, increasing on `[-1,1]`, so at most
`1521/1600 < 1`.

**What is still missing after this**: Section 2's tangency geometry — that the chord of the unit
circle through `a, b` IS the real line `X cosθ + Y sinθ = d` and that the write-up's condition is
tangency of that line to `K₀` (`tangency_scale` already certifies the algebraic identity behind
it) — and the continuity argument that every family triangle CONTAINS the caustic.  Neither is
carried as a hypothesis; the module still has no `Prop` parameter. -/

section Witness

/-- The outer conic `E : x²/4 + y² = 1`. -/
def Eset : Set (ℝ × ℝ) := {P | P.1 ^ 2 / 4 + P.2 ^ 2 = 1}

/-- The inner conic `K : (x − 31/20)²/(4/25) + y²/(63/1600) = 1`. -/
def Kset : Set (ℝ × ℝ) := {P | (P.1 - 31 / 20) ^ 2 / (4 / 25) + P.2 ^ 2 / (63 / 1600) = 1}

/-- The open region bounded by `K`. -/
def KsetInterior : Set (ℝ × ℝ) :=
  {P | (P.1 - 31 / 20) ^ 2 / (4 / 25) + P.2 ^ 2 / (63 / 1600) < 1}

/-- `c` is a centre of symmetry of `S`. -/
def IsCenter (S : Set (ℝ × ℝ)) (c : ℝ × ℝ) : Prop :=
  ∀ P : ℝ × ℝ, P ∈ S ↔ (2 * c.1 - P.1, 2 * c.2 - P.2) ∈ S

/-- The write-up's parametrisation of the caustic pulled back by `(x,y) = (2X, Y)`. -/
noncomputable def K0pt (t : ℝ) : ℝ × ℝ :=
  (31 / 40 + (1 / 5) * Real.cos t, (3 * Real.sqrt 7 / 40) * Real.sin t)

theorem sqrt7_sq : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)

/-- **Section 1's nesting.**  `X² + Y² = (v² + 496v + 1024)/1600` with `v = cos t`, and the
numerator is increasing on `[-1,1]`, so the maximum is `1521/1600 < 1`.  Hence the caustic is
strictly inside the unit circle, and `K` strictly inside `E`. -/
theorem K0_inside_unit_disc (t : ℝ) : (K0pt t).1 ^ 2 + (K0pt t).2 ^ 2 < 1 := by
  have hpy : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
  have h1 : Real.cos t ≤ 1 := Real.cos_le_one t
  have h2 : Real.cos t ^ 2 ≤ 1 := Real.cos_sq_le_one t
  have h7 : Real.sqrt 7 ^ 2 = 7 := sqrt7_sq
  simp only [K0pt]
  nlinarith [hpy, h1, h2, h7]

/-- `E` is symmetric about the origin. -/
theorem Eset_center : IsCenter Eset (0, 0) := by
  intro P
  simp only [Eset, Set.mem_setOf_eq]
  constructor <;> intro h <;> nlinarith [h]

/-- `K` is symmetric about `(31/20, 0)`. -/
theorem Kset_center : IsCenter Kset (31 / 20, 0) := by
  intro P
  simp only [Kset, Set.mem_setOf_eq]
  constructor <;> intro h <;> nlinarith [h]

/-- The origin is the ONLY centre of `E`: the two vertices `(±2, 0)` force `c₁ = 0` and then
`(0, ±1)` force `c₂ = 0`. -/
theorem Eset_center_unique {c : ℝ × ℝ} (h : IsCenter Eset c) : c = (0, 0) := by
  have h1 : ((2 : ℝ), (0 : ℝ)) ∈ Eset := by simp only [Eset, Set.mem_setOf_eq]; norm_num
  have h2 : ((-2 : ℝ), (0 : ℝ)) ∈ Eset := by simp only [Eset, Set.mem_setOf_eq]; norm_num
  have e1 := (h (2, 0)).mp h1
  have e2 := (h (-2, 0)).mp h2
  simp only [Eset, Set.mem_setOf_eq] at e1 e2
  have hc1 : c.1 = 0 := by nlinarith [e1, e2]
  have h3 : ((0 : ℝ), (1 : ℝ)) ∈ Eset := by simp only [Eset, Set.mem_setOf_eq]; norm_num
  have e3 := (h (0, 1)).mp h3
  simp only [Eset, Set.mem_setOf_eq] at e3
  have hc2 : c.2 = 0 := by rw [hc1] at e3; nlinarith [e3]
  exact Prod.ext hc1 hc2

/-- The origin is NOT a centre of `K`: it sends the vertex `(31/20 + 2/5, 0)` to a point at
squared normalised distance `1225/16`. -/
theorem Kset_not_center_zero : ¬ IsCenter Kset (0, 0) := by
  intro h
  have h1 : ((31 / 20 + 2 / 5 : ℝ), (0 : ℝ)) ∈ Kset := by
    simp only [Kset, Set.mem_setOf_eq]; norm_num
  have e1 := (h (31 / 20 + 2 / 5, 0)).mp h1
  simp only [Kset, Set.mem_setOf_eq] at e1
  norm_num at e1

/-- **The Dual configuration is excluded**: `E` and `K` have no common centre.  Its definition
in the cited classification requires the two conics to be concentric. -/
theorem not_concentric : ¬ ∃ c : ℝ × ℝ, IsCenter Eset c ∧ IsCenter Kset c := by
  rintro ⟨c, hE, hK⟩
  rw [Eset_center_unique hE] at hK
  exact Kset_not_center_zero hK

/-- **The MacBeath configuration is excluded**: `E` is not a circle.  A circle through
`(±2, 0)` and `(0, ±1)` would need radius squared both `4` and `1`. -/
theorem Eset_not_circle :
    ¬ ∃ cx cy rho : ℝ, Eset = {P : ℝ × ℝ | (P.1 - cx) ^ 2 + (P.2 - cy) ^ 2 = rho ^ 2} := by
  rintro ⟨cx, cy, rho, hEq⟩
  have mem : ∀ P : ℝ × ℝ, P ∈ Eset → (P.1 - cx) ^ 2 + (P.2 - cy) ^ 2 = rho ^ 2 := by
    intro P hP
    have := hEq ▸ hP
    exact this
  have e1 := mem (2, 0) (by simp only [Eset, Set.mem_setOf_eq]; norm_num)
  have e2 := mem (-2, 0) (by simp only [Eset, Set.mem_setOf_eq]; norm_num)
  have e3 := mem (0, 1) (by simp only [Eset, Set.mem_setOf_eq]; norm_num)
  have e4 := mem (0, -1) (by simp only [Eset, Set.mem_setOf_eq]; norm_num)
  simp only at e1 e2 e3 e4
  have hcx : cx = 0 := by nlinarith [e1, e2]
  have hcy : cy = 0 := by nlinarith [e3, e4]
  rw [hcx, hcy] at e1 e3
  nlinarith [e1, e3]

/-- **The focal-`X₄` configuration is excluded**: `K` is not a circle.  Its two squared
semiaxes are `4/25` and `63/1600`. -/
theorem Kset_not_circle :
    ¬ ∃ cx cy rho : ℝ, Kset = {P : ℝ × ℝ | (P.1 - cx) ^ 2 + (P.2 - cy) ^ 2 = rho ^ 2} := by
  rintro ⟨cx, cy, rho, hEq⟩
  have mem : ∀ P : ℝ × ℝ, P ∈ Kset → (P.1 - cx) ^ 2 + (P.2 - cy) ^ 2 = rho ^ 2 := by
    intro P hP
    have := hEq ▸ hP
    exact this
  have hs : Real.sqrt 63 ^ 2 = 63 := Real.sq_sqrt (by norm_num)
  have e1 := mem (31 / 20 + 2 / 5, 0) (by simp only [Kset, Set.mem_setOf_eq]; norm_num)
  have e2 := mem (31 / 20 - 2 / 5, 0) (by simp only [Kset, Set.mem_setOf_eq]; norm_num)
  have e3 := mem (31 / 20, Real.sqrt 63 / 40)
      (by simp only [Kset, Set.mem_setOf_eq]; rw [div_pow, hs]; norm_num)
  have e4 := mem (31 / 20, -(Real.sqrt 63 / 40))
      (by simp only [Kset, Set.mem_setOf_eq]; rw [neg_pow, div_pow, hs]; norm_num)
  simp only at e1 e2 e3 e4
  have hcx : cx = 31 / 20 := by nlinarith [e1, e2]
  have hcy : cy = 0 := by nlinarith [e3, e4, hs]
  rw [hcx, hcy] at e1 e3
  nlinarith [e1, e3, hs]

/-- **`H` is not a focus of `E`.**  The foci are `(±√3, 0)` and `(31/16)² ≠ 3`. -/
theorem H_not_focus (s : ℝ) (hs : s ^ 2 = 3) : (31 / 16 : ℝ) ≠ s := by
  intro h
  rw [← h] at hs
  norm_num at hs

/-- **`H` lies strictly inside `K`**, hence inside every family triangle: the write-up's
`(31/16 − 31/20)²/(4/25) = 961/1024 < 1`. -/
theorem H_mem_KsetInterior : ((31 : ℝ) / 16, (0 : ℝ)) ∈ KsetInterior := by
  simp only [KsetInterior, Set.mem_setOf_eq]
  norm_num

end Witness

/-! ### Section 2's tangency condition

The row's second residue was *"that every side touches `K`"* — only the algebraic scaling was
certified (`tangency_scale`), not the geometry behind it.  This section proves the geometry.

The write-up's step is: the chord of the unit circle through `a, b` is the real line
`X cosθ + Y sinθ = d`, and its tangency condition to the caustic `K₀` is

    `(d − (31/40)cosθ)² = (1/25)cos²θ + (63/1600)sin²θ`,

which multiplication by `1600` turns into the Vieta pair relation — and THAT identity is already
`tangency_scale`.

`tangency_condition` proves the middle equivalence, in the SUPPORTING-LINE form, which is what
"circumscribes" means for a convex caustic: the line touches `K₀` and `K₀` lies on one side of
it.  The engine is one campaign-agnostic fact, `a u + b v ≤ √(a² + b²)` on the unit circle with
equality attained — Cauchy–Schwarz as `(av − bu)² ≥ 0`, plus the witness `(a,b)/√(a²+b²)`.
`linear_le_sqrt_on_circle` and `exists_eq_sqrt_on_circle` mention no conic and are `Common/`
candidates.

`mem_K0set_iff` is the only place the caustic's shape enters: `u = 5(X − 31/40)` and
`v = 40Y/√63` put it on the unit circle, and then `(1/5)·cosθ` and `(√63/40)·sinθ` are the `a`
and `b` whose squares are the write-up's `1/25` and `63/1600`.

**WHAT IS STILL MISSING on this row**: the CHORD half — that the chord of the unit circle through
`a, b` with `r = ab` and `q = a+b` is the line `X cosθ + Y sinθ = d` with `r = e^{2iθ}` and
`q = 2de^{iθ}` — and the continuity argument that every family triangle CONTAINS the caustic.
Neither is carried as a hypothesis; the module still has no `Prop` parameter. -/

section Tangency

/-! ### Section 2's tangency condition

The write-up's step: the chord of the unit circle through `a, b` is the real line
`X cos θ + Y sin θ = d`, and its tangency condition to the caustic `K₀` is

    `(d − (31/40)cos θ)² = (1/25)cos²θ + (63/1600)sin²θ`,

which `tangency_scale` then converts, by a factor of `1600`, into the Vieta pair relation.

**What is proved here is the tangency half**, in the supporting-line form, which is what
"circumscribes" means for a convex caustic: the line touches `K₀` and `K₀` lies on one side.  The
engine is one campaign-agnostic fact — `a u + b v ≤ √(a² + b²)` on the unit circle, with equality
attained — which is Cauchy–Schwarz plus the witness `(a,b)/√(a²+b²)`.
-/

/-- `a u + b v ≤ √(a² + b²)` on the unit circle.  Cauchy–Schwarz, as `(av − bu)² ≥ 0`. -/
theorem linear_le_sqrt_on_circle (a b u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) :
    a * u + b * v ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  have hnn : 0 ≤ Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_nonneg _
  have hs : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  by_contra hcon
  push_neg at hcon
  have h1 : (a * u + b * v) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg (a * v - b * u), h]
  nlinarith [hcon, hnn, hs, h1]

/-- The bound is attained: the maximiser is `(a,b)/√(a²+b²)`, or `(1,0)` when `a = b = 0`. -/
theorem exists_eq_sqrt_on_circle (a b : ℝ) :
    ∃ u v : ℝ, u ^ 2 + v ^ 2 = 1 ∧ a * u + b * v = Real.sqrt (a ^ 2 + b ^ 2) := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ a ^ 2 + b ^ 2 by positivity) with h | h
  · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    refine ⟨1, 0, by norm_num, ?_⟩
    rw [ha, hb]
    norm_num
  · have hSpos : 0 < Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_pos.mpr h
    have hs : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (le_of_lt h)
    refine ⟨a / Real.sqrt (a ^ 2 + b ^ 2), b / Real.sqrt (a ^ 2 + b ^ 2), ?_, ?_⟩
    · field_simp
      linarith [hs]
    · field_simp
      linarith [hs]

/-- The caustic `K₀`, the inverse image of `K` under `(x,y) = (2X, Y)`. -/
def K0set : Set (ℝ × ℝ) :=
  {P | (P.1 - 31 / 40) ^ 2 / (1 / 25) + P.2 ^ 2 / (63 / 1600) = 1}

/-- The line `X cos θ + Y sin θ = d`. -/
def lineTD (th d : ℝ) : Set (ℝ × ℝ) :=
  {P | P.1 * Real.cos th + P.2 * Real.sin th = d}

/-- The half-width of `K₀` in the direction `θ`: `√((1/25)cos²θ + (63/1600)sin²θ)`. -/
noncomputable def halfWidth (th : ℝ) : ℝ :=
  Real.sqrt ((1 / 25) * Real.cos th ^ 2 + (63 / 1600) * Real.sin th ^ 2)

theorem sqrt63_sq : Real.sqrt 63 ^ 2 = 63 := Real.sq_sqrt (by norm_num)

/-- `K₀` written on the unit circle: `u = 5(X − 31/40)`, `v = 40Y/√63`. -/
theorem mem_K0set_iff (P : ℝ × ℝ) :
    P ∈ K0set ↔ (5 * (P.1 - 31 / 40)) ^ 2 + (40 * P.2 / Real.sqrt 63) ^ 2 = 1 := by
  simp only [K0set, Set.mem_setOf_eq]
  have h2 : (40 * P.2 / Real.sqrt 63) ^ 2 = 1600 * P.2 ^ 2 / 63 := by
    rw [div_pow, sqrt63_sq]
    ring
  have h3 : P.2 ^ 2 / (63 / 1600) = 1600 * P.2 ^ 2 / 63 := by ring
  have h4 : (P.1 - 31 / 40) ^ 2 / (1 / 25) = (5 * (P.1 - 31 / 40)) ^ 2 := by ring
  rw [h2, h3, h4]

/-- The direction coefficients whose squares are the write-up's `1/25` and `63/1600`. -/
theorem coeff_sq (th : ℝ) :
    ((1 / 5) * Real.cos th) ^ 2 + ((Real.sqrt 63 / 40) * Real.sin th) ^ 2
      = (1 / 25) * Real.cos th ^ 2 + (63 / 1600) * Real.sin th ^ 2 := by
  simp only [mul_pow, div_pow, sqrt63_sq]
  norm_num

/-- **Every point of `K₀` is on one side**, with `31/40·cos θ + halfWidth θ` the exact bound. -/
theorem inner_le_of_mem_K0set {th : ℝ} {P : ℝ × ℝ} (hP : P ∈ K0set) :
    P.1 * Real.cos th + P.2 * Real.sin th
      ≤ (31 / 40) * Real.cos th + halfWidth th := by
  rw [mem_K0set_iff] at hP
  have hkey := linear_le_sqrt_on_circle ((1 / 5) * Real.cos th)
    ((Real.sqrt 63 / 40) * Real.sin th) (5 * (P.1 - 31 / 40)) (40 * P.2 / Real.sqrt 63) hP
  rw [coeff_sq] at hkey
  have hlin : ((1 / 5) * Real.cos th) * (5 * (P.1 - 31 / 40))
      + ((Real.sqrt 63 / 40) * Real.sin th) * (40 * P.2 / Real.sqrt 63)
      = (P.1 - 31 / 40) * Real.cos th + P.2 * Real.sin th := by
    field_simp
  rw [hlin] at hkey
  rw [halfWidth]
  linarith

/-- **The bound is attained**: some point of `K₀` lies on the line. -/
theorem exists_mem_K0set_eq (th : ℝ) :
    ∃ P ∈ K0set, P.1 * Real.cos th + P.2 * Real.sin th
      = (31 / 40) * Real.cos th + halfWidth th := by
  obtain ⟨u, v, huv, heq⟩ := exists_eq_sqrt_on_circle ((1 / 5) * Real.cos th)
    ((Real.sqrt 63 / 40) * Real.sin th)
  rw [coeff_sq] at heq
  refine ⟨(31 / 40 + (1 / 5) * u, (Real.sqrt 63 / 40) * v), ?_, ?_⟩
  · rw [mem_K0set_iff]
    have h1 : (5 * (31 / 40 + (1 / 5) * u - 31 / 40)) = u := by ring
    have h2 : (40 * ((Real.sqrt 63 / 40) * v) / Real.sqrt 63) = v := by
      field_simp
    rw [h1, h2]
    exact huv
  · rw [halfWidth, ← heq]
    ring

/-- **Section 2's tangency condition.**  The line `X cos θ + Y sin θ = d` supports `K₀` and
touches it exactly when the write-up's squared condition holds on the far side.  Multiplying that
condition by `1600` is `tangency_scale`, already proved, which is what turns it into the Vieta
pair relation. -/
theorem tangency_condition {th d : ℝ} (hd : (31 / 40) * Real.cos th ≤ d) :
    ((∀ P ∈ K0set, P.1 * Real.cos th + P.2 * Real.sin th ≤ d) ∧
      (∃ P ∈ K0set, P ∈ lineTD th d))
    ↔ (d - (31 / 40) * Real.cos th) ^ 2
      = (1 / 25) * Real.cos th ^ 2 + (63 / 1600) * Real.sin th ^ 2 := by
  have hw : halfWidth th ^ 2 = (1 / 25) * Real.cos th ^ 2 + (63 / 1600) * Real.sin th ^ 2 := by
    rw [halfWidth]
    exact Real.sq_sqrt (by positivity)
  have hwnn : 0 ≤ halfWidth th := Real.sqrt_nonneg _
  constructor
  · rintro ⟨hle, ⟨P, hP, hPe⟩⟩
    have hPe' : P.1 * Real.cos th + P.2 * Real.sin th = d := hPe
    have h1 : d ≤ (31 / 40) * Real.cos th + halfWidth th := by
      rw [← hPe']
      exact inner_le_of_mem_K0set hP
    obtain ⟨Q, hQ, hQe⟩ := exists_mem_K0set_eq th
    have h2 : (31 / 40) * Real.cos th + halfWidth th ≤ d := by
      rw [← hQe]
      exact hle Q hQ
    have hdeq : d = (31 / 40) * Real.cos th + halfWidth th := le_antisymm h1 h2
    rw [hdeq, ← hw]
    ring
  · intro h
    have hdeq : d = (31 / 40) * Real.cos th + halfWidth th := by
      have h1 : (d - (31 / 40) * Real.cos th) ^ 2 = halfWidth th ^ 2 := by rw [hw]; exact h
      have h2 : 0 ≤ d - (31 / 40) * Real.cos th := by linarith
      nlinarith [h1, h2, hwnn]
    refine ⟨?_, ?_⟩
    · intro P hP
      rw [hdeq]
      exact inner_le_of_mem_K0set hP
    · obtain ⟨Q, hQ, hQe⟩ := exists_mem_K0set_eq th
      refine ⟨Q, hQ, ?_⟩
      show Q.1 * Real.cos th + Q.2 * Real.sin th = d
      rw [hQe, hdeq]

end Tangency

/-! ### The chord half of Section 2

The write-up: *"The chord of the unit circle through `a, b` has equation `z + r z̄ = q`.  Write
`r = e^{2iθ}` and `q = 2d e^{iθ}`.  This is the real line `X cosθ + Y sinθ = d`."*

`exists_chord_eq_lineTD` is that sentence with nothing assumed: for any `a, b` on the unit circle
there are `θ` and `d` such that the chord `{z : z + ab·z̄ = a+b}` is exactly the line
`lineTD θ d`.  With the previous section's `tangency_condition`, the write-up's Section 2 is
formal apart from the continuity argument.

**Two things carry it.**  The square root `u` with `u² = ab` on the circle EXISTS
(`exists_unit_sqrt`, as `exp(i·arg(ab)/2)`), so `θ = arg u` and `d = Re(ū(a+b))/2` are produced
rather than assumed.  And `ū(a+b)` is REAL (`conj_mul_sum_im`) — it is self-conjugate, since
`conj(ū(a+b)) = u(a⁻¹+b⁻¹) = u(a+b)/(ab) = ū(a+b)` using `ab = u²` and `1/u = ū`.  That
realness is what the REVERSE inclusion needs: without it the chord would be a proper subset of the
line, and the write-up's "this IS the real line" would be an overstatement.

The mechanism is one multiplication: multiplying `z + u²z̄ = a+b` by `ū` turns the left-hand side
into `ūz + conj(ūz) = 2Re(ūz)`, so a complex equation becomes a single real one. -/

section Chord

/-! ### The chord half of Section 2

The write-up: *"The chord of the unit circle through `a, b` has equation `z + r z̄ = q`.  Write
`r = e^{2iθ}` and `q = 2d e^{iθ}`.  This is the real line `X cos θ + Y sin θ = d`."*

`chord_eq_lineTD` is that sentence.  The square root `u` with `u² = ab` on the circle exists
(`exists_unit_sqrt`), `θ` is its argument, and `d` is `Re(ū(a+b))/2` — which is REAL, and that is
the one fact the equivalence needs in the reverse direction (`conj_mul_sum_im`).
-/

theorem norm_eq_one_of_normSq_one {w : ℂ} (h : normSq w = 1) : ‖w‖ = 1 := by
  have h2 : ‖w‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h
  nlinarith [norm_nonneg w, h2]

/-- A unit complex number has a unit square root: `exp(i·arg w /2)`. -/
theorem exists_unit_sqrt {w : ℂ} (h : normSq w = 1) :
    ∃ u : ℂ, u ^ 2 = w ∧ normSq u = 1 := by
  refine ⟨Complex.exp ((Complex.arg w / 2 : ℝ) * Complex.I), ?_, ?_⟩
  · rw [← Complex.exp_nat_mul]
    have harg : (2 : ℂ) * ((Complex.arg w / 2 : ℝ) * Complex.I)
        = (Complex.arg w : ℝ) * Complex.I := by
      push_cast
      ring
    rw [show ((2 : ℕ) : ℂ) * ((Complex.arg w / 2 : ℝ) * Complex.I)
        = (Complex.arg w : ℝ) * Complex.I from by push_cast; ring]
    have := Complex.norm_mul_exp_arg_mul_I w
    rw [norm_eq_one_of_normSq_one h] at this
    simpa using this
  · have hn : ‖Complex.exp ((Complex.arg w / 2 : ℝ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [Complex.normSq_eq_norm_sq, hn]
    norm_num

theorem cos_arg_of_normSq_one {u : ℂ} (h : normSq u = 1) :
    Real.cos (Complex.arg u) = u.re := by
  have hne : u ≠ 0 := by
    intro hz
    rw [hz] at h
    simp at h
  rw [Complex.cos_arg hne, norm_eq_one_of_normSq_one h, div_one]

theorem sin_arg_of_normSq_one {u : ℂ} (h : normSq u = 1) :
    Real.sin (Complex.arg u) = u.im := by
  rw [Complex.sin_arg, norm_eq_one_of_normSq_one h, div_one]

theorem conj_mul_self_eq_one {u : ℂ} (h : normSq u = 1) : (starRingEnd ℂ) u * u = 1 := by
  rw [mul_comm, Complex.mul_conj, h]
  norm_num

/-- **`ū(a+b)` is real.**  It is self-conjugate: `conj(ū(a+b)) = u(a⁻¹+b⁻¹) = u(a+b)/(ab) = ū(a+b)`
using `ab = u²` and `1/u = ū`.  This is what makes the chord a REAL line rather than a proper
subset of one. -/
theorem conj_mul_sum_im {a b u : ℂ} (ha : normSq a = 1) (hb : normSq b = 1)
    (hu2 : u ^ 2 = a * b) (hu1 : normSq u = 1) :
    ((starRingEnd ℂ) u * (a + b)).im = 0 := by
  have hane : a ≠ 0 := by intro hz; rw [hz] at ha; simp at ha
  have hbne : b ≠ 0 := by intro hz; rw [hz] at hb; simp at hb
  have hune : u ≠ 0 := by intro hz; rw [hz] at hu1; simp at hu1
  have hca : (starRingEnd ℂ) a = a⁻¹ := conj_eq_inv_of_normSq_one ha
  have hcb : (starRingEnd ℂ) b = b⁻¹ := conj_eq_inv_of_normSq_one hb
  have hcu : (starRingEnd ℂ) u = u⁻¹ := conj_eq_inv_of_normSq_one hu1
  have hself : (starRingEnd ℂ) ((starRingEnd ℂ) u * (a + b))
      = (starRingEnd ℂ) u * (a + b) := by
    rw [map_mul, map_add, Complex.conj_conj, hca, hcb, hcu]
    field_simp
    linear_combination (a + b) * hu2
  have := Complex.conj_eq_iff_im.mp hself
  exact this

/-- **The chord of the unit circle through `a, b` IS the real line.**  Multiplying
`z + u²z̄ = a+b` by `ū` turns the left side into `ūz + conj(ūz) = 2Re(ūz)`, and the right side is
real, so the complex equation is the single real one. -/
theorem chord_mem_iff_re {a b u z : ℂ} (ha : normSq a = 1) (hb : normSq b = 1)
    (hu2 : u ^ 2 = a * b) (hu1 : normSq u = 1) :
    z + (a * b) * (starRingEnd ℂ) z = a + b
      ↔ z.re * u.re + z.im * u.im = ((starRingEnd ℂ) u * (a + b)).re / 2 := by
  have hune : u ≠ 0 := by intro hz; rw [hz] at hu1; simp at hu1
  have hcune : (starRingEnd ℂ) u ≠ 0 := by
    simpa using (map_ne_zero_iff _ (starRingEnd ℂ).injective).mpr hune
  have hcu : (starRingEnd ℂ) u * u = 1 := conj_mul_self_eq_one hu1
  have him := conj_mul_sum_im ha hb hu2 hu1
  have hkey : (starRingEnd ℂ) u * (z + (a * b) * (starRingEnd ℂ) z)
      = ((2 * (z.re * u.re + z.im * u.im) : ℝ) : ℂ) := by
    rw [← hu2, mul_add]
    have h1 : (starRingEnd ℂ) u * ((u ^ 2) * (starRingEnd ℂ) z) = u * (starRingEnd ℂ) z := by
      rw [pow_two]
      calc (starRingEnd ℂ) u * (u * u * (starRingEnd ℂ) z)
          = ((starRingEnd ℂ) u * u) * (u * (starRingEnd ℂ) z) := by ring
        _ = u * (starRingEnd ℂ) z := by rw [hcu, one_mul]
    rw [h1]
    have h2 : u * (starRingEnd ℂ) z = (starRingEnd ℂ) ((starRingEnd ℂ) u * z) := by
      simp [map_mul]
    rw [h2, Complex.add_conj]
    push_cast
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    push_cast
    ring
  constructor
  · intro h
    have h3 : (starRingEnd ℂ) u * (z + (a * b) * (starRingEnd ℂ) z)
        = (starRingEnd ℂ) u * (a + b) := by rw [h]
    rw [hkey] at h3
    have h4 := congrArg Complex.re h3
    simp only [Complex.ofReal_re] at h4
    linarith
  · intro h
    have h5 : ((2 * (z.re * u.re + z.im * u.im) : ℝ) : ℂ) = (starRingEnd ℂ) u * (a + b) := by
      apply Complex.ext
      · simp only [Complex.ofReal_re]
        linarith
      · simp only [Complex.ofReal_im]
        exact him.symm
    rw [← hkey] at h5
    exact mul_left_cancel₀ hcune h5

/-- **Section 2's chord sentence, in the `lineTD` form the tangency condition consumes.** -/
theorem chord_eq_lineTD {a b u : ℂ} (ha : normSq a = 1) (hb : normSq b = 1)
    (hu2 : u ^ 2 = a * b) (hu1 : normSq u = 1) (z : ℂ) :
    z + (a * b) * (starRingEnd ℂ) z = a + b
      ↔ (z.re, z.im) ∈ lineTD (Complex.arg u) (((starRingEnd ℂ) u * (a + b)).re / 2) := by
  rw [chord_mem_iff_re ha hb hu2 hu1]
  simp only [lineTD, Set.mem_setOf_eq, cos_arg_of_normSq_one hu1, sin_arg_of_normSq_one hu1]

/-- **Section 2's chord sentence with nothing assumed**: for `a, b` on the unit circle there ARE
`θ` and `d` making the chord `{z : z + ab·z̄ = a+b}` equal to `lineTD θ d`.  The square root is
produced by `exists_unit_sqrt`, not hypothesised. -/
theorem exists_chord_eq_lineTD {a b : ℂ} (ha : normSq a = 1) (hb : normSq b = 1) :
    ∃ th d : ℝ, ∀ z : ℂ,
      z + (a * b) * (starRingEnd ℂ) z = a + b ↔ (z.re, z.im) ∈ lineTD th d := by
  have hab : normSq (a * b) = 1 := by
    rw [Complex.normSq_mul, ha, hb]
    norm_num
  obtain ⟨u, hu2, hu1⟩ := exists_unit_sqrt hab
  exact ⟨Complex.arg u, ((starRingEnd ℂ) u * (a + b)).re / 2,
    fun z => chord_eq_lineTD ha hb hu2 hu1 z⟩

end Chord

section Exclusion

/-! ### Section 4: the pair is in none of the three configurations

The write-up's Section 4 reads: *"The definitions in [special, Sections 3--4] distinguish the
three families by their actual Euclidean conic configurations"*, followed by a table naming, for
each family, the Euclidean feature this pair lacks — MacBeath, the OUTER conic is a circle;
focal-`X₄`, the INNER conic is a circle; Dual, the two ellipses are CONCENTRIC — plus two extra
remarks, that `H` is not a focus of `E` and that `H` lies strictly inside `K`.

**The three predicates below are TRANSCRIBED from the cited source, not derived here.**  The
projective definitions of the three families are not formalised, and neither is their
equivalence with these Euclidean conditions; the write-up cites that equivalence rather than
proving it, so this module carries it as a definition and says so.  What IS proved is that
`(E, K)` fails each condition — which is the whole content of Section 4, and which the module
already had in `Eset_not_circle`, `Kset_not_circle` and `not_concentric` without ever stating
what those three facts were FOR.

Each condition happens to constrain only one of the two conics, so the predicates take the pair
and use one side; keeping them binary is what makes `section_four` read as the source's table.

This was the second of the row's two remaining links, and it was mispriced in the module header
as *"needs definitions of focal-X₄, MacBeath and Dual families, which are not in Mathlib"*.  A
definition the source supplies is not a Mathlib gap.  The FIRST link — that every side of the
triangle touches `K` — is still open.
-/

/-- A Euclidean circle in the plane. -/
def IsCircle (S : Set (ℝ × ℝ)) : Prop :=
  ∃ cx cy rho : ℝ, S = {P : ℝ × ℝ | (P.1 - cx) ^ 2 + (P.2 - cy) ^ 2 = rho ^ 2}

/-- The **MacBeath** configuration, as the cited source's definition distinguishes it: the outer
conic is a circle. -/
def MacBeathPair (outer _inner : Set (ℝ × ℝ)) : Prop := IsCircle outer

/-- The **focal-`X₄`** configuration: the inner conic is a circle. -/
def FocalX4Pair (_outer inner : Set (ℝ × ℝ)) : Prop := IsCircle inner

/-- The **Dual** configuration: the two conics are concentric. -/
def DualPair (outer inner : Set (ℝ × ℝ)) : Prop :=
  ∃ c : ℝ × ℝ, IsCenter outer c ∧ IsCenter inner c

/-- A focus of `E`: the write-up's `(±√3, 0)`, from `4 − 1 = 3`. -/
def IsFocusE (P : ℝ × ℝ) : Prop :=
  ∃ s : ℝ, s ^ 2 = 3 ∧ (P = (s, 0) ∨ P = (-s, 0))

theorem not_macBeath : ¬ MacBeathPair Eset Kset := Eset_not_circle

theorem not_focalX4 : ¬ FocalX4Pair Eset Kset := Kset_not_circle

theorem not_dual : ¬ DualPair Eset Kset := not_concentric

/-- **`H` is not a focus of `E`** — the write-up's extra remark, `(31/16)² ≠ 3`. -/
theorem H_not_focusE : ¬ IsFocusE ((31 : ℝ) / 16, (0 : ℝ)) := by
  rintro ⟨s, hs, h | h⟩
  · exact H_not_focus s hs (congrArg Prod.fst h)
  · have h1 : (31 : ℝ) / 16 = -s := congrArg Prod.fst h
    refine H_not_focus (-s) ?_ h1
    rw [neg_sq]
    exact hs

/-- **Section 4 in full.**  The pair is none of the three configurations, `H` is not a focus of
`E`, and `H` lies strictly inside `K`. -/
theorem section_four :
    (¬ MacBeathPair Eset Kset ∧ ¬ FocalX4Pair Eset Kset ∧ ¬ DualPair Eset Kset)
      ∧ ¬ IsFocusE ((31 : ℝ) / 16, (0 : ℝ))
      ∧ ((31 : ℝ) / 16, (0 : ℝ)) ∈ KsetInterior :=
  ⟨⟨not_macBeath, not_focalX4, not_dual⟩, H_not_focusE, H_mem_KsetInterior⟩

end Exclusion

section CausticInside

/-! ### The caustic is inside every family triangle — WITHOUT a continuity argument

The write-up closes Section 2 with *"a tangent line cannot cross the centre of a nondegenerate
ellipse; continuity preserves the interior side"*: it obtains the containment of the caustic by
deforming along the family.  **That argument is not needed, and nothing here deforms anything.**
The containment follows from one elementary fact about chords:

> a line through two points of the unit circle meets the OPEN disc only STRICTLY BETWEEN them.

`chord_param_mem_disc` is that fact, and it is pure algebra: with `Q = a + s(b−a)` and `a`, `b` on
the circle,

    ‖Q‖² − 1 = s(s−1)·‖b−a‖²,

so `‖Q‖ < 1` forces `0 < s < 1` outright.  Then `vertex_le_of_touch` is linear arithmetic: if the
opposite side has `K₀` on its `≤` side and `K₀` touches the side through `a` and `b` at a point
`Q` of the open disc, then `⟨Q,n⟩ = (1−s)⟨a,n⟩ + s·d ≤ d` with `s < 1` gives `⟨a,n⟩ ≤ d`.  **The
vertex is on the caustic's side because the touching point is strictly inside the chord**, and
that is a fact about ONE triangle, with no family and no limit.

**Sharper than expected:** only `s < 1` is used, not `0 < s`.  The touching point has to fall
short of the far endpoint; it does not also have to clear the near one.
-/

/-- A vector annihilated by `(cos θ, sin θ)` is a multiple of `(−sin θ, cos θ)`, with the
multiplier written out.  The rotation matrix is its own inverse up to sign, which is the whole
content. -/
theorem lineTD_dir {th : ℝ} {y : ℝ × ℝ}
    (h : y.1 * Real.cos th + y.2 * Real.sin th = 0) :
    y.1 = -(y.2 * Real.cos th - y.1 * Real.sin th) * Real.sin th ∧
      y.2 = (y.2 * Real.cos th - y.1 * Real.sin th) * Real.cos th := by
  have hpy : Real.sin th ^ 2 + Real.cos th ^ 2 = 1 := Real.sin_sq_add_cos_sq th
  constructor
  · linear_combination Real.cos th * h - y.1 * hpy
  · linear_combination Real.sin th * h - y.2 * hpy

/-- **Three points on one line `lineTD θ d`, two of them distinct: the third is an affine
combination.** -/
theorem exists_param_of_lineTD {th d : ℝ} {a b Q : ℝ × ℝ}
    (ha : a ∈ lineTD th d) (hb : b ∈ lineTD th d) (hQ : Q ∈ lineTD th d) (hab : a ≠ b) :
    ∃ s : ℝ, Q.1 = a.1 + s * (b.1 - a.1) ∧ Q.2 = a.2 + s * (b.2 - a.2) := by
  simp only [lineTD, Set.mem_setOf_eq] at ha hb hQ
  have hbz : (b.1 - a.1) * Real.cos th + (b.2 - a.2) * Real.sin th = 0 := by linarith
  have hQz : (Q.1 - a.1) * Real.cos th + (Q.2 - a.2) * Real.sin th = 0 := by linarith
  obtain ⟨hb1, hb2⟩ := lineTD_dir (y := (b.1 - a.1, b.2 - a.2)) hbz
  obtain ⟨hQ1, hQ2⟩ := lineTD_dir (y := (Q.1 - a.1, Q.2 - a.2)) hQz
  simp only at hb1 hb2 hQ1 hQ2
  set m : ℝ := (b.2 - a.2) * Real.cos th - (b.1 - a.1) * Real.sin th with hmdef
  set k : ℝ := (Q.2 - a.2) * Real.cos th - (Q.1 - a.1) * Real.sin th with hkdef
  have hmne : m ≠ 0 := by
    intro h0
    apply hab
    have e1 : b.1 - a.1 = 0 := by rw [hb1, h0]; ring
    have e2 : b.2 - a.2 = 0 := by rw [hb2, h0]; ring
    exact Prod.ext (by linarith) (by linarith)
  refine ⟨k / m, ?_, ?_⟩
  · field_simp
    linear_combination m * hQ1 - k * hb1
  · field_simp
    linear_combination m * hQ2 - k * hb2

/-- **A chord meets the OPEN unit disc only strictly between its endpoints.**  The identity
`‖a + s(b−a)‖² − 1 = s(s−1)·‖b−a‖²` does all the work. -/
theorem chord_param_mem_disc {a b Q : ℝ × ℝ} {s : ℝ}
    (ha : a.1 ^ 2 + a.2 ^ 2 = 1) (hb : b.1 ^ 2 + b.2 ^ 2 = 1)
    (hQ1 : Q.1 = a.1 + s * (b.1 - a.1)) (hQ2 : Q.2 = a.2 + s * (b.2 - a.2))
    (hdisc : Q.1 ^ 2 + Q.2 ^ 2 < 1) : 0 < s ∧ s < 1 := by
  have hid : Q.1 ^ 2 + Q.2 ^ 2 - 1
      = s * (s - 1) * ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) := by
    rw [hQ1, hQ2]
    linear_combination (1 - s) * ha + s * hb
  have hneg : s * (s - 1) * ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) < 0 := by linarith
  have hlen : 0 < (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 := by
    rcases (show (0 : ℝ) ≤ (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 by positivity).lt_or_eq with h | h
    · exact h
    · rw [← h] at hneg
      simp only [mul_zero, lt_self_iff_false] at hneg
  have hs : s * (s - 1) < 0 := by
    by_contra hcon
    have hcon' : 0 ≤ s * (s - 1) := not_lt.mp hcon
    nlinarith [hcon', hlen]
  constructor
  · by_contra h
    have hle : s ≤ 0 := not_lt.mp h
    nlinarith [hs, hle]
  · by_contra h
    have hle : 1 ≤ s := not_lt.mp h
    nlinarith [hs, hle]

/-- **The engine.**  If the opposite side `⟨·,n⟩ = d` passes through `b` and has `K` on its `≤`
side, and `K` touches the chord from `a` to `b` at a point short of `b`, then `a` is on the `≤`
side too.  Linear arithmetic once `s < 1` is known. -/
theorem vertex_le_of_touch {th d s : ℝ} {a b Q : ℝ × ℝ}
    (hb : b ∈ lineTD th d)
    (hQ1 : Q.1 = a.1 + s * (b.1 - a.1)) (hQ2 : Q.2 = a.2 + s * (b.2 - a.2))
    (hs1 : s < 1)
    (hQle : Q.1 * Real.cos th + Q.2 * Real.sin th ≤ d) :
    a.1 * Real.cos th + a.2 * Real.sin th ≤ d := by
  simp only [lineTD, Set.mem_setOf_eq] at hb
  have hexp : Q.1 * Real.cos th + Q.2 * Real.sin th
      = (1 - s) * (a.1 * Real.cos th + a.2 * Real.sin th)
        + s * (b.1 * Real.cos th + b.2 * Real.sin th) := by
    rw [hQ1, hQ2]; ring
  rw [hexp, hb] at hQle
  nlinarith [hQle, hs1]

/-- **The caustic lies strictly inside the unit disc**, as a statement about `K0set` rather than
about the parametrisation `K0pt`.  In the circle coordinate `u = 5(X − 31/40)` the squared
distance is `(1024 + 496u + u²)/1600`, largest at `u = 1`, where it is `1521/1600`. -/
theorem K0set_inside_unit_disc {P : ℝ × ℝ} (hP : P ∈ K0set) :
    P.1 ^ 2 + P.2 ^ 2 < 1 := by
  simp only [K0set, Set.mem_setOf_eq] at hP
  have hc : 25 * (P.1 - 31 / 40) ^ 2 + (1600 / 63) * P.2 ^ 2 = 1 := by
    field_simp at hP
    linarith [hP]
  have hY : (0 : ℝ) ≤ P.2 ^ 2 := sq_nonneg _
  have hx1 : 25 * (P.1 - 31 / 40) ^ 2 ≤ 1 := by nlinarith [hc, hY]
  have hxu : P.1 ≤ 39 / 40 := by nlinarith [hx1]
  have hxl : 23 / 40 ≤ P.1 := by nlinarith [hx1]
  nlinarith [hc, hxu, hxl, hY]

/-- **THE ROW'S LAST LINK, WITHOUT CONTINUITY.**  Let `a`, `b` be two distinct vertices of a
family triangle on the unit circle, let the side opposite `a` lie on `lineTD θ d` through `b`
with the caustic `K₀` on its `≤` side, and let `K₀` touch the side `lineTD θ' d'` joining `a` and
`b`.  Then `a` is on the caustic's side of the opposite side as well. -/
theorem vertex_side_of_support {th d th' d' : ℝ} {a b Q : ℝ × ℝ}
    (ha1 : a.1 ^ 2 + a.2 ^ 2 = 1) (hb1 : b.1 ^ 2 + b.2 ^ 2 = 1) (hab : a ≠ b)
    (hbL : b ∈ lineTD th d)
    (haS : a ∈ lineTD th' d') (hbS : b ∈ lineTD th' d')
    (hQK : Q ∈ K0set) (hQS : Q ∈ lineTD th' d')
    (hsupp : ∀ P ∈ K0set, P.1 * Real.cos th + P.2 * Real.sin th ≤ d) :
    a.1 * Real.cos th + a.2 * Real.sin th ≤ d := by
  obtain ⟨s, hs1, hs2⟩ := exists_param_of_lineTD haS hbS hQS hab
  obtain ⟨_, hhi⟩ := chord_param_mem_disc ha1 hb1 hs1 hs2 (K0set_inside_unit_disc hQK)
  exact vertex_le_of_touch hbL hs1 hs2 hhi (hsupp Q hQK)

end CausticInside

section Triangle

/-! ### From the three side conditions to containment, by signed areas

With every vertex on the caustic's side of its opposite side, the containment is barycentric
coordinates and nothing else.  `sdet X Y Z` is twice the signed area of `XYZ`; the two facts it
obeys — that the three sub-areas sum to the whole (`sdet_split`) and that they reproduce the point
(`sdet_combo_fst`/`_snd`) — are ring identities.

The bridge to the half-planes is `sdet_of_lineTD`: for `b`, `c` on the line `⟨·,n⟩ = d`,

    `sdet X b c = m · (d − ⟨X,n⟩)`,   `m = (c₂−b₂)cos θ − (c₁−b₁)sin θ`,

so the SIGN of a signed area is the side of the line, and the ratio `sdet X b c / sdet a b c` is
`(d − ⟨X,n⟩)/(d − ⟨a,n⟩)` with `m` cancelling.
-/

/-- Twice the signed area of the triangle `X Y Z`. -/
def sdet (X Y Z : ℝ × ℝ) : ℝ := (Y.1 - X.1) * (Z.2 - X.2) - (Y.2 - X.2) * (Z.1 - X.1)

/-- The three sub-triangles at `P` partition the area. -/
theorem sdet_split (a b c P : ℝ × ℝ) : sdet P b c + sdet a P c + sdet a b P = sdet a b c := by
  simp only [sdet]; ring

theorem sdet_combo_fst (a b c P : ℝ × ℝ) :
    sdet P b c * a.1 + sdet a P c * b.1 + sdet a b P * c.1 = sdet a b c * P.1 := by
  simp only [sdet]; ring

theorem sdet_combo_snd (a b c P : ℝ × ℝ) :
    sdet P b c * a.2 + sdet a P c * b.2 + sdet a b P * c.2 = sdet a b c * P.2 := by
  simp only [sdet]; ring

/-- **A signed area against a side line is the side of that line**, up to the fixed factor `m`. -/
theorem sdet_of_lineTD {th d : ℝ} {b c : ℝ × ℝ}
    (hb : b ∈ lineTD th d) (hc : c ∈ lineTD th d) (X : ℝ × ℝ) :
    sdet X b c
      = ((c.2 - b.2) * Real.cos th - (c.1 - b.1) * Real.sin th)
          * (d - (X.1 * Real.cos th + X.2 * Real.sin th)) := by
  simp only [lineTD, Set.mem_setOf_eq] at hb hc
  have hz : (c.1 - b.1) * Real.cos th + (c.2 - b.2) * Real.sin th = 0 := by linarith
  obtain ⟨h1, h2⟩ := lineTD_dir (y := (c.1 - b.1, c.2 - b.2)) hz
  simp only at h1 h2
  simp only [sdet]
  linear_combination (b.1 - X.1) * h2 + (X.2 - b.2) * h1
    + ((c.2 - b.2) * Real.cos th - (c.1 - b.1) * Real.sin th) * hb

/-- **The barycentric ratio is nonnegative** when the point and the opposite vertex are on the
same side of the side line.  The factor `m` cancels. -/
theorem sdet_div_nonneg {th d : ℝ} {a b c X : ℝ × ℝ}
    (hb : b ∈ lineTD th d) (hc : c ∈ lineTD th d) (hD : sdet a b c ≠ 0)
    (hX : X.1 * Real.cos th + X.2 * Real.sin th ≤ d)
    (ha : a.1 * Real.cos th + a.2 * Real.sin th ≤ d) :
    0 ≤ sdet X b c / sdet a b c := by
  have hm : ((c.2 - b.2) * Real.cos th - (c.1 - b.1) * Real.sin th) ≠ 0 := by
    intro h0
    apply hD
    rw [sdet_of_lineTD hb hc a, h0, zero_mul]
  rw [sdet_of_lineTD hb hc X, sdet_of_lineTD hb hc a, mul_div_mul_left _ _ hm]
  exact div_nonneg (by linarith) (by linarith)

/-- **The point is a convex combination of the three vertices.** -/
theorem exists_convex_combo {a b c P : ℝ × ℝ} (hD : sdet a b c ≠ 0)
    (h1 : 0 ≤ sdet P b c / sdet a b c) (h2 : 0 ≤ sdet a P c / sdet a b c)
    (h3 : 0 ≤ sdet a b P / sdet a b c) :
    ∃ al be ga : ℝ, 0 ≤ al ∧ 0 ≤ be ∧ 0 ≤ ga ∧ al + be + ga = 1 ∧
      P.1 = al * a.1 + be * b.1 + ga * c.1 ∧ P.2 = al * a.2 + be * b.2 + ga * c.2 := by
  refine ⟨sdet P b c / sdet a b c, sdet a P c / sdet a b c, sdet a b P / sdet a b c,
    h1, h2, h3, ?_, ?_, ?_⟩
  · field_simp
    linarith [sdet_split a b c P]
  · field_simp
    linarith [sdet_combo_fst a b c P]
  · field_simp
    linarith [sdet_combo_snd a b c P]

/-- **THE CAUSTIC IS INSIDE THE TRIANGLE.**  Every point of `K₀` is a convex combination of the
three vertices, given only that each side line supports `K₀` and that each vertex is on the
caustic's side of its opposite side — the latter supplied by `vertex_side_of_support`, which needs
no continuity argument. -/
theorem K0set_subset_triangle {tha da thb db thc dc : ℝ} {a b c : ℝ × ℝ}
    (hD : sdet a b c ≠ 0)
    (hba : b ∈ lineTD tha da) (hca : c ∈ lineTD tha da)
    (hva : a.1 * Real.cos tha + a.2 * Real.sin tha ≤ da)
    (hsa : ∀ Q ∈ K0set, Q.1 * Real.cos tha + Q.2 * Real.sin tha ≤ da)
    (hcb : c ∈ lineTD thb db) (hab : a ∈ lineTD thb db)
    (hvb : b.1 * Real.cos thb + b.2 * Real.sin thb ≤ db)
    (hsb : ∀ Q ∈ K0set, Q.1 * Real.cos thb + Q.2 * Real.sin thb ≤ db)
    (hac : a ∈ lineTD thc dc) (hbc : b ∈ lineTD thc dc)
    (hvc : c.1 * Real.cos thc + c.2 * Real.sin thc ≤ dc)
    (hsc : ∀ Q ∈ K0set, Q.1 * Real.cos thc + Q.2 * Real.sin thc ≤ dc)
    {P : ℝ × ℝ} (hP : P ∈ K0set) :
    ∃ al be ga : ℝ, 0 ≤ al ∧ 0 ≤ be ∧ 0 ≤ ga ∧ al + be + ga = 1 ∧
      P.1 = al * a.1 + be * b.1 + ga * c.1 ∧ P.2 = al * a.2 + be * b.2 + ga * c.2 := by
  have hDb : sdet b c a ≠ 0 := by
    intro h0; apply hD; simp only [sdet] at h0 ⊢; linarith [h0]
  have hDc : sdet c a b ≠ 0 := by
    intro h0; apply hD; simp only [sdet] at h0 ⊢; linarith [h0]
  have h1 : 0 ≤ sdet P b c / sdet a b c := sdet_div_nonneg hba hca hD (hsa P hP) hva
  have h2' : 0 ≤ sdet P c a / sdet b c a := sdet_div_nonneg hcb hab hDb (hsb P hP) hvb
  have h3' : 0 ≤ sdet P a b / sdet c a b := sdet_div_nonneg hac hbc hDc (hsc P hP) hvc
  have e2 : sdet P c a / sdet b c a = sdet a P c / sdet a b c := by
    have ha1 : sdet P c a = sdet a P c := by simp only [sdet]; ring
    have ha2 : sdet b c a = sdet a b c := by simp only [sdet]; ring
    rw [ha1, ha2]
  have e3 : sdet P a b / sdet c a b = sdet a b P / sdet a b c := by
    have ha1 : sdet P a b = sdet a b P := by simp only [sdet]; ring
    have ha2 : sdet c a b = sdet a b c := by simp only [sdet]; ring
    rw [ha1, ha2]
  rw [e2] at h2'
  rw [e3] at h3'
  exact exists_convex_combo hD h1 h2' h3'

end Triangle

section FamilyTangency

/-! ### The Vieta relations give the tangency condition for EVERY side

`tangency_scale` was in this module as a ring identity between the write-up's squared tangency
condition and the expression

    `q² − (31/20)(1+r)q + (3/5)(1+r²) + (417/400)r`,   `q = a+b`, `r = ab`,

with nothing connecting that expression to a family member.  `family_pair_tangency` is the
connection, and it is the write-up's *"the chord condition is exactly the Vieta pair relation"*:
the two `Family` relations determine `c` from `q` and `r`, and eliminating it leaves precisely
that expression.

**No nonvanishing is needed.**  The obvious route divides by `1 − (3/5)r` to solve for `c`, which
would need `ab ≠ 5/3`; multiplying instead of dividing avoids it, and the identity is then an
unconditional linear combination of the two relations.  `Family` is symmetric in its three
arguments, so `Family.rotate` gives the other two sides for free.
-/

/-- `Family` is symmetric: its two relations are symmetric functions of `a`, `b`, `c`. -/
theorem Family.rotate {a b c : ℂ} (h : Family a b c) : Family b c a where
  ne_a := h.ne_b
  ne_b := h.ne_c
  ne_c := h.ne_a
  ua := h.ub
  ub := h.uc
  uc := h.ua
  sum := by have := h.sum; linear_combination this
  pair := by have := h.pair; linear_combination this

/-- **Every side of a family triangle satisfies the write-up's tangency relation.**  With
`q = a+b` and `r = ab`, eliminating `c` from the two `Family` relations gives exactly the
expression `tangency_scale` converts into the squared tangency condition. -/
theorem family_pair_tangency {a b c : ℂ} (h : Family a b c) :
    (a + b) ^ 2 - (31 / 20) * (1 + a * b) * (a + b) + (3 / 5) * (1 + (a * b) ^ 2)
      + (417 / 400) * (a * b) = 0 := by
  have hS : (1 - (3 / 5) * (a * b)) * c = 31 / 20 - (a + b) := by
    linear_combination h.sum
  linear_combination (-(1 - (3 / 5) * (a * b))) * h.pair + ((a + b) - (31 / 20) * (a * b)) * hS

/-- The same for the side through `b` and `c`. -/
theorem family_pair_tangency_bc {a b c : ℂ} (h : Family a b c) :
    (b + c) ^ 2 - (31 / 20) * (1 + b * c) * (b + c) + (3 / 5) * (1 + (b * c) ^ 2)
      + (417 / 400) * (b * c) = 0 :=
  family_pair_tangency h.rotate

/-- The same for the side through `c` and `a`. -/
theorem family_pair_tangency_ca {a b c : ℂ} (h : Family a b c) :
    (c + a) ^ 2 - (31 / 20) * (1 + c * a) * (c + a) + (3 / 5) * (1 + (c * a) ^ 2)
      + (417 / 400) * (c * a) = 0 :=
  family_pair_tangency h.rotate.rotate

end FamilyTangency

section Instantiate

/-! ### Instantiating the containment at a family triangle

Three items stood between `K0set_subset_triangle` and a family triangle, and all three are
algebra.

**(iii) the complex-to-real passage.**  `chord_eq_lineTD` puts the chord through `a`, `b` on
`lineTD (arg u) d` for a square root `u` of `ab`, with `d` real; equivalently `q = a + b = 2du`
and `r = ab = u^2`.  Substituting THAT into `family_pair_tangency`'s relation gives, exactly,

    `E = u^2 * (4d^2 - (31/5) d cos th + (12/5) cos^2 th - 63/400)`,

and the bracket is four times the write-up's squared tangency condition.  **The only fact used is
`u^2 + 1 = 2 (Re u) u`**, which is what `|u| = 1` says once `conj u = 2 Re u - u` is substituted
into `u conj u = 1`.  So the identity is a one-term `linear_combination` and the imaginary part
never has to be discussed.

**(i) the supporting branch.**  A squared condition cannot distinguish the two tangent lines with
a given normal, and `tangency_condition` needs the one with `(31/40) cos th <= d`.  The two
branches are exactly the two square roots: replacing `u` by `-u` negates both `cos th = Re u` and
`d`.  **The branch is chosen by picking the right root, not by rotating the angle** -- which is
why no `cos (th + pi)` identity appears anywhere below.

**(ii) nondegeneracy.**  Three DISTINCT points of the unit circle are never collinear, and the
proof reuses the chord identity already in the file: collinearity writes `C = A + t(B-A)`, and
`|A + t(B-A)|^2 - 1 = t(t-1)|B-A|^2` then forces `t = 0` or `t = 1`.

**`Family` does not require its three roots to be distinct**, so distinctness is a hypothesis of
the final statement rather than something derived; that is a genuine gap in the write-up's
`Family`, recorded rather than papered over.
-/

/-- `|u| = 1` in the form the substitution needs. -/
theorem unit_sq_add_one {u : ℂ} (h : normSq u = 1) : u ^ 2 + 1 = 2 * (u.re : ℂ) * u := by
  have hconj : (starRingEnd ℂ) u = 2 * (u.re : ℂ) - u := by
    have hac := Complex.add_conj u
    push_cast at hac
    linear_combination hac
  have hmc := Complex.mul_conj u
  rw [hconj, h] at hmc
  push_cast at hmc
  linear_combination -hmc

theorem unit_ne_zero {u : ℂ} (h : normSq u = 1) : u ≠ 0 := by
  intro hz
  rw [hz] at h
  simp at h

/-- **The write-up's squared tangency condition, from the Vieta pair relation.** -/
theorem tangency_eq_of_pair_rel {d : ℝ} {u : ℂ} (hu1 : normSq u = 1)
    (hrel : (2 * (d : ℂ) * u) ^ 2 - (31 / 20) * (1 + u ^ 2) * (2 * (d : ℂ) * u)
      + (3 / 5) * (1 + (u ^ 2) ^ 2) + (417 / 400) * u ^ 2 = 0) :
    (d - (31 / 40) * u.re) ^ 2
      = (1 / 25) * u.re ^ 2 + (63 / 1600) * u.im ^ 2 := by
  have hu := unit_sq_add_one hu1
  have hcs : u.re ^ 2 + u.im ^ 2 = 1 := by
    have := hu1
    rw [Complex.normSq_apply] at this
    nlinarith [this]
  have hE : (2 * (d : ℂ) * u) ^ 2 - (31 / 20) * (1 + u ^ 2) * (2 * (d : ℂ) * u)
      + (3 / 5) * (1 + (u ^ 2) ^ 2) + (417 / 400) * u ^ 2
      = u ^ 2 * ((4 * d ^ 2 - (31 / 5) * d * u.re + (12 / 5) * u.re ^ 2 - 63 / 400 : ℝ) : ℂ) := by
    push_cast
    linear_combination (-(31 / 10) * (d : ℂ) * u + (3 / 5) * u ^ 2 + (6 / 5) * (u.re : ℂ) * u
      + 3 / 5) * hu
  rw [hE] at hrel
  have hune : (u : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (unit_ne_zero hu1)
  have hz : ((4 * d ^ 2 - (31 / 5) * d * u.re + (12 / 5) * u.re ^ 2 - 63 / 400 : ℝ) : ℂ) = 0 := by
    rcases mul_eq_zero.mp hrel with h | h
    · exact absurd h hune
    · exact h
  have hTr : 4 * d ^ 2 - (31 / 5) * d * u.re + (12 / 5) * u.re ^ 2 - 63 / 400 = 0 :=
    Complex.ofReal_eq_zero.mp hz
  linear_combination (1 / 4) * hTr - (63 / 1600) * hcs

/-- **Two planar vectors with vanishing cross product are proportional**, the nonzero one first. -/
theorem param_of_cross_zero {x1 x2 y1 y2 : ℝ} (hx : 0 < x1 ^ 2 + x2 ^ 2)
    (h : x1 * y2 - x2 * y1 = 0) : ∃ t : ℝ, y1 = t * x1 ∧ y2 = t * x2 := by
  have hne : x1 ^ 2 + x2 ^ 2 ≠ 0 := ne_of_gt hx
  refine ⟨(x1 * y1 + x2 * y2) / (x1 ^ 2 + x2 ^ 2), ?_, ?_⟩
  · rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination (-x2) * h
  · rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination x1 * h

/-- **Three distinct points of the unit circle are not collinear.** -/
theorem sdet_ne_zero_of_circle {A B C : ℝ × ℝ}
    (hA : A.1 ^ 2 + A.2 ^ 2 = 1) (hB : B.1 ^ 2 + B.2 ^ 2 = 1) (hC : C.1 ^ 2 + C.2 ^ 2 = 1)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) : sdet A B C ≠ 0 := by
  intro h0
  have hlen : 0 < (B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2 := by
    rcases (show (0 : ℝ) ≤ (B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2 by positivity).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hAB
      have e1 : A.1 = B.1 := by nlinarith [sq_nonneg (B.1 - A.1), sq_nonneg (B.2 - A.2)]
      have e2 : A.2 = B.2 := by nlinarith [sq_nonneg (B.1 - A.1), sq_nonneg (B.2 - A.2)]
      exact Prod.ext e1 e2
  have hcross : (B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1) = 0 := by
    simpa [sdet] using h0
  obtain ⟨t, ht1, ht2⟩ := param_of_cross_zero hlen hcross
  have hQ1 : C.1 = A.1 + t * (B.1 - A.1) := by linarith
  have hQ2 : C.2 = A.2 + t * (B.2 - A.2) := by linarith
  have hid : C.1 ^ 2 + C.2 ^ 2 - 1
      = t * (t - 1) * ((B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2) := by
    rw [hQ1, hQ2]
    linear_combination (1 - t) * hA + t * hB
  rw [hC, sub_self] at hid
  have ht : t * (t - 1) = 0 := by
    rcases mul_eq_zero.mp hid.symm with h | h
    · exact h
    · exact absurd h (ne_of_gt hlen)
  rcases mul_eq_zero.mp ht with h | h
  · apply hAC
    refine Prod.ext ?_ ?_
    · rw [hQ1, h]; ring
    · rw [hQ2, h]; ring
  · apply hBC
    have ht1' : t = 1 := by linarith
    refine Prod.ext ?_ ?_
    · rw [hQ1, ht1']; ring
    · rw [hQ2, ht1']; ring

/-! **The side data never uses the family structure.**  `side_data_aux` was first written taking
a `Family x y z`; the linter reported the argument unused, and it is: the tangency of a side
depends only on the PAIR relation, which arrives separately.  Dropping it removes the third root
from the statement entirely. -/

/-- One side, for a FIXED square root `u` already known to be the supporting branch. -/
theorem side_data_aux {x y : ℂ} (hnx : normSq x = 1) (hny : normSq y = 1)
    (hrel : (x + y) ^ 2 - (31 / 20) * (1 + x * y) * (x + y) + (3 / 5) * (1 + (x * y) ^ 2)
      + (417 / 400) * (x * y) = 0)
    {u : ℂ} (hu2 : u ^ 2 = x * y) (hu1 : normSq u = 1)
    (hbr : (31 / 40) * u.re ≤ ((starRingEnd ℂ) u * (x + y)).re / 2) :
    ∃ th d : ℝ,
      ((x.re, x.im) : ℝ × ℝ) ∈ lineTD th d ∧ ((y.re, y.im) : ℝ × ℝ) ∈ lineTD th d ∧
        (∀ Q ∈ K0set, Q.1 * Real.cos th + Q.2 * Real.sin th ≤ d) ∧
        (∃ Q ∈ K0set, Q ∈ lineTD th d) := by
  have hxne : x ≠ 0 := unit_ne_zero hnx
  have hyne : y ≠ 0 := unit_ne_zero hny
  have hcx : (starRingEnd ℂ) x = x⁻¹ := conj_eq_inv_of_normSq_one hnx
  have hcy : (starRingEnd ℂ) y = y⁻¹ := conj_eq_inv_of_normSq_one hny
  set d : ℝ := ((starRingEnd ℂ) u * (x + y)).re / 2 with hddef
  have hcos : Real.cos (Complex.arg u) = u.re := cos_arg_of_normSq_one hu1
  have hsin : Real.sin (Complex.arg u) = u.im := sin_arg_of_normSq_one hu1
  -- the two vertices lie on the chord
  have hinvx : (x * y) * x⁻¹ = y := by
    rw [mul_comm x y, mul_assoc, mul_inv_cancel₀ hxne, mul_one]
  have hinvy : (x * y) * y⁻¹ = x := by
    rw [mul_assoc, mul_inv_cancel₀ hyne, mul_one]
  have hchx : x + (x * y) * (starRingEnd ℂ) x = x + y := by
    rw [hcx, hinvx]
  have hchy : y + (x * y) * (starRingEnd ℂ) y = x + y := by
    rw [hcy, hinvy]; ring
  have hmx := (chord_eq_lineTD hnx hny hu2 hu1 x).mp hchx
  have hmy := (chord_eq_lineTD hnx hny hu2 hu1 y).mp hchy
  -- the chord's offset really is `2d` times the root
  have him := conj_mul_sum_im hnx hny hu2 hu1
  have hw : (starRingEnd ℂ) u * (x + y) = ((2 * d : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re, hddef]; ring
    · rw [Complex.ofReal_im]; exact him
  have hmc : u * (starRingEnd ℂ) u = 1 := by rw [Complex.mul_conj, hu1]; norm_num
  have hq : x + y = 2 * (d : ℂ) * u := by
    calc x + y = (u * (starRingEnd ℂ) u) * (x + y) := by rw [hmc]; ring
      _ = u * ((starRingEnd ℂ) u * (x + y)) := by ring
      _ = u * ((2 * d : ℝ) : ℂ) := by rw [hw]
      _ = 2 * (d : ℂ) * u := by push_cast; ring
  have hrel' : (2 * (d : ℂ) * u) ^ 2 - (31 / 20) * (1 + u ^ 2) * (2 * (d : ℂ) * u)
      + (3 / 5) * (1 + (u ^ 2) ^ 2) + (417 / 400) * u ^ 2 = 0 := by
    rw [← hq, hu2]; exact hrel
  have htan := tangency_eq_of_pair_rel hu1 hrel'
  have hd' : (31 / 40) * Real.cos (Complex.arg u) ≤ d := by rw [hcos]; exact hbr
  have hcond : (d - (31 / 40) * Real.cos (Complex.arg u)) ^ 2
      = (1 / 25) * Real.cos (Complex.arg u) ^ 2
        + (63 / 1600) * Real.sin (Complex.arg u) ^ 2 := by
    rw [hcos, hsin]; exact htan
  obtain ⟨hsupp, htouch⟩ := (tangency_condition hd').mpr hcond
  exact ⟨Complex.arg u, d, hmx, hmy, hsupp, htouch⟩

/-- **One side of a family triangle, packaged**: an angle and an offset whose line carries the two
vertices, supports the caustic, and touches it.  The supporting branch is chosen by picking the
right square root of `xy`. -/
theorem side_data {x y : ℂ} (hnx : normSq x = 1) (hny : normSq y = 1)
    (hrel : (x + y) ^ 2 - (31 / 20) * (1 + x * y) * (x + y) + (3 / 5) * (1 + (x * y) ^ 2)
      + (417 / 400) * (x * y) = 0) :
    ∃ th d : ℝ,
      ((x.re, x.im) : ℝ × ℝ) ∈ lineTD th d ∧ ((y.re, y.im) : ℝ × ℝ) ∈ lineTD th d ∧
        (∀ Q ∈ K0set, Q.1 * Real.cos th + Q.2 * Real.sin th ≤ d) ∧
        (∃ Q ∈ K0set, Q ∈ lineTD th d) := by
  classical
  have hxy : normSq (x * y) = 1 := by rw [Complex.normSq_mul, hnx, hny]; norm_num
  obtain ⟨u0, hu02, hu01⟩ := exists_unit_sqrt hxy
  by_cases hbr : (31 / 40) * u0.re ≤ ((starRingEnd ℂ) u0 * (x + y)).re / 2
  · exact side_data_aux hnx hny hrel hu02 hu01 hbr
  · have hu12 : (-u0) ^ 2 = x * y := by rw [neg_sq]; exact hu02
    have hu11 : normSq (-u0) = 1 := by simpa using hu01
    have hbr' : (31 / 40) * (-u0).re
        ≤ ((starRingEnd ℂ) (-u0) * (x + y)).re / 2 := by
      have he : ((starRingEnd ℂ) (-u0) * (x + y)).re
          = -((starRingEnd ℂ) u0 * (x + y)).re := by
        rw [map_neg, neg_mul, Complex.neg_re]
      rw [he, Complex.neg_re]
      linarith [not_le.mp hbr]
    exact side_data_aux hnx hny hrel hu12 hu11 hbr'

/-- Every root of a `Family` is on the unit circle. -/
theorem Family.normSq_fst {a b c : ℂ} (h : Family a b c) : normSq a = 1 := by
  have hmc := Complex.mul_conj a
  rw [h.ua, mul_inv_cancel₀ h.ne_a] at hmc
  exact_mod_cast hmc.symm

/-- **THE CAUSTIC IS INSIDE EVERY NONDEGENERATE FAMILY TRIANGLE.**  Every point of `K₀` is a
convex combination of the three vertices.  Distinctness is a hypothesis because `Family` does not
require it; everything else comes from the two Vieta relations. -/
theorem caustic_inside_family_triangle {a b c : ℂ} (h : Family a b c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {P : ℝ × ℝ} (hP : P ∈ K0set) :
    ∃ al be ga : ℝ, 0 ≤ al ∧ 0 ≤ be ∧ 0 ≤ ga ∧ al + be + ga = 1 ∧
      P.1 = al * a.re + be * b.re + ga * c.re ∧
      P.2 = al * a.im + be * b.im + ga * c.im := by
  have hna : normSq a = 1 := h.normSq_fst
  have hnb : normSq b = 1 := h.rotate.normSq_fst
  have hnc : normSq c = 1 := h.rotate.rotate.normSq_fst
  have sq_of : ∀ w : ℂ, normSq w = 1 → w.re ^ 2 + w.im ^ 2 = 1 := by
    intro w hw
    rw [Complex.normSq_apply] at hw
    nlinarith [hw]
  have hA : ((a.re, a.im) : ℝ × ℝ).1 ^ 2 + ((a.re, a.im) : ℝ × ℝ).2 ^ 2 = 1 := sq_of a hna
  have hB : ((b.re, b.im) : ℝ × ℝ).1 ^ 2 + ((b.re, b.im) : ℝ × ℝ).2 ^ 2 = 1 := sq_of b hnb
  have hC : ((c.re, c.im) : ℝ × ℝ).1 ^ 2 + ((c.re, c.im) : ℝ × ℝ).2 ^ 2 = 1 := sq_of c hnc
  have ne_of : ∀ w v : ℂ, w ≠ v → ((w.re, w.im) : ℝ × ℝ) ≠ ((v.re, v.im) : ℝ × ℝ) := by
    intro w v hwv hEq
    exact hwv (Complex.ext (congrArg Prod.fst hEq) (congrArg Prod.snd hEq))
  have hD := sdet_ne_zero_of_circle hA hB hC (ne_of a b hab) (ne_of a c hac) (ne_of b c hbc)
  obtain ⟨thc, dc, hAc, hBc, hsc, hQc⟩ :=
    side_data hna hnb (family_pair_tangency h)
  obtain ⟨tha, da, hBa, hCa, hsa, hQa⟩ :=
    side_data hnb hnc (family_pair_tangency h.rotate)
  obtain ⟨thb, db, hCb, hAb, hsb, hQb⟩ :=
    side_data hnc hna (family_pair_tangency h.rotate.rotate)
  obtain ⟨Qc, hQcK, hQcL⟩ := hQc
  obtain ⟨Qa, hQaK, hQaL⟩ := hQa
  obtain ⟨Qb, hQbK, hQbL⟩ := hQb
  have hva := vertex_side_of_support hA hB (ne_of a b hab) hBa hAc hBc hQcK hQcL hsa
  have hvb := vertex_side_of_support hB hC (ne_of b c hbc) hCb hBa hCa hQaK hQaL hsb
  have hvc := vertex_side_of_support hC hA (ne_of c a (Ne.symm hac)) hAc hCb hAb hQbK hQbL hsc
  exact K0set_subset_triangle hD hBa hCa hva hsa hCb hAb hvb hsb hAc hBc hvc hsc hP

end Instantiate

section AffineTransport

/-! ### The physical plane: the vertex map is affine on the unit circle

Everything above lives in the `z`-plane, with the unit circle and the caustic `K₀`.  The write-up's
Section 1 says what connects it to the physical picture: *"Apply `(x,y) = (2X,Y)` to the unit
circle.  The inverse image of `K` is `K₀`."*  So the transport is an AFFINE map, not the Joukowski
map it might look like -- and `Z_eq_affine` is why: on the unit circle `z⁻¹ = conj z`, so

    `Z(z) = (3z + z⁻¹)/2 = (3z + conj z)/2 = (2 Re z, Im z)`.

An affine map carries lines to lines and preserves convex combinations, so the tangency and the
containment transport with no new geometry.  `mem_Kset_iff_halved` is the only computation, and it
is an identity rather than an implication: `(X/2 - 31/40)^2/(1/25)` and `(X - 31/20)^2/(4/25)` are
the SAME expression, so `K` and `K₀` define each other.
-/

/-- **On the unit circle the write-up's vertex map is the affine map `(X,Y) -> (2X,Y)`.** -/
theorem Z_eq_affine {z : ℂ} (hz : normSq z = 1) :
    ((3 * z + z⁻¹) / 2).re = 2 * z.re ∧ ((3 * z + z⁻¹) / 2).im = z.im := by
  have hc : z⁻¹ = (starRingEnd ℂ) z := (conj_eq_inv_of_normSq_one hz).symm
  rw [hc]
  constructor
  · simp only [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.add_im, Complex.mul_im, Complex.normSq_ofNat]
    norm_num
    ring
  · simp only [Complex.div_im, Complex.add_im, Complex.mul_im, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, Complex.normSq_ofNat]
    norm_num
    ring

/-- **`K` and `K₀` define each other under `(X,Y) -> (2X,Y)`** -- the two defining expressions are
literally equal, so this is an identity, not an implication. -/
theorem mem_Kset_iff_halved (Q : ℝ × ℝ) : Q ∈ Kset ↔ ((Q.1 / 2, Q.2) : ℝ × ℝ) ∈ K0set := by
  simp only [Kset, K0set, Set.mem_setOf_eq]
  have he : (Q.1 / 2 - 31 / 40) ^ 2 / (1 / 25) + Q.2 ^ 2 / (63 / 1600)
      = (Q.1 - 31 / 20) ^ 2 / (4 / 25) + Q.2 ^ 2 / (63 / 1600) := by ring
  rw [he]

/-- **The write-up's *"and its affine image touches `K`"*.**  A line supporting and touching `K₀`
transports to one supporting and touching `K`. -/
theorem Kset_side_touch {th d : ℝ}
    (hsupp : ∀ P ∈ K0set, P.1 * Real.cos th + P.2 * Real.sin th ≤ d)
    (htouch : ∃ P ∈ K0set, P ∈ lineTD th d) :
    (∀ Q ∈ Kset, (Q.1 / 2) * Real.cos th + Q.2 * Real.sin th ≤ d) ∧
      (∃ Q ∈ Kset, (Q.1 / 2) * Real.cos th + Q.2 * Real.sin th = d) := by
  constructor
  · intro Q hQ
    exact hsupp _ ((mem_Kset_iff_halved Q).mp hQ)
  · obtain ⟨P, hPK, hPL⟩ := htouch
    have hPL' : P.1 * Real.cos th + P.2 * Real.sin th = d := hPL
    have hhalf : (2 * P.1) / 2 = P.1 := by ring
    refine ⟨(2 * P.1, P.2), ?_, ?_⟩
    · rw [mem_Kset_iff_halved]
      show ((2 * P.1) / 2, P.2) ∈ K0set
      rw [hhalf]
      exact hPK
    · show (2 * P.1) / 2 * Real.cos th + P.2 * Real.sin th = d
      rw [hhalf]
      exact hPL'

/-- **THE PHYSICAL STATEMENT: the inner conic `K` is inside every nondegenerate family triangle**,
whose vertices are `Z(a), Z(b), Z(c) = (2 Re a, Im a), …`.  Affine maps preserve convex
combinations, so this is `caustic_inside_family_triangle` transported. -/
theorem Kset_inside_family_triangle {a b c : ℂ} (h : Family a b c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {Q : ℝ × ℝ} (hQ : Q ∈ Kset) :
    ∃ al be ga : ℝ, 0 ≤ al ∧ 0 ≤ be ∧ 0 ≤ ga ∧ al + be + ga = 1 ∧
      Q.1 = al * (2 * a.re) + be * (2 * b.re) + ga * (2 * c.re) ∧
      Q.2 = al * a.im + be * b.im + ga * c.im := by
  obtain ⟨al, be, ga, h1, h2, h3, hsum, hx, hy⟩ :=
    caustic_inside_family_triangle h hab hac hbc ((mem_Kset_iff_halved Q).mp hQ)
  simp only at hx hy
  exact ⟨al, be, ga, h1, h2, h3, hsum, by linarith [hx], hy⟩

end AffineTransport

section Distinct

/-! ### The three roots are distinct -- and the Blaschke winding argument is NOT needed

The write-up gets distinctness from the degree-three Blaschke product
`B(z) = z(z-f)(z-g)/((1-fz)(1-gz))` by way of its *"strictly positive argument derivative"* and
*"total argument change `6 pi`"*.  The second is a winding-number statement, and it is exactly the
apparatus this module was built to avoid.  **Only the first is needed for distinctness, and it is
a rational identity.**

A repeated root `w` of `P_lambda` satisfies `P_lambda(w) = 0` and `P_lambda'(w) = 0`.  Writing
`P_lambda = N - lambda * D` with `N = z(z-f)(z-g)` and `D = (1-fz)(1-gz)`, those say
`N(w) = lambda * D(w)` and `N'(w) = lambda * D'(w)`, so the Wronskian `W = N' * D - N * D'`
vanishes at `w`.  And `W` never vanishes on the unit circle, because

    `W = Pf * Pg + z (1 - f^2) Pg + z (1 - g^2) Pf`,    `Pf = (z-f)(1-fz)`,  `Pg = (z-g)(1-gz)`,

is a polynomial identity (`blaschke_wronskian`), while on the circle `Pf = z * |z - f|^2`
(`mul_conj_line`, since `conj z = 1/z` there).  Substituting,

    `W = z^2 * (|z-f|^2 |z-g|^2 + (9/25) |z-g|^2 + (7/16) |z-f|^2)`,

a strictly positive real times `z^2`.  **The positivity is pointwise and algebraic; no argument
principle, no total argument change, no winding number.**

Two notes on the formalisation.  `mul_conj_line` is stated for a COMPLEX `w` with `conj w = w`
rather than for a real `f` coerced in: the coerced form makes `normSq (z - ((4:R)/5 : C))` and
`normSq (z - (4/5 : C))` distinct terms, and every later rewrite has to chase the difference.
And `blaschke_wronskian` is a `ring` identity in one variable, so the write-up's *"argument
derivative"* never has to be differentiated -- the derivative polynomials are written down and the
identity is checked.
-/

/-- The Wronskian of the Blaschke numerator and denominator, in closed form.  A ring identity. -/
theorem blaschke_wronskian (z : ℂ) :
    (3 * z ^ 2 - (31 / 10) * z + 3 / 5) * ((1 - (4 / 5 : ℂ) * z) * (1 - (3 / 4 : ℂ) * z))
        - (z * (z - (4 / 5 : ℂ)) * (z - (3 / 4 : ℂ))) * (-(31 / 20) + (6 / 5 : ℂ) * z)
      = ((z - (4 / 5 : ℂ)) * (1 - (4 / 5 : ℂ) * z)) * ((z - (3 / 4 : ℂ)) * (1 - (3 / 4 : ℂ) * z))
        + z * (9 / 25) * ((z - (3 / 4 : ℂ)) * (1 - (3 / 4 : ℂ) * z))
        + z * (7 / 16) * ((z - (4 / 5 : ℂ)) * (1 - (4 / 5 : ℂ) * z)) := by
  ring

/-- **On the unit circle `(z - w)(1 - wz) = z |z - w|^2`** for real `w` -- the one place `|z| = 1`
enters, via `conj z = 1/z`. -/
theorem mul_conj_line {z w : ℂ} (hz : normSq z = 1) (hw : (starRingEnd ℂ) w = w) :
    (z - w) * (1 - w * z) = z * ((normSq (z - w) : ℝ) : ℂ) := by
  have hzne : z ≠ 0 := unit_ne_zero hz
  have hc : (starRingEnd ℂ) z = z⁻¹ := conj_eq_inv_of_normSq_one hz
  have hns : ((normSq (z - w) : ℝ) : ℂ) = (z - w) * (starRingEnd ℂ) (z - w) :=
    (Complex.mul_conj _).symm
  have hexp : z * ((z - w) * (z⁻¹ - w)) = (z - w) * (z * z⁻¹ - w * z) := by ring
  rw [hns, map_sub, hc, hw, hexp, mul_inv_cancel₀ hzne]

/-- `|z - w|^2 > 0` on the unit circle whenever `|w| != 1`. -/
theorem normSq_sub_pos {z w : ℂ} (hz : normSq z = 1) (hw : normSq w ≠ 1) :
    0 < normSq (z - w) := by
  rcases (normSq_nonneg (z - w)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hzw : z = w := by
      have h0 := normSq_eq_zero.mp h.symm
      linear_combination h0
    rw [hzw] at hz
    exact hw hz

/-- **The Wronskian never vanishes on the unit circle.** -/
theorem wronskian_ne_zero {z : ℂ} (hz : normSq z = 1) :
    (3 * z ^ 2 - (31 / 10) * z + 3 / 5) * ((1 - (4 / 5 : ℂ) * z) * (1 - (3 / 4 : ℂ) * z))
        - (z * (z - (4 / 5 : ℂ)) * (z - (3 / 4 : ℂ))) * (-(31 / 20) + (6 / 5 : ℂ) * z) ≠ 0 := by
  have hwf : (starRingEnd ℂ) (4 / 5 : ℂ) = (4 / 5 : ℂ) := by
    have hr : (((4 : ℝ) / 5 : ℝ) : ℂ) = (4 / 5 : ℂ) := by norm_num
    rw [← hr, Complex.conj_ofReal]
  have hwg : (starRingEnd ℂ) (3 / 4 : ℂ) = (3 / 4 : ℂ) := by
    have hr : (((3 : ℝ) / 4 : ℝ) : ℂ) = (3 / 4 : ℂ) := by norm_num
    rw [← hr, Complex.conj_ofReal]
  have hnf : normSq (4 / 5 : ℂ) ≠ 1 := by
    rw [Complex.normSq_apply]; norm_num
  have hng : normSq (3 / 4 : ℂ) ≠ 1 := by
    rw [Complex.normSq_apply]; norm_num
  have hSf : 0 < normSq (z - (4 / 5 : ℂ)) := normSq_sub_pos hz hnf
  have hSg : 0 < normSq (z - (3 / 4 : ℂ)) := normSq_sub_pos hz hng
  have hPf := mul_conj_line hz hwf
  have hPg := mul_conj_line hz hwg
  rw [blaschke_wronskian, hPf, hPg]
  have hbig : z * ((normSq (z - (4 / 5 : ℂ)) : ℝ) : ℂ) * (z * ((normSq (z - (3 / 4 : ℂ)) : ℝ) : ℂ))
        + z * (9 / 25) * (z * ((normSq (z - (3 / 4 : ℂ)) : ℝ) : ℂ))
        + z * (7 / 16) * (z * ((normSq (z - (4 / 5 : ℂ)) : ℝ) : ℂ))
      = z ^ 2 * ((normSq (z - (4 / 5 : ℂ)) * normSq (z - (3 / 4 : ℂ))
          + (9 / 25) * normSq (z - (3 / 4 : ℂ))
          + (7 / 16) * normSq (z - (4 / 5 : ℂ)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hbig]
  have hzne : z ^ 2 ≠ 0 := pow_ne_zero 2 (unit_ne_zero hz)
  have hpos : 0 < normSq (z - (4 / 5 : ℂ)) * normSq (z - (3 / 4 : ℂ))
      + (9 / 25) * normSq (z - (3 / 4 : ℂ)) + (7 / 16) * normSq (z - (4 / 5 : ℂ)) := by
    nlinarith [hSf, hSg]
  refine mul_ne_zero hzne ?_
  rw [Ne, Complex.ofReal_eq_zero]
  exact ne_of_gt hpos

/-- The derivative of `P_factor`, as its own ring identity. -/
theorem P_factor_deriv (lam z : ℂ) :
    3 * z ^ 2 - 2 * (31 / 20 + (3 / 5) * lam) * z + (3 / 5 + (31 / 20) * lam)
      = (3 * z ^ 2 - (31 / 10) * z + 3 / 5) - lam * (-(31 / 20) + (6 / 5) * z) := by
  ring

/-- **The first two roots of a family are distinct.**  No winding number. -/
theorem family_ne_fst {a b c : ℂ} (h : Family a b c) : a ≠ b := by
  intro hab
  subst hab
  have hna : normSq a = 1 := h.normSq_fst
  have hs := h.sum
  have hp := h.pair
  -- `a` is a root of `P_L`, and a DOUBLE root, so the derivative vanishes there too
  have hroot : a ^ 3 + (-(31 / 20 + (3 / 5) * (a * a * c))) * a ^ 2
      + (3 / 5 + (31 / 20) * (a * a * c)) * a + (-(a * a * c)) = 0 := by
    linear_combination (a ^ 2) * hs - a * hp
  have hderiv : 3 * a ^ 2 - 2 * (31 / 20 + (3 / 5) * (a * a * c)) * a
      + (3 / 5 + (31 / 20) * (a * a * c)) = 0 := by
    linear_combination (2 * a) * hs - hp
  -- rewrite both through the Blaschke factorisation
  have hN : a * (a - (4 / 5 : ℂ)) * (a - (3 / 4 : ℂ))
      - (a * a * c) * ((1 - (4 / 5 : ℂ) * a) * (1 - (3 / 4 : ℂ) * a)) = 0 := by
    have hpf := P_factor (a * a * c) a
    push_cast at hpf
    rw [← hpf]
    exact hroot
  have hNd : (3 * a ^ 2 - (31 / 10) * a + 3 / 5)
      - (a * a * c) * (-(31 / 20) + (6 / 5) * a) = 0 := by
    rw [← P_factor_deriv (a * a * c) a]
    exact hderiv
  -- hence the Wronskian vanishes at `a`, which it cannot
  refine wronskian_ne_zero hna ?_
  linear_combination ((1 - (4 / 5 : ℂ) * a) * (1 - (3 / 4 : ℂ) * a)) * hNd
    - (-(31 / 20) + (6 / 5 : ℂ) * a) * hN

/-- **The three roots of a family are pairwise distinct.** -/
theorem family_distinct {a b c : ℂ} (h : Family a b c) : a ≠ b ∧ b ≠ c ∧ a ≠ c :=
  ⟨family_ne_fst h, family_ne_fst h.rotate, (family_ne_fst h.rotate.rotate).symm⟩

/-- **THE CAUSTIC IS INSIDE EVERY FAMILY TRIANGLE**, with distinctness no longer assumed. -/
theorem Kset_inside_family_triangle' {a b c : ℂ} (h : Family a b c)
    {Q : ℝ × ℝ} (hQ : Q ∈ Kset) :
    ∃ al be ga : ℝ, 0 ≤ al ∧ 0 ≤ be ∧ 0 ≤ ga ∧ al + be + ga = 1 ∧
      Q.1 = al * (2 * a.re) + be * (2 * b.re) + ga * (2 * c.re) ∧
      Q.2 = al * a.im + be * b.im + ga * c.im := by
  obtain ⟨hab, hbc, hac⟩ := family_distinct h
  exact Kset_inside_family_triangle h hab hac hbc hQ

end Distinct

section Fullness

/-! ### The family is FULL: every point of the circle is a vertex

The write-up's last sentence of Section 2: *"They form a full Poncelet family: every point of `E`
occurs as a vertex, by choosing `lambda = B(z)` for its preimage `z`."*  That is the remaining
family-level obligation, and like distinctness it needs the Blaschke product only as a FORMULA,
never as a map with a winding number.

Given `z` on the unit circle, put `lambda = N(z)/D(z)`.  The denominator is nonzero for a reason
that needs no modulus estimate at all: `1 - (4/5)z = 0` would force `z = 5/4`, whose `normSq` is
`25/16`, not `1`.  Then `normSq lambda = 1` because `normSq N = normSq D` on the circle, which is
`normSq_one_sub_mul` -- itself a one-line consequence of `mul_conj_line`.  Finally `z` is a root
of `P_lambda` by construction, `family_exists` supplies a family for that `lambda`, and the three
roots of a monic cubic are its Vieta triple, so `z` is one of them.
-/

/-- On the unit circle `|1 - wz| = |z - w|` for real `w`. -/
theorem normSq_one_sub_mul {z w : ℂ} (hz : normSq z = 1) (hw : (starRingEnd ℂ) w = w)
    (hS : normSq (z - w) ≠ 0) : normSq (1 - w * z) = normSq (z - w) := by
  have h := congrArg normSq (mul_conj_line hz hw)
  rw [map_mul, map_mul, hz, one_mul, Complex.normSq_ofReal] at h
  exact mul_left_cancel₀ hS h

/-- **Every point of the unit circle is the first vertex of some family.** -/
theorem family_full {z : ℂ} (hz : normSq z = 1) : ∃ b c : ℂ, Family z b c := by
  have hnf : normSq (4 / 5 : ℂ) ≠ 1 := by rw [Complex.normSq_apply]; norm_num
  have hng : normSq (3 / 4 : ℂ) ≠ 1 := by rw [Complex.normSq_apply]; norm_num
  have hwf : (starRingEnd ℂ) (4 / 5 : ℂ) = (4 / 5 : ℂ) := by
    have hr : (((4 : ℝ) / 5 : ℝ) : ℂ) = (4 / 5 : ℂ) := by norm_num
    rw [← hr, Complex.conj_ofReal]
  have hwg : (starRingEnd ℂ) (3 / 4 : ℂ) = (3 / 4 : ℂ) := by
    have hr : (((3 : ℝ) / 4 : ℝ) : ℂ) = (3 / 4 : ℂ) := by norm_num
    rw [← hr, Complex.conj_ofReal]
  have hSf : 0 < normSq (z - (4 / 5 : ℂ)) := normSq_sub_pos hz hnf
  have hSg : 0 < normSq (z - (3 / 4 : ℂ)) := normSq_sub_pos hz hng
  -- the denominator cannot vanish: it would put `z` off the circle
  have hD1 : (1 - (4 / 5 : ℂ) * z) ≠ 0 := by
    intro h0
    have hz54 : z = (5 / 4 : ℂ) := by linear_combination (-(5 / 4 : ℂ)) * h0
    rw [hz54, Complex.normSq_apply] at hz
    norm_num at hz
  have hD2 : (1 - (3 / 4 : ℂ) * z) ≠ 0 := by
    intro h0
    have hz43 : z = (4 / 3 : ℂ) := by linear_combination (-(4 / 3 : ℂ)) * h0
    rw [hz43, Complex.normSq_apply] at hz
    norm_num at hz
  have hD : (1 - (4 / 5 : ℂ) * z) * (1 - (3 / 4 : ℂ) * z) ≠ 0 := mul_ne_zero hD1 hD2
  set N : ℂ := z * (z - (4 / 5 : ℂ)) * (z - (3 / 4 : ℂ)) with hNdef
  set D : ℂ := (1 - (4 / 5 : ℂ) * z) * (1 - (3 / 4 : ℂ) * z) with hDdef
  set lam : ℂ := N * D⁻¹ with hlamdef
  have hND : N = lam * D := by
    rw [hlamdef]
    field_simp
  -- `normSq N = normSq D` on the circle, so `lambda` is on the circle too
  have hNN : normSq N = normSq (z - (4 / 5 : ℂ)) * normSq (z - (3 / 4 : ℂ)) := by
    rw [hNdef, map_mul, map_mul, hz, one_mul]
  have hDD : normSq D = normSq (z - (4 / 5 : ℂ)) * normSq (z - (3 / 4 : ℂ)) := by
    rw [hDdef, map_mul, normSq_one_sub_mul hz hwf (ne_of_gt hSf),
      normSq_one_sub_mul hz hwg (ne_of_gt hSg)]
  have hDne : normSq D ≠ 0 := by rw [hDD]; positivity
  have hlam : normSq lam = 1 := by
    have h : normSq N = normSq lam * normSq D := by rw [hND, map_mul]
    rw [hNN, ← hDD] at h
    have h2 : normSq lam * normSq D = 1 * normSq D := by rw [← h, one_mul]
    exact mul_right_cancel₀ hDne h2
  -- `z` is a root of `P_lambda`
  obtain ⟨a, b, c, hfam, habc⟩ := family_exists lam hlam
  have hprod : (z - a) * (z - b) * (z - c) = 0 := by
    have hs := hfam.sum
    have hp := hfam.pair
    have hpf := P_factor lam z
    push_cast at hpf
    have hroot : z * (z - (4 / 5 : ℂ)) * (z - (3 / 4 : ℂ))
        - lam * ((1 - (4 / 5 : ℂ) * z) * (1 - (3 / 4 : ℂ) * z)) = 0 := by
      rw [← hNdef, ← hDdef]
      linear_combination hND
    rw [← hpf] at hroot
    linear_combination hroot - (z ^ 2) * hs + z * hp
      + (-(3 / 5) * z ^ 2 + (31 / 20) * z - 1) * habc
  rcases mul_eq_zero.mp hprod with h | hc0
  · rcases mul_eq_zero.mp h with ha0 | hb0
    · have : z = a := by linear_combination ha0
      rw [this]
      exact ⟨b, c, hfam⟩
    · have : z = b := by linear_combination hb0
      rw [this]
      exact ⟨c, a, hfam.rotate⟩
  · have : z = c := by linear_combination hc0
    rw [this]
    exact ⟨a, b, hfam.rotate.rotate⟩

end Fullness

section Capstone

/-! ### The counterexample, assembled

Every clause of the write-up is now a theorem about explicit objects, so they can be stated
together.  The only thing the statement quantifies over is the family parameter; nothing is
assumed about it beyond `|lambda| = 1`.

The side clause is stated for the pair `(a, b)` inside a `forall a b c, Family a b c -> ...`.
That is not a weakening: `Family` is symmetric (`Family.rotate`), so applying the statement to the
rotated family gives the `(b, c)` and `(c, a)` sides.
-/

/-- One side of a family triangle touches `K` and supports it. -/
theorem side_touches_Kset {x y z : ℂ} (h : Family x y z) :
    ∃ th d : ℝ,
      ((x.re, x.im) : ℝ × ℝ) ∈ lineTD th d ∧ ((y.re, y.im) : ℝ × ℝ) ∈ lineTD th d ∧
        (∀ Q ∈ Kset, (Q.1 / 2) * Real.cos th + Q.2 * Real.sin th ≤ d) ∧
        (∃ Q ∈ Kset, (Q.1 / 2) * Real.cos th + Q.2 * Real.sin th = d) := by
  obtain ⟨th, d, hx, hy, hsupp, htouch⟩ :=
    side_data h.normSq_fst h.rotate.normSq_fst (family_pair_tangency h)
  obtain ⟨hs, ht⟩ := Kset_side_touch hsupp htouch
  exact ⟨th, d, hx, hy, hs, ht⟩

/-- **THE COUNTEREXAMPLE TO GARCIA-HELMAN-REZNIK CONJECTURE 1, ASSEMBLED.**

`E : x^2/4 + y^2 = 1` and `K : (x - 31/20)^2/(4/25) + y^2/(63/1600) = 1` carry a Poncelet
triangle family -- full, nondegenerate, inscribed in `E`, circumscribing `K` -- every member of
which has its orthocenter at the SAME point `(31/16, 0)`; and the pair is in none of the three
configurations of the conjecture.

Nothing is carried: the module has no `Prop` parameter anywhere, and the only hypothesis in sight
is `|lambda| = 1` on the family parameter. -/
theorem counterexample :
    ((¬ MacBeathPair Eset Kset ∧ ¬ FocalX4Pair Eset Kset ∧ ¬ DualPair Eset Kset)
        ∧ ¬ IsFocusE ((31 : ℝ) / 16, (0 : ℝ))
        ∧ ((31 : ℝ) / 16, (0 : ℝ)) ∈ KsetInterior)
      ∧ (∀ lam : ℂ, normSq lam = 1 → ∃ a b c : ℂ, Family a b c ∧ a * b * c = lam)
      ∧ (∀ z : ℂ, normSq z = 1 → ∃ b c : ℂ, Family z b c)
      ∧ (∀ a b c : ℂ, Family a b c →
          (a ≠ b ∧ b ≠ c ∧ a ≠ c)
          ∧ ((V a).re ^ 2 / 4 + (V a).im ^ 2 = 1)
          ∧ (((31 : ℂ) / 16 - V a).re * (V b - V c).re
              + ((31 : ℂ) / 16 - V a).im * (V b - V c).im = 0)
          ∧ (∃ th d : ℝ,
              ((a.re, a.im) : ℝ × ℝ) ∈ lineTD th d ∧ ((b.re, b.im) : ℝ × ℝ) ∈ lineTD th d ∧
                (∀ Q ∈ Kset, (Q.1 / 2) * Real.cos th + Q.2 * Real.sin th ≤ d) ∧
                (∃ Q ∈ Kset, (Q.1 / 2) * Real.cos th + Q.2 * Real.sin th = d))
          ∧ (∀ Q ∈ Kset, ∃ al be ga : ℝ, 0 ≤ al ∧ 0 ≤ be ∧ 0 ≤ ga ∧ al + be + ga = 1 ∧
              Q.1 = al * (2 * a.re) + be * (2 * b.re) + ga * (2 * c.re) ∧
              Q.2 = al * a.im + be * b.im + ga * c.im)) := by
  refine ⟨section_four, fun lam hlam => family_exists lam hlam,
    fun z hz => family_full hz, fun a b c h => ?_⟩
  exact ⟨family_distinct h, V_on_ellipse h.ne_a h.ua, perp h, side_touches_Kset h,
    fun Q hQ => Kset_inside_family_triangle' h hQ⟩

end Capstone

end Principia.MathDB.P365004
