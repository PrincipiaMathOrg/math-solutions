import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# MathDB 351604 — a nonconvex incenter locus with nested circular caustics

Write-up: `mathdb-open-problems/problems/351604/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`.  It **refutes Conjecture 2** of the
source (p. 23): that the incenter locus of a bic-III triangle family is a convex curve.

The write-up states its reading explicitly, and this module follows it: *convex curve* is
meant in the usual **boundary-of-a-convex-set** sense, not "the curve is itself a convex
set".  That is the weaker reading, so refuting it refutes more.

## The witness

`h = 2/5`, `r = 7/12`, `A = 1 + h² - r² = 2951/3600`, the pencil
`C_λ : x² + y² - 2λhx - 1 + λA = 0` with circumcircle `C₀` the unit circle and caustics
`C₁`, `C_{7/4}`.  `Q` and `Z` are the second intersections of the two tangent chords from
`P(t)`, and `I = (aP + bQ + cZ)/(a+b+c)` is the incenter.

## The refutation is a support-line argument, and that is what is proved here

If the locus were the boundary of a convex set, some line would support it at `I t₀`.
Then:

* `dotp_deriv_eq_zero` — the supporting normal `n` is orthogonal to the tangent, because
  `t ↦ ⟪n, I t⟫` attains a **maximum** at `t₀`, so its derivative vanishes there.  (This
  is the write-up's "apply the support inequality for both signs of `ε` and differentiate
  at zero", done as a local-max argument instead.)
* `exists_cross_repr` — in the plane a nonzero `n` orthogonal to a nonzero `v` satisfies
  `⟪n, w⟫ = c·[v, w]` for some `c ≠ 0`.
* `no_support` — so all the cross products `[I' t₀, I t - I t₀]` would share a sign.  Two
  of strictly opposite sign is a contradiction.

## What is carried

`Setup` carries the three numerical enclosures, which the write-up obtains by rigorous
integer interval arithmetic (its `verify.py`, outward-rounded at denominator `10⁶⁰`), and
the fact that a convex set has a supporting line at each of its boundary points.

`Campaigns/MathDB-Formalization/verify_351604.py` **reproduces all three enclosures
independently**, with its own exact-rational interval arithmetic and integer square-root
bounds checked by squaring:
`I_x'(-1/3) ≈ 0.206784605635`, `[I'(-1/3), I(0) - I(-1/3)] ≈ 0.014992242972`,
`[I'(-1/3), I(-1/2) - I(-1/3)] ≈ -0.000144055818` — matching the write-up's
`(206784605, 206784606)/10⁹`, `(14992242, 14992243)/10⁹` and `(-144056, -144055)/10⁹`.
It also checks the conjecture's own hypotheses: the caustics are strictly nested proper
circles inside the circumcircle, their centres are distinct, and `P`, `Q`, `Z` stay
pairwise distinct so no triangle degenerates.
-/

namespace Principia.MathDB.P351604

/-! ## Plane vector algebra -/

/-- `[u,v] = u_x v_y - u_y v_x`. -/
def cross (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- The Euclidean inner product on `ℝ × ℝ`. -/
def dotp (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

/-- The quarter turn. -/
def J (u : ℝ × ℝ) : ℝ × ℝ := (-u.2, u.1)

theorem dotp_J (u v : ℝ × ℝ) : dotp (J u) v = cross u v := by
  unfold dotp J cross; ring

theorem dotp_sub (n u v : ℝ × ℝ) : dotp n (u - v) = dotp n u - dotp n v := by
  unfold dotp
  simp [Prod.fst_sub, Prod.snd_sub]
  ring

theorem ne_zero_of_fst_pos {v : ℝ × ℝ} (h : 0 < v.1) : v ≠ 0 := by
  intro hv
  rw [hv] at h
  simp at h

/-! ## The supporting normal is orthogonal to the tangent -/

/-- If `t ↦ ⟪n, I t⟫` is maximal at `t₀`, its derivative there vanishes; so a supporting
normal is orthogonal to the tangent. -/
theorem dotp_deriv_eq_zero {I : ℝ → ℝ × ℝ} {I' : ℝ × ℝ} {t₀ : ℝ} (n : ℝ × ℝ)
    (hd : HasDerivAt I I' t₀) (hsup : ∀ t, dotp n (I t) ≤ dotp n (I t₀)) :
    dotp n I' = 0 := by
  have h1 : HasDerivAt (fun t => (I t).1) I'.1 t₀ := hd.fst
  have h2 : HasDerivAt (fun t => (I t).2) I'.2 t₀ := hd.snd
  have hf : HasDerivAt (fun t => dotp n (I t)) (dotp n I') t₀ := by
    show HasDerivAt (fun t => n.1 * (I t).1 + n.2 * (I t).2)
      (n.1 * I'.1 + n.2 * I'.2) t₀
    have hsum := (HasDerivAt.const_mul n.1 h1).add (HasDerivAt.const_mul n.2 h2)
    simp only [Pi.add_def] at hsum
    exact hsum
  have hmax : IsLocalMax (fun t => dotp n (I t)) t₀ :=
    Filter.Eventually.of_forall hsup
  exact hmax.hasDerivAt_eq_zero hf

/-! ## Orthogonality in the plane -/

/-- A nonzero `n` orthogonal to a nonzero `v` computes the cross product with `v`, up to
a nonzero scalar. -/
theorem exists_cross_repr {n v : ℝ × ℝ} (hn : n ≠ 0) (h : dotp n v = 0) (hv1 : v ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ w : ℝ × ℝ, dotp n w = c * cross v w := by
  have hh : n.1 * v.1 + n.2 * v.2 = 0 := h
  by_cases hv : v.1 = 0
  · have hv2 : v.2 ≠ 0 := by
      intro h2
      exact hv1 (Prod.ext_iff.mpr ⟨hv, h2⟩)
    have hn2 : n.2 = 0 := by
      rw [hv, mul_zero, zero_add] at hh
      exact (mul_eq_zero.mp hh).resolve_right hv2
    have hn1 : n.1 ≠ 0 := by
      intro h1
      exact hn (Prod.ext_iff.mpr ⟨h1, hn2⟩)
    refine ⟨-n.1 / v.2, div_ne_zero (neg_ne_zero.mpr hn1) hv2, fun w => ?_⟩
    unfold dotp cross
    rw [hv, hn2]
    field_simp
    ring
  · refine ⟨n.2 / v.1, ?_, fun w => ?_⟩
    · refine div_ne_zero ?_ hv
      intro h2
      rw [h2, zero_mul, add_zero] at hh
      have hn1 : n.1 = 0 := (mul_eq_zero.mp hh).resolve_right hv
      exact hn (Prod.ext_iff.mpr ⟨hn1, h2⟩)
    · unfold dotp cross
      field_simp
      linear_combination w.1 * hh

/-! ## The refutation -/

/-- **No line supports the locus at `I t₀`** once two of its points lie strictly on
opposite sides of the tangent there. -/
theorem no_support {I : ℝ → ℝ × ℝ} {I' : ℝ × ℝ} {t₀ t₁ t₂ : ℝ}
    (hd : HasDerivAt I I' t₀) (hI' : I' ≠ 0)
    (h1 : 0 < cross I' (I t₁ - I t₀)) (h2 : cross I' (I t₂ - I t₀) < 0) :
    ¬ ∃ n : ℝ × ℝ, n ≠ 0 ∧ ∀ t, dotp n (I t) ≤ dotp n (I t₀) := by
  rintro ⟨n, hn, hsup⟩
  have horth := dotp_deriv_eq_zero n hd hsup
  obtain ⟨c, hc, hrep⟩ := exists_cross_repr hn horth hI'
  have e1 : dotp n (I t₁ - I t₀) ≤ 0 := by
    rw [dotp_sub]
    linarith [hsup t₁]
  have e2 : dotp n (I t₂ - I t₀) ≤ 0 := by
    rw [dotp_sub]
    linarith [hsup t₂]
  rw [hrep] at e1 e2
  rcases lt_trichotomy c 0 with hlt | heq | hgt
  · nlinarith
  · exact hc heq
  · nlinarith

/-! ## The carried numerics, and the conjecture -/

/-- The three enclosures, and the convexity reading. -/
structure Setup where
  /-- the incenter locus of the bic-III family -/
  I : ℝ → ℝ × ℝ
  /-- its derivative at `t₀ = -1/3` -/
  Ider : ℝ × ℝ
  t₀ : ℝ
  t₁ : ℝ
  t₂ : ℝ
  hd : HasDerivAt I Ider t₀
  /-- **CARRIED** (rigorous interval arithmetic, reproduced by `verify_351604.py`):
  `I_x'(-1/3) ∈ (206784605, 206784606)/10⁹`, so the tangent is nonzero. -/
  hIx : 0 < Ider.1
  /-- **CARRIED**: `[I'(-1/3), I(0) - I(-1/3)] ∈ (14992242, 14992243)/10⁹`. -/
  hcross₁ : 0 < cross Ider (I t₁ - I t₀)
  /-- **CARRIED**: `[I'(-1/3), I(-1/2) - I(-1/3)] ∈ (-144056, -144055)/10⁹`. -/
  hcross₂ : cross Ider (I t₂ - I t₀) < 0
  /-- the conjecture's assertion, in the write-up's stated reading -/
  ConvexCurve : Prop
  /-- **CARRIED**: a convex set has a supporting line at each of its boundary points. -/
  support_of_convex : ConvexCurve →
    ∃ n : ℝ × ℝ, n ≠ 0 ∧ ∀ t, dotp n (I t) ≤ dotp n (I t₀)

namespace Setup

variable (S : Setup)

theorem Ider_ne_zero : S.Ider ≠ 0 := ne_zero_of_fst_pos S.hIx

/-- **THE REFUTATION.**  The incenter locus of this bic-III family is not the boundary of
a convex set. -/
theorem refutation : ¬ S.ConvexCurve := fun hc =>
  no_support S.hd S.Ider_ne_zero S.hcross₁ S.hcross₂ (S.support_of_convex hc)

end Setup

end Principia.MathDB.P351604
