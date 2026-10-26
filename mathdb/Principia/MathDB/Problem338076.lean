import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-!
# MathDB #338076 — Lachaume's diagonal-concavity conjecture is FALSE

Write-up: `mathdb-open-problems/problems/338076/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-28 from the
third hundred, see `THIRD100-ENROLMENT.md`).
Source: Lachaume, **Conjecture 1** (stated pp. 3 and 8, repeated p. 18): for nonnegative
coefficients `a₀, …, a_p`, concavity of `(∑ₖ aₖ σₖ(x))^{1/p}` on the diagonal `x₁ = ⋯ = xₙ > 0`
is *equivalent* to concavity on `Γₙ = (0,∞)ⁿ`.

**The counterexample is the write-up's own**, at `n = p = 4`:

`F(x) = 20 + 40σ₁(x) + 21σ₂(x) + 40σ₃(x) + 20σ₄(x)`.

`F^{1/4}` is strictly concave along the whole positive diagonal, yet not concave on `Γ₄`.

## The refuting half needs no calculus, and that is a deliberate change of route

The write-up refutes concavity by a **second derivative**: along the line through
`(2, ½, ½, ½)` in direction `(1,1,1,1)` it computes `H(u) = 20u⁴ + 230u³ + 621u² + 713u + 1235/4`
and `4H(0)H''(0) − 3H'(0)² = 8763 > 0`. That is correct — `verify_338076.py` reproduces `H` by
exact interpolation and confirms the arithmetic — but it is an awkward thing to formalise, because
Mathlib has **no converse to `concaveOn_of_deriv2_nonpos`**: from `ConcaveOn` one cannot directly
get `deriv^[2] ≤ 0`, so the write-up's contradiction has no one-line Lean counterpart.

Concavity is violated *at a point*, so a **midpoint** violation is the thing to exhibit, and
`ConcaveOn` applies to it directly. The write-up's own witness is far too tight for that — its
midpoint margin at `h = 1/10` is `1.2 · 10⁻⁴` — so a wider one was searched for and checked
exactly:

`x₋ = (7, ¼, ¼, ¼)`,  `x₀ = (10, ¾, ¾, ¾)`,  `x₊ = (13, 5/4, 5/4, 5/4)`,

all strictly inside `Γ₄`, with `x₀` **exactly** the midpoint and

`F(x₋) = 999/2`,  `F(x₀) = 28707/16`,  `F(x₊) = 38685/8`,

whose midpoint margin is `2.5 · 10⁻²` — about **200 times** the write-up's. That slack is what
makes the fourth roots avoidable: each is compared with a rational of denominator `1000` by a
single fourth-power inequality (`(4727/1000)⁴ < 999/2`, `28707/16 < (6509/1000)⁴`,
`(8338/1000)⁴ < 38685/8`), and `4727/1000 + 8338/1000 > 2 · 6509/1000` with slack `47/1000`
closes it by `linarith`. **`not_concaveOn_orthant` is therefore unconditional and contains no
derivative at all.**

## The diagonal half is where the calculus lives

`strictConcaveOn_of_deriv2_neg` is the tool, and the sign it needs is the write-up's identity —
a *polynomial* identity, hence `ring`:

`3(Q′)² − 4QQ″ = 48[1180(t²−1)² + 80t(t²+1) + 83t²]`,
with `Q(t) = F(t,t,t,t) = 20t⁴+160t³+126t²+160t+20`,

whose right-hand side is manifestly positive for `t > 0`. Since
`(h^{1/4})″ = (4hh″ − 3(h′)²)/(16h^{7/4})`,
that is exactly `(Q^{1/4})″ < 0`.

## 215 check — what the write-up claims, and one place I over-read it

* **Every coefficient and coordinate is strictly positive** and the failure is *interior*, so no
  endpoint convention or vanishing coefficient is doing the work. One counterexample settles a
  universally quantified equivalence; the forward implication (orthant ⟹ diagonal) stays true and
  is not contradicted here.
* **`Q` is "not real-rooted" does NOT mean `Q` has no real root.** My first verifier asserted the
  latter and it *failed*: `Q(−1) = −154 < 0 < Q(0) = 20`, so `Q` has two negative real roots. The
  write-up's claim is the weaker and correct one — via `Q(t)/t² = 20w² + 160w + 86` with
  `w = t + t⁻¹`, which changes sign on `(−2, 2)` (values `−154` and `486`), and `|w| < 2` makes the
  discriminant `w² − 4` of `t² − wt + 1` negative, so *that* factor contributes a nonreal pair.
  Two real roots and two nonreal: not real-rooted. The remark's purpose in the source is to show
  the example does not challenge the real-rootedness sufficient condition, and it survives.
* `Q` is **palindromic** (`20, 160, 126, 160, 20`), which is why the `w`-substitution is available
  at all; the verifier checks that too.
-/

namespace Principia.MathDB.P338076

open Real

/-! ### The form `F` -/

/-- `σ₁` of a `4`-tuple. -/
def e1 (x : Fin 4 → ℝ) : ℝ := x 0 + x 1 + x 2 + x 3

/-- `σ₂` of a `4`-tuple. -/
def e2 (x : Fin 4 → ℝ) : ℝ :=
  x 0 * x 1 + x 0 * x 2 + x 0 * x 3 + x 1 * x 2 + x 1 * x 3 + x 2 * x 3

/-- `σ₃` of a `4`-tuple. -/
def e3 (x : Fin 4 → ℝ) : ℝ :=
  x 0 * x 1 * x 2 + x 0 * x 1 * x 3 + x 0 * x 2 * x 3 + x 1 * x 2 * x 3

/-- `σ₄` of a `4`-tuple. -/
def e4 (x : Fin 4 → ℝ) : ℝ := x 0 * x 1 * x 2 * x 3

/-- The write-up's form, with all five coefficients strictly positive. -/
def F (x : Fin 4 → ℝ) : ℝ := 20 + 40 * e1 x + 21 * e2 x + 40 * e3 x + 20 * e4 x

/-- The open positive orthant `Γ₄`. -/
def Orthant : Set (Fin 4 → ℝ) := {x | ∀ i, 0 < x i}

theorem convex_orthant : Convex ℝ Orthant := by
  intro x hx y hy a b ha hb hab i
  rcases lt_or_eq_of_le ha with ha' | ha'
  · have : 0 < a * x i := mul_pos ha' (hx i)
    have : 0 ≤ b * y i := mul_nonneg hb (le_of_lt (hy i))
    simpa [Pi.add_apply, Pi.smul_apply] using by positivity
  · have hb' : 0 < b := by simp [← ha'] at hab ⊢; linarith
    have : 0 < b * y i := mul_pos hb' (hy i)
    have : 0 ≤ a * x i := mul_nonneg ha (le_of_lt (hx i))
    simpa [Pi.add_apply, Pi.smul_apply] using by positivity

/-! ### The fourth root, and the two rational-sandwich lemmas that replace it -/

/-- The fourth root, as an `rpow`. -/
noncomputable def r4 (v : ℝ) : ℝ := v ^ ((1 : ℝ) / 4)

theorem r4_pow_self {a : ℝ} (ha : 0 ≤ a) : r4 (a ^ (4 : ℕ)) = a := by
  rw [r4, ← Real.rpow_natCast a 4, ← Real.rpow_mul ha]
  norm_num

/-- **Lower sandwich**: a rational whose fourth power undershoots is below the fourth root. -/
theorem lt_r4 {a v : ℝ} (ha : 0 ≤ a) (h : a ^ (4 : ℕ) < v) : a < r4 v := by
  rw [← r4_pow_self ha, r4, r4]
  exact Real.rpow_lt_rpow (by positivity) h (by norm_num)

/-- **Upper sandwich**: a rational whose fourth power overshoots is above the fourth root. -/
theorem r4_lt {b v : ℝ} (hb : 0 ≤ b) (hv : 0 ≤ v) (h : v < b ^ (4 : ℕ)) : r4 v < b := by
  rw [← r4_pow_self hb, r4, r4]
  exact Real.rpow_lt_rpow hv h (by norm_num)

/-! ### The diagonal restriction -/

/-- `Q(t) = F(t,t,t,t)`. -/
def Qd (t : ℝ) : ℝ := 20 * t ^ 4 + 160 * t ^ 3 + 126 * t ^ 2 + 160 * t + 20

/-- `Q′`. -/
def Qd1 (t : ℝ) : ℝ := 80 * t ^ 3 + 480 * t ^ 2 + 252 * t + 160

/-- `Q″`. -/
def Qd2 (t : ℝ) : ℝ := 240 * t ^ 2 + 960 * t + 252

theorem F_diag (t : ℝ) : F (fun _ => t) = Qd t := by
  simp [F, e1, e2, e3, e4, Qd]
  ring

theorem Qd_pos {t : ℝ} (ht : 0 < t) : 0 < Qd t := by
  have : (0:ℝ) < t ^ 4 := by positivity
  have : (0:ℝ) < t ^ 3 := by positivity
  have : (0:ℝ) < t ^ 2 := by positivity
  simp only [Qd]
  linarith

/-- **THE WRITE-UP'S DIAGONAL IDENTITY**, which is a polynomial identity and nothing more. -/
theorem diagonal_identity (t : ℝ) :
    3 * (Qd1 t) ^ 2 - 4 * Qd t * Qd2 t
      = 48 * (1180 * (t ^ 2 - 1) ^ 2 + 80 * t * (t ^ 2 + 1) + 83 * t ^ 2) := by
  simp only [Qd, Qd1, Qd2]
  ring

/-- The certificate whose sign is `−(Q^{1/4})″`: strictly positive on the whole positive axis. -/
theorem diagonal_certificate_pos {t : ℝ} (ht : 0 < t) :
    0 < 3 * (Qd1 t) ^ 2 - 4 * Qd t * Qd2 t := by
  rw [diagonal_identity]
  have h1 : (0:ℝ) ≤ 1180 * (t ^ 2 - 1) ^ 2 := by positivity
  have h2 : (0:ℝ) < 80 * t * (t ^ 2 + 1) := by positivity
  have h3 : (0:ℝ) < 83 * t ^ 2 := by positivity
  linarith

/-! ### The off-diagonal witness — no derivative appears below this line

The three points are collinear with `x₀` the exact midpoint, all strictly inside `Γ₄`, and were
chosen for a midpoint margin about 200 times the write-up's so that the fourth roots can be
compared with rationals of denominator `1000`. -/

noncomputable def XM : Fin 4 → ℝ := ![7, 1/4, 1/4, 1/4]
noncomputable def X0 : Fin 4 → ℝ := ![10, 3/4, 3/4, 3/4]
noncomputable def XP : Fin 4 → ℝ := ![13, 5/4, 5/4, 5/4]

theorem XM_mem : XM ∈ Orthant := by
  intro i; fin_cases i <;> norm_num [XM]

theorem X0_mem : X0 ∈ Orthant := by
  intro i; fin_cases i <;> norm_num [X0]

theorem XP_mem : XP ∈ Orthant := by
  intro i; fin_cases i <;> norm_num [XP]

/-- `x₀` is **exactly** the midpoint, so the concavity inequality applies to it verbatim. -/
theorem X0_midpoint : ((1:ℝ)/2) • XM + ((1:ℝ)/2) • XP = X0 := by
  funext i
  fin_cases i <;> norm_num [XM, XP, X0]

theorem F_XM : F XM = 999 / 2 := by
  have h0 : XM 0 = 7 := rfl
  have h1 : XM 1 = 1/4 := rfl
  have h2 : XM 2 = 1/4 := rfl
  have h3 : XM 3 = 1/4 := rfl
  simp only [F, e1, e2, e3, e4, h0, h1, h2, h3]
  norm_num

theorem F_X0 : F X0 = 28707 / 16 := by
  have h0 : X0 0 = 10 := rfl
  have h1 : X0 1 = 3/4 := rfl
  have h2 : X0 2 = 3/4 := rfl
  have h3 : X0 3 = 3/4 := rfl
  simp only [F, e1, e2, e3, e4, h0, h1, h2, h3]
  norm_num

theorem F_XP : F XP = 38685 / 8 := by
  have h0 : XP 0 = 13 := rfl
  have h1 : XP 1 = 5/4 := rfl
  have h2 : XP 2 = 5/4 := rfl
  have h3 : XP 3 = 5/4 := rfl
  simp only [F, e1, e2, e3, e4, h0, h1, h2, h3]
  norm_num

/-- **THE MIDPOINT VIOLATION.** Each fourth root is pinned against a rational of denominator
`1000` by one fourth-power inequality, and `linarith` finishes with slack `47/1000`. -/
theorem midpoint_violation : 2 * r4 (F X0) < r4 (F XM) + r4 (F XP) := by
  have hA : (4727 : ℝ) / 1000 < r4 (F XM) := by
    rw [F_XM]; exact lt_r4 (by norm_num) (by norm_num)
  have hC : (8338 : ℝ) / 1000 < r4 (F XP) := by
    rw [F_XP]; exact lt_r4 (by norm_num) (by norm_num)
  have hB : r4 (F X0) < (6509 : ℝ) / 1000 := by
    rw [F_X0]; exact r4_lt (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- **`F^{1/4}` IS NOT CONCAVE ON `Γ₄`** — unconditional, and with no derivative in the proof. -/
theorem not_concaveOn_orthant : ¬ ConcaveOn ℝ Orthant (fun x => r4 (F x)) := by
  intro h
  have := h.2 XM_mem XP_mem (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 + 1/2 = 1)
  rw [X0_midpoint] at this
  simp only [smul_eq_mul] at this
  have hv := midpoint_violation
  linarith

/-! ### The diagonal half: strict concavity, where the calculus lives

`(h^{1/4})″ = (4hh″ − 3(h′)²)/(16 h^{7/4})`, so the sign is entirely the certificate's. Nothing
below re-derives the polynomial algebra — `diagonal_certificate_pos` supplies it.

Every def-unfolding here is a `show`, because `simp only [Qd1]` after a `convert` silently made no
progress: a `show` is a definitional change that cannot fail quietly. -/

theorem hasDerivAt_Qd (t : ℝ) : HasDerivAt Qd (Qd1 t) t := by
  have h4 : HasDerivAt (fun s : ℝ => s ^ 4) (4 * t ^ 3) t := by
    simpa using hasDerivAt_pow 4 t
  have h3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
    simpa using hasDerivAt_pow 3 t
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have h1 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have e : Qd1 t = 20 * (4 * t ^ 3) + 160 * (3 * t ^ 2) + 126 * (2 * t) + 160 * 1 := by
    change (80 * t ^ 3 + 480 * t ^ 2 + 252 * t + 160 : ℝ) = _
    ring
  rw [show Qd = fun s : ℝ => 20 * s ^ 4 + 160 * s ^ 3 + 126 * s ^ 2 + 160 * s + 20 from rfl, e]
  exact ((((h4.const_mul 20).add (h3.const_mul 160)).add (h2.const_mul 126)).add
    (h1.const_mul 160)).add_const 20

theorem hasDerivAt_Qd1 (t : ℝ) : HasDerivAt Qd1 (Qd2 t) t := by
  have h3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
    simpa using hasDerivAt_pow 3 t
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have h1 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have e : Qd2 t = 80 * (3 * t ^ 2) + 480 * (2 * t) + 252 * 1 := by
    change (240 * t ^ 2 + 960 * t + 252 : ℝ) = _
    ring
  rw [show Qd1 = fun s : ℝ => 80 * s ^ 3 + 480 * s ^ 2 + 252 * s + 160 from rfl, e]
  exact (((h3.const_mul 80).add (h2.const_mul 480)).add (h1.const_mul 252)).add_const 160

/-- The diagonal restriction of `F^{1/4}`. -/
noncomputable def gdiag (t : ℝ) : ℝ := r4 (Qd t)

/-- Its first derivative, in the exact shape `HasDerivAt.rpow_const` produces. -/
noncomputable def gdiag1 (t : ℝ) : ℝ := Qd1 t * ((4:ℝ)⁻¹) * Qd t ^ ((4:ℝ)⁻¹ - 1)

/-- Its second derivative, in the shape the product rule produces. -/
noncomputable def gdiag2 (t : ℝ) : ℝ :=
  Qd2 t * ((4:ℝ)⁻¹) * Qd t ^ ((4:ℝ)⁻¹ - 1)
    + Qd1 t * ((4:ℝ)⁻¹) * (Qd1 t * ((4:ℝ)⁻¹ - 1) * Qd t ^ ((4:ℝ)⁻¹ - 1 - 1))

theorem gdiag_eq (t : ℝ) : gdiag t = Qd t ^ ((4:ℝ)⁻¹) := by
  change Qd t ^ ((1:ℝ)/4) = _
  norm_num

theorem hasDerivAt_gdiag {t : ℝ} (ht : 0 < t) : HasDerivAt gdiag (gdiag1 t) t := by
  have hP : Qd t ≠ 0 := ne_of_gt (Qd_pos ht)
  have h := (hasDerivAt_Qd t).rpow_const (p := (4:ℝ)⁻¹) (Or.inl hP)
  have hfun : gdiag = fun s : ℝ => Qd s ^ ((4:ℝ)⁻¹) := funext gdiag_eq
  rw [hfun]
  exact h

theorem hasDerivAt_gdiag1 {t : ℝ} (ht : 0 < t) : HasDerivAt gdiag1 (gdiag2 t) t := by
  have hP : Qd t ≠ 0 := ne_of_gt (Qd_pos ht)
  have hu : HasDerivAt (fun s : ℝ => Qd1 s * ((4:ℝ)⁻¹)) (Qd2 t * ((4:ℝ)⁻¹)) t :=
    (hasDerivAt_Qd1 t).mul_const _
  have hv : HasDerivAt (fun s : ℝ => Qd s ^ ((4:ℝ)⁻¹ - 1))
      (Qd1 t * ((4:ℝ)⁻¹ - 1) * Qd t ^ ((4:ℝ)⁻¹ - 1 - 1)) t :=
    (hasDerivAt_Qd t).rpow_const (Or.inl hP)
  have h := hu.mul hv
  -- `HasDerivAt.mul` hands back the Pi-product `f * g`, not `fun s => f s * g s`; that is the
  -- only gap, because the derivative it produces is `gdiag2 t` on the nose.
  have hfun : gdiag1 = (fun s : ℝ => Qd1 s * ((4:ℝ)⁻¹))
      * (fun s : ℝ => Qd s ^ ((4:ℝ)⁻¹ - 1)) := rfl
  rw [hfun]
  exact h

/-- **The second derivative is negative on the whole positive axis**, and the only input is the
polynomial certificate. -/
theorem gdiag2_neg {t : ℝ} (ht : 0 < t) : gdiag2 t < 0 := by
  have hP : 0 < Qd t := Qd_pos ht
  have hcert : 0 < 3 * (Qd1 t) ^ 2 - 4 * Qd t * Qd2 t := diagonal_certificate_pos ht
  have hpos : 0 < Qd t ^ ((4:ℝ)⁻¹ - 1 - 1) := Real.rpow_pos_of_pos hP _
  have hsplit : Qd t ^ ((4:ℝ)⁻¹ - 1) = Qd t ^ ((4:ℝ)⁻¹ - 1 - 1) * Qd t := by
    -- rewriting the exponent in place also rewrites the copy inside the replacement, so the
    -- addition law is applied in the direction whose target is the PRODUCT.
    have hadd := Real.rpow_add hP ((4:ℝ)⁻¹ - 1 - 1) 1
    rw [Real.rpow_one] at hadd
    rw [← hadd]
    norm_num
  have key : gdiag2 t
      = Qd t ^ ((4:ℝ)⁻¹ - 1 - 1) * ((4 * Qd t * Qd2 t - 3 * (Qd1 t) ^ 2) / 16) := by
    change Qd2 t * ((4:ℝ)⁻¹) * Qd t ^ ((4:ℝ)⁻¹ - 1)
        + Qd1 t * ((4:ℝ)⁻¹) * (Qd1 t * ((4:ℝ)⁻¹ - 1) * Qd t ^ ((4:ℝ)⁻¹ - 1 - 1)) = _
    rw [hsplit]
    ring
  rw [key]
  exact mul_neg_of_pos_of_neg hpos (by linarith)

theorem deriv_gdiag_eventuallyEq {t : ℝ} (ht : 0 < t) : deriv gdiag =ᶠ[nhds t] gdiag1 := by
  filter_upwards [Ioi_mem_nhds ht] with s hs using (hasDerivAt_gdiag hs).deriv

theorem deriv2_gdiag_neg {t : ℝ} (ht : 0 < t) : deriv^[2] gdiag t < 0 := by
  have h1 : deriv^[2] gdiag t = deriv (deriv gdiag) t := by
    simp [Function.iterate_succ]
  rw [h1, (deriv_gdiag_eventuallyEq ht).deriv_eq, (hasDerivAt_gdiag1 ht).deriv]
  exact gdiag2_neg ht

theorem continuousOn_gdiag : ContinuousOn gdiag (Set.Ioi 0) := fun _ ht =>
  ((hasDerivAt_gdiag ht).continuousAt).continuousWithinAt

/-- **`F^{1/4}` IS STRICTLY CONCAVE ON THE WHOLE POSITIVE DIAGONAL.** -/
theorem strictConcaveOn_diagonal : StrictConcaveOn ℝ (Set.Ioi 0) gdiag := by
  refine strictConcaveOn_of_deriv2_neg (convex_Ioi 0) continuousOn_gdiag ?_
  intro t ht
  rw [interior_Ioi] at ht
  exact deriv2_gdiag_neg ht

/-! ## The refutation, assembled -/

/-- **LACHAUME'S CONJECTURE 1 IS FALSE.** At `n = p = 4` the form
`F = 20 + 40σ₁ + 21σ₂ + 40σ₃ + 20σ₄` — every coefficient strictly positive — has `F^{1/4}`
*strictly* concave on the whole positive diagonal and *not* concave on `Γ₄`, so diagonal concavity
does not imply concavity on the orthant. The second component is unconditional and derivative-free;
the first is the write-up's polynomial certificate fed to `strictConcaveOn_of_deriv2_neg`. -/
theorem conjecture_1_false :
    StrictConcaveOn ℝ (Set.Ioi 0) (fun t => r4 (F (fun _ => t)))
      ∧ ¬ ConcaveOn ℝ Orthant (fun x => r4 (F x)) := by
  refine ⟨?_, not_concaveOn_orthant⟩
  have hfun : (fun t : ℝ => r4 (F (fun _ => t))) = gdiag := by
    funext t
    change r4 (F (fun _ => t)) = r4 (Qd t)
    rw [F_diag]
  rw [hfun]
  exact strictConcaveOn_diagonal

end Principia.MathDB.P338076
