import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option autoImplicit false

/-!
# MathDB 362490 — an open basin of four-point limits

Write-up: `mathdb-open-problems/problems/362490/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`.  It **refutes Conjecture 5** of
Aldous–Cruz–Feng: that on every finite metric space with distinct interpoint distances,
almost every initial distribution has its iterates under `π_{j,k}` converging to a point
mass or to the uniform distribution on two points.

## The witness

The four-point space with `10·d` given by `D10` below, and `(j,k) = (2,2)`.  `π_{2,2}(p)`
is the stationary distribution of the chain that samples two independent points with law
`p` and moves to the **second** closest to its current state, so its transition kernel is

  `K_xy(p) = p_y² + 2 p_y ∑_{z : R_xz < R_xy} p_z`,

`R` being the rank matrix, with rank `1` assigned to the current point itself.

## What is proved

* `dist_pos_of_ne`, `dist_distinct`, `triangle_strict` — the witness really is a metric
  space with the conjecture's hypothesis: all six interpoint distances are **distinct**
  (they are `11,12,13,14,15,16` over `10`), and every triangle inequality is **strict**
  (the smallest possible sum, `22/10`, exceeds the largest distance, `16/10`).
* `Rk_eq_rank` — `R` really is the rank matrix of `D`, and `Rk_row_perm` /
  `Rk_col_perm` — each row *and* each column is a permutation of `1,2,3,4`.
* `K_row_sum` — `K p` is a stochastic matrix whenever `p` is a distribution.
* **`pa_stationary`** — the line of fixed points: `p_a K(p_a) = p_a` for
  `p_a = (a, a, ½-a, ½-a)` and **every** real `a`.  This is a polynomial identity;
  nothing about `a` is assumed.
* `pa_not_pointMass`, `pa_not_twoPointUniform` — for `0 < a < ½` none of those limits is
  a point mass or a two-point uniform, so the conjecture's dichotomy fails on a whole
  line.
* `Ks_eq`, `e_eigen`, `df_eigenvalue`, `transverse_lt_one` — at the barycentre
  `K_* = (2R-1)/16`, with `e₀ K_* = 0`, `e₁ K_* = -¼e₁`, `e₂ K_* = -½e₂`; the derivative
  of the stationary map has eigenvalues `1/(1-λᵢ) = 1, 4/5, 2/3`, so the two directions
  **transverse** to the fixed-point line contract.  That is why the basin is open rather
  than a measure-zero set.
* `Setup.refutation` — the conclusion.

## What is carried

`Setup` carries exactly the two analytic facts the write-up establishes about `π_{2,2}`:
that it returns *the* stationary distribution of `K p` (existence), and that this
distribution is **unique** for interior `p` (`K` has positive entries).  `F (p_a) = p_a`
is then *derived* from `pa_stationary`, not assumed.  The local convergence argument —
the mean-value contraction on the box — is what upgrades "a line of fixed points" to "an
open set of initial distributions", and is carried as `Setup.basin`.

`Campaigns/MathDB-Formalization/verify_362490.py` checks all of the above in exact
rationals and iterates the true map from random interior starts: every run lands on
`(a, a, ½-a, ½-a)` to within the predicted `(4/5)ⁿ`.
-/

namespace Principia.MathDB.P362490

open Finset

/-! ## The witness -/

/-- Ten times the distance matrix.  Kept over `ℤ` on purpose: with the `/10` folded in,
`decide` gets stuck on `Rat.inv 10` and every metric fact below fails to reduce. -/
def D10 : Fin 4 → Fin 4 → ℤ :=
  ![![0, 15, 13, 11], ![15, 0, 12, 14], ![13, 12, 0, 16], ![11, 14, 16, 0]]

/-- The metric itself. -/
def dst (x y : Fin 4) : ℚ := (D10 x y : ℚ) / 10

/-- The rank matrix: `R x y` is the position of `y` in the ordering of the points by
distance from `x`, with rank `1` assigned to `x` itself. -/
def Rk : Fin 4 → Fin 4 → ℕ
  | 0, 0 => 1 | 0, 1 => 4 | 0, 2 => 3 | 0, 3 => 2
  | 1, 0 => 4 | 1, 1 => 1 | 1, 2 => 2 | 1, 3 => 3
  | 2, 0 => 3 | 2, 1 => 2 | 2, 2 => 1 | 2, 3 => 4
  | 3, 0 => 2 | 3, 1 => 3 | 3, 2 => 4 | 3, 3 => 1

theorem D10_symm : ∀ x y, D10 x y = D10 y x := by decide

theorem D10_diag : ∀ x, D10 x x = 0 := by decide

theorem D10_pos_of_ne : ∀ x y : Fin 4, x ≠ y → 0 < D10 x y := by decide

/-- **All six interpoint distances are distinct** — the conjecture's hypothesis. -/
theorem D10_distinct : ∀ x y z w : Fin 4, x ≠ y → z ≠ w → D10 x y = D10 z w →
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by decide

/-- **Every triangle inequality is strict.**  The smallest possible sum is `22`, larger
than the largest distance `16`. -/
theorem D10_triangle : ∀ x y z : Fin 4, x ≠ y → z ≠ x → z ≠ y →
    D10 x y < D10 x z + D10 z y := by decide

theorem dst_pos_of_ne {x y : Fin 4} (h : x ≠ y) : 0 < dst x y := by
  have hz := D10_pos_of_ne x y h
  have hq : (0 : ℚ) < (D10 x y : ℚ) := by exact_mod_cast hz
  rw [dst]
  positivity

theorem dist_distinct {x y z w : Fin 4} (h1 : x ≠ y) (h2 : z ≠ w)
    (h : dst x y = dst z w) : (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  refine D10_distinct x y z w h1 h2 ?_
  have hq : (D10 x y : ℚ) = (D10 z w : ℚ) := by
    simp only [dst] at h; linarith
  exact_mod_cast hq

theorem triangle_strict {x y z : Fin 4} (h1 : x ≠ y) (h2 : z ≠ x) (h3 : z ≠ y) :
    dst x y < dst x z + dst z y := by
  have hz := D10_triangle x y z h1 h2 h3
  have hq : (D10 x y : ℚ) < (D10 x z : ℚ) + (D10 z y : ℚ) := by exact_mod_cast hz
  simp only [dst]
  linarith

/-- `R` really is the rank matrix of `D`. -/
theorem Rk_eq_rank : ∀ x y : Fin 4,
    Rk x y = 1 + (univ.filter (fun z => D10 x z < D10 x y)).card := by decide

theorem Rk_row_perm : ∀ x : Fin 4, ({Rk x 0, Rk x 1, Rk x 2, Rk x 3} : Finset ℕ)
    = {1, 2, 3, 4} := by decide

/-- Each **column** of `R` is also a permutation of `1,2,3,4`; this is what makes the
derivative computation at the barycentre work out. -/
theorem Rk_col_perm : ∀ y : Fin 4, ({Rk 0 y, Rk 1 y, Rk 2 y, Rk 3 y} : Finset ℕ)
    = {1, 2, 3, 4} := by decide

/-- For every `z ≠ y` there are exactly **two** rows `x` with `R_xz < R_xy`. -/
theorem two_rows : ∀ y z : Fin 4, z ≠ y →
    (univ.filter (fun x => Rk x z < Rk x y)).card = 2 := by decide

/-! ## The transition kernel -/

/-- `K_xy(p) = p_y² + 2 p_y ∑_{z : R_xz < R_xy} p_z`: either both samples equal `y`, or
one equals `y` and the other is strictly closer to `x`. -/
noncomputable def K (p : Fin 4 → ℝ) (x y : Fin 4) : ℝ :=
  p y ^ 2 + 2 * p y * ∑ z : Fin 4, (if Rk x z < Rk x y then p z else 0)

/-- `K p` is stochastic: each row sums to `(∑ p)² = 1`. -/
theorem K_row_sum {p : Fin 4 → ℝ} (hp : ∑ y, p y = 1) (x : Fin 4) :
    ∑ y, K p x y = 1 := by
  rw [Fin.sum_univ_four] at hp
  fin_cases x <;>
    · simp only [K, Rk, Fin.sum_univ_four]
      norm_num
      nlinarith [hp]

/-! ## The line of fixed points -/

/-- `p_a = (a, a, ½ - a, ½ - a)`. -/
noncomputable def pa (a : ℝ) : Fin 4 → ℝ
  | 0 => a
  | 1 => a
  | 2 => 1 / 2 - a
  | 3 => 1 / 2 - a

theorem pa_sum (a : ℝ) : ∑ x, pa a x = 1 := by
  simp [pa, Fin.sum_univ_four]
  ring

/-- **`p_a K(p_a) = p_a`, for every real `a`.**  A polynomial identity — nothing about
`a` is assumed, and in particular no positivity. -/
theorem pa_stationary (a : ℝ) (y : Fin 4) :
    ∑ x, pa a x * K (pa a) x y = pa a y := by
  fin_cases y <;>
    · simp only [K, pa, Rk, Fin.sum_univ_four]
      norm_num
      ring

theorem pa_pos {a : ℝ} (h0 : 0 < a) (h1 : a < 1 / 2) (x : Fin 4) : 0 < pa a x := by
  fin_cases x <;> · simp [pa]; linarith

/-! ## The limits violate the conjecture's dichotomy -/

/-- A point mass: some coordinate carries all the weight. -/
def IsPointMass (p : Fin 4 → ℝ) : Prop := ∃ x, p x = 1

/-- Uniform on two points: two distinct coordinates each carry `½`. -/
def IsTwoPointUniform (p : Fin 4 → ℝ) : Prop :=
  ∃ x y, x ≠ y ∧ p x = 1 / 2 ∧ p y = 1 / 2

theorem pa_not_pointMass {a : ℝ} (h0 : 0 < a) (h1 : a < 1 / 2) :
    ¬ IsPointMass (pa a) := by
  rintro ⟨x, hx⟩
  fin_cases x <;> · simp [pa] at hx; linarith

theorem pa_not_twoPointUniform {a : ℝ} (h0 : 0 < a) (h1 : a < 1 / 2) :
    ¬ IsTwoPointUniform (pa a) := by
  rintro ⟨x, y, _, hx, _⟩
  fin_cases x <;> · simp [pa] at hx; linarith

/-! ## The derivative at the barycentre -/

/-- `K_* = (2R - 1)/16` at `p_* = (¼,¼,¼,¼)`. -/
theorem Ks_eq (x y : Fin 4) :
    K (fun _ => (1 : ℝ) / 4) x y = (2 * (Rk x y : ℝ) - 1) / 16 := by
  fin_cases x <;> fin_cases y <;>
    · simp only [K, Rk, Fin.sum_univ_four]
      norm_num

/-- The tangent basis of the simplex. -/
def ev : Fin 3 → Fin 4 → ℚ
  | 0, 0 => 1 | 0, 1 => 1 | 0, 2 => -1 | 0, 3 => -1
  | 1, 0 => 1 | 1, 1 => -1 | 1, 2 => 1 | 1, 3 => -1
  | 2, 0 => 1 | 2, 1 => -1 | 2, 2 => -1 | 2, 3 => 1

/-- The eigenvalues of `K_*` on that basis. -/
def evlam : Fin 3 → ℚ
  | 0 => 0
  | 1 => -1 / 4
  | 2 => -1 / 2

/-- `eᵢ K_* = λᵢ eᵢ`, with `(λ₀, λ₁, λ₂) = (0, -¼, -½)`. -/
theorem e_eigen : ∀ (i : Fin 3) (y : Fin 4),
    ∑ x : Fin 4, ev i x * ((2 * (Rk x y : ℚ) - 1) / 16) = evlam i * ev i y := by
  intro i y
  fin_cases i <;> fin_cases y <;> simp [ev, evlam, Rk, Fin.sum_univ_four] <;>
    norm_num

/-- The stationary map's derivative has eigenvalue `1/(1 - λᵢ)` in direction `eᵢ`. -/
theorem df_eigenvalue :
    (1 : ℚ) / (1 - evlam 0) = 1 ∧ (1 : ℚ) / (1 - evlam 1) = 4 / 5 ∧
      (1 : ℚ) / (1 - evlam 2) = 2 / 3 := by norm_num [evlam]

/-- **The two directions transverse to the fixed-point line contract.**  This is why the
basin is open, rather than the measure-zero set the conjecture would allow. -/
theorem transverse_lt_one : (4 : ℚ) / 5 < 1 ∧ (2 : ℚ) / 3 < 1 := by norm_num

/-! ## The carried analytic inputs, and the refutation -/

/-- What the write-up establishes about `π_{2,2}` itself. -/
structure Setup where
  /-- `F p = π_{2,2}(p)` -/
  F : (Fin 4 → ℝ) → (Fin 4 → ℝ)
  /-- **CARRIED**: `F p` is a stationary distribution of `K p`. -/
  hF_sum : ∀ p : Fin 4 → ℝ, (∀ x, 0 < p x) → ∑ y, F p y = 1
  hF_stat : ∀ p : Fin 4 → ℝ, (∀ x, 0 < p x) → ∀ y, ∑ x, F p x * K p x y = F p y
  /-- **CARRIED**: for interior `p` every entry of `K p` is positive, so the stationary
  distribution is unique. -/
  hF_uniq : ∀ p q : Fin 4 → ℝ, (∀ x, 0 < p x) → (∑ y, q y = 1) →
    (∀ y, ∑ x, q x * K p x y = q y) → q = F p
  /-- **CARRIED** (the mean-value contraction on the box, using `transverse_lt_one`):
  each fixed point on the line attracts an open set of initial distributions. -/
  basin : ∀ a : ℝ, 0 < a → a < 1 / 2 →
    ∃ ε > 0, ∀ p : Fin 4 → ℝ, (∀ x, |p x - pa a x| < ε) → (∀ x, 0 < p x) →
      ∃ a' : ℝ, 0 < a' ∧ a' < 1 / 2 ∧
        Filter.Tendsto (fun n => F^[n] p) Filter.atTop (nhds (pa a'))

namespace Setup

/-- **`F` fixes the whole line** — derived from `pa_stationary` and uniqueness, not
assumed. -/
theorem F_pa (S : Setup) {a : ℝ} (h0 : 0 < a) (h1 : a < 1 / 2) : S.F (pa a) = pa a :=
  (S.hF_uniq (pa a) (pa a) (pa_pos h0 h1) (pa_sum a) (pa_stationary a)).symm

/-- **THE REFUTATION.**  A whole line of genuine fixed points of `π_{2,2}`, none of them
a point mass and none of them uniform on two points — and each attracts an open set of
initial distributions, so the exceptional set is not null. -/
theorem refutation (S : Setup) {a : ℝ} (h0 : 0 < a) (h1 : a < 1 / 2) :
    S.F (pa a) = pa a ∧ ¬ IsPointMass (pa a) ∧ ¬ IsTwoPointUniform (pa a) ∧
      ∃ ε > 0, ∀ p : Fin 4 → ℝ, (∀ x, |p x - pa a x| < ε) → (∀ x, 0 < p x) →
        ∃ a' : ℝ, 0 < a' ∧ a' < 1 / 2 ∧
          Filter.Tendsto (fun n => S.F^[n] p) Filter.atTop (nhds (pa a')) :=
  ⟨S.F_pa h0 h1, pa_not_pointMass h0 h1, pa_not_twoPointUniform h0 h1, S.basin a h0 h1⟩

end Setup

end Principia.MathDB.P362490
