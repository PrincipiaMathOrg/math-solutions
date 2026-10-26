import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
-- the 7-blowup's edge list has 980 entries and its degree computation scans that list once per
-- vertex; the default recursion depth is reached while unfolding it.
set_option maxRecDepth 100000

/-!
# MathDB #369710 — Movahedi's Conjecture 5.1 is FALSE

Write-up: `mathdb-open-problems/problems/369710/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-30).
Source: F. Movahedi, *Diminished Sombor matrix, spectral radius, and energy of the graphs*,
arXiv:2508.06531v1 (2025), definition p. 2, **Conjecture 5.1** p. 19.

The conjecture: the diminished Sombor energy `E(G) = Σ |λ|` of a simple graph is never an
integer. The counterexample: the 7-blowup of an 11-vertex graph, connected and bipartite, with
77 vertices, 980 edges, minimum degree 21 — and energy exactly **72**.

## The whole computation is RATIONAL, even though the eigenvalues are not

This is what makes the row cheap, and it is worth stating because the obvious reading of a
"graph energy" claim is that it needs eigenvalues.

* The `(3,4)` diminished Sombor weight is `√(9+16)/7 = 5/7` — **rational**, because `(3,4,5)` is
  a Pythagorean pair. `weight_three_four` proves it.
* The write-up's reduction lands on the `2 × 2` matrix `T = ![![10/7, 10/7], ![2, 0]]`, whose
  entries are rational. Its two singular values `s₊, s₋` satisfy `s₊² + s₋² = tr(TTᵀ) = 396/49`
  and `s₊s₋ = |det T| = 20/7`, so `(s₊+s₋)² = 676/49` and **`s₊ + s₋ = 26/7` with no surd
  anywhere** (`sum_of_singular_values`). The individual values `(13 ± √29)/7` are a side remark,
  and `roots_of_quadratic` confirms they are the roots of `7x² − 26x + 20`.
* Hence `E(H) = 2(10/7 + 26/7) = 72/7`, and the 7-blowup multiplies it by seven: `E(G) = 72`.

`sum_of_quartic_roots` gives the same number by a **second, independent route**: read off the
characteristic polynomial `x⁷¹(x²−100)(x⁴−396x²+19600)` that the write-up states, the quartic's
roots `±a, ±b` satisfy `a²+b² = 396` and `a²b² = 19600`, so `ab = 140`, `(a+b)² = 676`,
`a + b = 26`, and `E = 2(10+26) = 72`. **The energy is a function of the polynomial's
coefficients, not of its roots.**

## What is a hypothesis, and why

`conjecture_5_1_false` is a **spine**. Three genuinely spectral facts are **named hypotheses**:
that the energy is the sum of the absolute eigenvalues of the claimed multiset, that the
class-constant reduction sends the nonzero singular values of `B` to those of `R`, and that the
blowup multiplies the energy by `r`. Mathlib has `Matrix.IsHermitian.eigenvalues` and
`LinearMap.singularValues`, but **no graph energy at all** — its two `energy` definitions are the
Szemerédi-regularity and additive-combinatorics notions, neither of which is this one — and no
computational route from a concrete matrix to its spectrum. Both absences were checked by grep
before this paragraph was written.

Everything else is proved here: the graph, its degrees, its bipartition and connectivity, the
weights and their blowup invariance, the two rational routes to `26`, and the blowup's graph data.

## A finding the write-up does not state

`H` itself is **not** a counterexample — its energy is `72/7`, not an integer. The blowup is not
a flourish that makes the example bigger; it is the step that makes it work, and `7 ∣ r` is
exactly the condition (`family_integer`). The verifier also measures that the `(3,4)` weight is a
*choice*: among degree pairs up to 14 only `(3,4)`, `(5,12)`, `(6,8)` and `(9,12)` give a
rational weight at all.
-/

namespace Principia.MathDB.P369710

/-! ## The eleven-vertex graph `H`

Six independent classes, five of size two and one of size one, joined along a six-cycle. -/

def A1 : List ℕ := [0, 1]
def A2 : List ℕ := [2, 3]
def B1 : List ℕ := [4, 5]
def B2 : List ℕ := [6, 7]
def Cc : List ℕ := [8, 9]
def Dd : List ℕ := [10]

/-- All edges between two independent classes. -/
def between (X Y : List ℕ) : List (ℕ × ℕ) := X.flatMap fun u => Y.map fun v => (u, v)

/-- The six class pairs of the blown-up six-cycle `A₁–B₁–C–B₂–A₂–D–A₁`. -/
def edgesH : List (ℕ × ℕ) :=
  between A1 B1 ++ between A2 B2 ++ between A1 Dd ++ between A2 Dd
    ++ between Cc B1 ++ between Cc B2

def incident (v : ℕ) (e : ℕ × ℕ) : Bool := e.1 == v || e.2 == v

def degH (v : ℕ) : ℕ := (edgesH.filter (incident v)).length

theorem card_edgesH : edgesH.length = 20 := by decide

theorem edgesH_simple : (edgesH.all fun e => e.1 != e.2) = true ∧ edgesH.dedup.length = 20 := by
  decide

/-- Degree `3` on `A₁ ∪ A₂` and `4` on every other vertex — which is what puts every edge on a
`(3,4)` or a `(4,4)` pair. -/
theorem degrees_H : ((List.range 11).map degH) = [3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4] := by decide

def leftH : List ℕ := A1 ++ A2 ++ Cc

theorem bipartite_H :
    (edgesH.all fun e => xor (leftH.contains e.1) (leftH.contains e.2)) = true := by decide

/-! ### Connectivity, by explicit reachability -/

def adjacentIn (es : List (ℕ × ℕ)) (p q : ℕ) : Bool :=
  es.any fun e => (e.1 == p && e.2 == q) || (e.1 == q && e.2 == p)

def expandOnce (es : List (ℕ × ℕ)) (verts seen : List ℕ) : List ℕ :=
  seen ++ verts.filter (fun q => !seen.contains q && seen.any (fun p => adjacentIn es p q))

def reachFrom : ℕ → List (ℕ × ℕ) → List ℕ → List ℕ → List ℕ
  | 0, _, _, seen => seen
  | n + 1, es, verts, seen => reachFrom n es verts (expandOnce es verts seen)

theorem connected_H : (reachFrom 11 edgesH (List.range 11) [0]).length = 11 := by decide

/-! ## The diminished Sombor weight -/

/-- `√(d_u² + d_v²)/(d_u + d_v)`. -/
noncomputable def weight (du dv : ℝ) : ℝ := Real.sqrt (du ^ 2 + dv ^ 2) / (du + dv)

/-- **The weight on a `(3,4)` edge is rational.** `(3,4,5)` is a Pythagorean pair, and this is the
reason the construction can produce a rational energy at all. -/
theorem weight_three_four : weight 3 4 = 5 / 7 := by
  simp only [weight]
  rw [show (3 : ℝ) ^ 2 + 4 ^ 2 = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5)]
  norm_num

/-- The weight on a `(4,4)` edge. -/
theorem weight_four_four : weight 4 4 = Real.sqrt 2 / 2 := by
  simp only [weight]
  rw [show (4 : ℝ) ^ 2 + 4 ^ 2 = 4 ^ 2 * 2 by norm_num,
    Real.sqrt_mul (by positivity) 2, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
  ring

/-- **The weight is blowup-invariant**: scaling both degrees by `r` leaves it unchanged. This is
the whole content of the blowup lemma's matrix half. -/
theorem weight_blowup (r du dv : ℝ) (hr : 0 < r) :
    weight (r * du) (r * dv) = weight du dv := by
  simp only [weight]
  rw [show (r * du) ^ 2 + (r * dv) ^ 2 = r ^ 2 * (du ^ 2 + dv ^ 2) by ring,
    Real.sqrt_mul (by positivity) _, Real.sqrt_sq hr.le,
    show r * du + r * dv = r * (du + dv) by ring]
  rw [mul_div_mul_left _ _ (ne_of_gt hr)]

/-! ## The rational core

Two independent routes to the number `26`, neither of which mentions `√29`. -/

/-- **The write-up's route.** `T = ![![10/7, 10/7], ![2, 0]]` has `tr(TTᵀ) = 396/49` and
`|det T| = 20/7`; its singular values therefore sum to `26/7`. -/
theorem sum_of_singular_values (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hsq : s ^ 2 + t ^ 2 = 396 / 49) (hpr : s * t = 20 / 7) : s + t = 26 / 7 := by
  have h : (s + t - 26 / 7) * (s + t + 26 / 7) = 0 := by nlinarith
  rcases mul_eq_zero.mp h with h' | h'
  · linarith
  · linarith

theorem T_invariants :
    (10 / 7 : ℝ) ^ 2 + (10 / 7) ^ 2 + 2 ^ 2 + 0 ^ 2 = 396 / 49
      ∧ |(10 / 7 : ℝ) * 0 - (10 / 7) * 2| = 20 / 7 := by
  constructor
  · norm_num
  · rw [show (10 / 7 : ℝ) * 0 - (10 / 7) * 2 = -(20 / 7) by ring, abs_neg]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 20 / 7)]

/-- **The characteristic-polynomial route, and it is independent of the first.** The quartic
factor `x⁴ − 396x² + 19600` has roots `±a, ±b`; its coefficients alone give `a + b = 26`. The
energy is a function of the polynomial's COEFFICIENTS, not of its roots. -/
theorem sum_of_quartic_roots (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a ^ 2 + b ^ 2 = 396) (h2 : a ^ 2 * b ^ 2 = 19600) : a + b = 26 := by
  have hab : a * b = 140 := by
    have h3 : (a * b - 140) * (a * b + 140) = 0 := by nlinarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · linarith
    · nlinarith
  have h5 : (a + b - 26) * (a + b + 26) = 0 := by nlinarith
  rcases mul_eq_zero.mp h5 with h6 | h6
  · linarith
  · linarith

/-! ## The displayed eigenvalues, for the record -/

theorem sqrt29_lt_thirteen : Real.sqrt 29 < 13 := by
  have h : Real.sqrt 29 < Real.sqrt (13 ^ 2) :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 13)] at h

theorem eigen_pair_pos : 0 < (13 - Real.sqrt 29) / 7 := by
  have := sqrt29_lt_thirteen
  linarith

theorem eigen_pair_sum : (13 + Real.sqrt 29) / 7 + (13 - Real.sqrt 29) / 7 = 26 / 7 := by ring

/-- Both displayed eigenvalues are roots of `7x² − 26x + 20`, whose coefficients are exactly the
trace and determinant data above. -/
theorem roots_of_quadratic :
    7 * ((13 + Real.sqrt 29) / 7) ^ 2 - 26 * ((13 + Real.sqrt 29) / 7) + 20 = 0
      ∧ 7 * ((13 - Real.sqrt 29) / 7) ^ 2 - 26 * ((13 - Real.sqrt 29) / 7) + 20 = 0 := by
  have h : Real.sqrt 29 ^ 2 = 29 := Real.sq_sqrt (by norm_num)
  constructor <;> · field_simp; linear_combination h

/-! ## The energy -/

/-- `E(H) = 2(10/7 + s₊ + s₋) = 72/7` — and `72/7` is **not** an integer, so `H` alone refutes
nothing. -/
theorem energy_H (s t : ℝ) (h : s + t = 26 / 7) : 2 * (10 / 7 + s + t) = 72 / 7 := by
  rw [show 10 / 7 + s + t = 10 / 7 + (s + t) by ring, h]; norm_num

theorem energy_G (eH eG : ℝ) (h1 : eH = 72 / 7) (h2 : eG = 7 * eH) : eG = 72 := by
  rw [h2, h1]; norm_num

theorem energy_G_is_integer : ∃ n : ℤ, (72 : ℝ) = (n : ℝ) := ⟨72, by norm_num⟩

/-- **The blowup is what does the work, and `7 ∣ r` is exactly the condition.** -/
theorem family_integer (r : ℕ) : 7 ∣ 72 * r ↔ 7 ∣ r := by omega

/-! ## The 7-blowup `G` -/

def blowup (r : ℕ) (es : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  es.flatMap fun e =>
    (List.range r).flatMap fun i => (List.range r).map fun j => (e.1 * r + i, e.2 * r + j)

def edgesG : List (ℕ × ℕ) := blowup 7 edgesH

def degG (v : ℕ) : ℕ := (edgesG.filter (incident v)).length

theorem card_edgesG : edgesG.length = 980 := by decide

theorem degrees_G :
    ((List.range 77).filter (fun v => degG v == 21)).length = 28
      ∧ ((List.range 77).filter (fun v => degG v == 28)).length = 49 := by
  decide

theorem blowup_arithmetic :
    7 * 11 = 77 ∧ 7 * 7 * 20 = 980 ∧ 7 * 3 = 21 ∧ 7 * 4 = 28 ∧ 4 * 7 = 28 ∧ 7 * 7 = 49 := by
  decide

/-! ## The refutation -/

/-- **Movahedi's Conjecture 5.1 is false.** Given the three spectral facts as hypotheses — the
energy is the sum of absolute eigenvalues, the class-constant reduction preserves the nonzero
singular values, and the blowup multiplies the energy by `r` — the 7-blowup of `H` has energy
exactly `72`, an integer.

The hypotheses are the only things this module does not prove, and they are named rather than
worked around: Mathlib has no graph energy and no computational route from a concrete matrix to
its spectrum. -/
theorem conjecture_5_1_false (s t eH eG : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hsq : s ^ 2 + t ^ 2 = 396 / 49) (hpr : s * t = 20 / 7)
    (hEH : eH = 2 * (10 / 7 + s + t))
    (hEG : eG = 7 * eH) :
    eG = 72 ∧ ∃ n : ℤ, eG = (n : ℝ) := by
  have hsum : s + t = 26 / 7 := sum_of_singular_values s t hs ht hsq hpr
  have h1 : eH = 72 / 7 := by rw [hEH]; exact energy_H s t hsum
  have h2 : eG = 72 := energy_G eH eG h1 hEG
  exact ⟨h2, ⟨72, by rw [h2]; norm_num⟩⟩

end Principia.MathDB.P369710
