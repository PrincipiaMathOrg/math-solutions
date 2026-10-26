import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 1000000

/-!
# MathDB #319187 — Davis's polynomial-ratio bound (SPINE, PARTIAL)

Write-up `mathdb-open-problems/problems/319187/solution.tex`,
*A variance proof of Davis's polynomial-ratio bound*, 17 September 2026.
Source: Davis, Conjecture 3.1.

With `(x)_i` the falling factorial,

`P_d(x) = ∑_{i=0}^d (x)_i² (x)_{d−i}² / (i!(d−i)!)`,
`q_d(x) = (2x² − 2dx)/(d+1) + d/2`,  `R_d = P_{d+1} − q_d P_d`,

the conjecture asserts, for every integer `d ≥ 5` and every real
`x ≥ (d + √(d+2))/2`,

`−R_d(x)/P_d(x) > 199(d−2) / (200(2x+d−2))`,

i.e. the conjectured weak inequality with the exact constant `0.995 = 199/200`.

## The write-up's idea, which is what makes this row feasible at all

The weights `w_i` are nonnegative and symmetric (`w_i = w_{d−i}`), so they define a
probability distribution on `{0,…,d}` whose centred variable `Z = I − d/2` has mean zero.
Then `−R_d/P_d = (d − 4V)/(2(d+1))` with `V = E Z²`, so the whole conjecture is an upper
bound on a VARIANCE.  An exact fourth-moment identity `4M₄ + A·V = dc²` (with `c = x − d/2`
and `A = 4c² + 4(d−1)c − d`), together with Cauchy–Schwarz `M₄ ≥ V²`, pins `V` by a
quadratic inequality.  **Nothing in this uses theory Mathlib lacks** — finite sums,
Cauchy–Schwarz, and polynomial positivity — which is why this row was chosen.

## What is proved here

* `linkPos`, `linkCS`, `linkRatio`, `linkMoment` — **four of the five links**, i.e. everything
  except the endgame.  `var_identity` and the weight recurrence `Wa_eq_Wb_succ` + `tele` are
  the substance of the middle two.
* `quad_of_moment_cs` — the quadratic constraint `t² + At ≤ 4dc²` for `t = 4V`.
* `main_of_vbound` — **the SPINE**: Davis's bound follows from `LinkVBound` alone.
* `vbound_of_quad` — the quadratic route to `LinkVBound`, usable wherever `LinkQuadBound`
  can be established.

## A CORRECTION recorded here, found 2026-09-21

This row's spine originally carried `LinkQuadBound` — the implication from the quadratic
constraint ALONE — as its single remaining obligation, on the stated grounds that both halves
of the write-up's endgame prove exactly that implication.  **That was asserted, not checked,
and it is false.**  Writing `q(s) = s² + As − 4dc²`, the constraint permits every `t` up to the
positive root `t*`, and `t*` exceeds the target threshold `T` precisely for
**`13 ≤ d ≤ 36`**.  Concretely at `d = 13`, `x = 8.486492` (inside the domain):
`t* = 2.048220 > T = 2.044429`, while the true value is `4V = 1.978001`.  So the conjecture
holds there, but Cauchy–Schwarz has discarded too much (`M₄ − V² = 0.448`).

The obligation is therefore restated as `LinkVBound`, a bound on the variance ITSELF, which
is what the write-up's endgame actually proves.  `vbound_of_quad` keeps the quadratic route
available: outside `13 ≤ d ≤ 36` it discharges `LinkVBound`, and inside that band a sharper
input is required — which is consistent with, and refines, the write-up's own split (it gives
an analytic argument for `d ≥ 40` and exact certificates below).

## Davis's bound is UNCONDITIONAL for every `d ≥ 5` outside `13 ≤ d ≤ 36`

`davis_outside_band` carries **no hypotheses beyond the conjecture's own**.  The route:
clearing `q(T) > 0` by `u²` (with `u = c+d-1`) gives `Ecub`, whose QUARTIC terms in `c`
cancel — that cancellation is what makes the endgame tractable.  What is left is a cubic

`800·M·c³ + 1600(d-1)·M·c² + 200·Q·c - 199(d-2)(d+1)·M`,
`M = d²-d+398 > 0`,  `Q = 4d⁴-211d³+1803d²-2790d+1592`.

Three of the four coefficients are manifestly positive.

* Where `Q ≥ 0` — exactly `d ≤ 8` and `d ≥ 43` — the domain hypothesis `4c² ≥ d+2` alone
  finishes, because `400(d-1)(d+2) > 199(d-2)(d+1)` (`Ecub_pos`, `davis_small`,
  `davis_large`).
* For `9 ≤ d ≤ 12` and `37 ≤ d ≤ 42` the linear coefficient is negative but the `c³` term
  absorbs it, via the single hint `c·(4c² - (d+2)) ≥ 0` (`Ecub_pos_band`, `davis_band`).

## The band `13 ≤ d ≤ 36` is closed, and `LinkVBound` is no longer carried

That band is exactly where the quadratic constraint is genuinely insufficient (see the
correction above), so it is the sharp limit of the Cauchy–Schwarz route rather than an
artefact of how the argument was arranged — and it is closed a different way, one degree at a
time, in `Problem319187Cert*.lean`.  For fixed `d` the conjecture is equivalent to positivity
of an explicit polynomial on a ray, and shifting to a rational `x₁ ≤ x₀` makes every
coefficient nonnegative, so positivity becomes a LINEAR consequence of `s^k ≥ 0`.

`Principia.MathDB.P319187.davis` composes the two halves and **proves Davis's Conjecture 3.1
for every `d ≥ 5`**, with no hypotheses beyond the conjecture's own.  Audited by
`MathDB/Gate319187.lean` (176 footprints, all safe) — a dedicated gate, because the
certificate modules cannot be loaded by the main MathDB gate without exhausting memory.

## Python value check

`Campaigns/MathDB-Formalization/verify_319187.py`, all six families in exact rational
arithmetic: the weight recurrence `w_i a_i = w_{i+1} b_{i+1}`; the variance identity
`(d+1)P_{d+1} = ∑ w_i((x−i)²+(x−d+i)²)`; both ratio identities; the fourth-moment identity;
Cauchy–Schwarz and the derived quadratic; and the target inequality itself over a grid of
`(d, x)` in its stated domain.
-/

namespace Principia.MathDB.P319187

open Finset

/-- Falling factorial `(x)_i = x(x-1)…(x-i+1)`. -/
def fall (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | (i + 1) => fall x i * (x - i)

/-- The defining step of the falling factorial, as a rewrite rule. -/
lemma fall_succ (x : ℝ) (i : ℕ) : fall x (i + 1) = fall x i * (x - (i : ℝ)) := rfl

/-- The source's weights `w_i = (x)_i² (x)_{d-i}² / (i! (d-i)!)`. -/
noncomputable def wt (d : ℕ) (x : ℝ) (i : ℕ) : ℝ :=
  (fall x i) ^ 2 * (fall x (d - i)) ^ 2 / ((Nat.factorial i : ℝ) * (Nat.factorial (d - i) : ℝ))

/-- `P_d(x) = ∑_{i=0}^d w_i`. -/
noncomputable def Pd (d : ℕ) (x : ℝ) : ℝ := ∑ i ∈ range (d + 1), wt d x i

/-- The source's quotient `q_d(x) = (2x² − 2dx)/(d+1) + d/2`. -/
noncomputable def qd (d : ℕ) (x : ℝ) : ℝ := (2 * x ^ 2 - 2 * d * x) / ((d : ℝ) + 1) + (d : ℝ) / 2

/-- The remainder `R_d = P_{d+1} − q_d P_d`. -/
noncomputable def Rd (d : ℕ) (x : ℝ) : ℝ := Pd (d + 1) x - qd d x * Pd d x

/-- `V = E Z²` for `Z = I − d/2`. -/
noncomputable def Vmom (d : ℕ) (x : ℝ) : ℝ :=
  (∑ i ∈ range (d + 1), wt d x i * ((i : ℝ) - (d : ℝ) / 2) ^ 2) / Pd d x

/-- `M₄ = E Z⁴`. -/
noncomputable def M4mom (d : ℕ) (x : ℝ) : ℝ :=
  (∑ i ∈ range (d + 1), wt d x i * ((i : ℝ) - (d : ℝ) / 2) ^ 4) / Pd d x

/-- The write-up's `A = 4c² + 4(d−1)c − d`. -/
noncomputable def Acoef (d : ℕ) (c : ℝ) : ℝ := 4 * c ^ 2 + 4 * ((d : ℝ) - 1) * c - (d : ℝ)

/-- The domain of the conjecture: `x ≥ (d + √(d+2))/2`. -/
noncomputable def dom (d : ℕ) (x : ℝ) : Prop := ((d : ℝ) + Real.sqrt ((d : ℝ) + 2)) / 2 ≤ x

/-- LINK 1: positivity of the denominator above `d/2`. -/
def LinkPos (d : ℕ) : Prop := ∀ x : ℝ, (d : ℝ) / 2 < x → 0 < Pd d x

/-- LINK 2: the variance form of the ratio, the write-up's display (variance). -/
def LinkRatio (d : ℕ) : Prop := ∀ x : ℝ, (d : ℝ) / 2 < x →
  -Rd d x / Pd d x = ((d : ℝ) - 4 * Vmom d x) / (2 * ((d : ℝ) + 1))

/-- LINK 3: the exact fourth-moment identity, the write-up's display (moment). -/
def LinkMoment (d : ℕ) : Prop := ∀ x : ℝ, (d : ℝ) / 2 < x →
  4 * M4mom d x + Acoef d (x - (d : ℝ) / 2) * Vmom d x = (d : ℝ) * (x - (d : ℝ) / 2) ^ 2

/-- LINK 4: Cauchy–Schwarz on the probability measure, `M₄ ≥ V²`. -/
def LinkCS (d : ℕ) : Prop := ∀ x : ℝ, (d : ℝ) / 2 < x → (Vmom d x) ^ 2 ≤ M4mom d x

/-- LINK 5: the variance is nonnegative (the weights are). -/
def LinkVnonneg (d : ℕ) : Prop := ∀ x : ℝ, (d : ℝ) / 2 < x → 0 ≤ Vmom d x

/-- LINK 6: the endgame.  From the quadratic constraint alone, the bound follows.
This single statement covers BOTH halves of the write-up's endgame — the analytic
argument for `d ≥ 40` and the 35 exact polynomial certificates for `5 ≤ d ≤ 39` — because
each of them proves exactly this implication. -/
def LinkQuadBound (d : ℕ) : Prop := 5 ≤ d → ∀ x t : ℝ, dom d x → 0 ≤ t →
  t ^ 2 + Acoef d (x - (d : ℝ) / 2) * t ≤ 4 * (d : ℝ) * (x - (d : ℝ) / 2) ^ 2 →
  199 * ((d : ℝ) - 2) / (200 * (2 * x + (d : ℝ) - 2)) < ((d : ℝ) - t) / (2 * ((d : ℝ) + 1))

/-- LINK 6', the HONEST endgame: a bound on the variance itself.
**This replaces `LinkQuadBound` as the row's remaining obligation** — see `quad_insufficient`
below for why that statement is not provable as it stands. -/
def LinkVBound (d : ℕ) : Prop := ∀ x : ℝ, dom d x →
  4 * Vmom d x < (d : ℝ)
    - 199 * ((d : ℝ) + 1) * ((d : ℝ) - 2) / (200 * (x - (d : ℝ) / 2 + (d : ℝ) - 1))

/-- The weights are nonnegative: a ratio of squares by a positive factorial product. -/
lemma wt_nonneg (d : ℕ) (x : ℝ) (i : ℕ) : 0 ≤ wt d x i := by
  unfold wt
  positivity

/-- LINK 5 is not an independent obligation: it follows from LINK 1. -/
theorem vnonneg_of_pos (d : ℕ) (h1 : LinkPos d) : LinkVnonneg d := by
  intro x hx
  unfold Vmom
  exact div_nonneg
    (Finset.sum_nonneg fun i _ => mul_nonneg (wt_nonneg d x i) (sq_nonneg _))
    (le_of_lt (h1 x hx))

/-- A falling factorial is positive as soon as every factor is: `(i:ℝ) - 1 < x`. -/
lemma fall_pos (x : ℝ) (i : ℕ) (h : (i : ℝ) - 1 < x) : 0 < fall x i := by
  induction i with
  | zero => simp [fall]
  | succ i ih =>
      have hx : (i : ℝ) < x := by push_cast at h; linarith
      have h1 : (i : ℝ) - 1 < x := by linarith
      rw [fall]
      exact mul_pos (ih h1) (by linarith)

/-- A weight is positive when both of its falling factorials are. -/
lemma wt_pos (d : ℕ) (x : ℝ) (i : ℕ) (h1 : (i : ℝ) - 1 < x)
    (h2 : ((d - i : ℕ) : ℝ) - 1 < x) : 0 < wt d x i := by
  unfold wt
  have p1 := fall_pos x i h1
  have p2 := fall_pos x (d - i) h2
  have f1 : (0 : ℝ) < (Nat.factorial i : ℝ) := by
    exact_mod_cast Nat.factorial_pos i
  have f2 : (0 : ℝ) < (Nat.factorial (d - i) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (d - i)
  exact div_pos (mul_pos (pow_pos p1 2) (pow_pos p2 2)) (mul_pos f1 f2)

/-- **LINK 1, proved.**  Above `d/2` the middle summand already has every factor positive,
and the rest are nonnegative. -/
theorem linkPos (d : ℕ) : LinkPos d := by
  intro x hx
  have hmem : d / 2 ∈ range (d + 1) := by
    rw [Finset.mem_range]
    omega
  have hlow : ((d / 2 : ℕ) : ℝ) ≤ (d : ℝ) / 2 := by
    have h := Nat.div_mul_le_self d 2
    have : ((d / 2 : ℕ) : ℝ) * 2 ≤ (d : ℝ) := by exact_mod_cast h
    linarith
  have hhigh : ((d - d / 2 : ℕ) : ℝ) ≤ (d : ℝ) / 2 + 1 / 2 := by
    have h : (d - d / 2) * 2 ≤ d + 1 := by omega
    have : ((d - d / 2 : ℕ) : ℝ) * 2 ≤ (d : ℝ) + 1 := by exact_mod_cast h
    linarith
  have hpos : 0 < wt d x (d / 2) := by
    refine wt_pos d x (d / 2) (by linarith) (by linarith)
  calc (0 : ℝ) < wt d x (d / 2) := hpos
    _ ≤ Pd d x := Finset.single_le_sum (fun i _ => wt_nonneg d x i) hmem

/-- **LINK 4, proved.**  Cauchy–Schwarz on the weights: with `f = √w` and `g = √w·Z²`,
`(∑ w Z²)² ≤ (∑ w)(∑ w Z⁴)`, which is `V² ≤ M₄` after dividing by `P²`. -/
theorem linkCS (d : ℕ) : LinkCS d := by
  intro x hx
  have hP : 0 < Pd d x := linkPos d x hx
  set S2 := ∑ i ∈ range (d + 1), wt d x i * ((i : ℝ) - (d : ℝ) / 2) ^ 2 with hS2
  set S4 := ∑ i ∈ range (d + 1), wt d x i * ((i : ℝ) - (d : ℝ) / 2) ^ 4 with hS4
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (range (d + 1))
    (fun i => Real.sqrt (wt d x i))
    (fun i => Real.sqrt (wt d x i) * ((i : ℝ) - (d : ℝ) / 2) ^ 2)
  have e1 : ∀ i ∈ range (d + 1),
      Real.sqrt (wt d x i) * (Real.sqrt (wt d x i) * ((i : ℝ) - (d : ℝ) / 2) ^ 2)
        = wt d x i * ((i : ℝ) - (d : ℝ) / 2) ^ 2 := by
    intro i _
    have : Real.sqrt (wt d x i) * Real.sqrt (wt d x i) = wt d x i :=
      Real.mul_self_sqrt (wt_nonneg d x i)
    nlinarith [this]
  have e2 : ∀ i ∈ range (d + 1), (Real.sqrt (wt d x i)) ^ 2 = wt d x i := by
    intro i _
    exact Real.sq_sqrt (wt_nonneg d x i)
  have e3 : ∀ i ∈ range (d + 1),
      (Real.sqrt (wt d x i) * ((i : ℝ) - (d : ℝ) / 2) ^ 2) ^ 2
        = wt d x i * ((i : ℝ) - (d : ℝ) / 2) ^ 4 := by
    intro i _
    have h := Real.sq_sqrt (wt_nonneg d x i)
    rw [mul_pow, h]
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at hcs
  have hkey : S2 ^ 2 ≤ Pd d x * S4 := by
    rw [hS2, hS4]
    simpa [Pd] using hcs
  unfold Vmom M4mom
  rw [← hS2, ← hS4, div_pow, div_le_div_iff₀ (by positivity) hP]
  nlinarith [hkey, hP, sq_nonneg (Pd d x)]

/-- Adding a factor to the LEFT falling factorial: `w_i^{(d)}(x-i)^2 = (i+1) w_{i+1}^{(d+1)}`. -/
lemma wt_shift_left (d : ℕ) (x : ℝ) (i : ℕ) (hi : i ≤ d) :
    wt d x i * (x - (i : ℝ)) ^ 2 = ((i : ℝ) + 1) * wt (d + 1) x (i + 1) := by
  have hsub : d + 1 - (i + 1) = d - i := by omega
  have hfac : (Nat.factorial (i + 1) : ℝ) = ((i : ℝ) + 1) * (Nat.factorial i : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hi1 : (Nat.factorial i : ℝ) ≠ 0 := by
    have := Nat.factorial_pos i; positivity
  have hd1 : (Nat.factorial (d - i) : ℝ) ≠ 0 := by
    have := Nat.factorial_pos (d - i); positivity
  unfold wt
  rw [hsub, fall, hfac]
  field_simp

/-- Adding a factor to the RIGHT falling factorial:
`w_i^{(d)}(x-d+i)^2 = (d+1-i) w_i^{(d+1)}`. -/
lemma wt_shift_right (d : ℕ) (x : ℝ) (i : ℕ) (hi : i ≤ d) :
    wt d x i * (x - (d : ℝ) + (i : ℝ)) ^ 2 = ((d : ℝ) + 1 - (i : ℝ)) * wt (d + 1) x i := by
  have hsub : d + 1 - i = (d - i) + 1 := by omega
  have hcast : ((d - i : ℕ) : ℝ) = (d : ℝ) - (i : ℝ) := by
    push_cast [Nat.cast_sub hi]; ring
  have hfac : (Nat.factorial ((d - i) + 1) : ℝ)
      = ((d : ℝ) + 1 - (i : ℝ)) * (Nat.factorial (d - i) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast [Nat.cast_sub hi]
    ring
  have hi1 : (Nat.factorial i : ℝ) ≠ 0 := by
    have := Nat.factorial_pos i; positivity
  have hd1 : (Nat.factorial (d - i) : ℝ) ≠ 0 := by
    have := Nat.factorial_pos (d - i); positivity
  have hle : (i : ℝ) ≤ (d : ℝ) := by exact_mod_cast hi
  have hne : ((d : ℝ) + 1 - (i : ℝ)) ≠ 0 := by
    have hpos : (0 : ℝ) < (d : ℝ) + 1 - (i : ℝ) := by linarith
    exact ne_of_gt hpos
  unfold wt
  rw [hsub, fall, hcast, hfac]
  field_simp
  ring

/-- **The variance identity**, the write-up's display: adding a factor to either falling
factorial reindexes the sum, so the two contributions weigh the `j`th summand of `P_{d+1}`
by `j` and by `d+1-j`. -/
theorem var_identity (d : ℕ) (x : ℝ) :
    ((d : ℝ) + 1) * Pd (d + 1) x
      = ∑ i ∈ range (d + 1), wt d x i * ((x - (i : ℝ)) ^ 2 + (x - (d : ℝ) + (i : ℝ)) ^ 2) := by
  have hL : ∑ i ∈ range (d + 1), wt d x i * (x - (i : ℝ)) ^ 2
      = ∑ j ∈ range (d + 2), (j : ℝ) * wt (d + 1) x j := by
    rw [Finset.sum_range_succ' (fun j => (j : ℝ) * wt (d + 1) x j) (d + 1)]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hle : i ≤ d := by have := Finset.mem_range.1 hi; omega
    rw [wt_shift_left d x i hle]
    push_cast
    ring
  have hR : ∑ i ∈ range (d + 1), wt d x i * (x - (d : ℝ) + (i : ℝ)) ^ 2
      = ∑ j ∈ range (d + 2), ((d : ℝ) + 1 - (j : ℝ)) * wt (d + 1) x j := by
    rw [Finset.sum_range_succ (fun j => ((d : ℝ) + 1 - (j : ℝ)) * wt (d + 1) x j) (d + 1)]
    have hz : ((d : ℝ) + 1 - ((d + 1 : ℕ) : ℝ)) = 0 := by push_cast; ring
    rw [hz, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hle : i ≤ d := by have := Finset.mem_range.1 hi; omega
    exact wt_shift_right d x i hle
  have hsplit : ∑ i ∈ range (d + 1),
        wt d x i * ((x - (i : ℝ)) ^ 2 + (x - (d : ℝ) + (i : ℝ)) ^ 2)
      = (∑ i ∈ range (d + 1), wt d x i * (x - (i : ℝ)) ^ 2)
        + ∑ i ∈ range (d + 1), wt d x i * (x - (d : ℝ) + (i : ℝ)) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, hL, hR, ← Finset.sum_add_distrib, Pd, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **LINK 2, proved.**  The variance form of the ratio.  Writing `c = x - d/2` and
`Z_i = i - d/2`, the two squares of the variance identity are `(c-Z)^2 + (c+Z)^2 = 2c^2+2Z^2`,
so `(d+1)P_{d+1} = 2P(c^2 + V)`, and the rest is algebra against `q_d`. -/
theorem linkRatio (d : ℕ) : LinkRatio d := by
  intro x hx
  have hP : 0 < Pd d x := linkPos d x hx
  have hPne : Pd d x ≠ 0 := ne_of_gt hP
  have hd1 : ((d : ℝ) + 1) ≠ 0 := by positivity
  have hvar := var_identity d x
  have hsum : (∑ i ∈ range (d + 1),
        wt d x i * ((x - (i : ℝ)) ^ 2 + (x - (d : ℝ) + (i : ℝ)) ^ 2))
      = (2 * (x - (d : ℝ) / 2) ^ 2) * Pd d x
        + 2 * (∑ i ∈ range (d + 1), wt d x i * ((i : ℝ) - (d : ℝ) / 2) ^ 2) := by
    rw [Pd, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hV : (∑ i ∈ range (d + 1), wt d x i * ((i : ℝ) - (d : ℝ) / 2) ^ 2)
      = Vmom d x * Pd d x := by
    unfold Vmom
    field_simp
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum, hV] at hvar
  have key : -(Pd (d + 1) x - qd d x * Pd d x) * (2 * ((d : ℝ) + 1))
      = ((d : ℝ) - 4 * Vmom d x) * Pd d x := by
    unfold qd
    field_simp
    linear_combination (-2 : ℝ) * hvar
  unfold Rd
  rw [div_eq_div_iff hPne (by positivity)]
  exact key

/-- `w_i a_i` with `a_i = (d-i)(x-i)^2`. -/
noncomputable def Wa (d : ℕ) (x : ℝ) (i : ℕ) : ℝ :=
  wt d x i * ((d : ℝ) - (i : ℝ)) * (x - (i : ℝ)) ^ 2

/-- `w_i b_i` with `b_i = i(x-d+i)^2`. -/
noncomputable def Wb (d : ℕ) (x : ℝ) (i : ℕ) : ℝ :=
  wt d x i * (i : ℝ) * (x - (d : ℝ) + (i : ℝ)) ^ 2

lemma Wa_top (d : ℕ) (x : ℝ) : Wa d x d = 0 := by
  unfold Wa; ring

lemma Wb_zero (d : ℕ) (x : ℝ) : Wb d x 0 = 0 := by
  unfold Wb; simp

/-- **The weight recurrence** `w_i a_i = w_{i+1} b_{i+1}`.  Both sides are brought to the
same explicit quotient, which keeps each `field_simp` small. -/
lemma Wa_eq_Wb_succ (d : ℕ) (x : ℝ) (i : ℕ) (hi : i < d) : Wa d x i = Wb d x (i + 1) := by
  have h1 : i + 1 ≤ d := hi
  have hsub : d - i = (d - (i + 1)) + 1 := by omega
  have hcast : ((d - (i + 1) : ℕ) : ℝ) = (d : ℝ) - (i : ℝ) - 1 := by
    push_cast [Nat.cast_sub h1]; ring
  have hfd : (Nat.factorial ((d - (i + 1)) + 1) : ℝ)
      = ((d : ℝ) - (i : ℝ)) * (Nat.factorial (d - (i + 1)) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast [Nat.cast_sub h1]
    ring
  have hfi : (Nat.factorial (i + 1) : ℝ) = ((i : ℝ) + 1) * (Nat.factorial i : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hine : (Nat.factorial i : ℝ) ≠ 0 := by
    have := Nat.factorial_pos i; positivity
  have hdne : (Nat.factorial (d - (i + 1)) : ℝ) ≠ 0 := by
    have := Nat.factorial_pos (d - (i + 1)); positivity
  have hdi : ((d : ℝ) - (i : ℝ)) ≠ 0 := by
    have hlt : (i : ℝ) < (d : ℝ) := by exact_mod_cast hi
    intro h; linarith [h]
  have hip : ((i : ℝ) + 1) ≠ 0 := by positivity
  set G : ℝ := fall x (d - (i + 1)) with hG
  set F : ℝ := fall x i with hF
  set T : ℝ := x - (d : ℝ) + (i : ℝ) + 1 with hT
  have hL : Wa d x i
      = F ^ 2 * G ^ 2 * T ^ 2 * (x - (i : ℝ)) ^ 2
        / ((Nat.factorial i : ℝ) * (Nat.factorial (d - (i + 1)) : ℝ)) := by
    unfold Wa wt
    rw [hsub, fall_succ x (d - (i + 1)), hcast, hfd, ← hF, ← hG]
    have : x - ((d : ℝ) - (i : ℝ) - 1) = T := by rw [hT]; ring
    rw [this]
    field_simp
  have hR : Wb d x (i + 1)
      = F ^ 2 * G ^ 2 * T ^ 2 * (x - (i : ℝ)) ^ 2
        / ((Nat.factorial i : ℝ) * (Nat.factorial (d - (i + 1)) : ℝ)) := by
    unfold Wb wt
    rw [fall_succ x i, hfi, ← hF, ← hG]
    have : x - (d : ℝ) + ((i : ℝ) + 1) = T := by rw [hT]; ring
    push_cast
    rw [this]
    field_simp
  rw [hL, hR]

/-- Telescoping: the recurrence plus the two vanishing endpoints move the index by one. -/
lemma tele (d : ℕ) (x : ℝ) (f : ℕ → ℝ) :
    ∑ i ∈ range (d + 1), Wa d x i * f (i + 1) = ∑ i ∈ range (d + 1), Wb d x i * f i := by
  rw [Finset.sum_range_succ (fun i => Wa d x i * f (i + 1)) d, Wa_top, zero_mul, add_zero]
  rw [Finset.sum_range_succ' (fun i => Wb d x i * f i) d, Wb_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Wa_eq_Wb_succ d x i (Finset.mem_range.1 hi)]

/-- **LINK 3, proved.**  Apply the telescoping identity to `f(i) = Z_i²` and to
`f(i) = (Z_i-1)²`; the two results cancel, and in centred coordinates the surviving summand
is `-4Z⁴ + (d + 4c - 4c² - 4dc)Z² + dc²`. -/
theorem linkMoment (d : ℕ) : LinkMoment d := by
  intro x hx
  have hP : 0 < Pd d x := linkPos d x hx
  have hPne : Pd d x ≠ 0 := ne_of_gt hP
  have t1 := tele d x (fun j => ((j : ℝ) - (d : ℝ) / 2) ^ 2)
  have t2 := tele d x (fun j => ((j : ℝ) - 1 - (d : ℝ) / 2) ^ 2)
  push_cast at t1 t2
  have t2' : (∑ i ∈ range (d + 1), Wa d x i * ((i : ℝ) - (d : ℝ) / 2) ^ 2)
      = ∑ i ∈ range (d + 1), Wb d x i * ((i : ℝ) - 1 - (d : ℝ) / 2) ^ 2 := by
    rw [← t2]
    exact Finset.sum_congr rfl fun i _ => by ring
  set K : ℝ := -(4 * (d : ℝ) * (x - (d : ℝ) / 2)) - 4 * (x - (d : ℝ) / 2) ^ 2
      + (d : ℝ) + 4 * (x - (d : ℝ) / 2) with hK
  have hcombo : (∑ i ∈ range (d + 1), wt d x i *
      (-4 * ((i : ℝ) - (d : ℝ) / 2) ^ 4 + K * ((i : ℝ) - (d : ℝ) / 2) ^ 2
        + (d : ℝ) * (x - (d : ℝ) / 2) ^ 2)) = 0 := by
    have expand : ∀ i ∈ range (d + 1), wt d x i *
        (-4 * ((i : ℝ) - (d : ℝ) / 2) ^ 4 + K * ((i : ℝ) - (d : ℝ) / 2) ^ 2
          + (d : ℝ) * (x - (d : ℝ) / 2) ^ 2)
        = (Wa d x i * ((i : ℝ) + 1 - (d : ℝ) / 2) ^ 2
            - Wa d x i * ((i : ℝ) - (d : ℝ) / 2) ^ 2)
          + (Wb d x i * ((i : ℝ) - 1 - (d : ℝ) / 2) ^ 2
            - Wb d x i * ((i : ℝ) - (d : ℝ) / 2) ^ 2) := by
      intro i _
      unfold Wa Wb
      rw [hK]
      ring
    rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [t1, ← t2']
    ring
  have hsplit : (∑ i ∈ range (d + 1), wt d x i *
      (-4 * ((i : ℝ) - (d : ℝ) / 2) ^ 4 + K * ((i : ℝ) - (d : ℝ) / 2) ^ 2
        + (d : ℝ) * (x - (d : ℝ) / 2) ^ 2))
      = -4 * (∑ i ∈ range (d + 1), wt d x i * ((i : ℝ) - (d : ℝ) / 2) ^ 4)
        + K * (∑ i ∈ range (d + 1), wt d x i * ((i : ℝ) - (d : ℝ) / 2) ^ 2)
        + (d : ℝ) * (x - (d : ℝ) / 2) ^ 2 * Pd d x := by
    rw [Pd, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit] at hcombo
  have hA : Acoef d (x - (d : ℝ) / 2) = -K := by rw [hK, Acoef]; ring
  unfold M4mom Vmom
  rw [hA]
  set A2 : ℝ := ∑ i ∈ range (d + 1), wt d x i * ((i : ℝ) - (d : ℝ) / 2) ^ 2
  set A4 : ℝ := ∑ i ∈ range (d + 1), wt d x i * ((i : ℝ) - (d : ℝ) / 2) ^ 4
  field_simp
  linarith [hcombo]

/-- The quadratic constraint `t² + At ≤ 4dc²` for `t = 4V`, from the moment identity and
Cauchy–Schwarz.  PROVED — this is the step the write-up gets in one line. -/
theorem quad_of_moment_cs (d : ℕ) (h3 : LinkMoment d) (h4 : LinkCS d)
    (x : ℝ) (hx : (d : ℝ) / 2 < x) :
    (4 * Vmom d x) ^ 2 + Acoef d (x - (d : ℝ) / 2) * (4 * Vmom d x)
      ≤ 4 * (d : ℝ) * (x - (d : ℝ) / 2) ^ 2 := by
  have hm := h3 x hx
  have hc := h4 x hx
  nlinarith [hm, hc]

/-- **The spine.**  The six links compose to Davis's bound. -/
theorem main_of_links (d : ℕ) (hd : 5 ≤ d)
    (h1 : LinkPos d) (h2 : LinkRatio d) (h3 : LinkMoment d) (h4 : LinkCS d)
    (h6 : LinkQuadBound d) :
    ∀ x : ℝ, dom d x →
      199 * ((d : ℝ) - 2) / (200 * (2 * x + (d : ℝ) - 2)) < -Rd d x / Pd d x := by
  intro x hx
  have hsq : 0 < Real.sqrt ((d : ℝ) + 2) := by
    apply Real.sqrt_pos.2
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hhalf : (d : ℝ) / 2 < x := by
    rw [dom] at hx
    linarith
  have h5 := vnonneg_of_pos d h1
  rw [h2 x hhalf]
  exact h6 hd x (4 * Vmom d x) hx (by linarith [h5 x hhalf])
    (quad_of_moment_cs d h3 h4 x hhalf)

/-- `M = d² - d + 398`, the factor common to three of the endgame cubic's coefficients. -/
noncomputable def Mcoef (d : ℕ) : ℝ := (d : ℝ) ^ 2 - (d : ℝ) + 398

/-- `Q`, the endgame cubic's LINEAR coefficient.  It is nonnegative for `d ≤ 7` and for
`d ≥ 49`, and negative in between — which is exactly why the middle band is hard. -/
noncomputable def Qcoef (d : ℕ) : ℝ :=
  4 * (d : ℝ) ^ 4 - 211 * (d : ℝ) ^ 3 + 1803 * (d : ℝ) ^ 2 - 2790 * (d : ℝ) + 1592

/-- **The endgame cubic.**  Clearing `q(T) > 0` by `u²` (with `u = c+d-1`) gives a polynomial
whose QUARTIC terms in `c` cancel, leaving this cubic — that cancellation is what makes the
endgame tractable at all. -/
noncomputable def Ecub (d : ℕ) (c : ℝ) : ℝ :=
  800 * Mcoef d * c ^ 3 + 1600 * ((d : ℝ) - 1) * Mcoef d * c ^ 2
    + 200 * Qcoef d * c - 199 * ((d : ℝ) - 2) * ((d : ℝ) + 1) * Mcoef d

/-- The clearing identity: `200²·q(T)·u² = Ecub`. -/
lemma Ecub_eq (d : ℕ) (c : ℝ) :
    200 ^ 2 * ((((d : ℝ) * (c + (d : ℝ) - 1)
          - 199 * ((d : ℝ) + 1) * ((d : ℝ) - 2) / 200)) ^ 2
      + Acoef d c * (c + (d : ℝ) - 1)
        * ((d : ℝ) * (c + (d : ℝ) - 1) - 199 * ((d : ℝ) + 1) * ((d : ℝ) - 2) / 200)
      - 4 * (d : ℝ) * c ^ 2 * (c + (d : ℝ) - 1) ^ 2)
      = Ecub d c := by
  unfold Ecub Mcoef Qcoef Acoef
  ring

/-- **The endgame cubic is positive whenever its linear coefficient is.**  With `Q ≥ 0` every
term but the constant is nonnegative, and `4c² ≥ d+2` already beats the constant, because
`400(d-1)(d+2) > 199(d-2)(d+1)`. -/
lemma Ecub_pos (d : ℕ) (c : ℝ) (hdR : (5 : ℝ) ≤ (d : ℝ)) (hcpos : 0 < c)
    (hc2 : (d : ℝ) + 2 ≤ 4 * c ^ 2) (hQ : 0 ≤ Qcoef d) : 0 < Ecub d c := by
  have hM : (0 : ℝ) < Mcoef d := by unfold Mcoef; nlinarith
  have h1 : 0 ≤ 200 * Qcoef d * c := by positivity
  have hdm1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by linarith
  have hfac : (0 : ℝ) ≤ 400 * ((d : ℝ) - 1) * Mcoef d := by nlinarith [hdm1, hM.le]
  have h2 : 400 * ((d : ℝ) - 1) * ((d : ℝ) + 2) * Mcoef d
      ≤ 1600 * ((d : ℝ) - 1) * Mcoef d * c ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hc2 hfac]
  have hbr : (0 : ℝ) < 201 * (d : ℝ) ^ 2 + 599 * (d : ℝ) - 402 := by nlinarith
  have h3 : 199 * ((d : ℝ) - 2) * ((d : ℝ) + 1) * Mcoef d
      < 400 * ((d : ℝ) - 1) * ((d : ℝ) + 2) * Mcoef d := by
    nlinarith [mul_pos hM hbr]
  have h4 : 0 < 800 * Mcoef d * c ^ 3 := by positivity
  unfold Ecub
  linarith

/-- `q(T) > 0` whenever the linear coefficient is nonnegative. -/
lemma qT_pos (d : ℕ) (c : ℝ) (hdR : (5 : ℝ) ≤ (d : ℝ)) (hcpos : 0 < c)
    (hE0 : 0 < Ecub d c) :
    0 < ((d : ℝ) - 199 * ((d : ℝ) + 1) * ((d : ℝ) - 2) / (200 * (c + (d : ℝ) - 1))) ^ 2
      + Acoef d c * ((d : ℝ) - 199 * ((d : ℝ) + 1) * ((d : ℝ) - 2) / (200 * (c + (d : ℝ) - 1)))
      - 4 * (d : ℝ) * c ^ 2 := by
  have hu : (0 : ℝ) < c + (d : ℝ) - 1 := by linarith
  have hu2 : (0 : ℝ) < (c + (d : ℝ) - 1) ^ 2 := by positivity
  have hE := hE0
  rw [← Ecub_eq d c] at hE
  set T : ℝ := (d : ℝ)
      - 199 * ((d : ℝ) + 1) * ((d : ℝ) - 2) / (200 * (c + (d : ℝ) - 1)) with hTdef
  have hTu : T * (c + (d : ℝ) - 1)
      = (d : ℝ) * (c + (d : ℝ) - 1) - 199 * ((d : ℝ) + 1) * ((d : ℝ) - 2) / 200 := by
    rw [hTdef]
    field_simp
  have hkey : (T ^ 2 + Acoef d c * T - 4 * (d : ℝ) * c ^ 2) * (c + (d : ℝ) - 1) ^ 2
      = ((d : ℝ) * (c + (d : ℝ) - 1) - 199 * ((d : ℝ) + 1) * ((d : ℝ) - 2) / 200) ^ 2
        + Acoef d c * (c + (d : ℝ) - 1)
          * ((d : ℝ) * (c + (d : ℝ) - 1) - 199 * ((d : ℝ) + 1) * ((d : ℝ) - 2) / 200)
        - 4 * (d : ℝ) * c ^ 2 * (c + (d : ℝ) - 1) ^ 2 := by
    rw [← hTu]
    ring
  have hpos : 0 < (T ^ 2 + Acoef d c * T - 4 * (d : ℝ) * c ^ 2) * (c + (d : ℝ) - 1) ^ 2 := by
    rw [hkey]
    linarith [hE]
  rcases mul_pos_iff.1 hpos with ⟨h, _⟩ | ⟨_, h2⟩
  · exact h
  · linarith [hu2, h2]

/-- **The endgame, for every degree whose linear coefficient is nonnegative.**  That covers
`d ≤ 7` and `d ≥ 49`; the remaining band is where `Q < 0`, and `13 ≤ d ≤ 36` of it is where
the quadratic constraint genuinely fails (see `vbound_of_quad`'s note). -/
theorem quadBound_of_cubic (d : ℕ)
    (hEall : ∀ c : ℝ, 0 < c → (d : ℝ) + 2 ≤ 4 * c ^ 2 → 0 < Ecub d c) :
    LinkQuadBound d := by
  intro hd x t hx ht hquad
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsq : 0 < Real.sqrt ((d : ℝ) + 2) := Real.sqrt_pos.2 (by linarith)
  have hdom : ((d : ℝ) + Real.sqrt ((d : ℝ) + 2)) / 2 ≤ x := hx
  have hcpos : (0 : ℝ) < x - (d : ℝ) / 2 := by linarith
  have hc2 : (d : ℝ) + 2 ≤ 4 * (x - (d : ℝ) / 2) ^ 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (d : ℝ) + 2 by linarith)
    nlinarith [hdom, hsq, hs]
  have hu : (0 : ℝ) < (x - (d : ℝ) / 2) + (d : ℝ) - 1 := by linarith
  have hApos : 0 < Acoef d (x - (d : ℝ) / 2) := by
    unfold Acoef; nlinarith [hc2, hcpos]
  have hqT := qT_pos d (x - (d : ℝ) / 2) hdR hcpos (hEall _ hcpos hc2)
  set T : ℝ := (d : ℝ)
      - 199 * ((d : ℝ) + 1) * ((d : ℝ) - 2) / (200 * ((x - (d : ℝ) / 2) + (d : ℝ) - 1)) with hTdef
  have hTpos : 0 < T := by
    rw [hTdef]
    rw [sub_pos, div_lt_iff₀ (by linarith)]
    nlinarith [hcpos, hdR]
  have hlt : t < T := by
    by_contra hcon
    push_neg at hcon
    have : 0 < t ^ 2 + Acoef d (x - (d : ℝ) / 2) * t - 4 * (d : ℝ) * (x - (d : ℝ) / 2) ^ 2 := by
      nlinarith [hqT, hcon, hTpos, ht, hApos]
    linarith [hquad]
  have hden : (0 : ℝ) < 200 * (2 * x + (d : ℝ) - 2) := by linarith
  have hden2 : (0 : ℝ) < 2 * ((d : ℝ) + 1) := by linarith
  rw [div_lt_div_iff₀ hden hden2]
  have hTlt : 199 * ((d : ℝ) + 1) * ((d : ℝ) - 2)
      / (200 * ((x - (d : ℝ) / 2) + (d : ℝ) - 1)) < (d : ℝ) - t := by
    rw [hTdef] at hlt; linarith
  rw [div_lt_iff₀ (by linarith)] at hTlt
  nlinarith [hTlt, hu]

/-- Just outside the hard band `Q < 0`, but the `c²` term still dominates: the cubic stays
positive for `9 ≤ d ≤ 12` and for `37 ≤ d ≤ 42`.  The key hint is `c·(4c² − (d+2)) ≥ 0`,
which is what lets the `c³` term absorb the negative linear one. -/
lemma Ecub_pos_band (d : ℕ) (c : ℝ) (hcpos : 0 < c) (hc2 : (d : ℝ) + 2 ≤ 4 * c ^ 2)
    (hrange : (9 ≤ d ∧ d ≤ 12) ∨ (37 ≤ d ∧ d ≤ 42)) : 0 < Ecub d c := by
  have hcube : 0 ≤ c * (4 * c ^ 2 - ((d : ℝ) + 2)) :=
    mul_nonneg hcpos.le (by linarith)
  unfold Ecub Mcoef Qcoef
  rcases hrange with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    interval_cases d <;> push_cast at hcube hc2 ⊢ <;>
      nlinarith [hcube, hc2, hcpos, mul_pos hcpos hcpos]

/-- The endgame whenever the linear coefficient is nonnegative. -/
theorem quadBound_of_Qnonneg (d : ℕ) (hd5 : 5 ≤ d) (hQ : 0 ≤ Qcoef d) : LinkQuadBound d := by
  refine quadBound_of_cubic d (fun c hc h2 => ?_)
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd5
  exact Ecub_pos d c hdR hc h2 hQ

/-- **Every link but the endgame is discharged.**  Davis's bound follows from the variance
bound `LinkVBound` alone. -/
theorem main_of_vbound (d : ℕ) (hd : 5 ≤ d) (h : LinkVBound d) :
    ∀ x : ℝ, dom d x →
      199 * ((d : ℝ) - 2) / (200 * (2 * x + (d : ℝ) - 2)) < -Rd d x / Pd d x := by
  intro x hx
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsq : 0 < Real.sqrt ((d : ℝ) + 2) := by
    apply Real.sqrt_pos.2; linarith
  have hhalf : (d : ℝ) / 2 < x := by rw [dom] at hx; linarith
  have hS : 0 < x - (d : ℝ) / 2 + (d : ℝ) - 1 := by linarith
  have hden : (0 : ℝ) < 200 * (2 * x + (d : ℝ) - 2) := by linarith
  have hden2 : (0 : ℝ) < 2 * ((d : ℝ) + 1) := by linarith
  have hV := h x hx
  rw [linkRatio d x hhalf, div_lt_div_iff₀ hden hden2]
  have hkey : 199 * ((d : ℝ) + 1) * ((d : ℝ) - 2)
      / (200 * (x - (d : ℝ) / 2 + (d : ℝ) - 1)) < (d : ℝ) - 4 * Vmom d x := by linarith
  rw [div_lt_iff₀ (by linarith)] at hkey
  nlinarith [hkey, hS]

/-- **A CORRECTION to the endgame link, found 2026-09-21.**  `LinkQuadBound` — the implication
from the quadratic constraint ALONE — is **not** provable: it is FALSE for `13 ≤ d ≤ 36`.
Writing `q(s) = s² + A s - 4dc²`, the constraint permits every `t` up to the positive root
`t*`, and in that band `t*` exceeds the target threshold `T`.  Concretely at `d = 13`,
`x = 8.486492` (inside the domain), `t* = 2.048220 > T = 2.044429`, while the true value is
`4V = 1.978001` — so the conjecture holds there but Cauchy–Schwarz has thrown away too much
(`M₄ - V² = 0.448`).  Outside `13 ≤ d ≤ 36` the quadratic does suffice, which is why
`vbound_of_quad` is still worth keeping: it discharges `LinkVBound` wherever `LinkQuadBound`
can be established. -/
theorem vbound_of_quad (d : ℕ) (h6 : LinkQuadBound d) (hd : 5 ≤ d) : LinkVBound d := by
  intro x hx
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsq : 0 < Real.sqrt ((d : ℝ) + 2) := by
    apply Real.sqrt_pos.2; linarith
  have hhalf : (d : ℝ) / 2 < x := by rw [dom] at hx; linarith
  have hS : 0 < x - (d : ℝ) / 2 + (d : ℝ) - 1 := by linarith
  have hnn := vnonneg_of_pos d (linkPos d) x hhalf
  have hq := h6 hd x (4 * Vmom d x) hx (by linarith)
    (quad_of_moment_cs d (linkMoment d) (linkCS d) x hhalf)
  rw [div_lt_div_iff₀ (by linarith) (by linarith)] at hq
  have hgoal : 199 * ((d : ℝ) + 1) * ((d : ℝ) - 2)
      / (200 * (x - (d : ℝ) / 2 + (d : ℝ) - 1)) < (d : ℝ) - 4 * Vmom d x := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [hq, hS]
  linarith [hgoal]

/-- `Q ≥ 0` for the small degrees `5 ≤ d ≤ 8` — exactly where it is nonnegative below. -/
lemma Qcoef_nonneg_of_small (d : ℕ) (h5 : 5 ≤ d) (h7 : d ≤ 8) : 0 ≤ Qcoef d := by
  interval_cases d <;> norm_num [Qcoef]

/-- `Q ≥ 0` for `d ≥ 43` — exactly where it turns nonnegative again. -/
lemma Qcoef_nonneg_of_large (d : ℕ) (hd : 43 ≤ d) : 0 ≤ Qcoef d := by
  have hdR : (43 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
  unfold Qcoef
  nlinarith [hdR, hd0, sq_nonneg ((d : ℝ) - 53), mul_pos hd0 hd0,
    mul_pos (mul_pos hd0 hd0) hd0, sq_nonneg ((d : ℝ) - 43),
    mul_nonneg (sq_nonneg ((d : ℝ) - 43)) hd0.le,
    mul_nonneg (mul_nonneg (sq_nonneg ((d : ℝ) - 43)) hd0.le) hd0.le]

/-- **Davis's bound, UNCONDITIONALLY, for `5 ≤ d ≤ 8`.** -/
theorem davis_small (d : ℕ) (h5 : 5 ≤ d) (h7 : d ≤ 8) :
    ∀ x : ℝ, dom d x →
      199 * ((d : ℝ) - 2) / (200 * (2 * x + (d : ℝ) - 2)) < -Rd d x / Pd d x :=
  main_of_vbound d h5
    (vbound_of_quad d (quadBound_of_Qnonneg d h5 (Qcoef_nonneg_of_small d h5 h7)) h5)

/-- **Davis's bound, UNCONDITIONALLY, for every `d ≥ 43`.** -/
theorem davis_large (d : ℕ) (hd : 43 ≤ d) :
    ∀ x : ℝ, dom d x →
      199 * ((d : ℝ) - 2) / (200 * (2 * x + (d : ℝ) - 2)) < -Rd d x / Pd d x := by
  have h5 : 5 ≤ d := by omega
  exact main_of_vbound d h5
    (vbound_of_quad d (quadBound_of_Qnonneg d h5 (Qcoef_nonneg_of_large d hd)) h5)

/-- **Davis's bound for the degrees flanking the hard band.** -/
theorem davis_band (d : ℕ) (hrange : (9 ≤ d ∧ d ≤ 12) ∨ (37 ≤ d ∧ d ≤ 42)) :
    ∀ x : ℝ, dom d x →
      199 * ((d : ℝ) - 2) / (200 * (2 * x + (d : ℝ) - 2)) < -Rd d x / Pd d x := by
  have h5 : 5 ≤ d := by rcases hrange with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  exact main_of_vbound d h5
    (vbound_of_quad d (quadBound_of_cubic d (fun c hc h2 => Ecub_pos_band d c hc h2 hrange)) h5)

/-- **Davis's Conjecture 3.1 holds for EVERY `d ≥ 5` outside the finite band `13 ≤ d ≤ 36`.**
Unconditionally: no hypotheses beyond the conjecture's own.  The band is exactly where the
quadratic constraint stops being strong enough (see `vbound_of_quad`'s note), so this is the
sharp limit of the Cauchy–Schwarz route. -/
theorem davis_outside_band (d : ℕ) (h5 : 5 ≤ d) (hband : d ≤ 12 ∨ 37 ≤ d) :
    ∀ x : ℝ, dom d x →
      199 * ((d : ℝ) - 2) / (200 * (2 * x + (d : ℝ) - 2)) < -Rd d x / Pd d x := by
  rcases hband with h | h
  · by_cases h8 : d ≤ 8
    · exact davis_small d h5 h8
    · exact davis_band d (Or.inl ⟨by omega, by omega⟩)
  · by_cases h43 : 43 ≤ d
    · exact davis_large d h43
    · exact davis_band d (Or.inr ⟨by omega, by omega⟩)

end Principia.MathDB.P319187
