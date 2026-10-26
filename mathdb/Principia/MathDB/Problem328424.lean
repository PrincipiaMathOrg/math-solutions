import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
-- the trace certificate raises a 10x10 integer matrix to the tenth power in the kernel; the
-- default recursion depth is reached while unfolding it.
set_option maxRecDepth 100000

/-!
# MathDB #328424 — Goldberg's Conjecture 6.2 is FALSE

Write-up: `mathdb-open-problems/problems/328424/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-30).
Source: F. Goldberg, *Graph energy estimates via the Chebyshev functional*, arXiv:1407.7430v3
(2014), **Conjecture 6.2**, p. 5.

The conjecture: `E(G) ≤ 2m/√λ₁` for every connected graph, where `E(G) = Σ|λᵢ|` is the adjacency
energy, `m` the number of edges and `λ₁` the spectral radius. The counterexample is the **corona
of the five-vertex star** — a ten-vertex tree with nine edges, energy `6 + 4√2` and spectral
radius `1 + √2`.

## Everything lives in `ℤ[√2]`, so the spectrum is WITNESSED rather than assumed

This row was priced one tick earlier as carrying "eigenvalue-theory risk", from memory, in a
commit message. That pricing was wrong, and the correction is the point of the module: the
spectrum of this tree is `{±(1+√2), ±(√2−1), 1×3, −1×3}`, every entry of which lies in `ℤ[√2]`,
and `ℤ[√2]` is a pair of integers that the kernel computes with.

Two independent certificates, both `decide`:

* **Eigenvectors.** `eigen_all` checks `A v = λ v` exactly for **ten** explicit vectors over
  `ℤ[√2]`, generated from the star's own eigenvectors by `liftVec` rather than transcribed. No
  eigenvalue is assumed; each is witnessed.
* **Traces.** `trace_powers` computes `tr(Aᵏ)` for `k = 1 … 10` by integer matrix powers and
  matches them against the power sums `Σλᵏ` of the claimed multiset, computed in `ℤ[√2]`. Power
  sums up to `n` determine a multiset of `n` reals, so this pins the spectrum rather than merely
  exhibiting members of it.

The one standing hypothesis is that last implication (Newton's identities), which is why
`conjecture_6_2_false` takes the energy and spectral radius as inputs. Mathlib has **no graph
energy** and no computational route from a concrete matrix to its spectrum — both re-checked by
grep this tick.

## The inequality itself is fully proved

`energy_gt_bound` is unconditional: `18/√(1+√2) < 6 + 4√2`. The write-up's reduction is exactly
the Lean proof — both sides are positive, squaring and multiplying by `1+√2` gives
`164 + 116√2 > 324`, which is `29√2 > 40`, which is the integer fact `2·29² = 1682 > 1600`.

## Findings the write-up does not state

* **The counterexample is the first member of its own family that works.** `T = T₄`, and the
  verifier measures that the ratio `E√λ₁/(2m)` first exceeds `1` at exactly `r = 4`.
* **The growth is slow, and a guessed threshold gets it wrong.** The ratio is `~ r^{1/4}/2`. A
  first draft of the verifier asserted it exceeds `1.5` within `r ≤ 39`; it does not (it reaches
  `1.427` there). The crossing points are now *measured and printed* rather than asserted:
  `1.0` at `r = 4`, `1.5` at `r = 51`, `2.0` at `r = 198`, `3.0` at `r = 1158`. Two of the three
  values I would have written by hand were wrong.
* **A partial answer to the write-up's own open Task 2.** It asks for the least order of a
  connected counterexample. An exhaustive sweep finds **none on six vertices or fewer**, so the
  least order is at least seven and the ten-vertex example is close to minimal.
-/

namespace Principia.MathDB.P328424

/-! ## The tree, as a corona -/

/-- `K_{1,4}` on `{0, 1, 2, 3, 4}` with centre `0`. -/
def edgesH : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4)]

/-- Attach one new leaf to each of the `n` vertices of a graph. -/
def corona (n : ℕ) (es : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  es ++ (List.range n).map (fun v => (v, v + n))

/-- The counterexample: the corona of the five-vertex star. -/
def edgesT : List (ℕ × ℕ) := corona 5 edgesH

theorem edgesT_eq :
    edgesT = [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)] := by
  decide

theorem card_edgesT : edgesT.length = 9 := by decide

/-- Ten vertices and nine edges, and the edge count is one less than the vertex count — together
with connectivity below, that is what makes `T` a tree. -/
theorem tree_count : edgesT.length + 1 = 10 := by decide

def incident (v : ℕ) (e : ℕ × ℕ) : Bool := e.1 == v || e.2 == v

def degT (v : ℕ) : ℕ := (edgesT.filter (incident v)).length

theorem degrees_T : ((List.range 10).map degT) = [5, 2, 2, 2, 2, 1, 1, 1, 1, 1] := by decide

def adjacentIn (es : List (ℕ × ℕ)) (p q : ℕ) : Bool :=
  es.any fun e => (e.1 == p && e.2 == q) || (e.1 == q && e.2 == p)

def expandOnce (es : List (ℕ × ℕ)) (verts seen : List ℕ) : List ℕ :=
  seen ++ verts.filter (fun q => !seen.contains q && seen.any (fun p => adjacentIn es p q))

def reachFrom : ℕ → List (ℕ × ℕ) → List ℕ → List ℕ → List ℕ
  | 0, _, _, seen => seen
  | n + 1, es, verts, seen => reachFrom n es verts (expandOnce es verts seen)

theorem connected_T : (reachFrom 10 edgesT (List.range 10) [0]).length = 10 := by decide

/-! ## `ℤ[√2]`, as a pair of integers -/

/-- `(a, b)` denotes `a + b√2`. -/
abbrev Z2 := ℤ × ℤ

def z2add (x y : Z2) : Z2 := (x.1 + y.1, x.2 + y.2)

def z2mul (x y : Z2) : Z2 := (x.1 * y.1 + 2 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

def z2ofInt (n : ℤ) : Z2 := (n, 0)

def z2pow (x : Z2) : ℕ → Z2
  | 0 => (1, 0)
  | n + 1 => z2mul (z2pow x n) x

/-! ## The adjacency matrix and the eigenvector certificate -/

def adjT : List (List ℤ) :=
  (List.range 10).map fun i => (List.range 10).map fun j =>
    if adjacentIn edgesT i j then 1 else 0

def mulVec (A : List (List ℤ)) (v : List Z2) : List Z2 :=
  A.map fun row => (row.zip v).foldl (fun acc p => z2add acc (z2mul (z2ofInt p.1) p.2)) (0, 0)

/-- From an eigenvector `w` of the star with eigenvalue `θ`, and a root `μ` of `x² − θx − 1`, the
corona's eigenvector is `(μ·w, w)`. Generating the ten vectors this way rather than typing a
hundred pairs is what keeps the certificate free of transcription error. -/
def liftVec (mu : Z2) (w : List ℤ) : List Z2 :=
  (w.map fun c => z2mul mu (z2ofInt c)) ++ (w.map fun c => z2ofInt c)

/-- The ten eigenpairs: `(μ, w)` with `μ` in `ℤ[√2]` and `w` an eigenvector of `K_{1,4}`. -/
def eigenData : List (Z2 × List ℤ) :=
  [((1, 1), [2, 1, 1, 1, 1]), ((1, -1), [2, 1, 1, 1, 1]),
   ((-1, 1), [-2, 1, 1, 1, 1]), ((-1, -1), [-2, 1, 1, 1, 1]),
   ((1, 0), [0, 1, -1, 0, 0]), ((-1, 0), [0, 1, -1, 0, 0]),
   ((1, 0), [0, 0, 1, -1, 0]), ((-1, 0), [0, 0, 1, -1, 0]),
   ((1, 0), [0, 0, 0, 1, -1]), ((-1, 0), [0, 0, 0, 1, -1])]

/-- **Every claimed eigenvalue is witnessed.** `A v = λ v` exactly, in `ℤ[√2]`, for all ten. -/
theorem eigen_all :
    (eigenData.all fun p =>
      mulVec adjT (liftVec p.1 p.2) == (liftVec p.1 p.2).map (z2mul p.1)) = true := by
  decide

theorem eigen_count : eigenData.length = 10 := by decide

/-! ## The trace certificate, which pins the multiset -/

def matMul (A B : List (List ℤ)) : List (List ℤ) :=
  A.map fun row => (List.range (B.headD []).length).map fun j =>
    ((row.zip B).map fun p => p.1 * (p.2.getD j 0)).sum

def matPow (A : List (List ℤ)) : ℕ → List (List ℤ)
  | 0 => (List.range A.length).map fun i => (List.range A.length).map fun j =>
      if i == j then 1 else 0
  | n + 1 => matMul (matPow A n) A

def trace (A : List (List ℤ)) : ℤ := ((List.range A.length).map fun i => (A.getD i []).getD i 0).sum

/-- The claimed spectrum, as elements of `ℤ[√2]`. -/
def spectrum : List Z2 :=
  [(1, 1), (-1, -1), (-1, 1), (1, -1), (1, 0), (1, 0), (1, 0), (-1, 0), (-1, 0), (-1, 0)]

def powerSum (k : ℕ) : Z2 :=
  spectrum.foldl (fun acc lam => z2add acc (z2pow lam k)) (0, 0)

/-- **The power sums match the traces for `k = 1 … 10`.** Power sums up to `n` determine a
multiset of `n` reals, so this pins the spectrum rather than merely exhibiting members of it —
and every trace is an ordinary integer, because the surd cancels. -/
theorem trace_powers :
    ((List.range 10).all fun k =>
      powerSum (k + 1) == z2ofInt (trace (matPow adjT (k + 1)))) = true := by
  decide

/-! ## The energy and the spectral radius, from the spectrum -/

/-- For `θ ≥ 0` the two corona roots have opposite signs, so their absolute values sum to
`√(θ²+4)`. This is the engine of both the specific energy and the family formula. -/
theorem corona_pair_abs_sum (t : ℝ) (ht : 0 ≤ t) :
    |(t + Real.sqrt (t ^ 2 + 4)) / 2| + |(t - Real.sqrt (t ^ 2 + 4)) / 2|
      = Real.sqrt (t ^ 2 + 4) := by
  have hs : Real.sqrt (t ^ 2 + 4) ^ 2 = t ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt (t ^ 2 + 4) := Real.sqrt_nonneg _
  have hgt : t < Real.sqrt (t ^ 2 + 4) := by nlinarith
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  ring

/-- `E(T) = 2(1+√2) + 2(√2−1) + 6 = 6 + 4√2`. -/
theorem energy_value : 2 * (1 + Real.sqrt 2) + 2 * (Real.sqrt 2 - 1) + 6 = 6 + 4 * Real.sqrt 2 := by
  ring

/-- `λ₁ = 1 + √2`, because `1 < √2 < 2`. -/
theorem sqrt2_bounds : 1 < Real.sqrt 2 ∧ Real.sqrt 2 < 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith

theorem spectral_radius_is_largest :
    Real.sqrt 2 - 1 < 1 + Real.sqrt 2 ∧ (1 : ℝ) < 1 + Real.sqrt 2 := by
  have := (sqrt2_bounds).1
  constructor <;> linarith

/-! ## The inequality, unconditionally -/

theorem sqrt2_gt_forty_over_29 : (40 : ℝ) / 29 < Real.sqrt 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

/-- **The refutation's arithmetic, in full.** `18/√(1+√2) < 6 + 4√2`. Both sides are positive;
squaring and multiplying by `1+√2` gives `164 + 116√2 > 324`, i.e. `29√2 > 40`, i.e. the integer
fact `2·29² = 1682 > 1600 = 40²`. -/
theorem energy_gt_bound : 18 / Real.sqrt (1 + Real.sqrt 2) < 6 + 4 * Real.sqrt 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 := (sqrt2_bounds).1
  have h40 := sqrt2_gt_forty_over_29
  have hpos : (0 : ℝ) < 1 + Real.sqrt 2 := by linarith
  have ht : Real.sqrt (1 + Real.sqrt 2) ^ 2 = 1 + Real.sqrt 2 := Real.sq_sqrt hpos.le
  have ht0 : 0 < Real.sqrt (1 + Real.sqrt 2) := Real.sqrt_pos.mpr hpos
  rw [div_lt_iff₀ ht0]
  set t := Real.sqrt (1 + Real.sqrt 2) with htdef
  have hx0 : 0 < (6 + 4 * Real.sqrt 2) * t := by positivity
  have hx2 : ((6 + 4 * Real.sqrt 2) * t) ^ 2 = 164 + 116 * Real.sqrt 2 := by
    rw [mul_pow, ht]; nlinarith [hs]
  have hbig : (324 : ℝ) < 164 + 116 * Real.sqrt 2 := by linarith
  nlinarith [hx0, hx2, hbig]

/-! ## The refutation -/

/-- **Goldberg's Conjecture 6.2 is false.** With the tree's energy and spectral radius as inputs
— the only facts this module does not prove, because Mathlib has no graph energy — the bound
`E ≤ 2m/√λ₁` fails on a connected ten-vertex tree with nine edges. -/
theorem conjecture_6_2_false (E lam1 : ℝ) (m : ℕ)
    (hE : E = 6 + 4 * Real.sqrt 2) (hlam : lam1 = 1 + Real.sqrt 2) (hm : m = 9) :
    2 * (m : ℝ) / Real.sqrt lam1 < E := by
  subst hE hlam hm
  have h : (2 : ℝ) * ((9 : ℕ) : ℝ) / Real.sqrt (1 + Real.sqrt 2)
      = 18 / Real.sqrt (1 + Real.sqrt 2) := by norm_num
  rw [h]
  exact energy_gt_bound

/-! ## The family, and why the growth is slow -/

/-- **The family's engine.** For `K_{1,r}` the star eigenvalues are `±√r`, and the corona sends
each to a pair whose absolute values sum to `√(r+4)`. Two such pairs give the `2√(r+4)` in
`E(T_r) = 2(r−1) + 2√(r+4)`; the `r−1` zero eigenvalues give the `2(r−1)`. -/
theorem corona_pair_of_sqrt (r : ℝ) (hr : 0 ≤ r) :
    |(Real.sqrt r + Real.sqrt (r + 4)) / 2| + |(Real.sqrt r - Real.sqrt (r + 4)) / 2|
      = Real.sqrt (r + 4) := by
  have h := corona_pair_abs_sum (Real.sqrt r) (Real.sqrt_nonneg r)
  rwa [Real.sq_sqrt hr] at h

end Principia.MathDB.P328424
