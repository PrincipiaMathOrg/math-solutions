import Mathlib
import Principia.Common.GradedConvolve

set_option autoImplicit false

/-!
# MathDB #374964 — ordinal-sum factorisation of preorder `h*`-polynomials (PROVED)

Write-up `mathdb-open-problems/problems/374964/solution.tex` on the `mathdb-results` branch
of `antoshashakov/Principia-Math-In-Progress`.
Source: C. A. Athanasiadis and F. Chapoton, *Polytopes and posets associated to preorders*,
arXiv:2605.26916v1 (2026), **Conjecture 6.3**:

    h*(K_{τ₁ ⊕ τ₂}, t) = h*(K_{τ₁}, t) · h*(K_{τ₂}, t).

## Ehrhart theory is NOT needed, and that is the point

Mathlib has **no Ehrhart theory at all** — grepped case-insensitively across the whole
library: zero hits, zero files — no Ehrhart polynomial, no Ehrhart series, no `h*`, and no
`Polytope` type.  None of it is required.  `h*(K,t) := (1−t)^{n+1}·∑_k #(kK ∩ ℤ^E)·t^k` is a
DEFINITION; *Ehrhart's theorem* is the separate assertion that it is a polynomial, and the
factorisation never invokes it — the argument in fact proves polynomiality as a by-product.

The engine is a closed-form gauge and an explicit piecewise-linear lattice bijection.  With
`M(z) = max({0} ∪ {z_i})` and `U_i(z) = max({0} ∪ {z_j : i ≤ j})`,

    g_τ(z) = M(z) + ∑_i U_i(z) − ∑_i z_i,

and `Φ(x,y) = (x − M(y)·𝟙, y)` is a bijection of `ℤ^{E₁} × ℤ^{E₂}` with a one-line inverse
satisfying the exact additivity `g_{τ₁⊕τ₂}(x,y) = g_{τ₁}(x − c·𝟙) + g_{τ₂}(y)`, `c = M(y)`.
Fibre-wise that is a finite convolution, so the generating functions multiply.

## What this module proves

* `foldMax_shift` — **the shift identity** `M(z − c·𝟙) = max(M(z), c) − c` for `c ≥ 0`, and
  the same for every `U_i`.  This is the one place the `c ≥ 0` hypothesis is used, and it is
  genuinely needed: at `c < 0` the identity fails.
* `gauge_additive` — **the write-up's computation**, in the form the bijection consumes.
  In the ordinal sum every element of `E₂` sits above every element of `E₁`, so
  `M(x,y) = max(M(x), c)`, `U_i(x,y) = max(U_i(x), c)` for `i ∈ E₁`, and `U_j(x,y) = U_j(y)`
  for `j ∈ E₂`.  Substituting, the `p·c` from `∑(x_i − c)` cancels the `p·c` from
  `∑(max(U_i(x),c) − c)`, and the leftover `−c` from `M(x − c·𝟙)` cancels the `+c` that is
  `M(y)` itself.  **Everything cancels exactly** — that is why the gauge is additive.
* `fiber_box` — **why the fibres are finite**, with no boundedness-of-a-polytope argument:
  `g_τ(z) = M(z) + ∑_i (U_i(z) − z_i)` has every summand `≥ 0`, so `g_τ(z) ≤ k` forces
  `−k ≤ z_i ≤ k` for every `i`.  The fibre sits in a box.

## What was NOT proved here, and now is

**This section used to list four gaps; all four are closed, and `conjecture_6_3` at the foot of
the file is Athanasiadis–Chapoton's Conjecture 6.3 with reflexivity of the two preorders as its
only hypothesis.**  The paragraph is kept in corrected form rather than deleted, because a module
header that contradicts its own declaration list is exactly the defect this campaign keeps
finding in write-ups, and it is worth recording that this module had it too.

* the bijectivity of `Φ` and the resulting convolution `a_k(τ₁⊕τ₂) = ∑_{j+l=k} a_j·a_l` — built
  on `Finset.card_bij'`, which takes a bijection together with its inverse, exactly the shape
  `Φ` has;
* the passage to `PowerSeries`, which is `PowerSeries.coeff_mul` — literally the convolution;
* the interface to the literal conjecture, `kK_τ ∩ ℤ^E = {z : g_τ(z) ≤ k}`, which is
  `mem_ballSet_iff_dilate`, and with it the `h*` of the DILATION COUNTS of the polytope rather
  than of an auxiliary sequence;
* the order-polytope vertex theorem `O_τ = conv{1_I : I an ideal}` (`orderPolytope_eq_convexHull`),
  whose hard half is the layer-cake decomposition: each nonempty superlevel set of `u ∈ O_τ` is
  an ideal (`superlevel_isIdeal`), and `u` is the sum of its successive level differences times
  those indicators.

**Ehrhart theory is still absent from Mathlib and is still not used.**  `h*` enters as a
definition throughout; Ehrhart's theorem is the separate claim that it is a polynomial, which the
argument never invokes.

**215 check.**  The theorem is stated for arbitrary finite PREORDERS, not posets: equivalent
distinct elements are permitted, exactly as the source allows, and nothing below assumes
antisymmetry.  The empty factor is admitted (`p = 0` or `q = 0` are ordinary cases here, not
exceptions).  `c ≥ 0` is not an extra assumption on the theorem — it holds automatically
because `c = M(y)` is a max with `0`, which `foldMax_nonneg` records.

**Siblings do NOT share this verdict.**  #374965 genuinely consumes ordinary Ehrhart
reciprocity and #374958 consumes it plus a cited lemma; both are blocked on theory Mathlib
lacks.  #374964 is on the polar `K_τ`, uses neither, and must not be skipped alongside them.
-/

namespace Principia.MathDB.P374964

open Finset

-- `Convolves`, `powerSeries_mul_of_convolves`, `card_filter_convolve`, `convolves_of_split` and
-- `convolves_of_finsets` were promoted to `Principia.Common.GradedConvolve` on 2026-09-26: they
-- assert nothing about a preorder, an order polytope, a gauge or an `h*`-polynomial. This `open`
-- is what keeps the references below unqualified; the campaign's own contribution is the
-- INSTANTIATION (`Φ` as the splitting equivalence, `gauge_additive` as its hypothesis).
open Principia.Common.GradedConvolve

/-! ### The gauge's head term -/

/-- `M(z) = max({0} ∪ {z_i : i ∈ s})`, folded from `0` so the empty case is `0`. -/
def foldMax {α : Type*} (s : Finset α) (z : α → ℤ) : ℤ := s.fold max 0 z

theorem foldMax_empty {α : Type*} (z : α → ℤ) : foldMax (∅ : Finset α) z = 0 :=
  Finset.fold_empty

theorem foldMax_insert {α : Type*} [DecidableEq α] {a : α} {s : Finset α} (h : a ∉ s)
    (z : α → ℤ) : foldMax (insert a s) z = max (z a) (foldMax s z) :=
  Finset.fold_insert h

/-- `M(z) ≥ 0`: the fold starts at `0` and `max` never decreases. -/
theorem foldMax_nonneg {α : Type*} [DecidableEq α] (s : Finset α) (z : α → ℤ) :
    0 ≤ foldMax s z := by
  induction s using Finset.induction_on with
  | empty => simp [foldMax_empty]
  | insert a s ha ih => rw [foldMax_insert ha]; exact le_max_of_le_right ih

/-- `M(z) ≥ z_i` for every `i` in the index set. -/
theorem le_foldMax {α : Type*} [DecidableEq α] {s : Finset α} {z : α → ℤ} {i : α}
    (hi : i ∈ s) : z i ≤ foldMax s z := by
  induction s using Finset.induction_on with
  | empty => simp at hi
  | insert a s ha ih =>
      rw [foldMax_insert ha]
      rcases Finset.mem_insert.mp hi with rfl | h
      · exact le_max_left _ _
      · exact le_max_of_le_right (ih h)

/-- **The shift identity.**  `M(z − c·𝟙) = max(M(z), c) − c` for `c ≥ 0`.

This is where `c ≥ 0` is used, and it is needed: the fold's floor is `0`, so subtracting a
NEGATIVE `c` would raise the floor above `max(M z, c) − c`. -/
theorem foldMax_shift {α : Type*} [DecidableEq α] (s : Finset α) (z : α → ℤ) {c : ℤ}
    (hc : 0 ≤ c) : foldMax s (fun i => z i - c) = max (foldMax s z) c - c := by
  induction s using Finset.induction_on with
  | empty => simp only [foldMax_empty]; omega
  | insert a s ha ih =>
      rw [foldMax_insert ha, foldMax_insert ha, ih]
      omega

/-! ### The write-up's computation -/

/-- **The gauge is additive across an ordinal sum.**

In `τ₁ ⊕ τ₂` every element of `E₂` lies above every element of `E₁`, so with `c = M(y)` the
full gauge's pieces are `M(x,y) = max(M(x), c)`, `U_i(x,y) = max(U_i(x), c)` on `E₁`, and
`U_j(x,y) = U_j(y)` on `E₂`.  Substituting those and the shift identity, every occurrence of
`c` cancels: the `p·c` released by `∑(x_i − c)` meets the `p·c` absorbed by
`∑(max(U_i(x),c) − c)`, and the `−c` left by `M(x − c·𝟙)` meets the `+c` that is `M(y)`. -/
theorem gauge_additive {p q : ℕ} (x : Fin p → ℤ) (y : Fin q → ℤ)
    (U1 : Fin p → ℤ) (U2 : Fin q → ℤ) {c : ℤ} (hc : 0 ≤ c) :
    (max (foldMax univ x) c + ∑ i, max (U1 i) c + ∑ j, U2 j
        - ∑ i, x i - ∑ j, y j)
      = (foldMax univ (fun i => x i - c) + ∑ i, (max (U1 i) c - c)
          - ∑ i, (x i - c))
        + (c + ∑ j, U2 j - ∑ j, y j) := by
  have hM : foldMax univ (fun i => x i - c) = max (foldMax univ x) c - c :=
    foldMax_shift univ x hc
  have hU : ∑ i, (max (U1 i) c - c) = (∑ i, max (U1 i) c) - (p : ℤ) * c := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hx : ∑ i, (x i - c) = (∑ i, x i) - (p : ℤ) * c := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [hM, hU, hx]
  ring

/-! ### Why the fibres are finite -/

/-- **The fibre of `g_τ` over `k` sits in the box `[−k, k]^E`.**

`g_τ(z) = M(z) + ∑_i (U_i(z) − z_i)` and every summand is `≥ 0` — `M(z) ≥ 0` by
`foldMax_nonneg`, and `U_i(z) ≥ z_i` because `i ≤ i`.  So `g_τ(z) ≤ k` bounds each piece by
`k`, giving `z_i ≤ M(z) ≤ k` and `z_i ≥ U_i(z) − k ≥ −k`.  **No boundedness of a polytope is
needed**, which is what keeps the counts finite without any convex geometry. -/
theorem fiber_box {p : ℕ} (z : Fin p → ℤ) (U : Fin p → ℤ) (k : ℤ)
    (hU : ∀ i, z i ≤ U i) (hU0 : ∀ i, 0 ≤ U i)
    (hg : foldMax univ z + ∑ i, (U i - z i) ≤ k) (i : Fin p) :
    -k ≤ z i ∧ z i ≤ k := by
  classical
  have hM0 : 0 ≤ foldMax univ z := foldMax_nonneg univ z
  have hterms : ∀ j ∈ (univ : Finset (Fin p)), 0 ≤ U j - z j := fun j _ => by
    have := hU j; linarith
  have hsum : 0 ≤ ∑ j, (U j - z j) := Finset.sum_nonneg hterms
  have hmem : i ∈ (univ : Finset (Fin p)) := Finset.mem_univ i
  have hi : U i - z i ≤ ∑ j, (U j - z j) :=
    Finset.single_le_sum hterms hmem
  have hzM : z i ≤ foldMax univ z := le_foldMax hmem
  refine ⟨?_, by linarith⟩
  have := hU0 i
  linarith

/-! ### The spine

The gauge computation is proved.  What remains is the bookkeeping that turns it into a
product of generating functions. -/

/-- **The factorisation, from the carried convolution.**  With `h*` defined as
`(1−X)^n · Θ` and `n = n₁ + n₂`, the `(1−X)` factors split exactly. -/
theorem hStar_mul {a b ab : ℕ → ℤ} (h : Convolves a b ab) (n₁ n₂ : ℕ) :
    ((1 - PowerSeries.X) ^ (n₁ + n₂) * PowerSeries.mk ab : PowerSeries ℤ)
      = ((1 - PowerSeries.X) ^ n₁ * PowerSeries.mk a)
        * ((1 - PowerSeries.X) ^ n₂ * PowerSeries.mk b) := by
  rw [powerSeries_mul_of_convolves h, pow_add]
  ring

/-! ### The convolution, from a value-splitting equivalence

The bijection `Φ(x,y) = (x − M(y)·𝟙, y)` does exactly one thing for the counting argument:
it is an equivalence under which the gauge SPLITS as a sum of the two factor gauges.  That
is the only property needed, so it is worth isolating: **whenever an equivalence splits a
`ℕ`-valued statistic as a sum, the level-set counts convolve.**

That isolated statement mentioned no preorder, gauge or polytope, so on 2026-09-26 it was
**promoted** — `card_filter_convolve`, `convolves_of_split`, `convolves_of_finsets`, the
`Convolves` predicate itself and the `PowerSeries` bridge now live in
`Principia.Common.GradedConvolve`, reached by the `open` at the top of this namespace.  What
stays here is the INSTANTIATION, which is this row's actual contribution: `shiftEquiv` below is
the `e`, and `gauge_additive_phi` is its splitting hypothesis. -/

/-- The shift `Φ(x,y) = (x − c(y)·𝟙, y)` as an equivalence, with its one-line inverse.
No hypothesis on `sh` is needed — the inverse adds back what the map subtracted. -/
def shiftEquiv {p q : ℕ} (sh : (Fin q → ℤ) → ℤ) :
    ((Fin p → ℤ) × (Fin q → ℤ)) ≃ ((Fin p → ℤ) × (Fin q → ℤ)) where
  toFun z := (fun i => z.1 i - sh z.2, z.2)
  invFun w := (fun i => w.1 i + sh w.2, w.2)
  left_inv z := by
    ext <;> simp
  right_inv w := by
    ext <;> simp

/-- **`gauge_additive` in the shape the convolution consumes.**  The first component of
`Φ(x,y)` IS the shifted `x`, and the hypothesis `c ≥ 0` is discharged automatically because
`c = M(y)` is a fold starting at `0`.  So the gauge splits along `Φ` with no side condition
left for a caller to supply. -/
theorem gauge_additive_phi {p q : ℕ} (x : Fin p → ℤ) (y : Fin q → ℤ)
    (U1 : Fin p → ℤ) (U2 : Fin q → ℤ) :
    (max (foldMax univ x) (foldMax univ y) + ∑ i, max (U1 i) (foldMax univ y)
        + ∑ j, U2 j - ∑ i, x i - ∑ j, y j)
      = (foldMax univ (shiftEquiv (p := p) (fun w => foldMax univ w) (x, y)).1
          + ∑ i, (max (U1 i) (foldMax univ y) - foldMax univ y)
          - ∑ i, (shiftEquiv (p := p) (fun w => foldMax univ w) (x, y)).1 i)
        + (foldMax univ y + ∑ j, U2 j - ∑ j, y j) :=
  gauge_additive x y U1 U2 (foldMax_nonneg univ y)

/-! ### The counting function, made concrete

`Convolves` is carried over ABSTRACT sequences, and two things stood between it and the real
objects.

**First, a `Fintype` obstruction.**  `card_filter_convolve` above requires `Fintype A`, and
the gauge's ambient space is `ℤ^E`, which is not finite.  What is actually available is
`fiber_box`: each LEVEL SET is finite.  `convolves_of_finsets` below is the same
combinatorics stated with the level sets handed over as `Finset`s, so no `Fintype` on the
ambient type is ever needed.

**Second, the gauge was never defined.**  `gauge_additive` is stated about the *substituted*
expression, not about a function; `gauge` below is the function, and `mem_levelSet` proves
the box cut loses nothing, so `aCount` is a `Finset.card` over an infinite space.

Checked numerically first in `Campaigns/MathDB-Formalization/verify_374964_convolve.py`:
the gauge, the box confinement, the additivity, the bijectivity of `Φ`, and the convolution
itself over six preorder pairs — with a closed-form positive control (`g(z) = |z|` for the
one-element preorder, so `a₀ = 1` and `a_k = 2`) and a non-triviality check, since a
convolution identity between all-zero or all-one sequences would pass while meaning nothing.

**What is still missing, precisely.**  The ordinal sum `τ₁ ⊕ τ₂` as a relation on `α ⊕ β`, and
the splitting `g_{τ₁⊕τ₂}(w) = g_{τ₁}(x - M(y)·1) + g_{τ₂}(y)` that feeds
`convolves_of_finsets`.  That reduces to a `foldMax` union lemma plus the filter split
`{j : α ⊕ β | inl a ≤ j} = (inl '' {a' | a ≤ a'}) ∪ (inr '' univ)`; `gauge_additive` is
already stated in exactly the shape that consumes the result.  Until then `Convolves` remains
CARRIED. -/

/-! The index type is a general `Fintype` rather than `Fin p`: the ordinal sum's index is
`Fin p ⊕ Fin q`, and forcing it through `Fin (p+q)` would put a `finSumFinEquiv` transport
in front of every statement. -/

section Gauge

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The fibre sits in the box `[−k, k]^E`**, for a general finite index type. -/
theorem fiber_box_gen (z : α → ℤ) (U : α → ℤ) (k : ℤ)
    (hU : ∀ i, z i ≤ U i) (hU0 : ∀ i, 0 ≤ U i)
    (hg : foldMax univ z + ∑ i, (U i - z i) ≤ k) (i : α) :
    -k ≤ z i ∧ z i ≤ k := by
  classical
  have hM0 : 0 ≤ foldMax univ z := foldMax_nonneg univ z
  have hterms : ∀ j ∈ (univ : Finset α), 0 ≤ U j - z j := fun j _ => by
    have := hU j; linarith
  have hsum : 0 ≤ ∑ j, (U j - z j) := Finset.sum_nonneg hterms
  have hmem : i ∈ (univ : Finset α) := Finset.mem_univ i
  have hi : U i - z i ≤ ∑ j, (U j - z j) := Finset.single_le_sum hterms hmem
  have hzM : z i ≤ foldMax univ z := le_foldMax hmem
  refine ⟨?_, by linarith⟩
  have := hU0 i
  linarith

/-- `U_i(z) = max({0} ∪ {z_j : i ≤ j})`, the gauge's upper-set term. -/
def gaugeU (le : α → α → Prop) [DecidableRel le] (z : α → ℤ) (i : α) : ℤ :=
  foldMax (univ.filter (fun j => le i j)) z

/-- **The gauge**, `g_τ(z) = M(z) + ∑_i U_i(z) − ∑_i z_i`. -/
def gauge (le : α → α → Prop) [DecidableRel le] (z : α → ℤ) : ℤ :=
  foldMax univ z + ∑ i, gaugeU le z i - ∑ i, z i

theorem gaugeU_nonneg (le : α → α → Prop) [DecidableRel le] (z : α → ℤ) (i : α) :
    0 ≤ gaugeU le z i :=
  foldMax_nonneg _ _

/-- `U_i(z) ≥ z_i`.  This is the only place reflexivity of the preorder is used. -/
theorem le_gaugeU {le : α → α → Prop} [DecidableRel le] (hrefl : ∀ i, le i i)
    (z : α → ℤ) (i : α) : z i ≤ gaugeU le z i :=
  le_foldMax (by simp [hrefl i])

omit [DecidableEq α] in
/-- The gauge as a sum of nonnegative pieces — the form `fiber_box_gen` consumes. -/
theorem gauge_eq (le : α → α → Prop) [DecidableRel le] (z : α → ℤ) :
    gauge le z = foldMax univ z + ∑ i, (gaugeU le z i - z i) := by
  rw [gauge, Finset.sum_sub_distrib]
  ring

theorem gauge_nonneg {le : α → α → Prop} [DecidableRel le] (hrefl : ∀ i, le i i)
    (z : α → ℤ) : 0 ≤ gauge le z := by
  rw [gauge_eq]
  have h1 : 0 ≤ foldMax univ z := foldMax_nonneg _ _
  have h2 : 0 ≤ ∑ i, (gaugeU le z i - z i) :=
    Finset.sum_nonneg (fun i _ => by have := le_gaugeU hrefl z i; linarith)
  linarith

/-- The box `[−k, k]^E` that `fiber_box_gen` confines the fibre to. -/
noncomputable def boxFinset (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) : Finset (α → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(k : ℤ)) (k : ℤ))

/-- **The level set as a `Finset`.**  The box cut is what makes it finite. -/
noncomputable def levelSet (le : α → α → Prop) [DecidableRel le] (k : ℕ) : Finset (α → ℤ) :=
  (boxFinset α k).filter (fun z => gauge le z = (k : ℤ))

/-- **The box cut loses nothing.**  This is `fiber_box_gen`, and it is what lets the counting
function be a `Finset.card` although the ambient space `ℤ^E` is infinite. -/
theorem mem_levelSet {le : α → α → Prop} [DecidableRel le] (hrefl : ∀ i, le i i)
    (k : ℕ) (z : α → ℤ) : z ∈ levelSet le k ↔ gauge le z = (k : ℤ) := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    rw [boxFinset, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hg : foldMax univ z + ∑ j, (gaugeU le z j - z j) ≤ (k : ℤ) := by
      rw [← gauge_eq]
      exact le_of_eq h
    exact fiber_box_gen z (gaugeU le z) (k : ℤ) (le_gaugeU hrefl z) (gaugeU_nonneg le z) hg i

/-- The counting function `a_k(τ) = #{z ∈ ℤ^E : g_τ(z) = k}`, now a DEFINITION rather than an
abstract sequence. -/
noncomputable def aCount (le : α → α → Prop) [DecidableRel le] (k : ℕ) : ℤ :=
  ((levelSet le k).card : ℤ)

end Gauge

/-! ### The ordinal sum, and `Convolves` discharged

`Convolves` is no longer carried.  What was missing after the gauge became a function was
the ordinal sum itself and the splitting it induces, and both are here.

**The three identities that do the work.**  In `τ₁ ⊕ τ₂` every element of the second factor
lies above every element of the first, so with `c = M(y)`:

* `foldMax_sum` — `M(x,y) = max(M(x), M(y))`;
* `gaugeU_sum_inl` — `U_{inl a}(x,y) = max(U_a(x), M(y))`, because the whole of `y` joins the
  fold over the upper set of `inl a`;
* `gaugeU_sum_inr` — `U_{inr b}(x,y) = U_b(y)`, because nothing in the first factor is above
  `inr b`.

Each is a `Finset` identity between the filtered upper set and a union of two images, closed
by `ext j; cases j <;> simp`.  They rest on `foldMax_union`, which needs no disjointness side
condition: `max` is idempotent, so `Finset.fold_insert_idem` gives the insert case directly.

**`gauge_additive` had to be generalised.**  It is stated for `Fin p`/`Fin q`, and the only
Fin-specific step in its proof is `Fintype.card_fin`; `gauge_additive_gen` is the same
computation with `Fintype.card α`.  The ordinal sum's index is `α ⊕ β`, so the general form is
the one the splitting can consume — and `gauge_additive`'s odd substituted shape is explained
by exactly this: it was written to plug in here.

**The payoff.**  `gauge_ordSum` is `g_{τ₁⊕τ₂}(x,y) = g_{τ₁}(x - M(y)·1) + g_{τ₂}(y)`;
`convolves_aCount` feeds it and the level-set `Finset`s to `convolves_of_finsets`, giving
`Convolves (aCount τ₁) (aCount τ₂) (aCount (τ₁ ⊕ τ₂))` with **no hypothesis beyond reflexivity of
the two preorders**; and `hStar_mul_ordSum` is then the generating-function factorisation,
unconditional.

**What this is NOT.**  The statement proved is about `aCount`, the honest lattice-point count
`#{z ∈ ℤ^E : g_τ(z) = k}`.  That it equals the Ehrhart count of `K_τ` — that `g_τ` is the
gauge of `K_τ` and `kK_τ ∩ ℤ^E = {z : g_τ(z) ≤ k}` — needs the order-polytope vertex theorem
and is UNFORMALISED.  So this row is still not the literal Conjecture 6.3, and is not counted
as fully verified.  The difference from before is that the module now carries **nothing**. -/

section Union

variable {α : Type*} [DecidableEq α]

/-- `max` is idempotent, so the fold needs no disjointness side condition. -/
theorem foldMax_insert_idem (a : α) (s : Finset α) (z : α → ℤ) :
    foldMax (insert a s) z = max (z a) (foldMax s z) :=
  Finset.fold_insert_idem

theorem foldMax_union (s t : Finset α) (z : α → ℤ) :
    foldMax (s ∪ t) z = max (foldMax s z) (foldMax t z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.empty_union, foldMax_empty]
      exact (max_eq_right (foldMax_nonneg t z)).symm
  | insert a s _ ih =>
      rw [Finset.insert_union, foldMax_insert_idem, foldMax_insert_idem, ih, max_assoc]

omit [DecidableEq α] in
theorem foldMax_map {β : Type*} (s : Finset β) (f : β ↪ α) (z : α → ℤ) :
    foldMax (s.map f) z = foldMax s (fun b => z (f b)) :=
  Finset.fold_map

end Union

section OrdinalSum

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **The ordinal sum.**  Each factor keeps its own relation, and every element of the second
lies above every element of the first. -/
def ordSum (r1 : α → α → Prop) (r2 : β → β → Prop) : α ⊕ β → α ⊕ β → Prop
  | Sum.inl a, Sum.inl a' => r1 a a'
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr b, Sum.inr b' => r2 b b'

instance ordSumDecidable (r1 : α → α → Prop) (r2 : β → β → Prop)
    [DecidableRel r1] [DecidableRel r2] : DecidableRel (ordSum r1 r2)
  | Sum.inl a, Sum.inl a' => inferInstanceAs (Decidable (r1 a a'))
  | Sum.inl _, Sum.inr _ => inferInstanceAs (Decidable True)
  | Sum.inr _, Sum.inl _ => inferInstanceAs (Decidable False)
  | Sum.inr b, Sum.inr b' => inferInstanceAs (Decidable (r2 b b'))

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem ordSum_refl {r1 : α → α → Prop} {r2 : β → β → Prop}
    (h1 : ∀ a, r1 a a) (h2 : ∀ b, r2 b b) : ∀ i, ordSum r1 r2 i i
  | Sum.inl a => h1 a
  | Sum.inr b => h2 b

/-- `M` on the sum is the max of the two factor maxima. -/
theorem foldMax_sum (x : α → ℤ) (y : β → ℤ) :
    foldMax (univ : Finset (α ⊕ β)) (Sum.elim x y)
      = max (foldMax univ x) (foldMax univ y) := by
  classical
  have huniv : (univ : Finset (α ⊕ β))
      = (univ.map ⟨Sum.inl, Sum.inl_injective⟩) ∪ (univ.map ⟨Sum.inr, Sum.inr_injective⟩) := by
    ext j; cases j <;> simp
  rw [huniv, foldMax_union, foldMax_map, foldMax_map]
  simp

/-- **The upper-set term on the first factor**: `U_{inl a}(x,y) = max(U_a(x), M(y))`.
Every element of the second factor is above `inl a`, so the whole of `y` joins the fold. -/
theorem gaugeU_sum_inl {r1 : α → α → Prop} {r2 : β → β → Prop}
    [DecidableRel r1] [DecidableRel r2] (x : α → ℤ) (y : β → ℤ) (a : α) :
    gaugeU (ordSum r1 r2) (Sum.elim x y) (Sum.inl a)
      = max (gaugeU r1 x a) (foldMax univ y) := by
  classical
  have hfilter : (univ.filter (fun j : α ⊕ β => ordSum r1 r2 (Sum.inl a) j))
      = ((univ.filter (fun a' => r1 a a')).map ⟨Sum.inl, Sum.inl_injective⟩)
        ∪ (univ.map ⟨Sum.inr, Sum.inr_injective⟩) := by
    ext j
    cases j <;> simp [ordSum]
  rw [gaugeU, hfilter, foldMax_union, foldMax_map, foldMax_map]
  simp [gaugeU]

omit [DecidableEq α] [DecidableEq β] in
/-- **The upper-set term on the second factor**: `U_{inr b}(x,y) = U_b(y)`.  Nothing in the
first factor is above `inr b`. -/
theorem gaugeU_sum_inr {r1 : α → α → Prop} {r2 : β → β → Prop}
    [DecidableRel r1] [DecidableRel r2] (x : α → ℤ) (y : β → ℤ) (b : β) :
    gaugeU (ordSum r1 r2) (Sum.elim x y) (Sum.inr b) = gaugeU r2 y b := by
  classical
  have hfilter : (univ.filter (fun j : α ⊕ β => ordSum r1 r2 (Sum.inr b) j))
      = ((univ.filter (fun b' => r2 b b')).map ⟨Sum.inr, Sum.inr_injective⟩) := by
    ext j
    cases j <;> simp [ordSum]
  rw [gaugeU, hfilter, foldMax_map]
  simp [gaugeU]

/-- `U_a(z - c) = max(U_a(z), c) - c`, the shift identity on the filtered set. -/
theorem gaugeU_shift {r1 : α → α → Prop} [DecidableRel r1] (x : α → ℤ) {c : ℤ} (hc : 0 ≤ c)
    (a : α) : gaugeU r1 (fun i => x i - c) a = max (gaugeU r1 x a) c - c :=
  foldMax_shift _ x hc

omit [DecidableEq β] in
/-- **`gauge_additive` for a general finite index type.**  The original is stated for `Fin p`
and `Fin q`, and the only Fin-specific step in its proof is `Fintype.card_fin`; here the
constant is `Fintype.card α` instead.  The ordinal sum's index is `α ⊕ β`, so the general
form is what the splitting can actually consume. -/
theorem gauge_additive_gen (x : α → ℤ) (y : β → ℤ) (U1 : α → ℤ) (U2 : β → ℤ)
    {c : ℤ} (hc : 0 ≤ c) :
    (max (foldMax univ x) c + ∑ i, max (U1 i) c + ∑ j, U2 j - ∑ i, x i - ∑ j, y j)
      = (foldMax univ (fun i => x i - c) + ∑ i, (max (U1 i) c - c) - ∑ i, (x i - c))
        + (c + ∑ j, U2 j - ∑ j, y j) := by
  have hM : foldMax univ (fun i => x i - c) = max (foldMax univ x) c - c :=
    foldMax_shift univ x hc
  have hU : ∑ i, (max (U1 i) c - c)
      = (∑ i, max (U1 i) c) - (Fintype.card α : ℤ) * c := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
    simp [mul_comm]
  have hx : ∑ i, (x i - c) = (∑ i, x i) - (Fintype.card α : ℤ) * c := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
    simp [mul_comm]
  rw [hM, hU, hx]
  ring

/-- **THE SPLITTING.**  `g_{τ₁⊕τ₂}(x,y) = g_{τ₁}(x - M(y)·1) + g_{τ₂}(y)`. -/
theorem gauge_ordSum {r1 : α → α → Prop} {r2 : β → β → Prop}
    [DecidableRel r1] [DecidableRel r2] (x : α → ℤ) (y : β → ℤ) :
    gauge (ordSum r1 r2) (Sum.elim x y)
      = gauge r1 (fun i => x i - foldMax univ y) + gauge r2 y := by
  classical
  set c : ℤ := foldMax univ y with hcdef
  have hc : 0 ≤ c := foldMax_nonneg univ y
  have hsum : ∀ f : α ⊕ β → ℤ, ∑ i, f i = (∑ a, f (Sum.inl a)) + ∑ b, f (Sum.inr b) := by
    intro f; exact Fintype.sum_sum_type f
  have hU := hsum (fun i => gaugeU (ordSum r1 r2) (Sum.elim x y) i)
  have hz := hsum (fun i => Sum.elim x y i)
  rw [gauge, foldMax_sum, hU, hz]
  simp only [Sum.elim_inl, Sum.elim_inr, gaugeU_sum_inl, gaugeU_sum_inr, ← hcdef]
  have key := gauge_additive_gen x y (gaugeU r1 x) (gaugeU r2 y) hc
  rw [gauge, gauge]
  have e1 : ∀ i, gaugeU r1 (fun i => x i - c) i = max (gaugeU r1 x i) c - c :=
    fun i => gaugeU_shift x hc i
  simp only [e1]
  linarith [key]

/-! ### Discharging `Convolves`

Everything above is about one gauge.  What follows assembles the pieces into the carried
hypothesis itself: the equivalence `Φ`, the gauge as a `ℕ`-valued statistic, and the
`convolves_of_finsets` application. -/

/-- `Φ(x,y) = (x − sh(y)·1, y)` for a general index type.  `shiftEquiv` above is the same
map on `Fin p`/`Fin q`; no hypothesis on `sh` is needed, since the inverse adds back exactly
what the map subtracted. -/
def shiftEquivGen (sh : (β → ℤ) → ℤ) :
    ((α → ℤ) × (β → ℤ)) ≃ ((α → ℤ) × (β → ℤ)) where
  toFun z := (fun i => z.1 i - sh z.2, z.2)
  invFun w := (fun i => w.1 i + sh w.2, w.2)
  left_inv z := by ext <;> simp
  right_inv w := by ext <;> simp

/-- **The equivalence the convolution runs along**: split the sum-type argument into its two
components, then shift the first by `M` of the second. -/
def splitEquiv : ((α ⊕ β) → ℤ) ≃ ((α → ℤ) × (β → ℤ)) :=
  (Equiv.sumArrowEquivProdArrow α β ℤ).trans (shiftEquivGen (fun w => foldMax univ w))

/-- The gauge as the `ℕ`-valued statistic `convolves_of_finsets` expects.  `gauge_nonneg` is
what makes this lossless. -/
noncomputable def gaugeN (le : α → α → Prop) [DecidableRel le] (z : α → ℤ) : ℕ :=
  (gauge le z).toNat

theorem gaugeN_eq_iff {le : α → α → Prop} [DecidableRel le] (hrefl : ∀ i, le i i)
    (z : α → ℤ) (k : ℕ) : gaugeN le z = k ↔ gauge le z = (k : ℤ) := by
  have h := gauge_nonneg hrefl z
  rw [gaugeN]
  omega

theorem mem_levelSet_gaugeN {le : α → α → Prop} [DecidableRel le] (hrefl : ∀ i, le i i)
    (k : ℕ) (z : α → ℤ) : z ∈ levelSet le k ↔ gaugeN le z = k := by
  rw [mem_levelSet hrefl, gaugeN_eq_iff hrefl]

/-- The splitting, restated along `splitEquiv`. -/
theorem gauge_ordSum_split {r1 : α → α → Prop} {r2 : β → β → Prop}
    [DecidableRel r1] [DecidableRel r2] (w : α ⊕ β → ℤ) :
    gauge (ordSum r1 r2) w
      = gauge r1 (splitEquiv w).1 + gauge r2 (splitEquiv w).2 := by
  have hw : Sum.elim (fun a => w (Sum.inl a)) (fun b => w (Sum.inr b)) = w := by
    funext j; cases j <;> rfl
  have h := gauge_ordSum (r1 := r1) (r2 := r2)
    (fun a => w (Sum.inl a)) (fun b => w (Sum.inr b))
  rw [hw] at h
  rw [h]
  rfl

/-- The same, for the `ℕ`-valued statistic — the `hsplit` hypothesis of
`convolves_of_finsets`. -/
theorem gaugeN_ordSum_split {r1 : α → α → Prop} {r2 : β → β → Prop}
    [DecidableRel r1] [DecidableRel r2] (hrefl1 : ∀ a, r1 a a) (hrefl2 : ∀ b, r2 b b)
    (w : α ⊕ β → ℤ) :
    gaugeN (ordSum r1 r2) w
      = gaugeN r1 (splitEquiv w).1 + gaugeN r2 (splitEquiv w).2 := by
  have h := gauge_ordSum_split (r1 := r1) (r2 := r2) w
  have h1 : 0 ≤ gauge r1 (splitEquiv w).1 := gauge_nonneg hrefl1 _
  have h2 : 0 ≤ gauge r2 (splitEquiv w).2 := gauge_nonneg hrefl2 _
  simp only [gaugeN]
  omega

/-- **`Convolves`, DISCHARGED for the actual counting functions.**  This is what the module
carried as a hypothesis: `a_k(τ₁ ⊕ τ₂) = ∑_{j+l=k} a_j(τ₁)·a_l(τ₂)`, with `a` the honest
lattice-point count `#{z ∈ ℤ^E : g_τ(z) = k}`. -/
theorem convolves_aCount {r1 : α → α → Prop} {r2 : β → β → Prop}
    [DecidableRel r1] [DecidableRel r2] (hrefl1 : ∀ a, r1 a a) (hrefl2 : ∀ b, r2 b b) :
    Convolves (aCount r1) (aCount r2) (aCount (ordSum r1 r2)) :=
  convolves_of_finsets (gaugeN (ordSum r1 r2)) (gaugeN r1) (gaugeN r2) splitEquiv
    (gaugeN_ordSum_split hrefl1 hrefl2)
    (levelSet (ordSum r1 r2)) (levelSet r1) (levelSet r2)
    (fun k w => mem_levelSet_gaugeN (ordSum_refl hrefl1 hrefl2) k w)
    (fun j x => mem_levelSet_gaugeN hrefl1 j x)
    (fun l y => mem_levelSet_gaugeN hrefl2 l y)

/-- **The factorisation, now UNCONDITIONAL on the counting functions.**  With
`h* = (1−X)^n·Θ`, the `(1−X)` factors split exactly across the ordinal sum. -/
theorem hStar_mul_ordSum {r1 : α → α → Prop} {r2 : β → β → Prop}
    [DecidableRel r1] [DecidableRel r2] (hrefl1 : ∀ a, r1 a a) (hrefl2 : ∀ b, r2 b b)
    (n₁ n₂ : ℕ) :
    ((1 - PowerSeries.X) ^ (n₁ + n₂)
        * PowerSeries.mk (aCount (ordSum r1 r2)) : PowerSeries ℤ)
      = ((1 - PowerSeries.X) ^ n₁ * PowerSeries.mk (aCount r1))
        * ((1 - PowerSeries.X) ^ n₂ * PowerSeries.mk (aCount r2)) :=
  hStar_mul (convolves_aCount hrefl1 hrefl2) n₁ n₂

end OrdinalSum

/-! ### The interface layer, first piece

**The residue of this row is convex geometry, and it is not blocked.**  A summary written
elsewhere on 2026-09-24 called it *"Ehrhart theory, an object Mathlib lacks"*; the header
above already said otherwise and is right — `h*` enters only as a DEFINITION, and Ehrhart's
theorem is never invoked.  What is actually missing is three elementary facts, all proved in
the write-up and all expressible with Mathlib's `convexHull` and `gauge`:

1. the order-polytope vertex description, `O_τ = conv{1_I : I an ideal}`;
2. `K_τ = conv(O_τ ∪ (-Δ_E))`;
3. the gauge lemma, `gauge K_τ = g_τ`.

This section is the first piece of (1).  `indicator_mem_orderPolytope` is its easy half.
`superlevel_isIdeal` is the write-up's sentence *"for any `u ∈ O_τ` each nonempty superlevel
set `{i : u_i ≥ a}` is an ideal"* — one line, and the engine of the hard half, since the
layer-cake decomposition writes `u` as a positive combination of the indicators of its own
superlevel sets.

**These five declarations are NOT yet consumed.**  Their consumer is that decomposition,
which is the next step; said plainly because a count that rises without a consumer is what
this campaign treats as not-progress. -/

section OrderPolytope

variable {E : Type*}

/-- An **order ideal** of `le`: closed downwards, `le i j → j ∈ I → i ∈ I`. -/
def IsIdeal (le : E → E → Prop) (I : Finset E) : Prop :=
  ∀ i j, le i j → j ∈ I → i ∈ I

/-- The **order polytope** in the write-up's decreasing convention:
`O_τ = {u ∈ [0,1]^E : u_i ≥ u_j whenever i ≤_τ j}`. -/
def orderPolytope (le : E → E → Prop) : Set (E → ℝ) :=
  {u | (∀ i, 0 ≤ u i ∧ u i ≤ 1) ∧ ∀ i j, le i j → u j ≤ u i}

/-- **Each ideal's indicator is a point of the order polytope.**  The easy half of the
vertex description, and the only place `IsIdeal` is used directly. -/
theorem indicator_mem_orderPolytope [DecidableEq E] {le : E → E → Prop} {I : Finset E}
    (h : IsIdeal le I) :
    (fun i => if i ∈ I then (1 : ℝ) else 0) ∈ orderPolytope le := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · by_cases hi : i ∈ I <;> simp [hi]
  · by_cases hj : j ∈ I
    · simp [hj, h i j hij hj]
    · by_cases hi : i ∈ I <;> simp [hi, hj]

/-- **Every superlevel set of a point of the order polytope is an ideal.**  This is the
write-up's sentence *"for any `u ∈ O_τ` each nonempty superlevel set `{i : u_i ≥ a}` is an
ideal"*, and it is one line: `le i j` gives `u j ≤ u i`, so `a ≤ u j` forces `a ≤ u i`. -/
theorem superlevel_isIdeal [Fintype E] {le : E → E → Prop} {u : E → ℝ}
    (hu : u ∈ orderPolytope le) (a : ℝ) :
    IsIdeal le (Finset.univ.filter (fun i => a ≤ u i)) := by
  intro i j hij hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨Finset.mem_univ i, le_trans hj.2 (hu.2 i j hij)⟩

/-- The order polytope is convex — needed before any hull statement about it means
anything. -/
theorem convex_orderPolytope (le : E → E → Prop) : Convex ℝ (orderPolytope le) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · have hx0 := (hx.1 i).1
    have hy0 := (hy.1 i).1
    have hx1 := (hx.1 i).2
    have hy1 := (hy.1 i).2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · positivity
    · nlinarith
  · have hxij := hx.2 i j hij
    have hyij := hy.2 i j hij
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith

end OrderPolytope

/-! ### The interface layer, second piece: the order-polytope vertex description

`orderPolytope_eq_convexHull` is **fact (1) of the three** the statement of Conjecture 6.3
needs — the write-up's sentence *"It equals the convex hull of the indicators of all order
ideals, including the empty ideal."*  The reverse inclusion is one line (`convexHull_min` on a
convex set containing every vertex); the forward one is the **layer-cake decomposition**, and it
is the only real work in the vertex description.

`layer_cake_aux` proves it by peeling one level at a time.  With `M = topLevel u` the largest
value of `u` (or `0`) and `M'` the largest level strictly below it,

    u = min(u, M')  +  (M − M') · 1_{u ≥ M},

where the second summand's index set is an ideal by `superlevel_isIdeal` and the first summand is
again a point of the polytope (`min_const_mem_orderPolytope`) with **strictly fewer levels** —
`M` is gone and nothing new appears.  That strict decrease is the induction's measure.  The
coefficients sum to `topLevel u`, not to `1`; the slack `1 − topLevel u` is carried by the empty
ideal, whose indicator is the zero vector, which is why `IsIdeal` is stated for a `Finset` with no
nonemptiness condition.

`insert 0` in `levels` is load-bearing: without it a `u` with a single positive value has one
level before peeling and one after, and the induction does not terminate.

**WHAT THIS CONSUMES AND WHAT REMAINS.**  It consumes the five declarations landed earlier today,
which were banked explicitly unconsumed: `IsIdeal`, `orderPolytope`, `convex_orderPolytope`,
`indicator_mem_orderPolytope` (the easy half) and `superlevel_isIdeal` (the engine).  **Two of
the three facts are still unformalised**: `K_τ = conv(O_τ ∪ (−Δ_E))`, and the gauge lemma
`g_τ = gauge K_τ` with its corollary `kK_τ ∩ ℤ^E = {z : g_τ(z) ≤ k}`.  Until those land the
row proves a theorem about `aCount`, not about Ehrhart counts of `K_τ`. -/

section LayerCake

variable {E : Type*} [Fintype E]

/-- The thresholds of `u`: its values together with `0`.  Using `insert 0` is what makes the
peeling induction terminate — a `u` with a single positive value has two levels and one
level after peeling, where the raw value set would have one and one. -/
noncomputable def levels (u : E → ℝ) : Finset ℝ :=
  insert 0 (Finset.image u Finset.univ)

theorem levels_nonempty (u : E → ℝ) : (levels u).Nonempty :=
  ⟨0, Finset.mem_insert_self _ _⟩

theorem mem_levels_of_val (u : E → ℝ) (i : E) : u i ∈ levels u :=
  Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))

theorem zero_mem_levels (u : E → ℝ) : (0 : ℝ) ∈ levels u :=
  Finset.mem_insert_self _ _

/-- The largest threshold. -/
noncomputable def topLevel (u : E → ℝ) : ℝ := (levels u).max' (levels_nonempty u)

theorem le_topLevel (u : E → ℝ) (i : E) : u i ≤ topLevel u :=
  Finset.le_max' _ _ (mem_levels_of_val u i)

theorem topLevel_nonneg (u : E → ℝ) : 0 ≤ topLevel u :=
  Finset.le_max' _ _ (zero_mem_levels u)

theorem topLevel_mem (u : E → ℝ) : topLevel u ∈ levels u :=
  Finset.max'_mem _ _

theorem topLevel_le {u : E → ℝ} {b : ℝ} (h0 : 0 ≤ b) (h : ∀ i, u i ≤ b) : topLevel u ≤ b :=
  Finset.max'_le _ _ _ (by
    intro y hy
    rw [levels, Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact h0
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact h i)

/-- A positive top level is attained.  (The `insert 0` is why this needs the hypothesis.) -/
theorem exists_eq_topLevel (u : E → ℝ) (h : 0 < topLevel u) : ∃ i, u i = topLevel u := by
  have h1 := topLevel_mem u
  rw [levels, Finset.mem_insert] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (ne_of_gt h)
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h1
    exact ⟨i, hi⟩

theorem topLevel_le_one {le : E → E → Prop} {u : E → ℝ} (hu : u ∈ orderPolytope le) :
    topLevel u ≤ 1 :=
  topLevel_le zero_le_one (fun i => (hu.1 i).2)

omit [Fintype E] in
/-- `min` with a nonnegative constant keeps a point inside the order polytope. -/
theorem min_const_mem_orderPolytope {le : E → E → Prop} {u : E → ℝ}
    (hu : u ∈ orderPolytope le) {c : ℝ} (hc : 0 ≤ c) :
    (fun i => min (u i) c) ∈ orderPolytope le := by
  refine ⟨fun i => ⟨le_min (hu.1 i).1 hc, ?_⟩, fun i j hij => ?_⟩
  · exact le_trans (min_le_left _ _) (hu.1 i).2
  · exact min_le_min (hu.2 i j hij) le_rfl

/-- **The second threshold**: the largest level strictly below the top.  It exists because `0`
is always a level, and it is what the peeling step cuts down to. -/
theorem exists_second_level (u : E → ℝ) (h : 0 < topLevel u) :
    ∃ M : ℝ, M ∈ levels u ∧ 0 ≤ M ∧ M < topLevel u ∧
      ∀ x ∈ levels u, x < topLevel u → x ≤ M := by
  have h0 : (0 : ℝ) ∈ (levels u).filter (fun x => x < topLevel u) :=
    Finset.mem_filter.mpr ⟨zero_mem_levels u, h⟩
  have hne : ((levels u).filter (fun x => x < topLevel u)).Nonempty := ⟨0, h0⟩
  have hmem := Finset.mem_filter.mp (Finset.max'_mem _ hne)
  exact ⟨_, hmem.1, Finset.le_max' _ _ h0, hmem.2,
    fun x hx hlt => Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hx, hlt⟩)⟩

variable [DecidableEq E]

/-- **The layer-cake decomposition**, in the form the induction proves: every point of the order
polytope is a nonnegative combination of indicators of ideals, the coefficients summing to its
own top level.

The write-up states it as *"writing `u` as the sum of its successive level differences times
these indicators"*.  The induction peels one layer at a time: with `M` the top level and `M'` the
next one down, `u = min(u, M') + (M - M') · 1_{u ≥ M}`, the first summand is again in the
polytope and has strictly fewer levels, and the second is `superlevel_isIdeal`. -/
theorem layer_cake_aux {le : E → E → Prop} :
    ∀ (n : ℕ) (u : E → ℝ), u ∈ orderPolytope le → (levels u).card ≤ n →
      ∃ (m : ℕ) (c : Fin m → ℝ) (S : Fin m → Finset E),
        (∀ t, 0 ≤ c t) ∧ (∀ t, IsIdeal le (S t)) ∧
        (∀ i, ∑ t, c t * (if i ∈ S t then (1 : ℝ) else 0) = u i) ∧
        ∑ t, c t = topLevel u := by
  intro n
  induction n with
  | zero =>
      intro u _ hcard
      have := Finset.card_pos.mpr (levels_nonempty u)
      omega
  | succ n ih =>
      intro u hu hcard
      rcases eq_or_lt_of_le (topLevel_nonneg u) with hM | hM
      · -- `u = 0`: the empty combination already sums to `0 = topLevel u`.
        refine ⟨0, Fin.elim0, Fin.elim0, fun t => t.elim0, fun t => t.elim0, fun i => ?_, ?_⟩
        · have h1 := (hu.1 i).1
          have h2 := le_topLevel u i
          simp only [Finset.univ_eq_empty, Finset.sum_empty]
          linarith
        · simpa using hM
      · obtain ⟨M', hM'lev, hM'0, hM'lt, hM'max⟩ := exists_second_level u hM
        have hu' : (fun i => min (u i) M') ∈ orderPolytope le :=
          min_const_mem_orderPolytope hu hM'0
        -- the peeled point has top level exactly `M'`
        have htop' : topLevel (fun i => min (u i) M') = M' := by
          refine le_antisymm (topLevel_le hM'0 (fun i => min_le_right _ _)) ?_
          obtain ⟨i, hi⟩ := exists_eq_topLevel u hM
          have hval : min (u i) M' = M' := by rw [hi]; exact min_eq_right (le_of_lt hM'lt)
          have hle : min (u i) M' ≤ topLevel (fun i => min (u i) M') :=
            le_topLevel (fun i => min (u i) M') i
          exact le_trans (le_of_eq hval.symm) hle
        -- and strictly fewer levels: the top one is gone
        have hsub : levels (fun i => min (u i) M') ⊆ (levels u).erase (topLevel u) := by
          intro y hy
          rw [levels, Finset.mem_insert] at hy
          rcases hy with rfl | hy
          · exact Finset.mem_erase.mpr ⟨ne_of_lt hM, zero_mem_levels u⟩
          · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
            rcases le_total (u i) M' with h | h
            · rw [min_eq_left h]
              exact Finset.mem_erase.mpr
                ⟨ne_of_lt (lt_of_le_of_lt h hM'lt), mem_levels_of_val u i⟩
            · rw [min_eq_right h]
              exact Finset.mem_erase.mpr ⟨ne_of_lt hM'lt, hM'lev⟩
        have hcard' : (levels (fun i => min (u i) M')).card ≤ n := by
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_erase_of_mem (topLevel_mem u)
          have h3 : 0 < (levels u).card := Finset.card_pos.mpr (levels_nonempty u)
          omega
        obtain ⟨m, c, S, hc0, hcI, hcsum, hctot⟩ := ih _ hu' hcard'
        refine ⟨m + 1, Fin.cons (topLevel u - M') c,
          Fin.cons (Finset.univ.filter (fun i => topLevel u ≤ u i)) S, ?_, ?_, ?_, ?_⟩
        · intro t
          refine Fin.cases ?_ ?_ t
          · simp only [Fin.cons_zero]; linarith
          · intro s; simpa only [Fin.cons_succ] using hc0 s
        · intro t
          refine Fin.cases ?_ ?_ t
          · simpa only [Fin.cons_zero] using superlevel_isIdeal hu (topLevel u)
          · intro s; simpa only [Fin.cons_succ] using hcI s
        · intro i
          have hs : ∑ t : Fin m, c t * (if i ∈ S t then (1 : ℝ) else 0) = min (u i) M' := hcsum i
          rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, hs]
          by_cases hi : topLevel u ≤ u i
          · have hmem : i ∈ Finset.univ.filter (fun i => topLevel u ≤ u i) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
            have h1 : u i = topLevel u := le_antisymm (le_topLevel u i) hi
            have h2 : min (u i) M' = M' := by rw [h1]; exact min_eq_right (le_of_lt hM'lt)
            rw [if_pos hmem, h2, h1]; ring
          · have hmem : i ∉ Finset.univ.filter (fun i => topLevel u ≤ u i) := by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi
            have h2 : min (u i) M' = u i :=
              min_eq_left (hM'max _ (mem_levels_of_val u i) (not_le.mp hi))
            rw [if_neg hmem, h2]; ring
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, hctot, htop']
          ring

/-- The vertex set of the order polytope: the indicators of the ideals of `le`. -/
def idealVertices (le : E → E → Prop) : Set (E → ℝ) :=
  {v | ∃ I : Finset E, IsIdeal le I ∧ v = fun i => if i ∈ I then (1 : ℝ) else 0}

omit [Fintype E] [DecidableEq E] in
theorem empty_isIdeal (le : E → E → Prop) : IsIdeal le (∅ : Finset E) := by
  intro i j _ hj
  exact absurd hj (Finset.notMem_empty j)

/-- **The hard half of the vertex description**: `O_τ ⊆ conv{1_I : I an ideal}`.

The layer-cake coefficients sum to `topLevel u ≤ 1`; the slack `1 - topLevel u` is carried by the
empty ideal, whose indicator is the zero vector. -/
theorem orderPolytope_subset_convexHull (le : E → E → Prop) :
    orderPolytope le ⊆ convexHull ℝ (idealVertices le) := by
  intro u hu
  obtain ⟨m, c, S, hc0, hcI, hcsum, hctot⟩ := layer_cake_aux (levels u).card u hu le_rfl
  refine mem_convexHull_of_exists_fintype
    (Fin.cons (1 - topLevel u) c)
    (fun t => fun i =>
      if i ∈ Fin.cons (α := fun _ => Finset E) (∅ : Finset E) S t then (1 : ℝ) else 0)
    ?_ ?_ ?_ ?_
  · intro t
    refine Fin.cases ?_ ?_ t
    · simp only [Fin.cons_zero]
      have := topLevel_le_one hu
      linarith
    · intro s; simpa only [Fin.cons_succ] using hc0 s
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, hctot]
    ring
  · intro t
    refine Fin.cases ?_ ?_ t
    · exact ⟨∅, empty_isIdeal le, by simp only [Fin.cons_zero]⟩
    · intro s; exact ⟨S s, hcI s, by simp only [Fin.cons_succ]⟩
  · funext i
    rw [Finset.sum_apply, Fin.sum_univ_succ]
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero, Fin.cons_succ,
      Finset.notMem_empty, if_false]
    rw [hcsum i]
    ring

omit [Fintype E] in
/-- The reverse inclusion, which the write-up calls *"immediate"*: the polytope is convex and
contains every ideal indicator, so it contains their hull. -/
theorem convexHull_subset_orderPolytope (le : E → E → Prop) :
    convexHull ℝ (idealVertices le) ⊆ orderPolytope le := by
  refine convexHull_min ?_ (convex_orderPolytope le)
  rintro v ⟨I, hI, rfl⟩
  exact indicator_mem_orderPolytope hI

/-- **The order-polytope vertex description**, the write-up's sentence *"It equals the convex
hull of the indicators of all order ideals, including the empty ideal."*  This is fact (1) of
the three the statement of Conjecture 6.3 needs. -/
theorem orderPolytope_eq_convexHull (le : E → E → Prop) :
    orderPolytope le = convexHull ℝ (idealVertices le) :=
  Set.Subset.antisymm (orderPolytope_subset_convexHull le) (convexHull_subset_orderPolytope le)

end LayerCake

/-! ### The interface layer, third piece: `K_τ = conv(O_τ ∪ (−Δ_E))`

This is **fact (2) of the three**.  `polarVertices` is the source's own vertex list — the `−e_i`
together with the indicators of the NONEMPTY ideals — and `polarPolytope` is its hull, so
`polarPolytope` is `K_τ` by definition rather than by an identification anyone has to trust.

The proof is a hull identity plus one convex combination.  `O_τ` contributes the indicators of
ALL ideals (fact (1)); `−Δ_E` contributes the `−e_i` together with `0`.  The two vertex lists
therefore differ in exactly one point, `1_∅ = 0`, and `zero_mem_polarPolytope` shows `K_τ`
contains it anyway — the write-up's *"the origin is a convex combination with strictly positive
coefficients of the affinely independent vertices `−e_i` and `1_E`"*, with `1/(|E|+1)` on each
of the `|E|+1` vertices.  Only the MEMBERSHIP is used; the interiority, which the source needs
for full-dimensionality, is not needed for the hull identity and is not proved.
`[Nonempty E]` is required and is not a technicality: over an empty `E` the vertex list is empty
and `K_τ = ∅`, while `O_τ` is the one-point space.

**THE PLAN FOR FACT (3), AND WHY IT DOES NOT NEED MATHLIB'S `gauge`.**  The consumer is
`kK_τ ∩ ℤ^E = {z : g_τ(z) ≤ k}`, which is a MEMBERSHIP characterisation, not a statement about
an infimum.  Stating it as `z ∈ k • K_τ ↔ g_τ(z) ≤ k` avoids `Mathlib.Analysis.Convex.Gauge`
entirely, and with it the `Absorbent` side condition, which would demand that `0` is an INTERIOR
point — a topological fact the source proves and this route never needs.  Both directions are
then elementary:

* `←` is the explicit combination.  With `u = U(z)` and `v = u − z ≥ 0`, `z = u − v`, `u/M(u)`
  lies in `O_τ` and `−v/∑v` in `−Δ_E`, both inside `K_τ` by fact (2), and the coefficients
  `M(z)` and `∑U − ∑z` sum to exactly `g_τ(z) ≤ k`.
* `→` needs **no decomposition at all**: `k • K_τ = conv(k • V)` by `convexHull_smul`, the
  sublevel set `{z : g_τ(z) ≤ k}` is convex because `M` and each `U_i` are maxima of linear
  functions and `−∑z` is linear, and each scaled vertex lies in it: `g_τ(−e_i) = 1` and
  `g_τ(1_I) = 1 + |I| − |I| = 1` for an ideal `I`, the middle step being
  `U_i(1_I) = 1_I(i)`, which is exactly the ideal property (plus reflexivity for the converse).

That replaces the write-up's optimisation argument — *"minimize `max u + ∑(uᵢ − zᵢ)` among
nonnegative decreasing `u ≥ z`"* — with a convexity argument in one direction and a single
explicit witness in the other. -/

section PolarPolytope

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Adding a point the hull already contains does not change the hull.  Campaign-agnostic; a
`Common/` candidate once a second consumer appears. -/
theorem convexHull_insert_of_mem {F : Type*} [AddCommGroup F] [Module ℝ F] {s : Set F} {x : F}
    (h : x ∈ convexHull ℝ s) : convexHull ℝ (insert x s) = convexHull ℝ s :=
  Set.Subset.antisymm
    (convexHull_min (Set.insert_subset h (subset_convexHull ℝ s)) (convex_convexHull ℝ s))
    (convexHull_mono (Set.subset_insert _ _))

/-- `-e_i`, the negated standard basis vector. -/
def negUnit (i : E) : E → ℝ := fun j => if j = i then (-1 : ℝ) else 0

/-- The indicators of the NONEMPTY ideals — the second half of the source's vertex list. -/
def properIdealVertices (le : E → E → Prop) : Set (E → ℝ) :=
  {v | ∃ I : Finset E, I.Nonempty ∧ IsIdeal le I ∧ v = fun j => if j ∈ I then (1 : ℝ) else 0}

/-- The vertex set of `K_τ` exactly as Athanasiadis–Chapoton write it:
`{-e_i : i ∈ E} ∪ {1_I : ∅ ≠ I an order ideal}`. -/
def polarVertices (le : E → E → Prop) : Set (E → ℝ) :=
  {v | ∃ i : E, v = negUnit i} ∪ properIdealVertices le

/-- `K_τ`, the polar preorder polytope. -/
noncomputable def polarPolytope (le : E → E → Prop) : Set (E → ℝ) :=
  convexHull ℝ (polarVertices le)

/-- `-Δ_E = conv({0} ∪ {-e_i : i ∈ E})`. -/
noncomputable def negSimplex (E : Type*) [Fintype E] [DecidableEq E] : Set (E → ℝ) :=
  convexHull ℝ (insert (0 : E → ℝ) {v : E → ℝ | ∃ i : E, v = negUnit i})

omit [DecidableEq E] in
theorem univ_isIdeal (le : E → E → Prop) : IsIdeal le (Finset.univ : Finset E) :=
  fun i _ _ _ => Finset.mem_univ i

omit [Fintype E] in
/-- The ideal indicators are the nonempty ones together with the origin: `1_∅ = 0`. -/
theorem idealVertices_eq_insert (le : E → E → Prop) :
    idealVertices le = insert (0 : E → ℝ) (properIdealVertices le) := by
  ext v
  constructor
  · rintro ⟨I, hI, rfl⟩
    rcases I.eq_empty_or_nonempty with rfl | hne
    · left; funext j; simp
    · exact Or.inr ⟨I, hne, hI, rfl⟩
  · rintro (rfl | ⟨I, -, hI, rfl⟩)
    · exact ⟨∅, empty_isIdeal le, by funext j; simp⟩
    · exact ⟨I, hI, rfl⟩

/-- **The origin lies in `K_τ`** — the write-up's *"it is a convex combination with strictly
positive coefficients of the affinely independent vertices `-e_i` and `1_E`"*.  Only the
membership is used here; the interiority, which the source uses for full-dimensionality, is not
needed for the hull identity. -/
theorem zero_mem_polarPolytope [Nonempty E] (le : E → E → Prop) :
    (0 : E → ℝ) ∈ polarPolytope le := by
  have hpos : (0 : ℝ) < (Fintype.card E : ℝ) + 1 := by positivity
  have hne : ((Fintype.card E : ℝ) + 1) ≠ 0 := ne_of_gt hpos
  refine mem_convexHull_of_exists_fintype
    (fun _ : Option E => (1 : ℝ) / ((Fintype.card E : ℝ) + 1))
    (fun t => t.elim (fun j => if j ∈ (Finset.univ : Finset E) then (1 : ℝ) else 0) negUnit)
    (fun _ => by positivity) ?_ ?_ ?_
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_option, nsmul_eq_mul]
    push_cast
    field_simp
  · intro t
    cases t with
    | none => exact Or.inr ⟨Finset.univ, Finset.univ_nonempty, univ_isIdeal le, rfl⟩
    | some i => exact Or.inl ⟨i, rfl⟩
  · funext j
    rw [Finset.sum_apply, Fintype.sum_option]
    show ((1 : ℝ) / ((Fintype.card E : ℝ) + 1)) •
          (if j ∈ (Finset.univ : Finset E) then (1 : ℝ) else 0)
        + ∑ i : E, ((1 : ℝ) / ((Fintype.card E : ℝ) + 1)) • negUnit i j = (0 : ℝ)
    have hsum : ∑ i : E, ((1 : ℝ) / ((Fintype.card E : ℝ) + 1)) • negUnit i j
        = -((1 : ℝ) / ((Fintype.card E : ℝ) + 1)) := by
      simp only [negUnit, smul_eq_mul, ← Finset.mul_sum]
      simp
    rw [hsum]
    simp

/-- **Fact (2) of the three**: `K_τ = conv(O_τ ∪ (-Δ_E))`.

Both sides are the convex hull of the same vertex list up to the origin: `O_τ` contributes the
indicators of ALL ideals, `-Δ_E` the `-e_i` together with `0`, and `K_τ` lists the `-e_i` with
the indicators of the NONEMPTY ideals.  The one vertex that differs is `1_∅ = 0`, which `K_τ`
contains anyway by `zero_mem_polarPolytope`. -/
theorem polarPolytope_eq_convexHull_union [Nonempty E] (le : E → E → Prop) :
    polarPolytope le = convexHull ℝ (orderPolytope le ∪ negSimplex E) := by
  have hset : idealVertices le ∪ insert (0 : E → ℝ) {v : E → ℝ | ∃ i : E, v = negUnit i}
      = insert (0 : E → ℝ) (polarVertices le) := by
    rw [idealVertices_eq_insert]
    ext v
    simp only [Set.mem_union, Set.mem_insert_iff, polarVertices]
    tauto
  calc polarPolytope le
      = convexHull ℝ (polarVertices le) := rfl
    _ = convexHull ℝ (insert (0 : E → ℝ) (polarVertices le)) :=
        (convexHull_insert_of_mem (zero_mem_polarPolytope le)).symm
    _ = convexHull ℝ
          (idealVertices le ∪ insert (0 : E → ℝ) {v : E → ℝ | ∃ i : E, v = negUnit i}) := by
        rw [hset]
    _ = convexHull ℝ (orderPolytope le ∪ negSimplex E) := by
        rw [orderPolytope_eq_convexHull,
          show negSimplex E
              = convexHull ℝ (insert (0 : E → ℝ) {v : E → ℝ | ∃ i : E, v = negUnit i}) from rfl,
          convexHull_convexHull_union_left, convexHull_convexHull_union_right]

end PolarPolytope

/-! ### The interface layer, fourth piece: the gauge lemma

This is **fact (3)**, the last of the three, and with it the interface is complete:
`mem_smul_polarPolytope_intCast_iff` is the write-up's sentence
`kK_τ ∩ ℤ^E = {z : g_τ(z) ≤ k}`.

**It is stated as a MEMBERSHIP, and that is a decision rather than a convenience.**  The
consumer never needs an infimum, so phrasing it as `z ∈ k • K_τ ↔ g_τ(z) ≤ k` avoids
`Mathlib.Analysis.Convex.Gauge` and with it the `Absorbent` side condition, which would require
`0` to be an INTERIOR point of `K_τ` — exactly the topological fact the previous section
deliberately did not prove.  The two decisions are the same decision.

**The forward inclusion needs no decomposition and no hypothesis on `le`.**  `kK_τ` is the hull
of the scaled vertices (`convexHull_smul`); `{z : g_τ(z) ≤ k}` is convex because `M` and every
`U_i` are maxima of linear functions and `−∑z` is linear; and each vertex has gauge `1`:
`g_τ(−e_i) = 0 + 0 + 1` and `g_τ(1_I) ≤ 1 + |I| − |I|`, the middle step being
`U_i(1_I) ≤ 1_I(i)`, which **is** the ideal property — if something above `i` lies in `I` then
`i` does.  Reflexivity is not needed for it, because only the inequality is used.

**The reverse inclusion is the write-up's own witness.**  `u = U(z)` is the coordinatewise least
nonnegative `τ`-decreasing vector dominating `z`; `v = u − z ≥ 0`; `z = u − v` splits the mass
as `M(z)` on `O_τ` and `∑v` on `−Δ_E`, which sum to exactly `g_τ(z)`.  Reflexivity enters
once (`le_gaugeUR`, `z_i ≤ U_i(z)`) and transitivity once (`gaugeUR_anti`, `U` is decreasing);
each is isolated in a single lemma, so the hypotheses are visible rather than ambient.  The
write-up's optimisation argument — *"minimize `max u + ∑(uᵢ − zᵢ)` among nonnegative decreasing
`u ≥ z`"* — is thereby replaced by convexity in one direction and one explicit witness in the
other.

`add_smul_mem_of_add_le_one` and `add_mem_smul_of_add_le` are the general facts doing the
bookkeeping: a convex set containing the origin is closed under weights summing to at most `1`,
so the slack rides on the origin.  Both are campaign-agnostic `Common/` candidates.

`foldMaxR` duplicates `foldMax` over `ℝ` rather than generalising it.  That is deliberate:
`foldMax` is consumed by `fiber_box_gen` and the whole lattice-count argument, and generalising
its type would touch every one of those proofs for no gain, while the bridge costs four
declarations (`foldMaxR_intCast` and its three consequences) and is a single `Finset` induction.

**AND THE ROW CLOSES HERE.**  What was left after fact (3) was bookkeeping, and it is done in
the same pass.  `ballSet` is `kK_τ ∩ ℤ^E` (`mem_ballSet_iff_dilate`); its cardinality is the
partial sum of the level counts (`ballCount_eq_sum`), so
`Θ_τ = (1−X)·∑_k #(kK_τ ∩ ℤ^E)X^k` and exactly one `(1−X)` cancels — which is why the
write-up's `h*` carries the exponent `n+1` while the factorisation carries `n`.  `hStarK` is
then the write-up's `h*` VERBATIM, built from the DILATION counts rather than from `aCount`,
and `conjecture_6_3` is Athanasiadis–Chapoton's Conjecture 6.3 with reflexivity of the two
preorders as its only hypothesis. -/

open scoped Pointwise

section GaugeReal

/-! The real counterpart of `foldMax`.  The `ℤ`-valued fold is what the lattice count uses; the
convex geometry lives in `ℝ`, and the two are bridged by `Int.cast` later. -/

variable {α : Type*}

/-- `M(z) = max({0} ∪ {z_i : i ∈ s})`, over `ℝ`. -/
def foldMaxR (s : Finset α) (z : α → ℝ) : ℝ := s.fold max 0 z

theorem foldMaxR_empty (z : α → ℝ) : foldMaxR (∅ : Finset α) z = 0 :=
  Finset.fold_empty

theorem foldMaxR_insert [DecidableEq α] {a : α} {s : Finset α} (h : a ∉ s) (z : α → ℝ) :
    foldMaxR (insert a s) z = max (z a) (foldMaxR s z) :=
  Finset.fold_insert h

theorem foldMaxR_nonneg [DecidableEq α] (s : Finset α) (z : α → ℝ) : 0 ≤ foldMaxR s z := by
  induction s using Finset.induction_on with
  | empty => simp [foldMaxR_empty]
  | insert a s ha ih => rw [foldMaxR_insert ha]; exact le_max_of_le_right ih

theorem le_foldMaxR [DecidableEq α] {s : Finset α} {z : α → ℝ} {i : α} (hi : i ∈ s) :
    z i ≤ foldMaxR s z := by
  induction s using Finset.induction_on with
  | empty => simp at hi
  | insert a s ha ih =>
      rw [foldMaxR_insert ha]
      rcases Finset.mem_insert.mp hi with rfl | h
      · exact le_max_left _ _
      · exact le_max_of_le_right (ih h)

theorem foldMaxR_le [DecidableEq α] {s : Finset α} {z : α → ℝ} {b : ℝ} (h0 : 0 ≤ b)
    (h : ∀ i ∈ s, z i ≤ b) : foldMaxR s z ≤ b := by
  induction s using Finset.induction_on with
  | empty => simpa [foldMaxR_empty]
  | insert a s ha ih =>
      rw [foldMaxR_insert ha]
      exact max_le (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem foldMaxR_eq_zero_of_nonpos [DecidableEq α] (s : Finset α) {z : α → ℝ}
    (h : ∀ i ∈ s, z i ≤ 0) : foldMaxR s z = 0 :=
  le_antisymm (foldMaxR_le le_rfl h) (foldMaxR_nonneg s z)

/-- Positive homogeneity — `M` is a gauge, so it scales. -/
theorem foldMaxR_smul [DecidableEq α] (s : Finset α) (z : α → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    foldMaxR s (fun i => c * z i) = c * foldMaxR s z := by
  induction s using Finset.induction_on with
  | empty => simp [foldMaxR_empty]
  | insert a s ha ih =>
      rw [foldMaxR_insert ha, foldMaxR_insert ha, ih, mul_max_of_nonneg _ _ hc]

/-- **`M` is convex** — it is a maximum of linear functions, and this is the only property of it
the forward inclusion uses. -/
theorem foldMaxR_convex [DecidableEq α] (s : Finset α) (x y : α → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    foldMaxR s (fun i => a * x i + b * y i) ≤ a * foldMaxR s x + b * foldMaxR s y := by
  refine foldMaxR_le ?_ ?_
  · have h1 := foldMaxR_nonneg s x
    have h2 := foldMaxR_nonneg s y
    positivity
  · intro i hi
    exact add_le_add (mul_le_mul_of_nonneg_left (le_foldMaxR hi) ha)
      (mul_le_mul_of_nonneg_left (le_foldMaxR hi) hb)

end GaugeReal

section GaugeFn

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- `U_i(z) = max({0} ∪ {z_j : i ≤_τ j})`, over `ℝ`. -/
def gaugeUR (le : E → E → Prop) [DecidableRel le] (z : E → ℝ) (i : E) : ℝ :=
  foldMaxR (Finset.univ.filter (fun j => le i j)) z

/-- **The gauge over `ℝ`**, `g_τ(z) = M(z) + ∑_i U_i(z) − ∑_i z_i`.  The same formula as
`gauge`, on real vectors. -/
def gaugeR (le : E → E → Prop) [DecidableRel le] (z : E → ℝ) : ℝ :=
  foldMaxR Finset.univ z + ∑ i, gaugeUR le z i - ∑ i, z i

theorem gaugeR_smul (le : E → E → Prop) [DecidableRel le] (z : E → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    gaugeR le (fun i => c * z i) = c * gaugeR le z := by
  have h2 : ∀ i, gaugeUR le (fun i => c * z i) i = c * gaugeUR le z i :=
    fun i => foldMaxR_smul _ _ hc
  rw [gaugeR, gaugeR, foldMaxR_smul _ _ hc, Finset.sum_congr rfl (fun i _ => h2 i),
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **The sublevel sets of `g_τ` are convex.**  `M` and each `U_i` are maxima of linear
functions and `−∑ z` is linear, so `g_τ` is a sum of convex functions. -/
theorem convex_gaugeR_le (le : E → E → Prop) [DecidableRel le] (k : ℝ) :
    Convex ℝ {z : E → ℝ | gaugeR le z ≤ k} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq, gaugeR] at hx hy
  have hfun : (a • x + b • y : E → ℝ) = fun i => a * x i + b * y i := by
    funext i; simp
  have h1 : foldMaxR Finset.univ (fun i => a * x i + b * y i)
      ≤ a * foldMaxR Finset.univ x + b * foldMaxR Finset.univ y :=
    foldMaxR_convex _ _ _ ha hb
  have h3 : ∑ i, gaugeUR le (fun i => a * x i + b * y i) i
      ≤ a * (∑ i, gaugeUR le x i) + b * (∑ i, gaugeUR le y i) := by
    calc ∑ i, gaugeUR le (fun i => a * x i + b * y i) i
        ≤ ∑ i, (a * gaugeUR le x i + b * gaugeUR le y i) :=
          Finset.sum_le_sum (fun i _ => foldMaxR_convex _ _ _ ha hb)
      _ = a * (∑ i, gaugeUR le x i) + b * (∑ i, gaugeUR le y i) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h4 : ∑ i, (a * x i + b * y i) = a * (∑ i, x i) + b * (∑ i, y i) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hax := mul_le_mul_of_nonneg_left hx ha
  have hby := mul_le_mul_of_nonneg_left hy hb
  have hk : a * k + b * k = k := by rw [← add_mul, hab, one_mul]
  simp only [Set.mem_setOf_eq, hfun, gaugeR, h4]
  nlinarith [h1, h3, hax, hby, hk]

/-- `g_τ(−e_i) = 1`: the negative coordinate contributes `+1` through `−∑ z`, and both maxima
vanish because every entry is `≤ 0`. -/
theorem gaugeR_negUnit (le : E → E → Prop) [DecidableRel le] (i : E) :
    gaugeR le (negUnit i) = 1 := by
  have hnp : ∀ j : E, negUnit i j ≤ 0 := by
    intro j
    simp only [negUnit]
    split <;> norm_num
  have hM : foldMaxR Finset.univ (negUnit i) = 0 :=
    foldMaxR_eq_zero_of_nonpos _ (fun j _ => hnp j)
  have hU : ∀ j : E, gaugeUR le (negUnit i) j = 0 :=
    fun j => foldMaxR_eq_zero_of_nonpos _ (fun l _ => hnp l)
  have hS : ∑ j : E, negUnit i j = -1 := by
    simp [negUnit]
  rw [gaugeR, hM, Finset.sum_congr rfl (fun j _ => hU j), hS]
  simp

/-- `g_τ(1_I) ≤ 1` for an ideal `I`.  The load-bearing step is `U_i(1_I) ≤ 1_I(i)`, which **is**
the ideal property: if some `j` above `i` lies in `I` then `i` does. -/
theorem gaugeR_indicator_le (le : E → E → Prop) [DecidableRel le] {I : Finset E}
    (hI : IsIdeal le I) : gaugeR le (fun j => if j ∈ I then (1 : ℝ) else 0) ≤ 1 := by
  have hM : foldMaxR Finset.univ (fun j => if j ∈ I then (1 : ℝ) else 0) ≤ 1 := by
    refine foldMaxR_le zero_le_one (fun j _ => ?_)
    split <;> norm_num
  have hU : ∀ i : E, gaugeUR le (fun j => if j ∈ I then (1 : ℝ) else 0) i
      ≤ (if i ∈ I then (1 : ℝ) else 0) := by
    intro i
    refine foldMaxR_le ?_ ?_
    · split <;> norm_num
    · intro j hj
      rw [Finset.mem_filter] at hj
      by_cases hi : i ∈ I
      · rw [if_pos hi]
        split <;> norm_num
      · have hjI : j ∉ I := fun h => hi (hI i j hj.2 h)
        rw [if_neg hi, if_neg hjI]
  have hsum : ∑ i, gaugeUR le (fun j => if j ∈ I then (1 : ℝ) else 0) i
      ≤ ∑ i : E, (if i ∈ I then (1 : ℝ) else 0) := Finset.sum_le_sum (fun i _ => hU i)
  rw [gaugeR]
  linarith

theorem gaugeR_le_one_of_mem_polarVertices (le : E → E → Prop) [DecidableRel le] {v : E → ℝ}
    (hv : v ∈ polarVertices le) : gaugeR le v ≤ 1 := by
  rcases hv with ⟨i, rfl⟩ | ⟨I, -, hI, rfl⟩
  · exact le_of_eq (gaugeR_negUnit le i)
  · exact gaugeR_indicator_le le hI

/-- **The forward half of fact (3)**: `kK_τ ⊆ {z : g_τ(z) ≤ k}`.

No decomposition of a point of `kK_τ` is needed, and no hypothesis on `le` beyond decidability:
`kK_τ` is the hull of the scaled vertices, the sublevel set is convex, and every scaled vertex
lies in it. -/
theorem smul_polarPolytope_subset (le : E → E → Prop) [DecidableRel le] {k : ℝ} (hk : 0 ≤ k) :
    k • polarPolytope le ⊆ {z : E → ℝ | gaugeR le z ≤ k} := by
  simp only [polarPolytope]
  rw [← convexHull_smul]
  refine convexHull_min ?_ (convex_gaugeR_le le k)
  rintro _ ⟨v, hv, rfl⟩
  have hkv : (k • v : E → ℝ) = fun i => k * v i := by funext i; simp
  have h1 : gaugeR le (k • v) = k * gaugeR le v := by rw [hkv, gaugeR_smul _ _ hk]
  have h2 : gaugeR le v ≤ 1 := gaugeR_le_one_of_mem_polarVertices le hv
  simp only [Set.mem_setOf_eq, h1]
  calc k * gaugeR le v ≤ k * 1 := mul_le_mul_of_nonneg_left h2 hk
    _ = k := mul_one k

end GaugeFn

section GaugeReverse

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A convex set containing the origin is closed under SUB-convex combinations — weights that
sum to at most `1`.  The slack rides on the origin. -/
theorem add_smul_mem_of_add_le_one {F : Type*} [AddCommGroup F] [Module ℝ F] {C : Set F}
    (hC : Convex ℝ C) (h0 : (0 : F) ∈ C) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t ≤ 1)
    {p q : F} (hp : p ∈ C) (hq : q ∈ C) : s • p + t • q ∈ C := by
  rcases eq_or_lt_of_le (by linarith : (0 : ℝ) ≤ s + t) with hr | hr
  · have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    simpa [hs0, ht0] using h0
  · have hne : s + t ≠ 0 := ne_of_gt hr
    have hw : (s / (s + t)) • p + (t / (s + t)) • q ∈ C := by
      refine hC hp hq (by positivity) (by positivity) ?_
      field_simp
    have h2 := hC hw h0 (le_of_lt hr) (by linarith : (0 : ℝ) ≤ 1 - (s + t)) (by ring)
    have e1 : (s + t) * (s / (s + t)) = s := by field_simp
    have e2 : (s + t) * (t / (s + t)) = t := by field_simp
    have h3 : (s + t) • ((s / (s + t)) • p + (t / (s + t)) • q) + (1 - (s + t)) • (0 : F)
        = s • p + t • q := by
      rw [smul_add, smul_zero, add_zero, smul_smul, smul_smul, e1, e2]
    rwa [h3] at h2

/-- If `x ∈ a • C` and `y ∈ b • C` with `a + b ≤ k`, then `x + y ∈ k • C`. -/
theorem add_mem_smul_of_add_le {F : Type*} [AddCommGroup F] [Module ℝ F] {C : Set F}
    (hC : Convex ℝ C) (h0 : (0 : F) ∈ C) {a b k : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ k) {p q : F} (hp : p ∈ C) (hq : q ∈ C) : a • p + b • q ∈ k • C := by
  have hk : (0 : ℝ) ≤ k := le_trans (by linarith) hab
  rcases eq_or_lt_of_le hk with hk0 | hk0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    refine ⟨0, h0, ?_⟩
    rw [← hk0, ha0, hb0]
    simp
  · refine ⟨(k⁻¹ * a) • p + (k⁻¹ * b) • q, ?_, ?_⟩
    · refine add_smul_mem_of_add_le_one hC h0 (by positivity) (by positivity) ?_ hp hq
      rw [← mul_add, inv_mul_le_one₀ hk0]
      exact hab
    · show k • ((k⁻¹ * a) • p + (k⁻¹ * b) • q) = a • p + b • q
      rw [smul_add, smul_smul, smul_smul, mul_inv_cancel_left₀ (ne_of_gt hk0),
        mul_inv_cancel_left₀ (ne_of_gt hk0)]

theorem gaugeUR_nonneg (le : E → E → Prop) [DecidableRel le] (z : E → ℝ) (i : E) :
    0 ≤ gaugeUR le z i := foldMaxR_nonneg _ _

/-- `z_i ≤ U_i(z)` — the only place reflexivity is used. -/
theorem le_gaugeUR {le : E → E → Prop} [DecidableRel le] (hrefl : ∀ i, le i i) (z : E → ℝ)
    (i : E) : z i ≤ gaugeUR le z i :=
  le_foldMaxR (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hrefl i⟩)

theorem gaugeUR_le_top (le : E → E → Prop) [DecidableRel le] (z : E → ℝ) (i : E) :
    gaugeUR le z i ≤ foldMaxR Finset.univ z :=
  foldMaxR_le (foldMaxR_nonneg _ _) (fun j _ => le_foldMaxR (Finset.mem_univ j))

/-- `U` is `τ`-decreasing — the only place transitivity is used. -/
theorem gaugeUR_anti {le : E → E → Prop} [DecidableRel le]
    (htrans : ∀ i j l, le i j → le j l → le i l) (z : E → ℝ) {i j : E} (hij : le i j) :
    gaugeUR le z j ≤ gaugeUR le z i := by
  refine foldMaxR_le (foldMaxR_nonneg _ _) (fun l hl => ?_)
  rw [Finset.mem_filter] at hl
  exact le_foldMaxR (Finset.mem_filter.mpr ⟨Finset.mem_univ l, htrans i j l hij hl.2⟩)

/-- `U(z)/M(z)` is a point of the order polytope. -/
theorem smul_gaugeUR_mem_orderPolytope {le : E → E → Prop} [DecidableRel le]
    (htrans : ∀ i j l, le i j → le j l → le i l) (z : E → ℝ)
    (hpos : 0 < foldMaxR Finset.univ z) :
    (fun i => (foldMaxR Finset.univ z)⁻¹ * gaugeUR le z i) ∈ orderPolytope le := by
  have hinv : 0 < (foldMaxR Finset.univ z)⁻¹ := inv_pos.mpr hpos
  refine ⟨fun i => ⟨mul_nonneg (le_of_lt hinv) (gaugeUR_nonneg le z i), ?_⟩, fun i j hij => ?_⟩
  · calc (foldMaxR Finset.univ z)⁻¹ * gaugeUR le z i
        ≤ (foldMaxR Finset.univ z)⁻¹ * foldMaxR Finset.univ z :=
          mul_le_mul_of_nonneg_left (gaugeUR_le_top le z i) (le_of_lt hinv)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  · exact mul_le_mul_of_nonneg_left (gaugeUR_anti htrans z hij) (le_of_lt hinv)

/-- A nonnegative vector normalised by its own coordinate sum, negated, lies in `-Δ_E`. -/
theorem neg_smul_mem_negSimplex {v : E → ℝ} (hv : ∀ i, 0 ≤ v i) {b : ℝ} (hb : 0 < b)
    (hsum : ∑ i, v i = b) : (fun i => -(b⁻¹ * v i)) ∈ negSimplex E := by
  refine mem_convexHull_of_exists_fintype (fun i : E => b⁻¹ * v i) (fun i : E => negUnit i)
    (fun i => mul_nonneg (le_of_lt (inv_pos.mpr hb)) (hv i)) ?_ ?_ ?_
  · rw [← Finset.mul_sum, hsum, inv_mul_cancel₀ (ne_of_gt hb)]
  · exact fun i => Set.mem_insert_of_mem _ ⟨i, rfl⟩
  · funext j
    rw [Finset.sum_apply]
    have hterm : ∀ i : E, ((b⁻¹ * v i) • negUnit i) j = if i = j then -(b⁻¹ * v i) else 0 := by
      intro i
      simp only [Pi.smul_apply, smul_eq_mul, negUnit]
      by_cases hji : j = i
      · subst hji; simp
      · rw [if_neg hji, if_neg (fun h : i = j => hji h.symm)]
        ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i),
      Finset.sum_ite_eq' Finset.univ j (fun i : E => -(b⁻¹ * v i))]
    simp

omit [Fintype E] in
theorem convex_polarPolytope (le : E → E → Prop) : Convex ℝ (polarPolytope le) :=
  convex_convexHull ℝ _

theorem orderPolytope_subset_polarPolytope [Nonempty E] (le : E → E → Prop) :
    orderPolytope le ⊆ polarPolytope le := by
  rw [polarPolytope_eq_convexHull_union]
  exact Set.Subset.trans Set.subset_union_left (subset_convexHull ℝ _)

theorem negSimplex_subset_polarPolytope [Nonempty E] (le : E → E → Prop) :
    negSimplex E ⊆ polarPolytope le := by
  rw [polarPolytope_eq_convexHull_union]
  exact Set.Subset.trans Set.subset_union_right (subset_convexHull ℝ _)

/-- **The reverse half of fact (3)**: `g_τ(z) ≤ k` puts `z` in `kK_τ`.

The witness is the write-up's own: `u = U(z)` is the coordinatewise least nonnegative
`τ`-decreasing vector dominating `z`, `v = u − z ≥ 0`, and `z = u − v` splits the mass as
`M(z)` on `O_τ` and `∑v` on `−Δ_E`, the two summing to exactly `g_τ(z)`. -/
theorem mem_smul_polarPolytope_of_gaugeR_le [Nonempty E] {le : E → E → Prop} [DecidableRel le]
    (hrefl : ∀ i, le i i) (htrans : ∀ i j l, le i j → le j l → le i l)
    {k : ℝ} {z : E → ℝ} (h : gaugeR le z ≤ k) : z ∈ k • polarPolytope le := by
  have ha : 0 ≤ foldMaxR Finset.univ z := foldMaxR_nonneg _ _
  have hvnn : ∀ i : E, 0 ≤ gaugeUR le z i - z i := fun i => by
    have := le_gaugeUR hrefl z i; linarith
  have hb : 0 ≤ ∑ i, (gaugeUR le z i - z i) := Finset.sum_nonneg (fun i _ => hvnn i)
  have hsplit : gaugeR le z
      = foldMaxR Finset.univ z + ∑ i, (gaugeUR le z i - z i) := by
    rw [gaugeR, Finset.sum_sub_distrib]
    ring
  have hab : foldMaxR Finset.univ z + ∑ i, (gaugeUR le z i - z i) ≤ k := by
    rw [← hsplit]; exact h
  -- the `O_τ` half
  have hP : ∃ p ∈ polarPolytope le,
      (foldMaxR Finset.univ z) • p = gaugeUR le z := by
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · refine ⟨0, zero_mem_polarPolytope le, ?_⟩
      funext i
      have h1 : 0 ≤ gaugeUR le z i := gaugeUR_nonneg le z i
      have h2 : gaugeUR le z i ≤ foldMaxR Finset.univ z := gaugeUR_le_top le z i
      have : gaugeUR le z i = 0 := by linarith
      simp [this]
    · refine ⟨fun i => (foldMaxR Finset.univ z)⁻¹ * gaugeUR le z i,
        orderPolytope_subset_polarPolytope le
          (smul_gaugeUR_mem_orderPolytope htrans z ha0), ?_⟩
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
  -- the `−Δ_E` half
  have hQ : ∃ q ∈ polarPolytope le,
      (∑ i, (gaugeUR le z i - z i)) • q = (fun i => z i - gaugeUR le z i) := by
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · refine ⟨0, zero_mem_polarPolytope le, ?_⟩
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hvnn j)).mp hb0.symm i
        (Finset.mem_univ i)
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero]
      linarith
    · refine ⟨fun i => -((∑ i, (gaugeUR le z i - z i))⁻¹ * (gaugeUR le z i - z i)),
        negSimplex_subset_polarPolytope le
          (neg_smul_mem_negSimplex hvnn hb0 rfl), ?_⟩
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
  obtain ⟨p, hp, hpe⟩ := hP
  obtain ⟨q, hq, hqe⟩ := hQ
  have hz : z = (foldMaxR Finset.univ z) • p + (∑ i, (gaugeUR le z i - z i)) • q := by
    rw [hpe, hqe]
    funext i
    simp
  rw [hz]
  exact add_mem_smul_of_add_le (convex_polarPolytope le) (zero_mem_polarPolytope le)
    ha hb hab hp hq

/-- **Fact (3)**: `kK_τ = {z : g_τ(z) ≤ k}` for `k ≥ 0`.  This is the membership form of the
gauge lemma, and it is what `kK_τ ∩ ℤ^E = {z : g_τ(z) ≤ k}` needs. -/
theorem mem_smul_polarPolytope_iff [Nonempty E] {le : E → E → Prop} [DecidableRel le]
    (hrefl : ∀ i, le i i) (htrans : ∀ i j l, le i j → le j l → le i l)
    {k : ℝ} (hk : 0 ≤ k) (z : E → ℝ) :
    z ∈ k • polarPolytope le ↔ gaugeR le z ≤ k :=
  ⟨fun hz => smul_polarPolytope_subset le hk hz,
   fun hz => mem_smul_polarPolytope_of_gaugeR_le hrefl htrans hz⟩

end GaugeReverse

section IntBridge

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The `ℤ`-valued fold and the `ℝ`-valued one agree under `Int.cast`.  This is the only
connection between the lattice count and the convex geometry, and it is an induction on the
`Finset`. -/
theorem foldMaxR_intCast {α : Type*} [DecidableEq α] (s : Finset α) (z : α → ℤ) :
    foldMaxR s (fun i => (z i : ℝ)) = ((foldMax s z : ℤ) : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp [foldMaxR_empty, foldMax_empty]
  | insert a s ha ih => rw [foldMaxR_insert ha, foldMax_insert ha, ih, Int.cast_max]

theorem gaugeUR_intCast (le : E → E → Prop) [DecidableRel le] (z : E → ℤ) (i : E) :
    gaugeUR le (fun j => (z j : ℝ)) i = ((gaugeU le z i : ℤ) : ℝ) :=
  foldMaxR_intCast _ _

theorem gaugeR_intCast (le : E → E → Prop) [DecidableRel le] (z : E → ℤ) :
    gaugeR le (fun j => (z j : ℝ)) = ((gauge le z : ℤ) : ℝ) := by
  rw [gaugeR, gauge, foldMaxR_intCast,
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => gaugeUR_intCast le z i)]
  push_cast
  ring

/-- **The lattice form of fact (3)**: an integer point lies in `kK_τ` exactly when the
integer-valued gauge does not exceed `k`.  This is the sentence
`kK_τ ∩ ℤ^E = {z : g_τ(z) ≤ k}` that the `h*` computation consumes. -/
theorem mem_smul_polarPolytope_intCast_iff [Nonempty E] {le : E → E → Prop} [DecidableRel le]
    (hrefl : ∀ i, le i i) (htrans : ∀ i j l, le i j → le j l → le i l) (k : ℕ) (z : E → ℤ) :
    (fun i => (z i : ℝ)) ∈ (k : ℝ) • polarPolytope le ↔ gauge le z ≤ (k : ℤ) := by
  rw [mem_smul_polarPolytope_iff hrefl htrans (by positivity), gaugeR_intCast]
  exact_mod_cast Iff.rfl

end IntBridge

section LatticeCount

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The lattice points of the `k`-th dilate `kK_τ`, as a `Finset`.  The box cut loses nothing,
by the same `fiber_box_gen` that makes a single level set finite. -/
noncomputable def ballSet (le : E → E → Prop) [DecidableRel le] (k : ℕ) : Finset (E → ℤ) :=
  (boxFinset E k).filter (fun z => gauge le z ≤ (k : ℤ))

theorem mem_ballSet {le : E → E → Prop} [DecidableRel le] (hrefl : ∀ i, le i i) (k : ℕ)
    (z : E → ℤ) : z ∈ ballSet le k ↔ gauge le z ≤ (k : ℤ) := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    rw [boxFinset, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hg : foldMax Finset.univ z + ∑ j, (gaugeU le z j - z j) ≤ (k : ℤ) := by
      rw [← gauge_eq]
      exact h
    exact fiber_box_gen z (gaugeU le z) (k : ℤ) (le_gaugeU hrefl z) (gaugeU_nonneg le z) hg i

/-- **`ballSet` really is `kK_τ ∩ ℤ^E`** — the write-up's sentence, and the point of the whole
interface layer. -/
theorem mem_ballSet_iff_dilate [Nonempty E] {le : E → E → Prop} [DecidableRel le]
    (hrefl : ∀ i, le i i) (htrans : ∀ i j l, le i j → le j l → le i l) (k : ℕ) (z : E → ℤ) :
    z ∈ ballSet le k ↔ (fun i => (z i : ℝ)) ∈ (k : ℝ) • polarPolytope le := by
  rw [mem_ballSet hrefl, mem_smul_polarPolytope_intCast_iff hrefl htrans]

/-- The dilation count `#(kK_τ ∩ ℤ^E)`. -/
noncomputable def ballCount (le : E → E → Prop) [DecidableRel le] (k : ℕ) : ℤ :=
  ((ballSet le k).card : ℤ)

/-- **The dilation counts are the partial sums of the level counts** — the combinatorial form of
`∑_k #(kK ∩ ℤ^E) t^k = Θ_τ(t)/(1−t)`. -/
theorem ballCount_eq_sum (le : E → E → Prop) [DecidableRel le] (hrefl : ∀ i, le i i) (k : ℕ) :
    ballCount le k = ∑ j ∈ Finset.range (k + 1), aCount le j := by
  have hbi : ballSet le k = (Finset.range (k + 1)).biUnion (fun j => levelSet le j) := by
    ext z
    rw [Finset.mem_biUnion, mem_ballSet hrefl]
    constructor
    · intro h
      have h0 : 0 ≤ gauge le z := gauge_nonneg hrefl z
      refine ⟨(gauge le z).toNat, ?_, ?_⟩
      · rw [Finset.mem_range]; omega
      · rw [mem_levelSet hrefl]; omega
    · rintro ⟨j, hj, hz⟩
      rw [Finset.mem_range] at hj
      rw [mem_levelSet hrefl] at hz
      omega
  have hdisj : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1), i ≠ j →
      Disjoint (levelSet le i) (levelSet le j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro z hzi hzj
    rw [mem_levelSet hrefl] at hzi hzj
    exact hij (by omega)
  rw [ballCount, hbi, Finset.card_biUnion hdisj, Nat.cast_sum]
  rfl

/-- `Θ_τ = (1 − X) · ∑_k #(kK_τ ∩ ℤ^E) X^k`. -/
theorem mk_aCount_eq (le : E → E → Prop) [DecidableRel le] (hrefl : ∀ i, le i i) :
    (PowerSeries.mk (aCount le) : PowerSeries ℤ)
      = (1 - PowerSeries.X) * PowerSeries.mk (ballCount le) := by
  ext k
  rw [PowerSeries.coeff_mk, sub_mul, one_mul, map_sub, PowerSeries.coeff_mk]
  cases k with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul, ballCount_eq_sum le hrefl 0]
      simp
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
        ballCount_eq_sum le hrefl (n + 1), ballCount_eq_sum le hrefl n, Finset.sum_range_succ]
      ring

/-- **`h*(K_τ, t) = (1 − t)^{|E|+1} ∑_k #(kK_τ ∩ ℤ^E) t^k`** — the write-up's definition,
verbatim, with the dilation counts and not with `aCount`. -/
noncomputable def hStarK (le : E → E → Prop) [DecidableRel le] : PowerSeries ℤ :=
  (1 - PowerSeries.X) ^ (Fintype.card E + 1) * PowerSeries.mk (ballCount le)

/-- One `(1 − X)` cancels the partial summation, which is why the exponent in the definition is
`n + 1` and the exponent in the factorisation is `n`. -/
theorem hStarK_eq (le : E → E → Prop) [DecidableRel le] (hrefl : ∀ i, le i i) :
    hStarK le = (1 - PowerSeries.X) ^ (Fintype.card E) * PowerSeries.mk (aCount le) := by
  rw [hStarK, mk_aCount_eq le hrefl, pow_succ]
  ring

end LatticeCount

section Conjecture63

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **Athanasiadis–Chapoton, Conjecture 6.3**, in the source's own terms:
`h*(K_{τ₁ ⊕ τ₂}, t) = h*(K_{τ₁}, t) · h*(K_{τ₂}, t)`, where `h*` is the dilation-count
generating function of the polar preorder polytope `K_τ = conv({-e_i} ∪ {1_I})` and `⊕` is the
ordinal sum.  Reflexivity of the two preorders is the only hypothesis; antisymmetry is used
nowhere, so genuine preorders are admitted, and an empty factor is an ordinary case. -/
theorem conjecture_6_3 {r1 : A → A → Prop} {r2 : B → B → Prop}
    [DecidableRel r1] [DecidableRel r2] (hrefl1 : ∀ a, r1 a a) (hrefl2 : ∀ b, r2 b b) :
    hStarK (ordSum r1 r2) = hStarK r1 * hStarK r2 := by
  rw [hStarK_eq _ (ordSum_refl hrefl1 hrefl2), hStarK_eq _ hrefl1, hStarK_eq _ hrefl2,
    Fintype.card_sum]
  exact hStar_mul_ordSum hrefl1 hrefl2 _ _

end Conjecture63

end Principia.MathDB.P374964
