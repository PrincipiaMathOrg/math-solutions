/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# MathDB #347688 — `rep(X_{2,9}) ≤ 5`

MathDB open problem #347688, from Alan Lew, *Representability and boxicity of simplicial
complexes*, arXiv:2008.09997, Conjecture 20 (Discrete & Comput. Geom. 68 (2022) 592–607).

`X_{2,9}` is the simplicial complex of **line-free** subsets of the affine plane `AG(2,3)`, whose
nine points are identified with `Fin 9` in lexicographic order and whose twelve lines are listed in
`pt`.  A complex is `d`-representable when it is the nerve of a finite family of **compact convex**
subsets of `ℝ^d`, and `rep` is the least such `d`.  The question asks whether `rep(X_{2,9}) ≤ 5`.

**It is.**  `representable_five` exhibits nine compact convex polytopes in `ℝ⁵` whose nerve is
exactly `X_{2,9}`:

  `C v = [-42,42]⁵ ∩ ⋂ {x | 1 ≤ ℓ_{L,v}(x)}`,  the intersection over the four lines `L` through `v`,

with `ℓ_{L,v}` the integral affine form `normal` attaches to the incidence `(L, v)`.

## Why the two directions are cheap

The construction is engineered so that each half of the nerve equality is a one-line consequence
of an integer fact about the certificate.

* **Nonfaces.**  For every line `L = {p,q,r}` the three rows `ℓ_{L,p}, ℓ_{L,q}, ℓ_{L,r}` sum to the
  zero row (`rowSum_zero`, checked by `decide`).  A point of `C_p ∩ C_q ∩ C_r` would make three
  forms that sum identically to `0` each at least `1`.  So a set containing a line is a nonface —
  no convexity, no geometry, just `1 + 1 + 1 ≤ 0`.
* **Faces.**  Every line-free set sits inside one of the 54 four-caps (`covering`), and each cap
  carries an explicit integral witness satisfying all of its incident inequalities and the box
  (`capWit_ok`).  Casting `ℤ → ℝ` is the only analysis involved.

Both `decide`s run on **integer** data: `ellZ` is the `ℤ`-valued evaluation and `ellZ_cast` is the
bridge to the `ℝ`-valued `ell`, so nothing undecidable is ever asked of the kernel.

## What is proved, and what is not

`representable_five` is the full statement: the nine sets are compact, convex, and their nerve is
`X_{2,9}` on the nose.  This is an **upper** bound only — the source claims no lower bound, and
neither does this file, so `rep(X_{2,9}) = 5` is not asserted.

The certificate is Anton's, generated and checked in Python; the Lean file re-checks every integer
fact it relies on rather than trusting that run.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset

namespace Principia.MathDB.P347688

open Finset

/-! ### Affine rows -/

/-- An integral affine form on `ℝ⁵`: the constant `c` and the five coefficients `a`. -/
structure Row where
  c : ℤ
  a : Fin 5 → ℤ

/-- Build a row from six integers. -/
def mkRow (c a0 a1 a2 a3 a4 : ℤ) : Row := ⟨c, ![a0, a1, a2, a3, a4]⟩

/-- The real affine form.  Written out rather than as a `Finset.sum`, so that `ellZ` below is
cheap for the kernel to evaluate. -/
def ell (r : Row) (x : Fin 5 → ℝ) : ℝ :=
  (r.c : ℝ) + (r.a 0 : ℝ) * x 0 + (r.a 1 : ℝ) * x 1 + (r.a 2 : ℝ) * x 2
    + (r.a 3 : ℝ) * x 3 + (r.a 4 : ℝ) * x 4

/-- The integer evaluation, which is what every `decide` in this file actually runs on. -/
def ellZ (r : Row) (y : Fin 5 → ℤ) : ℤ :=
  r.c + r.a 0 * y 0 + r.a 1 * y 1 + r.a 2 * y 2 + r.a 3 * y 3 + r.a 4 * y 4

theorem ellZ_cast (r : Row) (y : Fin 5 → ℤ) :
    ell r (fun i => (y i : ℝ)) = (ellZ r y : ℝ) := by
  unfold ell ellZ
  push_cast
  ring

/-- `ell` is affine: it commutes with convex combinations. -/
theorem ell_combo (r : Row) (x y : Fin 5 → ℝ) {a b : ℝ} (hab : a + b = 1) :
    ell r (a • x + b • y) = a * ell r x + b * ell r y := by
  simp only [ell, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(r.c : ℝ)) * hab

theorem continuous_ell (r : Row) : Continuous fun x : Fin 5 → ℝ => ell r x := by
  unfold ell
  first
  | fun_prop
  | continuity

/-- Three rows summing to the zero row give three forms summing to `0`. -/
theorem ell_sum_zero {r s t : Row} (hc : r.c + s.c + t.c = 0)
    (ha : ∀ i, r.a i + s.a i + t.a i = 0) (x : Fin 5 → ℝ) :
    ell r x + ell s x + ell t x = 0 := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  have h4 := ha 4
  have hc' : ((r.c : ℝ)) + (s.c : ℝ) + (t.c : ℝ) = 0 := by exact_mod_cast hc
  have e0 : ((r.a 0 : ℝ)) + (s.a 0 : ℝ) + (t.a 0 : ℝ) = 0 := by exact_mod_cast h0
  have e1 : ((r.a 1 : ℝ)) + (s.a 1 : ℝ) + (t.a 1 : ℝ) = 0 := by exact_mod_cast h1
  have e2 : ((r.a 2 : ℝ)) + (s.a 2 : ℝ) + (t.a 2 : ℝ) = 0 := by exact_mod_cast h2
  have e3 : ((r.a 3 : ℝ)) + (s.a 3 : ℝ) + (t.a 3 : ℝ) = 0 := by exact_mod_cast h3
  have e4 : ((r.a 4 : ℝ)) + (s.a 4 : ℝ) + (t.a 4 : ℝ) = 0 := by exact_mod_cast h4
  simp only [ell]
  linear_combination hc' + x 0 * e0 + x 1 * e1 + x 2 * e2 + x 3 * e3 + x 4 * e4


/-! The certificate data, generated from `certificate.json` in the campaign folder:
`normal i j` is the affine row for the `j`-th point of the `i`-th line, and `capWit`
pairs each line-free four-cap with its integral witness point. -/

/-- The `j`-th point of the `i`-th affine line of `AG(2,3)`. -/
def pt : Fin 12 → Fin 3 → Fin 9 :=
  ![![0, 3, 6], ![1, 4, 7], ![2, 5, 8], ![0, 1, 2], ![3, 4, 5], ![6, 7, 8], ![0, 4, 8], ![1, 5, 6], ![2, 3, 7], ![0, 5, 7], ![1, 3, 8], ![2, 4, 6]]

/-- The affine row attached to the `j`-th point of the `i`-th line. -/
def normal : Fin 12 → Fin 3 → Row :=
  ![![mkRow 10 16 (-18) 7 (-26) 34, mkRow 150 (-4) (-17) (-15) 24 (-17), mkRow (-160) (-12) 35 8 2 (-17)],
    ![mkRow 50 (-50) 0 (-25) 16 (-4), mkRow 120 (-8) (-12) 6 (-17) (-24), mkRow (-170) 58 12 19 1 28],
    ![mkRow 210 13 6 (-31) (-29) (-23), mkRow 260 11 22 6 0 6, mkRow (-470) (-24) (-28) 25 29 17],
    ![mkRow (-50) (-2) 15 (-1) (-29) 15, mkRow (-40) 13 13 (-32) 7 0, mkRow 90 (-11) (-28) 33 22 (-15)],
    ![mkRow (-50) (-14) 10 (-21) 14 25, mkRow (-260) 10 (-15) (-3) (-11) (-28), mkRow 310 4 5 24 (-3) 3],
    ![mkRow 40 (-9) 20 (-2) (-4) (-10), mkRow 10 25 0 (-9) (-7) 5, mkRow (-50) (-16) (-20) 11 11 5],
    ![mkRow 30 0 15 (-4) (-23) 11, mkRow 30 14 (-1) (-16) (-3) (-23), mkRow (-60) (-14) (-14) 20 26 12],
    ![mkRow (-40) 4 (-25) (-21) 7 11, mkRow 260 11 (-9) 15 (-8) 5, mkRow (-220) (-15) 34 6 1 (-16)],
    ![mkRow 80 (-11) (-11) 18 9 (-19), mkRow 110 (-22) 5 (-18) (-12) 4, mkRow (-190) 33 6 0 3 15],
    ![mkRow (-30) (-23) 6 0 (-27) 11, mkRow 240 (-16) (-5) 5 17 (-15), mkRow (-210) 39 (-1) (-5) 10 4],
    ![mkRow 70 19 31 (-19) 7 (-11), mkRow 70 (-5) (-1) (-27) (-34) 6, mkRow (-140) (-14) (-30) 46 27 5],
    ![mkRow 220 (-3) (-9) 6 10 22, mkRow (-60) 15 (-23) (-9) (-8) (-9), mkRow (-160) (-12) 32 3 (-2) (-13)]]

/-- The 54 line-free four-caps, each with its integral witness point. -/
def capWit : List (Finset (Fin 9) × (Fin 5 → ℤ)) :=
  [({0, 1, 3, 4}, ![-1, -2, -21, -16, -3]),
   ({0, 1, 3, 5}, ![-4, 3, -9, 3, 13]),
   ({0, 1, 3, 7}, ![7, 4, -23, -6, 10]),
   ({0, 1, 4, 5}, ![0, -4, -8, -10, -6]),
   ({0, 1, 4, 6}, ![7, 19, -40, -29, -4]),
   ({0, 1, 5, 8}, ![-6, 10, -1, 14, 28]),
   ({0, 1, 6, 7}, ![6, 23, -29, -7, 12]),
   ({0, 1, 6, 8}, ![-19, 21, -5, 25, 42]),
   ({0, 1, 7, 8}, ![0, 12, 0, 15, 42]),
   ({0, 2, 3, 4}, ![-19, -20, -14, -14, -2]),
   ({0, 2, 3, 5}, ![-11, -3, -1, -4, 4]),
   ({0, 2, 3, 8}, ![-13, -17, -2, -11, 9]),
   ({0, 2, 4, 5}, ![5, -9, 11, -14, -6]),
   ({0, 2, 4, 7}, ![15, -15, 10, -22, -2]),
   ({0, 2, 5, 6}, ![-9, 3, 14, -14, -2]),
   ({0, 2, 6, 7}, ![15, 12, 26, -15, 1]),
   ({0, 2, 6, 8}, ![-30, -8, 14, -21, -7]),
   ({0, 2, 7, 8}, ![12, -33, 12, -21, 12]),
   ({0, 3, 4, 7}, ![12, -7, -23, -16, 5]),
   ({0, 3, 5, 8}, ![-12, -4, -4, 2, 15]),
   ({0, 3, 7, 8}, ![4, -21, -8, -4, 25]),
   ({0, 4, 5, 6}, ![5, 4, 12, -17, -14]),
   ({0, 4, 6, 7}, ![17, 14, -2, -20, -7]),
   ({0, 5, 6, 8}, ![-7, 11, 14, 6, 15]),
   ({1, 2, 3, 4}, ![1, -14, -19, 7, -8]),
   ({1, 2, 3, 5}, ![-4, -2, -6, 4, -2]),
   ({1, 2, 3, 6}, ![-17, 2, -12, 9, -5]),
   ({1, 2, 4, 5}, ![7, -6, -2, 20, -15]),
   ({1, 2, 4, 8}, ![-2, -13, -7, 21, -16]),
   ({1, 2, 5, 7}, ![9, -1, -7, 19, -4]),
   ({1, 2, 6, 7}, ![11, 11, -12, 33, -10]),
   ({1, 2, 6, 8}, ![-21, -3, -13, 19, -14]),
   ({1, 2, 7, 8}, ![16, -23, -16, 27, -4]),
   ({1, 3, 4, 6}, ![-4, 5, -21, 0, -16]),
   ({1, 3, 5, 7}, ![4, 0, -9, 7, 9]),
   ({1, 3, 6, 7}, ![11, 19, -26, 7, 0]),
   ({1, 4, 5, 8}, ![9, -6, 2, 29, -19]),
   ({1, 4, 6, 8}, ![-9, -8, -7, 31, -35]),
   ({1, 5, 7, 8}, ![4, 0, -3, 16, 18]),
   ({2, 3, 4, 8}, ![-9, -22, -13, 5, -4]),
   ({2, 3, 5, 6}, ![-16, 2, 1, -4, -1]),
   ({2, 3, 6, 8}, ![-27, -5, -2, -1, -8]),
   ({2, 4, 5, 7}, ![14, -5, 17, -3, -7]),
   ({2, 4, 7, 8}, ![17, -29, 9, 0, -5]),
   ({2, 5, 6, 7}, ![11, 10, 13, -1, -3]),
   ({3, 4, 6, 7}, ![19, 19, -36, -18, -12]),
   ({3, 4, 6, 8}, ![-31, -13, -18, 13, -29]),
   ({3, 4, 7, 8}, ![10, -38, -15, -5, 16]),
   ({3, 5, 6, 7}, ![7, 13, -7, 2, -2]),
   ({3, 5, 6, 8}, ![-20, 1, 4, -1, 2]),
   ({3, 5, 7, 8}, ![3, -11, -7, 8, 16]),
   ({4, 5, 6, 7}, ![18, 10, 5, -3, -15]),
   ({4, 5, 6, 8}, ![8, -4, 20, 26, -37]),
   ({4, 5, 7, 8}, ![18, -11, 21, 10, -8])]

/-! ### The nine polytopes -/

/-- `C v = [-42,42]⁵ ∩ ⋂_{L ∋ v} {x | 1 ≤ ℓ_{L,v}(x)}`. -/
def C (v : Fin 9) : Set (Fin 5 → ℝ) :=
  {x | (∀ i, |x i| ≤ 42) ∧ ∀ (i : Fin 12) (j : Fin 3), pt i j = v → 1 ≤ ell (normal i j) x}

/-- The `i`-th affine line as a set of vertices. -/
def lineSet (i : Fin 12) : Finset (Fin 9) := {pt i 0, pt i 1, pt i 2}

/-- `X_{2,9}`: the subsets of `AG(2,3)` containing no line. -/
def X (S : Finset (Fin 9)) : Prop := ∀ i : Fin 12, ¬ (lineSet i ⊆ S)

/-- The nerve of the family `C`: the subsets whose sets have a common point. -/
def Nerve (S : Finset (Fin 9)) : Prop := ∃ x : Fin 5 → ℝ, ∀ v ∈ S, x ∈ C v

/-! ### The three integer checks

Each is a closed computation on the certificate's integers; nothing here touches `ℝ`. -/

/-- For every line, the three incident rows sum to the zero row. -/
theorem rowSum_zero : ∀ i : Fin 12,
    ((normal i 0).c + (normal i 1).c + (normal i 2).c = 0) ∧
      ∀ k : Fin 5, (normal i 0).a k + (normal i 1).a k + (normal i 2).a k = 0 := by decide

/-- Every cap's witness lies in the box and satisfies every inequality incident to the cap. -/
theorem capWit_ok : ∀ p ∈ capWit,
    (∀ i : Fin 5, -42 ≤ p.2 i ∧ p.2 i ≤ 42) ∧
      ∀ (i : Fin 12) (j : Fin 3), pt i j ∈ p.1 → 1 ≤ ellZ (normal i j) p.2 := by decide

-- The one check that ranges over all `2^9` subsets, so it needs a larger elaboration budget.
-- The option must precede the doc-string: `set_option ... in` may not sit between a doc-string
-- and its declaration.
set_option maxRecDepth 100000 in
/-- Every line-free subset of the nine points is contained in one of the 54 four-caps. -/
theorem covering : ∀ S : Finset (Fin 9),
    (∀ i : Fin 12, ¬ (lineSet i ⊆ S)) → ∃ p ∈ capWit, S ⊆ p.1 := by decide

/-! ### The nerve is exactly `X_{2,9}` -/

/-- A set containing a line is a nonface: three forms summing identically to `0` cannot all be
at least `1`. -/
theorem not_nerve_of_line {S : Finset (Fin 9)} {i : Fin 12} (h : lineSet i ⊆ S) : ¬ Nerve S := by
  rintro ⟨x, hx⟩
  have hp : pt i 0 ∈ S := h (by simp [lineSet])
  have hq : pt i 1 ∈ S := h (by simp [lineSet])
  have hr : pt i 2 ∈ S := h (by simp [lineSet])
  have h0 : 1 ≤ ell (normal i 0) x := (hx _ hp).2 i 0 rfl
  have h1 : 1 ≤ ell (normal i 1) x := (hx _ hq).2 i 1 rfl
  have h2 : 1 ≤ ell (normal i 2) x := (hx _ hr).2 i 2 rfl
  have hsum := ell_sum_zero (rowSum_zero i).1 (rowSum_zero i).2 x
  linarith

/-- A line-free set is a face: take the witness of any cap containing it. -/
theorem nerve_of_lineFree {S : Finset (Fin 9)} (h : X S) : Nerve S := by
  obtain ⟨p, hp, hsub⟩ := covering S h
  obtain ⟨hbox, hineq⟩ := capWit_ok p hp
  refine ⟨fun i => (p.2 i : ℝ), fun v hv => ?_⟩
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · have h1 : ((-42 : ℤ) : ℝ) ≤ ((p.2 i : ℤ) : ℝ) := by exact_mod_cast (hbox i).1
    have h2 : ((p.2 i : ℤ) : ℝ) ≤ ((42 : ℤ) : ℝ) := by exact_mod_cast (hbox i).2
    push_cast at h1 h2
    show |((p.2 i : ℤ) : ℝ)| ≤ 42
    rw [abs_le]
    exact ⟨h1, h2⟩
  · have hmem : pt i j ∈ p.1 := by
      rw [hij]
      exact hsub hv
    have hz := hineq i j hmem
    rw [ellZ_cast]
    exact_mod_cast hz

/-- **The nerve equality.** -/
theorem nerve_eq (S : Finset (Fin 9)) : Nerve S ↔ X S := by
  constructor
  · intro hN i hline
    exact not_nerve_of_line hline hN
  · exact nerve_of_lineFree

/-! ### The sets are compact and convex -/

theorem convex_C (v : Fin 9) : Convex ℝ (C v) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · have h1 := abs_le.mp (hx.1 i)
    have h2 := abs_le.mp (hy.1 i)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  · have h1 := hx.2 i j hij
    have h2 := hy.2 i j hij
    rw [ell_combo _ _ _ hab]
    nlinarith

theorem isClosed_C (v : Fin 9) : IsClosed (C v) := by
  have hbox : IsClosed {x : Fin 5 → ℝ | ∀ i, |x i| ≤ 42} := by
    have hrw : {x : Fin 5 → ℝ | ∀ i, |x i| ≤ 42}
        = ⋂ i : Fin 5, {x : Fin 5 → ℝ | |x i| ≤ 42} := by
      ext x
      simp
    rw [hrw]
    exact isClosed_iInter fun i =>
      isClosed_le (continuous_abs.comp (continuous_apply i)) continuous_const
  have hhalf : IsClosed {x : Fin 5 → ℝ |
      ∀ (i : Fin 12) (j : Fin 3), pt i j = v → 1 ≤ ell (normal i j) x} := by
    have hrw : {x : Fin 5 → ℝ |
        ∀ (i : Fin 12) (j : Fin 3), pt i j = v → 1 ≤ ell (normal i j) x}
        = ⋂ i : Fin 12, ⋂ j : Fin 3, ⋂ _ : pt i j = v,
            {x : Fin 5 → ℝ | 1 ≤ ell (normal i j) x} := by
      ext x
      simp
    rw [hrw]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_ell _)
  exact hbox.inter hhalf

theorem isCompact_C (v : Fin 9) : IsCompact (C v) := by
  have hsub : C v ⊆ Set.pi Set.univ fun _ : Fin 5 => Set.Icc (-42 : ℝ) 42 := by
    intro x hx i _
    exact Set.mem_Icc.mpr (abs_le.mp (hx.1 i))
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset (isClosed_C v) hsub

/-! ### The answer -/

/-- **MathDB #347688: `rep(X_{2,9}) ≤ 5`.**  Nine compact convex subsets of `ℝ⁵` whose nerve is
exactly the complex of line-free subsets of `AG(2,3)`.

This is an upper bound only; nothing here says `5` is least. -/
theorem representable_five :
    ∃ K : Fin 9 → Set (Fin 5 → ℝ),
      (∀ v, IsCompact (K v)) ∧ (∀ v, Convex ℝ (K v)) ∧
        ∀ S : Finset (Fin 9),
          (∃ x : Fin 5 → ℝ, ∀ v ∈ S, x ∈ K v) ↔ ∀ i : Fin 12, ¬ (lineSet i ⊆ S) :=
  ⟨C, isCompact_C, convex_C, nerve_eq⟩

end Principia.MathDB.P347688
