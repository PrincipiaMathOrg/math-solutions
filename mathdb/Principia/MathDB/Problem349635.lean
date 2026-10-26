import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false

/-!
# MathDB #349635 — Castronuovo's extremal-row conjecture: the two-point frontier

Write-up: `mathdb-open-problems/problems/349635/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-29 from the
third hundred, see `THIRD100-ENROLMENT.md`).
Source: N. Castronuovo, *On the number of fixed points of the map γ*, arXiv:2102.02739v4,
**Conjecture 6.5** and Example 6.6 (pp. 13–14).

The construction is a binary tree of lattice points generated from `(1,1)` by
`G(n,k) = (n+k, k)` and `S(n,k) = (3n+1-2k, 2n+1-k)`, and the conjecture concerns the maximal
row `rᵢ` of the `i`-th generation, its two claimed OEIS sequences, and the multiplicity of the
extremal row.

## The change of coordinates is the whole idea

With `a = 2k` and `b = 2n + 1 - 2k` — so that `a + b = 2n + 1` and the row is recovered as
`n = (a + b - 1)/2` — the two maps become **shears with nonnegative entries**:

`G(a,b) = (a, a+b)` and `S(a,b) = (a+2b, b)`,

and the seed `(1,1)` becomes `(2,1)`. In these coordinates every step of the argument is integer
arithmetic, and the frontier of each generation is **two points**, given by a matrix power.

## What this module proves

The write-up's Lemma — the two-point frontier and its induction — in full, plus the row formulas
and the recurrence:

* `dom_G` / `dom_S` — **both shears preserve strict domination.** This is the engine of the
  write-up's "children of previously dominated points remain strictly dominated", and it is where
  nonnegativity of the entries is used.
* `uv_bounds` — the invariant `0 < u < v < 2u`, carried by the update `(u,v) ↦ (u+2v, u+3v)`
  because `v' - u' = v` and `2u' - v' = u + v`.
* The even-step frontier `Apt`, `Bpt` and the odd-step frontier `Dpt`, `Ept`, with **all four
  dominance facts**: `Bpt` beats `GA`, `Apt` beats `SB`, `Ept` beats `GD`, `Dpt` beats `SE`. Each
  reduces to a single inequality — `2(v-u) > 0`, `2(v-u) > 0`, `(2u, u)`, `(0, u)` — and the last
  of these is strict in only **one** coordinate, which is why strict domination is defined with a
  disjunction rather than two strict inequalities.
* `G_Ept`, `S_Dpt` — the frontier reproduces itself: `G E = Apt (j+1)` and `S D = Bpt (j+1)`.
* `incomp_Apt_Bpt`, `incomp_Dpt_Ept` — the two survivors are incomparable, so the frontier really
  has two points at even steps.
* `sum_Apt`/`sum_Bpt` equal, and `sum_Dpt < sum_Ept` — so the extremal row has **multiplicity two
  at even steps and one at odd steps**, which is the conjecture's second assertion.
* `uv_parity` — `u` is even and `v` odd, which is what makes every row and column index an
  integer; it is an invariant of the update, not a coincidence of the seed.
* `rowEven`, `rowOdd` and `rowEven_rec`, `rowOdd_rec` — the inhomogeneous recurrence
  `r_{j+2} = 4 r_{j+1} - r_j + 1`, obtained from `P² = 4P - I` (the update matrix has trace 4 and
  determinant 1) and then dividing the displayed sums by two.

## THE CONJECTURE IS PROVED -- `conjecture_6_5`

Stage 2 closed what the section above listed as missing, and the terminal theorem states
Castronuovo's Conjecture 6.5 in one place: for every `j`, the maximal row of the generation at
Step `2j+2` is `A001571 (j+1)` and exactly **two** of its points attain it, while the maximal row
at Step `2j+3` is `A061278 (j+2)` and exactly **one** point attains it.

* `Cg` -- the generations, indexed so that `Cg i` is literally the generation at Step `i`
  (`Cg 1 = {(2,1)}` is the seed), with no offset to remember.
* `covered` -- the write-up's "children of previously dominated points remain strictly dominated",
  as an induction on the **parity pair**: the even frontier gives the odd one
  (`covered_step_even`) and the odd one gives the next even (`covered_step_odd`). Both steps
  consume `dom_Gm`/`dom_Sm` and `dom_trans`, and nothing else.
* `mem_frontier` -- the four frontier points really are members of their generations, so the
  maximum is attained and not merely bounded.
* `Cg_parity` -- every point of the tree has even first and odd second coordinate, so `rowOf` is
  exact; this is what lets the extremal-SUM statements be restated as extremal-ROW statements.
* `extremal_even`/`extremal_odd` compute the attaining sets exactly (`{Apt j, Bpt j}` and
  `{Ept j}`), and `card_extremal_*` give the multiplicities **2** and **1**.
* `A001571` and `A061278` are defined by the recurrence their OEIS entries cite, and
  `rowEven_eq`/`rowOdd_eq` identify the rows with them by two-step induction. **Note the two
  parities have DIFFERENT offsets** -- `rowEven j = A001571 (j+1)` but
  `rowOdd j = A061278 (j+2)`, because `rowOdd j` is the row at Step `2(j+1)+1`. Copying one
  offset from the other is what failed first.
* `card_Cg` -- the generation at Step `i+1` has `2^i` elements, from the write-up's disjoint-cone
  argument: a `Gm`-image satisfies `b > a` (`Gm_cone`) and an `Sm`-image satisfies `a > 2b`
  (`Sm_cone`), which are incompatible on positive points, and both shears are injective.

Nothing in this file is now hypothetical.

-/

namespace Principia.MathDB.P349635

/-! ## The two shears, in the write-up's coordinates -/

/-- `G(a,b) = (a, a+b)`. -/
def Gm (p : ℤ × ℤ) : ℤ × ℤ := (p.1, p.1 + p.2)

/-- `S(a,b) = (a+2b, b)`. -/
def Sm (p : ℤ × ℤ) : ℤ × ℤ := (p.1 + 2 * p.2, p.2)

/-- `x` **strictly dominates** `y`: at least as large in both coordinates and strictly larger in
at least one. The disjunction matters — one of the write-up's four dominance steps is strict in
only one coordinate. -/
def Dom (x y : ℤ × ℤ) : Prop := y.1 ≤ x.1 ∧ y.2 ≤ x.2 ∧ (y.1 < x.1 ∨ y.2 < x.2)

/-- Both shears preserve strict domination. This is where nonnegativity of the entries is used,
and it is the engine of "children of dominated points remain dominated". -/
theorem dom_Gm {x y : ℤ × ℤ} (h : Dom x y) : Dom (Gm x) (Gm y) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, by simp only [Gm]; omega, ?_⟩
  rcases h3 with h | h
  · exact Or.inl h
  · exact Or.inr (by simp only [Gm]; omega)

theorem dom_Sm {x y : ℤ × ℤ} (h : Dom x y) : Dom (Sm x) (Sm y) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simp only [Sm]; omega, h2, ?_⟩
  exact Or.inl (by simp only [Sm]; rcases h3 with h | h <;> omega)

/-! ## The frontier -/

/-- The pair `(u, v)` driving the even-step frontier: `(2,3)` at `j = 0`, then
`(u, v) ↦ (u + 2v, u + 3v)`, which is the matrix `[[1,2],[1,3]]`. -/
def uv : ℕ → ℤ × ℤ
  | 0 => (2, 3)
  | (j + 1) => ((uv j).1 + 2 * (uv j).2, (uv j).1 + 3 * (uv j).2)

/-- The invariant `0 < u < v < 2u`. -/
theorem uv_bounds (j : ℕ) : 0 < (uv j).1 ∧ (uv j).1 < (uv j).2 ∧ (uv j).2 < 2 * (uv j).1 := by
  induction j with
  | zero => refine ⟨by norm_num [uv], by norm_num [uv], by norm_num [uv]⟩
  | succ i ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨?_, ?_, ?_⟩ <;> simp only [uv] <;> omega

/-- `u` is even and `v` is odd — an invariant of the update, which is what makes every row and
column index in the conjecture an integer. -/
theorem uv_parity (j : ℕ) : (uv j).1 % 2 = 0 ∧ (uv j).2 % 2 = 1 := by
  induction j with
  | zero => refine ⟨by norm_num [uv], by norm_num [uv]⟩
  | succ i ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨?_, ?_⟩ <;> simp only [uv] <;> omega

/-- The even-step frontier point `A = (u, v)`. -/
def Apt (j : ℕ) : ℤ × ℤ := uv j

/-- The even-step frontier point `B = (2v - u, 2u - v)`. -/
def Bpt (j : ℕ) : ℤ × ℤ := (2 * (uv j).2 - (uv j).1, 2 * (uv j).1 - (uv j).2)

/-- The odd-step frontier point `D = (2v - u, u + v)`, which is `G B`. -/
def Dpt (j : ℕ) : ℤ × ℤ := (2 * (uv j).2 - (uv j).1, (uv j).1 + (uv j).2)

/-- The odd-step frontier point `E = (u + 2v, v)`, which is `S A`. -/
def Ept (j : ℕ) : ℤ × ℤ := ((uv j).1 + 2 * (uv j).2, (uv j).2)

theorem Gm_Bpt (j : ℕ) : Gm (Bpt j) = Dpt j :=
  Prod.ext_iff.mpr ⟨by simp only [Gm, Bpt, Dpt], by simp only [Gm, Bpt, Dpt]; ring⟩

theorem Sm_Apt (j : ℕ) : Sm (Apt j) = Ept j :=
  Prod.ext_iff.mpr ⟨by simp only [Sm, Apt, Ept], by simp only [Sm, Apt, Ept]⟩

/-- `G B` beats `G A`, by `2(v - u) > 0` in the first coordinate. -/
theorem dom_Dpt_Gm_Apt (j : ℕ) : Dom (Dpt j) (Gm (Apt j)) := by
  obtain ⟨h0, h1, h2⟩ := uv_bounds j
  refine ⟨?_, ?_, Or.inl ?_⟩ <;> simp only [Dpt, Gm, Apt] <;> omega

/-- `S A` beats `S B`, by `2(v - u) > 0` in **both** coordinates. -/
theorem dom_Ept_Sm_Bpt (j : ℕ) : Dom (Ept j) (Sm (Bpt j)) := by
  obtain ⟨h0, h1, h2⟩ := uv_bounds j
  refine ⟨?_, ?_, Or.inl ?_⟩ <;> simp only [Ept, Sm, Bpt] <;> omega

theorem Gm_Ept (j : ℕ) : Gm (Ept j) = Apt (j + 1) :=
  Prod.ext_iff.mpr ⟨by simp only [Gm, Ept, Apt, uv],
    by simp only [Gm, Ept, Apt, uv]; ring⟩

theorem Sm_Dpt (j : ℕ) : Sm (Dpt j) = Bpt (j + 1) :=
  Prod.ext_iff.mpr ⟨by simp only [Sm, Dpt, Bpt, uv]; ring,
    by simp only [Sm, Dpt, Bpt, uv]; ring⟩

/-- `G E` beats `G D`, with differences `(2u, u)`. -/
theorem dom_Apt_succ_Gm_Dpt (j : ℕ) : Dom (Apt (j + 1)) (Gm (Dpt j)) := by
  obtain ⟨h0, h1, h2⟩ := uv_bounds j
  refine ⟨?_, ?_, Or.inl ?_⟩ <;> simp only [Apt, Gm, Dpt, uv] <;> omega

/-- `S D` beats `S E`, with differences `(0, u)` — strict in only ONE coordinate, which is why
`Dom` is stated with a disjunction. -/
theorem dom_Bpt_succ_Sm_Ept (j : ℕ) : Dom (Bpt (j + 1)) (Sm (Ept j)) := by
  obtain ⟨h0, h1, h2⟩ := uv_bounds j
  refine ⟨?_, ?_, Or.inr ?_⟩ <;> simp only [Bpt, Sm, Ept, uv] <;> omega

/-! ## The two survivors are incomparable, so the frontier really has two points -/

theorem incomp_Apt_Bpt (j : ℕ) : ¬ Dom (Apt j) (Bpt j) ∧ ¬ Dom (Bpt j) (Apt j) := by
  obtain ⟨h0, h1, h2⟩ := uv_bounds j
  constructor
  · rintro ⟨g1, -, -⟩
    simp only [Apt, Bpt] at g1
    omega
  · rintro ⟨-, g2, -⟩
    simp only [Apt, Bpt] at g2
    omega

theorem incomp_Dpt_Ept (j : ℕ) : ¬ Dom (Dpt j) (Ept j) ∧ ¬ Dom (Ept j) (Dpt j) := by
  obtain ⟨h0, h1, h2⟩ := uv_bounds j
  constructor
  · rintro ⟨g1, -, -⟩
    simp only [Dpt, Ept] at g1
    omega
  · rintro ⟨-, g2, -⟩
    simp only [Dpt, Ept] at g2
    omega

/-! ## Coordinate sums: multiplicity two at even steps, one at odd steps -/

/-- The coordinate sum, which is `2n + 1` for a point in row `n`. -/
def csum (p : ℤ × ℤ) : ℤ := p.1 + p.2

/-- **Multiplicity two at even steps:** the two frontier points have the SAME sum. -/
theorem csum_Apt_eq_Bpt (j : ℕ) : csum (Apt j) = csum (Bpt j) := by
  simp only [csum, Apt, Bpt]
  ring

/-- **Multiplicity one at odd steps:** the two frontier points have DIFFERENT sums, and `E` wins,
by `u > 0`. -/
theorem csum_Dpt_lt_Ept (j : ℕ) : csum (Dpt j) < csum (Ept j) := by
  obtain ⟨h0, h1, h2⟩ := uv_bounds j
  simp only [csum, Dpt, Ept]
  omega

theorem csum_Apt (j : ℕ) : csum (Apt j) = (uv j).1 + (uv j).2 := rfl

theorem csum_Ept (j : ℕ) : csum (Ept j) = (uv j).1 + 3 * (uv j).2 := by
  simp only [csum, Ept]
  ring

/-! ## The recurrence -/

/-- The update matrix has trace `4` and determinant `1`, so `P² = 4P - I` and every linear form in
its iterates satisfies `z_{j+2} = 4 z_{j+1} - z_j`. -/
theorem uv_rec (j : ℕ) :
    (uv (j + 2)).1 = 4 * (uv (j + 1)).1 - (uv j).1 ∧
      (uv (j + 2)).2 = 4 * (uv (j + 1)).2 - (uv j).2 := by
  constructor <;> simp only [uv] <;> ring

/-- The maximal row at even step `2j`. -/
def rowEven (j : ℕ) : ℤ := ((uv j).1 + (uv j).2 - 1) / 2

/-- The maximal row at odd step `2j+1`. -/
def rowOdd (j : ℕ) : ℤ := ((uv j).1 + 3 * (uv j).2 - 1) / 2

theorem two_mul_rowEven (j : ℕ) : 2 * rowEven j + 1 = (uv j).1 + (uv j).2 := by
  obtain ⟨h0, h1⟩ := uv_parity j
  simp only [rowEven]
  omega

theorem two_mul_rowOdd (j : ℕ) : 2 * rowOdd j + 1 = (uv j).1 + 3 * (uv j).2 := by
  obtain ⟨h0, h1⟩ := uv_parity j
  simp only [rowOdd]
  omega

/-- **The conjecture's recurrence, even parity:** `r_{j+2} = 4 r_{j+1} - r_j + 1`. -/
theorem rowEven_rec (j : ℕ) : rowEven (j + 2) = 4 * rowEven (j + 1) - rowEven j + 1 := by
  obtain ⟨e1, e2⟩ := uv_rec j
  have h0 := two_mul_rowEven j
  have h1 := two_mul_rowEven (j + 1)
  have h2 := two_mul_rowEven (j + 2)
  omega

/-- **The conjecture's recurrence, odd parity.** -/
theorem rowOdd_rec (j : ℕ) : rowOdd (j + 2) = 4 * rowOdd (j + 1) - rowOdd j + 1 := by
  obtain ⟨e1, e2⟩ := uv_rec j
  have h0 := two_mul_rowOdd j
  have h1 := two_mul_rowOdd (j + 1)
  have h2 := two_mul_rowOdd (j + 2)
  omega

/-- The first values, against the write-up's own: `r₂ = 2`, `r₃ = 5`, `r₄ = 9`, `r₅ = 20`, and
Example 6.6's Step 6 with `(u,v) = (30,41)` and maximal row `35`.

**Mind the offset:** `uv j` drives Step `2(j+1)`, because the write-up's Lemma indexes the frontier
at Step `2j` by `M^(j-1)`. So Example 6.6's Step 6 is `uv 2`, not `uv 3`. This check is in the file
because it caught exactly that off-by-one when the constants were first copied across. -/
theorem row_values :
    rowEven 0 = 2 ∧ rowOdd 0 = 5 ∧ rowEven 1 = 9 ∧ rowOdd 1 = 20 ∧
      uv 2 = (30, 41) ∧ rowEven 2 = 35 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [rowEven, rowOdd, uv]

/-! ## Stage 2: the generations, the covering induction, and the conjecture itself

The write-up's "children of previously dominated points remain strictly dominated" is
`covered`, an induction on the PARITY PAIR: the even frontier gives the odd one and the odd
one gives the next even. Everything else follows from it. -/

/-- The generation at Step `i`, in the write-up's `(a,b)` coordinates. `Cg 1 = {(2,1)}` is the
seed, so `Cg i` is literally "the generation at Step `i`" with no offset to remember. -/
def Cg : ℕ → Finset (ℤ × ℤ)
  | 0 => ∅
  | 1 => {(2, 1)}
  | (i + 2) => (Cg (i + 1)).image Gm ∪ (Cg (i + 1)).image Sm

theorem Cg_succ (i : ℕ) :
    Cg (i + 2) = (Cg (i + 1)).image Gm ∪ (Cg (i + 1)).image Sm := rfl

/-- Strict domination is transitive. -/
theorem dom_trans {x y z : ℤ × ℤ} (h1 : Dom x y) (h2 : Dom y z) : Dom x z := by
  obtain ⟨a1, a2, a3⟩ := h1
  obtain ⟨b1, b2, b3⟩ := h2
  refine ⟨le_trans b1 a1, le_trans b2 a2, ?_⟩
  rcases b3 with h | h
  · exact Or.inl (lt_of_lt_of_le h a1)
  · exact Or.inr (lt_of_lt_of_le h a2)

/-- Strict domination strictly decreases the coordinate sum, which is what turns the frontier into
a statement about the extremal ROW. -/
theorem dom_csum {x y : ℤ × ℤ} (h : Dom x y) : csum y < csum x := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [csum]
  rcases h3 with h | h <;> omega

/-- Every point of `s` is one of `x`, `y`, or strictly dominated by one of them. -/
def CoveredBy (s : Finset (ℤ × ℤ)) (x y : ℤ × ℤ) : Prop :=
  ∀ p ∈ s, p = x ∨ p = y ∨ Dom x p ∨ Dom y p

theorem covered_step_even {s : Finset (ℤ × ℤ)} {j : ℕ} (h : CoveredBy s (Apt j) (Bpt j)) :
    CoveredBy (s.image Gm ∪ s.image Sm) (Dpt j) (Ept j) := by
  intro q hq
  rcases Finset.mem_union.mp hq with hg | hs
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hg
    rcases h p hp with rfl | rfl | hd | hd
    · exact Or.inr (Or.inr (Or.inl (dom_Dpt_Gm_Apt j)))
    · exact Or.inl (Gm_Bpt j)
    · exact Or.inr (Or.inr (Or.inl (dom_trans (dom_Dpt_Gm_Apt j) (dom_Gm hd))))
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [← Gm_Bpt j]
      exact dom_Gm hd
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
    rcases h p hp with rfl | rfl | hd | hd
    · exact Or.inr (Or.inl (Sm_Apt j))
    · exact Or.inr (Or.inr (Or.inr (dom_Ept_Sm_Bpt j)))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [← Sm_Apt j]
      exact dom_Sm hd
    · exact Or.inr (Or.inr (Or.inr (dom_trans (dom_Ept_Sm_Bpt j) (dom_Sm hd))))

theorem covered_step_odd {s : Finset (ℤ × ℤ)} {j : ℕ} (h : CoveredBy s (Dpt j) (Ept j)) :
    CoveredBy (s.image Gm ∪ s.image Sm) (Apt (j + 1)) (Bpt (j + 1)) := by
  intro q hq
  rcases Finset.mem_union.mp hq with hg | hs
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hg
    rcases h p hp with rfl | rfl | hd | hd
    · exact Or.inr (Or.inr (Or.inl (dom_Apt_succ_Gm_Dpt j)))
    · exact Or.inl (Gm_Ept j)
    · exact Or.inr (Or.inr (Or.inl (dom_trans (dom_Apt_succ_Gm_Dpt j) (dom_Gm hd))))
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [← Gm_Ept j]
      exact dom_Gm hd
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
    rcases h p hp with rfl | rfl | hd | hd
    · exact Or.inr (Or.inl (Sm_Dpt j))
    · exact Or.inr (Or.inr (Or.inr (dom_Bpt_succ_Sm_Ept j)))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [← Sm_Dpt j]
      exact dom_Sm hd
    · exact Or.inr (Or.inr (Or.inr (dom_trans (dom_Bpt_succ_Sm_Ept j) (dom_Sm hd))))

/-- **The write-up's "no other maximal points occur", by induction on the parity pair.** -/
theorem covered (j : ℕ) :
    CoveredBy (Cg (2 * j + 2)) (Apt j) (Bpt j) ∧
      CoveredBy (Cg (2 * j + 3)) (Dpt j) (Ept j) := by
  induction j with
  | zero =>
    have h1 : CoveredBy (Cg (2 * 0 + 2)) (Apt 0) (Bpt 0) := by
      intro p hp
      have e : Cg 2 = (Cg 1).image Gm ∪ (Cg 1).image Sm := Cg_succ 0
      rw [show (2 * 0 + 2 : ℕ) = 2 from by norm_num, e] at hp
      simp only [Cg, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hp
      rcases hp with ⟨a, ha, hpa⟩ | ⟨a, ha, hpa⟩
      · subst ha; subst hpa
        exact Or.inl (by simp [Gm, Apt, uv])
      · subst ha; subst hpa
        exact Or.inr (Or.inl (by simp [Sm, Bpt, uv]))
    refine ⟨h1, ?_⟩
    have e : Cg (2 * 0 + 3) = (Cg (2 * 0 + 2)).image Gm ∪ (Cg (2 * 0 + 2)).image Sm := by
      rw [show (2 * 0 + 3 : ℕ) = 1 + 2 from by norm_num,
        show (2 * 0 + 2 : ℕ) = 1 + 1 from by norm_num]
      exact Cg_succ 1
    rw [e]
    exact covered_step_even h1
  | succ i ih =>
    have e1 : (2 * (i + 1) + 2 : ℕ) = (2 * i + 2) + 2 := by omega
    have e2 : ((2 * i + 2) + 1 : ℕ) = 2 * i + 3 := by omega
    have h1 : CoveredBy (Cg (2 * (i + 1) + 2)) (Apt (i + 1)) (Bpt (i + 1)) := by
      rw [e1, Cg_succ, e2]
      exact covered_step_odd ih.2
    refine ⟨h1, ?_⟩
    have e3 : (2 * (i + 1) + 3 : ℕ) = (2 * (i + 1) + 1) + 2 := by omega
    have e4 : ((2 * (i + 1) + 1) + 1 : ℕ) = 2 * (i + 1) + 2 := by omega
    rw [e3, Cg_succ, e4]
    exact covered_step_even h1

/-- The four frontier points really are members of their generations. -/
theorem mem_frontier (j : ℕ) :
    Apt j ∈ Cg (2 * j + 2) ∧ Bpt j ∈ Cg (2 * j + 2) ∧
      Dpt j ∈ Cg (2 * j + 3) ∧ Ept j ∈ Cg (2 * j + 3) := by
  induction j with
  | zero =>
    have e2 : Cg (2 * 0 + 2) = (Cg 1).image Gm ∪ (Cg 1).image Sm := by
      rw [show (2 * 0 + 2 : ℕ) = 0 + 2 from by norm_num]
      exact Cg_succ 0
    have e3 : Cg (2 * 0 + 3) = (Cg (2 * 0 + 2)).image Gm ∪ (Cg (2 * 0 + 2)).image Sm := by
      rw [show (2 * 0 + 3 : ℕ) = 1 + 2 from by norm_num,
        show (2 * 0 + 2 : ℕ) = 1 + 1 from by norm_num]
      exact Cg_succ 1
    have hA : Apt 0 ∈ Cg (2 * 0 + 2) := by
      rw [e2]
      refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(2, 1), ?_, ?_⟩)
      · simp [Cg]
      · simp [Gm, Apt, uv]
    have hB : Bpt 0 ∈ Cg (2 * 0 + 2) := by
      rw [e2]
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(2, 1), ?_, ?_⟩)
      · simp [Cg]
      · simp [Sm, Bpt, uv]
    refine ⟨hA, hB, ?_, ?_⟩
    · rw [e3, ← Gm_Bpt 0]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem Gm hB)
    · rw [e3, ← Sm_Apt 0]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem Sm hA)
  | succ i ih =>
    obtain ⟨-, -, hD, hE⟩ := ih
    have e1 : (2 * (i + 1) + 2 : ℕ) = (2 * i + 2) + 2 := by omega
    have e2 : ((2 * i + 2) + 1 : ℕ) = 2 * i + 3 := by omega
    have hA : Apt (i + 1) ∈ Cg (2 * (i + 1) + 2) := by
      rw [e1, Cg_succ, e2, ← Gm_Ept i]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem Gm hE)
    have hB : Bpt (i + 1) ∈ Cg (2 * (i + 1) + 2) := by
      rw [e1, Cg_succ, e2, ← Sm_Dpt i]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem Sm hD)
    have e3 : (2 * (i + 1) + 3 : ℕ) = (2 * (i + 1) + 1) + 2 := by omega
    have e4 : ((2 * (i + 1) + 1) + 1 : ℕ) = 2 * (i + 1) + 2 := by omega
    refine ⟨hA, hB, ?_, ?_⟩
    · rw [e3, Cg_succ, e4, ← Gm_Bpt (i + 1)]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem Gm hB)
    · rw [e3, Cg_succ, e4, ← Sm_Apt (i + 1)]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem Sm hA)

/-! ### The extremal row and its multiplicity -/

theorem Cg_parity (i : ℕ) : ∀ p ∈ Cg (i + 1), p.1 % 2 = 0 ∧ p.2 % 2 = 1 := by
  induction i with
  | zero =>
    intro p hp
    simp only [Cg, Finset.mem_singleton] at hp
    subst hp
    norm_num
  | succ k ih =>
    intro p hp
    rw [Cg_succ] at hp
    rcases Finset.mem_union.mp hp with hg | hs
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨h1, h2⟩ := ih q hq
      simp only [Gm]
      omega
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨h1, h2⟩ := ih q hq
      simp only [Sm]
      omega

/-- The row of a point: `a + b = 2n + 1`. -/
def rowOf (p : ℤ × ℤ) : ℤ := (csum p - 1) / 2

theorem two_mul_rowOf {p : ℤ × ℤ} (h1 : p.1 % 2 = 0) (h2 : p.2 % 2 = 1) :
    2 * rowOf p + 1 = csum p := by
  simp only [rowOf, csum]
  omega

theorem Apt_ne_Bpt (j : ℕ) : Apt j ≠ Bpt j := by
  obtain ⟨h0, h1, h2⟩ := uv_bounds j
  intro h
  have hf := congrArg Prod.fst h
  simp only [Apt, Bpt] at hf
  omega

theorem csum_le_even (j : ℕ) : ∀ p ∈ Cg (2 * j + 2), csum p ≤ csum (Apt j) := by
  intro p hp
  rcases (covered j).1 p hp with rfl | rfl | hd | hd
  · exact le_rfl
  · exact le_of_eq (csum_Apt_eq_Bpt j).symm
  · exact le_of_lt (dom_csum hd)
  · rw [csum_Apt_eq_Bpt j]
    exact le_of_lt (dom_csum hd)

theorem csum_le_odd (j : ℕ) : ∀ p ∈ Cg (2 * j + 3), csum p ≤ csum (Ept j) := by
  intro p hp
  rcases (covered j).2 p hp with rfl | rfl | hd | hd
  · exact le_of_lt (csum_Dpt_lt_Ept j)
  · exact le_rfl
  · exact le_of_lt (lt_trans (dom_csum hd) (csum_Dpt_lt_Ept j))
  · exact le_of_lt (dom_csum hd)

/-- **Multiplicity two at even steps**: exactly `Apt j` and `Bpt j` attain the maximal sum. -/
theorem extremal_even (j : ℕ) :
    (Cg (2 * j + 2)).filter (fun p => csum p = csum (Apt j)) = {Apt j, Bpt j} := by
  obtain ⟨hA, hB, -, -⟩ := mem_frontier j
  ext p
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hmem, hsum⟩
    rcases (covered j).1 p hmem with rfl | rfl | hd | hd
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hsum (by have := dom_csum hd; omega)
    · exact absurd hsum (by
        have := dom_csum hd
        have e := csum_Apt_eq_Bpt j
        omega)
  · rintro (rfl | rfl)
    · exact ⟨hA, rfl⟩
    · exact ⟨hB, (csum_Apt_eq_Bpt j).symm⟩

theorem card_extremal_even (j : ℕ) :
    ((Cg (2 * j + 2)).filter (fun p => csum p = csum (Apt j))).card = 2 := by
  rw [extremal_even j, Finset.card_insert_of_notMem (by simpa using Apt_ne_Bpt j),
    Finset.card_singleton]

/-- **Multiplicity one at odd steps**: only `Ept j` attains the maximal sum. -/
theorem extremal_odd (j : ℕ) :
    (Cg (2 * j + 3)).filter (fun p => csum p = csum (Ept j)) = {Ept j} := by
  obtain ⟨-, -, -, hE⟩ := mem_frontier j
  ext p
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hmem, hsum⟩
    rcases (covered j).2 p hmem with rfl | rfl | hd | hd
    · exact absurd hsum (by have := csum_Dpt_lt_Ept j; omega)
    · rfl
    · exact absurd hsum (by
        have := dom_csum hd
        have := csum_Dpt_lt_Ept j
        omega)
    · exact absurd hsum (by have := dom_csum hd; omega)
  · rintro rfl
    exact ⟨hE, rfl⟩

theorem card_extremal_odd (j : ℕ) :
    ((Cg (2 * j + 3)).filter (fun p => csum p = csum (Ept j))).card = 1 := by
  rw [extremal_odd j, Finset.card_singleton]

/-- **The extremal row at even Step `2j+2` is `rowEven j`**, attained and not exceeded. -/
theorem extremal_row_even (j : ℕ) :
    (∀ p ∈ Cg (2 * j + 2), rowOf p ≤ rowEven j) ∧
      ∃ p ∈ Cg (2 * j + 2), rowOf p = rowEven j := by
  obtain ⟨hA, -, -, -⟩ := mem_frontier j
  have hpA := Cg_parity (2 * j + 1) (Apt j) (by
    rw [show (2 * j + 1) + 1 = 2 * j + 2 from by omega]; exact hA)
  have hsA : 2 * rowOf (Apt j) + 1 = csum (Apt j) := two_mul_rowOf hpA.1 hpA.2
  have hrA : rowOf (Apt j) = rowEven j := by
    have := two_mul_rowEven j
    have e := csum_Apt j
    omega
  refine ⟨fun p hp => ?_, ⟨Apt j, hA, hrA⟩⟩
  have hpp := Cg_parity (2 * j + 1) p (by
    rw [show (2 * j + 1) + 1 = 2 * j + 2 from by omega]; exact hp)
  have hsp : 2 * rowOf p + 1 = csum p := two_mul_rowOf hpp.1 hpp.2
  have := csum_le_even j p hp
  omega

/-- **The extremal row at odd Step `2j+3` is `rowOdd j`**, attained and not exceeded. -/
theorem extremal_row_odd (j : ℕ) :
    (∀ p ∈ Cg (2 * j + 3), rowOf p ≤ rowOdd j) ∧
      ∃ p ∈ Cg (2 * j + 3), rowOf p = rowOdd j := by
  obtain ⟨-, -, -, hE⟩ := mem_frontier j
  have hpE := Cg_parity (2 * j + 2) (Ept j) (by
    rw [show (2 * j + 2) + 1 = 2 * j + 3 from by omega]; exact hE)
  have hsE : 2 * rowOf (Ept j) + 1 = csum (Ept j) := two_mul_rowOf hpE.1 hpE.2
  have hrE : rowOf (Ept j) = rowOdd j := by
    have := two_mul_rowOdd j
    have e := csum_Ept j
    omega
  refine ⟨fun p hp => ?_, ⟨Ept j, hE, hrE⟩⟩
  have hpp := Cg_parity (2 * j + 2) p (by
    rw [show (2 * j + 2) + 1 = 2 * j + 3 from by omega]; exact hp)
  have hsp : 2 * rowOf p + 1 = csum p := two_mul_rowOf hpp.1 hpp.2
  have := csum_le_odd j p hp
  omega

/-! ### The two OEIS sequences, defined by the recurrence their entries cite -/

/-- A001571, as the write-up's citation defines it. -/
def A001571 : ℕ → ℤ
  | 0 => 0
  | 1 => 2
  | (j + 2) => 4 * A001571 (j + 1) - A001571 j + 1

/-- A061278, as the write-up's citation defines it. -/
def A061278 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (j + 2) => 4 * A061278 (j + 1) - A061278 j + 1

theorem rowEven_eq (j : ℕ) : rowEven j = A001571 (j + 1) := by
  induction j using Nat.twoStepInduction with
  | zero => norm_num [rowEven, uv, A001571]
  | one => norm_num [rowEven, uv, A001571]
  | more i ih1 ih2 =>
    rw [rowEven_rec i, ih1, ih2]
    simp only [A001571]

theorem rowOdd_eq (j : ℕ) : rowOdd j = A061278 (j + 2) := by
  induction j using Nat.twoStepInduction with
  | zero => norm_num [rowOdd, uv, A061278]
  | one => norm_num [rowOdd, uv, A061278]
  | more i ih1 ih2 =>
    rw [rowOdd_rec i, ih1, ih2]
    simp only [A061278]

/-- Step 1 has a single point, in row 1 -- the case the write-up notes separately. -/
theorem step_one : Cg 1 = {(2, 1)} ∧ rowOf ((2, 1) : ℤ × ℤ) = 1 := by
  refine ⟨rfl, ?_⟩
  norm_num [rowOf, csum]

/-! ### The generations are disjoint unions, so the tree enumerates distinct entries -/

theorem Cg_pos (i : ℕ) : ∀ p ∈ Cg (i + 1), 0 < p.1 ∧ 0 < p.2 := by
  induction i with
  | zero =>
    intro p hp
    simp only [Cg, Finset.mem_singleton] at hp
    subst hp
    norm_num
  | succ k ih =>
    intro p hp
    rw [Cg_succ] at hp
    rcases Finset.mem_union.mp hp with hg | hs
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨h1, h2⟩ := ih q hq
      simp only [Gm]
      omega
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨h1, h2⟩ := ih q hq
      simp only [Sm]
      omega

/-- A `Gm`-image lies in the cone `b > a`. -/
theorem Gm_cone {p : ℤ × ℤ} (h : 0 < p.2) : (Gm p).1 < (Gm p).2 := by
  simp only [Gm]; omega

/-- An `Sm`-image lies in the cone `a > 2b`. -/
theorem Sm_cone {p : ℤ × ℤ} (h : 0 < p.1) : 2 * (Sm p).2 < (Sm p).1 := by
  simp only [Sm]; omega

theorem Gm_inj : Function.Injective Gm := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Gm] at h1 h2
  exact Prod.ext_iff.mpr ⟨h1, by omega⟩

theorem Sm_inj : Function.Injective Sm := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Sm] at h1 h2
  exact Prod.ext_iff.mpr ⟨by omega, h2⟩

/-- **The two image cones are disjoint**, which is the write-up's reason the tree enumerates
distinct entries. -/
theorem Cg_disjoint (i : ℕ) :
    Disjoint ((Cg (i + 1)).image Gm) ((Cg (i + 1)).image Sm) := by
  rw [Finset.disjoint_left]
  intro q hg hs
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
  obtain ⟨y, hy, hyq⟩ := Finset.mem_image.mp hs
  have hxp := Cg_pos i x hx
  have hyp := Cg_pos i y hy
  have h1 := Gm_cone hxp.2
  have h2 := Sm_cone hyp.1
  rw [hyq] at h2
  have h3 : 0 < (Gm x).2 := by simp only [Gm]; omega
  omega

/-- **The generation at Step `i+1` has `2^i` elements.** -/
theorem card_Cg (i : ℕ) : (Cg (i + 1)).card = 2 ^ i := by
  induction i with
  | zero => simp [Cg]
  | succ k ih =>
    rw [Cg_succ, Finset.card_union_of_disjoint (Cg_disjoint k),
      Finset.card_image_of_injective _ Gm_inj, Finset.card_image_of_injective _ Sm_inj, ih]
    ring

/-! ### The conjecture, assembled in terms of ROWS -/

theorem filter_row_even (j : ℕ) :
    (Cg (2 * j + 2)).filter (fun p => rowOf p = rowEven j)
      = (Cg (2 * j + 2)).filter (fun p => csum p = csum (Apt j)) := by
  refine Finset.filter_congr fun p hp => ?_
  have hpp := Cg_parity (2 * j + 1) p (by
    rw [show (2 * j + 1) + 1 = 2 * j + 2 from by omega]; exact hp)
  have hsp := two_mul_rowOf hpp.1 hpp.2
  have hr := two_mul_rowEven j
  have he := csum_Apt j
  constructor <;> intro h <;> omega

theorem filter_row_odd (j : ℕ) :
    (Cg (2 * j + 3)).filter (fun p => rowOf p = rowOdd j)
      = (Cg (2 * j + 3)).filter (fun p => csum p = csum (Ept j)) := by
  refine Finset.filter_congr fun p hp => ?_
  have hpp := Cg_parity (2 * j + 2) p (by
    rw [show (2 * j + 2) + 1 = 2 * j + 3 from by omega]; exact hp)
  have hsp := two_mul_rowOf hpp.1 hpp.2
  have hr := two_mul_rowOdd j
  have he := csum_Ept j
  constructor <;> intro h <;> omega

/-- **Castronuovo's Conjecture 6.5, assembled.** For every `j`: the maximal row of the generation
at Step `2j+2` is `A001571 (j+1)` and exactly TWO of its points attain it; the maximal row at Step
`2j+3` is `A061278 (j+2)` and exactly ONE point attains it. -/
theorem conjecture_6_5 (j : ℕ) :
    (∀ p ∈ Cg (2 * j + 2), rowOf p ≤ A001571 (j + 1)) ∧
      (∃ p ∈ Cg (2 * j + 2), rowOf p = A001571 (j + 1)) ∧
      ((Cg (2 * j + 2)).filter (fun p => rowOf p = A001571 (j + 1))).card = 2 ∧
      (∀ p ∈ Cg (2 * j + 3), rowOf p ≤ A061278 (j + 2)) ∧
      (∃ p ∈ Cg (2 * j + 3), rowOf p = A061278 (j + 2)) ∧
      ((Cg (2 * j + 3)).filter (fun p => rowOf p = A061278 (j + 2))).card = 1 := by
  obtain ⟨hle, hex⟩ := extremal_row_even j
  obtain ⟨hle', hex'⟩ := extremal_row_odd j
  rw [← rowEven_eq j]
  rw [← rowOdd_eq j]
  exact ⟨hle, hex, by rw [filter_row_even j]; exact card_extremal_even j,
    hle', hex', by rw [filter_row_odd j]; exact card_extremal_odd j⟩
end Principia.MathDB.P349635
