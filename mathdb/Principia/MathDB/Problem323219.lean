import Principia.Common.FinsetReindex

set_option autoImplicit false

/-!
# MathDB #323219 — integrality of the α-triangle

Write-up `mathdb-open-problems/problems/323219/solution.tex` on the `mathdb-results` branch
of `antoshashakov/Principia-Math-In-Progress`.
Source: S. Govindarajan, *Notes on higher-dimensional partitions*, arXiv:1203.4419v1 (2012),
**Conjecture 3.1**, p. 16 (published: JCTA **120** (2013) 600–622).

Govindarajan defines coefficients `α_{m,z}` by

    a_{m+r+1,r} = (1/(2m)!!) · ∑_{z=0}^{2m} α_{m,z} · r^{2m-z},      (2m)!! = 2^m · m!,

and conjectures every `α_{m,z}` is an integer — equivalently that `2^m · m! · a_{m+r+1,r}`
lies in `ℤ[r]`.

## The objects

A **Ferrers diagram** in `ℕ^r` is a finite lower set for the coordinatewise order; it is
**strict** when it uses every coordinate, hence contains `μ_r = {0, e₁, …, e_r}`.  The
write-up's `a_{m+r+1,r}` counts the strict diagrams obtained by adding `m` nodes to `μ_r`;
every added node then automatically has coordinate sum `≥ 2`, since `μ_r` already holds
every point of sum `≤ 1`.

**This module states the theorem over the combinatorial definition**, which is what the
write-up actually proves.  Govindarajan's own generating-function definition of the
α-triangle is tied to this count in [G] §2.2–2.5, which the write-up imports rather than
reproves; that bridge is therefore an interface, recorded here and not formalised.

## The decomposition — three links, ALL PROVED

* **(A) `ReductionBijection`** — `a_{m+r+1,r} = ∑_{k≤2m} C(r,k) · d_{m,k}`, where `d_{m,k}`
  counts the *reduced* configurations: `S ⊆ ℕ^k` with `|S| = m`, every coordinate used, and
  `μ_k ∪ S` a diagram.  One chooses which `k` of the `r` coordinates the added nodes use.
  Purely a bijection — no group theory at all.  **PROVED**, as `reductionBijection`.
* **(B) `AutDivisibility`** — `k! ∣ 2^m · m! · d_{m,k}` for `k ≤ 2m`.  This is where the
  write-up's automorphism argument lives: orbit–stabiliser writes
  `d_{m,k} = ∑_{orbits} k!/|Aut S|`, and a lemma gives `|Aut S| ∣ 2^m m!`.  **PROVED**, as
  `autDivisibility` — but NOT by the write-up's reason, which is false (see the section on
  link (B) below), and the repaired argument does not need the bound `k ≤ 2m` at all.
* **(C) the assembly** — PROVED here, as `integrality`.

**(B) is load-bearing and cannot be dropped.**  (A) alone shows only that `a` is an
integer-VALUED polynomial in `r`, which is strictly weaker than integer coefficients;
`k! ∤ 2^m m!` already at `m = 2, k = 4` (`24 ∤ 8`) and at `m = 3, k = 6` (`720 ∤ 48`).  The
assembly turns the two into the conjecture by expanding in the falling-factorial basis,
where `descPochhammer ℤ k` is monic of degree `k` and evaluates to `r.descFactorial k`.

## What is NOT proved here

**Nothing is carried: the module has no hypotheses left.**  All three of the write-up's
clauses are theorems — `alpha_integral_final` (the polynomial exists and has integer
coefficients), `alpha_isInt` (hence every `α_{m,z}` is an integer, the conjecture in the
source's own terms) and `alpha_nonneg_combination` (the coefficients in the falling-factorial
basis are nonnegative).

**Nothing remains outside Lean, and the correction is worth recording.**  This section
previously said the row rested on a literature identification — that Govindarajan *"defines
`a_{n,r}` by a generating function"* and that [G] §2.2–2.5 identifies it with the diagram
count.  **Read at the source, that is wrong: `a_{n,r}` is DEFINED as the diagram count**, by
equation (2.3), *"`a_{n,r}` as the sum over all strict FD's with `n` nodes and i.d. `r`"*.
[G]'s definitions of intrinsic dimension and strictness are now formalised verbatim, and
`mem_diagrams_iff_strict` proves `diagrams m r` IS the set of strict Ferrers diagrams with
`m + r + 1` nodes.  `aCount_eq_weighted_class_sum` covers the other reading of (2.3) — a sum
of [G]'s weights `r!/ord(H)` over gFD classes — by orbit–stabiliser, so the row does not turn
on which is meant.  Equation (3.1), `a_{m+r+1,r} = (∑_z α_{m,z} r^{2m-z})/(2m)!!`, is exactly
the relation `alpha_isInt` consumes.

**The general lesson, and it cost this row a fortnight of "interface" status:** an
unformalised interface is sometimes an unread source.  The write-up's phrase *"prior results
in [G] §2.2–2.5"* is a citation, not a difficulty rating, and it was read as the latter.

**#374964 is NOT the same case, and the difference is now visible.**  Its residue is Ehrhart
theory — the `h*`-polynomial of a polytope, an object Mathlib does not have — so its Lean
statement genuinely reaches the source only through absent mathematics.  Here the source's
own definition is the one the module uses.

## Why this row is being opened

Its triage said the write-up imports "prior results in [G] §2.2–2.5" and was filed without
the source being read.  Read, the proof is elementary throughout — the deepest tool it uses
is orbit–stabiliser — and the imported material disappears entirely once the theorem is
stated over the combinatorial definition, which is what [G] §2.2–2.5 exists to license.

Values checked first, by exact enumeration, in `Campaigns/MathDB-Formalization/verify_323219.py`:
(A) for all `m ≤ 3`, `r ≤ 6`; (B) for all `m ≤ 3`, `k ≤ 2m`; and the assembled polynomials
`2^m m! · a = 1`, `r² + r`, `r⁴ + 2r³ - r² + 6r`, `r⁶ + 3r⁵ - 3r⁴ + 13r³ + 74r² - 40r`.
-/

namespace Principia.MathDB.P323219

open Finset
open Principia.Common.FinsetReindex

/-- A **Ferrers diagram** in `ℕ^r`: a finite lower set for the coordinatewise order. -/
def IsDiagram (r : ℕ) (D : Finset (Fin r → ℕ)) : Prop :=
  ∀ x ∈ D, ∀ y : Fin r → ℕ, y ≤ x → y ∈ D

/-- `μ_r = {0, e₁, …, e_r}`, the minimal strict diagram. -/
def mu (r : ℕ) : Finset (Fin r → ℕ) :=
  insert 0 (Finset.univ.image (fun i : Fin r => Pi.single i 1))

/-- `μ_r` really is a diagram: below `e_i` there is only `0`. -/
theorem isDiagram_mu (r : ℕ) : IsDiagram r (mu r) := by
  intro x hx y hxy
  simp only [mu, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
  rcases hx with rfl | ⟨i, rfl⟩
  · left
    exact funext fun j => Nat.le_zero.mp (hxy j)
  · -- `y ≤ e_i` forces `y j = 0` off `i` and `y i ≤ 1`; then `y ≠ 0` forces `y i = 1`
    have hoff : ∀ j, j ≠ i → y j = 0 := by
      intro j hj
      have h := hxy j
      rw [Pi.single_apply, if_neg hj] at h
      exact Nat.le_zero.mp h
    by_cases hy : y = 0
    · exact Or.inl hy
    · right
      refine ⟨i, funext fun j => ?_⟩
      have h0 : y i ≠ 0 := by
        intro h
        refine hy (funext fun l => ?_)
        rcases eq_or_ne l i with rfl | hl
        · exact h
        · exact hoff l hl
      rcases eq_or_ne j i with rfl | hj
      · have h1 : y j ≤ 1 := by simpa using hxy j
        simp only [Pi.single_eq_same]
        omega
      · rw [Pi.single_apply, if_neg hj]
        exact (hoff j hj).symm

/-- The strict diagrams obtained by adding `m` nodes to `μ_r` — the write-up's
`a_{m+r+1,r}` counts exactly these. -/
def diagrams (m r : ℕ) : Set (Finset (Fin r → ℕ)) :=
  {D | IsDiagram r D ∧ mu r ⊆ D ∧ D.card = m + r + 1}

/-- `a_{m+r+1,r}`. -/
noncomputable def aCount (m r : ℕ) : ℕ := Nat.card (diagrams m r)

/-- The **reduced** configurations on exactly `k` coordinates: `m` added nodes, every
coordinate genuinely used, and `μ_k ∪ S` still a diagram. -/
def reduced (m k : ℕ) : Set (Finset (Fin k → ℕ)) :=
  {S | IsDiagram k (mu k ∪ S) ∧ Disjoint (mu k) S ∧ S.card = m ∧
       ∀ i : Fin k, ∃ p ∈ S, p i ≠ 0}

/-- `d_{m,k}`. -/
noncomputable def dCount (m k : ℕ) : ℕ := Nat.card (reduced m k)

/-- The write-up's normaliser `(2m)!! = 2^m · m!`. -/
def normalizer (m : ℕ) : ℕ := 2 ^ m * m.factorial

/-! ### The two carried links -/

/-- **(A) The reduction bijection.**  Choose which `k` of the `r` coordinates the added
nodes use, then a reduced configuration on them.

**The write-up's stated reason for the bound `k ≤ 2m` does NOT work**, and the real one is
different.

The write-up says "every added node has coordinate sum `≥ 2`, so `m` nodes can touch at most
`2m` coordinates".  That does not follow: one node `e₁+e₂+e₃` has coordinate sum `3` and
touches `3` coordinates, so bounding by total coordinate sum bounds nothing useful.

The bound is true for a different reason, and it is the LOWER-SET property doing the work
rather than the sums.  If `p ∈ S` has two nonzero coordinates `i ≠ j` then `e_i + e_j ≤ p`
lies in `μ_k ∪ S` and is not in `μ_k`, so `e_i + e_j ∈ S`.  Hence every used coordinate is
witnessed by an element of `S` that is either a pair `e_i + e_j` or a `c·e_i`, and that
witness map is at most 2-to-1, giving `k ≤ 2|S| = 2m`.  Checked over 613 coordinate-witness
pairs in `Campaigns/MathDB-Formalization/verify_323219_support.py`, together with the
tightness `d_{m,2m} = 1, 3, 15 = (2m−1)!!`. -/
def ReductionBijection : Prop :=
  ∀ m r : ℕ, aCount m r = ∑ k ∈ Finset.range (2 * m + 1), r.choose k * dCount m k

/-- **(B) The automorphism-order divisibility.**  `d_{m,k} = ∑_{orbits} k!/|Aut S|` by
orbit–stabiliser, and the write-up's graph lemma gives `|Aut S| ∣ 2^m m!`. -/
def AutDivisibility : Prop :=
  ∀ m k : ℕ, k ≤ 2 * m → k.factorial ∣ normalizer m * dCount m k

/-! ### (C) The assembly — proved

Expanding in the falling-factorial basis is what converts "integer-valued" into "integer
coefficients": `descPochhammer ℤ k` is a genuine element of `ℤ[X]`, and
`k! · C(r,k) = r.descFactorial k` is exactly how (B)'s quotient meets (A)'s binomial. -/

/-- The integer coefficient of the `k`-th falling factorial, `2^m m! d_{m,k} / k!`. -/
noncomputable def qCoeff (m k : ℕ) : ℤ := (normalizer m * dCount m k : ℤ) / (k.factorial : ℤ)

theorem qCoeff_spec (hB : AutDivisibility) (m k : ℕ) (hk : k ≤ 2 * m) :
    (k.factorial : ℤ) * qCoeff m k = (normalizer m * dCount m k : ℤ) := by
  have h : (k.factorial : ℤ) ∣ (normalizer m * dCount m k : ℤ) := by
    exact_mod_cast Int.natCast_dvd_natCast.mpr (hB m k hk)
  rw [qCoeff, Int.mul_ediv_cancel' h]

/-- The assembled polynomial `P_m = ∑_{k≤2m} q_{m,k} · (r)_k ∈ ℤ[X]`. -/
noncomputable def Pm (m : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (2 * m + 1), Polynomial.C (qCoeff m k) * descPochhammer ℤ k

theorem Pm_natDegree_le (m : ℕ) : (Pm m).natDegree ≤ 2 * m := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun k hk => ?_)
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  rw [Polynomial.natDegree_C, zero_add, descPochhammer_natDegree]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)

theorem Pm_eval (hB : AutDivisibility) (m r : ℕ) :
    (Pm m).eval (r : ℤ)
      = ∑ k ∈ Finset.range (2 * m + 1), (normalizer m : ℤ) * (r.choose k * dCount m k : ℕ) := by
  rw [Pm, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ 2 * m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_descFactorial]
  have hd : (r.descFactorial k : ℤ) = (k.factorial : ℤ) * (r.choose k : ℤ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.descFactorial_eq_factorial_mul_choose r k)
  rw [hd]
  push_cast
  linear_combination (r.choose k : ℤ) * qCoeff_spec hB m k hk'

/-- **The conjecture, from the two links.**  `2^m · m! · a_{m+r+1,r}` is the evaluation of
an INTEGER polynomial of degree at most `2m`, so every `α_{m,z}` is an integer. -/
theorem integrality (hA : ReductionBijection) (hB : AutDivisibility) (m : ℕ) :
    (Pm m).natDegree ≤ 2 * m ∧
      ∀ r : ℕ, (Pm m).eval (r : ℤ) = (normalizer m : ℤ) * (aCount m r : ℤ) := by
  refine ⟨Pm_natDegree_le m, fun r => ?_⟩
  rw [Pm_eval hB m r, hA m r]
  push_cast
  rw [Finset.mul_sum]

/-- The conjecture in the write-up's own words: there is a polynomial with INTEGER
coefficients whose values are `(2m)!! · a_{m+r+1,r}`. -/
theorem alpha_integral (hA : ReductionBijection) (hB : AutDivisibility) (m : ℕ) :
    ∃ P : Polynomial ℤ, P.natDegree ≤ 2 * m ∧
      ∀ r : ℕ, P.eval (r : ℤ) = (normalizer m : ℤ) * (aCount m r : ℤ) :=
  ⟨Pm m, integrality hA hB m⟩

/-! ### The support bound `k ≤ 2m`, and why the write-up's reason for it does not work

`ReductionBijection` sums over `k ≤ 2m`, so it is only correct if `reduced m k` is empty
beyond that.  The write-up's one-line justification — "every added node has coordinate sum
`≥ 2`" — does NOT give the bound (one node `e₁+e₂+e₃` has coordinate sum 3 and touches 3
coordinates).  What does give it is the LOWER-SET property: a node with two nonzero
coordinates forces the pair `e_i + e_j` into `S`, so every used coordinate has a witness in
`S` with at most two nonzero coordinates, and that witness map is at most 2-to-1. -/

/-- A point with two distinct nonzero coordinates is not in `μ_k`: every element of `μ_k`
is `0` or some `e_l`, and neither has two nonzero coordinates. -/
theorem pair_not_mem_mu {k : ℕ} {q : Fin k → ℕ} {i j : Fin k} (hij : i ≠ j)
    (hi : q i ≠ 0) (hj : q j ≠ 0) : q ∉ mu k := by
  simp only [mu, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
  rintro (rfl | ⟨l, rfl⟩)
  · exact hi rfl
  · rcases eq_or_ne l i with rfl | hli
    · rw [Pi.single_apply, if_neg (Ne.symm hij)] at hj
      exact hj rfl
    · rw [Pi.single_apply, if_neg (Ne.symm hli)] at hi
      exact hi rfl

/-- **The pair is forced into `S`.**  If `p ∈ S` has two nonzero coordinates `i ≠ j`, then
`e_i + e_j ≤ p` lies in the lower set `μ_k ∪ S`, and it is not in `μ_k`, so it is in `S`.
*This* is what bounds the support — not the coordinate sums the write-up cites. -/
theorem pair_mem {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k)
    {p : Fin k → ℕ} (hp : p ∈ S) {i j : Fin k} (hij : i ≠ j)
    (hi : p i ≠ 0) (hj : p j ≠ 0) :
    (Pi.single i 1 + Pi.single j 1 : Fin k → ℕ) ∈ S := by
  obtain ⟨hdiag, -, -, -⟩ := hS
  have hi' : 1 ≤ p i := Nat.one_le_iff_ne_zero.mpr hi
  have hj' : 1 ≤ p j := Nat.one_le_iff_ne_zero.mpr hj
  have hle : (Pi.single i 1 + Pi.single j 1 : Fin k → ℕ) ≤ p := by
    intro l
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs with h1 h2 h2
    · exact absurd (h1.symm.trans h2) hij
    · subst h1; omega
    · subst h2; omega
    · omega
  have hqi : (Pi.single i 1 + Pi.single j 1 : Fin k → ℕ) i ≠ 0 := by
    simp [hij]
  have hqj : (Pi.single i 1 + Pi.single j 1 : Fin k → ℕ) j ≠ 0 := by
    simp [Ne.symm hij]
  have hmem : p ∈ mu k ∪ S := Finset.mem_union_right _ hp
  have h2 := hdiag p hmem _ hle
  rcases Finset.mem_union.mp h2 with hbad | hgood
  · exact absurd hbad (pair_not_mem_mu hij hqi hqj)
  · exact hgood

/-- The witness attached to coordinate `i`: the pair `e_i + e_j` when the chosen point has a
second nonzero coordinate `j`, and the point itself otherwise. -/
noncomputable def wit {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k)
    (i : Fin k) : Fin k → ℕ :=
  if h : ∃ j, j ≠ i ∧ (hS.2.2.2 i).choose j ≠ 0 then
    (Pi.single i 1 + Pi.single h.choose 1 : Fin k → ℕ)
  else (hS.2.2.2 i).choose

theorem wit_mem {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k) (i : Fin k) :
    wit hS i ∈ S := by
  have hspec := (hS.2.2.2 i).choose_spec
  obtain ⟨hpS, hpi⟩ := hspec
  simp only [wit]
  split_ifs with h
  · obtain ⟨hne, hnz⟩ := h.choose_spec
    exact pair_mem hS hpS (Ne.symm hne) hpi hnz
  · exact hpS

theorem wit_self {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k) (i : Fin k) :
    wit hS i i ≠ 0 := by
  have hspec := (hS.2.2.2 i).choose_spec
  obtain ⟨-, hpi⟩ := hspec
  simp only [wit]
  split_ifs with h
  · obtain ⟨hne, -⟩ := h.choose_spec
    simp [Pi.add_apply, Pi.single_apply, if_neg hne]
  · exact hpi

/-- The witness has at most two nonzero coordinates. -/
theorem wit_support {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k) (i : Fin k) :
    (Finset.univ.filter (fun l => wit hS i l ≠ 0)).card ≤ 2 := by
  classical
  simp only [wit]
  split_ifs with h
  · have hsub : (Finset.univ.filter
        (fun l => (Pi.single i 1 + Pi.single h.choose 1 : Fin k → ℕ) l ≠ 0))
        ⊆ ({i, h.choose} : Finset (Fin k)) := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply,
        Pi.single_apply] at hl
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hc
      push_neg at hc
      rw [if_neg hc.1, if_neg hc.2] at hl
      exact hl rfl
    exact le_trans (Finset.card_le_card hsub)
      (le_trans (Finset.card_insert_le _ _) (by simp))
  · push_neg at h
    have hsub : (Finset.univ.filter (fun l => (hS.2.2.2 i).choose l ≠ 0))
        ⊆ ({i} : Finset (Fin k)) := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp only [Finset.mem_singleton]
      by_contra hc
      exact hl (h l hc)
    exact le_trans (Finset.card_le_card hsub) (by simp)

/-- **`k ≤ 2m`.**  The witness map sends each coordinate into `S`, and its fibres have at
most two elements, because a witness has at most two nonzero coordinates and every
coordinate in a fibre is one of them. -/
theorem reduced_card_le {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k) :
    k ≤ 2 * m := by
  classical
  have hcard : S.card = m := hS.2.2.1
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin k)), wit hS i ∈ S :=
    fun i _ => wit_mem hS i
  have hfib : ∀ b ∈ S,
      ((Finset.univ : Finset (Fin k)).filter (fun i => wit hS i = b)).card ≤ 2 := by
    intro b _
    rcases Finset.eq_empty_or_nonempty
      ((Finset.univ : Finset (Fin k)).filter (fun i => wit hS i = b)) with he | ⟨i0, hi0⟩
    · simp [he]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi0
      refine le_trans (Finset.card_le_card ?_) (wit_support hS i0)
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      rw [hi0, ← hl]
      exact wit_self hS l
  have h := Finset.card_le_mul_card_image_of_maps_to hmaps 2 hfib
  simpa [hcard] using h

/-- **`reduced m k` is EMPTY once `k` exceeds `2m`.**  This is what makes link (A)'s
summation range `Finset.range (2*m+1)` correct rather than arbitrary, and it is the
consumer that makes `reduced_card_le` load-bearing. -/
theorem reduced_eq_empty {m k : ℕ} (h : 2 * m < k) : reduced m k = ∅ := by
  ext S
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hS
  exact absurd (reduced_card_le hS) (by omega)

/-- Hence `d_{m,k} = 0` beyond the range link (A) sums over — which is what makes
`ReductionBijection`'s `Finset.range (2*m+1)` the right range rather than an arbitrary one.
This is the consumer that makes `reduced_card_le` load-bearing. -/
theorem dCount_eq_zero {m k : ℕ} (h : 2 * m < k) : dCount m k = 0 := by
  rw [dCount, reduced_eq_empty h]
  simp

/-! ### The counting sets are FINITE

**`aCount` and `dCount` are `Nat.card` of `Set`s that nothing in this module proved
finite**, and `Nat.card` of an infinite set is `0`.  Neither set is obviously finite: both
live in `Finset (Fin r → ℕ)`, whose ambient type is infinite because the codomain is.  So
every counting statement above — including link (A) itself — rested on an unstated
finiteness fact.  It is supplied here, and it is a prerequisite for (A) rather than a
separate nicety: an identity between `Nat.card`s cannot be proved by a bijection until the
sets are known finite.

**The bound.**  A diagram is a lower set, so if `p ∈ D` and `p i = c`, the `c+1` points
`0, e_i, 2e_i, …, c·e_i` are all `≤ p` coordinatewise — coordinate `i` is `t ≤ c` and every
other coordinate is `0` — hence all lie in `D`, and they are pairwise distinct.  Therefore

    p i < |D|        for every `p ∈ D` and every `i`        (`coord_lt_card`)

and the bound is TIGHT: for `r = 1` the chain `{0, e, …, c·e}` attains it.  For
`diagrams m r` this gives `p i ≤ m + r`, confining `D` to the finite box `[0, m+r]^r`; for
`reduced m k`, `S` sits inside the diagram `μ_k ∪ S` whose size is at most `(k+1) + m`, so
`p i ≤ k + m`.  Only `|μ_k| ≤ k + 1` is needed, not the exact value.

Checked first in `Campaigns/MathDB-Formalization/verify_323219_finite.py`: the bound over
1552 `(D, p, i)` triples, its tightness, and — the check that matters — an enumeration with
a STRICTLY LARGER coordinate cap confirming nothing escapes the claimed box.

`aCount_eq_card` and `dCount_eq_card` then put both counts in the `Finset.card` form any
bijection argument needs, which is where (A) starts. -/

/-- **Every coordinate of every element of a diagram is below the diagram's size.**

If `p ∈ D` and `p i = c`, the `c+1` points `0, e_i, 2e_i, …, c·e_i` are all `≤ p`
coordinatewise, so the lower-set property puts all of them in `D`, and they are pairwise
distinct.  Hence `c + 1 ≤ |D|`.  The bound is TIGHT: for `r = 1` the chain
`{0, e, …, c·e}` attains it. -/
theorem coord_lt_card {r : ℕ} {D : Finset (Fin r → ℕ)} (hD : IsDiagram r D)
    {p : Fin r → ℕ} (hp : p ∈ D) (i : Fin r) : p i < D.card := by
  classical
  have hinj : Set.InjOn (fun t : ℕ => (Pi.single i t : Fin r → ℕ))
      (Finset.range (p i + 1)) := by
    intro a _ b _ hab
    have := congrFun hab i
    simpa using this
  have hsub : (Finset.range (p i + 1)).image (fun t : ℕ => (Pi.single i t : Fin r → ℕ))
      ⊆ D := by
    intro q hq
    simp only [Finset.mem_image, Finset.mem_range] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    have ht' : t ≤ p i := by omega
    refine hD p hp _ ?_
    intro l
    rw [Pi.single_apply]
    split_ifs with h
    · rw [h]; exact ht'
    · exact Nat.zero_le _
  have hcard : ((Finset.range (p i + 1)).image
      (fun t : ℕ => (Pi.single i t : Fin r → ℕ))).card = p i + 1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have := Finset.card_le_card hsub
  omega

/-- The finite box `[0, N]^r`, which the bound confines a diagram to. -/
def boxF (r N : ℕ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset (fun _ => Finset.range (N + 1))

theorem mem_boxF {r N : ℕ} {p : Fin r → ℕ} (h : ∀ i, p i ≤ N) : p ∈ boxF r N := by
  rw [boxF, Fintype.mem_piFinset]
  intro i
  exact Finset.mem_range.mpr (by have := h i; omega)

/-- **`diagrams m r` is FINITE.**  `aCount` is `Nat.card` of this set, and `Nat.card` of an
infinite set is `0`, so without this the counting statements are about junk.  Each `D` has
`|D| = m + r + 1`, so `coord_lt_card` confines it to the box `[0, m+r]^r`, and `D` is then a
subset of a fixed finite set. -/
theorem diagrams_finite (m r : ℕ) : (diagrams m r).Finite := by
  classical
  refine Set.Finite.subset (Finset.finite_toSet (boxF r (m + r)).powerset) ?_
  intro D hD
  obtain ⟨hlower, -, hcard⟩ := hD
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset]
  intro p hp
  refine mem_boxF (fun i => ?_)
  have := coord_lt_card hlower hp i
  omega

/-- `|μ_k| ≤ k + 1`.  The exact value is `k + 1`, but only the bound is needed. -/
theorem mu_card_le (k : ℕ) : (mu k).card ≤ k + 1 := by
  classical
  refine le_trans (Finset.card_insert_le _ _) ?_
  have := Finset.card_image_le (s := (univ : Finset (Fin k)))
    (f := fun i : Fin k => (Pi.single i 1 : Fin k → ℕ))
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

/-- **`reduced m k` is FINITE**, for the same reason: `S` sits inside the diagram `μ_k ∪ S`,
whose size is at most `(k+1) + m`. -/
theorem reduced_finite (m k : ℕ) : (reduced m k).Finite := by
  classical
  refine Set.Finite.subset (Finset.finite_toSet (boxF k (k + m)).powerset) ?_
  intro S hS
  obtain ⟨hlower, -, hcard, -⟩ := hS
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset]
  intro p hp
  refine mem_boxF (fun i => ?_)
  have hmem : p ∈ mu k ∪ S := Finset.mem_union_right _ hp
  have hlt := coord_lt_card hlower hmem i
  have hub : (mu k ∪ S).card ≤ (k + 1) + m := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have := mu_card_le k
    omega
  omega

/-! ### The counts as honest `Finset.card`s

Link (A) is an identity between `Nat.card`s.  Any bijection proof works with `Finset`s, and
the conversion is only available now that the sets are known finite — which is the point of
the two lemmas above.  These are the forms (A) starts from. -/

/-- `diagrams m r` as a `Finset`. -/
noncomputable def diagramsF (m r : ℕ) : Finset (Finset (Fin r → ℕ)) :=
  (diagrams_finite m r).toFinset

/-- `reduced m k` as a `Finset`. -/
noncomputable def reducedF (m k : ℕ) : Finset (Finset (Fin k → ℕ)) :=
  (reduced_finite m k).toFinset

theorem mem_diagramsF {m r : ℕ} {D : Finset (Fin r → ℕ)} :
    D ∈ diagramsF m r ↔ D ∈ diagrams m r := by
  rw [diagramsF, Set.Finite.mem_toFinset]

theorem mem_reducedF {m k : ℕ} {S : Finset (Fin k → ℕ)} :
    S ∈ reducedF m k ↔ S ∈ reduced m k := by
  rw [reducedF, Set.Finite.mem_toFinset]

/-- **`aCount` is a genuine `Finset.card`.** -/
theorem aCount_eq_card (m r : ℕ) : aCount m r = (diagramsF m r).card := by
  rw [aCount, Nat.card_coe_set_eq,
    Set.ncard_eq_toFinset_card _ (diagrams_finite m r), diagramsF]

/-- **`dCount` is a genuine `Finset.card`.** -/
theorem dCount_eq_card (m k : ℕ) : dCount m k = (reducedF m k).card := by
  rw [dCount, Nat.card_coe_set_eq,
    Set.ncard_eq_toFinset_card _ (reduced_finite m k), reducedF]

/-! ### The support-to-`Fin k` reindexing — the first half of link (A)

(A) says `a_{m,r} = ∑_k C(r,k)·d_{m,k}`.  The map behind it sends a diagram `D` to the pair
(which coordinates its added nodes use, the configuration they form once those coordinates
are renumbered).  This section builds that map and shows it does not collapse anything.

* `mu_card` — `|μ_r| = r + 1`, **exactly**.  `mu_card_le` above is the same fact as an
  inequality and is kept: that is all `reduced_finite` charged, and it is two lines, whereas
  the equality needs `Pi.single i 1 ≠ 0` and injectivity of `i ↦ Pi.single i 1`.  The
  reindexing is the consumer that charges the equality — `D \ μ_r` has `m` elements only if
  `|μ_r|` is known on the nose — so it is proved here, against a real demand, rather than
  speculatively when the inequality was first needed.
* `supp` — the coordinates the added nodes actually use.
* `zero_of_not_mem_supp` — off the support every added node vanishes.  **This is the whole
  content of injectivity**: two added nodes agreeing on the support agree everywhere,
  because both are zero elsewhere.
* `restrictTo`, `restrictTo_injOn`, `card_image_restrictTo` — the restriction, its
  injectivity on the added-node set, and the consequence that the reindexed configuration
  still has exactly `m` elements.

Checked first in `Campaigns/MathDB-Formalization/verify_323219_finite.py` §(5) over 91
enumerated diagrams, **including 51 in which the support is a PROPER subset of the
coordinates** — without those the restriction is the identity and the check proves nothing.

**What is still missing for (A)**, and it is the harder half: that the reindexed
configuration is actually REDUCED (`μ_k ∪ S'` a diagram, disjoint from `μ_k`, every
coordinate used), and that the map is a bijection onto `Σ k, (k-subsets) × reduced m k`. -/

/-- **`|μ_r| = r + 1`, exactly.**  `mu_card_le` was deliberately stated as an inequality
because `reduced_finite` charged only that much.  The reindexing charges the EQUALITY: the
added-node set is `D \ μ_r`, and it has `m` elements only if `|μ_r|` is known on the nose. -/
theorem mu_card (r : ℕ) : (mu r).card = r + 1 := by
  classical
  have hinj : Function.Injective (fun i : Fin r => (Pi.single i 1 : Fin r → ℕ)) := by
    intro i j hij
    by_contra hne
    have h := congrFun hij i
    simp only [Pi.single_eq_same, Pi.single_apply, if_neg hne] at h
    exact absurd h one_ne_zero
  have himg : (univ.image (fun i : Fin r => (Pi.single i 1 : Fin r → ℕ))).card = r := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hnot : (0 : Fin r → ℕ)
      ∉ univ.image (fun i : Fin r => (Pi.single i 1 : Fin r → ℕ)) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i hi
    have h := congrFun hi i
    simp only [Pi.single_eq_same, Pi.zero_apply] at h
    exact absurd h one_ne_zero
  rw [mu, Finset.card_insert_of_notMem hnot, himg]

/-- The added nodes of a diagram: exactly `m` of them. -/
theorem card_sdiff_mu {m r : ℕ} {D : Finset (Fin r → ℕ)} (hD : D ∈ diagrams m r) :
    (D \ mu r).card = m := by
  obtain ⟨-, hsub, hcard⟩ := hD
  rw [Finset.card_sdiff_of_subset hsub, hcard, mu_card]
  omega

/-! ### The reindexing adjunction lives in `Common/FinsetReindex`

`supp`, `restrictTo`, `extendByZero`, their round trips, `extendByZero_le`,
`equivFin_index_iff`, the four unit-vector lemmas and `sum_powerset_by_card` were **promoted
to `Principia/Common/FinsetReindex.lean`** on 2026-09-24: not one of them mentions a
diagram, a `μ_r` or a reduced configuration, so they belong where the next campaign can find
them.  They are `open`ed at the top of this namespace, so every use below reads unchanged.
The sections that follow still narrate them, because the narration is about THIS argument —
what each lemma is for here — and that is campaign-specific even when the lemma is not. -/

/-- By `restrictTo_injOn` (now in `Common/FinsetReindex`) the reindexed image has the
same size: `m`. -/
theorem card_image_restrictTo {m r : ℕ} {D : Finset (Fin r → ℕ)} (hD : D ∈ diagrams m r) :
    ((D \ mu r).image (restrictTo (supp (D \ mu r)))).card = m := by
  classical
  rw [Finset.card_image_of_injOn (restrictTo_injOn _), card_sdiff_mu hD]

/-! ### Extension by zero, and two of the four `reduced` clauses

`reduced m k` has four clauses: `μ_k ∪ S'` is a diagram, `Disjoint (μ_k) S'`, `|S'| = m`, and
every coordinate is used.  The third is `card_image_restrictTo` above.  This section adds
the inverse map and settles the fourth and the second.

**`extendByZero` is not bookkeeping** — it is what the lower-set clause will be proved with.
To show a point `y` below a restricted configuration is still in it, one extends `y` by zero
back to `Fin r`, applies `IsDiagram` THERE (where it is known), and restricts again.
`extendByZero_le` is the step that makes the lift admissible, and
`restrictTo_extendByZero`/`extendByZero_restrictTo` are the round trips.

**`restrictTo_not_mem_mu` is the disjointness clause**, and its hypotheses are exactly what
the proof uses: `p ∈ S` and `p ∉ μ_r`.  It was first written taking `D ∈ diagrams m r`, and
the unused-variable linter caught that the diagram hypothesis is never touched — so the
statement was narrowed rather than the binder renamed.  The content: a restricted added node
vanishes off the support, so if its restriction were `0` or `e_j`, the node itself would be
`0` or `e_i`, i.e. an element of `μ_r`.

**Still missing for (A)**: the lower-set clause itself, and then that the whole map is a
bijection onto `Σ k, (k-subsets of Fin r) × reduced m k`. -/

/-- **The reindexed configuration avoids `μ_k`.**  A restricted added node is neither `0`
nor a unit vector: it vanishes off the support, so if its restriction were `0` or `e_j` the
node itself would be `0` or `e_i`, i.e. an element of `μ_r`, which `D \ μ_r` excludes. -/
theorem restrictTo_not_mem_mu {r : ℕ} {S : Finset (Fin r → ℕ)} {p : Fin r → ℕ}
    (hp : p ∈ S) (hpmu : p ∉ mu r) :
    restrictTo (supp S) p ∉ mu (supp S).card := by
  classical
  set K := supp S with hK
  have hzero : ∀ l, l ∉ K → p l = 0 := zero_off_supp hp
  intro hcon
  rw [mu, Finset.mem_insert, Finset.mem_image] at hcon
  rcases hcon with h0 | ⟨j, -, hj⟩
  · exact hpmu (by
      have : p = 0 := by
        rw [← extendByZero_restrictTo K hzero, h0]
        funext l
        simp only [extendByZero, Pi.zero_apply]
        split_ifs <;> rfl
      rw [this, mu, Finset.mem_insert]
      exact Or.inl rfl)
  · refine hpmu ?_
    have hi : ((K.equivFin.symm j : {x // x ∈ K}) : Fin r) ∈ K := (K.equivFin.symm j).2
    have hpe : p = Pi.single ((K.equivFin.symm j : {x // x ∈ K}) : Fin r) 1 := by
      funext l
      by_cases hl : l ∈ K
      · -- the two index conditions correspond under the bijection
        have hiff : (K.equivFin ⟨l, hl⟩ = j)
            ↔ (l = ((K.equivFin.symm j : {x // x ∈ K}) : Fin r)) := by
          constructor
          · intro h
            have hsub : (⟨l, hl⟩ : {x // x ∈ K}) = K.equivFin.symm j := by
              rw [← h, Equiv.symm_apply_apply]
            exact congrArg Subtype.val hsub
          · intro h
            have hsub : (⟨l, hl⟩ : {x // x ∈ K}) = K.equivFin.symm j := Subtype.ext h
            rw [hsub, Equiv.apply_symm_apply]
        have hres : p l = restrictTo K p (K.equivFin ⟨l, hl⟩) := by
          simp only [restrictTo, Equiv.symm_apply_apply]
        rw [hres, ← hj, Pi.single_apply, Pi.single_apply]
        by_cases hc : l = ((K.equivFin.symm j : {x // x ∈ K}) : Fin r)
        · rw [if_pos hc, if_pos (hiff.mpr hc)]
        · rw [if_neg hc, if_neg (fun h => hc (hiff.mp h))]
      · rw [hzero l hl, Pi.single_apply,
          if_neg (fun hcon2 => hl (by rw [hcon2]; exact hi))]
    rw [hpe, mu, Finset.mem_insert, Finset.mem_image]
    exact Or.inr ⟨_, Finset.mem_univ _, rfl⟩

/-! ### The lower-set clause, and `restrictImage_mem_reduced`

The fourth and last clause of `reduced`, and then all four together: **the reindexed
configuration genuinely IS a reduced configuration.**

**Why the lower-set clause needs the lift.**  It says a point `y` below a restricted
configuration is still in it, and that cannot be decided downstairs — `IsDiagram` is known
about `D`, upstairs.  So lift `y` by zero to `ỹ = extendByZero K y`, note `ỹ ≤ p`
(`extendByZero_le`), conclude `ỹ ∈ D` because `D` IS a diagram, and split on whether `ỹ` is in
`μ_r`.  If it is, it is `0` or a unit vector `e_i`, and since `ỹ` vanishes off `K` the index
`i` must lie in `K`, so restricting gives `0` or `e_{K.equivFin i}` — both in `μ_k`.  If it
is not, then `ỹ ∈ D \ μ_r` and `restrictTo K ỹ = y` puts `y` in the image.

The `x ∈ μ_k` case needs nothing new: `isDiagram_mu` already says `μ_k` is a lower set, so
it is one application rather than a second unit-vector analysis.

`equivFin_index_iff` is the index correspondence, factored out.  Both unit-vector arguments
need it on each branch of an `if`, and proving the EQUIVALENCE is what avoids a `subst` that
would destroy the coordinate still being reasoned about.

**What remains for (A)** is now only the counting: that `D ↦ (supp, restricted config)` is a
BIJECTION onto `Σ k, (k-subsets of Fin r) × reduced m k`, with extension by zero as inverse,
assembled by `Finset.card_eq_sum_card_fiberwise` and `Finset.card_powersetCard`. -/

/-- **The lower-set clause — the last of the four.**

A point `y` below a restricted configuration cannot be handled downstairs, because
`IsDiagram` is known about `D`, upstairs.  So lift `y` by zero to `ỹ = extendByZero K y`, note
`ỹ ≤ p` (`extendByZero_le`), conclude `ỹ ∈ D` because `D` IS a diagram, and split:

* `ỹ ∈ μ_r` — then `ỹ` is `0` or a unit vector `e_i`, and since `ỹ` vanishes off `K` the
  index `i` lies in `K`; restricting gives `0` or `e_{K.equivFin i}`, both in `μ_k`.
* `ỹ ∉ μ_r` — then `ỹ ∈ D \ μ_r`, and `restrictTo K ỹ = y` puts `y` in the image.

The `x ∈ μ_k` case needs nothing new: `isDiagram_mu` already says `μ_k` is a lower set. -/
theorem isDiagram_image {m r : ℕ} {D : Finset (Fin r → ℕ)} (hD : D ∈ diagrams m r) :
    IsDiagram (supp (D \ mu r)).card
      (mu (supp (D \ mu r)).card ∪ (D \ mu r).image (restrictTo (supp (D \ mu r)))) := by
  classical
  obtain ⟨hdiag, -, -⟩ := hD
  set S := D \ mu r with hSdef
  set K := supp S with hKdef
  intro x hx y hle
  rcases Finset.mem_union.mp hx with hxmu | hxim
  · exact Finset.mem_union_left _ (isDiagram_mu _ x hxmu y hle)
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxim
    have hpD : p ∈ D := (Finset.mem_sdiff.mp hp).1
    have hext : extendByZero K y ≤ p := extendByZero_le K hle
    have hyD : extendByZero K y ∈ D := hdiag p hpD _ hext
    have hround : restrictTo K (extendByZero K y) = y := restrictTo_extendByZero K y
    by_cases hmu : extendByZero K y ∈ mu r
    · refine Finset.mem_union_left _ ?_
      rw [mu, Finset.mem_insert, Finset.mem_image] at hmu
      rcases hmu with h0 | ⟨i, -, hi1⟩
      · rw [h0, restrictTo_zero] at hround
        rw [← hround, mu, Finset.mem_insert]
        exact Or.inl rfl
      · have hiK : i ∈ K := by
          by_contra hno
          have hz := extendByZero_of_not_mem K y hno
          rw [← hi1] at hz
          simp only [Pi.single_eq_same] at hz
          exact one_ne_zero hz
        rw [← hi1, restrictTo_single K hiK] at hround
        rw [← hround, mu, Finset.mem_insert, Finset.mem_image]
        exact Or.inr ⟨_, Finset.mem_univ _, rfl⟩
    · refine Finset.mem_union_right _ ?_
      have hyS : extendByZero K y ∈ S := Finset.mem_sdiff.mpr ⟨hyD, hmu⟩
      have himg := Finset.mem_image_of_mem (restrictTo K) hyS
      rwa [hround] at himg

/-- **The reindexed configuration IS reduced** — all four clauses together. -/
theorem restrictImage_mem_reduced {m r : ℕ} {D : Finset (Fin r → ℕ)}
    (hD : D ∈ diagrams m r) :
    (D \ mu r).image (restrictTo (supp (D \ mu r)))
      ∈ reduced m (supp (D \ mu r)).card := by
  classical
  refine ⟨isDiagram_image hD, ?_, card_image_restrictTo hD, ?_⟩
  · rw [Finset.disjoint_right]
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact restrictTo_not_mem_mu hp (Finset.mem_sdiff.mp hp).2
  · intro j
    exact restrictTo_image_uses _ j

/-! ### The inverse direction

`restrictImage_mem_reduced` sends a diagram to a reduced configuration.  The counting needs
the other direction: from `S' ∈ reduced m K.card`, the diagram `μ_r ∪ S'.image (extendByZero K)`.
This section proves that lift has the properties the fibre argument will charge.

* `extendByZero_injective` / `card_image_extendByZero` — the lift does not collapse, so the
  lifted configuration still has `m` elements.  Injectivity is one line from the round trip.
* `extendByZero_zero`, `extendByZero_single`, `extendByZero_mem_mu`, `extendByZero_not_mem_mu` —
  the lift carries `μ_k` into `μ_r` and its complement into the complement.  Both directions
  are needed: the first to place lifted `μ`-points, the second for disjointness.
* `supp_image_extendByZero` — **the lifted configuration uses exactly `K`**.  This is what pins
  the support down, and hence what makes the fibre over `K` the right object to count.  It
  is the one place the `reduced` clause "every coordinate is used" is consumed.
* `isDiagram_union_image` — the mirror of `isDiagram_image`.  A point `y` below a lifted
  point vanishes off `K` (because the lift does), so it is ITSELF a lift, with
  `restrictTo K y ≤ q`; apply the diagram property downstairs and carry the `μ_k` case back
  up with `extendByZero_mem_mu`.

**Next**: the fibre bijection `{D | supp (D \ μ_r) = K} ≃ reduced m K.card`, then
`Finset.card_eq_sum_card_fiberwise` and `Finset.card_powersetCard`. -/

theorem extendByZero_mem_mu {r : ℕ} (K : Finset (Fin r)) {q : Fin K.card → ℕ}
    (hq : q ∈ mu K.card) : extendByZero K q ∈ mu r := by
  classical
  rw [mu, Finset.mem_insert, Finset.mem_image] at hq
  rcases hq with h0 | ⟨j, -, hj⟩
  · rw [h0, extendByZero_zero, mu, Finset.mem_insert]
    exact Or.inl rfl
  · rw [← hj, extendByZero_single, mu, Finset.mem_insert, Finset.mem_image]
    exact Or.inr ⟨_, Finset.mem_univ _, rfl⟩

theorem extendByZero_not_mem_mu {r : ℕ} (K : Finset (Fin r)) {q : Fin K.card → ℕ}
    (hq : q ∉ mu K.card) : extendByZero K q ∉ mu r := by
  classical
  intro hcon
  rw [mu, Finset.mem_insert, Finset.mem_image] at hcon
  have hround : restrictTo K (extendByZero K q) = q := restrictTo_extendByZero K q
  rcases hcon with h0 | ⟨i, -, hi1⟩
  · rw [h0, restrictTo_zero] at hround
    refine hq ?_
    rw [← hround, mu, Finset.mem_insert]
    exact Or.inl rfl
  · have hiK : i ∈ K := by
      by_contra hno
      have hz := extendByZero_of_not_mem K q hno
      rw [← hi1] at hz
      simp only [Pi.single_eq_same] at hz
      exact one_ne_zero hz
    rw [← hi1, restrictTo_single K hiK] at hround
    refine hq ?_
    rw [← hround, mu, Finset.mem_insert, Finset.mem_image]
    exact Or.inr ⟨_, Finset.mem_univ _, rfl⟩

/-- **The lifted configuration uses exactly the coordinates of `K`.**  This is what pins the
support down, and hence what makes the fibre over `K` the right thing to count. -/
theorem supp_image_extendByZero {r : ℕ} (K : Finset (Fin r)) (S' : Finset (Fin K.card → ℕ))
    (huse : ∀ j, ∃ q ∈ S', q j ≠ 0) :
    supp (S'.image (extendByZero K)) = K := by
  classical
  ext i
  rw [mem_supp]
  constructor
  · rintro ⟨p, hp, hne⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hp
    by_contra hno
    exact hne (extendByZero_of_not_mem K q hno)
  · intro hi
    obtain ⟨q, hq, hqne⟩ := huse (K.equivFin ⟨i, hi⟩)
    refine ⟨extendByZero K q, Finset.mem_image_of_mem _ hq, ?_⟩
    simp only [extendByZero, dif_pos hi]
    exact hqne

/-- **The lifted configuration spans a diagram** — the mirror of `isDiagram_image`.

A point `y` below a lifted point `extendByZero K q` vanishes off `K` (because the lift does),
so it is itself a lift: `y = extendByZero K (restrictTo K y)` with `restrictTo K y ≤ q`.
Applying the diagram property downstairs puts `restrictTo K y` in `μ_k ∪ S'`, and
`extendByZero_mem_mu` carries the `μ_k` case back up. -/
theorem isDiagram_union_image {r : ℕ} (K : Finset (Fin r)) (S' : Finset (Fin K.card → ℕ))
    (hdiag : IsDiagram K.card (mu K.card ∪ S')) :
    IsDiagram r (mu r ∪ S'.image (extendByZero K)) := by
  classical
  intro x hx y hle
  rcases Finset.mem_union.mp hx with hxmu | hxim
  · exact Finset.mem_union_left _ (isDiagram_mu _ x hxmu y hle)
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hxim
    have hyzero : ∀ l, l ∉ K → y l = 0 := by
      intro l hl
      have h : y l ≤ extendByZero K q l := hle l
      rw [extendByZero_of_not_mem K q hl] at h
      exact Nat.le_zero.mp h
    have hy : extendByZero K (restrictTo K y) = y := extendByZero_restrictTo K hyzero
    have hres : restrictTo K y ≤ q := by
      intro j
      have h1 := hle (((K.equivFin.symm j : {x // x ∈ K}) : Fin r))
      have hmem : ((K.equivFin.symm j : {x // x ∈ K}) : Fin r) ∈ K :=
        (K.equivFin.symm j).2
      have h2 : extendByZero K q ((K.equivFin.symm j : {x // x ∈ K}) : Fin r) = q j := by
        simp only [extendByZero, dif_pos hmem]
        congr 1
        exact K.equivFin.apply_symm_apply j
      rw [h2] at h1
      exact h1
    have hmem := hdiag q (Finset.mem_union_right _ hq) (restrictTo K y) hres
    rcases Finset.mem_union.mp hmem with hmu | hS
    · refine Finset.mem_union_left _ ?_
      rw [← hy]
      exact extendByZero_mem_mu K hmu
    · refine Finset.mem_union_right _ ?_
      rw [← hy]
      exact Finset.mem_image_of_mem _ hS

/-! ### The fibre count

**`card_fibre`: the diagrams whose added nodes use exactly the coordinate set `K` are in
bijection with `reduced m |K|`.**  Both maps and all their properties were built above, so
this is `Finset.card_bij'` with the two round trips:

* `roundTrip_diagram` — restricting the added nodes and lifting them back recovers `D`.
  The double image collapses because every added node vanishes off its own support
  (`zero_off_supp`), and `μ_r ∪ (D \ μ_r) = D` finishes it.
* `roundTrip_reduced` — lifting a reduced configuration and restricting recovers it.  The
  `sdiff` is computed by `disjoint_image_extendByZero`, which is where
  `extendByZero_not_mem_mu` is consumed.

**No dependent-type transport is needed, and that is why `K` is a parameter.**  The fibre is
indexed by a FIXED `K`, so the types `Fin K.card` never vary inside the proof; the only place
`supp (D \ μ_r)` occurs is rewritten to `K` by the filter's own hypothesis.  Stating the
lemma with `supp (D \ μ_r)` in the conclusion instead would have forced transporting along
an equality of `Finset`s through `Fin (·).card`, which is the usual source of pain here.

**What remains for (A)** is only the outer sum: `Finset.card_eq_sum_card_fiberwise` with
`f D = supp (D \ μ_r)` into `univ.powerset`, then regrouping by `K.card` with
`Finset.card_powersetCard` and truncating at `k ≤ 2m` via `dCount_eq_zero`. -/

/-- The lifted configuration is disjoint from `μ_r`. -/
theorem disjoint_image_extendByZero {m r : ℕ} (K : Finset (Fin r))
    {S' : Finset (Fin K.card → ℕ)} (hS' : S' ∈ reduced m K.card) :
    Disjoint (S'.image (extendByZero K)) (mu r) := by
  classical
  obtain ⟨-, hdisj, -, -⟩ := hS'
  rw [Finset.disjoint_left]
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  exact extendByZero_not_mem_mu K (Finset.disjoint_right.mp hdisj hp)

/-- **Round trip, diagram side.**  Restricting the added nodes and lifting them back
recovers the diagram. -/
theorem roundTrip_diagram {m r : ℕ} {D : Finset (Fin r → ℕ)} (hD : D ∈ diagrams m r) :
    mu r ∪ ((D \ mu r).image (restrictTo (supp (D \ mu r)))).image
        (extendByZero (supp (D \ mu r))) = D := by
  classical
  obtain ⟨-, hsub, -⟩ := hD
  have himg : ((D \ mu r).image (restrictTo (supp (D \ mu r)))).image
      (extendByZero (supp (D \ mu r))) = D \ mu r := by
    rw [Finset.image_image]
    refine (Finset.image_congr ?_).trans Finset.image_id
    intro p hp
    exact extendByZero_restrictTo _ (zero_off_supp (Finset.mem_coe.mp hp))
  rw [himg]
  exact Finset.union_sdiff_of_subset hsub

/-- **Round trip, configuration side.**  Lifting a reduced configuration and restricting the
added nodes recovers it.  The `sdiff` is computed by the disjointness. -/
theorem roundTrip_reduced {m r : ℕ} (K : Finset (Fin r)) {S' : Finset (Fin K.card → ℕ)}
    (hS' : S' ∈ reduced m K.card) :
    ((mu r ∪ S'.image (extendByZero K)) \ mu r).image (restrictTo K) = S' := by
  classical
  rw [Finset.union_sdiff_left,
    Finset.sdiff_eq_self_of_disjoint (disjoint_image_extendByZero K hS'),
    Finset.image_image]
  refine (Finset.image_congr ?_).trans Finset.image_id
  intro p _
  exact restrictTo_extendByZero K p

/-- The lift of a reduced configuration is a diagram of the right size. -/
theorem lift_mem_diagrams {m r : ℕ} (K : Finset (Fin r)) {S' : Finset (Fin K.card → ℕ)}
    (hS' : S' ∈ reduced m K.card) :
    mu r ∪ S'.image (extendByZero K) ∈ diagrams m r := by
  classical
  refine ⟨isDiagram_union_image K S' hS'.1, Finset.subset_union_left, ?_⟩
  rw [Finset.card_union_of_disjoint (disjoint_image_extendByZero K hS').symm,
    mu_card, card_image_extendByZero, hS'.2.2.1]
  omega

/-- The lift has support exactly `K`. -/
theorem supp_lift {m r : ℕ} (K : Finset (Fin r)) {S' : Finset (Fin K.card → ℕ)}
    (hS' : S' ∈ reduced m K.card) :
    supp ((mu r ∪ S'.image (extendByZero K)) \ mu r) = K := by
  classical
  rw [Finset.union_sdiff_left,
    Finset.sdiff_eq_self_of_disjoint (disjoint_image_extendByZero K hS')]
  exact supp_image_extendByZero K S' hS'.2.2.2

/-- **The fibre over `K` has exactly `d_{m,|K|}` elements.**

Both maps and all their properties are in place, so this is `Finset.card_bij'` with the two
round trips.  Note `K` is FIXED here, so no dependent-type transport is needed: the only
place `supp (D \ μ_r)` appears is rewritten to `K` by the filter's own hypothesis. -/
theorem card_fibre {m r : ℕ} (K : Finset (Fin r)) :
    ({D ∈ diagramsF m r | supp (D \ mu r) = K}).card = (reducedF m K.card).card := by
  classical
  refine Finset.card_bij'
    (fun D _ => (D \ mu r).image (restrictTo K))
    (fun S' _ => mu r ∪ S'.image (extendByZero K))
    ?_ ?_ ?_ ?_
  · intro D hD
    obtain ⟨hD1, hK⟩ := Finset.mem_filter.mp hD
    rw [mem_reducedF, ← hK]
    exact restrictImage_mem_reduced (mem_diagramsF.mp hD1)
  · intro S' hS'
    have hS'' := mem_reducedF.mp hS'
    refine Finset.mem_filter.mpr ⟨mem_diagramsF.mpr (lift_mem_diagrams K hS''), ?_⟩
    exact supp_lift K hS''
  · intro D hD
    obtain ⟨hD1, hK⟩ := Finset.mem_filter.mp hD
    rw [← hK]
    exact roundTrip_diagram (mem_diagramsF.mp hD1)
  · intro S' hS'
    exact roundTrip_reduced K (mem_reducedF.mp hS')

/-! ### The outer sum — **link (A) is DISCHARGED**

`reductionBijection` proves `a_{m,r} = ∑_{k ≤ 2m} C(r,k)·d_{m,k}`.  Fibre the diagrams by the
coordinate set their added nodes use; each fibre has `d_{m,|K|}` elements (`card_fibre`);
regroup the subsets by size (`sum_powerset_by_card`); truncate.

**Both truncations are needed, and for DIFFERENT reasons.**  The fibred sum runs to `k ≤ r`
and the target runs to `k ≤ 2m`, and neither bound dominates the other.  Terms with `k > 2m`
vanish because `reduced m k` is empty there (`dCount_eq_zero` — which is what the `k ≤ 2m`
support bound was for, and the write-up's justification for THAT was itself unsound, see the
row).  Terms with `k > r` vanish because `C(r,k) = 0`.  Passing through the common refinement
`range (r + 2m + 1)` handles both without a case split on which bound is larger.

`sum_powerset_by_card` mentions no diagrams and is the only place the binomial coefficient
enters — a `Common/` candidate.

`integrality_of_autDivisibility` and `alpha_integral_of_autDivisibility` restate the spine's
conclusions with (A) no longer assumed, so **the only remaining hypothesis of this module is
(B) `AutDivisibility`**. -/

/-- **LINK (A), DISCHARGED.**  `a_{m,r} = ∑_{k ≤ 2m} C(r,k)·d_{m,k}`.

Fibre the diagrams by the coordinate set their added nodes use; each fibre has `d_{m,|K|}`
elements (`card_fibre`); regroup the subsets by size (`sum_powerset_by_card`); and truncate.

**Both truncations are needed, and for different reasons.**  The fibred sum runs to `k ≤ r`
and the target runs to `k ≤ 2m`, and neither bound dominates the other.  Terms with `k > 2m`
vanish because `reduced m k` is empty there (`dCount_eq_zero`, which is what the `k ≤ 2m`
support bound was for); terms with `k > r` vanish because `C(r,k) = 0`.  Passing through the
common refinement `range (r + 2m + 1)` handles both. -/
theorem reductionBijection : ReductionBijection := by
  classical
  intro m r
  have hmaps : ∀ D ∈ diagramsF m r,
      supp (D \ mu r) ∈ (univ : Finset (Fin r)).powerset :=
    fun D _ => Finset.mem_powerset.mpr (Finset.subset_univ _)
  have hstep : aCount m r
      = ∑ K ∈ (univ : Finset (Fin r)).powerset, dCount m K.card := by
    rw [aCount_eq_card, Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    rw [card_fibre K, ← dCount_eq_card]
  have hL : ∑ k ∈ Finset.range (r + 1), r.choose k * dCount m k
      = ∑ k ∈ Finset.range (r + 2 * m + 1), r.choose k * dCount m k := by
    refine Finset.sum_subset
      (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))) ?_
    intro k _ hk
    rw [Finset.mem_range] at hk
    have hk' : r < k := by omega
    rw [Nat.choose_eq_zero_of_lt hk', zero_mul]
  have hR : ∑ k ∈ Finset.range (2 * m + 1), r.choose k * dCount m k
      = ∑ k ∈ Finset.range (r + 2 * m + 1), r.choose k * dCount m k := by
    refine Finset.sum_subset
      (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))) ?_
    intro k _ hk
    rw [Finset.mem_range] at hk
    have hk' : 2 * m < k := by omega
    rw [dCount_eq_zero hk', Nat.mul_zero]
  rw [hstep, sum_powerset_by_card]
  exact hL.trans hR.symm

/-! ### The spine, with (A) no longer assumed

`integrality` and `alpha_integral` were stated taking BOTH links.  Now that (A) is proved,
they specialise: only (B) remains a hypothesis.  These are what make `reductionBijection`
consumed rather than a theorem standing on its own. -/

/-- `integrality`, with link (A) discharged. -/
theorem integrality_of_autDivisibility (hB : AutDivisibility) (m : ℕ) :
    (Pm m).natDegree ≤ 2 * m ∧
      ∀ r : ℕ, (Pm m).eval (r : ℤ) = (normalizer m : ℤ) * (aCount m r : ℤ) :=
  integrality reductionBijection hB m

/-- `alpha_integral`, with link (A) discharged: the ONLY remaining hypothesis of the spine
is (B) `AutDivisibility`. -/
theorem alpha_integral_of_autDivisibility (hB : AutDivisibility) (m : ℕ) :
    ∃ P : Polynomial ℤ, P.natDegree ≤ 2 * m ∧
      ∀ r : ℕ, P.eval (r : ℤ) = (normalizer m : ℤ) * (aCount m r : ℤ) :=
  alpha_integral reductionBijection hB m

/-! ### Link (B): the coordinate-permutation action

(B) is `∀ m k, k ≤ 2m → k! ∣ 2^m·m!·d_{m,k}`, and everything about it happens inside the
`S_k` action on configurations.  This section builds the action and proves `reduced m k`
invariant, which is what makes an orbit decomposition meaningful.

**THE WRITE-UP'S REASON FOR (B) IS FALSE, and the repair is recorded in the row.**  The
source derives (B) from orbit–stabiliser plus `|Aut S| ∣ 2^m m!`, justifying the latter by
*the `m` added nodes ARE `m` edges*, so an automorphism permutes them and may flip each.
**An added node need not be an edge**: `pair_mem` says that if `p ∈ S` has two nonzero
coordinates then the PAIR `e_i+e_j` is also in `S`, not that `p` is a pair.  Counterexample
at `m = 4`: `S = {e₁+e₂, e₁+e₃, e₂+e₃, e₁+e₂+e₃}` on `k = 3` is reduced and contains a
three-coordinate point.  It cannot occur for `m ≤ 3`, since such a point forces its three
pairs into `S`.

**The repaired argument uses only `pair_mem`.**  Let `N` be the kernel of `Aut S → Sym(S)`.
(a) every `σ ∈ N` is an involution — a size-3 orbit would force `e_i+e_j ∈ S`, which is not
constant on that orbit; (b) each transposition occurring in some `σ ∈ N` forces a distinct
`e_i+e_j ∈ S`, so the pair set `T` has `|T| ≤ m`; (c) `N` lies in the elementary abelian
group generated by `T`, so `|N| ∣ 2^{|T|} ∣ 2^m`; (d) `Aut S / N ↪ Sym(S)` divides `m!`.
Checked over 149 configurations in
`Campaigns/MathDB-Formalization/verify_323219_aut.py`, with orbit–stabiliser as a positive
control, the tight case `m=1, k=2` where `|Aut| = 2 = 2^1 1!`, and 88 configurations with a
non-trivial kernel — without which step (c) would be vacuous.

What is here so far: the action `permPt`/`permCfg`, that it is an order isomorphism on points
(`permPt_le_iff`, which is what transports the lower-set property), that `μ_k` is invariant,
and that **`reduced m k` is invariant** (`permCfg_mem_reduced`). -/

/-- `σ` acting on a point by permuting coordinates. -/
def permPt {k : ℕ} (σ : Equiv.Perm (Fin k)) (p : Fin k → ℕ) : Fin k → ℕ :=
  fun i => p (σ.symm i)

/-- `σ` acting on a configuration. -/
noncomputable def permCfg {k : ℕ} (σ : Equiv.Perm (Fin k)) (S : Finset (Fin k → ℕ)) :
    Finset (Fin k → ℕ) :=
  S.image (permPt σ)

theorem permPt_symm_apply {k : ℕ} (σ : Equiv.Perm (Fin k)) (p : Fin k → ℕ) :
    permPt σ (permPt σ.symm p) = p := by
  funext i
  simp [permPt]

theorem permPt_apply_symm {k : ℕ} (σ : Equiv.Perm (Fin k)) (p : Fin k → ℕ) :
    permPt σ.symm (permPt σ p) = p := by
  funext i
  simp [permPt]

theorem permPt_injective {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    Function.Injective (permPt σ) := by
  intro a b hab
  funext i
  have h := congrFun hab (σ i)
  simpa [permPt] using h

/-- The action is an order isomorphism on points — which is what lets it transport the
lower-set property. -/
theorem permPt_le_iff {k : ℕ} (σ : Equiv.Perm (Fin k)) (p q : Fin k → ℕ) :
    permPt σ p ≤ permPt σ q ↔ p ≤ q := by
  constructor
  · intro h j
    have hj := h (σ j)
    simpa [permPt] using hj
  · intro h i
    exact h _

theorem permPt_zero {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    permPt σ (0 : Fin k → ℕ) = 0 := rfl

theorem permPt_single {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    permPt σ (Pi.single i 1 : Fin k → ℕ) = Pi.single (σ i) 1 := by
  funext j
  simp only [permPt, Pi.single_apply]
  by_cases h : j = σ i
  · rw [if_pos h, if_pos (by rw [h, Equiv.symm_apply_apply])]
  · rw [if_neg h, if_neg]
    intro hc
    exact h (by rw [← hc, Equiv.apply_symm_apply])

/-- `μ_k` is invariant: the action permutes the unit vectors and fixes `0`. -/
theorem permPt_mem_mu {k : ℕ} (σ : Equiv.Perm (Fin k)) (p : Fin k → ℕ) :
    permPt σ p ∈ mu k ↔ p ∈ mu k := by
  classical
  constructor
  · intro h
    rw [mu, Finset.mem_insert, Finset.mem_image] at h
    rcases h with h0 | ⟨i, -, hi⟩
    · have hp : p = 0 := by
        have h2 := congrArg (permPt σ.symm) h0
        rwa [permPt_apply_symm, permPt_zero] at h2
      rw [hp, mu, Finset.mem_insert]
      exact Or.inl rfl
    · have hp : p = Pi.single (σ.symm i) 1 := by
        have h2 := congrArg (permPt σ.symm) hi
        rw [permPt_single, permPt_apply_symm] at h2
        exact h2.symm
      rw [hp, mu, Finset.mem_insert, Finset.mem_image]
      exact Or.inr ⟨_, Finset.mem_univ _, rfl⟩
  · intro h
    rw [mu, Finset.mem_insert, Finset.mem_image] at h
    rcases h with h0 | ⟨i, -, hi⟩
    · rw [h0, permPt_zero, mu, Finset.mem_insert]
      exact Or.inl rfl
    · rw [← hi, permPt_single, mu, Finset.mem_insert, Finset.mem_image]
      exact Or.inr ⟨_, Finset.mem_univ _, rfl⟩

theorem permCfg_mu {k : ℕ} (σ : Equiv.Perm (Fin k)) : permCfg σ (mu k) = mu k := by
  classical
  ext q
  rw [permCfg, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (permPt_mem_mu σ p).mpr hp
  · intro hq
    refine ⟨permPt σ.symm q, ?_, permPt_symm_apply σ q⟩
    have := (permPt_mem_mu σ.symm q).mpr hq
    exact this

theorem permCfg_union {k : ℕ} (σ : Equiv.Perm (Fin k)) (S T : Finset (Fin k → ℕ)) :
    permCfg σ (S ∪ T) = permCfg σ S ∪ permCfg σ T := by
  classical
  simp [permCfg, Finset.image_union]

/-- The lower-set property transports along the action. -/
theorem isDiagram_permCfg {k : ℕ} (σ : Equiv.Perm (Fin k)) {T : Finset (Fin k → ℕ)}
    (h : IsDiagram k T) : IsDiagram k (permCfg σ T) := by
  classical
  intro x hx y hle
  rw [permCfg, Finset.mem_image] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  have hy : permPt σ.symm y ≤ p := by
    rw [← permPt_le_iff σ, permPt_symm_apply]
    exact hle
  have hmem := h p hp _ hy
  rw [permCfg, Finset.mem_image]
  exact ⟨permPt σ.symm y, hmem, permPt_symm_apply σ y⟩

/-- **`reduced m k` is invariant under the action** — the fact that makes the orbit
decomposition of link (B) meaningful. -/
theorem permCfg_mem_reduced {m k : ℕ} (σ : Equiv.Perm (Fin k)) {S : Finset (Fin k → ℕ)}
    (hS : S ∈ reduced m k) : permCfg σ S ∈ reduced m k := by
  classical
  obtain ⟨hdiag, hdisj, hcard, huse⟩ := hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← permCfg_mu σ, ← permCfg_union]
    exact isDiagram_permCfg σ hdiag
  · rw [Finset.disjoint_right]
    intro q hq
    rw [permCfg, Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [permPt_mem_mu]
    exact Finset.disjoint_right.mp hdisj hp
  · rw [permCfg, Finset.card_image_of_injective _ (permPt_injective σ), hcard]
  · intro j
    obtain ⟨p, hp, hpne⟩ := huse (σ.symm j)
    exact ⟨permPt σ p, Finset.mem_image_of_mem _ hp, hpne⟩

/-! ### Link (B) step (a): the stabilisers, and the involution property

`autCfg S` is `Aut S`; `ptStab S` is the POINTWISE stabiliser, the kernel `N` of
`Aut S → Sym(S)` that the repaired argument is built around.

**`ptStab_sq` is step (a), and it is what replaces the write-up's false picture.**  Every
element of `N` is an involution.  The proof uses only `pair_mem`: if `σ` had an orbit of
size three through `i`, then `i`, `σ i`, `σ² i` are pairwise distinct; every point of `S` is
constant along `σ`-orbits (`permPt_eq_self_iff`), so a point `p` with `p i ≠ 0` — one exists
because every coordinate is used — also has `p (σ i) ≠ 0`; then `pair_mem` puts
`e_i + e_{σ i}` into `S`, and THAT point is constant along orbits too, yet takes the value
`1` at `σ i` and `0` at `σ² i`, which share an orbit.

Note the shape: the contradiction comes from applying invariance to a point that `pair_mem`
MANUFACTURES, not to the point one started with.  That is why the write-up's "every node is
an edge" claim is not needed — only that the pairs are present.

**Next**: step (b), each transposition occurring in some `σ ∈ N` forces a distinct
`e_i + e_j ∈ S`, so the pair set has at most `m` elements. -/

/-- Invariance of a point, in the form the argument uses: `σ` fixes `p` exactly when `p` is
constant along `σ`-orbits. -/
theorem permPt_eq_self_iff {k : ℕ} (σ : Equiv.Perm (Fin k)) (p : Fin k → ℕ) :
    permPt σ p = p ↔ ∀ x, p (σ x) = p x := by
  constructor
  · intro h x
    have hx := congrFun h (σ x)
    simp only [permPt, Equiv.symm_apply_apply] at hx
    exact hx.symm
  · intro h
    funext x
    simp only [permPt]
    have hx := h (σ.symm x)
    rw [Equiv.apply_symm_apply] at hx
    exact hx.symm

/-- The full stabiliser `Aut S` of a configuration. -/
noncomputable def autCfg {k : ℕ} (S : Finset (Fin k → ℕ)) :
    Finset (Equiv.Perm (Fin k)) :=
  Finset.univ.filter (fun σ => permCfg σ S = S)

theorem mem_autCfg {k : ℕ} {S : Finset (Fin k → ℕ)} {σ : Equiv.Perm (Fin k)} :
    σ ∈ autCfg S ↔ permCfg σ S = S := by
  classical
  rw [autCfg, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ σ, h⟩⟩

/-- The POINTWISE stabiliser: the kernel of `Aut S → Sym(S)`.  This is the `N` of the
repaired argument. -/
noncomputable def ptStab {k : ℕ} (S : Finset (Fin k → ℕ)) :
    Finset (Equiv.Perm (Fin k)) :=
  Finset.univ.filter (fun σ => ∀ p ∈ S, permPt σ p = p)

theorem mem_ptStab {k : ℕ} {S : Finset (Fin k → ℕ)} {σ : Equiv.Perm (Fin k)} :
    σ ∈ ptStab S ↔ ∀ p ∈ S, permPt σ p = p := by
  classical
  rw [ptStab, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ σ, h⟩⟩

/-- The pointwise stabiliser sits inside the full one. -/
theorem ptStab_subset_autCfg {k : ℕ} (S : Finset (Fin k → ℕ)) :
    ptStab S ⊆ autCfg S := by
  classical
  intro σ hσ
  rw [mem_ptStab] at hσ
  rw [mem_autCfg, permCfg]
  refine Finset.image_congr (fun p hp => hσ p (Finset.mem_coe.mp hp)) |>.trans ?_
  exact Finset.image_id

/-- **Step (a) of the repaired argument: every element of the pointwise stabiliser is an
involution.**

This is what replaces the write-up's false "the `m` added nodes are `m` edges" picture, and
it uses only `pair_mem`.  If `σ` had an orbit of size three through `i`, then `i`, `σ i` and
`σ² i` are pairwise distinct.  Every point of `S` is constant along `σ`-orbits, so a point
`p` with `p i ≠ 0` — one exists because every coordinate is used — also has `p (σ i) ≠ 0`.
Then `pair_mem` puts `e_i + e_{σ i}` into `S`, and THAT point is constant along orbits too;
but it takes the value `1` at `σ i` and `0` at `σ² i`, which lie in the same orbit. -/
theorem ptStab_sq {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k)
    {σ : Equiv.Perm (Fin k)} (hσ : σ ∈ ptStab S) (i : Fin k) : σ (σ i) = i := by
  classical
  rw [mem_ptStab] at hσ
  have hinv : ∀ q ∈ S, ∀ x, q (σ x) = q x :=
    fun q hq => (permPt_eq_self_iff σ q).mp (hσ q hq)
  by_contra hne
  have hij : i ≠ σ i := by
    intro h
    apply hne
    rw [← h]
    exact h.symm
  have hjl : σ i ≠ σ (σ i) := fun h => hij (σ.injective h)
  obtain ⟨p, hp, hpi⟩ := hS.2.2.2 i
  have hpj : p (σ i) ≠ 0 := by rw [hinv p hp i]; exact hpi
  have hq := pair_mem hS hp hij hpi hpj
  have hql : (Pi.single i 1 + Pi.single (σ i) 1 : Fin k → ℕ) (σ (σ i))
      = (Pi.single i 1 + Pi.single (σ i) 1 : Fin k → ℕ) (σ i) :=
    hinv _ hq (σ i)
  have h1 : (Pi.single i 1 + Pi.single (σ i) 1 : Fin k → ℕ) (σ i) = 1 := by
    simp [Pi.add_apply, Ne.symm hij]
  have h0 : (Pi.single i 1 + Pi.single (σ i) 1 : Fin k → ℕ) (σ (σ i)) = 0 := by
    simp [Pi.add_apply, hne, Ne.symm hjl]
  rw [h1, h0] at hql
  exact absurd hql (by norm_num)

/-! ### Link (B) step (b): the stabiliser pairs, and there are at most `m` of them

`ptStab_one`/`ptStab_mul`/`ptStab_inv` make `N` a subgroup (step (c) will need that);
`pair_mem_of_ptStab` is step (b) proper: **if `σ` fixes every point of `S` and MOVES `i`,
then `e_i + e_{σ i} ∈ S`.**  It is the first half of `ptStab_sq`'s argument, isolated because
the counting needs it on its own.

**The counting is a one-liner because of how `stabPairs` is defined.**  The obvious
formulation — a `Finset` of unordered index pairs, plus an injection into `S` — would need
the injection built and proved.  Defining the pairs instead as a SUBSET OF `S`
(`S.filter (…)`) makes `|T| ≤ |S| = m` exactly `Finset.card_filter_le`.  The pairs really
are elements of `S`; there is no reason to represent them twice.

`stabPair_apply` records that a pair is `1` at its two coordinates and `0` elsewhere, which
is what step (c) will use to recover the transposition from the pair.

**Next**: step (c) — every element of `N` is an involution (`ptStab_sq`), so `N` is
elementary abelian and `|N|` is a power of two; and `σ ∈ N` is determined by which pairs it
moves, so `|N| ∣ 2^{|stabPairs S|} ∣ 2^m`.  Then (d), `Aut S / N ↪ Sym(S)` divides `m!`. -/

theorem permPt_mul {k : ℕ} (σ τ : Equiv.Perm (Fin k)) (p : Fin k → ℕ) :
    permPt (σ * τ) p = permPt σ (permPt τ p) := rfl

theorem permPt_one {k : ℕ} (p : Fin k → ℕ) :
    permPt (1 : Equiv.Perm (Fin k)) p = p := rfl

theorem ptStab_one {k : ℕ} (S : Finset (Fin k → ℕ)) :
    (1 : Equiv.Perm (Fin k)) ∈ ptStab S := by
  rw [mem_ptStab]
  intro p _
  exact permPt_one p

theorem ptStab_mul {k : ℕ} {S : Finset (Fin k → ℕ)} {σ τ : Equiv.Perm (Fin k)}
    (hσ : σ ∈ ptStab S) (hτ : τ ∈ ptStab S) : σ * τ ∈ ptStab S := by
  rw [mem_ptStab] at hσ hτ ⊢
  intro p hp
  rw [permPt_mul, hτ p hp, hσ p hp]

theorem ptStab_inv {k : ℕ} {S : Finset (Fin k → ℕ)} {σ : Equiv.Perm (Fin k)}
    (hσ : σ ∈ ptStab S) : σ⁻¹ ∈ ptStab S := by
  rw [mem_ptStab] at hσ ⊢
  intro p hp
  have h := hσ p hp
  have h2 := congrArg (permPt σ⁻¹) h
  rw [← permPt_mul, inv_mul_cancel, permPt_one] at h2
  exact h2.symm

/-- **Step (b), the pair lemma.**  If `σ` fixes every point of `S` and MOVES `i`, then the
pair `e_i + e_{σ i}` lies in `S`.  This is the first half of `ptStab_sq`'s argument, isolated
because the counting needs it on its own: a point `p` with `p i ≠ 0` exists since every
coordinate is used, invariance carries the nonzero value to `σ i`, and `pair_mem` concludes. -/
theorem pair_mem_of_ptStab {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k)
    {σ : Equiv.Perm (Fin k)} (hσ : σ ∈ ptStab S) {i : Fin k} (hi : σ i ≠ i) :
    (Pi.single i 1 + Pi.single (σ i) 1 : Fin k → ℕ) ∈ S := by
  rw [mem_ptStab] at hσ
  have hinv : ∀ q ∈ S, ∀ x, q (σ x) = q x :=
    fun q hq => (permPt_eq_self_iff σ q).mp (hσ q hq)
  obtain ⟨p, hp, hpi⟩ := hS.2.2.2 i
  have hpj : p (σ i) ≠ 0 := by rw [hinv p hp i]; exact hpi
  exact pair_mem hS hp (Ne.symm hi) hpi hpj

/-- **The pairs realised by the pointwise stabiliser, AS A SUBSET OF `S`.**

Defining them this way — rather than as a `Finset` of unordered index pairs together with an
injection — is what makes the counting a one-liner: they are already elements of `S`, so
`|T| ≤ |S| = m` is `Finset.card_filter_le`. -/
noncomputable def stabPairs {k : ℕ} (S : Finset (Fin k → ℕ)) : Finset (Fin k → ℕ) :=
  S.filter (fun q => ∃ σ ∈ ptStab S, ∃ i : Fin k,
    σ i ≠ i ∧ q = (Pi.single i 1 + Pi.single (σ i) 1 : Fin k → ℕ))

theorem mem_stabPairs {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k)
    {σ : Equiv.Perm (Fin k)} (hσ : σ ∈ ptStab S) {i : Fin k} (hi : σ i ≠ i) :
    (Pi.single i 1 + Pi.single (σ i) 1 : Fin k → ℕ) ∈ stabPairs S := by
  classical
  rw [stabPairs, Finset.mem_filter]
  exact ⟨pair_mem_of_ptStab hS hσ hi, σ, hσ, i, hi, rfl⟩

/-- **Step (b)'s conclusion: there are at most `m` such pairs.** -/
theorem stabPairs_card_le {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k) :
    (stabPairs S).card ≤ m := by
  classical
  rw [← hS.2.2.1]
  exact Finset.card_filter_le _ _

/-- A stabiliser pair is `1` at both of its own coordinates and `0` elsewhere — the fact
that lets step (c) recover the transposition from the pair. -/
theorem stabPair_apply {k : ℕ} {i j : Fin k} (hij : i ≠ j) (l : Fin k) :
    (Pi.single i 1 + Pi.single j 1 : Fin k → ℕ) l = if l = i ∨ l = j then 1 else 0 := by
  classical
  by_cases hi : l = i
  · simp [Pi.add_apply, hi, hij]
  · by_cases hj : l = j
    · simp [Pi.add_apply, hj, Ne.symm hij]
    · simp [Pi.add_apply, hi, hj]

/-! ### Link (B) step (c), first half: `|N|` is a power of two

Step (c) is `|N| ∣ 2^m`, and it needs TWO independent facts.  This section supplies the one
that is easy to overlook.

**A bound is not a divisibility.**  The pair count gives `|N| ≤ 2^{|stabPairs S|} ≤ 2^m`, and
that alone says nothing about `2^m` being a multiple of `|N|`.  It becomes a divisibility
exactly when `|N|` is already known to be a power of two — so this half is unavoidable, not
a convenience.

`ptStab_sq` says every element of `N` is an involution, so `N` is a 2-group
(`ptStabGroup_isPGroup`), and `IsPGroup.exists_card_eq` turns that into
`|N| = 2^t` (`ptStab_card_eq_two_pow`).

**Two presentations of the same subgroup, deliberately.**  `ptStab` is a `Finset`, which is
what the pair counting consumes; `ptStabGroup` is a `Subgroup`, which is what the order
argument needs.  `card_ptStabGroup` is the bridge, and keeping both is cheaper than forcing
either half through the other's representation.

**Next**: the other half of (c) — `σ ∈ N` is determined by the set of pairs its
transpositions produce, so `|N| ≤ 2^{|stabPairs S|}`; `stabPair_apply` is what recovers the
transposition from a pair.  Then (d), `Aut S / N ↪ Sym(S)` divides `m!`. -/

/-- `ptStab_sq` as a group equation. -/
theorem ptStab_mul_self {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k)
    {σ : Equiv.Perm (Fin k)} (hσ : σ ∈ ptStab S) : σ * σ = 1 := by
  apply Equiv.ext
  intro i
  exact ptStab_sq hS hσ i

/-- The pointwise stabiliser as a SUBGROUP.  The `Finset` form `ptStab` is what the pair
counting uses; the subgroup form is what the order argument needs. -/
def ptStabGroup {k : ℕ} (S : Finset (Fin k → ℕ)) : Subgroup (Equiv.Perm (Fin k)) where
  carrier := {σ | ∀ p ∈ S, permPt σ p = p}
  one_mem' := fun p _ => permPt_one p
  mul_mem' := fun {σ τ} hσ hτ p hp => by
    show permPt (σ * τ) p = p
    rw [permPt_mul, hτ p hp, hσ p hp]
  inv_mem' := fun {σ} hσ p hp => by
    show permPt σ⁻¹ p = p
    have h2 := congrArg (permPt σ⁻¹) (hσ p hp)
    rw [← permPt_mul, inv_mul_cancel, permPt_one] at h2
    exact h2.symm

theorem mem_ptStabGroup {k : ℕ} {S : Finset (Fin k → ℕ)} {σ : Equiv.Perm (Fin k)} :
    σ ∈ ptStabGroup S ↔ ∀ p ∈ S, permPt σ p = p := Iff.rfl

theorem ptStabGroup_isPGroup {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k) :
    IsPGroup 2 (ptStabGroup S) := by
  intro g
  refine ⟨1, ?_⟩
  have hg : (g : Equiv.Perm (Fin k)) ∈ ptStab S := by
    rw [mem_ptStab]
    exact g.2
  have hsq := ptStab_mul_self hS hg
  apply Subtype.ext
  push_cast
  rw [pow_two, hsq]

theorem card_ptStabGroup {k : ℕ} (S : Finset (Fin k → ℕ)) :
    Nat.card (ptStabGroup S) = (ptStab S).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext σ
  simp [ptStab, mem_ptStabGroup]

/-- **The power-of-two half of step (c).**  Every element of the pointwise stabiliser is an
involution (`ptStab_sq`), so `N` is a 2-group and its order is a power of two.

This half is unavoidable.  The other half gives only `|N| ≤ 2^m`, and a BOUND does not imply
DIVISIBILITY — it does so exactly when the order is already known to be a power of two. -/
theorem ptStab_card_eq_two_pow {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k) :
    ∃ t : ℕ, (ptStab S).card = 2 ^ t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := (ptStabGroup_isPGroup hS).exists_card_eq
  exact ⟨t, by rw [← card_ptStabGroup, ht]⟩

/-! ### Link (B) step (c), completed: `|N| ∣ 2^m`

`σ ∈ N` is recoverable from the set of pairs its transpositions produce, so `N` injects into
the powerset of `stabPairs S` and `|N| ≤ 2^{|stabPairs S|} ≤ 2^m`.  With
`ptStab_card_eq_two_pow` — `|N|` is a power of two — the bound upgrades to a divisibility.

**The map is INJECTIVE but NOT a homomorphism**, and that is not a defect of the proof but
the reason the two halves are independent: `(12)(34)` and `(13)(24)` multiply to `(14)(23)`,
whose pair set is not the symmetric difference of theirs.  So no group-theoretic shortcut
turns the injection into a divisibility, and `|N| = 2^t` has to be established on its own.

`stabPair_eq_iff` carries the combinatorial content: two pairs are equal exactly when their
supports are, proved by evaluating at the four indices.  The injectivity argument is then a
clean case split — for `i` moved by `σ`, the pair `e_i + e_{σ i}` lies in `τ`'s pair set, so
`{i, σ i} = {j, τ j}` for some `j`; either `j = i` (giving `τ i = σ i` directly) or `j = σ i`,
and then `τ` being an involution gives the same conclusion.  A point fixed by `σ` but moved by
`τ` runs the same argument in reverse and contradicts the fixing.

**Next**: step (d), `Aut S / N ↪ Sym(S)` divides `m!`; then orbit–stabiliser assembles (B). -/

/-- **Two pairs are equal exactly when their supports are.**  This is what lets the
injectivity argument read off the transposition from the pair, and it is proved by
evaluating at the four indices. -/
theorem stabPair_eq_iff {k : ℕ} {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d) :
    (Pi.single a 1 + Pi.single b 1 : Fin k → ℕ)
        = (Pi.single c 1 + Pi.single d 1 : Fin k → ℕ)
      ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  constructor
  · intro h
    have ha : (if a = c ∨ a = d then 1 else 0) = (1 : ℕ) := by
      rw [← stabPair_apply hcd a, ← h, stabPair_apply hab a, if_pos (Or.inl rfl)]
    have hb : (if b = c ∨ b = d then 1 else 0) = (1 : ℕ) := by
      rw [← stabPair_apply hcd b, ← h, stabPair_apply hab b, if_pos (Or.inr rfl)]
    have ha' : a = c ∨ a = d := by
      by_contra hc
      rw [if_neg hc] at ha
      exact absurd ha (by norm_num)
    have hb' : b = c ∨ b = d := by
      by_contra hc
      rw [if_neg hc] at hb
      exact absurd hb (by norm_num)
    rcases ha' with hac | had
    · refine Or.inl ⟨hac, ?_⟩
      rcases hb' with hbc | hbd
      · exact absurd (hac.trans hbc.symm) hab
      · exact hbd
    · refine Or.inr ⟨had, ?_⟩
      rcases hb' with hbc | hbd
      · exact hbc
      · exact absurd (had.trans hbd.symm) hab
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact add_comm _ _

/-- The set of pairs produced by `σ`'s transpositions, as a subset of `stabPairs S`. -/
noncomputable def pairSet {k : ℕ} (S : Finset (Fin k → ℕ)) (σ : Equiv.Perm (Fin k)) :
    Finset (Fin k → ℕ) :=
  (stabPairs S).filter
    (fun q => ∃ i : Fin k, σ i ≠ i ∧ q = (Pi.single i 1 + Pi.single (σ i) 1 : Fin k → ℕ))

theorem pairSet_subset {k : ℕ} (S : Finset (Fin k → ℕ)) (σ : Equiv.Perm (Fin k)) :
    pairSet S σ ⊆ stabPairs S := by
  classical
  exact Finset.filter_subset _ _

theorem mem_pairSet {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k)
    {σ : Equiv.Perm (Fin k)} (hσ : σ ∈ ptStab S) {i : Fin k} (hi : σ i ≠ i) :
    (Pi.single i 1 + Pi.single (σ i) 1 : Fin k → ℕ) ∈ pairSet S σ := by
  classical
  rw [pairSet, Finset.mem_filter]
  exact ⟨mem_stabPairs hS hσ hi, i, hi, rfl⟩

/-- **`σ` is recoverable from its pair set.**  Note the map is INJECTIVE but NOT a
homomorphism — `(12)(34)` and `(13)(24)` multiply to `(14)(23)`, whose pair set is not the
symmetric difference of theirs — which is why the power-of-two half of step (c) cannot be
obtained this way and has to be proved separately. -/
theorem pairSet_injOn {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k) :
    Set.InjOn (pairSet S) (ptStab S) := by
  classical
  intro σ hσ τ hτ hst
  have hσ' : σ ∈ ptStab S := hσ
  have hτ' : τ ∈ ptStab S := hτ
  apply Equiv.ext
  intro i
  by_cases hfix : σ i = i
  · -- if `σ` fixes `i` then so does `τ`
    by_contra hne
    have hτi : τ i ≠ i := fun h => hne (hfix.trans h.symm)
    have hmem := mem_pairSet hS hτ' hτi
    rw [← hst, pairSet, Finset.mem_filter] at hmem
    obtain ⟨-, j, hj, hq⟩ := hmem
    rcases (stabPair_eq_iff (Ne.symm hτi) (Ne.symm hj)).mp hq with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact hj (by rw [← h1, hfix])
    · -- `i = σ j` and `σ` is an involution, so `σ i = j`; with `σ i = i` this forces `i = j`
      refine absurd ?_ hj
      have hinv := ptStab_sq hS hσ' j
      rw [← h1, hfix] at hinv
      rw [← hinv]
      exact hfix
  · have hmem := mem_pairSet hS hσ' hfix
    rw [hst, pairSet, Finset.mem_filter] at hmem
    obtain ⟨-, j, hj, hq⟩ := hmem
    rcases (stabPair_eq_iff (Ne.symm hfix) (Ne.symm hj)).mp hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1] at h2; exact h2
    · have : τ i = j := by rw [h1, ptStab_sq hS hτ' j]
      rw [this, h2]

/-- **Step (c), second half**: `|N| ≤ 2^{|stabPairs S|}`. -/
theorem ptStab_card_le {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k) :
    (ptStab S).card ≤ 2 ^ (stabPairs S).card := by
  classical
  rw [← Finset.card_powerset (stabPairs S)]
  refine Finset.card_le_card_of_injOn (pairSet S) ?_ (pairSet_injOn hS)
  intro σ _
  exact Finset.mem_powerset.mpr (pairSet_subset S σ)

/-- **Step (c), complete**: `|N| ∣ 2^m`.  The bound and the power-of-two shape are both
needed; neither implies the divisibility alone. -/
theorem ptStab_card_dvd {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k) :
    (ptStab S).card ∣ 2 ^ m := by
  obtain ⟨t, ht⟩ := ptStab_card_eq_two_pow hS
  have hle : (ptStab S).card ≤ 2 ^ m :=
    le_trans (ptStab_card_le hS)
      (Nat.pow_le_pow_right (by norm_num) (stabPairs_card_le hS))
  rw [ht] at hle ⊢
  exact pow_dvd_pow 2 ((pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp hle)

/-! ### Link (B) step (d), and the assembly: `AutDivisibility` DISCHARGED

Step (d) is Lagrange applied to the restriction homomorphism `Aut S → Sym(S)`.  Its kernel
is exactly the pointwise stabiliser `N` of step (c), so

    |Aut S| = |Aut S / N| · |N|,   |Aut S / N| ∣ |Sym(S)| = m!,   |N| ∣ 2^m,

giving `|Aut S| ∣ 2^m m!` (`autCfg_card_dvd`).  Nothing here mentions the write-up's false
"the added nodes are edges" picture: the embedding it claimed is replaced by an embedding
that always exists, and the arithmetic that picture was supplying is supplied by step (c).

The assembly is orbit–stabiliser: `|orbit S| · |Aut S| = k!`, so with `2^m m! = |Aut S| · c`
each orbit contributes `2^m m! · |orbit S| = c · k!`, and `d_{m,k}` is the sum of the orbit
sizes.  **The support bound `k ≤ 2m` is not used** — (B) holds for all `m, k`, and the
hypothesis is kept only because the carried `Prop` was stated with it.

Two presentations of `Aut S` are kept, as with `N`: `autCfg` is the `Finset` the counting
consumes, `autCfgGroup` the `Subgroup` Lagrange needs, bridged by `card_autCfgGroup`. -/

/-- The action of `Sym(k)` on configurations is a group action: the identity acts trivially. -/
theorem permCfg_one {k : ℕ} (S : Finset (Fin k → ℕ)) : permCfg (1 : Equiv.Perm (Fin k)) S = S := by
  classical
  rw [permCfg]
  exact (Finset.image_congr (fun p _ => permPt_one p)).trans Finset.image_id

theorem permCfg_mul {k : ℕ} (σ τ : Equiv.Perm (Fin k)) (S : Finset (Fin k → ℕ)) :
    permCfg (σ * τ) S = permCfg σ (permCfg τ S) := by
  classical
  have h : permPt (σ * τ) = (permPt σ) ∘ (permPt τ) := funext fun p => permPt_mul σ τ p
  rw [permCfg, permCfg, permCfg, Finset.image_image, h]

/-- `Aut S` as a `Subgroup`, alongside the `Finset` presentation `autCfg`. -/
def autCfgGroup {k : ℕ} (S : Finset (Fin k → ℕ)) : Subgroup (Equiv.Perm (Fin k)) where
  carrier := {σ | permCfg σ S = S}
  one_mem' := permCfg_one S
  mul_mem' := fun {σ τ} hσ hτ => by
    show permCfg (σ * τ) S = S
    rw [permCfg_mul, hτ, hσ]
  inv_mem' := fun {σ} hσ => by
    show permCfg σ⁻¹ S = S
    have h := congrArg (permCfg σ⁻¹) hσ
    rw [← permCfg_mul, inv_mul_cancel, permCfg_one] at h
    exact h.symm

theorem mem_autCfgGroup {k : ℕ} {S : Finset (Fin k → ℕ)} {σ : Equiv.Perm (Fin k)} :
    σ ∈ autCfgGroup S ↔ permCfg σ S = S := Iff.rfl

theorem card_autCfgGroup {k : ℕ} (S : Finset (Fin k → ℕ)) :
    Nat.card (autCfgGroup S) = (autCfg S).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext σ
  simp [autCfg, mem_autCfgGroup]

theorem ptStabGroup_le_autCfgGroup {k : ℕ} (S : Finset (Fin k → ℕ)) :
    ptStabGroup S ≤ autCfgGroup S := by
  classical
  intro σ hσ
  show permCfg σ S = S
  rw [permCfg]
  exact (Finset.image_congr (fun p hp => hσ p (Finset.mem_coe.mp hp))).trans Finset.image_id

/-- An automorphism maps `S` into itself pointwise. -/
theorem permPt_mem_of_autCfg {k : ℕ} {S : Finset (Fin k → ℕ)} {σ : Equiv.Perm (Fin k)}
    (hσ : permCfg σ S = S) {p : Fin k → ℕ} (hp : p ∈ S) : permPt σ p ∈ S := by
  classical
  rw [← hσ, permCfg]
  exact Finset.mem_image_of_mem _ hp

/-- The permutation of `S` induced by an automorphism. -/
noncomputable def cfgPerm {k : ℕ} (S : Finset (Fin k → ℕ)) (σ : autCfgGroup S) :
    Equiv.Perm {x // x ∈ S} where
  toFun := fun p => ⟨permPt (σ : Equiv.Perm (Fin k)) (p : Fin k → ℕ),
    permPt_mem_of_autCfg σ.2 p.2⟩
  invFun := fun p => ⟨permPt ((σ : Equiv.Perm (Fin k))⁻¹) (p : Fin k → ℕ),
    permPt_mem_of_autCfg (inv_mem σ.2) p.2⟩
  left_inv := fun p => by
    apply Subtype.ext
    show permPt ((σ : Equiv.Perm (Fin k))⁻¹)
        (permPt (σ : Equiv.Perm (Fin k)) (p : Fin k → ℕ)) = (p : Fin k → ℕ)
    rw [← permPt_mul, inv_mul_cancel, permPt_one]
  right_inv := fun p => by
    apply Subtype.ext
    show permPt (σ : Equiv.Perm (Fin k))
        (permPt ((σ : Equiv.Perm (Fin k))⁻¹) (p : Fin k → ℕ)) = (p : Fin k → ℕ)
    rw [← permPt_mul, mul_inv_cancel, permPt_one]

theorem cfgPerm_apply {k : ℕ} (S : Finset (Fin k → ℕ)) (σ : autCfgGroup S)
    (p : {x // x ∈ S}) :
    ((cfgPerm S σ p : {x // x ∈ S}) : Fin k → ℕ)
      = permPt (σ : Equiv.Perm (Fin k)) (p : Fin k → ℕ) := rfl

/-- **The restriction homomorphism `Aut S → Sym(S)`.**  Its kernel is the pointwise
stabiliser `N`, which is what makes step (d) an application of Lagrange. -/
noncomputable def cfgHom {k : ℕ} (S : Finset (Fin k → ℕ)) :
    autCfgGroup S →* Equiv.Perm {x // x ∈ S} where
  toFun := cfgPerm S
  map_one' := by
    apply Equiv.ext
    intro p
    apply Subtype.ext
    rw [cfgPerm_apply]
    show permPt (1 : Equiv.Perm (Fin k)) (p : Fin k → ℕ) = (p : Fin k → ℕ)
    exact permPt_one _
  map_mul' := fun σ τ => by
    apply Equiv.ext
    intro p
    apply Subtype.ext
    rw [cfgPerm_apply]
    show permPt ((σ : Equiv.Perm (Fin k)) * (τ : Equiv.Perm (Fin k))) (p : Fin k → ℕ)
      = permPt (σ : Equiv.Perm (Fin k)) (permPt (τ : Equiv.Perm (Fin k)) (p : Fin k → ℕ))
    exact permPt_mul _ _ _

theorem cfgHom_apply {k : ℕ} (S : Finset (Fin k → ℕ)) (σ : autCfgGroup S) :
    cfgHom S σ = cfgPerm S σ := rfl

theorem ker_cfgHom {k : ℕ} (S : Finset (Fin k → ℕ)) :
    (cfgHom S).ker = (ptStabGroup S).subgroupOf (autCfgGroup S) := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_ptStabGroup]
  constructor
  · intro h p hp
    have := congrArg (fun e => ((e ⟨p, hp⟩ : {x // x ∈ S}) : Fin k → ℕ)) h
    simpa [cfgHom_apply, cfgPerm_apply] using this
  · intro h
    apply Equiv.ext
    intro p
    apply Subtype.ext
    rw [cfgHom_apply, cfgPerm_apply]
    show permPt (σ : Equiv.Perm (Fin k)) (p : Fin k → ℕ)
      = ((1 : Equiv.Perm {x // x ∈ S}) p : Fin k → ℕ)
    exact h _ p.2

theorem card_ker_cfgHom {k : ℕ} (S : Finset (Fin k → ℕ)) :
    Nat.card (cfgHom S).ker = (ptStab S).card := by
  rw [ker_cfgHom,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (ptStabGroup_le_autCfgGroup S)).toEquiv]
  exact card_ptStabGroup S

/-- **Step (d)**: `|Aut S| ∣ 2^m · m!`. -/
theorem autCfg_card_dvd {m k : ℕ} {S : Finset (Fin k → ℕ)} (hS : S ∈ reduced m k) :
    (autCfg S).card ∣ 2 ^ m * m.factorial := by
  classical
  have hcard : S.card = m := hS.2.2.1
  have hS' : Nat.card {x // x ∈ S} = m := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hcard]
  have hq : Nat.card (autCfgGroup S ⧸ (cfgHom S).ker) ∣ m.factorial := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (cfgHom S)).toEquiv]
    refine dvd_trans (Subgroup.card_subgroup_dvd_card _) ?_
    rw [Nat.card_perm, hS']
  have hk : Nat.card (cfgHom S).ker ∣ 2 ^ m := by
    rw [card_ker_cfgHom]
    exact ptStab_card_dvd hS
  rw [← card_autCfgGroup, Subgroup.card_eq_card_quotient_mul_card_subgroup (cfgHom S).ker,
    Nat.mul_comm (2 ^ m) m.factorial]
  exact mul_dvd_mul hq hk

/-! ### The assembly of link (B)

Orbit–stabiliser over the `Sym(k)`-action on `reduced m k`: every orbit has size
`k!/|Aut S|`, and step (d) says `|Aut S|` divides `2^m m!`, so `2^m m! ·|orbit|` is a
multiple of `k!` term by term. -/

/-- The `Sym(k)`-action on reduced configurations. -/
noncomputable instance reducedAction (m k : ℕ) :
    MulAction (Equiv.Perm (Fin k)) {S : Finset (Fin k → ℕ) // S ∈ reduced m k} where
  smul σ S := ⟨permCfg σ (S : Finset (Fin k → ℕ)), permCfg_mem_reduced σ S.2⟩
  one_smul S := Subtype.ext (permCfg_one (S : Finset (Fin k → ℕ)))
  mul_smul σ τ S := Subtype.ext (permCfg_mul σ τ (S : Finset (Fin k → ℕ)))

theorem reducedAction_smul_coe {m k : ℕ} (σ : Equiv.Perm (Fin k))
    (S : {S : Finset (Fin k → ℕ) // S ∈ reduced m k}) :
    ((σ • S : {S : Finset (Fin k → ℕ) // S ∈ reduced m k}) : Finset (Fin k → ℕ))
      = permCfg σ (S : Finset (Fin k → ℕ)) := rfl

instance reducedSubtypeFinite (m k : ℕ) :
    Finite {S : Finset (Fin k → ℕ) // S ∈ reduced m k} :=
  (reduced_finite m k).to_subtype

/-- The stabiliser of the action IS `Aut S`. -/
theorem stabilizer_eq_autCfgGroup {m k : ℕ}
    (S : {S : Finset (Fin k → ℕ) // S ∈ reduced m k}) :
    MulAction.stabilizer (Equiv.Perm (Fin k)) S = autCfgGroup (S : Finset (Fin k → ℕ)) := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, mem_autCfgGroup]
  constructor
  · intro h
    have h' := congrArg (fun T : {S : Finset (Fin k → ℕ) // S ∈ reduced m k} =>
      (T : Finset (Fin k → ℕ))) h
    rw [reducedAction_smul_coe] at h'
    exact h'
  · intro h
    exact Subtype.ext (by rw [reducedAction_smul_coe, h])

/-- **Orbit–stabiliser, in the campaign's own notation.** -/
theorem card_orbit_mul_card_autCfg {m k : ℕ}
    (S : {S : Finset (Fin k → ℕ) // S ∈ reduced m k}) :
    Nat.card (MulAction.orbit (Equiv.Perm (Fin k)) S)
        * (autCfg (S : Finset (Fin k → ℕ))).card = k.factorial := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Equiv.Perm (Fin k)) S)
  rw [Nat.card_prod, stabilizer_eq_autCfgGroup, card_autCfgGroup] at h
  rw [h, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Each orbit contributes a multiple of `k!` once weighted by the normaliser. -/
theorem factorial_dvd_normalizer_mul_orbit {m k : ℕ}
    (S : {S : Finset (Fin k → ℕ) // S ∈ reduced m k}) :
    k.factorial ∣ normalizer m * Nat.card (MulAction.orbit (Equiv.Perm (Fin k)) S) := by
  obtain ⟨c, hc⟩ := autCfg_card_dvd S.2
  refine ⟨c, ?_⟩
  simp only [normalizer]
  rw [hc, ← card_orbit_mul_card_autCfg S]
  ring

/-- **Link (B), discharged.**  `k! ∣ 2^m · m! · d_{m,k}`, and the support bound `k ≤ 2m`
is not even needed. -/
theorem autDivisibility : AutDivisibility := by
  classical
  intro m k _
  letI : Fintype (MulAction.orbitRel.Quotient (Equiv.Perm (Fin k))
      {S : Finset (Fin k → ℕ) // S ∈ reduced m k}) := Fintype.ofFinite _
  have hdec : dCount m k
      = ∑ ω : MulAction.orbitRel.Quotient (Equiv.Perm (Fin k))
            {S : Finset (Fin k → ℕ) // S ∈ reduced m k},
          Nat.card (MulAction.orbit (Equiv.Perm (Fin k)) ω.out) := by
    rw [dCount, Nat.card_congr (MulAction.selfEquivSigmaOrbits (Equiv.Perm (Fin k))
      {S : Finset (Fin k → ℕ) // S ∈ reduced m k}), Nat.card_sigma]
  rw [hdec, Finset.mul_sum]
  exact Finset.dvd_sum (fun ω _ => factorial_dvd_normalizer_mul_orbit _)

/-! ### Both links discharged -/

/-- **The integrality theorem, unconditionally.** -/
theorem integrality_final (m : ℕ) :
    (Pm m).natDegree ≤ 2 * m ∧
      ∀ r : ℕ, (Pm m).eval (r : ℤ) = (normalizer m : ℤ) * (aCount m r : ℤ) :=
  integrality_of_autDivisibility autDivisibility m

/-- **The conjecture, unconditionally**: there is a polynomial with INTEGER coefficients, of
degree at most `2m`, whose value at `r` is `(2m)!! · a_{m+r+1,r}`. -/
theorem alpha_integral_final (m : ℕ) :
    ∃ P : Polynomial ℤ, P.natDegree ≤ 2 * m ∧
      ∀ r : ℕ, P.eval (r : ℤ) = (normalizer m : ℤ) * (aCount m r : ℤ) :=
  alpha_integral_of_autDivisibility autDivisibility m

/-! ### The write-up's other two clauses

Theorem \ref{main} of the write-up has three clauses, and the polynomial's existence is
only the first.  The second — *"consequently every `α_{m,z}` is an integer"* — needs the
interpolating polynomial to be UNIQUE, since the `α_{m,z}` are *defined* by the displayed
relation rather than by our construction; `eq_map_Pm_of_eval` supplies that, and
`alpha_isInt` is the conjecture in the source's own terms.  The third — *"a nonnegative
integer linear combination of the falling factorials"* — is `alpha_nonneg_combination`, and
it is immediate once the coefficients are known to be integers, because the numerator
`2^m m! d_{m,k}` counts something.

`exists_ratPoly_eval` exhibits a `Q` satisfying the hypothesis, so neither statement is
vacuously true. -/

/-- The falling-factorial coefficients are NONNEGATIVE: the numerator counts something. -/
theorem qCoeff_nonneg (m k : ℕ) : 0 ≤ qCoeff m k :=
  Int.ediv_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)

/-- **The write-up's third clause**: `2^m m! · a_{m+r+1,r}` is a NONNEGATIVE integer
combination of the falling factorials `(r)_k`. -/
theorem alpha_nonneg_combination (m : ℕ) :
    ∃ q : ℕ → ℤ, (∀ k, 0 ≤ q k) ∧
      Pm m = ∑ k ∈ Finset.range (2 * m + 1), Polynomial.C (q k) * descPochhammer ℤ k :=
  ⟨qCoeff m, fun k => qCoeff_nonneg m k, rfl⟩

/-- The hypothesis of `eq_map_Pm_of_eval` and `alpha_isInt` is SATISFIABLE — without this
those statements could be vacuously true. -/
theorem exists_ratPoly_eval (m : ℕ) :
    ∃ Q : Polynomial ℚ, ∀ r : ℕ, Q.eval (r : ℚ) = (normalizer m : ℚ) * (aCount m r : ℚ) := by
  refine ⟨(Pm m).map (Int.castRingHom ℚ), fun r => ?_⟩
  rw [Polynomial.eval_natCast_map, (integrality_final m).2 r]
  simp

/-- **The interpolating polynomial is unique**, so the write-up's "consequently every
`α_{m,z}` is an integer" is not merely an existence claim: the `α_{m,z}` are *defined* by
the displayed relation, and any rational polynomial satisfying it is `Pm m` with its
integer coefficients cast. -/
theorem eq_map_Pm_of_eval (m : ℕ) (Q : Polynomial ℚ)
    (hQ : ∀ r : ℕ, Q.eval (r : ℚ) = (normalizer m : ℚ) * (aCount m r : ℚ)) :
    Q = (Pm m).map (Int.castRingHom ℚ) := by
  have hinf : (Set.range ((↑) : ℕ → ℚ)).Infinite :=
    Set.infinite_range_of_injective (fun a b h => Nat.cast_injective h)
  refine Polynomial.eq_of_infinite_eval_eq _ _ (hinf.mono ?_)
  rintro _ ⟨r, rfl⟩
  refine Set.mem_setOf.mpr ?_
  rw [hQ r, Polynomial.eval_natCast_map, (integrality_final m).2 r]
  simp

/-- **Govindarajan's Conjecture 3.1**: every `α_{m,z}` is an integer. -/
theorem alpha_isInt (m : ℕ) (Q : Polynomial ℚ)
    (hQ : ∀ r : ℕ, Q.eval (r : ℚ) = (normalizer m : ℚ) * (aCount m r : ℚ)) (z : ℕ) :
    ∃ c : ℤ, Q.coeff z = (c : ℚ) := by
  refine ⟨(Pm m).coeff z, ?_⟩
  rw [eq_map_Pm_of_eval m Q hQ, Polynomial.coeff_map]
  rfl

/-! ### [G]'s own definitions, and that this module's objects ARE them

**The residue this row carried was described as an unformalised interface — "[G] §2.2–2.5
identifies Govindarajan's `a_{n,r}` with the diagram count".  Read at the source, that is
wrong in a way worth recording: `a_{n,r}` is DEFINED as the diagram count.**

From `arXiv:1203.4419v1`, quoted as the ar5iv rendering gives them:

* equation (2.3) defines *"`a_{n,r}` as the sum over all strict FD's with `n` nodes and
  i.d. `r`"*;
* *"Given a Ferrers diagram, let it be contained in an `r`-dimensional hyperplane but not in
  any `(r-1)`-dimensional hyperplane.  The intrinsic dimension (i.d.) of the Ferrers diagram
  is defined to be `r`."*;
* *"A Ferrers diagram is said to be strict when its intrinsic dimension equals its
  dimension."*;
* *"The weight of a gFD of i.d. `r` and symmetry `H ⊆ S_r` is defined to be `r!/ord(H)`."*;
* equation (3.1): `a_{m+r+1,r} = (∑_{z=0}^{2m} α_{m,z} r^{2m-z})/(2m)!!`, which is exactly the
  relation `alpha_isInt` consumes, and Conjecture 3.1 is *"The entries of the α-triangle,
  i.e., α_{m,z}, are all integers."*

So this section formalises [G]'s definitions rather than assuming them:

* `intrinsicDim` with `intrinsicDim_is_least` — the support IS the minimal coordinate set
  containing the diagram, which is the hyperplane phrasing.
* `IsStrict`, and `mem_diagrams_iff_strict`: **`diagrams m r` is exactly the set of strict
  Ferrers diagrams with `m + r + 1` nodes**, so `aCount` is `a_{m+r+1,r}` by (2.3).  The
  content is `mu_subset_iff_isStrict`: for a finite lower set, "uses every coordinate" and
  "contains `μ_r`" are the same condition.
* `aCount_eq_weighted_class_sum` — (2.3) read instead as a sum of [G]'s weights over gFD
  classes gives the same number, by orbit–stabiliser.  **The row therefore does not turn on
  which reading of (2.3) is meant**, and the weight is stated as `w · |H| = r!` so that no
  natural-number division hides the exactness.

**Provenance, stated plainly**: the source was read through ar5iv's HTML rendering, not the
PDF, and the quotations above are verbatim as that rendering returned them. -/

/-- **[G]'s INTRINSIC DIMENSION**, verbatim: *"Given a Ferrers diagram, let it be contained
in an `r`-dimensional hyperplane but not in any `(r-1)`-dimensional hyperplane.  The
intrinsic dimension (i.d.) of the Ferrers diagram is defined to be `r`."*

Rendered as the number of coordinates actually used.  `intrinsicDim_is_least` proves this is
the same thing: the support is a coordinate set containing the diagram, and no smaller one
does. -/
noncomputable def intrinsicDim {r : ℕ} (D : Finset (Fin r → ℕ)) : ℕ := (supp D).card

/-- `D` lies in the coordinate subspace spanned by `K` exactly when `supp D ⊆ K`. -/
theorem supp_subset_iff {r : ℕ} {D : Finset (Fin r → ℕ)} {K : Finset (Fin r)} :
    supp D ⊆ K ↔ ∀ p ∈ D, ∀ i, i ∉ K → p i = 0 := by
  classical
  constructor
  · intro h p hp i hi
    by_contra hne
    exact hi (h (mem_supp.mpr ⟨p, hp, hne⟩))
  · intro h i hi
    obtain ⟨p, hp, hne⟩ := mem_supp.mp hi
    by_contra hK
    exact hne (h p hp i hK)

/-- **`intrinsicDim` really is [G]'s minimum.**  The support is a coordinate set containing
the diagram, and every such set is at least as big. -/
theorem intrinsicDim_is_least {r : ℕ} (D : Finset (Fin r → ℕ)) :
    (∀ p ∈ D, ∀ i, i ∉ supp D → p i = 0) ∧
      ∀ K : Finset (Fin r), (∀ p ∈ D, ∀ i, i ∉ K → p i = 0) →
        intrinsicDim D ≤ K.card := by
  classical
  refine ⟨fun p hp i hi => zero_of_not_mem_supp hp hi, fun K hK => ?_⟩
  exact Finset.card_le_card (supp_subset_iff.mpr hK)

/-- **[G]'s STRICT**, verbatim: *"A Ferrers diagram is said to be strict when its intrinsic
dimension equals its dimension."* -/
def IsStrict {r : ℕ} (D : Finset (Fin r → ℕ)) : Prop := intrinsicDim D = r

theorem isStrict_iff_supp {r : ℕ} {D : Finset (Fin r → ℕ)} :
    IsStrict D ↔ supp D = Finset.univ := by
  classical
  constructor
  · intro h
    refine Finset.eq_univ_of_card _ ?_
    rw [Fintype.card_fin]
    exact h
  · intro h
    rw [IsStrict, intrinsicDim, h, Finset.card_univ, Fintype.card_fin]

/-- **The bridge this module's definition needed.**  For a finite lower set, "uses every
coordinate" and "contains `μ_r`" are the same condition.

`←` is the one with content: if coordinate `i` is used by some `p ∈ D`, then `e_i ≤ p`, and a
lower set containing `p` contains `e_i`; and `0 ∈ D` because `D` is a nonempty lower set. -/
theorem mu_subset_iff_isStrict {r : ℕ} {D : Finset (Fin r → ℕ)} (hD : IsDiagram r D)
    (hne : D.Nonempty) : mu r ⊆ D ↔ IsStrict D := by
  classical
  rw [isStrict_iff_supp]
  constructor
  · intro h
    refine Finset.eq_univ_of_forall (fun i => ?_)
    refine mem_supp.mpr ⟨Pi.single i 1, ?_, ?_⟩
    · refine h ?_
      rw [mu, Finset.mem_insert, Finset.mem_image]
      exact Or.inr ⟨i, Finset.mem_univ i, rfl⟩
    · rw [Pi.single_eq_same]
      exact one_ne_zero
  · intro h q hq
    rw [mu, Finset.mem_insert, Finset.mem_image] at hq
    obtain ⟨x, hx⟩ := hne
    rcases hq with rfl | ⟨i, -, rfl⟩
    · exact hD x hx 0 (fun j => Nat.zero_le _)
    · have hi : i ∈ supp D := by rw [h]; exact Finset.mem_univ i
      obtain ⟨p, hp, hpi⟩ := mem_supp.mp hi
      refine hD p hp _ (fun j => ?_)
      rw [Pi.single_apply]
      split_ifs with hj
      · rw [hj]
        exact Nat.one_le_iff_ne_zero.mpr hpi
      · exact Nat.zero_le _

/-- **`diagrams m r` IS [G]'s set of strict Ferrers diagrams with `m + r + 1` nodes.**

So `aCount m r` is `a_{m+r+1, r}` as [G] defines it — equation (2.3), *"`a_{n,r}` as the sum
over all strict FD's with `n` nodes and i.d. `r`"* — rather than a count this module chose. -/
theorem mem_diagrams_iff_strict {m r : ℕ} {D : Finset (Fin r → ℕ)} :
    D ∈ diagrams m r ↔ IsDiagram r D ∧ IsStrict D ∧ D.card = m + r + 1 := by
  classical
  constructor
  · rintro ⟨hdiag, hmu, hcard⟩
    have hne : D.Nonempty := Finset.card_pos.mp (by omega)
    exact ⟨hdiag, (mu_subset_iff_isStrict hdiag hne).mp hmu, hcard⟩
  · rintro ⟨hdiag, hstrict, hcard⟩
    have hne : D.Nonempty := Finset.card_pos.mp (by omega)
    exact ⟨hdiag, (mu_subset_iff_isStrict hdiag hne).mpr hstrict, hcard⟩

/-! ### [G]'s (2.3) read as a WEIGHTED sum over classes

[G] defines the weight of a gFD — a diagram up to the `S_r` action — of i.d. `r` and symmetry
`H ⊆ S_r` to be `r!/ord(H)`.  Reading (2.3) as a sum of those weights over classes gives the
same number as the plain labelled count, by orbit–stabiliser, and that is proved here so the
row does not depend on which reading of (2.3) is meant.

The weight is stated as `w ω * |Aut| = r!` rather than `r!/|Aut|`, so no natural-number
division appears and the exactness is part of the statement. -/

theorem permCfg_mem_diagrams {m r : ℕ} (σ : Equiv.Perm (Fin r)) {D : Finset (Fin r → ℕ)}
    (hD : D ∈ diagrams m r) : permCfg σ D ∈ diagrams m r := by
  classical
  obtain ⟨hdiag, hmu, hcard⟩ := hD
  refine ⟨isDiagram_permCfg σ hdiag, ?_, ?_⟩
  · intro q hq
    rw [← permCfg_mu σ] at hq
    rw [permCfg, Finset.mem_image] at hq ⊢
    obtain ⟨p, hp, rfl⟩ := hq
    exact ⟨p, hmu hp, rfl⟩
  · rw [permCfg, Finset.card_image_of_injective _ (permPt_injective σ), hcard]

/-- The `S_r`-action on strict diagrams. -/
noncomputable instance diagramsAction (m r : ℕ) :
    MulAction (Equiv.Perm (Fin r)) {D : Finset (Fin r → ℕ) // D ∈ diagrams m r} where
  smul σ D := ⟨permCfg σ (D : Finset (Fin r → ℕ)), permCfg_mem_diagrams σ D.2⟩
  one_smul D := Subtype.ext (permCfg_one (D : Finset (Fin r → ℕ)))
  mul_smul σ τ D := Subtype.ext (permCfg_mul σ τ (D : Finset (Fin r → ℕ)))

theorem diagramsAction_smul_coe {m r : ℕ} (σ : Equiv.Perm (Fin r))
    (D : {D : Finset (Fin r → ℕ) // D ∈ diagrams m r}) :
    ((σ • D : {D : Finset (Fin r → ℕ) // D ∈ diagrams m r}) : Finset (Fin r → ℕ))
      = permCfg σ (D : Finset (Fin r → ℕ)) := rfl

instance diagramsSubtypeFinite (m r : ℕ) :
    Finite {D : Finset (Fin r → ℕ) // D ∈ diagrams m r} :=
  (diagrams_finite m r).to_subtype

/-- The stabiliser of a diagram IS its symmetry group `H` in [G]'s sense. -/
theorem stabilizer_eq_autCfgGroup_diagrams {m r : ℕ}
    (D : {D : Finset (Fin r → ℕ) // D ∈ diagrams m r}) :
    MulAction.stabilizer (Equiv.Perm (Fin r)) D
      = autCfgGroup (D : Finset (Fin r → ℕ)) := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, mem_autCfgGroup]
  constructor
  · intro h
    have h' := congrArg (fun T : {D : Finset (Fin r → ℕ) // D ∈ diagrams m r} =>
      (T : Finset (Fin r → ℕ))) h
    rw [diagramsAction_smul_coe] at h'
    exact h'
  · intro h
    exact Subtype.ext (by rw [diagramsAction_smul_coe, h])

theorem card_orbit_mul_card_autCfg_diagrams {m r : ℕ}
    (D : {D : Finset (Fin r → ℕ) // D ∈ diagrams m r}) :
    Nat.card (MulAction.orbit (Equiv.Perm (Fin r)) D)
        * (autCfg (D : Finset (Fin r → ℕ))).card = r.factorial := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Equiv.Perm (Fin r)) D)
  rw [Nat.card_prod, stabilizer_eq_autCfgGroup_diagrams, card_autCfgGroup] at h
  rw [h, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The classes ("gFDs") form a finite type, so they can be summed over. -/
noncomputable instance diagramsOrbitFintype (m r : ℕ) :
    Fintype (MulAction.orbitRel.Quotient (Equiv.Perm (Fin r))
      {D : Finset (Fin r → ℕ) // D ∈ diagrams m r}) := Fintype.ofFinite _

/-- **[G]'s equation (2.3) with the weight of its own definition.**  There is a weight on
each class — exactly `r!/|H|`, stated without division so the exactness is part of the
claim — whose total is `a_{m+r+1,r}`.

So the labelled count this module uses and [G]'s weighted sum over classes are the same
number, and the row does not turn on which of the two (2.3) means. -/
theorem aCount_eq_weighted_class_sum (m r : ℕ) :
    ∃ w : MulAction.orbitRel.Quotient (Equiv.Perm (Fin r))
            {D : Finset (Fin r → ℕ) // D ∈ diagrams m r} → ℕ,
      (∀ ω, w ω * (autCfg ((ω.out : {D : Finset (Fin r → ℕ) // D ∈ diagrams m r}) :
              Finset (Fin r → ℕ))).card = r.factorial)
        ∧ aCount m r = ∑ ω, w ω := by
  classical
  refine ⟨fun ω => Nat.card (MulAction.orbit (Equiv.Perm (Fin r)) ω.out),
    fun ω => card_orbit_mul_card_autCfg_diagrams _, ?_⟩
  rw [aCount, Nat.card_congr (MulAction.selfEquivSigmaOrbits (Equiv.Perm (Fin r))
    {D : Finset (Fin r → ℕ) // D ∈ diagrams m r}), Nat.card_sigma]

end Principia.MathDB.P323219
