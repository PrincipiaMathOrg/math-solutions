/-
Copyright (c) 2026 PrincipiaAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Graded counting convolves along a product decomposition

If a `ℕ`-valued statistic on `A` is carried by an equivalence `e : A ≃ B × C` to the SUM of
statistics on the two factors, then the level-set counts of `A` are the Cauchy convolution of
those of `B` and `C` -- and therefore the generating functions multiply.

Promoted out of MathDB #374964 (the ordinal-sum factorisation of polar preorder-polytope
`h*`-polynomials), which paid for it. **Nothing here mentions a preorder, an order polytope, a
gauge or an `h*`-polynomial**: every statement quantifies over arbitrary types `A`, `B`, `C`, an
arbitrary equivalence, and arbitrary `ℕ`-valued statistics. That campaign's contribution was the
INSTANTIATION -- its `Φ` is such an `e` and its `gauge_additive` is the splitting hypothesis --
and the instantiation stays behind in the campaign.

**Two forms, because finiteness arrives in two shapes.** `card_filter_convolve` assumes
`Fintype A` and reads the level sets off `univ.filter`. A graded space need not be a `Fintype`
(the motivating case is `ℤ^E`, where only each individual level set is finite), so
`convolves_of_finsets` takes the level sets as `Finset` families characterised by membership and
never mentions a `Fintype` on `A` at all. Neither subsumes the other in use: the first is what you
want when the ambient type is finite, the second when only the fibres are.

`Convolves` is the predicate, `powerSeries_mul_of_convolves` is the bridge to `PowerSeries`
multiplication (via `PowerSeries.coeff_mul` and the antidiagonal-to-range rewrite), and
`convolves_of_split` packages `card_filter_convolve` in the predicate's vocabulary so a caller
discharges a carried convolution hypothesis the moment it exhibits a splitting equivalence.

**What deliberately did NOT come along.** #374964's `hStar_mul` -- that
`(1 - X)^(n₁+n₂) * mk ab` factors when `Convolves a b ab` -- is *general as a statement* and
mentions no campaign object either, but it is named for, and shaped by, that campaign's
`h*`-polynomial. Moving it would require renaming it, which makes the change an edit rather than
a promotion, so it stayed. If a second row ever needs it, promote it then under a neutral name.
-/

namespace Principia.Common.GradedConvolve

open Finset

/-- The counting function `a_k(τ) = #{z : g_τ(z) = k}`, carried as an abstract sequence
together with the convolution the bijection `Φ` produces. -/
def Convolves (a b ab : ℕ → ℤ) : Prop :=
  ∀ k : ℕ, ab k = ∑ j ∈ Finset.range (k + 1), a j * b (k - j)

/-- **The generating functions multiply.**  This is `PowerSeries.coeff_mul` once the
convolution is known, and it is proved here so the carried part is only the combinatorics. -/
theorem powerSeries_mul_of_convolves {a b ab : ℕ → ℤ} (h : Convolves a b ab) :
    (PowerSeries.mk ab : PowerSeries ℤ) = PowerSeries.mk a * PowerSeries.mk b := by
  ext k
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, h k]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (PowerSeries.mk a).coeff i *
    (PowerSeries.mk b).coeff j)]
  exact Finset.sum_congr rfl (fun j _ => by simp [PowerSeries.coeff_mk])

/-- **Counts convolve across a value-splitting equivalence.**

If `e : A ≃ B × C` carries a `ℕ`-valued statistic `vA` to the SUM of statistics on the two
factors, then the level-set counts satisfy the Cauchy convolution.  This is the whole
combinatorial content of the ordinal-sum factorisation: `Φ` is such an `e`, and
`gauge_additive` is the splitting hypothesis. -/
theorem card_filter_convolve {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (vA : A → ℕ) (vB : B → ℕ) (vC : C → ℕ) (e : A ≃ B × C)
    (hsplit : ∀ a, vA a = vB (e a).1 + vC (e a).2) (k : ℕ) :
    (univ.filter (fun a => vA a = k)).card
      = ∑ j ∈ Finset.range (k + 1),
          (univ.filter (fun b => vB b = j)).card
            * (univ.filter (fun c => vC c = k - j)).card := by
  classical
  -- transport the level set along `e`
  have h1 : (univ.filter (fun a => vA a = k)).card
      = (univ.filter (fun z : B × C => vB z.1 + vC z.2 = k)).card := by
    refine Finset.card_nbij' (fun a => e a) (fun z => e.symm z) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and] at ha ⊢
      rw [← hsplit a]; exact ha
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and] at hz ⊢
      rw [hsplit (e.symm z), Equiv.apply_symm_apply]; exact hz
    · intro a _; exact e.symm_apply_apply a
    · intro z _; exact e.apply_symm_apply z
  rw [h1]
  -- split the pair level set by the value on the first factor
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun z : B × C => vB z.1) (t := Finset.range (k + 1)) (fun z hz => ?_)]
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
    have hset : ((univ.filter (fun z : B × C => vB z.1 + vC z.2 = k)).filter
          (fun z => vB z.1 = j))
        = (univ.filter (fun b => vB b = j)) ×ˢ (univ.filter (fun c => vC c = k - j)) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
      constructor
      · rintro ⟨hk, hj'⟩
        exact ⟨hj', by omega⟩
      · rintro ⟨hj', hc⟩
        exact ⟨by omega, hj'⟩
    rw [hset, Finset.card_product]
  · have hz' : vB z.1 + vC z.2 = k := by simpa using hz
    show vB z.1 ∈ Finset.range (k + 1)
    exact Finset.mem_range.mpr (by omega)

/-- **`Convolves` from the splitting.**  Packaged in the spine's own vocabulary, so the
carried hypothesis is discharged the moment a splitting equivalence is exhibited. -/
theorem convolves_of_split {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (vA : A → ℕ) (vB : B → ℕ) (vC : C → ℕ) (e : A ≃ B × C)
    (hsplit : ∀ a, vA a = vB (e a).1 + vC (e a).2) :
    Convolves (fun j => ((univ.filter (fun b => vB b = j)).card : ℤ))
      (fun l => ((univ.filter (fun c => vC c = l)).card : ℤ))
      (fun k => ((univ.filter (fun a => vA a = k)).card : ℤ)) := by
  intro k
  show ((univ.filter (fun a => vA a = k)).card : ℤ)
      = ∑ j ∈ Finset.range (k + 1),
          ((univ.filter (fun b => vB b = j)).card : ℤ)
            * ((univ.filter (fun c => vC c = k - j)).card : ℤ)
  rw [card_filter_convolve vA vB vC e hsplit k]
  push_cast
  rfl

/-- **Counts convolve when the level sets are given as explicit `Finset`s.**

`card_filter_convolve` needs `Fintype A`, which the gauge's ambient space `ℤ^E` is not.  What
is actually available is that each LEVEL SET is finite (`fiber_box`), so the statement takes
the level sets as `Finset`s and never mentions a `Fintype`. -/
theorem convolves_of_finsets {A B C : Type*} [DecidableEq B] [DecidableEq C]
    (vA : A → ℕ) (vB : B → ℕ) (vC : C → ℕ) (e : A ≃ B × C)
    (hsplit : ∀ a, vA a = vB (e a).1 + vC (e a).2)
    (FA : ℕ → Finset A) (FB : ℕ → Finset B) (FC : ℕ → Finset C)
    (hFA : ∀ k a, a ∈ FA k ↔ vA a = k)
    (hFB : ∀ j b, b ∈ FB j ↔ vB b = j)
    (hFC : ∀ l c, c ∈ FC l ↔ vC c = l) :
    Convolves (fun j => ((FB j).card : ℤ)) (fun l => ((FC l).card : ℤ))
      (fun k => ((FA k).card : ℤ)) := by
  classical
  intro k
  show ((FA k).card : ℤ)
      = ∑ j ∈ Finset.range (k + 1), ((FB j).card : ℤ) * ((FC (k - j)).card : ℤ)
  have hmapcard : (FA k).card = ((FA k).map e.toEmbedding).card := (Finset.card_map _).symm
  have hset : (FA k).map e.toEmbedding
      = (Finset.range (k + 1)).biUnion (fun j => (FB j) ×ˢ (FC (k - j))) := by
    ext z
    simp only [Finset.mem_map_equiv, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_product]
    constructor
    · intro hz
      rw [hFA] at hz
      rw [hsplit (e.symm z), Equiv.apply_symm_apply] at hz
      refine ⟨vB z.1, by omega, ?_, ?_⟩
      · exact (hFB _ _).mpr rfl
      · exact (hFC _ _).mpr (by omega)
    · rintro ⟨j, hj, hb, hc⟩
      rw [hFB] at hb
      rw [hFC] at hc
      rw [hFA, hsplit (e.symm z), Equiv.apply_symm_apply]
      omega
  have hdisj : ∀ x ∈ Finset.range (k + 1), ∀ y ∈ Finset.range (k + 1), x ≠ y →
      Disjoint ((FB x) ×ˢ (FC (k - x))) ((FB y) ×ˢ (FC (k - y))) := by
    intro x _ y _ hxy
    rw [Finset.disjoint_left]
    rintro z hzx hzy
    rw [Finset.mem_product] at hzx hzy
    have h1 := (hFB _ _).mp hzx.1
    have h2 := (hFB _ _).mp hzy.1
    exact hxy (by omega)
  rw [hmapcard, hset, Finset.card_biUnion hdisj]
  push_cast
  exact Finset.sum_congr rfl (fun j _ => by rw [Finset.card_product]; push_cast; ring)

end Principia.Common.GradedConvolve
