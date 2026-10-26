/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# Restriction to a coordinate subset, and extension by zero

**PROMOTED to `Common/` on 2026-09-24**, out of MathDB #323219, which paid for it.  The
promotion test the project applies is whether a declaration mentions the campaign's objects,
and not one of these twenty does: there is no Ferrers diagram, no `μ_r`, no reduced
configuration and no `α`-triangle below.  What is left is the adjunction between functions on
`Fin r` supported in a `Finset K` and functions on `Fin K.card`, which any counting argument
that reindexes a support will want.

## What is here

* `supp S` — the coordinates some member of `S` is nonzero at, with `mem_supp` and
  `zero_of_not_mem_supp`/`zero_off_supp` (the same fact, packaged for two consumers).
* `restrictTo K` and `extendByZero K` — the two directions, with both round trips:
  `restrictTo_extendByZero` unconditionally, `extendByZero_restrictTo` for points vanishing off
  `K`.  **Write both halves or neither**: the pair is what makes the map a bijection, and the
  inverse is the same function the monotonicity argument needs.
* `extendByZero_le` — the lift is admissible: `y ≤ restrictTo K q` gives `extendByZero K y ≤ q`.
  This is what lets a lower-set property known upstairs be applied to a point produced
  downstairs.
* `equivFin_index_iff` — the index correspondence under `K.equivFin`, as an EQUIVALENCE.
  Proving the equivalence rather than substituting is what avoids destroying the coordinate
  still being reasoned about; both unit-vector arguments need it on each branch of an `if`.
* `restrictTo_zero`/`restrictTo_single` and `extendByZero_zero`/`extendByZero_single` — the two
  maps on the distinguished points, in both directions.
* `restrictTo_injOn`, `extendByZero_injective`, `card_image_extendByZero`,
  `restrictTo_image_uses` — the counting consequences.
* `sum_powerset_by_card` — `∑_{K ⊆ univ} g |K| = ∑_{k ≤ r} C(r,k)·g k`.  Independent of the
  rest, and the only place a binomial coefficient enters the argument it came from.

## The name had to change, and the reason generalises

This was `extendFrom` inside the campaign's namespace, where it SHADOWED Mathlib's
`_root_.extendFrom` — the topological extension of a function from a subset by limits, an
entirely different operation — and nothing complained. Promoting it here and `open`ing the
namespace put the two at equal priority and made every use site ambiguous. **A local
declaration can sit on top of a Mathlib name for as long as it stays local; promotion is
when you find out.** Grep `_root_.<name>` before promoting, not after.

## The one design decision worth carrying forward

`restrictTo` and `extendByZero` take the coordinate set `K` as a PARAMETER rather than deriving
it from the data.  The target type `Fin K.card → ℕ` depends on `K`, so a version that computed
`K` internally would make every rewrite a dependent-type transport; with `K` a parameter the
transports never arise.  That is why `supp` is a separate definition and is never unfolded
inside the adjunction.
-/
import Mathlib

set_option autoImplicit false

open Finset

namespace Principia.Common.FinsetReindex

/-- **The support of a family**: the coordinates at which some member is nonzero. -/
def supp {r : ℕ} (S : Finset (Fin r → ℕ)) : Finset (Fin r) :=
  univ.filter (fun i => ∃ p ∈ S, p i ≠ 0)

theorem mem_supp {r : ℕ} {S : Finset (Fin r → ℕ)} {i : Fin r} :
    i ∈ supp S ↔ ∃ p ∈ S, p i ≠ 0 := by
  classical
  rw [supp, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ i, h⟩⟩

/-- Off the support every member vanishes — which is what makes the restriction
injective, and hence what makes the reindexing preserve cardinality. -/
theorem zero_of_not_mem_supp {r : ℕ} {S : Finset (Fin r → ℕ)} {p : Fin r → ℕ}
    (hp : p ∈ S) {i : Fin r} (hi : i ∉ supp S) : p i = 0 := by
  by_contra h
  exact hi (mem_supp.mpr ⟨p, hp, h⟩)

/-- Restriction of a point to a coordinate subset, reindexed to `Fin K.card`. -/
noncomputable def restrictTo {r : ℕ} (K : Finset (Fin r)) (q : Fin r → ℕ) :
    Fin K.card → ℕ :=
  fun j => q (K.equivFin.symm j : Fin r)

/-- **The restriction is injective on `S`.**  Two members agreeing on the support agree
everywhere, because both vanish off it. -/
theorem restrictTo_injOn {r : ℕ} (S : Finset (Fin r → ℕ)) :
    Set.InjOn (restrictTo (supp S)) S := by
  classical
  intro p hp q hq hpq
  funext i
  by_cases hi : i ∈ supp S
  · have h := congrFun hpq ((supp S).equivFin ⟨i, hi⟩)
    simpa only [restrictTo, Equiv.symm_apply_apply] using h
  · rw [zero_of_not_mem_supp hp hi, zero_of_not_mem_supp hq hi]

/-- **Extension by zero along a coordinate subset** — the inverse of `restrictTo`.

This is the direction a downward-closure argument needs.  A property known about the
AMBIENT family (that it is closed under passing to smaller points, say) cannot be applied
to a point produced downstairs; lifting the point back to `Fin r` by zero, applying the
property there, and restricting again is what makes it usable.  `extendByZero_le` is the
step that makes the lift admissible. -/
noncomputable def extendByZero {r : ℕ} (K : Finset (Fin r)) (y : Fin K.card → ℕ) : Fin r → ℕ :=
  fun l => if h : l ∈ K then y (K.equivFin ⟨l, h⟩) else 0

theorem extendByZero_of_not_mem {r : ℕ} (K : Finset (Fin r)) (y : Fin K.card → ℕ)
    {l : Fin r} (hl : l ∉ K) : extendByZero K y l = 0 := by
  simp only [extendByZero, dif_neg hl]

/-- `restrict ∘ extend = id`. -/
theorem restrictTo_extendByZero {r : ℕ} (K : Finset (Fin r)) (y : Fin K.card → ℕ) :
    restrictTo K (extendByZero K y) = y := by
  funext j
  have hmem : ((K.equivFin.symm j : {x // x ∈ K}) : Fin r) ∈ K := (K.equivFin.symm j).2
  simp only [restrictTo, extendByZero, dif_pos hmem]
  congr 1
  exact K.equivFin.apply_symm_apply j

/-- `extend ∘ restrict = id`, for points that already vanish off `K`. -/
theorem extendByZero_restrictTo {r : ℕ} (K : Finset (Fin r)) {q : Fin r → ℕ}
    (hq : ∀ l, l ∉ K → q l = 0) : extendByZero K (restrictTo K q) = q := by
  funext l
  simp only [extendByZero]
  split_ifs with h
  · simp only [restrictTo, Equiv.symm_apply_apply]
  · exact (hq l h).symm

/-- The extension is monotone into `q` whenever the restriction was. -/
theorem extendByZero_le {r : ℕ} (K : Finset (Fin r)) {y : Fin K.card → ℕ} {q : Fin r → ℕ}
    (h : y ≤ restrictTo K q) : extendByZero K y ≤ q := by
  intro l
  simp only [extendByZero]
  split_ifs with hl
  · have hj := h (K.equivFin ⟨l, hl⟩)
    simpa only [restrictTo, Equiv.symm_apply_apply] using hj
  · exact Nat.zero_le _

/-- **Every coordinate of the reindexed family is genuinely used.**  Restricting to the
support leaves no dead coordinate — which is the whole reason to reindex by it. -/
theorem restrictTo_image_uses {r : ℕ} (S : Finset (Fin r → ℕ)) (j : Fin (supp S).card) :
    ∃ q ∈ S.image (restrictTo (supp S)), q j ≠ 0 := by
  classical
  have hmem : (((supp S).equivFin.symm j : {x // x ∈ supp S}) : Fin r) ∈ supp S :=
    ((supp S).equivFin.symm j).2
  obtain ⟨p, hp, hpne⟩ := mem_supp.mp hmem
  exact ⟨restrictTo (supp S) p, Finset.mem_image_of_mem _ hp, hpne⟩

/-- A point of `S` vanishes off `supp S`, packaged for `extendByZero_restrictTo`. -/
theorem zero_off_supp {r : ℕ} {S : Finset (Fin r → ℕ)} {p : Fin r → ℕ} (hp : p ∈ S) :
    ∀ l, l ∉ supp S → p l = 0 :=
  fun _ hl => zero_of_not_mem_supp hp hl

/-- The two index conditions correspond under `K.equivFin`.  Factored out because both the
unit-vector cases need it on each branch of an `if`, and because proving the equivalence is
what avoids a `subst` that would destroy the coordinate being reasoned about. -/
theorem equivFin_index_iff {r : ℕ} (K : Finset (Fin r)) {i : Fin r} (hi : i ∈ K)
    (j : Fin K.card) :
    ((K.equivFin.symm j : {x // x ∈ K}) : Fin r) = i ↔ j = K.equivFin ⟨i, hi⟩ := by
  constructor
  · intro h
    have hsub : K.equivFin.symm j = (⟨i, hi⟩ : {x // x ∈ K}) := Subtype.ext h
    rw [← hsub, Equiv.apply_symm_apply]
  · intro h
    rw [h, Equiv.symm_apply_apply]

theorem restrictTo_zero {r : ℕ} (K : Finset (Fin r)) :
    restrictTo K (0 : Fin r → ℕ) = 0 := rfl

/-- A unit vector restricts to a unit vector, at the reindexed coordinate. -/
theorem restrictTo_single {r : ℕ} (K : Finset (Fin r)) {i : Fin r} (hi : i ∈ K) :
    restrictTo K (Pi.single i 1 : Fin r → ℕ) = Pi.single (K.equivFin ⟨i, hi⟩) 1 := by
  funext j
  simp only [restrictTo, Pi.single_apply]
  by_cases h : ((K.equivFin.symm j : {x // x ∈ K}) : Fin r) = i
  · rw [if_pos h, if_pos ((equivFin_index_iff K hi j).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((equivFin_index_iff K hi j).mpr hc))]

/-- `extendByZero K` is injective — immediate from the round trip. -/
theorem extendByZero_injective {r : ℕ} (K : Finset (Fin r)) :
    Function.Injective (extendByZero K) := by
  intro a b hab
  rw [← restrictTo_extendByZero K a, ← restrictTo_extendByZero K b, hab]

theorem card_image_extendByZero {r : ℕ} (K : Finset (Fin r))
    (S' : Finset (Fin K.card → ℕ)) :
    (S'.image (extendByZero K)).card = S'.card :=
  Finset.card_image_of_injective _ (extendByZero_injective K)

theorem extendByZero_zero {r : ℕ} (K : Finset (Fin r)) :
    extendByZero K (0 : Fin K.card → ℕ) = 0 := by
  funext l
  simp only [extendByZero, Pi.zero_apply]
  split_ifs <;> rfl

/-- A unit vector lifts to a unit vector, at the un-reindexed coordinate. -/
theorem extendByZero_single {r : ℕ} (K : Finset (Fin r)) (j : Fin K.card) :
    extendByZero K (Pi.single j 1 : Fin K.card → ℕ)
      = Pi.single ((K.equivFin.symm j : {x // x ∈ K}) : Fin r) 1 := by
  classical
  have hiK : ((K.equivFin.symm j : {x // x ∈ K}) : Fin r) ∈ K := (K.equivFin.symm j).2
  have hzero : ∀ l, l ∉ K →
      (Pi.single ((K.equivFin.symm j : {x // x ∈ K}) : Fin r) 1 : Fin r → ℕ) l = 0 := by
    intro l hl
    rw [Pi.single_apply, if_neg]
    intro hc
    exact hl (by rw [hc]; exact hiK)
  have h1 : restrictTo K
      (Pi.single ((K.equivFin.symm j : {x // x ∈ K}) : Fin r) 1 : Fin r → ℕ)
      = Pi.single j 1 := by
    rw [restrictTo_single K hiK]
    congr 1
    exact ((equivFin_index_iff K hiK j).mp rfl).symm
  rw [← h1, extendByZero_restrictTo K hzero]

/-- **`∑_{K ⊆ univ} g |K| = ∑_{k ≤ r} C(r,k)·g k`.**  Summing a function of the CARDINALITY
over all subsets of `Fin r` collapses to a binomial sum over the cardinality.  Independent
of the rest of this file. -/
theorem sum_powerset_by_card {r : ℕ} (g : ℕ → ℕ) :
    ∑ K ∈ (univ : Finset (Fin r)).powerset, g K.card
      = ∑ k ∈ Finset.range (r + 1), r.choose k * g k := by
  classical
  have hmaps : ∀ K ∈ (univ : Finset (Fin r)).powerset,
      K.card ∈ Finset.range (r + 1) := by
    intro K hK
    rw [Finset.mem_range, Nat.lt_succ_iff]
    calc K.card ≤ (univ : Finset (Fin r)).card :=
          Finset.card_le_card (Finset.mem_powerset.mp hK)
      _ = r := by rw [Finset.card_univ, Fintype.card_fin]
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps g]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_const, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end Principia.Common.FinsetReindex
