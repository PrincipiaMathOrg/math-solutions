import Mathlib

/-!
# MathDB #367940 — words over `m` letters with a given Fubini ranking

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/367940/solution.tex`, §1–2.  A *Fubini ranking* of length `n` is a
word `x` with `x i = 1 + #{k | x k < x i}` (competition ranks with ties, `IsFub`).  Every word
`y` over a linear order has one, `fub y`, with the same strict comparisons (`fub_lt_iff`).  The
write-up passes through packed words and chooses the used subalphabet; here the two steps are one
bijection: for a Fubini ranking `x` with `d` distinct values, the words `y : Fin n → Fin m` with
`fub y = x` correspond to their value sets, the `d`-subsets of `Fin m` (`card_fiber`), so there are
`C(m, d)` of them.  The maximum-run count is the consumer.
-/

namespace Principia.MathDB.P367940

open Finset

variable {n : ℕ}

/-- `#{k | y k < y i}`. -/
def rk {α : Type*} [LinearOrder α] (y : Fin n → α) (i : Fin n) : ℕ :=
  (univ.filter fun k => y k < y i).card

/-- The number of distinct values of `y`. -/
def dv {α : Type*} [LinearOrder α] (y : Fin n → α) : ℕ := (univ.image y).card

/-- The number of distinct values of `y` below `y i`. -/
def drk {α : Type*} [LinearOrder α] (y : Fin n → α) (i : Fin n) : ℕ :=
  ((univ.image y).filter fun v => v < y i).card

/-- A Fubini ranking of length `n`, with values in `{1, …, n}`. -/
def IsFub (x : Fin n → Fin (n + 1)) : Prop := ∀ i, (x i : ℕ) = 1 + rk x i

theorem rk_lt {α : Type*} [LinearOrder α] (y : Fin n → α) (i : Fin n) : rk y i < n := by
  have h : (univ.filter fun k => y k < y i) ⊂ univ :=
    Finset.ssubset_iff_subset_ne.2 ⟨filter_subset _ _, fun h => by
      have : i ∈ univ.filter fun k => y k < y i := by rw [h]; exact mem_univ i
      exact lt_irrefl _ (mem_filter.1 this).2⟩
  simpa [rk] using card_lt_card h

/-- The Fubini ranking of a word. -/
def fub {α : Type*} [LinearOrder α] (y : Fin n → α) : Fin n → Fin (n + 1) :=
  fun i => ⟨1 + rk y i, by have := rk_lt y i; omega⟩

theorem rk_lt_iff {α : Type*} [LinearOrder α] (y : Fin n → α) (i k : Fin n) :
    rk y k < rk y i ↔ y k < y i := by
  constructor
  · intro h
    by_contra hc
    rw [not_lt] at hc
    have : (univ.filter fun l => y l < y i) ⊆ univ.filter fun l => y l < y k := by
      intro l hl
      rw [mem_filter] at hl ⊢
      exact ⟨hl.1, lt_of_lt_of_le hl.2 hc⟩
    exact absurd (card_le_card this) (not_le.2 h)
  · intro h
    refine card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨fun l hl => ?_, fun he => ?_⟩)
    · rw [mem_filter] at hl ⊢
      exact ⟨hl.1, hl.2.trans h⟩
    · have : k ∈ univ.filter fun l => y l < y i := mem_filter.2 ⟨mem_univ _, h⟩
      rw [← he, mem_filter] at this
      exact lt_irrefl _ this.2

theorem fub_lt_iff {α : Type*} [LinearOrder α] (y : Fin n → α) (i k : Fin n) :
    fub y k < fub y i ↔ y k < y i := by
  change 1 + rk y k < 1 + rk y i ↔ y k < y i
  rw [← rk_lt_iff y i k]
  omega

/-- Words with the same strict comparisons. -/
def OE {α β : Type*} [LinearOrder α] [LinearOrder β] (y : Fin n → α) (z : Fin n → β) : Prop :=
  ∀ i k, y k < y i ↔ z k < z i

theorem OE.symm {α β : Type*} [LinearOrder α] [LinearOrder β] {y : Fin n → α} {z : Fin n → β}
    (h : OE y z) : OE z y := fun i k => (h i k).symm

theorem OE.eq_iff {α β : Type*} [LinearOrder α] [LinearOrder β] {y : Fin n → α} {z : Fin n → β}
    (h : OE y z) (i k : Fin n) : y k = y i ↔ z k = z i := by
  constructor
  · intro he
    rcases lt_trichotomy (z k) (z i) with hl | hl | hl
    · exact absurd ((h i k).2 hl) (by rw [he]; exact lt_irrefl _)
    · exact hl
    · exact absurd ((h k i).2 hl) (by rw [he]; exact lt_irrefl _)
  · intro he
    rcases lt_trichotomy (y k) (y i) with hl | hl | hl
    · exact absurd ((h i k).1 hl) (by rw [he]; exact lt_irrefl _)
    · exact hl
    · exact absurd ((h k i).1 hl) (by rw [he]; exact lt_irrefl _)

theorem oe_fub {α : Type*} [LinearOrder α] (y : Fin n → α) : OE (fub y) y :=
  fun i k => fub_lt_iff y i k

theorem rk_eq_of_oe {α β : Type*} [LinearOrder α] [LinearOrder β] {y : Fin n → α}
    {z : Fin n → β} (h : OE y z) (i : Fin n) : rk y i = rk z i := by
  unfold rk
  congr 1
  ext k
  simp only [mem_filter, mem_univ, true_and]
  exact h i k

theorem fub_eq_of_oe {α β : Type*} [LinearOrder α] [LinearOrder β] {y : Fin n → α}
    {z : Fin n → β} (h : OE y z) : fub y = fub z := by
  funext i
  exact Fin.ext (by simp only [fub, rk_eq_of_oe h i])

theorem fub_isFub {α : Type*} [LinearOrder α] (y : Fin n → α) : IsFub (fub y) := fun i => by
  change 1 + rk y i = 1 + rk (fub y) i
  rw [rk_eq_of_oe (oe_fub y) i]

theorem fub_self {x : Fin n → Fin (n + 1)} (hx : IsFub x) : fub x = x := by
  funext i
  exact Fin.ext (hx i).symm

/-- Images of a finset under maps inducing the same equalities have the same size. -/
theorem card_image_eq {α β : Type*} [DecidableEq α] [DecidableEq β] (T : Finset (Fin n))
    (y : Fin n → α) (z : Fin n → β) (h : ∀ k ∈ T, ∀ l ∈ T, y k = y l ↔ z k = z l) :
    (T.image y).card = (T.image z).card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have h' : ∀ k ∈ T, ∀ l ∈ T, y k = y l ↔ z k = z l := fun k hk l hl =>
      h k (mem_insert_of_mem hk) l (mem_insert_of_mem hl)
    rw [image_insert, image_insert]
    have hmem : y a ∈ T.image y ↔ z a ∈ T.image z := by
      simp only [mem_image]
      constructor
      · rintro ⟨k, hk, hk'⟩
        exact ⟨k, hk, (h k (mem_insert_of_mem hk) a (mem_insert_self a T)).1 hk'⟩
      · rintro ⟨k, hk, hk'⟩
        exact ⟨k, hk, (h k (mem_insert_of_mem hk) a (mem_insert_self a T)).2 hk'⟩
    by_cases hy : y a ∈ T.image y
    · rw [insert_eq_of_mem hy, insert_eq_of_mem (hmem.1 hy), ih h']
    · rw [card_insert_of_notMem hy, card_insert_of_notMem (fun hz => hy (hmem.2 hz)), ih h']

theorem dv_eq_of_oe {α β : Type*} [LinearOrder α] [LinearOrder β] {y : Fin n → α}
    {z : Fin n → β} (h : OE y z) : dv y = dv z :=
  card_image_eq univ y z fun k _ l _ => h.eq_iff l k

theorem drk_eq_filter {α : Type*} [LinearOrder α] (y : Fin n → α) (i : Fin n) :
    drk y i = ((univ.filter fun k => y k < y i).image y).card := by
  unfold drk
  congr 1
  ext v
  simp only [mem_filter, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨⟨k, rfl⟩, hk⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, rfl⟩, hk⟩

theorem drk_eq_of_oe {α β : Type*} [LinearOrder α] [LinearOrder β] {y : Fin n → α}
    {z : Fin n → β} (h : OE y z) (i : Fin n) : drk y i = drk z i := by
  rw [drk_eq_filter, drk_eq_filter]
  have hT : (univ.filter fun k => y k < y i) = univ.filter fun k => z k < z i := by
    ext k
    simp only [mem_filter, mem_univ, true_and]
    exact h i k
  rw [hT]
  exact card_image_eq _ y z fun k _ l _ => h.eq_iff l k

theorem drk_lt {α : Type*} [LinearOrder α] (y : Fin n → α) (i : Fin n) : drk y i < dv y := by
  refine card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨filter_subset _ _, fun he => ?_⟩)
  have : y i ∈ (univ.image y).filter fun v => v < y i := by
    rw [he]
    exact mem_image_of_mem y (mem_univ i)
  exact lt_irrefl _ (mem_filter.1 this).2

theorem drk_lt_iff {α : Type*} [LinearOrder α] (y : Fin n → α) (i k : Fin n) :
    drk y k < drk y i ↔ y k < y i := by
  constructor
  · intro h
    by_contra hc
    rw [not_lt] at hc
    have : ((univ.image y).filter fun v => v < y i) ⊆ (univ.image y).filter fun v => v < y k := by
      intro v hv
      rw [mem_filter] at hv ⊢
      exact ⟨hv.1, lt_of_lt_of_le hv.2 hc⟩
    exact absurd (card_le_card this) (not_le.2 h)
  · intro h
    refine card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨fun v hv => ?_, fun he => ?_⟩)
    · rw [mem_filter] at hv ⊢
      exact ⟨hv.1, hv.2.trans h⟩
    · have : y k ∈ (univ.image y).filter fun v => v < y i :=
        mem_filter.2 ⟨mem_image_of_mem y (mem_univ k), h⟩
      rw [← he, mem_filter] at this
      exact lt_irrefl _ this.2

/-- **The fiber of `fub` over a Fubini ranking with `d` values has `C(m, d)` words.** -/
theorem card_fiber (m : ℕ) {x : Fin n → Fin (n + 1)} (hx : IsFub x) :
    (univ.filter fun y : Fin n → Fin m => fub y = x).card = m.choose (dv x) := by
  classical
  have hoe : ∀ y : Fin n → Fin m, fub y = x → OE y x := fun y hy i k => by
    rw [← fub_lt_iff y i k, hy]
  have hC : m.choose (dv x) = (powersetCard (dv x) (univ : Finset (Fin m))).card := by
    rw [card_powersetCard, card_univ, Fintype.card_fin]
  rw [hC]
  refine card_bij (fun y _ => univ.image y) ?_ ?_ ?_
  · intro y hy
    have hy' := (mem_filter.1 hy).2
    rw [mem_powersetCard]
    exact ⟨subset_univ _, dv_eq_of_oe (hoe y hy')⟩
  · intro y1 hy1 y2 hy2 himg
    have h1 := hoe y1 (mem_filter.1 hy1).2
    have h2 := hoe y2 (mem_filter.1 hy2).2
    funext i
    have r1 := drk_eq_of_oe h1 i
    have r2 := drk_eq_of_oe h2 i
    unfold drk at r1 r2
    have himg' : univ.image y1 = univ.image y2 := himg
    rw [himg'] at r1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : ((univ.image y2).filter fun v => v < y1 i)
          ⊂ (univ.image y2).filter fun v => v < y2 i := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨fun v hv => ?_, fun he => ?_⟩
        · rw [mem_filter] at hv ⊢
          exact ⟨hv.1, hv.2.trans hlt⟩
        · have : y1 i ∈ (univ.image y2).filter fun v => v < y2 i :=
            mem_filter.2 ⟨himg' ▸ mem_image_of_mem y1 (mem_univ i), hlt⟩
          rw [← he, mem_filter] at this
          exact lt_irrefl _ this.2
      have := card_lt_card this
      omega
    · have : ((univ.image y2).filter fun v => v < y2 i)
          ⊂ (univ.image y2).filter fun v => v < y1 i := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨fun v hv => ?_, fun he => ?_⟩
        · rw [mem_filter] at hv ⊢
          exact ⟨hv.1, hv.2.trans hlt⟩
        · have : y2 i ∈ (univ.image y2).filter fun v => v < y1 i :=
            mem_filter.2 ⟨mem_image_of_mem y2 (mem_univ i), hlt⟩
          rw [← he, mem_filter] at this
          exact lt_irrefl _ this.2
      have := card_lt_card this
      omega
  · intro S hS
    rw [mem_powersetCard] at hS
    let y : Fin n → Fin m := fun i => S.orderEmbOfFin hS.2 ⟨drk x i, drk_lt x i⟩
    have hyx : OE y x := fun i k => by
      simp only [y, OrderEmbedding.lt_iff_lt]
      exact drk_lt_iff x i k
    refine ⟨y, mem_filter.2 ⟨mem_univ _, ?_⟩, ?_⟩
    · rw [fub_eq_of_oe hyx, fub_self hx]
    · refine eq_of_subset_of_card_le (fun v hv => ?_) ?_
      · obtain ⟨i, _, rfl⟩ := mem_image.1 hv
        exact orderEmbOfFin_mem S hS.2 _
      · rw [hS.2]
        exact (dv_eq_of_oe hyx).ge

end Principia.MathDB.P367940
