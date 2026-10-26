import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Counting weakly increasing tuples with a prescribed entry

Campaign-agnostic combinatorics, promoted out of MathDB #334350 (`Problem334350.lean`),
which is where it was paid for.  Nothing here mentions that problem.

The main result is `fiber_binom`:

> the weakly increasing `j`-tuples with entries in `[1, A]` whose `mm`-th entry equals `v`
> number `C(v + mm - 1, mm) * C((A - v) + (j - 1 - mm), j - 1 - mm)`.

Mathlib has **no** count of monotone maps (`Fin k →o Fin m`) and **no** splitting lemma for
`Finset.powersetCard` — its Vandermonde (`Nat.add_choose_eq`) is proved algebraically from
`(X+1)^m * (X+1)^n`, so there is no combinatorial bijection to reuse.

## Why the subset encoding

Two encodings of a weakly increasing tuple are standard: its GAP vector, and the set
`{l i + i}`.  The gap route needs `Fin (j+1) ≃ Fin (m+1) ⊕ Fin (j-m)`, i.e. dependent-type
surgery across a `ℕ`-subtraction.  The subset route keeps the whole split inside `Finset`:

* `split_card` — `S ↦ (S.filter (· < w), S.filter (w < ·))`, inverse `(A,B) ↦ insert w (A ∪ B)`;
* `split_Icc` — the same in binomial form over `[1, M]`.

No dependent types appear anywhere.  `split_card` is stated at arity `m + 1 + p` so that every
index is a genuine sum; `split_Icc'` re-exposes it at a general arity `k` with `k = m + 1 + p`
as a hypothesis, so callers never rewrite a type index either.

## The bijection

`enc j l = image (fun i => l i + i) univ` is injective on monotone tuples because
`i ↦ l i + i` is STRICTLY monotone, and `Finset.orderEmbOfFin_unique` identifies it with the
set's own order enumeration.  Going back, `l i = S.orderEmbOfFin h i - i` is monotone by two
counting arguments rather than by induction (`orderEmb_ge`, `orderEmb_gap`), which is what
keeps the `ℕ`-subtraction harmless.

Note `Finset.card_sdiff` in this Mathlib is the HYPOTHESIS-FREE form `#(s \ t) = #s - #(t ∩ s)`,
so `orderEmb_gap` routes its subset through `Finset.inter_eq_left`.
-/

namespace Principia.Common.MonotoneTuples

open Finset

/-- Splitting a `(m+1+p)`-subset of `T` at a distinguished element `w`, with exactly `m`
elements below it.  Stated with `m + 1 + p` rather than `j` so that no `ℕ`-subtraction
appears anywhere. -/
lemma split_card (T : Finset ℕ) (w : ℕ) (hw : w ∈ T) (m p : ℕ) :
    #((T.powersetCard (m + 1 + p)).filter
        (fun S => w ∈ S ∧ #(S.filter (fun x => x < w)) = m))
      = #((T.filter (fun x => x < w)).powersetCard m)
        * #((T.filter (fun x => w < x)).powersetCard p) := by
  rw [← Finset.card_product]
  refine Finset.card_bij'
    (fun S _ => (S.filter (fun x => x < w), S.filter (fun x => w < x)))
    (fun AB _ => insert w (AB.1 ∪ AB.2)) ?_ ?_ ?_ ?_
  · -- forward lands in the product
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS
    obtain ⟨⟨hsub, hcard⟩, hwS, hlow⟩ := hS
    simp only [Finset.mem_product, Finset.mem_powersetCard]
    refine ⟨⟨?_, hlow⟩, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hsub hx.1, hx.2⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hsub hx.1, hx.2⟩
    · -- the three blocks partition S
      have hpart : #(S.filter (fun x => x < w)) + 1 + #(S.filter (fun x => w < x)) = #S := by
        have h1 : S.filter (fun x => x < w) ∪ S.filter (fun x => w < x)
            = S.erase w := by
          ext x
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro (⟨hx, h⟩ | ⟨hx, h⟩) <;> exact ⟨by omega, hx⟩
          · rintro ⟨hne, hx⟩
            rcases lt_or_gt_of_ne hne with h | h
            · exact Or.inl ⟨hx, h⟩
            · exact Or.inr ⟨hx, h⟩
        have hdisj : Disjoint (S.filter (fun x => x < w)) (S.filter (fun x => w < x)) := by
          rw [Finset.disjoint_left]
          intro x hx hx2
          simp only [Finset.mem_filter] at hx hx2
          omega
        have := Finset.card_union_of_disjoint hdisj
        rw [h1] at this
        have herase : #(S.erase w) + 1 = #S := by
          rw [Finset.card_erase_of_mem hwS]
          have : 1 ≤ #S := Finset.card_pos.2 ⟨w, hwS⟩
          omega
        omega
      omega
  · -- backward lands in the filtered powerset
    intro AB hAB
    simp only [Finset.mem_product, Finset.mem_powersetCard] at hAB
    obtain ⟨⟨hA, hAc⟩, hB, hBc⟩ := hAB
    have hAlow : ∀ x ∈ AB.1, x < w := fun x hx => (Finset.mem_filter.1 (hA hx)).2
    have hBhigh : ∀ x ∈ AB.2, w < x := fun x hx => (Finset.mem_filter.1 (hB hx)).2
    have hwnot : w ∉ AB.1 ∪ AB.2 := by
      intro h
      rcases Finset.mem_union.1 h with h | h
      · exact absurd (hAlow w h) (lt_irrefl w)
      · exact absurd (hBhigh w h) (lt_irrefl w)
    have hdisj : Disjoint AB.1 AB.2 := by
      rw [Finset.disjoint_left]
      intro x hx hx2
      exact absurd (hBhigh x hx2) (not_lt.2 (le_of_lt (hAlow x hx)))
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self _ _, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hw
      · rcases Finset.mem_union.1 hx with h | h
        · exact (Finset.mem_filter.1 (hA h)).1
        · exact (Finset.mem_filter.1 (hB h)).1
    · rw [Finset.card_insert_of_notMem hwnot, Finset.card_union_of_disjoint hdisj, hAc, hBc]
      omega
    · have : (insert w (AB.1 ∪ AB.2)).filter (fun x => x < w) = AB.1 := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
        constructor
        · rintro ⟨rfl | h | h, hlt⟩
          · exact absurd hlt (lt_irrefl _)
          · exact h
          · exact absurd (hBhigh x h) (not_lt.2 (le_of_lt hlt))
        · intro h
          exact ⟨Or.inr (Or.inl h), hAlow x h⟩
      rw [this, hAc]
  · -- left inverse
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS
    obtain ⟨⟨hsub, hcard⟩, hwS, hlow⟩ := hS
    ext x
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (rfl | ⟨hx, _⟩ | ⟨hx, _⟩)
      · exact hwS
      · exact hx
      · exact hx
    · intro hx
      rcases lt_trichotomy x w with h | h | h
      · exact Or.inr (Or.inl ⟨hx, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨hx, h⟩)
  · -- right inverse
    intro AB hAB
    simp only [Finset.mem_product, Finset.mem_powersetCard] at hAB
    obtain ⟨⟨hA, hAc⟩, hB, hBc⟩ := hAB
    have hAlow : ∀ x ∈ AB.1, x < w := fun x hx => (Finset.mem_filter.1 (hA hx)).2
    have hBhigh : ∀ x ∈ AB.2, w < x := fun x hx => (Finset.mem_filter.1 (hB hx)).2
    ext1
    · ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro ⟨rfl | h | h, hlt⟩
        · exact absurd hlt (lt_irrefl _)
        · exact h
        · exact absurd (hBhigh x h) (not_lt.2 (le_of_lt hlt))
      · intro h
        exact ⟨Or.inr (Or.inl h), hAlow x h⟩
    · ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro ⟨rfl | h | h, hlt⟩
        · exact absurd hlt (lt_irrefl _)
        · exact absurd (hAlow x h) (not_lt.2 (le_of_lt hlt))
        · exact h
      · intro h
        exact ⟨Or.inr (Or.inr h), hBhigh x h⟩

/-- The same split over `[1, M]`, in binomial form: choosing a `(m+1+p)`-subset whose
`m`-th smallest element (0-indexed) is `w`. -/
lemma split_Icc (M w m p : ℕ) (hw : w ∈ Finset.Icc 1 M) :
    #(((Finset.Icc 1 M).powersetCard (m + 1 + p)).filter
        (fun S => w ∈ S ∧ #(S.filter (fun x => x < w)) = m))
      = (w - 1).choose m * (M - w).choose p := by
  have hlow : (Finset.Icc 1 M).filter (fun x => x < w) = Finset.Icc 1 (w - 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc] at *
    omega
  have hhigh : (Finset.Icc 1 M).filter (fun x => w < x) = Finset.Icc (w + 1) M := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc] at *
    omega
  rw [split_card _ w hw m p, hlow, hhigh, Finset.card_powersetCard,
    Finset.card_powersetCard, Nat.card_Icc, Nat.card_Icc]
  simp only [Finset.mem_Icc] at hw
  congr 2 <;> omega

/-- The classical encoding of a weakly increasing tuple as a set: `l ↦ {l i + i}`. -/
def enc (j : ℕ) (l : Fin j → ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin j)).image (fun i => l i + i)

lemma enc_strictMono {j : ℕ} {l : Fin j → ℕ} (hl : Monotone l) :
    StrictMono (fun i : Fin j => l i + i) := by
  intro a b hab
  have h1 : l a ≤ l b := hl hab.le
  have h2 : (a : ℕ) < (b : ℕ) := hab
  simp only
  omega

lemma enc_card {j : ℕ} {l : Fin j → ℕ} (hl : Monotone l) : #(enc j l) = j := by
  rw [enc, Finset.card_image_of_injective _ (enc_strictMono hl).injective, Finset.card_univ,
    Fintype.card_fin]

lemma mem_enc {j : ℕ} {l : Fin j → ℕ} {x : ℕ} : x ∈ enc j l ↔ ∃ i : Fin j, l i + i = x := by
  simp [enc]

/-- Below the `i`-th encoded value sit exactly the `i` earlier ones. -/
lemma enc_filter_lt {j : ℕ} {l : Fin j → ℕ} (hl : Monotone l) (i : Fin j) :
    #((enc j l).filter (fun x => x < l i + i)) = (i : ℕ) := by
  have hmono := enc_strictMono hl
  have hset : (enc j l).filter (fun x => x < l i + i)
      = (Finset.univ.filter (fun k : Fin j => k < i)).image (fun k => l k + k) := by
    ext x
    simp only [Finset.mem_filter, mem_enc, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨k, rfl⟩, hlt⟩
      exact ⟨k, by simpa using hmono.lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, rfl⟩, hmono hk⟩
  rw [hset, Finset.card_image_of_injective _ hmono.injective]
  have hIio : (Finset.univ.filter (fun k : Fin j => k < i)) = Finset.Iio i := by
    ext k; simp
  rw [hIio, Fin.card_Iio]

/-- A strictly monotone enumeration realizes its own image as `orderEmbOfFin`. -/
lemma image_orderEmbOfFin {S : Finset ℕ} {j : ℕ} (h : #S = j) :
    (Finset.univ : Finset (Fin j)).image (S.orderEmbOfFin h) = S := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact S.orderEmbOfFin_mem h i
  · intro hx
    have hr : x ∈ Set.range (S.orderEmbOfFin h) := by
      rw [Finset.range_orderEmbOfFin]
      exact hx
    obtain ⟨i, hi⟩ := hr
    exact ⟨i, hi⟩

/-- Below the `i`-th value of a strictly monotone enumeration sit exactly `i` values. -/
lemma image_filter_lt {j : ℕ} (f : Fin j → ℕ) (hf : StrictMono f) (i : Fin j) :
    #(((Finset.univ : Finset (Fin j)).image f).filter (fun x => x < f i)) = (i : ℕ) := by
  have hset : (((Finset.univ : Finset (Fin j)).image f).filter (fun x => x < f i))
      = (Finset.univ.filter (fun k : Fin j => k < i)).image f := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨k, rfl⟩, hlt⟩
      exact ⟨k, hf.lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, rfl⟩, hf hk⟩
  rw [hset, Finset.card_image_of_injective _ hf.injective]
  have hIio : (Finset.univ.filter (fun k : Fin j => k < i)) = Finset.Iio i := by
    ext k; simp
  rw [hIio, Fin.card_Iio]

/-- The order-statistic count, for any `j`-subset of `ℕ`. -/
lemma orderEmb_filter_lt {S : Finset ℕ} {j : ℕ} (h : #S = j) (i : Fin j) :
    #(S.filter (fun x => x < S.orderEmbOfFin h i)) = (i : ℕ) := by
  have hS := image_orderEmbOfFin h
  have hres := image_filter_lt (S.orderEmbOfFin h) (S.orderEmbOfFin h).strictMono i
  rwa [hS] at hres

/-- A strictly monotone enumeration of a set of positive integers grows at least as fast as
the index: `i + 1 ≤ f i`.  Proved by counting, not by induction. -/
lemma orderEmb_ge {S : Finset ℕ} {j : ℕ} (h : #S = j) (hpos : ∀ x ∈ S, 1 ≤ x) (i : Fin j) :
    (i : ℕ) + 1 ≤ S.orderEmbOfFin h i := by
  have hcard := orderEmb_filter_lt h i
  have hsub : S.filter (fun x => x < S.orderEmbOfFin h i)
      ⊆ Finset.Icc 1 (S.orderEmbOfFin h i - 1) := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    simp only [Finset.mem_Icc]
    exact ⟨hpos x hx.1, by omega⟩
  have hle := Finset.card_le_card hsub
  rw [hcard, Nat.card_Icc] at hle
  have h1 : 1 ≤ S.orderEmbOfFin h i := hpos _ (S.orderEmbOfFin_mem h i)
  omega

/-- The decoded tuple is monotone: `f i - i` increases.  Again by counting.
NOTE `Finset.card_sdiff` here is the HYPOTHESIS-FREE form `#(s \ t) = #s - #(t ∩ s)`,
so the subset is routed through `Finset.inter_eq_left`. -/
lemma orderEmb_gap {S : Finset ℕ} {j : ℕ} (h : #S = j) {a b : Fin j} (hab : a ≤ b) :
    S.orderEmbOfFin h a + (b : ℕ) ≤ S.orderEmbOfFin h b + (a : ℕ) := by
  have hmono : StrictMono (S.orderEmbOfFin h) := (S.orderEmbOfFin h).strictMono
  have hfab : S.orderEmbOfFin h a ≤ S.orderEmbOfFin h b := hmono.monotone hab
  have hsubf : S.filter (fun x => x < S.orderEmbOfFin h a)
      ⊆ S.filter (fun x => x < S.orderEmbOfFin h b) := by
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_of_lt_of_le hx.2 hfab⟩
  have hdiff : (S.filter (fun x => x < S.orderEmbOfFin h b))
      \ (S.filter (fun x => x < S.orderEmbOfFin h a))
      ⊆ Finset.Ico (S.orderEmbOfFin h a) (S.orderEmbOfFin h b) := by
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hx
    obtain ⟨⟨hxS, hxb⟩, hna⟩ := hx
    have hfa : ¬ (x < S.orderEmbOfFin h a) := fun hlt => hna ⟨hxS, hlt⟩
    rw [Finset.mem_Ico]
    omega
  have hc := Finset.card_le_card hdiff
  have hinter : (S.filter (fun x => x < S.orderEmbOfFin h a))
      ∩ (S.filter (fun x => x < S.orderEmbOfFin h b))
      = S.filter (fun x => x < S.orderEmbOfFin h a) := Finset.inter_eq_left.mpr hsubf
  rw [Finset.card_sdiff, hinter, orderEmb_filter_lt h a, orderEmb_filter_lt h b,
    Nat.card_Ico] at hc
  have hba : (a : ℕ) ≤ (b : ℕ) := Fin.le_def.mp hab
  omega

/-- Below / at / above a member of `S` partitions `S`. -/
lemma card_split_at (S : Finset ℕ) (w : ℕ) (hw : w ∈ S) :
    #(S.filter (fun x => x < w)) + 1 + #(S.filter (fun x => w < x)) = #S := by
  have h1 : S.filter (fun x => x < w) ∪ S.filter (fun x => w < x) = S.erase w := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro (⟨hx, h⟩ | ⟨hx, h⟩) <;> exact ⟨by omega, hx⟩
    · rintro ⟨hne, hx⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hdisj : Disjoint (S.filter (fun x => x < w)) (S.filter (fun x => w < x)) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_filter] at hx hx2
    omega
  have hu := Finset.card_union_of_disjoint hdisj
  rw [h1] at hu
  have herase : #(S.erase w) + 1 = #S := by
    rw [Finset.card_erase_of_mem hw]
    have : 1 ≤ #S := Finset.card_pos.2 ⟨w, hw⟩
    omega
  omega

/-- A member of `S` is determined by how many members sit below it. -/
lemma eq_of_card_lt_eq {S : Finset ℕ} {w w' : ℕ} (hw : w ∈ S) (hw' : w' ∈ S)
    (h : #(S.filter (fun x => x < w)) = #(S.filter (fun x => x < w'))) : w = w' := by
  by_contra hne
  have key : ∀ u u' : ℕ, u ∈ S → u' ∈ S → u < u' →
      #(S.filter (fun x => x < u)) < #(S.filter (fun x => x < u')) := by
    intro u u' hu hu' hlt
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨u, by simp [Finset.mem_filter, hu, hlt], by simp⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, lt_trans hx.2 hlt⟩
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd h (Nat.ne_of_lt (key w w' hw hw' hlt))
  · exact absurd h.symm (Nat.ne_of_lt (key w' w hw' hw hlt))

/-- The number of members above the `i`-th one. -/
lemma orderEmb_above {S : Finset ℕ} {j : ℕ} (h : #S = j) (i : Fin j) :
    (i : ℕ) + 1 + #(S.filter (fun x => S.orderEmbOfFin h i < x)) = j := by
  have := card_split_at S (S.orderEmbOfFin h i) (S.orderEmbOfFin_mem h i)
  rw [orderEmb_filter_lt h i, h] at this
  exact this

/-- The `i`-th member is at most `M` minus the number of members above it. -/
lemma orderEmb_le {S : Finset ℕ} {j M : ℕ} (h : #S = j) (hub : ∀ x ∈ S, x ≤ M) (i : Fin j) :
    S.orderEmbOfFin h i + #(S.filter (fun x => S.orderEmbOfFin h i < x)) ≤ M := by
  have hsub : S.filter (fun x => S.orderEmbOfFin h i < x)
      ⊆ Finset.Icc (S.orderEmbOfFin h i + 1) M := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    simp only [Finset.mem_Icc]
    exact ⟨hx.2, hub x hx.1⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have hmem : S.orderEmbOfFin h i ≤ M := hub _ (S.orderEmbOfFin_mem h i)
  omega

/-- `Set.range` of the encoding is its `Finset` image. -/
lemma range_enc {j : ℕ} (l : Fin j → ℕ) :
    Set.range (fun i : Fin j => l i + i) = ↑(enc j l) := by
  ext x
  simp [enc, eq_comm]

/-- Arity-agnostic form of `split_Icc`, so the caller never rewrites a type index. -/
lemma split_Icc' (M w m p k : ℕ) (hk : k = m + 1 + p) (hw : w ∈ Finset.Icc 1 M) :
    #(((Finset.Icc 1 M).powersetCard k).filter
        (fun S => w ∈ S ∧ #(S.filter (fun x => x < w)) = m))
      = (w - 1).choose m * (M - w).choose p := by
  subst hk
  exact split_Icc M w m p hw

/-- **The fibre count.**  Weakly increasing `j`-tuples in `[1, A]` whose `mm`-th entry equals
`v` correspond, under `l ↦ {l i + i}`, to the `j`-subsets of `[1, A+j-1]` whose `mm`-th
smallest element is `v + mm`.  Stated for a general arity `j`, so nothing downstream has to
rewrite a type index. -/
lemma fiber_card (A j : ℕ) (mm : Fin j) (v : ℕ) :
    #(((Fintype.piFinset fun _ : Fin j => Finset.Icc 1 A).filter
          (fun l => Monotone l)).filter (fun l => l mm = v))
      = #(((Finset.Icc 1 (A + j - 1)).powersetCard j).filter
          (fun S => (v + mm) ∈ S ∧ #(S.filter (fun x => x < v + mm)) = mm)) := by
  classical
  have hjpos : 0 < j := mm.pos
  refine Finset.card_bij (fun l _ => enc j l) ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hl
    obtain ⟨⟨hmem, hmono⟩, hlv⟩ := hl
    have hbd : ∀ i : Fin j, 1 ≤ l i ∧ l i ≤ A := fun i => Finset.mem_Icc.1 (hmem i)
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, enc_card hmono⟩, ?_, ?_⟩
    · intro x hx
      rw [mem_enc] at hx
      obtain ⟨i, rfl⟩ := hx
      have h1 := hbd i
      have h2 := i.isLt
      rw [Finset.mem_Icc]
      omega
    · rw [mem_enc]
      exact ⟨mm, by rw [hlv]⟩
    · have hf := enc_filter_lt hmono mm
      rw [hlv] at hf
      exact hf
  · intro l hl l' hl' heq
    simp only [Finset.mem_filter] at hl hl'
    have hm : Monotone l := hl.1.2
    have hm' : Monotone l' := hl'.1.2
    have hr : Set.range (fun i : Fin j => l i + i)
        = Set.range (fun i : Fin j => l' i + i) := by
      rw [range_enc, range_enc, heq]
    have hfg := (StrictMono.range_inj (enc_strictMono hm) (enc_strictMono hm')).1 hr
    funext i
    have hi := congrFun hfg i
    omega
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS
    obtain ⟨⟨hsub, hcard⟩, hwmem, hwlt⟩ := hS
    have hpos : ∀ x ∈ S, 1 ≤ x := fun x hx => (Finset.mem_Icc.1 (hsub hx)).1
    have hub : ∀ x ∈ S, x ≤ A + j - 1 := fun x hx => (Finset.mem_Icc.1 (hsub hx)).2
    have hfix : ∀ i : Fin j,
        (S.orderEmbOfFin hcard i - i) + i = S.orderEmbOfFin hcard i := by
      intro i
      have := orderEmb_ge hcard hpos i
      omega
    refine ⟨fun i => S.orderEmbOfFin hcard i - i, ?_, ?_⟩
    · simp only [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro i
        have hge := orderEmb_ge hcard hpos i
        have hab := orderEmb_above hcard i
        have hle := orderEmb_le hcard hub i
        have hi := i.isLt
        rw [Finset.mem_Icc]
        omega
      · intro a b hab
        have hgap := orderEmb_gap hcard hab
        have hga := orderEmb_ge hcard hpos a
        have hgb := orderEmb_ge hcard hpos b
        have hba : (a : ℕ) ≤ (b : ℕ) := Fin.le_def.mp hab
        dsimp only
        omega
      · have hfm : S.orderEmbOfFin hcard mm = v + mm := by
          refine eq_of_card_lt_eq (S.orderEmbOfFin_mem hcard mm) hwmem ?_
          rw [orderEmb_filter_lt hcard mm, hwlt]
        rw [hfm]
        omega
    · rw [enc]
      calc (Finset.univ : Finset (Fin j)).image
              (fun i => (S.orderEmbOfFin hcard i - i) + i)
          = (Finset.univ : Finset (Fin j)).image (S.orderEmbOfFin hcard) :=
            Finset.image_congr (fun i _ => hfix i)
        _ = S := image_orderEmbOfFin hcard

/-- **The fibre count in closed binomial form.** -/
lemma fiber_binom (A j : ℕ) (mm : Fin j) (v : ℕ) (hv : 1 ≤ v) (hvA : v ≤ A) :
    #(((Fintype.piFinset fun _ : Fin j => Finset.Icc 1 A).filter
          (fun l => Monotone l)).filter (fun l => l mm = v))
      = (v + mm - 1).choose mm * ((A - v) + (j - 1 - mm)).choose (j - 1 - mm) := by
  have hlt := mm.isLt
  rw [fiber_card A j mm v]
  have hmem : (v + (mm : ℕ)) ∈ Finset.Icc 1 (A + j - 1) := by
    rw [Finset.mem_Icc]
    omega
  have hk : j = (mm : ℕ) + 1 + (j - 1 - (mm : ℕ)) := by omega
  rw [split_Icc' (A + j - 1) (v + mm) (mm : ℕ) (j - 1 - (mm : ℕ)) j hk hmem]
  have hres : A + j - 1 - (v + (mm : ℕ)) = (A - v) + (j - 1 - (mm : ℕ)) := by omega
  rw [hres]

end Principia.Common.MonotoneTuples
