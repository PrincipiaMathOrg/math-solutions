/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Defs
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Set.Finite.Lattice

set_option autoImplicit false

/-!
# Natural-density toolkit for `Principia.Erdos1054`

Everything here is about the counting function and the densities fixed in
`Principia.Erdos1054.Defs`:

* `cnt S X = #{1 ≤ N ≤ ⌊X⌋ : N ∈ S}` (for `X : ℝ`);
* `lowerDens S = liminf_{n → ∞} cnt S n / n`, `upperDens S = limsup_{n → ∞} cnt S n / n`
  (along `n : ℕ`);
* `HasDens S d` (the ratio tends to `d`) and `DensZero S = HasDens S 0`.

None of this is in Mathlib. All results are axiom-clean.

## 1. `cnt` basics
`mem_cntFinset`, `cnt_natCast`, `cnt_floor`, `cnt_le_floor`, `cnt_natCast_le`, `cnt_of_lt_one`,
`cnt_zero`, `cnt_empty`, `cnt_mono`, `cnt_mono_right`, `cnt_union_le`,
`cnt_le_cnt_add_of_subset_union`, `cnt_le_cnt_sdiff_add`, `cnt_sub_le_cnt_sdiff`, `cnt_sdiff_le`,
`cnt_add_cnt_of_compl`, `cnt_add_cnt_compl` (valid for every real `X`, not only `X ≥ 0`),
`cnt_univ`, `cnt_le_card_of_finite`, `cnt_eventually_const_of_finite`, `cnt_succ`.

**Decidability gotcha.** `cnt` is defined under `open Classical`, so `cnt (S ∪ T)` filters with
`Classical.propDecidable (· ∈ S ∪ T)`, while a fresh `Finset.mem_filter` rewrite at a compound set
synthesizes `Set.decidableUnion` and fails ("synthesized instance is not definitionally equal").
Rewrite with `mem_cntFinset` (stated for a generic set) instead.

## 2. The ratio lies in `[0, 1]`; the densities are genuine liminf/limsup
`cnt_div_nonneg`, `cnt_div_le_one`, `isBoundedUnder_le_cnt_div`, `isBoundedUnder_ge_cnt_div`,
`isCoboundedUnder_le_cnt_div`, `isCoboundedUnder_ge_cnt_div`, `lowerDens_nonneg`,
`upperDens_le_one`, `lowerDens_le_upperDens`, `upperDens_nonneg`, `lowerDens_le_one`.

## 3. Monotonicity, subadditivity, complements, `HasDens`
`cnt_div_mono`, `cnt_div_le_add_of_subset_union`, `cnt_div_union_le`, `cnt_div_compl`,
`lowerDens_mono`, `upperDens_mono`, `upperDens_union_le`, `lowerDens_union_le`,
`lowerDens_add_upperDens_compl`, `upperDens_add_lowerDens_compl`, `HasDens.lowerDens_eq`,
`HasDens.upperDens_eq`, `hasDens_of_lowerDens_eq_upperDens`, `hasDens_iff`, `HasDens.unique`,
`HasDens.compl`.

## 4. Density zero
`densZero_iff_upperDens_eq_zero`, `densZero_of_finite`, `densZero_empty`, `hasDens_univ`,
`densZero_subset`, `densZero_union`, `densZero_biUnion`, `densZero_iUnion`,
`lowerDens_eq_of_subset_of_densZero_sdiff`, `upperDens_eq_of_subset_of_densZero_sdiff`,
`lowerDens_sdiff_of_densZero`, `upperDens_sdiff_of_densZero`, `lowerDens_union_of_densZero`,
`upperDens_union_of_densZero`, `HasDens.sdiff_densZero`, `HasDens.union_densZero`.

## 5. Little-o form
`densZero_iff_eventually_le` (along `n : ℕ`), `densZero_iff_exists_real` and
`DensZero.exists_le_mul` (along real `X`).

## 6. Periodic sets
`cnt_add_period`, `cnt_mul_period_add`, `cnt_periodic_decomp`, `abs_cnt_sub_le_of_periodic`
(`|cnt S X − k X / Q| ≤ k` with `k = cnt S Q` the number of classes), `abs_cnt_sub_le_period`
(the same with bound `Q`), `hasDens_of_periodic`, `cnt_mod_mem_period`, `hasDens_mod_mem`,
`abs_cnt_mod_mem_sub_le`, `hasDens_of_mem_iff_mod_mem`.

## 7. Multiples
`cnt_dvd_eq` (`cnt {N | a ∣ N} X = ⌊X⌋ / a`), `cnt_dvd_le` (`≤ X / a`, for `X ≥ 0`),
`setOf_dvd_eq_mod_mem`, `abs_cnt_dvd_sub_le`, `hasDens_dvd` (`HasDens {N | a ∣ N} (1 / a)`).

## 8. Eventual bounds ↔ density bounds, and rescaling
`le_lowerDens_of_eventually`, `upperDens_le_of_eventually`, `le_lowerDens_of_forall_ge`,
`upperDens_le_of_forall_ge`, `le_lowerDens_of_scaled`, `upperDens_le_of_scaled`,
`eventually_mul_lt_cnt_of_lt_lowerDens`, `eventually_cnt_lt_mul_of_upperDens_lt`,
`exists_mul_le_cnt_of_lt_lowerDens`, `exists_cnt_le_mul_of_upperDens_lt`.
-/

namespace Principia.Erdos1054

open Filter
open scoped Topology

/-! ## 1. `cnt` basics -/

open Classical in
/-- Membership in the finset that `cnt` counts. Stated for a *generic* set, so its decidability
instance is the classical one that `cnt` itself uses; instantiating it at a compound set such as
`S ∪ T` then matches `cnt (S ∪ T)` syntactically (a direct `Finset.mem_filter` rewrite would
synthesize `Set.decidableUnion` instead and fail). -/
theorem mem_cntFinset {S : Set ℕ} {m n : ℕ} :
    n ∈ (Finset.Icc 1 m).filter (· ∈ S) ↔ (1 ≤ n ∧ n ≤ m) ∧ n ∈ S := by
  rw [Finset.mem_filter, Finset.mem_Icc]

open Classical in
theorem cnt_natCast (S : Set ℕ) (n : ℕ) :
    cnt S (n : ℝ) = ((Finset.Icc 1 n).filter (· ∈ S)).card := by
  unfold cnt
  rw [Nat.floor_natCast]

theorem cnt_floor (S : Set ℕ) (X : ℝ) : cnt S (⌊X⌋₊ : ℝ) = cnt S X := by
  unfold cnt
  rw [Nat.floor_natCast]

theorem cnt_le_floor (S : Set ℕ) (X : ℝ) : cnt S X ≤ ⌊X⌋₊ := by
  classical
  unfold cnt
  refine (Finset.card_filter_le _ _).trans ?_
  simp

theorem cnt_natCast_le (S : Set ℕ) (n : ℕ) : cnt S (n : ℝ) ≤ n := by
  have h := cnt_le_floor S (n : ℝ)
  rwa [Nat.floor_natCast] at h

theorem cnt_of_lt_one (S : Set ℕ) {X : ℝ} (hX : X < 1) : cnt S X = 0 := by
  have h0 : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.2 hX
  have := cnt_le_floor S X
  omega

theorem cnt_zero (S : Set ℕ) : cnt S 0 = 0 := cnt_of_lt_one S (by norm_num)

theorem cnt_empty (X : ℝ) : cnt ∅ X = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro n hn
  exact (mem_cntFinset.1 hn).2

theorem cnt_mono {S T : Set ℕ} (h : S ⊆ T) (X : ℝ) : cnt S X ≤ cnt T X := by
  unfold cnt
  apply Finset.card_le_card
  intro n hn
  rw [mem_cntFinset] at hn ⊢
  exact ⟨hn.1, h hn.2⟩

theorem cnt_mono_right (S : Set ℕ) {X Y : ℝ} (h : X ≤ Y) : cnt S X ≤ cnt S Y := by
  unfold cnt
  apply Finset.card_le_card
  intro n hn
  rw [mem_cntFinset] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_mono h)⟩, hn.2⟩

theorem cnt_union_le (S T : Set ℕ) (X : ℝ) : cnt (S ∪ T) X ≤ cnt S X + cnt T X := by
  unfold cnt
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  rw [mem_cntFinset] at hn
  rw [Finset.mem_union, mem_cntFinset, mem_cntFinset]
  rcases hn.2 with h | h
  · exact Or.inl ⟨hn.1, h⟩
  · exact Or.inr ⟨hn.1, h⟩

theorem cnt_le_cnt_add_of_subset_union {S T U : Set ℕ} (h : S ⊆ T ∪ U) (X : ℝ) :
    cnt S X ≤ cnt T X + cnt U X :=
  (cnt_mono h X).trans (cnt_union_le T U X)

theorem cnt_le_cnt_sdiff_add (S T : Set ℕ) (X : ℝ) : cnt S X ≤ cnt (S \ T) X + cnt T X :=
  cnt_le_cnt_add_of_subset_union (fun n hn => by
    by_cases h : n ∈ T
    · exact Or.inr h
    · exact Or.inl ⟨hn, h⟩) X

theorem cnt_sub_le_cnt_sdiff (S T : Set ℕ) (X : ℝ) : cnt S X - cnt T X ≤ cnt (S \ T) X := by
  have := cnt_le_cnt_sdiff_add S T X
  omega

theorem cnt_sdiff_le (S T : Set ℕ) (X : ℝ) : cnt (S \ T) X ≤ cnt S X :=
  cnt_mono Set.sdiff_subset X

/-- Generic form of `cnt_add_cnt_compl`: `T` is any set with `n ∈ T ↔ n ∉ S`. -/
theorem cnt_add_cnt_of_compl {S T : Set ℕ} (hT : ∀ n, n ∈ T ↔ n ∉ S) (X : ℝ) :
    cnt S X + cnt T X = ⌊X⌋₊ := by
  classical
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · have e : (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ S) ∪ (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ T) =
        Finset.Icc 1 ⌊X⌋₊ := by
      ext x
      rw [Finset.mem_union, mem_cntFinset, mem_cntFinset, hT x, Finset.mem_Icc]
      tauto
    rw [e]
    simp
  · rw [Finset.disjoint_left]
    intro x h1 h2
    exact (hT x).1 (mem_cntFinset.1 h2).2 (mem_cntFinset.1 h1).2

theorem cnt_add_cnt_compl (S : Set ℕ) (X : ℝ) : cnt S X + cnt Sᶜ X = ⌊X⌋₊ :=
  cnt_add_cnt_of_compl (fun _ => Iff.rfl) X

theorem cnt_univ (X : ℝ) : cnt Set.univ X = ⌊X⌋₊ := by
  have h := cnt_add_cnt_compl Set.univ X
  rw [Set.compl_univ, cnt_empty] at h
  omega

theorem cnt_le_card_of_finite {S : Set ℕ} (hS : S.Finite) (X : ℝ) :
    cnt S X ≤ hS.toFinset.card := by
  unfold cnt
  apply Finset.card_le_card
  intro n hn
  rw [mem_cntFinset] at hn
  exact hS.mem_toFinset.2 hn.2

/-- The count of a finite set is eventually constant. -/
theorem cnt_eventually_const_of_finite {S : Set ℕ} (hS : S.Finite) :
    ∃ c : ℕ, ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → cnt S X = c := by
  obtain ⟨B, hB⟩ := hS.bddAbove
  refine ⟨cnt S (B : ℝ), B, fun X hX => ?_⟩
  unfold cnt
  rw [Nat.floor_natCast]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, hn⟩
    exact ⟨⟨h1, hB hn⟩, hn⟩
  · rintro ⟨⟨h1, h2⟩, hn⟩
    exact ⟨⟨h1, h2.trans (Nat.le_floor hX)⟩, hn⟩

open Classical in
/-- One step of the count along the integers. -/
theorem cnt_succ (S : Set ℕ) (n : ℕ) :
    cnt S ((n + 1 : ℕ) : ℝ) = cnt S (n : ℝ) + if n + 1 ∈ S then 1 else 0 := by
  rw [cnt_natCast, cnt_natCast]
  have hI : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hI, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    rw [Finset.mem_filter, Finset.mem_Icc]
    omega
  · rfl

/-! ## 2. The ratio `cnt S n / n` lies in `[0, 1]` -/

theorem cnt_div_nonneg (S : Set ℕ) (n : ℕ) : 0 ≤ (cnt S n : ℝ) / n := by
  positivity

theorem cnt_div_le_one (S : Set ℕ) (n : ℕ) : (cnt S n : ℝ) / n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast cnt_natCast_le S n

theorem isBoundedUnder_le_cnt_div (S : Set ℕ) :
    IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (cnt S n : ℝ) / n) :=
  isBoundedUnder_of_eventually_le (a := 1) (Eventually.of_forall (cnt_div_le_one S))

theorem isBoundedUnder_ge_cnt_div (S : Set ℕ) :
    IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ => (cnt S n : ℝ) / n) :=
  isBoundedUnder_of_eventually_ge (a := 0) (Eventually.of_forall (cnt_div_nonneg S))

theorem isCoboundedUnder_le_cnt_div (S : Set ℕ) :
    IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => (cnt S n : ℝ) / n) :=
  (isBoundedUnder_ge_cnt_div S).isCoboundedUnder_le

theorem isCoboundedUnder_ge_cnt_div (S : Set ℕ) :
    IsCoboundedUnder (· ≥ ·) atTop (fun n : ℕ => (cnt S n : ℝ) / n) :=
  (isBoundedUnder_le_cnt_div S).isCoboundedUnder_ge

theorem lowerDens_nonneg (S : Set ℕ) : 0 ≤ lowerDens S :=
  le_liminf_of_le (isCoboundedUnder_ge_cnt_div S) (Eventually.of_forall (cnt_div_nonneg S))

theorem upperDens_le_one (S : Set ℕ) : upperDens S ≤ 1 :=
  limsup_le_of_le (isCoboundedUnder_le_cnt_div S) (Eventually.of_forall (cnt_div_le_one S))

theorem lowerDens_le_upperDens (S : Set ℕ) : lowerDens S ≤ upperDens S :=
  liminf_le_limsup (isBoundedUnder_le_cnt_div S) (isBoundedUnder_ge_cnt_div S)

theorem upperDens_nonneg (S : Set ℕ) : 0 ≤ upperDens S :=
  (lowerDens_nonneg S).trans (lowerDens_le_upperDens S)

theorem lowerDens_le_one (S : Set ℕ) : lowerDens S ≤ 1 :=
  (lowerDens_le_upperDens S).trans (upperDens_le_one S)

/-! ## 3. Monotonicity, subadditivity, complements, `HasDens` -/

theorem cnt_div_mono {S T : Set ℕ} (h : S ⊆ T) (n : ℕ) :
    (cnt S n : ℝ) / n ≤ (cnt T n : ℝ) / n :=
  div_le_div_of_nonneg_right (by exact_mod_cast cnt_mono h (n : ℝ)) (Nat.cast_nonneg n)

theorem cnt_div_le_add_of_subset_union {S T U : Set ℕ} (h : S ⊆ T ∪ U) (n : ℕ) :
    (cnt S n : ℝ) / n ≤ (cnt T n : ℝ) / n + (cnt U n : ℝ) / n := by
  rw [← add_div]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast cnt_le_cnt_add_of_subset_union h (n : ℝ)) (Nat.cast_nonneg n)

theorem cnt_div_union_le (S T : Set ℕ) (n : ℕ) :
    (cnt (S ∪ T) n : ℝ) / n ≤ (cnt S n : ℝ) / n + (cnt T n : ℝ) / n :=
  cnt_div_le_add_of_subset_union subset_rfl n

theorem cnt_div_compl (S : Set ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (cnt Sᶜ n : ℝ) / n = 1 - (cnt S n : ℝ) / n := by
  have h := cnt_add_cnt_compl S (n : ℝ)
  rw [Nat.floor_natCast] at h
  have hn' : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hn']
  exact_mod_cast (by omega : cnt Sᶜ n + cnt S n = n)

theorem lowerDens_mono {S T : Set ℕ} (h : S ⊆ T) : lowerDens S ≤ lowerDens T :=
  liminf_le_liminf (Eventually.of_forall (cnt_div_mono h)) (isBoundedUnder_ge_cnt_div S)
    (isCoboundedUnder_ge_cnt_div T)

theorem upperDens_mono {S T : Set ℕ} (h : S ⊆ T) : upperDens S ≤ upperDens T :=
  limsup_le_limsup (Eventually.of_forall (cnt_div_mono h)) (isCoboundedUnder_le_cnt_div S)
    (isBoundedUnder_le_cnt_div T)

theorem upperDens_union_le (S T : Set ℕ) : upperDens (S ∪ T) ≤ upperDens S + upperDens T := by
  unfold upperDens
  have hb : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (cnt S n : ℝ) / n + (cnt T n : ℝ) / n) :=
    isBoundedUnder_of_eventually_le (a := 2) (Eventually.of_forall fun n => by
      have h1 := cnt_div_le_one S n
      have h2 := cnt_div_le_one T n
      change (cnt S n : ℝ) / n + (cnt T n : ℝ) / n ≤ 2
      linarith)
  refine (limsup_le_limsup (Eventually.of_forall (cnt_div_union_le S T))
    (isCoboundedUnder_le_cnt_div _) hb).trans ?_
  exact limsup_add_le (isBoundedUnder_ge_cnt_div S) (isBoundedUnder_le_cnt_div S)
    (isCoboundedUnder_le_cnt_div T) (isBoundedUnder_le_cnt_div T)

theorem lowerDens_union_le (S T : Set ℕ) : lowerDens (S ∪ T) ≤ upperDens S + lowerDens T := by
  unfold lowerDens upperDens
  have hc : IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ => (cnt S n : ℝ) / n + (cnt T n : ℝ) / n) :=
    isCoboundedUnder_ge_of_le atTop (x := 2) fun n => by
      have h1 := cnt_div_le_one S n
      have h2 := cnt_div_le_one T n
      change (cnt S n : ℝ) / n + (cnt T n : ℝ) / n ≤ 2
      linarith
  refine (liminf_le_liminf (Eventually.of_forall (cnt_div_union_le S T))
    (isBoundedUnder_ge_cnt_div _) hc).trans ?_
  exact liminf_add_le (isBoundedUnder_ge_cnt_div S) (isBoundedUnder_le_cnt_div S)
    (isBoundedUnder_ge_cnt_div T) (isCoboundedUnder_ge_cnt_div T)

theorem lowerDens_add_upperDens_compl (S : Set ℕ) : lowerDens S + upperDens Sᶜ = 1 := by
  have h : upperDens Sᶜ = limsup (fun n : ℕ => 1 - (cnt S n : ℝ) / n) atTop := by
    unfold upperDens
    apply limsup_congr
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact cnt_div_compl S hn
  rw [h, limsup_const_sub atTop _ 1 (isCoboundedUnder_ge_cnt_div S)
    (isBoundedUnder_ge_cnt_div S)]
  unfold lowerDens
  ring

theorem upperDens_add_lowerDens_compl (S : Set ℕ) : upperDens S + lowerDens Sᶜ = 1 := by
  have h := lowerDens_add_upperDens_compl Sᶜ
  rw [compl_compl] at h
  linarith

theorem HasDens.lowerDens_eq {S : Set ℕ} {d : ℝ} (h : HasDens S d) : lowerDens S = d :=
  Tendsto.liminf_eq h

theorem HasDens.upperDens_eq {S : Set ℕ} {d : ℝ} (h : HasDens S d) : upperDens S = d :=
  Tendsto.limsup_eq h

theorem hasDens_of_lowerDens_eq_upperDens {S : Set ℕ} (h : lowerDens S = upperDens S) :
    HasDens S (lowerDens S) :=
  tendsto_of_liminf_eq_limsup rfl h.symm (isBoundedUnder_le_cnt_div S)
    (isBoundedUnder_ge_cnt_div S)

theorem hasDens_iff {S : Set ℕ} {d : ℝ} : HasDens S d ↔ lowerDens S = d ∧ upperDens S = d := by
  constructor
  · intro h
    exact ⟨h.lowerDens_eq, h.upperDens_eq⟩
  · rintro ⟨h1, h2⟩
    exact tendsto_of_liminf_eq_limsup h1 h2 (isBoundedUnder_le_cnt_div S)
      (isBoundedUnder_ge_cnt_div S)

theorem HasDens.unique {S : Set ℕ} {d d' : ℝ} (h : HasDens S d) (h' : HasDens S d') : d = d' :=
  h.lowerDens_eq.symm.trans h'.lowerDens_eq

theorem HasDens.compl {S : Set ℕ} {d : ℝ} (h : HasDens S d) : HasDens Sᶜ (1 - d) := by
  have h1 : Tendsto (fun n : ℕ => 1 - (cnt S n : ℝ) / n) atTop (𝓝 (1 - d)) :=
    Tendsto.sub tendsto_const_nhds h
  unfold HasDens
  refine Tendsto.congr' ?_ h1
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (cnt_div_compl S hn).symm

/-! ## 4. Density zero -/

theorem densZero_iff_upperDens_eq_zero {S : Set ℕ} : DensZero S ↔ upperDens S = 0 := by
  constructor
  · intro h
    exact HasDens.upperDens_eq h
  · intro h
    have h1 : lowerDens S = 0 :=
      le_antisymm (h ▸ lowerDens_le_upperDens S) (lowerDens_nonneg S)
    have h2 := hasDens_of_lowerDens_eq_upperDens (h1.trans h.symm)
    rw [h1] at h2
    exact h2

theorem densZero_of_finite {S : Set ℕ} (hS : S.Finite) : DensZero S := by
  unfold DensZero HasDens
  refine squeeze_zero (cnt_div_nonneg S) (fun n => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat (hS.toFinset.card : ℝ))
  exact div_le_div_of_nonneg_right (by exact_mod_cast cnt_le_card_of_finite hS (n : ℝ))
    (Nat.cast_nonneg n)

theorem densZero_empty : DensZero ∅ := densZero_of_finite Set.finite_empty

theorem hasDens_univ : HasDens Set.univ 1 := by
  have h := HasDens.compl (densZero_empty : HasDens ∅ 0)
  rwa [Set.compl_empty, sub_zero] at h

theorem densZero_subset {S T : Set ℕ} (hT : DensZero T) (h : S ⊆ T) : DensZero S :=
  squeeze_zero (cnt_div_nonneg S) (cnt_div_mono h) hT

theorem densZero_union {S T : Set ℕ} (hS : DensZero S) (hT : DensZero T) :
    DensZero (S ∪ T) := by
  have h := Tendsto.add hS hT
  rw [add_zero] at h
  exact squeeze_zero (cnt_div_nonneg _) (cnt_div_union_le S T) h

theorem densZero_biUnion {ι : Type*} (s : Finset ι) {A : ι → Set ℕ}
    (h : ∀ i ∈ s, DensZero (A i)) : DensZero (⋃ i ∈ s, A i) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using densZero_empty
  | insert a s ha ih =>
    intro h
    rw [Finset.set_biUnion_insert]
    exact densZero_union (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem densZero_iUnion {ι : Type*} [Finite ι] {A : ι → Set ℕ} (h : ∀ i, DensZero (A i)) :
    DensZero (⋃ i, A i) := by
  have : Fintype ι := Fintype.ofFinite ι
  have := densZero_biUnion Finset.univ (A := A) (fun i _ => h i)
  simpa using this

/-- If `S ⊆ T` and `T \ S` has density zero, the lower densities agree. -/
theorem lowerDens_eq_of_subset_of_densZero_sdiff {S T : Set ℕ} (hST : S ⊆ T)
    (hD : DensZero (T \ S)) : lowerDens S = lowerDens T := by
  refine le_antisymm (lowerDens_mono hST) ?_
  have h1 : T ⊆ (T \ S) ∪ S := fun n hn => by
    by_cases h : n ∈ S
    · exact Or.inr h
    · exact Or.inl ⟨hn, h⟩
  calc lowerDens T ≤ lowerDens ((T \ S) ∪ S) := lowerDens_mono h1
    _ ≤ upperDens (T \ S) + lowerDens S := lowerDens_union_le _ _
    _ = lowerDens S := by rw [densZero_iff_upperDens_eq_zero.1 hD, zero_add]

/-- If `S ⊆ T` and `T \ S` has density zero, the upper densities agree. -/
theorem upperDens_eq_of_subset_of_densZero_sdiff {S T : Set ℕ} (hST : S ⊆ T)
    (hD : DensZero (T \ S)) : upperDens S = upperDens T := by
  refine le_antisymm (upperDens_mono hST) ?_
  have h1 : T ⊆ (T \ S) ∪ S := fun n hn => by
    by_cases h : n ∈ S
    · exact Or.inr h
    · exact Or.inl ⟨hn, h⟩
  calc upperDens T ≤ upperDens ((T \ S) ∪ S) := upperDens_mono h1
    _ ≤ upperDens (T \ S) + upperDens S := upperDens_union_le _ _
    _ = upperDens S := by rw [densZero_iff_upperDens_eq_zero.1 hD, zero_add]

theorem lowerDens_sdiff_of_densZero (S : Set ℕ) {T : Set ℕ} (hT : DensZero T) :
    lowerDens (S \ T) = lowerDens S :=
  lowerDens_eq_of_subset_of_densZero_sdiff Set.sdiff_subset
    (densZero_subset hT fun n hn => by
      by_contra h
      exact hn.2 ⟨hn.1, h⟩)

theorem upperDens_sdiff_of_densZero (S : Set ℕ) {T : Set ℕ} (hT : DensZero T) :
    upperDens (S \ T) = upperDens S :=
  upperDens_eq_of_subset_of_densZero_sdiff Set.sdiff_subset
    (densZero_subset hT fun n hn => by
      by_contra h
      exact hn.2 ⟨hn.1, h⟩)

theorem lowerDens_union_of_densZero (S : Set ℕ) {T : Set ℕ} (hT : DensZero T) :
    lowerDens (S ∪ T) = lowerDens S :=
  (lowerDens_eq_of_subset_of_densZero_sdiff Set.subset_union_left
    (densZero_subset hT fun _ hn => hn.1.resolve_left hn.2)).symm

theorem upperDens_union_of_densZero (S : Set ℕ) {T : Set ℕ} (hT : DensZero T) :
    upperDens (S ∪ T) = upperDens S :=
  (upperDens_eq_of_subset_of_densZero_sdiff Set.subset_union_left
    (densZero_subset hT fun _ hn => hn.1.resolve_left hn.2)).symm

theorem HasDens.sdiff_densZero {S T : Set ℕ} {d : ℝ} (h : HasDens S d) (hT : DensZero T) :
    HasDens (S \ T) d := by
  rw [hasDens_iff] at h ⊢
  rw [lowerDens_sdiff_of_densZero S hT, upperDens_sdiff_of_densZero S hT]
  exact h

theorem HasDens.union_densZero {S T : Set ℕ} {d : ℝ} (h : HasDens S d) (hT : DensZero T) :
    HasDens (S ∪ T) d := by
  rw [hasDens_iff] at h ⊢
  rw [lowerDens_union_of_densZero S hT, upperDens_union_of_densZero S hT]
  exact h

/-! ## 5. Little-o form of density zero -/

theorem densZero_iff_eventually_le {S : Set ℕ} :
    DensZero S ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (cnt S n : ℝ) ≤ ε * n := by
  constructor
  · intro h ε hε
    filter_upwards [Tendsto.eventually h (gt_mem_nhds hε), eventually_ge_atTop 1] with n hn hn1
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [div_lt_iff₀ hpos] at hn
    exact hn.le
  · intro h
    unfold DensZero HasDens
    rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha (cnt_div_nonneg S n),
      fun a ha => ?_⟩
    filter_upwards [h (a / 2) (by linarith), eventually_ge_atTop 1] with n hn hn1
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [div_lt_iff₀ hpos]
    have := mul_pos ha hpos
    linarith

theorem DensZero.exists_le_mul {S : Set ℕ} (h : DensZero S) {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → (cnt S X : ℝ) ≤ ε * X := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (densZero_iff_eventually_le.1 h ε hε)
  refine ⟨N, fun X hX => ?_⟩
  have hX0 : 0 ≤ X := le_trans (Nat.cast_nonneg N) hX
  have h1 := hN ⌊X⌋₊ (Nat.le_floor hX)
  rw [cnt_floor] at h1
  have h2 : ε * (⌊X⌋₊ : ℝ) ≤ ε * X := mul_le_mul_of_nonneg_left (Nat.floor_le hX0) hε.le
  linarith

theorem densZero_iff_exists_real {S : Set ℕ} :
    DensZero S ↔ ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → (cnt S X : ℝ) ≤ ε * X := by
  constructor
  · intro h ε hε
    exact h.exists_le_mul hε
  · intro h
    rw [densZero_iff_eventually_le]
    intro ε hε
    obtain ⟨X₀, hX₀⟩ := h ε hε
    exact eventually_atTop.2 ⟨⌈X₀⌉₊, fun n hn => hX₀ n (Nat.ceil_le.1 hn)⟩

/-! ## 6. Periodic sets -/

theorem cnt_add_period {S : Set ℕ} {Q : ℕ} (hper : ∀ N, N + Q ∈ S ↔ N ∈ S) (n : ℕ) :
    cnt S ((n + Q : ℕ) : ℝ) = cnt S (n : ℝ) + cnt S (Q : ℝ) := by
  induction n with
  | zero =>
    rw [zero_add, Nat.cast_zero, cnt_zero, zero_add]
  | succ n ih =>
    rw [show n + 1 + Q = (n + Q) + 1 by omega, cnt_succ, ih, cnt_succ]
    by_cases h : n + 1 ∈ S
    · have h' : n + Q + 1 ∈ S := by
        rw [show n + Q + 1 = (n + 1) + Q by omega]
        exact (hper _).2 h
      simp only [h, h', ↓reduceIte]
      omega
    · have h' : n + Q + 1 ∉ S := by
        rw [show n + Q + 1 = (n + 1) + Q by omega]
        exact fun hh => h ((hper _).1 hh)
      simp only [h, h', ↓reduceIte]
      omega

theorem cnt_mul_period_add {S : Set ℕ} {Q : ℕ} (hper : ∀ N, N + Q ∈ S ↔ N ∈ S) (q r : ℕ) :
    cnt S ((q * Q + r : ℕ) : ℝ) = q * cnt S (Q : ℝ) + cnt S (r : ℝ) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show (q + 1) * Q + r = (q * Q + r) + Q by ring, cnt_add_period hper, ih]
    ring

theorem cnt_periodic_decomp {S : Set ℕ} {Q : ℕ} (hper : ∀ N, N + Q ∈ S ↔ N ∈ S) (n : ℕ) :
    cnt S (n : ℝ) = n / Q * cnt S (Q : ℝ) + cnt S ((n % Q : ℕ) : ℝ) := by
  conv_lhs => rw [← Nat.div_add_mod' n Q]
  exact cnt_mul_period_add hper (n / Q) (n % Q)

/-- **Explicit periodic count.** If `S` is invariant under `N ↦ N + Q` then, with
`k = cnt S Q` (the number of residue classes mod `Q` that `S` occupies),
`|cnt S X − k X / Q| ≤ k` for every real `X ≥ 0`. -/
theorem abs_cnt_sub_le_of_periodic {S : Set ℕ} {Q : ℕ} (hQ : 0 < Q)
    (hper : ∀ N, N + Q ∈ S ↔ N ∈ S) {X : ℝ} (hX : 0 ≤ X) :
    |(cnt S X : ℝ) - cnt S (Q : ℝ) * X / Q| ≤ cnt S (Q : ℝ) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hcnt := cnt_periodic_decomp hper ⌊X⌋₊
  rw [cnt_floor] at hcnt
  have hr_le : cnt S ((⌊X⌋₊ % Q : ℕ) : ℝ) ≤ cnt S (Q : ℝ) :=
    cnt_mono_right S (by exact_mod_cast (Nat.mod_lt ⌊X⌋₊ hQ).le)
  have hr_lt : ⌊X⌋₊ % Q + 1 ≤ Q := Nat.mod_lt ⌊X⌋₊ hQ
  have hnX : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX
  have hXn : X < ⌊X⌋₊ + 1 := Nat.lt_floor_add_one X
  have hdiv : ⌊X⌋₊ / Q * Q + ⌊X⌋₊ % Q = ⌊X⌋₊ := Nat.div_add_mod' ⌊X⌋₊ Q
  generalize ⌊X⌋₊ = n at *
  generalize hq : n / Q = q at *
  generalize hr : n % Q = r at *
  generalize hk : cnt S (Q : ℝ) = k at *
  generalize hc : cnt S (r : ℝ) = c at *
  have hdivR : (q : ℝ) * Q + r = n := by exact_mod_cast hdiv
  have hrR : (r : ℝ) + 1 ≤ Q := by exact_mod_cast hr_lt
  have hcR : (cnt S X : ℝ) = q * k + c := by
    rw [hcnt]
    push_cast
    ring
  have hcle : (c : ℝ) ≤ k := by exact_mod_cast hr_le
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ht1 : (q : ℝ) ≤ X / Q := by
    rw [le_div_iff₀ hQr]
    linarith
  have ht2 : X / Q ≤ q + 1 := by
    rw [div_le_iff₀ hQr]
    linarith
  have hk1 : (k : ℝ) * q ≤ k * (X / Q) := mul_le_mul_of_nonneg_left ht1 hk0
  have hk2 : (k : ℝ) * (X / Q) ≤ k * (q + 1) := mul_le_mul_of_nonneg_left ht2 hk0
  rw [mul_div_assoc, abs_sub_le_iff, hcR]
  constructor
  · linarith
  · linarith

/-- The same bound with the (weaker, but `S`-free) constant `Q`. -/
theorem abs_cnt_sub_le_period {S : Set ℕ} {Q : ℕ} (hQ : 0 < Q)
    (hper : ∀ N, N + Q ∈ S ↔ N ∈ S) {X : ℝ} (hX : 0 ≤ X) :
    |(cnt S X : ℝ) - cnt S (Q : ℝ) * X / Q| ≤ Q :=
  (abs_cnt_sub_le_of_periodic hQ hper hX).trans (by exact_mod_cast cnt_natCast_le S Q)

/-- A set invariant under `N ↦ N + Q` has natural density `cnt S Q / Q`. -/
theorem hasDens_of_periodic {S : Set ℕ} {Q : ℕ} (hQ : 0 < Q) (hper : ∀ N, N + Q ∈ S ↔ N ∈ S) :
    HasDens S (cnt S (Q : ℝ) / Q) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have key : ∀ n : ℕ, 1 ≤ n →
      |(cnt S n : ℝ) / n - (cnt S (Q : ℝ) : ℝ) / Q| ≤ (cnt S (Q : ℝ) : ℝ) / n := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
    have h := abs_cnt_sub_le_of_periodic hQ hper (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have e : (cnt S n : ℝ) / n - (cnt S (Q : ℝ) : ℝ) / Q =
        ((cnt S n : ℝ) - (cnt S (Q : ℝ) : ℝ) * n / Q) / n := by
      rw [eq_div_iff hn0, sub_mul, div_mul_cancel₀ _ hn0]
      ring
    rw [e, abs_div, abs_of_pos hnR]
    exact div_le_div_of_nonneg_right h hnR.le
  unfold HasDens
  have hlo : Tendsto (fun n : ℕ => (cnt S (Q : ℝ) : ℝ) / Q - (cnt S (Q : ℝ) : ℝ) / n) atTop
      (𝓝 ((cnt S (Q : ℝ) : ℝ) / Q)) := by
    have := Tendsto.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (cnt S (Q : ℝ) : ℝ) / Q) atTop
        (𝓝 ((cnt S (Q : ℝ) : ℝ) / Q)))
      (tendsto_const_div_atTop_nhds_zero_nat (cnt S (Q : ℝ) : ℝ))
    rwa [sub_zero] at this
  have hhi : Tendsto (fun n : ℕ => (cnt S (Q : ℝ) : ℝ) / Q + (cnt S (Q : ℝ) : ℝ) / n) atTop
      (𝓝 ((cnt S (Q : ℝ) : ℝ) / Q)) := by
    have := Tendsto.add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (cnt S (Q : ℝ) : ℝ) / Q) atTop
        (𝓝 ((cnt S (Q : ℝ) : ℝ) / Q)))
      (tendsto_const_div_atTop_nhds_zero_nat (cnt S (Q : ℝ) : ℝ))
    rwa [add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have := (abs_sub_le_iff.1 (key n hn)).2
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have := (abs_sub_le_iff.1 (key n hn)).1
    linarith

/-- A complete set of residues: `{1 ≤ N ≤ Q : N mod Q ∈ A}` has exactly `#A` elements. -/
theorem cnt_mod_mem_period {Q : ℕ} (hQ : 0 < Q) (A : Finset ℕ) (hA : ∀ a ∈ A, a < Q) :
    cnt {N : ℕ | N % Q ∈ A} (Q : ℝ) = A.card := by
  rw [cnt_natCast]
  apply Finset.card_nbij' (fun N => N % Q) (fun a => if a = 0 then Q else a)
  · intro N hN
    rw [Finset.mem_coe, mem_cntFinset, Set.mem_setOf_eq] at hN
    rw [Finset.mem_coe]
    exact hN.2
  · intro a ha
    rw [Finset.mem_coe] at ha
    rw [Finset.mem_coe, mem_cntFinset, Set.mem_setOf_eq]
    have haQ := hA a ha
    dsimp only
    split_ifs with h0
    · subst h0
      exact ⟨⟨hQ, le_rfl⟩, by rw [Nat.mod_self]; exact ha⟩
    · exact ⟨⟨Nat.pos_of_ne_zero h0, haQ.le⟩, by rw [Nat.mod_eq_of_lt haQ]; exact ha⟩
  · intro N hN
    rw [Finset.mem_coe, mem_cntFinset, Set.mem_setOf_eq] at hN
    by_cases hNQ : N = Q
    · subst hNQ
      simp
    · have hlt : N < Q := lt_of_le_of_ne hN.1.2 hNQ
      simp only [Nat.mod_eq_of_lt hlt]
      have : N ≠ 0 := by omega
      simp [this]
  · intro a ha
    simp only [Finset.mem_coe] at ha
    have haQ := hA a ha
    simp only
    split_ifs with h0
    · subst h0
      exact Nat.mod_self Q
    · exact Nat.mod_eq_of_lt haQ

/-- **Residue classes.** A union of `#A` residue classes modulo `Q` has density `#A / Q`. -/
theorem hasDens_mod_mem {Q : ℕ} (hQ : 0 < Q) (A : Finset ℕ) (hA : ∀ a ∈ A, a < Q) :
    HasDens {N : ℕ | N % Q ∈ A} (A.card / Q) := by
  have h := hasDens_of_periodic hQ (S := {N : ℕ | N % Q ∈ A})
    (fun N => by simp only [Set.mem_setOf_eq, Nat.add_mod_right])
  rwa [cnt_mod_mem_period hQ A hA] at h

/-- Explicit error term for a union of `#A` residue classes modulo `Q`. -/
theorem abs_cnt_mod_mem_sub_le {Q : ℕ} (hQ : 0 < Q) (A : Finset ℕ) (hA : ∀ a ∈ A, a < Q)
    {X : ℝ} (hX : 0 ≤ X) :
    |(cnt {N : ℕ | N % Q ∈ A} X : ℝ) - A.card * X / Q| ≤ A.card := by
  have h := abs_cnt_sub_le_of_periodic hQ (S := {N : ℕ | N % Q ∈ A})
    (fun N => by simp only [Set.mem_setOf_eq, Nat.add_mod_right]) hX
  rwa [cnt_mod_mem_period hQ A hA] at h

open Classical in
/-- **Membership depending only on `N mod Q`.** Then `S` has density `k / Q`, where `k` is the
number of residues `0 ≤ a < Q` lying in `S`. -/
theorem hasDens_of_mem_iff_mod_mem {S : Set ℕ} {Q : ℕ} (hQ : 0 < Q)
    (hS : ∀ N, N ∈ S ↔ N % Q ∈ S) :
    HasDens S (((Finset.range Q).filter (· ∈ S)).card / Q) := by
  have hSeq : S = {N : ℕ | N % Q ∈ (Finset.range Q).filter (· ∈ S)} := by
    ext N
    simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      exact ⟨Nat.mod_lt N hQ, (hS N).1 h⟩
    · intro h
      exact (hS N).2 h.2
  have h := hasDens_mod_mem hQ ((Finset.range Q).filter (· ∈ S))
    (fun a ha => Finset.mem_range.1 (Finset.mem_filter.1 ha).1)
  rw [← hSeq] at h
  exact h

/-! ## 7. Multiples -/

theorem cnt_dvd_eq (a : ℕ) (X : ℝ) : cnt {N : ℕ | a ∣ N} X = ⌊X⌋₊ / a := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div ⌊X⌋₊ a]
  unfold cnt
  congr 1
  ext x
  rw [mem_cntFinset, Finset.mem_filter, Finset.mem_Ioc, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by omega, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by omega, h2⟩, h3⟩

theorem cnt_dvd_le (a : ℕ) {X : ℝ} (hX : 0 ≤ X) : (cnt {N : ℕ | a ∣ N} X : ℝ) ≤ X / a := by
  rw [cnt_dvd_eq]
  calc ((⌊X⌋₊ / a : ℕ) : ℝ) ≤ (⌊X⌋₊ : ℝ) / a := Nat.cast_div_le
    _ ≤ X / a := div_le_div_of_nonneg_right (Nat.floor_le hX) (Nat.cast_nonneg a)

theorem setOf_dvd_eq_mod_mem (a : ℕ) :
    {N : ℕ | N % a ∈ ({0} : Finset ℕ)} = {N : ℕ | a ∣ N} := by
  ext N
  simp only [Set.mem_setOf_eq, Finset.mem_singleton]
  exact (Nat.dvd_iff_mod_eq_zero).symm

theorem abs_cnt_dvd_sub_le {a : ℕ} (ha : 1 ≤ a) {X : ℝ} (hX : 0 ≤ X) :
    |(cnt {N : ℕ | a ∣ N} X : ℝ) - X / a| ≤ 1 := by
  have h := abs_cnt_mod_mem_sub_le ha {0}
    (fun x hx => by rw [Finset.mem_singleton] at hx; omega) hX
  rw [setOf_dvd_eq_mod_mem, Finset.card_singleton, Nat.cast_one, one_mul] at h
  exact h

theorem hasDens_dvd {a : ℕ} (ha : 1 ≤ a) : HasDens {N : ℕ | a ∣ N} (1 / a) := by
  have h := hasDens_mod_mem ha {0} (fun x hx => by rw [Finset.mem_singleton] at hx; omega)
  rw [setOf_dvd_eq_mod_mem, Finset.card_singleton, Nat.cast_one] at h
  exact h

/-! ## 8. Eventual bounds ↔ density bounds, and rescaling -/

theorem le_lowerDens_of_eventually {S : Set ℕ} {c : ℝ}
    (h : ∀ᶠ n : ℕ in atTop, c * n ≤ cnt S n) : c ≤ lowerDens S := by
  apply le_liminf_of_le (isCoboundedUnder_ge_cnt_div S)
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [le_div_iff₀ hpos]
  exact hn

theorem upperDens_le_of_eventually {S : Set ℕ} {c : ℝ}
    (h : ∀ᶠ n : ℕ in atTop, (cnt S n : ℝ) ≤ c * n) : upperDens S ≤ c := by
  apply limsup_le_of_le (isCoboundedUnder_le_cnt_div S)
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [div_le_iff₀ hpos]
  exact hn

theorem le_lowerDens_of_forall_ge {S : Set ℕ} {c X₀ : ℝ}
    (h : ∀ X : ℝ, X₀ ≤ X → c * X ≤ cnt S X) : c ≤ lowerDens S :=
  le_lowerDens_of_eventually (eventually_atTop.2 ⟨⌈X₀⌉₊, fun n hn => h n (Nat.ceil_le.1 hn)⟩)

theorem upperDens_le_of_forall_ge {S : Set ℕ} {c X₀ : ℝ}
    (h : ∀ X : ℝ, X₀ ≤ X → (cnt S X : ℝ) ≤ c * X) : upperDens S ≤ c :=
  upperDens_le_of_eventually (eventually_atTop.2 ⟨⌈X₀⌉₊, fun n hn => h n (Nat.ceil_le.1 hn)⟩)

/-- **Rescaling (lower).** If `cnt S (C X) ≥ c X` for all large `X`, then `lowerDens S ≥ c / C`. -/
theorem le_lowerDens_of_scaled {S : Set ℕ} {C c X₀ : ℝ} (hC : 0 < C)
    (h : ∀ X : ℝ, X₀ ≤ X → c * X ≤ cnt S (C * X)) : c / C ≤ lowerDens S := by
  apply le_lowerDens_of_forall_ge (X₀ := C * X₀)
  intro Y hY
  have hY' : X₀ ≤ Y / C := by
    rw [le_div_iff₀ hC]
    linarith
  have h1 := h (Y / C) hY'
  have e : C * (Y / C) = Y := by
    field_simp
  rw [e] at h1
  calc c / C * Y = c * (Y / C) := by ring
    _ ≤ cnt S Y := h1

/-- **Rescaling (upper).** If `cnt S (C X) ≤ c X` for all large `X`, then `upperDens S ≤ c / C`. -/
theorem upperDens_le_of_scaled {S : Set ℕ} {C c X₀ : ℝ} (hC : 0 < C)
    (h : ∀ X : ℝ, X₀ ≤ X → (cnt S (C * X) : ℝ) ≤ c * X) : upperDens S ≤ c / C := by
  apply upperDens_le_of_forall_ge (X₀ := C * X₀)
  intro Y hY
  have hY' : X₀ ≤ Y / C := by
    rw [le_div_iff₀ hC]
    linarith
  have h1 := h (Y / C) hY'
  have e : C * (Y / C) = Y := by
    field_simp
  rw [e] at h1
  calc (cnt S Y : ℝ) ≤ c * (Y / C) := h1
    _ = c / C * Y := by ring

theorem eventually_mul_lt_cnt_of_lt_lowerDens {S : Set ℕ} {c : ℝ} (h : c < lowerDens S) :
    ∀ᶠ n : ℕ in atTop, c * n < cnt S n := by
  filter_upwards [eventually_lt_of_lt_liminf h (isBoundedUnder_ge_cnt_div S),
    eventually_ge_atTop 1] with n hn hn1
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
  rwa [lt_div_iff₀ hpos] at hn

theorem eventually_cnt_lt_mul_of_upperDens_lt {S : Set ℕ} {c : ℝ} (h : upperDens S < c) :
    ∀ᶠ n : ℕ in atTop, (cnt S n : ℝ) < c * n := by
  filter_upwards [eventually_lt_of_limsup_lt h (isBoundedUnder_le_cnt_div S),
    eventually_ge_atTop 1] with n hn hn1
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
  rwa [div_lt_iff₀ hpos] at hn

/-- Real-variable converse: `lowerDens S > c` gives `cnt S X ≥ c X` for all large real `X`. -/
theorem exists_mul_le_cnt_of_lt_lowerDens {S : Set ℕ} {c : ℝ} (h : c < lowerDens S) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → c * X ≤ cnt S X := by
  obtain ⟨c', hc1, hc2⟩ := exists_between h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_mul_lt_cnt_of_lt_lowerDens hc2)
  refine ⟨((max N ⌈c / (c' - c)⌉₊ : ℕ) : ℝ), fun X hX => ?_⟩
  have hX0 : 0 ≤ X := le_trans (Nat.cast_nonneg _) hX
  have hfl : max N ⌈c / (c' - c)⌉₊ ≤ ⌊X⌋₊ := Nat.le_floor hX
  have h1 : c' * ⌊X⌋₊ < cnt S X := by
    rw [← cnt_floor]
    exact hN _ (le_trans (le_max_left _ _) hfl)
  have hXlt : X < ⌊X⌋₊ + 1 := Nat.lt_floor_add_one X
  have hcnt0 : (0 : ℝ) ≤ cnt S X := Nat.cast_nonneg _
  rcases le_or_gt c 0 with hc | hc
  · nlinarith
  · have hd : 0 < c' - c := sub_pos.2 hc1
    have hM : c / (c' - c) ≤ ⌊X⌋₊ :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hfl)
    have hM' : c ≤ (c' - c) * ⌊X⌋₊ := by
      rw [div_le_iff₀ hd] at hM
      linarith
    have h2 : c * X ≤ c * (⌊X⌋₊ + 1) := mul_le_mul_of_nonneg_left hXlt.le hc.le
    nlinarith

/-- Real-variable converse: `upperDens S < c` gives `cnt S X ≤ c X` for all large real `X`. -/
theorem exists_cnt_le_mul_of_upperDens_lt {S : Set ℕ} {c : ℝ} (h : upperDens S < c) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → (cnt S X : ℝ) ≤ c * X := by
  have hc : 0 < c := lt_of_le_of_lt (upperDens_nonneg S) h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_cnt_lt_mul_of_upperDens_lt h)
  refine ⟨N, fun X hX => ?_⟩
  have hX0 : 0 ≤ X := le_trans (Nat.cast_nonneg _) hX
  have h1 := hN ⌊X⌋₊ (Nat.le_floor hX)
  rw [cnt_floor] at h1
  have h2 : c * (⌊X⌋₊ : ℝ) ≤ c * X := mul_le_mul_of_nonneg_left (Nat.floor_le hX0) hc.le
  linarith

end Principia.Erdos1054
