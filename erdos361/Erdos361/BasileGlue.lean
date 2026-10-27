import Mathlib
set_option maxHeartbeats 400000
open Finset

/-!
# Erdős #361 — Basile's Problem 7.1 (snd = 3 linear case): combinatorial glue

The combinatorial GLUE — distinctification (`Fin`→multiset bridge) + `Represents ↔ ¬Avoids` — that
turns a good core `G` covering `t` as an `h`-fold sum (`hLev`) into a genuine subset-sum witness. The
two classical inputs enter as HYPOTHESES to `basile71` (never axioms): Alon's Prop 2.5 good core
(discharged in-project by `good_core_exists`) and the located covering (discharged by `hLev_covering`,
which avoids Lev 1997 entirely). All theorems here are machine-verified: `#print axioms` is exactly
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Erdos361Basile71

/-- Avoider model (identical to `Erdos361_DSH_complete.Avoids`): `n ∉ Σ(A)`. -/
def Avoids (A : Finset ℕ) (n : ℕ) : Prop := ∀ B ⊆ A, B.sum id = n → B = ∅

/-- `A` has a nonempty subset of **distinct** elements summing to `t` — i.e. `t ∈ Σ(A)`. -/
def Represents (A : Finset ℕ) (t : ℕ) : Prop := ∃ B ⊆ A, B.Nonempty ∧ B.sum id = t

/-- `t` is a sum of exactly `h` elements of `G`, **repetitions allowed** (the `h`-fold sumset). -/
def RepWithRep (G : Finset ℕ) (h t : ℕ) : Prop :=
  ∃ f : Fin h → ℕ, (∀ i, f i ∈ G) ∧ (∑ i, f i) = t

/-- `g` is the midpoint of at least `11` three-term APs in `A`: there are `≥ 11` elements `x ∈ A`
with `x < g` and `2g - x ∈ A` (the pair `{x, 2g-x}`; distinct `x` give disjoint pairs). -/
def GoodCore (A G : Finset ℕ) : Prop :=
  G ⊆ A ∧ ∀ g ∈ G, 11 ≤ (A.filter (fun x => x < g ∧ 2 * g - x ∈ A)).card

/-- `Represents` is exactly the negation of `Avoids`. [glue] -/
theorem represents_iff_not_avoids (A : Finset ℕ) (t : ℕ) :
    Represents A t ↔ ¬ Avoids A t := by
  constructor
  · rintro ⟨B, hBA, hBne, hBsum⟩ hav
    exact absurd (hav B hBA hBsum) (Finset.nonempty_iff_ne_empty.mp hBne)
  · intro hav
    unfold Avoids at hav
    push_neg at hav
    obtain ⟨B, hBA, hBsum, hBne⟩ := hav
    exact ⟨B, hBA, hBne, hBsum⟩

/-- **Fresh-pair pigeonhole** [glue sub-lemma, the crux of distinctification].
A good `g` is the midpoint of `≥ 11` pairs `{x, 2g-x} ⊆ A` (indexed by `x ∈ A`, `x < g`, `2g-x ∈ A`);
distinct `x` give disjoint pairs, and each element of a support set `S` (`|S| ≤ 9`) blocks at most one
pair, so at least `2` pairs avoid `S`. -/
lemma good_fresh_pair (A G : Finset ℕ) (hgood : GoodCore A G) {g : ℕ} (hg : g ∈ G)
    (S : Finset ℕ) (hS : S.card ≤ 9) :
    ∃ x, x ∈ A ∧ (2 * g - x) ∈ A ∧ x < g ∧ x ∉ S ∧ (2 * g - x) ∉ S := by
  set P : Finset ℕ := A.filter (fun x => x < g ∧ 2 * g - x ∈ A) with hP
  have hPcard : 11 ≤ P.card := by rw [hP]; exact hgood.2 g hg
  have hmem : ∀ x ∈ P, x ∈ A ∧ x < g ∧ 2 * g - x ∈ A := by
    intro x hx; rw [hP, Finset.mem_filter] at hx; exact ⟨hx.1, hx.2.1, hx.2.2⟩
  set Bl : Finset ℕ := P.filter (fun x => x ∈ S ∨ 2 * g - x ∈ S) with hBl
  have hBlsub : Bl ⊆ P := by rw [hBl]; exact Finset.filter_subset _ _
  have hBlcard : Bl.card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun x => if x ∈ S then x else 2 * g - x)
    · intro x hx
      simp only [Finset.mem_coe, hBl, Finset.mem_filter] at hx
      by_cases hxS : x ∈ S
      · simpa [hxS] using hxS
      · rcases hx.2 with h | h
        · exact absurd h hxS
        · simpa [hxS] using h
    · intro x₁ hx₁ x₂ hx₂ heq
      simp only [Finset.mem_coe, hBl, Finset.mem_filter] at hx₁ hx₂
      have hlt₁ := (hmem x₁ hx₁.1).2.1
      have hlt₂ := (hmem x₂ hx₂.1).2.1
      by_cases h1 : x₁ ∈ S <;> by_cases h2 : x₂ ∈ S <;> simp only [h1, h2, if_true, if_false] at heq <;> omega
  have hBl9 : Bl.card ≤ 9 := le_trans hBlcard hS
  have hfree : (P \ Bl).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨x, hx⟩ := hfree
  rw [Finset.mem_sdiff] at hx
  obtain ⟨hxP, hxnBl⟩ := hx
  have hxm := hmem x hxP
  refine ⟨x, hxm.1, hxm.2.2, hxm.2.1, ?_, ?_⟩
  · intro hxS; exact hxnBl (by rw [hBl, Finset.mem_filter]; exact ⟨hxP, Or.inl hxS⟩)
  · intro hxS; exact hxnBl (by rw [hBl, Finset.mem_filter]; exact ⟨hxP, Or.inr hxS⟩)

/-- **Multiset distinctification** [glue — the induction].
A multiset `M` over `A` of size `≤ 11`, whose repeated elements are all good, has the same sum as some
`Nodup` multiset over `A` (repeatedly replace a doubled good `g` by a fresh pair `x + (2g-x)`). -/
lemma distinctify_ms (A G : Finset ℕ) (hgood : GoodCore A G) :
    ∀ M : Multiset ℕ, M.card ≤ 11 → (∀ x ∈ M, x ∈ A) → (∀ x, 2 ≤ M.count x → x ∈ G) →
      ∃ N : Multiset ℕ, N.Nodup ∧ (∀ x ∈ N, x ∈ A) ∧ N.sum = M.sum ∧ N.card = M.card := by
  suffices H : ∀ e : ℕ, ∀ M : Multiset ℕ, M.card - M.toFinset.card ≤ e → M.card ≤ 11 →
      (∀ x ∈ M, x ∈ A) → (∀ x, 2 ≤ M.count x → x ∈ G) →
      ∃ N : Multiset ℕ, N.Nodup ∧ (∀ x ∈ N, x ∈ A) ∧ N.sum = M.sum ∧ N.card = M.card by
    intro M h1 h2 h3; exact H _ M le_rfl h1 h2 h3
  intro e
  induction e with
  | zero =>
    intro M he hcard hA hrep
    have hnd : M.Nodup := by
      have h1 := Multiset.toFinset_card_le M
      have hcd : M.toFinset.card = M.dedup.card := rfl
      have hded : M.dedup = M :=
        Multiset.eq_of_le_of_card_le (Multiset.dedup_le M) (by omega)
      exact (Multiset.dedup_eq_self).mp hded
    exact ⟨M, hnd, hA, rfl, rfl⟩
  | succ e ih =>
    intro M he hcard hA hrep
    by_cases hnd : M.Nodup
    · exact ⟨M, hnd, hA, rfl, rfl⟩
    · -- pick a repeated (hence good) element g
      rw [Multiset.nodup_iff_count_le_one] at hnd
      push_neg at hnd
      obtain ⟨g, hgc⟩ := hnd
      have hg2 : 2 ≤ M.count g := by omega
      have hgG : g ∈ G := hrep g hg2
      have hgM : g ∈ M := Multiset.count_pos.mp (by omega)
      have hg_in_e : g ∈ M.erase g := by
        rw [← Multiset.count_pos, Multiset.count_erase_self]; omega
      set M0 : Multiset ℕ := (M.erase g).erase g with hM0
      -- M = g ::ₘ g ::ₘ M0
      have hMeq : M = g ::ₘ g ::ₘ M0 := by
        rw [hM0, Multiset.cons_erase hg_in_e, Multiset.cons_erase hgM]
      have hM0le : M0 ≤ M := (Multiset.erase_le _ _).trans (Multiset.erase_le _ _)
      have hM0card : M0.card + 2 = M.card := by
        rw [hMeq]; simp only [Multiset.card_cons]
      have hScard : M0.toFinset.card ≤ 9 := by
        have h1 := Multiset.toFinset_card_le M0
        have h2 : M0.card ≤ 9 := by omega
        omega
      obtain ⟨x, hxA, hyA, hxg, hxS, hyS⟩ := good_fresh_pair A G hgood hgG M0.toFinset hScard
      set y : ℕ := 2 * g - x with hy
      have hxM0 : x ∉ M0 := fun h => hxS (Multiset.mem_toFinset.mpr h)
      have hyM0 : y ∉ M0 := fun h => hyS (Multiset.mem_toFinset.mpr h)
      have hxney : x ≠ y := by rw [hy]; omega
      set M' : Multiset ℕ := x ::ₘ y ::ₘ M0 with hM'
      have hM'card : M'.card = M.card := by
        rw [hM', Multiset.card_cons, Multiset.card_cons]; omega
      have hxy : x + y = 2 * g := by rw [hy]; omega
      have hM'sum : M'.sum = M.sum := by
        rw [hM', hMeq, Multiset.sum_cons, Multiset.sum_cons, Multiset.sum_cons,
          Multiset.sum_cons]; omega
      -- counts: fresh x,y have count 1; everything else ≤ M
      have hcx0 : M0.count x = 0 := Multiset.count_eq_zero.mpr hxM0
      have hcy0 : M0.count y = 0 := Multiset.count_eq_zero.mpr hyM0
      have hM'A : ∀ z ∈ M', z ∈ A := by
        intro z hz
        rw [hM', Multiset.mem_cons, Multiset.mem_cons] at hz
        rcases hz with rfl | rfl | hz
        · exact hxA
        · exact hyA
        · exact hA z (Multiset.mem_of_le hM0le hz)
      have hM'rep : ∀ z, 2 ≤ M'.count z → z ∈ G := by
        intro z hz2
        have hcount : M'.count z =
            M0.count z + (if z = x then 1 else 0) + (if z = y then 1 else 0) := by
          rw [hM', Multiset.count_cons, Multiset.count_cons]; ring
        rw [hcount] at hz2
        have hle : M0.count z ≤ M.count z := Multiset.count_le_of_le z hM0le
        by_cases hzx : z = x
        · have hzny : ¬ z = y := fun h => hxney (by rw [← hzx]; exact h)
          rw [if_pos hzx, if_neg hzny, hzx, hcx0] at hz2; omega
        · by_cases hzy : z = y
          · rw [if_neg hzx, if_pos hzy, hzy, hcy0] at hz2; omega
          · rw [if_neg hzx, if_neg hzy] at hz2
            exact hrep z (by omega)
      -- excess strictly decreased: M'.toFinset.card = M0.toFinset.card + 2 > M.toFinset.card
      have hMtf : M.toFinset.card ≤ M0.toFinset.card + 1 := by
        rw [hMeq, Multiset.toFinset_cons, Multiset.toFinset_cons, Finset.insert_idem]
        exact Finset.card_insert_le _ _
      have hxni : x ∉ insert y M0.toFinset := by
        rw [Finset.mem_insert]; push_neg; exact ⟨hxney, hxS⟩
      have hM'tf : M'.toFinset.card = M0.toFinset.card + 2 := by
        rw [hM', Multiset.toFinset_cons, Multiset.toFinset_cons,
          Finset.card_insert_of_notMem hxni, Finset.card_insert_of_notMem hyS]
      have hexc : M'.card - M'.toFinset.card ≤ e := by
        rw [hM'card, hM'tf]; omega
      obtain ⟨N, hNnd, hNA, hNsum, hNcard⟩ :=
        ih M' hexc (by omega) hM'A hM'rep
      exact ⟨N, hNnd, hNA, by rw [hNsum, hM'sum], by rw [hNcard, hM'card]⟩

/-- **Distinctification** [glue — assembles the two lemmas above].
An `h`-fold sum (`h ≤ 11`, `t > 0`) of good-core elements is a genuine distinct subset sum of `A`. -/
theorem distinctify
    (A G : Finset ℕ) (hgood : GoodCore A G) {h t : ℕ} (hh : h ≤ 11) (ht : 0 < t)
    (hrep : RepWithRep G h t) : Represents A t := by
  obtain ⟨f, hfG, hfsum⟩ := hrep
  -- the multiset of the h summands
  set M : Multiset ℕ := (Finset.univ : Finset (Fin h)).val.map f with hM
  have hMcard : M.card ≤ 11 := by
    rw [hM]; simpa using hh
  have hMsum : M.sum = t := by
    rw [hM]; simpa [Finset.sum] using hfsum
  have hMA : ∀ x ∈ M, x ∈ A := by
    intro x hx; rw [hM] at hx; simp only [Multiset.mem_map, Finset.mem_val,
      Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx; exact hgood.1 (hfG i)
  have hMrep : ∀ x, 2 ≤ M.count x → x ∈ G := by
    intro x _; -- any element of M is f i ∈ G; refine via membership
    by_cases hxM : x ∈ M
    · rw [hM] at hxM; simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
        true_and] at hxM; obtain ⟨i, rfl⟩ := hxM; exact hfG i
    · exact absurd (Multiset.count_pos.mp (by omega)) hxM
  obtain ⟨N, hNnodup, hNA, hNsum, hNcard⟩ := distinctify_ms A G hgood M hMcard hMA hMrep
  have hNt : N.sum = t := by rw [hNsum, hMsum]
  have hNne : N ≠ 0 := by
    rintro rfl; simp only [Multiset.sum_zero] at hNt; omega
  refine ⟨N.toFinset, ?_, ?_, ?_⟩
  · intro x hx; exact hNA x (Multiset.mem_toFinset.mp hx)
  · obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hNne
    exact ⟨a, Multiset.mem_toFinset.mpr ha⟩
  · calc N.toFinset.sum id
        = (N.toFinset.val.map id).sum := rfl
      _ = N.toFinset.val.sum := by rw [Multiset.map_id]
      _ = N.dedup.sum := by rw [Multiset.toFinset_val]
      _ = N.sum := by rw [Multiset.Nodup.dedup hNnodup]
      _ = t := hNt

/-- **Covering** [glue — arithmetic from Lev's interval].
The hypothesis `hLev` packages Lev 1997 Thm 1′: for a good core `G` with `gcd ≤ 2` and the right
density, the union of the located intervals `hG` (`h ≤ 11`) contains every admissible `t ∈ (2E, 3E)`.
Here it is taken directly as the conclusion `∃ h ≤ 11, t ∈ hG`. -/
theorem basile71_glue
    (E t : ℕ) (A : Finset ℕ) (hAsub : A ⊆ Finset.Icc 1 E)
    (ht2 : 2 ∣ t) (ht3 : ¬ 3 ∣ t) (htlo : 2 * E < t) (hthi : t < 3 * E)
    (G : Finset ℕ) (hgood : GoodCore A G)
    (hLev : ∃ h, h ≤ 11 ∧ RepWithRep G h t) :
    ¬ Avoids A t := by
  obtain ⟨h, hh, hrep⟩ := hLev
  have ht : 0 < t := by omega
  have hR : Represents A t := distinctify A G hgood hh ht hrep
  exact (represents_iff_not_avoids A t).mp hR

/-- **Basile 7.1 (snd = 3 linear case), top-level candidate statement.**
For every `ε > 0`, every `A ⊆ [1,E]` of density `≥ 1/3 + ε` contains a subset summing to any even
`t ∈ (2E, 3E)` with `3 ∤ t`. The two external inputs enter as hypotheses, each a genuine classical
theorem (NOT trivially satisfiable):
* `hAlon` — **Alon's Proposition 2.5**: a dense set has a 3-AP *good core* of size `≥ (1/3+ε/2)E`.
  Formalizable on Mathlib's Roth theorem (`rothNumberNat_isLittleO_id`) + a 3-uniform-hypergraph Turán
  bound + the good/bad split.
* `hLev` — **Lev 1997 located interval + the gcd≤2 covering**: a good core of that size covers `t` as an
  `h`-fold sum, `h ≤ 11`. No Lean port; research-scale.
The size bound is essential to `hLev` — without it `hAlon` would be vacuously true (`G = ∅`) and `hLev`
unfactorable. -/
theorem basile71
    (ε : ℝ) (hε : 0 < ε)
    (hAlon : ∀ E : ℕ, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E → (1/3 + ε) * E ≤ A.card →
      ∃ G : Finset ℕ, GoodCore A G ∧ (1/3 + ε/2) * E ≤ (G.card : ℝ))
    (hLev : ∀ E t : ℕ, ∀ A G : Finset ℕ, GoodCore A G → (1/3 + ε/2) * E ≤ (G.card : ℝ) →
      2 * E < t → t < 3 * E → 2 ∣ t → ¬ 3 ∣ t → ∃ h, h ≤ 11 ∧ RepWithRep G h t) :
    ∀ E : ℕ, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E → (1/3 + ε) * E ≤ A.card →
      ∀ t : ℕ, 2 * E < t → t < 3 * E → 2 ∣ t → ¬ 3 ∣ t → ¬ Avoids A t := by
  intro E A hAsub hden t htlo hthi ht2 ht3
  obtain ⟨G, hgood, hGsize⟩ := hAlon E A hAsub hden
  exact basile71_glue E t A hAsub ht2 ht3 htlo hthi G hgood
    (hLev E t A G hgood hGsize htlo hthi ht2 ht3)

end Erdos361Basile71

-- Footprint gate:
#print axioms Erdos361Basile71.basile71
#print axioms Erdos361Basile71.basile71_glue
#print axioms Erdos361Basile71.distinctify
#print axioms Erdos361Basile71.distinctify_ms
#print axioms Erdos361Basile71.good_fresh_pair
#print axioms Erdos361Basile71.represents_iff_not_avoids
