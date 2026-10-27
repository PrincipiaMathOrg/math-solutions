import Mathlib
set_option maxHeartbeats 1000000
open Finset
open scoped Pointwise

/-!
# Erdős #361 — toward Freiman's `3k-3` in Lean (to discharge the last `hFreiman` hypothesis)

Goal: prove, from scratch (no Mathlib port exists), the lower bound in the exact shape the Basile-7.1
covering needs:

  `B ⊆ [0,L]`, `0,L ∈ B`, `|B| = k ≥ 3`, `gcd(B) = 1`, `L ≥ 2k-3`  ⟹  `3k-3 ≤ |B+B|`.

This is the contrapositive lower-bound form of Freiman's `3k-4` theorem. Built bottom-up.

Banked so far:
* `card_add_ge_two_mul_sub_one` — the ordered staircase baseline `2k-1 ≤ |B+B|` (the min·B and
  B·max chains meet in exactly one point). Foundation + sumset-counting infrastructure.

The hard `3k-3` step (case analysis on the AP-hull structure) is pending a constants-forced blueprint.
-/

namespace Erdos361Freiman

/-- **Staircase baseline** `2|B|-1 ≤ |B+B|` for a nonempty finite `B ⊆ ℕ`. The two chains
`a + B` (`a = min B`) and `B + z` (`z = max B`) each have `|B|` elements and meet only at `a+z`,
so their union — a subset of `B+B` — has `2|B|-1` elements. -/
lemma card_add_ge_two_mul_sub_one (B : Finset ℕ) (hB : B.Nonempty) :
    2 * B.card - 1 ≤ (B + B).card := by
  set a := B.min' hB with ha
  set z := B.max' hB with hz
  have haB : a ∈ B := B.min'_mem hB
  have hzB : z ∈ B := B.max'_mem hB
  have ha_le : ∀ b ∈ B, a ≤ b := fun b hb => B.min'_le b hb
  have hle_z : ∀ b ∈ B, b ≤ z := fun b hb => B.le_max' b hb
  -- the two chains
  set S1 := B.image (fun b => a + b) with hS1
  set S2 := B.image (fun b => b + z) with hS2
  have hS1sub : S1 ⊆ B + B := by
    intro x hx; rw [hS1, Finset.mem_image] at hx
    obtain ⟨b, hb, rfl⟩ := hx; exact Finset.add_mem_add haB hb
  have hS2sub : S2 ⊆ B + B := by
    intro x hx; rw [hS2, Finset.mem_image] at hx
    obtain ⟨b, hb, rfl⟩ := hx; exact Finset.add_mem_add hb hzB
  have hunionsub : S1 ∪ S2 ⊆ B + B := Finset.union_subset hS1sub hS2sub
  -- cardinalities of the chains
  have hS1card : S1.card = B.card :=
    Finset.card_image_of_injOn (fun x _ y _ h => by omega)
  have hS2card : S2.card = B.card :=
    Finset.card_image_of_injOn (fun x _ y _ h => by omega)
  -- the chains meet only at a + z
  have hinter : S1 ∩ S2 ⊆ {a + z} := by
    intro x hx
    rw [Finset.mem_inter] at hx
    obtain ⟨b, hb, hb1⟩ := Finset.mem_image.mp hx.1
    obtain ⟨b', hb', hb2⟩ := Finset.mem_image.mp hx.2
    have h1 := hle_z b hb; have h2 := ha_le b' hb'
    rw [Finset.mem_singleton]; omega
  have hintercard : (S1 ∩ S2).card ≤ 1 := le_trans (Finset.card_le_card hinter) (by simp)
  -- |S1 ∪ S2| = |S1| + |S2| - |S1 ∩ S2| ≥ 2k - 1
  have hadd := Finset.card_union_add_card_inter S1 S2
  rw [hS1card, hS2card] at hadd
  have : 2 * B.card - 1 ≤ (S1 ∪ S2).card := by omega
  exact le_trans this (Finset.card_le_card hunionsub)

#print axioms card_add_ge_two_mul_sub_one

/-- **Fact 2.3 (two-point overlap), the `≤ 3` direction.** If `P` has max `v` with no element strictly
between `u` and `v`, and `Q` has min `u` with no element strictly between `u` and `v`, then
`(P+P) ∩ (Q+Q) ⊆ {2u, u+v, 2v}`, so the overlap has at most `3` elements. (This is the direction the
induction's union bound `|X∪Y| = |X|+|Y|-|X∩Y|` needs.) -/
lemma two_point_overlap_le (P Q : Finset ℕ) (u v : ℕ) (huv : u < v)
    (hPmax : ∀ x ∈ P, x ≤ v) (hPgap : ∀ x ∈ P, u < x → v ≤ x)
    (hQmin : ∀ x ∈ Q, u ≤ x) (hQgap : ∀ x ∈ Q, x < v → x ≤ u) :
    ((P + P) ∩ (Q + Q)).card ≤ 3 := by
  have hsub : (P + P) ∩ (Q + Q) ⊆ ({2 * u, u + v, 2 * v} : Finset ℕ) := by
    intro z hz
    rw [Finset.mem_inter] at hz
    obtain ⟨p1, hp1, p2, hp2, hpz⟩ := Finset.mem_add.mp hz.1
    obtain ⟨q1, hq1, q2, hq2, hqz⟩ := Finset.mem_add.mp hz.2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases le_or_gt (u + v) z with hge | hlt
    · -- z ≥ u+v: both P-summands lie in {u,v}
      have hp1v := hPmax p1 hp1; have hp2v := hPmax p2 hp2
      have hp1u : u ≤ p1 := by by_contra h; push_neg at h; omega
      have hp2u : u ≤ p2 := by by_contra h; push_neg at h; omega
      have hp1uv : p1 = u ∨ p1 = v := by
        rcases eq_or_lt_of_le hp1u with h | h
        · left; omega
        · right; exact hPgap p1 hp1 h |>.antisymm hp1v |>.symm
      have hp2uv : p2 = u ∨ p2 = v := by
        rcases eq_or_lt_of_le hp2u with h | h
        · left; omega
        · right; exact hPgap p2 hp2 h |>.antisymm hp2v |>.symm
      rcases hp1uv with rfl | rfl <;> rcases hp2uv with rfl | rfl <;> omega
    · -- z < u+v: both Q-summands equal u, so z = 2u
      have hq1u := hQmin q1 hq1; have hq2u := hQmin q2 hq2
      have hq1eq : q1 = u := by
        rcases eq_or_lt_of_le hq1u with h | h
        · exact h.symm
        · exfalso
          have hge : v ≤ q1 := by
            by_contra hh; push_neg at hh; have := hQgap q1 hq1 hh; omega
          omega
      have hq2eq : q2 = u := by
        rcases eq_or_lt_of_le hq2u with h | h
        · exact h.symm
        · exfalso
          have hge : v ≤ q2 := by
            by_contra hh; push_neg at hh; have := hQgap q2 hq2 hh; omega
          omega
      omega
  have h3 : ({2 * u, u + v, 2 * v} : Finset ℕ).card ≤ 3 := by
    have e1 := Finset.card_insert_le (2 * u) ({u + v, 2 * v} : Finset ℕ)
    have e2 := Finset.card_insert_le (u + v) ({2 * v} : Finset ℕ)
    simp only [Finset.card_singleton] at *
    omega
  exact le_trans (Finset.card_le_card hsub) h3

#print axioms two_point_overlap_le

/-- **Hole-covering (crux of the small-diameter lemma).** For `A ⊆ [0,M]` with `0,M ∈ A`,
`M ≤ 2|A|-3`, and a hole `w ∈ [1,M-1] \ A`, at least one of `w`, `M+w` lies in `A+A`. Proof: the
families `Y_w` (size `|A|-1`) and `Z_w = {M+w-a : a∈A, 0<a<M}` (size `|A|-2`) both sit inside the
length-`(M-1)` window `[w+1, w+M-1]`, and `(|A|-1)+(|A|-2) = 2|A|-3 > M-1`, so they intersect. -/
lemma hole_covered (A : Finset ℕ) (M : ℕ) (hAsub : A ⊆ Finset.Icc 0 M)
    (h0 : 0 ∈ A) (hM : M ∈ A) (hMle : M ≤ 2 * A.card - 3)
    (w : ℕ) (hw1 : 1 ≤ w) (hw2 : w ≤ M - 1) (hwA : w ∉ A) :
    w ∈ A + A ∨ M + w ∈ A + A := by
  set n := A.card with hn
  have hMx : ∀ a ∈ A, a ≤ M := fun a ha => by have := hAsub ha; rw [Finset.mem_Icc] at this; omega
  have hM2 : 2 ≤ M := by omega
  have hn3 : 3 ≤ n := by omega
  -- pieces of Y_w
  set F1 := A.filter (fun a => w < a) with hF1
  set F2 := A.filter (fun a => 0 < a ∧ a < w) with hF2
  set F2img := F2.image (fun a => M + a) with hF2img
  set Yw := F1 ∪ F2img with hYw
  -- Z_w
  set G := A.filter (fun a => 0 < a ∧ a < M) with hG
  set Zw := G.image (fun a => M + w - a) with hZw
  set Iw := Finset.Icc (w + 1) (w + M - 1) with hIw
  -- |F1| + |F2| = n - 1  (F1 ⊔ F2 = positive elements of A)
  have hposA : A.filter (fun a => 0 < a) = F1 ∪ F2 := by
    rw [hF1, hF2]; ext a
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨ha, hapos⟩
      have hane : a ≠ w := fun h => hwA (h ▸ ha)
      rcases lt_or_gt_of_ne hane with h | h
      · exact Or.inr ⟨ha, hapos, h⟩
      · exact Or.inl ⟨ha, h⟩
    · rintro (⟨ha, h⟩ | ⟨ha, hp, h⟩) <;> exact ⟨ha, by omega⟩
  have hF12disj : Disjoint F1 F2 := by
    rw [hF1, hF2, Finset.disjoint_filter]
    intro a _ h; omega
  have hposcard : (A.filter (fun a => 0 < a)).card = n - 1 := by
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := A) (p := fun a => 0 < a)
    have h0only : (A.filter (fun a => ¬ 0 < a)).card = 1 := by
      have : A.filter (fun a => ¬ 0 < a) = {0} := by
        ext a; simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨_, h⟩; omega
        · rintro rfl; exact ⟨h0, by omega⟩
      rw [this]; simp
    omega
  have hF1F2 : F1.card + F2.card = n - 1 := by
    rw [← Finset.card_union_of_disjoint hF12disj, ← hposA, hposcard]
  -- |Y_w| = n - 1
  have hF2imgcard : F2img.card = F2.card :=
    Finset.card_image_of_injOn (fun a _ b _ h => by omega)
  have hYdisj : Disjoint F1 F2img := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [hF1, Finset.mem_filter] at hx1
    rw [hF2img, Finset.mem_image] at hx2
    obtain ⟨b, hb, rfl⟩ := hx2
    rw [hF2, Finset.mem_filter] at hb
    have hxM := hMx (M + b) hx1.1
    omega
  have hYcard : Yw.card = n - 1 := by
    rw [hYw, Finset.card_union_of_disjoint hYdisj, hF2imgcard, hF1F2]
  -- |Z_w| = n - 2
  have hGcard : G.card = n - 2 := by
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := A) (p := fun a => 0 < a ∧ a < M)
    have hcompl : A.filter (fun a => ¬ (0 < a ∧ a < M)) = {0, M} := by
      ext a; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, h⟩; have := hMx a ha; omega
      · rintro (rfl | rfl) <;> [exact ⟨h0, by omega⟩; exact ⟨hM, by omega⟩]
    have : (A.filter (fun a => ¬ (0 < a ∧ a < M))).card = 2 := by
      rw [hcompl, Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    rw [← hG] at hsplit; omega
  have hZcard : Zw.card = n - 2 :=
    (Finset.card_image_of_injOn (fun a ha b hb h => by
      rw [hG, Finset.mem_coe, Finset.mem_filter] at ha hb; omega)).trans hGcard
  -- both ⊆ I_w
  have hYsub : Yw ⊆ Iw := by
    intro x hx
    rw [hYw, Finset.mem_union] at hx
    rw [hIw, Finset.mem_Icc]
    rcases hx with hx | hx
    · rw [hF1, Finset.mem_filter] at hx
      have := hMx x hx.1; omega
    · rw [hF2img, Finset.mem_image] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      rw [hF2, Finset.mem_filter] at hb; omega
  have hZsub : Zw ⊆ Iw := by
    intro x hx
    rw [hZw, Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hG, Finset.mem_filter] at ha
    rw [hIw, Finset.mem_Icc]; omega
  have hIcard : Iw.card = M - 1 := by rw [hIw, Nat.card_Icc]; omega
  -- pigeonhole
  have hinter : (Yw ∩ Zw).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hdisj : Disjoint Yw Zw := Finset.disjoint_iff_inter_eq_empty.mpr hemp
    have hle : Yw.card + Zw.card ≤ Iw.card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (Finset.union_subset hYsub hZsub)
    rw [hYcard, hZcard, hIcard] at hle; omega
  obtain ⟨c, hc⟩ := hinter
  rw [Finset.mem_inter] at hc
  -- c ∈ Z_w gives c = M + w - a  (a ∈ A, 0 < a < M)
  obtain ⟨a, ha, hca⟩ := Finset.mem_image.mp (by rw [← hZw]; exact hc.2)
  rw [hG, Finset.mem_filter] at ha
  -- c ∈ Y_w: either c = a' ∈ A (a' > w) → M+w ∈ A+A, or c = M + a' (a' ∈ A) → w ∈ A+A
  rw [hYw, Finset.mem_union] at hc
  rcases hc.1 with hcY | hcY
  · -- c ∈ F1: c ∈ A, c > w.  M + w - a = c, so M + w = c + a ∈ A+A
    rw [hF1, Finset.mem_filter] at hcY
    right
    have : M + w = c + a := by omega
    rw [this]; exact Finset.add_mem_add hcY.1 ha.1
  · -- c ∈ F2img: c = M + a', a' ∈ A, 0 < a' < w.  M+w-a = M+a', so w = a' + a ∈ A+A
    rw [hF2img, Finset.mem_image] at hcY
    obtain ⟨a', ha', hca'⟩ := hcY
    rw [hF2, Finset.mem_filter] at ha'
    left
    have : w = a' + a := by omega
    rw [this]; exact Finset.add_mem_add ha'.1 ha.1

#print axioms hole_covered

/-- **Lemma 3.1 (small-diameter).** If `A ⊆ [0,M]` with `0,M ∈ A`, `n = |A| ≥ 2`, and `M ≤ 2n-3`,
then `n + M ≤ |A+A|`. The boundary staircase `S = A ∪ (M+A)` has `2n-1` elements; each of the `M+1-n`
holes `w` contributes a fresh element (`w` or `M+w`, by `hole_covered`) disjoint from `S`. -/
lemma small_diameter (A : Finset ℕ) (M : ℕ) (hAsub : A ⊆ Finset.Icc 0 M)
    (h0 : 0 ∈ A) (hM : M ∈ A) (hn2 : 2 ≤ A.card) (hMle : M ≤ 2 * A.card - 3) :
    A.card + M ≤ (A + A).card := by
  set n := A.card with hn
  have hMx : ∀ a ∈ A, a ≤ M := fun a ha => by have := hAsub ha; rw [Finset.mem_Icc] at this; omega
  have hM1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with hM0 | h
    · subst hM0
      have hsub : A ⊆ {0} := by intro a ha; have := hMx a ha; simp; omega
      have := Finset.card_le_card hsub; simp at this; omega
    · exact h
  -- boundary staircase S = A ∪ (M + A), size 2n-1
  set MA := A.image (fun a => M + a) with hMA
  set S := A ∪ MA with hS
  have hMAcard : MA.card = n := Finset.card_image_of_injOn (fun a _ b _ h => by omega)
  have hAMAinter : A ∩ MA = {M} := by
    ext x; simp only [Finset.mem_inter, Finset.mem_singleton, hMA, Finset.mem_image]
    constructor
    · rintro ⟨hxA, b, hb, rfl⟩; have := hMx (M + b) hxA; omega
    · rintro rfl; exact ⟨hM, 0, h0, by omega⟩
  have hScard : S.card = 2 * n - 1 := by
    have hadd : S.card + (A ∩ MA).card = A.card + MA.card := by
      rw [hS]; exact Finset.card_union_add_card_inter A MA
    rw [hAMAinter, Finset.card_singleton, hMAcard, ← hn] at hadd
    omega
  have hSsub : S ⊆ A + A := by
    intro x hx; rw [hS, Finset.mem_union] at hx
    rcases hx with hx | hx
    · rw [show x = 0 + x by omega]; exact Finset.add_mem_add h0 hx
    · rw [hMA, Finset.mem_image] at hx; obtain ⟨b, hb, rfl⟩ := hx
      exact Finset.add_mem_add hM hb
  -- holes H = [1,M-1] \ A, size M+1-n
  set H := (Finset.Icc 1 (M - 1)) \ A with hH
  have hHcard : H.card = M + 1 - n := by
    rw [hH, Finset.card_sdiff]
    have hint : A ∩ Finset.Icc 1 (M - 1) = A.filter (fun a => 0 < a ∧ a < M) := by
      ext a; simp only [Finset.mem_inter, Finset.mem_Icc, Finset.mem_filter]
      constructor
      · rintro ⟨ha, h⟩; exact ⟨ha, by omega⟩
      · rintro ⟨ha, h⟩; refine ⟨ha, by omega, ?_⟩; have := hMx a ha; omega
    have hmid : (A.filter (fun a => 0 < a ∧ a < M)).card = n - 2 := by
      have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := A) (p := fun a => 0 < a ∧ a < M)
      have hcompl : A.filter (fun a => ¬ (0 < a ∧ a < M)) = {0, M} := by
        ext a; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨ha, h⟩; have := hMx a ha; omega
        · rintro (rfl | rfl) <;> [exact ⟨h0, by omega⟩; exact ⟨hM, by omega⟩]
      have h2 : (A.filter (fun a => ¬ (0 < a ∧ a < M))).card = 2 := by
        rw [hcompl, Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      omega
    rw [hint, hmid, Nat.card_Icc]; omega
  -- split H by membership in A+A
  set H1 := H.filter (fun w => w ∈ A + A) with hH1
  set H2 := H.filter (fun w => w ∉ A + A) with hH2
  set H2img := H2.image (fun w => M + w) with hH2img
  set phiH := H1 ∪ H2img with hphi
  have hH12 : H1.card + H2.card = H.card := by
    rw [hH1, hH2]
    exact Finset.filter_card_add_filter_neg_card_eq_card (s := H) (p := fun w => w ∈ A + A)
  have hH2imgcard : H2img.card = H2.card := Finset.card_image_of_injOn (fun a _ b _ h => by omega)
  -- φH ⊆ A+A
  have hphisub : phiH ⊆ A + A := by
    intro x hx; rw [hphi, Finset.mem_union] at hx
    rcases hx with hx | hx
    · rw [hH1, Finset.mem_filter] at hx; exact hx.2
    · rw [hH2img, Finset.mem_image] at hx; obtain ⟨w, hw, rfl⟩ := hx
      rw [hH2, Finset.mem_filter, hH, Finset.mem_sdiff, Finset.mem_Icc] at hw
      rcases hole_covered A M hAsub h0 hM hMle w hw.1.1.1 hw.1.1.2 hw.1.2 with h | h
      · exact absurd h hw.2
      · exact h
  -- φH is disjoint from S and internally, so |φH| = |H|
  have hH1H2img : Disjoint H1 H2img := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    rw [hH1, Finset.mem_filter, hH, Finset.mem_sdiff, Finset.mem_Icc] at hx1
    rw [hH2img, Finset.mem_image] at hx2; obtain ⟨w, hw, rfl⟩ := hx2
    rw [hH2, Finset.mem_filter, hH, Finset.mem_sdiff, Finset.mem_Icc] at hw
    omega
  have hphicard : phiH.card = M + 1 - n := by
    rw [hphi, Finset.card_union_of_disjoint hH1H2img, hH2imgcard, hH12, hHcard]
  -- S and φH are disjoint
  have hSphi : Disjoint S phiH := by
    rw [Finset.disjoint_left]; intro x hxS hxphi
    rw [hphi, Finset.mem_union] at hxphi
    rw [hS, Finset.mem_union, hMA, Finset.mem_image] at hxS
    rcases hxphi with hx1 | hx2
    · rw [hH1, Finset.mem_filter, hH, Finset.mem_sdiff, Finset.mem_Icc] at hx1
      rcases hxS with hxA | ⟨b, hb, rfl⟩
      · exact hx1.1.2 hxA
      · have := hMx b hb; omega
    · rw [hH2img, Finset.mem_image] at hx2; obtain ⟨w, hw, rfl⟩ := hx2
      rw [hH2, Finset.mem_filter, hH, Finset.mem_sdiff, Finset.mem_Icc] at hw
      rcases hxS with hxA | ⟨b, hb, hbeq⟩
      · have := hMx (M + w) hxA; omega
      · have := hMx b hb; have hwA := hw.1.2; apply hwA
        have : b = w := by omega
        rw [← this]; exact hb
  -- assemble
  have hunion : S ∪ phiH ⊆ A + A := Finset.union_subset hSsub hphisub
  have : (S ∪ phiH).card = 2 * n - 1 + (M + 1 - n) := by
    rw [Finset.card_union_of_disjoint hSphi, hScard, hphicard]
  have hfinal : n + M ≤ (S ∪ phiH).card := by rw [this]; omega
  exact le_trans hfinal (Finset.card_le_card hunion)

#print axioms small_diameter

/-- **Induction case `d > 1`** (blueprint §5). If the spacing gcd `d = gcd(B∖{L}) > 1`, then
`A' := B∖{L}` is `d`-divisible while `L+A'` is not (as `gcd(B)=1 ⟹ d ∤ L`), and `2L` exceeds both;
so `(A'+A'), (L+A'), {2L}` are pairwise disjoint in `B+B`, giving `(2k-3)+(k-1)+1 = 3k-3`. -/
lemma case_d_gt_one (B : Finset ℕ) (L : ℕ) (hAsub : B ⊆ Finset.Icc 0 L)
    (h0 : 0 ∈ B) (hL : L ∈ B) (hk3 : 3 ≤ B.card) (hgcd : B.gcd id = 1)
    (hd : 1 < (B.erase L).gcd id) :
    3 * B.card - 3 ≤ (B + B).card := by
  set A' := B.erase L with hA'
  set d := A'.gcd id with hd'
  have hLpos : 0 < L := by
    by_contra h; push_neg at h
    have hsub : B ⊆ {0} := fun b hb => by
      have := hAsub hb; rw [Finset.mem_Icc] at this; simp; omega
    have := Finset.card_le_card hsub; simp at this; omega
  have hA'card : A'.card = B.card - 1 := by rw [hA', Finset.card_erase_of_mem hL]
  have hA'sub : A' ⊆ B := Finset.erase_subset _ _
  have h0' : 0 ∈ A' := Finset.mem_erase.mpr ⟨by omega, h0⟩
  have hA'ne : A'.Nonempty := ⟨0, h0'⟩
  have haLt : ∀ a ∈ A', a < L := by
    intro a ha
    have haL : a ≠ L := (Finset.mem_erase.mp ha).1
    have := hAsub (hA'sub ha); rw [Finset.mem_Icc] at this; omega
  have hdvd : ∀ a ∈ A', d ∣ a := fun a ha => Finset.gcd_dvd ha
  have hdnL : ¬ d ∣ L := by
    intro hdL
    have hdB : d ∣ B.gcd id := Finset.dvd_gcd (fun b hb => by
      by_cases h : b = L
      · rw [h]; exact hdL
      · exact hdvd b (Finset.mem_erase.mpr ⟨h, hb⟩))
    rw [hgcd] at hdB
    have := Nat.le_of_dvd Nat.one_pos hdB; omega
  set P := A' + A' with hP
  set Q := A'.image (fun a => L + a) with hQ
  have hPsub : P ⊆ B + B := by
    rw [hP]; intro x hx; rw [Finset.mem_add] at hx ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hx; exact ⟨a, hA'sub ha, b, hA'sub hb, rfl⟩
  have hQsub : Q ⊆ B + B := by
    rw [hQ]; intro x hx; rw [Finset.mem_image] at hx; obtain ⟨a, ha, rfl⟩ := hx
    exact Finset.add_mem_add hL (hA'sub ha)
  have h2Lsub : ({2 * L} : Finset ℕ) ⊆ B + B := by
    intro x hx; rw [Finset.mem_singleton] at hx; subst hx
    rw [show 2 * L = L + L by ring]; exact Finset.add_mem_add hL hL
  have hPd : ∀ x ∈ P, d ∣ x := by
    rw [hP]; intro x hx; rw [Finset.mem_add] at hx; obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact dvd_add (hdvd a ha) (hdvd b hb)
  have hQnd : ∀ x ∈ Q, ¬ d ∣ x := by
    rw [hQ]; intro x hx; rw [Finset.mem_image] at hx; obtain ⟨a, ha, rfl⟩ := hx
    intro hdx
    exact hdnL ((Nat.dvd_add_right (hdvd a ha)).mp (by rwa [Nat.add_comm] at hdx))
  have hPlt : ∀ x ∈ P, x < 2 * L := by
    rw [hP]; intro x hx; rw [Finset.mem_add] at hx; obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have := haLt a ha; have := haLt b hb; omega
  have hQlt : ∀ x ∈ Q, x < 2 * L := by
    rw [hQ]; intro x hx; rw [Finset.mem_image] at hx; obtain ⟨a, ha, rfl⟩ := hx
    have := haLt a ha; omega
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]; intro x hxP hxQ; exact hQnd x hxQ (hPd x hxP)
  have hP2L : Disjoint P ({2 * L} : Finset ℕ) := by
    rw [Finset.disjoint_left]; intro x hxP hx2; rw [Finset.mem_singleton] at hx2
    have := hPlt x hxP; omega
  have hQ2L : Disjoint Q ({2 * L} : Finset ℕ) := by
    rw [Finset.disjoint_left]; intro x hxQ hx2; rw [Finset.mem_singleton] at hx2
    have := hQlt x hxQ; omega
  have hQcard : Q.card = A'.card := Finset.card_image_of_injOn (fun a _ b _ h => by omega)
  have hPcard : 2 * A'.card - 1 ≤ P.card := by rw [hP]; exact card_add_ge_two_mul_sub_one A' hA'ne
  have hun : P ∪ Q ∪ {2 * L} ⊆ B + B :=
    Finset.union_subset (Finset.union_subset hPsub hQsub) h2Lsub
  have hdisj12 : Disjoint (P ∪ Q) ({2 * L} : Finset ℕ) := Finset.disjoint_union_left.mpr ⟨hP2L, hQ2L⟩
  have hcard : (P ∪ Q ∪ {2 * L}).card = P.card + Q.card + 1 := by
    rw [Finset.card_union_of_disjoint hdisj12, Finset.card_union_of_disjoint hPQ,
      Finset.card_singleton]
  have hfinal : 3 * B.card - 3 ≤ (P ∪ Q ∪ {2 * L}).card := by
    rw [hcard, hQcard, hA'card]; omega
  exact le_trans hfinal (Finset.card_le_card hun)

#print axioms case_d_gt_one

/-- **Base case `k = 3`** (blueprint §4.1). `B = {0,a,L}` with `0<a<L`, `gcd = 1`, `L ≥ 3`. The six
sums `0,a,2a,L,L+a,2L` are distinct — the only possible clash `2a=L` is killed because then `a` divides
every element, so `a ∣ gcd(B) = 1`, forcing `a=1, L=2 < 3`. Hence `|B+B| ≥ 6 = 3k-3`. -/
lemma base_case_k3 (B : Finset ℕ) (L : ℕ) (hAsub : B ⊆ Finset.Icc 0 L)
    (h0 : 0 ∈ B) (hL : L ∈ B) (hcard3 : B.card = 3) (hgcd : B.gcd id = 1) (hLge : 3 ≤ L) :
    3 * B.card - 3 ≤ (B + B).card := by
  rw [hcard3]
  obtain ⟨a, haB, ha0, haL⟩ : ∃ a ∈ B, a ≠ 0 ∧ a ≠ L := by
    by_contra hcon; push_neg at hcon
    have hsub : B ⊆ {0, L} := by
      intro b hb; rw [Finset.mem_insert, Finset.mem_singleton]
      by_cases hb0 : b = 0
      · exact Or.inl hb0
      · exact Or.inr (hcon b hb hb0)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton] at hle
    omega
  have haLt : a < L := by have := hAsub haB; rw [Finset.mem_Icc] at this; omega
  have hapos : 0 < a := by omega
  have hBeq : B = {0, a, L} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx; rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      exacts [h0, haB, hL]
    · rw [hcard3]
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  have h2aL : 2 * a ≠ L := by
    intro he
    have hacd : a ∣ B.gcd id := Finset.dvd_gcd (fun b hb => by
      rw [hBeq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with h | h | h
      · rw [h]; exact dvd_zero a
      · rw [h]; exact dvd_refl a
      · rw [h]; show a ∣ L; rw [← he]; exact dvd_mul_left a 2)
    rw [hgcd] at hacd
    have := Nat.le_of_dvd Nat.one_pos hacd; omega
  -- the six distinct sums
  have hsub : ({0, a, 2 * a, L, L + a, 2 * L} : Finset ℕ) ⊆ B + B := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h | h | h
    · rw [h, show (0 : ℕ) = 0 + 0 by ring]; exact Finset.add_mem_add h0 h0
    · rw [h, show a = 0 + a by ring]; exact Finset.add_mem_add h0 haB
    · rw [h, show 2 * a = a + a by ring]; exact Finset.add_mem_add haB haB
    · rw [h, show L = 0 + L by ring]; exact Finset.add_mem_add h0 hL
    · rw [h, show L + a = a + L by ring]; exact Finset.add_mem_add haB hL
    · rw [h, show 2 * L = L + L by ring]; exact Finset.add_mem_add hL hL
  have hc6 : ({0, a, 2 * a, L, L + a, 2 * L} : Finset ℕ).card = 6 := by
    rw [Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  have h6 : (6 : ℕ) ≤ (B + B).card := hc6 ▸ Finset.card_le_card hsub
  omega

#print axioms base_case_k3

/-- **Fill lemma (core of Case 1).** If `0 ∈ A'` and for every `c ∈ [1,K]` we have
`c ≤ 2·#{a∈A' : 0<a<c}` (the density condition), then `[0,K] ⊆ A'+A'`. Proof: a hole `c` gives
`D1 = {a∈A':0<a<c}` and `D2 = {c-a : a∈D1}`, both in `[1,c-1]`, with `|D1|+|D2| = 2·|D1| ≥ c > c-1`,
so they intersect and `c` is a subset sum. -/
lemma fill (A' : Finset ℕ) (K : ℕ) (h0 : 0 ∈ A')
    (hdens : ∀ c, 1 ≤ c → c ≤ K → c ∉ A' → c ≤ 2 * (A'.filter (fun a => 0 < a ∧ a < c)).card) :
    Finset.Icc 0 K ⊆ A' + A' := by
  intro c hc
  rw [Finset.mem_Icc] at hc
  rcases Nat.eq_zero_or_pos c with rfl | hcpos
  · rw [show (0 : ℕ) = 0 + 0 by ring]; exact Finset.add_mem_add h0 h0
  · by_cases hcA : c ∈ A'
    · rw [show c = 0 + c by ring]; exact Finset.add_mem_add h0 hcA
    · set D1 := A'.filter (fun a => 0 < a ∧ a < c) with hD1
      set D2 := D1.image (fun a => c - a) with hD2
      have hd1sub : D1 ⊆ Finset.Icc 1 (c - 1) := by
        intro a ha; rw [hD1, Finset.mem_filter] at ha; rw [Finset.mem_Icc]; omega
      have hd2sub : D2 ⊆ Finset.Icc 1 (c - 1) := by
        intro x hx; rw [hD2, Finset.mem_image] at hx; obtain ⟨a, ha, rfl⟩ := hx
        rw [hD1, Finset.mem_filter] at ha; rw [Finset.mem_Icc]; omega
      have hd2card : D2.card = D1.card :=
        Finset.card_image_of_injOn (fun a ha b hb h => by
          rw [hD1, Finset.mem_coe, Finset.mem_filter] at ha hb; omega)
      have hdens' := hdens c hcpos hc.2 hcA
      rw [← hD1] at hdens'
      have hinter : (D1 ∩ D2).Nonempty := by
        by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have hdisj : Disjoint D1 D2 := Finset.disjoint_iff_inter_eq_empty.mpr hemp
        have hle : D1.card + D2.card ≤ (Finset.Icc 1 (c - 1)).card := by
          rw [← Finset.card_union_of_disjoint hdisj]
          exact Finset.card_le_card (Finset.union_subset hd1sub hd2sub)
        rw [hd2card, Nat.card_Icc] at hle; omega
      obtain ⟨z, hz⟩ := hinter
      rw [Finset.mem_inter] at hz
      have hzD1 := hz.1; rw [hD1, Finset.mem_filter] at hzD1
      obtain ⟨a', ha'D1, hza'⟩ := Finset.mem_image.mp (show z ∈ D1.image (fun a => c - a) from hz.2)
      rw [hD1, Finset.mem_filter] at ha'D1
      have hce : c = z + a' := by omega
      rw [hce]; exact Finset.add_mem_add hzD1.1 ha'D1.1

#print axioms fill

/-- **Case 1 (index-free), direct `3k-3`.** If every positive non-maximal `x ∈ B` satisfies the
dense-prefix condition `x < 2·#{a∈B : 0<a≤x}` (equivalently `a_i < 2i` for the sorted enumeration),
then `[0,2k-4] ⊆ B+B`; together with the top chain `L+B` (disjoint, size `k`) this gives `3k-3`.
This is the fully index-free formalization of §7 (Case 1) of the blueprint — the sorted enumeration
is replaced by the count `#{a∈B : 0<a≤x}`, and the `(j+1)`-th element is recovered as the `min'`
of the tail `{a∈B : c≤a<L}`. -/
lemma case1_direct (B : Finset ℕ) (L : ℕ) (hBsub : B ⊆ Finset.Icc 0 L)
    (h0 : 0 ∈ B) (hLB : L ∈ B) (hk : 3 ≤ B.card) (hL : 2 * B.card - 2 ≤ L)
    (hcase1 : ∀ x ∈ B, 0 < x → x < L →
      x < 2 * (B.filter (fun a => 0 < a ∧ a ≤ x)).card) :
    3 * B.card - 3 ≤ (B + B).card := by
  set k := B.card with hkdef
  have hMx : ∀ a ∈ B, a ≤ L := fun a ha => by
    have := hBsub ha; rw [Finset.mem_Icc] at this; omega
  -- Step 1: derive fill's density hypothesis for K = 2k-4
  have hdens : ∀ c, 1 ≤ c → c ≤ 2 * k - 4 → c ∉ B →
      c ≤ 2 * (B.filter (fun a => 0 < a ∧ a < c)).card := by
    intro c hc1 hcK hcB
    set D1 := B.filter (fun a => 0 < a ∧ a < c) with hD1
    set j := D1.card with hj
    -- tail T = positive elements in [c, L)
    set T := B.filter (fun a => c ≤ a ∧ a < L) with hT
    by_cases hTne : T.Nonempty
    · -- b* = min of T ; then #{0<a≤b*} = j+1
      obtain ⟨bs, hbsT⟩ := hTne
      set b := T.min' ⟨bs, hbsT⟩ with hb
      have hbT : b ∈ T := T.min'_mem _
      rw [hT, Finset.mem_filter] at hbT
      have hbB : b ∈ B := hbT.1
      have hbge : c ≤ b := hbT.2.1
      have hblt : b < L := hbT.2.2
      have hbpos : 0 < b := by omega
      have hbmin : ∀ a ∈ T, b ≤ a := fun a ha => T.min'_le a ha
      -- {a∈B : 0<a≤b} = insert b D1
      have hset : B.filter (fun a => 0 < a ∧ a ≤ b) = insert b D1 := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_insert, hD1]
        constructor
        · rintro ⟨haB, hapos, hab⟩
          by_cases hac : a < c
          · exact Or.inr ⟨haB, hapos, hac⟩
          · left
            by_cases haL : a < L
            · have : a ∈ T := by rw [hT, Finset.mem_filter]; exact ⟨haB, by omega, haL⟩
              have := hbmin a this; omega
            · exfalso; have := hMx a haB; omega
        · rintro (rfl | ⟨haB, hapos, hac⟩)
          · exact ⟨hbB, hbpos, le_refl b⟩
          · exact ⟨haB, hapos, by omega⟩
      have hbnotD1 : b ∉ D1 := by rw [hD1, Finset.mem_filter]; push_neg; intro _ _; omega
      have hcard : (B.filter (fun a => 0 < a ∧ a ≤ b)).card = j + 1 := by
        rw [hset, Finset.card_insert_of_notMem hbnotD1, hj]
      have hcltb : c < b := lt_of_le_of_ne hbge (fun h => hcB (h ▸ hbB))
      have hc1' : b < 2 * (j + 1) := by rw [← hcard]; exact hcase1 b hbB hbpos hblt
      omega
    · -- T empty: all positive elements except L are < c, so j = k-2
      rw [Finset.not_nonempty_iff_eq_empty] at hTne
      have hTe : T = ∅ := hTne
      have hposset : B.filter (fun a => 0 < a) = insert L D1 := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_insert, hD1]
        constructor
        · rintro ⟨haB, hapos⟩
          by_cases hac : a < c
          · exact Or.inr ⟨haB, hapos, hac⟩
          · left
            by_cases haL : a < L
            · exfalso
              have : a ∈ T := by rw [hT, Finset.mem_filter]; exact ⟨haB, by omega, haL⟩
              rw [hTe] at this; exact Finset.notMem_empty a this
            · have := hMx a haB; omega
        · rintro (rfl | ⟨haB, hapos, hac⟩)
          · exact ⟨hLB, by omega⟩
          · exact ⟨haB, hapos⟩
      have hLnotD1 : L ∉ D1 := by rw [hD1, Finset.mem_filter]; push_neg; intro _ _; omega
      have hposcard : (B.filter (fun a => 0 < a)).card = j + 1 := by
        rw [hposset, Finset.card_insert_of_notMem hLnotD1, hj]
      have herase : B.filter (fun a => 0 < a) = B.erase 0 := by
        ext a; simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨haB, hapos⟩; exact ⟨by omega, haB⟩
        · rintro ⟨hane, haB⟩; exact ⟨haB, by omega⟩
      have herasecard : (B.erase 0).card = k - 1 := by
        rw [Finset.card_erase_of_mem h0, hkdef]
      rw [herase, herasecard] at hposcard
      omega
  -- Step 2: fill gives [0, 2k-4] ⊆ B+B
  have hfill := fill B (2 * k - 4) h0 hdens
  -- Step 3: L+B ⊆ B+B, disjoint from [0,2k-4], card k
  set LB := B.image (fun a => L + a) with hLBdef
  have hLBcard : LB.card = k := by
    rw [hLBdef]; exact Finset.card_image_of_injOn (fun a _ b _ h => by omega)
  have hLBsub : LB ⊆ B + B := by
    intro x hx; rw [hLBdef, Finset.mem_image] at hx; obtain ⟨b, hb, rfl⟩ := hx
    exact Finset.add_mem_add hLB hb
  have hIsub : Finset.Icc 0 (2 * k - 4) ⊆ B + B := hfill
  have hIcard : (Finset.Icc 0 (2 * k - 4)).card = 2 * k - 3 := by
    rw [Nat.card_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 0 (2 * k - 4)) LB := by
    rw [Finset.disjoint_left]
    intro x hxI hxLB
    rw [Finset.mem_Icc] at hxI
    rw [hLBdef, Finset.mem_image] at hxLB
    obtain ⟨b, hb, rfl⟩ := hxLB
    omega
  have hunion : (Finset.Icc 0 (2 * k - 4)) ∪ LB ⊆ B + B := Finset.union_subset hIsub hLBsub
  have hcardun : ((Finset.Icc 0 (2 * k - 4)) ∪ LB).card = (2 * k - 3) + k := by
    rw [Finset.card_union_of_disjoint hdisj, hIcard, hLBcard]
  have := Finset.card_le_card hunion
  rw [hcardun] at this
  omega

#print axioms case1_direct

/-- **Reflection preserves sumset cardinality.** For `B ⊆ [0,L]`, the reflected set
`B* = {L - x : x ∈ B}` has `|B*+B*| = |B+B|`, via the bijection `s ↦ 2L - s` on `B+B`.
Reusable for Case 3's `m=1` reflect-and-repeat branch (blueprint §11). -/
lemma reflect_sumset (B : Finset ℕ) (L : ℕ) (hBsub : B ⊆ Finset.Icc 0 L) :
    ((B.image (fun x => L - x)) + (B.image (fun x => L - x))).card = (B + B).card := by
  set Bs := B.image (fun x => L - x) with hBs
  have hMx : ∀ a ∈ B, a ≤ L := fun a ha => by
    have := hBsub ha; rw [Finset.mem_Icc] at this; omega
  have hkey : Bs + Bs = (B + B).image (fun s => 2 * L - s) := by
    ext w
    simp only [Finset.mem_add, Finset.mem_image, hBs]
    constructor
    · rintro ⟨x, ⟨a, haB, rfl⟩, y, ⟨b, hbB, rfl⟩, rfl⟩
      refine ⟨a + b, ⟨a, haB, b, hbB, rfl⟩, ?_⟩
      have := hMx a haB; have := hMx b hbB; omega
    · rintro ⟨s, ⟨a, haB, b, hbB, rfl⟩, rfl⟩
      refine ⟨L - a, ⟨a, haB, rfl⟩, L - b, ⟨b, hbB, rfl⟩, ?_⟩
      have := hMx a haB; have := hMx b hbB; omega
  rw [hkey]
  apply Finset.card_image_of_injOn
  intro s hs t ht hst
  rw [Finset.mem_coe, Finset.mem_add] at hs ht
  obtain ⟨a, haB, b, hbB, rfl⟩ := hs
  obtain ⟨c, hcB, d, hdB, rfl⟩ := ht
  simp only [] at hst
  have := hMx a haB; have := hMx b hbB; have := hMx c hcB; have := hMx d hdB
  omega

/-- The reflected set stays in `[0,L]`, contains `0` and `L`, and has the same cardinality. -/
lemma reflect_basic (B : Finset ℕ) (L : ℕ) (hBsub : B ⊆ Finset.Icc 0 L)
    (h0 : 0 ∈ B) (hLB : L ∈ B) :
    (B.image (fun x => L - x)) ⊆ Finset.Icc 0 L ∧
    0 ∈ (B.image (fun x => L - x)) ∧ L ∈ (B.image (fun x => L - x)) ∧
    (B.image (fun x => L - x)).card = B.card := by
  have hMx : ∀ a ∈ B, a ≤ L := fun a ha => by
    have := hBsub ha; rw [Finset.mem_Icc] at this; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy; rw [Finset.mem_image] at hy; obtain ⟨x, hx, rfl⟩ := hy
    rw [Finset.mem_Icc]; have := hMx x hx; omega
  · rw [Finset.mem_image]; exact ⟨L, hLB, by omega⟩
  · rw [Finset.mem_image]; exact ⟨0, h0, by omega⟩
  · apply Finset.card_image_of_injOn
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    simp only [] at hab
    have := hMx a ha; have := hMx b hb; omega

#print axioms reflect_sumset

/-- **Translation preserves sumset cardinality.** If `c ≤ a` for every `a ∈ A`, the shifted set
`A* = {a - c : a ∈ A}` has `|A*+A*| = |A+A|`, via the bijection `s ↦ s - 2c` on `A+A`. Used to
move `A_2` down to start at `0` before applying the induction hypothesis (Case 2/3). -/
lemma translate_sumset (A : Finset ℕ) (c : ℕ) (hc : ∀ a ∈ A, c ≤ a) :
    ((A.image (fun x => x - c)) + (A.image (fun x => x - c))).card = (A + A).card := by
  set As := A.image (fun x => x - c) with hAs
  have hkey : As + As = (A + A).image (fun s => s - 2 * c) := by
    ext w
    simp only [Finset.mem_add, Finset.mem_image, hAs]
    constructor
    · rintro ⟨x, ⟨a, haA, rfl⟩, y, ⟨b, hbA, rfl⟩, rfl⟩
      refine ⟨a + b, ⟨a, haA, b, hbA, rfl⟩, ?_⟩
      have := hc a haA; have := hc b hbA; omega
    · rintro ⟨s, ⟨a, haA, b, hbA, rfl⟩, rfl⟩
      refine ⟨a - c, ⟨a, haA, rfl⟩, b - c, ⟨b, hbA, rfl⟩, ?_⟩
      have := hc a haA; have := hc b hbA; omega
  rw [hkey]
  apply Finset.card_image_of_injOn
  intro s hs t ht hst
  rw [Finset.mem_coe, Finset.mem_add] at hs ht
  obtain ⟨a, haA, b, hbA, rfl⟩ := hs
  obtain ⟨p, hpA, q, hqA, rfl⟩ := ht
  simp only [] at hst
  have := hc a haA; have := hc b hbA; have := hc p hpA; have := hc q hqA
  omega

/-- A finite set of naturals containing `1` has `gcd = 1`. (The translated `A_2*` contains `0,1`.) -/
lemma gcd_eq_one_of_one_mem (A : Finset ℕ) (h1 : 1 ∈ A) : A.gcd id = 1 :=
  Nat.eq_one_of_dvd_one (Finset.gcd_dvd h1)

#print axioms translate_sumset

/-- **Transition-pair extraction (Case 2, index-free).** When Case 1 fails (`Bad` nonempty) and the
largest non-maximal element is "good" (`amax < 2(k-2)`), the largest bad element `u = max Bad` and
its successor are consecutive integers `u = 2n`, `u+1 = 2n+1` (where `n = #{a∈B:0<a≤u}`), both in
`B`, with `u+1 < L`. This is the sorted `a_{s-1}=2s-2, a_s=2s-1` fact, without the enumeration. -/
lemma transition_pair (B : Finset ℕ) (L : ℕ) (hsub : B ⊆ Finset.Icc 0 L)
    (h0 : 0 ∈ B) (hLB : L ∈ B) (hk : 3 ≤ B.card)
    (hBadne : (B.filter (fun x => 0 < x ∧ x < L ∧
      2 * (B.filter (fun a => 0 < a ∧ a ≤ x)).card ≤ x)).Nonempty)
    (hne_eraseL : (B.erase L).Nonempty)
    (hterm : (B.erase L).max' hne_eraseL < 2 * (B.card - 2)) :
    ∃ u, u ∈ B ∧ (u + 1) ∈ B ∧ 0 < u ∧ u + 1 < L ∧
      2 * (B.filter (fun a => 0 < a ∧ a ≤ u)).card = u := by
  have hMx : ∀ a ∈ B, a ≤ L := fun a ha => by
    have := hsub ha; rw [Finset.mem_Icc] at this; omega
  set Bad := B.filter (fun x => 0 < x ∧ x < L ∧
    2 * (B.filter (fun a => 0 < a ∧ a ≤ x)).card ≤ x) with hBad
  set u := Bad.max' hBadne with hu
  have huBad : u ∈ Bad := Bad.max'_mem _
  rw [hBad, Finset.mem_filter] at huBad
  obtain ⟨huB, hupos, huL, hubadge⟩ := huBad
  set n := (B.filter (fun a => 0 < a ∧ a ≤ u)).card with hn
  have hubadge' : 2 * n ≤ u := hubadge
  have hmaxBad : ∀ x ∈ Bad, x ≤ u := fun x hx => Bad.le_max' x hx
  -- successor y = min of {a∈B : a > u}
  have hSne : (B.filter (fun a => u < a)).Nonempty := ⟨L, by rw [Finset.mem_filter]; exact ⟨hLB, huL⟩⟩
  set y := (B.filter (fun a => u < a)).min' hSne with hy
  have hymem : y ∈ B.filter (fun a => u < a) := (B.filter (fun a => u < a)).min'_mem _
  rw [Finset.mem_filter] at hymem
  have hyB : y ∈ B := hymem.1
  have hyu : u < y := hymem.2
  have hymin : ∀ a ∈ B.filter (fun a => u < a), y ≤ a :=
    fun a ha => (B.filter (fun a => u < a)).min'_le a ha
  -- amax = max(B.erase L), u < amax  (u is bad, amax is good ⇒ u ≠ amax, and u ≤ amax)
  set amax := (B.erase L).max' hne_eraseL with hamax
  have hamaxmem : amax ∈ B.erase L := (B.erase L).max'_mem _
  rw [Finset.mem_erase] at hamaxmem
  have hamaxB : amax ∈ B := hamaxmem.2
  have hamaxneL : amax ≠ L := hamaxmem.1
  have hamaxL : amax < L := lt_of_le_of_ne (hMx amax hamaxB) hamaxneL
  have hule_amax : u ≤ amax := by
    apply (B.erase L).le_max'
    exact Finset.mem_erase.mpr ⟨by omega, huB⟩
  -- #{0<a≤amax} = k-2 : all positive except L
  have hcount_amax : (B.filter (fun a => 0 < a ∧ a ≤ amax)).card = B.card - 2 := by
    have hset : B.filter (fun a => 0 < a ∧ a ≤ amax) = (B.erase 0).erase L := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨haB, hapos, hale⟩
        exact ⟨by omega, by omega, haB⟩
      · rintro ⟨haL, ha0, haB⟩
        refine ⟨haB, by omega, ?_⟩
        -- a ≠ L, a ∈ B ⇒ a ≤ amax
        apply (B.erase L).le_max'
        exact Finset.mem_erase.mpr ⟨haL, haB⟩
    rw [hset]
    have hLe0 : L ∈ B.erase 0 := Finset.mem_erase.mpr ⟨by omega, hLB⟩
    rw [Finset.card_erase_of_mem hLe0, Finset.card_erase_of_mem h0]
    omega
  -- amax good: amax < 2(k-2) = 2·#{0<a≤amax}
  have hamax_good : amax < 2 * (B.filter (fun a => 0 < a ∧ a ≤ amax)).card := by
    rw [hcount_amax]; omega
  -- hence amax ∉ Bad ; combined with u ∈ Bad and u ≤ amax ⇒ u < amax
  have hu_lt_amax : u < amax := by
    rcases lt_or_eq_of_le hule_amax with h | h
    · exact h
    · exfalso
      -- u = amax, but amax good contradicts u bad
      rw [← h] at hamax_good
      omega
  -- y ≤ amax < L
  have hyle_amax : y ≤ amax := hymin amax (by rw [Finset.mem_filter]; exact ⟨hamaxB, hu_lt_amax⟩)
  have hyL : y < L := by omega
  have hypos : 0 < y := by omega
  -- y good (y ∉ Bad since y > u = max Bad, y positive non-max)
  have hy_notBad : y ∉ Bad := by
    intro hyBad
    have := hmaxBad y hyBad; omega
  have hy_good : y < 2 * (B.filter (fun a => 0 < a ∧ a ≤ y)).card := by
    by_contra hcon
    push_neg at hcon
    exact hy_notBad (by rw [hBad, Finset.mem_filter]; exact ⟨hyB, hypos, hyL, hcon⟩)
  -- #{0<a≤y} = n+1 (y is the immediate successor of u)
  have hcount_y : (B.filter (fun a => 0 < a ∧ a ≤ y)).card = n + 1 := by
    have hset : B.filter (fun a => 0 < a ∧ a ≤ y) = insert y (B.filter (fun a => 0 < a ∧ a ≤ u)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨haB, hapos, hay⟩
        by_cases hau : a ≤ u
        · exact Or.inr ⟨haB, hapos, hau⟩
        · -- u < a ≤ y ⇒ a = y (y minimal above u)
          left
          have : a ∈ B.filter (fun a => u < a) := by
            rw [Finset.mem_filter]; exact ⟨haB, by omega⟩
          have := hymin a this; omega
      · rintro (rfl | ⟨haB, hapos, hau⟩)
        · exact ⟨hyB, hypos, le_refl y⟩
        · exact ⟨haB, hapos, by omega⟩
    have hynotin : y ∉ B.filter (fun a => 0 < a ∧ a ≤ u) := by
      rw [Finset.mem_filter]; push_neg; intro _ _; omega
    rw [hset, Finset.card_insert_of_notMem hynotin, hn]
  rw [hcount_y] at hy_good
  -- now: 2n ≤ u < y ≤ 2n+1  ⇒  u = 2n, y = 2n+1
  have huval : u = 2 * n := by omega
  have hyval : y = u + 1 := by omega
  refine ⟨u, huB, ?_, hupos, ?_, ?_⟩
  · rw [← hyval]; exact hyB
  · rw [← hyval]; exact hyL
  · rw [← hn]; omega

#print axioms transition_pair

/-- **Case 2 (transition), given the transition pair `u`.** With `u, u+1 ∈ B` consecutive,
`u = 2·#{a∈B:0<a≤u}`, `u+1 < L`: split `B` into `A_1 = {a≤u+1}` (small diameter, `max = 2|A_1|-3`)
and `A_2 = {a≥u}` (translate to start at 0, apply the induction hypothesis), overlapping in `≤ 3`
sums. Inclusion–exclusion gives `3k-3`. -/
lemma case2_transition (B : Finset ℕ) (L : ℕ) (hsub : B ⊆ Finset.Icc 0 L)
    (h0 : 0 ∈ B) (hLB : L ∈ B) (hk : 3 ≤ B.card) (hL : 2 * B.card - 2 ≤ L)
    (IH : ∀ (B' : Finset ℕ) (L' : ℕ), B'.card < B.card → B' ⊆ Finset.Icc 0 L' → 0 ∈ B' → L' ∈ B' →
      3 ≤ B'.card → B'.gcd id = 1 → 2 * B'.card - 3 ≤ L' → 3 * B'.card - 3 ≤ (B' + B').card)
    (u : ℕ) (huB : u ∈ B) (hu1B : u + 1 ∈ B) (hupos : 0 < u) (hu1L : u + 1 < L)
    (huval : 2 * (B.filter (fun a => 0 < a ∧ a ≤ u)).card = u) :
    3 * B.card - 3 ≤ (B + B).card := by
  set k := B.card with hkdef
  set n := (B.filter (fun a => 0 < a ∧ a ≤ u)).card with hn
  have hu2n : u = 2 * n := by omega
  have hn1 : 1 ≤ n := by omega
  have hMx : ∀ a ∈ B, a ≤ L := fun a ha => by
    have := hsub ha; rw [Finset.mem_Icc] at this; omega
  -- ===== A_1 = {a ∈ B : a ≤ u+1} =====
  set A1 := B.filter (fun a => a ≤ u + 1) with hA1
  have hA1sub : A1 ⊆ Finset.Icc 0 (u + 1) := by
    intro a ha; rw [hA1, Finset.mem_filter] at ha; rw [Finset.mem_Icc]; omega
  have h0A1 : 0 ∈ A1 := by rw [hA1, Finset.mem_filter]; exact ⟨h0, by omega⟩
  have hu1A1 : u + 1 ∈ A1 := by rw [hA1, Finset.mem_filter]; exact ⟨hu1B, le_refl _⟩
  -- |A_1| = n + 2
  have hA1card : A1.card = n + 2 := by
    set pos1 := B.filter (fun a => 0 < a ∧ a ≤ u + 1) with hpos1
    have hA1eq : A1 = insert 0 pos1 := by
      ext a; rw [hA1, hpos1]
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨haB, hau⟩
        rcases Nat.eq_zero_or_pos a with rfl | hpos
        · exact Or.inl rfl
        · exact Or.inr ⟨haB, hpos, hau⟩
      · rintro (rfl | ⟨haB, hpos, hau⟩)
        · exact ⟨h0, by omega⟩
        · exact ⟨haB, hau⟩
    have h0pos1 : 0 ∉ pos1 := by rw [hpos1, Finset.mem_filter]; push_neg; intro _ h; omega
    have hpos1eq : pos1 = insert (u + 1) (B.filter (fun a => 0 < a ∧ a ≤ u)) := by
      ext a; rw [hpos1]
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨haB, hpos, hau⟩
        rcases Nat.lt_or_ge a (u + 1) with hlt | hge
        · exact Or.inr ⟨haB, hpos, by omega⟩
        · exact Or.inl (by omega)
      · rintro (rfl | ⟨haB, hpos, hau⟩)
        · exact ⟨hu1B, by omega, le_refl _⟩
        · exact ⟨haB, hpos, by omega⟩
    have hu1notin : u + 1 ∉ B.filter (fun a => 0 < a ∧ a ≤ u) := by
      rw [Finset.mem_filter]; push_neg; intro _ _; omega
    rw [hA1eq, Finset.card_insert_of_notMem h0pos1, hpos1eq,
      Finset.card_insert_of_notMem hu1notin, ← hn]
  have hA1card2 : 2 ≤ A1.card := by omega
  have hA1Mle : u + 1 ≤ 2 * A1.card - 3 := by omega
  have hA1sd := small_diameter A1 (u + 1) hA1sub h0A1 hu1A1 hA1card2 hA1Mle
  -- |A_1+A_1| ≥ 3n+3
  have hA1sum : 3 * n + 3 ≤ (A1 + A1).card := by rw [hA1card] at hA1sd; omega
  -- ===== A_2 = {a ∈ B : u ≤ a} =====
  set A2 := B.filter (fun a => u ≤ a) with hA2
  have hA2sub : A2 ⊆ B := Finset.filter_subset _ _
  have huA2 : u ∈ A2 := by rw [hA2, Finset.mem_filter]; exact ⟨huB, le_refl _⟩
  have hu1A2 : u + 1 ∈ A2 := by rw [hA2, Finset.mem_filter]; exact ⟨hu1B, by omega⟩
  have hLA2 : L ∈ A2 := by rw [hA2, Finset.mem_filter]; exact ⟨hLB, by omega⟩
  have hA2ge : ∀ a ∈ A2, u ≤ a := fun a ha => by rw [hA2, Finset.mem_filter] at ha; exact ha.2
  -- A_1 ∪ A_2 = B, A_1 ∩ A_2 = {u, u+1}
  have hunionB : A1 ∪ A2 = B := by
    ext a
    rw [hA1, hA2]; simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨haB, _⟩ | ⟨haB, _⟩) <;> exact haB
    · intro haB
      rcases Nat.lt_or_ge a (u + 1) with hlt | hge
      · exact Or.inl ⟨haB, by omega⟩
      · exact Or.inr ⟨haB, by omega⟩
  have hinterB : A1 ∩ A2 = {u, u + 1} := by
    ext a
    rw [hA1, hA2]; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨haB, hle⟩, ⟨_, hge⟩⟩
      -- u ≤ a ≤ u+1
      rcases Nat.lt_or_ge a (u + 1) with hlt | hge2
      · left; omega
      · right; omega
    · rintro (rfl | rfl)
      · exact ⟨⟨huB, by omega⟩, ⟨huB, le_refl _⟩⟩
      · exact ⟨⟨hu1B, le_refl _⟩, ⟨hu1B, by omega⟩⟩
  have hintercard : (A1 ∩ A2).card = 2 := by
    rw [hinterB, Finset.card_pair (by omega : u ≠ u + 1)]
  -- |A_1| + |A_2| = |B| + 2
  have hpartition : A1.card + A2.card = k + 2 := by
    have := Finset.card_union_add_card_inter A1 A2
    rw [hunionB, hintercard, ← hkdef] at this; omega
  have hA2card : A2.card = k - n := by omega
  have hA2ge3 : 3 ≤ A2.card := by
    have hsub3 : ({u, u + 1, L} : Finset ℕ) ⊆ A2 := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      exacts [huA2, hu1A2, hLA2]
    have hc3 : ({u, u + 1, L} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have := Finset.card_le_card hsub3; omega
  -- ===== A_2* = A_2 - u, apply IH =====
  set A2s := A2.image (fun x => x - u) with hA2s
  have h0A2s : 0 ∈ A2s := by rw [hA2s, Finset.mem_image]; exact ⟨u, huA2, by omega⟩
  have h1A2s : 1 ∈ A2s := by rw [hA2s, Finset.mem_image]; exact ⟨u + 1, hu1A2, by omega⟩
  have hLuA2s : L - u ∈ A2s := by rw [hA2s, Finset.mem_image]; exact ⟨L, hLA2, rfl⟩
  have hA2ssub : A2s ⊆ Finset.Icc 0 (L - u) := by
    intro y hy; rw [hA2s, Finset.mem_image] at hy; obtain ⟨a, haA2, rfl⟩ := hy
    rw [Finset.mem_Icc]; have := hA2ge a haA2; have := hMx a (hA2sub haA2); omega
  have hA2scard : A2s.card = A2.card :=
    Finset.card_image_of_injOn (fun a ha b hb hab => by
      rw [Finset.mem_coe] at ha hb
      have := hA2ge a ha; have := hA2ge b hb; omega)
  have hA2sgcd : A2s.gcd id = 1 := gcd_eq_one_of_one_mem A2s h1A2s
  have hA2scard3 : 3 ≤ A2s.card := by rw [hA2scard]; exact hA2ge3
  have hA2scardlt : A2s.card < k := by rw [hA2scard, hA2card]; omega
  have hA2sdiam : 2 * A2s.card - 3 ≤ L - u := by rw [hA2scard, hA2card]; omega
  have hIH := IH A2s (L - u) hA2scardlt hA2ssub h0A2s hLuA2s hA2scard3 hA2sgcd hA2sdiam
  -- translate back: |A_2+A_2| = |A_2*+A_2*|
  have htrans := translate_sumset A2 u hA2ge
  rw [← hA2s] at htrans
  have hA2sum : 3 * (k - n) - 3 ≤ (A2 + A2).card := by
    rw [← htrans]; rw [hA2scard, hA2card] at hIH; exact hIH
  -- ===== overlap ≤ 3 =====
  have hoverlap := two_point_overlap_le A1 A2 u (u + 1) (by omega)
    (fun x hx => by rw [hA1, Finset.mem_filter] at hx; exact hx.2)
    (fun x hx hxu => by rw [hA1, Finset.mem_filter] at hx; omega)
    (fun x hx => hA2ge x hx)
    (fun x hx hxv => by have := hA2ge x hx; omega)
  -- ===== assembly =====
  have hA1A1sub : A1 + A1 ⊆ B + B := by
    intro x hx; rw [Finset.mem_add] at hx ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨a, (Finset.filter_subset _ _) ha, b, (Finset.filter_subset _ _) hb, rfl⟩
  have hA2A2sub : A2 + A2 ⊆ B + B := by
    intro x hx; rw [Finset.mem_add] at hx ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨a, hA2sub ha, b, hA2sub hb, rfl⟩
  have hunionsub : (A1 + A1) ∪ (A2 + A2) ⊆ B + B := Finset.union_subset hA1A1sub hA2A2sub
  have hie := Finset.card_union_add_card_inter (A1 + A1) (A2 + A2)
  have hbb := Finset.card_le_card hunionsub
  omega

#print axioms case2_transition

/-- **Second-largest structure of a sumset.** If `p` is the max of `X'` and `q` the second-largest
(every element `≠ p` is `≤ q`), then every sum `z ∈ X'+X'` is `≤ 2p`, and the only sums exceeding
`p+q` equal the maximum `2p`. Foundation for Case 3 (the three new terminal sums `M+q<M+p<2M`). -/
lemma sumset_second_max (X' : Finset ℕ) (p q : ℕ) (hp : p ∈ X') (hpmax : ∀ a ∈ X', a ≤ p)
    (hqlt : q < p) (hqmax : ∀ a ∈ X', a ≠ p → a ≤ q) :
    ∀ z ∈ X' + X', z ≤ 2 * p ∧ (p + q < z → z = 2 * p) := by
  intro z hz
  rw [Finset.mem_add] at hz
  obtain ⟨s, hs, t, ht, rfl⟩ := hz
  have hsp := hpmax s hs
  have htp := hpmax t ht
  refine ⟨by omega, fun hgt => ?_⟩
  by_cases hseq : s = p
  · by_cases hteq : t = p
    · omega
    · have := hqmax t ht hteq; omega
  · by_cases hteq : t = p
    · have := hqmax s hs hseq; omega
    · have := hqmax s hs hseq; have := hqmax t ht hteq; omega

#print axioms sumset_second_max

/-- Extraction of the top two elements below `M`. For `X` with `0, M ∈ X`, `|X| ≥ 3`, the erased set
`X' = X.erase M` has a maximum `p` and a distinct second element `q < p` dominating the rest. -/
lemma top_two (X : Finset ℕ) (M : ℕ) (h0 : 0 ∈ X) (hM : M ∈ X) (hk : 3 ≤ X.card)
    (hMmax : ∀ a ∈ X, a ≤ M) (h0M : 0 < M) :
    ∃ p q, p ∈ X ∧ q ∈ X ∧ p ≠ M ∧ q ≠ M ∧ q < p ∧ p < M ∧
      (∀ a ∈ X, a ≠ M → a ≤ p) ∧ (∀ a ∈ X, a ≠ M → a ≠ p → a ≤ q) := by
  set X' := X.erase M with hX'
  have hX'card : X'.card = X.card - 1 := by rw [hX', Finset.card_erase_of_mem hM]
  have hX'ne : X'.Nonempty := Finset.card_pos.mp (by rw [hX'card]; omega)
  set p := X'.max' hX'ne with hp
  have hpX' : p ∈ X' := X'.max'_mem _
  have hpX : p ∈ X := Finset.mem_of_mem_erase hpX'
  have hpneM : p ≠ M := (Finset.mem_erase.mp hpX').1
  have hpmax : ∀ a ∈ X', a ≤ p := fun a ha => X'.le_max' a ha
  have hplt : p < M := lt_of_le_of_ne (hMmax p hpX) hpneM
  -- second: erase p too
  set X'' := X'.erase p with hX''
  have hX''card : X''.card = X.card - 2 := by
    rw [hX'', Finset.card_erase_of_mem hpX', hX'card]; omega
  have hX''ne : X''.Nonempty := Finset.card_pos.mp (by rw [hX''card]; omega)
  set q := X''.max' hX''ne with hq
  have hqX'' : q ∈ X'' := X''.max'_mem _
  have hqX' : q ∈ X' := Finset.mem_of_mem_erase hqX''
  have hqX : q ∈ X := Finset.mem_of_mem_erase hqX'
  have hqneM : q ≠ M := (Finset.mem_erase.mp hqX').1
  have hqnep : q ≠ p := (Finset.mem_erase.mp hqX'').1
  have hqlep : q ≤ p := hpmax q hqX'
  have hqlt : q < p := lt_of_le_of_ne hqlep hqnep
  have hqmax : ∀ a ∈ X'', a ≤ q := fun a ha => X''.le_max' a ha
  refine ⟨p, q, hpX, hqX, hpneM, hqneM, hqlt, hplt, ?_, ?_⟩
  · intro a haX haM
    exact hpmax a (Finset.mem_erase.mpr ⟨haM, haX⟩)
  · intro a haX haM hap
    exact hqmax a (Finset.mem_erase.mpr ⟨hap, Finset.mem_erase.mpr ⟨haM, haX⟩⟩)

#print axioms top_two

/-- **Terminal case, non-corner (Subcase 3A + 3B(i) modular escape).** For terminal `X` (with top
two `p > q` below `M`, `gcd = 1`), unless the top three are exactly `{M-2, M-1, M}`, there are three
new sums `M+w' < M+p < 2M` outside `A'+A'` (`A' = X.erase M`). With the induction bound
`3k-6 ≤ |A'+A'|` this gives `3k-3`. The third sum `M+w'` is `M+q` when `M+q ≠ 2p` (3A), else the
modular-escape witness `w = max{a : m ∤ (M-a)}` where `m = M-p ≥ 2` (3B(i)). -/
lemma terminal_nonAP1 (X : Finset ℕ) (M p q : ℕ)
    (hXsub : X ⊆ Finset.Icc 0 M) (hM : M ∈ X) (h0 : 0 ∈ X) (hgcd : X.gcd id = 1)
    (hpX : p ∈ X) (hqX : q ∈ X) (hpM : p < M) (hqp : q < p)
    (hpmax : ∀ a ∈ X, a ≠ M → a ≤ p)
    (hqmax : ∀ a ∈ X, a ≠ M → a ≠ p → a ≤ q)
    (hncorner : ¬ (p = M - 1 ∧ q = M - 2))
    (hbound : 3 * X.card - 6 ≤ ((X.erase M) + (X.erase M)).card) :
    3 * X.card - 3 ≤ (X + X).card := by
  set A' := X.erase M with hA'
  have hpA' : p ∈ A' := Finset.mem_erase.mpr ⟨by omega, hpX⟩
  have hpmax' : ∀ a ∈ A', a ≤ p := by
    intro a ha; rw [hA', Finset.mem_erase] at ha; exact hpmax a ha.2 ha.1
  have hqmax' : ∀ a ∈ A', a ≠ p → a ≤ q := by
    intro a ha hap; rw [hA', Finset.mem_erase] at ha; exact hqmax a ha.2 ha.1 hap
  have hpsum := sumset_second_max A' p q hpA' hpmax' hqp hqmax'
  have hMx : ∀ a ∈ X, a ≤ M := fun a ha => by
    have := hXsub ha; rw [Finset.mem_Icc] at this; omega
  -- find w' : w' ∈ X, w' < p, M + w' ∉ A'+A'
  obtain ⟨w', hw'X, hw'p, hw'not⟩ : ∃ w', w' ∈ X ∧ w' < p ∧ M + w' ∉ A' + A' := by
    by_cases hMq : M + q = 2 * p
    · -- 3B: modular escape, m = M - p ≥ 2
      have hm2 : 2 ≤ M - p := by
        rcases Nat.lt_or_ge (M - p) 2 with h | h
        · exfalso; apply hncorner
          have hpM1 : p = M - 1 := by omega
          refine ⟨hpM1, ?_⟩; omega
        · exact h
      set m := M - p with hmdef
      -- not all a ≡ M (mod m)
      have hnotall : ∃ a ∈ X, ¬ (m ∣ (M - a)) := by
        by_contra hcon; push_neg at hcon
        have hmM : m ∣ M := by have := hcon 0 h0; simpa using this
        have hmall : ∀ a ∈ X, m ∣ a := by
          intro a ha
          have h1 := hcon a ha
          have h2 : a = M - (M - a) := by have := hMx a ha; omega
          rw [h2]; exact Nat.dvd_sub hmM h1
        have hmg : m ∣ X.gcd id := Finset.dvd_gcd (fun a ha => hmall a ha)
        rw [hgcd] at hmg
        have := Nat.le_of_dvd Nat.one_pos hmg; omega
      -- w = max of {a ∈ X : ¬ m ∣ (M-a)}
      set W := X.filter (fun a => ¬ (m ∣ (M - a))) with hW
      have hWne : W.Nonempty := by
        obtain ⟨a, haX, ha⟩ := hnotall; exact ⟨a, by rw [hW, Finset.mem_filter]; exact ⟨haX, ha⟩⟩
      set w := W.max' hWne with hw
      have hwW : w ∈ W := W.max'_mem _
      rw [hW, Finset.mem_filter] at hwW
      have hwX : w ∈ X := hwW.1
      have hwndvd : ¬ (m ∣ (M - w)) := hwW.2
      have hwmax : ∀ a ∈ W, a ≤ w := fun a ha => W.le_max' a ha
      have hwneM : w ≠ M := by intro h; apply hwndvd; rw [h]; simp
      have hwlep : w ≤ p := hpmax w hwX hwneM
      have hwnep : w ≠ p := by
        intro h; apply hwndvd; rw [h]
      have hwltp : w < p := lt_of_le_of_ne hwlep hwnep
      refine ⟨w, hwX, hwltp, ?_⟩
      intro hin
      rw [Finset.mem_add] at hin
      obtain ⟨s, hs, t, ht, hst⟩ := hin
      have hsX : s ∈ X := Finset.mem_of_mem_erase hs
      have htX : t ∈ X := Finset.mem_of_mem_erase ht
      have hsp := hpmax' s hs
      have htp := hpmax' t ht
      -- if s > w and t > w then both ≡ M mod m
      by_cases hsw : w < s
      · by_cases htw : w < t
        · -- both > w ⇒ ≡ M mod m ⇒ contradiction
          have hsdvd : m ∣ (M - s) := by
            by_contra hc
            have : s ∈ W := by rw [hW, Finset.mem_filter]; exact ⟨hsX, hc⟩
            have := hwmax s this; omega
          have htdvd : m ∣ (M - t) := by
            by_contra hc
            have : t ∈ W := by rw [hW, Finset.mem_filter]; exact ⟨htX, hc⟩
            have := hwmax t this; omega
          have hsum : m ∣ ((M - s) + (M - t)) := dvd_add hsdvd htdvd
          have hsM := hMx s hsX; have htM := hMx t htX
          have heq : (M - s) + (M - t) = M - w := by omega
          rw [heq] at hsum
          exact hwndvd hsum
        · -- t ≤ w ⇒ s+t ≤ p + w < M + w
          push_neg at htw; omega
      · push_neg at hsw; omega
    · -- 3A: M + q ∉ A'+A'
      refine ⟨q, hqX, hqp, ?_⟩
      intro hin
      have := (hpsum (M + q) hin).2 (by omega)
      omega
  -- ===== counting: three new sums =====
  set T := ({M + w', M + p, 2 * M} : Finset ℕ) with hT
  have hTsub : T ⊆ X + X := by
    intro x hx; rw [hT] at hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.add_mem_add hM hw'X
    · exact Finset.add_mem_add hM hpX
    · rw [show 2 * M = M + M by ring]; exact Finset.add_mem_add hM hM
  have hA'sub : A' + A' ⊆ X + X := by
    intro x hx; rw [Finset.mem_add] at hx ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨a, Finset.mem_of_mem_erase ha, b, Finset.mem_of_mem_erase hb, rfl⟩
  have hTdisj : Disjoint (A' + A') T := by
    rw [Finset.disjoint_right]
    intro x hx hxA'
    rw [hT] at hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hle := (hpsum x hxA').1
    rcases hx with rfl | rfl | rfl
    · exact hw'not hxA'
    · omega
    · omega
  have hTcard : T.card = 3 := by
    rw [hT, Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  have hunion : (A' + A') ∪ T ⊆ X + X := Finset.union_subset hA'sub hTsub
  have hcardun : ((A' + A') ∪ T).card = (A' + A').card + 3 := by
    rw [Finset.card_union_of_disjoint hTdisj, hTcard]
  have := Finset.card_le_card hunion
  rw [hcardun] at this
  omega

#print axioms terminal_nonAP1

/-- **Consecutive split (shared core of Case 2 and §12).** Given two adjacent elements `x < v` of
`X` (nothing of `X` strictly between), split `X` into `A_1 = {a ≤ v}` and `A_2 = {x ≤ a}`; they
cover `X`, overlap exactly in `{x,v}`, and their sumsets overlap in `≤ 3` elements. If both halves
satisfy `3k_i-3 ≤ |A_i+A_i|`, inclusion–exclusion (`k_1+k_2 = k+2`) gives `3k-3 ≤ |X+X|`. -/
lemma consecutive_split (X : Finset ℕ) (x v : ℕ)
    (hxX : x ∈ X) (hvX : v ∈ X) (hxv : x < v)
    (hadj : ∀ a ∈ X, x < a → v ≤ a)
    (hA1 : 3 * (X.filter (fun a => a ≤ v)).card - 3 ≤
      ((X.filter (fun a => a ≤ v)) + (X.filter (fun a => a ≤ v))).card)
    (hA2 : 3 * (X.filter (fun a => x ≤ a)).card - 3 ≤
      ((X.filter (fun a => x ≤ a)) + (X.filter (fun a => x ≤ a))).card) :
    3 * X.card - 3 ≤ (X + X).card := by
  set A1 := X.filter (fun a => a ≤ v) with hA1def
  set A2 := X.filter (fun a => x ≤ a) with hA2def
  have hA1sub : A1 ⊆ X := Finset.filter_subset _ _
  have hA2sub : A2 ⊆ X := Finset.filter_subset _ _
  -- cover + overlap
  have hunionX : A1 ∪ A2 = X := by
    ext a
    rw [hA1def, hA2def]; simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨haX, _⟩ | ⟨haX, _⟩) <;> exact haX
    · intro haX
      rcases le_or_gt a v with hle | hgt
      · exact Or.inl ⟨haX, hle⟩
      · exact Or.inr ⟨haX, by omega⟩
  have hinter : A1 ∩ A2 = {x, v} := by
    ext a
    rw [hA1def, hA2def]; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨haX, hav⟩, ⟨_, hxa⟩⟩
      -- x ≤ a ≤ v, a ∈ X, adjacency ⇒ a = x or a = v
      rcases Nat.eq_or_lt_of_le hxa with h | h
      · exact Or.inl h.symm
      · have := hadj a haX h; right; omega
    · rintro (rfl | rfl)
      · exact ⟨⟨hxX, by omega⟩, ⟨hxX, le_refl _⟩⟩
      · exact ⟨⟨hvX, le_refl _⟩, ⟨hvX, by omega⟩⟩
  have hintercard : (A1 ∩ A2).card = 2 := by
    rw [hinter, Finset.card_pair (by omega : x ≠ v)]
  have hpartition : A1.card + A2.card = X.card + 2 := by
    have := Finset.card_union_add_card_inter A1 A2
    rw [hunionX, hintercard] at this; omega
  -- sumset overlap ≤ 3
  have hoverlap := two_point_overlap_le A1 A2 x v hxv
    (fun a ha => by rw [hA1def, Finset.mem_filter] at ha; exact ha.2)
    (fun a ha hxa => by
      rw [hA1def, Finset.mem_filter] at ha; exact hadj a ha.1 hxa)
    (fun a ha => by rw [hA2def, Finset.mem_filter] at ha; exact ha.2)
    (fun a ha hav => by
      rw [hA2def, Finset.mem_filter] at ha
      rcases Nat.lt_or_ge x a with h | h
      · have := hadj a ha.1 h; omega
      · omega)
  -- assembly
  have hA1A1sub : A1 + A1 ⊆ X + X := by
    intro z hz; rw [Finset.mem_add] at hz ⊢; obtain ⟨a, ha, b, hb, rfl⟩ := hz
    exact ⟨a, hA1sub ha, b, hA1sub hb, rfl⟩
  have hA2A2sub : A2 + A2 ⊆ X + X := by
    intro z hz; rw [Finset.mem_add] at hz ⊢; obtain ⟨a, ha, b, hb, rfl⟩ := hz
    exact ⟨a, hA2sub ha, b, hA2sub hb, rfl⟩
  have hunionsub : (A1 + A1) ∪ (A2 + A2) ⊆ X + X := Finset.union_subset hA1A1sub hA2A2sub
  have hie := Finset.card_union_add_card_inter (A1 + A1) (A2 + A2)
  have hbb := Finset.card_le_card hunionsub
  omega

#print axioms consecutive_split

lemma gcd_eq_one_of_consec (A : Finset ℕ) (c : ℕ) (hc : c ∈ A) (hc1 : c + 1 ∈ A) :
    A.gcd id = 1 := by
  have hd1 : A.gcd id ∣ c := Finset.gcd_dvd hc
  have hd2 : A.gcd id ∣ (c + 1) := Finset.gcd_dvd hc1
  have : A.gcd id ∣ 1 := by
    have := Nat.dvd_sub hd2 hd1; simpa using this
  exact Nat.eq_one_of_dvd_one this

/-- **§12 double-ended final split.** The last unresolved configuration: `{0,1,2} ⊆ X` and
`{M-2,M-1,M} ⊆ X`, `k ≥ 6`. Split at the first "bad" element `v = min{a : a ≥ 2·#{0<b≤a}}` (index
`ℓ ∈ [3,k-3]`) and its predecessor `x`. Both halves get `gcd = 1` (left from `1`, right from the
consecutive top `M-2,M-1,M`) and diameter `≥ 2kᵢ-3`, so the induction hypothesis bounds both;
`consecutive_split` finishes. -/
lemma double_ended_split (X : Finset ℕ) (M : ℕ) (hXsub : X ⊆ Finset.Icc 0 M)
    (h0 : 0 ∈ X) (hM : M ∈ X) (hk6 : 6 ≤ X.card) (hMlo : 2 * X.card - 2 ≤ M)
    (IH : ∀ (B' : Finset ℕ) (L' : ℕ), B'.card < X.card → B' ⊆ Finset.Icc 0 L' → 0 ∈ B' → L' ∈ B' →
      3 ≤ B'.card → B'.gcd id = 1 → 2 * B'.card - 3 ≤ L' → 3 * B'.card - 3 ≤ (B' + B').card)
    (h1 : 1 ∈ X) (h2 : 2 ∈ X) (hM1 : M - 1 ∈ X) (hM2 : M - 2 ∈ X) :
    3 * X.card - 3 ≤ (X + X).card := by
  set k := X.card with hkdef
  have hMx : ∀ a ∈ X, a ≤ M := fun a ha => by
    have := hXsub ha; rw [Finset.mem_Icc] at this; omega
  have hMbig : 10 ≤ M := by omega
  -- count of positive elements ≤ M-2 is k-3 (only M-1,M lie above)
  have hposcount_M2 : (X.filter (fun b => 0 < b ∧ b ≤ M - 2)).card = k - 3 := by
    have hset : X.filter (fun b => 0 < b ∧ b ≤ M - 2) = ((X.erase 0).erase M).erase (M - 1) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨haX, hapos, hale⟩
        exact ⟨by omega, by omega, by omega, haX⟩
      · rintro ⟨haM1, haM, ha0, haX⟩
        exact ⟨haX, by omega, by
          -- a ∈ X, a ≠ 0, a ≠ M, a ≠ M-1 ⇒ a ≤ M-2
          have := hMx a haX; omega⟩
    rw [hset]
    rw [Finset.card_erase_of_mem (by
        rw [Finset.mem_erase, Finset.mem_erase]; exact ⟨by omega, by omega, hM1⟩),
      Finset.card_erase_of_mem (by rw [Finset.mem_erase]; exact ⟨by omega, hM⟩),
      Finset.card_erase_of_mem h0]
    omega
  -- Bad set (index ≥ 1 by good 1,2); nonempty because M-2 is bad
  set Bad := X.filter (fun a => 0 < a ∧ a < M ∧
    2 * (X.filter (fun b => 0 < b ∧ b ≤ a)).card ≤ a) with hBad
  have hM2bad : M - 2 ∈ Bad := by
    rw [hBad, Finset.mem_filter]
    refine ⟨hM2, by omega, by omega, ?_⟩
    rw [hposcount_M2]; omega
  have hBadne : Bad.Nonempty := ⟨M - 2, hM2bad⟩
  set v := Bad.min' hBadne with hv
  have hvBad : v ∈ Bad := Bad.min'_mem _
  rw [hBad, Finset.mem_filter] at hvBad
  obtain ⟨hvX, hvpos, hvM, hvge⟩ := hvBad
  set ℓ := (X.filter (fun b => 0 < b ∧ b ≤ v)).card with hℓ
  have hvge' : 2 * ℓ ≤ v := hvge
  have hminBad : ∀ a ∈ Bad, v ≤ a := fun a ha => Bad.min'_le a ha
  have hvleM2 : v ≤ M - 2 := hminBad (M - 2) hM2bad
  -- good below v : for a ∈ X, 0<a<v ⇒ a < 2·#{0<b≤a}
  have hgood : ∀ a ∈ X, 0 < a → a < v → a < 2 * (X.filter (fun b => 0 < b ∧ b ≤ a)).card := by
    intro a haX hapos haltv
    by_contra hcon; push_neg at hcon
    have : a ∈ Bad := by
      rw [hBad, Finset.mem_filter]; exact ⟨haX, hapos, by omega, hcon⟩
    have := hminBad a this; omega
  -- 1,2 are good and below v ⇒ v ≥ 3, and ℓ ≥ 3
  have hv3 : 3 ≤ v := by
    by_contra hcon; push_neg at hcon
    have h1in : (1 : ℕ) ∈ X.filter (fun b => 0 < b ∧ b ≤ v) := by
      rw [Finset.mem_filter]; exact ⟨h1, by omega, by omega⟩
    have hge1 : 1 ≤ ℓ := by rw [hℓ]; exact Finset.card_pos.mpr ⟨1, h1in⟩
    by_cases hv2 : v = 2
    · have h2in : (2 : ℕ) ∈ X.filter (fun b => 0 < b ∧ b ≤ v) := by
        rw [Finset.mem_filter]; exact ⟨h2, by omega, by omega⟩
      have hsub2 : ({1, 2} : Finset ℕ) ⊆ X.filter (fun b => 0 < b ∧ b ≤ v) := by
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        exacts [h1in, h2in]
      have hle := Finset.card_le_card hsub2
      rw [Finset.card_pair (by omega : (1:ℕ) ≠ 2), ← hℓ] at hle
      omega
    · omega
  -- ℓ ≥ 3 : {1,2,v} ⊆ {0<b≤v}
  have hℓ3 : 3 ≤ ℓ := by
    have hsub3 : ({1, 2, v} : Finset ℕ) ⊆ X.filter (fun b => 0 < b ∧ b ≤ v) := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · rw [Finset.mem_filter]; exact ⟨h1, by omega, by omega⟩
      · rw [Finset.mem_filter]; exact ⟨h2, by omega, by omega⟩
      · rw [Finset.mem_filter]; exact ⟨hvX, by omega, by omega⟩
    have hc3 : ({1, 2, v} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have := Finset.card_le_card hsub3; rw [hℓ] ; omega
  -- ℓ ≤ k-3 : {0<b≤v} ⊆ {0<b≤M-2}
  have hℓub : ℓ ≤ k - 3 := by
    have hmono : X.filter (fun b => 0 < b ∧ b ≤ v) ⊆ X.filter (fun b => 0 < b ∧ b ≤ M - 2) := by
      intro a ha; rw [Finset.mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.1, by omega⟩
    have := Finset.card_le_card hmono
    rw [← hℓ, hposcount_M2] at this; omega
  -- predecessor x = max{a ∈ X : a < v}
  have hPne : (X.filter (fun a => a < v)).Nonempty := ⟨0, by rw [Finset.mem_filter]; exact ⟨h0, by omega⟩⟩
  set x := (X.filter (fun a => a < v)).max' hPne with hx
  have hxmem : x ∈ X.filter (fun a => a < v) := (X.filter (fun a => a < v)).max'_mem _
  rw [Finset.mem_filter] at hxmem
  have hxX : x ∈ X := hxmem.1
  have hxv : x < v := hxmem.2
  have hxmax : ∀ a ∈ X.filter (fun a => a < v), a ≤ x :=
    fun a ha => (X.filter (fun a => a < v)).le_max' a ha
  have hadj : ∀ a ∈ X, x < a → v ≤ a := by
    intro a haX hxa
    by_contra hcon; push_neg at hcon
    have : a ∈ X.filter (fun a => a < v) := by rw [Finset.mem_filter]; exact ⟨haX, hcon⟩
    have := hxmax a this; omega
  -- x ≥ 2 (2 is < v, so 2 ≤ x); and #{0<b≤x} = ℓ-1
  have hx2 : 2 ≤ x := hxmax 2 (by rw [Finset.mem_filter]; exact ⟨h2, by omega⟩)
  -- ===== Left half A1 = filter(·≤v), apply IH =====
  set A1 := X.filter (fun a => a ≤ v) with hA1def
  have hA1card : A1.card = ℓ + 1 := by
    have hins : A1 = insert 0 (X.filter (fun b => 0 < b ∧ b ≤ v)) := by
      ext a; rw [hA1def]; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨haX, hav⟩
        rcases Nat.eq_zero_or_pos a with rfl | hpos
        · exact Or.inl rfl
        · exact Or.inr ⟨haX, hpos, hav⟩
      · rintro (rfl | ⟨haX, hpos, hav⟩)
        · exact ⟨h0, by omega⟩
        · exact ⟨haX, hav⟩
    have h0notin : 0 ∉ X.filter (fun b => 0 < b ∧ b ≤ v) := by
      rw [Finset.mem_filter]; push_neg; intro _ h; omega
    rw [hins, Finset.card_insert_of_notMem h0notin, ← hℓ]
  have hA1sub : A1 ⊆ Finset.Icc 0 v := by
    intro a ha; rw [hA1def, Finset.mem_filter] at ha; rw [Finset.mem_Icc]; omega
  have h0A1 : 0 ∈ A1 := by rw [hA1def, Finset.mem_filter]; exact ⟨h0, by omega⟩
  have hvA1 : v ∈ A1 := by rw [hA1def, Finset.mem_filter]; exact ⟨hvX, le_refl _⟩
  have hA1gcd : A1.gcd id = 1 := by
    have h1A1 : (1:ℕ) ∈ A1 := by rw [hA1def, Finset.mem_filter]; exact ⟨h1, by omega⟩
    exact Nat.eq_one_of_dvd_one (Finset.gcd_dvd h1A1)
  have hA1cardlt : A1.card < k := by rw [hA1card]; omega
  have hA1card3 : 3 ≤ A1.card := by rw [hA1card]; omega
  have hA1diam : 2 * A1.card - 3 ≤ v := by rw [hA1card]; omega
  have hIH1 := IH A1 v hA1cardlt hA1sub h0A1 hvA1 hA1card3 hA1gcd hA1diam
  -- ===== Right half A2 = filter(x≤·) =====
  set A2 := X.filter (fun a => x ≤ a) with hA2def
  have hA2sub : A2 ⊆ X := Finset.filter_subset _ _
  have hxA2 : x ∈ A2 := by rw [hA2def, Finset.mem_filter]; exact ⟨hxX, le_refl _⟩
  have hMA2 : M ∈ A2 := by rw [hA2def, Finset.mem_filter]; exact ⟨hM, by omega⟩
  have hM1A2 : M - 1 ∈ A2 := by rw [hA2def, Finset.mem_filter]; exact ⟨hM1, by omega⟩
  have hA2ge : ∀ a ∈ A2, x ≤ a := fun a ha => by rw [hA2def, Finset.mem_filter] at ha; exact ha.2
  -- |A1|+|A2| = k+2 (union X, inter {x,v})
  have hunionX : A1 ∪ A2 = X := by
    ext a; rw [hA1def, hA2def]; simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨haX, _⟩ | ⟨haX, _⟩) <;> exact haX
    · intro haX
      rcases le_or_gt a v with hle | hgt
      · exact Or.inl ⟨haX, hle⟩
      · exact Or.inr ⟨haX, by have := hadj a haX (by omega); omega⟩
  have hinterX : A1 ∩ A2 = {x, v} := by
    ext a; rw [hA1def, hA2def]; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨haX, hav⟩, ⟨_, hxa⟩⟩
      rcases Nat.eq_or_lt_of_le hxa with h | h
      · exact Or.inl h.symm
      · have := hadj a haX h; right; omega
    · rintro (rfl | rfl)
      · exact ⟨⟨hxX, by omega⟩, ⟨hxX, le_refl _⟩⟩
      · exact ⟨⟨hvX, le_refl _⟩, ⟨hvX, by omega⟩⟩
  have hpart : A1.card + A2.card = k + 2 := by
    have := Finset.card_union_add_card_inter A1 A2
    rw [hunionX, hinterX, Finset.card_pair (by omega : x ≠ v)] at this; omega
  have hA2card : A2.card = k - ℓ + 1 := by omega
  -- A2* = A2 - x, apply IH
  set A2s := A2.image (fun a => a - x) with hA2s
  have h0A2s : 0 ∈ A2s := by rw [hA2s, Finset.mem_image]; exact ⟨x, hxA2, by omega⟩
  have hMxA2s : M - x ∈ A2s := by rw [hA2s, Finset.mem_image]; exact ⟨M, hMA2, rfl⟩
  have hM1xA2s : M - 1 - x ∈ A2s := by rw [hA2s, Finset.mem_image]; exact ⟨M - 1, hM1A2, by omega⟩
  have hA2ssub : A2s ⊆ Finset.Icc 0 (M - x) := by
    intro y hy; rw [hA2s, Finset.mem_image] at hy; obtain ⟨a, haA2, rfl⟩ := hy
    rw [Finset.mem_Icc]; have := hA2ge a haA2; have := hMx a (hA2sub haA2); omega
  have hA2scard : A2s.card = A2.card :=
    Finset.card_image_of_injOn (fun a ha b hb hab => by
      rw [Finset.mem_coe] at ha hb; have := hA2ge a ha; have := hA2ge b hb; omega)
  have hA2sgcd : A2s.gcd id = 1 := by
    have hcons : M - 1 - x + 1 = M - x := by omega
    exact gcd_eq_one_of_consec A2s (M - 1 - x) hM1xA2s (by rw [hcons]; exact hMxA2s)
  have hA2scardlt : A2s.card < k := by rw [hA2scard, hA2card]; omega
  have hA2scard3 : 3 ≤ A2s.card := by rw [hA2scard, hA2card]; omega
  -- max(A2*) = M - x ≥ 2|A2*|-3 : uses x ≤ 2ℓ-3 (x good, #{0<b≤x} = ℓ-1)
  have hxcount : (X.filter (fun b => 0 < b ∧ b ≤ x)).card = ℓ - 1 := by
    -- {0<b≤v} = insert v {0<b≤x} (v is the successor of x; nothing between x and v)
    have hins : X.filter (fun b => 0 < b ∧ b ≤ v) = insert v (X.filter (fun b => 0 < b ∧ b ≤ x)) := by
      ext a; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨haX, hapos, hav⟩
        rcases le_or_gt a x with hle | hgt
        · exact Or.inr ⟨haX, hapos, hle⟩
        · left; have := hadj a haX hgt; omega
      · rintro (rfl | ⟨haX, hapos, hax⟩)
        · exact ⟨hvX, by omega, le_refl _⟩
        · exact ⟨haX, hapos, by omega⟩
    have hvnotin : v ∉ X.filter (fun b => 0 < b ∧ b ≤ x) := by
      rw [Finset.mem_filter]; push_neg; intro _ _; omega
    rw [hℓ, hins, Finset.card_insert_of_notMem hvnotin]; omega
  have hxgood : x < 2 * (ℓ - 1) := by
    have := hgood x hxX (by omega) hxv
    rw [hxcount] at this; omega
  have hA2sdiam : 2 * A2s.card - 3 ≤ M - x := by
    rw [hA2scard, hA2card]; omega
  have hIH2 := IH A2s (M - x) hA2scardlt hA2ssub h0A2s hMxA2s hA2scard3 hA2sgcd hA2sdiam
  have htrans := translate_sumset A2 x hA2ge
  rw [← hA2s] at htrans
  -- assemble the two filter-form bounds for consecutive_split
  have hbA1 : 3 * A1.card - 3 ≤ (A1 + A1).card := hIH1
  have hbA2 : 3 * A2.card - 3 ≤ (A2 + A2).card := by
    rw [← htrans]; rw [hA2scard] at hIH2; exact hIH2
  exact consecutive_split X x v hxX hvX hxv hadj (by rw [← hA1def]; exact hbA1)
    (by rw [← hA2def]; exact hbA2)

#print axioms double_ended_split

/-- **d = 1, non-terminal ⟹ Case 1 or Case 2.** When the largest non-maximal element is "good"
(`amax < 2(k-2)`), either every positive non-max element is good (Case 1, `case1_direct`) or the
transition pair exists (Case 2, `transition_pair` + `case2_transition`). No `gcd` needed. -/
lemma d1_nonterminal (X : Finset ℕ) (M : ℕ) (hsub : X ⊆ Finset.Icc 0 M)
    (h0 : 0 ∈ X) (hM : M ∈ X) (hk3 : 3 ≤ X.card) (hMlo : 2 * X.card - 2 ≤ M)
    (IH : ∀ (B' : Finset ℕ) (L' : ℕ), B'.card < X.card → B' ⊆ Finset.Icc 0 L' → 0 ∈ B' → L' ∈ B' →
      3 ≤ B'.card → B'.gcd id = 1 → 2 * B'.card - 3 ≤ L' → 3 * B'.card - 3 ≤ (B' + B').card)
    (hne : (X.erase M).Nonempty)
    (hnonterm : (X.erase M).max' hne < 2 * (X.card - 2)) :
    3 * X.card - 3 ≤ (X + X).card := by
  by_cases hcase1 : ∀ y ∈ X, 0 < y → y < M →
      y < 2 * (X.filter (fun a => 0 < a ∧ a ≤ y)).card
  · exact case1_direct X M hsub h0 hM hk3 hMlo hcase1
  · push_neg at hcase1
    obtain ⟨y0, hy0X, hy0pos, hy0M, hy0ge⟩ := hcase1
    have hBadne : (X.filter (fun x => 0 < x ∧ x < M ∧
        2 * (X.filter (fun a => 0 < a ∧ a ≤ x)).card ≤ x)).Nonempty :=
      ⟨y0, by rw [Finset.mem_filter]; exact ⟨hy0X, hy0pos, hy0M, hy0ge⟩⟩
    obtain ⟨u, huX, hu1X, hupos, hu1M, huval⟩ :=
      transition_pair X M hsub h0 hM hk3 hBadne hne hnonterm
    exact case2_transition X M hsub h0 hM hk3 hMlo IH u huX hu1X hupos hu1M huval

#print axioms d1_nonterminal

/-- **Terminal bound (wraps `terminal_nonAP1`).** For terminal `Y` (with `gcd = 1` and the erased
`gcd = 1`) whose top three are not `{M-2,M-1,M}` (index-free: not both `M-1,M-2 ∈ Y`), the induction
hypothesis on `Y.erase M` supplies the `3k-6` bound and `terminal_nonAP1` gives `3k-3`. -/
lemma terminal_bound (Y : Finset ℕ) (M : ℕ) (hsub : Y ⊆ Finset.Icc 0 M)
    (h0 : 0 ∈ Y) (hM : M ∈ Y) (hk4 : 4 ≤ Y.card) (hgcd : Y.gcd id = 1)
    (hgcdE : (Y.erase M).gcd id = 1)
    (IH : ∀ (B' : Finset ℕ) (L' : ℕ), B'.card < Y.card → B' ⊆ Finset.Icc 0 L' → 0 ∈ B' → L' ∈ B' →
      3 ≤ B'.card → B'.gcd id = 1 → 2 * B'.card - 3 ≤ L' → 3 * B'.card - 3 ≤ (B' + B').card)
    (hne : (Y.erase M).Nonempty)
    (hterm : 2 * (Y.card - 2) ≤ (Y.erase M).max' hne)
    (hnc : ¬ (M - 1 ∈ Y ∧ M - 2 ∈ Y)) :
    3 * Y.card - 3 ≤ (Y + Y).card := by
  have hMx : ∀ a ∈ Y, a ≤ M := fun a ha => by
    have := hsub ha; rw [Finset.mem_Icc] at this; omega
  have h0M : 0 < M := by
    rcases Nat.eq_zero_or_pos M with hM0 | h
    · exfalso
      have : Y ⊆ {0} := fun a ha => by have := hMx a ha; simp; omega
      have := Finset.card_le_card this; simp at this; omega
    · exact h
  obtain ⟨p, q, hpY, hqY, hpneM, hqneM, hqp, hpM, hpmax, hqmax⟩ :=
    top_two Y M h0 hM (by omega) hMx h0M
  have hncorner : ¬ (p = M - 1 ∧ q = M - 2) := by
    rintro ⟨hp, hq⟩; exact hnc ⟨hp ▸ hpY, hq ▸ hqY⟩
  -- p = max(Y.erase M) ⇒ 2(k-2) ≤ p
  have hple : (Y.erase M).max' hne ≤ p :=
    Finset.max'_le (Y.erase M) hne p
      (fun a ha => hpmax a (Finset.mem_of_mem_erase ha) (Finset.mem_erase.mp ha).1)
  have hp_ge : 2 * (Y.card - 2) ≤ p := le_trans hterm hple
  -- IH on A' = Y.erase M
  set A' := Y.erase M with hA'
  have hA'card : A'.card = Y.card - 1 := by rw [hA', Finset.card_erase_of_mem hM]
  have hpA' : p ∈ A' := Finset.mem_erase.mpr ⟨hpneM, hpY⟩
  have hA'sub : A' ⊆ Finset.Icc 0 p := by
    intro a ha; rw [Finset.mem_Icc]
    have haY := Finset.mem_of_mem_erase ha
    have haneM := (Finset.mem_erase.mp ha).1
    exact ⟨by omega, hpmax a haY haneM⟩
  have h0A' : 0 ∈ A' := Finset.mem_erase.mpr ⟨by omega, h0⟩
  have hIH := IH A' p (by rw [hA'card]; omega) hA'sub h0A' hpA' (by rw [hA'card]; omega) hgcdE
    (by rw [hA'card]; omega)
  have hbound : 3 * Y.card - 6 ≤ (A' + A').card := by rw [hA'card] at hIH; omega
  exact terminal_nonAP1 Y M p q hsub hM h0 hgcd hpY hqY hpM hqp hpmax hqmax hncorner hbound

#print axioms terminal_bound

/-- **Case 3 (terminal), full assembly with reflection.** For terminal `X` (`d=1` branch: `gcd X=1`,
`gcd(X.erase M)=1`), if the top three aren't `{M-2,M-1,M}` use `terminal_bound` directly. Otherwise
reflect `X → C = M - X` (`|C+C|=|X+X|`); `C` is either non-terminal (`d1_nonterminal`), terminal
non-corner (`terminal_bound`), or also a corner — in which case `{0,1,2},{M-2,M-1,M} ⊆ X` and
`double_ended_split` finishes (the six distinct elements force `k ≥ 6`). -/
lemma case3_terminal (X : Finset ℕ) (M : ℕ) (hsub : X ⊆ Finset.Icc 0 M)
    (h0 : 0 ∈ X) (hM : M ∈ X) (hk4 : 4 ≤ X.card) (hMlo : 2 * X.card - 2 ≤ M)
    (hgcd : X.gcd id = 1) (hgcdE : (X.erase M).gcd id = 1)
    (IH : ∀ (B' : Finset ℕ) (L' : ℕ), B'.card < X.card → B' ⊆ Finset.Icc 0 L' → 0 ∈ B' → L' ∈ B' →
      3 ≤ B'.card → B'.gcd id = 1 → 2 * B'.card - 3 ≤ L' → 3 * B'.card - 3 ≤ (B' + B').card)
    (hne : (X.erase M).Nonempty)
    (hterm : 2 * (X.card - 2) ≤ (X.erase M).max' hne) :
    3 * X.card - 3 ≤ (X + X).card := by
  have hMx : ∀ a ∈ X, a ≤ M := fun a ha => by
    have := hsub ha; rw [Finset.mem_Icc] at this; omega
  have hMbig : 6 ≤ M := by omega
  by_cases hXnc : ¬ (M - 1 ∈ X ∧ M - 2 ∈ X)
  · exact terminal_bound X M hsub h0 hM hk4 hgcd hgcdE IH hne hterm hXnc
  · push_neg at hXnc
    obtain ⟨hM1X, hM2X⟩ := hXnc
    -- reflect
    have hCsum : ((X.image (fun x => M - x)) + (X.image (fun x => M - x))).card = (X + X).card :=
      reflect_sumset X M hsub
    obtain ⟨hCsub, h0C, hMC, hCcard⟩ := reflect_basic X M hsub h0 hM
    set C := X.image (fun x => M - x) with hCdef
    have h1C : (1 : ℕ) ∈ C := by
      rw [hCdef, Finset.mem_image]; exact ⟨M - 1, hM1X, by omega⟩
    have hgcdC : C.gcd id = 1 := gcd_eq_one_of_one_mem C h1C
    have hgcdCE : (C.erase M).gcd id = 1 :=
      gcd_eq_one_of_one_mem (C.erase M) (Finset.mem_erase.mpr ⟨by omega, h1C⟩)
    have hneC : (C.erase M).Nonempty := ⟨0, Finset.mem_erase.mpr ⟨by omega, h0C⟩⟩
    -- IH transfers to C (C.card = X.card)
    have IHC : ∀ (B' : Finset ℕ) (L' : ℕ), B'.card < C.card → B' ⊆ Finset.Icc 0 L' → 0 ∈ B' →
        L' ∈ B' → 3 ≤ B'.card → B'.gcd id = 1 → 2 * B'.card - 3 ≤ L' →
        3 * B'.card - 3 ≤ (B' + B').card :=
      fun B' L' hc => IH B' L' (hCcard ▸ hc)
    -- reduce goal to |C+C|
    rw [← hCsum]
    by_cases hCterm : 2 * (C.card - 2) ≤ (C.erase M).max' hneC
    · -- C terminal
      by_cases hCnc : ¬ (M - 1 ∈ C ∧ M - 2 ∈ C)
      · have := terminal_bound C M hCsub h0C hMC (by omega) hgcdC hgcdCE IHC hneC hCterm hCnc
        rw [hCcard] at this; exact this
      · push_neg at hCnc
        obtain ⟨hM1C, hM2C⟩ := hCnc
        -- M-1∈C ⇒ 1∈X ; M-2∈C ⇒ 2∈X
        have h1X : (1 : ℕ) ∈ X := by
          rw [hCdef, Finset.mem_image] at hM1C; obtain ⟨a, haX, ha⟩ := hM1C
          have ha2 : M - a = M - 1 := ha
          have haM := hMx a haX; have hae : a = 1 := by omega
          rw [hae] at haX; exact haX
        have h2X : (2 : ℕ) ∈ X := by
          rw [hCdef, Finset.mem_image] at hM2C; obtain ⟨a, haX, ha⟩ := hM2C
          have ha2 : M - a = M - 2 := ha
          have haM := hMx a haX; have hae : a = 2 := by omega
          rw [hae] at haX; exact haX
        -- k ≥ 6 : {0,1,2,M-2,M-1,M} ⊆ X distinct
        have hk6 : 6 ≤ X.card := by
          have hsub6 : ({0, 1, 2, M - 2, M - 1, M} : Finset ℕ) ⊆ X := by
            intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
            exacts [h0, h1X, h2X, hM2X, hM1X, hM]
          have hc6 : ({0, 1, 2, M - 2, M - 1, M} : Finset ℕ).card = 6 := by
            rw [Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
          have := Finset.card_le_card hsub6; omega
        rw [hCsum]
        exact double_ended_split X M hsub h0 hM hk6 hMlo IH h1X h2X hM1X hM2X
    · -- C non-terminal
      push_neg at hCterm
      have := d1_nonterminal C M hCsub h0C hMC (by omega) (by rw [hCcard]; exact hMlo) IHC hneC hCterm
      rw [hCcard] at this; exact this

#print axioms case3_terminal

/-- **Freiman's `3k-3` theorem (large-diameter form).** For `B ⊆ [0,L]` with `0,L ∈ B`, `|B| ≥ 3`,
`gcd(B) = 1`, and `L ≥ 2|B|-3`: `3|B|-3 ≤ |B+B|`. Strong induction on `|B|` composing the base case,
the small-diameter boundary, the `d>1` residue case, and the `d=1` Case 1/2/3 split. -/
theorem freiman_3k3 : ∀ (B : Finset ℕ) (L : ℕ), B ⊆ Finset.Icc 0 L → 0 ∈ B → L ∈ B →
    3 ≤ B.card → B.gcd id = 1 → 2 * B.card - 3 ≤ L → 3 * B.card - 3 ≤ (B + B).card := by
  suffices H : ∀ k, ∀ (B : Finset ℕ) (L : ℕ), B.card = k → B ⊆ Finset.Icc 0 L → 0 ∈ B → L ∈ B →
      3 ≤ B.card → B.gcd id = 1 → 2 * B.card - 3 ≤ L → 3 * B.card - 3 ≤ (B + B).card by
    intro B L hsub h0 hLB hk hgcd hL
    exact H B.card B L rfl hsub h0 hLB hk hgcd hL
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro B L hcard hsub h0 hLB hk hgcd hL
    have IH' : ∀ (B' : Finset ℕ) (L' : ℕ), B'.card < B.card → B' ⊆ Finset.Icc 0 L' → 0 ∈ B' →
        L' ∈ B' → 3 ≤ B'.card → B'.gcd id = 1 → 2 * B'.card - 3 ≤ L' →
        3 * B'.card - 3 ≤ (B' + B').card := by
      intro B' L' hlt hsub' h0' hL' hk' hg' hL2'
      exact IH B'.card (by omega) B' L' rfl hsub' h0' hL' hk' hg' hL2'
    by_cases hk3 : B.card = 3
    · exact base_case_k3 B L hsub h0 hLB hk3 hgcd (by omega)
    · have hk4 : 4 ≤ B.card := by omega
      by_cases hbdry : L ≤ 2 * B.card - 3
      · have := small_diameter B L hsub h0 hLB (by omega) (by omega); omega
      · push_neg at hbdry
        set d := (B.erase L).gcd id with hddef
        by_cases hd : 1 < d
        · exact case_d_gt_one B L hsub h0 hLB hk hgcd hd
        · -- d = 1
          have hne : (B.erase L).Nonempty := ⟨0, Finset.mem_erase.mpr ⟨by omega, h0⟩⟩
          have hgcdE : (B.erase L).gcd id = 1 := by
            rw [← hddef]
            by_contra hcon
            have hd0 : d = 0 := by omega
            -- a nonzero element of B.erase L
            have hcard2 : 2 ≤ ((B.erase L).erase 0).card := by
              rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨by omega, h0⟩),
                Finset.card_erase_of_mem hLB]; omega
            obtain ⟨x, hx⟩ : ((B.erase L).erase 0).Nonempty := by
              rw [← Finset.card_pos]; omega
            have hxel : x ∈ B.erase L := Finset.mem_of_mem_erase hx
            have hxne0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
            have hdvd : d ∣ x := hddef ▸ Finset.gcd_dvd hxel
            rw [hd0] at hdvd
            exact hxne0 (Nat.eq_zero_of_zero_dvd hdvd)
          by_cases hterm : 2 * (B.card - 2) ≤ (B.erase L).max' hne
          · exact case3_terminal B L hsub h0 hLB hk4 (by omega) hgcd hgcdE IH' hne hterm
          · push_neg at hterm
            exact d1_nonterminal B L hsub h0 hLB hk (by omega) IH' hne hterm

#print axioms freiman_3k3











end Erdos361Freiman
