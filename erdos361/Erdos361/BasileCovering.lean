import Mathlib
set_option maxHeartbeats 1000000
open Finset
open scoped Pointwise

/-!
# Erdős #361 — the hLev covering lemma (elementary route, GPT-5 Pro blueprint 2026-07-28)

Goal: discharge the `hLev` hypothesis of `Erdos361Basile71.basile71` WITHOUT Lev 1997. Every
even `t ∈ (2E,3E)` is an `h`-fold sum (repetitions allowed) of a size-`≥(1/3+ε/2)E` set
`G ⊆ [1,E]`, for some `h ≤ 9`. Blueprint in
`Problems/campaign/erdos_361_irregularity/conj8/GPT-hLev-covering-blueprint.md`.

Structure (banked bottom-up):
* `lemma1_holes`  — holes give a central 2-fold interval `[2q, 2M-2q] ⊆ X+X`. Pure pigeonhole.
* `lemma2_dense`  — a `≥½`-dense normalized set covers `[Γ₁, hL-Γ₁] ⊆ hB`. [TODO]
* `lemma3_third`  — the `1/3`-density regime via doubling + Freiman `3N-3` (hypothesis). [TODO]
* gcd normalization + affine pullback + interval-chain covering → `hLev`. [TODO]

The ONLY external input is Freiman's `3k-3` (`|B+B| ≥ min{L,2|B|-3}+|B|`), carried as a hypothesis
(regime (c) of the lean-proving skill), NOT an axiom.
-/

namespace Erdos361Covering

/-- **Lemma 1** (holes give a two-fold central interval). If `X ⊆ [0,M]` has `q = M+1-|X|` holes,
then every `z ∈ [2q, 2M-2q]` is a sum of two elements of `X`. Unified pigeonhole over the window
`U' = [z-M, min M z]` (no reflection sub-case): the "left-bad" `{u ∈ U' : u ∉ X}` and "right-bad"
`{u ∈ U' : z-u ∉ X}` each have `≤ q` elements (both inject into the `q` holes), and `|U'| ≥ 2q+1`,
so some `u ∈ U'` has `u ∈ X` and `z-u ∈ X`. -/
lemma lemma1_holes (X : Finset ℕ) (M : ℕ) (hXM : X ⊆ Finset.Icc 0 M) :
    ∀ z, 2 * (M + 1 - X.card) ≤ z → z ≤ 2 * M - 2 * (M + 1 - X.card) →
      ∃ u ∈ X, ∃ v ∈ X, u + v = z := by
  set q := M + 1 - X.card with hq
  intro z hzlo hzhi
  -- the hole set and its cardinality
  set hole := (Finset.Icc 0 M) \ X with hhole
  have hXcardle : X.card ≤ M + 1 := by
    have := Finset.card_le_card hXM
    simpa [Nat.card_Icc] using this
  have hholecard : hole.card = q := by
    rw [hhole, Finset.card_sdiff_of_subset hXM]
    simp [Nat.card_Icc, hq]
  -- the window U'
  set lo := z - M with hlo
  set hi := min M z with hhi
  set U := Finset.Icc lo hi with hU
  -- membership facts on U
  have hUsub : U ⊆ Finset.Icc 0 M := by
    intro u hu
    rw [hU, Finset.mem_Icc] at hu
    rw [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, le_trans hu.2 (min_le_left _ _)⟩
  have huz : ∀ u ∈ U, u ≤ z := by
    intro u hu; rw [hU, Finset.mem_Icc] at hu
    exact le_trans hu.2 (min_le_right _ _)
  have huge : ∀ u ∈ U, z - M ≤ u := by
    intro u hu; rw [hU, Finset.mem_Icc] at hu; exact hu.1
  -- |U| = hi + 1 - lo ≥ 2q + 1
  have hUcard : (2 * q + 1) ≤ U.card := by
    rw [hU, Nat.card_Icc]
    -- hi + 1 - lo ≥ 2q+1, with hhi : hi = min M z, hlo : lo = z - M (omega handles min/-)
    omega
  -- left-bad set injects into holes
  set badL := U.filter (fun u => u ∉ X) with hbadL
  have hbadLcard : badL.card ≤ q := by
    rw [← hholecard]
    apply Finset.card_le_card
    intro u hu
    rw [hbadL, Finset.mem_filter] at hu
    rw [hhole, Finset.mem_sdiff]
    exact ⟨hUsub hu.1, hu.2⟩
  -- right-bad set injects into holes via u ↦ z - u
  set badR := U.filter (fun u => z - u ∉ X) with hbadR
  have hbadRcard : badR.card ≤ q := by
    rw [← hholecard]
    apply Finset.card_le_card_of_injOn (fun u => z - u)
    · intro u hu
      simp only [hbadR, Finset.mem_coe, Finset.mem_filter] at hu
      simp only [hhole, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_Icc]
      have hle : u ≤ z := huz u hu.1
      have hge : z - M ≤ u := huge u hu.1
      refine ⟨⟨Nat.zero_le _, ?_⟩, hu.2⟩
      omega
    · intro a ha b hb hab
      simp only [hbadR, Finset.mem_coe, Finset.mem_filter] at ha hb
      have hale : a ≤ z := huz a ha.1
      have hble : b ≤ z := huz b hb.1
      have hab' : z - a = z - b := hab
      omega
  -- pigeonhole: badL ∪ badR ⊊ U
  have hcup : (badL ∪ badR).card < U.card := by
    calc (badL ∪ badR).card ≤ badL.card + badR.card := Finset.card_union_le _ _
      _ ≤ q + q := Nat.add_le_add hbadLcard hbadRcard
      _ = 2 * q := by ring
      _ < 2 * q + 1 := Nat.lt_succ_self _
      _ ≤ U.card := hUcard
  have hsub : badL ∪ badR ⊆ U :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hne : badL ∪ badR ≠ U := fun h => absurd hcup (by rw [h]; exact lt_irrefl _)
  obtain ⟨u, huU, hunotin⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hsub hne)
  -- u ∈ U, u ∉ badL ∪ badR  ⟹  u ∈ X and z - u ∈ X
  rw [Finset.mem_union] at hunotin
  push_neg at hunotin
  have huX : u ∈ X := by
    by_contra h
    exact hunotin.1 (by rw [hbadL, Finset.mem_filter]; exact ⟨huU, h⟩)
  have hvX : z - u ∈ X := by
    by_contra h
    exact hunotin.2 (by rw [hbadR, Finset.mem_filter]; exact ⟨huU, h⟩)
  refine ⟨u, huX, z - u, hvX, ?_⟩
  have : u ≤ z := huz u huU
  omega

#print axioms lemma1_holes

/-- `x` is a sum of exactly `h` elements of `B`, repetitions allowed (the `h`-fold sumset `hB`).
Identical to `Erdos361Basile71.RepWithRep`. -/
def hfold (B : Finset ℕ) (h x : ℕ) : Prop :=
  ∃ f : Fin h → ℕ, (∀ i, f i ∈ B) ∧ (∑ i, f i) = x

/-- The empty sum: `0 ∈ 0·B`. -/
lemma hfold_zero (B : Finset ℕ) : hfold B 0 0 :=
  ⟨Fin.elim0, fun i => i.elim0, by simp⟩

/-- Prepend one element `b ∈ B` to an `h`-fold representation. -/
lemma hfold_cons {B : Finset ℕ} {h x b : ℕ} (hb : b ∈ B) (hx : hfold B h x) :
    hfold B (h + 1) (b + x) := by
  obtain ⟨f, hf, hsum⟩ := hx
  refine ⟨Fin.cons b f, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ ?_ i
    · simpa using hb
    · intro j; simpa using hf j
  · rw [Fin.sum_cons, hsum]

/-- Append `k` copies of an element `b ∈ B`. -/
lemma hfold_add_copies {B : Finset ℕ} {h x : ℕ} (b : ℕ) (hb : b ∈ B) (k : ℕ)
    (hx : hfold B h x) : hfold B (h + k) (x + k * b) := by
  induction k with
  | zero => simpa using hx
  | succ n ih =>
      have hstep := hfold_cons hb ih
      have e1 : h + (n + 1) = (h + n) + 1 := by ring
      have e2 : x + (n + 1) * b = b + (x + n * b) := by ring
      rw [e1, e2]; exact hstep

/-- A two-element sum `u + v` with `u, v ∈ B` is a `2`-fold representation. -/
lemma hfold_two {B : Finset ℕ} {u v : ℕ} (hu : u ∈ B) (hv : v ∈ B) : hfold B 2 (u + v) := by
  have h1 : hfold B 1 (v + 0) := hfold_cons hv (hfold_zero B)
  have h2 : hfold B 2 (u + (v + 0)) := hfold_cons hu h1
  simpa using h2

/-- Rewrite the parameters of an `hfold` along equalities. -/
lemma hfold_congr {B : Finset ℕ} {h h' x x' : ℕ} (hh : h = h') (hx : x = x')
    (H : hfold B h x) : hfold B h' x' := by rw [← hh, ← hx]; exact H

/-- Concatenate two representations (`Fin.append`). -/
lemma hfold_add {B : Finset ℕ} {a b x y : ℕ} (Hx : hfold B a x) (Hy : hfold B b y) :
    hfold B (a + b) (x + y) := by
  obtain ⟨f, hf, hfs⟩ := Hx
  obtain ⟨g, hg, hgs⟩ := Hy
  refine ⟨Fin.append f g, ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_)
    · rw [Fin.append_left]; exact hf j
    · rw [Fin.append_right]; exact hg j
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hfs, hgs]

/-- Peel the first element off an `(n+1)`-fold representation. -/
lemma hfold_uncons {C : Finset ℕ} {n x : ℕ} (H : hfold C (n + 1) x) :
    ∃ c ∈ C, ∃ x', hfold C n x' ∧ c + x' = x := by
  obtain ⟨f, hf, hfs⟩ := H
  refine ⟨f 0, hf 0, ∑ i : Fin n, f i.succ, ⟨fun i => f i.succ, fun i => hf _, rfl⟩, ?_⟩
  rw [← hfs, Fin.sum_univ_succ]

/-- **Sumset bridge**: a `q`-fold sum of elements of `B+B` is a `2q`-fold sum of elements of `B`. -/
lemma hfold_sumset {B : Finset ℕ} : ∀ {q x : ℕ}, hfold (B + B) q x → hfold B (2 * q) x := by
  intro q
  induction q with
  | zero =>
      intro x H
      obtain ⟨f, hf, hfs⟩ := H
      have hx0 : x = 0 := by rw [← hfs]; simp
      rw [hx0]; simpa using hfold_zero B
  | succ n ih =>
      intro x H
      obtain ⟨c, hc, x', Hx', hcx⟩ := hfold_uncons H
      rw [Finset.mem_add] at hc
      obtain ⟨u, hu, v, hv, huv⟩ := hc
      have h2 : hfold B 2 c := by rw [← huv]; exact hfold_two hu hv
      have hrec : hfold B (2 * n) x' := ih Hx'
      have hcomb := hfold_add h2 hrec
      rw [hcx] at hcomb
      exact hfold_congr (by ring) rfl hcomb

/-- **Affine pullback** `hG = ha + d·hB`. If every normalized element `b ∈ B` lifts to
`a + d·b ∈ G`, then an `h`-fold representation `y ∈ hB` lifts to `(ha + d·y) ∈ hG`. No injectivity
or divisibility needed — just the forward lift. -/
lemma hfold_pullback {G B : Finset ℕ} {a d h y : ℕ}
    (hBG : ∀ b ∈ B, a + d * b ∈ G) (H : hfold B h y) :
    hfold G h (h * a + d * y) := by
  obtain ⟨f, hf, hfs⟩ := H
  refine ⟨fun i => a + d * f i, fun i => hBG _ (hf i), ?_⟩
  rw [Finset.sum_add_distrib]
  congr 1
  · simp [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  · rw [← Finset.mul_sum, hfs]

/-- **Modular representation** (the ℤ/L pigeonhole core of Lemma 2). If `C ⊆ ℕ` has all elements
`< L`, its residues are distinct (automatic), and `L < 2|C|`, then for every `r < L` there exist
`c₁, c₂ ∈ C` with `c₁ + c₂ = r` or `c₁ + c₂ = r + L`. -/
lemma modular_rep (C : Finset ℕ) (L : ℕ) (hL : 0 < L) (hClt : ∀ c ∈ C, c < L)
    (hcard : L < 2 * C.card) (r : ℕ) (hr : r < L) :
    ∃ c₁ ∈ C, ∃ c₂ ∈ C, c₁ + c₂ = r ∨ c₁ + c₂ = r + L := by
  haveI : NeZero L := ⟨hL.ne'⟩
  -- distinct naturals < L stay distinct mod L
  have castInj : ∀ a ∈ C, ∀ b ∈ C, (a : ZMod L) = (b : ZMod L) → a = b := by
    intro a ha b hb hab
    have hmod : a % L = b % L := (ZMod.natCast_eq_natCast_iff a b L).mp hab
    rwa [Nat.mod_eq_of_lt (hClt a ha), Nat.mod_eq_of_lt (hClt b hb)] at hmod
  -- images of C under (· : ZMod L) and (r - ·)
  set f1 : ℕ → ZMod L := fun c => (c : ZMod L) with hf1
  set f2 : ℕ → ZMod L := fun c => (r : ZMod L) - (c : ZMod L) with hf2
  have hinj1 : Set.InjOn f1 ↑C := by
    intro a ha b hb hab
    exact castInj a (by simpa using ha) b (by simpa using hb) hab
  have hinj2 : Set.InjOn f2 ↑C := by
    intro a ha b hb hab
    rw [hf2] at hab
    have : (a : ZMod L) = (b : ZMod L) := sub_right_inj.mp hab
    exact castInj a (by simpa using ha) b (by simpa using hb) this
  have hcard1 : (C.image f1).card = C.card := Finset.card_image_of_injOn hinj1
  have hcard2 : (C.image f2).card = C.card := Finset.card_image_of_injOn hinj2
  -- pigeonhole: the two images intersect
  have hinter : (C.image f1 ∩ C.image f2).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hdisj : Disjoint (C.image f1) (C.image f2) :=
      Finset.disjoint_iff_inter_eq_empty.mpr hemp
    have hle : (C.image f1).card + (C.image f2).card ≤ (Finset.univ : Finset (ZMod L)).card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (Finset.subset_univ _)
    rw [hcard1, hcard2, Finset.card_univ, ZMod.card] at hle
    omega
  obtain ⟨a, ha⟩ := hinter
  rw [Finset.mem_inter] at ha
  obtain ⟨c₁, hc₁C, hc₁⟩ := Finset.mem_image.mp ha.1
  obtain ⟨c₂, hc₂C, hc₂⟩ := Finset.mem_image.mp ha.2
  have hkey : (c₁ : ZMod L) = (r : ZMod L) - (c₂ : ZMod L) := by
    have e1 : (c₁ : ZMod L) = a := hc₁
    have e2 : (r : ZMod L) - (c₂ : ZMod L) = a := hc₂
    rw [e1, e2]
  have hsum : ((c₁ + c₂ : ℕ) : ZMod L) = (r : ZMod L) := by
    push_cast; rw [hkey]; ring
  have hmod : (c₁ + c₂) % L = r := by
    have := (ZMod.natCast_eq_natCast_iff (c₁ + c₂) r L).mp hsum
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hr] at this
  have hc1l := hClt c₁ hc₁C
  have hc2l := hClt c₂ hc₂C
  refine ⟨c₁, hc₁C, c₂, hc₂C, ?_⟩
  -- c₁+c₂ = L·Q + r with Q < 2, so = r or r+L
  obtain ⟨Q, hQeq⟩ : ∃ Q, c₁ + c₂ = L * Q + r :=
    ⟨(c₁ + c₂) / L, by rw [← hmod]; exact (Nat.div_add_mod _ _).symm⟩
  have hQlt : Q < 2 := by
    by_contra h
    push_neg at h
    have hmul : L * 2 ≤ L * Q := Nat.mul_le_mul_left L h
    omega
  interval_cases Q <;> omega

/-- **Lemma 2** (dense normalized interval theorem). If `B ⊆ [0,L]` with `0,L ∈ B`, `N = |B| ≥ 3`,
and `L ≤ 2N-4` (density `≥ ½`), then for every `h ≥ 2` the whole interval `[Γ₁, hL-Γ₁] ⊆ hB`, where
`Γ₁ = 2L-2N+2`. Proof: `lemma1_holes` gives `[Γ₁,2L-Γ₁] ⊆ 2B`; for `x` in the low part append
`0`'s, in the high part append `L`'s, and in the middle use `modular_rep` on `C = B \ {L}`. -/
lemma lemma2_dense (B : Finset ℕ) (L : ℕ) (hBsub : B ⊆ Finset.Icc 0 L)
    (h0 : 0 ∈ B) (hLB : L ∈ B) (hN3 : 3 ≤ B.card) (hdense : L ≤ 2 * B.card - 4) :
    ∀ h, 2 ≤ h → ∀ x, 2 * L + 2 - 2 * B.card ≤ x → x ≤ h * L - (2 * L + 2 - 2 * B.card) →
      hfold B h x := by
  set N := B.card with hN
  intro h hh2 x hxlo hxhi
  -- basic facts
  have hcardle : N ≤ L + 1 := by
    rw [hN]; have := Finset.card_le_card hBsub; simpa [Nat.card_Icc] using this
  have hLpos : 0 < L := by
    rcases Nat.eq_zero_or_pos L with hL0 | hLpos
    · exfalso
      have hsub : B ⊆ {0} := by
        intro b hb; have := hBsub hb; rw [Finset.mem_Icc] at this
        simp only [Finset.mem_singleton]; omega
      have := Finset.card_le_card hsub; rw [← hN] at this; simp at this; omega
    · exact hLpos
  have hG1le : 2 * L + 2 - 2 * N ≤ L - 2 := by omega
  -- Lemma 1: the 2-fold central interval  [Γ₁, 2N-2] = [Γ₁, 2L-Γ₁] ⊆ 2B
  have hL1 : ∀ z, 2 * L + 2 - 2 * N ≤ z → z ≤ 2 * N - 2 → ∃ u ∈ B, ∃ v ∈ B, u + v = z := by
    intro z hz1 hz2
    exact lemma1_holes B L hBsub z (by omega) (by omega)
  -- C = B \ {L}
  set C := B.erase L with hC
  have hCsub : C ⊆ B := Finset.erase_subset _ _
  have hCcard : C.card = N - 1 := by rw [hC, Finset.card_erase_of_mem hLB, ← hN]
  have hClt : ∀ c ∈ C, c < L := by
    intro c hc
    have hcB : c ∈ B := hCsub hc
    have hcL : c ≠ L := Finset.ne_of_mem_erase hc
    have := hBsub hcB; rw [Finset.mem_Icc] at this; omega
  have h2C : L < 2 * C.card := by rw [hCcard]; omega
  -- three cases on x's position
  rcases le_or_gt x (2 * N - 2) with hposA | hposA
  · -- Case A: x ≤ 2L-Γ₁, use 2B + (h-2) copies of 0
    obtain ⟨u, hu, v, hv, huv⟩ := hL1 x (by omega) hposA
    have base : hfold B 2 (u + v) := hfold_two hu hv
    have add0 := hfold_add_copies 0 h0 (h - 2) base
    exact hfold_congr (by omega) (by omega) add0
  · rcases le_or_gt ((h - 2) * L + (2 * L + 2 - 2 * N)) x with hposB | hposB
    · -- Case B: x ≥ (h-2)L+Γ₁, use 2B on w = x-(h-2)L + (h-2) copies of L
      set w := x - (h - 2) * L with hw
      have hwlo : 2 * L + 2 - 2 * N ≤ w := by rw [hw]; omega
      have hwhi : w ≤ 2 * N - 2 := by
        -- w = x - (h-2)L ≤ hL - Γ₁ - (h-2)L = 2L - Γ₁ = 2N-2
        have hexp : h * L = (h - 2) * L + 2 * L := by
          rw [← Nat.add_mul, Nat.sub_add_cancel hh2]
        rw [hw]; omega
      obtain ⟨u, hu, v, hv, huv⟩ := hL1 w hwlo hwhi
      have base : hfold B 2 (u + v) := hfold_two hu hv
      have addL := hfold_add_copies L hLB (h - 2) base
      refine hfold_congr (by omega) ?_ addL
      -- (u+v) + (h-2)*L = x, since u+v = w = x-(h-2)L
      rw [huv, hw]; omega
    · -- Case C (middle): 2L-Γ₁ < x < (h-2)L+Γ₁
      obtain ⟨k, r, hr, hxkr⟩ : ∃ k r, r < L ∧ x = L * k + r :=
        ⟨x / L, x % L, Nat.mod_lt x hLpos, (Nat.div_add_mod x L).symm⟩
      have hxgtL : L < x := by omega
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | hpos
        · simp only [Nat.mul_zero] at hxkr; omega
        · exact hpos
      have hk2 : k ≤ h - 2 := by
        have hexp : L * (h - 1) = L * (h - 2) + L := by
          have h' : h - 1 = (h - 2) + 1 := by omega
          rw [h']; ring
        have hxlt : x < L * (h - 2) + L := by
          have hcomm : (h - 2) * L = L * (h - 2) := Nat.mul_comm _ _
          omega
        have hbound : L * k < L * (h - 1) := by omega
        have := Nat.lt_of_mul_lt_mul_left hbound
        omega
      -- modular representation of r
      obtain ⟨c₁, hc₁, c₂, hc₂, hrep⟩ := modular_rep C L hLpos hClt h2C r hr
      have hc₁B : c₁ ∈ B := hCsub hc₁
      have hc₂B : c₂ ∈ B := hCsub hc₂
      have base : hfold B 2 (c₁ + c₂) := hfold_two hc₁B hc₂B
      rcases hrep with hj0 | hj1
      · -- c₁+c₂ = r: append k copies of L and (h-2-k) copies of 0
        have addL := hfold_add_copies L hLB k base
        have add0 := hfold_add_copies 0 h0 (h - 2 - k) addL
        refine hfold_congr (by omega) ?_ add0
        -- ((c₁+c₂) + k*L) + (h-2-k)*0 = x = L*k + r
        have hcomm : k * L = L * k := Nat.mul_comm _ _
        rw [hj0]; omega
      · -- c₁+c₂ = r+L: append (k-1) copies of L and (h-1-k) copies of 0
        have addL := hfold_add_copies L hLB (k - 1) base
        have add0 := hfold_add_copies 0 h0 (h - 1 - k) addL
        refine hfold_congr (by omega) ?_ add0
        -- ((c₁+c₂) + (k-1)*L) + (h-1-k)*0 = x, with c₁+c₂ = r+L
        have hcomm : (k - 1) * L = L * (k - 1) := Nat.mul_comm _ _
        have hexp : L * (k - 1) + L = L * k := by
          rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hk1]
        rw [hj1]; omega

/-- **Lemma 3** (the `1/3`-density regime, even multiplicities, via doubling). If `B ⊆ [0,L]` with
`0,L ∈ B`, `N=|B|≥3`, `2N-3 ≤ L ≤ 3N-6`, and the Freiman bound `3N-3 ≤ |B+B|` (carried as a
hypothesis — the one cited fact, not an axiom), then for every `q ≥ 2` the interval
`[Γ₂, 2qL-Γ₂] ⊆ (2q)B`, where `Γ₂ = 4L+8-6N`. Proof: `B+B` is `≥½`-dense in `[0,2L]`, so
`lemma2_dense` covers `[Γ', q·2L-Γ'] ⊆ q(B+B)` with `Γ' = 4L+2-2S ≤ Γ₂`; then `hfold_sumset`. -/
lemma lemma3_third (B : Finset ℕ) (L : ℕ) (hBsub : B ⊆ Finset.Icc 0 L)
    (h0 : 0 ∈ B) (hLB : L ∈ B) (hN3 : 3 ≤ B.card)
    (hLlo : 2 * B.card - 3 ≤ L) (hLhi : L ≤ 3 * B.card - 6)
    (hFreiman : 3 * B.card - 3 ≤ (B + B).card) :
    ∀ q, 2 ≤ q → ∀ x, 4 * L + 8 - 6 * B.card ≤ x → x ≤ 2 * q * L - (4 * L + 8 - 6 * B.card) →
      hfold B (2 * q) x := by
  set N := B.card with hN
  set S := (B + B).card with hS
  intro q hq2 x hxlo hxhi
  -- sumset facts for  B+B ⊆ [0,2L]
  have hBBsub : (B + B) ⊆ Finset.Icc 0 (2 * L) := by
    intro w hw; rw [Finset.mem_add] at hw
    obtain ⟨u, hu, v, hv, huv⟩ := hw
    have hu' := hBsub hu; have hv' := hBsub hv
    rw [Finset.mem_Icc] at hu' hv' ⊢; omega
  have h0BB : 0 ∈ B + B := by
    have := Finset.add_mem_add h0 h0; simpa using this
  have hLLBB : 2 * L ∈ B + B := by
    have h := Finset.add_mem_add hLB hLB
    rwa [show L + L = 2 * L from by ring] at h
  have hS3 : 3 ≤ S := by omega
  have hdense : 2 * L ≤ 2 * S - 4 := by omega
  -- apply lemma2_dense to B+B (ambient interval [0,2L])
  have hL2 := lemma2_dense (B + B) (2 * L) hBBsub h0BB hLLBB hS3 hdense
  -- Γ' = 2*(2L)+2-2*S ≤ Γ₂ = 4L+8-6N
  have hGle : 2 * (2 * L) + 2 - 2 * S ≤ 4 * L + 8 - 6 * N := by omega
  have hqL : q * (2 * L) = 2 * q * L := by ring
  have hrep := hL2 q hq2 x (by omega) (by omega)
  exact hfold_sumset hrep

/-- **gcd normalization.** For `G ⊆ [1,E]` with `|G| ≥ 3`, let `a = min G`, `d = gcd{g-a : g∈G}`,
`L = (max G - a)/d`, `B = {(g-a)/d : g∈G}`. Then `d > 0`, `1 ≤ a`, `a + d·L ≤ E`, `|B| = |G|`, every
`b ∈ B` lifts (`a + d·b ∈ G`), `0,L ∈ B`, and `B ⊆ [0,L]`. This packages the affine reduction feeding
`hfold_pullback`. (The `d ∈ {1,2}` bound and the interval-chain covering build on top of this.) -/
lemma normalize_setup (E : ℕ) (G : Finset ℕ) (hGsub : G ⊆ Finset.Icc 1 E) (hG3 : 3 ≤ G.card) :
    ∃ a d L : ℕ, ∃ B : Finset ℕ,
      0 < d ∧ 1 ≤ a ∧ a + d * L ≤ E ∧ B.card = G.card ∧
      (∀ b ∈ B, a + d * b ∈ G) ∧ 0 ∈ B ∧ L ∈ B ∧ B ⊆ Finset.Icc 0 L ∧ B.gcd id = 1 := by
  have hne : G.Nonempty := by rw [← Finset.card_pos]; omega
  set a := G.min' hne with ha
  set b := G.max' hne with hb
  set d := G.gcd (fun g => g - a) with hd
  have haG : a ∈ G := G.min'_mem hne
  have hbG : b ∈ G := G.max'_mem hne
  have ha_le : ∀ g ∈ G, a ≤ g := fun g hg => G.min'_le g hg
  have hle_b : ∀ g ∈ G, g ≤ b := fun g hg => G.le_max' g hg
  have hdvd : ∀ g ∈ G, d ∣ (g - a) := fun g hg => Finset.gcd_dvd hg
  -- d > 0
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · exfalso
      rw [hd, Finset.gcd_eq_zero_iff] at hd0
      -- then g - a = 0 for all g, so G ⊆ {a}, card ≤ 1
      have hsub : G ⊆ {a} := by
        intro g hg
        have := hd0 g hg; have := ha_le g hg
        simp only [Finset.mem_singleton]; omega
      have := Finset.card_le_card hsub; simp at this; omega
    · exact hdpos
  set L := (b - a) / d with hL
  set B := G.image (fun g => (g - a) / d) with hB
  have ha1 : 1 ≤ a := by have := hGsub haG; rw [Finset.mem_Icc] at this; omega
  have hbE : b ≤ E := by have := hGsub hbG; rw [Finset.mem_Icc] at this; omega
  have hdL : d * L = b - a := Nat.mul_div_cancel' (hdvd b hbG)
  have hab : a ≤ b := G.min'_le_max' hne
  -- lift: a + d·b' ∈ G for b' ∈ B
  have hpull : ∀ y ∈ B, a + d * y ∈ G := by
    intro y hy
    rw [hB, Finset.mem_image] at hy
    obtain ⟨g, hg, hgy⟩ := hy
    have hgd : d * ((g - a) / d) = g - a := Nat.mul_div_cancel' (hdvd g hg)
    have : a + d * y = g := by rw [← hgy, hgd]; have := ha_le g hg; omega
    rw [this]; exact hg
  refine ⟨a, d, L, B, hdpos, ha1, ?_, ?_, hpull, ?_, ?_, ?_, ?_⟩
  · -- a + d*L ≤ E:  a + (b-a) = b ≤ E
    rw [hdL]; omega
  · -- |B| = |G|
    rw [hB]
    apply Finset.card_image_of_injOn
    intro g hg g' hg' hgg'
    simp only at hgg'
    have h1 : d * ((g - a) / d) = g - a := Nat.mul_div_cancel' (hdvd g hg)
    have h2 : d * ((g' - a) / d) = g' - a := Nat.mul_div_cancel' (hdvd g' hg')
    have hga := ha_le g hg; have hg'a := ha_le g' hg'
    have : g - a = g' - a := by rw [← h1, ← h2, hgg']
    omega
  · -- 0 ∈ B
    rw [hB, Finset.mem_image]
    exact ⟨a, haG, by simp⟩
  · -- L ∈ B
    rw [hB, Finset.mem_image]
    exact ⟨b, hbG, rfl⟩
  · -- B ⊆ Icc 0 L
    intro y hy
    rw [hB, Finset.mem_image] at hy
    obtain ⟨g, hg, hgy⟩ := hy
    rw [Finset.mem_Icc]
    refine ⟨Nat.zero_le _, ?_⟩
    rw [← hgy, hL]
    apply Nat.div_le_div_right
    have := hle_b g hg; have := ha_le g hg; omega
  · -- B.gcd id = 1  (dividing by the spacing gcd d normalizes to gcd 1)
    have hcongr : G.gcd (fun g => d * ((g - a) / d)) = G.gcd (fun g => g - a) :=
      Finset.gcd_congr rfl (fun g hg => Nat.mul_div_cancel' (hdvd g hg))
    rw [Finset.gcd_mul_left, ← hd, normalize_eq] at hcongr
    -- hcongr : d * G.gcd (fun g => (g-a)/d) = d
    have hg1 : G.gcd (fun g => (g - a) / d) = 1 :=
      Nat.eq_of_mul_eq_mul_left hdpos (by rw [hcongr, mul_one])
    rw [hB, Finset.gcd_image]
    simpa using hg1

/-- **`d ∈ {1,2}`**. With `N ≤ L+1` (from `B ⊆ [0,L]`, `|B|=N`), `d·L ≤ E-1`, and the size lower
bound `E+24 ≤ 3N` (i.e. `N ≥ E/3 + 8`), the spacing gcd `d` is at most `2`. If `d ≥ 3` then
`3(N-1) ≤ d·L ≤ E-1`, but `3(N-1) = 3N-3 ≥ E+21`. -/
lemma gcd_le_two {E d L N : ℕ} (hd : 0 < d) (hNL : N ≤ L + 1) (hdLE : d * L ≤ E - 1)
    (hsize : E + 24 ≤ 3 * N) : d ≤ 2 := by
  by_contra hc
  push_neg at hc
  have h1 : 3 * (N - 1) ≤ d * (N - 1) := Nat.mul_le_mul (by omega) (le_refl _)
  have h2 : d * (N - 1) ≤ d * L := Nat.mul_le_mul (le_refl _) (by omega)
  omega

/-- **Interval-chain covering, `d=1` dense case** (blueprint §4.1). With the affine data `d=1`
(`∀ b ∈ B, a + b ∈ G`), `B` `≥½`-dense (`L ≤ 2N-4`), `1 ≤ a`, `a+L ≤ E`, size `E+24 ≤ 3N`, every
`t ∈ (2E,3E)` lies in `hG` for some `3 ≤ h ≤ 9`. The seven `h`-intervals `[ha+Γ, ha+hL-Γ]` (via
`lemma2_dense` + `hfold_pullback`) overlap/abut and run from below `2E` to above `3E`; a 7-way search
finds the covering `h`. All location/overlap inequalities are linear once `h` is a literal, so `omega`
discharges them. -/
lemma cover_d1_dense (a L E t : ℕ) (B G : Finset ℕ)
    (hpull : ∀ b ∈ B, a + 1 * b ∈ G)
    (hBsub : B ⊆ Finset.Icc 0 L) (h0 : 0 ∈ B) (hLB : L ∈ B) (hN3 : 3 ≤ B.card)
    (hdense : L ≤ 2 * B.card - 4) (ha1 : 1 ≤ a) (habE : a + L ≤ E)
    (hsize : E + 24 ≤ 3 * B.card) (htlo : 2 * E < t) (hthi : t < 3 * E) :
    ∃ h, 3 ≤ h ∧ h ≤ 9 ∧ hfold G h t := by
  set N := B.card with hN
  have hNL : N ≤ L + 1 := by
    rw [hN]; have := Finset.card_le_card hBsub; simpa [Nat.card_Icc] using this
  have hcov := lemma2_dense B L hBsub h0 hLB hN3 hdense
  have step : ∀ h : ℕ, 2 ≤ h → h * a + (2 * L + 2 - 2 * N) ≤ t →
      t ≤ h * a + h * L - (2 * L + 2 - 2 * N) → hfold G h t := by
    intro h hh2 hlo hhi
    have hHL : 2 * L ≤ h * L := Nat.mul_le_mul hh2 (le_refl L)
    have hyf := hcov h hh2 (t - h * a) (by omega) (by omega)
    have hpb := hfold_pullback hpull hyf
    exact hfold_congr rfl (by omega) hpb
  rcases le_or_gt t (3 * a + 3 * L - (2 * L + 2 - 2 * N)) with c3 | c3
  · exact ⟨3, by norm_num, by norm_num, step 3 (by norm_num) (by omega) c3⟩
  · rcases le_or_gt t (4 * a + 4 * L - (2 * L + 2 - 2 * N)) with c4 | c4
    · exact ⟨4, by norm_num, by norm_num, step 4 (by norm_num) (by omega) c4⟩
    · rcases le_or_gt t (5 * a + 5 * L - (2 * L + 2 - 2 * N)) with c5 | c5
      · exact ⟨5, by norm_num, by norm_num, step 5 (by norm_num) (by omega) c5⟩
      · rcases le_or_gt t (6 * a + 6 * L - (2 * L + 2 - 2 * N)) with c6 | c6
        · exact ⟨6, by norm_num, by norm_num, step 6 (by norm_num) (by omega) c6⟩
        · rcases le_or_gt t (7 * a + 7 * L - (2 * L + 2 - 2 * N)) with c7 | c7
          · exact ⟨7, by norm_num, by norm_num, step 7 (by norm_num) (by omega) c7⟩
          · rcases le_or_gt t (8 * a + 8 * L - (2 * L + 2 - 2 * N)) with c8 | c8
            · exact ⟨8, by norm_num, by norm_num, step 8 (by norm_num) (by omega) c8⟩
            · exact ⟨9, by norm_num, by norm_num, step 9 (by norm_num) (by omega) (by omega)⟩

/-- **Interval-chain covering, `d=1` sparse case** (blueprint §4.2). Same as `cover_d1_dense` but in
the `2N-3 ≤ L ≤ 3N-6` regime, using `lemma3_third` (even `h ∈ {4,6,8}`, `q ∈ {2,3,4}`), which needs
the Freiman bound `3N-3 ≤ |B+B|` (carried as a hypothesis). Since `d=1` the intervals are full (no
parity gap); a 3-way search over the abutting `I_4,I_6,I_8` finds the covering `h`. -/
lemma cover_d1_sparse (a L E t : ℕ) (B G : Finset ℕ)
    (hpull : ∀ b ∈ B, a + 1 * b ∈ G)
    (hBsub : B ⊆ Finset.Icc 0 L) (h0 : 0 ∈ B) (hLB : L ∈ B) (hN3 : 3 ≤ B.card)
    (hLlo : 2 * B.card - 3 ≤ L) (hLhi : L ≤ 3 * B.card - 6)
    (hFreiman : 3 * B.card - 3 ≤ (B + B).card)
    (ha1 : 1 ≤ a) (habE : a + L ≤ E)
    (hsize : E + 24 ≤ 3 * B.card) (htlo : 2 * E < t) (hthi : t < 3 * E) :
    ∃ h, 3 ≤ h ∧ h ≤ 9 ∧ hfold G h t := by
  set N := B.card with hN
  have hNL : N ≤ L + 1 := by
    rw [hN]; have := Finset.card_le_card hBsub; simpa [Nat.card_Icc] using this
  have hcov3 := lemma3_third B L hBsub h0 hLB hN3 hLlo hLhi hFreiman
  have step : ∀ q : ℕ, 2 ≤ q → 2 * q * a + (4 * L + 8 - 6 * N) ≤ t →
      t ≤ 2 * q * a + 2 * q * L - (4 * L + 8 - 6 * N) → hfold G (2 * q) t := by
    intro q hq2 hlo hhi
    have hHL : 4 * L ≤ 2 * q * L := Nat.mul_le_mul (by omega) (le_refl L)
    have hyf := hcov3 q hq2 (t - 2 * q * a) (by omega) (by omega)
    have hpb := hfold_pullback hpull hyf
    exact hfold_congr rfl (by omega) hpb
  rcases le_or_gt t (2 * 2 * a + 2 * 2 * L - (4 * L + 8 - 6 * N)) with c4 | c4
  · exact ⟨4, by norm_num, by norm_num, step 2 (by norm_num) (by omega) c4⟩
  · rcases le_or_gt t (2 * 3 * a + 2 * 3 * L - (4 * L + 8 - 6 * N)) with c6 | c6
    · exact ⟨6, by norm_num, by norm_num, step 3 (by norm_num) (by omega) c6⟩
    · exact ⟨8, by norm_num, by norm_num, step 4 (by norm_num) (by omega) (by omega)⟩

/-- **Interval-chain covering, `d=2`, `a` even** (blueprint §5.1). Here `L ≤ 2N-4` always holds, so only
`lemma2_dense` is needed; the intervals `I_h = {h a + 2y : Γ ≤ y ≤ hL-Γ}` are step-2 progressions of even
integers (`a` even). For even `t ∈ (2E,3E)`, the abutting `I_3,I_4,I_5` cover it (`h ∈ {3,4,5}`). -/
lemma cover_d2_even (a L E t : ℕ) (B G : Finset ℕ)
    (hpull : ∀ b ∈ B, a + 2 * b ∈ G)
    (hBsub : B ⊆ Finset.Icc 0 L) (h0 : 0 ∈ B) (hLB : L ∈ B) (hN3 : 3 ≤ B.card)
    (hdense : L ≤ 2 * B.card - 4) (ha1 : 1 ≤ a) (haeven : 2 ∣ a) (hab2E : a + 2 * L ≤ E)
    (hsize : E + 24 ≤ 3 * B.card) (ht2 : 2 ∣ t) (htlo : 2 * E < t) (hthi : t < 3 * E) :
    ∃ h, 3 ≤ h ∧ h ≤ 9 ∧ hfold G h t := by
  set N := B.card with hN
  have hNL : N ≤ L + 1 := by
    rw [hN]; have := Finset.card_le_card hBsub; simpa [Nat.card_Icc] using this
  have hcov := lemma2_dense B L hBsub h0 hLB hN3 hdense
  have step : ∀ h : ℕ, 2 ≤ h → h * a + 2 * (2 * L + 2 - 2 * N) ≤ t →
      t ≤ h * a + 2 * (h * L - (2 * L + 2 - 2 * N)) → hfold G h t := by
    intro h hh2 hlo hhi
    have hha : 2 ∣ (h * a) := haeven.mul_left h
    have hdvd : 2 ∣ (t - h * a) := by omega
    have hHL : 2 * L ≤ h * L := Nat.mul_le_mul hh2 (le_refl L)
    set Y := (t - h * a) / 2 with hY
    have h2y : 2 * Y = t - h * a := by rw [hY]; exact Nat.mul_div_cancel' hdvd
    have hyf := hcov h hh2 Y (by omega) (by omega)
    have hpb := hfold_pullback hpull hyf
    refine hfold_congr rfl ?_ hpb
    omega
  rcases le_or_gt t (3 * a + 2 * (3 * L - (2 * L + 2 - 2 * N))) with c3 | c3
  · exact ⟨3, by norm_num, by norm_num, step 3 (by norm_num) (by omega) c3⟩
  · rcases le_or_gt t (4 * a + 2 * (4 * L - (2 * L + 2 - 2 * N))) with c4 | c4
    · exact ⟨4, by norm_num, by norm_num, step 4 (by norm_num) (by omega) c4⟩
    · exact ⟨5, by norm_num, by norm_num, step 5 (by norm_num) (by omega) (by omega)⟩

/-- **Interval-chain covering, `d=2`, `a` odd** (blueprint §5.2). An `h`-term sum has parity `h·a ≡ h`
(`a` odd); since `t` is even only even `h` qualify, so `h ∈ {4,6}`. Again `L ≤ 2N-4`, `lemma2_dense`,
and the abutting even-lattice intervals `I_4,I_6` cover every even `t ∈ (2E,3E)`. -/
lemma cover_d2_odd (a L E t : ℕ) (B G : Finset ℕ)
    (hpull : ∀ b ∈ B, a + 2 * b ∈ G)
    (hBsub : B ⊆ Finset.Icc 0 L) (h0 : 0 ∈ B) (hLB : L ∈ B) (hN3 : 3 ≤ B.card)
    (hdense : L ≤ 2 * B.card - 4) (ha1 : 1 ≤ a) (hab2E : a + 2 * L ≤ E)
    (hsize : E + 24 ≤ 3 * B.card) (ht2 : 2 ∣ t) (htlo : 2 * E < t) (hthi : t < 3 * E) :
    ∃ h, 3 ≤ h ∧ h ≤ 9 ∧ hfold G h t := by
  set N := B.card with hN
  have hNL : N ≤ L + 1 := by
    rw [hN]; have := Finset.card_le_card hBsub; simpa [Nat.card_Icc] using this
  have hcov := lemma2_dense B L hBsub h0 hLB hN3 hdense
  have step : ∀ h : ℕ, 2 ≤ h → 2 ∣ h → h * a + 2 * (2 * L + 2 - 2 * N) ≤ t →
      t ≤ h * a + 2 * (h * L - (2 * L + 2 - 2 * N)) → hfold G h t := by
    intro h hh2 hheven hlo hhi
    have hha : 2 ∣ (h * a) := hheven.mul_right a
    have hdvd : 2 ∣ (t - h * a) := by omega
    have hHL : 2 * L ≤ h * L := Nat.mul_le_mul hh2 (le_refl L)
    set Y := (t - h * a) / 2 with hY
    have h2y : 2 * Y = t - h * a := by rw [hY]; exact Nat.mul_div_cancel' hdvd
    have hyf := hcov h hh2 Y (by omega) (by omega)
    have hpb := hfold_pullback hpull hyf
    refine hfold_congr rfl ?_ hpb
    omega
  rcases le_or_gt t (4 * a + 2 * (4 * L - (2 * L + 2 - 2 * N))) with c4 | c4
  · exact ⟨4, by norm_num, by norm_num, step 4 (by norm_num) (by norm_num) (by omega) c4⟩
  · exact ⟨6, by norm_num, by norm_num, step 6 (by norm_num) (by norm_num) (by omega) (by omega)⟩

/-- **Normalized covering** — combines the four interval-chain cases. Given normalized data
`(a,d,L,B)` with `d ∈ {1,2}`, the lift `∀ b∈B, a+d·b ∈ G`, `B ⊆ [0,L]` with `0,L ∈ B`, `|B|≥3`,
`1≤a`, `a+d·L ≤ E`, size `E+24 ≤ 3|B|`, and the Freiman bound `3|B|-3 ≤ |B+B|` (used only in the
`d=1` sparse sub-case), every even `t ∈ (2E,3E)` is in `hG` for some `3 ≤ h ≤ 9`. -/
lemma covering_normalized (a d L E t : ℕ) (B G : Finset ℕ)
    (hd12 : d = 1 ∨ d = 2)
    (hpull : ∀ b ∈ B, a + d * b ∈ G)
    (hBsub : B ⊆ Finset.Icc 0 L) (h0 : 0 ∈ B) (hLB : L ∈ B) (hN3 : 3 ≤ B.card)
    (ha1 : 1 ≤ a) (habE : a + d * L ≤ E) (hsize : E + 24 ≤ 3 * B.card)
    (hFreiman : 2 * B.card - 3 ≤ L → 3 * B.card - 3 ≤ (B + B).card)
    (ht2 : 2 ∣ t) (htlo : 2 * E < t) (hthi : t < 3 * E) :
    ∃ h, 3 ≤ h ∧ h ≤ 9 ∧ hfold G h t := by
  rcases hd12 with rfl | rfl
  · -- d = 1
    rcases le_or_gt L (2 * B.card - 4) with hdense | hsparse
    · exact cover_d1_dense a L E t B G hpull hBsub h0 hLB hN3 hdense ha1 (by omega) hsize htlo hthi
    · have hLlo : 2 * B.card - 3 ≤ L := by omega
      have hLhi : L ≤ 3 * B.card - 6 := by omega
      exact cover_d1_sparse a L E t B G hpull hBsub h0 hLB hN3 hLlo hLhi (hFreiman hLlo) ha1 (by omega)
        hsize htlo hthi
  · -- d = 2
    have hdense : L ≤ 2 * B.card - 4 := by omega
    rcases Nat.even_or_odd a with haev | haodd
    · exact cover_d2_even a L E t B G hpull hBsub h0 hLB hN3 hdense ha1 haev.two_dvd habE hsize
        ht2 htlo hthi
    · exact cover_d2_odd a L E t B G hpull hBsub h0 hLB hN3 hdense ha1 habE hsize ht2 htlo hthi

/-- **hLev — the full covering theorem.** For `G ⊆ [1,E]` with `|G| ≥ 3` and the size bound
`E+24 ≤ 3|G|` (i.e. `|G| ≥ E/3 + 8`), assuming Freiman's `3k-3` theorem (carried as the hypothesis
`hFreiman`, the one cited fact — regime (c), NOT an axiom), every even `t ∈ (2E,3E)` is a sum of at
most `9` elements of `G` (repetitions allowed). This discharges `basile71`'s `hLev` (with `h ≤ 9 ≤ 11`),
using ONLY the size + range of `G` — the good-core midpoint richness and `3∤t` are not needed. -/
theorem hLev_covering (E : ℕ) (G : Finset ℕ) (hGsub : G ⊆ Finset.Icc 1 E) (hG3 : 3 ≤ G.card)
    (hsize : E + 24 ≤ 3 * G.card)
    (hFreiman : ∀ (B' : Finset ℕ) (L' : ℕ), B' ⊆ Finset.Icc 0 L' → 0 ∈ B' → L' ∈ B' →
      3 ≤ B'.card → 2 * B'.card - 3 ≤ L' → B'.gcd id = 1 → 3 * B'.card - 3 ≤ (B' + B').card)
    (t : ℕ) (ht2 : 2 ∣ t) (htlo : 2 * E < t) (hthi : t < 3 * E) :
    ∃ h, 3 ≤ h ∧ h ≤ 9 ∧ hfold G h t := by
  obtain ⟨a, d, L, B, hdpos, ha1, habE, hBcard, hpull, h0, hLB, hBsub, hgcdB⟩ :=
    normalize_setup E G hGsub hG3
  have hN3 : 3 ≤ B.card := by rw [hBcard]; exact hG3
  have hsizeB : E + 24 ≤ 3 * B.card := by rw [hBcard]; exact hsize
  have hNL : B.card ≤ L + 1 := by
    have := Finset.card_le_card hBsub; simpa [Nat.card_Icc] using this
  have hd2 : d ≤ 2 := gcd_le_two hdpos hNL (by omega) hsizeB
  exact covering_normalized a d L E t B G (by omega) hpull hBsub h0 hLB hN3 ha1 habE hsizeB
    (fun hL => hFreiman B L hBsub h0 hLB hN3 hL hgcdB) ht2 htlo hthi

#print axioms hLev_covering

#print axioms covering_normalized

#print axioms cover_d2_even
#print axioms cover_d2_odd

#print axioms normalize_setup

#print axioms hfold_zero
#print axioms hfold_add_copies
#print axioms hfold_two
#print axioms hfold_add
#print axioms hfold_sumset
#print axioms hfold_pullback
#print axioms modular_rep
#print axioms lemma2_dense
#print axioms lemma3_third

end Erdos361Covering
