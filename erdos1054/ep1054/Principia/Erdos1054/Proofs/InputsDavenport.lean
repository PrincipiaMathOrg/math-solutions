/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Density
import Principia.Erdos1054.Statements.Inputs
import Principia.Common.Davenport.Concentration

set_option autoImplicit false

/-!
# EP1054: Davenport's theorem in progressions — the `InputsDavenport` package of the spine

Discharges `Principia.Erdos1054.Cite_PollackAP` (Pollack, *Integers* 15A (2015), Lemma 2; paper
`Campaigns/Erdos-1054/collab-paper/EP1054.tex`, §7, lines 2733–2748):

  for every `Q > 0` and residue `a` there is a **continuous** `D` with `D(u) → 1` (`u → ∞`) and
  `HasDens {n : n ≡ a (mod Q), σ(n)/n ≤ u} (D(u)/Q)` for **every** real `u`.

With `D(u) := Q · upperDens {n ≡ a, h(n) ≤ u}` (`h = σ(n)/n`) the proof has three ingredients.

1. **Existence of the density at every `u`, given no concentration.** The truncation
   `h_K(n) = ∑_{d ≤ K, d ∣ n} 1/d ≤ h(n)` is periodic mod `Q · K!`, so `{n ≡ a, h_K(n) ≤ v}` has a
   density (`hasDens_of_periodic`). Since `{h ≤ u − ε} ⊆ {h_K ≤ u − ε} ⊆ {h ≤ u} ∪ {h − h_K > ε}`
   and the last set has upper density `≤ 2/((K+1)ε)` (Markov, `Common.Davenport.card_tail_gt_le`),
   `upperDens {h ≤ u − ε} ≤ lowerDens {h ≤ u}` for every `ε > 0`
   (`upperDens_shift_le_lowerDens`). The gap `upperDens {h ≤ u} − upperDens {h ≤ u − ε}` is at most
   the upper density of `{|h − u| ≤ ε}`, which no-concentration makes arbitrarily small
   (`hasDens_Aset`).
2. **Continuity of `D`** is the same no-concentration statement
   (`Common.Davenport.eventually_card_abund_near_le`: for every `c`, `η > 0` there is `δ > 0`
   with `upperDens {|h − c| ≤ δ} ≤ η`), proved from the divergence of `∑ 1/p` alone
   (`continuous_upperDens_Aset`).
3. **`D → 1`**: `D ≤ Q · dens{n ≡ a} = 1`, and `D(u) ≥ 1 − 2Q/u` because
   `upperDens {h > u} ≤ 2/u` (Markov with `∑_{n ≤ X} h(n) ≤ 2X`).

The class of `n = 0` plays no role (`cnt` counts from `1`); the lemmas `upperDens_le_of_pos` and
`lowerDens_le_of_pos` make that explicit. `Cite_Davenport` (the `Q = 1` case) is recorded as
`davenport`.
-/

namespace Principia.Erdos1054.Proofs.InputsDavenport

open Filter Finset
open scoped Topology
open Principia.Common.Davenport

theorem abundancy_eq_abund (n : ℕ) : abundancy n = abund n := rfl

/-! ## Bridges between `cnt`/densities and plain finset counts -/

/-- `cnt S X ≤ #{1 ≤ n ≤ X : p n}` whenever every `n ≥ 1` in `S` satisfies `p`. -/
theorem cnt_le_card_filter {S : Set ℕ} (p : ℕ → Prop) [DecidablePred p]
    (h : ∀ n, 1 ≤ n → n ∈ S → p n) (X : ℕ) :
    cnt S (X : ℝ) ≤ ((Icc 1 X).filter p).card := by
  rw [cnt_natCast]
  apply Finset.card_le_card
  intro n hn
  rw [mem_cntFinset] at hn
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨hn.1, h n hn.1.1 hn.2⟩

/-- An eventual count bound `#{1 ≤ n ≤ X : p n} ≤ c X` bounds the upper density. -/
theorem upperDens_le_of_card {S : Set ℕ} (p : ℕ → Prop) [DecidablePred p]
    (h : ∀ n, 1 ≤ n → n ∈ S → p n) {c : ℝ}
    (hc : ∀ᶠ X : ℕ in atTop, (((Icc 1 X).filter p).card : ℝ) ≤ c * X) :
    upperDens S ≤ c := by
  apply upperDens_le_of_eventually
  filter_upwards [hc] with X hX
  exact le_trans (by exact_mod_cast cnt_le_card_filter p h X) hX

theorem subset_union_zero_of_pos {S T : Set ℕ} (h : ∀ n, 1 ≤ n → n ∈ S → n ∈ T) :
    S ⊆ T ∪ {0} := by
  intro n hn
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · exact Or.inr h0
  · exact Or.inl (h n h0 hn)

/-- Upper densities only see `n ≥ 1`. -/
theorem upperDens_le_of_pos {S T : Set ℕ} (h : ∀ n, 1 ≤ n → n ∈ S → n ∈ T) :
    upperDens S ≤ upperDens T :=
  (upperDens_mono (subset_union_zero_of_pos h)).trans
    (upperDens_union_of_densZero T (densZero_of_finite (Set.finite_singleton 0))).le

/-- Lower densities only see `n ≥ 1`. -/
theorem lowerDens_le_of_pos {S T : Set ℕ} (h : ∀ n, 1 ≤ n → n ∈ S → n ∈ T) :
    lowerDens S ≤ lowerDens T :=
  (lowerDens_mono (subset_union_zero_of_pos h)).trans
    (lowerDens_union_of_densZero T (densZero_of_finite (Set.finite_singleton 0))).le

/-! ## Density forms of the `Common.Davenport` count bounds -/

/-- **Markov, density form.** `upperDens {h − h_K > ε} ≤ 2/((K+1)ε)`. -/
theorem upperDens_tail_le (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    upperDens {n : ℕ | ε < abundancy n - abundTrunc K n} ≤ 2 / ((K + 1) * ε) := by
  apply upperDens_le_of_card (fun n => ε < abund n - abundTrunc K n) (fun n _ hn => hn)
  refine Eventually.of_forall fun X => ?_
  calc (((Icc 1 X).filter (fun n => ε < abund n - abundTrunc K n)).card : ℝ)
      ≤ X * (2 / (K + 1)) / ε := card_tail_gt_le K X hε
    _ = 2 / ((K + 1) * ε) * X := by rw [← div_div]; ring

/-- `upperDens {h > u} ≤ 2/u`. -/
theorem upperDens_abund_gt_le {u : ℝ} (hu : 0 < u) :
    upperDens {n : ℕ | u < abundancy n} ≤ 2 / u := by
  apply upperDens_le_of_card (fun n => u < abund n) (fun n _ hn => hn)
  refine Eventually.of_forall fun X => ?_
  calc (((Icc 1 X).filter (fun n => u < abund n)).card : ℝ) ≤ 2 * X / u := card_abund_gt_le X hu
    _ = 2 / u * X := by ring

/-- **No concentration, density form (Davenport's continuity).** -/
theorem exists_upperDens_near_le (c : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ upperDens {n : ℕ | |abundancy n - c| ≤ δ} ≤ η := by
  obtain ⟨δ, hδ, hev⟩ := eventually_card_abund_near_le c hη
  exact ⟨δ, hδ, upperDens_le_of_card (fun n => |abund n - c| ≤ δ) (fun n _ hn => hn) hev⟩

/-! ## The truncated sets are periodic -/

theorem hasDens_trunc (Q a K : ℕ) (hQ : 0 < Q) (v : ℝ) :
    ∃ d : ℝ, HasDens {n : ℕ | n % Q = a % Q ∧ abundTrunc K n ≤ v} d := by
  have hL : 0 < Q * K.factorial := Nat.mul_pos hQ (Nat.factorial_pos K)
  refine ⟨_, hasDens_of_periodic hL fun N => ?_⟩
  simp only [Set.mem_setOf_eq]
  rw [Nat.add_mul_mod_self_left, abundTrunc_add_of_dvd K N (Q * K.factorial)
    (fun d hd => (dvd_factorial_of_mem_Icc K d hd).mul_left Q)]

/-! ## The sets `{n ≡ a (mod Q) : σ(n)/n ≤ u}` -/

/-- `{n : n ≡ a (mod Q), σ(n)/n ≤ u}`. -/
def Aset (Q a : ℕ) (u : ℝ) : Set ℕ := {n : ℕ | n % Q = a % Q ∧ abundancy n ≤ u}

theorem Aset_mono (Q a : ℕ) {u v : ℝ} (h : u ≤ v) : Aset Q a u ⊆ Aset Q a v :=
  fun _ hn => ⟨hn.1, hn.2.trans h⟩

/-- **Step 1.** `upperDens {h ≤ u − ε} ≤ lowerDens {h ≤ u}` (in the class `a mod Q`). -/
theorem upperDens_shift_le_lowerDens (Q a : ℕ) (hQ : 0 < Q) (u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    upperDens (Aset Q a (u - ε)) ≤ lowerDens (Aset Q a u) := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / (ε * η))
  obtain ⟨d, hd⟩ := hasDens_trunc Q a K hQ (u - ε)
  have h1 : upperDens (Aset Q a (u - ε)) ≤
      upperDens {n : ℕ | n % Q = a % Q ∧ abundTrunc K n ≤ u - ε} :=
    upperDens_le_of_pos fun n hn hA =>
      ⟨hA.1, (abundTrunc_le_abund K n (by omega)).trans hA.2⟩
  have h2 : lowerDens {n : ℕ | n % Q = a % Q ∧ abundTrunc K n ≤ u - ε} ≤
      lowerDens ({n : ℕ | ε < abundancy n - abundTrunc K n} ∪ Aset Q a u) :=
    lowerDens_le_of_pos fun n _ hS => by
      by_cases hu : abundancy n ≤ u
      · exact Or.inr ⟨hS.1, hu⟩
      · refine Or.inl ?_
        rw [not_le] at hu
        change ε < abundancy n - abundTrunc K n
        linarith [hS.2]
  have h3 := lowerDens_union_le {n : ℕ | ε < abundancy n - abundTrunc K n} (Aset Q a u)
  have h4 := upperDens_tail_le K hε
  have h5 : 2 / ((K + 1) * ε) ≤ η := by
    have hεη : 0 < ε * η := mul_pos hε hη
    have hK' : 2 < (K : ℝ) * (ε * η) := (div_lt_iff₀ hεη).1 hK
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rw [hd.upperDens_eq] at h1
  rw [hd.lowerDens_eq] at h2
  linarith

/-- **Step 2.** `{n ≡ a : h(n) ≤ u}` has a density, namely its upper density. -/
theorem hasDens_Aset (Q a : ℕ) (hQ : 0 < Q) (u : ℝ) :
    HasDens (Aset Q a u) (upperDens (Aset Q a u)) := by
  rw [hasDens_iff]
  refine ⟨le_antisymm (lowerDens_le_upperDens _) ?_, rfl⟩
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨δ, hδ, hW⟩ := exists_upperDens_near_le u hη
  have h1 : Aset Q a u ⊆ Aset Q a (u - δ) ∪ {n : ℕ | |abundancy n - u| ≤ δ} := by
    intro n hn
    by_cases h : abundancy n ≤ u - δ
    · exact Or.inl ⟨hn.1, h⟩
    · refine Or.inr ?_
      rw [not_le] at h
      change |abundancy n - u| ≤ δ
      rw [abs_le]
      constructor
      · linarith
      · linarith [hn.2]
  have h2 := (upperDens_mono h1).trans (upperDens_union_le _ _)
  have h3 := upperDens_shift_le_lowerDens Q a hQ u hδ
  linarith

/-- The window estimate: `upperDens (A v) ≤ upperDens (A u) + upperDens {|h − c| ≤ δ}` when
`(u, v]` lies within `δ` of `c`. -/
theorem upperDens_Aset_le_add (Q a : ℕ) {u v : ℝ} (c δ : ℝ)
    (hwin : ∀ x : ℝ, u < x → x ≤ v → |x - c| ≤ δ) :
    upperDens (Aset Q a v) ≤
      upperDens (Aset Q a u) + upperDens {n : ℕ | |abundancy n - c| ≤ δ} := by
  have h1 : Aset Q a v ⊆ Aset Q a u ∪ {n : ℕ | |abundancy n - c| ≤ δ} := by
    intro n hn
    by_cases h : abundancy n ≤ u
    · exact Or.inl ⟨hn.1, h⟩
    · rw [not_le] at h
      exact Or.inr (hwin _ h hn.2)
  exact (upperDens_mono h1).trans (upperDens_union_le _ _)

/-- **Step 3 (continuity).** `u ↦ upperDens {n ≡ a : h(n) ≤ u}` is continuous. -/
theorem continuous_upperDens_Aset (Q a : ℕ) :
    Continuous (fun u : ℝ => upperDens (Aset Q a u)) := by
  rw [Metric.continuous_iff]
  intro c η hη
  obtain ⟨δ, hδ, hW⟩ := exists_upperDens_near_le c (half_pos hη)
  refine ⟨δ, hδ, fun v hv => ?_⟩
  show dist (upperDens (Aset Q a v)) (upperDens (Aset Q a c)) < η
  rw [Real.dist_eq] at hv ⊢
  rw [abs_lt] at hv
  obtain ⟨hv1, hv2⟩ := hv
  rcases le_total c v with h | h
  · have hmono := upperDens_mono (Aset_mono Q a h)
    have hup := upperDens_Aset_le_add Q a (u := c) (v := v) c δ fun x hx1 hx2 => by
      rw [abs_le]
      constructor <;> linarith
    rw [abs_lt]
    constructor <;> linarith
  · have hmono := upperDens_mono (Aset_mono Q a h)
    have hup := upperDens_Aset_le_add Q a (u := v) (v := c) c δ fun x hx1 hx2 => by
      rw [abs_le]
      constructor <;> linarith
    rw [abs_lt]
    constructor <;> linarith

/-- The progression `{n ≡ a (mod Q)}` has density `1/Q`. -/
theorem hasDens_AP (Q a : ℕ) (hQ : 0 < Q) : HasDens {n : ℕ | n % Q = a % Q} (1 / Q) := by
  have h := hasDens_mod_mem hQ {a % Q} (fun x hx => by
    rw [Finset.mem_singleton] at hx
    rw [hx]
    exact Nat.mod_lt a hQ)
  have hset : {N : ℕ | N % Q ∈ ({a % Q} : Finset ℕ)} = {n : ℕ | n % Q = a % Q} := by
    ext N
    simp only [Set.mem_setOf_eq, Finset.mem_singleton]
  rw [hset, Finset.card_singleton, Nat.cast_one] at h
  exact h

theorem upperDens_Aset_le (Q a : ℕ) (hQ : 0 < Q) (u : ℝ) :
    upperDens (Aset Q a u) ≤ 1 / (Q : ℝ) := by
  have h := upperDens_mono (show Aset Q a u ⊆ {n : ℕ | n % Q = a % Q} from fun _ hn => hn.1)
  rwa [(hasDens_AP Q a hQ).upperDens_eq] at h

theorem upperDens_Aset_ge (Q a : ℕ) (hQ : 0 < Q) {u : ℝ} (hu : 0 < u) :
    1 / (Q : ℝ) - 2 / u ≤ upperDens (Aset Q a u) := by
  have hB := upperDens_abund_gt_le hu
  have h1 : {n : ℕ | n % Q = a % Q} ⊆ {n : ℕ | u < abundancy n} ∪ Aset Q a u := by
    intro n hn
    by_cases h : abundancy n ≤ u
    · exact Or.inr ⟨hn, h⟩
    · rw [not_le] at h
      exact Or.inl h
  have h2 := (lowerDens_mono h1).trans (lowerDens_union_le _ _)
  rw [(hasDens_AP Q a hQ).lowerDens_eq] at h2
  have h3 := lowerDens_le_upperDens (Aset Q a u)
  linarith

/-- **Davenport's theorem in arithmetic progressions** (Pollack, Lemma 2), in the encoding of
`Cite_PollackAP`. -/
theorem pollackAP (Q : ℕ) (hQ : 0 < Q) (a : ℕ) :
    ∃ D : ℝ → ℝ, Continuous D ∧ Tendsto D atTop (𝓝 1) ∧
      ∀ u : ℝ, HasDens {n : ℕ | n % Q = a % Q ∧ abundancy n ≤ u} (D u / Q) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  refine ⟨fun u => (Q : ℝ) * upperDens (Aset Q a u), ?_, ?_, fun u => ?_⟩
  · exact continuous_const.mul (continuous_upperDens_Aset Q a)
  · have h0 : Tendsto (fun u : ℝ => 2 * (Q : ℝ) / u) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
    have hlo : Tendsto (fun u : ℝ => 1 - 2 * (Q : ℝ) / u) atTop (𝓝 1) := by
      have h1 := h0.const_sub 1
      rwa [sub_zero] at h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with u hu
      have h1 := upperDens_Aset_ge Q a hQ hu
      have e : (Q : ℝ) * (1 / Q - 2 / u) = 1 - 2 * Q / u := by
        rw [mul_sub, mul_one_div_cancel hQR.ne']
        ring
      calc 1 - 2 * (Q : ℝ) / u = Q * (1 / Q - 2 / u) := e.symm
        _ ≤ Q * upperDens (Aset Q a u) := mul_le_mul_of_nonneg_left h1 hQR.le
    · refine Eventually.of_forall fun u => ?_
      have h1 := upperDens_Aset_le Q a hQ u
      calc (Q : ℝ) * upperDens (Aset Q a u) ≤ Q * (1 / Q) := mul_le_mul_of_nonneg_left h1 hQR.le
        _ = 1 := mul_one_div_cancel hQR.ne'
  · change HasDens (Aset Q a u) ((Q : ℝ) * upperDens (Aset Q a u) / Q)
    rw [mul_div_cancel_left₀ _ hQR.ne']
    exact hasDens_Aset Q a hQ u

/-- **Davenport's theorem** (`Q = 1`): `Cite_Davenport`. -/
theorem davenport : Principia.Erdos1054.Cite_Davenport := by
  obtain ⟨D, hc, ht, hd⟩ := pollackAP 1 one_pos 0
  exact ⟨D, hc, ht, fun u => by simpa [Nat.mod_one] using hd u⟩

end Principia.Erdos1054.Proofs.InputsDavenport

namespace Principia.Erdos1054.Proofs

/-- **`Cite_PollackAP`**, discharged: Davenport's theorem in arithmetic progressions, with
continuity from the divergence of `∑ 1/p` (`Principia.Common.Davenport`). -/
theorem input_Cite_PollackAP : Principia.Erdos1054.Cite_PollackAP :=
  fun Q hQ a => InputsDavenport.pollackAP Q hQ a

end Principia.Erdos1054.Proofs
