import Mathlib
open Finset
open scoped Classical

/-!
# Erdős #361 — greedy independent set in a bounded-degree 3-uniform hypergraph (Lemma 2.4 core)
Proven axiom-free (2026-07-28). Feeds `hypergraph_indep` → the good/bad split → `hAlon`.
-/

/-- Greedy independent set in a 3-uniform hypergraph of bounded degree.
`D` = edge set (each edge a 3-element `Finset ℕ`); an independent `I` contains no edge.
If for every `v` the closed edge-neighbourhood has size `≤ N` (`3·deg(v)+1 ≤ N`), then every vertex set
`C'` has an independent subset `I` with `|C'| ≤ N·|I|`. Deterministic strong induction: pick `v`, delete
its closed neighbourhood `nb`, recurse. -/
lemma greedy_indep (D : Finset (Finset ℕ)) (N : ℕ)
    (hd3 : ∀ e ∈ D, e.card = 3)
    (hdeg : ∀ v : ℕ, 3 * (D.filter (fun e => v ∈ e)).card + 1 ≤ N) :
    ∀ C' : Finset ℕ, ∃ I ⊆ C', (∀ e ∈ D, ¬ e ⊆ I) ∧ C'.card ≤ N * I.card := by
  intro C'
  induction C' using Finset.strongInduction with
  | _ C' ih =>
    rcases C'.eq_empty_or_nonempty with hE | hne
    · refine ⟨∅, by simp, ?_, by simp [hE]⟩
      intro e he hsub
      rw [Finset.subset_empty] at hsub
      have h3 := hd3 e he; rw [hsub] at h3; simp at h3
    · obtain ⟨v, hv⟩ := hne
      set nb : Finset ℕ := insert v ((D.filter (fun e => v ∈ e)).biUnion id) with hnb
      have hnbcard : nb.card ≤ N := by
        calc nb.card ≤ ((D.filter (fun e => v ∈ e)).biUnion id).card + 1 := by
              rw [hnb]; exact Finset.card_insert_le _ _
          _ ≤ (∑ e ∈ D.filter (fun e => v ∈ e), (id e).card) + 1 :=
              Nat.add_le_add_right (Finset.card_biUnion_le) 1
          _ = 3 * (D.filter (fun e => v ∈ e)).card + 1 := by
              rw [Finset.sum_congr rfl (fun e he => by
                simp only [id_eq]; exact hd3 e (Finset.mem_of_mem_filter e he))]
              rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
          _ ≤ N := hdeg v
      have hvnb : v ∈ nb := by rw [hnb]; exact Finset.mem_insert_self _ _
      set C'' : Finset ℕ := C' \ nb with hC''
      have hss : C'' ⊂ C' := by
        refine ⟨Finset.sdiff_subset, fun hsup => ?_⟩
        exact (Finset.mem_sdiff.mp (hsup hv)).2 hvnb
      obtain ⟨I', hI'sub, hI'ind, hI'card⟩ := ih C'' hss
      have hvI' : v ∉ I' := fun h => (Finset.mem_sdiff.mp (hI'sub h)).2 hvnb
      refine ⟨insert v I', ?_, ?_, ?_⟩
      · exact Finset.insert_subset hv (hI'sub.trans (Finset.sdiff_subset))
      · intro e he hesub
        by_cases hve : v ∈ e
        · -- e ⊆ nb, so its ≠v vertex lands in I' ∩ nb = ∅
          obtain ⟨u, hue, huv⟩ : ∃ u ∈ e, u ≠ v := by
            have h3 := hd3 e he
            by_contra hcon; push_neg at hcon
            have : e ⊆ {v} := fun x hx => Finset.mem_singleton.mpr (hcon x hx)
            have := Finset.card_le_card this
            simp at this; omega
          have huI' : u ∈ I' := by
            have := hesub hue
            rcases Finset.mem_insert.mp this with h | h
            · exact absurd h huv
            · exact h
          have hunb : u ∈ nb := by
            rw [hnb]; refine Finset.mem_insert_of_mem ?_
            exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hve⟩, hue⟩
          exact (Finset.mem_sdiff.mp (hI'sub huI')).2 hunb
        · have : e ⊆ I' := by
            intro x hx
            rcases Finset.mem_insert.mp (hesub hx) with h | h
            · exact absurd (h ▸ hx) hve
            · exact h
          exact hI'ind e he this
      · have hcardI : (insert v I').card = I'.card + 1 := Finset.card_insert_of_notMem hvI'
        have hCsub : C' ⊆ C'' ∪ nb := by
          intro x hx
          by_cases hxnb : x ∈ nb
          · exact Finset.mem_union_right _ hxnb
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxnb⟩)
        calc C'.card ≤ (C'' ∪ nb).card := Finset.card_le_card hCsub
          _ ≤ C''.card + nb.card := Finset.card_union_le _ _
          _ ≤ N * I'.card + N := Nat.add_le_add hI'card hnbcard
          _ = N * (I'.card + 1) := by ring
          _ = N * (insert v I').card := by rw [hcardI]

#print axioms greedy_indep

/-- **Alon's Lemma 2.4** (sparse 3-uniform hypergraph has a large independent set), via a degree
restriction + `greedy_indep`. `D` = edges (each a 3-element subset of `C`), `|D| ≤ ℓ|C|`; then there is
an independent `I ⊆ C` with `|C| ≤ (36ℓ+2)|I|`. -/
lemma hypergraph_indep (C : Finset ℕ) (D : Finset (Finset ℕ)) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hd3 : ∀ e ∈ D, e ⊆ C ∧ e.card = 3) (hDcard : D.card ≤ ℓ * C.card) :
    ∃ I ⊆ C, (∀ e ∈ D, ¬ e ⊆ I) ∧ C.card ≤ (36 * ℓ + 2) * I.card := by
  classical
  -- degree double-counting: ∑_{v∈C} deg v = 3|D|
  have hsum : ∑ v ∈ C, (D.filter (fun e => v ∈ e)).card = 3 * D.card := by
    have key : ∀ e ∈ D, (∑ v ∈ C, if v ∈ e then (1:ℕ) else 0) = 3 := by
      intro e he
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.mpr (hd3 e he).1]
      exact (hd3 e he).2
    calc ∑ v ∈ C, (D.filter (fun e => v ∈ e)).card
        = ∑ v ∈ C, ∑ e ∈ D, (if v ∈ e then (1:ℕ) else 0) := by simp_rw [Finset.card_filter]
      _ = ∑ e ∈ D, ∑ v ∈ C, (if v ∈ e then (1:ℕ) else 0) := Finset.sum_comm
      _ = ∑ e ∈ D, 3 := Finset.sum_congr rfl key
      _ = 3 * D.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- high-degree vertices are few
  set Chi : Finset ℕ := C.filter (fun v => 6 * ℓ < (D.filter (fun e => v ∈ e)).card) with hChi
  set Clo : Finset ℕ := C.filter (fun v => (D.filter (fun e => v ∈ e)).card ≤ 6 * ℓ) with hClo
  have hpart : Chi.card + Clo.card = C.card := by
    rw [hChi, hClo]
    have := Finset.filter_card_add_filter_neg_card_eq_card
      (s := C) (p := fun v => 6 * ℓ < (D.filter (fun e => v ∈ e)).card)
    simpa using this
  have hChihi : (6 * ℓ + 1) * Chi.card ≤ 3 * D.card := by
    calc (6 * ℓ + 1) * Chi.card = ∑ _v ∈ Chi, (6 * ℓ + 1) := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ Chi, (D.filter (fun e => v ∈ e)).card :=
          Finset.sum_le_sum (fun v hv => by have := (Finset.mem_filter.mp hv).2; omega)
      _ ≤ ∑ v ∈ C, (D.filter (fun e => v ∈ e)).card :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = 3 * D.card := hsum
  have hClo2 : C.card ≤ 2 * Clo.card := by
    have h3 : 3 * D.card ≤ 3 * ℓ * C.card := by
      have := hDcard; nlinarith [hDcard]
    have hkey : 2 * ((6 * ℓ + 1) * Chi.card) ≤ (6 * ℓ + 1) * C.card := by nlinarith [hChihi, h3]
    have : 2 * Chi.card ≤ C.card := by
      have h6 : 0 < 6 * ℓ + 1 := by omega
      have := hkey; nlinarith [this, h6]
    omega
  -- restrict edges to Clo and apply greedy
  set Dlo : Finset (Finset ℕ) := D.filter (fun e => e ⊆ Clo) with hDlo
  obtain ⟨I, hIsub, hIind, hIcard⟩ := greedy_indep Dlo (18 * ℓ + 1)
    (fun e he => (hd3 e (Finset.mem_of_mem_filter e he)).2)
    (fun v => by
      by_cases hvC : v ∈ Clo
      · have hle : (Dlo.filter (fun e => v ∈ e)).card
            ≤ (D.filter (fun e => v ∈ e)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
        have hd := (Finset.mem_filter.mp hvC).2
        omega
      · have hemp : Dlo.filter (fun e => v ∈ e) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro e he hve
          exact hvC ((Finset.mem_filter.mp he).2 hve)
        rw [hemp]; simp) Clo
  refine ⟨I, hIsub.trans (Finset.filter_subset _ _), ?_, ?_⟩
  · intro e he hesub
    exact hIind e (Finset.mem_filter.mpr ⟨he, hesub.trans hIsub⟩) hesub
  · calc C.card ≤ 2 * Clo.card := hClo2
      _ ≤ 2 * ((18 * ℓ + 1) * I.card) := by
          have := hIcard; omega
      _ = (36 * ℓ + 2) * I.card := by ring

#print axioms hypergraph_indep

open scoped Classical in
/-- **Good/bad split** (Alon Prop 2.5). With `A ⊆ [1,E]`, the "bad" set `C` of elements that are the
midpoint of `≤ 10` three-term APs of `A` satisfies `|C| ≤ 362·r₃(E+1)`. Builds the AP-hypergraph on `C`
(edges `{x,y,2y-x}`), bounds it by `10|C|` via the midpoint fibers, and turns independence into
`ThreeAPFree`. -/
lemma good_core_split (E : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 E) :
    (A.filter (fun a => (A.filter (fun x => x < a ∧ 2 * a - x ∈ A)).card ≤ 10)).card
      ≤ 362 * rothNumberNat (E + 1) := by
  set C : Finset ℕ := A.filter (fun a => (A.filter (fun x => x < a ∧ 2 * a - x ∈ A)).card ≤ 10)
    with hCdef
  have hCA : C ⊆ A := Finset.filter_subset _ _
  -- the AP-hypergraph on C
  set D : Finset (Finset ℕ) :=
    C.biUnion (fun y => (C.filter (fun x => x < y ∧ 2 * y - x ∈ C)).image
      (fun x => ({x, y, 2 * y - x} : Finset ℕ))) with hDdef
  have hd3 : ∀ e ∈ D, e ⊆ C ∧ e.card = 3 := by
    intro e he
    rw [hDdef, Finset.mem_biUnion] at he
    obtain ⟨y, hyC, he⟩ := he
    rw [Finset.mem_image] at he
    obtain ⟨x, hx, rfl⟩ := he
    rw [Finset.mem_filter] at hx
    obtain ⟨hxC, hxy, hzC⟩ := hx
    refine ⟨?_, ?_⟩
    · intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact hxC
      · exact hyC
      · exact hzC
    · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton]; omega
      · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hDcard : D.card ≤ 10 * C.card := by
    calc D.card ≤ ∑ y ∈ C, ((C.filter (fun x => x < y ∧ 2 * y - x ∈ C)).image
              (fun x => ({x, y, 2 * y - x} : Finset ℕ))).card := Finset.card_biUnion_le
      _ ≤ ∑ y ∈ C, (C.filter (fun x => x < y ∧ 2 * y - x ∈ C)).card :=
            Finset.sum_le_sum (fun y _ => Finset.card_image_le)
      _ ≤ ∑ y ∈ C, 10 := by
            refine Finset.sum_le_sum (fun y hyC => ?_)
            have hsub : C.filter (fun x => x < y ∧ 2 * y - x ∈ C)
                ⊆ A.filter (fun x => x < y ∧ 2 * y - x ∈ A) := by
              intro x hx
              rw [Finset.mem_filter] at hx ⊢
              exact ⟨hCA hx.1, hx.2.1, hCA hx.2.2⟩
            have hle := Finset.card_le_card hsub
            have h10 := (Finset.mem_filter.mp hyC).2
            omega
      _ = 10 * C.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  obtain ⟨I, hIC, hIind, hIcard⟩ := hypergraph_indep C D 10 (by norm_num) hd3 hDcard
  have hIfree : ThreeAPFree (I : Set ℕ) := by
    rw [threeAPFree_iff_eq_right]
    intro a ha b hb c hc habc
    by_contra hac
    have hkey : ∀ x z : ℕ, x ∈ I → z ∈ I → x < z → x + z = b + b → False := by
      intro x z hx hz hxz hxz2
      have hzeq : 2 * b - x = z := by omega
      have hmem : ({x, b, z} : Finset ℕ) ∈ D := by
        rw [hDdef, Finset.mem_biUnion]
        refine ⟨b, hIC hb, ?_⟩
        rw [Finset.mem_image]
        exact ⟨x, Finset.mem_filter.mpr ⟨hIC hx, by omega, by rw [hzeq]; exact hIC hz⟩, by rw [hzeq]⟩
      have hsub : ({x, b, z} : Finset ℕ) ⊆ I := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        exacts [hx, hb, hz]
      exact hIind _ hmem hsub
    rcases lt_or_gt_of_ne hac with h | h
    · exact hkey a c ha hc h habc
    · exact hkey c a hc ha h (by omega)
  have hIlt : ∀ x ∈ I, x < E + 1 := by
    intro x hx
    have := hA (hCA (hIC hx))
    rw [Finset.mem_Icc] at this; omega
  have hIroth : I.card ≤ rothNumberNat (E + 1) :=
    ThreeAPFree.le_rothNumberNat I hIfree hIlt rfl
  calc C.card ≤ (36 * 10 + 2) * I.card := hIcard
    _ = 362 * I.card := by norm_num
    _ ≤ 362 * rothNumberNat (E + 1) := Nat.mul_le_mul_left _ hIroth

#print axioms good_core_split

open Asymptotics Filter in
/-- `K·r₃(E+1) ≤ (ε/2)·E` eventually — Roth smallness in the shifted/scaled form the split needs. -/
lemma roth_small_nat (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → (K : ℝ) * (rothNumberNat (E + 1) : ℝ) ≤ (ε / 2) * (E : ℝ) := by
  have hc : (0:ℝ) < ε / (4 * (K + 1)) := by positivity
  have hev := (Asymptotics.isLittleO_iff.mp rothNumberNat_isLittleO_id) hc
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  refine ⟨max N₀ 1, fun E hE => ?_⟩
  have h := hN₀ (E + 1) (by omega)
  rw [Real.norm_natCast, Real.norm_natCast] at h
  push_cast at h
  have hE1 : (1:ℝ) ≤ (E:ℝ) := by
    have : 1 ≤ E := le_trans (le_max_right _ _) hE; exact_mod_cast this
  have hKc : (K:ℝ) * (ε / (4 * (K + 1))) ≤ ε / 4 := by
    have hK1 : ((K:ℝ) + 1) ≠ 0 := by positivity
    have h1 : (K:ℝ) * (ε / (4 * (K + 1))) = ((K:ℝ) / ((K:ℝ) + 1)) * (ε / 4) := by
      field_simp
    rw [h1]
    have hfrac : (K:ℝ) / ((K:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hq : (0:ℝ) ≤ ε / 4 := by positivity
    calc ((K:ℝ) / ((K:ℝ) + 1)) * (ε / 4) ≤ 1 * (ε / 4) := by gcongr
      _ = ε / 4 := by ring
  calc (K : ℝ) * (rothNumberNat (E + 1) : ℝ)
      ≤ (K : ℝ) * (ε / (4 * (K + 1)) * ((E:ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = ((K:ℝ) * (ε / (4 * (K + 1)))) * ((E:ℝ) + 1) := by ring
    _ ≤ (ε / 4) * ((E:ℝ) + 1) := mul_le_mul_of_nonneg_right hKc (by positivity)
    _ ≤ (ε / 2) * (E:ℝ) := by nlinarith [hE1, hε]

open scoped Classical in
/-- **`hAlon` discharged** (Alon Prop 2.5): for large `E`, a density-`≥1/3+ε` set `A ⊆ [1,E]` has a
3-AP good core `G` (each element the midpoint of `≥11` APs of `A`) of size `≥ (1/3+ε/2)E`. -/
lemma good_core_exists (ε : ℝ) (hε : 0 < ε) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E →
      (1 / 3 + ε) * E ≤ (A.card : ℝ) →
      ∃ G ⊆ A, (∀ g ∈ G, 11 ≤ (A.filter (fun x => x < g ∧ 2 * g - x ∈ A)).card)
        ∧ (1 / 3 + ε / 2) * E ≤ (G.card : ℝ) := by
  obtain ⟨E₀, hE₀⟩ := roth_small_nat 362 ε hε
  refine ⟨E₀, fun E hE A hA hden => ?_⟩
  set p : ℕ → Prop := fun a => 11 ≤ (A.filter (fun x => x < a ∧ 2 * a - x ∈ A)).card with hp
  set G : Finset ℕ := A.filter p with hG
  have hsplit := good_core_split E A hA
  set C : Finset ℕ := A.filter (fun a => (A.filter (fun x => x < a ∧ 2 * a - x ∈ A)).card ≤ 10)
    with hC
  have hCeq : C = A.filter (fun a => ¬ p a) := by
    apply Finset.filter_congr; intro a _; rw [hp]; constructor <;> intro h <;> omega
  have hGC : G.card + C.card = A.card := by
    rw [hG, hCeq]; exact Finset.filter_card_add_filter_neg_card_eq_card _
  have hCle : (C.card : ℝ) ≤ 362 * (rothNumberNat (E + 1) : ℝ) := by exact_mod_cast hsplit
  have hroth := hE₀ E hE
  refine ⟨G, Finset.filter_subset _ _, fun g hg => (Finset.mem_filter.mp hg).2, ?_⟩
  have hGCr : (G.card : ℝ) + (C.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hGC
  linarith [hden, hCle, hroth, hGCr]

#print axioms roth_small_nat
#print axioms good_core_exists
