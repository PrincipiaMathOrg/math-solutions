import Principia.MathDB.Problem367940Words
import Principia.MathDB.Problem367940Fiber

/-!
# MathDB #367940 — maximum-run flattened Fubini rankings and second-order Eulerian numbers

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/367940/solution.tex`, resolving the maximum-run enumeration of
Barrese, Elder, Harris and Simpson, *Enumerating flat Fubini rankings* (ADAM, 2026), §4.1,
Conjecture 4.4.  The printed equation (4.1) has indexing errors (the write-up shows the literal
formula fails at `j = 2`); the statement proved is the one the source's text, Table 2 and OEIS
A112487 specify, as in the write-up.

**Objects.**  A Fubini ranking of length `n` is `x : Fin n → Fin (n+1)` with
`x i = 1 + #{k | x k < x i}` (`IsFub`).  A maximal strictly increasing run starts at position `0`
and at every `p` with `x(p−1) ≥ x p` (`starts`); the ranking is *flattened* when the first entries
of its runs strictly increase (`Flat`).  `s n r` counts flattened Fubini rankings of length `n`
with exactly `r` runs.  `E2` are the second-order Eulerian numbers of A340556.

**What is proved.**
* `runs_le`, `runs_max`: a flattened word of length `2j+1` has at most `j+1` runs, and some
  flattened Fubini ranking of length `2j+1` has exactly `j+1`;
* `main`: `s(2j+1, j+1) = ∑_{k ≤ j} E2(j,k) 2^k` for every `j` (the write-up's boxed formula).

**Route.**  Flattened with `j+1` runs is equivalent to the inequalities `Adm` (`flat_iff_adm`,
the write-up's (2)); words over `m` letters satisfying them number `∑_x C(m, dv x)` over
admissible Fubini rankings `x` (`card_fiber`) and also `∑_i E2(j,i) C(m+i, 2j+1)` (`T_eq`,
`V_eq`); comparing coefficients in the binomial basis (`total`) replaces the write-up's infinite
average and generating function.  Values checked by brute force in Python for `j ≤ 3`.
**Absent:** the write-up's alternating-sum refinement (2) of the count by number of ranks, and
Tasks 2 onward.
-/

namespace Principia.MathDB.P367940

open Finset

/-- The starting positions of the maximal strictly increasing runs of a word of length `n`. -/
def starts (n : ℕ) (y : ℕ → ℕ) : Finset ℕ := (range n).filter fun p => p = 0 ∨ y p ≤ y (p - 1)

/-- Flattened: the first entries of the runs strictly increase. -/
def Flat (n : ℕ) (y : ℕ → ℕ) : Prop :=
  ∀ p ∈ starts n y, ∀ q ∈ starts n y, p < q → y p < y q

open Classical in
/-- Flattened Fubini rankings of length `n` with exactly `r` runs. -/
noncomputable def s (n r : ℕ) : ℕ :=
  (univ.filter fun x : Fin n → Fin (n + 1) =>
    IsFub x ∧ Flat n (wd x) ∧ (starts n (wd x)).card = r).card

theorem mem_starts (n : ℕ) (y : ℕ → ℕ) (p : ℕ) :
    p ∈ starts n y ↔ p < n ∧ (p = 0 ∨ y p ≤ y (p - 1)) := by
  simp [starts]

theorem no_consecutive {n : ℕ} {y : ℕ → ℕ} (hf : Flat n y) {p : ℕ} (hp : p ∈ starts n y)
    (hp1 : p + 1 ∈ starts n y) : False := by
  have h1 := hf p hp (p + 1) hp1 (by omega)
  rcases ((mem_starts n y (p + 1)).1 hp1).2 with h | h
  · omega
  · rw [show p + 1 - 1 = p by omega] at h
    omega

theorem half_injOn {n : ℕ} {y : ℕ → ℕ} (hf : Flat n y) (c : ℕ) (hc : c ≤ 1) :
    Set.InjOn (fun p => (p + c) / 2) (starts n y : Set ℕ) := by
  intro p hp q hq hpq
  have hpq' : (p + c) / 2 = (q + c) / 2 := hpq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : q = p + 1 := by omega
    subst this
    exact no_consecutive hf hp hq
  · have : p = q + 1 := by omega
    subst this
    exact no_consecutive hf hq hp

/-- **A flattened word of length `2j+1` has at most `j+1` runs.** -/
theorem runs_le (j : ℕ) (y : ℕ → ℕ) (hf : Flat (2 * j + 1) y) :
    (starts (2 * j + 1) y).card ≤ j + 1 := by
  have := card_le_card_of_injOn (fun p => (p + 0) / 2) (s := starts (2 * j + 1) y)
    (t := range (j + 1)) (fun p hp => by
      have := ((mem_starts _ y p).1 hp).1
      simp only [coe_range, Set.mem_Iio]
      omega) (half_injOn hf 0 (by omega))
  simpa using this

theorem even_chain (j : ℕ) (y : ℕ → ℕ) (h : Adm j y) :
    ∀ b ≤ j, ∀ a < b, y (2 * a) < y (2 * b) := by
  intro b
  induction b with
  | zero => intro _ a ha; omega
  | succ c ih =>
    intro hb a ha
    have hc := (h c (by omega)).1
    rw [show 2 * (c + 1) = 2 * c + 2 by ring]
    rcases Nat.lt_or_ge a c with hac | hac
    · exact (ih (by omega) a hac).trans hc
    · rw [show a = c by omega]
      exact hc

/-- **Flattened with `j+1` runs is exactly the inequalities `Adm`.** -/
theorem flat_iff_adm (j : ℕ) (y : ℕ → ℕ) :
    (Flat (2 * j + 1) y ∧ (starts (2 * j + 1) y).card = j + 1) ↔ Adm j y := by
  constructor
  · rintro ⟨hf, hc⟩
    set A := starts (2 * j + 1) y with hA
    have half : ∀ c ≤ 1, Set.InjOn (fun p => (p + c) / 2) (A : Set ℕ) := fun c hc =>
      half_injOn hf c hc
    have hmaps : ∀ c ≤ 1, ∀ p ∈ A, (p + c) / 2 ∈ range (j + 1) := fun c hc p hp => by
      have := ((mem_starts _ y p).1 hp).1
      rw [mem_range]
      omega
    have himg : ∀ c ≤ 1, A.image (fun p => (p + c) / 2) = range (j + 1) := fun c hc' => by
      refine eq_of_subset_of_card_le (fun t ht => ?_) ?_
      · obtain ⟨p, hp, rfl⟩ := mem_image.1 ht
        exact hmaps c hc' p hp
      · simp only [card_image_of_injOn (half c hc'), card_range, hc, le_refl]
    have hsum : ∀ c ≤ 1, ∑ p ∈ A, (p + c) / 2 = ∑ t ∈ range (j + 1), t := fun c hc' => by
      rw [← himg c hc', sum_image (half c hc')]
    have heven : ∀ p ∈ A, p % 2 = 0 := by
      by_contra hne
      push_neg at hne
      obtain ⟨p0, hp0, hodd⟩ := hne
      have hlt : ∑ p ∈ A, (p + 0) / 2 < ∑ p ∈ A, (p + 1) / 2 :=
        sum_lt_sum (fun p _ => by omega) ⟨p0, hp0, by omega⟩
      rw [hsum 0 (by omega), hsum 1 le_rfl] at hlt
      exact lt_irrefl _ hlt
    have hall : ∀ i ≤ j, 2 * i ∈ A := by
      intro i hi
      have : i ∈ A.image (fun p => (p + 0) / 2) := by
        rw [himg 0 (by omega)]
        exact mem_range.2 (by omega)
      obtain ⟨p, hp, hpi⟩ := mem_image.1 this
      have := heven p hp
      have hpi' : (p + 0) / 2 = i := hpi
      rw [show 2 * i = p by omega]
      exact hp
    intro i hi
    refine ⟨hf _ (hall i hi.le) _ (hall (i + 1) hi) (by omega) |>.trans_eq ?_, ?_⟩
    · rw [show 2 * (i + 1) = 2 * i + 2 by ring]
    · rcases ((mem_starts _ y _).1 (hall (i + 1) hi)).2 with h | h
      · omega
      · rw [show 2 * (i + 1) = 2 * i + 2 by ring] at h
        rwa [show 2 * i + 2 - 1 = 2 * i + 1 by omega] at h
  · intro h
    have hmem : ∀ p, p ∈ starts (2 * j + 1) y ↔ p ∈ (range (j + 1)).image (fun i => 2 * i) := by
      intro p
      rw [mem_starts, mem_image]
      simp only [mem_range]
      obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' p
      · constructor
        · rintro ⟨hp, _⟩
          exact ⟨i, by omega, rfl⟩
        · rintro ⟨i', hi', he⟩
          refine ⟨by omega, ?_⟩
          rcases i with _ | i
          · left; rfl
          · right
            have := (h i (by omega)).2
            rw [show 2 * (i + 1) = 2 * i + 2 by ring, show 2 * i + 2 - 1 = 2 * i + 1 by omega]
            exact this
      · constructor
        · rintro ⟨hp, h0 | hle⟩
          · omega
          · exfalso
            rw [show 2 * i + 1 - 1 = 2 * i by omega] at hle
            have h1 := h i (by omega)
            omega
        · rintro ⟨i', _, he⟩
          exact absurd he (by omega)
    have hset : starts (2 * j + 1) y = (range (j + 1)).image (fun i => 2 * i) := by
      ext p
      exact hmem p
    refine ⟨fun p hp q hq hpq => ?_, ?_⟩
    · rw [hset, mem_image] at hp hq
      obtain ⟨a, ha, rfl⟩ := hp
      obtain ⟨b, hb, rfl⟩ := hq
      exact even_chain j y h b (by have := mem_range.1 hb; omega) a (by omega)
    · rw [hset, card_image_of_injective _ (fun a b hab => by
        have : 2 * a = 2 * b := hab
        omega), card_range]

theorem wd_lt_iff {n m m' : ℕ} {y : Fin n → Fin m} {z : Fin n → Fin m'} (h : OE y z)
    (p q : ℕ) (hp : p < n) (hq : q < n) : wd y p < wd y q ↔ wd z p < wd z q := by
  simp only [wd, hp, hq, ↓reduceDIte]
  exact h ⟨q, hq⟩ ⟨p, hp⟩

theorem wd_le_iff {n m m' : ℕ} {y : Fin n → Fin m} {z : Fin n → Fin m'} (h : OE y z)
    (p q : ℕ) (hp : p < n) (hq : q < n) : wd y p ≤ wd y q ↔ wd z p ≤ wd z q := by
  rw [← not_lt, ← not_lt]
  exact not_congr (wd_lt_iff h q p hq hp)

theorem adm_oe {j m m' : ℕ} {y : Fin (2 * j + 1) → Fin m} {z : Fin (2 * j + 1) → Fin m'}
    (h : OE y z) : Adm j (wd y) ↔ Adm j (wd z) := by
  have key : ∀ i < j, (wd y (2 * i) < wd y (2 * i + 2) ∧ wd y (2 * i + 2) ≤ wd y (2 * i + 1))
      ↔ (wd z (2 * i) < wd z (2 * i + 2) ∧ wd z (2 * i + 2) ≤ wd z (2 * i + 1)) :=
    fun i hi => and_congr (wd_lt_iff h _ _ (by omega) (by omega))
      (wd_le_iff h _ _ (by omega) (by omega))
  exact ⟨fun ha i hi => (key i hi).1 (ha i hi), fun ha i hi => (key i hi).2 (ha i hi)⟩

/-- **The maximum-run enumeration**: `s(2j+1, j+1) = ∑_{k ≤ j} E2(j,k) 2^k`. -/
theorem main (j : ℕ) : s (2 * j + 1) (j + 1) = ∑ i ∈ range (j + 1), E2 j i * 2 ^ i := by
  classical
  set F := (univ : Finset (Fin (2 * j + 1) → Fin (2 * j + 1 + 1))).filter
    fun x => IsFub x ∧ Adm j (wd x) with hF
  have hs : s (2 * j + 1) (j + 1) = F.card := by
    unfold s
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and, hF]
    rw [flat_iff_adm]
  have hdv : ∀ x ∈ F, dv x ∈ range (2 * j + 1 + 1) := fun x _ => by
    have : dv x ≤ 2 * j + 1 := card_image_le.trans (by simp)
    exact mem_range.2 (by omega)
  have hsum := card_eq_sum_card_fiberwise (f := fun x => dv x) (s := F)
    (t := range (2 * j + 1 + 1)) fun x hx => hdv x hx
  have hcnt : ∀ m : ℕ, ∑ k ∈ range (2 * j + 1 + 1), m.choose k * (F.filter fun x => dv x = k).card
      = ∑ i ∈ range (j + 1), E2 j i * (m + i).choose (2 * j + 1) := by
    intro m
    rw [← V_eq, ← T_eq]
    have h1 : ∑ k ∈ range (2 * j + 1 + 1), m.choose k * (F.filter fun x => dv x = k).card
        = ∑ x ∈ F, m.choose (dv x) := by
      rw [← sum_fiberwise_of_maps_to hdv (fun x => m.choose (dv x))]
      refine sum_congr rfl fun k _ => ?_
      have hk : ∑ i ∈ F.filter (fun x => dv x = k), m.choose (dv i)
          = (F.filter fun x => dv x = k).card * m.choose k :=
        sum_const_nat fun x hx => congrArg m.choose (mem_filter.1 hx).2
      rw [hk, mul_comm]
    have h2 : ∑ x ∈ F, m.choose (dv x)
        = ∑ x ∈ F, (univ.filter fun y : Fin (2 * j + 1) → Fin m => fub y = x).card :=
      sum_congr rfl fun x hx => (card_fiber m (mem_filter.1 hx).2.1).symm
    have h3 : ∑ x ∈ F, (univ.filter fun y : Fin (2 * j + 1) → Fin m => fub y = x).card
        = (univ.filter fun y : Fin (2 * j + 1) → Fin m => fub y ∈ F).card := by
      rw [card_eq_sum_card_fiberwise (f := fub)
        (s := univ.filter fun y : Fin (2 * j + 1) → Fin m => fub y ∈ F) (t := F)
        (fun y hy => (mem_filter.1 hy).2)]
      refine sum_congr rfl fun x hx => ?_
      congr 1
      ext y
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h => ⟨h ▸ hx, h⟩, fun h => h.2⟩
    have h4 : (univ.filter fun y : Fin (2 * j + 1) → Fin m => fub y ∈ F).card = T j m := by
      unfold T
      rw [← card_filter]
      congr 1
      ext y
      simp only [mem_filter, mem_univ, true_and, hF]
      exact ⟨fun h => (adm_oe (oe_fub y)).1 h.2, fun h => ⟨fub_isFub y, (adm_oe (oe_fub y)).2 h⟩⟩
    rw [h1, h2, h3, h4]
  rw [hs, hsum]
  exact total j (fun k => (F.filter fun x => dv x = k).card) hcnt

theorem E2_self_pos (j : ℕ) : 0 < E2 j j := by
  induction j with
  | zero => simp [E2]
  | succ j ih =>
    rw [E2_succ_succ, E2_eq_zero j (j + 1) (by omega), mul_zero, zero_add]
    exact Nat.mul_pos (by omega) ih

/-- **The run bound is attained**: some flattened Fubini ranking of length `2j+1` has `j+1`
runs, and none has more. -/
theorem runs_max (j : ℕ) :
    (∀ x : Fin (2 * j + 1) → Fin (2 * j + 1 + 1), IsFub x → Flat (2 * j + 1) (wd x) →
      (starts (2 * j + 1) (wd x)).card ≤ j + 1) ∧
    ∃ x : Fin (2 * j + 1) → Fin (2 * j + 1 + 1), IsFub x ∧ Flat (2 * j + 1) (wd x) ∧
      (starts (2 * j + 1) (wd x)).card = j + 1 := by
  classical
  refine ⟨fun x _ hf => runs_le j _ hf, ?_⟩
  have hpos : 0 < s (2 * j + 1) (j + 1) := by
    rw [main]
    exact lt_of_lt_of_le (Nat.mul_pos (E2_self_pos j) (pow_pos two_pos j))
      (single_le_sum (f := fun i => E2 j i * 2 ^ i) (fun i _ => Nat.zero_le _)
        (mem_range.2 (by omega)))
  unfold s at hpos
  obtain ⟨x, hx⟩ := card_pos.1 hpos
  exact ⟨x, (mem_filter.1 hx).2⟩

end Principia.MathDB.P367940
