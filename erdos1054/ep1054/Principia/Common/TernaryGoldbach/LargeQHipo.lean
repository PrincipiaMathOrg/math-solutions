/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.LargeQSpine
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

set_option autoImplicit false

/-!
# `LQ.Hipo`, `LQ.HipoWo`, `LQ.F1Seven` PROVED: rearrangement over the prime factors of `q`

`eq:modo`/`eq:hipo` (`ternvin.tex` 3034-3048) and their `210 ∤ q` variants (3049-3064):
"`(p/(p−1))·f₁(p)` and `p ↦ (log p)/p` are decreasing functions of `p` for `p ≥ 3`; moreover, for
both functions, the value at `p ≥ 7` is smaller than for `p = 2`" — hence, for `q < Π_{p≤p₀} p`,
the prime factors of `q` can be traded for the primes below `p₀`.

## The proof

* **Two rearrangement lemmas**, by induction on a bound `B`: `upper_sum` (for `F ≥ 0` non-increasing
  on a set `S` of naturals, any `T ⊆ S` with `#T ≤ #(S ∩ [0,B))` has `Σ_T F ≤ Σ_{S∩[0,B)} F`) and
  `lower_prod` (any `T ⊆ S` with `#T ≥ #(S ∩ [0,B))` has `Π_T t ≥ Π_{S∩[0,B)} p`). Products of `g`
  are handled as sums of `log g`.
* **`2` is the exception** (`with_two_sum`): the odd part obeys the monotone lemma, and a factor
  `t > n` that would push `#T` past the odd primes `≤ n` is traded for `2` (`F(t) ≤ F(2)`).
* **The count** (`card_pf_le`, `card_pf_le_wo`): `Π_{p∣q} p ≤ q < Π_{p≤n+1} p` bounds `#{p ∣ q}` by
  `lower_prod`; for `210 ∤ q` a `7 ∣ q` is first swapped for a missing `m ∈ {2,3,5}`.
* **`g(p) = (p/(p−1))f₁(p) = G(p^{1/3})`**, `G(u) = (u⁵ + u³)/(u⁵ − u² + u + 1)` (`gP_eq`). `G` is
  NOT monotone on `[3^{1/3}, ∞)` (its maximum is near `p = 3.2`), but `G' ≤ 0` on `u ≥ 1.7`
  (`−G'D² = u²(2u⁵ + 3u⁴ − 4u³ − 4u² − 2u − 3)`), and `5^{1/3} ≥ 1.7`; with `g(3) ≥ g(5)` and
  `g(7) ≤ g(2)` evaluated from cube-root brackets, `g` decreases along the odd primes.
* **`F1Seven`**: `f₁(7) = (6/7)G(7^{1/3}) ≥ 1.1241324`, from `7^{1/3} ∈ [1.9129311, 1.9129312]`
  (slack `1.3·10⁻⁵` in `6.62365f₁(7) ≥ 7.44586`; true `f₁(7) = 1.12413438`).
-/

namespace Principia.Common.TernaryGoldbach.LQ

open Principia.Common.TernaryGoldbach.HC (sumLogP mertProd)

/-! ## (1) Rearrangement -/

/-- **Upper rearrangement for sums**: `F ≥ 0` non-increasing on `S`, `T ⊆ S`,
`#T ≤ #(S ∩ [0,B))` ⟹ `Σ_T F ≤ Σ_{S ∩ [0,B)} F`. -/
theorem upper_sum (S : ℕ → Prop) [DecidablePred S] (F : ℕ → ℝ) (hF0 : ∀ p, S p → 0 ≤ F p)
    (hanti : ∀ p p', S p → S p' → p ≤ p' → F p' ≤ F p) (B : ℕ) :
    ∀ T : Finset ℕ, (∀ t ∈ T, S t) → T.card ≤ ((Finset.range B).filter S).card →
      ∑ t ∈ T, F t ≤ ∑ p ∈ (Finset.range B).filter S, F p := by
  induction B with
  | zero =>
    intro T _ hc
    simp only [Finset.range_zero, Finset.filter_empty, Finset.card_empty, nonpos_iff_eq_zero,
      Finset.card_eq_zero] at hc
    subst hc
    simp
  | succ B ih =>
    intro T hT hc
    by_cases hB : S B
    · have hU : (Finset.range (B + 1)).filter S = insert B ((Finset.range B).filter S) := by
        rw [Finset.range_add_one, Finset.filter_insert, if_pos hB]
      have hBn : B ∉ (Finset.range B).filter S := by simp
      rw [hU] at hc ⊢
      rw [Finset.card_insert_of_notMem hBn] at hc
      by_cases hsub : ∀ t ∈ T, t ≤ B
      · have hTs : T ⊆ insert B ((Finset.range B).filter S) := by
          intro t ht
          rcases (hsub t ht).lt_or_eq with h | h
          · exact Finset.mem_insert_of_mem
              (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, hT t ht⟩)
          · rw [h]
            exact Finset.mem_insert_self _ _
        exact Finset.sum_le_sum_of_subset_of_nonneg hTs fun p hp _ => hF0 p (by
          rcases Finset.mem_insert.mp hp with h | h
          · rw [h]; exact hB
          · exact (Finset.mem_filter.mp h).2)
      · push Not at hsub
        obtain ⟨t, ht, htB⟩ := hsub
        have hT' := ih (T.erase t) (fun s hs => hT s (Finset.mem_of_mem_erase hs)) (by
          rw [Finset.card_erase_of_mem ht]
          omega)
        have hFt : F t ≤ F B := hanti B t hB (hT t ht) htB.le
        rw [Finset.sum_insert hBn, ← Finset.add_sum_erase T F ht]
        linarith
    · have hU : (Finset.range (B + 1)).filter S = (Finset.range B).filter S := by
        rw [Finset.range_add_one, Finset.filter_insert, if_neg hB]
      rw [hU] at hc ⊢
      exact ih T hT hc

/-- **Lower rearrangement for products of the elements**: `T ⊆ S ⊆ [1, ∞)`,
`#T ≥ #(S ∩ [0,B))` ⟹ `Π_{S ∩ [0,B)} p ≤ Π_T t`. -/
theorem lower_prod (S : ℕ → Prop) [DecidablePred S] (hS1 : ∀ p, S p → 1 ≤ p) (B : ℕ) :
    ∀ T : Finset ℕ, (∀ t ∈ T, S t) → ((Finset.range B).filter S).card ≤ T.card →
      ∏ p ∈ (Finset.range B).filter S, p ≤ ∏ t ∈ T, t := by
  induction B with
  | zero =>
    intro T hT _
    simp only [Finset.range_zero, Finset.filter_empty, Finset.prod_empty]
    exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun t ht => by
      have := hS1 t (hT t ht)
      omega)
  | succ B ih =>
    intro T hT hc
    by_cases hB : S B
    · have hU : (Finset.range (B + 1)).filter S = insert B ((Finset.range B).filter S) := by
        rw [Finset.range_add_one, Finset.filter_insert, if_pos hB]
      have hBn : B ∉ (Finset.range B).filter S := by simp
      rw [hU] at hc ⊢
      rw [Finset.card_insert_of_notMem hBn] at hc
      have hex : ∃ t ∈ T, B ≤ t := by
        by_contra h
        push Not at h
        have hTs : T ⊆ (Finset.range B).filter S := fun t ht =>
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (h t ht), hT t ht⟩
        have := Finset.card_le_card hTs
        omega
      obtain ⟨t, ht, htB⟩ := hex
      have hT' := ih (T.erase t) (fun s hs => hT s (Finset.mem_of_mem_erase hs)) (by
        rw [Finset.card_erase_of_mem ht]
        omega)
      rw [Finset.prod_insert hBn, ← Finset.mul_prod_erase T (fun x => x) ht]
      exact Nat.mul_le_mul htB hT'
    · have hU : (Finset.range (B + 1)).filter S = (Finset.range B).filter S := by
        rw [Finset.range_add_one, Finset.filter_insert, if_neg hB]
      rw [hU] at hc ⊢
      exact ih T hT hc

/-- **`2` as the exception**: with `R` the odd part (`R p → p ≠ 2`), `F ≥ 0`, `F` non-increasing
on `R`, and `F(t) ≤ F(2)` for `R t`, `t > n`: any `T ⊆ {2} ∪ R` with at most as many elements as
`({2} ∪ R) ∩ [0,n]` has `Σ_T F ≤ Σ_{({2} ∪ R) ∩ [0,n]} F`. -/
theorem with_two_sum (R : ℕ → Prop) [DecidablePred R] (F : ℕ → ℝ) (hR : ∀ p, R p → p ≠ 2)
    (hF0 : ∀ p, (p = 2 ∨ R p) → 0 ≤ F p) (hanti : ∀ p p', R p → R p' → p ≤ p' → F p' ≤ F p)
    (n : ℕ) (hn : 2 ≤ n) (h2 : ∀ t, R t → n < t → F t ≤ F 2) (T : Finset ℕ)
    (hT : ∀ t ∈ T, t = 2 ∨ R t)
    (hc : T.card ≤ ((Finset.range (n + 1)).filter (fun p => p = 2 ∨ R p)).card) :
    ∑ t ∈ T, F t ≤ ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p = 2 ∨ R p), F p := by
  have hZ : (Finset.range (n + 1)).filter (fun p => p = 2 ∨ R p) =
      insert 2 ((Finset.range (n + 1)).filter R) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨hp, h | h⟩
      · exact Or.inl h
      · exact Or.inr ⟨hp, h⟩
    · rintro (h | ⟨hp, h⟩)
      · exact ⟨by omega, Or.inl h⟩
      · exact ⟨hp, Or.inr h⟩
  have h2n : 2 ∉ (Finset.range (n + 1)).filter R := fun h => hR 2 (Finset.mem_filter.mp h).2 rfl
  rw [hZ] at hc ⊢
  rw [Finset.card_insert_of_notMem h2n] at hc
  rw [Finset.sum_insert h2n]
  have hRF0 : ∀ p, R p → 0 ≤ F p := fun p hp => hF0 p (Or.inr hp)
  have hF2 : 0 ≤ F 2 := hF0 2 (Or.inl rfl)
  by_cases h2T : 2 ∈ T
  · have hT' : ∀ t ∈ T.erase 2, R t := fun t ht => by
      rcases hT t (Finset.mem_of_mem_erase ht) with h | h
      · exact absurd h (Finset.ne_of_mem_erase ht)
      · exact h
    have hs := upper_sum R F hRF0 hanti (n + 1) (T.erase 2) hT' (by
      rw [Finset.card_erase_of_mem h2T]
      omega)
    rw [← Finset.add_sum_erase T F h2T]
    linarith
  · have hTR : ∀ t ∈ T, R t := fun t ht => by
      rcases hT t ht with h | h
      · exact absurd (h ▸ ht) h2T
      · exact h
    by_cases hbig : ∃ t ∈ T, n < t
    · obtain ⟨t, ht, htn⟩ := hbig
      have hs := upper_sum R F hRF0 hanti (n + 1) (T.erase t)
        (fun s hs => hTR s (Finset.mem_of_mem_erase hs)) (by
          rw [Finset.card_erase_of_mem ht]
          omega)
      have hFt := h2 t (hTR t ht) htn
      rw [← Finset.add_sum_erase T F ht]
      linarith
    · push Not at hbig
      have hTs : T ⊆ (Finset.range (n + 1)).filter R := fun t ht =>
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hbig t ht; omega), hTR t ht⟩
      have hs := upper_sum R F hRF0 hanti (n + 1) T hTR (Finset.card_le_card hTs)
      linarith

/-! ## (2) The counts -/

/-- `#(primes ≤ n+1) ≤ #(primes ≤ n) + 1`. -/
theorem card_primes_succ (n : ℕ) :
    ((Finset.range (n + 2)).filter Nat.Prime).card ≤
      ((Finset.range (n + 1)).filter Nat.Prime).card + 1 := by
  rw [show n + 2 = n + 1 + 1 by ring, Finset.range_add_one, Finset.filter_insert]
  split_ifs
  · exact Finset.card_insert_le _ _
  · omega

/-- `Π_{p ∣ q} p ≤ q`. -/
theorem prod_pf_le (q : ℕ) (hq : 1 ≤ q) : ∏ t ∈ q.primeFactors, t ≤ q :=
  Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)

/-- **The count for `eq:modo`**: `q < Π_{p≤n+1} p` ⟹ `#{p ∣ q} ≤ #{p ≤ n}`. -/
theorem card_pf_le (q n : ℕ) (hq : 1 ≤ q) (hqn : q < primorial (n + 1)) :
    q.primeFactors.card ≤ ((Finset.range (n + 1)).filter Nat.Prime).card := by
  by_contra h
  push Not at h
  have hs := card_primes_succ n
  have hlow := lower_prod Nat.Prime (fun p hp => hp.one_lt.le) (n + 2) q.primeFactors
    (fun t ht => Nat.prime_of_mem_primeFactors ht) (by omega)
  have hp : primorial (n + 1) = ∏ p ∈ (Finset.range (n + 2)).filter Nat.Prime, p := rfl
  have := prod_pf_le q hq
  omega

/-- The primes `≤ n+1` other than `7` multiply to `Π_{p≤n+1} p / 7` (`n ≥ 6`). -/
theorem primorial_div_seven (n : ℕ) (hn : 6 ≤ n) :
    ∏ p ∈ (Finset.range (n + 2)).filter (fun p => p.Prime ∧ p ≠ 7), p = primorial (n + 1) / 7 := by
  have hsplit : (Finset.range (n + 2)).filter Nat.Prime =
      insert 7 ((Finset.range (n + 2)).filter (fun p => p.Prime ∧ p ≠ 7)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨hp, hpr⟩
      by_cases h7 : p = 7
      · exact Or.inl h7
      · exact Or.inr ⟨hp, hpr, h7⟩
    · rintro (h | ⟨hp, hpr, _⟩)
      · subst h
        exact ⟨by omega, by norm_num⟩
      · exact ⟨hp, hpr⟩
  have h7n : 7 ∉ (Finset.range (n + 2)).filter (fun p => p.Prime ∧ p ≠ 7) := by simp
  have hp : primorial (n + 1) = ∏ p ∈ (Finset.range (n + 2)).filter Nat.Prime, p := rfl
  rw [hp, hsplit, Finset.prod_insert h7n]
  omega

/-- **The count for `eq:modowo`**: `210 ∤ q`, `q < Π_{p≤n+1, p≠7} p` ⟹ `#{p ∣ q} + 1 ≤ #{p ≤ n}`
(`n ≥ 7`). A `7 ∣ q` is swapped for a missing `m ∈ {2,3,5}`, which lowers the product. -/
theorem card_pf_le_wo (q n : ℕ) (hq : 1 ≤ q) (hn : 7 ≤ n) (h210 : ¬210 ∣ q)
    (hqn : q < primorial (n + 1) / 7) :
    q.primeFactors.card + 1 ≤ ((Finset.range (n + 1)).filter Nat.Prime).card := by
  by_contra h
  push Not at h
  set T := q.primeFactors with hTdef
  have hTp : ∀ t ∈ T, t.Prime := fun t ht => Nat.prime_of_mem_primeFactors ht
  have hs := card_primes_succ n
  have hW : ((Finset.range (n + 2)).filter (fun p => p.Prime ∧ p ≠ 7)).card + 1 =
      ((Finset.range (n + 2)).filter Nat.Prime).card := by
    have hsplit : (Finset.range (n + 2)).filter Nat.Prime =
        insert 7 ((Finset.range (n + 2)).filter (fun p => p.Prime ∧ p ≠ 7)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      constructor
      · rintro ⟨hp, hpr⟩
        by_cases h7 : p = 7
        · exact Or.inl h7
        · exact Or.inr ⟨hp, hpr, h7⟩
      · rintro (h | ⟨hp, hpr, _⟩)
        · subst h
          exact ⟨by omega, by norm_num⟩
        · exact ⟨hp, hpr⟩
    rw [hsplit, Finset.card_insert_of_notMem (by simp)]
  have hPq : ∏ t ∈ T, t ≤ q := prod_pf_le q hq
  have hdiv := primorial_div_seven n (by omega)
  -- a set `T*` of primes `≠ 7`, as large as `T`, with product `≤ q`
  obtain ⟨Ts, hTs7, hTsc, hTsP⟩ : ∃ Ts : Finset ℕ, (∀ t ∈ Ts, t.Prime ∧ t ≠ 7) ∧
      T.card ≤ Ts.card ∧ ∏ t ∈ Ts, t ≤ q := by
    by_cases h7 : 7 ∈ T
    · have hm : ∃ m ∈ ({2, 3, 5} : Finset ℕ), m ∉ T := by
        by_contra hall
        push Not at hall
        have hsub : ({2, 3, 5, 7} : Finset ℕ) ⊆ T := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact hall 2 (by simp)
          · exact hall 3 (by simp)
          · exact hall 5 (by simp)
          · exact h7
        have hd1 : ∏ t ∈ ({2, 3, 5, 7} : Finset ℕ), t ∣ ∏ t ∈ T, t :=
          Finset.prod_dvd_prod_of_subset _ _ _ hsub
        have hd2 : ∏ t ∈ ({2, 3, 5, 7} : Finset ℕ), t = 210 := by decide
        rw [hd2] at hd1
        exact h210 (dvd_trans hd1 (Nat.prod_primeFactors_dvd q))
      obtain ⟨m, hmS, hmT⟩ := hm
      have hm7 : m < 7 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmS
        omega
      have hmp : m.Prime := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmS
        rcases hmS with rfl | rfl | rfl <;> norm_num
      refine ⟨insert m (T.erase 7), ?_, ?_, ?_⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with h | h
        · subst h
          exact ⟨hmp, by omega⟩
        · exact ⟨hTp t (Finset.mem_of_mem_erase h), Finset.ne_of_mem_erase h⟩
      · rw [Finset.card_insert_of_notMem (fun h => hmT (Finset.mem_of_mem_erase h)),
          Finset.card_erase_of_mem h7]
        omega
      · rw [Finset.prod_insert (fun h => hmT (Finset.mem_of_mem_erase h))]
        have h1 : 7 * ∏ t ∈ T.erase 7, t = ∏ t ∈ T, t := Finset.mul_prod_erase T (fun x => x) h7
        have h2 : m * ∏ t ∈ T.erase 7, t ≤ 7 * ∏ t ∈ T.erase 7, t :=
          Nat.mul_le_mul_right _ hm7.le
        omega
    · exact ⟨T, fun t ht => ⟨hTp t ht, fun h => h7 (h ▸ ht)⟩, le_rfl, hPq⟩
  have hlow := lower_prod (fun p => p.Prime ∧ p ≠ 7) (fun p hp => hp.1.one_lt.le) (n + 2) Ts
    hTs7 (by omega)
  omega

/-! ## (3) The two functions -/

/-- `f(p) = log p / p`. -/
noncomputable def fP (p : ℕ) : ℝ := Real.log p / p

/-- `g(p) = (p/(p−1))·f₁(p)`. -/
noncomputable def gP (p : ℕ) : ℝ := (p : ℝ) / ((p : ℝ) - 1) * CY.f1 p

/-- `G(u) = (u⁵ + u³)/(u⁵ − u² + u + 1)`, so that `g(p) = G(p^{1/3})`. -/
noncomputable def gG3 (u : ℝ) : ℝ := (u ^ 5 + u ^ 3) / (u ^ 5 - u ^ 2 + u + 1)

/-- The denominator of `G` is positive for `u ≥ 1`. -/
theorem den_pos {u : ℝ} (hu : 1 ≤ u) : 0 < u ^ 5 - u ^ 2 + u + 1 := by
  have h : u ^ 2 ≤ u ^ 5 := pow_le_pow_right₀ hu (by norm_num)
  linarith

/-- `G(u) ≥ 1` for `u ≥ 1` (`G − 1 = (u+1)²(u−1)/D`). -/
theorem one_le_gG3 {u : ℝ} (hu : 1 ≤ u) : 1 ≤ gG3 u := by
  unfold gG3
  rw [le_div_iff₀ (den_pos hu)]
  have h1 : (0 : ℝ) ≤ u + 1 := by linarith
  have h2 : (0 : ℝ) ≤ u - 1 := by linarith
  have e : u ^ 5 + u ^ 3 - (u ^ 5 - u ^ 2 + u + 1) = (u + 1) * (u + 1) * (u - 1) := by ring
  have := mul_nonneg (mul_nonneg h1 h1) h2
  linarith

/-- The cube root: `p = (p^{1/3})³`. -/
theorem cube_cbrt {p : ℝ} (hp : 0 ≤ p) : (p ^ ((1 : ℝ) / 3)) ^ 3 = p := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp]
  norm_num

/-- **`g(p) = G(p^{1/3})`** for `p ≥ 2` prime. -/
theorem gP_eq (p : ℕ) (hp : p.Prime) : gP p = gG3 ((p : ℝ) ^ ((1 : ℝ) / 3)) := by
  unfold gP gG3
  rw [f1_prime p hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  set u := (p : ℝ) ^ ((1 : ℝ) / 3) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos (by linarith) _
  have hu3 : u ^ 3 = p := cube_cbrt (by linarith)
  have h23 : (p : ℝ) ^ ((2 : ℝ) / 3) = u ^ 2 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hm23 : (p : ℝ) ^ (-(2 : ℝ) / 3) = (u ^ 2)⁻¹ := by
    rw [← h23, ← Real.rpow_neg (by linarith)]
    norm_num
  rw [h23, hm23, ← hu3]
  have hu1 : 1 < u := by
    by_contra h
    have : u ^ 3 ≤ 1 := pow_le_one₀ hu0.le (not_lt.mp h)
    linarith
  have hd : u ^ 3 - 1 ≠ 0 := by nlinarith
  have hD : u ^ 5 - u ^ 2 + u + 1 ≠ 0 := (den_pos hu1.le).ne'
  have hD2 : u ^ 3 * (u ^ 3 - 1) + (u + u ^ 2) ≠ 0 := by nlinarith
  field_simp
  ring

/-- **`G` is non-increasing on `[1.7, ∞)`**:
`−G'·D² = u²(2u⁵ + 3u⁴ − 4u³ − 4u² − 2u − 3) ≥ 0`. -/
theorem gG3_anti : AntitoneOn gG3 (Set.Ici 1.7) := by
  have hderiv : ∀ u : ℝ, 1 ≤ u → HasDerivAt gG3
      (((5 * u ^ 4 + 3 * u ^ 2) * (u ^ 5 - u ^ 2 + u + 1) -
        (u ^ 5 + u ^ 3) * (5 * u ^ 4 - 2 * u + 1)) / (u ^ 5 - u ^ 2 + u + 1) ^ 2) u := by
    intro u hu
    have hN : HasDerivAt (fun x : ℝ => x ^ 5 + x ^ 3) (5 * u ^ 4 + 3 * u ^ 2) u := by
      have h := ((hasDerivAt_pow 5 u).add (hasDerivAt_pow 3 u))
      refine h.congr_deriv ?_
      norm_num
    have hD : HasDerivAt (fun x : ℝ => x ^ 5 - x ^ 2 + x + 1) (5 * u ^ 4 - 2 * u + 1) u := by
      have h := (((hasDerivAt_pow 5 u).sub (hasDerivAt_pow 2 u)).add
        (hasDerivAt_id u)).add_const 1
      refine h.congr_deriv ?_
      norm_num
    exact hN.div hD (den_pos hu).ne'
  refine antitoneOn_of_deriv_nonpos (convex_Ici _) ?_ ?_ ?_
  · intro u hu
    exact (hderiv u (le_trans (by norm_num) hu)).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ici] at hu
    exact (hderiv u (le_trans (by norm_num) (le_of_lt hu))).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [interior_Ici] at hu
    have hu' : (1.7 : ℝ) < u := hu
    rw [(hderiv u (by linarith)).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have hpoly : 0 ≤ 2 * u ^ 5 + 3 * u ^ 4 - 4 * u ^ 3 - 4 * u ^ 2 - 2 * u - 3 := by
      obtain ⟨d, rfl⟩ : ∃ d, u = 1.7 + d := ⟨u - 1.7, by ring⟩
      have hd : 0 ≤ d := by linarith
      nlinarith [pow_nonneg hd 2, pow_nonneg hd 3, pow_nonneg hd 4, pow_nonneg hd 5]
    have e : (5 * u ^ 4 + 3 * u ^ 2) * (u ^ 5 - u ^ 2 + u + 1) -
        (u ^ 5 + u ^ 3) * (5 * u ^ 4 - 2 * u + 1) =
        -(u ^ 2 * (2 * u ^ 5 + 3 * u ^ 4 - 4 * u ^ 3 - 4 * u ^ 2 - 2 * u - 3)) := by ring
    rw [e]
    exact neg_nonpos.mpr (mul_nonneg (sq_nonneg u) hpoly)

/-- Cube-root brackets: `a ≤ p^{1/3}` from `a³ ≤ p`. -/
theorem le_cbrt {a p : ℝ} (hp : 0 ≤ p) (h : a ^ 3 ≤ p) : a ≤ p ^ ((1 : ℝ) / 3) := by
  by_contra hc
  have := pow_lt_pow_left₀ (not_le.mp hc) (Real.rpow_nonneg hp _) (by norm_num : (3 : ℕ) ≠ 0)
  rw [cube_cbrt hp] at this
  linarith

/-- Cube-root brackets: `p^{1/3} ≤ b` from `p ≤ b³`. -/
theorem cbrt_le {b p : ℝ} (hb : 0 ≤ b) (hp : 0 ≤ p) (h : p ≤ b ^ 3) : p ^ ((1 : ℝ) / 3) ≤ b := by
  by_contra hc
  have := pow_lt_pow_left₀ (not_le.mp hc) hb (by norm_num : (3 : ℕ) ≠ 0)
  rw [cube_cbrt hp] at this
  linarith

/-- `G(u) ≥ N(a)/D(b)` and `G(u) ≤ N(b)/D(a)` for `1 ≤ a ≤ u ≤ b` (`N`, `D` increasing). -/
theorem gG3_bracket {a b u : ℝ} (ha : 1 ≤ a) (hau : a ≤ u) (hub : u ≤ b) :
    (a ^ 5 + a ^ 3) / (b ^ 5 - b ^ 2 + b + 1) ≤ gG3 u ∧
      gG3 u ≤ (b ^ 5 + b ^ 3) / (a ^ 5 - a ^ 2 + a + 1) := by
  have hu : 1 ≤ u := le_trans ha hau
  have hb : 1 ≤ b := le_trans hu hub
  have hDa := den_pos ha
  have hDu := den_pos hu
  have hDb := den_pos hb
  have hNmono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → x ^ 5 + x ^ 3 ≤ y ^ 5 + y ^ 3 := fun x y hx hxy => by
    have h5 := pow_le_pow_left₀ (by linarith) hxy 5
    have h3 := pow_le_pow_left₀ (by linarith) hxy 3
    linarith
  have hDmono : ∀ x y : ℝ, 1 ≤ x → x ≤ y →
      x ^ 5 - x ^ 2 + x + 1 ≤ y ^ 5 - y ^ 2 + y + 1 := fun x y hx hxy => by
    obtain ⟨d, rfl⟩ : ∃ d, y = x + d := ⟨y - x, by ring⟩
    have hd : 0 ≤ d := by linarith
    have hx4 : x ≤ x ^ 4 := by
      have := pow_le_pow_right₀ hx (by norm_num : 1 ≤ 4)
      simpa using this
    have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hx
    have hA : 0 ≤ d * (5 * x ^ 4 - 2 * x) := mul_nonneg hd (by linarith)
    have hB : 0 ≤ d ^ 2 * (10 * x ^ 3 - 1) := mul_nonneg (sq_nonneg d) (by linarith)
    have hC : 0 ≤ x ^ 2 * d ^ 3 := mul_nonneg (sq_nonneg x) (pow_nonneg hd 3)
    have hE : 0 ≤ x * d ^ 4 := mul_nonneg (by linarith) (pow_nonneg hd 4)
    have hF : 0 ≤ d ^ 5 := pow_nonneg hd 5
    have e : (x + d) ^ 5 - (x + d) ^ 2 + (x + d) + 1 - (x ^ 5 - x ^ 2 + x + 1) =
        d * (5 * x ^ 4 - 2 * x) + d ^ 2 * (10 * x ^ 3 - 1) + 10 * (x ^ 2 * d ^ 3) +
          5 * (x * d ^ 4) + d ^ 5 + d := by ring
    linarith
  have hN0 : 0 ≤ a ^ 5 + a ^ 3 := by positivity
  unfold gG3
  constructor
  · calc (a ^ 5 + a ^ 3) / (b ^ 5 - b ^ 2 + b + 1)
        ≤ (a ^ 5 + a ^ 3) / (u ^ 5 - u ^ 2 + u + 1) :=
          div_le_div_of_nonneg_left hN0 hDu (hDmono u b hu hub)
      _ ≤ (u ^ 5 + u ^ 3) / (u ^ 5 - u ^ 2 + u + 1) :=
          div_le_div_of_nonneg_right (hNmono a u ha hau) hDu.le
  · calc (u ^ 5 + u ^ 3) / (u ^ 5 - u ^ 2 + u + 1)
        ≤ (b ^ 5 + b ^ 3) / (u ^ 5 - u ^ 2 + u + 1) :=
          div_le_div_of_nonneg_right (hNmono u b hu hub) hDu.le
      _ ≤ (b ^ 5 + b ^ 3) / (a ^ 5 - a ^ 2 + a + 1) :=
          div_le_div_of_nonneg_left (by positivity) hDa (hDmono a u ha hau)

/-- `g(p) ≥ 1` for primes. -/
theorem one_le_gP (p : ℕ) (hp : p.Prime) : 1 ≤ gP p := by
  rw [gP_eq p hp]
  refine one_le_gG3 (le_cbrt (Nat.cast_nonneg p) ?_)
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  linarith

/-- `g` is non-increasing on the primes `≥ 5`. -/
theorem gP_anti5 (p p' : ℕ) (hp : p.Prime) (hp' : p'.Prime) (h5 : 5 ≤ p) (hpp : p ≤ p') :
    gP p' ≤ gP p := by
  rw [gP_eq p hp, gP_eq p' hp']
  have h5r : (5 : ℝ) ≤ p := by exact_mod_cast h5
  have hppr : (p : ℝ) ≤ p' := by exact_mod_cast hpp
  have hc : (1.7 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 3) :=
    le_cbrt (by linarith) (by norm_num; linarith)
  have hm : (p : ℝ) ^ ((1 : ℝ) / 3) ≤ (p' : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (by linarith) hppr (by norm_num)
  exact gG3_anti hc (le_trans hc hm) hm

/-- `g(5) ≤ g(3)` (`1.36193 ≤ 1.39953`). -/
theorem gP_5_le_3 : gP 5 ≤ gP 3 := by
  rw [gP_eq 5 (by norm_num), gP_eq 3 (by norm_num)]
  have h5 := (gG3_bracket (a := 1.7099) (b := 1.71) (u := ((5 : ℕ) : ℝ) ^ ((1 : ℝ) / 3))
    (by norm_num) (le_cbrt (by norm_num) (by norm_num))
    (cbrt_le (by norm_num) (by norm_num) (by norm_num))).2
  have h3 := (gG3_bracket (a := 1.4422) (b := 1.4423) (u := ((3 : ℕ) : ℝ) ^ ((1 : ℝ) / 3))
    (by norm_num) (le_cbrt (by norm_num) (by norm_num))
    (cbrt_le (by norm_num) (by norm_num) (by norm_num))).1
  have hn : ((1.71 : ℝ) ^ 5 + 1.71 ^ 3) / (1.7099 ^ 5 - 1.7099 ^ 2 + 1.7099 + 1) ≤
      (1.4422 ^ 5 + 1.4422 ^ 3) / (1.4423 ^ 5 - 1.4423 ^ 2 + 1.4423 + 1) := by norm_num
  linarith

/-- `g(7) ≤ g(2)` (`1.31149 ≤ 1.34504`). -/
theorem gP_7_le_2 : gP 7 ≤ gP 2 := by
  rw [gP_eq 7 (by norm_num), gP_eq 2 (by norm_num)]
  have h7 := (gG3_bracket (a := 1.9129) (b := 1.913) (u := ((7 : ℕ) : ℝ) ^ ((1 : ℝ) / 3))
    (by norm_num) (le_cbrt (by norm_num) (by norm_num))
    (cbrt_le (by norm_num) (by norm_num) (by norm_num))).2
  have h2 := (gG3_bracket (a := 1.2599) (b := 1.26) (u := ((2 : ℕ) : ℝ) ^ ((1 : ℝ) / 3))
    (by norm_num) (le_cbrt (by norm_num) (by norm_num))
    (cbrt_le (by norm_num) (by norm_num) (by norm_num))).1
  have hn : ((1.913 : ℝ) ^ 5 + 1.913 ^ 3) / (1.9129 ^ 5 - 1.9129 ^ 2 + 1.9129 + 1) ≤
      (1.2599 ^ 5 + 1.2599 ^ 3) / (1.26 ^ 5 - 1.26 ^ 2 + 1.26 + 1) := by norm_num
  linarith

/-- **`g` decreases along the odd primes.** -/
theorem gP_anti_odd (p p' : ℕ) (hp : p.Prime) (hp' : p'.Prime) (h2 : p ≠ 2) (hpp : p ≤ p') :
    gP p' ≤ gP p := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rcases Nat.lt_or_ge p 5 with h | h
  · -- `p ∈ {3, 4}`, so `p = 3`
    have hp3' : p = 3 := by
      interval_cases p
      · rfl
      · exact absurd hp (by norm_num)
    subst hp3'
    rcases Nat.lt_or_ge p' 5 with h' | h'
    · have : p' = 3 ∨ p' = 4 := by omega
      rcases this with rfl | rfl
      · exact le_rfl
      · exact absurd hp' (by norm_num)
    · exact le_trans (gP_anti5 5 p' (by norm_num) hp' le_rfl h') gP_5_le_3
  · exact gP_anti5 p p' hp hp' h hpp

/-- `f(p) = log p/p` decreases along the primes `≥ 3`. -/
theorem fP_anti_odd (p p' : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (hpp : p ≤ p') : fP p' ≤ fP p := by
  have hp3 : (3 : ℝ) ≤ p := by
    have := hp.two_le
    exact_mod_cast (by omega : 3 ≤ p)
  have he : Real.exp 1 ≤ (p : ℝ) := le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9
    (by norm_num))) hp3
  have hppr : (p : ℝ) ≤ p' := by exact_mod_cast hpp
  exact Real.log_div_self_antitoneOn he (le_trans he hppr) hppr

/-- `f(7) ≤ f(2)` (`2 log 7 ≤ 7 log 2`, i.e. `49 ≤ 128`). -/
theorem fP_7_le_2 : fP 7 ≤ fP 2 := by
  unfold fP
  have h : 2 * Real.log 7 ≤ 7 * Real.log 2 := by
    have h1 : Real.log ((7 : ℝ) ^ 2) ≤ Real.log ((2 : ℝ) ^ 7) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    linarith
  push_cast
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  linarith

/-- `f ≥ 0` at primes. -/
theorem fP_nonneg (p : ℕ) : 0 ≤ fP p :=
  div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

/-! ## (4) The identities -/

/-- **`(q/φ(q))·f₁(q) = Π_{p∣q} g(p)`**. -/
theorem ratio_f1_eq (q : ℕ) (hq : 1 ≤ q) :
    (q : ℝ) / q.totient * CY.f1 q = ∏ p ∈ q.primeFactors, gP p := by
  have h1 := PSieve.prod_inv_eq q hq
  have hf : (q.primeFactors.filter fun p => p.Prime) = q.primeFactors :=
    Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp
  rw [hf] at h1
  have e1 : ∀ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    have h0 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h1 : (p : ℝ) ≠ 0 := by linarith
    field_simp
  rw [Finset.prod_congr rfl e1] at h1
  have e2 : CY.f1 q = ∏ p ∈ q.primeFactors, CY.f1 p := by
    unfold CY.f1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.Prime.primeFactors (Nat.prime_of_mem_primeFactors hp), Finset.prod_singleton]
  rw [← h1, e2, ← Finset.prod_mul_distrib]
  rfl

/-- **`Π_{p≤n} p/(p−1) · F(n) = Π_{p≤n} g(p)`**. -/
theorem mert_f1_eq (n : ℕ) :
    mertProd n * f1Prod n = ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, gP p := by
  unfold mertProd f1Prod
  rw [← Finset.prod_mul_distrib]
  rfl

/-- `Π_T g = exp(Σ_T log g)` on primes. -/
theorem prod_gP_eq_exp (T : Finset ℕ) (hT : ∀ t ∈ T, t.Prime) :
    ∏ t ∈ T, gP t = Real.exp (∑ t ∈ T, Real.log (gP t)) := by
  rw [Real.exp_sum]
  exact Finset.prod_congr rfl fun t ht =>
    (Real.exp_log (lt_of_lt_of_le one_pos (one_le_gP t (hT t ht)))).symm

/-- The prime filter as `{2} ∪ (odd primes)`. -/
theorem filter_prime_two (n : ℕ) :
    (Finset.range (n + 1)).filter Nat.Prime =
      (Finset.range (n + 1)).filter (fun p => p = 2 ∨ (p.Prime ∧ p ≠ 2)) := by
  refine Finset.filter_congr fun p _ => ?_
  constructor
  · intro hp
    by_cases h : p = 2
    · exact Or.inl h
    · exact Or.inr ⟨hp, h⟩
  · rintro (h | h)
    · rw [h]; exact Nat.prime_two
    · exact h.1

/-- The prime-but-not-`7` filter as `{2} ∪ (odd primes ≠ 7)`. -/
theorem filter_prime_wo (n : ℕ) :
    (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ≠ 7) =
      (Finset.range (n + 1)).filter (fun p => p = 2 ∨ (p.Prime ∧ p ≠ 2 ∧ p ≠ 7)) := by
  refine Finset.filter_congr fun p _ => ?_
  constructor
  · rintro ⟨hp, h7⟩
    by_cases h : p = 2
    · exact Or.inl h
    · exact Or.inr ⟨hp, h, h7⟩
  · rintro (h | h)
    · rw [h]; exact ⟨Nat.prime_two, by norm_num⟩
    · exact ⟨h.1, h.2.2⟩

/-! ## (5) `Hipo` -/

/-- **`LQ.Hipo`, PROVED** (`eq:modo`, `eq:hipo`). -/
theorem hipo : Hipo := by
  intro q n hq hn hqn
  have hc := card_pf_le q n hq hqn
  set T := q.primeFactors with hTdef
  have hTp : ∀ t ∈ T, t.Prime := fun t ht => Nat.prime_of_mem_primeFactors ht
  have hT2 : ∀ t ∈ T, t = 2 ∨ (t.Prime ∧ t ≠ 2) := fun t ht => by
    by_cases h : t = 2
    · exact Or.inl h
    · exact Or.inr ⟨hTp t ht, h⟩
  rw [filter_prime_two n] at hc
  have hR : ∀ p, (p.Prime ∧ p ≠ 2) → p ≠ 2 := fun p h => h.2
  constructor
  · -- the sum of `log p/p`
    have h := with_two_sum (fun p => p.Prime ∧ p ≠ 2) fP hR (fun p _ => fP_nonneg p)
      (fun p p' hp _ hpp => fP_anti_odd p p' hp.1 hp.2 hpp) n (by omega)
      (fun t ht htn => le_trans (fP_anti_odd 7 t (by norm_num) (by norm_num) (by omega))
        fP_7_le_2) T hT2 hc
    rw [← filter_prime_two n] at h
    exact h
  · -- the product of `g`
    have h := with_two_sum (fun p => p.Prime ∧ p ≠ 2) (fun p => Real.log (gP p)) hR
      (fun p hp => by
        rcases hp with rfl | hp
        · exact Real.log_nonneg (one_le_gP 2 Nat.prime_two)
        · exact Real.log_nonneg (one_le_gP p hp.1))
      (fun p p' hp hp' hpp => Real.log_le_log (lt_of_lt_of_le one_pos (one_le_gP p' hp'.1))
        (gP_anti_odd p p' hp.1 hp'.1 hp.2 hpp))
      n (by omega)
      (fun t ht htn => Real.log_le_log (lt_of_lt_of_le one_pos (one_le_gP t ht.1))
        (le_trans (gP_anti5 7 t (by norm_num) ht.1 (by norm_num) (by omega)) gP_7_le_2))
      T hT2 hc
    rw [← filter_prime_two n] at h
    rw [ratio_f1_eq q hq, mert_f1_eq n, prod_gP_eq_exp T hTp,
      prod_gP_eq_exp _ (fun t ht => (Finset.mem_filter.mp ht).2)]
    exact Real.exp_le_exp.mpr h

/-! ## (6) `HipoWo` -/

/-- **`LQ.HipoWo`, PROVED** (`eq:modowo`, `eq:hipowo`). -/
theorem hipoWo : HipoWo := by
  intro q n hq hn h210 hqn
  have hc := card_pf_le_wo q n hq hn h210 hqn
  set T := q.primeFactors with hTdef
  have hTp : ∀ t ∈ T, t.Prime := fun t ht => Nat.prime_of_mem_primeFactors ht
  -- the targets without `7`
  have hU7 : (Finset.range (n + 1)).filter Nat.Prime =
      insert 7 ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ≠ 7)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨hp, hpr⟩
      by_cases h7 : p = 7
      · exact Or.inl h7
      · exact Or.inr ⟨hp, hpr, h7⟩
    · rintro (h | ⟨hp, hpr, _⟩)
      · subst h
        exact ⟨by omega, by norm_num⟩
      · exact ⟨hp, hpr⟩
  have h7n : 7 ∉ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ≠ 7) := by simp
  have hcW : ((Finset.range (n + 1)).filter Nat.Prime).card =
      ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ≠ 7)).card + 1 := by
    rw [hU7, Finset.card_insert_of_notMem h7n]
  -- the swap: a set `T*` of primes `≠ 7`, `#T* = #T`, `Σ_T F ≤ Σ_{T*} F` for `F = f`, `log g`
  have hswap : ∃ Ts : Finset ℕ, (∀ t ∈ Ts, t.Prime ∧ t ≠ 7) ∧ Ts.card = T.card ∧
      ∑ t ∈ T, fP t ≤ ∑ t ∈ Ts, fP t ∧
        ∑ t ∈ T, Real.log (gP t) ≤ ∑ t ∈ Ts, Real.log (gP t) := by
    by_cases h7 : 7 ∈ T
    · have hm : ∃ m ∈ ({2, 3, 5} : Finset ℕ), m ∉ T := by
        by_contra hall
        push Not at hall
        have hsub : ({2, 3, 5, 7} : Finset ℕ) ⊆ T := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact hall 2 (by simp)
          · exact hall 3 (by simp)
          · exact hall 5 (by simp)
          · exact h7
        have hd1 : ∏ t ∈ ({2, 3, 5, 7} : Finset ℕ), t ∣ ∏ t ∈ T, t :=
          Finset.prod_dvd_prod_of_subset _ _ _ hsub
        have hd2 : ∏ t ∈ ({2, 3, 5, 7} : Finset ℕ), t = 210 := by decide
        rw [hd2] at hd1
        exact h210 (dvd_trans hd1 (Nat.prod_primeFactors_dvd q))
      obtain ⟨m, hmS, hmT⟩ := hm
      have hmp : m.Prime ∧ m ≠ 7 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmS
        rcases hmS with rfl | rfl | rfl <;> norm_num
      have hf7 : fP 7 ≤ fP m := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmS
        rcases hmS with rfl | rfl | rfl
        · exact fP_7_le_2
        · exact fP_anti_odd 3 7 (by norm_num) (by norm_num) (by norm_num)
        · exact fP_anti_odd 5 7 (by norm_num) (by norm_num) (by norm_num)
      have hg7 : gP 7 ≤ gP m := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmS
        rcases hmS with rfl | rfl | rfl
        · exact gP_7_le_2
        · exact le_trans (gP_anti5 5 7 (by norm_num) (by norm_num) le_rfl (by norm_num))
            gP_5_le_3
        · exact gP_anti5 5 7 (by norm_num) (by norm_num) le_rfl (by norm_num)
      have hmT' : m ∉ T.erase 7 := fun h => hmT (Finset.mem_of_mem_erase h)
      refine ⟨insert m (T.erase 7), ?_, ?_, ?_, ?_⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with h | h
        · rw [h]; exact hmp
        · exact ⟨hTp t (Finset.mem_of_mem_erase h), Finset.ne_of_mem_erase h⟩
      · rw [Finset.card_insert_of_notMem hmT', Finset.card_erase_of_mem h7]
        have := Finset.card_pos.mpr ⟨7, h7⟩
        omega
      · rw [Finset.sum_insert hmT', ← Finset.add_sum_erase T fP h7]
        linarith
      · rw [Finset.sum_insert hmT', ← Finset.add_sum_erase T (fun t => Real.log (gP t)) h7]
        have := Real.log_le_log (lt_of_lt_of_le one_pos (one_le_gP 7 (by norm_num))) hg7
        linarith
    · exact ⟨T, fun t ht => ⟨hTp t ht, fun h => h7 (h ▸ ht)⟩, rfl, le_rfl, le_rfl⟩
  obtain ⟨Ts, hTs7, hTsc, hsf, hsg⟩ := hswap
  have hTs2 : ∀ t ∈ Ts, t = 2 ∨ (t.Prime ∧ t ≠ 2 ∧ t ≠ 7) := fun t ht => by
    by_cases h : t = 2
    · exact Or.inl h
    · exact Or.inr ⟨(hTs7 t ht).1, h, (hTs7 t ht).2⟩
  have hcs : Ts.card ≤
      ((Finset.range (n + 1)).filter (fun p => p = 2 ∨ (p.Prime ∧ p ≠ 2 ∧ p ≠ 7))).card := by
    rw [← filter_prime_wo n]
    omega
  have hR : ∀ p, (p.Prime ∧ p ≠ 2 ∧ p ≠ 7) → p ≠ 2 := fun p h => h.2.1
  constructor
  · have h := with_two_sum (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 7) fP hR (fun p _ => fP_nonneg p)
      (fun p p' hp _ hpp => fP_anti_odd p p' hp.1 hp.2.1 hpp) n (by omega)
      (fun t ht htn => le_trans (fP_anti_odd 7 t (by norm_num) (by norm_num) (by omega))
        fP_7_le_2) Ts hTs2 hcs
    rw [← filter_prime_wo n] at h
    have hsum : sumLP n = fP 7 + ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ≠ 7),
        fP p := by
      unfold sumLP
      rw [hU7, Finset.sum_insert h7n]
      rfl
    have hf7 : fP 7 = Real.log 7 / 7 := by unfold fP; push_cast; rfl
    unfold sumLogP
    change ∑ t ∈ T, fP t ≤ sumLP n - Real.log 7 / 7
    linarith
  · have h := with_two_sum (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 7) (fun p => Real.log (gP p)) hR
      (fun p hp => by
        rcases hp with rfl | hp
        · exact Real.log_nonneg (one_le_gP 2 Nat.prime_two)
        · exact Real.log_nonneg (one_le_gP p hp.1))
      (fun p p' hp hp' hpp => Real.log_le_log (lt_of_lt_of_le one_pos (one_le_gP p' hp'.1))
        (gP_anti_odd p p' hp.1 hp'.1 hp.2.1 hpp))
      n (by omega)
      (fun t ht htn => Real.log_le_log (lt_of_lt_of_le one_pos (one_le_gP t ht.1))
        (le_trans (gP_anti5 7 t (by norm_num) ht.1 (by norm_num) (by omega)) gP_7_le_2))
      Ts hTs2 hcs
    rw [← filter_prime_wo n] at h
    have hWp : ∀ t ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ≠ 7), t.Prime :=
      fun t ht => (Finset.mem_filter.mp ht).2.1
    have hprod : mertProd n * f1Prod n = gP 7 *
        ∏ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ≠ 7), gP p := by
      rw [mert_f1_eq n, hU7, Finset.prod_insert h7n]
    have hg7 : gP 7 = 7 / 6 * CY.f1 7 := by
      unfold gP
      norm_num
    have hg7pos : 0 < gP 7 := lt_of_lt_of_le one_pos (one_le_gP 7 (by norm_num))
    rw [hprod, ← hg7, mul_div_cancel_left₀ _ hg7pos.ne', ratio_f1_eq q hq,
      prod_gP_eq_exp T hTp, prod_gP_eq_exp _ hWp]
    exact Real.exp_le_exp.mpr (le_trans hsg h)

/-! ## (7) `F1Seven` -/

/-- **`LQ.F1Seven`, PROVED**: `6.62365·f₁(7) ≥ 7.44586`, from `f₁(7) = (6/7)·G(7^{1/3})` and
`7^{1/3} ≤ 1.9129312`. -/
theorem f1Seven : F1Seven := by
  unfold F1Seven
  have hg : gP 7 = 7 / 6 * CY.f1 7 := by
    unfold gP
    norm_num
  have h7 := (gG3_bracket (a := 1.9129311) (b := 1.9129312) (u := ((7 : ℕ) : ℝ) ^ ((1 : ℝ) / 3))
    (by norm_num) (le_cbrt (by norm_num) (by norm_num))
    (cbrt_le (by norm_num) (by norm_num) (by norm_num))).1
  rw [← gP_eq 7 (by norm_num), hg] at h7
  have hn : (7.44586 : ℝ) ≤ 6.62365 * (6 / 7 * ((1.9129311 ^ 5 + 1.9129311 ^ 3) /
      (1.9129312 ^ 5 - 1.9129312 ^ 2 + 1.9129312 + 1))) := by norm_num
  linarith

end Principia.Common.TernaryGoldbach.LQ
