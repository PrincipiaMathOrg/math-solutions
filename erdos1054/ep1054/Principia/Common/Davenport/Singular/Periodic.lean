/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Cast.Order.Field

set_option autoImplicit false

/-!
# Periodic sets, and the independence of coprime periods (Chinese remainder theorem)

* `card_filter_Icc_le_of_periodic`: an `M`-periodic set meets `[1, X]` in at most
  `(X/M + 1) · #(period)` points.
* `card_filter_range_mul`: for coprime `M, N`, an `M`-periodic condition and an `N`-periodic
  condition are independent on a period `[0, MN)` (the map `r ↦ (r mod M, r mod N)` is a
  bijection onto `[0, M) × [0, N)`).
* `card_Icc_forall_not_coprime_le`: for pairwise coprime moduli `M_i`,
  `#{n ≤ X : gcd(n, M_i) > 1 for every i < J} ≤ X ∏_{i<J} (1 − φ(M_i)/M_i) + ∏_{i<J} M_i`.

With `M_i = ∏_{p ∈ R_i} p` for disjoint prime ranges `R_i` this is the statement that "`n` has a
prime factor in each `R_i`" behaves like independent events — the ingredient that replaces the
Jessen–Wintner purity law in the singularity proof.
-/

namespace Principia.Common.Davenport.Singular

open Finset

/-- A periodic set meets `[1, X]` in at most `(X/M + 1)` periods' worth of points. -/
theorem card_filter_Icc_le_of_periodic (M X : ℕ) (hM : 0 < M) (P : ℕ → Prop)
    [DecidablePred P] (hP : ∀ n, P n ↔ P (n % M)) :
    ((Icc 1 X).filter P).card ≤ (X / M + 1) * ((range M).filter P).card := by
  have h := Finset.card_le_card_of_injOn (s := (Icc 1 X).filter P)
    (t := (range (X / M + 1)) ×ˢ ((range M).filter P)) (fun n => (n / M, n % M)) ?_ ?_
  · rwa [Finset.card_product, Finset.card_range] at h
  · intro n hn
    have hn' := Finset.mem_coe.1 hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn'
    apply Finset.mem_coe.2
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.div_le_div_right hn'.1.2), Nat.mod_lt n hM, (hP n).1 hn'.2⟩
  · intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    rw [← Nat.div_add_mod a M, ← Nat.div_add_mod b M, hab.1, hab.2]

/-- **CRT independence.** -/
theorem card_filter_range_mul (M N : ℕ) (hMN : Nat.Coprime M N) (hM : 0 < M) (hN : 0 < N)
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hP : ∀ n, P n ↔ P (n % M)) (hQ : ∀ n, Q n ↔ Q (n % N)) :
    ((range (M * N)).filter (fun n => P n ∧ Q n)).card =
      ((range M).filter P).card * ((range N).filter Q).card := by
  rw [← Finset.card_product]
  refine Finset.card_nbij' (fun n => (n % M, n % N))
    (fun ab => (Nat.chineseRemainder hMN ab.1 ab.2 : ℕ)) ?_ ?_ ?_ ?_
  · intro n hn
    have hn' := Finset.mem_coe.1 hn
    rw [Finset.mem_filter] at hn'
    apply Finset.mem_coe.2
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, Finset.mem_range,
      Finset.mem_range]
    exact ⟨⟨Nat.mod_lt n hM, (hP n).1 hn'.2.1⟩, ⟨Nat.mod_lt n hN, (hQ n).1 hn'.2.2⟩⟩
  · intro ab hab
    have hab' := Finset.mem_coe.1 hab
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, Finset.mem_range,
      Finset.mem_range] at hab'
    obtain ⟨⟨ha, hPa⟩, ⟨hb, hQb⟩⟩ := hab'
    apply Finset.mem_coe.2
    set k := Nat.chineseRemainder hMN ab.1 ab.2 with hk
    have hk1 : (k : ℕ) % M = ab.1 := by
      have := k.2.1
      rw [Nat.ModEq, Nat.mod_eq_of_lt ha] at this
      exact this
    have hk2 : (k : ℕ) % N = ab.2 := by
      have := k.2.2
      rw [Nat.ModEq, Nat.mod_eq_of_lt hb] at this
      exact this
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.chineseRemainder_lt_mul hMN ab.1 ab.2 hM.ne' hN.ne', ?_, ?_⟩
    · rw [hP, hk1]
      exact hPa
    · rw [hQ, hk2]
      exact hQb
  · intro n hn
    have hn' := Finset.mem_coe.1 hn
    rw [Finset.mem_filter, Finset.mem_range] at hn'
    set k := Nat.chineseRemainder hMN (n % M) (n % N) with hk
    have h1 : (k : ℕ) ≡ n [MOD M] := k.2.1.trans (Nat.mod_modEq n M)
    have h2 : (k : ℕ) ≡ n [MOD N] := k.2.2.trans (Nat.mod_modEq n N)
    have h3 : (k : ℕ) ≡ n [MOD M * N] := (Nat.modEq_and_modEq_iff_modEq_mul hMN).1 ⟨h1, h2⟩
    have hklt : (k : ℕ) < M * N := Nat.chineseRemainder_lt_mul hMN _ _ hM.ne' hN.ne'
    rw [Nat.ModEq, Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt hn'.1] at h3
    exact h3
  · intro ab hab
    have hab' := Finset.mem_coe.1 hab
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, Finset.mem_range,
      Finset.mem_range] at hab'
    obtain ⟨⟨ha, _⟩, ⟨hb, _⟩⟩ := hab'
    set k := Nat.chineseRemainder hMN ab.1 ab.2 with hk
    have hk1 : (k : ℕ) % M = ab.1 := by
      have := k.2.1
      rw [Nat.ModEq, Nat.mod_eq_of_lt ha] at this
      exact this
    have hk2 : (k : ℕ) % N = ab.2 := by
      have := k.2.2
      rw [Nat.ModEq, Nat.mod_eq_of_lt hb] at this
      exact this
    simp only
    rw [hk1, hk2]

/-- Coprimality to `M` depends only on the residue modulo any multiple of `M`. -/
theorem coprime_iff_mod {M N n : ℕ} (h : M ∣ N) : Nat.Coprime M n ↔ Nat.Coprime M (n % N) := by
  have hmod : n % N ≡ n [MOD M] := (Nat.mod_modEq n N).of_dvd h
  unfold Nat.Coprime
  rw [Nat.gcd_comm M n, Nat.gcd_comm M (n % N), hmod.gcd_eq]

/-- The count on a full period: `∏_{i<k} (M_i − φ(M_i))`. -/
theorem card_range_forall_not_coprime (M : ℕ → ℕ) (hpos : ∀ i, 0 < M i)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (M i) (M j)) (k : ℕ) :
    ((range (∏ i ∈ range k, M i)).filter (fun n => ∀ i < k, ¬ Nat.Coprime (M i) n)).card =
      ∏ i ∈ range k, (M i - Nat.totient (M i)) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hN : 0 < ∏ i ∈ range k, M i := Finset.prod_pos fun i _ => hpos i
    have hcopN : Nat.Coprime (∏ i ∈ range k, M i) (M k) :=
      Nat.Coprime.prod_left fun i hi => hcop i k (by rw [Finset.mem_range] at hi; omega)
    have hfilt : (range ((∏ i ∈ range k, M i) * M k)).filter
          (fun n => ∀ i < k + 1, ¬ Nat.Coprime (M i) n) =
        (range ((∏ i ∈ range k, M i) * M k)).filter
          (fun n => (∀ i < k, ¬ Nat.Coprime (M i) n) ∧ ¬ Nat.Coprime (M k) n) := by
      apply Finset.filter_congr
      intro n _
      exact Nat.forall_lt_succ_right
    rw [Finset.prod_range_succ, hfilt,
      card_filter_range_mul _ _ hcopN hN (hpos k)
        (fun n => ∀ i < k, ¬ Nat.Coprime (M i) n) (fun n => ¬ Nat.Coprime (M k) n) ?_ ?_,
      ih, Finset.prod_range_succ]
    · congr 1
      have h1 := Finset.card_filter_add_card_filter_not (s := range (M k))
        (fun n => Nat.Coprime (M k) n)
      rw [Finset.card_range, ← Nat.totient_eq_card_coprime] at h1
      omega
    · intro n
      constructor
      · intro h i hi hc
        exact h i hi ((coprime_iff_mod (Finset.dvd_prod_of_mem M
          (Finset.mem_range.2 hi))).2 hc)
      · intro h i hi hc
        exact h i hi ((coprime_iff_mod (Finset.dvd_prod_of_mem M
          (Finset.mem_range.2 hi))).1 hc)
    · intro n
      rw [coprime_iff_mod (dvd_refl (M k))]

/-- **Independence of coprime periodic events.** For pairwise coprime `M_i ≥ 1`,
`#{1 ≤ n ≤ X : gcd(M_i, n) > 1 ∀ i < J} ≤ X ∏_{i<J} (1 − φ(M_i)/M_i) + ∏_{i<J} M_i`. -/
theorem card_Icc_forall_not_coprime_le (M : ℕ → ℕ) (hpos : ∀ i, 0 < M i)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (M i) (M j)) (J X : ℕ) :
    (((Icc 1 X).filter (fun n => ∀ i < J, ¬ Nat.Coprime (M i) n)).card : ℝ) ≤
      X * ∏ i ∈ range J, (1 - (Nat.totient (M i) : ℝ) / M i) + ∏ i ∈ range J, (M i : ℝ) := by
  set N := ∏ i ∈ range J, M i with hNdef
  have hN : 0 < N := Finset.prod_pos fun i _ => hpos i
  have hper : ∀ n, (∀ i < J, ¬ Nat.Coprime (M i) n) ↔ (∀ i < J, ¬ Nat.Coprime (M i) (n % N)) := by
    intro n
    constructor
    · intro h i hi hc
      exact h i hi ((coprime_iff_mod (Finset.dvd_prod_of_mem M (Finset.mem_range.2 hi))).2 hc)
    · intro h i hi hc
      exact h i hi ((coprime_iff_mod (Finset.dvd_prod_of_mem M (Finset.mem_range.2 hi))).1 hc)
  have h1 := card_filter_Icc_le_of_periodic N X hN _ hper
  rw [card_range_forall_not_coprime M hpos hcop J] at h1
  set c := ∏ i ∈ range J, (M i - Nat.totient (M i)) with hcdef
  have hcN : c ≤ N := by
    rw [hcdef, hNdef]
    exact Finset.prod_le_prod' fun i _ => Nat.sub_le _ _
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hcR : (c : ℝ) / N = ∏ i ∈ range J, (1 - (Nat.totient (M i) : ℝ) / M i) := by
    rw [hcdef, hNdef]
    push_cast [Nat.cast_prod]
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hMi : (0 : ℝ) < M i := by exact_mod_cast hpos i
    rw [Nat.cast_sub (Nat.totient_le (M i))]
    field_simp
  have hdiv : ((X / N : ℕ) : ℝ) ≤ (X : ℝ) / N := Nat.cast_div_le
  calc (((Icc 1 X).filter (fun n => ∀ i < J, ¬ Nat.Coprime (M i) n)).card : ℝ)
      ≤ (((X / N + 1) * c : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ((X / N : ℕ) : ℝ) * c + c := by push_cast; ring
    _ ≤ (X : ℝ) / N * c + N := by
        have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
        have := mul_le_mul_of_nonneg_right hdiv hc0
        have hcN' : (c : ℝ) ≤ N := by exact_mod_cast hcN
        linarith
    _ = X * ((c : ℝ) / N) + N := by ring
    _ = X * ∏ i ∈ range J, (1 - (Nat.totient (M i) : ℝ) / M i) + ∏ i ∈ range J, (M i : ℝ) := by
        rw [hcR, hNdef, Nat.cast_prod]

end Principia.Common.Davenport.Singular
