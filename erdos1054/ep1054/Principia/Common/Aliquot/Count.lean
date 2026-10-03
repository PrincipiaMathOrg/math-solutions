/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Counting integers coprime to `R`, and the classes `gcd(N, Q) = g`

* `card_coprime_Ico`: `#{x ∈ [n, n + qR) : gcd(R, x) = 1} = q φ(R)` (blocks of length `R`);
* `card_coprime_Icc_ge` / `card_coprime_Icc_le`: on `[1, Z]` the count lies between
  `⌊Z/R⌋ φ(R)` and `(⌊Z/R⌋ + 1) φ(R)`;
* `card_class_ge`: `#{N ≤ X : gcd(N, Q) = g} ≥ ⌊X/Q⌋ φ(Q/g)` for `g ∣ Q` (the class is
  `g · {N₁ ≤ X/g : gcd(N₁, Q/g) = 1}`).
-/

namespace Principia.Common.Aliquot

open Finset

theorem card_coprime_Ico (R n : ℕ) :
    ∀ q : ℕ, #{x ∈ Ico n (n + q * R) | R.Coprime x} = q * Nat.totient R
  | 0 => by simp
  | q + 1 => by
      have hsplit : Ico n (n + (q + 1) * R) =
          Ico n (n + q * R) ∪ Ico (n + q * R) (n + q * R + R) := by
        rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
        congr 1
        ring
      rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
        card_coprime_Ico R n q, Nat.filter_coprime_Ico_eq_totient]
      ring

theorem Icc_one_eq_Ico (Z : ℕ) : Icc 1 Z = Ico 1 (1 + Z) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

/-- `⌊Z/R⌋ φ(R) ≤ #{1 ≤ x ≤ Z : gcd(R, x) = 1}`. -/
theorem card_coprime_Icc_ge (R Z : ℕ) :
    Z / R * Nat.totient R ≤ #{x ∈ Icc 1 Z | R.Coprime x} := by
  rw [← card_coprime_Ico R 1 (Z / R)]
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  rw [Icc_one_eq_Ico]
  apply Finset.Ico_subset_Ico le_rfl
  have := Nat.div_mul_le_self Z R
  omega

/-- `#{1 ≤ x ≤ Z : gcd(R, x) = 1} ≤ (⌊Z/R⌋ + 1) φ(R)`. -/
theorem card_coprime_Icc_le (R Z : ℕ) (hR : 0 < R) :
    #{x ∈ Icc 1 Z | R.Coprime x} ≤ (Z / R + 1) * Nat.totient R := by
  rw [← card_coprime_Ico R 1 (Z / R + 1)]
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  rw [Icc_one_eq_Ico]
  apply Finset.Ico_subset_Ico le_rfl
  have := Nat.lt_div_mul_add (a := Z) hR
  rw [Nat.add_mul, one_mul]
  omega

/-- **The class `gcd(N, Q) = g` has at least `⌊X/Q⌋ φ(Q/g)` members up to `X`.** -/
theorem card_class_ge (Q g X : ℕ) (hQ : 0 < Q) (hg : g ∣ Q) :
    X / Q * Nat.totient (Q / g) ≤ #{N ∈ Icc 1 X | Nat.gcd N Q = g} := by
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hg hQ
  have hgQ : g * (Q / g) = Q := Nat.mul_div_cancel' hg
  have hXQ : X / g / (Q / g) = X / Q := by
    rw [Nat.div_div_eq_div_mul, hgQ]
  rw [← hXQ]
  refine (card_coprime_Icc_ge (Q / g) (X / g)).trans ?_
  apply Finset.card_le_card_of_injOn (fun n => g * n)
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hg0.ne' (by omega))
    · calc g * n ≤ g * (X / g) := Nat.mul_le_mul_left g hn.1.2
        _ ≤ X := Nat.mul_div_le X g
    · conv_lhs => rw [← hgQ]
      rw [Nat.gcd_mul_left, (Nat.Coprime.symm hn.2).gcd_eq_one, mul_one]
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hg0 h

end Principia.Common.Aliquot
