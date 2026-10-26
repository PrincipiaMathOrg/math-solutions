import Mathlib

/-!
# MathDB #367940 — second-order Eulerian numbers and the binomial basis

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/367940/solution.tex` (flattened Fubini rankings of Barrese, Elder,
Harris and Simpson, Conjecture 4.4).  The write-up evaluates `∑_k N_j(k)` by an infinite average of
`e_j(1, …, m)` and a generating function.  This module replaces that with a finite route:

* `E2`: the second-order Eulerian numbers in the A340556 convention (the write-up's (1));
* `e`: `e_j(1, …, m)`, defined by adjoining the largest argument, and `e_eq`:
  `e_j(1, …, m) = ∑_i E2(j,i) C(m+i, 2j)`;
* `V_eq`: `∑_{u<m} e_j(1, …, u) = ∑_i E2(j,i) C(m+i, 2j+1)`;
* `binom_unique` and `total`: if `∑_d C(m,d) cnt(d)` equals the latter for every `m`, then
  `∑_d cnt(d) = ∑_i E2(j,i) 2^i`.

All identities were checked in Python for `j ≤ 5`, `m ≤ 11`.  The word count is the consumer.
-/

namespace Principia.MathDB.P367940

open Finset

/-- Second-order Eulerian numbers, `E2(j,k) = k E2(j−1,k) + (2j−k) E2(j−1,k−1)`. -/
def E2 : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | _ + 1, 0 => 0
  | j + 1, k + 1 => (k + 1) * E2 j (k + 1) + (2 * j + 1 - k) * E2 j k

theorem E2_succ_succ (j k : ℕ) :
    E2 (j + 1) (k + 1) = (k + 1) * E2 j (k + 1) + (2 * j + 1 - k) * E2 j k := rfl

theorem E2_eq_zero (j k : ℕ) (h : j < k) : E2 j k = 0 := by
  induction j generalizing k with
  | zero =>
    change (if k = 0 then 1 else 0) = 0
    rw [if_neg (by omega)]
  | succ j ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [E2_succ_succ, ih (k + 1) (by omega), ih k (by omega)]
    simp

/-- `e_j(1, …, m)`, by adjoining the largest argument. -/
def e : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 0
  | j + 1, m + 1 => e (j + 1) m + (m + 1) * e j m

theorem e_succ_succ (j m : ℕ) : e (j + 1) (m + 1) = e (j + 1) m + (m + 1) * e j m := rfl

/-- The termwise identity behind `e_eq`. -/
theorem choose_step (m i j : ℕ) (hi : i ≤ j) :
    i * (m + i).choose (2 * j + 1) + (2 * j + 1 - i) * (m + i + 1).choose (2 * j + 1)
      = (m + 1) * (m + i).choose (2 * j) := by
  rw [Nat.choose_succ_succ' (m + i) (2 * j)]
  by_cases hN : m + i < 2 * j
  · rw [Nat.choose_eq_zero_of_lt hN, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  · have h := Nat.choose_succ_right_eq (m + i) (2 * j)
    obtain ⟨t, ht⟩ : ∃ t, m + i = 2 * j + t := ⟨m + i - 2 * j, by omega⟩
    rw [ht] at h ⊢
    rw [show 2 * j + t - 2 * j = t by omega] at h
    have e1 : 2 * j + 1 - i + i = 2 * j + 1 := by omega
    have e2 : m + 1 = t + (2 * j + 1 - i) := by omega
    have h3 : (2 * j + 1 - i + i) * (2 * j + t).choose (2 * j + 1)
        = (2 * j + 1) * (2 * j + t).choose (2 * j + 1) := by rw [e1]
    have h4 : (m + 1) * (2 * j + t).choose (2 * j)
        = (t + (2 * j + 1 - i)) * (2 * j + t).choose (2 * j) := by rw [e2]
    linarith

theorem e_eq (j m : ℕ) : e j m = ∑ i ∈ range (j + 1), E2 j i * (m + i).choose (2 * j) := by
  induction j generalizing m with
  | zero => simp [e, E2]
  | succ j ih =>
    induction m with
    | zero =>
      rw [show e (j + 1) 0 = 0 from rfl]
      refine (sum_eq_zero fun i hi => ?_).symm
      rw [mem_range] at hi
      rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
    | succ m ihm =>
      rw [e_succ_succ, ihm, ih m]
      have split : ∀ i ∈ range (j + 1 + 1), E2 (j + 1) i * (m + 1 + i).choose (2 * (j + 1))
          = E2 (j + 1) i * (m + i).choose (2 * (j + 1))
            + E2 (j + 1) i * (m + i).choose (2 * j + 1) := by
        intro i _
        rw [show m + 1 + i = (m + i) + 1 by ring, show 2 * (j + 1) = (2 * j + 1) + 1 by ring,
          Nat.choose_succ_succ']
        ring
      rw [sum_congr rfl split, sum_add_distrib]
      congr 1
      have hshift : ∑ i ∈ range (j + 1), (i + 1) * E2 j (i + 1) * (m + (i + 1)).choose (2 * j + 1)
          = ∑ i ∈ range (j + 1), i * E2 j i * (m + i).choose (2 * j + 1) := by
        have h1 := sum_range_succ' (fun i => i * E2 j i * (m + i).choose (2 * j + 1)) (j + 1)
        have h2 := sum_range_succ (fun i => i * E2 j i * (m + i).choose (2 * j + 1)) (j + 1)
        rw [E2_eq_zero j (j + 1) (by omega)] at h2
        simp only [zero_mul, mul_zero, add_zero] at h1 h2
        linarith
      have hR : ∑ i ∈ range (j + 1 + 1), E2 (j + 1) i * (m + i).choose (2 * j + 1)
          = (m + 1) * ∑ i ∈ range (j + 1), E2 j i * (m + i).choose (2 * j) := by
        rw [sum_range_succ', show E2 (j + 1) 0 = 0 from rfl, zero_mul, add_zero]
        have hsplit : ∑ i ∈ range (j + 1), E2 (j + 1) (i + 1) * (m + (i + 1)).choose (2 * j + 1)
            = ∑ i ∈ range (j + 1), (i + 1) * E2 j (i + 1) * (m + (i + 1)).choose (2 * j + 1)
              + ∑ i ∈ range (j + 1),
                  (2 * j + 1 - i) * E2 j i * (m + (i + 1)).choose (2 * j + 1) := by
          rw [← sum_add_distrib]
          refine sum_congr rfl fun i _ => ?_
          rw [E2_succ_succ]
          ring
        rw [hsplit, hshift, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun i hi => ?_
        rw [mem_range] at hi
        have hs := choose_step m i j (by omega)
        have hs' : E2 j i * (i * (m + i).choose (2 * j + 1)
            + (2 * j + 1 - i) * (m + i + 1).choose (2 * j + 1))
            = E2 j i * ((m + 1) * (m + i).choose (2 * j)) := by rw [hs]
        rw [show m + (i + 1) = m + i + 1 by ring]
        linarith
      rw [hR]

/-- `V j m = ∑_{u<m} e_j(1, …, u)`. -/
def V (j m : ℕ) : ℕ := ∑ u ∈ range m, e j u

theorem V_eq (j m : ℕ) : V j m = ∑ i ∈ range (j + 1), E2 j i * (m + i).choose (2 * j + 1) := by
  induction m with
  | zero =>
    unfold V
    rw [sum_range_zero]
    refine (sum_eq_zero fun i hi => ?_).symm
    rw [mem_range] at hi
    rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
  | succ m ih =>
    unfold V at ih ⊢
    rw [sum_range_succ, ih, e_eq, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [show m + 1 + i = (m + i) + 1 by ring, Nat.choose_succ_succ']
    ring

/-- Coefficients in the binomial basis are unique. -/
theorem binom_unique (D : ℕ) (u v : ℕ → ℕ)
    (h : ∀ m : ℕ, ∑ d ∈ range (D + 1), m.choose d * u d
      = ∑ d ∈ range (D + 1), m.choose d * v d) :
    ∀ d ≤ D, u d = v d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    have trunc : ∀ w : ℕ → ℕ, ∑ d' ∈ range (D + 1), d.choose d' * w d'
        = ∑ d' ∈ range d, d.choose d' * w d' + w d := by
      intro w
      rw [← sum_subset (range_subset_range.2 (show d + 1 ≤ D + 1 by omega)), sum_range_succ,
        Nat.choose_self, one_mul]
      intro x _ hx
      rw [mem_range, not_lt] at hx
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
    have hm := h d
    have hs : ∑ d' ∈ range d, d.choose d' * u d' = ∑ d' ∈ range d, d.choose d' * v d' :=
      sum_congr rfl fun d' hd' => by
        rw [ih d' (mem_range.1 hd') (by have := mem_range.1 hd'; omega)]
    rw [trunc u, trunc v, hs] at hm
    exact Nat.add_left_cancel hm

/-- **The finite replacement for the write-up's averaging formula.** -/
theorem total (j : ℕ) (cnt : ℕ → ℕ)
    (h : ∀ m : ℕ, ∑ d ∈ range (2 * j + 1 + 1), m.choose d * cnt d
      = ∑ i ∈ range (j + 1), E2 j i * (m + i).choose (2 * j + 1)) :
    ∑ d ∈ range (2 * j + 1 + 1), cnt d = ∑ i ∈ range (j + 1), E2 j i * 2 ^ i := by
  set v : ℕ → ℕ := fun d => ∑ i ∈ range (j + 1), E2 j i * i.choose (2 * j + 1 - d) with hv
  have hvand : ∀ m : ℕ, ∑ d ∈ range (2 * j + 1 + 1), m.choose d * v d
      = ∑ i ∈ range (j + 1), E2 j i * (m + i).choose (2 * j + 1) := by
    intro m
    simp only [hv, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [Nat.add_choose_eq]
    simp only [Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
    exact sum_congr rfl fun d _ => by ring
  have huv := binom_unique (2 * j + 1) cnt v fun m => by rw [h m, hvand m]
  have hcv : ∑ d ∈ range (2 * j + 1 + 1), cnt d = ∑ d ∈ range (2 * j + 1 + 1), v d :=
    sum_congr rfl fun d hd => huv d (by have := mem_range.1 hd; omega)
  rw [hcv]
  simp only [hv]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [← mul_sum]
  have hi' := mem_range.1 hi
  have hrefl : ∑ d ∈ range (2 * j + 1 + 1), i.choose (2 * j + 1 + 1 - 1 - d)
      = ∑ d ∈ range (2 * j + 1 + 1), i.choose d :=
    sum_range_reflect (fun d => i.choose d) (2 * j + 1 + 1)
  have hr : ∑ d ∈ range (2 * j + 1 + 1), i.choose (2 * j + 1 - d)
      = ∑ d ∈ range (2 * j + 1 + 1), i.choose d := by
    rw [← hrefl]
    refine sum_congr rfl fun d _ => ?_
    congr 1 <;> omega
  rw [hr, ← sum_subset (range_subset_range.2 (show i + 1 ≤ 2 * j + 1 + 1 by omega)),
    Nat.sum_range_choose]
  intro x _ hx
  rw [mem_range, not_lt] at hx
  exact Nat.choose_eq_zero_of_lt (by omega)

end Principia.MathDB.P367940
