/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# MathDB #338641 — the exact deficit of the Bovdi–Leung cone

MathDB open problem #338641.  For `k ≥ 2` put `n = 4k+7`, `m = 4k`, `r = 2k`.  Section 4 of Bovdi
and Leung's construction produces a maximal commutative algebraic system `Cone ⊆ 𝒫ₙ(*)`, and the
source conjectures `|Cone| / 2^(n-2) → 1`.

The campaign result is the **exact identity**, which is strictly stronger:

  `|Cone| = 2^(n-2) - 3 · C(4k, 2k)`

so the observed strict inequality `|Cone| < 2^(n-2)` holds for every `k ≥ 2`, and the normalized
deficit tends to zero.  Campaign source: `mathdb-open-problems/problems/338641/` in the
collaborator repository `antoshashakov/Principia-Math-In-Progress`.

## The split between what is assumed and what is proved

The **layer data is an input, not a theorem here.**  That the exceptional layers at `r+1`, `r+3`,
`r+5` have sizes `B₁`, `7B₀+21B₁+7B₂+B₃` and `B₅+7B₄+21B₃+35B₂+35B₁+21B₀`, and that every odd
layer from `r+7` up is full, is a fact about Bovdi–Leung's construction.  Formalizing the
construction is a separate and much larger job, so it enters as the hypothesis `LayerData` —
never as an `axiom`.  Lean therefore certifies the **implication**, which is exactly the part the
campaign actually derived.

Everything downstream of that hypothesis is proved here: the odd-tail evaluation, the two
Vandermonde collections, and the cancellation.

## Statement shapes

`ℕ` subtraction truncates, so the identity is stated additively as
`cone + 3 * B k 0 = 2 ^ (4k+5)` rather than with a `-`.  `4k+5 = n-2`.

The alternating-tail identity the derivation needs is already in Mathlib
(`Int.alternating_sum_range_choose_eq_choose`), so no campaign copy of it is written.
-/
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Sqrt

namespace Principia.MathDB.P338641

open Finset

/-! ### The source's parameters -/

/-- `N k = 4k + 7`, the source's `n`. -/
def N (k : ℕ) : ℕ := 4 * k + 7

/-- `B k t = C(4k, 2k + t)`, the source's `B_t`. -/
def B (k t : ℕ) : ℕ := (4 * k).choose (2 * k + t)

/-- The odd upper tail `∑_{j ≥ s, j odd} C(N k, j)`. -/
def T (k s : ℕ) : ℕ :=
  ∑ j ∈ (Icc s (N k)).filter (fun j => j % 2 = 1), (N k).choose j

/-- The reflected coefficient `C(4k, 2k - t)` equals `B k t`; this is what lets the two
Vandermonde expansions be collected. -/
theorem choose_reflect (k t : ℕ) (ht : t ≤ 2 * k) :
    (4 * k).choose (2 * k - t) = B k t := by
  have h : 4 * k = (2 * k - t) + (2 * k + t) := by omega
  exact Nat.choose_symm_of_eq_add h

/-! ### The Bovdi–Leung layer data — the hypothesis -/

/-- The source's layer description: the three exceptional odd layers, and the fact that every odd
layer from `r + 7` upward is full.  This is Bovdi–Leung's construction, assumed here. -/
structure LayerData (k cone : ℕ) : Prop where
  decomposition :
    cone = B k 1
      + (7 * B k 0 + 21 * B k 1 + 7 * B k 2 + B k 3)
      + (B k 5 + 7 * B k 4 + 21 * B k 3 + 35 * B k 2 + 35 * B k 1 + 21 * B k 0)
      + T k (2 * k + 7)

/-! ### The combinatorial spine

Each lemma below is a link; `cone_add_deficit` is nothing but their composition. -/

-- The alternating partial sum `∑_{j ≤ s} (-1)^j C(M+1, j) = (-1)^s C(M, s)` is ALREADY IN
-- MATHLIB as `Int.alternating_sum_range_choose_eq_choose`; a campaign copy would be a
-- duplicate, so `upper_half_alternating` below calls it directly.

/-- `Icc a b = Ico a (b+1)` over `ℕ`, proved by `ext` rather than looked up: the name of the
library lemma moved, and an `ext`/`omega` proof cannot go stale. -/
theorem Icc_eq_Ico_succ (a b : ℕ) : Icc a b = Ico a (b + 1) := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

/-- The lower half of row `N k` — indices below `r + 4` — has size `2^(n-1)`.  `N k = 2(2k+3)+1`
is odd, so this is Mathlib's `Nat.sum_range_choose_halfway`. -/
theorem lower_half_card (k : ℕ) :
    ∑ j ∈ range (2 * k + 4), (N k).choose j = 2 ^ (4 * k + 6) := by
  have h : N k = 2 * (2 * k + 3) + 1 := by simp only [N]; omega
  have hm := Nat.sum_range_choose_halfway (2 * k + 3)
  rw [show 2 * k + 3 + 1 = 2 * k + 4 from by omega] at hm
  rw [h, hm, show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul]
  congr 1
  omega

/-- The upper half of row `N k` starting at `r + 4` has size `2^(n-1)`: the row totals `2^n` and
the lower half is `2^(n-1)`. -/
theorem upper_half_card (k : ℕ) :
    ∑ j ∈ Icc (2 * k + 4) (N k), (N k).choose j = 2 ^ (4 * k + 6) := by
  have hlow := lower_half_card k
  have htot : ∑ j ∈ range (N k + 1), (N k).choose j = 2 ^ (4 * k + 7) := by
    rw [Nat.sum_range_choose]; simp only [N]
  have hsplit :
      (∑ i ∈ Ico 0 (2 * k + 4), (N k).choose i)
        + ∑ i ∈ Ico (2 * k + 4) (N k + 1), (N k).choose i
        = ∑ i ∈ Ico 0 (N k + 1), (N k).choose i :=
    Finset.sum_Ico_consecutive _ (by omega) (by simp only [N]; omega)
  rw [← Finset.range_eq_Ico, ← Finset.range_eq_Ico] at hsplit
  rw [Icc_eq_Ico_succ]
  have hpow : (2 : ℕ) ^ (4 * k + 7) = 2 * 2 ^ (4 * k + 6) := by ring
  omega

/-- Within that upper half, `#even − #odd = C(n-1, r+3)`; this is
`Int.alternating_sum_range_choose_eq_choose` at the even index `s = r + 4`, where the full
alternating row sum vanishes. -/
theorem upper_half_alternating (k : ℕ) :
    ∑ j ∈ Icc (2 * k + 4) (N k), (-1 : ℤ) ^ j * ((N k).choose j : ℤ)
      = ((4 * k + 6).choose (2 * k + 3) : ℤ) := by
  have hN : N k = (4 * k + 6) + 1 := by simp only [N]
  have hpre : ∑ j ∈ range (2 * k + 4), (-1 : ℤ) ^ j * ((N k).choose j : ℤ)
      = -((4 * k + 6).choose (2 * k + 3) : ℤ) := by
    have hsign : (-1 : ℤ) ^ (2 * k + 3) = -1 := Odd.neg_one_pow ⟨k + 1, rfl⟩
    rw [hN, show 2 * k + 4 = (2 * k + 3) + 1 from by omega,
      Int.alternating_sum_range_choose_eq_choose, hsign]
    ring
  have htot : ∑ j ∈ range (N k + 1), (-1 : ℤ) ^ j * ((N k).choose j : ℤ) = 0 := by
    have h0 : N k ≠ 0 := by simp only [N]; omega
    exact Int.alternating_sum_range_choose_of_ne h0
  have hsplit :
      (∑ i ∈ Ico 0 (2 * k + 4), (-1 : ℤ) ^ i * ((N k).choose i : ℤ))
        + ∑ i ∈ Ico (2 * k + 4) (N k + 1), (-1 : ℤ) ^ i * ((N k).choose i : ℤ)
        = ∑ i ∈ Ico 0 (N k + 1), (-1 : ℤ) ^ i * ((N k).choose i : ℤ) :=
    Finset.sum_Ico_consecutive _ (by omega) (by simp only [N]; omega)
  rw [← Finset.range_eq_Ico, ← Finset.range_eq_Ico] at hsplit
  rw [hpre, htot] at hsplit
  rw [Icc_eq_Ico_succ]
  linarith

/-- Odd `j ≥ r + 4` is the same as odd `j ≥ r + 5`, because `r + 4` is even. -/
theorem filter_odd_shift (k : ℕ) :
    (Icc (2 * k + 4) (N k)).filter (fun j => j % 2 = 1)
      = (Icc (2 * k + 5) (N k)).filter (fun j => j % 2 = 1) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, h3⟩

/-- Evaluation of the odd tail from `r + 5`: the upper half splits into evens and odds, whose sum
is `2^(n-1)` and whose difference is `C(n-1, r+3)`. -/
theorem two_mul_tail_five (k : ℕ) :
    2 * T k (2 * k + 5) + (4 * k + 6).choose (2 * k + 3) = 2 ^ (4 * k + 6) := by
  classical
  set U : Finset ℕ := Icc (2 * k + 4) (N k) with hUdef
  set O : ℕ := ∑ j ∈ U.filter (fun j => j % 2 = 1), (N k).choose j with hOdef
  set E : ℕ := ∑ j ∈ U.filter (fun j => ¬ (j % 2 = 1)), (N k).choose j with hEdef
  have hsum : O + E = 2 ^ (4 * k + 6) := by
    rw [hOdef, hEdef, Finset.sum_filter_add_sum_filter_not, hUdef]
    exact upper_half_card k
  have hoddPart :
      (∑ j ∈ U.filter (fun j => j % 2 = 1), (-1 : ℤ) ^ j * ((N k).choose j : ℤ)) + (O : ℤ) = 0 := by
    rw [hOdef]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj2 : j % 2 = 1 := (Finset.mem_filter.mp hj).2
    have hs : (-1 : ℤ) ^ j = -1 := Odd.neg_one_pow ⟨j / 2, by omega⟩
    rw [hs]
    ring
  have hevenPart :
      (∑ j ∈ U.filter (fun j => ¬ (j % 2 = 1)), (-1 : ℤ) ^ j * ((N k).choose j : ℤ))
        = (E : ℤ) := by
    rw [hEdef]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj2 : ¬ (j % 2 = 1) := (Finset.mem_filter.mp hj).2
    have hs : (-1 : ℤ) ^ j = 1 := Even.neg_one_pow ⟨j / 2, by omega⟩
    rw [hs]
    ring
  have hsplit := Finset.sum_filter_add_sum_filter_not U (fun j => j % 2 = 1)
    (fun j => (-1 : ℤ) ^ j * ((N k).choose j : ℤ))
  have halt : (E : ℤ) - (O : ℤ) = ((4 * k + 6).choose (2 * k + 3) : ℤ) := by
    have hU2 : ∑ j ∈ U, (-1 : ℤ) ^ j * ((N k).choose j : ℤ)
        = ((4 * k + 6).choose (2 * k + 3) : ℤ) := by
      rw [hUdef]; exact upper_half_alternating k
    rw [hevenPart] at hsplit
    linarith [hsplit, hU2, hoddPart]
  have hT : T k (2 * k + 5) = O := by
    rw [hOdef, hUdef]
    simp only [T]
    rw [filter_odd_shift k]
  rw [hT]
  omega

/-- Peeling the layer at `r + 5` off the tail: `r + 6` is even, so the only odd index between
`r + 5` and `r + 7` is `r + 5` itself. -/
theorem tail_seven_add (k : ℕ) :
    T k (2 * k + 7) + (4 * k + 7).choose (2 * k + 5) = T k (2 * k + 5) := by
  classical
  have hins : (Icc (2 * k + 5) (N k)).filter (fun j => j % 2 = 1)
      = insert (2 * k + 5) ((Icc (2 * k + 7) (N k)).filter (fun j => j % 2 = 1)) := by
    ext j
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc, N]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases hj : j = 2 * k + 5
      · exact Or.inl hj
      · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨by omega, by omega⟩, by omega⟩
      · exact ⟨⟨by omega, h2⟩, h3⟩
  have hnot : (2 * k + 5) ∉ (Icc (2 * k + 7) (N k)).filter (fun j => j % 2 = 1) := by
    simp only [Finset.mem_filter, Finset.mem_Icc, N]
    omega
  simp only [T]
  rw [hins, Finset.sum_insert hnot]
  have hNk : N k = 4 * k + 7 := rfl
  rw [hNk]
  omega

/-- The seven-term Vandermonde expansion of `C(6 + 4k, 2k+3)`: only `i ≤ 6` contributes. -/
theorem vandermonde_six_expand (k : ℕ) (hk : 2 ≤ k) :
    (4 * k + 6).choose (2 * k + 3)
      = ∑ i ∈ range 7, (6).choose i * (4 * k).choose (2 * k + 3 - i) := by
  have hcomm : 4 * k + 6 = 6 + 4 * k := by omega
  have hsub : range 7 ⊆ range (2 * k + 3 + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hzero : ∀ x ∈ range (2 * k + 3 + 1), x ∉ range 7 →
      (6).choose x * (4 * k).choose (2 * k + 3 - x) = 0 := by
    intro x _ hx
    have hxb : 7 ≤ x := by
      simp only [Finset.mem_range, not_lt] at hx
      exact hx
    rw [Nat.choose_eq_zero_of_lt (show 6 < x by omega)]
    simp
  rw [hcomm, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Finset.sum_subset hsub hzero]

/-- **First Vandermonde collection**: `n - 1 = m + 6`, so
`C(n-1, r+3) = 2 (10B₀ + 15B₁ + 6B₂ + B₃)`. -/
theorem vandermonde_six (k : ℕ) (hk : 2 ≤ k) :
    (4 * k + 6).choose (2 * k + 3) = 2 * (10 * B k 0 + 15 * B k 1 + 6 * B k 2 + B k 3) := by
  rw [vandermonde_six_expand k hk]
  have b3 : (4 * k).choose (2 * k + 3 - 0) = B k 3 := by
    rw [show 2 * k + 3 - 0 = 2 * k + 3 from by omega]
    rfl
  have b2 : (4 * k).choose (2 * k + 3 - 1) = B k 2 := by
    rw [show 2 * k + 3 - 1 = 2 * k + 2 from by omega]
    rfl
  have b1 : (4 * k).choose (2 * k + 3 - 2) = B k 1 := by
    rw [show 2 * k + 3 - 2 = 2 * k + 1 from by omega]
    rfl
  have b0 : (4 * k).choose (2 * k + 3 - 3) = B k 0 := by
    rw [show 2 * k + 3 - 3 = 2 * k + 0 from by omega]
    rfl
  have r1 : (4 * k).choose (2 * k + 3 - 4) = B k 1 := by
    rw [show 2 * k + 3 - 4 = 2 * k - 1 from by omega]
    exact choose_reflect k 1 (by omega)
  have r2 : (4 * k).choose (2 * k + 3 - 5) = B k 2 := by
    rw [show 2 * k + 3 - 5 = 2 * k - 2 from by omega]
    exact choose_reflect k 2 (by omega)
  have r3 : (4 * k).choose (2 * k + 3 - 6) = B k 3 := by
    rw [show 2 * k + 3 - 6 = 2 * k - 3 from by omega]
    exact choose_reflect k 3 (by omega)
  have n0 : Nat.choose 6 0 = 1 := rfl
  have n1 : Nat.choose 6 1 = 6 := rfl
  have n2 : Nat.choose 6 2 = 15 := rfl
  have n3 : Nat.choose 6 3 = 20 := rfl
  have n4 : Nat.choose 6 4 = 15 := rfl
  have n5 : Nat.choose 6 5 = 6 := rfl
  have n6 : Nat.choose 6 6 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, b3, b2, b1, b0, r1, r2, r3,
    n0, n1, n2, n3, n4, n5, n6]
  ring

/-- The eight-term Vandermonde expansion of `C(7 + 4k, 2k+5)`. -/
theorem vandermonde_seven_expand (k : ℕ) (hk : 2 ≤ k) :
    (4 * k + 7).choose (2 * k + 5)
      = ∑ i ∈ range 8, (7).choose i * (4 * k).choose (2 * k + 5 - i) := by
  have hcomm : 4 * k + 7 = 7 + 4 * k := by omega
  have hsub : range 8 ⊆ range (2 * k + 5 + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hzero : ∀ x ∈ range (2 * k + 5 + 1), x ∉ range 8 →
      (7).choose x * (4 * k).choose (2 * k + 5 - x) = 0 := by
    intro x _ hx
    have hxb : 8 ≤ x := by
      simp only [Finset.mem_range, not_lt] at hx
      exact hx
    rw [Nat.choose_eq_zero_of_lt (show 7 < x by omega)]
    simp
  rw [hcomm, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Finset.sum_subset hsub hzero]

/-- **Second Vandermonde collection**: `n = m + 7`, so
`C(n, r+5) = B₅ + 7B₄ + 21B₃ + 36B₂ + 42B₁ + 21B₀`. -/
theorem vandermonde_seven (k : ℕ) (hk : 2 ≤ k) :
    (4 * k + 7).choose (2 * k + 5)
      = B k 5 + 7 * B k 4 + 21 * B k 3 + 36 * B k 2 + 42 * B k 1 + 21 * B k 0 := by
  rw [vandermonde_seven_expand k hk]
  have c5 : (4 * k).choose (2 * k + 5 - 0) = B k 5 := by
    rw [show 2 * k + 5 - 0 = 2 * k + 5 from by omega]
    rfl
  have c4 : (4 * k).choose (2 * k + 5 - 1) = B k 4 := by
    rw [show 2 * k + 5 - 1 = 2 * k + 4 from by omega]
    rfl
  have c3 : (4 * k).choose (2 * k + 5 - 2) = B k 3 := by
    rw [show 2 * k + 5 - 2 = 2 * k + 3 from by omega]
    rfl
  have c2 : (4 * k).choose (2 * k + 5 - 3) = B k 2 := by
    rw [show 2 * k + 5 - 3 = 2 * k + 2 from by omega]
    rfl
  have c1 : (4 * k).choose (2 * k + 5 - 4) = B k 1 := by
    rw [show 2 * k + 5 - 4 = 2 * k + 1 from by omega]
    rfl
  have c0 : (4 * k).choose (2 * k + 5 - 5) = B k 0 := by
    rw [show 2 * k + 5 - 5 = 2 * k + 0 from by omega]
    rfl
  have d1 : (4 * k).choose (2 * k + 5 - 6) = B k 1 := by
    rw [show 2 * k + 5 - 6 = 2 * k - 1 from by omega]
    exact choose_reflect k 1 (by omega)
  have d2 : (4 * k).choose (2 * k + 5 - 7) = B k 2 := by
    rw [show 2 * k + 5 - 7 = 2 * k - 2 from by omega]
    exact choose_reflect k 2 (by omega)
  have m0 : Nat.choose 7 0 = 1 := rfl
  have m1 : Nat.choose 7 1 = 7 := rfl
  have m2 : Nat.choose 7 2 = 21 := rfl
  have m3 : Nat.choose 7 3 = 35 := rfl
  have m4 : Nat.choose 7 4 = 35 := rfl
  have m5 : Nat.choose 7 5 = 21 := rfl
  have m6 : Nat.choose 7 6 = 7 := rfl
  have m7 : Nat.choose 7 7 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c5, c4, c3, c2, c1, c0, d1, d2,
    m0, m1, m2, m3, m4, m5, m6, m7]
  ring

/-! ### The exact identity -/

/-- **MathDB #338641, the exact form.**  Under the source's layer data,
`|Cone| = 2^(n-2) - 3 C(4k, 2k)`, stated additively. -/
theorem cone_add_deficit (k cone : ℕ) (hk : 2 ≤ k) (h : LayerData k cone) :
    cone + 3 * B k 0 = 2 ^ (4 * k + 5) := by
  have hd := h.decomposition
  have h5 := two_mul_tail_five k
  have h7 := tail_seven_add k
  have h6 := vandermonde_six k hk
  have hv7 := vandermonde_seven k hk
  have hpow : (2 : ℕ) ^ (4 * k + 6) = 2 * 2 ^ (4 * k + 5) := by ring
  omega

/-! ### The limit -/

/-- `C(2m,m)² (m+1) ≤ 16^m`: the elementary square bound on the central binomial coefficient.
Induction on `m` through `Nat.succ_mul_centralBinom_succ`; the step is the polynomial inequality
`4(2m+1)²(m+2) ≤ 16(m+1)³`, which holds because the two sides differ by `12m + 8`. -/
theorem centralBinom_sq_mul_le (m : ℕ) :
    ((2 * m).choose m) ^ 2 * (m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hrec : (m + 1) * ((2 * (m + 1)).choose (m + 1))
        = 2 * (2 * m + 1) * ((2 * m).choose m) := by
      have h := Nat.succ_mul_centralBinom_succ m
      simpa [Nat.centralBinom] using h
    have hsq : ((m + 1) * ((2 * (m + 1)).choose (m + 1))) ^ 2
        = (2 * (2 * m + 1)) ^ 2 * ((2 * m).choose m) ^ 2 := by
      rw [hrec]; ring
    have hpoly : 4 * (2 * m + 1) ^ 2 * (m + 2) ≤ 16 * (m + 1) ^ 3 := by nlinarith
    have key : (m + 1) ^ 3 * (((2 * (m + 1)).choose (m + 1)) ^ 2 * (m + 1 + 1))
        ≤ (m + 1) ^ 3 * 16 ^ (m + 1) := by
      calc (m + 1) ^ 3 * (((2 * (m + 1)).choose (m + 1)) ^ 2 * (m + 1 + 1))
          = ((m + 1) * ((2 * (m + 1)).choose (m + 1))) ^ 2 * ((m + 2) * (m + 1)) := by ring
        _ = (2 * (2 * m + 1)) ^ 2 * (((2 * m).choose m) ^ 2 * (m + 1)) * (m + 2) := by
            rw [hsq]; ring
        _ ≤ (2 * (2 * m + 1)) ^ 2 * 16 ^ m * (m + 2) := by gcongr
        _ = (4 * (2 * m + 1) ^ 2 * (m + 2)) * 16 ^ m := by ring
        _ ≤ (16 * (m + 1) ^ 3) * 16 ^ m := by gcongr
        _ = (m + 1) ^ 3 * 16 ^ (m + 1) := by ring
    have hpos : 0 < (m + 1) ^ 3 := by positivity
    exact Nat.le_of_mul_le_mul_left key hpos

/-- The central-binomial ratio `C(4k, 2k) / 2^(4k)` tends to zero.  Its square is at most
`1/(2k+1) ≤ 1/(k+1)` by `centralBinom_sq_mul_le`, so the ratio is squeezed by `√(1/(k+1))`. -/
theorem central_ratio_tendsto_zero :
    Filter.Tendsto (fun k : ℕ => ((4 * k).choose (2 * k) : ℝ) / 2 ^ (4 * k))
      Filter.atTop (nhds 0) := by
  have hnonneg : ∀ k : ℕ, (0 : ℝ) ≤ ((4 * k).choose (2 * k) : ℝ) / 2 ^ (4 * k) := by
    intro k; positivity
  have hbound : ∀ k : ℕ, ((4 * k).choose (2 * k) : ℝ) / 2 ^ (4 * k)
      ≤ Real.sqrt (1 / ((k : ℝ) + 1)) := by
    intro k
    have hnat := centralBinom_sq_mul_le (2 * k)
    have h4k : 2 * (2 * k) = 4 * k := by ring
    rw [h4k] at hnat
    have hpow : ((16 : ℝ)) ^ (2 * k) = (2 ^ (4 * k)) ^ 2 := by
      rw [← pow_mul, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]
      ring_nf
    have hcast : (((4 * k).choose (2 * k) : ℝ)) ^ 2 * ((2 * k : ℝ) + 1) ≤ (2 ^ (4 * k)) ^ 2 := by
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this
      calc (((4 * k).choose (2 * k) : ℝ)) ^ 2 * ((2 * k : ℝ) + 1) ≤ (16 : ℝ) ^ (2 * k) := this
        _ = (2 ^ (4 * k)) ^ 2 := hpow
    have hden : (0 : ℝ) < 2 ^ (4 * k) := by positivity
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hD2 : (0 : ℝ) < ((2 : ℝ) ^ (4 * k)) ^ 2 := by positivity
    have hkey : (((4 * k).choose (2 * k) : ℝ)) ^ 2 * ((k : ℝ) + 1) ≤ ((2 : ℝ) ^ (4 * k)) ^ 2 := by
      nlinarith [hcast, Nat.cast_nonneg (α := ℝ) k,
        sq_nonneg (((4 * k).choose (2 * k) : ℝ))]
    have hsq : (((4 * k).choose (2 * k) : ℝ) / 2 ^ (4 * k)) ^ 2 ≤ 1 / ((k : ℝ) + 1) := by
      rw [div_pow, div_le_iff₀ hD2]
      have hrw : (1 : ℝ) / ((k : ℝ) + 1) * ((2 : ℝ) ^ (4 * k)) ^ 2
          = ((2 : ℝ) ^ (4 * k)) ^ 2 / ((k : ℝ) + 1) := by ring
      rw [hrw, le_div_iff₀ hk1]
      linarith [hkey]
    calc ((4 * k).choose (2 * k) : ℝ) / 2 ^ (4 * k)
        = Real.sqrt ((((4 * k).choose (2 * k) : ℝ) / 2 ^ (4 * k)) ^ 2) :=
          (Real.sqrt_sq (hnonneg k)).symm
      _ ≤ Real.sqrt (1 / ((k : ℝ) + 1)) := Real.sqrt_le_sqrt hsq
  have hsqrt : Filter.Tendsto (fun k : ℕ => Real.sqrt (1 / ((k : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hcomp := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h0
    rw [Real.sqrt_zero] at hcomp
    simpa [Function.comp_def] using hcomp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsqrt hnonneg hbound

/-- `B k 0` is the central binomial coefficient. -/
theorem B_zero (k : ℕ) : B k 0 = (4 * k).choose (2 * k) := by
  simp [B]

/-- **The source's conjecture.**  `|Cone| / 2^(n-2) → 1`. -/
theorem cone_ratio_tendsto_one (cone : ℕ → ℕ)
    (h : ∀ k, 2 ≤ k → LayerData k (cone k)) :
    Filter.Tendsto (fun k : ℕ => (cone k : ℝ) / 2 ^ (4 * k + 5)) Filter.atTop (nhds 1) := by
  have hlim : Filter.Tendsto
      (fun k : ℕ => 1 - 3 / 32 * (((4 * k).choose (2 * k) : ℝ) / 2 ^ (4 * k)))
      Filter.atTop (nhds 1) := by
    have hmul := central_ratio_tendsto_zero.const_mul (3 / 32 : ℝ)
    have hsub := (tendsto_const_nhds (X := ℝ) (x := (1 : ℝ))
      (f := (Filter.atTop : Filter ℕ))).sub hmul
    simpa using hsub
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 2] with k hk
  have hd := cone_add_deficit k (cone k) hk (h k hk)
  rw [B_zero] at hd
  have hcast : (cone k : ℝ) + 3 * ((4 * k).choose (2 * k) : ℝ) = 2 ^ (4 * k + 5) := by
    exact_mod_cast hd
  have hpow : (2 : ℝ) ^ (4 * k + 5) = 32 * 2 ^ (4 * k) := by ring
  have hden : (0 : ℝ) < 2 ^ (4 * k) := by positivity
  rw [hpow] at hcast ⊢
  field_simp
  linarith [hcast]

/-! ### The carried hypothesis is inhabited, and the capstone specializes

`cone_ratio_tendsto_one` does not carry `LayerData` at a single `k`: it quantifies over a
FUNCTION `cone : ℕ → ℕ` and demands the spec at every `k ≥ 2`.  That is a strictly stronger
obligation than a one-point witness, and nothing above discharged it — so nothing above ruled
out the capstone holding vacuously.  No existing gate can see that: a vacuous theorem is
axiom-free, gates clean, and passes `check_unused_hypotheses`, because the hypothesis really
is used in the proof.

The structure's single field is an EQUATION pinning `cone` to a closed-form expression, so the
family is available definitionally and `rfl` discharges it.  The capstone then specializes to an
unconditional limit.

WHAT THIS DOES NOT DO.  `coneWitness` is the source's arithmetic expression for the layer sizes,
not a proof that the geometric cone's layers have those sizes.  That construction is this row's
real remaining debt — named in the module header as "a separate and much larger job" — and it is
untouched here.  What is established is that the spec is satisfiable, hence that the capstone and
the exact identity are not vacuous. -/

/-- The closed-form value `LayerData` pins `cone` to. -/
def coneWitness (k : ℕ) : ℕ :=
  B k 1
    + (7 * B k 0 + 21 * B k 1 + 7 * B k 2 + B k 3)
    + (B k 5 + 7 * B k 4 + 21 * B k 3 + 35 * B k 2 + 35 * B k 1 + 21 * B k 0)
    + T k (2 * k + 7)

/-- `LayerData` is satisfiable at every `k`, by `rfl`: its one field is an equation. -/
theorem layerData_coneWitness (k : ℕ) : LayerData k (coneWitness k) := ⟨rfl⟩

/-- The capstone's hypothesis shape, discharged: a uniform family does exist. -/
theorem exists_layerData_family : ∃ cone : ℕ → ℕ, ∀ k, 2 ≤ k → LayerData k (cone k) :=
  ⟨coneWitness, fun k _ => layerData_coneWitness k⟩

/-- The exact additive identity at the witness, with no hypothesis carried. -/
theorem coneWitness_add_deficit (k : ℕ) (hk : 2 ≤ k) :
    coneWitness k + 3 * B k 0 = 2 ^ (4 * k + 5) :=
  cone_add_deficit k (coneWitness k) hk (layerData_coneWitness k)

/-- **The capstone at the witness, unconditional.** -/
theorem coneWitness_ratio_tendsto_one :
    Filter.Tendsto (fun k : ℕ => (coneWitness k : ℝ) / 2 ^ (4 * k + 5)) Filter.atTop (nhds 1) :=
  cone_ratio_tendsto_one coneWitness fun k _ => layerData_coneWitness k

end Principia.MathDB.P338641
