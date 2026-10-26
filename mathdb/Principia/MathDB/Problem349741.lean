import Mathlib

/-!
# MathDB #349741 — semicompleteness of the hypercube division sequences

Write-up `mathdb-open-problems/problems/349741/solution.tex`, 18 September 2026.

`C_M^N`, the maximum number of pieces of an `M`-dimensional hypercube cut by `N−1` hyperplanes,
is `∑_{i≤M} C(N−1, i)`.  Hoelscher's Conjecture 1.3 asks whether every integer below the mean of
a prefix is a sum of distinct terms of that prefix; the write-up proves the stronger statement
that **every** integer from `0` to the whole prefix sum is such a sum.

Everything here is indexed from `0`: `pieces M n = ∑_{i≤M} C(n, i)` is the source's `C_M^{n+1}`.
That removes every truncating `ℕ` subtraction from the development.

## The shape of the argument

`brown` is Brown's classical criterion — if `b 0 = 1` and `b (n+1) ≤ 1 + ∑_{k≤n} b k`, then every
`t` up to a prefix sum is a subset sum of that prefix.  Its inductive step turns on one
inequality: when `t` exceeds the prefix sum `S j`, growth gives `b j ≤ 1 + S j ≤ t`, which is
exactly what makes `t − b j` a legitimate (non-negative) target for the induction hypothesis.

`pieces_growth` supplies that hypothesis via the hockey stick `∑_{k≤n} C(k,i) = C(n+1, i+1)`
(`Nat.sum_Icc_choose`), after which the condition reduces to
`∑_{i=1}^{M} C(n+1,i) ≤ ∑_{i=1}^{M+1} C(n+1,i)`, which is monotonicity of a sum of extra
nonnegative terms.

A first attempt to get growth from the last term alone fails and is worth not retrying:
`C(n+1,i) = C(n,i) + C(n,i−1)` leaves `∑_{i<M} C(n,i) ≤ 1`, false in general.  The full prefix
sum is genuinely needed.

Neither Brown's criterion nor the region-count formula is new; the source claims only the
extension to all `M`, and this file follows that scope.

Checked in Python before formalizing: `M = 2` gives `1,2,4,7,11,16` (lazy-caterer) and `M = 3`
gives `1,2,4,8,15,26` (cake numbers); the growth condition holds for `M ≤ 8`, `N < 40`; the
hockey-stick form for `M ≤ 6`, `N ≤ 24`; and the subset-sum claim was brute-forced with no gaps
for `M ≤ 3`, `j ≤ 9`.
-/

namespace Principia.MathDB.P349741

open Finset

/-- `range m ⊆ range (m+1)`.  Note `Finset.range_subset` is NOT the endpoint comparison — that
is `Multiset.range_subset`; the `Finset` one unfolds the subset itself. -/
theorem range_succ_subset (m : ℕ) : range m ⊆ range (m + 1) :=
  Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega)

/-- `pieces M n = ∑_{i ≤ M} C(n, i)`, the source's `C_M^{n+1}`. -/
def pieces (M n : ℕ) : ℕ := ∑ i ∈ range (M + 1), n.choose i

/-- The hockey stick in the form needed: `∑_{k ≤ n} C(k, i) = C(n+1, i+1)`.  Terms with `k < i`
vanish, so the `range` sum agrees with Mathlib's `Icc` version. -/
theorem sum_range_choose_eq (n i : ℕ) :
    ∑ k ∈ range (n + 1), k.choose i = (n + 1).choose (i + 1) := by
  by_cases h : i ≤ n
  · rw [← Nat.sum_Icc_choose n i]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro x hx
      rw [mem_Icc] at hx
      rw [mem_range]
      omega
    · intro x hx hnot
      rw [mem_range] at hx
      rw [mem_Icc] at hnot
      exact Nat.choose_eq_zero_of_lt (by omega)
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [mem_range] at hx
    exact Nat.choose_eq_zero_of_lt (by omega)

/-- `pieces M 0 = 1`: only `i = 0` contributes. -/
theorem pieces_zero (M : ℕ) : pieces M 0 = 1 := by
  unfold pieces
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    exact Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb)
  · intro h
    exact absurd (mem_range.mpr (Nat.succ_pos M)) h

/-- The prefix sum of `pieces`, via the hockey stick. -/
theorem sum_pieces (M n : ℕ) :
    ∑ k ∈ range (n + 1), pieces M k = ∑ i ∈ range (M + 1), (n + 1).choose (i + 1) := by
  unfold pieces
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => sum_range_choose_eq n i

/-- **The growth condition.**  `pieces M (n+1) ≤ 1 + ∑_{k ≤ n} pieces M k`. -/
theorem pieces_growth (M n : ℕ) :
    pieces M (n + 1) ≤ 1 + ∑ k ∈ range (n + 1), pieces M k := by
  rw [sum_pieces]
  unfold pieces
  rw [Finset.sum_range_succ' (fun i => (n + 1).choose i) M]
  simp only [Nat.choose_zero_right]
  have : ∑ i ∈ range M, (n + 1).choose (i + 1) ≤ ∑ i ∈ range (M + 1), (n + 1).choose (i + 1) := by
    apply Finset.sum_le_sum_of_subset
    exact range_succ_subset M
  omega

/-- **Brown's criterion.**  The step turns on `b j ≤ 1 + S j ≤ t`, which is what makes `t − b j`
a valid target for the induction hypothesis. -/
theorem brown (b : ℕ → ℕ) (h0 : b 0 = 1)
    (hgrow : ∀ n, b (n + 1) ≤ 1 + ∑ k ∈ range (n + 1), b k) :
    ∀ j t, t ≤ ∑ k ∈ range j, b k → ∃ I ⊆ range j, ∑ i ∈ I, b i = t := by
  intro j
  induction j with
  | zero =>
    intro t ht
    simp only [range_zero, Finset.sum_empty, Nat.le_zero] at ht
    exact ⟨∅, by simp, by simp [ht]⟩
  | succ j ih =>
    intro t ht
    rw [Finset.sum_range_succ] at ht
    by_cases hle : t ≤ ∑ k ∈ range j, b k
    · obtain ⟨I, hI, hsum⟩ := ih t hle
      exact ⟨I, hI.trans (range_succ_subset j), hsum⟩
    · have hgt : ∑ k ∈ range j, b k < t := by omega
      have hbj : b j ≤ t := by
        cases j with
        | zero => simp only [range_zero, Finset.sum_empty] at hgt; omega
        | succ m =>
          have := hgrow m
          simp only [Finset.sum_range_succ] at hgt ⊢
          omega
      obtain ⟨I, hI, hsum⟩ := ih (t - b j) (by omega)
      have hnot : j ∉ I := fun hc => by
        have := mem_range.mp (hI hc); omega
      refine ⟨insert j I, ?_, ?_⟩
      · intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · exact mem_range.mpr (Nat.lt_succ_self _)
        · exact range_succ_subset j (hI hx)
      · rw [Finset.sum_insert hnot, hsum]
        omega

/-- **MathDB #349741 — Hoelscher's Conjecture 1.3 holds, in the stronger prefix form.**  Every
`t` from `0` to the full prefix sum is a sum of distinct terms of that prefix. -/
theorem main (M j t : ℕ) (ht : t ≤ ∑ k ∈ range j, pieces M k) :
    ∃ I ⊆ range j, ∑ i ∈ I, pieces M i = t :=
  brown (pieces M) (pieces_zero M) (pieces_growth M) j t ht

end Principia.MathDB.P349741
