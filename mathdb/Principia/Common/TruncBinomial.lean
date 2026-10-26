/-
# The truncating integer binomial

`ibin a k` is `C(a, k)` for `a ≥ 0` and `0` for `a < 0`.  It is the coefficient that *counting*
identities over `ℤ` need, and it is **not** `Ring.choose`: the generalized binomial stays
non-zero at negative arguments, where a count is zero.  That difference is not cosmetic — the
inclusion–exclusion formula for compositions with bounded parts is **false** with `Ring.choose`
(measured: 120 mismatches, every one at a negative argument, in
`Campaigns/MathDB-Formalization/probe_334350_vt.py`), and true with `ibin`.  Since both spellings
typecheck, the negative control is the only thing separating them.

Two facts are proved, and they are exactly what an induction over the number of parts consumes:

* `ibin_pascal` — Pascal, valid for **every** integer, with no side condition.  The lower index
  is written `k + 1` so that the `a < 0` and `a = 0` cases agree with the generic one instead of
  needing their own hypotheses; at lower index `0` the statement would be false at `a = 0`.
* `ibin_telescope` — `∑_{a=1}^{n} ibin (z - a) k = ibin z (k+1) - ibin (z-n) (k+1)`, the discrete
  antiderivative, which is where the summation over one part's value goes.
-/
import Mathlib

namespace Principia.Common

open Finset

/-- `C(a, k)` for `a ≥ 0`, and `0` for `a < 0`. -/
def ibin (a : ℤ) (k : ℕ) : ℤ := if 0 ≤ a then (a.toNat.choose k : ℤ) else 0

theorem ibin_of_neg {a : ℤ} (k : ℕ) (h : a < 0) : ibin a k = 0 := by
  simp [ibin, not_le.2 h]

theorem ibin_of_nonneg {a : ℤ} (k : ℕ) (h : 0 ≤ a) :
    ibin a k = (a.toNat.choose k : ℤ) := by
  simp [ibin, h]

theorem ibin_nonneg (a : ℤ) (k : ℕ) : 0 ≤ ibin a k := by
  unfold ibin
  split
  · exact Int.natCast_nonneg _
  · exact le_refl 0

/-- **Pascal for `ibin`, with no side condition on the argument.**  At lower index `k+1` the
negative and zero cases agree with the generic one, which is what lets `ibin_telescope` avoid a
case split. -/
theorem ibin_pascal (z : ℤ) (k : ℕ) :
    ibin z (k + 1) - ibin (z - 1) (k + 1) = ibin (z - 1) k := by
  rcases lt_trichotomy z 0 with h | h | h
  · rw [ibin_of_neg _ h, ibin_of_neg _ (by omega), ibin_of_neg _ (by omega)]
    ring
  · subst h
    rw [ibin_of_nonneg _ (le_refl 0), ibin_of_neg _ (by norm_num), ibin_of_neg _ (by norm_num)]
    simp
  · have hz1 : (0 : ℤ) ≤ z - 1 := by omega
    obtain ⟨Z, hZ⟩ : ∃ Z, z.toNat = Z + 1 := ⟨z.toNat - 1, by omega⟩
    have h1 : (z - 1).toNat = Z := by omega
    rw [ibin_of_nonneg _ (le_of_lt h), ibin_of_nonneg _ hz1, ibin_of_nonneg _ hz1, hZ, h1,
      Nat.choose_succ_succ' Z k]
    push_cast
    ring

/-- **The discrete antiderivative.**  Summing `ibin (· ) k` over one part's value telescopes. -/
theorem ibin_telescope (n : ℕ) (z : ℤ) (k : ℕ) :
    ∑ a ∈ Icc 1 n, ibin (z - (a : ℤ)) k = ibin z (k + 1) - ibin (z - (n : ℤ)) (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hins : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
        ext a
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : (n + 1) ∉ Icc 1 n := by
        simp only [Finset.mem_Icc]
        omega
      rw [hins, Finset.sum_insert hnot, ih]
      have hp := ibin_pascal (z - (n : ℤ)) k
      have harg : z - ((n + 1 : ℕ) : ℤ) = z - (n : ℤ) - 1 := by push_cast; ring
      rw [harg]
      linarith [hp]

/-- **The alternating binomial transform of a first difference raises the binomial index.**
For any `u`, `∑_{i≤m} (-1)^i C(m,i) (u i - u (i+1)) = ∑_{i≤m+1} (-1)^i C(m+1,i) u i`.  This is
Pascal in disguise: the `u (i+1)` half reindexes onto `C(m, i-1)`, and the top term vanishes
because `C(m, m+1) = 0`.  It is what reassembles the coefficients after a telescoping.

The sign is folded into the exponent throughout (`-((-1)^i x) = (-1)^(i+1) x`) so that no
negation of a *sum* ever appears; every step is then `sum_add_distrib` plus one
`Finset.sum_congr`. -/
theorem alt_binom_diff_sum (u : ℕ → ℤ) (m : ℕ) :
    ∑ i ∈ range (m + 1), (-1 : ℤ) ^ i * (m.choose i : ℤ) * (u i - u (i + 1))
      = ∑ i ∈ range (m + 2), (-1 : ℤ) ^ i * ((m + 1).choose i : ℤ) * u i := by
  have hsplit : ∀ i ∈ range (m + 1),
      (-1 : ℤ) ^ i * (m.choose i : ℤ) * (u i - u (i + 1))
        = (-1 : ℤ) ^ i * (m.choose i : ℤ) * u i
          + (-1 : ℤ) ^ (i + 1) * (m.choose i : ℤ) * u (i + 1) := by
    intro i _
    rw [pow_succ]
    ring
  have hR : ∑ i ∈ range (m + 2), (-1 : ℤ) ^ i * ((m + 1).choose i : ℤ) * u i
      = (∑ i ∈ range (m + 1), (-1 : ℤ) ^ (i + 1) * ((m + 1).choose (i + 1) : ℤ) * u (i + 1))
        + (-1 : ℤ) ^ 0 * ((m + 1).choose 0 : ℤ) * u 0 :=
    Finset.sum_range_succ' (fun i => (-1 : ℤ) ^ i * ((m + 1).choose i : ℤ) * u i) (m + 1)
  have hpas : ∀ i ∈ range (m + 1),
      (-1 : ℤ) ^ (i + 1) * ((m + 1).choose (i + 1) : ℤ) * u (i + 1)
        = (-1 : ℤ) ^ (i + 1) * (m.choose i : ℤ) * u (i + 1)
          + (-1 : ℤ) ^ (i + 1) * (m.choose (i + 1) : ℤ) * u (i + 1) := by
    intro i _
    rw [Nat.choose_succ_succ' m i]
    push_cast
    ring
  have htop : ∑ i ∈ range (m + 1), (-1 : ℤ) ^ (i + 1) * (m.choose (i + 1) : ℤ) * u (i + 1)
      = ∑ i ∈ range m, (-1 : ℤ) ^ (i + 1) * (m.choose (i + 1) : ℤ) * u (i + 1) := by
    rw [Finset.sum_range_succ]
    have hz : (m.choose (m + 1) : ℤ) = 0 := by
      rw [Nat.choose_succ_self]
      norm_num
    rw [hz]
    ring
  have hA2 : ∑ i ∈ range m, (-1 : ℤ) ^ (i + 1) * (m.choose (i + 1) : ℤ) * u (i + 1)
      = (∑ i ∈ range (m + 1), (-1 : ℤ) ^ i * (m.choose i : ℤ) * u i) - u 0 := by
    rw [Finset.sum_range_succ' (fun i => (-1 : ℤ) ^ i * (m.choose i : ℤ) * u i) m]
    norm_num
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hR,
    Finset.sum_congr rfl hpas, Finset.sum_add_distrib, htop, hA2]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul]
  ring

end Principia.Common
