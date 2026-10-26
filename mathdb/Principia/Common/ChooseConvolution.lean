/-
# A Vandermonde-type convolution for binomial coefficients

`choose_convolution` below is the whole residue of #334350's truncated bands, and it
mentions **no** object of that campaign: neither the part bound `n`, nor the number of
parts `j`, nor any truncation.  Measurement is what revealed that -- the campaign's own
record described the residue as "a family of identities indexed by the number of parts
exceeding `n`", but the family is one identity with every index free, and `n` enters only
through a parameter that the identity never constrains.  So it is recorded here, where
the next campaign can find it, rather than in `Principia/MathDB/`.

Vandermonde comes from `Principia.Common.vandermonde_range`, which this campaign already
had.  An earlier draft of this file re-proved it, because the search for it went to Mathlib
and never to `Common/`.  The duplicate is gone.

The proof is Pascal twice on the left and trinomial revision plus Vandermonde on the
right; the two halves meet at
`C(s-1,k-1) * C(M+s-k, j-k) + C(s-1,k) * C(M+s-k-1, j-k-1)`.

Everything is stated **subtraction-free in the parameters** (`t` for `s-1`, `c` for
`M-k`, `d` for `j-k`, and `k+1` for the index that the campaign's sum starts at), because
`Nat` truncated subtraction in a *statement* is what makes such an identity false at its
own boundary.  The only subtractions left are `d - i` inside a sum over `range (d+1)`,
where the index is genuinely below the bound.
-/
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Principia.Common.Vandermonde

namespace Principia.Common

open Finset

/-- Trinomial revision in the additive shape the convolution consumes: `Nat.choose_mul`
with the subtraction on the right already cancelled. -/
theorem choose_mul_choose_add (t k i : ℕ) :
    t.choose (k + i) * (k + i).choose k = t.choose k * (t - k).choose i := by
  have h := Nat.choose_mul (n := t) (k := k + i) (s := k) (Nat.le_add_right k i)
  simpa using h

/-- The convolution identity.  Reading `t = s-1`, `c = M-k`, `d = j-k` and the summation
index `e = k+1+i`, this is

`C(s+M-k, j-k) * C(s,k) - C(s+M-k-1, j-k) * C(s-1,k)
    = ∑_{e=k}^{j} C(M, j-e) * C(e,k) * C(s-1, e-1)`

with the subtracted term moved to the right so that no subtraction appears. -/
theorem choose_convolution (t c d k : ℕ) :
    (t + 1 + c).choose d * (t + 1).choose (k + 1)
      = (t + c).choose d * t.choose (k + 1)
        + ∑ i ∈ range (d + 1),
            (k + 1 + c).choose (d - i) * (k + 1 + i).choose (k + 1) * t.choose (k + i) := by
  rcases lt_or_ge t k with hkt | hkt
  · -- `k > t`: every `choose` taken at `t` vanishes, on both sides.
    have h1 : (t + 1).choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : t.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h3 : ∑ i ∈ range (d + 1),
        (k + 1 + c).choose (d - i) * (k + 1 + i).choose (k + 1) * t.choose (k + i) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        have hz : t.choose (k + i) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hz, Nat.mul_zero]
    rw [h1, h2, h3, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
  rcases eq_or_lt_of_le hkt with heq | hkt'
  · -- `k = t`: only the `i = 0` term of the sum survives, and it is the whole left side.
    have h2 : t.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h3 : ∑ i ∈ range (d + 1),
        (k + 1 + c).choose (d - i) * (k + 1 + i).choose (k + 1) * t.choose (k + i)
          = (k + 1 + c).choose (d - 0) * (k + 1 + 0).choose (k + 1) * t.choose (k + 0) := by
      refine Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos d)) ?_
      intro i _ hi
      have hz : t.choose (k + i) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hz, Nat.mul_zero]
    rw [h2, h3, Nat.mul_zero, Nat.zero_add]
    subst heq
    simp
  -- the substantial case, `k + 1 ≤ t`.
  have hA : k + 1 + c + (t - k) = t + 1 + c := by omega
  have hB : k + 1 + c + (t - (k + 1)) = t + c := by omega
  have hsplit : ∀ i ∈ range (d + 1),
      (k + 1 + c).choose (d - i) * (k + 1 + i).choose (k + 1) * t.choose (k + i)
        = (k + 1 + c).choose (d - i) * (t.choose k * (t - k).choose i)
          + (k + 1 + c).choose (d - i) * ((k + i).choose (k + 1) * t.choose (k + i)) := by
    intro i _
    have hp : (k + 1 + i).choose (k + 1) = (k + i).choose k + (k + i).choose (k + 1) := by
      have h : k + 1 + i = k + i + 1 := by omega
      rw [h, Nat.choose_succ_succ']
    have ht : (k + i).choose k * t.choose (k + i) = t.choose k * (t - k).choose i := by
      rw [mul_comm]
      exact choose_mul_choose_add t k i
    calc (k + 1 + c).choose (d - i) * (k + 1 + i).choose (k + 1) * t.choose (k + i)
        = (k + 1 + c).choose (d - i) * ((k + i).choose k * t.choose (k + i))
          + (k + 1 + c).choose (d - i) * ((k + i).choose (k + 1) * t.choose (k + i)) := by
          rw [hp]; ring
      _ = _ := by rw [ht]
  have hs1 : ∑ i ∈ range (d + 1), (k + 1 + c).choose (d - i) * (t.choose k * (t - k).choose i)
      = t.choose k * (t + 1 + c).choose d := by
    rw [← hA, ← vandermonde_range (k + 1 + c) (t - k) d, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hs2 : ∑ i ∈ range (d + 1),
      (k + 1 + c).choose (d - i) * ((k + i).choose (k + 1) * t.choose (k + i))
      = t.choose (k + 1)
          * ∑ j ∈ range d, (k + 1 + c).choose (d - 1 - j) * (t - (k + 1)).choose j := by
    rw [Finset.sum_range_succ']
    have hz : (k + 1 + c).choose (d - 0) * ((k + 0).choose (k + 1) * t.choose (k + 0)) = 0 := by
      simp
    rw [hz, Nat.add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsub : d - (j + 1) = d - 1 - j := by omega
    have ht : (k + (j + 1)).choose (k + 1) * t.choose (k + (j + 1))
        = t.choose (k + 1) * (t - (k + 1)).choose j := by
      have hidx : k + (j + 1) = k + 1 + j := by omega
      rw [hidx, mul_comm]
      exact choose_mul_choose_add t (k + 1) j
    rw [hsub, ht]
    ring
  have hinner : (t + c).choose d
      + ∑ j ∈ range d, (k + 1 + c).choose (d - 1 - j) * (t - (k + 1)).choose j
      = (t + 1 + c).choose d := by
    cases d with
    | zero => simp
    | succ e =>
      have h1 : ∑ j ∈ range (e + 1),
          (k + 1 + c).choose (e + 1 - 1 - j) * (t - (k + 1)).choose j = (t + c).choose e := by
        rw [← hB, ← vandermonde_range (k + 1 + c) (t - (k + 1)) e]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show e + 1 - 1 - j = e - j from by omega]
      rw [h1, show t + 1 + c = t + c + 1 from by omega, Nat.choose_succ_succ' (t + c) e]
      omega
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hs1, hs2,
    Nat.choose_succ_succ' t k, ← hinner]
  ring

/-- **`choose_convolution` reindexed onto a full `range`.**  Substituting `e = κ + i` turns the
sum over `range (d+1)` into a sum over `range (d+κ+1)`: the extra terms `e < κ` vanish because
`C(e+1, κ+1) = 0` there, so the range may be taken to start at `0`.  This is the shape a
consumer produces when its outer index runs over all parts rather than over the offset. -/
theorem choose_convolution_range (t c d k : ℕ) :
    (t + 1 + c).choose d * (t + 1).choose (k + 1)
      = (t + c).choose d * t.choose (k + 1)
        + ∑ e ∈ range (d + k + 1),
            (k + 1 + c).choose (d + k - e) * (e + 1).choose (k + 1) * t.choose e := by
  classical
  have hmap : ∑ e ∈ (range (d + 1)).map ⟨fun i => k + i, add_right_injective k⟩,
      (k + 1 + c).choose (d + k - e) * (e + 1).choose (k + 1) * t.choose e
      = ∑ i ∈ range (d + 1),
          (k + 1 + c).choose (d + k - (k + i)) * (k + i + 1).choose (k + 1) * t.choose (k + i) :=
    Finset.sum_map _ _ _
  have hsub : ∑ e ∈ (range (d + 1)).map ⟨fun i => k + i, add_right_injective k⟩,
      (k + 1 + c).choose (d + k - e) * (e + 1).choose (k + 1) * t.choose e
      = ∑ e ∈ range (d + k + 1),
          (k + 1 + c).choose (d + k - e) * (e + 1).choose (k + 1) * t.choose e := by
    refine Finset.sum_subset ?_ ?_
    · intro e he
      simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk] at he
      obtain ⟨i, hi, rfl⟩ := he
      simp only [Finset.mem_range]
      omega
    · intro e he hne
      have hlt : e < k := by
        simp only [Finset.mem_range] at he
        by_contra hk
        exact hne (by
          simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
          exact ⟨e - k, by omega, by omega⟩)
      have : (e + 1).choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [this]
      ring
  rw [← hsub, hmap]
  have hcong : ∀ i ∈ range (d + 1),
      (k + 1 + c).choose (d + k - (k + i)) * (k + i + 1).choose (k + 1) * t.choose (k + i)
        = (k + 1 + c).choose (d - i) * (k + 1 + i).choose (k + 1) * t.choose (k + i) := by
    intro i _
    have h1 : d + k - (k + i) = d - i := by omega
    have h2 : k + i + 1 = k + 1 + i := by omega
    rw [h1, h2]
  rw [Finset.sum_congr rfl hcong]
  exact choose_convolution t c d k

end Principia.Common
