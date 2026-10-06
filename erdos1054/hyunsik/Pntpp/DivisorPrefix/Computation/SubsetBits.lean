import Pntpp.DivisorPrefix.SubsetSums

namespace Pntpp.DivisorPrefix.Computation

/-- Truncated subset-sum dynamic programming, with one bit for each attainable sum. -/
def subsetBits (limit : ℕ) : List ℕ → ℕ
  | [] => 1
  | p :: ps =>
    let b := subsetBits limit ps
    (b ||| (b <<< p)) &&& ((1 <<< (limit + 1)) - 1)

theorem subsetBits_sound {limit n : ℕ} {ps : List ℕ}
    (hd : ps.Nodup) (h : (subsetBits limit ps).testBit n = true) :
    IsSubsetSum ps.toFinset n := by
  induction ps generalizing n with
  | nil =>
    have hn : n = 0 := Nat.testBit_one_eq_true_iff_self_eq_zero.mp h
    subst n
    exact ⟨∅, by simp, by simp⟩
  | cons p ps ih =>
    rw [List.nodup_cons] at hd
    simp only [subsetBits, Nat.testBit_and, Nat.testBit_or,
      Nat.testBit_shiftLeft, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h.1 with h | ⟨hpn, h⟩
    · obtain ⟨s, hs, hsum⟩ := ih hd.2 h
      exact ⟨s, hs.trans (by simp), hsum⟩
    · obtain ⟨s, hs, hsum⟩ := ih hd.2 h
      have hp : p ∉ s := fun hp => hd.1 (List.mem_toFinset.mp (hs hp))
      refine ⟨insert p s, ?_, ?_⟩
      · simpa using Finset.insert_subset_insert p hs
      · rw [Finset.sum_insert hp, hsum]
        omega

/-- Named computation boundary keeps theorem application from reevaluating the bitset. -/
def subsetBitsCover (limit lo hi : ℕ) (ps : List ℕ) : Prop :=
  ((subsetBits limit ps >>> lo) &&& ((1 <<< (hi - lo + 1)) - 1)) =
    ((1 <<< (hi - lo + 1)) - 1)

instance (limit lo hi : ℕ) (ps : List ℕ) : Decidable (subsetBitsCover limit lo hi ps) :=
  inferInstanceAs (Decidable
    (((subsetBits limit ps >>> lo) &&& ((1 <<< (hi - lo + 1)) - 1)) =
      ((1 <<< (hi - lo + 1)) - 1)))

/-- A single bitwise equality certifies every value in a closed interval. -/
theorem subsetBits_interval {limit lo hi : ℕ} {ps : List ℕ}
    (hd : ps.Nodup)
    (h : subsetBitsCover limit lo hi ps) :
    ∀ n, lo ≤ n → n ≤ hi → IsSubsetSum ps.toFinset n := by
  unfold subsetBitsCover at h
  intro n hlo hhi
  apply subsetBits_sound (limit := limit) hd
  have hn : n - lo < hi - lo + 1 := by omega
  have heq := congrArg (fun b : ℕ => b.testBit (n - lo)) h
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.shiftLeft_eq,
    Nat.one_mul, Nat.testBit_two_pow_sub_one, hn, decide_true,
    Bool.and_true] at heq
  simpa only [Nat.add_sub_of_le hlo] using heq

end Pntpp.DivisorPrefix.Computation
