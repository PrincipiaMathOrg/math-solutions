/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/SubsetSums.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.Statement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pntpp.DivisorPrefix

/-- A natural number is a sum of a subset of `A`. -/
def IsSubsetSum (A : Finset ℕ) (n : ℕ) : Prop :=
  ∃ s : Finset ℕ, s ⊆ A ∧ ∑ x ∈ s, x = n

/-- A list whose successive adjunctions satisfy the interval-extension inequality. -/
def IsSubsetSumExtensionChain
    (A : Finset ℕ) (C U : ℕ) : List ℕ → Prop
  | [] => True
  | p :: ps =>
      p ∉ A ∧
      p ≤ U - C + 1 ∧
      IsSubsetSumExtensionChain (insert p A) C (U + p) ps

theorem subsetSum_interval_extension
    {A : Finset ℕ} {C U p : ℕ}
    (hCU : C ≤ U)
    (hpA : p ∉ A)
    (hcover : ∀ n, C ≤ n → n ≤ U → IsSubsetSum A n)
    (hp : p ≤ U - C + 1) :
    ∀ n, C ≤ n → n ≤ U + p → IsSubsetSum (insert p A) n := by
  intro n hCn hnUp
  by_cases hnU : n ≤ U
  · obtain ⟨s, hsA, hsum⟩ := hcover n hCn hnU
    exact ⟨s, hsA.trans (Finset.subset_insert p A), hsum⟩
  · have hpn : p ≤ n := by omega
    have hCsub : C ≤ n - p := by omega
    have hsubU : n - p ≤ U := by omega
    obtain ⟨s, hsA, hsum⟩ := hcover (n - p) hCsub hsubU
    have hps : p ∉ s := fun hps => hpA (hsA hps)
    refine ⟨insert p s, Finset.insert_subset_insert p hsA, ?_⟩
    simp [hps, hsum, Nat.add_sub_of_le hpn]

theorem subsetSum_extension_chain
    {A : Finset ℕ} {C U : ℕ} {ps : List ℕ}
    (hCU : C ≤ U)
    (hcover : ∀ n, C ≤ n → n ≤ U → IsSubsetSum A n)
    (hchain : IsSubsetSumExtensionChain A C U ps) :
    ∀ n,
      C ≤ n →
      n ≤ U + ps.sum →
      IsSubsetSum (A ∪ ps.toFinset) n := by
  induction ps generalizing A U with
  | nil =>
      simpa using hcover
  | cons p ps ih =>
      rcases hchain with ⟨hpA, hpWidth, htail⟩
      have hstep :
          ∀ n,
            C ≤ n →
            n ≤ U + p →
            IsSubsetSum (insert p A) n :=
        subsetSum_interval_extension hCU hpA hcover hpWidth
      have htailCover :=
        ih (A := insert p A) (U := U + p) (by omega) hstep htail
      intro n hCn hn
      have hn' : n ≤ U + p + ps.sum := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
      have hnSubset := htailCover n hCn hn'
      simpa [Finset.union_insert, Finset.insert_union,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnSubset

/-- A list of fresh summands whose members all fit the initial interval width is an
extension chain.  Later members also fit because each preceding adjunction only increases the
right endpoint. -/
theorem isSubsetSumExtensionChain_of_bounded_list
    {A : Finset ℕ} {C U : ℕ} (ps : List ℕ)
    (hCU : C ≤ U)
    (hdisjoint : Disjoint A ps.toFinset)
    (hnodup : ps.Nodup)
    (hbound : ∀ p ∈ ps, p ≤ U - C + 1) :
    IsSubsetSumExtensionChain A C U ps := by
  induction ps generalizing A U with
  | nil => trivial
  | cons p ps ih =>
      rw [List.nodup_cons] at hnodup
      refine ⟨?_, hbound p (by simp), ?_⟩
      · intro hpA
        exact (Finset.disjoint_left.mp hdisjoint hpA (by simp)).elim
      · apply ih (A := insert p A) (U := U + p)
        · omega
        · rw [Finset.disjoint_left]
          intro q hq hpq
          rcases Finset.mem_insert.mp hq with rfl | hqA
          · exact hnodup.1 (by simpa using hpq)
          · exact (Finset.disjoint_left.mp hdisjoint hqA
              (by simpa only [List.toFinset_cons, Finset.mem_insert] using Or.inr hpq)).elim
        · exact hnodup.2
        · intro q hq
          have hqBound := hbound q (by simp [hq])
          omega

/-- Extend a covered subset-sum interval by every element of a bounded fresh list at once. -/
theorem subsetSum_extend_bounded_list
    {A : Finset ℕ} {C U : ℕ} (ps : List ℕ)
    (hCU : C ≤ U)
    (hcover : ∀ n, C ≤ n → n ≤ U → IsSubsetSum A n)
    (hdisjoint : Disjoint A ps.toFinset)
    (hnodup : ps.Nodup)
    (hbound : ∀ p ∈ ps, p ≤ U - C + 1) :
    ∀ n, C ≤ n → n ≤ U + ps.sum → IsSubsetSum (A ∪ ps.toFinset) n :=
  subsetSum_extension_chain hCU hcover
    (isSubsetSumExtensionChain_of_bounded_list ps hCU hdisjoint hnodup hbound)

theorem subsetSum_bertrand_extension
    {A : Finset ℕ} {C U p : ℕ}
    (hCU : C ≤ U)
    (hp0 : p ≠ 0)
    (hmax : ∀ a ∈ A, a ≤ p)
    (hcover : ∀ n, C ≤ n → n ≤ U → IsSubsetSum A n)
    (hwidth : 2 * p ≤ U - C + 1) :
    ∃ q : ℕ,
      q.Prime ∧
      p < q ∧
      q ≤ U - C + 1 ∧
      ∀ n, C ≤ n → n ≤ U + q → IsSubsetSum (insert q A) n := by
  obtain ⟨q, hqPrime, hpq, hqTwo⟩ :=
    Nat.exists_prime_lt_and_le_two_mul p hp0
  have hqWidth : q ≤ U - C + 1 := hqTwo.trans hwidth
  have hqA : q ∉ A := by
    intro hqMem
    exact (not_le_of_gt hpq) (hmax q hqMem)
  exact
    ⟨q, hqPrime, hpq, hqWidth,
      subsetSum_interval_extension hCU hqA hcover hqWidth⟩

end Pntpp.DivisorPrefix
