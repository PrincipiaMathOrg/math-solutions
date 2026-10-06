import Pntpp.DivisorPrefix.Computation.FirstWindowData
import Pntpp.DivisorPrefix.SubsetSums

namespace Pntpp.DivisorPrefix.Computation

def firstWindowLower : ℕ := 469615

def firstWindowUpper : ℕ := 480503

def firstWindowPrimes : Finset ℕ :=
  firstWindowSeed.toFinset

def maskSum : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: as, mask =>
      (if mask % 2 = 1 then a else 0) + maskSum as (mask / 2)

def maskFinset : List ℕ → ℕ → Finset ℕ
  | [], _ => ∅
  | a :: as, mask =>
      if mask % 2 = 1 then insert a (maskFinset as (mask / 2))
      else maskFinset as (mask / 2)

theorem maskFinset_subset_toFinset (xs : List ℕ) (mask : ℕ) :
    maskFinset xs mask ⊆ xs.toFinset := by
  induction xs generalizing mask with
  | nil => simp [maskFinset]
  | cons a as ih =>
      by_cases hbit : mask % 2 = 1
      · simp [maskFinset, hbit, ih]
      · simp only [maskFinset, hbit, ↓reduceIte]
        simpa using (ih _).trans (Finset.subset_insert a as.toFinset)

theorem sum_maskFinset
    (xs : List ℕ) (mask : ℕ) (hnodup : xs.Nodup) :
    ∑ x ∈ maskFinset xs mask, x = maskSum xs mask := by
  induction xs generalizing mask with
  | nil => simp [maskFinset, maskSum]
  | cons a as ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hbit : mask % 2 = 1
      · have ha :
            a ∉ maskFinset as (mask / 2) := by
          intro ha
          exact hnodup.1 (by
            simpa using maskFinset_subset_toFinset as (mask / 2) ha)
        simp [maskFinset, maskSum, hbit, ha, ih _ hnodup.2]
      · simp [maskFinset, maskSum, hbit, ih _ hnodup.2]

theorem firstWindowSeed_nodup : firstWindowSeed.Nodup := by
  decide

theorem firstWindowSeed_length : firstWindowSeed.length = 94 := by
  decide

theorem firstWindowSeed_lower :
    ∀ p ∈ firstWindowSeed, 10000 < p := by
  decide

theorem firstWindowSeed_upper :
    ∀ p ∈ firstWindowSeed, p ≤ 10883 := by
  decide

theorem firstWindowSeed_sorted : firstWindowSeed.SortedLT := by
  rw [List.sortedLT_iff_pairwise]
  decide

theorem firstWindowPrime_card : firstWindowPrimes.card = 94 := by
  decide

end Pntpp.DivisorPrefix.Computation
