import Pntpp.DivisorPrefix.SubsetSums

namespace Pntpp.DivisorPrefix.Computation

def largeSeedStart : ℕ := 105000000

def largeSeedEnd : ℕ := 156000000

def largeSeedPrimeLower : ℕ := 20000000

def largeSeedPrimeUpper : ℕ := 40000000

def largeSeedOffsetBase : ℕ := 2048

def largeSeedPrimeWindow : Finset ℕ :=
  (Finset.Ioo largeSeedPrimeLower largeSeedPrimeUpper).filter Nat.Prime

def largeSeedTarget (n : ℕ) : ℕ :=
  if n % 2 = 0 then n else n - 20000003

def largeSeedFirstChunk (n : ℕ) : ℕ :=
  let half := largeSeedTarget n / 2
  if half % 2 = 0 then half else half - 1

def largeSeedSecondChunk (n : ℕ) : ℕ :=
  largeSeedTarget n - largeSeedFirstChunk n

def largeSeedPairStart (even : ℕ) : ℕ :=
  max (largeSeedPrimeLower + 1) (even - largeSeedPrimeUpper + 1)

def largeSeedPair (even offset : ℕ) : List ℕ :=
  let p := largeSeedPairStart even + 2 * offset
  [p, even - p]

theorem sum_toFinset_eq_sum
    (xs : List ℕ) (hnodup : xs.Nodup) :
    ∑ x ∈ xs.toFinset, x = xs.sum := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      rw [List.nodup_cons] at hnodup
      simp [hnodup.1, ih hnodup.2]

end Pntpp.DivisorPrefix.Computation
