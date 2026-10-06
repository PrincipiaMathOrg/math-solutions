/-
Lean formalization by Hyunsik Chae, Apache License 2.0 (text: Chae/Pntpp/LICENSE).
Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file `Pntpp/DivisorPrefix/Computation/LargeSeed.lean`,
written by Hyunsik Chae for Lean v4.35.0-rc2.
The Lean statements and proofs are his; the mathematical argument they formalize is the
divisor-prefix argument of Jimmy Fraiture (JIF), github.com/jif-perso/erdos_1054 (see CREDITS.md).
Ported to Principia (Lean v4.31.0, Mathlib v4.31.0) by Claude, 2026-10-05.
Changes: import paths `Pntpp.*` -> `Principia.Erdos1054.Chae.Pntpp.*`; `set_option autoImplicit false` and `set_option maxRecDepth 100000` added at file level (his lakefile set both globally)
-/
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.SubsetSums

set_option autoImplicit false
set_option maxRecDepth 100000

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
