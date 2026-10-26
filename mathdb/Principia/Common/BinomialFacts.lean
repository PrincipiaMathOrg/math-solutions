import Mathlib

/-!
# Two binomial facts Mathlib states only in a neighbouring form

Both were paid for by MathDB #334350 and mention nothing of it.

**The count of plain-function antidiagonals.**  Mathlib's stars and bars is
`Finset.card_finsuppAntidiag_nat_eq_choose`, stated for `ι →₀ ℕ`.  The same count for plain
functions is `Finset.piAntidiag`, which has `Finset.mem_piAntidiag` but NO cardinality theorem in
this pin.  Deriving one looks like it needs the equiv `(ι →₀ ℕ) ≃ (ι → ℕ)` — and it does not,
because `finsuppAntidiag s n` is *defined* as `(piAntidiag s n).attach.map ⟨…⟩`.  Two cardinality
rewrites transfer the count.

**The generalized binomial below its lower index.**  `Ring.choose a k = 0` for `0 ≤ a < k` is the
ordinary `Nat.choose_eq_zero_of_lt` transported along `Ring.choose_natCast`.  Mathlib has
`Ring.choose_zero_succ` and `Ring.choose_neg`, but not this.
-/

namespace Principia.Common

/-- **The plain-function antidiagonal has the `Finsupp` one's cardinality**, because the latter is
a `map` of the former's `attach`. -/
theorem card_piAntidiag_nat {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ℕ) :
    (Finset.piAntidiag s m).card = (s.card + m - 1).choose m := by
  rw [← Finset.card_finsuppAntidiag_nat_eq_choose, Finset.finsuppAntidiag,
    Finset.card_map, Finset.card_attach]

/-- **The generalized binomial vanishes when `0 ≤ a < k`.** -/
theorem ringChoose_eq_zero_of_lt {a : ℤ} {k : ℕ} (ha : 0 ≤ a) (hak : a < (k : ℤ)) :
    Ring.choose a k = 0 := by
  have hc : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha
  have h : Ring.choose a k = ((a.toNat.choose k : ℕ) : ℤ) := by
    conv_lhs => rw [← hc]
    exact Ring.choose_natCast _ _
  rw [h, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

end Principia.Common
