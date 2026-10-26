import Principia.MathDB.Problem317353

/-!
# MathDB #317354 — Star of David matrices are NOT closed under contiguous `2 × 2` minors

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/317354/solution.tex`, refuting Conjecture 2.15 of Sun: *if
`A ∈ SDR_∞` then `A^{[j]} ∈ SDR_∞` for every `j ≥ 1`*, where
`A^{[j]}_{n,k} = det [A_{n+i, k+ℓ}]_{0 ≤ i, ℓ < j}`.

Built on #317353's module, which already carries Sun's products `L`, `R`, the block-plus-identity
construction `ext`, and the same witness `A = M ⊕ I`.

**What is refuted, and why the hypothesis is NOT weakened.**  The source's hypothesis is
`A ∈ SDR_∞` — the rule at EVERY order `p ≥ 2`.  Replacing it by `SDR_3` would make the conjecture
stronger, and refuting a stronger statement refutes nothing here, so `SDRinf` below keeps every
`p`.  The CONCLUSION is weakened freely: only `j = 2` is used, the failure is exhibited already at
order three, and the matrices are integer and lower triangular.

**The unbounded part.**  `A_sdrinf` proves the rule for every `p`, `r`, `n ≥ k`, following the
write-up's Lemma 1: when `k < n` and row `n + p` lies past the block, one factor on each side sits
in that identity row off the diagonal; when `k = n` one factor on each side lies above the
diagonal; the 25 remaining cases with `n + p ≤ 4` are finite computations.

**The failure.**  With `C = A^{[2]}`, at `(p, r, n, k) = (2, 0, 1, 0)`:
`L = C₁₀ C₃₁ C₂₂ = 1 · (−1) · 1 = −1` while `R = C₃₂ C₁₁ C₂₀ = 2 · 1 · 0 = 0`.
Every value was checked against the write-up in Python before this file was written.
-/

namespace Principia.MathDB.P317354

open Finset
open Principia.MathDB.P317353

/-- Sun's `SDR_∞`: the Star of David rule at every order `p ≥ 2`. -/
def SDRinf (X : Mat) : Prop :=
  ∀ p r n k, 2 ≤ p → r ≤ p - 1 → k ≤ n → L p r n k X = R p r n k X

/-- The contiguous `2 × 2` minor matrix `X^{[2]}`. -/
def minor2 (X : Mat) : Mat :=
  fun n k => X n k * X (n + 1) (k + 1) - X n (k + 1) * X (n + 1) k

/-- Sun's Conjecture 2.15 at `j = 2`, over lower triangular integer matrices — the hypothesis at
its full `SDR_∞` strength, the conclusion weakened. -/
def SunConj215 : Prop :=
  ∀ X : Mat, LowerTri X → SDRinf X → SDRinf (minor2 X)

/-- **`A ∈ SDR_∞`**, the input hypothesis at full strength. -/
theorem A_sdrinf : SDRinf A := by
  intro p r n k hp hr hkn
  rcases Nat.lt_or_ge k n with hk | hk
  · by_cases hsmall : n + p ≤ 4
    · -- the 25 finite identities inside the block
      have hn : n ≤ 2 := by omega
      have hp4 : p ≤ 4 := by omega
      have hrp : r < p := by omega
      interval_cases n <;> interval_cases p <;>
        first
        | omega
        | (interval_cases k <;> interval_cases r <;>
            simp only [L, R, Finset.prod_range_succ, Finset.prod_range_zero, one_mul] <;>
            decide)
    · -- row n + p is an identity row past the block, and k < n
      rw [L_zero_of_second (i := 0) (by omega) (A_zero (n + (p - 0)) (k + r + 0 + 1) (by omega)),
        R_zero_of_first (i := 0) (by omega) (A_zero (n + (p - 0)) (k + (p - r) + 0) (by omega))]
  · -- k = n (from hk and hkn): one factor on each side lies above the diagonal
    have zL : L p r n k A = 0 := by
      rcases Nat.eq_zero_or_pos r with rfl | hr1
      · exact L_zero_of_second (i := p - 1) (by omega)
          (A_zero (n + (p - (p - 1))) (k + 0 + (p - 1) + 1) (by omega))
      · exact L_zero_of_first (i := 0) (by omega) (A_zero (n + 0) (k + (r - 0)) (by omega))
    have zR : R p r n k A = 0 := by
      by_cases hrp : r + 2 ≤ p
      · exact R_zero_of_second (i := 0) (by omega)
          (A_zero (n + 0) (k + (p - r - 0 - 1)) (by omega))
      · exact R_zero_of_first (i := r) (by omega)
          (A_zero (n + (p - r)) (k + (p - r) + r) (by omega))
    rw [zL, zR]

/-- At `(p, r, n, k) = (2, 0, 1, 0)` the minor matrix has `L = C₁₀ C₃₁ C₂₂ = −1`. -/
theorem minor_L : L 2 0 1 0 (minor2 A) = -1 := by
  simp only [L, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  decide

/-- … and `R = C₃₂ C₁₁ C₂₀ = 0`. -/
theorem minor_R : R 2 0 1 0 (minor2 A) = 0 := by
  simp only [R, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  decide

theorem minor_not_sdrinf : ¬ SDRinf (minor2 A) := by
  intro h
  have := h 2 0 1 0 (by norm_num) (by norm_num) (by norm_num)
  rw [minor_L, minor_R] at this
  norm_num at this

/-- **MathDB #317354: Sun's Conjecture 2.15 is false** — already for `j = 2`, with the failure at
order three. -/
theorem not_sunConj215 : ¬ SunConj215 := fun h =>
  minor_not_sdrinf (h A A_lower A_sdrinf)

end Principia.MathDB.P317354
