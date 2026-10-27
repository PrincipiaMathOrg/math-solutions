/-
MathDB #351647 — restricted reciprocal-permutation sums (Sun's Conjecture 4.4).

For an odd prime `p`, `n = p − 1` and `a ∈ ℤ`, the hollow Cauchy matrix is
`M_p(a)_{ij} = (a + ij)⁻¹` when `p ∤ a + ij`, and `0` otherwise, for `1 ≤ i, j ≤ n`.  Sun's
Conjecture 4.4 (p. 26) asserts, for every integer `a`,

    det M_p(a) ≡ (a/p) · (3 − a^{p−1}) / 2   (mod p²),

with a companion congruence for the permanent.

**THE LITERAL CONJECTURE IS FALSE, AND THIS ROW REFUTES IT WITH A FINITE WITNESS.**  The
write-up's own abstract says the signed formula holds for `p ≥ 5` when `p ∣ a`, but that at
`p = 3` the exact value is `−a (mod 9)` — so the literal statement "for every integer `a`" has
**exactly the exceptional class `p = 3`, `a ≡ 3, 6 (mod 9)`**.  At `p = 3` the matrix is `2 × 2`,
so the counterexample is completely computable, and that is what is proved here.

WHAT IS PROVED.

* `det3` — the determinant of `M₃(a)` as an element of `ZMod 9`.  When `3 ∣ a` the entries
  `a+1, a+2, a+4` are all units mod 3, so **no entry is hollow** and the matrix is the plain
  `2 × 2` reciprocal matrix; the hollow case never arises, which is why this specialisation is
  faithful rather than a convenient sub-case.
* `det3_three`, `det3_six`, `det3_zero`, `det3_nine` — the exact values `6`, `3`, `0`, `0`.
* `det3_eq_neg_self` — on the whole class `3 ∣ a`, `det3 a = −a`, the write-up's correction.
* **`conjecture44_literal_false`** — the conjectured right-hand side vanishes when `p ∣ a`
  (the Legendre symbol is `0`), while `det3 3 = 6 ≠ 0`.  So the literal quantifier "every
  integer `a`" is refuted, at the smallest odd prime and the smallest exceptional `a`.
* `exceptional_iff` — the exceptions are **exactly** `a ≡ 3, 6 (mod 9)`: the correction `−a`
  vanishes precisely when `9 ∣ a`, so `a ≡ 0 (mod 9)` is *not* exceptional even though `3 ∣ a`.
  Stating this is what turns "the conjecture is false" into "here is exactly where".

CARRIED.  The positive half — the congruences for `p ∤ a`, and the signed formula for `p ≥ 5`
with `p ∣ a` — whose proof is the first-order deformation of a hollow Cauchy matrix.  Named
hypotheses, never a `sorry`.

Reference: Z.-W. Sun, *Arithmetic properties of some permanents*, Conjecture 4.4, p. 26.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false

namespace Principia.MathDB.P351647

/-! ## 1. The `p = 3` determinant

At `p = 3` we have `n = 2`, and the entries are `a+ij` for `i, j ∈ {1,2}`, i.e.
`a+1, a+2, a+2, a+4`.  For `3 ∣ a` these are `1, 2, 1 (mod 3)` — all units, so the matrix has
**no hollow entry** and the determinant is the plain `2 × 2` one. -/

/-- The inverse of a unit of `ZMod 9`, written as a POWER so that everything below is pure ring
arithmetic and `decide` can evaluate it.  The unit group of `ZMod 9` has order `φ(9) = 6`, so
`x ^ 6 = 1` and `x ^ 5 = x⁻¹` for every unit.  `ZMod.inv` itself goes through `Nat.gcdA`, which
`decide` will not reduce — that is why the powers appear. -/
def inv9 (x : ZMod 9) : ZMod 9 := x ^ 5

/-- The encoding is justified: on every unit of `ZMod 9`, `x * inv9 x = 1`. -/
theorem mul_inv9 (x : ZMod 9)
    (h : x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 5 ∨ x = 7 ∨ x = 8) : x * inv9 x = 1 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `det M₃(a)` in `ZMod 9`. -/
def det3 (a : ZMod 9) : ZMod 9 := inv9 (a + 1) * inv9 (a + 4) - inv9 (a + 2) * inv9 (a + 2)

@[simp] theorem det3_zero : det3 0 = 0 := by decide

@[simp] theorem det3_three : det3 3 = 6 := by decide

@[simp] theorem det3_six : det3 6 = 3 := by decide

@[simp] theorem det3_nine : det3 9 = 0 := by decide

/-- **The write-up's correction**: on the whole class `3 ∣ a`, `det M₃(a) ≡ −a (mod 9)`. -/
theorem det3_eq_neg_self (a : ZMod 9) (h : a = 0 ∨ a = 3 ∨ a = 6) : det3 a = -a := by
  rcases h with rfl | rfl | rfl <;> decide

/-! ## 2. The refutation -/

/-- The conjectured right-hand side, at a prime dividing `a`.  The Legendre symbol `(a/p)`
vanishes there, so whatever `(3 − a^{p−1})/2` is, the product is `0`. -/
def conjecturedValue : ZMod 9 := 0

/-- **The literal Conjecture 4.4 is false.**  At `p = 3` and `a = 3` the conjectured value is
`0`, because the Legendre symbol vanishes, while the determinant is `6`. -/
theorem conjecture44_literal_false : det3 3 ≠ conjecturedValue := by decide

/-- and the same at `a = 6`. -/
theorem conjecture44_literal_false' : det3 6 ≠ conjecturedValue := by decide

/-- **The exceptions are exactly `a ≡ 3, 6 (mod 9)`.**  The correction `−a` vanishes precisely
when `9 ∣ a`, so `a ≡ 0 (mod 9)` satisfies the conjecture despite `3 ∣ a` — which is why the
exceptional class is `{3, 6}` and not "all multiples of 3".  This is what turns "the conjecture
is false" into "here is exactly where". -/
theorem exceptional_iff (a : ZMod 9) (h : a = 0 ∨ a = 3 ∨ a = 6) :
    (det3 a ≠ conjecturedValue) ↔ (a = 3 ∨ a = 6) := by
  rcases h with rfl | rfl | rfl <;> constructor <;> intro _ <;> first
    | decide
    | (exfalso; revert ‹_›; decide)

/-! ## 3. The surviving statement -/

/-- The positive half of the write-up's theorem, carried: the congruences for `p ∤ a`, and the
signed formula for `p ≥ 5` when `p ∣ a`.  `detM` and `perM` are supplied as parameters — building
the hollow Cauchy matrix and its permanent is a substantial development — but both appear in the
statement, so it cannot be satisfied by ignoring them. -/
def SunTheorem (detM perM : ℕ → ℤ → ℤ) (leg : ℕ → ℤ → ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ a : ℤ,
    (¬ ((p : ℤ) ∣ a) →
      (detM p a - leg p a * ((3 - a ^ (p - 1)) / 2)) % ((p : ℤ) ^ 2) = 0) ∧
    (¬ ((p : ℤ) ∣ a) →
      (perM p a - (-1) ^ ((p + 1) / 2) * ((3 - a ^ (p - 1)) / 2)) % ((p : ℤ) ^ 2) = 0) ∧
    (5 ≤ p → (p : ℤ) ∣ a →
      (detM p a - leg p a * ((3 - a ^ (p - 1)) / 2)) % ((p : ℤ) ^ 2) = 0)

/-- The corrected statement at `p = 3`: the exceptional value is `−a`, not `0`. -/
def ThreeCorrection (detM : ℕ → ℤ → ℤ) : Prop :=
  ∀ a : ℤ, (3 : ℤ) ∣ a → (detM 3 a + a) % 9 = 0

end Principia.MathDB.P351647
