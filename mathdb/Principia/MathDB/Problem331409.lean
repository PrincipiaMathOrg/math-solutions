/-
MathDB #331409 — eventual prime divisibility of the chocolate numbers.

`B_n` counts the ordered ways to break a 2-by-n chocolate bar into unit squares, with

    B_1 = 1,   B_n = (2n−2)! + ∑_{i=1}^{n−1} C(2n−2, 2i−1) B_i B_{n−i}   (n ≥ 2).

Conjecture 16 of the source (Conjecture 1 of the preprint) asks which primes divide every
sufficiently late `B_n`.  The answer is `p = 2`, `p = 5`, or `p ≡ ±1 (mod 5)` — equivalently,
the primes for which **5 is a quadratic residue**.  For the complementary primes the write-up
exhibits an arithmetic progression of nonzero terms, whose value involves the product
`∏_{h=0}^{(p−1)/2} (4h² − 2h − 1)`.

WHAT IS PROVED HERE.  The arithmetic spine, which mentions neither the chocolate numbers nor
the divided-power ring:

* `d`, the integer recurrence `d_0 = 1, d_1 = 0, d_{j+2} = (j² − j − 1) d_j`, and `d_odd` —
  every odd-indexed term vanishes.
* **`quad_ne_zero`, the load-bearing fact, and it needs no reciprocity at all.**  The identity
  `(4h − 1)² = 4(4h² − 2h − 1) + 5` is a `ring` fact in any commutative ring, so a vanishing
  factor `4h² − 2h − 1` would exhibit `5` as a square.  Hence when 5 is a nonresidue mod `p`
  **no factor of the product vanishes**, and `prod_ne_zero` follows.  This is exactly the
  dichotomy that separates the two halves of the conjecture, and the same dichotomy #331410
  runs on — which is why that row imports this file.
* `five_sq_iff`, the reciprocity translation `IsSquare (5 : ZMod p) ↔ p % 5 = 1 ∨ p % 5 = 4`,
  so the source's congruence condition and the residue condition are interchangeable.

CARRIED.  `B` itself enters through `Recurrence`, a named hypothesis rather than a definition:
the recurrence is not structural (it refers to `B i` and `B (n−i)` for all `i < n`), and the
divided-power generating-function argument that turns it into the congruence is the write-up's
real content.  Per the spine rule the gap is a hypothesis, never a `sorry`.

Reference: the source cited as \cite{chocolate} by the write-up, Theorem 8 and Conjecture 16
(Conjecture 1 of the preprint).  Sibling row: `Problem331410.lean` (Conjecture 23, the prime
periods), which is the same paper and shares every definition below.
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

namespace Principia.MathDB.P331409

open Finset

/-! ## 1. The integer recurrence behind the auxiliary series -/

/-- `d_0 = 1`, `d_1 = 0`, `d_{j+2} = (j² − j − 1) d_j`. -/
def d : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | j + 2 => ((j : ℤ) ^ 2 - j - 1) * d j

@[simp] theorem d_zero : d 0 = 1 := rfl

@[simp] theorem d_one : d 1 = 0 := rfl

theorem d_add_two (j : ℕ) : d (j + 2) = ((j : ℤ) ^ 2 - j - 1) * d j := rfl

/-- Every odd-indexed `d` vanishes. -/
theorem d_odd (k : ℕ) : d (2 * k + 1) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
      rw [h, d_add_two, ih, mul_zero]

/-! ## 2. The quadratic dichotomy — the shared engine

`4h² − 2h − 1` is the quadratic whose roots are `(1 ± √5)/4`, so it has a root mod `p`
exactly when 5 is a quadratic residue.  The completing-the-square identity makes this
elementary: no discriminant theory and no reciprocity are needed for the direction we use. -/

/-- The completing-the-square identity, in any commutative ring. -/
theorem sq_four_sub_one {R : Type*} [CommRing R] (h : R) :
    (4 * h - 1) ^ 2 = 4 * (4 * h ^ 2 - 2 * h - 1) + 5 := by ring

/-- **If 5 is not a square mod `p`, no factor `4h² − 2h − 1` vanishes.** -/
theorem quad_ne_zero (p : ℕ) [Fact p.Prime] (h5 : ¬ IsSquare (5 : ZMod p)) (h : ZMod p) :
    4 * h ^ 2 - 2 * h - 1 ≠ 0 := by
  intro hz
  exact h5 ⟨4 * h - 1, by linear_combination (-4 : ZMod p) * hz⟩

/-- Hence the whole product is nonzero — the write-up's nonvanishing claim. -/
theorem prod_ne_zero (p : ℕ) [Fact p.Prime] (h5 : ¬ IsSquare (5 : ZMod p)) (n : ℕ) :
    ∏ h ∈ range n, (4 * (h : ZMod p) ^ 2 - 2 * (h : ZMod p) - 1) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => quad_ne_zero p h5 (i : ZMod p)

/-! ## 3. Reciprocity: the residue condition equals the congruence condition -/

/-- The squares of `ZMod 5` are `0, 1, 4`.  **The `∀` is load-bearing:** `decide` needs a CLOSED
goal, and a theorem *parameter* `(r : Fin 5)` is itself a free variable — writing it that way
fails with "Expected type must not contain free variables" even at top level, with no local
context in sight.  Binding `r` inside the statement (or `decide +revert`) is the fix. -/
theorem isSquare_zmod_five : ∀ r : Fin 5,
    IsSquare (((r : ℕ) : ZMod 5)) ↔ ((r : ℕ) = 0 ∨ (r : ℕ) = 1 ∨ (r : ℕ) = 4) := by decide

/-- `5` is a square mod `p` exactly when `p ≡ ±1 (mod 5)`.  This is where quadratic
reciprocity enters, and it is the only place. -/
theorem five_sq_iff (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    IsSquare (5 : ZMod p) ↔ p % 5 = 1 ∨ p % 5 = 4 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  -- the reciprocity step, with `p := 5` and `q := p`; note the direction needs `.symm`
  have hrec : IsSquare ((5 : ℕ) : ZMod p) ↔ IsSquare ((p : ℕ) : ZMod 5) :=
    (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by decide) hp2).symm
  have hcast : ((5 : ℕ) : ZMod p) = (5 : ZMod p) := by push_cast; ring
  rw [hcast] at hrec
  have hmod : ((p : ℕ) : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) := (ZMod.natCast_mod p 5).symm
  have hlt : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hp0 : p % 5 ≠ 0 := by
    intro h
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd 5 (Nat.dvd_of_mod_eq_zero h) with h1 | h1
    · norm_num at h1
    · exact hp5 h1.symm
  have hk := isSquare_zmod_five ⟨p % 5, hlt⟩
  -- `simp only []` still does structure-eta, which is what reduces `(⟨p % 5, _⟩ : Fin 5).val`;
  -- naming `Fin.val_mk` here is what the linter calls an unused simp argument.
  simp only [] at hk
  rw [hrec, hmod, hk]
  omega

/-! ## 4. The conjecture -/

/-- The chocolate-number recurrence, carried as a hypothesis.  It is not structural — the sum
refers to `B i` and `B (n − i)` for every `i < n` — and the generating-function argument that
turns it into the congruence is the write-up's real content. -/
def Recurrence (B : ℕ → ℤ) : Prop :=
  B 1 = 1 ∧ ∀ n, 2 ≤ n →
    B n = (Nat.factorial (2 * n - 2) : ℤ)
      + ∑ i ∈ Ico 1 n, ((2 * n - 2).choose (2 * i - 1) : ℤ) * B i * B (n - i)

/-- **Conjecture 16** (Conjecture 1 of the preprint): the primes dividing every sufficiently
late chocolate number are exactly `2`, `5`, and those with `5` a quadratic residue. -/
def Conjecture16 (B : ℕ → ℤ) : Prop :=
  ∀ p : ℕ, p.Prime →
    ((∃ N, ∀ n, N ≤ n → (p : ℤ) ∣ B n) ↔ (p = 2 ∨ p = 5 ∨ p % 5 = 1 ∨ p % 5 = 4))

/-- The complementary half, stated so the two directions cannot drift apart: for a prime
outside the class, the terms along the progression are the ones the write-up exhibits, and
`prod_ne_zero` is what makes them nonzero. -/
def NonzeroProgression (B : ℕ → ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 → ¬ (p % 5 = 1 ∨ p % 5 = 4) →
    ∀ k : ℕ, ¬ (p : ℤ) ∣ B ((p + 1) / 2 + k * (p * (p - 1) / 2))

end Principia.MathDB.P331409
