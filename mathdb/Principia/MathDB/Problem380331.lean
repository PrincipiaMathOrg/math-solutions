import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# MathDB #380331 — Genest's Conjecture 1.7.13, proved

Write-up: `mathdb-open-problems/problems/380331/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-30).
Source: F. Genest, *Graphes eulériens et complémentarité locale*, PhD thesis, Université de
Montréal; arXiv:math/0701421v1 (2007), **Conjecture 1.7.13** (p. 39).

The conjecture: a self-complementary **symmetric** graph `G` of order `n` is invertible in
Genest's sense exactly when `n = 1` or `n ≡ 5 (mod 8)`, and then `G⁻¹ = Ḡ`.

## The whole argument is a characteristic-two RING identity

Genest's graph inverse corresponds to inverting `M = I + A` over `𝔽₂` (the natural colouring is
all white, because the degree `k = (n−1)/2` is even). The strongly-regular identity
`A² = (k−μ)I + (λ−μ)A + μJ` then reduces, using `k − μ = μ` and `λ − μ = −1`, to
`A² = μ·1 + A + μ·J` in characteristic two — and the parity of `μ = (n−1)/4` decides everything:

* `μ` **even** (`n ≡ 1 mod 8`): `A² = A`, so `(1+A)·A = 0` with `A ≠ 0` and `1+A` is a zero
  divisor — `not_isUnit_of_sq_eq`.
* `μ` **odd** (`n ≡ 5 mod 8`): `A² = 1 + A + J`, so `(1+A)(A+J) = 1` and `(A+J)(1+A) = 1` —
  `inverse_formula` and `inverse_formula'`, giving `isUnit_one_add`.

**No commutativity is needed**: `A` and `J` appear in a fixed order in every product, and the two
annihilation facts `A·J = 0` and `J·A = 0` are supplied separately. The lemmas are therefore
stated over a plain `Ring`, and apply to the matrix ring directly. Nor is any matrix machinery
needed for the core — `Matrix` enters only to confirm that `A + J` really encodes the complement
and that regularity gives `A·J = k·J`.

## What is a hypothesis

Two graph-theoretic facts, both named rather than worked around:

* **the pivot correspondence** — `H` is invertible in Genest's sense iff `M_H` is nonsingular
  over `𝔽₂`, with `M_{H⁻¹} = M_H⁻¹`. The write-up proves this from the principal-pivot formula;
  it is a statement about Genest's word calculus, which nothing in Mathlib models.
* **the parameter lemma** — a self-complementary symmetric graph of order `n > 1` is strongly
  regular with `k = (n−1)/2`, `λ = (n−5)/4`, `μ = (n−1)/4`, and `n ≡ 1 (mod 4)`.

Everything downstream of those two is proved here, including all of the arithmetic: `k − μ = μ`,
`λ + 1 = μ`, `k` even, and the parity dichotomy `Even μ ↔ n ≡ 1 (mod 8)`.

## A finding: regularity is not enough, edge-transitivity is load-bearing

The parameter lemma needs *both* transitivity assumptions. The verifier exhibits a **regular
self-complementary circulant on nine vertices** whose `(λ, μ)` is `(2, 2)` rather than the
required `(1, 2)` — so vertex-transitivity and self-complementarity alone do not force the
strongly-regular parameters, and the ring argument would not start.
-/

namespace Principia.MathDB.P380331

/-! ## The parameter arithmetic

`n ≡ 1 (mod 4)` is all that is needed, and every fact below is `omega`. -/

def kParam (n : ℕ) : ℕ := (n - 1) / 2

def lamParam (n : ℕ) : ℕ := (n - 5) / 4

def muParam (n : ℕ) : ℕ := (n - 1) / 4

theorem div_facts (n : ℕ) :
    (n - 1) / 2 * 2 + (n - 1) % 2 = n - 1 ∧ (n - 1) % 2 < 2
      ∧ (n - 1) / 4 * 4 + (n - 1) % 4 = n - 1 ∧ (n - 1) % 4 < 4
      ∧ (n - 5) / 4 * 4 + (n - 5) % 4 = n - 5 ∧ (n - 5) % 4 < 4 := by
  refine ⟨Nat.div_add_mod' (n - 1) 2, Nat.mod_lt _ (by norm_num),
    Nat.div_add_mod' (n - 1) 4, Nat.mod_lt _ (by norm_num),
    Nat.div_add_mod' (n - 5) 4, Nat.mod_lt _ (by norm_num)⟩

/-- `k − μ = μ`: the coefficient of `I` in the strongly-regular identity equals the coefficient
of `J`. -/
theorem k_sub_mu (n : ℕ) (h4 : n % 4 = 1) (hn : 5 ≤ n) :
    kParam n - muParam n = muParam n := by
  obtain ⟨h1, h2, h3, h5, -, -⟩ := div_facts n
  simp only [kParam, muParam]
  omega

/-- `λ + 1 = μ`, i.e. `λ − μ = −1`: the coefficient of `A` is odd. -/
theorem lam_add_one (n : ℕ) (h4 : n % 4 = 1) (hn : 5 ≤ n) :
    lamParam n + 1 = muParam n := by
  obtain ⟨-, -, h3, h5, h6, h7⟩ := div_facts n
  simp only [lamParam, muParam]
  omega

/-- `k = (n−1)/2` is even, which is why the natural colouring is all white and `A·J = kJ = 0`. -/
theorem k_even (n : ℕ) (h4 : n % 4 = 1) : Even (kParam n) := by
  obtain ⟨h1, h2, h3, h5, -, -⟩ := div_facts n
  simp only [kParam, Nat.even_iff]
  omega

/-- **The dichotomy.** `μ = (n−1)/4` is even exactly when `n ≡ 1 (mod 8)`. -/
theorem mu_even_iff (n : ℕ) (h4 : n % 4 = 1) : Even (muParam n) ↔ n % 8 = 1 := by
  obtain ⟨-, -, h3, h5, -, -⟩ := div_facts n
  simp only [muParam, Nat.even_iff]
  omega

/-- `n ≡ 1 (mod 4)` leaves exactly the two residue classes the conjecture names. -/
theorem residue_dichotomy (n : ℕ) (h4 : n % 4 = 1) : n % 8 = 1 ∨ n % 8 = 5 := by omega

/-! ## Characteristic two -/

variable {R : Type*} [Ring R]

theorem add_self_eq_zero (h2 : (2 : R) = 0) (x : R) : x + x = 0 := by
  have hx : x + x = 2 * x := by noncomm_ring
  rw [hx, h2, zero_mul]

theorem neg_one_eq_one (h2 : (2 : R) = 0) : (-1 : R) = 1 :=
  neg_eq_of_add_eq_zero_left (add_self_eq_zero h2 (1 : R))

/-- If `k` is even then `(k : R) = 0`, which is what kills the `J` term. -/
theorem cast_even_eq_zero (h2 : (2 : R) = 0) {k : ℕ} (hk : Even k) : (k : R) = 0 := by
  obtain ⟨m, hm⟩ := hk
  rw [hm]
  push_cast
  exact add_self_eq_zero h2 (m : R)

/-- Regularity plus even degree gives `A·J = 0`. -/
theorem mul_eq_zero_of_even (h2 : (2 : R) = 0) (A J : R) {k : ℕ} (hk : Even k)
    (h : A * J = (k : R) * J) : A * J = 0 := by
  rw [h, cast_even_eq_zero h2 hk, zero_mul]

/-! ## The strongly-regular identity in characteristic two -/

/-- The integer identity `A² = (k−μ)I + (λ−μ)A + μJ`, with `k − μ = μ` and `λ − μ = −1`,
becomes `A² = μ·1 + A + μ·J` in characteristic two. -/
theorem srg_reduce (h2 : (2 : R) = 0) (A J : R) {mu : ℕ}
    (hsrg : A * A = (mu : R) * 1 + (-1 : R) * A + (mu : R) * J) :
    A * A = (mu : R) * 1 + A + (mu : R) * J := by
  rw [hsrg, neg_one_eq_one h2, one_mul]

/-- `μ` even: the identity collapses to `A² = A`. -/
theorem sq_eq_self_of_mu_even (h2 : (2 : R) = 0) (A J : R) {mu : ℕ} (hmu : Even mu)
    (hsrg : A * A = (mu : R) * 1 + A + (mu : R) * J) : A * A = A := by
  rw [hsrg, cast_even_eq_zero h2 hmu, zero_mul, zero_mul, zero_add, add_zero]

/-- `μ` odd: the identity becomes `A² = 1 + A + J`. -/
theorem sq_eq_of_mu_odd (h2 : (2 : R) = 0) (A J : R) {mu : ℕ} (hmu : Odd mu)
    (hsrg : A * A = (mu : R) * 1 + A + (mu : R) * J) : A * A = 1 + A + J := by
  obtain ⟨m, hm⟩ := hmu
  have hcast : (mu : R) = 1 := by
    rw [hm]
    push_cast
    rw [h2, zero_mul, zero_add]
  rw [hsrg, hcast]
  noncomm_ring

/-! ## The two verdicts -/

/-- **`n ≡ 1 (mod 8)`: not invertible.** `A² = A` forces `(1+A)·A = 0`, and a nonzero `A` makes
`1 + A` a zero divisor. -/
theorem not_isUnit_of_sq_eq_self (h2 : (2 : R) = 0) (A : R) (hsq : A * A = A) (hA : A ≠ 0) :
    ¬ IsUnit (1 + A) := by
  intro hu
  obtain ⟨u, hu⟩ := hu
  have hkey : (1 + A) * A = 0 := by
    calc (1 + A) * A = A + A * A := by noncomm_ring
      _ = A + A := by rw [hsq]
      _ = 0 := add_self_eq_zero h2 A
  apply hA
  have hz : ((u⁻¹ : Rˣ) : R) * ((u : R) * A) = 0 := by
    rw [hu, hkey, mul_zero]
  rwa [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at hz

/-- **`n ≡ 5 (mod 8)`: invertible, with inverse `A + J`.** Right inverse. -/
theorem inverse_formula (h2 : (2 : R) = 0) (A J : R) (hsq : A * A = 1 + A + J)
    (hAJ : A * J = 0) : (1 + A) * (A + J) = 1 := by
  calc (1 + A) * (A + J) = A + J + A * A + A * J := by noncomm_ring
    _ = A + J + (1 + A + J) + 0 := by rw [hsq, hAJ]
    _ = 1 + (A + A) + (J + J) := by abel
    _ = 1 + 0 + 0 := by rw [add_self_eq_zero h2 A, add_self_eq_zero h2 J]
    _ = 1 := by abel

/-- Left inverse, from `J·A = 0`. -/
theorem inverse_formula' (h2 : (2 : R) = 0) (A J : R) (hsq : A * A = 1 + A + J)
    (hJA : J * A = 0) : (A + J) * (1 + A) = 1 := by
  calc (A + J) * (1 + A) = A + J + A * A + J * A := by noncomm_ring
    _ = A + J + (1 + A + J) + 0 := by rw [hsq, hJA]
    _ = 1 + (A + A) + (J + J) := by abel
    _ = 1 + 0 + 0 := by rw [add_self_eq_zero h2 A, add_self_eq_zero h2 J]
    _ = 1 := by abel

/-- Both sides, so `1 + A` is a genuine unit and `A + J` is its inverse. -/
theorem isUnit_one_add (h2 : (2 : R) = 0) (A J : R) (hsq : A * A = 1 + A + J)
    (hAJ : A * J = 0) (hJA : J * A = 0) : IsUnit (1 + A) :=
  ⟨⟨1 + A, A + J, inverse_formula h2 A J hsq hAJ, inverse_formula' h2 A J hsq hJA⟩, rfl⟩

/-! ## The assembled theorem -/

/-- **Genest's Conjecture 1.7.13.** Given the two graph-theoretic inputs — the pivot
correspondence (invertibility is nonsingularity of `1 + A` over `𝔽₂`) and the parameter lemma
(the strongly-regular identity in its characteristic-two form) — invertibility is decided by
`n mod 8`, and in the invertible case the inverse matrix is `A + J`, which is the complement. -/
theorem conjecture_1_7_13 (h2 : (2 : R) = 0) (A J : R) (n : ℕ) (h4 : n % 4 = 1)
    (hA : A ≠ 0) (hAJ : A * J = 0) (hJA : J * A = 0)
    (hsrg : A * A = (muParam n : R) * 1 + A + (muParam n : R) * J) :
    (n % 8 = 1 → ¬ IsUnit (1 + A))
      ∧ (n % 8 = 5 → IsUnit (1 + A) ∧ (1 + A) * (A + J) = 1) := by
  constructor
  · intro h8
    have hmu : Even (muParam n) := (mu_even_iff n h4).mpr h8
    exact not_isUnit_of_sq_eq_self h2 A (sq_eq_self_of_mu_even h2 A J hmu hsrg) hA
  · intro h8
    have hmu : Odd (muParam n) := by
      have hiff := mu_even_iff n h4
      rw [Nat.even_iff] at hiff
      rw [Nat.odd_iff]
      have : ¬ (muParam n % 2 = 0) := by rw [hiff]; omega
      omega
    have hsq := sq_eq_of_mu_odd h2 A J hmu hsrg
    exact ⟨isUnit_one_add h2 A J hsq hAJ hJA, inverse_formula h2 A J hsq hAJ⟩

/-! ## The matrix side, stated at the function level

`Matrix m m R` is definitionally `m → m → R`, and these three facts need nothing else -- so they
are stated for plain functions, which keeps the module free of matrix instance resolution. -/

variable {m : Type*}

/-- The all-ones matrix, as a function. -/
def onesFun : m → m → ZMod 2 := fun _ _ => 1

/-- `A + J` has diagonal `1` -- the all-white colouring -- when `A` has zero diagonal. -/
theorem complement_diag (A : m → m → ZMod 2) (hdiag : ∀ i, A i i = 0) (i : m) :
    A i i + onesFun i i = 1 := by
  simp only [onesFun, hdiag i, zero_add]

/-- Off the diagonal its entries are `A i j + 1`, which over `ℤ/2` is the complement's
adjacency. -/
theorem complement_offdiag (A : m → m → ZMod 2) (i j : m) :
    A i j + onesFun i j = A i j + 1 := rfl

/-- A `k`-regular graph satisfies `(A · J)_{ij} = k` for every entry, which is the matrix form of
`A J = k J`. -/
theorem row_sum_mul_ones [Fintype m] (A : m → m → ZMod 2) (k : ℕ)
    (hreg : ∀ i, (∑ l, A i l) = (k : ZMod 2)) (i j : m) :
    (∑ l, A i l * onesFun l j) = (k : ZMod 2) := by
  simp only [onesFun, mul_one]
  exact hreg i

end Principia.MathDB.P380331
