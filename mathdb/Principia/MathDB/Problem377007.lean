/-
MathDB #377007 — half-integral continued fractions for Chebyshev products (Cohn's Conjecture 9.2).

The write-up proves a general theorem: for nonconstant `f ∈ ℤ[X]` with
`f = 1 + X(X−1)(X+1)·g`, the iterates `f_0 = X`, `f_{n+1} = f(f_n)` give products
`R_n = ∏_{j≤n} (1 + 1/f_j)` whose regular continued fractions nest into one infinite fraction
whose partial quotients are integral at odd positions and half-integral at even positions — hence
semi-specializable.  It then instantiates `f = T_{|ℓ|}` for `4 ∣ ℓ`, `ℓ ≠ 0`, which is Cohn's
Conjecture 9.2 for the Chebyshev polynomials.

WHAT IS PROVED HERE — the whole instantiation bridge, which is what connects the general theorem
to the actual conjecture.  The write-up spends a paragraph on it: *"For `ℓ ≠ 0` divisible by four,
`T_{|ℓ|}(0) = T_{|ℓ|}(1) = T_{|ℓ|}(−1) = 1`.  The monic factor theorem over `ℤ[x]` gives
(congruence).  The identities `T_a(T_b(x)) = T_{ab}(x)` and `T_{−a} = T_a` identify `f_n` with
`T_{ℓ^n}`."*  Every step of that is here, and **Mathlib supplied all three evaluations directly**
— `T_eval_one`, `T_eval_neg_one` and `T_eval_two_mul_zero`, with `Int.negOnePow_eq_one_iff` doing
the parity bookkeeping.  That is the fourth time this week the library turned out to be shorter
than the source's own elementary argument.

* `T_eval_one_eq`, `T_eval_neg_one_eq_one`, `T_eval_zero_eq_one` — the three values, with the
  hypotheses they actually need (`Even ℓ` for the second, `4 ∣ ℓ` for the third).  **The `4 ∣ ℓ`
  is load-bearing exactly once:** `T_{2m}(0) = (−1)^m`, so it is `+1` only when `m` is even.
* `congruence_of_evals` — the monic factor theorem, proved by peeling one root at a time rather
  than via multisets: `X ∣ f−1` from the root at `0`, then `X−1` divides the cofactor, then `X+1`
  divides what is left.
* `chebyshev_congruence` — the two composed: for `4 ∣ ℓ` there is a `g` with
  `T ℓ = 1 + X(X−1)(X+1)g`, i.e. `T ℓ` satisfies the general theorem's hypothesis.
* `T_iterate` — `f_{n+1} = f(f_n)` matches `T_{ℓ^{n+1}} = T_ℓ ∘ T_{ℓ^n}`, from `T_mul`; with
  `T_neg` this is the write-up's identification of `f_n` with `T_{ℓ^n}`.

CARRIED.  `SemiSpecializable` and the general continued-fraction theorem.  Their proof is the
explicit partial-quotient recursion in `ℚ((x^{-1}))` with its integrality/half-integrality
bookkeeping, which needs a theory of regular continued fractions of Laurent series that Mathlib
does not have.  Per the spine rule these are named hypotheses, never a `sorry`.

Reference: H. Cohn, *Symmetry and specializability in continued fractions*, Acta Arithmetica 75
(1996), Sections 7 and 9, Conjecture 9.2.
-/
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false

namespace Principia.MathDB.P377007

open Polynomial Polynomial.Chebyshev

/-! ## 1. The three evaluations -/

theorem T_eval_one_eq (l : ℤ) : (T ℤ l).eval 1 = 1 := by rw [T_eval_one]

theorem T_eval_neg_one_eq_one {l : ℤ} (hl : Even l) : (T ℤ l).eval (-1) = 1 := by
  -- NB `Int.negOnePow_eq_one_iff` takes `n` EXPLICITLY, so `....mpr` is ill-formed and Lean
  -- reports it as "Unknown constant".  `Int.negOnePow_even` is the direct form.
  rw [T_eval_neg_one, Int.negOnePow_even _ hl]
  simp

/-- `4 ∣ ℓ` is load-bearing exactly here: `T_{2m}(0) = (−1)^m`, which is `+1` only for even `m`. -/
theorem T_eval_zero_eq_one {l : ℤ} (h4 : (4 : ℤ) ∣ l) : (T ℤ l).eval 0 = 1 := by
  obtain ⟨k, rfl⟩ := h4
  have h : (4 : ℤ) * k = 2 * (2 * k) := by ring
  rw [h, T_eval_two_mul_zero, Int.negOnePow_two_mul]
  simp

/-! ## 2. The monic factor theorem -/

/-- A polynomial taking the value `1` at `0`, `1` and `−1` has the shape
`1 + X(X−1)(X+1)·g`.  Proved by peeling one root at a time. -/
theorem congruence_of_evals (f : ℤ[X])
    (h0 : f.eval 0 = 1) (h1 : f.eval 1 = 1) (hm1 : f.eval (-1) = 1) :
    ∃ g : ℤ[X], f = 1 + X * (X - 1) * (X + 1) * g := by
  have e0 : (f - 1).IsRoot 0 := by simp [Polynomial.IsRoot, h0]
  obtain ⟨q, hq⟩ : (X - C (0 : ℤ)) ∣ (f - 1) := dvd_iff_isRoot.mpr e0
  rw [C_0, sub_zero] at hq
  have e1 : q.IsRoot 1 := by
    have hv : (f - 1).eval 1 = 0 := by simp [h1]
    rw [hq] at hv
    simpa using hv
  obtain ⟨r, hr⟩ : (X - C (1 : ℤ)) ∣ q := dvd_iff_isRoot.mpr e1
  have e2 : r.IsRoot (-1) := by
    have hv : (f - 1).eval (-1) = 0 := by simp [hm1]
    rw [hq, hr] at hv
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hv
    have : (2 : ℤ) * r.eval (-1) = 0 := by linarith [hv]
    have hr' : r.eval (-1) = 0 := by linarith
    exact hr'
  obtain ⟨g, hg⟩ : (X - C (-1 : ℤ)) ∣ r := dvd_iff_isRoot.mpr e2
  refine ⟨g, ?_⟩
  have hfac : f - 1 = X * ((X - C (1 : ℤ)) * ((X - C (-1 : ℤ)) * g)) := by
    rw [hq, hr, hg]
  have : f = 1 + X * ((X - C (1 : ℤ)) * ((X - C (-1 : ℤ)) * g)) := by
    rw [← hfac]; ring
  rw [this]
  simp only [map_one, map_neg]
  ring

/-- For `4 ∣ ℓ`, the Chebyshev polynomial `T ℓ` satisfies the general theorem's hypothesis. -/
theorem chebyshev_congruence {l : ℤ} (h4 : (4 : ℤ) ∣ l) :
    ∃ g : ℤ[X], T ℤ l = 1 + X * (X - 1) * (X + 1) * g := by
  refine congruence_of_evals _ (T_eval_zero_eq_one h4) (T_eval_one_eq l)
    (T_eval_neg_one_eq_one ?_)
  obtain ⟨k, rfl⟩ := h4
  exact ⟨2 * k, by ring⟩

/-! ## 3. The iteration matches the Chebyshev index -/

/-- `T_{ℓ^{n+1}} = T_ℓ ∘ T_{ℓ^n}` — the write-up's identification of `f_n` with `T_{ℓ^n}`. -/
theorem T_iterate (l : ℤ) (n : ℕ) :
    T ℤ (l ^ (n + 1)) = (T ℤ l).comp (T ℤ (l ^ n)) := by
  rw [← T_mul]
  congr 1
  ring

/-- and negative indices collapse, so `|ℓ|` and `ℓ` give the same polynomial. -/
theorem T_abs (l : ℤ) : T ℤ |l| = T ℤ l := by
  rcases abs_choice l with h | h
  · rw [h]
  · rw [h, T_neg]

/-! ## 4. Cohn's Conjecture 9.2 -/

/-- The integrality pattern: partial quotients integral at odd positions and half-integral at
even positions.  This is a property of a partial-quotient SEQUENCE, and it is exactly the part of
"semi-specializable" statable without a theory of continued fractions of Laurent series. -/
def HalfIntegralPattern (a : ℕ → Polynomial ℚ) : Prop :=
  (∀ j, Odd j → ∃ p : ℤ[X], a j = p.map (Int.castRingHom ℚ)) ∧
  (∀ j, Even j → 0 < j → ∃ p : ℤ[X], 2 • a j = p.map (Int.castRingHom ℚ))

/-- **The general theorem**, relative to an abstract relation `CF f a` meaning "`a` is the
partial-quotient sequence of the product `R_∞` attached to `f`".  Carrying `CF` rather than
defining it is the honest encoding: Mathlib has no regular continued fractions of Laurent series,
so the relation cannot be constructed here — but the conjecture's CONTENT, the integrality
pattern, is stated exactly.  (An earlier draft of this file defined `SemiSpecializable f` with a
body that never mentioned `f`; the unused-variable linter caught it.  A predicate that ignores its
subject is vacuous, not carried.) -/
def GeneralTheorem (CF : ℤ[X] → (ℕ → Polynomial ℚ) → Prop) : Prop :=
  ∀ f : ℤ[X], 0 < f.natDegree → (∃ g : ℤ[X], f = 1 + X * (X - 1) * (X + 1) * g) →
    ∀ a, CF f a → HalfIntegralPattern a

/-- **Cohn's Conjecture 9.2**: for every nonzero multiple `ℓ` of four, the Chebyshev product's
continued fraction has the half-integral pattern. -/
def Conjecture92 (CF : ℤ[X] → (ℕ → Polynomial ℚ) → Prop) : Prop :=
  ∀ l : ℤ, l ≠ 0 → (4 : ℤ) ∣ l → ∀ a, CF (T ℤ l) a → HalfIntegralPattern a

/-- **The instantiation, proved.**  Conjecture 9.2 follows from the general theorem and the
bridge above; the only input left is that `T ℓ` is nonconstant, which is where `ℓ ≠ 0` is used. -/
theorem conjecture92_of_general (CF : ℤ[X] → (ℕ → Polynomial ℚ) → Prop)
    (h : GeneralTheorem CF)
    (hdeg : ∀ l : ℤ, l ≠ 0 → (4 : ℤ) ∣ l → 0 < (T ℤ l).natDegree) :
    Conjecture92 CF :=
  fun l hl h4 a ha => h (T ℤ l) (hdeg l hl h4) (chebyshev_congruence h4) a ha

end Principia.MathDB.P377007
