/-
MathDB #350746 — a denominator bound for a contiguous basic hypergeometric ratio.

With `F(z) = ₂φ₁(a,b;c;q,z)`, `G(z) = ₂φ₁(aq,bq;cq;q,z)` and
`R(z) = G(z) / ((1−c)F(z)) = ∑ rₙ zⁿ`, Kim–Stanton Conjecture 8.3 (final 2023 version of
*Three families of q-Lommel polynomials*) asserts that

    Dₙ · rₙ  is a POLYNOMIAL in a, b, c, q,      Dₙ = ∏_{k=0}^{n} (1 − c qᵏ)^⌊(n+1)/(k+1)⌋.

That is a *denominator bound*: `Dₙ` is enough to clear `rₙ`.

WHAT IS PROVED HERE — the exponent structure of `Dₙ`, which is pure arithmetic and is what makes
the write-up's "the recurrence preserves the bound" a meaningful statement across `n`.

* `expo n k = (n+1)/(k+1)` (truncated division), with `expo_zero : expo n 0 = n + 1` and
  `expo_self : expo n n = 1` — so the exponents run from `n+1` down to `1`, which is the shape
  the write-up describes in prose.
* **`expo_mono`** — `expo n k ≤ expo (n+1) k`: every exponent is nondecreasing in `n`.
* **`D_dvd_succ`** — hence `Dₙ ∣ Dₙ₊₁` in any commutative ring.  This is the fact that makes a
  *bound preserved by a recurrence* coherent: a clearing denominator that did not grow
  monotonically would let a later coefficient need a factor an earlier one had already dropped.
  The write-up assumes it silently.
* `qPoch` — the q-Pochhammer `(x;q)_m = ∏_{j<m}(1 − x qʲ)`, with the empty product at `m = 0`,
  and `qPoch_zero`/`qPoch_succ`.

CARRIED.  `Conjecture83` itself.  Its proof is the quadratic coefficient recurrence obtained from
the basic hypergeometric equation, run over the integer polynomial ring — real `q`-series work.
The coefficients `r` and the integral subring `S` enter as parameters, and **both appear in the
statement**, so it cannot be satisfied by ignoring them.

Reference: J. S. Kim and D. Stanton, *Three families of q-Lommel polynomials*, Séminaire
Lotharingien de Combinatoire; Conjecture 8.3 of the final 2023 version.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Subring.Basic

set_option autoImplicit false

namespace Principia.MathDB.P350746

open Finset

/-! ## 1. The q-Pochhammer symbol -/

variable {R : Type*} [CommRing R]

/-- `(x;q)_m = ∏_{j<m} (1 − x qʲ)`, with the empty product at `m = 0`. -/
def qPoch (x q : R) (m : ℕ) : R := ∏ j ∈ range m, (1 - x * q ^ j)

@[simp] theorem qPoch_zero (x q : R) : qPoch x q 0 = 1 := by simp [qPoch]

theorem qPoch_succ (x q : R) (m : ℕ) :
    qPoch x q (m + 1) = qPoch x q m * (1 - x * q ^ m) := by
  simp [qPoch, Finset.prod_range_succ]

/-! ## 2. The exponent structure of the denominator -/

/-- The exponent of `(1 − c qᵏ)` in `Dₙ`, namely `⌊(n+1)/(k+1)⌋`. -/
def expo (n k : ℕ) : ℕ := (n + 1) / (k + 1)

@[simp] theorem expo_zero (n : ℕ) : expo n 0 = n + 1 := by simp [expo]

theorem expo_self (n : ℕ) : expo n n = 1 := by
  simp [expo, Nat.div_self (Nat.succ_pos n)]

/-- **Every exponent is nondecreasing in `n`.** -/
theorem expo_mono (n k : ℕ) : expo n k ≤ expo (n + 1) k :=
  Nat.div_le_div_right (by omega)

/-! ## 3. The denominator, and the divisibility the write-up assumes silently -/

/-- `Dₙ = ∏_{k=0}^{n} (1 − c qᵏ)^{⌊(n+1)/(k+1)⌋}`. -/
def D (c q : R) (n : ℕ) : R := ∏ k ∈ range (n + 1), (1 - c * q ^ k) ^ expo n k

@[simp] theorem D_zero (c q : R) : D c q 0 = 1 - c := by
  simp [D, expo]

/-- **`Dₙ ∣ Dₙ₊₁`** — the clearing denominator grows monotonically.  This is what makes "the
recurrence preserves the bound" coherent: were it false, a later coefficient could need a factor
an earlier one had already dropped. -/
theorem D_dvd_succ (c q : R) (n : ℕ) : D c q n ∣ D c q (n + 1) := by
  have h : (∏ k ∈ range (n + 1), (1 - c * q ^ k) ^ expo n k) ∣
      (∏ k ∈ range (n + 1), (1 - c * q ^ k) ^ expo (n + 1) k) :=
    Finset.prod_dvd_prod_of_dvd _ _ (fun k _ => pow_dvd_pow _ (expo_mono n k))
  -- NB the `prod_range_succ` rewrite must target the RIGHT side: applied blind it splits the
  -- LEFT product first, which is not what is wanted.
  have hD : D c q (n + 1)
      = (∏ k ∈ range (n + 1), (1 - c * q ^ k) ^ expo (n + 1) k)
        * (1 - c * q ^ (n + 1)) ^ expo (n + 1) (n + 1) := by
    rw [D, Finset.prod_range_succ]
  rw [D, hD]
  exact h.mul_right _

/-! ## 4. The conjecture -/

/-- **Kim–Stanton Conjecture 8.3**, relative to the coefficient sequence `r` of `R(z)` and the
integral subring `S = ℤ[a,b,c,q]` of the field `K`.  Both are parameters — constructing the
`₂φ₁` series and inverting `F` in `K[[z]]` is a development in itself — but **both appear in the
statement**, so the conjecture cannot be satisfied vacuously. -/
def Conjecture83 {K : Type*} [CommRing K] (S : Subring K) (c q : K) (r : ℕ → K) : Prop :=
  ∀ n : ℕ, D c q n * r n ∈ S

/-- The `n = 0` instance, made explicit: the bound there is just `1 − c`, matching
`R(z) = G(z)/((1−c)F(z))` and `F(0) = G(0) = 1`, so `r₀ = 1/(1−c)`. -/
theorem conjecture83_zero {K : Type*} [CommRing K] (S : Subring K) (c q : K) (r : ℕ → K)
    (h : Conjecture83 S c q r) : (1 - c) * r 0 ∈ S := by
  have := h 0
  rwa [D_zero] at this

end Principia.MathDB.P350746
