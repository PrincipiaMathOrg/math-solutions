/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Goldbach.MinSum
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

/-!
# The large sieve for primes over major arcs (Helfgott `prop:bellen`): the objects

Campaign-agnostic. Helfgott, *The ternary Goldbach problem* (`ternvin.tex`), `prop:ramar`
(2356-2475) and `prop:bellen` (2491-2603), after Ramaré and Selberg (Bombieri, Astérisque 18,
Thm. 7A): for coefficients supported on integers with no prime factor `≤ 2Q`,
`∫_{𝔐_{δ₀,Q₀}} |S|² ≤ (max_{q even ≤ 2Q₀} max_{s ≤ 2Q₀/q} G_q(2Q₀/sq)/G_q(2Q/sq)) ∑|aₙ|²`.

This file fixes the objects and the SCALE-FREE statement `BellenG`:

* `eS a α = ∑ₙ aₙ e(nα)`;
* `gQ q R = G_q(R) = ∑_{r ≤ R, (r,q)=1} μ²(r)/φ(r)` (`eq:malbo`, `eq:malar`);
* `oeArcs h L`: the odd moduli `q ≤ L` with half-width `h/2q` and the even moduli `q ≤ 2L` with
  half-width `h/q` — Helfgott's `𝔐_{δ₀,Q₀}` (`eq:majdef`) is `oeArcs (δ₀Q₀/x) Q₀`;
* `BellenG`: with `Q = √(x/2δ₀)` one has `δ₀Q₀/x = Q₀/(2Q²)`, so `x` and `δ₀` disappear and the
  statement is in `Q₀ ≤ Q` alone. The right side is `B·∫_{(0,1]}|S|²` (Parseval turns it into
  `B·∑|aₙ|²`; that step lives with the consumer, which already has it).

The max of the source is carried as a bound `B` on every ratio (the hypothesis `hB`), which is
exactly how it is used.

## Two corrections to the printed hypotheses

* `prop:bellen` asks `a_n = 0` for `n ≤ √x` and `δ₀ ≥ 1`. The proof needs every modulus up to
  `2Q = √(2x/δ₀)` to be coprime to the support, which `n > √x` prime gives only when `δ₀ ≥ 2`.
  `BellenG` asks for the coprimality itself.
* The max runs over EVEN `q` only (the odd moduli enter through `G_{2q}`), so a finite check
  for `prop:espagn` that only feeds `prop:bellen` never needs odd `q` — in particular never
  `q = 1`, the single largest part of Helfgott's computation.
-/

namespace Principia.Common.PSieve

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction.Moebius

/-- **`S(α) = ∑ₙ aₙ e(nα)`**, an exponential sum over `n : ℕ` (junk `0` off `ℓ¹`). -/
noncomputable def eS (a : ℕ → ℂ) (α : ℝ) : ℂ := ∑' n : ℕ, a n * e ((n : ℝ) * α)

/-- **`G_q(R) = ∑_{r ≤ R, (r,q) = 1} μ²(r)/φ(r)`** (`ternvin.tex` `eq:malbo` 2373, `eq:malar`
2504). -/
noncomputable def gQ (q : ℕ) (R : ℝ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Nat.Coprime r q),
    ((μ r : ℤ) : ℝ) ^ 2 / (r.totient : ℝ)

/-- **The odd/even arc family** `oeArcs h L`: about `a/q`, `(a,q) = 1`, half-width `h/(2q)` for
odd `1 ≤ q ≤ L` and `h/q` for even `1 ≤ q ≤ 2L`. Helfgott's `𝔐_{δ₀,Q₀}` (`eq:majdef`, 730) is
`oeArcs (δ₀Q₀/x) Q₀`. -/
def oeArcs (h L : ℝ) : Set ℝ :=
  (⋃ q : ℕ, ⋃ (_ : 1 ≤ q ∧ (q : ℝ) ≤ L ∧ Odd q), ⋃ a : ℤ, ⋃ (_ : Int.gcd a q = 1),
      Set.Ioo ((a : ℝ) / q - h / (2 * q)) ((a : ℝ) / q + h / (2 * q))) ∪
    (⋃ q : ℕ, ⋃ (_ : 1 ≤ q ∧ (q : ℝ) ≤ 2 * L ∧ Even q), ⋃ a : ℤ, ⋃ (_ : Int.gcd a q = 1),
      Set.Ioo ((a : ℝ) / q - h / q) ((a : ℝ) / q + h / q))

/-- **`prop:bellen`, scale-free** (`ternvin.tex` 2491-2603, with `Q = √(x/2δ₀)`, so that
`δ₀Q₀/x = Q₀/(2Q²)`): for `ℓ¹` coefficients coprime to every modulus `≤ 2Q`, and any `B`
bounding every ratio `G_q(2Q₀/sq)/G_q(2Q/sq)`, `q ≤ 2Q₀` even, `1 ≤ s ≤ 2Q₀/q`,
`∫_{(0,1] ∩ 𝔐} |S|² ≤ B ∫_{(0,1]} |S|²`. -/
def BellenG : Prop :=
  ∀ (a : ℕ → ℂ) (Q₀ Q B : ℝ), (Summable fun n => ‖a n‖) → 1 ≤ Q₀ → Q₀ ≤ Q →
    (∀ n : ℕ, a n ≠ 0 → ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ 2 * Q → Nat.Coprime n m) →
    (∀ q : ℕ, Even q → 1 ≤ q → (q : ℝ) ≤ 2 * Q₀ → ∀ s : ℝ, 1 ≤ s → s ≤ 2 * Q₀ / q →
      gQ q (2 * Q₀ / (s * q)) ≤ B * gQ q (2 * Q / (s * q))) →
    ∫ α in Set.Ioc (0 : ℝ) 1 ∩ oeArcs (Q₀ / (2 * Q ^ 2)) Q₀, ‖eS a α‖ ^ 2 ≤
      B * ∫ α in Set.Ioc (0 : ℝ) 1, ‖eS a α‖ ^ 2

/-- `G_q(R) ≥ 0`. -/
theorem gQ_nonneg (q : ℕ) (R : ℝ) : 0 ≤ gQ q R :=
  Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- **`G_q(R) ≥ 1` for `R ≥ 1`**: the term `r = 1`. -/
theorem one_le_gQ (q : ℕ) (R : ℝ) (hR : 1 ≤ R) : 1 ≤ gQ q R := by
  have h1 : 1 ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Nat.Coprime r q) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, ?_⟩, Nat.coprime_one_left q⟩
    exact Nat.le_floor (by exact_mod_cast hR)
  have h := Finset.single_le_sum (f := fun r => ((μ r : ℤ) : ℝ) ^ 2 / (r.totient : ℝ))
    (fun r _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) h1
  simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_pow, Nat.totient_one,
    Nat.cast_one, div_one] at h
  exact h

end Principia.Common.PSieve
