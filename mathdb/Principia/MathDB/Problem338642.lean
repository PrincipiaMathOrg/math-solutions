/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# MathDB #338642 — the exact excess of the Bovdi–Leung system `𝒟`

MathDB open problem #338642.  For `k ≥ 2` put `n = 4k+7`, `m = 4k`, `r = 2k`.  Section 4 of Bovdi
and Leung's construction produces a maximal commutative algebraic system `𝒟 ⊆ 𝒫ₙ(*)` whose only
layers are one exceptional layer at `r+3` of size `7B₀ + 21B₁ + 7B₂ + B₃`, together with every odd
layer from `r+5` upward, which is full.  The source conjectures `|𝒟| / 2^(n-2) → 1`.

The campaign result is the **exact identity**, which is strictly stronger:

  `|𝒟| − 2^(n-2) = 2(4k+3)(2k−1) / ((2k+1)(2k+2)) · C(4k, 2k)`

so the excess is strictly positive for every `k ≥ 2` — matching the source's finite computations —
and the normalized excess tends to zero.  Campaign source:
`mathdb-open-problems/problems/338642/` in the collaborator repository
`antoshashakov/Principia-Math-In-Progress`.

## What is assumed and what is proved

As in `Problem338641`, the **layer data is an input, not a theorem here**: that `𝒟` has exactly
these layers is a fact about Bovdi–Leung's construction, so it enters as the hypothesis
`DLayerData` — never as an `axiom`.  Lean certifies the implication, which is the part the campaign
derived.

## Reuse

This problem is the twin of #338641 and shares its machinery, so the odd-tail evaluation
(`two_mul_tail_five`), the first Vandermonde collection (`vandermonde_six`), the central-binomial
square bound and its limit (`central_ratio_tendsto_zero`) are **imported from `Problem338641`**
rather than restated.  Only the two adjacent-binomial recurrences `B₁/B₀ = 2k/(2k+1)` and
`B₂/B₁ = (2k−1)/(2k+2)` — which #338641 never needed, because its deficit collapsed to a multiple
of `B₀` alone — are new.

## Statement shapes

`ℕ` subtraction truncates, so the identity is stated additively as
`D + 3 * B k 0 = 2^(4k+5) + 6 * B k 1 + B k 2` (Lemma `D_add_three_central`); the source's boxed
rational form is `D_excess_exact`, over `ℝ`, where subtraction is honest.  `4k+5 = n-2`.
-/
import Principia.MathDB.Problem338641
import Mathlib.Tactic.LinearCombination

namespace Principia.MathDB.P338642

open Finset
open Principia.MathDB.P338641

/-! ### The Bovdi–Leung layer data — the hypothesis -/

/-- The source's layer description for `𝒟`: one exceptional layer at `r + 3`, and every odd layer
from `r + 5` upward is full.  This is Bovdi–Leung's construction, assumed here. -/
structure DLayerData (k D : ℕ) : Prop where
  decomposition :
    D = (7 * B k 0 + 21 * B k 1 + 7 * B k 2 + B k 3) + T k (2 * k + 5)

/-! ### The two adjacent-binomial recurrences

These are the only genuinely new combinatorial content relative to #338641: its deficit was a
multiple of `B₀` alone, whereas here `B₁` and `B₂` survive the cancellation and must be converted
into `B₀`. -/

/-- `B k 0 = C(4k, 2k)` is positive. -/
theorem B_zero_pos (k : ℕ) : 0 < B k 0 := by
  simp only [B]
  exact Nat.choose_pos (by omega)

/-- The central coefficient dominates the whole row: `B k t ≤ B k 0`. -/
theorem B_le_B_zero (k t : ℕ) : B k t ≤ B k 0 := by
  have h := Nat.choose_le_middle (2 * k + t) (4 * k)
  have e : 4 * k / 2 = 2 * k := by omega
  rw [e] at h
  simpa only [B, Nat.add_zero] using h

/-- `B₁ / B₀ = 2k / (2k+1)`, in cleared form. -/
theorem B_one_rec (k : ℕ) : (2 * k + 1) * B k 1 = 2 * k * B k 0 := by
  have h := Nat.choose_succ_right_eq (4 * k) (2 * k)
  have e : 4 * k - 2 * k = 2 * k := by omega
  rw [e] at h
  simp only [B, Nat.add_zero]
  rw [mul_comm (2 * k + 1) ((4 * k).choose (2 * k + 1)), h]
  ring

/-- `B₂ / B₁ = (2k−1) / (2k+2)`, in cleared, subtraction-free form.  The `k = j + 1` destructuring
is what turns the truncated `4k − (2k+1)` into the literal `2j + 1`. -/
theorem B_two_rec (k : ℕ) (hk : 1 ≤ k) :
    (2 * k + 2) * B k 2 + B k 1 = 2 * k * B k 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := Nat.choose_succ_right_eq (4 * (j + 1)) (2 * (j + 1) + 1)
  have e1 : 2 * (j + 1) + 1 + 1 = 2 * (j + 1) + 2 := by omega
  have e2 : 4 * (j + 1) - (2 * (j + 1) + 1) = 2 * j + 1 := by omega
  rw [e1, e2] at h
  simp only [B]
  rw [mul_comm (2 * (j + 1) + 2) ((4 * (j + 1)).choose (2 * (j + 1) + 2)), h]
  ring

/-! ### The exact identity -/

/-- **MathDB #338642, the exact form over `ℕ`.**  Under the source's layer data,
`|𝒟| = 2^(n-2) − 3B₀ + 6B₁ + B₂`, stated additively.

The proof is pure cancellation against #338641's tail evaluation and Vandermonde collection —
which is exactly what validates the decomposition: nothing here inspects the construction. -/
theorem D_add_three_central (k D : ℕ) (hk : 2 ≤ k) (h : DLayerData k D) :
    D + 3 * B k 0 = 2 ^ (4 * k + 5) + 6 * B k 1 + B k 2 := by
  have hd := h.decomposition
  have h5 := two_mul_tail_five k
  have h6 := vandermonde_six k hk
  have hpow : (2 : ℕ) ^ (4 * k + 6) = 2 * 2 ^ (4 * k + 5) := by ring
  omega

/-- `3B₀ < 6B₁`: the step that makes the excess positive.  From `(2k+1)B₁ = 2kB₀` and `6k > 3`. -/
theorem three_B_zero_lt_six_B_one (k : ℕ) (hk : 1 ≤ k) : 3 * B k 0 < 6 * B k 1 := by
  have hpos : 0 < B k 0 := B_zero_pos k
  have hrec := B_one_rec k
  have hstep : (6 * k + 3) * B k 0 < 12 * k * B k 0 :=
    mul_lt_mul_of_pos_right (by omega) hpos
  have hmain : (2 * k + 1) * (3 * B k 0) < (2 * k + 1) * (6 * B k 1) := by
    calc (2 * k + 1) * (3 * B k 0) = (6 * k + 3) * B k 0 := by ring
      _ < 12 * k * B k 0 := hstep
      _ = 6 * (2 * k * B k 0) := by ring
      _ = 6 * ((2 * k + 1) * B k 1) := by rw [hrec]
      _ = (2 * k + 1) * (6 * B k 1) := by ring
  exact lt_of_mul_lt_mul_left hmain (Nat.zero_le _)

/-- **The excess is strictly positive for every `k ≥ 2`**, matching the source's finite
computations.  This is the direction the conjecture alone does not give. -/
theorem two_pow_lt_D (k D : ℕ) (hk : 2 ≤ k) (h : DLayerData k D) :
    2 ^ (4 * k + 5) < D := by
  have hid := D_add_three_central k D hk h
  have hlt := three_B_zero_lt_six_B_one k (by omega)
  omega

/-- The exact excess with denominators cleared.  Everything is a linear combination of the
additive identity and the two recurrences; the coefficients are what the cancellation forces. -/
theorem D_excess_cleared (k D : ℕ) (hk : 2 ≤ k) (h : DLayerData k D) :
    ((D : ℝ) - 2 ^ (4 * k + 5)) * ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2))
      = 2 * (4 * (k : ℝ) + 3) * (2 * (k : ℝ) - 1) * ((4 * k).choose (2 * k) : ℝ) := by
  have hnat := D_add_three_central k D hk h
  have hcast : (D : ℝ) + 3 * (B k 0 : ℝ)
      = 2 ^ (4 * k + 5) + 6 * (B k 1 : ℝ) + (B k 2 : ℝ) := by exact_mod_cast hnat
  have h1 : (2 * (k : ℝ) + 1) * (B k 1 : ℝ) = 2 * (k : ℝ) * (B k 0 : ℝ) := by
    exact_mod_cast B_one_rec k
  have h2 : (2 * (k : ℝ) + 2) * (B k 2 : ℝ) + (B k 1 : ℝ) = 2 * (k : ℝ) * (B k 1 : ℝ) := by
    exact_mod_cast B_two_rec k (by omega)
  have hB0 : (B k 0 : ℝ) = ((4 * k).choose (2 * k) : ℝ) := by rw [B_zero]
  rw [← hB0]
  linear_combination ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)) * hcast
    + (14 * (k : ℝ) + 11) * h1 + (2 * (k : ℝ) + 1) * h2

/-- **MathDB #338642, the source's boxed identity.**
`|𝒟| − 2^(n-2) = 2(4k+3)(2k−1) / ((2k+1)(2k+2)) · C(4k, 2k)`. -/
theorem D_excess_exact (k D : ℕ) (hk : 2 ≤ k) (h : DLayerData k D) :
    (D : ℝ) - 2 ^ (4 * k + 5)
      = 2 * (4 * (k : ℝ) + 3) * (2 * (k : ℝ) - 1) * ((4 * k).choose (2 * k) : ℝ)
          / ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)) := by
  have hne : ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)) ≠ 0 := by positivity
  rw [eq_div_iff hne]
  exact D_excess_cleared k D hk h

/-! ### The limit -/

/-- **The source's conjecture.**  `|𝒟| / 2^(n-2) → 1`.

Squeezed between `1 − (3/32)·C(4k,2k)/2^(4k)` and `1 + (7/32)·C(4k,2k)/2^(4k)`, using
`B₁, B₂ ≤ B₀` and #338641's `central_ratio_tendsto_zero`. -/
theorem D_ratio_tendsto_one (D : ℕ → ℕ) (h : ∀ k, 2 ≤ k → DLayerData k (D k)) :
    Filter.Tendsto (fun k : ℕ => (D k : ℝ) / 2 ^ (4 * k + 5)) Filter.atTop (nhds 1) := by
  have hlow : Filter.Tendsto
      (fun k : ℕ => 1 - 3 / 32 * (((4 * k).choose (2 * k) : ℝ) / 2 ^ (4 * k)))
      Filter.atTop (nhds 1) := by
    have hmul := central_ratio_tendsto_zero.const_mul (3 / 32 : ℝ)
    have hsub := (tendsto_const_nhds (X := ℝ) (x := (1 : ℝ))
      (f := (Filter.atTop : Filter ℕ))).sub hmul
    simpa using hsub
  have hhigh : Filter.Tendsto
      (fun k : ℕ => 1 + 7 / 32 * (((4 * k).choose (2 * k) : ℝ) / 2 ^ (4 * k)))
      Filter.atTop (nhds 1) := by
    have hmul := central_ratio_tendsto_zero.const_mul (7 / 32 : ℝ)
    have hadd := (tendsto_const_nhds (X := ℝ) (x := (1 : ℝ))
      (f := (Filter.atTop : Filter ℕ))).add hmul
    simpa using hadd
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 2] with k hk
    have hnat := D_add_three_central k (D k) hk (h k hk)
    have hcast : (D k : ℝ) + 3 * (B k 0 : ℝ)
        = 2 ^ (4 * k + 5) + 6 * (B k 1 : ℝ) + (B k 2 : ℝ) := by exact_mod_cast hnat
    have hn1 : (0 : ℝ) ≤ (B k 1 : ℝ) := by positivity
    have hn2 : (0 : ℝ) ≤ (B k 2 : ℝ) := by positivity
    have hP : (0 : ℝ) < 2 ^ (4 * k) := by positivity
    have hpow : (2 : ℝ) ^ (4 * k + 5) = 32 * 2 ^ (4 * k) := by ring
    have hB0 : (B k 0 : ℝ) = ((4 * k).choose (2 * k) : ℝ) := by rw [B_zero]
    have hcancel : ((4 * k).choose (2 * k) : ℝ) / 2 ^ (4 * k) * 2 ^ (4 * k)
        = ((4 * k).choose (2 * k) : ℝ) := div_mul_cancel₀ _ (ne_of_gt hP)
    rw [hpow] at hcast
    rw [hpow, le_div_iff₀ (by positivity)]
    have hexp : (1 - 3 / 32 * (((4 * k).choose (2 * k) : ℝ) / 2 ^ (4 * k))) * (32 * 2 ^ (4 * k))
        = 32 * 2 ^ (4 * k)
            - 3 * (((4 * k).choose (2 * k) : ℝ) / 2 ^ (4 * k) * 2 ^ (4 * k)) := by ring
    rw [hexp, hcancel, ← hB0]
    linarith
  · filter_upwards [Filter.eventually_ge_atTop 2] with k hk
    have hnat := D_add_three_central k (D k) hk (h k hk)
    have hcast : (D k : ℝ) + 3 * (B k 0 : ℝ)
        = 2 ^ (4 * k + 5) + 6 * (B k 1 : ℝ) + (B k 2 : ℝ) := by exact_mod_cast hnat
    have hb1 : (B k 1 : ℝ) ≤ (B k 0 : ℝ) := by exact_mod_cast B_le_B_zero k 1
    have hb2 : (B k 2 : ℝ) ≤ (B k 0 : ℝ) := by exact_mod_cast B_le_B_zero k 2
    have hn0 : (0 : ℝ) ≤ (B k 0 : ℝ) := by positivity
    have hP : (0 : ℝ) < 2 ^ (4 * k) := by positivity
    have hpow : (2 : ℝ) ^ (4 * k + 5) = 32 * 2 ^ (4 * k) := by ring
    have hB0 : (B k 0 : ℝ) = ((4 * k).choose (2 * k) : ℝ) := by rw [B_zero]
    have hcancel : ((4 * k).choose (2 * k) : ℝ) / 2 ^ (4 * k) * 2 ^ (4 * k)
        = ((4 * k).choose (2 * k) : ℝ) := div_mul_cancel₀ _ (ne_of_gt hP)
    rw [hpow] at hcast
    rw [hpow, div_le_iff₀ (by positivity)]
    have hexp : (1 + 7 / 32 * (((4 * k).choose (2 * k) : ℝ) / 2 ^ (4 * k))) * (32 * 2 ^ (4 * k))
        = 32 * 2 ^ (4 * k)
            + 7 * (((4 * k).choose (2 * k) : ℝ) / 2 ^ (4 * k) * 2 ^ (4 * k)) := by ring
    rw [hexp, hcancel, ← hB0]
    linarith

/-! ### The carried hypothesis is inhabited, and both headline results specialize

Every theorem above carries `DLayerData`, and the capstone carries it at FUNCTION level —
`D_ratio_tendsto_one` quantifies over `D : ℕ → ℕ` and demands the spec at every `k ≥ 2`, which is
a strictly stronger obligation than a one-point witness.  Nothing above discharged it, so nothing
above ruled out these results holding vacuously; and no existing gate can see that, since a
vacuous theorem is axiom-free and gates clean.

The structure's single field is an EQUATION pinning `D` to a closed-form expression, so `rfl`
discharges it.  Both of the row's headline results then specialize with no hypothesis carried:
the strict positivity of the excess, and the source's boxed exact identity.

WHAT THIS DOES NOT DO.  `DWitness` is the source's arithmetic expression for the layer sizes of
`𝒟`, not a proof that Bovdi–Leung's construction has those layers — that remains this row's real
debt, exactly as for #338641.  Satisfiability is what is established. -/

/-- The closed-form value `DLayerData` pins `D` to. -/
def DWitness (k : ℕ) : ℕ :=
  (7 * B k 0 + 21 * B k 1 + 7 * B k 2 + B k 3) + T k (2 * k + 5)

/-- `DLayerData` is satisfiable at every `k`, by `rfl`: its one field is an equation. -/
theorem dLayerData_DWitness (k : ℕ) : DLayerData k (DWitness k) := ⟨rfl⟩

/-- The capstone's hypothesis shape, discharged: a uniform family does exist. -/
theorem exists_dLayerData_family : ∃ D : ℕ → ℕ, ∀ k, 2 ≤ k → DLayerData k (D k) :=
  ⟨DWitness, fun k _ => dLayerData_DWitness k⟩

/-- **The excess is strictly positive at the witness**, unconditional. -/
theorem two_pow_lt_DWitness (k : ℕ) (hk : 2 ≤ k) : 2 ^ (4 * k + 5) < DWitness k :=
  two_pow_lt_D k (DWitness k) hk (dLayerData_DWitness k)

/-- **The source's boxed identity at the witness**, unconditional. -/
theorem DWitness_excess_exact (k : ℕ) (hk : 2 ≤ k) :
    (DWitness k : ℝ) - 2 ^ (4 * k + 5)
      = 2 * (4 * (k : ℝ) + 3) * (2 * (k : ℝ) - 1) * ((4 * k).choose (2 * k) : ℝ)
          / ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)) :=
  D_excess_exact k (DWitness k) hk (dLayerData_DWitness k)

/-- **The capstone at the witness, unconditional.** -/
theorem DWitness_ratio_tendsto_one :
    Filter.Tendsto (fun k : ℕ => (DWitness k : ℝ) / 2 ^ (4 * k + 5)) Filter.atTop (nhds 1) :=
  D_ratio_tendsto_one DWitness fun k _ => dLayerData_DWitness k

end Principia.MathDB.P338642
