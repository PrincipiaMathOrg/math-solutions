import HRTLambdaZero
import HRTResonantFibre

/-!
# `hthree` for `Λ₀`, discharged

`HRTResonant.heil_speegle_lambda_zero` carries two hypotheses.  This file discharges the first:

  `hthree : ∀ c : Fin 4 → ℂ, (∑ i, c i • lambdaZeroFamily g i) = 0 → (∃ i, c i = 0) → ∀ i, c i = 0`

A dependence among the four `Λ₀` translates with one vanishing coefficient is a THREE-point
dependence, so `hthree` is exactly the four three-point subsets of
`Λ₀ = {(0,0), (1,0), (0,1), (√2,√2)}`, all four of which are now theorems:

| `c i = 0` | surviving triple              | route                                     |
|-----------|-------------------------------|-------------------------------------------|
| `i = 3`   | `{(0,0),(1,0),(0,1)}`         | `hrt_lambdaZero_triple1` — integer lattice |
| `i = 1`   | `{(0,0),(0,1),(√2,√2)}`       | `hrt_lambdaZero_triple3` — shear `κ = 1`   |
| `i = 2`   | `{(0,0),(1,0),(√2,√2)}`       | `hrt_lambdaZero_triple2` — **Fourier**     |
| `i = 0`   | `{(1,0),(0,1),(√2,√2)}`       | `hrt_lambdaZero_triple4` — **Fourier**     |

The last two are the configurations the Borel subgroup provably cannot reach.

**This does NOT prove Heil–Speegle Conjecture 2.**  `heil_speegle_lambda_zero` also carries
`hreduction`.  What this file delivers is one of its two inputs.

(Correcting this docstring's original claim, which said `hreduction` "remains open" because
"neither the Zak transform nor pointwise Birkhoff is in Mathlib".  Both statements were wrong:
this repo builds pointwise Birkhoff itself in `BirkhoffErgodic`, and a full Zak apparatus in
`ZakTransform`, chaining to `HRTMaster.rootCount_of_cocycle`.  As of `905d7988` no open
mathematics is known to remain in `hreduction` — four of its six side conditions are discharged in
`HRTReduction`, `hGne` follows from ergodicity via `ae_ne_zero_of_cocycle`, and what is left is
assembly.)

Expected footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 1000000

namespace HRTHthree

open Complex MeasureTheory HRTRect HRTLambdaZero

/-- The four `Λ₀` translates are exactly the `tf` family at `(0,0)`, `(1,0)`, `(0,1)`, `(√2,√2)`.
`tf x ω g t = e^{2πiωt} g(t−x)`; `timeShift` and `modulate` are its two coordinate axes. -/
theorem tf_eq_family (g : ℝ → ℂ) (t : ℝ) :
    tf 0 0 g t = g t
    ∧ tf 1 0 g t = HRTResonant.timeShift 1 g t
    ∧ tf 0 1 g t = HRTResonant.modulate 1 g t
    ∧ tf (Real.sqrt 2) (Real.sqrt 2) g t
        = HRTResonant.modulate (Real.sqrt 2) (HRTResonant.timeShift (Real.sqrt 2) g) t := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [tf, HRTTransfer.ee, HRTResonant.timeShift, HRTResonant.modulate, mul_assoc]

/-- The family equation, evaluated pointwise as a four-term `tf` dependence. -/
theorem pointwise_of_sum {g : ℝ → ℂ} (c : Fin 4 → ℂ)
    (hsum : (∑ i, c i • HRTResonant.lambdaZeroFamily g i) = 0) (t : ℝ) :
    c 0 * tf 0 0 g t + c 1 * tf 1 0 g t + c 2 * tf 0 1 g t
      + c 3 * tf (Real.sqrt 2) (Real.sqrt 2) g t = 0 := by
  obtain ⟨e0, e1, e2, e3⟩ := tf_eq_family g t
  rw [e0, e1, e2, e3]
  have h := congrFun hsum t
  simpa [Fin.sum_univ_four, HRTResonant.lambdaZeroFamily] using h

/-- **`hthree` for `Λ₀`, discharged.**  Every three-point subset of
`Λ₀ = {(0,0),(1,0),(0,1),(√2,√2)}` is linearly independent, so a four-term dependence with one
coefficient already zero has all four zero. -/
theorem hthree_lambdaZero {g : ℝ → ℂ} (hgm : Measurable g)
    (hgL : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (c : Fin 4 → ℂ) (hsum : (∑ i, c i • HRTResonant.lambdaZeroFamily g i) = 0)
    (hex : ∃ i, c i = 0) : ∀ i, c i = 0 := by
  have hgL0 : hgL.toLp g ≠ 0 := fun hc =>
    hgne (hgL.coeFn_toLp.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hc))
  have hpt := pointwise_of_sum c hsum
  obtain ⟨i, hi⟩ := hex
  fin_cases i
  · -- `c 0 = 0`: the surviving triple is `{(1,0),(0,1),(√2,√2)}` — needs the Fourier route
    have h3 : ∀ᵐ t : ℝ, c 1 * tf 1 0 g t + c 2 * tf 0 1 g t
        + c 3 * tf (Real.sqrt 2) (Real.sqrt 2) g t = 0 := by
      filter_upwards with t
      have h := hpt t
      have hi' : c 0 = 0 := hi
      rw [hi', zero_mul, zero_add] at h
      exact h
    obtain ⟨k1, k2, k3⟩ := hrt_lambdaZero_triple4 hgm hgL hgne _ _ _ h3
    intro j; fin_cases j
    · exact hi
    · exact k1
    · exact k2
    · exact k3
  · -- `c 1 = 0`: the surviving triple is `{(0,0),(0,1),(√2,√2)}` — the shear `κ = 1`
    have h3 : ∀ᵐ t : ℝ, c 0 * tf 0 0 g t + c 2 * tf 0 1 g t
        + c 3 * tf (Real.sqrt 2) (Real.sqrt 2) g t = 0 := by
      filter_upwards with t
      have h := hpt t
      have hi' : c 1 = 0 := hi
      rw [hi', zero_mul] at h
      linear_combination h
    obtain ⟨k0, k2, k3⟩ := hrt_lambdaZero_triple3 hgm hgL hgne _ _ _ h3
    intro j; fin_cases j
    · exact k0
    · exact hi
    · exact k2
    · exact k3
  · -- `c 2 = 0`: the surviving triple is `{(0,0),(1,0),(√2,√2)}` — needs the Fourier route
    have h3 : ∀ᵐ t : ℝ, c 0 * tf 0 0 g t + c 1 * tf 1 0 g t
        + c 3 * tf (Real.sqrt 2) (Real.sqrt 2) g t = 0 := by
      filter_upwards with t
      have h := hpt t
      have hi' : c 2 = 0 := hi
      rw [hi', zero_mul] at h
      linear_combination h
    obtain ⟨k0, k1, k3⟩ := hrt_lambdaZero_triple2 hgL hgL0 _ _ _ h3
    intro j; fin_cases j
    · exact k0
    · exact k1
    · exact hi
    · exact k3
  · -- `c 3 = 0`: the surviving triple is `{(0,0),(1,0),(0,1)}` — the integer lattice
    have h3 : ∀ᵐ t : ℝ, c 0 * tf 0 0 g t + c 1 * tf 1 0 g t + c 2 * tf 0 1 g t = 0 := by
      filter_upwards with t
      have h := hpt t
      have hi' : c 3 = 0 := hi
      rw [hi', zero_mul, add_zero] at h
      exact h
    obtain ⟨k0, k1, k2⟩ := hrt_lambdaZero_triple1 hgm hgL hgne _ _ _ h3
    intro j; fin_cases j
    · exact k0
    · exact k1
    · exact k2
    · exact hi

end HRTHthree

/-! ## Acceptance gate -/

#print axioms HRTHthree.tf_eq_family
#print axioms HRTHthree.pointwise_of_sum
#print axioms HRTHthree.hthree_lambdaZero
