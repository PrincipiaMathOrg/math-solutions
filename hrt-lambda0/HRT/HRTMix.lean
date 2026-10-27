import HRTZakL2

/-!
# The mixing formula for a non-lattice shift

`HRTTransfer.W_rep` handles a LATTICE time–frequency shift as a twisted reindex of the coefficient
array, with no hypotheses.  An irrational shift admits no such reindex, and this file states what
replaces it.

The obstruction is structural, not technical.  `Zg(t+1, ω) = e^{2πiω}·Zg(t, ω)` — the Zak transform
is QUASI-periodic in `t`, so the object on `T²` is a section of a line bundle.  Translating `t` past
the edge of the fundamental domain picks up the twist `e^{2πiω}` on the part that WRAPS.  A lattice
shift never wraps a fractional amount; an irrational shift always does.

Two pieces are already proved in `HRTZakL2`:

* `W_shift_real` — the substitution `u = s − a` moves the window to `[−a, 1−a]` and pulls out
  `e(−jθa)`;
* `integral_wrap_piece` — the sub-`0` part of `[−a, 1−a]` is, after `u = v − 1`, an integral over
  `[1−a, 1]` at index `k − 1`, carrying `e(jθ)`.

What remains is to split `[−a, 1−a]` at `0` and name the two halves.  Since neither half is a full
`W`, the statement needs the PARTIAL transform below; the shifted coefficient at `k` is then a phase
times a combination of a partial at `k` and a partial at `k − 1`.

## This file is DIAGNOSTIC, not the route forward — read this before building on it

The formula below is at the COEFFICIENT level, and that is the wrong level for the operator
identity the campaign actually needs.  Working this out on paper (cheap) rather than in Lean
(expensive on this machine) saved building a tower on it:

To make the mixing an operator statement one would have to express `partialW θ g j k 0 (1−a)` in
terms of `W`.  It *is* expressible — for fixed `k` the family `{W θ g j k}_j` are the Fourier
coefficients of `s ↦ g(s+k)` on `[0,1]`, so cutting the window to `[0,1−a]` is multiplication by an
indicator, i.e. **convolution in `j`** with the Fourier coefficients of `1_{[0,1−a]}`.  Those decay
like `1/j`: they are in `ℓ²` but **NOT `ℓ¹`**.  So the coefficient-level covariance is a
non-summable convolution — bounded, but with no algebraic normal form.  That is a bad object to
carry through a cocycle argument.

**At the FUNCTION level on the torus the same map is clean.**  Define

    (S_a F)(t, ω) = F(t − a, ω)                     for t ≥ a
                  = e^{−2πiω} · F(t − a + 1, ω)     for t < a

— a measure-preserving rearrangement composed with a unimodular multiplier, hence an ISOMETRY of
`L²(T²)` with no summability anywhere.  The wrap factor `e^{−2πiω}` is exactly the line-bundle twist
described above; it appears once, as a multiplier, instead of being smeared across a convolution.

**Derivation, checked rather than sketched.**  On `ℝ × ℝ` the shift is LITERALLY a translation:
`Z(T_a g)(t,ω) = ∑ₙ g(t−a−n)e^{2πinω} = Zg(t−a, ω)` — no twist at all.  The twist is an artefact of
restricting to the fundamental domain, via `Zg(t+1,ω) = ∑ₙ g(t+1−n)e^{2πinω} = e^{2πiω}Zg(t,ω)`.
For `t ∈ [0,1)` and `0 < a < 1`: if `t ≥ a` then `t−a ∈ [0,1)` and no correction occurs; if `t < a`
then `t−a+1 ∈ [1−a,1)` and `Zg(t−a,ω) = e^{−2πiω}Zg(t−a+1,ω)`.  Isometry is then immediate — the
unimodular factor drops and `[0,1−a) ∪ [1−a,1)` reassembles the domain.

**The decomposition that matters — both factors ALREADY EXIST in this repo.**

    S_a = M_φ ∘ R_a,    R_a(t,ω) = (t − a mod 1, ω),    φ(t,ω) = e^{−2πiω}·1_{t<a} + 1_{t≥a}

* `R_a` is a ROTATION of the first torus coordinate, hence measure preserving —
  `HRTReduction.measurePreserving_sub_circle` is this map on `AddCircle 1`, and
  `MeasureTheory.Lp.compMeasurePreserving` turns it into an operator (an AddMonoidHom needing the
  `translLm`/`mkContinuous` upgrade already done once in `HRTChar`).
* `M_φ` is multiplication by a UNIMODULAR measurable function — exactly the construction
  `HRTChar.chrAE`/`modL`/`modLC` performs for `L²(ℝ)`, via `AEEqFun` multiplication with the bound
  `1` coming from an equality of seminorms, not an estimate.

So neither factor is new mathematics; it is the `HRTChar` pattern transported from `L²(ℝ)` to
`L²(T²)`, with `φ` a two-valued indicator-times-character instead of a pure character.

**So the route is:** (1) build `S_a = M_φ ∘ R_a` as above; (2) prove `Z ∘ T_a = S_a ∘ Z` on the
COMPACTLY SUPPORTED class, where the pointwise Zak series is a finite sum and
`ZakTransform.zak_covariance` applies; (3) extend to all of `L²` by continuity, since both sides are
bounded operators agreeing on a dense subspace.  That is the density argument that WORKS (see the
note in `HRTZakL2` on the two extension problems), and it retires compact support.

What survives from this file is the honest computation of WHY the coefficient level fails, plus
`partialW` if it is ever wanted.  Nothing downstream should depend on `W_shift_mix`.

Expected footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace HRTMix

open MeasureTheory HRTTransfer

/-- **The partial transform** — `W` with the integration window cut down to `[c, d]`.
`W θ g j k = partialW θ g j k 0 1`, and a non-lattice shift produces exactly these. -/
noncomputable def partialW (θ : ℝ) (g : ℝ → ℂ) (j k : ℤ) (c d : ℝ) : ℂ :=
  (Real.sqrt θ : ℂ) * ∫ s in c..d, g (s + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * s))

/-- `W` is the partial transform over the full fundamental domain. -/
theorem W_eq_partialW (θ : ℝ) (g : ℝ → ℂ) (j k : ℤ) :
    W θ g j k = partialW θ g j k 0 1 := rfl

/-- The partial transform is additive in adjacent windows, given integrability on each. -/
theorem partialW_add_adjacent (θ : ℝ) (g : ℝ → ℂ) (j k : ℤ) (c d e : ℝ)
    (h₁ : IntervalIntegrable
      (fun s : ℝ => g (s + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * s))) volume c d)
    (h₂ : IntervalIntegrable
      (fun s : ℝ => g (s + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * s))) volume d e) :
    partialW θ g j k c d + partialW θ g j k d e = partialW θ g j k c e := by
  unfold partialW
  rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals h₁ h₂]

/-- **THE MIXING FORMULA.**  A shift by `a` sends the coefficient at index `k` to a phase times the
sum of a PARTIAL transform at `k` and a PARTIAL transform at `k − 1`, split at `1 − a`.

This is the exact analogue of `W_rep` for a non-lattice shift, and the contrast is the point:
`W_rep`'s right-hand side is a single reindexed coefficient, whereas this one cannot be written in
terms of `W` at all — the two partials do not individually extend to full fundamental domains. -/
theorem W_shift_mix (θ a : ℝ) (g : ℝ → ℂ) (j k : ℤ)
    (h₁ : IntervalIntegrable
      (fun s : ℝ => g (s + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * s))) volume (-a) 0)
    (h₂ : IntervalIntegrable
      (fun s : ℝ => g (s + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * s))) volume 0 (1 - a)) :
    W θ (fun y => g (y - a)) j k
      = HRTTransfer.ee (-((j : ℝ) * θ * a))
        * (partialW θ g j k 0 (1 - a)
            + HRTTransfer.ee ((j : ℝ) * θ) * partialW θ g j (k - 1) (1 - a) 1) := by
  rw [HRTZakL2.W_shift_real θ a g j k]
  congr 1
  -- split `[−a, 1−a]` at `0`, then rewrite the sub-`0` half as a `k−1` contribution
  have hsplit : (∫ u in (-a)..(1 - a), g (u + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * u)))
      = (∫ u in (-a)..(0:ℝ), g (u + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * u)))
        + ∫ u in (0:ℝ)..(1 - a), g (u + (k : ℝ)) * HRTTransfer.ee (-((j : ℝ) * θ * u)) :=
    (intervalIntegral.integral_add_adjacent_intervals h₁ h₂).symm
  rw [hsplit, HRTZakL2.integral_wrap_piece θ a g j k]
  unfold partialW
  ring

/-! ### The index convention of the `zakL2` ↔ pointwise-`zak` bridge

The bridge relating `zakL2 g` to the `L²` class of the pointwise `zak` is NOT the identity: the two
index conventions differ by a TRANSPOSE and a NEGATION.  Writing `c(j,m)` for the coefficient of the
pointwise Zak sum at `t`-frequency `j` and `ω`-frequency `m`,

    c(j,m) = ∫₀¹ g(t−m)·e(−jt) dt = W 1 g j (−m)

whereas `repr_zakL2 … i = W θ g (i 1) (i 0)`.

**This is verified here rather than asserted, because a wrong identification would fail SILENTLY:**
both objects are honest `L²` elements with the correct norms, so neither a build error nor a change
in axiom footprint would reveal it.  The two lemmas below are the whole content — the first is the
actual computation, the second shows the negation is bookkeeping (`W`'s index enters as `g (s + k)`,
the Zak series as `g (t − n)`, hence `k = −m`) and not something deeper. -/

/-- **Orthogonality of the integer characters on `[0,1]`** — what collapses the Zak series to its
`n = m` term when the `ω`-integral is taken. -/
theorem integral_char_orthogonal (c : ℤ) :
    (∫ ω in (0:ℝ)..1, HRTTransfer.ee ((c : ℝ) * ω)) = if c = 0 then 1 else 0 := by
  by_cases hc : c = 0
  · subst hc
    simp [HRTTransfer.ee]
  · rw [if_neg hc]
    have hne : (2 * (Real.pi : ℂ) * Complex.I * (c : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hc, Complex.ext_iff]
    have hpt : ∀ ω : ℝ, HRTTransfer.ee ((c : ℝ) * ω)
        = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (c : ℂ)) * (ω : ℂ)) := by
      intro ω
      unfold HRTTransfer.ee
      congr 1
      push_cast
      ring
    rw [intervalIntegral.integral_congr (g := fun ω : ℝ =>
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (c : ℂ)) * (ω : ℂ))) (fun ω _ => hpt ω),
      integral_exp_mul_complex hne]
    have h1 : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (c : ℂ)) * (1 : ℂ)) = 1 := by
      rw [mul_one]
      have hcomm : (2 * (Real.pi : ℂ) * Complex.I * (c : ℂ))
          = (c : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
      rw [hcomm, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
    have h0 : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (c : ℂ)) * (0 : ℂ)) = 1 := by simp
    push_cast
    rw [h1, h0, sub_self, zero_div]

/-- **The negation is bookkeeping, not depth.**  `W`'s index enters as `g (s + k)` and the Zak
series as `g (t − n)`, so the `(j,m)` coefficient is `W 1 g j (−m)`. -/
theorem coeff_eq_W_neg (g : ℝ → ℂ) (j m : ℤ) :
    (∫ t in (0:ℝ)..1, g (t - (m : ℝ)) * HRTTransfer.ee (-((j : ℝ) * t)))
      = W 1 g j (-m) := by
  unfold W
  rw [Real.sqrt_one, Complex.ofReal_one, one_mul]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  simp only [Int.cast_neg, mul_one, sub_eq_add_neg]

/-! ### Coefficient extraction — the computation the bridge runs on

The bridge identifies `zakL2 (θ = 1) g` with the `L²` class of `(t,ω) ↦ zak g t ω` on the compactly
supported class, by matching Fourier coefficients.  `repr_zakL2` gives one side; these two lemmas
give the other.  Doing the `ω`-integral FIRST collapses the Zak sum to its `m`-th term, leaving
exactly the integral `coeff_eq_W_neg` identifies with `W 1 g j (−m)` — so no Fubini juggling is
needed, the inner integral is evaluated pointwise in `t`.

Note the two `θ`s are different objects and must not be conflated: `W θ`'s is a lattice STEP, while
`zakFibre g θ t = zak g t (t+θ)`'s is a fibre OFFSET.  `zak` has integer shifts, so the bridge is
the `θ = 1` instance of `zakL2`, with the fibre parameter a separate variable. -/

/-- **Coefficient extraction.**  Integrating a finite character sum against `e(−mω)` picks out the
`m`-th coefficient. -/
theorem inner_omega_integral (S : Finset ℤ) (c : ℤ → ℂ) (m : ℤ) :
    (∫ ω in (0:ℝ)..1, (∑ n ∈ S, c n * HRTTransfer.ee ((n : ℝ) * ω))
        * HRTTransfer.ee (-((m : ℝ) * ω)))
      = if m ∈ S then c m else 0 := by
  have hpt : ∀ ω : ℝ, (∑ n ∈ S, c n * HRTTransfer.ee ((n : ℝ) * ω))
      * HRTTransfer.ee (-((m : ℝ) * ω))
      = ∑ n ∈ S, c n * HRTTransfer.ee (((n - m : ℤ) : ℝ) * ω) := by
    intro ω
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_assoc, ← HRTTransfer.ee_add]
    congr 2
    push_cast
    ring
  rw [intervalIntegral.integral_congr (g := fun ω : ℝ =>
      ∑ n ∈ S, c n * HRTTransfer.ee (((n - m : ℤ) : ℝ) * ω)) (fun ω _ => hpt ω)]
  rw [intervalIntegral.integral_finset_sum]
  · have hterm : ∀ n ∈ S, (∫ ω in (0:ℝ)..1, c n * HRTTransfer.ee (((n - m : ℤ) : ℝ) * ω))
        = if n = m then c n else 0 := by
      intro n _
      rw [intervalIntegral.integral_const_mul, integral_char_orthogonal (n - m)]
      by_cases h : n = m
      · subst h; simp
      · rw [if_neg (sub_ne_zero.mpr h), if_neg h, mul_zero]
    rw [Finset.sum_congr rfl hterm]
    by_cases hm : m ∈ S
    · rw [if_pos hm, Finset.sum_ite_eq' S m c, if_pos hm]
    · rw [if_neg hm, Finset.sum_ite_eq' S m c, if_neg hm]
  · intro n _
    have hcont : Continuous (fun ω : ℝ => c n * HRTTransfer.ee (((n - m : ℤ) : ℝ) * ω)) := by
      unfold HRTTransfer.ee
      fun_prop
    exact hcont.intervalIntegrable 0 1

/-- **The full 2-D coefficient of a finite Zak sum**, which `coeff_eq_W_neg` then identifies with
`W 1 g j (−m)`. -/
theorem coeff_zak_finsum (S : Finset ℤ) (g : ℝ → ℂ) (j m : ℤ) :
    (∫ t in (0:ℝ)..1,
        (∫ ω in (0:ℝ)..1, (∑ n ∈ S, g (t - (n : ℝ)) * HRTTransfer.ee ((n : ℝ) * ω))
            * HRTTransfer.ee (-((m : ℝ) * ω)))
          * HRTTransfer.ee (-((j : ℝ) * t)))
      = if m ∈ S then ∫ t in (0:ℝ)..1, g (t - (m : ℝ)) * HRTTransfer.ee (-((j : ℝ) * t)) else 0 := by
  have hpt : ∀ t : ℝ,
      (∫ ω in (0:ℝ)..1, (∑ n ∈ S, g (t - (n : ℝ)) * HRTTransfer.ee ((n : ℝ) * ω))
          * HRTTransfer.ee (-((m : ℝ) * ω)))
        * HRTTransfer.ee (-((j : ℝ) * t))
        = (if m ∈ S then g (t - (m : ℝ)) else 0) * HRTTransfer.ee (-((j : ℝ) * t)) := by
    intro t
    rw [inner_omega_integral S (fun n => g (t - (n : ℝ))) m]
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      (if m ∈ S then g (t - (m : ℝ)) else 0) * HRTTransfer.ee (-((j : ℝ) * t))) (fun t _ => hpt t)]
  by_cases hm : m ∈ S
  · simp only [if_pos hm]
  · simp only [if_neg hm, zero_mul, intervalIntegral.integral_zero]

end HRTMix

/-! ## Acceptance gate -/

#print axioms HRTMix.W_eq_partialW
#print axioms HRTMix.partialW_add_adjacent
#print axioms HRTMix.W_shift_mix
#print axioms HRTMix.integral_char_orthogonal
#print axioms HRTMix.coeff_eq_W_neg
#print axioms HRTMix.inner_omega_integral
#print axioms HRTMix.coeff_zak_finsum
