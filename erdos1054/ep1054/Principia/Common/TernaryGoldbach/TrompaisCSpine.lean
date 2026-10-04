/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TrompaisAB
import Principia.Common.TernaryGoldbach.HelfgottCited
import Principia.Common.CscSq

set_option autoImplicit false

/-!
# `MPT.TrompaisC` and `MPT.TrompaisLogC` spined to Poisson + a Fourier bound

The third part of `eq:trompais` is the Poisson-summation bound. With `ρ = x/d`, `β = dγ`,
summing `η₂(n/ρ)e(βn)` over odd `n` only and applying Poisson to `n ↦ η₂(n/ρ)e(βn)` and to
`n ↦ η₂(n/ρ)e((β + 1/2)n)` gives

  `T_{d,∘}(γ) = (ρ/2) ∑_{j ∈ ℤ} (−1)^j η̂₂(ρ(j/2 − β))`,

and `|η̂₂(u)|(2πu)² ≤ c₀` turns each term into `(c₀/2π²ρ)/(j − 2β)²`; the sum over `j` is
`π²/sin²(2πβ)` EXACTLY (`CscSq.hasSum_inv_sq`, PROVED), so `|T|sin²(2πdγ) ≤ (d/x)(c₀/2)` with
no loss at all. That exactness is why this route clears the `c₀ = 31.521` bar (true sup
`31.52065`), where two summations by parts give `24 > 15.76` (`MPT.TrompaisC`'s docstring).

```
 TrompaisC    ← PoissonOdd     the odd-n Poisson identity for η₂ (Mathlib Poisson + decay)
              ← EtaHatBound    |η̂₂(u)|(2πu)² ≤ c₀
                  ← EtaHatIBP  (2πu)²η̂₂(u) = −(4g(u) + f̂(u)) (two integrations by parts;
                               g = HC.wollG, f̂ = HC.cameloFHat: Helfgott's objects verbatim)
                  ← CameloSup  |4g(t) + f̂(t)| ≤ c₀ for every real t (HC.CameloGridCited
                               + HC.WollustCited + interpolation + tail + t ↦ −t)
 TrompaisLogC ← PoissonOddLog  the same identity for log(ρt)η₂(t)
              ← EtaHatLBound   |FT(log(ρ·)η₂)(u)|(2πu)² ≤ c₀ log ρ for ρ ≥ 4 (eq:puella part 3)
 sin_sq_le (the generic composition), trompaisC_of, trompaisLogC_of, etaHatBound_of : PROVED
```

**`EtaHatLBound` is TRUE numerically but NOT reachable from a citation.** A float scan
(`u ∈ [0, 150]`, step `0.005`) of `sup_u |FT(g_ρ'')(u)|/log ρ` gives `16.34` (`ρ = 4`), `20.47`
(`ρ = 10`), `25.00` (`ρ = 100`), `28.90` (`ρ = 10⁵`), `30.43` (`ρ = 10¹²`): it rises to the
`η₂` value `31.5207` from BELOW as `ρ → ∞`, because the `log t·η₂(t)` correction is
anti-aligned with `FT(η₂'')` at its peak `u ≈ 17.4`. The triangle inequality cannot see that
(it gives `c₀ log ρ + |FT((log·η₂)'')|`), and Helfgott's grid is at `η₂` only — a computation
at a different object is not citable — so `EtaHatLBound` needs its own proof (an analytic
cancellation argument, or a new cited computation).
-/

namespace Principia.Common.TernaryGoldbach.MPTC

open Principia.Common.Goldbach Principia.Common.TernaryGoldbach.MPB2
  Principia.Common.TernaryGoldbach.MPB1 Principia.Common.TernaryGoldbach.MPT
  Principia.Common.TernaryGoldbach.MPc

/-! ## (1) The objects -/

/-- **`η̂₂(u) = ∫ η₂(t)e(−tu) dt`** (Helfgott's normalisation). -/
noncomputable def etaHat (u : ℝ) : ℂ := ∫ t, ((HW.eta2 t : ℝ) : ℂ) * e (-(t * u))

/-- **`η̂_{(ρ)}(u) = ∫ log(ρt)η₂(t)e(−tu) dt`** (`eq:puella`'s `η_{(ρ)}`). -/
noncomputable def etaHatL (ρ u : ℝ) : ℂ :=
  ∫ t, ((Real.log (ρ * t) * HW.eta2 t : ℝ) : ℂ) * e (-(t * u))

/-! ## (2) The links -/

/-- **Link [PoissonOdd]**: for `x > 0`, `d ≥ 1`, with `ρ = x/d`,
`T_{d,∘}(γ) = ∑_{j ∈ ℤ} (ρ/2)(−1)^j η̂₂(ρ(j/2 − dγ))` (Poisson summation for the continuous,
compactly supported `η₂`, whose transform is `O(u⁻²)` by `EtaHatIBP`). OPEN. -/
def PoissonOdd : Prop :=
  ∀ x γ : ℝ, 0 < x → ∀ d : ℕ, 1 ≤ d →
    HasSum (fun j : ℤ => ((x / d / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ j *
      etaHat (x / d * ((j : ℝ) / 2 - d * γ))) (tmo x γ d)

/-- **Link [PoissonOddLog]**: the same identity for `T^{log}_{d,∘}`, with `log m = log(ρ·m/ρ)`.
OPEN. -/
def PoissonOddLog : Prop :=
  ∀ x γ : ℝ, 0 < x → ∀ d : ℕ, 1 ≤ d →
    HasSum (fun j : ℤ => ((x / d / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ j *
      etaHatL (x / d) (x / d * ((j : ℝ) / 2 - d * γ))) (tlo x γ d)

/-- **Link [EtaHatBound]** — `|η̂₂(u)|(2πu)² ≤ c₀` (`lem:camelo`). OPEN. -/
def EtaHatBound : Prop := ∀ u : ℝ, ‖etaHat u‖ * (2 * Real.pi * u) ^ 2 ≤ c0

/-- **Link [EtaHatLBound]** — `eq:puella`'s third part: `|η̂_{(ρ)}(u)|(2πu)² ≤ c₀ log ρ` for
`ρ ≥ 4`. True numerically, own proof owed (module doc). OPEN. -/
def EtaHatLBound : Prop :=
  ∀ ρ : ℝ, 4 ≤ ρ → ∀ u : ℝ, ‖etaHatL ρ u‖ * (2 * Real.pi * u) ^ 2 ≤ c0 * Real.log ρ

/-- **Link [EtaHatIBP]** — `(2πu)²η̂₂(u) = −(4g(u) + f̂(u))`, i.e. `FT(η₂'') = 4g + f̂` with
`η₂'' = f + 4(4δ_{1/4} − 4δ_{1/2} + δ₁)` (`minarcs.tex` 5770-5775). OPEN. -/
def EtaHatIBP : Prop :=
  ∀ u : ℝ, (((2 * Real.pi * u) ^ 2 : ℝ) : ℂ) * etaHat u = -(4 * HC.wollG u + HC.cameloFHat u)

/-- **Link [CameloSup]** — `|4g(t) + f̂(t)| ≤ c₀ = 31.521` for every real `t` (`lem:camelo`:
the cited grid `HC.CameloGridCited` gives `31.520705` on `[0, 655]`, interpolation `0.000237`,
the tail `|t| ≥ 655` from `HC.WollustCited` and `|f̂(t)| ≤ Var(f)/2π|t|`, and `t ↦ −t` by
conjugation). OPEN. -/
def CameloSup : Prop := ∀ t : ℝ, ‖4 * HC.wollG t + HC.cameloFHat t‖ ≤ c0

/-! ## (3) The compositions, PROVED -/

/-- `‖(−1)^j‖ = 1`. -/
theorem norm_neg_one_zpow (j : ℤ) : ‖(-1 : ℂ) ^ j‖ = 1 := by
  rw [norm_zpow, norm_neg, norm_one, one_zpow]

/-- **The generic composition, PROVED**: if `S = ∑_j (ρ/2)(−1)^j H(ρ(j/2 − β))` and
`‖H(u)‖(2πu)² ≤ C` for every `u`, then `‖S‖ sin²(2πβ) ≤ C/(2ρ)`. -/
theorem sin_sq_le (S : ℂ) (H : ℝ → ℂ) (ρ β C : ℝ) (hρ : 0 < ρ)
    (hS : HasSum (fun j : ℤ => ((ρ / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ j * H (ρ * ((j : ℝ) / 2 - β))) S)
    (hH : ∀ u : ℝ, ‖H u‖ * (2 * Real.pi * u) ^ 2 ≤ C) :
    ‖S‖ * Real.sin (2 * Real.pi * β) ^ 2 ≤ C / (2 * ρ) := by
  have hC : 0 ≤ C := by
    have := hH 0
    simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
    linarith
  by_cases hs : Real.sin (2 * Real.pi * β) = 0
  · rw [hs]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    positivity
  have hpi := Real.pi_pos
  -- `y = −2β` avoids the integers
  have hy : ∀ n : ℤ, -2 * β + n ≠ 0 := by
    intro n h0
    apply hs
    have : 2 * Real.pi * β = n * Real.pi := by linear_combination (-Real.pi) * h0
    rw [this, Real.sin_int_mul_pi]
  have hcsc := CscSq.hasSum_inv_sq (-2 * β) hy
  have hsin : Real.sin (Real.pi * (-2 * β)) ^ 2 = Real.sin (2 * Real.pi * β) ^ 2 := by
    rw [show Real.pi * (-2 * β) = -(2 * Real.pi * β) by ring, Real.sin_neg, neg_sq]
  rw [hsin] at hcsc
  have hs2 : 0 < Real.sin (2 * Real.pi * β) ^ 2 := by positivity
  have hb := hcsc.mul_left (C / (2 * Real.pi ^ 2 * ρ))
  have hterm : ∀ j : ℤ, ‖((ρ / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ j * H (ρ * ((j : ℝ) / 2 - β))‖ ≤
      C / (2 * Real.pi ^ 2 * ρ) * (1 / (-2 * β + j) ^ 2) := by
    intro j
    have hj : -2 * β + j ≠ 0 := hy j
    set u := ρ * ((j : ℝ) / 2 - β) with hu
    have hu2 : (2 * Real.pi * u) ^ 2 = Real.pi ^ 2 * ρ ^ 2 * (-2 * β + j) ^ 2 := by
      rw [hu]; ring
    have hpos : 0 < (2 * Real.pi * u) ^ 2 := by
      rw [hu2]; have : 0 < (-2 * β + j) ^ 2 := by positivity
      positivity
    have hHu : ‖H u‖ ≤ C / (2 * Real.pi * u) ^ 2 := by
      rw [le_div_iff₀ hpos]; exact hH u
    rw [norm_mul, norm_mul, norm_neg_one_zpow, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    calc ρ / 2 * ‖H u‖ ≤ ρ / 2 * (C / (2 * Real.pi * u) ^ 2) :=
          mul_le_mul_of_nonneg_left hHu (by positivity)
      _ = C / (2 * Real.pi ^ 2 * ρ) * (1 / (-2 * β + j) ^ 2) := by
          rw [hu2]; field_simp
  have hle := hS.norm_le_of_bounded hb hterm
  have e : C / (2 * Real.pi ^ 2 * ρ) * (Real.pi ^ 2 / Real.sin (2 * Real.pi * β) ^ 2) =
      C / (2 * ρ) / Real.sin (2 * Real.pi * β) ^ 2 := by
    field_simp
  rw [e, le_div_iff₀ hs2] at hle
  exact hle

/-- **`MPT.TrompaisC` from `PoissonOdd` and `EtaHatBound`, PROVED.** -/
theorem trompaisC_of (hP : PoissonOdd) (hB : EtaHatBound) : TrompaisC := by
  intro x γ hx d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := sin_sq_le (tmo x γ d) etaHat (x / d) (d * γ) c0 (by positivity) (hP x γ hx d hd) hB
  rw [show 2 * Real.pi * (d * γ) = 2 * Real.pi * d * γ by ring] at h
  calc _ ≤ c0 / (2 * (x / d)) := h
    _ = d / x * (c0 / 2) := by field_simp

/-- **`MPT.TrompaisLogC` from `PoissonOddLog` and `EtaHatLBound`, PROVED.** -/
theorem trompaisLogC_of (hP : PoissonOddLog) (hB : EtaHatLBound) : TrompaisLogC := by
  intro x γ hx d hd hdx
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hρ : 4 ≤ x / d := by rw [le_div_iff₀ hdR]; linarith
  have h := sin_sq_le (tlo x γ d) (etaHatL (x / d)) (x / d) (d * γ) (c0 * Real.log (x / d))
    (by positivity) (hP x γ hx d hd) (hB (x / d) hρ)
  rw [show 2 * Real.pi * (d * γ) = 2 * Real.pi * d * γ by ring] at h
  calc _ ≤ c0 * Real.log (x / d) / (2 * (x / d)) := h
    _ = Real.log (x / d) * (d / x * (c0 / 2)) := by field_simp

/-- **`EtaHatBound` from `EtaHatIBP` and `CameloSup`, PROVED.** -/
theorem etaHatBound_of (h1 : EtaHatIBP) (h2 : CameloSup) : EtaHatBound := by
  intro u
  have e := congrArg norm (h1 u)
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at e
  rw [mul_comm, e]
  exact h2 u

/-- **`MPT.TrompaisC` from `PoissonOdd`, `EtaHatIBP`, `CameloSup`, PROVED.** -/
theorem trompaisC_of_camelo (hP : PoissonOdd) (h1 : EtaHatIBP) (h2 : CameloSup) : TrompaisC :=
  trompaisC_of hP (etaHatBound_of h1 h2)

end Principia.Common.TernaryGoldbach.MPTC
