import Principia.Common.CompleteMonotonicity
import Principia.Common.PowerSeriesCoeff

set_option autoImplicit false

/-!
# MathDB #351688 — complete monotonicity of squared derivative ratios of the Mills ratio

Write-up `mathdb-open-problems/problems/351688/solution.tex` on the `mathdb-results` branch of
`antoshashakov/Principia-Math-In-Progress`.

Ferreira–Simon (arXiv:2108.09244v2; Trans. AMS 376 (2023) 855–890) **Conjecture 3** asserts that
for every `n`,

    F_n(z) = -(r^(n)(z))^2 / r^(2n+1)(z)

is completely monotone on `(0, +inf)`, where `r` is the Mills ratio of the standard normal.  The
write-up refutes it at `n = 1` by a single rational sandwich at the exact point `c = 1/100`:

    -461/10^54  <  F_1^(70)(1/100) / 70!  <  -460/10^54  <  0.

## This module is the SPINE, not the certificate

Per the project's spine rule, the chain from the numeric witness to the refutation is written first,
with the arithmetic left as a named hypothesis.  Two things fall out of writing it, and neither was
visible in prose.

**The refutation needs no smoothness obligation.**  A complete-monotonicity predicate must carry its
own `ContDiffOn` (junk derivatives are `0`, which satisfies every sign condition), so the hypothesis
is discharged by whoever asserts the conjecture, not by whoever refutes it.  The campaign's earlier
triage listed "show `F_1` is smooth on `(0, +inf)`" as work; it is not.

**Order 70 enters only through `(-1)^70 = 1`.**  Nothing else in the reduction knows the order, so
the chain is unchanged if a cheaper witness at another order is found -- and the write-up's own
`F_0` / order-40 / `z = 0` route is exactly such a candidate.

## What remains, precisely

ONE inequality, and it is now stated about the object the recurrence actually produces.  The
coefficient recurrence of `r` is linear (`r' = z r - 1`, so every Taylor coefficient of `F_1` at `c`
is `alpha_k + beta_k * r(c)` with `alpha, beta` rational), and `conjecture3_false_of_coeff`
takes its
70th output directly: the row's residue is `p.coeff 70 < 0` for a power series `p` of `F_1` at
`1/100`.  The step from a coefficient to `iteratedDeriv` was priced here as a missing Mathlib lemma
and is not one -- see `Principia/Common/PowerSeriesCoeff.lean`.

What is genuinely left is the SERIES, not the bridge: exhibiting `HasFPowerSeriesAt (F 1) p (1/100)`
with `p.coeff` the recurrence's output, which needs analyticity of `r`, its ODE, a Cauchy
product and
a division by a series with nonzero constant term.

`millsRatio_zero` is proved here because it is the sole irrational input of the cheap route: at
`z = 0` both hard analytic inputs of the `c = 1/100` route (`e^(c^2/2)` and the incomplete Gaussian)
disappear, and what is left is `r(0) = sqrt(pi/2)`.
-/

namespace Principia.MathDB.P351688

open Principia.Common MeasureTheory
open Set Filter Topology
open scoped ContDiff
open scoped Real

/-- The **Mills ratio** of the standard normal,
`r(z) = e^(z^2/2) * integral_z^inf e^(-t^2/2) dt`. -/
noncomputable def millsRatio (z : ℝ) : ℝ :=
  Real.exp (z ^ 2 / 2) * ∫ t in Set.Ioi z, Real.exp (-t ^ 2 / 2)

/-- The Ferreira–Simon family `F_n = -(r^(n))^2 / r^(2n+1)`. -/
noncomputable def F (n : ℕ) (z : ℝ) : ℝ :=
  (-((iteratedDeriv n millsRatio z) ^ 2)) / iteratedDeriv (2 * n + 1) millsRatio z

/-- **Ferreira–Simon Conjecture 3.** -/
def Conjecture3 : Prop := ∀ n : ℕ, CompletelyMonotoneOn (F n) (Set.Ioi (0 : ℝ))

/-- **The reduction.**  A single negative value of `F_1^(70)` on the positive axis refutes the whole
conjecture.  The order is even, so no sign bookkeeping survives. -/
theorem conjecture3_false_of_witness (hw : iteratedDeriv 70 (F 1) (1 / 100) < 0) :
    ¬ Conjecture3 := by
  intro h
  refine not_completelyMonotoneOn_of_iteratedDeriv_lt isOpen_Ioi (n := 70) (x := 1 / 100)
    (by norm_num) ?_ (h 1)
  have hone : ((-1 : ℝ)) ^ (70 : ℕ) = 1 := by norm_num
  rw [hone, one_mul]
  exact hw

/-- **The reduction in the write-up's own units.**  The published certificate bounds
`F_1^(70)(1/100) / 70!`, not the derivative itself. -/
theorem conjecture3_false_of_certificate
    (hc : iteratedDeriv 70 (F 1) (1 / 100) / (Nat.factorial 70 : ℝ) < -(460 / 10 ^ 54)) :
    ¬ Conjecture3 := by
  refine conjecture3_false_of_witness ?_
  have hfac : (0 : ℝ) < (Nat.factorial 70 : ℝ) := by
    exact_mod_cast Nat.factorial_pos 70
  rw [div_lt_iff₀ hfac] at hc
  have hneg : -(460 / 10 ^ 54 : ℝ) * (Nat.factorial 70 : ℝ) < 0 :=
    mul_neg_of_neg_of_pos (by norm_num) hfac
  linarith

/-- **The reduction the certificate generator can hit directly.**  A coefficient recurrence emits
Taylor coefficients, not iterated derivatives; this is the same refutation phrased about the former,
so the remaining obligation is a single sign in the recurrence's output. -/
theorem conjecture3_false_of_coeff {p : FormalMultilinearSeries ℝ ℝ ℝ}
    (hp : HasFPowerSeriesAt (F 1) p (1 / 100)) (hc : p.coeff 70 < 0) : ¬ Conjecture3 :=
  conjecture3_false_of_witness (iteratedDeriv_neg_of_coeff_neg hp hc)

/-- **The sole irrational input of the cheap route**: `r(0) = sqrt(pi/2)`, which is the Gaussian
integral `integral_gaussian_Ioi (1/2)` after clearing the `e^0` prefactor. -/
theorem millsRatio_zero : millsRatio 0 = Real.sqrt (Real.pi / 2) := by
  have h : ∀ t : ℝ, -t ^ 2 / 2 = -(1 / 2 : ℝ) * t ^ 2 := fun t => by ring
  have hz : (0 : ℝ) ^ 2 / 2 = 0 := by norm_num
  simp only [millsRatio, h, hz, Real.exp_zero, one_mul]
  rw [integral_gaussian_Ioi]
  rw [show Real.pi / (1 / 2 : ℝ) = 2 ^ 2 * (Real.pi / 2) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  ring


/-- The Gaussian tail integrand, in the form the Mathlib integrability lemma states. -/
theorem gauss_eq : (fun t : ℝ => Real.exp (-t ^ 2 / 2))
    = fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
  funext t
  congr 1
  ring

theorem gauss_integrable : Integrable (fun t : ℝ => Real.exp (-t ^ 2 / 2)) := by
  rw [gauss_eq]
  exact integrable_exp_neg_mul_sq (by norm_num)

theorem gauss_continuous : Continuous (fun t : ℝ => Real.exp (-t ^ 2 / 2)) := by
  fun_prop

/-- **The tail integral differentiates to minus the integrand.**  `∫_z^∞` is rewritten as a
constant minus `∫_a^z` on a neighbourhood of `z`, where the fundamental theorem applies. -/
theorem hasDerivAt_tail (z : ℝ) :
    HasDerivAt (fun w : ℝ => ∫ t in Ioi w, Real.exp (-t ^ 2 / 2))
      (-Real.exp (-z ^ 2 / 2)) z := by
  set f : ℝ → ℝ := fun t => Real.exp (-t ^ 2 / 2) with hf
  set a : ℝ := z - 1 with ha
  have hint : IntegrableOn f (Ioi a) := gauss_integrable.integrableOn
  -- on `(a, ∞)` the tail is a constant minus an interval integral
  have hsplit : ∀ w : ℝ, a ≤ w →
      (∫ t in Ioi w, f t) = (∫ t in Ioi a, f t) - ∫ t in a..w, f t := by
    intro w hw
    have := intervalIntegral.integral_Ioi_sub_Ioi (μ := volume) (f := f) hint hw
    linarith [this]
  have hev : (fun w : ℝ => ∫ t in Ioi w, f t)
      =ᶠ[𝓝 z] fun w : ℝ => (∫ t in Ioi a, f t) - ∫ t in a..w, f t := by
    filter_upwards [eventually_gt_nhds (by linarith : a < z)] with w hw
    exact hsplit w hw.le
  have hftc : HasDerivAt (fun w : ℝ => ∫ t in a..w, f t) (f z) z :=
    intervalIntegral.integral_hasDerivAt_right
      gauss_integrable.intervalIntegrable
      (gauss_continuous.stronglyMeasurableAtFilter _ _)
      gauss_continuous.continuousAt
  have hconst : HasDerivAt (fun w : ℝ => (∫ t in Ioi a, f t) - ∫ t in a..w, f t) (-f z) z :=
    hftc.const_sub (∫ t in Ioi a, f t)
  exact hconst.congr_of_eventuallyEq hev

/-- **The Mills ratio satisfies `r' = z·r − 1`.**  This is the ODE the whole coefficient
recurrence rests on, and it needs no error function: the `e^(−z²/2)` produced by the fundamental
theorem cancels the `e^(z²/2)` prefactor exactly. -/
theorem hasDerivAt_millsRatio (z : ℝ) :
    HasDerivAt millsRatio (z * millsRatio z - 1) z := by
  have hexp : HasDerivAt (fun w : ℝ => Real.exp (w ^ 2 / 2)) (z * Real.exp (z ^ 2 / 2)) z := by
    have h1 : HasDerivAt (fun w : ℝ => w ^ 2 / 2) z z := by
      simpa using ((hasDerivAt_pow 2 z).div_const 2)
    simpa [mul_comm] using h1.exp
  have hmul := hexp.mul (hasDerivAt_tail z)
  have hcancel : Real.exp (z ^ 2 / 2) * Real.exp (-z ^ 2 / 2) = 1 := by
    rw [← Real.exp_add, show z ^ 2 / 2 + -z ^ 2 / 2 = 0 by ring, Real.exp_zero]
  have hval : z * millsRatio z - 1
      = z * Real.exp (z ^ 2 / 2) * (∫ t in Ioi z, Real.exp (-t ^ 2 / 2))
        + Real.exp (z ^ 2 / 2) * -Real.exp (-z ^ 2 / 2) := by
    simp only [millsRatio]
    nlinarith [hcancel]
  rw [hval]
  exact hmul


/-- The tail integral's derivative, in `deriv` form. -/
theorem deriv_tail :
    deriv (fun w : ℝ => ∫ t in Ioi w, Real.exp (-t ^ 2 / 2))
      = fun z : ℝ => -Real.exp (-z ^ 2 / 2) := by
  funext z
  exact (hasDerivAt_tail z).deriv

/-- **The tail is smooth**, by the bootstrap: it is differentiable and its derivative is
`-exp(-z²/2)`, which is smooth outright. -/
theorem contDiff_tail :
    ContDiff ℝ ∞ (fun w : ℝ => ∫ t in Ioi w, Real.exp (-t ^ 2 / 2)) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun z => (hasDerivAt_tail z).differentiableAt, ?_⟩
  rw [deriv_tail]
  fun_prop

/-- `millsRatio` is smooth: a product of `exp(z²/2)` with the tail. -/
theorem contDiff_millsRatio : ContDiff ℝ ∞ millsRatio := by
  have h : millsRatio = fun z : ℝ =>
      Real.exp (z ^ 2 / 2) * ∫ t in Ioi z, Real.exp (-t ^ 2 / 2) := rfl
  rw [h]
  exact (Real.contDiff_exp.comp (by fun_prop)).mul contDiff_tail

/-- The ODE in `deriv` form, which is what the iterated-derivative recurrence consumes. -/
theorem deriv_millsRatio : deriv millsRatio = fun z : ℝ => z * millsRatio z - 1 := by
  funext z
  exact (hasDerivAt_millsRatio z).deriv

/-- **One step of the recurrence.**  Differentiating the ODE `k` more times turns the `(k+1)`-st
derivative of `r` into the `k`-th derivative of `z ↦ z·r(z) − 1`; the Leibniz expansion of that
product is what produces `r^(k+1) = z·r^(k) + k·r^(k−1)`. -/
theorem iteratedDeriv_millsRatio_succ (k : ℕ) :
    iteratedDeriv (k + 1) millsRatio
      = iteratedDeriv k (fun z : ℝ => z * millsRatio z - 1) := by
  rw [iteratedDeriv_succ', deriv_millsRatio]

/-- **Leibniz on `w ↦ w · r w` keeps only two terms**, because `iteratedDeriv j (fun a => a)`
vanishes for `j ≥ 2`.  Stated at `m + 1` so that `m + 1 - i` is the only subtraction and the two
surviving indices `0, 1` are genuinely in range. -/
theorem iteratedDeriv_id_mul (m : ℕ) (z : ℝ) :
    iteratedDeriv (m + 1) (fun w : ℝ => w * millsRatio w) z
      = z * iteratedDeriv (m + 1) millsRatio z + (m + 1) * iteratedDeriv m millsRatio z := by
  have hid : ContDiffAt ℝ (m + 1 : ℕ) (fun w : ℝ => w) z := contDiff_id.contDiffAt
  -- `∞` is NOT `⊤` in `ℕ∞ω`, so `le_top` does not witness `↑(m+1) ≤ ∞`; the idiom is `mod_cast`.
  have hr : ContDiffAt ℝ (m + 1 : ℕ) millsRatio z :=
    contDiff_millsRatio.contDiffAt.of_le (mod_cast le_top)
  rw [iteratedDeriv_fun_mul hid hr]
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (m + 2) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp
  have hzero : ∀ i ∈ Finset.range (m + 2), i ∉ ({0, 1} : Finset ℕ) →
      ((m + 1).choose i : ℝ) * iteratedDeriv i (fun w : ℝ => w) z
        * iteratedDeriv (m + 1 - i) millsRatio z = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [iteratedDeriv_fun_id, if_neg hi.1, if_neg hi.2]
    ring
  rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  rw [iteratedDeriv_fun_id, iteratedDeriv_fun_id]
  norm_num


/-- Every iterated derivative of `r` is again smooth. -/
theorem contDiff_iteratedDeriv_millsRatio (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k millsRatio) := by
  rw [iteratedDeriv_eq_iterate]
  exact contDiff_millsRatio.iterate_deriv k

/-- **The defining identity of `F₁`, cleared of its denominator.** -/
theorem F_one_mul {z : ℝ} (h : iteratedDeriv 3 millsRatio z ≠ 0) :
    F 1 z * iteratedDeriv 3 millsRatio z = -(iteratedDeriv 1 millsRatio z) ^ 2 := by
  -- `2 * 1 + 1` reduces to `3` definitionally, so unfolding `F` already closes this.
  have hF : F 1 z
      = (-(iteratedDeriv 1 millsRatio z) ^ 2) / iteratedDeriv 3 millsRatio z := by
    simp only [F]
  rw [hF, div_mul_cancel₀ _ h]

/-- Where `r'''` is nonvanishing the identity holds on a whole NEIGHBOURHOOD, which is what an
iterated derivative can be applied to. -/
theorem F_one_eventuallyEq {z : ℝ}
    (hnz : ∀ᶠ w in 𝓝 z, iteratedDeriv 3 millsRatio w ≠ 0) :
    (fun w : ℝ => F 1 w * iteratedDeriv 3 millsRatio w)
      =ᶠ[𝓝 z] fun w : ℝ => -(iteratedDeriv 1 millsRatio w) ^ 2 := by
  filter_upwards [hnz] with w hw
  exact F_one_mul hw

/-- **The quotient's Taylor coefficients, with no series division.**  Differentiating the CLEARED
identity `n` times by Leibniz expresses `F₁^(n)` through the lower coefficients of `F₁` and the
derivatives of `r` — the `i = n` term carries `F₁^(n)` and everything else is already known. -/
theorem iteratedDeriv_F_one_leibniz (n : ℕ) {z : ℝ}
    (hnz : ∀ᶠ w in 𝓝 z, iteratedDeriv 3 millsRatio w ≠ 0)
    (hF : ContDiffAt ℝ (n : ℕ) (F 1) z) :
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * iteratedDeriv i (F 1) z
        * iteratedDeriv (n - i) (iteratedDeriv 3 millsRatio) z
      = iteratedDeriv n (fun w : ℝ => -(iteratedDeriv 1 millsRatio w) ^ 2) z := by
  have h3 : ContDiffAt ℝ (n : ℕ) (iteratedDeriv 3 millsRatio) z :=
    (contDiff_iteratedDeriv_millsRatio 3).contDiffAt.of_le (mod_cast le_top)
  rw [← iteratedDeriv_fun_mul hF h3]
  exact (F_one_eventuallyEq hnz).iteratedDeriv_eq n


/-- `r'(z) = z·r(z) − 1`. -/
theorem iteratedDeriv_one_millsRatio (z : ℝ) :
    iteratedDeriv 1 millsRatio z = z * millsRatio z - 1 := by
  rw [iteratedDeriv_one, deriv_millsRatio]

/-- `r''(z) = (1 + z²)·r(z) − z`. -/
theorem iteratedDeriv_two_millsRatio (z : ℝ) :
    iteratedDeriv 2 millsRatio z = (1 + z ^ 2) * millsRatio z - z := by
  have h : iteratedDeriv 2 millsRatio = deriv (fun w : ℝ => w * millsRatio w - 1) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_millsRatio]
  rw [h]
  have hd : HasDerivAt (fun w : ℝ => w * millsRatio w - 1)
      ((1 + z ^ 2) * millsRatio z - z) z := by
    -- state the derivative in the shape `HasDerivAt.mul` produces, then rewrite the VALUE;
    -- `convert` leaves a goal that `ring` cannot see into.
    have hm : HasDerivAt (fun w : ℝ => w * millsRatio w)
        (1 * millsRatio z + z * (z * millsRatio z - 1)) z :=
      (hasDerivAt_id z).mul (hasDerivAt_millsRatio z)
    have hval : 1 * millsRatio z + z * (z * millsRatio z - 1)
        = (1 + z ^ 2) * millsRatio z - z := by ring
    rw [← hval]
    exact hm.sub_const 1
  exact hd.deriv

/-- `r'''(z) = (z³ + 3z)·r(z) − (z² + 2)`.  This is the closed form the nonvanishing test uses. -/
theorem iteratedDeriv_three_millsRatio (z : ℝ) :
    iteratedDeriv 3 millsRatio z = (z ^ 3 + 3 * z) * millsRatio z - (z ^ 2 + 2) := by
  have h : iteratedDeriv 3 millsRatio
      = deriv (fun w : ℝ => (1 + w ^ 2) * millsRatio w - w) := by
    rw [iteratedDeriv_succ]
    congr 1
    funext w
    exact iteratedDeriv_two_millsRatio w
  rw [h]
  have hd : HasDerivAt (fun w : ℝ => (1 + w ^ 2) * millsRatio w - w)
      ((z ^ 3 + 3 * z) * millsRatio z - (z ^ 2 + 2)) z := by
    have hp : HasDerivAt (fun w : ℝ => 1 + w ^ 2) (2 * z) z := by
      simpa using (hasDerivAt_pow 2 z).const_add 1
    have hm : HasDerivAt (fun w : ℝ => (1 + w ^ 2) * millsRatio w)
        (2 * z * millsRatio z + (1 + z ^ 2) * (z * millsRatio z - 1)) z :=
      hp.mul (hasDerivAt_millsRatio z)
    have hval : 2 * z * millsRatio z + (1 + z ^ 2) * (z * millsRatio z - 1) - 1
        = (z ^ 3 + 3 * z) * millsRatio z - (z ^ 2 + 2) := by ring
    rw [← hval]
    exact hm.sub (hasDerivAt_id z)
  exact hd.deriv

/-- `r` is bounded by the Gaussian mass to its right, which is largest at `0`. -/
theorem millsRatio_le_gauss {z : ℝ} (hz : 0 ≤ z) :
    millsRatio z ≤ Real.exp (z ^ 2 / 2) * Real.sqrt (Real.pi / 2) := by
  have h0 : (∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2 / 2)) = Real.sqrt (Real.pi / 2) := by
    have h := millsRatio_zero
    simp only [millsRatio] at h
    simpa using h
  have hmono : (∫ t in Ioi z, Real.exp (-t ^ 2 / 2))
      ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2 / 2) := by
    refine setIntegral_mono_set gauss_integrable.integrableOn ?_ ?_
    · filter_upwards with t using (Real.exp_pos _).le
    · exact (Set.Ioi_subset_Ioi hz).eventuallyLE
  have hpos : (0 : ℝ) < Real.exp (z ^ 2 / 2) := Real.exp_pos _
  calc millsRatio z = Real.exp (z ^ 2 / 2) * ∫ t in Ioi z, Real.exp (-t ^ 2 / 2) := rfl
    _ ≤ Real.exp (z ^ 2 / 2) * ∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hmono hpos.le
    _ = Real.exp (z ^ 2 / 2) * Real.sqrt (Real.pi / 2) := by rw [h0]

/-- A deliberately crude bound: enough to decide the sign of `r'''` near `0`. -/
theorem millsRatio_le_six {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 50) : millsRatio z ≤ 6 := by
  have hexp : Real.exp (z ^ 2 / 2) ≤ 3 := by
    have h1 : z ^ 2 / 2 ≤ 1 := by nlinarith
    calc Real.exp (z ^ 2 / 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
      _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hs : Real.sqrt (Real.pi / 2) ≤ 2 := by
    have h4 : Real.sqrt (Real.pi / 2) ≤ Real.sqrt 4 :=
      Real.sqrt_le_sqrt (by linarith [Real.pi_le_four])
    have : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    linarith [h4, this.le, this.ge]
  have hb := millsRatio_le_gauss hz0
  have hsp : (0 : ℝ) ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  nlinarith [hb, hexp, hs, hsp, Real.exp_pos (z ^ 2 / 2)]

/-- **`r''' < 0` on `[0, 1/50]`** — so in particular it does not vanish at `c = 1/100`. -/
theorem iteratedDeriv_three_neg {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 50) :
    iteratedDeriv 3 millsRatio z < 0 := by
  rw [iteratedDeriv_three_millsRatio]
  have hcoef : (0 : ℝ) ≤ z ^ 3 + 3 * z := by positivity
  have hprod : (z ^ 3 + 3 * z) * millsRatio z ≤ (z ^ 3 + 3 * z) * 6 :=
    mul_le_mul_of_nonneg_left (millsRatio_le_six hz0 hz) hcoef
  nlinarith [hprod, hz, hz0]

/-- **The hypothesis of `iteratedDeriv_F_one_leibniz`, discharged at the certificate's point.** -/
theorem eventually_iteratedDeriv_three_ne_zero :
    ∀ᶠ w in 𝓝 (1 / 100 : ℝ), iteratedDeriv 3 millsRatio w ≠ 0 := by
  filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1 / 100),
    eventually_lt_nhds (by norm_num : (1 / 100 : ℝ) < 1 / 50)] with w h1 h2
  exact ne_of_lt (iteratedDeriv_three_neg h1.le h2.le)

end Principia.MathDB.P351688
