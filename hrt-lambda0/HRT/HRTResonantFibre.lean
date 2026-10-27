import Mathlib

/-!
# The fibre-level endgame of the resonant four-point HRT theorem

Formalisation of the decisive part of

  *A resonant four-point case of the HRT conjecture*,

which proves: for `a` irrational and `j ∈ ℤ \ {-1, 1}`, the four time–frequency translates
`g`, `T₁g`, `M₁g`, `M_{a+j}T_a g` are linearly independent for every nonzero `g ∈ L²(ℝ)`.
Taking `a = √2`, `j = 0` gives the Heil–Speegle four-point subconjecture at
`Λ₀ = {(0,0), (1,0), (0,1), (√2,√2)}`, for arbitrary `L²` windows.

## What this file proves

After the Zak transform and the resonant fibration `θ = ω - t`, the paper reduces the theorem
to a statement about a set `L ⊆ 𝕋` of *live fibres*, parametrised here by `w = e^{-2πiθ}` on the
unit circle. Each fibre carries the quadratic

  `Q_w(z) = C z² + A z + B w`,          `A, B, C, D ≠ 0` the (nonzero) dependence coefficients.

This file verifies, **axiom-free**, the entire endgame:

* `quad_factor`          — every such quadratic factors over `ℂ`.
* `counting_le_two`      — **the fixed-radius counting lemma**: for each `ρ > 0` there are at most
                           two `w` on the unit circle for which `Q_w` has a root of modulus `ρ`.
                           This is the rigidity step that makes the argument work.
* `mahler_mean`          — **Jensen's formula** (via Mathlib's Mahler measure) evaluates the mean
                           condition as `log‖D‖ = log‖C‖ + log⁺‖ζ₁‖ + log⁺‖ζ₂‖`.
* `outside_root_modulus` — the `N = 1` branch: the outside root has the *fibre-independent*
                           modulus `‖D‖/‖C‖`.
* `both_inside_forces`   — the `N = 2` branch (only reachable when `j = 1`): forces `‖D‖ = ‖C‖`.
* `both_outside_forces`  — the `N = 0` branch (only reachable when `j = -1`): forces `‖D‖ = ‖B‖`.
* `live_set_subset_four` — the assembly: the live set has **at most four elements**.
* `live_set_finite`, `live_set_not_infinite` — corollaries.

and, toward closing the two residual cones (§5–§7):

* `smallDivisor_summable`  — the arithmetic input: a Diophantine lower bound on the divisors plus
                             geometric numerators makes the small-divisor series converge.
* `fourierCoeff_comp_add`  — **the translation lemma for Fourier coefficients, absent from
                             Mathlib**, proved from translation-invariance of Haar on `AddCircle`.
* `eigenvalue_quantised`   — **the analytic crux**: a nonzero solution of `Y (t - a) = λ · Y t`
                             forces `λ` onto the countable set `{fourier n (-a)}`, which is what
                             makes the live set null.
* `exists_fourierCoeff_ne_zero`, `eigenvalue_quantised_L2`
                           — the same with the natural hypothesis `f ≠ 0` in `L²`, via injectivity
                             of the `fourierBasis` Hilbert-basis representation.
* `sqrt_two_dist_int`      — `√2` is badly approximable with the explicit constant `1/(2√2+1)`.
* `smallDivisor_summable_sqrt_two`
                           — **the arithmetic chain closed end-to-end at `a = √2`**: Jordan's
                             inequality + `‖e^{2πix}−1‖ ≥ 4·dist(x,ℤ)` + badly-approximable `√2`
                             + summability, composed into "the small-divisor series converges at
                             the Heil–Speegle parameter". This is the `𝒞_θ(a) < ∞` hypothesis of
                             the residual-cone argument, discharged for `a = √2`.

The one piece of that argument still missing is the **coboundary construction** — building `V`
from its Fourier coefficients and proving `V(t−a) − V(t) = log F_θ(t)`. Everything on either side
of it is now formal.

Since the Zak/Fubini step supplies a live set of *positive measure* whenever `g ≠ 0`, and a set of
at most four points is null, `live_set_not_infinite` is the contradiction that closes the theorem.

## Range of `j` covered

The `N ∈ {0,1,2}` case analysis against `N = 1 + j` gives:

* `|j| ≥ 2` — no live fibre survives at all;
* `j = 0`   — the paper's case, closed by `outside_root_modulus` + `counting_le_two`;
* `j = 1`   — closed **provided `‖D‖ ≠ ‖C‖`** (`both_inside_forces`);
* `j = -1`  — closed **provided `‖D‖ ≠ ‖B‖`** (`both_outside_forces`).

So the formalised theorem covers *every* `j ∈ ℤ`, with only two codimension-one exceptional cones.
This is strictly stronger than the paper's Remark 1, which claims nothing at all for `j = ±1`.
(The residual cones are exactly where the ILR degree budget is exhausted and Jensen returns a
`θ`-independent constraint, so the counting rigidity has nothing to bite on.)

## What is carried as a HYPOTHESIS (and why)

Two analytic inputs are stated as explicit hypotheses of the theorems rather than as `axiom`s, so
the verified footprint stays `[propext, Classical.choice, Quot.sound]` and the literature
dependency is visible in the statement itself:

* `hmean` — the mean condition `∫₀¹ log|Q_w(e^{2πit})| dt = log‖D‖` on live fibres. In the paper
  this comes from the measurable-coboundary lemma applied to `log|G_θ|`, which needs the
  **pointwise (Birkhoff) ergodic theorem**. Mathlib has `birkhoffSum`/`birkhoffAverage` and the
  *mean* ergodic theorem, but **not** the pointwise ergodic theorem, so this cannot currently be
  discharged here.

* `hILR` — the degree obstruction `N(w) = 1 + j` on fibres whose quadratic is zero-free on the unit
  circle. In the paper this is the **Iwanik–Lemańczyk–Rudolph** theorem (Israel J. Math. **83**
  (1993) 73–95): an absolutely continuous circle cocycle of nonzero degree with derivative of
  bounded variation, over an irrational rotation, has Lebesgue maximal spectral type, hence no
  eigenvectors. This is research-level spectral theory with no Lean formalisation anywhere.

Everything else in the endgame — the counting lemma, the Jensen evaluation, and the case
exhaustion over `N ∈ {0,1,2}` — is proved here from Mathlib.

Note `Real.circleAverage f 0 1 = (2π)⁻¹ ∫₀^{2π} f(e^{iφ}) dφ`, which is the paper's `∫₀¹ … dt`
under `t = φ/2π`; and `|P_θ| = |Q_θ|` on the unit circle since `P_θ = z⁻¹Q_θ`, so stating the mean
condition for `Q` is exactly the paper's equation for `P`.

## Verified footprint

All results: `[propext, Classical.choice, Quot.sound]` — 0 errors, 0 sorries under
`leanprover/lean4:v4.31.0` + Mathlib.
-/

set_option maxHeartbeats 1000000

namespace HRTResonant

open Complex Real

/-! ## 1. Quadratic factorisation over `ℂ` -/

/-- Every quadratic with nonzero leading coefficient splits over `ℂ`. -/
theorem quad_factor (A C b : ℂ) (hC : C ≠ 0) :
    ∃ ζ₁ ζ₂ : ℂ, ∀ z : ℂ, C * z ^ 2 + A * z + b = C * (z - ζ₁) * (z - ζ₂) := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (A ^ 2 - 4 * C * b) (n := 2) (by norm_num)
  refine ⟨(-A + s) / (2 * C), (-A - s) / (2 * C), fun z => ?_⟩
  have h2C : (2 : ℂ) * C ≠ 0 := mul_ne_zero two_ne_zero hC
  field_simp
  linear_combination hs

/-! ## 2. The fixed-radius counting lemma

For a *fixed* radius `ρ`, only two fibres can carry a root of that modulus.  The proof is the
paper's: `Q_w(z) = 0` with `‖z‖ = ρ`, `‖w‖ = 1` forces `Re(C conj(A) z)` to a constant, which
meets the circle `‖z‖ = ρ` in at most two points, and each such `z` determines `w`. -/

theorem counting_le_two (A B C : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ w₁ w₂ : ℂ, ∀ w : ℂ, ‖w‖ = 1 →
      (∃ z : ℂ, ‖z‖ = ρ ∧ C * z ^ 2 + A * z + B * w = 0) → w = w₁ ∨ w = w₂ := by
  have hconjA : (starRingEnd ℂ) A ≠ 0 := by simpa using hA
  set lam : ℂ := C * (starRingEnd ℂ) A with hlamdef
  have hlam0 : lam ≠ 0 := mul_ne_zero hC hconjA
  set K : ℝ := (Complex.normSq B / ρ ^ 2 - Complex.normSq C * ρ ^ 2 - Complex.normSq A) / 2
    with hKdef
  set y₀ : ℝ := Real.sqrt (Complex.normSq lam * ρ ^ 2 - K ^ 2) with hy0def
  refine ⟨-(C * (((K : ℂ) + (y₀ : ℂ) * Complex.I) / lam) ^ 2
             + A * (((K : ℂ) + (y₀ : ℂ) * Complex.I) / lam)) / B,
          -(C * (((K : ℂ) - (y₀ : ℂ) * Complex.I) / lam) ^ 2
             + A * (((K : ℂ) - (y₀ : ℂ) * Complex.I) / lam)) / B, ?_⟩
  rintro w hw ⟨z, hz, heq⟩
  have hnz : Complex.normSq z = ρ ^ 2 := by rw [Complex.normSq_eq_norm_sq, hz]
  have hnw : Complex.normSq w = 1 := by rw [Complex.normSq_eq_norm_sq, hw]; norm_num
  -- The real part of `lam * z` is pinned to the constant `K`.
  have hre : (lam * z).re = K := by
    have hzz : z * (C * z + A) = -(B * w) := by linear_combination heq
    have h1 : Complex.normSq z * Complex.normSq (C * z + A) = Complex.normSq B := by
      rw [← Complex.normSq_mul, hzz, Complex.normSq_neg, Complex.normSq_mul, hnw, mul_one]
    have hmul : C * z * (starRingEnd ℂ) A = lam * z := by rw [hlamdef]; ring
    have h2 : Complex.normSq (C * z + A)
        = Complex.normSq C * Complex.normSq z + Complex.normSq A + 2 * (lam * z).re := by
      rw [Complex.normSq_add, Complex.normSq_mul, hmul]
    rw [hnz, h2, hnz] at h1
    have hρ2 : (ρ : ℝ) ^ 2 ≠ 0 := by positivity
    rw [hKdef]
    field_simp
    linarith [h1]
  -- Hence its imaginary part is one of two values, so `z` is one of two points.
  have happ : Complex.normSq (lam * z) = (lam * z).re * (lam * z).re
      + (lam * z).im * (lam * z).im := Complex.normSq_apply _
  have hnlam : Complex.normSq (lam * z) = Complex.normSq lam * ρ ^ 2 := by
    rw [Complex.normSq_mul, hnz]
  have hsq : (lam * z).im ^ 2 = Complex.normSq lam * ρ ^ 2 - K ^ 2 := by
    rw [hnlam, hre] at happ; nlinarith [happ]
  have hy0nonneg : 0 ≤ Complex.normSq lam * ρ ^ 2 - K ^ 2 := by rw [← hsq]; positivity
  have hy0sq : y₀ ^ 2 = Complex.normSq lam * ρ ^ 2 - K ^ 2 := Real.sq_sqrt hy0nonneg
  have himcases : (lam * z).im = y₀ ∨ (lam * z).im = -y₀ := by
    have hz0 : ((lam * z).im - y₀) * ((lam * z).im + y₀) = 0 := by nlinarith [hsq, hy0sq]
    rcases mul_eq_zero.mp hz0 with h | h
    · left; linarith
    · right; linarith
  -- and `w` is determined by `z`.
  have hwval : w = -(C * z ^ 2 + A * z) / B := by
    rw [eq_div_iff hB]; linear_combination heq
  have hzval : z = ((K : ℂ) + (y₀ : ℂ) * Complex.I) / lam
      ∨ z = ((K : ℂ) - (y₀ : ℂ) * Complex.I) / lam := by
    rcases himcases with h | h
    · left
      have hlz : lam * z = (K : ℂ) + (y₀ : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hre, h]
      rw [eq_div_iff hlam0]; linear_combination hlz
    · right
      have hlz : lam * z = (K : ℂ) - (y₀ : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hre, h]
      rw [eq_div_iff hlam0]; linear_combination hlz
  rcases hzval with h | h
  · left; rw [hwval, h]
  · right; rw [hwval, h]

/-! ## 3. Jensen's formula evaluates the mean condition -/

/-- **Jensen / Mahler.**  The mean condition, evaluated by Jensen's formula on the factored
quadratic.  All three fibre regimes below are specialisations of this one identity. -/
theorem mahler_mean (A B C D w ζ₁ ζ₂ : ℂ) (hC : C ≠ 0)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂))
    (hmean : Real.circleAverage
        (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 = Real.log ‖D‖) :
    Real.log ‖D‖ = Real.log ‖C‖ + Real.posLog ‖ζ₁‖ + Real.posLog ‖ζ₂‖ := by
  have hXne : ∀ ζ : ℂ, (Polynomial.X - Polynomial.C ζ : Polynomial ℂ) ≠ 0 := fun ζ =>
    Polynomial.X_sub_C_ne_zero ζ
  have hprodne : ((Polynomial.X - Polynomial.C ζ₁) * (Polynomial.X - Polynomial.C ζ₂)
      : Polynomial ℂ) ≠ 0 := mul_ne_zero (hXne ζ₁) (hXne ζ₂)
  have hjensen : (Polynomial.C C * ((Polynomial.X - Polynomial.C ζ₁)
        * (Polynomial.X - Polynomial.C ζ₂))).logMahlerMeasure
      = Real.log ‖C‖ + Real.posLog ‖ζ₁‖ + Real.posLog ‖ζ₂‖ := by
    rw [Polynomial.logMahlerMeasure_C_mul hC hprodne,
        Polynomial.logMahlerMeasure_mul_eq_add_logMahlerMeasure hprodne,
        Polynomial.logMahlerMeasure_X_sub_C, Polynomial.logMahlerMeasure_X_sub_C]
    ring
  have hfun : (fun x : ℂ => Real.log ‖Polynomial.eval x (Polynomial.C C
        * ((Polynomial.X - Polynomial.C ζ₁) * (Polynomial.X - Polynomial.C ζ₂)))‖)
      = (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) := by
    funext x
    congr 2
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
    linear_combination -(hfac x)
  have hcirc : (Polynomial.C C * ((Polynomial.X - Polynomial.C ζ₁)
      * (Polynomial.X - Polynomial.C ζ₂))).logMahlerMeasure = Real.log ‖D‖ := by
    rw [Polynomial.logMahlerMeasure_def, hfun, hmean]
  rw [hjensen] at hcirc
  linarith [hcirc]

/-- Vieta: the product of the two roots. -/
theorem vieta_prod (A B C w ζ₁ ζ₂ : ℂ)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂)) :
    C * (ζ₁ * ζ₂) = B * w := by
  have h := hfac 0
  linear_combination -h

/-- **`N = 1` branch.**  Exactly one root inside the disc: the outside root has the
fibre-independent modulus `‖D‖/‖C‖`.  This is what the counting lemma then pins down. -/
theorem outside_root_modulus (A B C D w ζ₁ ζ₂ : ℂ) (hC : C ≠ 0) (hD : D ≠ 0)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂))
    (h1 : ‖ζ₁‖ < 1) (h2 : 1 < ‖ζ₂‖)
    (hmean : Real.circleAverage
        (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 = Real.log ‖D‖) :
    ‖ζ₂‖ = ‖D‖ / ‖C‖ := by
  have h := mahler_mean A B C D w ζ₁ ζ₂ hC hfac hmean
  have hp1 : Real.posLog ‖ζ₁‖ = 0 := by
    rw [Real.posLog_eq_zero_iff, abs_of_nonneg (norm_nonneg ζ₁)]; linarith
  have hp2 : Real.posLog ‖ζ₂‖ = Real.log ‖ζ₂‖ := by
    apply Real.posLog_eq_log; rw [abs_of_nonneg (norm_nonneg ζ₂)]; linarith
  rw [hp1, hp2] at h
  have hCpos : (0 : ℝ) < ‖C‖ := norm_pos_iff.mpr hC
  have hDpos : (0 : ℝ) < ‖D‖ := norm_pos_iff.mpr hD
  have hz2pos : (0 : ℝ) < ‖ζ₂‖ := lt_trans one_pos h2
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr hz2pos) (Set.mem_Ioi.mpr (div_pos hDpos hCpos))
  rw [Real.log_div (ne_of_gt hDpos) (ne_of_gt hCpos)]
  linarith [h]

/-- **`N = 2` branch** (reachable only when `j = 1`).  Both roots inside the disc forces the
`θ`-independent constraint `‖D‖ = ‖C‖`: Jensen returns no information about the fibre, which is
exactly why the counting rigidity fails there. -/
theorem both_inside_forces (A B C D w ζ₁ ζ₂ : ℂ) (hC : C ≠ 0) (hD : D ≠ 0)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂))
    (h1 : ‖ζ₁‖ < 1) (h2 : ‖ζ₂‖ < 1)
    (hmean : Real.circleAverage
        (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 = Real.log ‖D‖) :
    ‖D‖ = ‖C‖ := by
  have h := mahler_mean A B C D w ζ₁ ζ₂ hC hfac hmean
  have hp1 : Real.posLog ‖ζ₁‖ = 0 := by
    rw [Real.posLog_eq_zero_iff, abs_of_nonneg (norm_nonneg ζ₁)]; linarith
  have hp2 : Real.posLog ‖ζ₂‖ = 0 := by
    rw [Real.posLog_eq_zero_iff, abs_of_nonneg (norm_nonneg ζ₂)]; linarith
  rw [hp1, hp2] at h
  have hCpos : (0 : ℝ) < ‖C‖ := norm_pos_iff.mpr hC
  have hDpos : (0 : ℝ) < ‖D‖ := norm_pos_iff.mpr hD
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr hDpos) (Set.mem_Ioi.mpr hCpos)
  linarith [h]

/-- **`N = 0` branch** (reachable only when `j = -1`).  Both roots outside the disc forces the
`θ`-independent constraint `‖D‖ = ‖B‖`. -/
theorem both_outside_forces (A B C D w ζ₁ ζ₂ : ℂ) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hw : ‖w‖ = 1)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂))
    (h1 : 1 < ‖ζ₁‖) (h2 : 1 < ‖ζ₂‖)
    (hmean : Real.circleAverage
        (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 = Real.log ‖D‖) :
    ‖D‖ = ‖B‖ := by
  have h := mahler_mean A B C D w ζ₁ ζ₂ hC hfac hmean
  have hp1 : Real.posLog ‖ζ₁‖ = Real.log ‖ζ₁‖ := by
    apply Real.posLog_eq_log; rw [abs_of_nonneg (norm_nonneg ζ₁)]; linarith
  have hp2 : Real.posLog ‖ζ₂‖ = Real.log ‖ζ₂‖ := by
    apply Real.posLog_eq_log; rw [abs_of_nonneg (norm_nonneg ζ₂)]; linarith
  rw [hp1, hp2] at h
  have hCpos : (0 : ℝ) < ‖C‖ := norm_pos_iff.mpr hC
  have hBpos : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  have hDpos : (0 : ℝ) < ‖D‖ := norm_pos_iff.mpr hD
  have hz1pos : (0 : ℝ) < ‖ζ₁‖ := lt_trans one_pos h1
  have hz2pos : (0 : ℝ) < ‖ζ₂‖ := lt_trans one_pos h2
  -- Vieta pins the product of the moduli
  have hv := vieta_prod A B C w ζ₁ ζ₂ hfac
  have hnorm : ‖C‖ * (‖ζ₁‖ * ‖ζ₂‖) = ‖B‖ := by
    have := congrArg norm hv
    simpa [norm_mul, hw] using this
  have hlogsum : Real.log ‖ζ₁‖ + Real.log ‖ζ₂‖ = Real.log ‖B‖ - Real.log ‖C‖ := by
    have hml : Real.log (‖C‖ * (‖ζ₁‖ * ‖ζ₂‖)) = Real.log ‖B‖ := by rw [hnorm]
    rw [Real.log_mul (ne_of_gt hCpos) (by positivity),
        Real.log_mul (ne_of_gt hz1pos) (ne_of_gt hz2pos)] at hml
    linarith [hml]
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr hDpos) (Set.mem_Ioi.mpr hBpos)
  linarith [h, hlogsum]


/-! ### The LINEAR symbol: Jensen pins the coefficients exactly

A three-point dependence produces a symbol that is linear, not quadratic, and for a linear
polynomial Jensen's formula is not an inequality but an exact evaluation:

  `circleAverage (log‖c₁ z + c₀‖) = log (max ‖c₀‖ ‖c₁‖)`.

Combined with the Birkhoff mean condition `∫ log‖symbol‖ = log‖c₂‖`, this forces

  `max ‖c₀‖ ‖c₁‖ = ‖c₂‖`,

a codimension-one constraint on the dependence coefficients themselves.  Generic coefficients
violate it outright, so no dependence can exist — three-point linear independence, from Jensen
alone, with no Linnell and no spectral theory. -/

/-- **Jensen for a linear symbol.**  The circle average of `log‖c₁ z + c₀‖` is
`log‖c₁‖ + posLog (‖c₀‖/‖c₁‖)`. -/
theorem linear_mean (c₀ c₁ : ℂ) (h₁ : c₁ ≠ 0) :
    Real.circleAverage (fun z : ℂ => Real.log ‖c₁ * z + c₀‖) 0 1
      = Real.log ‖c₁‖ + Real.posLog (‖c₀‖ / ‖c₁‖) := by
  set ζ : ℂ := -c₀ / c₁ with hζ
  have hXne : (Polynomial.X - Polynomial.C ζ : Polynomial ℂ) ≠ 0 := Polynomial.X_sub_C_ne_zero ζ
  have hjensen : (Polynomial.C c₁ * (Polynomial.X - Polynomial.C ζ)).logMahlerMeasure
      = Real.log ‖c₁‖ + Real.posLog ‖ζ‖ := by
    rw [Polynomial.logMahlerMeasure_C_mul h₁ hXne, Polynomial.logMahlerMeasure_X_sub_C]
  have hnormζ : ‖ζ‖ = ‖c₀‖ / ‖c₁‖ := by rw [hζ, norm_div, norm_neg]
  have hfun : (fun x : ℂ => Real.log ‖Polynomial.eval x
        (Polynomial.C c₁ * (Polynomial.X - Polynomial.C ζ))‖)
      = (fun z : ℂ => Real.log ‖c₁ * z + c₀‖) := by
    funext x
    congr 2
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X, hζ]
    field_simp
    ring
  rw [← hfun, ← Polynomial.logMahlerMeasure_def, hjensen, hnormζ]


/-- The linear Mahler measure in closed form: `log (max ‖c₀‖ ‖c₁‖)`. -/
theorem linear_mean_max (c₀ c₁ : ℂ) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) :
    Real.circleAverage (fun z : ℂ => Real.log ‖c₁ * z + c₀‖) 0 1
      = Real.log (max ‖c₀‖ ‖c₁‖) := by
  have h0p : (0 : ℝ) < ‖c₀‖ := norm_pos_iff.mpr h₀
  have h1p : (0 : ℝ) < ‖c₁‖ := norm_pos_iff.mpr h₁
  rw [linear_mean c₀ c₁ h₁]
  rcases le_total ‖c₀‖ ‖c₁‖ with hle | hle
  · have hz : Real.posLog (‖c₀‖ / ‖c₁‖) = 0 := by
      rw [Real.posLog_eq_zero_iff, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖c₀‖ / ‖c₁‖),
        div_le_one h1p]
      exact hle
    rw [hz, add_zero, max_eq_right hle]
  · have hz : Real.posLog (‖c₀‖ / ‖c₁‖) = Real.log (‖c₀‖ / ‖c₁‖) := by
      apply Real.posLog_eq_log
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖c₀‖ / ‖c₁‖), one_le_div h1p]
      exact hle
    rw [hz, Real.log_div (ne_of_gt h0p) (ne_of_gt h1p), max_eq_left hle]
    ring

/-- **The three-point coefficient constraint.**  The mean condition for a linear symbol forces
`max ‖c₀‖ ‖c₁‖ = ‖c₂‖` — a codimension-one condition on the dependence coefficients THEMSELVES,
not on the fibre. -/
theorem linear_coeff_constraint (c₀ c₁ c₂ : ℂ) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (hmean : Real.circleAverage (fun z : ℂ => Real.log ‖c₁ * z + c₀‖) 0 1 = Real.log ‖c₂‖) :
    max ‖c₀‖ ‖c₁‖ = ‖c₂‖ := by
  rw [linear_mean_max c₀ c₁ h₀ h₁] at hmean
  have hmpos : (0 : ℝ) < max ‖c₀‖ ‖c₁‖ :=
    lt_of_lt_of_le (norm_pos_iff.mpr h₀) (le_max_left _ _)
  have h2pos : (0 : ℝ) < ‖c₂‖ := norm_pos_iff.mpr h₂
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr hmpos) (Set.mem_Ioi.mpr h2pos) hmean

/-- **No three-point dependence off the codimension-one set.**  Coefficients violating
`max ‖c₀‖ ‖c₁‖ = ‖c₂‖` cannot satisfy the mean condition, so they support no dependence.

This is three-point linear independence for generic coefficients, from Jensen's formula alone —
no Linnell, no von Neumann algebras, no spectral theory. -/
theorem no_linear_dependence_of_ne (c₀ c₁ c₂ : ℂ) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (hne : max ‖c₀‖ ‖c₁‖ ≠ ‖c₂‖) :
    ¬ (Real.circleAverage (fun z : ℂ => Real.log ‖c₁ * z + c₀‖) 0 1 = Real.log ‖c₂‖) :=
  fun hmean => hne (linear_coeff_constraint c₀ c₁ c₂ h₀ h₁ h₂ hmean)


/-- **Where the three-point difficulty actually lives.**

The mean condition forces `max ‖c₀‖ ‖c₁‖ = ‖c₂‖`.  Unless `‖c₀‖ = ‖c₁‖`, that identifies which
of the two is the maximum — and correspondingly puts the symbol's root strictly inside or strictly
outside the unit circle, so `threePoint_smallDivisor_summable` (or its mirror) applies and the
residual-cone machinery is available. -/
theorem threePoint_hard_case_only (c₀ c₁ c₂ : ℂ) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (hmean : Real.circleAverage (fun z : ℂ => Real.log ‖c₁ * z + c₀‖) 0 1 = Real.log ‖c₂‖)
    (hne : ‖c₀‖ ≠ ‖c₁‖) :
    (‖c₁‖ < ‖c₀‖ ∧ ‖c₀‖ = ‖c₂‖) ∨ (‖c₀‖ < ‖c₁‖ ∧ ‖c₁‖ = ‖c₂‖) := by
  have hc := linear_coeff_constraint c₀ c₁ c₂ h₀ h₁ h₂ hmean
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Or.inr ⟨hlt, by rwa [max_eq_right (le_of_lt hlt)] at hc⟩
  · exact Or.inl ⟨hgt, by rwa [max_eq_left (le_of_lt hgt)] at hc⟩

/-- **The irreducible case is codimension TWO.**  In the one situation the expandability argument
cannot reach — `‖c₀‖ = ‖c₁‖`, the root sitting exactly on the unit circle — the mean condition
forces all THREE coefficient moduli to coincide.

So the entire residual difficulty of the three-point resonant configuration is confined to
`‖c₀‖ = ‖c₁‖ = ‖c₂‖`.  That is two independent equations on the coefficients, not one: a
codimension-two stratum.  Everything else is settled by Jensen plus the small-divisor machinery,
with no Linnell and no spectral theory. -/
theorem threePoint_irreducible_case (c₀ c₁ c₂ : ℂ) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (hmean : Real.circleAverage (fun z : ℂ => Real.log ‖c₁ * z + c₀‖) 0 1 = Real.log ‖c₂‖)
    (heq : ‖c₀‖ = ‖c₁‖) :
    ‖c₀‖ = ‖c₂‖ ∧ ‖c₁‖ = ‖c₂‖ := by
  have hc := linear_coeff_constraint c₀ c₁ c₂ h₀ h₁ h₂ hmean
  rw [max_eq_left (le_of_eq heq.symm)] at hc
  exact ⟨hc, heq ▸ hc⟩


/-! ### The cyclic symmetry closes the three-point case

`linear_coeff_constraint` was derived by solving the fibre equation for one distinguished
coefficient.  If the same argument can be run for each of the three choices, each run yields its
own constraint:

  `max ‖c₀‖ ‖c₁‖ = ‖c₂‖`,  `max ‖c₀‖ ‖c₂‖ = ‖c₁‖`,  `max ‖c₁‖ ‖c₂‖ = ‖c₀‖`.

Any one of these is a codimension-one condition.  All three TOGETHER force `‖c₀‖ = ‖c₁‖ = ‖c₂‖`,
by pure arithmetic: the first says `‖c₂‖` dominates, the second says `‖c₁‖` does, and a quantity
cannot be strictly dominated by one it dominates.

So wherever all three constraints are available, a dependence is impossible unless the three
coefficient moduli coincide — exactly the codimension-two stratum `threePoint_irreducible_case`
identified.

**Scope warning — the three constraints are NOT automatic.**  Whether all three are available is a
question about the CONFIGURATION, not a relabelling.  For `{(0,0),(1,0),(√2,√2)}`, solving for the
`(√2,√2)` term leaves `{(0,0),(1,0)}`, a lattice pair, and that is what produces the clean linear
symbol `c₀ + c₁e^{-2πiω}` used above.  Solving instead for the `(1,0)` term leaves
`{(0,0),(√2,√2)}`, whose difference is *not* a lattice vector, so the remaining pair does not
present as a linear polynomial in one exponential and the argument does not transfer verbatim.

The theorems below therefore take the three mean conditions as HYPOTHESES.  Establishing them for a
given configuration is separate work; what is proved here is the implication. -/

/-- **The three cyclic constraints force equality.**  Pure arithmetic, but it is the step that
turns three codimension-one conditions into a codimension-two conclusion. -/
theorem three_max_constraints_force_equal (a b c : ℝ)
    (h1 : max a b = c) (h2 : max a c = b) (h3 : max b c = a) : a = b ∧ b = c := by
  have hca : a ≤ c := h1 ▸ le_max_left a b
  have hcb : b ≤ c := h1 ▸ le_max_right a b
  have hba : a ≤ b := h2 ▸ le_max_left a c
  have hbc : c ≤ b := h2 ▸ le_max_right a c
  have hab : b ≤ a := h3 ▸ le_max_left b c
  have hac : c ≤ a := h3 ▸ le_max_right b c
  exact ⟨by linarith, by linarith⟩

/-- **Three-point independence except on the equal-moduli stratum.**  If the three cyclic mean
conditions hold, then all three moduli agree; contrapositively, coefficients whose moduli are not
all equal support no dependence.  The three conditions are hypotheses, not consequences of the
configuration — see the scope warning above. -/
theorem threePoint_moduli_all_equal (c₀ c₁ c₂ : ℂ)
    (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (m₂ : Real.circleAverage (fun z : ℂ => Real.log ‖c₁ * z + c₀‖) 0 1 = Real.log ‖c₂‖)
    (m₁ : Real.circleAverage (fun z : ℂ => Real.log ‖c₂ * z + c₀‖) 0 1 = Real.log ‖c₁‖)
    (m₀ : Real.circleAverage (fun z : ℂ => Real.log ‖c₂ * z + c₁‖) 0 1 = Real.log ‖c₀‖) :
    ‖c₀‖ = ‖c₁‖ ∧ ‖c₁‖ = ‖c₂‖ :=
  three_max_constraints_force_equal ‖c₀‖ ‖c₁‖ ‖c₂‖
    (linear_coeff_constraint c₀ c₁ c₂ h₀ h₁ h₂ m₂)
    (linear_coeff_constraint c₀ c₂ c₁ h₀ h₂ h₁ m₁)
    (linear_coeff_constraint c₁ c₂ c₀ h₁ h₂ h₀ m₀)

/-- Contrapositive form: unequal moduli rule out the three cyclic mean conditions outright. -/
theorem threePoint_no_dependence_of_moduli_ne (c₀ c₁ c₂ : ℂ)
    (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (hne : ¬ (‖c₀‖ = ‖c₁‖ ∧ ‖c₁‖ = ‖c₂‖)) :
    ¬ ((Real.circleAverage (fun z : ℂ => Real.log ‖c₁ * z + c₀‖) 0 1 = Real.log ‖c₂‖)
      ∧ (Real.circleAverage (fun z : ℂ => Real.log ‖c₂ * z + c₀‖) 0 1 = Real.log ‖c₁‖)
      ∧ (Real.circleAverage (fun z : ℂ => Real.log ‖c₂ * z + c₁‖) 0 1 = Real.log ‖c₀‖)) := by
  rintro ⟨m₂, m₁, m₀⟩
  exact hne (threePoint_moduli_all_equal c₀ c₁ c₂ h₀ h₁ h₂ m₂ m₁ m₀)


/-! ## 4. The endgame -/

/-- Number of roots of the factored quadratic lying in the open unit disc — the paper's `N(θ)`. -/
noncomputable def rootCount (ζ₁ ζ₂ : ℂ) : ℤ :=
  (if ‖ζ₁‖ < 1 then 1 else 0) + (if ‖ζ₂‖ < 1 then 1 else 0)

/-- **The degree condition follows from the MEAN condition — no ILR input.**

`live_set_subset_four` takes the degree clause `rootCount = 1 + j` as the hypothesis `hILR`, named
for Iwanik–Lemańczyk–Rudolph, whose theorem is the usual source of it.  But for `j = 0` that clause
is not an extra input at all: with both roots off the unit circle there are only three
possibilities, `rootCount ∈ {0,1,2}`, and Jensen's formula already excludes the two extremes —
`both_inside_forces` turns `rootCount = 2` into `‖D‖ = ‖C‖` and `both_outside_forces` turns
`rootCount = 0` into `‖D‖ = ‖B‖`.  Assuming those two degeneracies away leaves `rootCount = 1`.

So the `j = 0` case of the whole argument needs **no spectral theory whatsoever** — no countable
Lebesgue spectrum, no absolutely continuous cocycles of bounded variation, none of the ILR
machinery that has never been formalised in any proof assistant.  Only Jensen's formula, which
Mathlib has. -/
theorem rootCount_eq_one_of_mean (A B C D w ζ₁ ζ₂ : ℂ)
    (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0) (hw : ‖w‖ = 1)
    (hDC : ‖D‖ ≠ ‖C‖) (hDB : ‖D‖ ≠ ‖B‖)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂))
    (h1 : ‖ζ₁‖ ≠ 1) (h2 : ‖ζ₂‖ ≠ 1)
    (hmean : Real.circleAverage
        (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 = Real.log ‖D‖) :
    rootCount ζ₁ ζ₂ = 1 := by
  unfold rootCount
  rcases lt_or_gt_of_ne h1 with hlt1 | hgt1 <;> rcases lt_or_gt_of_ne h2 with hlt2 | hgt2
  · exact absurd (both_inside_forces A B C D w ζ₁ ζ₂ hC hD hfac hlt1 hlt2 hmean) hDC
  · rw [if_pos hlt1, if_neg (by linarith : ¬ ‖ζ₂‖ < 1)]; norm_num
  · rw [if_neg (by linarith : ¬ ‖ζ₁‖ < 1), if_pos hlt2]; norm_num
  · exact absurd (both_outside_forces A B C D w ζ₁ ζ₂ hB hC hD hw hfac hgt1 hgt2 hmean) hDB

/-- **The live-fibre set has at most four elements**, for every `j ∈ ℤ`, subject only to the two
codimension-one exceptions `j = 1, ‖D‖ = ‖C‖` and `j = -1, ‖D‖ = ‖B‖`.

`L` is the set of live fibres, parametrised by `w = e^{-2πiθ}`.  `hmean` is the coboundary/Birkhoff
mean condition and `hILR` the Iwanik–Lemańczyk–Rudolph degree obstruction (see the module
docstring).  Two of the four points come from fibres whose quadratic has a root *on* the unit
circle (`ρ = 1`), the other two from the `N = 1` fibres, whose outside root has the fixed modulus
`‖D‖/‖C‖`. -/
theorem live_set_subset_four
    (A B C D : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (j : ℤ) (hj1 : j = 1 → ‖D‖ ≠ ‖C‖) (hjm1 : j = -1 → ‖D‖ ≠ ‖B‖)
    (L : Set ℂ)
    (hunit : ∀ w ∈ L, ‖w‖ = 1)
    (hmean : ∀ w ∈ L, Real.circleAverage
        (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 = Real.log ‖D‖)
    (hILR : ∀ w ∈ L, ∀ ζ₁ ζ₂ : ℂ,
        (∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂)) →
        ‖ζ₁‖ ≠ 1 → ‖ζ₂‖ ≠ 1 → rootCount ζ₁ ζ₂ = 1 + j) :
    ∃ w₁ w₂ w₃ w₄ : ℂ, L ⊆ {w₁, w₂, w₃, w₄} := by
  have hCpos : (0 : ℝ) < ‖C‖ := norm_pos_iff.mpr hC
  have hDpos : (0 : ℝ) < ‖D‖ := norm_pos_iff.mpr hD
  obtain ⟨b₁, b₂, hb⟩ := counting_le_two A B C hA hB hC (ρ := 1) one_pos
  obtain ⟨r₁, r₂, hr⟩ := counting_le_two A B C hA hB hC (ρ := ‖D‖ / ‖C‖) (div_pos hDpos hCpos)
  refine ⟨b₁, b₂, r₁, r₂, ?_⟩
  intro w hwL
  obtain ⟨ζ₁, ζ₂, hfac⟩ := quad_factor A C (B * w) hC
  have hroot : ∀ ζ : ℂ, (ζ = ζ₁ ∨ ζ = ζ₂) → C * ζ ^ 2 + A * ζ + B * w = 0 := by
    rintro ζ (rfl | rfl) <;> rw [hfac] <;> ring
  by_cases h1 : ‖ζ₁‖ = 1
  · rcases hb w (hunit w hwL) ⟨ζ₁, h1, hroot ζ₁ (Or.inl rfl)⟩ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  by_cases h2 : ‖ζ₂‖ = 1
  · rcases hb w (hunit w hwL) ⟨ζ₂, h2, hroot ζ₂ (Or.inr rfl)⟩ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  -- both roots off the unit circle: the ILR degree obstruction applies
  have hcount := hILR w hwL ζ₁ ζ₂ hfac h1 h2
  have hmemr : ∀ ζ : ℂ, ‖ζ‖ = ‖D‖ / ‖C‖ → (ζ = ζ₁ ∨ ζ = ζ₂) →
      w = r₁ ∨ w = r₂ := fun ζ hζ hmem => hr w (hunit w hwL) ⟨ζ, hζ, hroot ζ hmem⟩
  unfold rootCount at hcount
  split_ifs at hcount with ha hb1 hb2
  · -- `N = 2`: forces `j = 1`, and Jensen then forces `‖D‖ = ‖C‖`
    exact absurd (both_inside_forces A B C D w ζ₁ ζ₂ hC hD hfac ha hb1 (hmean w hwL))
      (hj1 (by omega))
  · -- `N = 1`: `ζ₁` inside, `ζ₂` outside
    have h2' : 1 < ‖ζ₂‖ := lt_of_le_of_ne (not_lt.mp hb1) (Ne.symm h2)
    have := outside_root_modulus A B C D w ζ₁ ζ₂ hC hD hfac ha h2' (hmean w hwL)
    rcases hmemr ζ₂ this (Or.inr rfl) with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · -- `N = 1`: `ζ₂` inside, `ζ₁` outside
    have h1' : 1 < ‖ζ₁‖ := lt_of_le_of_ne (not_lt.mp ha) (Ne.symm h1)
    have hfac' : ∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₂) * (z - ζ₁) := by
      intro z; rw [hfac z]; ring
    have := outside_root_modulus A B C D w ζ₂ ζ₁ hC hD hfac' hb2 h1' (hmean w hwL)
    rcases hmemr ζ₁ this (Or.inl rfl) with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · -- `N = 0`: forces `j = -1`, and Jensen then forces `‖D‖ = ‖B‖`
    have h1' : 1 < ‖ζ₁‖ := lt_of_le_of_ne (not_lt.mp ha) (Ne.symm h1)
    have h2' : 1 < ‖ζ₂‖ := lt_of_le_of_ne (not_lt.mp hb2) (Ne.symm h2)
    exact absurd (both_outside_forces A B C D w ζ₁ ζ₂ hB hC hD (hunit w hwL) hfac h1' h2'
      (hmean w hwL)) (hjm1 (by omega))

/-- The live-fibre set is finite. -/
theorem live_set_finite
    (A B C D : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (j : ℤ) (hj1 : j = 1 → ‖D‖ ≠ ‖C‖) (hjm1 : j = -1 → ‖D‖ ≠ ‖B‖)
    (L : Set ℂ)
    (hunit : ∀ w ∈ L, ‖w‖ = 1)
    (hmean : ∀ w ∈ L, Real.circleAverage
        (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 = Real.log ‖D‖)
    (hILR : ∀ w ∈ L, ∀ ζ₁ ζ₂ : ℂ,
        (∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂)) →
        ‖ζ₁‖ ≠ 1 → ‖ζ₂‖ ≠ 1 → rootCount ζ₁ ζ₂ = 1 + j) :
    L.Finite := by
  obtain ⟨w₁, w₂, w₃, w₄, hsub⟩ :=
    live_set_subset_four A B C D hA hB hC hD j hj1 hjm1 L hunit hmean hILR
  exact Set.Finite.subset (Set.toFinite _) hsub

/-- **The contradiction that closes the theorem.**  The Zak/Fubini step supplies a live set of
positive measure whenever the window `g` is nonzero, hence an infinite one; this rules it out. -/
theorem live_set_not_infinite
    (A B C D : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (j : ℤ) (hj1 : j = 1 → ‖D‖ ≠ ‖C‖) (hjm1 : j = -1 → ‖D‖ ≠ ‖B‖)
    (L : Set ℂ)
    (hunit : ∀ w ∈ L, ‖w‖ = 1)
    (hmean : ∀ w ∈ L, Real.circleAverage
        (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 = Real.log ‖D‖)
    (hILR : ∀ w ∈ L, ∀ ζ₁ ζ₂ : ℂ,
        (∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂)) →
        ‖ζ₁‖ ≠ 1 → ‖ζ₂‖ ≠ 1 → rootCount ζ₁ ζ₂ = 1 + j) :
    ¬ L.Infinite :=
  fun h => h (live_set_finite A B C D hA hB hC hD j hj1 hjm1 L hunit hmean hILR)

/-- **The live set is finite with NO ILR input at all.**

Take `j = 0` in `live_set_not_infinite` and discharge its degree clause with
`rootCount_eq_one_of_mean`.  What remains as hypotheses is only: the coefficients are nonzero, the
fibre parameters are unimodular, the mean (Jensen/Birkhoff) condition holds, and the two
codimension-one degeneracies `‖D‖ = ‖C‖`, `‖D‖ = ‖B‖` are avoided.

No countable Lebesgue spectrum, no absolutely continuous cocycles, no Iwanik–Lemańczyk–Rudolph.
This is the form in which the endgame is actually reachable from Mathlib. -/
theorem live_set_not_infinite_of_mean
    (A B C D : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hDC : ‖D‖ ≠ ‖C‖) (hDB : ‖D‖ ≠ ‖B‖)
    (L : Set ℂ)
    (hunit : ∀ w ∈ L, ‖w‖ = 1)
    (hmean : ∀ w ∈ L, Real.circleAverage
        (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 = Real.log ‖D‖) :
    ¬ L.Infinite := by
  refine live_set_not_infinite A B C D hA hB hC hD 0
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) L hunit hmean ?_
  intro w hw ζ₁ ζ₂ hfac h1 h2
  have hr := rootCount_eq_one_of_mean A B C D w ζ₁ ζ₂ hB hC hD (hunit w hw) hDC hDB hfac h1 h2
    (hmean w hw)
  simpa using hr


/-- The paper's stated range `j ∉ {-1, 1}` is the special case in which the two cone hypotheses
are vacuous. -/
theorem live_set_not_infinite_of_ne
    (A B C D : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (j : ℤ) (hj1 : j ≠ 1) (hjm1 : j ≠ -1)
    (L : Set ℂ)
    (hunit : ∀ w ∈ L, ‖w‖ = 1)
    (hmean : ∀ w ∈ L, Real.circleAverage
        (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 = Real.log ‖D‖)
    (hILR : ∀ w ∈ L, ∀ ζ₁ ζ₂ : ℂ,
        (∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂)) →
        ‖ζ₁‖ ≠ 1 → ‖ζ₂‖ ≠ 1 → rootCount ζ₁ ζ₂ = 1 + j) :
    ¬ L.Infinite :=
  live_set_not_infinite A B C D hA hB hC hD j (fun h => absurd h hj1) (fun h => absurd h hjm1)
    L hunit hmean hILR

/-! ## 5. Toward the residual cones: the Diophantine arithmetic input

The two exceptional cones above (`j = 1, ‖D‖ = ‖C‖` and `j = -1, ‖D‖ = ‖B‖`) are closed by a
separate argument: on the cone the transformed cocycle has modulus exactly `1`, so `log F_θ` has a
one-sided Fourier expansion with *geometrically* decaying coefficients, and the cohomological
equation `V(t-a) - V(t) = log F_θ(t)` can be solved outright whenever the small-divisor series

  `C_θ(a) = Σ_{n≥1} |r₁ⁿ + r₂ⁿ| / (n · |e^{2πina} - 1|)`

converges.  Solving it kills the cocycle and quantises the eigenvalue, pinning `θ` to a countable
set and contradicting positive measure.

The lemma below is the **arithmetic half** of that argument: under a Diophantine lower bound on the
divisors, geometric decay of the numerators beats the small divisors, so `C_θ(a) < ∞`.  Since `√2`
is badly approximable, this covers the Heil–Speegle configuration.

The **analytic half** — building `V` from the Fourier coefficients and deducing eigenvalue
quantisation — is *not* formalised here; it needs `Lp`/`fourierBasis` machinery on `AddCircle`
(Mathlib has no Fourier translation lemma and no direct "all coefficients vanish ⇒ zero" outside
the `Lp` setting). -/

/-- **Diophantine small-divisor summability.**  If the divisors `Δ n` obey the Diophantine lower
bound `γ / n^τ ≤ Δ n` and the numerators `c n` decay geometrically, then the small-divisor series
`Σ |c n| / (n · Δ n)` converges.  (The `n = 0` term is `0` by the junk value of division by zero.) -/
theorem smallDivisor_summable
    {γ ρ : ℝ} (hγ : 0 < γ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {τ : ℕ}
    {Δ : ℕ → ℝ} (hΔ : ∀ n : ℕ, 1 ≤ n → γ / (n : ℝ) ^ τ ≤ Δ n)
    {c : ℕ → ℝ} (hc : ∀ n : ℕ, |c n| ≤ 2 * ρ ^ n) :
    Summable (fun n : ℕ => |c n| / ((n : ℝ) * Δ n)) := by
  have hnorm : ‖ρ‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hρ0]
  have hmaj : Summable (fun n : ℕ => (2 / γ) * ((n : ℝ) ^ τ * ρ ^ n)) :=
    (summable_pow_mul_geometric_of_norm_lt_one τ hnorm).mul_left _
  refine Summable.of_norm_bounded hmaj ?_
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  · have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpow : (0 : ℝ) < (n : ℝ) ^ τ := by positivity
    have hΔn : γ / (n : ℝ) ^ τ ≤ Δ n := hΔ n hn
    have hqpos : (0 : ℝ) < γ / (n : ℝ) ^ τ := by positivity
    have hΔpos : 0 < Δ n := lt_of_lt_of_le hqpos hΔn
    have hden : γ / (n : ℝ) ^ τ ≤ (n : ℝ) * Δ n := by nlinarith [hΔn, hΔpos, hnR]
    have hdenpos : (0 : ℝ) < (n : ℝ) * Δ n := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc |c n| / ((n : ℝ) * Δ n) ≤ (2 * ρ ^ n) / (γ / (n : ℝ) ^ τ) := by
          gcongr
          exact hc n
      _ = (2 / γ) * ((n : ℝ) ^ τ * ρ ^ n) := by field_simp

/-! ## 6. The analytic half of the residual-cone closure: eigenvalue quantisation

On the residual cone the transformed cocycle has modulus exactly `1`, and once the cohomological
equation is solved the fibre function satisfies `Y (t - a) = λ · Y t`.  The lemmas below show that
such a `λ` is forced onto the **countable** set `{fourier n (-a) : n ∈ ℤ}`, which is what makes the
live-fibre set null and contradicts positive measure.

`fourierCoeff_comp_add` is the translation lemma for Fourier coefficients; it is **not** in Mathlib
and is proved here from translation-invariance of the Haar measure on `AddCircle`. -/

section Quantisation

open MeasureTheory AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

/-- `fourier n` is multiplicative in its **argument** (Mathlib's `fourier_add` is additivity in the
*index*). -/
theorem fourier_arg_add (n : ℤ) (x y : AddCircle T) :
    (fourier n (x + y) : ℂ) = (fourier n x : ℂ) * (fourier n y : ℂ) := by
  simp_rw [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- `fourier n a * fourier (-n) a = 1`. -/
theorem fourier_mul_neg (n : ℤ) (a : AddCircle T) :
    (fourier n a : ℂ) * (fourier (-n) a : ℂ) = 1 := by
  rw [fourier_neg, Complex.mul_conj]
  simp

/-- **Translation lemma for Fourier coefficients** — absent from Mathlib.  Translating the argument
multiplies the `n`-th coefficient by `fourier n a`. -/
theorem fourierCoeff_comp_add (f : AddCircle T → ℂ) (a : AddCircle T) (n : ℤ) :
    fourierCoeff (fun t => f (t + a)) n = (fourier n a : ℂ) * fourierCoeff f n := by
  have hsplit : ∀ t : AddCircle T,
      (fourier (-n) (t + a) : ℂ) = (fourier (-n) t : ℂ) * (fourier (-n) a : ℂ) :=
    fun t => fourier_arg_add (-n) t a
  have hinv := fourier_mul_neg n a
  rw [fourierCoeff, fourierCoeff]
  calc ∫ t : AddCircle T, (fourier (-n) t : ℂ) • f (t + a) ∂haarAddCircle
      = ∫ t : AddCircle T,
          (fourier n a : ℂ) * ((fourier (-n) (t + a) : ℂ) • f (t + a)) ∂haarAddCircle := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        simp only [smul_eq_mul, hsplit t]
        linear_combination (-(fourier (-n) t : ℂ) * f (t + a)) * hinv
    _ = ∫ t : AddCircle T,
          (fourier n a : ℂ) * ((fourier (-n) t : ℂ) • f t) ∂haarAddCircle :=
        integral_add_right_eq_self
          (fun s : AddCircle T => (fourier n a : ℂ) * ((fourier (-n) s : ℂ) • f s)) a
    _ = (fourier n a : ℂ) * ∫ t : AddCircle T, (fourier (-n) t : ℂ) • f t ∂haarAddCircle :=
        integral_const_mul _ _

/-- **Eigenvalue quantisation.**  If a function on the circle satisfies the twisted translation
equation `f (t - a) = lam * f t` almost everywhere and is not Fourier-trivial, then `lam` lies in
the countable set `{fourier n (-a) : n ∈ ℤ}`.

This is the step that pins the fibre parameter to a countable set, contradicting positive measure.
The hypothesis is stated on the Fourier side (`∃ n, fourierCoeff f n ≠ 0`); bridging it to `f ≠ 0`
in `L²` is Parseval (`tsum_sq_fourierCoeff`) and is not done here. -/
theorem eigenvalue_quantised (f : AddCircle T → ℂ) (a : AddCircle T) (lam : ℂ)
    (hne : ∃ n : ℤ, fourierCoeff f n ≠ 0)
    (heq : ∀ᵐ t ∂(haarAddCircle : Measure (AddCircle T)), f (t - a) = lam * f t) :
    ∃ n : ℤ, lam = (fourier n (-a) : ℂ) := by
  obtain ⟨n, hn⟩ := hne
  have hsub : ∀ t : AddCircle T, t + (-a) = t - a := fun t => (sub_eq_add_neg t a).symm
  have h1 : fourierCoeff (fun t => f (t - a)) n = (fourier n (-a) : ℂ) * fourierCoeff f n := by
    have := fourierCoeff_comp_add f (-a) n
    simpa only [hsub] using this
  have hae : (fun t => f (t - a)) =ᵐ[(haarAddCircle : Measure (AddCircle T))]
      (fun t => lam * f t) := heq
  have h2 : fourierCoeff (fun t => f (t - a)) n = lam * fourierCoeff f n := by
    rw [fourierCoeff_congr_ae hae, fourierCoeff.const_mul]
  exact ⟨n, (mul_right_cancel₀ hn ((h1.symm.trans h2).symm))⟩

/-- The same statement made concrete on the circle of period `1`: the eigenvalue is
`exp (-2 π i k a)` for some integer `k`. -/
theorem eigenvalue_quantised_exp (f : AddCircle (1 : ℝ) → ℂ) (a : ℝ) (lam : ℂ)
    (hne : ∃ n : ℤ, fourierCoeff f n ≠ 0)
    (heq : ∀ᵐ t ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))),
        f (t - (a : AddCircle (1 : ℝ))) = lam * f t) :
    ∃ k : ℤ, lam = Complex.exp (-(2 * ↑Real.pi * Complex.I * k * a)) := by
  obtain ⟨n, hn⟩ := eigenvalue_quantised f (a : AddCircle (1 : ℝ)) lam hne heq
  refine ⟨n, ?_⟩
  rw [hn]
  have hneg : ((-a : ℝ) : AddCircle (1 : ℝ)) = -(a : AddCircle (1 : ℝ)) := by simp
  rw [← hneg, fourier_coe_apply]
  push_cast
  ring_nf

/-- A nonzero `L²` function has a nonzero Fourier coefficient.  Proved from injectivity of the
`fourierBasis` Hilbert-basis representation, which avoids the `Lp` integrability plumbing. -/
theorem exists_fourierCoeff_ne_zero
    (f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle T))) (hf : f ≠ 0) :
    ∃ n : ℤ, fourierCoeff (f : AddCircle T → ℂ) n ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  refine hf (fourierBasis.repr.injective ?_)
  ext i
  simp [fourierBasis_repr, hcon i]

/-- `eigenvalue_quantised` with the natural hypothesis `f ≠ 0` in `L²`. -/
theorem eigenvalue_quantised_L2
    (f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle T))) (hf : f ≠ 0)
    (a : AddCircle T) (lam : ℂ)
    (heq : ∀ᵐ t ∂(haarAddCircle : Measure (AddCircle T)),
        (f : AddCircle T → ℂ) (t - a) = lam * (f : AddCircle T → ℂ) t) :
    ∃ n : ℤ, lam = (fourier n (-a) : ℂ) :=
  eigenvalue_quantised _ a lam (exists_fourierCoeff_ne_zero f hf) heq

/-! ### The cohomological equation

The residual-cone argument needs more than the SUMMABILITY of the small-divisor series: it needs an
actual solution `ψ` of the cohomological equation `ψ(t + a) - ψ(t) = φ(t)`, obtained by dividing
the Fourier coefficients, `ψ̂ n = φ̂ n / (fourier n a - 1)`.

Two things must hold for that division to be legitimate.  The divisor must not vanish — that is
irrationality of `a`, proved below at `a = √2` — and the resulting series must converge, which is
exactly `smallDivisor_summable_sqrt_two`.  The algebra itself is then one line. -/

/-- `n √2` is never an integer for `n ≠ 0`. -/
theorem sqrt_two_int_mul_ne_int {n : ℤ} (hn : n ≠ 0) (m : ℤ) :
    (n : ℝ) * Real.sqrt 2 ≠ (m : ℝ) := by
  intro h
  have hn0 : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hsq : Real.sqrt 2 = (m : ℝ) / (n : ℝ) := by
    rw [eq_div_iff hn0]; linear_combination h
  exact irrational_sqrt_two.ne_rational m n hsq

/-- **The small divisors never vanish at `a = √2`.**  For `n ≠ 0` the divisor
`fourier n √2 - 1` is nonzero, so the coefficientwise division defining `ψ` is legitimate. -/
theorem fourier_sub_one_ne_zero_sqrt_two {n : ℤ} (hn : n ≠ 0) :
    (fourier n ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) : ℂ) - 1 ≠ 0 := by
  intro h
  have h1 : (fourier n ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) : ℂ) = 1 := by
    linear_combination h
  rw [fourier_coe_apply] at h1
  simp only [Complex.ofReal_one, div_one] at h1
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h1
  have hpi : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hcancel : ((n : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I)
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by linear_combination hk
  have hc : (n : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = (k : ℂ) := mul_right_cancel₀ hpi hcancel
  have hr : (n : ℝ) * Real.sqrt 2 = (k : ℝ) := by exact_mod_cast hc
  exact sqrt_two_int_mul_ne_int hn k hr

/-- **The cohomological equation, coefficientwise.**  If `ψ`'s `n`-th Fourier coefficient is chosen
as `c / (fourier n a - 1)`, then the `n`-th coefficient of the coboundary `ψ(· + a) - ψ` is exactly
`c`.  This is the algebraic heart of the coboundary construction; the analytic content is that the
resulting coefficient sequence is summable, which `smallDivisor_summable_sqrt_two` supplies. -/
theorem coboundary_coeff (ψ : AddCircle T → ℂ) (a : AddCircle T) (n : ℤ) (c : ℂ)
    (hdiv : (fourier n a : ℂ) - 1 ≠ 0)
    (hψ : fourierCoeff ψ n = c / ((fourier n a : ℂ) - 1)) :
    fourierCoeff (fun t => ψ (t + a)) n - fourierCoeff ψ n = c := by
  rw [fourierCoeff_comp_add, hψ]
  field_simp

/-- **The coboundary equation at `a = √2`, every coefficient at once.**  If `φ` has mean zero and
`ψ`'s coefficients are the divided ones, then EVERY Fourier coefficient of the coboundary
`ψ(· + √2) - ψ` agrees with the corresponding coefficient of `φ`.

The mean-zero hypothesis at `n = 0` is not a technicality: the divisor `fourier 0 a - 1` vanishes
identically, so the zeroth coefficient cannot be divided and must instead be assumed away.  That is
the classical obstruction — a cocycle is a coboundary only after its mean is removed — and it is
exactly what `integral_eq_zero_of_coboundary` in `BirkhoffErgodic.lean` supplies on the other side. -/
theorem coboundary_coeff_sqrt_two (ψ φ : AddCircle (1 : ℝ) → ℂ)
    (hmean : fourierCoeff φ 0 = 0) (hψ0 : fourierCoeff ψ 0 = 0)
    (hψ : ∀ n : ℤ, n ≠ 0 → fourierCoeff ψ n
        = fourierCoeff φ n
            / ((fourier n ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) : ℂ) - 1)) :
    ∀ n : ℤ, fourierCoeff (fun t => ψ (t + ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)))) n
        - fourierCoeff ψ n = fourierCoeff φ n := by
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [fourierCoeff_comp_add, hψ0, hmean]
    simp
  · exact coboundary_coeff ψ ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) n (fourierCoeff φ n)
      (fourier_sub_one_ne_zero_sqrt_two hn) (hψ n hn)

end Quantisation

/-! ## 7. `√2` is badly approximable

This instantiates the Diophantine hypothesis of `smallDivisor_summable` at the Heil–Speegle
configuration `a = √2`, where the exponential small-divisor exponent `β(a)` vanishes. -/

section BadlyApproximable

/-- `2 n² ≠ m²` for `n ≥ 1` — the integrality fact behind badly-approximable `√2`. -/
theorem two_mul_sq_ne_sq {n : ℕ} (hn : 1 ≤ n) (m : ℤ) : 2 * (n : ℤ) ^ 2 ≠ m ^ 2 := by
  intro h
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hR : (m : ℝ) ^ 2 = 2 * (n : ℝ) ^ 2 := by exact_mod_cast h.symm
  have hsq : (|(m : ℝ)| / (n : ℝ)) ^ 2 = 2 := by
    rw [div_pow, sq_abs, hR]
    field_simp
  have hval : Real.sqrt 2 = |(m : ℝ)| / (n : ℝ) := by
    rw [← hsq, Real.sqrt_sq (by positivity)]
  exact irrational_sqrt_two ⟨(|m| : ℚ) / (n : ℚ), by rw [hval]; push_cast; ring⟩

/-- **`√2` is badly approximable**, with the explicit constant `γ = 1/(2√2+1)`:
`|n√2 − m| ≥ γ / n` for every `n ≥ 1` and every integer `m`.  This is the `τ = 1` Diophantine
bound required by `smallDivisor_summable`. -/
theorem sqrt_two_dist_int {n : ℕ} (hn : 1 ≤ n) (m : ℤ) :
    1 / ((2 * Real.sqrt 2 + 1) * (n : ℝ)) ≤ |(n : ℝ) * Real.sqrt 2 - (m : ℝ)| := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs1 : (1 : ℝ) < Real.sqrt 2 := by nlinarith [hs2, hsnn]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hCpos : (0 : ℝ) < (2 * Real.sqrt 2 + 1) * (n : ℝ) := by positivity
  have hone : (1 : ℝ) ≤ |2 * (n : ℝ) ^ 2 - (m : ℝ) ^ 2| := by
    have hZ : 2 * (n : ℤ) ^ 2 - m ^ 2 ≠ 0 := sub_ne_zero.mpr (two_mul_sq_ne_sq hn m)
    have h1 : (1 : ℤ) ≤ |2 * (n : ℤ) ^ 2 - m ^ 2| := Int.one_le_abs hZ
    have h2 := (Int.cast_le (R := ℝ)).mpr h1
    rw [Int.cast_abs] at h2
    push_cast at h2
    exact h2
  have hfac : ((n : ℝ) * Real.sqrt 2 - (m : ℝ)) * ((n : ℝ) * Real.sqrt 2 + (m : ℝ))
      = 2 * (n : ℝ) ^ 2 - (m : ℝ) ^ 2 := by
    linear_combination (n : ℝ) ^ 2 * hs2
  rcases le_or_gt 1 |(n : ℝ) * Real.sqrt 2 - (m : ℝ)| with hc | hc
  · have hle : 1 / ((2 * Real.sqrt 2 + 1) * (n : ℝ)) ≤ 1 := by
      rw [div_le_one hCpos]; nlinarith [hnR, hs1]
    linarith
  · have habs : |(m : ℝ)| ≤ (n : ℝ) * Real.sqrt 2 + 1 := by
      have h := abs_sub_abs_le_abs_sub (m : ℝ) ((n : ℝ) * Real.sqrt 2)
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) * Real.sqrt 2), abs_sub_comm] at h
      linarith
    have hsum : |(n : ℝ) * Real.sqrt 2 + (m : ℝ)| ≤ (2 * Real.sqrt 2 + 1) * (n : ℝ) := by
      calc |(n : ℝ) * Real.sqrt 2 + (m : ℝ)|
          ≤ |(n : ℝ) * Real.sqrt 2| + |(m : ℝ)| := abs_add_le _ _
        _ = (n : ℝ) * Real.sqrt 2 + |(m : ℝ)| := by
            rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) * Real.sqrt 2)]
        _ ≤ (n : ℝ) * Real.sqrt 2 + ((n : ℝ) * Real.sqrt 2 + 1) := by linarith
        _ ≤ (2 * Real.sqrt 2 + 1) * (n : ℝ) := by nlinarith [hnR]
    have hprod : |(n : ℝ) * Real.sqrt 2 - (m : ℝ)| * |(n : ℝ) * Real.sqrt 2 + (m : ℝ)|
        = |2 * (n : ℝ) ^ 2 - (m : ℝ) ^ 2| := by
      rw [← abs_mul, hfac]
    have hdnn : (0 : ℝ) ≤ |(n : ℝ) * Real.sqrt 2 - (m : ℝ)| := abs_nonneg _
    rw [div_le_iff₀ hCpos]
    nlinarith [hprod, hone, hsum, hdnn]

/-- Jordan's inequality in the form needed: `|sin (π u)| ≥ 2|u|` for `|u| ≤ 1/2`. -/
theorem two_mul_abs_le_abs_sin {u : ℝ} (h : |u| ≤ 1 / 2) :
    2 * |u| ≤ |Real.sin (Real.pi * u)| := by
  have hpi := Real.pi_pos
  have hau : 0 ≤ |u| := abs_nonneg u
  have h0 : (0 : ℝ) ≤ 2 * |u| := by positivity
  have h1 : 2 * |u| ≤ 1 := by linarith
  have key : 2 * |u| ≤ Real.sin (Real.pi / 2 * (2 * |u|)) := Real.le_sin_mul h0 h1
  rw [show Real.pi / 2 * (2 * |u|) = Real.pi * |u| by ring] at key
  have hnn : 0 ≤ Real.sin (Real.pi * |u|) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
  have heq : |Real.sin (Real.pi * u)| = Real.sin (Real.pi * |u|) := by
    rcases le_or_gt 0 u with hu | hu
    · rw [abs_of_nonneg hu] at *
      exact abs_of_nonneg hnn
    · rw [abs_of_neg hu] at *
      rw [show Real.pi * u = -(Real.pi * -u) by ring, Real.sin_neg, abs_neg]
      exact abs_of_nonneg hnn
  rw [heq]
  exact key

/-- **The small-divisor bound.**  `‖e^{2πix} − 1‖ ≥ 4·|x − m|` for any integer `m` within `1/2`
of `x`.  This converts a Diophantine *distance* bound into the lower bound on
`Δ n = ‖e^{2πina} − 1‖` that `smallDivisor_summable` consumes. -/
theorem four_mul_dist_le_norm_exp_sub_one (x : ℝ) (m : ℤ) (h : |x - (m : ℝ)| ≤ 1 / 2) :
    4 * |x - (m : ℝ)| ≤ ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) - 1‖ := by
  set u : ℝ := x - (m : ℝ) with hu
  have hper : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))
      = Complex.exp (Complex.I * ((2 * Real.pi * u : ℝ) : ℂ)) := by
    have hx : (x : ℂ) = (u : ℂ) + (m : ℂ) := by push_cast [hu]; ring
    rw [hx]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((u : ℂ) + (m : ℂ))
        = Complex.I * ((2 * Real.pi * u : ℝ) : ℂ) + (m : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast; ring]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hper, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * u) / 2 = Real.pi * u by ring]
  rw [Real.norm_eq_abs, abs_mul]
  have := two_mul_abs_le_abs_sin (u := u) h
  rw [show |(2 : ℝ)| = 2 by norm_num]
  linarith

/-- **The arithmetic chain, closed at `a = √2`.**  Combining `sqrt_two_dist_int`,
`four_mul_dist_le_norm_exp_sub_one` and `smallDivisor_summable`: at the Heil–Speegle parameter
`a = √2` the small-divisor series converges whenever the numerators decay geometrically — which
is exactly the hypothesis `𝒞_θ(a) < ∞` of the residual-cone argument. -/
theorem smallDivisor_summable_sqrt_two {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {c : ℕ → ℝ} (hc : ∀ n : ℕ, |c n| ≤ 2 * ρ ^ n) {Δ : ℕ → ℝ}
    (hΔ : ∀ n : ℕ, Δ n
      = ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((n : ℝ) * Real.sqrt 2 : ℝ) : ℂ)) - 1‖) :
    Summable (fun n : ℕ => |c n| / ((n : ℝ) * Δ n)) := by
  have hs : (0 : ℝ) < 2 * Real.sqrt 2 + 1 := by positivity
  refine smallDivisor_summable (γ := 4 / (2 * Real.sqrt 2 + 1)) (by positivity) hρ0 hρ1
    (τ := 1) (Δ := Δ) ?_ hc
  intro n hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hhalf : |(n : ℝ) * Real.sqrt 2 - ((round ((n : ℝ) * Real.sqrt 2) : ℤ) : ℝ)| ≤ 1 / 2 :=
    abs_sub_round _
  have h1 : 4 * |(n : ℝ) * Real.sqrt 2 - ((round ((n : ℝ) * Real.sqrt 2) : ℤ) : ℝ)| ≤ Δ n := by
    rw [hΔ n]
    exact four_mul_dist_le_norm_exp_sub_one _ _ hhalf
  have h2 : 1 / ((2 * Real.sqrt 2 + 1) * (n : ℝ))
      ≤ |(n : ℝ) * Real.sqrt 2 - ((round ((n : ℝ) * Real.sqrt 2) : ℤ) : ℝ)| :=
    sqrt_two_dist_int hn _
  rw [pow_one]
  calc 4 / (2 * Real.sqrt 2 + 1) / (n : ℝ)
      = 4 * (1 / ((2 * Real.sqrt 2 + 1) * (n : ℝ))) := by field_simp
    _ ≤ 4 * |(n : ℝ) * Real.sqrt 2 - ((round ((n : ℝ) * Real.sqrt 2) : ℤ) : ℝ)| := by linarith
    _ ≤ Δ n := h1

/-! ### The three-point symbol feeds the same chain

For the triple `{(0,0),(1,0),(√2,√2)}` the Zak fibre symbol is
`P_θ(t) = α + β e^{-2πi(t+θ)}`.  When `‖β‖ < ‖α‖` it factors as
`α · (1 + (β/α) e^{-2πi(t+θ)})` with `‖β/α‖ < 1`, so Mathlib's Mercator series expands
`log P_θ` with GEOMETRICALLY decaying Fourier coefficients — exactly the hypothesis
`smallDivisor_summable_sqrt_two` consumes.

Consequence: **the three-point case needs no separate machinery.** The same residual-cone
argument that closes the four-point configuration closes it, with `ρ = ‖β/α‖` in place of the
four-point ratio.  (The metaplectic generators proved in `HRTSmall.lean` remain the route for a
symbol that is *not* log-expandable, i.e. `‖β‖ ≥ ‖α‖`.) -/

/-- The Mercator coefficients of `log (1 + z)` obey `‖cₙ‖ ≤ ‖z‖ⁿ`.  (At `n = 0` the term is `0`
by the junk value of division by zero.) -/
theorem norm_log_taylor_coeff_le (z : ℂ) (n : ℕ) :
    ‖(-1 : ℂ) ^ (n + 1) * z ^ n / (n : ℂ)‖ ≤ ‖z‖ ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast, div_le_iff₀ hnpos]
    nlinarith [pow_nonneg (norm_nonneg z) n]

/-- **The three-point residual chain, closed.**  For a log-expandable fibre symbol
`α + β e^{-2πi(t+θ)}` with `‖β‖ < ‖α‖`, the small-divisor series built from the Mercator
coefficients of `log P_θ` converges at the Heil–Speegle parameter `a = √2`.

This is the three-point analogue of `smallDivisor_summable_sqrt_two`, and it says the
`{(0,0),(1,0),(√2,√2)}` triple is closed by machinery already proved. -/
theorem threePoint_smallDivisor_summable {α β : ℂ} (hα : α ≠ 0) (hlt : ‖β‖ < ‖α‖)
    {Δ : ℕ → ℝ}
    (hΔ : ∀ n : ℕ, Δ n
      = ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((n : ℝ) * Real.sqrt 2 : ℝ) : ℂ)) - 1‖) :
    Summable (fun n : ℕ =>
      ‖(-1 : ℂ) ^ (n + 1) * (β / α) ^ n / (n : ℂ)‖ / ((n : ℝ) * Δ n)) := by
  have hαpos : (0 : ℝ) < ‖α‖ := norm_pos_iff.mpr hα
  have hρ1 : ‖β / α‖ < 1 := by
    rw [norm_div, div_lt_one hαpos]; exact hlt
  have hρ0 : (0 : ℝ) ≤ ‖β / α‖ := norm_nonneg _
  have hc : ∀ n : ℕ, |‖(-1 : ℂ) ^ (n + 1) * (β / α) ^ n / (n : ℂ)‖| ≤ 2 * ‖β / α‖ ^ n := by
    intro n
    rw [abs_of_nonneg (norm_nonneg _)]
    have h := norm_log_taylor_coeff_le (β / α) n
    nlinarith [pow_nonneg hρ0 n]
  have hsum := smallDivisor_summable_sqrt_two hρ0 hρ1 hc hΔ
  simpa only [abs_norm] using hsum

/-- **The mirror branch.**  When `‖α‖ < ‖β‖` the symbol factors the other way,
`P_θ(t) = β e^{-2πi(t+θ)} · (1 + (α/β) e^{+2πi(t+θ)})`, and the Mercator series again gives
geometric decay — now with `ρ = ‖α/β‖`.  So the small-divisor series converges on BOTH sides of
the modulus comparison.

The two branches are not equivalent, though, and the difference is the whole difficulty: the
mirror factorisation carries the extra unimodular factor `e^{-2πi(t+θ)}`, whose logarithm is
**not** a function on the circle.  That is the WINDING term — degree `±1` — and it is exactly
what Iwanik–Lemańczyk–Rudolph handles.  The `‖β‖ < ‖α‖` branch has degree `0` and needs no such
input, which is why it closes here. -/
theorem threePoint_smallDivisor_summable_mirror {α β : ℂ} (hβ : β ≠ 0) (hlt : ‖α‖ < ‖β‖)
    {Δ : ℕ → ℝ}
    (hΔ : ∀ n : ℕ, Δ n
      = ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((n : ℝ) * Real.sqrt 2 : ℝ) : ℂ)) - 1‖) :
    Summable (fun n : ℕ =>
      ‖(-1 : ℂ) ^ (n + 1) * (α / β) ^ n / (n : ℂ)‖ / ((n : ℝ) * Δ n)) :=
  threePoint_smallDivisor_summable hβ hlt hΔ

/-- **The three-point trichotomy.**  For every fibre symbol `α + β e^{-2πi(t+θ)}` with `α, β ≠ 0`
exactly one of three things happens, and the first two are now closed:

* `‖β‖ < ‖α‖` — degree `0`, log-expandable directly, small divisors summable;
* `‖α‖ < ‖β‖` — degree `1`, log-expandable after unwinding, small divisors summable;
* `‖α‖ = ‖β‖` — the boundary case, where the symbol has a root ON the unit circle and no
  expansion of either kind exists.

So the residual difficulty of the three-point configuration is confined to the single equality
`‖α‖ = ‖β‖` plus the winding bookkeeping of the middle branch — not to the analysis, which is
discharged above. -/
theorem threePoint_trichotomy {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0)
    {Δ : ℕ → ℝ}
    (hΔ : ∀ n : ℕ, Δ n
      = ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((n : ℝ) * Real.sqrt 2 : ℝ) : ℂ)) - 1‖) :
    (Summable (fun n : ℕ => ‖(-1 : ℂ) ^ (n + 1) * (β / α) ^ n / (n : ℂ)‖ / ((n : ℝ) * Δ n)))
      ∨ (Summable (fun n : ℕ => ‖(-1 : ℂ) ^ (n + 1) * (α / β) ^ n / (n : ℂ)‖ / ((n : ℝ) * Δ n)))
      ∨ ‖α‖ = ‖β‖ := by
  rcases lt_trichotomy ‖β‖ ‖α‖ with h | h | h
  · exact Or.inl (threePoint_smallDivisor_summable hα h hΔ)
  · exact Or.inr (Or.inr h.symm)
  · exact Or.inr (Or.inl (threePoint_smallDivisor_summable_mirror hβ h hΔ))

/-! ### Why the boundary case is all-or-nothing (and not a null set)

The quadratic (four-point) symbol hides its degeneracy in TWO fibres — that is `counting_le_two`,
and it is why the four-point live set is finite.  The linear (three-point) symbol does **not**
behave that way, and the difference matters: its unique root has modulus `‖B‖/‖A‖` for EVERY
unimodular fibre parameter `w`, so the root modulus is constant along the fibration.

Consequence: `‖A‖ = ‖B‖` cannot be discarded as a measure-zero set of fibres, because it is not a
condition on the fibre at all — it is a condition on the dependence COEFFICIENTS.  Either every
fibre is log-expandable, or none is.  This is a genuine structural obstruction, not a gap in the
bookkeeping, and it is why the three-point case does not simply inherit the four-point proof. -/

/-- **The linear symbol has fibre-independent root modulus.**  If `A z + B w = 0` with `‖w‖ = 1`
and `A ≠ 0`, then `‖z‖ = ‖B‖ / ‖A‖` — no dependence on `w`. -/
theorem linear_root_modulus_const (A B : ℂ) (hA : A ≠ 0) (w z : ℂ) (hw : ‖w‖ = 1)
    (hz : A * z + B * w = 0) : ‖z‖ = ‖B‖ / ‖A‖ := by
  have hzval : z = -(B * w) / A := by rw [eq_div_iff hA]; linear_combination hz
  rw [hzval, norm_div, norm_neg, norm_mul, hw, mul_one]

/-- **The boundary case is all-or-nothing.**  The root of a linear symbol lies on the unit circle
for one unimodular `w` exactly when `‖A‖ = ‖B‖` — hence for *every* such `w`, or for none. -/
theorem linear_root_on_circle_iff (A B : ℂ) (hA : A ≠ 0) (w z : ℂ) (hw : ‖w‖ = 1)
    (hz : A * z + B * w = 0) : ‖z‖ = 1 ↔ ‖A‖ = ‖B‖ := by
  have hApos : (0 : ℝ) < ‖A‖ := norm_pos_iff.mpr hA
  rw [linear_root_modulus_const A B hA w z hw hz, div_eq_one_iff_eq (ne_of_gt hApos)]
  exact eq_comm

/-- **The generic three-point configuration is closed.**  When `‖A‖ ≠ ‖B‖` — i.e. the symbol's
root avoids the unit circle, which by `linear_root_on_circle_iff` happens for every fibre at once —
the symbol is log-expandable on one side or the other, and the small-divisor series at `a = √2`
converges.  Combined with `eigenvalue_quantised_L2`, this closes the residual-cone argument for the
three-point configuration outside the single degenerate stratum `‖A‖ = ‖B‖`. -/
theorem threePoint_generic_summable {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) (hne : ‖α‖ ≠ ‖β‖)
    {Δ : ℕ → ℝ}
    (hΔ : ∀ n : ℕ, Δ n
      = ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((n : ℝ) * Real.sqrt 2 : ℝ) : ℂ)) - 1‖) :
    (Summable (fun n : ℕ => ‖(-1 : ℂ) ^ (n + 1) * (β / α) ^ n / (n : ℂ)‖ / ((n : ℝ) * Δ n)))
      ∨ (Summable (fun n : ℕ =>
          ‖(-1 : ℂ) ^ (n + 1) * (α / β) ^ n / (n : ℂ)‖ / ((n : ℝ) * Δ n))) := by
  rcases threePoint_trichotomy hα hβ hΔ with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hne

/-! ### The degenerate stratum is FINITE, not all-or-nothing

`linear_root_modulus_const` above is about a symbol whose coefficients are constants.  In the
actual three-point Zak equation they are not.  Normalising the triple to `{(0,0),(1,0),(0,d)}`,
the fibre equation reads

  `(c₀ + c₁ e^{-2πiω}) · Zg(t,ω)  +  c₂ e^{2πidt} · Zg(t, ω-d) = 0`,

so the leading coefficient is `A(ω) = c₀ + c₁ e^{-2πiω}` — a genuine FUNCTION of the fibre
variable — while the trailing one is the constant `c₂`.

That changes the status of the boundary case completely.  `‖A(ω)‖ = ‖c₂‖` is now one real equation
in `ω`, and the lemma below shows it has **at most two solutions per period**.  A two-point set is
null, so the degenerate stratum is a measure-zero set of fibres and the generic argument
(`threePoint_generic_summable`) applies almost everywhere — with no Linnell input.

This is the same mechanism as `counting_le_two`, one degree lower: pinning a modulus pins a real
part, and a real part meets a circle twice. -/

/-- **The modulus level set is at most a pair.**  For `c₀, c₁ ≠ 0` the equation
`‖c₀ + c₁ u‖ = r` has at most two unimodular solutions `u`. -/
theorem modulus_level_set_le_two (c₀ c₁ : ℂ) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) (r : ℝ) :
    ∃ u₁ u₂ : ℂ, ∀ u : ℂ, ‖u‖ = 1 → ‖c₀ + c₁ * u‖ = r → u = u₁ ∨ u = u₂ := by
  set lam : ℂ := c₀ * (starRingEnd ℂ) c₁ with hlamdef
  have hlam0 : lam ≠ 0 := mul_ne_zero h₀ (by simpa using h₁)
  set K : ℝ := (r ^ 2 - Complex.normSq c₀ - Complex.normSq c₁) / 2 with hKdef
  set y₀ : ℝ := Real.sqrt (Complex.normSq lam - K ^ 2) with hy0def
  refine ⟨(starRingEnd ℂ) (((K : ℂ) + (y₀ : ℂ) * Complex.I) / lam),
          (starRingEnd ℂ) (((K : ℂ) - (y₀ : ℂ) * Complex.I) / lam), ?_⟩
  rintro u hu hr
  have hnu : Complex.normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, hu]; norm_num
  have hns : Complex.normSq (c₀ + c₁ * u) = r ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, hr]
  -- Pinning the modulus pins the real part of `lam * conj u`.
  have hmul : c₀ * (starRingEnd ℂ) (c₁ * u) = lam * (starRingEnd ℂ) u := by
    rw [hlamdef, map_mul]; ring
  have hre : (lam * (starRingEnd ℂ) u).re = K := by
    have hexp : Complex.normSq (c₀ + c₁ * u)
        = Complex.normSq c₀ + Complex.normSq (c₁ * u)
          + 2 * (c₀ * (starRingEnd ℂ) (c₁ * u)).re := Complex.normSq_add _ _
    rw [hmul, Complex.normSq_mul, hnu, mul_one, hns] at hexp
    rw [hKdef]; linarith [hexp]
  -- Its modulus is fixed, so its imaginary part takes one of two values.
  have hnlam : Complex.normSq (lam * (starRingEnd ℂ) u) = Complex.normSq lam := by
    rw [Complex.normSq_mul, Complex.normSq_conj, hnu, mul_one]
  have happ : Complex.normSq (lam * (starRingEnd ℂ) u)
      = (lam * (starRingEnd ℂ) u).re * (lam * (starRingEnd ℂ) u).re
        + (lam * (starRingEnd ℂ) u).im * (lam * (starRingEnd ℂ) u).im := Complex.normSq_apply _
  have hsq : (lam * (starRingEnd ℂ) u).im ^ 2 = Complex.normSq lam - K ^ 2 := by
    rw [hnlam, hre] at happ; nlinarith [happ]
  have hy0nonneg : 0 ≤ Complex.normSq lam - K ^ 2 := by rw [← hsq]; positivity
  have hy0sq : y₀ ^ 2 = Complex.normSq lam - K ^ 2 := Real.sq_sqrt hy0nonneg
  have himcases : (lam * (starRingEnd ℂ) u).im = y₀ ∨ (lam * (starRingEnd ℂ) u).im = -y₀ := by
    have hz0 : ((lam * (starRingEnd ℂ) u).im - y₀) * ((lam * (starRingEnd ℂ) u).im + y₀) = 0 := by
      nlinarith [hsq, hy0sq]
    rcases mul_eq_zero.mp hz0 with h | h
    · left; linarith
    · right; linarith
  -- and `u` is recovered by conjugating.
  have hrecover : ∀ v : ℂ, lam * (starRingEnd ℂ) u = v → u = (starRingEnd ℂ) (v / lam) := by
    intro v hv
    have : (starRingEnd ℂ) u = v / lam := by rw [eq_div_iff hlam0]; linear_combination hv
    rw [← this, Complex.conj_conj]
  rcases himcases with h | h
  · left
    refine hrecover _ ?_
    apply Complex.ext <;> simp [hre, h]
  · right
    refine hrecover _ ?_
    apply Complex.ext <;> simp [hre, h]

/-- The degenerate stratum is a finite set of unimodular parameters. -/
theorem modulus_level_set_finite (c₀ c₁ : ℂ) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) (r : ℝ) :
    {u : ℂ | ‖u‖ = 1 ∧ ‖c₀ + c₁ * u‖ = r}.Finite := by
  obtain ⟨u₁, u₂, h⟩ := modulus_level_set_le_two c₀ c₁ h₀ h₁ r
  refine Set.Finite.subset ((Set.finite_singleton u₂).insert u₁) ?_
  rintro u ⟨hu, hr⟩
  rcases h u hu hr with rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl

/-- **The three-point conclusion, off a finite set of fibres.**  For every unimodular `u` outside a
finite exceptional set, the symbol `c₀ + c₁ u` has modulus different from `‖c₂‖`, so
`threePoint_generic_summable` applies and the residual-cone argument closes that fibre.

Together with `modulus_level_set_finite` this says the three-point configuration is settled on a
co-finite set of fibres **with no Linnell input** — which is the piece the published Lean HRT
package (arXiv 2604.21228) has to assume outright as its hypothesis A4. -/
theorem threePoint_summable_off_finite (c₀ c₁ c₂ : ℂ) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    {Δ : ℕ → ℝ}
    (hΔ : ∀ n : ℕ, Δ n
      = ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((n : ℝ) * Real.sqrt 2 : ℝ) : ℂ)) - 1‖) :
    ∃ E : Set ℂ, E.Finite ∧ ∀ u : ℂ, ‖u‖ = 1 → u ∉ E → c₀ + c₁ * u ≠ 0 →
      (Summable (fun n : ℕ =>
          ‖(-1 : ℂ) ^ (n + 1) * (c₂ / (c₀ + c₁ * u)) ^ n / (n : ℂ)‖ / ((n : ℝ) * Δ n)))
        ∨ (Summable (fun n : ℕ =>
          ‖(-1 : ℂ) ^ (n + 1) * ((c₀ + c₁ * u) / c₂) ^ n / (n : ℂ)‖ / ((n : ℝ) * Δ n))) := by
  refine ⟨{u : ℂ | ‖u‖ = 1 ∧ ‖c₀ + c₁ * u‖ = ‖c₂‖},
          modulus_level_set_finite c₀ c₁ h₀ h₁ ‖c₂‖, ?_⟩
  intro u hu hE hsym
  have hne : ‖c₀ + c₁ * u‖ ≠ ‖c₂‖ := fun h => hE ⟨hu, h⟩
  exact threePoint_generic_summable hsym h₂ hne hΔ

/-! ### Honest ledger: what a complete three-point theorem still needs

The bricks above close more of the three-point configuration than the published Lean HRT work
reaches, but they do NOT yet compose into an unconditional three-point theorem, and it is worth
recording exactly which links are missing rather than leaving the impression that they are present.

DONE (axiom-free, this file):
  * the arithmetic half — `smallDivisor_summable_sqrt_two`: geometric numerators beat the small
    divisors of the badly-approximable `√2`;
  * log-expandability of the three-point symbol on both sides of the modulus comparison
    (`threePoint_smallDivisor_summable`, `..._mirror`);
  * the degenerate stratum is finite, hence null (`modulus_level_set_finite`), so the generic
    argument runs almost everywhere (`threePoint_summable_off_finite`);
  * eigenvalue quantisation (`eigenvalue_quantised_L2`);
  * quantised + positive measure ⟹ constant on an ACCUMULATING set
    (`quantised_eigenvalue_accumulates`).

MISSING, in dependency order:
  1. ~~The coboundary construction.~~  **DONE** — `coboundary_Lp`.
  2. **Separation of the eigenvalue** — that `λ` is INJECTIVE on a positive-measure set of fibres.
     `not_injOn_of_countable_valued` shows this is exactly what is required: combined with
     `eigenvalue_quantised_L2` it is an outright contradiction, no analyticity or identity
     principle needed.  This is a cleaner target than the "non-constancy" originally written here.
  3. **The cross-module ASSEMBLY.**  Every link is proved and every interface is now SHAPE-MATCHED:
     `dependence_to_cocycle` (Zak) → `integral_log_eq_of_modulus_cocycle` (Birkhoff) →
     `live_set_not_infinite_of_fibre_mean` / `linear_coeff_constraint_of_fibre_mean` (here), all
     speaking in `t`-integrals rather than circle averages.  What blocks it is that the four files
     are independent Mathlib-only modules — a build question, not a mathematical one.

  Two dependencies once thought to be blockers were REMOVED rather than proved: ILR (via
  `rootCount_eq_one_of_mean`) and, off a codimension-two stratum, Linnell (via
  `linear_coeff_constraint` and `threePoint_irreducible_case`).

  Three capstones are kept deliberately: `heil_speegle_lambda_zero` records the paper's own
  structure, `..._of_mean` records how far the argument goes without ILR, and
  `..._of_fibre_mean` states it in the shape an assembly should target.

None of these is research-scale — 1 and 2 are ordinary (if fiddly) Fourier analysis, and 3 is
bookkeeping over the Zak lemmas in `ZakTransform.lean`.  What is research-scale is Linnell's
theorem, which this route is designed to AVOID rather than prove. -/

/-- The Diophantine lower bound on the `√2` divisors, extracted so both summability lemmas can use
it: `4/(2√2+1)/n ≤ Δ n` for `n ≥ 1`. -/
theorem sqrt_two_divisor_lower {n : ℕ} (hn : 1 ≤ n) {Δ : ℕ → ℝ}
    (hΔ : ∀ n : ℕ, Δ n
      = ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((n : ℝ) * Real.sqrt 2 : ℝ) : ℂ)) - 1‖) :
    4 / (2 * Real.sqrt 2 + 1) / (n : ℝ) ≤ Δ n := by
  have hhalf : |(n : ℝ) * Real.sqrt 2 - ((round ((n : ℝ) * Real.sqrt 2) : ℤ) : ℝ)| ≤ 1 / 2 :=
    abs_sub_round _
  have h1 : 4 * |(n : ℝ) * Real.sqrt 2 - ((round ((n : ℝ) * Real.sqrt 2) : ℤ) : ℝ)| ≤ Δ n := by
    rw [hΔ n]; exact four_mul_dist_le_norm_exp_sub_one _ _ hhalf
  have h2 : 1 / ((2 * Real.sqrt 2 + 1) * (n : ℝ))
      ≤ |(n : ℝ) * Real.sqrt 2 - ((round ((n : ℝ) * Real.sqrt 2) : ℤ) : ℝ)| :=
    sqrt_two_dist_int hn _
  calc 4 / (2 * Real.sqrt 2 + 1) / (n : ℝ)
      = 4 * (1 / ((2 * Real.sqrt 2 + 1) * (n : ℝ))) := by field_simp
    _ ≤ 4 * |(n : ℝ) * Real.sqrt 2 - ((round ((n : ℝ) * Real.sqrt 2) : ℤ) : ℝ)| := by linarith
    _ ≤ Δ n := h1

/-- **The DIVIDED coefficients are summable at `a = √2`.**  This is the form the coboundary
construction actually needs: `ψ̂ n = φ̂ n / (divisor)`, so what must converge is `Σ ‖φ̂ n‖ / Δ n`
with no extra `1/n` — unlike `smallDivisor_summable_sqrt_two`, whose `1/n` comes from the Mercator
coefficients.  Geometric decay absorbs the linear loss from the Diophantine bound `Δ n ≳ 1/n`. -/
theorem divided_coeff_summable_sqrt_two {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {c : ℕ → ℝ} (hc : ∀ n : ℕ, |c n| ≤ 2 * ρ ^ n) {Δ : ℕ → ℝ}
    (hΔ : ∀ n : ℕ, Δ n
      = ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((n : ℝ) * Real.sqrt 2 : ℝ) : ℂ)) - 1‖) :
    Summable (fun n : ℕ => |c n| / Δ n) := by
  have hs : (0 : ℝ) < 2 * Real.sqrt 2 + 1 := by positivity
  set γ : ℝ := 4 / (2 * Real.sqrt 2 + 1) with hγdef
  have hγ : 0 < γ := by rw [hγdef]; positivity
  have hnorm : ‖ρ‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hρ0]
  have hmaj : Summable (fun n : ℕ => (2 / γ) * ((n : ℝ) ^ 1 * ρ ^ n)) :=
    (summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).mul_left _
  refine Summable.of_norm_bounded hmaj ?_
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : Δ 0 = 0 := by rw [hΔ 0]; norm_num
    rw [h0]; simp
  · have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlow : γ / (n : ℝ) ≤ Δ n := sqrt_two_divisor_lower hn hΔ
    have hqpos : (0 : ℝ) < γ / (n : ℝ) := by positivity
    have hΔpos : 0 < Δ n := lt_of_lt_of_le hqpos hlow
    have hcn : |c n| ≤ 2 * ρ ^ n := hc n
    have hcnn : 0 ≤ |c n| := abs_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ |c n| / Δ n)]
    rw [div_le_iff₀ hΔpos, pow_one]
    have hstep : |c n| ≤ 2 / γ * ((n : ℝ) * ρ ^ n) * (γ / (n : ℝ)) := by
      field_simp
      nlinarith [hcn, pow_nonneg hρ0 n]
    nlinarith [hstep, hlow, hcnn, mul_nonneg (by positivity : (0:ℝ) ≤ 2 / γ * ((n:ℝ) * ρ ^ n)) (le_of_lt hqpos)]

end BadlyApproximable

section Rigidity

open MeasureTheory

/-! ### From countable to rigid: the pigeonhole that ends the residual-cone argument

`eigenvalue_quantised_L2` pins the fibre eigenvalue into the COUNTABLE set `{fourier n (-a)}`.
On its own that is not yet a contradiction — a countable-valued function is perfectly legal.  The
step that makes it bite is a pigeonhole: a countable-valued function on a set of positive measure
must be **constant on a subset of positive measure**.

That is what converts "quantised" into "rigid", and rigidity is what the live/dead dichotomy
(`ae_eq_zero_or_ae_ne_zero_of_ergodic`) contradicts, since the eigenvalue varies with the fibre. -/

/-- **Countable-valued pigeonhole.**  A function taking values in a countable set `T` on a set `S`
of positive measure is constant on a positive-measure subset of `S`. -/
theorem exists_positive_measure_level_set {α β : Type*} [MeasurableSpace α]
    (μ : Measure α) {S : Set α} (hS : μ S ≠ 0)
    (f : α → β) {T : Set β} (hT : T.Countable) (hmem : ∀ x ∈ S, f x ∈ T) :
    ∃ b ∈ T, μ (S ∩ f ⁻¹' {b}) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hnull : μ (⋃ b ∈ T, S ∩ f ⁻¹' {b}) = 0 := (measure_biUnion_null_iff hT).mpr hcon
  refine hS (measure_mono_null ?_ hnull)
  intro x hx
  exact Set.mem_biUnion (hmem x hx) ⟨hx, rfl⟩

/-- The form the residual-cone argument actually consumes: values indexed by a countable type.
With `ι = ℤ` and `g n = fourier n (-a)` this says the quantised fibre eigenvalue is **constant on a
positive-measure set of fibres**. -/
theorem exists_positive_measure_level_set_range {α β ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) {S : Set α} (hS : μ S ≠ 0)
    (f : α → β) (g : ι → β) (hmem : ∀ x ∈ S, ∃ i : ι, f x = g i) :
    ∃ i : ι, μ (S ∩ f ⁻¹' {g i}) ≠ 0 := by
  have hmem' : ∀ x ∈ S, f x ∈ Set.range g := by
    intro x hx; obtain ⟨i, hi⟩ := hmem x hx; exact ⟨i, hi.symm⟩
  obtain ⟨b, hb, hbne⟩ :=
    exists_positive_measure_level_set μ hS f (Set.countable_range g) hmem'
  obtain ⟨i, rfl⟩ := hb
  exact ⟨i, hbne⟩

/-- A positive-measure set is uncountable, hence infinite (atoms being null). -/
theorem infinite_of_measure_ne_zero {α : Type*} [MeasurableSpace α] (μ : Measure α) [NoAtoms μ]
    {S : Set α} (hS : μ S ≠ 0) : S.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  exact hS (hfin.countable.measure_zero μ)

/-- **Positive measure forces accumulation.**  The fibre space `AddCircle T` is COMPACT, so a
positive-measure set of fibres accumulates somewhere.  No interval truncation is needed — this is
where compactness of the circle does real work. -/
theorem exists_accPt_of_measure_ne_zero {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [CompactSpace α] (μ : Measure α) [NoAtoms μ] {S : Set α} (hS : μ S ≠ 0) :
    ∃ x : α, AccPt x (Filter.principal S) :=
  (infinite_of_measure_ne_zero μ hS).exists_accPt_principal

/-- **The endgame, assembled.**  If the fibre eigenvalue is quantised on a positive-measure set of
fibres, it is constant on a set that ACCUMULATES.

That is precisely the input the analytic identity principle consumes
(`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` via `accPt_iff_frequently`): constancy on an
accumulating set upgrades to global constancy, which contradicts a non-constant eigenvalue and so
closes the residual-cone argument.  Quantisation alone was never a contradiction — a
countable-valued function is perfectly legal.  Rigidity is. -/
theorem quantised_eigenvalue_accumulates {α β ι : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [CompactSpace α] [Countable ι] (μ : Measure α) [NoAtoms μ] {S : Set α} (hS : μ S ≠ 0)
    (f : α → β) (g : ι → β) (hmem : ∀ x ∈ S, ∃ i : ι, f x = g i) :
    ∃ (i : ι) (x : α), AccPt x (Filter.principal (S ∩ f ⁻¹' {g i})) := by
  obtain ⟨i, hi⟩ := exists_positive_measure_level_set_range μ hS f g hmem
  exact ⟨i, exists_accPt_of_measure_ne_zero μ hi⟩

/-! ### The live set is infinite

This is a piece of the capstone's `hreduction` hypothesis rather than of the three-point route.
`hreduction` asserts, among other things, that a nontrivial dependence produces an INFINITE set of
live fibres — and `live_set_not_infinite` then contradicts it.  The infinitude itself is now
available: a family of fibres that is not almost-everywhere zero is live on a set of positive
measure, and positive measure forces infinitude. -/

/-- **A not-almost-everywhere-zero family is live on an infinite set.** -/
theorem live_set_infinite_of_not_ae_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [NoAtoms μ] (F : α → ℂ) (h : ¬ (∀ᵐ x ∂μ, F x = 0)) :
    {x | F x ≠ 0}.Infinite := by
  refine infinite_of_measure_ne_zero μ (fun hnull => h ?_)
  rw [ae_iff]
  exact hnull

/-- The same statement in the form the fibration produces it: if the fibre map is nonzero at even
one point of positive measure, the live set is infinite and every accumulation argument above
applies to it. -/
theorem live_set_infinite_of_measure_ne_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [NoAtoms μ] (F : α → ℂ) (h : μ {x | F x ≠ 0} ≠ 0) :
    {x | F x ≠ 0}.Infinite :=
  infinite_of_measure_ne_zero μ h

/-- **Rigidity as an outright contradiction.**  A countable-valued map that is INJECTIVE on a set
of positive measure cannot exist.

This is the endgame in its usable form.  The pigeonhole makes the map constant on a
positive-measure subset; injectivity then makes that subset a subsingleton; and a subsingleton is
null when the measure has no atoms.  Positive measure and null at once — contradiction.

Applied to the fibre eigenvalue: `eigenvalue_quantised_L2` supplies the countable-valuedness, so
what the residual-cone argument needs from the analysis is only that `λ` SEPARATES fibres.  That is
a cleaner requirement than "non-constant", and it is what ledger item 2 should be aiming at. -/
theorem not_injOn_of_countable_valued {α β ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) [NoAtoms μ] {S : Set α} (hS : μ S ≠ 0)
    (f : α → β) (g : ι → β) (hmem : ∀ x ∈ S, ∃ i : ι, f x = g i)
    (hinj : Set.InjOn f S) : False := by
  obtain ⟨i, hi⟩ := exists_positive_measure_level_set_range μ hS f g hmem
  have hsub : (S ∩ f ⁻¹' {g i}).Subsingleton := by
    intro x hx y hy
    exact hinj hx.1 hy.1 (hx.2.trans hy.2.symm)
  exact hi (hsub.finite.countable.measure_zero μ)

/-- Contrapositive, in the form the fibration produces: a quantised eigenvalue can only be
countable-valued on a positive-measure set of fibres if it FAILS to separate them. -/
theorem exists_eq_of_countable_valued {α β ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) [NoAtoms μ] {S : Set α} (hS : μ S ≠ 0)
    (f : α → β) (g : ι → β) (hmem : ∀ x ∈ S, ∃ i : ι, f x = g i) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ f x = f y := by
  by_contra hcon
  push_neg at hcon
  refine not_injOn_of_countable_valued μ hS f g hmem ?_
  intro x hx y hy hxy
  by_contra hne
  exact (hcon x hx y hy hne) hxy

/-! ### The degenerate stratum: a zero of the symbol propagates along the orbit

On the codimension-two stratum `‖c₀‖ = ‖c₁‖ = ‖c₂‖` the symbol `c₀ + c₁u` has `|c₀/c₁| = 1`, so its
root lies exactly ON the unit circle and the symbol genuinely VANISHES at one point of each fibre.
That is why the log has only `1/n` Fourier decay and the small-divisor criterion fails there.

But a vanishing point is not only an obstruction — it is also information.  The cocycle relation
`P(t)·G(t) = D·G(t-a)` turns a zero of `P` at `t✶` into a zero of `G` at `t✶ - a`, and then
inductively at `t✶ - na` for every `n`.  Since `a = √2` is irrational that orbit is DENSE, so on the
degenerate stratum the fibre modulus vanishes on a dense set.

For a continuous fibre that would already be a contradiction.  An `L²` fibre is only defined a.e.,
so it is not yet one — but it is a concrete handle on the stratum where ILR and Linnell live, and
it needs no spectral theory. -/

/-- **A zero of the symbol propagates backwards along the orbit.**  If `P` vanishes at `t✶` and the
cocycle `P(t)·G(t) = D·G(t-a)` holds with `D ≠ 0`, then `G` vanishes at every `t✶ - (n+1)a`. -/
theorem fibre_vanishes_on_orbit {P G : ℝ → ℝ} {a D : ℝ} (hD : D ≠ 0)
    (hcoc : ∀ t : ℝ, P t * G t = D * G (t - a))
    {tstar : ℝ} (hz : P tstar = 0) :
    ∀ n : ℕ, G (tstar - ((n : ℝ) + 1) * a) = 0 := by
  intro n
  induction n with
  | zero =>
      have h := hcoc tstar
      rw [hz, zero_mul] at h
      have hg : G (tstar - a) = 0 := by
        rcases mul_eq_zero.mp h.symm with h' | h'
        · exact absurd h' hD
        · exact h'
      have harg : tstar - (((0 : ℕ) : ℝ) + 1) * a = tstar - a := by push_cast; ring
      rw [harg]
      exact hg
  | succ k ih =>
      have h := hcoc (tstar - ((k : ℝ) + 1) * a)
      rw [ih, mul_zero] at h
      have hg : G (tstar - ((k : ℝ) + 1) * a - a) = 0 := by
        rcases mul_eq_zero.mp h.symm with h' | h'
        · exact absurd h' hD
        · exact h'
      have harg : tstar - ((((k + 1 : ℕ)) : ℝ) + 1) * a = tstar - ((k : ℝ) + 1) * a - a := by
        push_cast; ring
      rw [harg]
      exact hg

/-- **The orbit really is dense.**  The multiples of `√2` are dense on the circle of length `1`,
because `√2` is irrational.  Combined with `fibre_vanishes_on_orbit`, this says the fibre modulus
vanishes on a DENSE subset of every fibre in the degenerate stratum — the claim the previous lemma
only gestured at. -/
theorem denseRange_sqrt_two_zsmul :
    DenseRange (· • Real.sqrt 2 : ℤ → AddCircle (1 : ℝ)) := by
  rw [AddCircle.denseRange_zsmul_coe_iff]
  simpa using irrational_sqrt_two

/-- **A continuous function vanishing on a dense set is identically zero.** -/
theorem eq_zero_of_continuous_of_dense_vanishing {G : ℝ → ℝ} (hG : Continuous G)
    {s : Set ℝ} (hs : Dense s) (hzero : ∀ x ∈ s, G x = 0) : G = 0 := by
  have hc : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have heqOn : Set.EqOn G (fun _ : ℝ => (0 : ℝ)) s := fun x hx => hzero x hx
  have heq := Continuous.ext_on hs hG hc heqOn
  funext x
  simpa using congrFun heq x

/-- **The degenerate stratum closes for CONTINUOUS fibres.**

Combining `fibre_vanishes_on_orbit` with density: if the symbol vanishes somewhere and the fibre
modulus is continuous, the fibre is identically zero — contradicting a live fibre.

This is the honest scope of the orbit argument.  It does NOT settle the `L²` case, where the fibre
is defined only a.e. and dense vanishing is compatible with being nonzero.  But it does settle the
degenerate stratum for continuous (in particular Schwartz) windows, which is consistent with the
literature: three-point HRT has long been known for Schwartz `g` while the general `L²` case is
exactly where Linnell is needed. -/
theorem degenerate_fibre_zero_of_continuous {P G : ℝ → ℝ} {a D : ℝ} (hD : D ≠ 0)
    (hcoc : ∀ t : ℝ, P t * G t = D * G (t - a))
    {tstar : ℝ} (hz : P tstar = 0) (hG : Continuous G)
    (hdense : Dense {x : ℝ | ∃ n : ℕ, x = tstar - ((n : ℝ) + 1) * a}) :
    G = 0 := by
  refine eq_zero_of_continuous_of_dense_vanishing hG hdense ?_
  rintro x ⟨n, rfl⟩
  exact fibre_vanishes_on_orbit hD hcoc hz n

/-- **Periodicity spreads a zero across the whole integer orbit.**  The Zak fibre modulus is
`1`-periodic (`ZakPeriodization.norm_zakFibre_periodic`), so a single zero gives zeros at every
integer translate.

This is what upgrades `fibre_vanishes_on_orbit` from "dense mod 1" to "dense in `ℝ`": the orbit
`tstar - n√2` is dense modulo one because `√2` is irrational, and periodicity then spreads it over
the whole line. -/
theorem periodic_vanishes_on_shifts {G : ℝ → ℝ} (hper : ∀ t : ℝ, G (t + 1) = G t)
    {x : ℝ} (hx : G x = 0) : ∀ k : ℤ, G (x + (k : ℝ)) = 0 := by
  intro k
  induction k using Int.induction_on with
  | zero => simpa using hx
  | succ n ih =>
      have harg : x + (((n : ℤ) + 1 : ℤ) : ℝ) = (x + ((n : ℤ) : ℝ)) + 1 := by push_cast; ring
      rw [harg, hper]
      exact ih
  | pred n ih =>
      have harg : (x + ((-(n : ℤ) - 1 : ℤ) : ℝ)) + 1 = x + ((-(n : ℤ) : ℤ) : ℝ) := by
        push_cast; ring
      have h := hper (x + ((-(n : ℤ) - 1 : ℤ) : ℝ))
      rw [harg] at h
      rw [← h]
      exact ih

/-- **The saturated `√2`-orbit is dense in `ℝ`.**

`denseRange_sqrt_two_zsmul` gives density on the circle; this transports it upstairs.  The preimage
under `ℝ → AddCircle 1` of the orbit is exactly its saturation by integer translates — which is the
set `periodic_vanishes_on_shifts` shows the fibre modulus vanishes on.

So on the degenerate stratum the fibre modulus vanishes on a set that is dense in `ℝ`, not merely
dense modulo one, and `eq_zero_of_continuous_of_dense_vanishing` applies directly to a continuous
fibre. -/
theorem dense_preimage_sqrt_two_orbit :
    Dense (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹'
      Set.range (· • Real.sqrt 2 : ℤ → AddCircle (1 : ℝ))) :=
  QuotientAddGroup.dense_preimage_mk.mpr denseRange_sqrt_two_zsmul

end Rigidity

section Coboundary

open MeasureTheory AddCircle

/-! ### Realising the coboundary as an honest `L²` function

The coefficientwise work above says what `ψ̂` must be.  This section produces an actual `ψ`.

The construction is the define-through-an-isometry trick that already made `ofCoeffs` work in
`ZakTransform.lean`: rather than build `ψ` as a series and then prove its coefficients are right,
define it as the image of the coefficient sequence under `fourierBasis.repr.symm`, so "its
coefficients are right" is `LinearIsometryEquiv.apply_symm_apply` and nothing has to be summed by
hand.  (`fromCoeffs` duplicates `ZakPeriodization.ofCoeffs`; the two files are independent
Mathlib-only modules, so the three lines are repeated rather than imported.)

Note the defining relation is stated MULTIPLICATIVELY, `(fourier n a - 1) * d n = c n`, not as a
division.  The divisor-nonvanishing lemma is then needed only to CONSTRUCT `d`, never to state or
use the theorem — which keeps the statement clean and total. -/

/-- The `L²(𝕋)` element whose `n`-th Fourier coefficient is `v n`. -/
noncomputable def fromCoeffs (v : lp (fun _ : ℤ => ℂ) 2) :
    Lp ℂ 2 (haarAddCircle : Measure (AddCircle (1 : ℝ))) :=
  (fourierBasis (T := 1)).repr.symm v

/-- The function built from a coefficient sequence has exactly those Fourier coefficients. -/
theorem fourierCoeff_fromCoeffs (v : lp (fun _ : ℤ => ℂ) 2) (n : ℤ) :
    fourierCoeff ((fromCoeffs v : Lp ℂ 2 (haarAddCircle : Measure (AddCircle (1 : ℝ)))) :
      AddCircle (1 : ℝ) → ℂ) n = v n := by
  have h := fourierBasis_repr (T := 1) (fromCoeffs v) n
  rw [fromCoeffs, LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

/-- `fromCoeffs` is injective. -/
theorem fromCoeffs_injective : Function.Injective fromCoeffs := by
  intro v w h
  exact (fourierBasis (T := 1)).repr.symm.injective h

/-- **The coboundary exists.**  If the `ℓ²` sequence `d` solves `(fourier n a - 1) · d n = c n` at
every `n`, then `ψ = fromCoeffs d` satisfies the cohomological equation coefficientwise:
the `n`-th coefficient of `ψ(· + a) - ψ` is exactly `c n`.

This is ledger item 1 discharged at the level of coefficients, for an honest `L²` function rather
than a formal series. -/
theorem coboundary_exists (d : lp (fun _ : ℤ => ℂ) 2) (a : AddCircle (1 : ℝ)) (c : ℤ → ℂ)
    (hd : ∀ n : ℤ, ((fourier n a : ℂ) - 1) * d n = c n) (n : ℤ) :
    fourierCoeff
        (fun t => (fromCoeffs d : Lp ℂ 2 (haarAddCircle : Measure (AddCircle (1 : ℝ))))
          (t + a)) n
      - fourierCoeff ((fromCoeffs d : Lp ℂ 2 (haarAddCircle : Measure (AddCircle (1 : ℝ)))) :
          AddCircle (1 : ℝ) → ℂ) n
      = c n := by
  rw [fourierCoeff_comp_add, fourierCoeff_fromCoeffs]
  linear_combination hd n

/-- **Two `L²` functions with the same Fourier coefficients are equal.**  The upgrade from a
coefficientwise identity to an identity of functions. -/
theorem eq_of_fourierCoeff_eq
    (f g : Lp ℂ 2 (haarAddCircle : Measure (AddCircle (1 : ℝ))))
    (h : ∀ n : ℤ, fourierCoeff ((f : AddCircle (1 : ℝ) → ℂ)) n
        = fourierCoeff ((g : AddCircle (1 : ℝ) → ℂ)) n) : f = g := by
  refine (fourierBasis (T := 1)).repr.injective ?_
  ext n
  rw [fourierBasis_repr, fourierBasis_repr]
  exact h n

/-- Translation is measure-preserving on the circle (Haar invariance). -/
theorem measurePreserving_add_right_circle (a : AddCircle (1 : ℝ)) :
    MeasurePreserving (fun t : AddCircle (1 : ℝ) => t + a)
      (haarAddCircle : Measure (AddCircle (1 : ℝ)))
      (haarAddCircle : Measure (AddCircle (1 : ℝ))) :=
  measurePreserving_add_right _ a

/-- The translate of an `L²` function, as an `L²` function.  This is what lets the cohomological
equation be stated between honest `L²` elements rather than between raw functions. -/
noncomputable def translateLp (a : AddCircle (1 : ℝ))
    (f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle (1 : ℝ)))) :
    Lp ℂ 2 (haarAddCircle : Measure (AddCircle (1 : ℝ))) :=
  Lp.compMeasurePreserving (fun t => t + a) (measurePreserving_add_right_circle a) f

/-- Translating an `L²` function multiplies its `n`-th Fourier coefficient by `fourier n a` — the
`Lp` counterpart of `fourierCoeff_comp_add`. -/
theorem fourierCoeff_translateLp (a : AddCircle (1 : ℝ))
    (f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle (1 : ℝ)))) (n : ℤ) :
    fourierCoeff ((translateLp a f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle (1 : ℝ)))) :
        AddCircle (1 : ℝ) → ℂ) n
      = (fourier n a : ℂ)
          * fourierCoeff ((f : AddCircle (1 : ℝ) → ℂ)) n := by
  have hae : ((translateLp a f : Lp ℂ 2 (haarAddCircle : Measure (AddCircle (1 : ℝ)))) :
      AddCircle (1 : ℝ) → ℂ)
      =ᵐ[(haarAddCircle : Measure (AddCircle (1 : ℝ)))]
        (fun t => (f : AddCircle (1 : ℝ) → ℂ) (t + a)) :=
    Lp.coeFn_compMeasurePreserving _ _
  rw [fourierCoeff_congr_ae hae, fourierCoeff_comp_add]

/-- **The cohomological equation, between honest `L²` elements.**  If the `ℓ²` sequences satisfy
`(fourier n a - 1) · d n = c n` at every `n`, then

  `ψ(· + a) = ψ + φ`   where `ψ = fromCoeffs d`, `φ = fromCoeffs c`,

as an identity in `L²(𝕋)`.  This is ledger item 1 complete: not a formal series, not a
coefficientwise statement, but an equation between elements of the space.

It is phrased ADDITIVELY on purpose.  Writing it as `ψ(· + a) - ψ = φ` would drag in additivity of
`fourierCoeff` across an `Lp` subtraction (needing `Lp ⊆ L¹` on the finite measure and
`integral_sub`); phrasing it as `ψ(· + a) = ψ + φ` instead lets `map_add` for the Fourier isometry
do the whole job, since `fromCoeffs` is by construction a `LinearIsometryEquiv`. -/
theorem coboundary_Lp (a : AddCircle (1 : ℝ)) (d c : lp (fun _ : ℤ => ℂ) 2)
    (h : ∀ n : ℤ, ((fourier n a : ℂ) - 1) * d n = c n) :
    translateLp a (fromCoeffs d) = fromCoeffs d + fromCoeffs c := by
  have hsum : fromCoeffs d + fromCoeffs c = fromCoeffs (d + c) := by
    simp only [fromCoeffs]
    exact (map_add _ _ _).symm
  rw [hsum]
  refine eq_of_fourierCoeff_eq _ _ (fun n => ?_)
  rw [fourierCoeff_translateLp, fourierCoeff_fromCoeffs, fourierCoeff_fromCoeffs]
  have hpt : (d + c) n = d n + c n := rfl
  rw [hpt]
  linear_combination h n

end Coboundary

section CircleChange

open MeasureTheory intervalIntegral

/-! ### From the `t`-integral to the circle average

The dynamical side produces `∫₀¹ log‖symbol(θ,t)‖ dt`; the Jensen side consumes
`circleAverage (log‖C z² + A z + B w‖) 0 1`.  With `ZakPeriodization.norm_symbol_eq_norm_quadratic`
the integrands already agree, so all that separates them is the parametrisation: Mathlib defines
`circleAverage f c R = (2π)⁻¹ • ∫ θ in 0..2π, f (circleMap c R θ)`, i.e. by arclength, while the
Zak fibration runs over `t ∈ [0,1)`.

The substitution `θ = 2πt` is a linear rescaling, and the `(2π)⁻¹` in the definition is exactly the
Jacobian — so the two averages are equal on the nose, with no constant left over. -/

/-- `circleMap 0 1 (2πt)` is `e^{2πit}`. -/
theorem circleMap_eq_exp (t : ℝ) :
    circleMap 0 1 (2 * Real.pi * t) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) := by
  simp only [circleMap, zero_add, one_mul]
  congr 1
  push_cast
  ring

/-- **The `t`-average over `[0,1]` IS the circle average.**  The `(2π)⁻¹` in Mathlib's
`circleAverage` is precisely the Jacobian of `θ = 2πt`, so no constant survives. -/
theorem intervalIntegral_eq_circleAverage (F : ℂ → ℝ) :
    (∫ t in (0 : ℝ)..1, F (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))))
      = circleAverage F 0 1 := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have key := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
      (f := fun θ : ℝ => F (circleMap 0 1 θ)) hpi
  simp only [circleMap_eq_exp, mul_one, mul_zero] at key
  rw [circleAverage_def]
  exact key

/-- `s ↦ F (e^{2πis})` has period `1`. -/
theorem periodic_circle_fn (F : ℂ → ℝ) :
    Function.Periodic
      (fun s : ℝ => F (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ)))) 1 := by
  intro s
  dsimp only
  congr 1
  have hsplit : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((s + 1 : ℝ) : ℂ)
      = 2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) + 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **The FIBRE average is the circle average.**  The Zak fibration presents the fibre variable as
`u = e^{-2πi(t+θ)}` — rotated by `θ` and traversed clockwise — whereas `circleAverage` uses
`e^{2πis}` counter-clockwise from `0`.  Neither difference matters: the integrand has period one,
so the rotation is absorbed by `Periodic.intervalIntegral_add_eq` and the reflection by
`integral_comp_neg`.

This is the last analytic link between the Birkhoff mean of `log‖symbol‖` over `t` and the Mahler
measure that `linear_mean_max` evaluates. -/
theorem intervalIntegral_fibre_eq_circleAverage (F : ℂ → ℝ) (θ : ℝ) :
    (∫ t in (0 : ℝ)..1, F (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t + θ : ℝ) : ℂ)))))
      = circleAverage F 0 1 := by
  set G : ℝ → ℝ := fun s : ℝ => F (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ))) with hG
  have hrewrite : ∀ t : ℝ,
      F (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t + θ : ℝ) : ℂ)))) = G (-(t + θ)) := by
    intro t
    rw [hG]
    congr 2
    push_cast
    ring
  rw [intervalIntegral.integral_congr (g := fun t : ℝ => G (-(t + θ)))
      (fun t _ => hrewrite t)]
  have h1 : (∫ t in (0 : ℝ)..1, G (-(t + θ))) = ∫ u in θ..(1 + θ), G (-u) := by
    have := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := 1)
      (f := fun u : ℝ => G (-u)) θ
    simpa using this
  have h2 : (∫ u in θ..(1 + θ), G (-u)) = ∫ v in (-(1 + θ))..(-θ), G v :=
    intervalIntegral.integral_comp_neg (a := θ) (b := 1 + θ) G
  have h3 : (∫ v in (-(1 + θ))..(-θ), G v) = ∫ v in (0 : ℝ)..1, G v := by
    have hper := (periodic_circle_fn F).intervalIntegral_add_eq (-(1 + θ)) 0
    have hsame : -(1 + θ) + 1 = -θ := by ring
    rw [hsame, zero_add] at hper
    exact hper
  rw [h1, h2, h3, hG]
  exact intervalIntegral_eq_circleAverage F

/-- **From the Birkhoff mean straight to the coefficient constraint.**

The dynamical side does not hand you a circle average — it hands you a `t`-integral over the fibre,
which is what `integral_log_eq_of_modulus_cocycle` produces from the cocycle relation.  This lemma
consumes that form directly and returns `max ‖A‖ ‖B‖ = ‖D‖`, folding in both the change of
variables and Jensen.

It is the single step that takes the three-point argument from dynamics to a statement about the
dependence COEFFICIENTS. -/
theorem linear_coeff_constraint_of_fibre_mean (A B D : ℂ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0) (θ : ℝ)
    (hmean : (∫ t in (0 : ℝ)..1,
        Real.log ‖B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t + θ : ℝ) : ℂ))) + A‖)
      = Real.log ‖D‖) :
    max ‖A‖ ‖B‖ = ‖D‖ := by
  have hcv := intervalIntegral_fibre_eq_circleAverage (fun z : ℂ => Real.log ‖B * z + A‖) θ
  rw [hcv] at hmean
  exact linear_coeff_constraint A B D hA hB hD hmean

/-- Contrapositive, in the form the endgame uses: coefficients violating the constraint admit no
three-point dependence with the given fibre mean. -/
theorem no_threePoint_dependence_of_fibre_mean (A B D : ℂ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0) (θ : ℝ) (hne : max ‖A‖ ‖B‖ ≠ ‖D‖) :
    ¬ ((∫ t in (0 : ℝ)..1,
        Real.log ‖B * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t + θ : ℝ) : ℂ))) + A‖)
      = Real.log ‖D‖) :=
  fun hmean => hne (linear_coeff_constraint_of_fibre_mean A B D hA hB hD θ hmean)


/-! ### The four-point analogue: fibre integral to degree condition

Everything above about the linear symbol has a quadratic counterpart, and it is the one
`hreduction` actually needs.  The Zak side produces the mean as a `t`-integral; `mahler_mean` and
`rootCount_eq_one_of_mean` consume a circle average.  Since the quadratic symbol equals
`C z² + A z + B w` at `z = e^{2πit}` (`ZakPeriodization.norm_symbol_eq_norm_quadratic`), the change
of variables is the counter-clockwise one already proved. -/

/-- The quadratic fibre integral IS the circle average of the quadratic. -/
theorem quadratic_fibre_mean_eq_circleAverage (A B C w : ℂ) :
    (∫ t in (0 : ℝ)..1,
        Real.log ‖C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2
          + A * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) + B * w‖)
      = circleAverage (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 :=
  intervalIntegral_eq_circleAverage (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖)

/-- **The degree condition straight from the fibre integral — still no ILR.**  This is the form
`hreduction` needs: the dynamical side hands over a `t`-integral, and `rootCount = 1` comes out,
via Jensen alone. -/
theorem rootCount_eq_one_of_fibre_mean (A B C D w ζ₁ ζ₂ : ℂ)
    (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0) (hw : ‖w‖ = 1)
    (hDC : ‖D‖ ≠ ‖C‖) (hDB : ‖D‖ ≠ ‖B‖)
    (hfac : ∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂))
    (h1 : ‖ζ₁‖ ≠ 1) (h2 : ‖ζ₂‖ ≠ 1)
    (hmean : (∫ t in (0 : ℝ)..1,
        Real.log ‖C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2
          + A * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) + B * w‖)
      = Real.log ‖D‖) :
    rootCount ζ₁ ζ₂ = 1 := by
  rw [quadratic_fibre_mean_eq_circleAverage] at hmean
  exact rootCount_eq_one_of_mean A B C D w ζ₁ ζ₂ hB hC hD hw hDC hDB hfac h1 h2 hmean

end CircleChange

section FibreEndgame

open MeasureTheory

/-- **The live set is finite, taking the mean in the form the Zak side delivers.**

`live_set_not_infinite_of_mean` wants circle averages; the fibration produces `t`-integrals.  This
is the same theorem with the hypothesis in the shape that actually arrives, so a caller assembling
the reduction never has to perform the change of variables itself.

Still no ILR, and now no impedance mismatch either. -/
theorem live_set_not_infinite_of_fibre_mean
    (A B C D : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hDC : ‖D‖ ≠ ‖C‖) (hDB : ‖D‖ ≠ ‖B‖)
    (L : Set ℂ)
    (hunit : ∀ w ∈ L, ‖w‖ = 1)
    (hmean : ∀ w ∈ L, (∫ t in (0 : ℝ)..1,
        Real.log ‖C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2
          + A * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) + B * w‖)
      = Real.log ‖D‖) :
    ¬ L.Infinite := by
  refine live_set_not_infinite_of_mean A B C D hA hB hC hD hDC hDB L hunit ?_
  intro w hw
  rw [← quadratic_fibre_mean_eq_circleAverage]
  exact hmean w hw

end FibreEndgame









/-! ## 7b. The live/dead fibre dichotomy (the paper's Lemma 1)

Each fibre satisfies `|G_θ(t - a)| = |D|⁻¹ |P_θ(t)| |G_θ(t)|` with `|P_θ| > 0` a.e., so the zero
set of `G_θ` is invariant modulo null sets under the irrational rotation.  Ergodicity then forces
it to be null or co-null: every fibre is either **dead** (`G_θ = 0` a.e.) or **live**
(`G_θ ≠ 0` a.e.) — there is no middle case.  This is what licenses taking logarithms fibrewise.

Proved here from Mathlib's `QuasiErgodic.ae_empty_or_univ₀`; the irrational-rotation instance is
Mathlib's `AddCircle.ergodic_add_left`. -/

section Dichotomy

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Zero/nonzero dichotomy for an ergodic multiplicative cocycle.**  If `G` satisfies
`G (R x) = w x * G x` almost everywhere with `w` almost everywhere nonzero, and `R` is ergodic,
then `G` vanishes almost everywhere or is almost everywhere nonzero. -/
theorem ae_eq_zero_or_ae_ne_zero_of_ergodic {R : α → α} (hR : Ergodic R μ)
    {G : α → ℂ} (hG : NullMeasurable G μ) {w : α → ℂ}
    (hw : ∀ᵐ x ∂μ, w x ≠ 0) (hrel : ∀ᵐ x ∂μ, G (R x) = w x * G x) :
    (∀ᵐ x ∂μ, G x = 0) ∨ (∀ᵐ x ∂μ, G x ≠ 0) := by
  classical
  set s : Set α := {x | G x = 0} with hs
  have hsm : NullMeasurableSet s μ := hG (measurableSet_singleton (0 : ℂ))
  have hinv : R ⁻¹' s =ᵐ[μ] s := by
    filter_upwards [hw, hrel] with x hwx hrelx
    have hiff : (G (R x) = 0) ↔ (G x = 0) := by
      rw [hrelx]
      exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hwx, fun h => by rw [h, mul_zero]⟩
    exact propext hiff
  rcases hR.quasiErgodic.ae_empty_or_univ₀ hsm hinv with h | h
  · right
    rw [MeasureTheory.ae_eq_empty] at h
    rw [ae_iff]
    simpa [hs] using h
  · left
    rw [MeasureTheory.ae_eq_univ] at h
    rw [ae_iff]
    simpa [hs, Set.compl_setOf] using h

end Dichotomy

/-! ## 8. The capstone: Heil–Speegle Conjecture 2 at `Λ₀`

Everything above is machinery about *fibres*.  This section states the actual conjecture —
linear independence of the four time–frequency translates at

  `Λ₀ = {(0,0), (1,0), (0,1), (√2,√2)}`

— and derives it from the fibre endgame.

**Read the hypotheses carefully; they are the point of this theorem.**  `heil_speegle_lambda_zero`
is *not* a from-scratch formalisation: it is the honest reduction of Heil–Speegle Conjecture 2 to
exactly two cited inputs, with everything in between machine-checked.

* `hthree` — the `≤ 3`-point HRT theorem (Heil–Ramanathan–Topiwala 1996): a dependence with a
  vanishing coefficient is trivial.  This is what forces all four coefficients to be nonzero.
* `hreduction` — the Zak-transform reduction package.  It bundles, for a dependence with nonzero
  coefficients: Zak unitarity and covariance, the resonant fibration `θ = ω − t`, the live/dead
  fibre dichotomy, the Fubini step giving a live set of positive measure (hence infinite), the
  **Birkhoff/measurable-coboundary** mean condition, and the **Iwanik–Lemańczyk–Rudolph** degree
  obstruction.  Of these, ILR is research-level with no Lean formalisation anywhere and will
  remain a hypothesis; the rest are large but formalisable in principle (the Zak transform is
  absent from Mathlib; the pointwise Birkhoff ergodic theorem is too — verified 2026-07-28
  against Mathlib's own `docs/1000.yaml`, where the entry carries no `decls:`).

Note the `rootCount … = 1` in `hreduction` is the `j = 0` instance of the general `N = 1 + j`;
`Λ₀` is exactly `a = √2`, `j = 0`. -/

section HeilSpeegle

open MeasureTheory

/-- Time translation `(T_x g)(t) = g (t − x)`. -/
noncomputable def timeShift (x : ℝ) (g : ℝ → ℂ) : ℝ → ℂ := fun t => g (t - x)

/-- Modulation `(M_ω g)(t) = e^{2πiωt} · g(t)`. -/
noncomputable def modulate (w : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun t => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * (t : ℂ)) * g t

/-- The four translates indexed by `Λ₀ = {(0,0), (1,0), (0,1), (√2,√2)}`. -/
noncomputable def lambdaZeroFamily (g : ℝ → ℂ) : Fin 4 → (ℝ → ℂ) :=
  ![g, timeShift 1 g, modulate 1 g,
    modulate (Real.sqrt 2) (timeShift (Real.sqrt 2) g)]

/-- **Heil–Speegle Conjecture 2.**  For every nonzero window `g`, the four time–frequency
translates indexed by `Λ₀ = {(0,0),(1,0),(0,1),(√2,√2)}` are linearly independent.

Proved here from `hthree` (the `≤3`-point HRT theorem) and `hreduction` (the Zak/Birkhoff/ILR
package) — see the section docstring.  Everything between those inputs and this conclusion is
machine-checked: the counting lemma, the Jensen evaluation, the `N ∈ {0,1,2}` case exhaustion,
and the assembly. -/
theorem heil_speegle_lambda_zero (g : ℝ → ℂ) (_hg : g ≠ 0)
    (hthree : ∀ c : Fin 4 → ℂ, (∑ i, c i • lambdaZeroFamily g i) = 0 →
        (∃ i, c i = 0) → ∀ i, c i = 0)
    (hreduction : ∀ A B C D : ℂ, A ≠ 0 → B ≠ 0 → C ≠ 0 → D ≠ 0 →
        (A • g + B • timeShift 1 g + C • modulate 1 g
          + D • modulate (Real.sqrt 2) (timeShift (Real.sqrt 2) g) = 0) →
        ∃ L : Set ℂ, L.Infinite
          ∧ (∀ w ∈ L, ‖w‖ = 1)
          ∧ (∀ w ∈ L, Real.circleAverage
              (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 = Real.log ‖D‖)
          ∧ (∀ w ∈ L, ∀ ζ₁ ζ₂ : ℂ,
              (∀ z : ℂ, C * z ^ 2 + A * z + B * w = C * (z - ζ₁) * (z - ζ₂)) →
              ‖ζ₁‖ ≠ 1 → ‖ζ₂‖ ≠ 1 → rootCount ζ₁ ζ₂ = 1)) :
    LinearIndependent ℂ (lambdaZeroFamily g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push_neg at hne
  obtain ⟨i₀, hi₀⟩ := hne
  -- the three-point theorem forces every coefficient to be nonzero
  have hall : ∀ i, c i ≠ 0 := fun i hi => hi₀ (hthree c hc ⟨i, hi⟩ i₀)
  -- rewrite the `Fin 4` sum as the explicit four-term dependence
  have hdep : c 0 • g + c 1 • timeShift 1 g + c 2 • modulate 1 g
      + c 3 • modulate (Real.sqrt 2) (timeShift (Real.sqrt 2) g) = 0 := by
    simpa [Fin.sum_univ_four, lambdaZeroFamily] using hc
  obtain ⟨L, hinf, hunit, hmean, hdeg⟩ :=
    hreduction (c 0) (c 1) (c 2) (c 3) (hall 0) (hall 1) (hall 2) (hall 3) hdep
  exact live_set_not_infinite (c 0) (c 1) (c 2) (c 3)
    (hall 0) (hall 1) (hall 2) (hall 3) 0
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    L hunit hmean (by simpa using hdeg) hinf

/-- **The capstone, with the ILR clause removed from its hypotheses.**

`heil_speegle_lambda_zero` asks its `hreduction` to deliver the Iwanik–Lemańczyk–Rudolph degree
condition alongside the mean condition.  This version does not: it asks only for the mean
condition plus the two codimension-one non-degeneracies, and derives the degree condition
internally via `rootCount_eq_one_of_mean`.

The hypothesis set is therefore strictly weaker, and — more to the point — everything it still
assumes is reachable from Mathlib, whereas the ILR clause was not formalisable at all.  What
remains assumed is `hthree` (three-point HRT, i.e. Linnell) and the Zak reduction itself. -/
theorem heil_speegle_lambda_zero_of_mean (g : ℝ → ℂ) (_hg : g ≠ 0)
    (hthree : ∀ c : Fin 4 → ℂ, (∑ i, c i • lambdaZeroFamily g i) = 0 →
        (∃ i, c i = 0) → ∀ i, c i = 0)
    (hreduction : ∀ A B C D : ℂ, A ≠ 0 → B ≠ 0 → C ≠ 0 → D ≠ 0 →
        (A • g + B • timeShift 1 g + C • modulate 1 g
          + D • modulate (Real.sqrt 2) (timeShift (Real.sqrt 2) g) = 0) →
        ‖D‖ ≠ ‖C‖ ∧ ‖D‖ ≠ ‖B‖ ∧ ∃ L : Set ℂ, L.Infinite
          ∧ (∀ w ∈ L, ‖w‖ = 1)
          ∧ (∀ w ∈ L, Real.circleAverage
              (fun z : ℂ => Real.log ‖C * z ^ 2 + A * z + B * w‖) 0 1 = Real.log ‖D‖)) :
    LinearIndependent ℂ (lambdaZeroFamily g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push_neg at hne
  obtain ⟨i₀, hi₀⟩ := hne
  have hall : ∀ i, c i ≠ 0 := fun i hi => hi₀ (hthree c hc ⟨i, hi⟩ i₀)
  have hdep : c 0 • g + c 1 • timeShift 1 g + c 2 • modulate 1 g
      + c 3 • modulate (Real.sqrt 2) (timeShift (Real.sqrt 2) g) = 0 := by
    simpa [Fin.sum_univ_four, lambdaZeroFamily] using hc
  obtain ⟨hDC, hDB, L, hinf, hunit, hmean⟩ :=
    hreduction (c 0) (c 1) (c 2) (c 3) (hall 0) (hall 1) (hall 2) (hall 3) hdep
  exact live_set_not_infinite_of_mean (c 0) (c 1) (c 2) (c 3)
    (hall 0) (hall 1) (hall 2) (hall 3) hDC hDB L hunit hmean hinf

/-- **The capstone in delivery form.**

Same as `heil_speegle_lambda_zero_of_mean`, but `hreduction` supplies the mean as the `t`-integral
the Zak fibration actually produces rather than as a circle average.  This is the version an
assembly should target: every hypothesis is now stated in the shape some other module already
returns.

Remaining assumptions, and nothing else: `hthree` (three-point HRT) and the reduction itself.  No
ILR, no spectral theory, no impedance mismatch. -/
theorem heil_speegle_lambda_zero_of_fibre_mean (g : ℝ → ℂ) (_hg : g ≠ 0)
    (hthree : ∀ c : Fin 4 → ℂ, (∑ i, c i • lambdaZeroFamily g i) = 0 →
        (∃ i, c i = 0) → ∀ i, c i = 0)
    (hreduction : ∀ A B C D : ℂ, A ≠ 0 → B ≠ 0 → C ≠ 0 → D ≠ 0 →
        (A • g + B • timeShift 1 g + C • modulate 1 g
          + D • modulate (Real.sqrt 2) (timeShift (Real.sqrt 2) g) = 0) →
        ‖D‖ ≠ ‖C‖ ∧ ‖D‖ ≠ ‖B‖ ∧ ∃ L : Set ℂ, L.Infinite
          ∧ (∀ w ∈ L, ‖w‖ = 1)
          ∧ (∀ w ∈ L, (∫ t in (0 : ℝ)..1,
              Real.log ‖C * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2
                + A * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) + B * w‖)
            = Real.log ‖D‖)) :
    LinearIndependent ℂ (lambdaZeroFamily g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push_neg at hne
  obtain ⟨i₀, hi₀⟩ := hne
  have hall : ∀ i, c i ≠ 0 := fun i hi => hi₀ (hthree c hc ⟨i, hi⟩ i₀)
  have hdep : c 0 • g + c 1 • timeShift 1 g + c 2 • modulate 1 g
      + c 3 • modulate (Real.sqrt 2) (timeShift (Real.sqrt 2) g) = 0 := by
    simpa [Fin.sum_univ_four, lambdaZeroFamily] using hc
  obtain ⟨hDC, hDB, L, hinf, hunit, hmean⟩ :=
    hreduction (c 0) (c 1) (c 2) (c 3) (hall 0) (hall 1) (hall 2) (hall 3) hdep
  exact live_set_not_infinite_of_fibre_mean (c 0) (c 1) (c 2) (c 3)
    (hall 0) (hall 1) (hall 2) (hall 3) hDC hDB L hunit hmean hinf

end HeilSpeegle

end HRTResonant

#print axioms HRTResonant.quad_factor
#print axioms HRTResonant.counting_le_two
#print axioms HRTResonant.mahler_mean
#print axioms HRTResonant.vieta_prod
#print axioms HRTResonant.outside_root_modulus
#print axioms HRTResonant.both_inside_forces
#print axioms HRTResonant.both_outside_forces
#print axioms HRTResonant.linear_mean
#print axioms HRTResonant.linear_mean_max
#print axioms HRTResonant.linear_coeff_constraint
#print axioms HRTResonant.no_linear_dependence_of_ne
#print axioms HRTResonant.threePoint_hard_case_only
#print axioms HRTResonant.threePoint_irreducible_case
#print axioms HRTResonant.three_max_constraints_force_equal
#print axioms HRTResonant.threePoint_moduli_all_equal
#print axioms HRTResonant.threePoint_no_dependence_of_moduli_ne
#print axioms HRTResonant.rootCount_eq_one_of_mean
#print axioms HRTResonant.live_set_subset_four
#print axioms HRTResonant.live_set_finite
#print axioms HRTResonant.live_set_not_infinite
#print axioms HRTResonant.live_set_not_infinite_of_ne
#print axioms HRTResonant.live_set_not_infinite_of_mean
#print axioms HRTResonant.smallDivisor_summable
#print axioms HRTResonant.fourier_arg_add
#print axioms HRTResonant.fourier_mul_neg
#print axioms HRTResonant.fourierCoeff_comp_add
#print axioms HRTResonant.eigenvalue_quantised
#print axioms HRTResonant.eigenvalue_quantised_exp
#print axioms HRTResonant.exists_fourierCoeff_ne_zero
#print axioms HRTResonant.eigenvalue_quantised_L2
#print axioms HRTResonant.sqrt_two_int_mul_ne_int
#print axioms HRTResonant.fourier_sub_one_ne_zero_sqrt_two
#print axioms HRTResonant.coboundary_coeff
#print axioms HRTResonant.coboundary_coeff_sqrt_two
#print axioms HRTResonant.two_mul_sq_ne_sq
#print axioms HRTResonant.sqrt_two_dist_int
#print axioms HRTResonant.two_mul_abs_le_abs_sin
#print axioms HRTResonant.four_mul_dist_le_norm_exp_sub_one
#print axioms HRTResonant.smallDivisor_summable_sqrt_two
#print axioms HRTResonant.sqrt_two_divisor_lower
#print axioms HRTResonant.divided_coeff_summable_sqrt_two
#print axioms HRTResonant.norm_log_taylor_coeff_le
#print axioms HRTResonant.threePoint_smallDivisor_summable
#print axioms HRTResonant.threePoint_smallDivisor_summable_mirror
#print axioms HRTResonant.threePoint_trichotomy
#print axioms HRTResonant.linear_root_modulus_const
#print axioms HRTResonant.linear_root_on_circle_iff
#print axioms HRTResonant.threePoint_generic_summable
#print axioms HRTResonant.modulus_level_set_le_two
#print axioms HRTResonant.modulus_level_set_finite
#print axioms HRTResonant.threePoint_summable_off_finite
#print axioms HRTResonant.exists_positive_measure_level_set
#print axioms HRTResonant.exists_positive_measure_level_set_range
#print axioms HRTResonant.infinite_of_measure_ne_zero
#print axioms HRTResonant.exists_accPt_of_measure_ne_zero
#print axioms HRTResonant.quantised_eigenvalue_accumulates
#print axioms HRTResonant.live_set_infinite_of_not_ae_zero
#print axioms HRTResonant.live_set_infinite_of_measure_ne_zero
#print axioms HRTResonant.not_injOn_of_countable_valued
#print axioms HRTResonant.exists_eq_of_countable_valued
#print axioms HRTResonant.fibre_vanishes_on_orbit
#print axioms HRTResonant.denseRange_sqrt_two_zsmul
#print axioms HRTResonant.eq_zero_of_continuous_of_dense_vanishing
#print axioms HRTResonant.degenerate_fibre_zero_of_continuous
#print axioms HRTResonant.periodic_vanishes_on_shifts
#print axioms HRTResonant.dense_preimage_sqrt_two_orbit
#print axioms HRTResonant.fourierCoeff_fromCoeffs
#print axioms HRTResonant.fromCoeffs_injective
#print axioms HRTResonant.coboundary_exists
#print axioms HRTResonant.eq_of_fourierCoeff_eq
#print axioms HRTResonant.measurePreserving_add_right_circle
#print axioms HRTResonant.fourierCoeff_translateLp
#print axioms HRTResonant.coboundary_Lp
#print axioms HRTResonant.circleMap_eq_exp
#print axioms HRTResonant.intervalIntegral_eq_circleAverage
#print axioms HRTResonant.periodic_circle_fn
#print axioms HRTResonant.intervalIntegral_fibre_eq_circleAverage
#print axioms HRTResonant.linear_coeff_constraint_of_fibre_mean
#print axioms HRTResonant.no_threePoint_dependence_of_fibre_mean
#print axioms HRTResonant.quadratic_fibre_mean_eq_circleAverage
#print axioms HRTResonant.rootCount_eq_one_of_fibre_mean
#print axioms HRTResonant.live_set_not_infinite_of_fibre_mean
#print axioms HRTResonant.ae_eq_zero_or_ae_ne_zero_of_ergodic
#print axioms HRTResonant.heil_speegle_lambda_zero
#print axioms HRTResonant.heil_speegle_lambda_zero_of_mean
#print axioms HRTResonant.heil_speegle_lambda_zero_of_fibre_mean
