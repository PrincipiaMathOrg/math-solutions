/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.Spine

set_option autoImplicit false

/-!
# The circle-method identity for the ternary Λ-count — link 1 of the spine, DISCHARGED

`Spine.lean` reduced the EP1054 chain's last trusted input to a chain of seven links, four of which
were still hypotheses. This file **proves one of them outright**:

  `CircleMethodIdentity : ∀ H, ((lambdaTriple H : ℝ) : ℂ) = ∫_{(0,1]} S(α)³ e(−Hα) dα`

with no hypotheses and footprint `[propext, Classical.choice, Quot.sound]`. The spine's headline
result therefore now takes **three** links instead of four
(`ternaryLogCountLower_of_three`, `cite_Helfgott_weighted_of_three`).

## The proof, in four steps

1. **Expand the cube.** `sum_cube` turns `(∑_{n ∈ s} f n)³` into the triple sum
   `∑_{n₁}∑_{n₂}∑_{n₃} f n₁ f n₂ f n₃`, and `kern_eq_sum_integrand` folds the twist `e(−Hα)` into
   each summand's frequency, giving `kern H α = ∑∑∑ Λ(n₁)Λ(n₂)Λ(n₃) e((n₁+n₂+n₃−H)α)`.
2. **Interchange.** Each summand is continuous, hence interval-integrable, so
   `intervalIntegral.integral_finsetSum` applies three times.
3. **Orthogonality.** `MinorArc.integral_e` gives `∫₀¹ e(kα) dα = [k = 0]` for `k : ℤ`, so only
   the triples with `n₁ + n₂ + n₃ = H` survive (`integral_integrand`). The result is
   `integral_kern_eq_tripleSum`.
4. **Reindex** (`lambdaTriple_eq_tripleSum`). This is the only step with any content, because the
   two index sets **do not match**: the cube runs over `Finset.Ioc 0 H` three times, while
   `lambdaTriple` runs over `Finset.range H` twice with the guard `p + q < H` and the natural
   subtraction `H − p − q`. Neither `Ioc 0 H = {1,…,H}` nor `range H = {0,…,H−1}` contains the
   other, so the reconciliation goes through their common superset `range (H+1)`:

   * collapsing `n₃` is `Finset.sum_eq_single_of_mem` at `n₃ = H − n₁ − n₂` when `n₁ + n₂ < H`,
     and `Finset.sum_eq_zero` otherwise (every `n₃ ≥ 1` overshoots);
   * `Ioc 0 H ↪ range (H+1)` adds only the index `0`, where the summand vanishes because
     **`Λ 0 = 0`**;
   * `range H ↪ range (H+1)` adds only the index `H`, where the summand vanishes because
     **the guard `p + q < H` fails** as soon as one coordinate is `H`.

   Both vanishing mechanisms are needed and they are different: one is arithmetic (`Λ 0 = 0`), one
   is combinatorial (the guard). That is exactly the reconciliation the brief flagged as delicate,
   and it is the reason the identity holds for **every** `H : ℕ`, with no positivity,
   parity or size hypothesis — including the degenerate `H ≤ 2`, where both sides are `0`.

## Numerical corroboration, before any Lean was written

Both sides were computed independently in Python for every `H ≤ 39`:

* `lambdaTriple H` from the `Finset.range H` definition, verbatim;
* the triple sum over `Ioc 0 H` (step 4's target), the double sum over `Ioc 0 H` and the double
  sum over `range (H+1)` — the three intermediate forms, each recomputed separately;
* the integral, two independent ways: an exact `M`-point DFT with `M > 3H` (legitimate because the
  integrand is a trigonometric polynomial with frequencies in `[3−H, 2H]`) **and** a 4001-point
  midpoint Riemann sum.

All five agreed to `10⁻⁹` at every `H`, with the imaginary part of the integral below `5·10⁻¹²`
throughout. `H = 7, 9, 11, 15, 21, 33, 45` and the even `H = 8, 10, 12` were checked explicitly;
`H = 0, 1, 2` return `0` on both sides.

## THE ADVERSARIAL PASS — this file introduces no new `Prop`, and the discharge is not vacuous

There is nothing here to satisfy degenerately: `circleMethodIdentity_holds` *removes* a hypothesis
rather than adding one, and every object in it (`lambdaTriple`, `kern`, `expSum`) was already
concretely defined in `Spine.lean`. The degenerate-witness attack on an identity is instead
**"both sides are identically zero"**, and it is refuted by a theorem rather than by inspection:

* `integral_kern_nine_pos` — `0 < (∫_{(0,1]} kern 9 α).re`, via `Probes.ternaryLogCount_nine_pos`
  (`ternaryLogCount 9 = (log 3)³`) and `Spine.ternaryLogCount_le_lambdaTriple`. So the circle
  integral is provably non-zero at an explicit `H`;
* `integral_kern_two_eq_zero` — `∫_{(0,1]} kern 2 α = 0`, so the identity is *not* satisfied by a
  constant on either side: it separates `H = 2` from `H = 9`;
* `integral_kern_im_eq_zero` — `(∫_{(0,1]} kern H α).im = 0` for every `H`. This is a genuine
  consequence rather than a restatement: `kern H α` is not real at any individual `α`, and nothing
  in the definition of the integral makes its imaginary part vanish. It is the statement Python
  measured as `< 5·10⁻¹²`.

`lambdaTriple_le_circle` then uses the identity to prove the spine's **first unconditional two-sided
estimate**, `lambdaTriple H ≤ (7/5)·H²(log H)²` for `H ≥ 10^27`, by running the already-proved
Hölder/second-moment pair over the whole circle instead of the minor arcs. It is a ceiling, not the
floor the route needs — `MajorArcLower` is untouched — but it certifies that the circle-method
integral is of the right order, and it is a log-factor sharper than the trivial
`H²(log H)³` that counting the `range H × range H` pairs gives.

## What is NOT claimed

Nothing about ternary Goldbach. Three links of `Spine.lean` remain hypotheses
(`MajorArcLower`, `MinorSupBound`, `PrimePowerRemoval`) and the hard mathematics is entirely in the
first two; this file removes the one link the spine itself labelled *REACHABLE*, and the
measurements recorded in `Spine.lean` (the minor-arc shortfall of `13.6×`, the major-arc error
budget) are unaffected.
-/

namespace Principia.Common.TernaryGoldbach.CircleMethod

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction

/-! ## Step 1 — expanding the cube

`sum_cube` is campaign-agnostic: it is the cubic analogue of the `Finset.sum_mul_sum` step inside
`MinorArc.fourier_coeff_sq`, and mentions nothing about Goldbach. -/

/-- **The cube of a finite sum as a triple sum.** Three applications of `Finset.sum_mul_sum` /
`Finset.sum_mul`; no commutativity of the index sets is used, so the three copies of `s` are the
same set only by choice. -/
theorem sum_cube {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i) ^ 3 = ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, f i * f j * f k := by
  calc (∑ i ∈ s, f i) ^ 3
      = ((∑ i ∈ s, f i) * (∑ j ∈ s, f j)) * (∑ k ∈ s, f k) := by ring
    _ = (∑ i ∈ s, ∑ j ∈ s, f i * f j) * (∑ k ∈ s, f k) := by rw [Finset.sum_mul_sum]
    _ = ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, f i * f j * f k := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]

/-- **One term of the expanded integrand**: `Λ(n₁)Λ(n₂)Λ(n₃) · e((n₁+n₂+n₃−H)α)`. The frequency is
an **integer** (it can be negative, as at `n₁ = n₂ = n₃ = 1 < H`), which is why the orthogonality
lemma used below is `MinorArc.integral_e` over `ℤ` rather than `MinorArc.integral_e_nat`. -/
noncomputable def integrand (H n₁ n₂ n₃ : ℕ) (α : ℝ) : ℂ :=
  ((Λ n₁ * Λ n₂ * Λ n₃ : ℝ) : ℂ)
    * e (((((n₁ : ℤ) + (n₂ : ℤ) + (n₃ : ℤ) - (H : ℤ)) : ℤ) : ℝ) * α)

/-- **The integrand, expanded.** `kern H α = S(α)³e(−Hα)` is the triple sum of `integrand`. -/
theorem kern_eq_sum_integrand (H : ℕ) (α : ℝ) :
    Spine.kern H α = ∑ n₁ ∈ Finset.Ioc 0 H, ∑ n₂ ∈ Finset.Ioc 0 H, ∑ n₃ ∈ Finset.Ioc 0 H,
      integrand H n₁ n₂ n₃ α := by
  rw [Spine.kern, Spine.expSum, sum_cube, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n₁ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun n₂ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun n₃ _ => ?_
  have h4 : e ((n₁ : ℝ) * α) * e ((n₂ : ℝ) * α) * e ((n₃ : ℝ) * α) * e (-(H : ℝ) * α)
      = e (((((n₁ : ℤ) + (n₂ : ℤ) + (n₃ : ℤ) - (H : ℤ)) : ℤ) : ℝ) * α) := by
    rw [e_add, e_add, e_add]
    congr 1
    push_cast
    ring
  rw [integrand, ← h4]
  push_cast
  ring

/-! ## Step 2 — integrability, and the interchange -/

/-- Each summand is continuous, hence interval-integrable. -/
theorem integrable_integrand (H n₁ n₂ n₃ : ℕ) :
    IntervalIntegrable (integrand H n₁ n₂ n₃) volume 0 1 := by
  apply Continuous.intervalIntegrable
  unfold integrand Principia.Common.Goldbach.e
  fun_prop

/-- The inner sum over `n₃` is interval-integrable. -/
theorem integrable_sum3 (H n₁ n₂ : ℕ) :
    IntervalIntegrable (fun α : ℝ => ∑ n₃ ∈ Finset.Ioc 0 H, integrand H n₁ n₂ n₃ α)
      volume 0 1 := by
  apply Continuous.intervalIntegrable
  apply continuous_finsetSum
  intro n₃ _
  unfold integrand Principia.Common.Goldbach.e
  fun_prop

/-- The double sum over `(n₂, n₃)` is interval-integrable. -/
theorem integrable_sum23 (H n₁ : ℕ) :
    IntervalIntegrable
      (fun α : ℝ => ∑ n₂ ∈ Finset.Ioc 0 H, ∑ n₃ ∈ Finset.Ioc 0 H, integrand H n₁ n₂ n₃ α)
      volume 0 1 := by
  apply Continuous.intervalIntegrable
  apply continuous_finsetSum
  intro n₂ _
  apply continuous_finsetSum
  intro n₃ _
  unfold integrand Principia.Common.Goldbach.e
  fun_prop

/-! ## Step 3 — orthogonality -/

/-- **Orthogonality, one term at a time.** `∫₀¹ e(kα) dα = [k = 0]` with `k = n₁+n₂+n₃−H` in `ℤ`;
`omega` discharges the translation between `(n₁ : ℤ) + n₂ + n₃ − H = 0` and `n₁ + n₂ + n₃ = H`. -/
theorem integral_integrand (H n₁ n₂ n₃ : ℕ) :
    (∫ α in (0 : ℝ)..1, integrand H n₁ n₂ n₃ α)
      = if n₁ + n₂ + n₃ = H then ((Λ n₁ * Λ n₂ * Λ n₃ : ℝ) : ℂ) else 0 := by
  simp only [integrand]
  rw [intervalIntegral.integral_const_mul, MinorArc.integral_e]
  by_cases h : n₁ + n₂ + n₃ = H
  · rw [if_pos (show ((n₁ : ℤ) + (n₂ : ℤ) + (n₃ : ℤ) - (H : ℤ)) = 0 by omega), if_pos h, mul_one]
  · rw [if_neg (show ¬(((n₁ : ℤ) + (n₂ : ℤ) + (n₃ : ℤ) - (H : ℤ)) = 0) by omega), if_neg h,
      mul_zero]

/-- **The circle integral, evaluated.** Steps 1–3 assembled: the integral of `kern` over the
fundamental domain is the diagonal triple sum. -/
theorem integral_kern_eq_tripleSum (H : ℕ) :
    (∫ α in Set.Ioc (0 : ℝ) 1, Spine.kern H α)
      = ∑ n₁ ∈ Finset.Ioc 0 H, ∑ n₂ ∈ Finset.Ioc 0 H, ∑ n₃ ∈ Finset.Ioc 0 H,
          (if n₁ + n₂ + n₃ = H then ((Λ n₁ * Λ n₂ * Λ n₃ : ℝ) : ℂ) else 0) := by
  rw [← intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  rw [intervalIntegral.integral_congr
    (g := fun α : ℝ => ∑ n₁ ∈ Finset.Ioc 0 H, ∑ n₂ ∈ Finset.Ioc 0 H, ∑ n₃ ∈ Finset.Ioc 0 H,
      integrand H n₁ n₂ n₃ α) (fun α _ => kern_eq_sum_integrand H α)]
  rw [intervalIntegral.integral_finsetSum (fun n₁ _ => integrable_sum23 H n₁)]
  refine Finset.sum_congr rfl fun n₁ _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun n₂ _ => integrable_sum3 H n₁ n₂)]
  refine Finset.sum_congr rfl fun n₂ _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun n₃ _ => integrable_integrand H n₁ n₂ n₃)]
  exact Finset.sum_congr rfl fun n₃ _ => integral_integrand H n₁ n₂ n₃

/-! ## Step 4 — the reindexing

The only step with content. `lambdaTriple` sums over `range H × range H` with a guard; the circle
method delivers a diagonal sum over `(Ioc 0 H)³`. Neither index set contains the other. -/

/-- **Collapsing the third coordinate.** For fixed `n₁, n₂` the inner sum has at most one surviving
term, at `n₃ = H − n₁ − n₂`, and it survives exactly when `n₁ + n₂ < H` (otherwise every
`n₃ ≥ 1` overshoots `H`). The natural subtraction is exact there. -/
theorem sum_third (H n₁ n₂ : ℕ) :
    (∑ n₃ ∈ Finset.Ioc 0 H, (if n₁ + n₂ + n₃ = H then Λ n₁ * Λ n₂ * Λ n₃ else 0))
      = if n₁ + n₂ < H then Λ n₁ * Λ n₂ * Λ (H - n₁ - n₂) else 0 := by
  by_cases h : n₁ + n₂ < H
  · rw [if_pos h, Finset.sum_eq_single_of_mem (H - n₁ - n₂)
      (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)
      (fun b hb hne => by rw [Finset.mem_Ioc] at hb; exact if_neg (by omega))]
    exact if_pos (by omega)
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun n₃ hn₃ => ?_
    rw [Finset.mem_Ioc] at hn₃
    exact if_neg (by omega)

/-- **The common superset.** For any index set `A ⊆ range (H+1)` on whose complement the guarded
summand vanishes in each coordinate, the double sum over `A` equals the double sum over
`range (H+1)`. Applied twice below, with `A = Ioc 0 H` and `A = range H`. -/
theorem double_sum_eq (H : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.range (H + 1))
    (h1 : ∀ n ∈ Finset.range (H + 1), n ∉ A →
      ∀ m : ℕ, (if n + m < H then Λ n * Λ m * Λ (H - n - m) else 0) = 0)
    (h2 : ∀ n ∈ Finset.range (H + 1), n ∉ A →
      ∀ m : ℕ, (if m + n < H then Λ m * Λ n * Λ (H - m - n) else 0) = 0) :
    (∑ p ∈ A, ∑ q ∈ A, (if p + q < H then Λ p * Λ q * Λ (H - p - q) else 0))
      = ∑ p ∈ Finset.range (H + 1), ∑ q ∈ Finset.range (H + 1),
          (if p + q < H then Λ p * Λ q * Λ (H - p - q) else 0) := by
  calc (∑ p ∈ A, ∑ q ∈ A, (if p + q < H then Λ p * Λ q * Λ (H - p - q) else 0))
      = ∑ p ∈ A, ∑ q ∈ Finset.range (H + 1),
          (if p + q < H then Λ p * Λ q * Λ (H - p - q) else 0) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_subset hA fun n hn hnot => h2 n hn hnot p
    _ = ∑ p ∈ Finset.range (H + 1), ∑ q ∈ Finset.range (H + 1),
          (if p + q < H then Λ p * Λ q * Λ (H - p - q) else 0) :=
        Finset.sum_subset hA fun n hn hnot => Finset.sum_eq_zero fun m _ => h1 n hn hnot m

/-- **The reindexing.** `lambdaTriple H` is the diagonal triple sum over `(Ioc 0 H)³`.

The two vanishing mechanisms are different and both are needed: passing from `Ioc 0 H` to
`range (H+1)` adds the index `0`, killed by `Λ 0 = 0`; passing from `range H` to `range (H+1)` adds
the index `H`, killed by the guard `p + q < H`. -/
theorem lambdaTriple_eq_tripleSum (H : ℕ) :
    Spine.lambdaTriple H = ∑ n₁ ∈ Finset.Ioc 0 H, ∑ n₂ ∈ Finset.Ioc 0 H,
      ∑ n₃ ∈ Finset.Ioc 0 H, (if n₁ + n₂ + n₃ = H then Λ n₁ * Λ n₂ * Λ n₃ else 0) := by
  have hz0 : Λ 0 = 0 := ArithmeticFunction.map_zero
  have hIoc : Finset.Ioc 0 H ⊆ Finset.range (H + 1) := fun n hn => by
    rw [Finset.mem_Ioc] at hn; rw [Finset.mem_range]; omega
  have hrng : Finset.range H ⊆ Finset.range (H + 1) := fun n hn => by
    rw [Finset.mem_range] at hn; rw [Finset.mem_range]; omega
  have e1 := double_sum_eq H (Finset.Ioc 0 H) hIoc
    (fun n hn hnot m => by
      have hn0 : n = 0 := by
        rw [Finset.mem_range] at hn; rw [Finset.mem_Ioc] at hnot; omega
      subst hn0; simp [hz0])
    (fun n hn hnot m => by
      have hn0 : n = 0 := by
        rw [Finset.mem_range] at hn; rw [Finset.mem_Ioc] at hnot; omega
      subst hn0; simp [hz0])
  have e2 := double_sum_eq H (Finset.range H) hrng
    (fun n hn hnot m => by
      have hn0 : n = H := by
        rw [Finset.mem_range] at hn; rw [Finset.mem_range] at hnot; omega
      subst hn0; exact if_neg (by omega))
    (fun n hn hnot m => by
      have hn0 : n = H := by
        rw [Finset.mem_range] at hn; rw [Finset.mem_range] at hnot; omega
      subst hn0; exact if_neg (by omega))
  calc Spine.lambdaTriple H
      = ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H,
          (if p + q < H then Λ p * Λ q * Λ (H - p - q) else 0) := rfl
    _ = ∑ n₁ ∈ Finset.Ioc 0 H, ∑ n₂ ∈ Finset.Ioc 0 H,
          (if n₁ + n₂ < H then Λ n₁ * Λ n₂ * Λ (H - n₁ - n₂) else 0) := e2.trans e1.symm
    _ = ∑ n₁ ∈ Finset.Ioc 0 H, ∑ n₂ ∈ Finset.Ioc 0 H, ∑ n₃ ∈ Finset.Ioc 0 H,
          (if n₁ + n₂ + n₃ = H then Λ n₁ * Λ n₂ * Λ n₃ else 0) :=
        Finset.sum_congr rfl fun n₁ _ =>
          Finset.sum_congr rfl fun n₂ _ => (sum_third H n₁ n₂).symm

/-! ## THE LINK, DISCHARGED -/

/-- **Link 1 of the spine is a theorem.** No hypotheses; footprint
`[propext, Classical.choice, Quot.sound]`. -/
theorem circleMethodIdentity_holds : Spine.CircleMethodIdentity := by
  intro H
  rw [integral_kern_eq_tripleSum H, lambdaTriple_eq_tripleSum H, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n₁ _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n₂ _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n₃ _ => ?_
  split <;> simp

/-! ## The spine, now needing three links -/

/-- **The spine with `CircleMethodIdentity` discharged.** The headline theorem
`Spine.ternaryLogCountLower_of_links_main` carried four hypotheses; it now carries three, and the
remaining three are exactly the open mathematics: the major-arc main term, the minor-arc sup bound,
and the prime-power removal. -/
theorem ternaryLogCountLower_of_three (P Q : ℕ → ℕ)
    (mj : Spine.MajorArcLower P Q (1 / 2)) (mn : Spine.MinorSupBound P Q (3 / 10))
    (pp : Spine.PrimePowerRemoval 10) : TernaryLogCountLower :=
  Spine.ternaryLogCountLower_of_links_main P Q circleMethodIdentity_holds mj mn pp

/-- The same at the sharp constants `cMaj = 13/20`, `κ = 46/100`. -/
theorem ternaryLogCountLower_of_three_sharp (P Q : ℕ → ℕ)
    (mj : Spine.MajorArcLower P Q (13 / 20)) (mn : Spine.MinorSupBound P Q (46 / 100))
    (pp : Spine.PrimePowerRemoval 10) : TernaryLogCountLower :=
  Spine.ternaryLogCountLower_of_links_sharp P Q circleMethodIdentity_holds mj mn pp

/-- **The EP1054 input from three links.** The chain's one remaining trusted input,
`Principia.Erdos1054.Cite_Helfgott_weighted`, now follows from three hypotheses. -/
theorem cite_Helfgott_weighted_of_three (P Q : ℕ → ℕ)
    (mj : Spine.MajorArcLower P Q (1 / 2)) (mn : Spine.MinorSupBound P Q (3 / 10))
    (pp : Spine.PrimePowerRemoval 10) : Principia.Erdos1054.Cite_Helfgott_weighted :=
  cite_Helfgott_weighted_of_logCount (ternaryLogCountLower_of_three P Q mj mn pp)

/-- The same with Platt's numerical verification kept visible in the signature. **This is
bookkeeping, not a reduction to Platt** — see the long note on
`Spine.ternaryLogCountLower_of_links_platt`: taking both `MajorArcFromGRH PlattGRH …` and `PlattGRH`
is strictly more demanding than taking `MajorArcLower`, and the reduction is real only once
`MajorArcFromGRH PlattGRH P Q (1/2)` is proved. -/
theorem ternaryLogCountLower_of_three_platt (P Q : ℕ → ℕ)
    (mjG : Spine.MajorArcFromGRH Spine.PlattGRH P Q (1 / 2)) (grh : Spine.PlattGRH)
    (mn : Spine.MinorSupBound P Q (3 / 10)) (pp : Spine.PrimePowerRemoval 10) :
    TernaryLogCountLower :=
  ternaryLogCountLower_of_three P Q (mjG grh) mn pp

/-! ## What the remaining major-arc obligation actually says

With the identity discharged and `Spine.arcSplit_holds` already a theorem, the count splits over the
arcs **exactly**, and `MajorArcLower` can be restated with `majorIntegral` eliminated. This is a
restatement, not progress on the analysis; it is recorded because it names the exact quantity the
major-arc front has to bound, and because an `iff` cannot have weakened the target. -/

/-- **The count splits over the arcs, exactly**: `lambdaTriple H = Re 𝔐 + Re 𝔪`, for every pair of
cutoffs. Identity plus `Spine.arcSplit_holds`; no hypotheses, no size or parity condition. -/
theorem lambdaTriple_eq_arcs (H P Q : ℕ) :
    Spine.lambdaTriple H = (Spine.majorIntegral H P Q).re + (Spine.minorIntegral H P Q).re := by
  have heq : ((Spine.lambdaTriple H : ℝ) : ℂ)
      = Spine.majorIntegral H P Q + Spine.minorIntegral H P Q := by
    rw [circleMethodIdentity_holds H, Spine.arcSplit_holds H P Q]
  simpa using congrArg Complex.re heq

/-- **The major-arc link with `majorIntegral` eliminated.** `MajorArcLower P Q cMaj` holds exactly
when the Λ-triple count exceeds `cMaj·H²` *after paying the minor-arc integral*. The two sides are
equivalent, so nothing here is a weakening; what it buys is that the open obligation now mentions
only the count and the minor integral, i.e. the two objects the other two fronts work on. -/
theorem majorArcLower_iff (P Q : ℕ → ℕ) (cMaj : ℝ) :
    Spine.MajorArcLower P Q cMaj ↔
      ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H →
        cMaj * (H : ℝ) ^ 2 + (Spine.minorIntegral H (P H) (Q H)).re
          ≤ Spine.lambdaTriple H := by
  constructor
  · intro h H hodd hH
    have hmj := h H hodd hH
    rw [lambdaTriple_eq_arcs H (P H) (Q H)]
    linarith
  · intro h H hodd hH
    have hmj := h H hodd hH
    rw [lambdaTriple_eq_arcs H (P H) (Q H)] at hmj
    linarith

/-! ## THE ADVERSARIAL PASS — the discharge is not vacuous

An identity is satisfied degenerately exactly when both sides vanish identically. Three theorems
refute that, and none of them is a restatement of the identity. -/

/-- The circle integral's real part **is** the Λ-triple count. -/
theorem integral_kern_re (H : ℕ) :
    (∫ α in Set.Ioc (0 : ℝ) 1, Spine.kern H α).re = Spine.lambdaTriple H := by
  rw [← circleMethodIdentity_holds H, Complex.ofReal_re]

/-- **The imaginary part vanishes, for every `H`.** `kern H α = S(α)³e(−Hα)` is not real at any
individual `α`, and nothing in the definition of the integral forces its imaginary part to vanish —
this is a consequence of the identity, not a reformulation of it, and it is the quantity Python
measured as `< 5·10⁻¹²` for every `H ≤ 39`. -/
theorem integral_kern_im_eq_zero (H : ℕ) :
    (∫ α in Set.Ioc (0 : ℝ) 1, Spine.kern H α).im = 0 := by
  rw [← circleMethodIdentity_holds H, Complex.ofReal_im]

/-- **Attack: both sides are identically zero.** Refuted at `H = 9`:
`Probes.ternaryLogCount_nine_pos` gives `ternaryLogCount 9 = (log 3)³ > 0` and
`Spine.ternaryLogCount_le_lambdaTriple` lifts it to `lambdaTriple`, so the circle integral is
provably non-zero at an explicit `H`. -/
theorem integral_kern_nine_pos : 0 < (∫ α in Set.Ioc (0 : ℝ) 1, Spine.kern 9 α).re := by
  rw [integral_kern_re]
  exact lt_of_lt_of_le ternaryLogCount_nine_pos (Spine.ternaryLogCount_le_lambdaTriple 9)

/-- **The identity separates `H`s**: at `H = 2` the integral is exactly `0`, because `Λ 0 = Λ 1 = 0`
leaves no admissible triple. Together with `integral_kern_nine_pos` this shows the identity is not
satisfied by a constant on either side. -/
theorem integral_kern_two_eq_zero : (∫ α in Set.Ioc (0 : ℝ) 1, Spine.kern 2 α) = 0 := by
  rw [← circleMethodIdentity_holds 2]
  norm_num [Spine.lambdaTriple, Finset.sum_range_succ, ArithmeticFunction.map_zero,
    ArithmeticFunction.vonMangoldt_apply_one]

/-! ## What the identity buys unconditionally, and what it does not

Two unconditional ceilings on `lambdaTriple`, and the honest comparison between them. Neither is
the *floor* the route needs, and — this is the point — **neither constrains the route**: the spine's
open links are lower bounds, and an upper bound of size `H²·polylog` excludes no constant `cMaj`,
because `log H → ∞`. They are calibrations. They are recorded because the alternative is to leave
the reader guessing which of the two arguments is sharper, and the answer is not the flattering one.

Measured at the threshold `H = 10^27` (`log H = 62.1698`), against the truth `≈ 0.660162 H²`:

| bound | size | vs. the elementary one |
|---|---|---|
| trivial pair count, `H²(log H)³` | `2.40·10⁵ H²` | `1933×` worse |
| circle method (`lambdaTriple_le_circle`), `1.4 H²(log H)²` | `5.41·10³ H²` | `43.5×` worse |
| elementary (`lambdaTriple_le_two`), `2 H² log H` | `124.3 H²` | — |
| the truth | `0.660 H²` | `188×` below it |

So the circle-method ceiling is **weaker** than a three-line elementary argument. That is not a
defect of the identity; it is the `sup × L²` Hölder step throwing away exactly the minor-arc saving
that `MinorSupBound` is there to supply, and it measures how much that step costs: `(log H)²/1.4`
against `log H/2`, i.e. a factor `1.4·log H/2 = 43.5`. -/

/-- **The circle-method ceiling**, `lambdaTriple H ≤ (7/5)·H²(log H)²` for `H ≥ 10^27`: run
`Spine.secondMoment_holds` and the `sup × L²` Hölder arrangement over the **whole** circle rather
than the minor arcs, with `Spine.expSum_sup_trivial` as the sup.

It certifies that the identity composes end to end with the spine's three already-discharged links
and that the circle integral is of order `H²·polylog`. It is *not* the sharpest thing available:
`lambdaTriple_le_two` beats it by `43.5×` at the threshold by elementary means. Kept because the
comparison is the measurement. -/
theorem lambdaTriple_le_circle (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Spine.lambdaTriple H ≤ 7 / 5 * (H : ℝ) ^ 2 * Real.log (H : ℝ) ^ 2 := by
  have hL : (61 : ℝ) ≤ Real.log (H : ℝ) := Spine.log_ge_61 H hH
  have hcont := Spine.continuous_normExpSum H
  have hHR : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hC0 : (0 : ℝ) ≤ (H : ℝ) * Real.log (H : ℝ) := by positivity
  have h1 : ‖∫ α in Set.Ioc (0 : ℝ) 1, Spine.kern H α‖
      ≤ ∫ α in Set.Ioc (0 : ℝ) 1, ‖Spine.kern H α‖ := norm_integral_le_integral_norm _
  have h2 : (∫ α in Set.Ioc (0 : ℝ) 1, ‖Spine.kern H α‖)
      = ∫ α in Set.Ioc (0 : ℝ) 1, ‖Spine.expSum H α‖ ^ 3 :=
    setIntegral_congr_fun measurableSet_Ioc (fun α _ => Spine.norm_kern H α)
  have h3 : (∫ α in Set.Ioc (0 : ℝ) 1, ‖Spine.expSum H α‖ ^ 3)
      ≤ ∫ α in Set.Ioc (0 : ℝ) 1, ((H : ℝ) * Real.log (H : ℝ)) * ‖Spine.expSum H α‖ ^ 2 := by
    refine setIntegral_mono_on ((hcont.pow 3).integrableOn_Ioc)
      (((hcont.pow 2).const_smul ((H : ℝ) * Real.log (H : ℝ))).integrableOn_Ioc)
      measurableSet_Ioc (fun α _ => ?_)
    have hb := Spine.expSum_sup_trivial H α
    nlinarith [norm_nonneg (Spine.expSum H α), sq_nonneg ‖Spine.expSum H α‖]
  have h4 : (∫ α in Set.Ioc (0 : ℝ) 1, ((H : ℝ) * Real.log (H : ℝ)) * ‖Spine.expSum H α‖ ^ 2)
      = ((H : ℝ) * Real.log (H : ℝ)) * ∫ α in Set.Ioc (0 : ℝ) 1, ‖Spine.expSum H α‖ ^ 2 :=
    integral_const_mul _ _
  have h5 := Spine.secondMoment_holds H hH
  have h6 : ((H : ℝ) * Real.log (H : ℝ)) * ∫ α in Set.Ioc (0 : ℝ) 1, ‖Spine.expSum H α‖ ^ 2
      ≤ ((H : ℝ) * Real.log (H : ℝ)) * (7 / 5 * (H : ℝ) * Real.log (H : ℝ)) :=
    mul_le_mul_of_nonneg_left h5 hC0
  have hre : Spine.lambdaTriple H ≤ ‖∫ α in Set.Ioc (0 : ℝ) 1, Spine.kern H α‖ := by
    rw [← integral_kern_re H]
    exact le_trans (le_abs_self _)
      (Complex.abs_re_le_norm (∫ α in Set.Ioc (0 : ℝ) 1, Spine.kern H α))
  have hfin : ((H : ℝ) * Real.log (H : ℝ)) * (7 / 5 * (H : ℝ) * Real.log (H : ℝ))
      = 7 / 5 * (H : ℝ) ^ 2 * Real.log (H : ℝ) ^ 2 := by ring
  linarith [h1, h2.le, h2.ge, h3, h4.le, h4.ge, h6, hre, hfin.le, hfin.ge]

/-! ## The sharper elementary ceiling, for comparison

Three steps, no circle method: bound the determined third factor by `log H`, recognize what is left
as `(∑_{n < H} Λ n)²`, and bound that by `ψ(H)²`. -/

/-- `Λ n ≤ log H` for every `n ≤ H` — including `n = 0`, where `Λ 0 = 0 ≤ log H`. The `n = 0` case
is not cosmetic: `lambdaTriple`'s third coordinate `H − p − q` is `0` on part of the index set. -/
theorem vonMangoldt_le_log_cast (n H : ℕ) (hn : n ≤ H) (hH : 1 ≤ H) : Λ n ≤ Real.log (H : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    rw [ArithmeticFunction.map_zero]
    exact Real.log_nonneg (by exact_mod_cast hH)
  · exact le_trans vonMangoldt_le_log
      (Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hn))

/-- `∑_{p < H} Λ p ≤ ψ(H)`. The sums differ in two places and both are harmless: `range H` carries
the index `0`, where `Λ 0 = 0`, and `Ioc 0 H` carries the extra index `H`, where `Λ H ≥ 0`. -/
theorem sum_vonMangoldt_range_le_psi (H : ℕ) :
    ∑ p ∈ Finset.range H, Λ p ≤ Chebyshev.psi (H : ℝ) := by
  rw [Chebyshev.psi, Nat.floor_natCast]
  have hsub1 : Finset.Ico 1 H ⊆ Finset.range H := fun n hn => by
    rw [Finset.mem_Ico] at hn; rw [Finset.mem_range]; omega
  have heq : ∑ p ∈ Finset.Ico 1 H, Λ p = ∑ p ∈ Finset.range H, Λ p :=
    Finset.sum_subset hsub1 fun n hn hnot => by
      have hn0 : n = 0 := by
        rw [Finset.mem_range] at hn; rw [Finset.mem_Ico] at hnot; omega
      subst hn0; exact ArithmeticFunction.map_zero
  rw [← heq]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => vonMangoldt_nonneg
  intro n hn
  rw [Finset.mem_Ico] at hn
  rw [Finset.mem_Ioc]
  omega

/-- **The elementary ceiling, in closed form**: `lambdaTriple H ≤ log H · ψ(H)²`. The third
coordinate of every summand is determined by the first two, so bounding it by `log H` leaves the
unconstrained double sum `(∑_{p < H} Λ p)²`. No circle method, no second moment. -/
theorem lambdaTriple_le_log_mul_psi_sq (H : ℕ) (hH : 1 ≤ H) :
    Spine.lambdaTriple H ≤ Real.log (H : ℝ) * Chebyshev.psi (H : ℝ) ^ 2 := by
  have hlog0 : (0 : ℝ) ≤ Real.log (H : ℝ) := Real.log_nonneg (by exact_mod_cast hH)
  have hpsi : ∑ p ∈ Finset.range H, Λ p ≤ Chebyshev.psi (H : ℝ) := sum_vonMangoldt_range_le_psi H
  have hpsi0 : (0 : ℝ) ≤ ∑ p ∈ Finset.range H, Λ p :=
    Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg
  have hstep : Spine.lambdaTriple H ≤ Real.log (H : ℝ) * (∑ p ∈ Finset.range H, Λ p) ^ 2 := by
    rw [Spine.lambdaTriple, sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    have hp : (0 : ℝ) ≤ Λ p := vonMangoldt_nonneg
    have hq : (0 : ℝ) ≤ Λ q := vonMangoldt_nonneg
    split
    · have h3 : Λ (H - p - q) ≤ Real.log (H : ℝ) :=
        vonMangoldt_le_log_cast (H - p - q) H (by omega) hH
      calc Λ p * Λ q * Λ (H - p - q) ≤ Λ p * Λ q * Real.log (H : ℝ) :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg hp hq)
        _ = Real.log (H : ℝ) * (Λ p * Λ q) := by ring
    · exact mul_nonneg hlog0 (mul_nonneg hp hq)
  exact le_trans hstep
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpsi0 hpsi 2) hlog0)

/-- **The elementary ceiling, numerically**: `lambdaTriple H ≤ 2 H² log H` for `H ≥ 10^27`.

The constants, all exact rationals: Mathlib's `Chebyshev.psi_le` gives
`ψ(H) ≤ log 4 · H + 2√H log H`, `Spine.log_le_sqrt_div` turns the second term into `2H/10⁴`, and
`log 4 ≤ 1.3862943616`, so `ψ(H) ≤ 1.3865 H` (margin `5.64·10⁻⁶`) and
`ψ(H)² ≤ 1.92238225 H² ≤ 2 H²` (`13865² = 192238225`, checked as an integer). -/
theorem lambdaTriple_le_two (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Spine.lambdaTriple H ≤ 2 * (H : ℝ) ^ 2 * Real.log (H : ℝ) := by
  have hH1 : (1 : ℕ) ≤ H := le_trans (by norm_num) hH
  have hHR : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
  have hlog0 : (0 : ℝ) ≤ Real.log (H : ℝ) := Real.log_nonneg hHR
  have hcheb : Chebyshev.psi (H : ℝ)
      ≤ Real.log 4 * (H : ℝ) + 2 * Real.sqrt (H : ℝ) * Real.log (H : ℝ) := Chebyshev.psi_le hHR
  have hlog4 : Real.log 4 ≤ 1.3862943616 := by
    have h2 := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; nlinarith
  have hroot := Spine.log_le_sqrt_div H hH
  have hss : Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ) = (H : ℝ) := Real.mul_self_sqrt (by positivity)
  have hpsi0 : (0 : ℝ) ≤ Chebyshev.psi (H : ℝ) := by
    rw [Chebyshev.psi]
    exact Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg
  have hs2 : 2 * Real.sqrt (H : ℝ) * Real.log (H : ℝ) ≤ 2 / 10 ^ 4 * (H : ℝ) := by
    calc 2 * Real.sqrt (H : ℝ) * Real.log (H : ℝ)
        ≤ 2 * Real.sqrt (H : ℝ) * (Real.sqrt (H : ℝ) / 10 ^ 4) :=
          mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = 2 / 10 ^ 4 * (Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ)) := by ring
      _ = 2 / 10 ^ 4 * (H : ℝ) := by rw [hss]
  have hpsiH : Chebyshev.psi (H : ℝ) ≤ 1.3865 * (H : ℝ) := by nlinarith [hcheb, hlog4, hs2, hHR]
  have hpsisq : Chebyshev.psi (H : ℝ) ^ 2 ≤ 2 * (H : ℝ) ^ 2 := by
    nlinarith [hpsiH, hpsi0, hHR, sq_nonneg ((H : ℝ))]
  calc Spine.lambdaTriple H ≤ Real.log (H : ℝ) * Chebyshev.psi (H : ℝ) ^ 2 :=
        lambdaTriple_le_log_mul_psi_sq H hH1
    _ ≤ Real.log (H : ℝ) * (2 * (H : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hpsisq hlog0
    _ = 2 * (H : ℝ) ^ 2 * Real.log (H : ℝ) := by ring

/-! ## The integrand at the centre of the principal major arc

`α = 0` is the centre of the Farey window at `a/q = 0/1`, and it is where the whole main term comes
from. The identity says nothing about the *size* of `majorIntegral`, but these two lines say exactly
what the integrand is at that point, which is the datum the major-arc front starts from: the value
is real, positive and of size `≈ 2.665 H³` (since `ψ(H) ≤ 1.3865 H` and `1.3865³ = 2.66535`). The
principal window has width `2/(Q+1)`, so `H³/Q` is the scale of the main term — the arithmetic of
*which* `H³/Q` is Helfgott §3, not this file. -/

/-- `S(0) = ψ(H)`: at the arc centre every phase is `1` and the exponential sum degenerates to the
Chebyshev function. -/
theorem expSum_zero (H : ℕ) : Spine.expSum H 0 = ((Chebyshev.psi (H : ℝ) : ℝ) : ℂ) := by
  rw [Spine.expSum, Chebyshev.psi, Nat.floor_natCast, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_zero]
  simp [Principia.Common.Goldbach.e]

/-- `kern H 0 = ψ(H)³`, real and non-negative. -/
theorem kern_zero (H : ℕ) : Spine.kern H 0 = ((Chebyshev.psi (H : ℝ) : ℝ) : ℂ) ^ 3 := by
  rw [Spine.kern, expSum_zero, mul_zero]
  simp [Principia.Common.Goldbach.e]

end Principia.Common.TernaryGoldbach.CircleMethod
