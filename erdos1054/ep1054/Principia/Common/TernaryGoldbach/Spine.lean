/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.Probes
import Principia.Common.Goldbach.ArcDecomposition
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.DirichletContinuation

set_option autoImplicit false

/-!
# The spine of Helfgott's ternary Goldbach proof

**The obligation.** `Reduction.lean` replaced the EP1054 chain's one remaining trusted input,
`Principia.Erdos1054.Cite_Helfgott_weighted`, by the smoothing-free

  `TernaryLogCountLower : ∀ odd H ≥ 10^27, 0.00026 · H² ≤ ternaryLogCount H`.

This file is the **chain of inferences to that goal, with every gap a named hypothesis and no
`sorry`** (CLAUDE.md, the SPINE RULE). Three of the links are *proved here*; four remain
hypotheses, and each carries a docstring saying which paper section it is, what in the library
could close it, whether it is pointwise or `n`-averaged, and whether it is REACHABLE, HARD or
NUMERICAL.

## The route, and why it is not Helfgott's §7.4

Helfgott's §7.4 works with two coordinated smoothings `η₊`, `η_*` and the scale `ϰ = 49`; the
`Reduction.lean` sandwich shows the input is equivalent, up to the factor `1.079955²·1.414`, to a
statement with **no smoothing functions in it**, so `η₊`, `η_*`, `ϰ`, the band-limited Mellin
approximation `h_H` and the whole of Helfgott §4 are off the critical path. What survives is the
architecture: a circle-method identity, a split at a finite union of Farey arcs, a main term on the
arcs, an exponential-sum bound off them, and the removal of prime powers. That is the route
encoded below, with the **sharp cutoff** `∑_{0 < n ≤ H}` in place of a smoothing — the arrangement
the library's own `MinSum.vinogradov_sup_tight2` is built for.

```
                       PlattGRH  (NUMERICAL)
                          │
                          ▼
   CircleMethodIdentity   MajorArcLower cMaj        MinorSupBound κ
        (REACHABLE)            (HARD)                   (HARD)
            │                    │                        │
            │      ArcSplit ◄────┴────► MinorHolderBound ──┤
            │     (PROVED)              (PROVED)           │
            │                                    SecondMoment cL2 (PROVED)
            ▼                                              │
        lambdaTriple_lower_of_links :  (cMaj − κ·cL2)·H² ≤ lambdaTriple H
            │
            │  PrimePowerRemoval cPP  (REACHABLE)
            ▼
   ternaryLogCountLower_of_links :  TernaryLogCountLowerWith c₀
            │  cite_Helfgott_weighted_of_logCount  (Reduction.lean)
            ▼
        Principia.Erdos1054.Cite_Helfgott_weighted
```

## The constants, and the budget

The assembly is **parametric** in `(cMaj, κ, cL2, cPP, c₀)` with the single side condition

  `c₀ + κ·cL2 + cPP/10⁴ ≤ cMaj`.

`ternaryLogCountLower_of_links_main` instantiates it at `cMaj = 1/2`, `κ = 3/10`, `cL2 = 7/5`,
`cPP = 10`, `c₀ = 0.00026` (budget `0.42126 ≤ 0.5`), and
`ternaryLogCountLower_of_links_sharp` at `cMaj = 13/20`, `κ = 46/100` (budget `0.64526 ≤ 0.65`),
which is the weakest minor-arc hypothesis this arrangement can use.

Every constant was checked in exact/high-precision arithmetic before any Lean was written:

* the ternary singular series satisfies `inf_{H odd} 𝔖₃(H) = 1.3203236317` — twice the
  Hardy–Littlewood twin-prime constant. (An earlier draft said `1.320323674`, wrong past the 8th
  digit; corrected 2026-09-29.) Also `∏_p (1 + 1/(p−1)³) = 2.300961545`, so
  the true main term is `𝔖₃(H)H²/2 ≥ 0.660162 H²`. `cMaj = 1/2` therefore leaves **24.3 %** of the
  main term for the arc error, and `cMaj = 13/20` leaves **1.5 %**;
* `cL2 = 7/5` is proved below, and `log 4 = 1.386294…`, so the proof has `0.0137` of room in a
  place where it needs `0.0002`;
* the prime-power removal is really of size `≈ 8.7·10⁻¹² H²` (Helfgott's own constants) or
  `≈ 1.0·10⁻⁹ H²` with Mathlib's weaker `ψ − θ ≤ 2√x log x`, against the `cPP/10⁴ = 10⁻³ H²` the
  budget charges it — three orders of magnitude of deliberate slack, because the slack lemma
  `pp_slack` is proved through crude root bounds rather than through the true size.

## THE ADVERSARIAL PASS — what was tried, and what it found

A chain of `Prop`s that composes but does not *constrain* is worthless. Every link here is a
statement about **concretely defined objects** (`expSum`, `kern`, `lambdaTriple`,
`Goldbach.MajorArcs`, `ternaryLogCount`), so there is no function, measure or witness to
instantiate degenerately: each link is simply true or false. That removes the usual degenerate
satisfier, and leaves exactly two failure modes, both of which are recorded here as *theorems*.

1. **Everything zero is free, and it is provable.** `lowerWith_nonpos_free` proves
   `TernaryLogCountLowerWith c` outright for every `c ≤ 0`. So the composition at zero constants
   delivers nothing, and **all of the content sits in the positive margin `cMaj − κ·cL2`**.
2. **The arc cutoffs can be chosen so that the split buys nothing, and that is provable too.**
   `minorSet_one_one` proves `minorSet 1 1 = ∅` — the Farey windows of `MajorArcs 1 1` are the
   balls of radius `1/2` about the integers, which cover `ℝ`. Hence
   `minorSup_vacuous_at_one_one`: at those cutoffs `MinorSupBound` holds **for every `κ`**,
   including `κ = 0`; and `majorLower_at_one_one_is_whole_target` shows that the major-arc link
   then delivers the entire lower bound on `lambdaTriple` by itself. **The arc split is therefore
   not itself progress**; the progress is the design condition "few and narrow"
   (`ternvin.tex` 141–146), which no type can enforce and which the parameters `P`, `Q` carry.
   This is stated rather than hidden.
3. **The minor-arc link is not satisfiable by the bound the library gives for free.**
   `expSum_sup_trivial` is `‖S(α)‖ ≤ H log H` everywhere (`MinorArc.vonMangoldt_expsum_sup`), and
   `minorSup_demands_saving` proves that the link's `κ·H/log H` is at least **3000 times smaller**
   at every `H ≥ 10^27`. Measured against the sharpest thing the library actually has,
   `MinSum.vinogradov_sup_tight2` optimized over `(q,U,V)` at `H = 10^27` gives `0.0656 H`
   (two independent transcriptions: `0.0656 H` and `0.0699 H`), while `κ = 3/10` demands
   `0.004825 H` and `κ = 46/100` demands `0.007399 H` — short by **13.6×** and **8.9×**. The
   `6.4×` in `HELFGOTT-PROOF-MAP.md` is the same number at the litmap's sharper `(cMaj, cL2)`.
4. **The numerical input cannot be a free rider.** `spine_needs_grh` proves that if the major-arc
   link held with the GRH verification replaced by an *arbitrary* proposition, the verification
   would be doing no work — the exact analogue of `TwinPrime.Chain.spine_needs_fmmkls`.
5. **`Odd H` is load-bearing in every link.** `lowerWith_needs_odd` proves that for every even
   `H > 0` the conclusion is *false* for any `c > 0` (via
   `Probes.ternaryLogCount_eq_zero_of_even`), so dropping the hypothesis does not merely strengthen
   the links, it falsifies the goal. (`H = 0` is excluded because there `c·H² = 0` equals
   `ternaryLogCount 0` and the obligation is vacuously satisfied — the boundary case, not a
   counterexample.)
6. **The two counts are related in the wrong direction, and that is why link 7 exists.**
   `ternaryLogCount_le_lambdaTriple` proves `ternaryLogCount H ≤ lambdaTriple H` unconditionally.
   The circle method delivers a lower bound on `lambdaTriple`; the goal is about
   `ternaryLogCount`; so the inequality the spine needs is the *reverse* one with an error, which
   is precisely `PrimePowerRemoval`. The link cannot be dropped as "bookkeeping".

## What is NOT claimed

Nothing here proves any part of ternary Goldbach. `MajorArcLower` and `MinorSupBound` are
`def … : Prop` and unproved; `PlattGRH` is a *statement about zeros of Dirichlet L-functions* that
no proof assistant can currently establish (it is a verified-numerics stack, not a finite table —
about `5·10¹³` zeros over `1.6·10¹⁰` characters). `sorry` appears nowhere, deliberately: a `sorry`
would claim these steps are ours to discharge, and two of them are obligations someone else owes.
-/

namespace Principia.Common.TernaryGoldbach.Spine

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction

/-! ## The objects

All five are concretely defined, and `expSum` is written **character for character** as the sum
`MinSum.vinogradov_sup_tight2` and `MinorArc.minor_sup_uniform` bound, so the minor-arc link
attaches to the library's own object rather than to a lookalike. -/

/-- **The Λ-exponential sum with a sharp cutoff**, `S(α) = ∑_{0 < n ≤ H} Λ(n) e(nα)`. Identical to
the sum in `MinorArc.minor_sup_uniform`, `MinorArc.parseval_vonMangoldt` and
`MinSum.vinogradov_sup_tight2`. -/
noncomputable def expSum (H : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 H, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)

/-- **The circle-method integrand** `S(α)³ e(−Hα)`. -/
noncomputable def kern (H : ℕ) (α : ℝ) : ℂ := (expSum H α) ^ 3 * e (-(H : ℝ) * α)

open Classical in
/-- **The full Λ-triple count** `∑_{n₁+n₂+n₃ = H, nᵢ ≥ 1} Λ(n₁)Λ(n₂)Λ(n₃)`, written in the same
shape as `ternaryLogCount`: ordered pairs over `Finset.range H` twice, the third coordinate the
natural subtraction `H − p − q`, which is `≥ 1` exactly when `p + q < H`. This is what the circle
method computes; `ternaryLogCount` is the sub-sum over *odd primes*. -/
noncomputable def lambdaTriple (H : ℕ) : ℝ :=
  ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H,
    if p + q < H then Λ p * Λ q * Λ (H - p - q) else 0

/-- The major arcs intersected with the fundamental domain `(0,1]`. `Goldbach.MajorArcs P Q` is the
union of the Farey windows `|α − a/q| ≤ 1/(q(Q+1))` over moduli `q ≤ P`. -/
def majorSet (P Q : ℕ) : Set ℝ := Set.Ioc (0 : ℝ) 1 ∩ MajorArcs P Q

/-- The minor arcs: `(0,1] ∖ MajorArcs P Q`. This is **verbatim** the set on which
`MinorArc.minor_sup_uniform` concludes its sup bound. -/
def minorSet (P Q : ℕ) : Set ℝ := Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q

/-- `∫_{𝔐} S(α)³ e(−Hα) dα`. -/
noncomputable def majorIntegral (H P Q : ℕ) : ℂ := ∫ α in majorSet P Q, kern H α

/-- `∫_{𝔪} S(α)³ e(−Hα) dα`. -/
noncomputable def minorIntegral (H P Q : ℕ) : ℂ := ∫ α in minorSet P Q, kern H α

/-! ## Elementary facts about the objects -/

theorem norm_kern (H : ℕ) (α : ℝ) : ‖kern H α‖ = ‖expSum H α‖ ^ 3 := by
  rw [kern, norm_mul, norm_pow, e_norm, mul_one]

theorem continuous_e : Continuous e := by
  unfold Principia.Common.Goldbach.e; fun_prop

theorem continuous_kern (H : ℕ) : Continuous (kern H) := by
  unfold kern expSum
  exact ((MinorArc.vonMangoldt_expsum_continuous H).pow 3).mul
    (continuous_e.comp (by fun_prop))

theorem continuous_normExpSum (H : ℕ) : Continuous (fun α : ℝ => ‖expSum H α‖) :=
  (MinorArc.vonMangoldt_expsum_continuous H).norm

theorem measurableSet_minorSet (P Q : ℕ) : MeasurableSet (minorSet P Q) :=
  measurableSet_Ioc.diff (MinorArc.measurableSet_majorArcs P Q)

theorem minorSet_subset (P Q : ℕ) : minorSet P Q ⊆ Set.Ioc (0 : ℝ) 1 := Set.sdiff_subset

/-- **The only sup bound on `expSum` the library gives for free**: `‖S(α)‖ ≤ H log H`, everywhere.
`minorSup_demands_saving` measures how far below this the minor-arc link sits. -/
theorem expSum_sup_trivial (H : ℕ) (α : ℝ) : ‖expSum H α‖ ≤ (H : ℝ) * Real.log (H : ℝ) :=
  MinorArc.vonMangoldt_expsum_sup H α

/-- **The two counts, and the direction that makes `PrimePowerRemoval` necessary.** Every summand
of `ternaryLogCount` is a summand of `lambdaTriple` (`Λ p = log p` at a prime) and the rest are
`≥ 0`, so the log-count is *below* the Λ-triple count. The circle method lower-bounds
`lambdaTriple`; the goal is about `ternaryLogCount`; so this inequality points the wrong way and
the removal link is doing real work, not bookkeeping. -/
theorem ternaryLogCount_le_lambdaTriple (H : ℕ) : ternaryLogCount H ≤ lambdaTriple H := by
  simp only [ternaryLogCount, lambdaTriple]
  refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
  by_cases hc : p + q < H ∧ Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime (H - p - q) ∧
      Odd p ∧ Odd q ∧ Odd (H - p - q)
  · rw [if_pos hc, if_pos hc.1, vonMangoldt_apply_prime hc.2.1,
      vonMangoldt_apply_prime hc.2.2.1, vonMangoldt_apply_prime hc.2.2.2.1]
  · rw [if_neg hc]
    split
    · exact mul_nonneg (mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg) vonMangoldt_nonneg
    · exact le_refl 0

/-! ## Arithmetic at the threshold

Three crude bounds on `log H` for `H ≥ 10^27`, used by the discharged links and by the budget.
They are deliberately lossy (the `(log H)²` bound has a factor `8·10⁵` of slack at the threshold)
because their only job is to make the budget's `cPP/10⁴` charge affordable. -/

/-- `(10^27)^{1/4} ≥ 10^6`. -/
theorem qroot_ge (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    (10 : ℝ) ^ 6 ≤ Real.sqrt (Real.sqrt (H : ℝ)) := by
  have hHR : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH
  have h1 : (10 : ℝ) ^ 12 ≤ Real.sqrt (H : ℝ) := by
    rw [show ((10:ℝ) ^ 12) = Real.sqrt ((10:ℝ) ^ 24) by
      rw [show ((10:ℝ) ^ 24) = ((10:ℝ) ^ 12) ^ 2 by ring, Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 24])
  rw [show ((10:ℝ) ^ 6) = Real.sqrt ((10:ℝ) ^ 12) by
    rw [show ((10:ℝ) ^ 12) = ((10:ℝ) ^ 6) ^ 2 by ring, Real.sqrt_sq (by positivity)]]
  exact Real.sqrt_le_sqrt h1

/-- `log x ≤ 4 x^{1/4}`, from `log t ≤ t − 1` at `t = x^{1/4}`. -/
theorem log_le_qroot (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log (H : ℝ) ≤ 4 * Real.sqrt (Real.sqrt (H : ℝ)) := by
  set s : ℝ := Real.sqrt (Real.sqrt (H : ℝ)) with hs
  have hslb : (10 : ℝ) ^ 6 ≤ s := qroot_ge H hH
  have hspos : (0 : ℝ) < s := by positivity
  have hs2 : s ^ 2 = Real.sqrt (H : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hs4 : s ^ 4 = (H : ℝ) := by
    have h := Real.sq_sqrt (show (0:ℝ) ≤ (H:ℝ) by positivity)
    calc s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = Real.sqrt (H:ℝ) ^ 2 := by rw [hs2]
      _ = (H : ℝ) := h
  have hlog : Real.log (H : ℝ) = 4 * Real.log s := by
    rw [← hs4, Real.log_pow]; norm_num
  have h1 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hspos
  rw [hlog]; linarith

/-- `log H ≤ √H/10⁴` for `H ≥ 10^27`. -/
theorem log_le_sqrt_div (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log (H : ℝ) ≤ Real.sqrt (H : ℝ) / 10 ^ 4 := by
  set s : ℝ := Real.sqrt (Real.sqrt (H : ℝ)) with hs
  have hslb : (10 : ℝ) ^ 6 ≤ s := qroot_ge H hH
  have hs2 : s ^ 2 = Real.sqrt (H : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h4 := log_le_qroot H hH
  rw [← hs2]
  nlinarith [hslb, h4]

/-- `(log H)² ≤ √H/10⁴` for `H ≥ 10^27`, via `log H ≤ 8 H^{1/8}`. The eighth root is needed: the
quarter-root bound gives only `(log H)² ≤ 16√H`, which is false against this right-hand side. -/
theorem log_sq_le_sqrt_div (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    Real.log (H : ℝ) ^ 2 ≤ Real.sqrt (H : ℝ) / 10 ^ 4 := by
  set s : ℝ := Real.sqrt (Real.sqrt (H : ℝ)) with hs
  set t : ℝ := Real.sqrt s with ht
  have hslb : (10 : ℝ) ^ 6 ≤ s := qroot_ge H hH
  have hspos : (0 : ℝ) < s := by positivity
  have ht2 : t ^ 2 = s := Real.sq_sqrt (le_of_lt hspos)
  have htpos : (0 : ℝ) < t := by rw [ht]; exact Real.sqrt_pos.mpr hspos
  have hs2 : s ^ 2 = Real.sqrt (H : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have ht8 : t ^ 8 = (H : ℝ) := by
    have h := Real.sq_sqrt (show (0:ℝ) ≤ (H:ℝ) by positivity)
    calc t ^ 8 = ((t ^ 2) ^ 2) ^ 2 := by ring
      _ = ((s) ^ 2) ^ 2 := by rw [ht2]
      _ = Real.sqrt (H:ℝ) ^ 2 := by rw [hs2]
      _ = (H : ℝ) := h
  have hlog : Real.log (H : ℝ) = 8 * Real.log t := by
    rw [← ht8, Real.log_pow]; norm_num
  have h1 : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos htpos
  have hub : Real.log (H : ℝ) ≤ 8 * t := by rw [hlog]; linarith
  have hlb : (0 : ℝ) ≤ Real.log (H : ℝ) := by
    apply Real.log_nonneg
    have : (10:ℝ) ^ 27 ≤ (H:ℝ) := by exact_mod_cast hH
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 27]
  have hsq : Real.log (H : ℝ) ^ 2 ≤ 64 * s := by nlinarith [hub, hlb, ht2]
  rw [← hs2]
  nlinarith [hslb, hsq]

/-- `log H ≥ 61` for `H ≥ 10^27`, via `2^89 ≤ 10^27` and `Real.log_two_gt_d9`
(`89 · 0.6931471803 = 61.6901…`). The truth is `62.1698`. -/
theorem log_ge_61 (H : ℕ) (hH : 10 ^ 27 ≤ H) : (61 : ℝ) ≤ Real.log (H : ℝ) := by
  have h2 : (2 : ℕ) ^ 89 ≤ H := le_trans (by norm_num) hH
  have h2R : (2 : ℝ) ^ 89 ≤ (H : ℝ) := by exact_mod_cast h2
  have hmono : Real.log ((2:ℝ) ^ 89) ≤ Real.log (H : ℝ) := Real.log_le_log (by positivity) h2R
  rw [Real.log_pow] at hmono
  have := Real.log_two_gt_d9
  push_cast at hmono
  nlinarith [hmono, this]

/-! ## THE LINKS

Seven of them. Each is a `def … : Prop` about the concretely defined objects above, so there is
no witness to instantiate degenerately; and each is tagged REACHABLE / HARD / NUMERICAL. -/

/-- **Link 1 — the circle-method identity.** *REACHABLE.*

`∑_{n₁+n₂+n₃=H} Λ(n₁)Λ(n₂)Λ(n₃) = ∫₀¹ S(α)³ e(−Hα) dα`, an *exact* identity because `S` is
supported on `[1,H]`.

* **Paper:** `(7.49)` = `eq:masd`, `ternvin.tex` line 5317 (with `η ≡ 1`, i.e. a sharp cutoff).
* **Library:** `MinorArc.integral_e_nat` and `MinorArc.char_orthogonality` supply the
  orthogonality; `MinorArc.parseval_vonMangoldt` is the *quadratic* case of exactly this argument
  and is the model to imitate. No cube appears anywhere in the library, so this is new Lean but
  not new mathematics.
* **Pointwise** in `H` (not `n`-averaged). -/
def CircleMethodIdentity : Prop :=
  ∀ H : ℕ, ((lambdaTriple H : ℝ) : ℂ) = ∫ α in Set.Ioc (0 : ℝ) 1, kern H α

/-- **Link 2 — the arc split.** *PROVED below* (`arcSplit_holds`), so it is not a hypothesis of
the instantiated theorems.

`∫_{(0,1]} = ∫_{𝔐} + ∫_{𝔪}`, for **every** pair of cutoffs. Pure measure theory:
`MeasureTheory.integral_inter_add_sdiff` with `MinorArc.measurableSet_majorArcs` and continuity of
the integrand. Step 2 of `ternvin.tex` §7.4. -/
def ArcSplit : Prop :=
  ∀ H P Q : ℕ, (∫ α in Set.Ioc (0 : ℝ) 1, kern H α) = majorIntegral H P Q + minorIntegral H P Q

/-- **Link 3 — the major-arc lower bound.** *HARD*, and it is where the numerical input enters.

`cMaj · H² ≤ Re ∫_{𝔐} S(α)³ e(−Hα) dα` for odd `H ≥ 10^27`, with the cutoffs `P H`, `Q H`.

* **Paper:** Helfgott §3 + §7.1–§7.2, concluding in `(7.25)` = `eq:juventud`
  (`≥ 1.058259 x²/ϰ`). The asymptotic is `𝔖₃(H)H²/2 ≥ 0.660162 H²` for odd `H`, so any
  `cMaj < 0.66` is consistent with the truth; the gap to `0.66` is the arc-error budget.
* **Library:** the `MajorArc.cRam` layer (`cRam`, `ramSum_eq_cRam`, `cRam_mul`, `cRam_prime`,
  `cRam_eq_conv`) is campaign-agnostic and transfers verbatim, but every bound above it
  (`singSeries_ge`, `one_add_Tarith_ge`, `kernel_real_lb`, `hmain_bound`) is stated for the
  **binary** local term `μ(q)²c_q(n)/φ(q)²` and carries `Even n`, so nothing applies as-is: the
  ternary local term `μ(q)³c_q(H)/φ(q)³` and its Euler product must be re-proved.
  `MinorArc.major_window_eval` is pointwise in `α` but its constant is existential in `ε` with no
  uniformity in `q`, so it gives nothing at an explicit threshold.
* **Pointwise** in `H`. Note `RatedWindow.core_variance` and every `major_bessel_*` lemma are
  `n`-**averaged** and binary — an `ℓ²`-in-`n` bound is consistent with the count vanishing at any
  single `H`, so they cannot serve here. -/
def MajorArcLower (P Q : ℕ → ℕ) (cMaj : ℝ) : Prop :=
  ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H → cMaj * (H : ℝ) ^ 2 ≤ (majorIntegral H (P H) (Q H)).re

/-- **Link 4 — the minor-arc sup bound.** *HARD*; this is the binding constraint of the whole
route.

`‖S(α)‖ ≤ κ·H/log H` for every `α` off the major arcs, for odd `H ≥ 10^27`.

* **Paper:** Helfgott's minor-arc paper, [arXiv:1205.5252] Main Theorem (`eq:kraw`), used through
  §6 of the ternary paper; essentially `((log q)/√φ(q))·x`.
* **Library:** `MinorArc.minor_sup_uniform` is the *exact* bridge — it concludes a sup bound on
  `Set.Ioc 0 1 \ MajorArcs P Q`, which is `minorSet P Q` by definition — fed by
  `MinSum.vinogradov_sup_tight2`. `minorSupBound_of_envelope` below discharges this link down to a
  purely explicit inequality on `MinorArc.tightSupRHS`, so the remaining obligation is elementary
  in form. It is nevertheless out of reach: optimized over `(q,U,V)` at `H = 10^27` the tight RHS
  floors at `0.0656 H`, against `0.004825 H` demanded at `κ = 3/10` — short by `13.6×`, and the
  obstruction is structural (a `q`-independent Type-I term `~8·U·V·log(UV)` fights the Type-II
  terms that force `U`, `V` up). Do **not** route through `MinorArc.minorCsup_bound`: its
  `P³ ≤ N` hypothesis caps `P ≤ 10⁹` and it gives `2507 H`.
* **Pointwise** in `α`. -/
def MinorSupBound (P Q : ℕ → ℕ) (κ : ℝ) : Prop :=
  ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H → ∀ α ∈ minorSet (P H) (Q H),
    ‖expSum H α‖ ≤ κ * (H : ℝ) / Real.log (H : ℝ)

/-- **Link 5 — the second moment.** *PROVED below* (`secondMoment_holds` at `cL2 = 7/5`), so it is
not a hypothesis of the instantiated theorems.

`∫₀¹ ‖S(α)‖² dα ≤ cL2 · H log H`. Parseval (`MinorArc.parseval_vonMangoldt`, exact) turns the
integral into `∑_{n ≤ H} Λ(n)²`, and `Λ(n) ≤ log H` plus Mathlib's `Chebyshev.psi_le`
(`ψ x ≤ log 4 · x + 2√x log x`) closes it. The library's own `MinorArc.sum_vonMangoldt_sq_le` is a
factor `log H = 62.17` weaker and would not do: it gives `H (log H)²`, which makes the minor
contribution `κ·cL2·H² log H` and the route fails. Rosser–Schoenfeld's `ψ(x) < 1.03883x` would
give `cL2 = 1.04`; it is not in Mathlib. -/
def SecondMoment (cL2 : ℝ) : Prop :=
  ∀ H : ℕ, 10 ^ 27 ≤ H →
    (∫ α in Set.Ioc (0 : ℝ) 1, ‖expSum H α‖ ^ 2) ≤ cL2 * (H : ℝ) * Real.log (H : ℝ)

/-- **Link 6 — the Hölder step.** *PROVED below* (`minorHolder_holds`), so it is not a hypothesis
of the instantiated theorems.

`‖∫_𝔪 S³e‖ ≤ (sup_𝔪‖S‖) · ∫₀¹‖S‖²`, the `sup × L²` arrangement of §7.3. Note this is the *crude*
arrangement: Helfgott's §5–§6 (Ramaré's improved large sieve, the `ℓ²`-over-arcs bound `H(r₀)` and
the subtraction of the major-arc `ℓ²` mass) is worth a measured factor `1.73` over it, which is
exactly what the weight-free target's constant slack pays for. `MinorArc.minor_arc_L4_bound` is
the same idiom one power up. -/
def MinorHolderBound : Prop :=
  ∀ (H P Q : ℕ) (C : ℝ), 0 ≤ C → (∀ α ∈ minorSet P Q, ‖expSum H α‖ ≤ C) →
    ‖minorIntegral H P Q‖ ≤ C * ∫ α in Set.Ioc (0 : ℝ) 1, ‖expSum H α‖ ^ 2

/-- **Link 7 — prime-power and parity removal.** *REACHABLE.*

`lambdaTriple H − cPP·H^{3/2}(log H)² ≤ ternaryLogCount H`: the passage from the Λ-triple count to
the count over *odd primes*. `ternaryLogCount_le_lambdaTriple` shows the reverse inequality holds
unconditionally, so this is the direction that carries content.

* **Paper:** `(7.50)` = `eq:duke`, `ternvin.tex` line 5346, bounded by
  `3 (log N) (∑_{n ≤ N non-prime or 2} Λ(n))(∑_{n ≤ N} Λ(n))`.
* **Library:** `Common/Chebyshev` (`psi_ge_chebyshev`, `theta_ge_chebyshev`, `PrimeSum.lean`) and
  Mathlib's `Chebyshev.psi_sub_theta_le` (`ψ − θ ≤ 2√x log x`) give the proper-prime-power sum;
  `ArcDecomposition.card_properPrimePow_le` and `badRep_le` are the binary analogues of exactly
  this bookkeeping. The `(log H)²` (rather than Helfgott's `log H`) is the price of Mathlib's
  weaker `ψ − θ` bound; the true size is `≈ 10⁻⁹ H²` either way.
* **Pointwise** in `H`. -/
def PrimePowerRemoval (cPP : ℝ) : Prop :=
  ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H →
    lambdaTriple H - cPP * ((H : ℝ) * Real.sqrt (H : ℝ)) * Real.log (H : ℝ) ^ 2
      ≤ ternaryLogCount H

/-! ## The numerical input, stated rather than buried -/

/-- **Platt's finite GRH verification**, the one input of Helfgott's proof that is a *computation*.
*NUMERICAL.*

> For every primitive Dirichlet character `χ` of conductor `q ≤ 3·10⁵`, every non-trivial zero `ρ`
> of `L(s,χ)` with `|Im ρ| ≤ 10⁸/q` satisfies `Re ρ = 1/2`.

(`majarcs.tex` §"A verification of zeros and its consequences", lines 4750–4765; Platt,
[arXiv:1305.3087].) "Non-trivial" is encoded as `0 < Re s < 1`. Platt certifies *more* for even
`q` (height `max(10⁸/q, 200 + 7.5·10⁷/q)`) and up to `q ≤ 4·10⁵`; the form here is the common
weaker part, which is all Helfgott uses at `r = 3·10⁵`, `δ₀ = 8`.

It is stated concretely rather than left an opaque `Prop` because it *is* statable — and stating it
shows what it is: a **negative statement about a continuum**, not a finite table. It is certified
by Turing's method over interval-arithmetic `L`-function evaluation; a table is also out of the
question on size grounds (`≈ 4.96·10⁸/q` zeros per character, `≈ 5·10¹³` zeros over `≈ 1.6·10¹⁰`
characters, `~0.9 PB`). No proof assistant has a verified rigorous `L(s,χ)` evaluator, a verified
`S(T)` zero count, or a verified isolation argument, so **this link is an obligation someone else
owes** — which is why it is a hypothesis and never a `sorry`.

It enters the proof **only** through the major arcs (`ternvin.tex` 363–366: *"It is in [HelfMaj],
and not elsewhere, that the major L-function computation in [Plattfresh] gets used"*); the minor
arcs use no `L`-function information at all. A zero-free region cannot substitute: with Kadiri's
`C = 6.397` a single zero at `|τ| ≈ 1`, `q = 150000` contributes `44.65 %` of the main term against
an affordable `3.06 %`, and reaching `3.06 %` needs `x ≥ 10¹¹⁵`. This repository's
`SW.dvp_zero_free_uniform` is the only uniform effective zero-free region for Dirichlet
`L`-functions in any prover and it **cannot be aimed at 10^27**. -/
def PlattGRH : Prop :=
  ∀ (q : ℕ) [NeZero q], q ≤ 300000 → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 10 ^ 8 / (q : ℝ) → s.re = 1 / 2

/-- **The major-arc link as a consumer of a numerical input.** `G` is left an arbitrary `Prop` so
that `spine_needs_grh` can show the input is load-bearing; instantiate `G := PlattGRH`. -/
def MajorArcFromGRH (G : Prop) (P Q : ℕ → ℕ) (cMaj : ℝ) : Prop := G → MajorArcLower P Q cMaj

/-! ## The three links that are discharged outright -/

/-- **Link 2 is a theorem.** Measure additivity over the partition of `(0,1]` by the major arcs. -/
theorem arcSplit_holds : ArcSplit := by
  intro H P Q
  rw [majorIntegral, minorIntegral, majorSet, minorSet]
  exact (MeasureTheory.integral_inter_add_sdiff (MinorArc.measurableSet_majorArcs P Q)
    ((continuous_kern H).integrableOn_Ioc)).symm

/-- Parseval, in the set-integral form the links use. -/
theorem parseval_set (H : ℕ) :
    (∫ α in Set.Ioc (0 : ℝ) 1, ‖expSum H α‖ ^ 2) = ∑ n ∈ Finset.Ioc 0 H, Λ n ^ 2 := by
  rw [← intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  exact MinorArc.parseval_vonMangoldt H

/-- `∑_{n ≤ N} Λ(n)² ≤ log N · ψ(N)`, from `Λ(n) ≤ log n ≤ log N` and `Λ ≥ 0`. This is the step
that turns the library's `H(log H)²` into the `H log H` the route needs. -/
theorem sum_vonMangoldt_sq_le_psi (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 ≤ Real.log (N : ℝ) * Chebyshev.psi (N : ℝ) := by
  rw [Chebyshev.psi, Nat.floor_natCast, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Finset.mem_Ioc] at hn
  have h1 : Λ n ≤ Real.log (N : ℝ) :=
    le_trans vonMangoldt_le_log
      (Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2))
  calc Λ n ^ 2 = Λ n * Λ n := by ring
    _ ≤ Real.log (N : ℝ) * Λ n := mul_le_mul_of_nonneg_right h1 vonMangoldt_nonneg

/-- **Link 5 is a theorem, at `cL2 = 7/5`.** `log 4 = 1.3862943611…`, and the proof needs
`1/5000 = 0.0002` of room above it, so `7/5` clears by `0.0137`. -/
theorem secondMoment_holds : SecondMoment (7 / 5) := by
  intro H hH
  have hH1 : (1 : ℕ) ≤ H := le_trans (by norm_num) hH
  have hHR : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
  have hlog0 : (0 : ℝ) ≤ Real.log (H : ℝ) := Real.log_nonneg hHR
  have hcheb : Chebyshev.psi (H : ℝ)
      ≤ Real.log 4 * (H : ℝ) + 2 * Real.sqrt (H : ℝ) * Real.log (H : ℝ) := Chebyshev.psi_le hHR
  have hlog4 : Real.log 4 ≤ 1.3862943616 := by
    have h2 := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; nlinarith
  have hroot := log_le_sqrt_div H hH
  have hsq : (0 : ℝ) ≤ Real.sqrt (H : ℝ) := Real.sqrt_nonneg _
  have hss : Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ) = (H : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hstep : 2 * Real.sqrt (H : ℝ) * Real.log (H : ℝ) * Real.log (H : ℝ)
      ≤ 2 / 10 ^ 4 * (H : ℝ) * Real.log (H : ℝ) := by
    calc 2 * Real.sqrt (H : ℝ) * Real.log (H : ℝ) * Real.log (H : ℝ)
        = (2 * Real.sqrt (H : ℝ) * Real.log (H : ℝ)) * Real.log (H : ℝ) := by ring
      _ ≤ (2 * Real.sqrt (H : ℝ) * Real.log (H : ℝ)) * (Real.sqrt (H : ℝ) / 10 ^ 4) :=
          mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = 2 / 10 ^ 4 * (Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ)) * Real.log (H : ℝ) := by ring
      _ = 2 / 10 ^ 4 * (H : ℝ) * Real.log (H : ℝ) := by rw [hss]
  have hHL : (0 : ℝ) ≤ (H : ℝ) * Real.log (H : ℝ) := by positivity
  rw [parseval_set]
  calc ∑ n ∈ Finset.Ioc 0 H, Λ n ^ 2 ≤ Real.log (H : ℝ) * Chebyshev.psi (H : ℝ) :=
        sum_vonMangoldt_sq_le_psi H
    _ ≤ Real.log (H : ℝ) * (Real.log 4 * (H : ℝ) + 2 * Real.sqrt (H : ℝ) * Real.log (H : ℝ)) :=
        mul_le_mul_of_nonneg_left hcheb hlog0
    _ = Real.log 4 * ((H : ℝ) * Real.log (H : ℝ))
          + 2 * Real.sqrt (H : ℝ) * Real.log (H : ℝ) * Real.log (H : ℝ) := by ring
    _ ≤ 1.3862943616 * ((H : ℝ) * Real.log (H : ℝ)) + 2 / 10 ^ 4 * (H : ℝ) * Real.log (H : ℝ) := by
        have := mul_le_mul_of_nonneg_right hlog4 hHL
        linarith
    _ ≤ 7 / 5 * (H : ℝ) * Real.log (H : ℝ) := by nlinarith [hHL]

/-- **Link 6 is a theorem.** `‖∫_𝔪 S³e‖ ≤ ∫_𝔪‖S‖³ ≤ C∫_𝔪‖S‖² ≤ C∫₀¹‖S‖²`. -/
theorem minorHolder_holds : MinorHolderBound := by
  intro H P Q C hC hsup
  have hcont := continuous_normExpSum H
  have hms := measurableSet_minorSet P Q
  have hsub := minorSet_subset P Q
  have hint3 : IntegrableOn (fun α : ℝ => ‖expSum H α‖ ^ 3) (minorSet P Q) volume :=
    ((hcont.pow 3).integrableOn_Ioc).mono_set hsub
  have hint2C : IntegrableOn (fun α : ℝ => C * ‖expSum H α‖ ^ 2) (minorSet P Q) volume :=
    (((hcont.pow 2).const_smul C).integrableOn_Ioc).mono_set hsub
  have h1 : ‖∫ α in minorSet P Q, kern H α‖ ≤ ∫ α in minorSet P Q, ‖kern H α‖ :=
    norm_integral_le_integral_norm _
  have h2 : (∫ α in minorSet P Q, ‖kern H α‖) = ∫ α in minorSet P Q, ‖expSum H α‖ ^ 3 :=
    setIntegral_congr_fun hms (fun α _ => norm_kern H α)
  have h3 : (∫ α in minorSet P Q, ‖expSum H α‖ ^ 3)
      ≤ ∫ α in minorSet P Q, C * ‖expSum H α‖ ^ 2 := by
    refine setIntegral_mono_on hint3 hint2C hms (fun α hα => ?_)
    have hb := hsup α hα
    nlinarith [norm_nonneg (expSum H α), sq_nonneg ‖expSum H α‖]
  have h4 : (∫ α in minorSet P Q, C * ‖expSum H α‖ ^ 2)
      = C * ∫ α in minorSet P Q, ‖expSum H α‖ ^ 2 := integral_const_mul _ _
  have h5 : (∫ α in minorSet P Q, ‖expSum H α‖ ^ 2)
      ≤ ∫ α in Set.Ioc (0 : ℝ) 1, ‖expSum H α‖ ^ 2 := by
    refine setIntegral_mono_set ((hcont.pow 2).integrableOn_Ioc) ?_ hsub.eventuallyLE
    exact Filter.Eventually.of_forall (fun α => by positivity)
  rw [minorIntegral]
  calc ‖∫ α in minorSet P Q, kern H α‖ ≤ ∫ α in minorSet P Q, ‖expSum H α‖ ^ 3 := by
        rw [← h2]; exact h1
    _ ≤ C * ∫ α in minorSet P Q, ‖expSum H α‖ ^ 2 := by rw [← h4]; exact h3
    _ ≤ C * ∫ α in Set.Ioc (0 : ℝ) 1, ‖expSum H α‖ ^ 2 := mul_le_mul_of_nonneg_left h5 hC

/-! ## The minor-arc link, reduced to an explicit elementary inequality

`minorSupBound_of_envelope` is the attachment point: it takes the *exact* hypothesis of
`MinorArc.minor_sup_uniform` and returns `MinorSupBound`. After it, the remaining obligation
mentions no exponential sum and no arc — only the closed-form `MinorArc.tightSupRHS`. That the
inequality is elementary in form does not make it true: see the `13.6×` shortfall recorded above. -/

/-- **The minor-arc link follows from a `tightSupRHS` envelope**, via
`MinorArc.minor_sup_uniform` and `MinSum.vinogradov_sup_tight2`.

**REPAIRED 2026-09-29: every hypothesis is now restricted to `10^27 ≤ H`.** As first written they
were quantified over *all* `H`, which made them **jointly unsatisfiable** and the lemma impossible
to apply: `hU 0 : U 0 ≤ 0` forces `U 0 = 0`, contradicting `hUV1 0 : 1 ≤ U 0 * V 0`. So the
declaration advertised above as "the attachment point" for this link could never have been used by
anybody, and nothing noticed for two rounds because nobody had tried — the defect is invisible to
typechecking, to `#print axioms` and to the gate, and surfaced only when the minor-arc front
attempted the application. (It proved the obstruction: `MinorArcBound.envelope_hyps_unsatisfiable`.)
`MinorSupBound` itself only ever quantifies over `H ≥ 10^27`, so the restriction costs nothing.
This is the spine rule's own moral in miniature: re-reading confirms what you meant, and only
*proving* tests what you wrote. -/
theorem minorSupBound_of_envelope (P Q U V : ℕ → ℕ) (κ : ℝ)
    (hP : ∀ H : ℕ, 10 ^ 27 ≤ H → 0 < P H) (hPQ : ∀ H : ℕ, 10 ^ 27 ≤ H → P H ≤ Q H)
    (hU : ∀ H : ℕ, 10 ^ 27 ≤ H → U H ≤ H) (hUV : ∀ H : ℕ, 10 ^ 27 ≤ H → U H * V H ≤ H)
    (hUV1 : ∀ H : ℕ, 10 ^ 27 ≤ H → 1 ≤ U H * V H)
    (henv : ∀ H : ℕ, 10 ^ 27 ≤ H → ∀ q : ℕ, P H < q → q ≤ Q H →
      MinorArc.tightSupRHS q (U H) (V H) H ≤ κ * (H : ℝ) / Real.log (H : ℝ)) :
    MinorSupBound P Q κ := fun H _ hH α hα =>
  MinorArc.minor_sup_uniform H (P H) (Q H) (U H) (V H) (hP H hH) (hPQ H hH) (hU H hH) (hUV H hH)
    (hUV1 H hH) (κ * (H : ℝ) / Real.log (H : ℝ)) (fun q h1 h2 => henv H hH q h1 h2) α hα

/-! ## The budget lemma -/

/-- The prime-power removal charge is affordable: `H^{3/2}(log H)² ≤ H²/10⁴` for `H ≥ 10^27`. The
truth at the threshold is `1.22·10⁻⁶ · H²/10⁴`, i.e. this is lossy by six orders of magnitude and
still enough. -/
theorem pp_slack (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    (H : ℝ) * Real.sqrt (H : ℝ) * Real.log (H : ℝ) ^ 2 ≤ (H : ℝ) ^ 2 / 10 ^ 4 := by
  have h1 := log_sq_le_sqrt_div H hH
  have hHR : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hss : Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ) = (H : ℝ) := Real.mul_self_sqrt hHR
  calc (H : ℝ) * Real.sqrt (H : ℝ) * Real.log (H : ℝ) ^ 2
      ≤ (H : ℝ) * Real.sqrt (H : ℝ) * (Real.sqrt (H : ℝ) / 10 ^ 4) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (H : ℝ) * (Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ)) / 10 ^ 4 := by ring
    _ = (H : ℝ) ^ 2 / 10 ^ 4 := by rw [hss]; ring

/-! ## THE SPINE

Two compositions. Both are function application plus elementary rearrangement; the elaborator,
not prose, checks that the links line up. -/

/-- **The circle-method half.** The four analytic links deliver a lower bound on the Λ-triple
count with the *margin* `cMaj − κ·cL2` — which is the whole content of the route, and is why
`lowerWith_nonpos_free` matters. -/
theorem lambdaTriple_lower_of_links (P Q : ℕ → ℕ) (cMaj κ cL2 : ℝ) (hκ : 0 ≤ κ)
    (cm : CircleMethodIdentity) (sp : ArcSplit) (mj : MajorArcLower P Q cMaj)
    (mn : MinorSupBound P Q κ) (l2 : SecondMoment cL2) (ho : MinorHolderBound) :
    ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H → (cMaj - κ * cL2) * (H : ℝ) ^ 2 ≤ lambdaTriple H := by
  intro H hodd hH
  have hL : (61 : ℝ) ≤ Real.log (H : ℝ) := log_ge_61 H hH
  have hLpos : (0 : ℝ) < Real.log (H : ℝ) := by linarith
  set C : ℝ := κ * (H : ℝ) / Real.log (H : ℝ) with hC
  have hC0 : 0 ≤ C := by
    rw [hC]; exact div_nonneg (mul_nonneg hκ (Nat.cast_nonneg H)) (le_of_lt hLpos)
  have hCeq : C * (cL2 * (H : ℝ) * Real.log (H : ℝ)) = κ * cL2 * (H : ℝ) ^ 2 := by
    rw [hC]; field_simp
  have hminnorm : ‖minorIntegral H (P H) (Q H)‖ ≤ κ * cL2 * (H : ℝ) ^ 2 :=
    le_trans (ho H (P H) (Q H) C hC0 (mn H hodd hH))
      (by rw [← hCeq]; exact mul_le_mul_of_nonneg_left (l2 H hH) hC0)
  have hre : -(κ * cL2 * (H : ℝ) ^ 2) ≤ (minorIntegral H (P H) (Q H)).re := by
    have h := Complex.abs_re_le_norm (minorIntegral H (P H) (Q H))
    exact (abs_le.mp (le_trans h hminnorm)).1
  have heq : ((lambdaTriple H : ℝ) : ℂ)
      = majorIntegral H (P H) (Q H) + minorIntegral H (P H) (Q H) := by
    rw [cm H, sp H (P H) (Q H)]
  have hsplit : lambdaTriple H
      = (majorIntegral H (P H) (Q H)).re + (minorIntegral H (P H) (Q H)).re := by
    simpa using congrArg Complex.re heq
  have hmaj := mj H hodd hH
  have hring : (cMaj - κ * cL2) * (H : ℝ) ^ 2
      = cMaj * (H : ℝ) ^ 2 - κ * cL2 * (H : ℝ) ^ 2 := by ring
  linarith

/-- **THE SPINE.** The five remaining links plus the budget condition deliver the obligation.
`ArcSplit`, `SecondMoment` and `MinorHolderBound` appear here because the composition is stated
parametrically in `cL2`; the instantiated corollaries below supply them from
`arcSplit_holds`, `secondMoment_holds` and `minorHolder_holds`, so they are **not** hypotheses of
the final theorems. -/
theorem ternaryLogCountLower_of_links (P Q : ℕ → ℕ) (cMaj κ cL2 cPP c₀ : ℝ)
    (hκ : 0 ≤ κ) (hcPP : 0 ≤ cPP) (hbudget : c₀ + κ * cL2 + cPP / 10 ^ 4 ≤ cMaj)
    (cm : CircleMethodIdentity) (sp : ArcSplit) (mj : MajorArcLower P Q cMaj)
    (mn : MinorSupBound P Q κ) (l2 : SecondMoment cL2) (ho : MinorHolderBound)
    (pp : PrimePowerRemoval cPP) :
    TernaryLogCountLowerWith c₀ := by
  intro H hodd hH
  have hH2 : (0 : ℝ) ≤ (H : ℝ) ^ 2 := sq_nonneg _
  have h3 := lambdaTriple_lower_of_links P Q cMaj κ cL2 hκ cm sp mj mn l2 ho H hodd hH
  have hpp := pp H hodd hH
  have h4 : cPP * ((H : ℝ) * Real.sqrt (H : ℝ)) * Real.log (H : ℝ) ^ 2
      ≤ cPP * ((H : ℝ) ^ 2 / 10 ^ 4) := by
    have := mul_le_mul_of_nonneg_left (pp_slack H hH) hcPP
    calc cPP * ((H : ℝ) * Real.sqrt (H : ℝ)) * Real.log (H : ℝ) ^ 2
        = cPP * ((H : ℝ) * Real.sqrt (H : ℝ) * Real.log (H : ℝ) ^ 2) := by ring
      _ ≤ cPP * ((H : ℝ) ^ 2 / 10 ^ 4) := this
  have h1 : c₀ ≤ cMaj - κ * cL2 - cPP / 10 ^ 4 := by linarith
  have h2 : c₀ * (H : ℝ) ^ 2 ≤ (cMaj - κ * cL2 - cPP / 10 ^ 4) * (H : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right h1 hH2
  have h5 : (cMaj - κ * cL2 - cPP / 10 ^ 4) * (H : ℝ) ^ 2
      = (cMaj - κ * cL2) * (H : ℝ) ^ 2 - cPP * ((H : ℝ) ^ 2 / 10 ^ 4) := by ring
  linarith

/-- **The spine, composed with `Reduction.lean`**: the EP1054 chain's one trusted input follows
from the same links. -/
theorem cite_Helfgott_weighted_of_links (P Q : ℕ → ℕ) (cMaj κ cL2 cPP : ℝ)
    (hκ : 0 ≤ κ) (hcPP : 0 ≤ cPP) (hbudget : 0.00026 + κ * cL2 + cPP / 10 ^ 4 ≤ cMaj)
    (cm : CircleMethodIdentity) (sp : ArcSplit) (mj : MajorArcLower P Q cMaj)
    (mn : MinorSupBound P Q κ) (l2 : SecondMoment cL2) (ho : MinorHolderBound)
    (pp : PrimePowerRemoval cPP) :
    Principia.Erdos1054.Cite_Helfgott_weighted :=
  cite_Helfgott_weighted_of_logCount
    (ternaryLogCountLower_iff.mpr
      (ternaryLogCountLower_of_links P Q cMaj κ cL2 cPP 0.00026 hκ hcPP hbudget cm sp mj mn l2
        ho pp))

/-! ## The instantiations

The three discharged links are supplied, so what remains in each statement is exactly the open
mathematics: the circle-method identity, the major-arc main term, the minor-arc sup bound and the
prime-power removal. -/

/-- **`cMaj = 1/2`, `κ = 3/10`, `cPP = 10`.** Budget `0.00026 + 0.42 + 0.001 = 0.42126 ≤ 0.5`.
`cMaj = 1/2` is `24.3 %` below the true main term `0.660162 H²`, so this instantiation is
comfortable on the major-arc side and demands `sup_𝔪‖S‖ ≤ 0.004825 H` at `H = 10^27`. -/
theorem ternaryLogCountLower_of_links_main (P Q : ℕ → ℕ)
    (cm : CircleMethodIdentity) (mj : MajorArcLower P Q (1 / 2))
    (mn : MinorSupBound P Q (3 / 10)) (pp : PrimePowerRemoval 10) :
    TernaryLogCountLower :=
  ternaryLogCountLower_iff.mpr
    (ternaryLogCountLower_of_links P Q (1 / 2) (3 / 10) (7 / 5) 10 0.00026 (by norm_num)
      (by norm_num) (by norm_num) cm arcSplit_holds mj mn secondMoment_holds minorHolder_holds pp)

/-- The same, landing on the EP1054 input. -/
theorem cite_Helfgott_weighted_of_links_main (P Q : ℕ → ℕ)
    (cm : CircleMethodIdentity) (mj : MajorArcLower P Q (1 / 2))
    (mn : MinorSupBound P Q (3 / 10)) (pp : PrimePowerRemoval 10) :
    Principia.Erdos1054.Cite_Helfgott_weighted :=
  cite_Helfgott_weighted_of_logCount (ternaryLogCountLower_of_links_main P Q cm mj mn pp)

/-- **The spine with the numerical input in its own signature.** Identical to
`ternaryLogCountLower_of_links_main` except that the major-arc link is supplied as a *consumer* of
Platt's finite GRH verification, so `PlattGRH` — the one step that is a computation rather than a
theorem — is visible in the type rather than absorbed into `MajorArcLower`. This is the honest shape
of Helfgott's dependency: `ternvin.tex` 363–366 records that the `L`-function computation is used in
the major arcs *and nowhere else*, and the minor arcs use no `L`-function information at all.

**IT DEMONSTRATES NO REDUCTION, AND MUST NOT BE READ AS ONE** (coordinator, 2026-09-29, after a
round-2 auditor flagged the shape). Because `MajorArcFromGRH G P Q c` unfolds to
`G → MajorArcLower P Q c`, taking BOTH it and `G` is strictly *more* demanding than
`ternaryLogCountLower_of_links_main`, and with `G := True` this theorem degenerates to exactly that
one. So the `PlattGRH` slot carries no weight beyond what `MajorArcFromGRH` already carries: nothing
here has been reduced to Platt's computation. What this theorem does is display the shape the final
result must take, which is worth having only because `PlattGRH` will never *be* a Lean theorem — it
is a rigorous-numerics certification, so "analysis + `PlattGRH` as a hypothesis" is the honest
endpoint rather than a defect. **The reduction becomes real only when
`MajorArcFromGRH PlattGRH P Q (1/2)` is itself proved**; until then this theorem is bookkeeping. -/
theorem ternaryLogCountLower_of_links_platt (P Q : ℕ → ℕ)
    (cm : CircleMethodIdentity) (mjG : MajorArcFromGRH PlattGRH P Q (1 / 2)) (grh : PlattGRH)
    (mn : MinorSupBound P Q (3 / 10)) (pp : PrimePowerRemoval 10) :
    TernaryLogCountLower :=
  ternaryLogCountLower_of_links_main P Q cm (mjG grh) mn pp

/-- **The weakest minor-arc hypothesis this arrangement can use**: `cMaj = 13/20`, `κ = 46/100`,
budget `0.00026 + 0.644 + 0.001 = 0.64526 ≤ 0.65`. Now `cMaj` is only `1.5 %` below the true main
term — the major-arc error budget is nearly exhausted — in exchange for a minor-arc demand of
`0.007399 H`, still `8.9×` beyond `MinSum.vinogradov_sup_tight2`. **This is the trade the route
offers, and both ends of it are out of reach at `10^27`.** -/
theorem ternaryLogCountLower_of_links_sharp (P Q : ℕ → ℕ)
    (cm : CircleMethodIdentity) (mj : MajorArcLower P Q (13 / 20))
    (mn : MinorSupBound P Q (46 / 100)) (pp : PrimePowerRemoval 10) :
    TernaryLogCountLower :=
  ternaryLogCountLower_iff.mpr
    (ternaryLogCountLower_of_links P Q (13 / 20) (46 / 100) (7 / 5) 10 0.00026 (by norm_num)
      (by norm_num) (by norm_num) cm arcSplit_holds mj mn secondMoment_holds minorHolder_holds pp)

/-! ## THE ADVERSARIAL PASS, as theorems

Each of these is an attempt to satisfy the spine with something that does no work. They are kept
because the project's most expensive recurring error is a decomposition whose pieces are satisfiable
degenerately, and prose cannot see it. -/

/-- **Attack 1: take every constant to be zero.** It works, and it delivers nothing — the
obligation at a non-positive constant is `ternaryLogCount_nonneg`. So the spine's entire content is
the positive margin `cMaj − κ·cL2 − cPP/10⁴`, and any instantiation must be read as a claim about
that number. -/
theorem lowerWith_nonpos_free {c : ℝ} (hc : c ≤ 0) : TernaryLogCountLowerWith c := by
  intro H _ _
  have h1 : c * (H : ℝ) ^ 2 ≤ 0 := by nlinarith [sq_nonneg ((H : ℝ))]
  linarith [ternaryLogCount_nonneg H]

/-- **Attack 2: make the minor arcs empty.** `MajorArcs 1 1` is the union of the closed balls of
radius `1/2` about the integers, which covers `ℝ`; so at the cutoffs `P = Q = 1` the minor set is
empty. -/
theorem minorSet_one_one : minorSet 1 1 = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro α ⟨-, hnot⟩
  apply hnot
  refine Set.mem_biUnion (show (1 : ℕ) ∈ Set.Icc 1 1 from ⟨le_refl 1, le_refl 1⟩) ?_
  refine Set.mem_iUnion.mpr ⟨round α, ?_⟩
  rw [Metric.mem_closedBall, Real.dist_eq]
  norm_num
  exact abs_sub_round α

/-- **Attack 2, continued: the minor-arc link is then vacuous for every `κ`** — including `κ = 0`
and negative `κ`. So `MinorSupBound` carries content only through the cutoffs, and no type can
enforce Helfgott's design condition that the arcs be *few and narrow*. -/
theorem minorSup_vacuous_at_one_one (κ : ℝ) :
    MinorSupBound (fun _ => 1) (fun _ => 1) κ := by
  intro H _ _ α hα
  rw [minorSet_one_one] at hα
  exact absurd hα (Set.notMem_empty α)

/-- **Attack 2, the verdict: at those cutoffs the split buys nothing.** The major-arc link alone
delivers the entire lower bound on `lambdaTriple`, because the minor integral over the empty set is
`0`. **The arc split is therefore not itself progress.** What makes it progress is a choice of
`P`, `Q` for which the major-arc integral is computable from the singular series *and* the minor
set is most of the circle — a design constraint, stated here rather than hidden. -/
theorem majorLower_at_one_one_is_whole_target (cMaj : ℝ)
    (cm : CircleMethodIdentity) (sp : ArcSplit)
    (mj : MajorArcLower (fun _ => 1) (fun _ => 1) cMaj) :
    ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H → cMaj * (H : ℝ) ^ 2 ≤ lambdaTriple H := by
  intro H hodd hH
  have hzero : minorIntegral H 1 1 = 0 := by rw [minorIntegral, minorSet_one_one]; simp
  have heq : ((lambdaTriple H : ℝ) : ℂ) = majorIntegral H 1 1 + minorIntegral H 1 1 := by
    rw [cm H, sp H 1 1]
  have hsplit : lambdaTriple H = (majorIntegral H 1 1).re + (minorIntegral H 1 1).re := by
    simpa using congrArg Complex.re heq
  rw [hzero] at hsplit
  simp only [Complex.zero_re, add_zero] at hsplit
  rw [hsplit]
  exact mj H hodd hH

/-- **Attack 3: satisfy the minor-arc link with the bound the library gives for free.** It fails by
a factor of at least `3000` at every `H ≥ 10^27`: the only unconditional sup bound on `expSum` is
`H log H` (`expSum_sup_trivial`), and the link demands `κ·H/log H`, which is smaller by
`(log H)²/κ ≥ 3721/κ`. So the link is nowhere near a restatement of something already known. -/
theorem minorSup_demands_saving (H : ℕ) (hH : 10 ^ 27 ≤ H) (κ : ℝ) (hκ1 : κ ≤ 1) :
    3000 * (κ * (H : ℝ) / Real.log (H : ℝ)) ≤ (H : ℝ) * Real.log (H : ℝ) := by
  have hL : (61 : ℝ) ≤ Real.log (H : ℝ) := log_ge_61 H hH
  have hLpos : (0 : ℝ) < Real.log (H : ℝ) := by linarith
  have hHR : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  rw [show 3000 * (κ * (H : ℝ) / Real.log (H : ℝ)) = 3000 * κ * (H : ℝ) / Real.log (H : ℝ) by ring,
    div_le_iff₀ hLpos]
  nlinarith [hL, hHR, hκ1, mul_nonneg hHR (le_of_lt hLpos)]

/-- **Attack 4: let the numerical input be a free rider.** If the major-arc link held with the GRH
verification replaced by an *arbitrary* proposition, then the verification would be doing no work
and could be dropped. The exact analogue of `TwinPrime.Chain.spine_needs_fmmkls`. -/
theorem spine_needs_grh (P Q : ℕ → ℕ) (cMaj : ℝ)
    (h : ∀ G : Prop, MajorArcFromGRH G P Q cMaj) : MajorArcLower P Q cMaj :=
  h True trivial

/-- **Attack 5: drop `Odd H`.** The conclusion is then *false*, not merely stronger: for even `H`
the count is exactly `0` (`Probes.ternaryLogCount_eq_zero_of_even`), so every link's `Odd H`
hypothesis is load-bearing. `0 < H` is required only because at `H = 0` both sides are `0` and the
obligation is vacuously satisfied. -/
theorem lowerWith_needs_odd {c : ℝ} (hc : 0 < c) (H : ℕ) (hE : Even H) (hHpos : 0 < H) :
    ¬ (c * (H : ℝ) ^ 2 ≤ ternaryLogCount H) := by
  rw [ternaryLogCount_eq_zero_of_even hE]
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hHpos
  have : (0 : ℝ) < c * (H : ℝ) ^ 2 := by positivity
  linarith

end Principia.Common.TernaryGoldbach.Spine
