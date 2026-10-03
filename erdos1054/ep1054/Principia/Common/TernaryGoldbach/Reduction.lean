/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Statements.Inputs

set_option autoImplicit false

/-!
# Ternary Goldbach: the smoothing weights come out of the Helfgott input

`Principia.Erdos1054.Cite_Helfgott_weighted` is the **one** trusted input the whole EP1054 chain
still rests on. It is Helfgott's explicit lower bound for the *smoothed* ternary Goldbach sum, and
it carries two functions `η₊`, `η_*` that no formalization can be expected to reconstruct. This
file removes them, replacing the obligation by a statement with **no smoothing functions in it**:

  `TernaryLogCountLower : ∀ odd H ≥ 10^27, 0.00026 · H² ≤ ternaryLogCount H`

where `ternaryLogCount H` is the plain log-weighted count of ternary Goldbach representations of
`H`. Every later phase of the ternary-Goldbach programme targets that, not the smoothed sum.

## Why the weights can be removed, and why that is not cheating

`Cite_Helfgott_weighted` quantifies the weights **existentially** (`∃ ηp ηs`), constrains them
only by their sup norms, and lets them depend on `H` — its own docstring records that this is
*weaker* than Helfgott's theorem, in which `η₊`, `η_*` are fixed once for all `H`. Constant
weights are therefore admissible: taking `ηp ≡ 1.079955` and `ηs ≡ 1.414` saturates both sup
bounds, and the smoothed sum collapses to

  `K · ternaryLogCount H`,     `K = 1.079955² · 1.414 = 1.64915216206335`  (exact, terminating).

So `K · c₀ ≥ 0.000422` is all the reduction needs.

## The constant, and its margin

`0.000422 / K = 0.00025588906209358…`, so `c₀ = 0.000256` clears the bar by `1.83·10⁻⁷`
absolute — `4.34·10⁻⁴` relative — which is real but too thin to be worth carrying. We take

  **`c₀ = 0.00026`**, giving `K · c₀ = 0.000428779562136471 ≥ 0.000422`, a relative margin of
  `+1.6065 %`.

Both numbers are exact rationals (`1.079955`, `1.414`, `0.00026` all terminate in base 10), so
`norm_num` closes the inequality in `ℚ` — the margin does not live in floating point. Checked
twice independently: as `Fraction` arithmetic, and by hand from
`1079955² = (1080000 − 45)² = 1166302802025`.

## The degenerate weighting, and why it fails

The input's weights are existential, so the first thing to try is to satisfy it with weights that do
no work. `ηp = ηs = 0` meets both sup-norm constraints and sends the smoothed sum to `0`, which
fails `0.000422 · H² ≤ 0` for `H ≥ 10^27`; so the input is not vacuous. More is true, and it is
`weightedCount_le`: because every summand of `ternaryLogCount` is non-negative, **no** admissible
weighting — signed, `H`-dependent, adversarial — can exceed `K · ternaryLogCount H`. So no choice
of weights satisfies the input unless the weight-free count is genuinely large. The
degenerate-witness attack on this reduction is refuted by a theorem, not by inspection.
`Probes.lean` carries the corresponding attacks on `ternaryLogCount` itself.

## The reduction is tight, and that is the honest reading of it

`logCount_of_cite_Helfgott_weighted` proves the **converse** with `c = 0.000255`: since every
summand of `ternaryLogCount` is non-negative and `|ηp| ≤ 1.079955`, `|ηs| ≤ 1.414`, *any*
admissible weighting is dominated by `K · ternaryLogCount H`. So

  `LowerWith 0.00026` ⟹ `Cite_Helfgott_weighted` ⟹ `LowerWith 0.000255`

(writing `LowerWith` for `TernaryLogCountLowerWith`), and the two constants differ by a factor
`1.0196`. The input and the weight-free bound are the **same statement up to `K`** — the weights
were never doing mathematical work in the Erdős-1054 chain, only carrying Helfgott's proof *method*
into the statement of the chain's hypothesis. This file is therefore an interface simplification,
not mathematical progress on ternary Goldbach: the analytic content of `TernaryLogCountLower` is
exactly as hard as before, and it is what a later phase has to prove.

## How much slack the new obligation has (a measurement, not a theorem)

The asymptotic for the ternary log-count is `∑_{p+q+r=H} log p log q log r ~ (𝔖(H)/2) H²`, so the
truth is of order `H²`, not `10⁻⁴ H²`. Summing the definition exactly for odd `H` up to `1.5·10⁵`
gives `ternaryLogCount H / H²` between `0.71` and `1.14` — a factor `2700`–`4400` above
`c₀ = 0.00026`. The small constant is an artefact of Helfgott's smoothing and arc accounting, not of
the count being small, so **a future proof of `TernaryLogCountLower` may be extremely lossy**: three
orders of magnitude of the main term may be thrown away and the bound still holds. That is the most
useful thing this reduction tells the programme.

## What `ternaryLogCount` counts

`∑_{p<H} ∑_{q<H} [p+q<H ∧ p,q,H−p−q all odd primes] · log p · log q · log (H−p−q)`.

* **Ordered pairs.** `p` and `q` each run over all of `Finset.range H`, so the representation
  `(3, 5, H−8)` and `(5, 3, H−8)` are counted separately (as they are in Helfgott's sum, and as
  the EP1054 consumer expects).
* **The diagonal is included.** Nothing in the condition forbids `p = q` (so `H = 2p + r` is
  counted once as an ordered pair `(p, p)`), nor `p = H − p − q`, nor `q = H − p − q`.
* `p = 2` is excluded by `Odd p`, as are `q = 2` and `H − p − q = 2`: the sum is over *odd*
  primes, matching `[Helfgott, §7.4]`.
* Under `p + q < H` the natural subtraction `H - p - q` is exact and `≥ 1`, so every surviving
  summand is a product of three non-negative logarithms (`ternaryLogCount_nonneg`).

## The transcription probe

`cite_Helfgott_weighted_iff` is `Iff.rfl`: it pins `weightedCount` — this file's transcription of
Helfgott's smoothed sum — to the sum inside `Cite_Helfgott_weighted` **by definitional equality**,
so a single character out of place (a different cast, `Finset.Iio` for `Finset.range`, a reordered
conjunct, a different `Decidable` instance) fails to compile. `weightedCount_const` and
`logCount_of_cite_Helfgott_weighted` then pin `ternaryLogCount`'s summation condition to
`weightedCount`'s: both are proved through `ite_eq_const_mul` / `ite_le_const_mul`, whose statements
mention the condition **once**, so the two `ite`s must unify.

Nothing here is asserted about ternary Goldbach: `TernaryLogCountLower` is a `def … : Prop`, and
the theorems are implications between it and the existing input.
-/

namespace Principia.Common.TernaryGoldbach

open Principia.Erdos1054

/-! ## The two sums -/

open Classical in
/-- **Helfgott's smoothed ternary sum**, transcribed from `Cite_Helfgott_weighted` verbatim and
pinned to it by `cite_Helfgott_weighted_iff` (`Iff.rfl`). `ηp` plays `η₊` (twice) and `ηs` plays
`η_*`; the scale is `helfgottX H`. -/
noncomputable def weightedCount (H : ℕ) (ηp ηs : ℝ → ℝ) : ℝ :=
  ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H,
    if p + q < H ∧ p.Prime ∧ q.Prime ∧ (H - p - q).Prime ∧ Odd p ∧ Odd q ∧ Odd (H - p - q)
    then Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ) *
      ηp ((p : ℝ) / helfgottX H) * ηp ((q : ℝ) / helfgottX H) *
        ηs (((H - p - q : ℕ) : ℝ) / helfgottX H)
    else 0

open Classical in
/-- **The weight-free ternary log-count.** `weightedCount`'s summand with the three smoothing
factors deleted and everything else identical: the same `Finset.range H` twice, the same condition,
the same casts (including the natural subtraction `H - p - q` under `Real.log`). Ordered pairs;
diagonal included; `2` excluded by `Odd`. -/
noncomputable def ternaryLogCount (H : ℕ) : ℝ :=
  ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H,
    if p + q < H ∧ p.Prime ∧ q.Prime ∧ (H - p - q).Prime ∧ Odd p ∧ Odd q ∧ Odd (H - p - q)
    then Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ)
    else 0

/-- **The transcription probe.** `Cite_Helfgott_weighted` *is* the statement about `weightedCount`,
by definitional equality. If this compiles, `weightedCount` is the input's sum character for
character. -/
theorem cite_Helfgott_weighted_iff :
    Cite_Helfgott_weighted ↔
      ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H →
        ∃ ηp ηs : ℝ → ℝ, (∀ u : ℝ, |ηp u| ≤ 1.079955) ∧ (∀ u : ℝ, |ηs u| ≤ 1.414) ∧
          0.000422 * (H : ℝ) ^ 2 ≤ weightedCount H ηp ηs :=
  Iff.rfl

/-! ## The obligation, with no smoothing functions in it -/

/-- `c · H² ≤ ternaryLogCount H` for every odd `H ≥ 10^27`, with the constant a parameter. -/
def TernaryLogCountLowerWith (c : ℝ) : Prop :=
  ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H → c * (H : ℝ) ^ 2 ≤ ternaryLogCount H

/-- **The next-level-down form of the EP1054 trusted input.** A lower bound on the log-weighted
count of ternary Goldbach representations of `H`, with no smoothing functions.

`c₀ = 0.00026` is chosen so that `1.079955² · 1.414 · c₀ = 0.000428779562136471` clears the
`0.000422` of `Cite_Helfgott_weighted` with a `+1.6065 %` relative margin (the least admissible
constant is `0.000422 / 1.64915216206335 = 0.000255889…`). -/
def TernaryLogCountLower : Prop :=
  ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H → 0.00026 * (H : ℝ) ^ 2 ≤ ternaryLogCount H

theorem ternaryLogCountLower_iff :
    TernaryLogCountLower ↔ TernaryLogCountLowerWith 0.00026 :=
  Iff.rfl

/-- The obligation weakens as the constant drops. -/
theorem lowerWith_mono {c d : ℝ} (hcd : c ≤ d) (h : TernaryLogCountLowerWith d) :
    TernaryLogCountLowerWith c := fun H hodd hH =>
  le_trans (mul_le_mul_of_nonneg_right hcd (sq_nonneg _)) (h H hodd hH)

/-! ## Elementary facts about the summand -/

/-- Three primes have non-negative logarithms, so every surviving summand is `≥ 0`. -/
theorem log_triple_nonneg {H p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : (H - p - q).Prime) :
    (0 : ℝ) ≤ Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ) :=
  mul_nonneg (mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
    (Real.log_nonneg (by exact_mod_cast hq.one_lt.le)))
    (Real.log_nonneg (by exact_mod_cast hr.one_lt.le))

theorem ternaryLogCount_nonneg (H : ℕ) : 0 ≤ ternaryLogCount H := by
  simp only [ternaryLogCount]
  refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => ?_
  split
  · rename_i hc
    obtain ⟨-, hpp, hqq, hrr, -, -, -⟩ := hc
    exact log_triple_nonneg hpp hqq hrr
  · exact le_refl 0

/-! ## Pulling a constant through a guarded summand

Both statements mention the guard `c` **once**, which is what forces the two `ite`s — the one from
`weightedCount` and the one from `ternaryLogCount` — to unify when these are applied. -/

theorem ite_eq_const_mul {c : Prop} [Decidable c] {x y k : ℝ} (h : c → x = k * y) :
    (if c then x else 0) = k * (if c then y else 0) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc, h hc]
  · rw [if_neg hc, if_neg hc, mul_zero]

/-- No sign condition on `k` is needed: when the guard fails both sides are `0`. -/
theorem ite_le_const_mul {c : Prop} [Decidable c] {x y k : ℝ} (h : c → x ≤ k * y) :
    (if c then x else 0) ≤ k * (if c then y else 0) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]
    exact h hc
  · simp only [if_neg hc, mul_zero, le_refl]

/-! ## Constant weights collapse the smoothed sum -/

/-- With constant weights the smoothed sum is a constant multiple of the weight-free one. This is
the whole content of the reduction; the rest is arithmetic on `1.079955² · 1.414`. -/
theorem weightedCount_const (H : ℕ) (a b : ℝ) :
    weightedCount H (fun _ => a) (fun _ => b) = a * a * b * ternaryLogCount H := by
  simp only [weightedCount, ternaryLogCount]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact ite_eq_const_mul fun _ => by ring

/-- Any admissible weighting is dominated by `1.079955² · 1.414` times the weight-free sum. -/
theorem weightedCount_le (H : ℕ) {ηp ηs : ℝ → ℝ} (hbp : ∀ u : ℝ, |ηp u| ≤ 1.079955)
    (hbs : ∀ u : ℝ, |ηs u| ≤ 1.414) :
    weightedCount H ηp ηs ≤ 1.079955 * 1.079955 * 1.414 * ternaryLogCount H := by
  simp only [weightedCount, ternaryLogCount]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  refine ite_le_const_mul (fun hc => ?_)
  obtain ⟨-, hpp, hqq, hrr, -, -, -⟩ := hc
  have hL : (0 : ℝ) ≤ Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ) :=
    log_triple_nonneg hpp hqq hrr
  have hw : ηp ((p : ℝ) / helfgottX H) * ηp ((q : ℝ) / helfgottX H) *
      ηs (((H - p - q : ℕ) : ℝ) / helfgottX H) ≤ 1.079955 * 1.079955 * 1.414 := by
    refine le_trans (le_abs_self _) ?_
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hbp _) (hbp _) (abs_nonneg _) (by norm_num)) (hbs _)
      (abs_nonneg _) (by norm_num)
  calc Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ) *
        ηp ((p : ℝ) / helfgottX H) * ηp ((q : ℝ) / helfgottX H) *
          ηs (((H - p - q : ℕ) : ℝ) / helfgottX H)
      = (Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ)) *
          (ηp ((p : ℝ) / helfgottX H) * ηp ((q : ℝ) / helfgottX H) *
            ηs (((H - p - q : ℕ) : ℝ) / helfgottX H)) := by ring
    _ ≤ (Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ)) *
          (1.079955 * 1.079955 * 1.414) := mul_le_mul_of_nonneg_left hw hL
    _ = 1.079955 * 1.079955 * 1.414 *
          (Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ)) := by ring

/-! ## The reduction -/

/-- **The deliverable.** The EP1054 chain's one trusted input follows from the weight-free lower
bound `0.00026 · H² ≤ ternaryLogCount H`.

The weights are the constants `1.079955` and `1.414`, which saturate the two sup-norm bounds; the
smoothed sum is then `1.64915216206335 · ternaryLogCount H`, and
`1.64915216206335 · 0.00026 = 0.000428779562136471 ≥ 0.000422`. -/
theorem cite_Helfgott_weighted_of_logCount :
    TernaryLogCountLower → Cite_Helfgott_weighted := by
  intro h H hodd hH
  refine ⟨fun _ => 1.079955, fun _ => 1.414, ?_, ?_, ?_⟩
  · intro _
    have habs : |(1.079955 : ℝ)| = 1.079955 := abs_of_nonneg (by norm_num)
    exact habs.le
  · intro _
    have habs : |(1.414 : ℝ)| = 1.414 := abs_of_nonneg (by norm_num)
    exact habs.le
  · have key : 0.000422 * (H : ℝ) ^ 2 ≤ weightedCount H (fun _ => 1.079955) (fun _ => 1.414) := by
      rw [weightedCount_const]
      calc 0.000422 * (H : ℝ) ^ 2
          ≤ 1.079955 * 1.079955 * 1.414 * 0.00026 * (H : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
        _ = 1.079955 * 1.079955 * 1.414 * (0.00026 * (H : ℝ) ^ 2) := by ring
        _ ≤ 1.079955 * 1.079955 * 1.414 * ternaryLogCount H :=
            mul_le_mul_of_nonneg_left (h H hodd hH) (by norm_num)
    exact key

/-- **The converse**, with the constant lowered by the weight product. Since every summand of
`ternaryLogCount` is non-negative and the weights are bounded in sup norm, no admissible weighting
can exceed `1.64915216206335 · ternaryLogCount H`; and
`1.64915216206335 · 0.000255 = 0.00042053380132615… ≤ 0.000422`. -/
theorem logCount_of_cite_Helfgott_weighted (h : Cite_Helfgott_weighted) :
    TernaryLogCountLowerWith 0.000255 := by
  intro H hodd hH
  obtain ⟨ηp, ηs, hbp, hbs, hsum⟩ := h H hodd hH
  refine le_of_mul_le_mul_left ?_ (show (0 : ℝ) < 1.079955 * 1.079955 * 1.414 by norm_num)
  calc 1.079955 * 1.079955 * 1.414 * (0.000255 * (H : ℝ) ^ 2)
      = 1.079955 * 1.079955 * 1.414 * 0.000255 * (H : ℝ) ^ 2 := by ring
    _ ≤ 0.000422 * (H : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
    _ ≤ weightedCount H ηp ηs := hsum
    _ ≤ 1.079955 * 1.079955 * 1.414 * ternaryLogCount H := weightedCount_le H hbp hbs

/-- **The sandwich.** The input sits between the weight-free bound at `0.00026` and the one at
`0.000255`: the two differ by the factor `1.0196`, so removing the smoothing functions costs only
the constant `1.079955² · 1.414`. This is the evidence that the reduction is not a strengthening. -/
theorem cite_Helfgott_weighted_sandwich :
    (TernaryLogCountLowerWith 0.00026 → Cite_Helfgott_weighted) ∧
      (Cite_Helfgott_weighted → TernaryLogCountLowerWith 0.000255) :=
  ⟨cite_Helfgott_weighted_of_logCount, logCount_of_cite_Helfgott_weighted⟩

end Principia.Common.TernaryGoldbach
