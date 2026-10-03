/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Proofs.Assembly

set_option autoImplicit false

/-!
# EP1054 Theorem 1.4 without `Cite_MV_exceptional`: the two routes

**Status (2026-09-26, round 4):** Route A is DISCHARGED. `Rate/Bridge.lean` proves
`std_GoldbachRate_unconditional : Std_GoldbachRate` from the ported circle method
(`Principia.Common.GoldbachRate`), and with it `lem_AOR_unconditional` and
`thm_SubexpGrowth_unconditional`, so Theorem 1.4 now needs no hypothesis. The rest of this header is
the original design text; "input" below means an input at the time this module was written.

Theorem 1.4 (`thm:subexp-growth`, `Thm_SubexpGrowth`) is the last main theorem that still takes
`Cite_MV_exceptional`. Its proof (`Proofs.Thm14.subexpCore`, EP1054.tex lines 2219–2224) consumes
that input only as `Lem_AnalyticOddRepresentability`, and only through its `LittleO` half at one
fixed `η₀ = c₁/10`: `cnt oddUnrep X ≤ η₀ · X / log₃ X` for large `X`. Density zero of the Goldbach
exceptional set does not give this (it is a *rate*), so the qualitative route that works for
Theorem 1.3 (`Alt.GoldbachRoute`) does not reach Theorem 1.4.

This module isolates the one step and offers two inputs for it. The design study behind it is
`Campaigns/Erdos-1054/THM14-RATE-PLAN.md`.

* `thm_SubexpGrowth_of_lemAOR` — Theorem 1.4 from `Lem_AnalyticOddRepresentability` alone,
  composing the proved links, leaves and discharged inputs exactly as `spine_Thm_SubexpGrowth`
  does. Every other input of that spine is already discharged, so this is the whole remaining
  obligation.

**Route A — a Goldbach rate (discharges the input; no trade).**
* `Std_GoldbachRate` — `#{n ≤ X : n even, not a sum of two primes} ≤ C · X / log X` for large
  `X`, stated with the master's own `countUpTo`/`notSumOfTwoPrimes` (the verbatim copies in
  `Alt.GoldbachRoute`). It is strictly weaker than `Cite_MV_exceptional` (`O(X^{1-c})`) and is
  what the circle-method chain gives once its `ε`-dependence is made explicit: every estimate in
  it is already explicit except one tail of a convergent series (see the plan).
* `cnt_mvSet_le_of_goldbachRate` — the rate transported to `cnt OddRepr.mvSet X` for every real
  `X ≥ 3`.
* `lemAOR_of_mvSet_bound`, `lemAOR_of_goldbachRate` — **both halves** of
  `Lem_AnalyticOddRepresentability`: the rate fits the paper's own bound
  `≪ X^{1-c} + X / log X` through its second term.
* `thm_SubexpGrowth_of_goldbachRate` — **Theorem 1.4 from `Std_GoldbachRate` alone.**
* `std_GoldbachDensZero_of_goldbachRate`, `thm_AlmostLogTail_of_goldbachRate` — the same input
  also gives Theorem 1.3 (through `Alt.GoldbachRoute`).

**Route B — no rate at all (a trade, not a discharge).**
* `lemAOR_of_eventually_R` — if every `n ≥ M` is represented, the odd unrepresented set is finite
  and `Lem_AnalyticOddRepresentability` holds with `cnt ≤ M`.
* `thm_SubexpGrowth_of_fraitureTail`, `thm_SubexpGrowth_of_helfgott` — Theorem 1.4 from
  `Prop_FraitureTail` (every `n ≥ 10^27 + 10^8` is in `𝓡`), hence from
  `Cite_Helfgott_weighted` alone. That swaps Montgomery–Vaughan for Helfgott; it removes no
  trusted input from Theorem 1.4 on its own, but `ep1054_all` already carries Helfgott.

**The other Montgomery–Vaughan consumer.**
* `eq_OddUntouchables_of_goldbachDensZero` — `Std_GoldbachDensZero → Eq_OddUntouchables`. The
  spine takes it from `Cite_MV_exceptional` (`Link_Eq_OddUntouchables`, used by `Prop_ThetaTwo` and
  `Cor_EtaTwo`); it is a density-zero statement. With this and `lemAOR_of_goldbachRate`, both
  spine links that consume `Cite_MV_exceptional` have MV-free replacements.
-/

namespace Principia.Erdos1054.Rate

open Finset Filter Principia.Erdos1054 Principia.Erdos1054.Proofs Principia.Erdos1054.UpperTails

/-! ## 1. Theorem 1.4 from `Lem_AnalyticOddRepresentability` -/

/-- **Theorem 1.4 (`thm:subexp-growth`) from `Lem_AnalyticOddRepresentability` alone.** The
composition is `Spine.spine_Thm_SubexpGrowth`'s, line for line, with every link, leaf and
discharged input supplied by its proof (the same providers `Proofs.ep1054_Thm_SubexpGrowth`
uses); only `v_Lem_AnalyticOddRepresentability` comes from the hypothesis instead of from
`Cite_MV_exceptional`. -/
theorem thm_SubexpGrowth_of_lemAOR (hA : Lem_AnalyticOddRepresentability) : Thm_SubexpGrowth :=
  have v_Lem_FmModulus : Lem_FmModulus := link_Lem_FmModulus leaf_Fact_KmodGeTwo
  have v_Lem_SigmaRate_OddPrime : Lem_SigmaRate_OddPrime :=
    link_Lem_SigmaRate_OddPrime input_Cite_Pollack_Lemma24 input_Std_SiegelWalfisz_dyadic
  have v_Lem_SigmaRate_B2 : Lem_SigmaRate_B2 := link_Lem_SigmaRate_B2 input_Std_sigma_odd_iff
  have v_Lem_SigmaRate : Lem_SigmaRate := And.intro v_Lem_SigmaRate_OddPrime v_Lem_SigmaRate_B2
  have v_Lem_Moment : Lem_Moment := link_Lem_Moment leaf_Eq_Reflection
  have v_Eq_SharpPrimeSum : Eq_SharpPrimeSum := link_Eq_SharpPrimeSum input_Std_Mertens2
  have v_Eq_MovingKernelTail : Eq_MovingKernelTail :=
    link_Eq_MovingKernelTail leaf_Eq_RankinKernel v_Eq_SharpPrimeSum
      leaf_UpperTails_Claim_EulerHigherTerms
  have v_Eq_SharpRoughTargetCount : Eq_SharpRoughTargetCount :=
    link_Eq_SharpRoughTargetCount leaf_Notation_Delta_density input_Std_Mertens3
  have v_Eq_SharpBadSourceCount : Eq_SharpBadSourceCount :=
    link_Eq_SharpBadSourceCount v_Lem_SigmaRate
  have v_BadPairs : UpperTails.Claim_SubexpBadPairs :=
    link_UpperTails_Claim_SubexpBadPairs v_Eq_SharpBadSourceCount v_Eq_SharpRoughTargetCount
  have v_WitnessStructure : UpperTails.Claim_SubexpWitnessStructure :=
    link_UpperTails_Claim_SubexpWitnessStructure v_Lem_FmModulus leaf_Fact_KmodGeTwo
  have v_MovingKernelLowerBound : Eq_MovingKernelLowerBound :=
    link_Eq_MovingKernelLowerBound v_WitnessStructure leaf_UpperTails_Claim_SubexpFltP
      input_Std_Mertens3
  have v_CoprimeCount : UpperTails.Claim_SubexpCoprimeCount :=
    link_UpperTails_Claim_SubexpCoprimeCount leaf_Notation_Delta_density
  have v_LowCofactorSum : UpperTails.Claim_SubexpLowCofactorSum :=
    link_UpperTails_Claim_SubexpLowCofactorSum v_WitnessStructure v_MovingKernelLowerBound
      v_CoprimeCount leaf_UpperTails_Claim_SubexpFltP
  have v_LowCofactor : UpperTails.Claim_SubexpLowCofactor :=
    link_UpperTails_Claim_SubexpLowCofactor v_LowCofactorSum v_Eq_MovingKernelTail
  have v_LargeCofactor : UpperTails.Claim_SubexpLargeCofactor :=
    link_UpperTails_Claim_SubexpLargeCofactor input_Std_Mertens3
  have v_Core : UpperTails.Claim_SubexpCore :=
    link_UpperTails_Claim_SubexpCore v_Eq_SharpRoughTargetCount
      leaf_UpperTails_Claim_RoughNonsquarefree v_BadPairs leaf_UpperTails_Claim_SubexpCofactorOne
      v_LowCofactor v_LargeCofactor v_Lem_Moment hA
  have v_Threshold : UpperTails.Claim_SubexpThreshold :=
    link_UpperTails_Claim_SubexpThreshold leaf_UpperTails_Claim_SubexpLogT
  have v_Eq_SubexpGrowth : Eq_SubexpGrowth := link_Eq_SubexpGrowth v_Core v_Threshold
  And.intro v_Eq_SubexpGrowth (link_Eq_PositiveMomentGrowth v_Eq_SubexpGrowth)

/-! ## 2. Route A: a rate for the binary Goldbach exceptional set -/

/-- **The binary Goldbach exceptional set is `O(X / log X)`.** Stated, like
`Alt.Std_GoldbachDensZero`, over the master's own `countUpTo` and `notSumOfTwoPrimes` (the
verbatim copies in `Alt.GoldbachRoute`; the ported `Principia.Common.Goldbach` versions are the
same constants up to `rfl`), with a natural-number threshold as the master's statements use.

This is the classical Chudakov–Estermann–van der Corput rate, strictly weaker than
`Cite_MV_exceptional` (`O(X^{1-c})`). The circle-method chain proves every estimate it needs with
an explicit `N`-dependence except one convergent-series tail, which has an explicit majorant in
the same file; `Campaigns/Erdos-1054/THM14-RATE-PLAN.md` lists the lemmas to restate. -/
def Std_GoldbachRate : Prop :=
  ∃ C : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    (Alt.countUpTo Alt.notSumOfTwoPrimes X : ℝ) ≤ C * X / Real.log X

/-- `log X / 2 ≤ log ⌊X⌋₊` once `X ≥ 4`: `⌊X⌋₊ ≥ X/2` and `log 2 ≤ (log X)/2`. -/
theorem half_log_le_log_floor (X : ℝ) (hX : 4 ≤ X) :
    Real.log X / 2 ≤ Real.log (⌊X⌋₊ : ℝ) := by
  have hXpos : 0 < X := by linarith
  have hfl : X - 1 < (⌊X⌋₊ : ℝ) := Nat.sub_one_lt_floor X
  have hhalf : X / 2 ≤ (⌊X⌋₊ : ℝ) := by linarith
  have h1 : Real.log (X / 2) ≤ Real.log (⌊X⌋₊ : ℝ) :=
    Real.log_le_log (by positivity) hhalf
  have h2 : Real.log (X / 2) = Real.log X - Real.log 2 :=
    Real.log_div hXpos.ne' (by norm_num)
  have h4 : Real.log 4 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have h42 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith

/-- **The rate, transported to `cnt OddRepr.mvSet X` for every real `X ≥ 3`.** Above
`max X₀ 4` it is the master's count at `⌊X⌋₊` with `⌊X⌋₊ / log ⌊X⌋₊ ≤ 2X / log X`; on the
compact range `[3, max X₀ 4)` the trivial `cnt ≤ X = log X · (X / log X)` is absorbed by the
constant `log (max X₀ 4)`. -/
theorem cnt_mvSet_le_of_goldbachRate (h : Std_GoldbachRate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 3 ≤ X →
      (cnt OddRepr.mvSet X : ℝ) ≤ C * (X / Real.log X) := by
  obtain ⟨C, X₀, hC⟩ := h
  set B : ℝ := max (X₀ : ℝ) 4 with hB
  have hB4 : (4 : ℝ) ≤ B := le_max_right _ _
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨2 * max C 0 + Real.log B, by linarith, fun X hX => ?_⟩
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hd : 0 ≤ X / Real.log X := div_nonneg hXpos.le hlogX.le
  have hsplit : (2 * max C 0 + Real.log B) * (X / Real.log X) =
      2 * max C 0 * (X / Real.log X) + Real.log B * (X / Real.log X) := by ring
  rw [hsplit]
  by_cases hXB : B ≤ X
  · -- the master's range
    have h4X : (4 : ℝ) ≤ X := hB4.trans hXB
    have hX₀X : (X₀ : ℝ) ≤ X := (le_max_left _ _).trans hXB
    have hn₀ : X₀ ≤ ⌊X⌋₊ := Nat.le_floor hX₀X
    have hnX : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hXpos.le
    have hlogn := half_log_le_log_floor X h4X
    have hlogn0 : 0 < Real.log (⌊X⌋₊ : ℝ) := by linarith
    have hcnt : (cnt OddRepr.mvSet X : ℝ) ≤ Alt.countUpTo Alt.notSumOfTwoPrimes ⌊X⌋₊ := by
      have e : cnt OddRepr.mvSet X =
          cnt {m : ℕ | Alt.notSumOfTwoPrimes m} ((⌊X⌋₊ : ℕ) : ℝ) := by
        rw [Alt.setOf_notSumOfTwoPrimes_eq_mvSet]
        unfold cnt
        rw [Nat.floor_natCast]
      rw [e]
      exact_mod_cast Alt.cnt_le_countUpTo Alt.notSumOfTwoPrimes ⌊X⌋₊
    have hrate := hC ⌊X⌋₊ hn₀
    have hstep1 : C * (⌊X⌋₊ : ℝ) / Real.log (⌊X⌋₊ : ℝ) ≤
        max C 0 * (⌊X⌋₊ : ℝ) / Real.log (⌊X⌋₊ : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)) hlogn0.le
    have hstep2 : max C 0 * (⌊X⌋₊ : ℝ) / Real.log (⌊X⌋₊ : ℝ) ≤
        max C 0 * X / (Real.log X / 2) := by
      rw [div_le_div_iff₀ hlogn0 (by linarith)]
      have ha : max C 0 * (⌊X⌋₊ : ℝ) ≤ max C 0 * X := mul_le_mul_of_nonneg_left hnX hC0
      have hb : 0 ≤ max C 0 * X := mul_nonneg hC0 hXpos.le
      exact mul_le_mul ha hlogn (by linarith) hb
    have hstep3 : max C 0 * X / (Real.log X / 2) = 2 * max C 0 * (X / Real.log X) := by
      rw [div_div_eq_mul_div]
      ring
    have hB0 : 0 ≤ Real.log B * (X / Real.log X) := mul_nonneg hlogB hd
    linarith
  · -- the compact range `3 ≤ X < max X₀ 4`
    have hXB' : X ≤ B := le_of_lt (not_le.1 hXB)
    have htriv : (cnt OddRepr.mvSet X : ℝ) ≤ X := by
      have h1 : (cnt OddRepr.mvSet X : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
        exact_mod_cast cnt_le_floor OddRepr.mvSet X
      exact h1.trans (Nat.floor_le hXpos.le)
    have hlogXB : Real.log X ≤ Real.log B := Real.log_le_log hXpos hXB'
    have hXle : X ≤ Real.log B * (X / Real.log X) := by
      rw [mul_div_assoc', le_div_iff₀ hlogX]
      nlinarith [mul_le_mul_of_nonneg_left hlogXB hXpos.le]
    have hA0 : 0 ≤ 2 * max C 0 * (X / Real.log X) := mul_nonneg (by linarith) hd
    linarith

/-- **`Lem_AnalyticOddRepresentability` (both halves) from an `O(X / log X)` bound on the
Goldbach exceptional set.** For odd `n ∉ 𝓡`, `n − 1` is a Goldbach exception or `2p`
(`OddRepr.cnt_oddUnrep_le`), and `π(X) ≤ 8X / log X` (`OddRepr.primeCounting_le`); the sum fits
the paper's bound `C (X^{1-c} + X / log X)` at `c = 1/2` through its second term. The
`o(X / log₃ X)` half is the proved link `link_Lem_AnalyticOddRepresentability_LittleO`. -/
theorem lemAOR_of_mvSet_bound
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 3 ≤ X → (cnt OddRepr.mvSet X : ℝ) ≤ C * (X / Real.log X)) :
    Lem_AnalyticOddRepresentability := by
  obtain ⟨C, hC0, hC⟩ := h
  have hB : Lem_AnalyticOddRepresentability_Bound := by
    refine ⟨1 / 2, by norm_num, C + 8, fun X hX => ?_⟩
    have hXpos : 0 < X := by linarith
    have hd : 0 ≤ X / Real.log X := div_nonneg hXpos.le (Real.log_nonneg (by linarith))
    have hr : 0 ≤ X ^ (1 - (1 / 2 : ℝ)) := Real.rpow_nonneg hXpos.le _
    have h1 := hC X hX
    have h2 := OddRepr.primeCounting_le X hX
    have h3 : (cnt oddUnrep X : ℝ) ≤ cnt OddRepr.mvSet X + Nat.primeCounting ⌊X⌋₊ := by
      exact_mod_cast OddRepr.cnt_oddUnrep_le X
    have h4 : 0 ≤ (C + 8) * X ^ (1 - (1 / 2 : ℝ)) := mul_nonneg (by linarith) hr
    have e : (C + 8) * (X ^ (1 - (1 / 2 : ℝ)) + X / Real.log X) =
        (C + 8) * X ^ (1 - (1 / 2 : ℝ)) + C * (X / Real.log X) + 8 * (X / Real.log X) := by ring
    rw [e]
    linarith
  exact ⟨hB, link_Lem_AnalyticOddRepresentability_LittleO hB⟩

/-- `Lem_AnalyticOddRepresentability` from `Std_GoldbachRate`. -/
theorem lemAOR_of_goldbachRate (h : Std_GoldbachRate) : Lem_AnalyticOddRepresentability :=
  lemAOR_of_mvSet_bound (cnt_mvSet_le_of_goldbachRate h)

/-- **Theorem 1.4 (`thm:subexp-growth`) from `Std_GoldbachRate` alone.** No other hypothesis:
`Cite_MV_exceptional` is not used, and every other input of the spine is discharged. -/
theorem thm_SubexpGrowth_of_goldbachRate (h : Std_GoldbachRate) : Thm_SubexpGrowth :=
  thm_SubexpGrowth_of_lemAOR (lemAOR_of_goldbachRate h)

/-- The rate implies density zero (`Alt.Std_GoldbachDensZero`): `C X / log X ≤ ε X` once
`log X ≥ C / ε`. -/
theorem std_GoldbachDensZero_of_goldbachRate (h : Std_GoldbachRate) :
    Alt.Std_GoldbachDensZero := by
  obtain ⟨C, hC0, hC⟩ := cnt_mvSet_le_of_goldbachRate h
  show DensZero OddRepr.mvSet
  rw [densZero_iff_exists_real]
  intro ε hε
  refine ⟨max 3 (Real.exp (C / ε)), fun X hX => ?_⟩
  have hX3 : (3 : ℝ) ≤ X := (le_max_left _ _).trans hX
  have hXe : Real.exp (C / ε) ≤ X := (le_max_right _ _).trans hX
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog : C / ε ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).2 hXe
  have hCe : C ≤ ε * Real.log X := by
    rw [div_le_iff₀ hε] at hlog
    linarith [mul_comm (Real.log X) ε]
  have h1 := hC X hX3
  have h2 : C * (X / Real.log X) ≤ ε * X := by
    rw [mul_div_assoc', div_le_iff₀ hlogX]
    nlinarith [mul_le_mul_of_nonneg_right hCe hXpos.le]
  linarith

/-- Theorem 1.3 from `Std_GoldbachRate`, through `Alt.thm_AlmostLogTail_of_goldbachDensZero`. -/
theorem thm_AlmostLogTail_of_goldbachRate (h : Std_GoldbachRate) : Thm_AlmostLogTail :=
  Alt.thm_AlmostLogTail_of_goldbachDensZero (std_GoldbachDensZero_of_goldbachRate h)

/-! ## 3. Route B: representability of every large integer (no rate needed) -/

/-- A set all of whose members are `< M` has at most `M` members up to any `X`. -/
theorem cnt_le_of_forall_lt (S : Set ℕ) (M : ℕ) (hS : ∀ n ∈ S, n < M) (X : ℝ) :
    cnt S X ≤ M := by
  classical
  unfold cnt
  refine (Finset.card_le_card ?_).trans (Finset.card_range M).le
  intro n hn
  exact Finset.mem_range.2 (hS n (Finset.mem_filter.1 hn).2)

/-- **`Lem_AnalyticOddRepresentability` from representability of every `n ≥ M`.** The odd
unrepresented integers are then all `< M`, so their count is at most `M ≤ M · X^{1/2}`. -/
theorem lemAOR_of_eventually_R (M : ℕ) (hM : ∀ n : ℕ, M ≤ n → n ∈ R) :
    Lem_AnalyticOddRepresentability := by
  have hB : Lem_AnalyticOddRepresentability_Bound := by
    refine ⟨1 / 2, by norm_num, (M : ℝ), fun X hX => ?_⟩
    have hsub : ∀ n ∈ oddUnrep, n < M := fun n hn => by
      have hn' : Odd n ∧ n ∉ R := hn
      by_contra hlt
      exact hn'.2 (hM n (not_lt.1 hlt))
    have h1 : (cnt oddUnrep X : ℝ) ≤ M := by exact_mod_cast cnt_le_of_forall_lt oddUnrep M hsub X
    have hX1 : (1 : ℝ) ≤ X ^ (1 - (1 / 2 : ℝ)) := Real.one_le_rpow (by linarith) (by norm_num)
    have hd : 0 ≤ X / Real.log X := div_nonneg (by linarith) (Real.log_nonneg (by linarith))
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    calc (cnt oddUnrep X : ℝ) ≤ M := h1
      _ = (M : ℝ) * 1 := (mul_one _).symm
      _ ≤ (M : ℝ) * (X ^ (1 - (1 / 2 : ℝ)) + X / Real.log X) :=
          mul_le_mul_of_nonneg_left (by linarith) hM0
  exact ⟨hB, link_Lem_AnalyticOddRepresentability_LittleO hB⟩

/-- `Lem_AnalyticOddRepresentability` from `Prop_FraitureTail` (every `n ≥ 10^27 + 10^8` is
represented). The threshold is never evaluated. -/
theorem lemAOR_of_fraitureTail (hT : Prop_FraitureTail) : Lem_AnalyticOddRepresentability :=
  lemAOR_of_eventually_R (10 ^ 27 + 10 ^ 8) hT

/-- Theorem 1.4 from `Prop_FraitureTail`. -/
theorem thm_SubexpGrowth_of_fraitureTail (hT : Prop_FraitureTail) : Thm_SubexpGrowth :=
  thm_SubexpGrowth_of_lemAOR (lemAOR_of_fraitureTail hT)

/-- **Theorem 1.4 from `Cite_Helfgott_weighted` alone**, through `ep1054_Prop_FraitureTail`
(Helfgott's weighted ternary bound, with Mathlib's `θ(x) ≤ x log 4` in place of
Rosser–Schoenfeld). This trades Montgomery–Vaughan for Helfgott rather than discharging it. -/
theorem thm_SubexpGrowth_of_helfgott (h : Cite_Helfgott_weighted) : Thm_SubexpGrowth :=
  thm_SubexpGrowth_of_fraitureTail (ep1054_Prop_FraitureTail h)

/-! ## 4. The other place Montgomery–Vaughan enters the spine -/

/-- **`eq:odd-untouchables` from Goldbach density zero.** The spine derives it from
`Cite_MV_exceptional` (`Spine.Link_Eq_OddUntouchables`, feeding `Prop_ThetaTwo` and `Cor_EtaTwo`),
but the statement is `DensZero` of the odd untouchables and the proof
(`ThetaTight.cnt_oddU_le`: `N − 1` is a Goldbach exception or `2p`) needs only density zero of
the exceptions, plus `π(X) ≤ 8X / log X`. -/
theorem eq_OddUntouchables_of_goldbachDensZero (hG : Alt.Std_GoldbachDensZero) :
    Eq_OddUntouchables := by
  have hMV : DensZero ThetaTight.mvSet := hG
  show DensZero ThetaTight.oddU
  rw [densZero_iff_exists_real]
  intro ε hε
  obtain ⟨X₁, hX₁⟩ := hMV.exists_le_mul (half_pos hε)
  refine ⟨max X₁ (max 3 (Real.exp (16 / ε))), fun X hX => ?_⟩
  have hX1 : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hX3 : (3 : ℝ) ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXe : Real.exp (16 / ε) ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hXpos : 0 < X := by linarith
  have h16 : 0 < 16 / ε := div_pos (by norm_num) hε
  have hlog : 16 / ε ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).2 hXe
  have hpi : (Nat.primeCounting ⌊X⌋₊ : ℝ) ≤ 8 * (X / Real.log X) :=
    ThetaTight.primeCounting_le X hX3
  have hdiv : X / Real.log X ≤ X / (16 / ε) := div_le_div_of_nonneg_left hXpos.le h16 hlog
  have heq : X / (16 / ε) = ε / 16 * X := by
    rw [div_div_eq_mul_div]
    ring
  have hmv : (cnt ThetaTight.mvSet X : ℝ) ≤ ε / 2 * X := hX₁ X hX1
  have hcnt : (cnt ThetaTight.oddU X : ℝ) ≤
      cnt ThetaTight.mvSet X + Nat.primeCounting ⌊X⌋₊ := by
    exact_mod_cast ThetaTight.cnt_oddU_le X
  linarith

end Principia.Erdos1054.Rate
