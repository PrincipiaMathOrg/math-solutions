/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.GoldbachRate.Harc
import Principia.Common.GoldbachRate.Core
import Principia.Common.SW.Unconditional

/-!
# Goldbach rate: the binary Goldbach exceptional set is `O(X / log X)`

`Principia.Common.Goldbach.GoldbachReduction.almost_all_binary_goldbach_of_mediumPNT` proves that
the even numbers which are not a sum of two primes have density zero. Its proof is a weighted
variance bound on each dyadic block `(X/2, X]` (a Chebyshev count against the main term
`𝔖(n)·r_{X+1}(n) ≥ (X+1)/16`), then a dyadic sum. This module runs the same argument with the
rates of `GoldbachRate.Harc` and `GoldbachRate.Core`:

* `hvar_rate` (R9) — `∑_{n∈(X/2,X]} (repWeight X n − mainTerm X n)² ≤ K X³ / log X`;
* `block_rate` (R10) — `#{n ∈ (X/2, X] : n even, n ≠ p + q} ≤ K X / log X`;
* `count_rate_of_block` (R11) — for any predicate, a block bound `≤ K X / log X` gives
  `#{n ≤ X} ≤ A X / log X` (a dyadic sum: `log(X/4) ≥ ¾ log X` once `X ≥ 256`);
* `goldbach_exceptional_rate_of_mediumPNT` (R12) — **`MediumPNTBound → ∃ C X₀, ∀ X ≥ X₀,
  #{n ≤ X : n even, n ≠ p + q} ≤ C X / log X`**, in the master's own `countUpTo` and
  `notSumOfTwoPrimes`;
* `goldbach_exceptional_rate` — the same with `MediumPNTBound` discharged by
  `Principia.Common.SW.mediumPNTBound`: **unconditional**.

The constant `C` is ineffective (through Siegel–Walfisz). This is the classical
Chudakov–Estermann–van der Corput rate, strictly weaker than Montgomery–Vaughan's `X^{1-c}`.
-/

set_option autoImplicit false
open DirichletCharacter Complex PowerSeries ArithmeticFunction Finset Filter Metric MeasureTheory
open Principia.Common.SW (MediumPNTBound)

namespace Principia.Common.GoldbachRate

open Principia.Common.Goldbach
open Principia.Common.Goldbach.MinSum
open Principia.Common.Goldbach.MinorArc
open Principia.Common.Goldbach.MajorArcMainTerm
open scoped ArithmeticFunction

/-- **R9 (`hvar_rate`): the weighted variance against the main term, with a `1 / log X` rate.**
`∑_{n∈(X/2,X]} (repWeight X n − mainTerm X n)² ≤ K X³ / log X` for all large `X`: the triangle
`(a − b)² ≤ 2(a − c)² + 2(c − b)²` through `Re cmodel(X+1, n)`, with R8 and R5. The donor is
`hvar_of_arc_error`. -/
theorem hvar_rate (hPNT : MediumPNTBound) :
    ∃ K : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X, (GoldbachReduction.repWeight X n - mainTerm X n) ^ 2
        ≤ K * (X : ℝ) ^ 3 / Real.log X := by
  obtain ⟨K₁, X₁, h1⟩ := core_variance_repWeight_rate hPNT
  obtain ⟨K₂, X₂, h2⟩ := harc_rate
  refine ⟨2 * K₁ + 2 * K₂, max X₁ X₂, fun X hX => ?_⟩
  have hc := h1 X (le_trans (le_max_left _ _) hX)
  have ha : ∑ n ∈ Finset.Ioc (X / 2) X,
      ((GoldbachReduction.cmodel (X + 1) n).re - mainTerm X n) ^ 2
      ≤ K₂ * (X : ℝ) ^ 3 / Real.log X := by
    have hh := h2 X (le_trans (le_max_right _ _) hX)
    simpa only [GoldbachReduction.cmodel, mainTerm, Tarithv] using hh
  have hpt : ∀ n ∈ Finset.Ioc (X / 2) X,
      (GoldbachReduction.repWeight X n - mainTerm X n) ^ 2
      ≤ 2 * (GoldbachReduction.repWeight X n - (GoldbachReduction.cmodel (X + 1) n).re) ^ 2
        + 2 * ((GoldbachReduction.cmodel (X + 1) n).re - mainTerm X n) ^ 2 := by
    intro n _
    nlinarith [sq_nonneg (GoldbachReduction.repWeight X n
      - (GoldbachReduction.cmodel (X + 1) n).re
      - ((GoldbachReduction.cmodel (X + 1) n).re - mainTerm X n))]
  calc ∑ n ∈ Finset.Ioc (X / 2) X, (GoldbachReduction.repWeight X n - mainTerm X n) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (X / 2) X,
          (2 * (GoldbachReduction.repWeight X n - (GoldbachReduction.cmodel (X + 1) n).re) ^ 2
            + 2 * ((GoldbachReduction.cmodel (X + 1) n).re - mainTerm X n) ^ 2) :=
        Finset.sum_le_sum hpt
    _ = 2 * ∑ n ∈ Finset.Ioc (X / 2) X,
          (GoldbachReduction.repWeight X n - (GoldbachReduction.cmodel (X + 1) n).re) ^ 2
        + 2 * ∑ n ∈ Finset.Ioc (X / 2) X,
          ((GoldbachReduction.cmodel (X + 1) n).re - mainTerm X n) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * (K₁ * (X : ℝ) ^ 3 / Real.log X) + 2 * (K₂ * (X : ℝ) ^ 3 / Real.log X) := by
        linarith [hc, ha]
    _ = (2 * K₁ + 2 * K₂) * (X : ℝ) ^ 3 / Real.log X := by ring

/-- **R10 (`block_rate`): the Goldbach exceptions in a dyadic block, with a `1 / log X` rate.**
`#{n ∈ (X/2, X] : notSumOfTwoPrimes n} ≤ K X / log X` for all large `X`. For such `n` the weighted
count `repWeight X n` is at most the prime-power contribution (`badRep_le`, `negl_bound`), while
`mainTerm X n ≥ (X+1)/16` (`hmain_bound`); so `|repWeight − mainTerm| ≥ (X+1)/32` and the
Chebyshev count (`card_bad_le_of_sq_sum`) against R9 gives `#bad · X²/1024 ≤ K X³ / log X`. The
donor is the block step of `almost_all_goldbach_of_weighted_variance_indexed`. -/
theorem block_rate (hPNT : MediumPNTBound) [DecidablePred GoldbachReduction.notSumOfTwoPrimes] :
    ∃ K : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((Finset.Ioc (X / 2) X).filter GoldbachReduction.notSumOfTwoPrimes).card : ℝ)
        ≤ K * X / Real.log X := by
  obtain ⟨K, Xv, hv⟩ := hvar_rate hPNT
  obtain ⟨Xm, hXm⟩ := hmain_bound
  obtain ⟨Xn, hXn⟩ := negl_bound (1 / 16) (by norm_num)
  refine ⟨1024 * max K 0, max 2 (max Xm (max Xn Xv)), fun X hX => ?_⟩
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hXmX : Xm ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXnX : Xn ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hX
  have hXvX : Xv ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hX
  have hX2R : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
  have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hδpos : (0 : ℝ) < ((X : ℝ) + 1) / 16 / 2 := by positivity
  have hBbound : ∀ n ∈ (Finset.Ioc (X / 2) X).filter GoldbachReduction.notSumOfTwoPrimes,
      ((X : ℝ) + 1) / 16 / 2 ≤ |GoldbachReduction.repWeight X n - mainTerm X n| := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hn1, hn2⟩, hbad⟩ := hn
    have hRle : GoldbachReduction.repWeight X n ≤ ((X : ℝ) + 1) / 16 / 2 := by
      unfold GoldbachReduction.repWeight
      have h := hXn X hXnX n hn1 hn2
      have hδ' : 1 / 16 * (X : ℝ) / 2 ≤ ((X : ℝ) + 1) / 16 / 2 := by linarith
      exact le_trans (GoldbachReduction.badRep_le (X + 1) n (by omega) hbad.2) (le_trans h hδ')
    have hδm : ((X : ℝ) + 1) / 16 ≤ mainTerm X n := hXm X hXmX n hn1 hn2 hbad.1
    calc ((X : ℝ) + 1) / 16 / 2 ≤ mainTerm X n - GoldbachReduction.repWeight X n := by linarith
      _ ≤ |mainTerm X n - GoldbachReduction.repWeight X n| := le_abs_self _
      _ = |GoldbachReduction.repWeight X n - mainTerm X n| := abs_sub_comm _ _
  have hcard := GoldbachReduction.card_bad_le_of_sq_sum (Finset.Ioc (X / 2) X)
      (fun n => GoldbachReduction.repWeight X n - mainTerm X n) (((X : ℝ) + 1) / 16 / 2)
      (K * (X : ℝ) ^ 3 / Real.log X) hδpos
      ((Finset.Ioc (X / 2) X).filter GoldbachReduction.notSumOfTwoPrimes)
      (Finset.filter_subset _ _) hBbound (hv X hXvX)
  set c : ℝ := ((((Finset.Ioc (X / 2) X).filter GoldbachReduction.notSumOfTwoPrimes).card : ℝ))
    with hcdef
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hδ2 : (X : ℝ) ^ 2 / 1024 ≤ (((X : ℝ) + 1) / 16 / 2) ^ 2 := by nlinarith
  have hK : K * (X : ℝ) ^ 3 / Real.log X ≤ max K 0 * (X : ℝ) ^ 3 / Real.log X :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hlogX.le
  have h1 : c * ((X : ℝ) ^ 2 / 1024) ≤ max K 0 * (X : ℝ) ^ 3 / Real.log X :=
    le_trans (mul_le_mul_of_nonneg_left hδ2 hc0) (hcard.trans hK)
  rw [le_div_iff₀ hlogX] at h1
  rw [le_div_iff₀ hlogX]
  have hX2pos : (0 : ℝ) < (X : ℝ) ^ 2 := by positivity
  have h2 : (c * Real.log X) * (X : ℝ) ^ 2 ≤ (1024 * max K 0 * (X : ℝ)) * (X : ℝ) ^ 2 := by
    calc (c * Real.log X) * (X : ℝ) ^ 2 = 1024 * (c * ((X : ℝ) ^ 2 / 1024) * Real.log X) := by
          ring
      _ ≤ 1024 * (max K 0 * (X : ℝ) ^ 3) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = (1024 * max K 0 * (X : ℝ)) * (X : ℝ) ^ 2 := by ring
  exact le_of_mul_le_mul_right h2 hX2pos

/-- **R11 (`count_rate_of_block`): a dyadic sum with `1 / log` weights.** If every block
`(X/2, X]` with `X ≥ X₀` holds at most `K X / log X` members of `Bad`, then
`#{n ≤ X : Bad n} ≤ A X / log X` for every `X ≥ 2`. Strong induction on `X` through
`[0, X] = [0, X/2] ⊔ (X/2, X]` (`cnt_split`): for `X ≥ B = max X₀ 256`,
`⌊X/2⌋ / log ⌊X/2⌋ ≤ (2/3)·X / log X` because `log(X/4) ≥ ¾ log X`, so `A ≥ 3K` closes the
step; below `B` the trivial `#{n ≤ X} ≤ 2X` is absorbed by `A ≥ 2 log B`. This replaces
`cnt_bound`/`densityZero_of_block`. -/
theorem count_rate_of_block (Bad : ℕ → Prop) [DecidablePred Bad] (K : ℝ) (X₀ : ℕ)
    (hblk : ∀ X : ℕ, X₀ ≤ X →
      (((Finset.Ioc (X / 2) X).filter Bad).card : ℝ) ≤ K * X / Real.log X) :
    ∃ A : ℝ, ∀ X : ℕ, 2 ≤ X →
      (((Finset.range (X + 1)).filter Bad).card : ℝ) ≤ A * X / Real.log X := by
  set B : ℕ := max X₀ 256 with hBdef
  have hB256 : 256 ≤ B := le_max_right _ _
  have hBR : (256 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB256
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  set A : ℝ := 3 * max K 0 + 2 * Real.log B with hAdef
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hKA : K ≤ A / 3 := by
    have := le_max_left K 0
    rw [hAdef]; linarith
  have hBA : 2 * Real.log B ≤ A := by rw [hAdef]; linarith
  have hlog256 : Real.log 256 = 4 * Real.log 4 := by
    rw [show (256 : ℝ) = 4 ^ 4 by norm_num, Real.log_pow]; norm_num
  refine ⟨A, ?_⟩
  intro X
  induction X using Nat.strong_induction_on with
  | _ X IH =>
    intro hX2
    have hX2R : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
    have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
    have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
    by_cases hXB : B ≤ X
    · -- the recursive range
      have hX0 : X₀ ≤ X := le_trans (le_max_left _ _) hXB
      have hX256 : 256 ≤ X := le_trans hB256 hXB
      have hX256R : (256 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX256
      have hmX : X / 2 < X := Nat.div_lt_self (by omega) (by norm_num)
      have hm2 : 2 ≤ X / 2 := by omega
      have hIH := IH (X / 2) hmX hm2
      have hb := hblk X hX0
      rw [GoldbachReduction.cnt_split Bad X]
      push_cast
      have hmR : ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) / 2 := by
        have h : 2 * (X / 2) ≤ X := Nat.mul_div_le X 2
        have h' : (2 : ℝ) * ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast h
        linarith
      have hmR' : (X : ℝ) / 4 ≤ ((X / 2 : ℕ) : ℝ) := by
        have h : X ≤ 4 * (X / 2) := by omega
        have h' : (X : ℝ) ≤ 4 * ((X / 2 : ℕ) : ℝ) := by exact_mod_cast h
        linarith
      have hmpos : (0 : ℝ) < ((X / 2 : ℕ) : ℝ) := by linarith
      have hlogm : (3 / 4) * Real.log X ≤ Real.log ((X / 2 : ℕ) : ℝ) := by
        have h1 : Real.log ((X : ℝ) / 4) ≤ Real.log ((X / 2 : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) hmR'
        have h2 : Real.log ((X : ℝ) / 4) = Real.log X - Real.log 4 :=
          Real.log_div hXpos.ne' (by norm_num)
        have h3 : Real.log 256 ≤ Real.log X := Real.log_le_log (by norm_num) hX256R
        linarith
      have hlogmpos : 0 < Real.log ((X / 2 : ℕ) : ℝ) := by linarith
      have hratio : A * ((X / 2 : ℕ) : ℝ) / Real.log ((X / 2 : ℕ) : ℝ)
          ≤ (2 / 3) * (A * X / Real.log X) := by
        rw [div_le_iff₀ hlogmpos]
        have hAX : 0 ≤ A * X / Real.log X := div_nonneg (mul_nonneg hA0 hXpos.le) hlogX.le
        calc A * ((X / 2 : ℕ) : ℝ) ≤ A * ((X : ℝ) / 2) := mul_le_mul_of_nonneg_left hmR hA0
          _ = (2 / 3) * (A * X / Real.log X) * ((3 / 4) * Real.log X) := by
              rw [show (2 / 3 : ℝ) * (A * X / Real.log X) * ((3 / 4) * Real.log X)
                  = (1 / 2) * (A * X) * (Real.log X / Real.log X) by ring,
                div_self hlogX.ne']
              ring
          _ ≤ (2 / 3) * (A * X / Real.log X) * Real.log ((X / 2 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hlogm (by positivity)
      have hKX : K * X / Real.log X ≤ (1 / 3) * (A * X / Real.log X) := by
        rw [show (1 / 3 : ℝ) * (A * X / Real.log X) = (A / 3) * X / Real.log X by ring]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKA hXpos.le) hlogX.le
      have hsum : (2 / 3) * (A * X / Real.log X) + (1 / 3) * (A * X / Real.log X)
          = A * X / Real.log X := by ring
      linarith [hIH, hb, hratio, hKX]
    · -- the finite range `2 ≤ X < B`
      have hXB' : (X : ℝ) ≤ (B : ℝ) := by exact_mod_cast (le_of_lt (not_le.mp hXB))
      have hcard : (((Finset.range (X + 1)).filter Bad).card : ℝ) ≤ (X : ℝ) + 1 := by
        have h := Finset.card_filter_le (Finset.range (X + 1)) Bad
        simp only [Finset.card_range] at h
        exact_mod_cast h
      have hlogXB : Real.log X ≤ Real.log B := Real.log_le_log hXpos hXB'
      rw [le_div_iff₀ hlogX]
      calc (((Finset.range (X + 1)).filter Bad).card : ℝ) * Real.log X
          ≤ ((X : ℝ) + 1) * Real.log X := mul_le_mul_of_nonneg_right hcard hlogX.le
        _ ≤ (2 * (X : ℝ)) * Real.log B := by
            apply mul_le_mul (by linarith) hlogXB hlogX.le (by positivity)
        _ = (2 * Real.log B) * X := by ring
        _ ≤ A * X := mul_le_mul_of_nonneg_right hBA hXpos.le

/-- **R12: the binary Goldbach exceptional set is `O(X / log X)`, from `MediumPNTBound`.**
`#{n ≤ X : n even, n ≠ p + q} ≤ C X / log X` for all `X ≥ 2`, stated with the master's own
`countUpTo` and `notSumOfTwoPrimes` (those of `GoldbachReduction`). R10 and R11. -/
theorem goldbach_exceptional_rate_of_mediumPNT (hPNT : MediumPNTBound) :
    ∃ C : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (GoldbachReduction.countUpTo GoldbachReduction.notSumOfTwoPrimes X : ℝ)
        ≤ C * X / Real.log X := by
  classical
  obtain ⟨K, X₀, hblk⟩ := block_rate hPNT
  obtain ⟨A, hA⟩ := count_rate_of_block GoldbachReduction.notSumOfTwoPrimes K X₀ hblk
  refine ⟨A, 2, fun X hX => ?_⟩
  have h := hA X hX
  unfold GoldbachReduction.countUpTo
  exact h

/-- **The binary Goldbach exceptional set is `O(X / log X)`, unconditionally.** R12 with
`MediumPNTBound` discharged by `Principia.Common.SW.mediumPNTBound` (the ported PNT+
`MediumPNT`). The constant is ineffective (Siegel–Walfisz). -/
theorem goldbach_exceptional_rate :
    ∃ C : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (GoldbachReduction.countUpTo GoldbachReduction.notSumOfTwoPrimes X : ℝ)
        ≤ C * X / Real.log X :=
  goldbach_exceptional_rate_of_mediumPNT Principia.Common.SW.mediumPNTBound

end Principia.Common.GoldbachRate
