/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Goldbach.MinSum

/-!
# Almost-all binary Goldbach, `Vaughan`: Vaughan's identity and the Vinogradov minor-arc sup bound `vinogradov_sup`

Ported **verbatim** from the circle-method half of the comparator-certified master
`GoldbachChainMaster.lean` (PNT+ workspace, lines 17487–19846; there
`#print axioms GoldbachChain.GoldbachReduction.almost_all_binary_goldbach_proven =
[propext, Classical.choice, Quot.sound]`, built on Mathlib `db127794`, one day from ours). The
master's lines 1–15806 are the Siegel–Walfisz master, ported separately as `Principia.Common.SW`
and not duplicated here. The master imported `Mathlib` and two PNT+ modules; here the imports are
narrowed, the namespace `GoldbachChain` is `Principia.Common.Goldbach`, and the one Siegel–Walfisz
input carries the SW port's hypothesis `MediumPNTBound` (see `Principia.Common.Goldbach.Reduction`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DirichletCharacter Complex PowerSeries ArithmeticFunction Finset Filter Metric MeasureTheory

namespace Principia.Common.Goldbach
set_option maxHeartbeats 1000000
open Finset

namespace MinSum
open Finset

section VaughanDecomposition

open ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Vaughan's identity (self-contained copy of `Vaughan.vaughan_identity` from
    `VaughanIdentity.lean`, re-verified here so this file stays standalone). -/
lemma vaughan_identity (a b : ArithmeticFunction ℝ) :
    Λ = a * ArithmeticFunction.log - a * b * (ζ : ArithmeticFunction ℝ) + b
      + ((μ : ArithmeticFunction ℝ) - a) * (Λ - b) * (ζ : ArithmeticFunction ℝ) := by
  have hlog : (ζ : ArithmeticFunction ℝ) * Λ = ArithmeticFunction.log := zeta_mul_vonMangoldt
  have hμζ : ((μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) = 1 :=
    coe_moebius_mul_coe_zeta
  rw [← hlog]
  linear_combination (b - Λ) * hμζ

/-- **The Vaughan sum decomposition**: `∑_{n≤N} Λ(n)·w(n) = S₁ − S₂ + S₃ + S₄`,
    each `Sᵢ` a convolution sum ready for the hyperbola unfolding
    (`sum_Ioc_mul_weight`) and then Type I / Abel / Type II. -/
lemma vaughan_sum_decomposition (a b : ArithmeticFunction ℝ) (w : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * w n
      = (∑ n ∈ Finset.Ioc 0 N, (((a * ArithmeticFunction.log) n : ℝ) : ℂ) * w n)
        - (∑ n ∈ Finset.Ioc 0 N, (((a * b * (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * w n)
        + (∑ n ∈ Finset.Ioc 0 N, ((b n : ℝ) : ℂ) * w n)
        + (∑ n ∈ Finset.Ioc 0 N,
            (((((μ : ArithmeticFunction ℝ) - a) * (Λ - b) * (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ)
              * w n) := by
  have hpt : ∀ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * w n
      = (((a * ArithmeticFunction.log) n : ℝ) : ℂ) * w n
        - (((a * b * (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * w n
        + ((b n : ℝ) : ℂ) * w n
        + (((((μ : ArithmeticFunction ℝ) - a) * (Λ - b) * (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ)
            * w n := by
    intro n _
    have h1 : (Λ : ArithmeticFunction ℝ) n
        = (a * ArithmeticFunction.log) n - (a * b * (ζ : ArithmeticFunction ℝ)) n + b n
          + (((μ : ArithmeticFunction ℝ) - a) * (Λ - b) * (ζ : ArithmeticFunction ℝ)) n := by
      conv_lhs => rw [vaughan_identity a b]
      have e1 : (a * ArithmeticFunction.log - a * b * (ζ : ArithmeticFunction ℝ) + b
          + ((μ : ArithmeticFunction ℝ) - a) * (Λ - b) * (ζ : ArithmeticFunction ℝ))
          = ((a * ArithmeticFunction.log + -(a * b * (ζ : ArithmeticFunction ℝ))) + b)
            + ((μ : ArithmeticFunction ℝ) - a) * (Λ - b) * (ζ : ArithmeticFunction ℝ) := by
        ring
      rw [e1, ArithmeticFunction.add_apply, ArithmeticFunction.add_apply,
        ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply]
      ring
    rw [h1]
    push_cast
    ring
  rw [Finset.sum_congr rfl hpt]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Truncation of an arithmetic function to `n ≤ U` (the Vaughan `a`, `b` pieces). -/
noncomputable def truncate (f : ArithmeticFunction ℝ) (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then f n else 0, by
    split
    · exact f.map_zero
    · rfl⟩

@[simp] lemma truncate_apply (f : ArithmeticFunction ℝ) (U n : ℕ) :
    truncate f U n = if n ≤ U then f n else 0 := rfl

/-- The truncated Möbius is sup-bounded by 1. -/
lemma abs_truncate_moebius_le_one (U n : ℕ) :
    |truncate (μ : ArithmeticFunction ℝ) U n| ≤ 1 := by
  rw [truncate_apply]
  split
  · have h := abs_moebius_le_one (n := n)
    rw [ArithmeticFunction.intCoe_apply]
    calc |((μ n : ℤ) : ℝ)| = ((|μ n| : ℤ) : ℝ) := by rw [Int.cast_abs]
      _ ≤ 1 := by exact_mod_cast h
  · simp

lemma truncate_vonMangoldt_nonneg (V n : ℕ) : 0 ≤ truncate Λ V n := by
  rw [truncate_apply]
  split
  · exact vonMangoldt_nonneg
  · exact le_refl 0

lemma truncate_vonMangoldt_le (V n : ℕ) : truncate Λ V n ≤ Λ n := by
  rw [truncate_apply]
  split
  · exact le_refl _
  · exact vonMangoldt_nonneg

/-- **The S₂ coefficient bound**: the Vaughan `a·b` coefficients are log-bounded,
    `|(a∗b)(t)| ≤ log t` (via `|μ| ≤ 1`, `0 ≤ Λ_trunc ≤ Λ`, and `∑_{d∣t} Λ(d) = log t`). -/
lemma abs_truncate_mul_le_log (U V t : ℕ) :
    |(truncate (μ : ArithmeticFunction ℝ) U * truncate Λ V) t| ≤ Real.log t := by
  rw [ArithmeticFunction.mul_apply]
  calc |∑ x ∈ t.divisorsAntidiagonal,
        truncate (μ : ArithmeticFunction ℝ) U x.1 * truncate Λ V x.2|
      ≤ ∑ x ∈ t.divisorsAntidiagonal,
        |truncate (μ : ArithmeticFunction ℝ) U x.1 * truncate Λ V x.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ t.divisorsAntidiagonal, Λ x.2 := by
        apply Finset.sum_le_sum
        intro x _
        rw [abs_mul]
        have h1 := abs_truncate_moebius_le_one U x.1
        have h2 : |truncate Λ V x.2| = truncate Λ V x.2 :=
          abs_of_nonneg (truncate_vonMangoldt_nonneg V x.2)
        calc |truncate (μ : ArithmeticFunction ℝ) U x.1| * |truncate Λ V x.2|
            ≤ 1 * |truncate Λ V x.2| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          _ = truncate Λ V x.2 := by rw [one_mul, h2]
          _ ≤ Λ x.2 := truncate_vonMangoldt_le V x.2
    _ = ∑ d ∈ t.divisors, Λ d := Nat.sum_divisorsAntidiagonal' (f := fun _ e => Λ e)
    _ = Real.log t := vonMangoldt_sum

/-- **The regrouping**: `∑_{n≤N} (f∗g)(n)w(n) = ∑_{d≤N} f(d)·∑_{m≤N/d} g(m)w(dm)` —
    each Vaughan piece becomes per-`d` inner sums in exp-sum shape
    (with `w n = e(nα)` the inner sum is `∑_{m≤N/d} g(m)e(m·(dα))`). -/
lemma sum_Ioc_mul_weight_eq_sum_sum (f g : ArithmeticFunction ℝ) (w : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, ((f * g) n : ℂ) * w n
      = ∑ d ∈ Finset.Ioc 0 N, (f d : ℂ) *
          ∑ m ∈ Finset.Ioc 0 (N / d), (g m : ℂ) * w (d * m) := by
  rw [sum_Ioc_mul_weight, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.mem_Ioc] at hd
  have hset : (Finset.Ioc 0 N).filter (fun m => d * m ≤ N) = Finset.Ioc 0 (N / d) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      refine ⟨h1, ?_⟩
      rw [Nat.le_div_iff_mul_le hd.1]
      rwa [mul_comm]
    · rintro ⟨h1, h2⟩
      have h3 : m * d ≤ N := (Nat.le_div_iff_mul_le hd.1).mp h2
      refine ⟨⟨h1, ?_⟩, by rwa [mul_comm] at h3⟩
      calc m ≤ N / d := h2
        _ ≤ N := Nat.div_le_self N d
  calc ∑ m ∈ Finset.Ioc 0 N,
        (if d * m ≤ N then (f d : ℂ) * (g m : ℂ) * w (d * m) else 0)
      = ∑ m ∈ (Finset.Ioc 0 N).filter (fun m => d * m ≤ N),
          (f d : ℂ) * (g m : ℂ) * w (d * m) := (Finset.sum_filter _ _).symm
    _ = ∑ m ∈ Finset.Ioc 0 (N / d), (f d : ℂ) * (g m : ℂ) * w (d * m) := by rw [hset]
    _ = (f d : ℂ) * ∑ m ∈ Finset.Ioc 0 (N / d), (g m : ℂ) * w (d * m) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun m _ => by ring)

/-- **The dyadic N/h-cap workhorse (Vaughan Lemma 2.2 final form)**. -/
lemma dyadic_cap_sum_le (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (N H : ℕ) :
    ∑ h ∈ Finset.Ioc 0 H,
      (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then ((N / h : ℕ) : ℝ)
       else min ((N / h : ℕ) : ℝ) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|)))
      ≤ ((Nat.log 2 H + 1 : ℕ) : ℝ) * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
        + 32 * H * (1 + Real.log (2 * q)) + 4 * N := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hL0 : (0 : ℝ) ≤ 1 + Real.log (2 * q) := by
    have : (0 : ℝ) ≤ Real.log (2 * q) := Real.log_nonneg (by linarith)
    linarith
  set L : ℝ := 1 + Real.log (2 * q) with hLdef
  rcases Nat.eq_zero_or_pos H with hH0 | hH1
  · subst hH0
    simp only [Finset.Ioc_self, Finset.sum_empty]
    push_cast
    have h2 : (0 : ℝ) ≤ 4 * q * L := mul_nonneg (by positivity) hL0
    have h4 : (0 : ℝ) ≤ 8 * N / q := by positivity
    have h6 : (0 : ℝ) ≤ ((Nat.log 2 0 : ℝ) + 1) * (8 * N / q + 4 * q * L) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  set T : ℕ := Nat.log 2 H + 1 with hT
  have h2T : (2 : ℕ) ^ T ≤ 2 * H := by
    rw [hT, pow_succ, mul_comm]
    have := Nat.pow_log_le_self 2 (by omega : H ≠ 0)
    omega
  set w : ℕ → ℝ := fun h =>
    (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then ((N / h : ℕ) : ℝ)
     else min ((N / h : ℕ) : ℝ) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) with hw
  set wt : ℕ → ℕ → ℝ := fun t h =>
    (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then ((N / 2 ^ t : ℕ) : ℝ)
     else min ((N / 2 ^ t : ℕ) : ℝ) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) with hwt
  have hwt0 : ∀ t h, 0 ≤ wt t h := by
    intro t h
    rw [hwt]
    dsimp only
    split
    · positivity
    · exact le_min (by positivity) (by positivity)
  have hww : ∀ h ∈ Finset.Ioc 0 H, w h ≤ wt (Nat.log 2 h) h := by
    intro h hh
    simp only [Finset.mem_Ioc] at hh
    have hple : 2 ^ Nat.log 2 h ≤ h := Nat.pow_log_le_self 2 (by omega)
    have hdivle : (N / h : ℕ) ≤ N / 2 ^ Nat.log 2 h := Nat.div_le_div_left hple (by positivity)
    have hcast : ((N / h : ℕ) : ℝ) ≤ ((N / 2 ^ Nat.log 2 h : ℕ) : ℝ) := by exact_mod_cast hdivle
    rw [hw, hwt]
    dsimp only
    split
    · exact hcast
    · exact min_le_min hcast le_rfl
  have hsum1 : ∑ h ∈ Finset.Ioc 0 H, w h
      ≤ ∑ t ∈ Finset.range T, ∑ h ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t), wt t h := by
    have hcover : Finset.Ioc 0 H ⊆
        (Finset.range T).biUnion (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)) := by
      intro h hh
      simp only [Finset.mem_Ioc] at hh
      rw [Finset.mem_biUnion]
      refine ⟨Nat.log 2 h, ?_, ?_⟩
      · rw [Finset.mem_range, hT]
        have hlog : Nat.log 2 h ≤ Nat.log 2 H := Nat.log_mono_right hh.2
        omega
      · rw [Finset.mem_Ico]
        constructor
        · exact Nat.pow_log_le_self 2 (by omega)
        · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) h
          rw [pow_succ] at this
          omega
    have hdisj : (↑(Finset.range T) : Set ℕ).PairwiseDisjoint
        (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)) := by
      intro t₁ _ t₂ _ hne
      apply Finset.disjoint_left.mpr
      intro h h1 h2
      simp only [Finset.mem_Ico] at h1 h2
      rcases Nat.lt_or_ge t₁ t₂ with hlt | hge
      · have : (2 : ℕ) ^ (t₁ + 1) ≤ 2 ^ t₂ := Nat.pow_le_pow_right (by norm_num) hlt
        rw [pow_succ] at this
        omega
      · have hlt2 : t₂ < t₁ := lt_of_le_of_ne hge (Ne.symm hne)
        have : (2 : ℕ) ^ (t₂ + 1) ≤ 2 ^ t₁ := Nat.pow_le_pow_right (by norm_num) hlt2
        rw [pow_succ] at this
        omega
    calc ∑ h ∈ Finset.Ioc 0 H, w h
        ≤ ∑ h ∈ Finset.Ioc 0 H, wt (Nat.log 2 h) h := Finset.sum_le_sum hww
      _ ≤ ∑ h ∈ (Finset.range T).biUnion (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)),
            wt (Nat.log 2 h) h :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover (fun h _ _ => hwt0 _ h)
      _ = ∑ t ∈ Finset.range T, ∑ h ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
            wt (Nat.log 2 h) h := Finset.sum_biUnion hdisj
      _ = ∑ t ∈ Finset.range T, ∑ h ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t), wt t h := by
          apply Finset.sum_congr rfl
          intro t _
          apply Finset.sum_congr rfl
          intro h hh
          simp only [Finset.mem_Ico] at hh
          have hlog : Nat.log 2 h = t := by
            apply Nat.log_eq_of_pow_le_of_lt_pow hh.1
            rw [pow_succ]
            omega
          rw [hlog]
  have hblock : ∀ t : ℕ, ∑ h ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t), wt t h
      ≤ 8 * N / q + 16 * L * (2 : ℝ) ^ t + 2 * N / (2 : ℝ) ^ t + 4 * q * L := by
    intro t
    have happ := range_min_sum_le a q hq ha α hα ((N / 2 ^ t : ℕ) : ℝ) (by positivity)
      (2 ^ t) (2 ^ t)
    have hq2pos : (0 : ℝ) < ((q / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < q / 2)
    have hcast1 : (((2 ^ t) / (q / 2) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ t * (4 / q) + 1 := by
      have h3 : (q : ℝ) ≤ 4 * ((q / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : q ≤ 4 * (q / 2))
      have hinv : 1 / ((q / 2 : ℕ) : ℝ) ≤ 4 / (q : ℝ) := by
        rw [div_le_div_iff₀ hq2pos hqR]
        linarith
      have h1 : (((2 ^ t) / (q / 2) : ℕ) : ℝ) ≤ ((2 ^ t : ℕ) : ℝ) / ((q / 2 : ℕ) : ℝ) :=
        Nat.cast_div_le
      have h5 : ((2 ^ t : ℕ) : ℝ) / ((q / 2 : ℕ) : ℝ)
          = ((2 ^ t : ℕ) : ℝ) * (1 / ((q / 2 : ℕ) : ℝ)) := by ring
      have h6 : ((2 ^ t : ℕ) : ℝ) * (1 / ((q / 2 : ℕ) : ℝ)) ≤ ((2 ^ t : ℕ) : ℝ) * (4 / q) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      have h7 : (((2 ^ t) / (q / 2) + 1 : ℕ) : ℝ) = (((2 ^ t) / (q / 2) : ℕ) : ℝ) + 1 := by
        push_cast
        ring
      have h8 : ((2 ^ t : ℕ) : ℝ) = (2 : ℝ) ^ t := by push_cast; ring
      rw [h7]
      rw [h8] at h5 h6
      rw [h8] at h1
      linarith [h1, h5, h6]
    have hcast2 : ((N / 2 ^ t : ℕ) : ℝ) ≤ (N : ℝ) / (2 : ℝ) ^ t := by
      have h9 := Nat.cast_div_le (m := N) (n := 2 ^ t) (α := ℝ)
      push_cast at h9
      exact h9
    have hnn2 : (0 : ℝ) ≤ 2 * ((N / 2 ^ t : ℕ) : ℝ) + 4 * q * L := by
      have : (0 : ℝ) ≤ 4 * q * L := mul_nonneg (by positivity) hL0
      positivity
    have h2t : ((2 : ℝ) ^ t) ≠ 0 := by positivity
    have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
    calc ∑ h ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t), wt t h
        ≤ (((2 ^ t) / (q / 2) + 1 : ℕ) : ℝ) * (2 * ((N / 2 ^ t : ℕ) : ℝ) + 4 * q * L) := happ
      _ ≤ ((2 : ℝ) ^ t * (4 / q) + 1) * (2 * ((N : ℝ) / (2 : ℝ) ^ t) + 4 * q * L) := by
          apply mul_le_mul hcast1 _ hnn2 (by positivity)
          have h10 : 2 * ((N / 2 ^ t : ℕ) : ℝ) ≤ 2 * ((N : ℝ) / (2 : ℝ) ^ t) := by linarith
          linarith
      _ = 8 * N / q + 16 * L * (2 : ℝ) ^ t + 2 * N / (2 : ℝ) ^ t + 4 * q * L := by
          field_simp
          ring
  have hgeo1 : ∑ t ∈ Finset.range T, (2 : ℝ) ^ t ≤ (2 : ℝ) ^ T := by
    have heq : ((2 : ℝ) ^ T - 1) / (2 - 1) = (2 : ℝ) ^ T - 1 := by norm_num
    rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1), heq]
    have : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
    linarith
  have hgeo2 : ∑ t ∈ Finset.range T, (1 / (2 : ℝ)) ^ t ≤ 2 := by
    have heq : ((1 / 2 : ℝ) ^ T - 1) / (1 / 2 - 1) = 2 * (1 - (1 / 2 : ℝ) ^ T) := by ring
    rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1), heq]
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ T := by positivity
    linarith
  have hsum2 : ∑ t ∈ Finset.range T,
      (8 * (N : ℝ) / q + 16 * L * (2 : ℝ) ^ t + 2 * N / (2 : ℝ) ^ t + 4 * q * L)
      ≤ (T : ℝ) * (8 * N / q + 4 * q * L) + 16 * L * (2 : ℝ) ^ T + 4 * N := by
    have hsplit : ∀ t ∈ Finset.range T,
        8 * (N : ℝ) / q + 16 * L * (2 : ℝ) ^ t + 2 * N / (2 : ℝ) ^ t + 4 * q * L
        = (8 * (N : ℝ) / q + 4 * q * L)
          + (16 * L * (2 : ℝ) ^ t + 2 * N * (1 / (2 : ℝ)) ^ t) := by
      intro t _
      have hp : (1 / (2 : ℝ)) ^ t = 1 / (2 : ℝ) ^ t := by
        rw [div_pow, one_pow]
      rw [hp]
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      nsmul_eq_mul]
    have h1 : 16 * L * ∑ t ∈ Finset.range T, (2 : ℝ) ^ t ≤ 16 * L * (2 : ℝ) ^ T :=
      mul_le_mul_of_nonneg_left hgeo1 (by linarith)
    have h2 : 2 * (N : ℝ) * ∑ t ∈ Finset.range T, (1 / (2 : ℝ)) ^ t ≤ 2 * N * 2 :=
      mul_le_mul_of_nonneg_left hgeo2 (by positivity)
    linarith
  have h2TR : (2 : ℝ) ^ T ≤ 2 * H := by exact_mod_cast h2T
  calc ∑ h ∈ Finset.Ioc 0 H, w h
      ≤ ∑ t ∈ Finset.range T, ∑ h ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t), wt t h := hsum1
    _ ≤ ∑ t ∈ Finset.range T,
        (8 * (N : ℝ) / q + 16 * L * (2 : ℝ) ^ t + 2 * N / (2 : ℝ) ^ t + 4 * q * L) :=
        Finset.sum_le_sum (fun t _ => hblock t)
    _ ≤ (T : ℝ) * (8 * N / q + 4 * q * L) + 16 * L * (2 : ℝ) ^ T + 4 * N := hsum2
    _ ≤ (T : ℝ) * (8 * N / q + 4 * q * L) + 16 * L * (2 * H) + 4 * N := by
        have h11 : 16 * L * (2 : ℝ) ^ T ≤ 16 * L * (2 * H) :=
          mul_le_mul_of_nonneg_left h2TR (by linarith)
        linarith
    _ = ((Nat.log 2 H + 1 : ℕ) : ℝ) * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
        + 32 * H * (1 + Real.log (2 * q)) + 4 * N := by
        rw [hT, hLdef]
        push_cast
        ring

/-- The S₂ support bound: the convolution of truncations vanishes past `U·V`. -/
lemma truncate_mul_eq_zero_of_gt (f g : ArithmeticFunction ℝ) (U V t : ℕ) (ht : U * V < t) :
    (truncate f U * truncate g V) t = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Nat.mem_divisorsAntidiagonal] at hx
  by_cases h1 : x.1 ≤ U
  · have h2 : ¬ x.2 ≤ V := by
      intro h2
      have hle : x.1 * x.2 ≤ U * V := Nat.mul_le_mul h1 h2
      obtain ⟨P, hP⟩ : ∃ P, P = x.1 * x.2 := ⟨_, rfl⟩
      obtain ⟨Q, hQ⟩ : ∃ Q, Q = U * V := ⟨_, rfl⟩
      rw [← hP] at hle
      rw [← hP] at hx
      rw [← hQ] at hle ht
      omega
    rw [truncate_apply, truncate_apply, if_neg h2, mul_zero]
  · rw [truncate_apply, if_neg h1, zero_mul]

/-- The S₃ trivial bound: `∑_{n≤V} Λ(n) ≤ V·log V`. -/
lemma sum_vonMangoldt_le (V : ℕ) :
    ∑ n ∈ Finset.Ioc 0 V, Λ n ≤ (V : ℝ) * Real.log V := by
  calc ∑ n ∈ Finset.Ioc 0 V, Λ n
      ≤ ∑ _n ∈ Finset.Ioc 0 V, Real.log V := by
        apply Finset.sum_le_sum
        intro n hn
        simp only [Finset.mem_Ioc] at hn
        calc Λ n ≤ Real.log n := vonMangoldt_le_log
          _ ≤ Real.log V := by
            apply Real.log_le_log (by exact_mod_cast hn.1)
            exact_mod_cast hn.2
    _ = (V : ℝ) * Real.log V := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
        norm_num

/-- ζ collapses on positive ranges: `∑_{0<m≤M} ζ(m)·z(m) = ∑_{0<m≤M} z(m)`. -/
lemma sum_Ioc_zeta_mul (z : ℕ → ℂ) (M : ℕ) :
    ∑ m ∈ Finset.Ioc 0 M, (((ζ : ArithmeticFunction ℝ) m : ℝ) : ℂ) * z m
      = ∑ m ∈ Finset.Ioc 0 M, z m := by
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_Ioc] at hm
  have h1 : ((ζ : ArithmeticFunction ℝ) m : ℝ) = 1 := by
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
      if_neg (by omega : ¬ m = 0)]
    norm_num
  rw [h1]
  norm_num

/-- The Ioc exp-sum cap: `‖∑_{0<m≤M} e(mβ)‖ ≤ [β∈ℤ ? M : min(M, 1/(2‖β‖))]`. -/
lemma exp_sum_Ioc_min_bound (β : ℝ) (M : ℕ) :
    ‖∑ m ∈ Finset.Ioc 0 M, e (m * β)‖
      ≤ (if β - round β = 0 then (M : ℝ)
         else min (M : ℝ) (1 / (2 * |β - round β|))) := by
  have hset : Finset.Ioc 0 M = Finset.Ico 1 (M + 1) := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hset]
  have := exp_sum_Ico_min_bound β 1 (M + 1)
  have hM : (M + 1 - 1 : ℕ) = M := by omega
  rwa [hM] at this

/-- **Near-integer points are large** (tight min-sum keystone): if `hα` is within
    `1/(2q)` of an integer then `2h > q`. Contrapositive: for `0 < h ≤ q/2`,
    `q ∤ ha` forces `‖ha/q‖ ≥ 1/q`, and the `≤ 1/(2q)` perturbation from
    `|α−a/q| ≤ 1/q²` leaves `‖hα‖ ≥ 1/(2q)`. -/
lemma nearint_h_lower (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (h : ℕ) (hh0 : 0 < h) (hhq : 2 * h ≤ q) :
    1 / (2 * (q : ℝ)) ≤ |(h : ℝ) * α - round ((h : ℝ) * α)| := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  -- q ∤ h*a (in ℕ, via coprimality)
  have hnd : ¬ (q : ℤ) ∣ ((h * a : ℕ) : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    intro hdvd
    have hqh : q ∣ h := (ha.symm).dvd_of_dvd_mul_right hdvd
    exact absurd (Nat.le_of_dvd hh0 hqh) (by omega)
  -- ‖ha/q‖ ≥ 1/q
  have hbase : 1 / (q : ℝ) ≤ |((h * a : ℕ) : ℝ) / q - round (((h * a : ℕ) : ℝ) / q)| :=
    dist_int_div_ge ((h * a : ℕ) : ℤ) q (by omega) hnd
  have hcast : (((h * a : ℕ) : ℝ) / q) = (h : ℝ) * ((a : ℝ) / q) := by
    push_cast
    ring
  rw [hcast] at hbase
  -- perturbation: |h(a/q) − hα| ≤ h/q² ≤ 1/(2q)
  have hpert : |(h : ℝ) * ((a : ℝ) / q) - (h : ℝ) * α| ≤ 1 / (2 * (q : ℝ)) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (h:ℝ))]
    rw [abs_sub_comm]
    have h1 : (h : ℝ) * |α - (a : ℝ) / q| ≤ (h : ℝ) * (1 / (q : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hα (by positivity)
    have h2 : (h : ℝ) * (1 / (q : ℝ) ^ 2) ≤ 1 / (2 * (q : ℝ)) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 : (2 : ℝ) * h ≤ q := by exact_mod_cast hhq
      nlinarith [hqR]
    linarith
  -- combine via 1-Lipschitz dist: ‖h(a/q)‖ ≤ |h(a/q) − hα| + ‖hα‖
  have hlip := dist_round_le ((h : ℝ) * ((a : ℝ) / q)) ((h : ℝ) * α)
  have hbridge : 1 / (2 * (q : ℝ)) = (1 / (q : ℝ)) - 1 / (2 * (q : ℝ)) := by
    field_simp
    ring
  linarith [hbase, hpert, hlip, hbridge]

/-- Distance to ℤ is subadditive under subtraction. -/
lemma dist_round_sub_le (x y : ℝ) :
    |(x - y) - round (x - y)| ≤ |x - round x| + |y - round y| := by
  calc |(x - y) - round (x - y)|
      ≤ |(x - y) - ((round x : ℤ) - (round y : ℤ) : ℤ)| :=
        round_le (x - y) ((round x : ℤ) - (round y : ℤ))
    _ = |(x - round x) + (-(y - round y))| := by push_cast; ring_nf
    _ ≤ |x - round x| + |-(y - round y)| := abs_add_le _ _
    _ = |x - round x| + |y - round y| := by rw [abs_neg]

/-- **Resonant points are `q/2`-separated**: two distinct near-integer (`< 1/(4q)`)
    points `h' < h` differ by more than `q/2`, so `⌊2h/q⌋ ≠ ⌊2h'/q⌋`. -/
lemma resonant_spaced (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (h h' : ℕ) (hh'0 : 0 < h') (hlt : h' < h)
    (hres : |(h : ℝ) * α - round ((h : ℝ) * α)| < 1 / (4 * (q : ℝ)))
    (hres' : |(h' : ℝ) * α - round ((h' : ℝ) * α)| < 1 / (4 * (q : ℝ))) :
    q < 2 * (h - h') := by
  by_contra hcon
  push_neg at hcon
  set d : ℕ := h - h' with hd
  have hd0 : 0 < d := by omega
  have hdq : 2 * d ≤ q := hcon
  have hdcast : (d : ℝ) * α = (h : ℝ) * α - (h' : ℝ) * α := by
    rw [hd, Nat.cast_sub hlt.le]
    ring
  have hsub := dist_round_sub_le ((h : ℝ) * α) ((h' : ℝ) * α)
  rw [← hdcast] at hsub
  have hlow := nearint_h_lower a q hq ha α hα d hd0 hdq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hbridge : 1 / (2 * (q : ℝ)) = 1 / (4 * (q : ℝ)) + 1 / (4 * (q : ℝ)) := by
    field_simp
    ring
  linarith [hlow, hsub, hres, hres', hbridge]

/-- **The resonant floor sum has no bare `N`** (the key to killing the spurious `4N`):
    the near-integer `h` (bin `φ h = 2h/q ≥ 1`, `φ` injective by `resonant_spaced`)
    satisfy `⌊N/h⌋ ≤ 2N/(q·φ h)`, so their sum telescopes to `(2N/q)·harmonic`. -/
lemma resonant_floor_sum_le (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (N H : ℕ) :
    ∑ h ∈ (Finset.Ioc 0 H).filter
        (fun h : ℕ => |(h : ℝ) * α - round ((h : ℝ) * α)| < 1 / (4 * (q : ℝ))),
        ((N / h : ℕ) : ℝ)
      ≤ (2 * (N : ℝ) / q) * (1 + Real.log H) := by
  classical
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  set R := (Finset.Ioc 0 H).filter
      (fun h : ℕ => |(h : ℝ) * α - round ((h : ℝ) * α)| < 1 / (4 * (q : ℝ))) with hR
  set φ : ℕ → ℕ := fun h => 2 * h / q with hφ
  have hφe : ∀ x : ℕ, φ x = 2 * x / q := fun _ => rfl
  -- membership + resonance facts
  have hmem : ∀ h ∈ R, 0 < h ∧ h ≤ H ∧
      |(h : ℝ) * α - round ((h : ℝ) * α)| < 1 / (4 * (q : ℝ)) := by
    intro h hh
    rw [hR, Finset.mem_filter, Finset.mem_Ioc] at hh
    exact ⟨hh.1.1, hh.1.2, hh.2⟩
  have hbig : ∀ h ∈ R, q < 2 * h := by
    intro h hh
    obtain ⟨hh0, _, hres⟩ := hmem h hh
    by_contra hc
    push_neg at hc
    have hlow := nearint_h_lower a q hq ha α hα h hh0 hc
    have : (1 : ℝ) / (2 * q) ≤ 1 / (4 * q) := le_trans hlow hres.le
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at this
    linarith
  have hφpos : ∀ h ∈ R, 1 ≤ φ h := by
    intro h hh
    have hh2 := hbig h hh
    rw [hφe]
    exact (Nat.one_le_div_iff (show 0 < q by omega)).mpr (by omega)
  -- φ is injective on R (resonant_spaced ⟹ bins strictly increase)
  have hinj : Set.InjOn φ (R : Set ℕ) := by
    intro h₁ hh₁ h₂ hh₂ hfe
    rcases lt_trichotomy h₁ h₂ with hlt | heq | hgt
    · exfalso
      obtain ⟨hh₁0, _, hr₁⟩ := hmem h₁ (Finset.mem_coe.mp hh₁)
      obtain ⟨_, _, hr₂⟩ := hmem h₂ (Finset.mem_coe.mp hh₂)
      have hsp := resonant_spaced a q hq ha α hα h₂ h₁ hh₁0 hlt hr₂ hr₁
      have hge : 2 * h₁ + q ≤ 2 * h₂ := by omega
      have hk : 2 * h₁ / q + 1 = (2 * h₁ + q) / q :=
        (Nat.add_div_right (2 * h₁) (show 0 < q by omega)).symm
      have hle : (2 * h₁ + q) / q ≤ 2 * h₂ / q := Nat.div_le_div_right hge
      have hbin : φ h₁ < φ h₂ := by rw [hφe, hφe]; omega
      omega
    · exact heq
    · exfalso
      obtain ⟨_, _, hr₁⟩ := hmem h₁ (Finset.mem_coe.mp hh₁)
      obtain ⟨hh₂0, _, hr₂⟩ := hmem h₂ (Finset.mem_coe.mp hh₂)
      have hsp := resonant_spaced a q hq ha α hα h₁ h₂ hh₂0 hgt hr₁ hr₂
      have hge : 2 * h₂ + q ≤ 2 * h₁ := by omega
      have hk : 2 * h₂ / q + 1 = (2 * h₂ + q) / q :=
        (Nat.add_div_right (2 * h₂) (show 0 < q by omega)).symm
      have hle : (2 * h₂ + q) / q ≤ 2 * h₁ / q := Nat.div_le_div_right hge
      have hbin : φ h₂ < φ h₁ := by rw [hφe, hφe]; omega
      omega
  -- termwise: ⌊N/h⌋ ≤ 2N/(q·φ h)
  have hterm : ∀ h ∈ R, ((N / h : ℕ) : ℝ) ≤ (2 * (N : ℝ) / q) * (1 / (φ h : ℝ)) := by
    intro h hh
    obtain ⟨hh0, _, _⟩ := hmem h hh
    have hφ1 := hφpos h hh
    have hφ0 : (0 : ℝ) < (φ h : ℝ) := by exact_mod_cast hφ1
    have hqφ : (q : ℝ) * (φ h : ℝ) ≤ 2 * (h : ℝ) := by
      have := Nat.div_mul_le_self (2 * h) q
      rw [hφe]
      have hcast : ((2 * h / q : ℕ) * q : ℕ) ≤ 2 * h := this
      have : ((2 * h / q : ℕ) : ℝ) * (q : ℝ) ≤ 2 * (h : ℝ) := by exact_mod_cast hcast
      nlinarith [this]
    have hNh : ((N / h : ℕ) : ℝ) ≤ (N : ℝ) / (h : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hh0)]
      have := Nat.div_mul_le_self N h
      have : ((N / h : ℕ) * h : ℕ) ≤ N := this
      exact_mod_cast this
    have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh0
    have hNn : (0:ℝ) ≤ (N:ℝ) := by positivity
    have hbound : (N : ℝ) / (h : ℝ) ≤ (2 * (N : ℝ) / q) * (1 / (φ h : ℝ)) := by
      rw [show (2 * (N : ℝ) / q) * (1 / (φ h : ℝ)) = (2 * (N:ℝ)) / (q * (φ h : ℝ)) from by
        field_simp, div_le_div_iff₀ hhpos (by positivity)]
      nlinarith [hqφ, hNn, hhpos, hqR, hφ0]
    linarith
  calc ∑ h ∈ R, ((N / h : ℕ) : ℝ)
      ≤ ∑ h ∈ R, (2 * (N : ℝ) / q) * (1 / (φ h : ℝ)) := Finset.sum_le_sum hterm
    _ = (2 * (N : ℝ) / q) * ∑ h ∈ R, (1 / (φ h : ℝ)) := by rw [Finset.mul_sum]
    _ = (2 * (N : ℝ) / q) * ∑ b ∈ R.image φ, (1 / (b : ℝ)) := by
        rw [Finset.sum_image (fun x hx y hy => hinj (Finset.mem_coe.mpr hx)
          (Finset.mem_coe.mpr hy))]
    _ ≤ (2 * (N : ℝ) / q) * ∑ b ∈ Finset.Icc 1 H, (1 / (b : ℝ)) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro b hb
          rw [Finset.mem_image] at hb
          obtain ⟨h, hhR, rfl⟩ := hb
          obtain ⟨hh0, hhH, _⟩ := hmem h hhR
          rw [Finset.mem_Icc]
          refine ⟨hφpos h hhR, ?_⟩
          rw [hφe]
          have hhle : 2 * h / q ≤ h :=
            Nat.div_le_of_le_mul (by nlinarith [hq])
          omega
        · intro b _ _
          positivity
    _ ≤ (2 * (N : ℝ) / q) * (1 + Real.log H) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ b ∈ Finset.Icc 1 H, (1 / (b : ℝ)) ≤ 1 + Real.log H := sum_one_div_le H

/-- **The tight min-sum bound** (replaces `dyadic_cap_sum_le`, NO bare `N`):
    `∑_{h≤H} min(⌊N/h⌋, 1/2‖hα‖) ≤ (2N/q)(1+log H) + (2H/q+1)(4q + 4q(1+log 2q))`.
    Resonant `h` (near-integer) contribute `(2N/q)·harmonic` (via
    `resonant_floor_sum_le`); non-resonant `h` route through `range_min_sum_le`
    with cap `V = 2q` (since `1/2‖hα‖ ≤ 2q` there). -/
lemma min_sum_tight (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (N H : ℕ) :
    ∑ h ∈ Finset.Ioc 0 H,
      (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then ((N / h : ℕ) : ℝ)
       else min ((N / h : ℕ) : ℝ) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|)))
      ≤ (2 * (N : ℝ) / q) * (1 + Real.log H)
        + ((H / (q / 2) + 1 : ℕ) : ℝ) * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))) := by
  classical
  set res : ℕ → Prop := fun h => |(h : ℝ) * α - round ((h : ℝ) * α)| < 1 / (4 * (q : ℝ))
    with hres
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 H) res]
  apply add_le_add
  · -- resonant half: each term ≤ ⌊N/h⌋
    refine le_trans (Finset.sum_le_sum ?_)
      (resonant_floor_sum_le a q hq ha α hα N H)
    intro h _
    split
    · exact le_refl _
    · exact min_le_left _ _
  · -- non-resonant half: route through range_min_sum_le at V = 2q
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hIoc : Finset.Ioc 0 H = Finset.Ico 1 (1 + H) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    have hrange := range_min_sum_le a q hq ha α hα (2 * (q : ℝ)) (by positivity) 1 H
    rw [show (1 : ℕ) + H = 1 + H from rfl] at hrange
    -- termwise: non-res term ≤ range-term (V = 2q); then superset + Ioc=Ico
    calc ∑ h ∈ (Finset.Ioc 0 H).filter (fun h => ¬ res h),
          (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then ((N / h : ℕ) : ℝ)
           else min ((N / h : ℕ) : ℝ) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|)))
        ≤ ∑ h ∈ (Finset.Ioc 0 H).filter (fun h => ¬ res h),
            (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then 2 * (q : ℝ)
             else min (2 * (q : ℝ)) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) := by
          apply Finset.sum_le_sum
          intro h hh
          rw [Finset.mem_filter] at hh
          have hnr : ¬ res h := hh.2
          rw [hres] at hnr
          push_neg at hnr
          -- ‖hα‖ ≥ 1/(4q) > 0 so the `= 0` branch is false; cap ≤ 2q
          have habs : 1 / (4 * (q : ℝ)) ≤ |(h : ℝ) * α - round ((h : ℝ) * α)| := hnr
          have hne : (h : ℝ) * α - round ((h : ℝ) * α) ≠ 0 := by
            intro h0
            rw [h0, abs_zero] at habs
            have : (0:ℝ) < 1 / (4 * (q : ℝ)) := by positivity
            linarith
          rw [if_neg hne, if_neg hne]
          have hcaple : 1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|) ≤ 2 * (q : ℝ) := by
            rw [div_le_iff₀ (by positivity)]
            have habspos : 0 < |(h : ℝ) * α - round ((h : ℝ) * α)| := by
              rw [abs_pos]; exact hne
            rw [div_le_iff₀ (by positivity)] at habs
            nlinarith [habs, hqR]
          calc min ((N / h : ℕ) : ℝ) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))
              ≤ 1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|) := min_le_right _ _
            _ = min (2 * (q : ℝ)) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|)) := by
                rw [min_eq_right hcaple]
      _ ≤ ∑ h ∈ Finset.Ioc 0 H,
            (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then 2 * (q : ℝ)
             else min (2 * (q : ℝ)) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro h _ _
          split
          · positivity
          · exact le_min (by positivity) (by positivity)
      _ = ∑ h ∈ Finset.Ico 1 (1 + H),
            (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then 2 * (q : ℝ)
             else min (2 * (q : ℝ)) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) := by
          rw [hIoc]
      _ ≤ ((H / (q / 2) + 1 : ℕ) : ℝ)
            * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))) := hrange


lemma S2_bound (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U V N : ℕ)
    (hUV : U * V ≤ N) (hUV1 : 1 ≤ U * V) :
    ‖∑ n ∈ Finset.Ioc 0 N,
        (((truncate (μ : ArithmeticFunction ℝ) U * truncate Λ V
            * (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ Real.log (U * V) *
          (((Nat.log 2 (U * V) + 1 : ℕ) : ℝ)
              * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
            + 32 * (U * V) * (1 + Real.log (2 * q)) + 4 * N) := by
  set c : ArithmeticFunction ℝ := truncate (μ : ArithmeticFunction ℝ) U * truncate Λ V with hc
  have hlogUV0 : (0 : ℝ) ≤ Real.log (U * V) := by
    apply Real.log_nonneg
    exact_mod_cast hUV1
  -- regroup + collapse ζ + normalize the e-argument
  have hre : ∑ n ∈ Finset.Ioc 0 N,
      ((c * (ζ : ArithmeticFunction ℝ)) n : ℂ) * e ((n : ℝ) * α)
      = ∑ t ∈ Finset.Ioc 0 N, (c t : ℂ) *
          ∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α)) := by
    rw [sum_Ioc_mul_weight_eq_sum_sum c (ζ : ArithmeticFunction ℝ)
      (fun n => e ((n : ℝ) * α)) N]
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    rw [sum_Ioc_zeta_mul (fun m => e (((t * m : ℕ) : ℝ) * α)) (N / t)]
    apply Finset.sum_congr rfl
    intro m _
    exact congrArg e (by push_cast; ring)
  rw [hre]
  -- cap the sum over the support
  set cap : ℕ → ℝ := fun t =>
    (if (t : ℝ) * α - round ((t : ℝ) * α) = 0 then ((N / t : ℕ) : ℝ)
     else min ((N / t : ℕ) : ℝ) (1 / (2 * |(t : ℝ) * α - round ((t : ℝ) * α)|))) with hcap
  have hcap0 : ∀ t, 0 ≤ cap t := by
    intro t
    rw [hcap]
    dsimp only
    split
    · positivity
    · exact le_min (by positivity) (by positivity)
  have hterm : ∀ t ∈ Finset.Ioc 0 N,
      ‖(c t : ℂ) * ∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α))‖
      ≤ (if t ≤ U * V then Real.log (U * V) * cap t else 0) := by
    intro t ht
    simp only [Finset.mem_Ioc] at ht
    by_cases htuv : t ≤ U * V
    · rw [if_pos htuv, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |c t| ≤ Real.log (U * V) := by
        calc |c t| ≤ Real.log t := abs_truncate_mul_le_log U V t
          _ ≤ Real.log (U * V) := by
            apply Real.log_le_log (by exact_mod_cast ht.1)
            exact_mod_cast htuv
      have h2 : ‖∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α))‖ ≤ cap t := by
        rw [hcap]
        exact exp_sum_Ioc_min_bound ((t : ℝ) * α) (N / t)
      exact mul_le_mul h1 h2 (norm_nonneg _) hlogUV0
    · rw [if_neg htuv]
      push_neg at htuv
      have hz : c t = 0 := truncate_mul_eq_zero_of_gt _ _ U V t htuv
      rw [hz]
      simp
  calc ‖∑ t ∈ Finset.Ioc 0 N, (c t : ℂ) *
        ∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α))‖
      ≤ ∑ t ∈ Finset.Ioc 0 N,
          ‖(c t : ℂ) * ∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ t ∈ Finset.Ioc 0 N, (if t ≤ U * V then Real.log (U * V) * cap t else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ t ∈ Finset.Ioc 0 (U * V), Real.log (U * V) * cap t := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun t _ => rfl)
        ext t
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, le_trans h2 hUV⟩, h2⟩
    _ = Real.log (U * V) * ∑ t ∈ Finset.Ioc 0 (U * V), cap t := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.log (U * V) *
        (((Nat.log 2 (U * V) + 1 : ℕ) : ℝ) * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
          + 32 * (U * V) * (1 + Real.log (2 * q)) + 4 * N) := by
        apply mul_le_mul_of_nonneg_left _ hlogUV0
        have := dyadic_cap_sum_le a q hq ha α hα N (U * V)
        rw [hcap]
        push_cast at this ⊢
        exact this

/-- `log` of a natural cast is nonneg (`log 0 = 0`). -/
lemma log_natCast_nonneg (m : ℕ) : 0 ≤ Real.log m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · rcases Nat.eq_or_lt_of_le h with h1 | h1
    · rw [← h1]; simp
    · exact Real.log_nonneg (by exact_mod_cast h1.le)

/-- `log ∘ (↑·)` is monotone on ℕ. -/
lemma log_natCast_monotone : Monotone (fun m : ℕ => Real.log m) := by
  intro m₁ m₂ h
  rcases Nat.eq_zero_or_pos m₁ with h1 | h1
  · subst h1
    simp only [Nat.cast_zero, Real.log_zero]
    exact log_natCast_nonneg m₂
  · exact Real.log_le_log (by exact_mod_cast h1) (by exact_mod_cast h)

/-- The min-cap grows by at most 1 when the size cap grows by 1. -/
lemma cap_succ_le (β : ℝ) (M : ℕ) :
    (if β - round β = 0 then ((M + 1 : ℕ) : ℝ)
     else min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|)))
    ≤ (if β - round β = 0 then (M : ℝ)
       else min (M : ℝ) (1 / (2 * |β - round β|))) + 1 := by
  split
  · push_cast; linarith
  · have h1 : min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|))
        ≤ min ((M : ℝ) + 1) (1 / (2 * |β - round β|) + 1) := by
      apply min_le_min _ (by linarith)
      push_cast
      linarith
    calc min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|))
        ≤ min ((M : ℝ) + 1) (1 / (2 * |β - round β|) + 1) := h1
      _ = min (M : ℝ) (1 / (2 * |β - round β|)) + 1 := by
          rw [← min_add_add_right]

/-- **THE S₁ BOUND**: the log-weighted Vaughan piece. -/
lemma S1_bound (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U N : ℕ) (hU : U ≤ N) :
    ‖∑ n ∈ Finset.Ioc 0 N,
        (((truncate (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log) n : ℝ) : ℂ)
          * e ((n : ℝ) * α)‖
      ≤ 2 * Real.log (N + 1) *
          ((((Nat.log 2 U + 1 : ℕ) : ℝ) * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
            + 32 * U * (1 + Real.log (2 * q)) + 4 * N) + U) := by
  have hlogN0 : (0 : ℝ) ≤ Real.log (N + 1) := by
    apply Real.log_nonneg
    push_cast
    linarith
  set cap : ℕ → ℝ := fun t =>
    (if (t : ℝ) * α - round ((t : ℝ) * α) = 0 then ((N / t : ℕ) : ℝ)
     else min ((N / t : ℕ) : ℝ) (1 / (2 * |(t : ℝ) * α - round ((t : ℝ) * α)|))) with hcap
  have hcap0 : ∀ t, 0 ≤ cap t := by
    intro t
    rw [hcap]
    dsimp only
    split
    · positivity
    · exact le_min (by positivity) (by positivity)
  -- regroup
  rw [sum_Ioc_mul_weight_eq_sum_sum (truncate (μ : ArithmeticFunction ℝ) U)
    ArithmeticFunction.log (fun n => e ((n : ℝ) * α)) N]
  -- per-d inner bound
  have hinner : ∀ d ∈ Finset.Ioc 0 N,
      ‖∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)‖
      ≤ 2 * Real.log (N + 1) * (cap d + 1) := by
    intro d hd
    simp only [Finset.mem_Ioc] at hd
    set M : ℕ := N / d with hM
    set β : ℝ := (d : ℝ) * α with hβ
    -- normalize the argument and the log
    have hstep1 : ∑ m ∈ Finset.Ioc 0 M, ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)
        = ∑ m ∈ Finset.Ioc 0 M, ((Real.log m : ℝ) : ℂ) * e ((m : ℝ) * β) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [ArithmeticFunction.log_apply]
      congr 1
      exact congrArg e (by rw [hβ]; push_cast; ring)
    -- extend Ioc 0 M to range (M+1) (the m = 0 term vanishes)
    have hstep2 : ∑ m ∈ Finset.Ioc 0 M, ((Real.log m : ℝ) : ℂ) * e ((m : ℝ) * β)
        = ∑ m ∈ Finset.range (M + 1), ((Real.log m : ℝ) : ℂ) * e ((m : ℝ) * β) := by
      apply Finset.sum_subset
      · intro m hm
        simp only [Finset.mem_Ioc] at hm
        simp only [Finset.mem_range]
        omega
      · intro m hm hnotm
        simp only [Finset.mem_range] at hm
        simp only [Finset.mem_Ioc] at hnotm
        have hm0 : m = 0 := by omega
        subst hm0
        simp
    -- the capped weight agrees with log on the range
    have hstep3 : ∑ m ∈ Finset.range (M + 1), ((Real.log m : ℝ) : ℂ) * e ((m : ℝ) * β)
        = ∑ m ∈ Finset.range (M + 1),
            ((Real.log ((min m (M + 1) : ℕ) : ℝ) : ℝ) : ℂ) * e ((m : ℝ) * β) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mem_range] at hm
      rw [min_eq_left (by omega : m ≤ M + 1)]
    have habel := abel_exp_sum (fun m => Real.log ((min m (M + 1) : ℕ) : ℝ))
      (fun m => log_natCast_nonneg _)
      (by
        intro x y h
        exact log_natCast_monotone (by omega : min x (M + 1) ≤ min y (M + 1)))
      (Real.log ((M + 1 : ℕ) : ℝ))
      (fun m => by exact log_natCast_monotone (min_le_right m (M + 1)))
      β (M + 1)
    have hlogM : Real.log ((M + 1 : ℕ) : ℝ) ≤ Real.log (N + 1) := by
      have h1 : (M : ℕ) + 1 ≤ N + 1 := by
        have : M ≤ N := hM ▸ Nat.div_le_self N d
        omega
      have := log_natCast_monotone (show (M + 1 : ℕ) ≤ (N + 1 : ℕ) from h1)
      push_cast at this ⊢
      exact this
    have hcapd : (if β - round β = 0 then ((M + 1 : ℕ) : ℝ)
        else min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|))) ≤ cap d + 1 := by
      have h1 := cap_succ_le β M
      have h2 : (if β - round β = 0 then (M : ℝ)
          else min (M : ℝ) (1 / (2 * |β - round β|))) = cap d := by
        rw [hcap, hβ, hM]
      rw [h2] at h1
      exact h1
    have hcapnn : (0 : ℝ) ≤ (if β - round β = 0 then ((M + 1 : ℕ) : ℝ)
        else min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|))) := by
      split
      · positivity
      · exact le_min (by positivity) (by positivity)
    calc ‖∑ m ∈ Finset.Ioc 0 M, ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)‖
        = ‖∑ m ∈ Finset.range (M + 1),
            ((Real.log ((min m (M + 1) : ℕ) : ℝ) : ℝ) : ℂ) * e ((m : ℝ) * β)‖ := by
          rw [hstep1, hstep2, hstep3]
      _ ≤ 2 * Real.log ((M + 1 : ℕ) : ℝ)
            * (if β - round β = 0 then ((M + 1 : ℕ) : ℝ)
               else min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|))) := by
          have := habel
          push_cast at this ⊢
          exact this
      _ ≤ 2 * Real.log (N + 1) * (cap d + 1) := by
          apply mul_le_mul
          · have : (0:ℝ) ≤ 2 := by norm_num
            nlinarith [hlogM]
          · exact hcapd
          · exact hcapnn
          · positivity
  -- support + assembly
  have hterm : ∀ d ∈ Finset.Ioc 0 N,
      ‖(truncate (μ : ArithmeticFunction ℝ) U d : ℂ) *
        ∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)‖
      ≤ (if d ≤ U then 2 * Real.log (N + 1) * (cap d + 1) else 0) := by
    intro d hd
    by_cases hdU : d ≤ U
    · rw [if_pos hdU, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |truncate (μ : ArithmeticFunction ℝ) U d| *
            ‖∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
              * e (((d * m : ℕ) : ℝ) * α)‖
          ≤ 1 * (2 * Real.log (N + 1) * (cap d + 1)) := by
            apply mul_le_mul (abs_truncate_moebius_le_one U d) (hinner d hd)
              (norm_nonneg _) (by norm_num)
        _ = 2 * Real.log (N + 1) * (cap d + 1) := one_mul _
    · rw [if_neg hdU]
      have hz : truncate (μ : ArithmeticFunction ℝ) U d = 0 := by
        rw [truncate_apply, if_neg hdU]
      rw [hz]
      simp
  calc ‖∑ d ∈ Finset.Ioc 0 N, (truncate (μ : ArithmeticFunction ℝ) U d : ℂ) *
        ∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)‖
      ≤ ∑ d ∈ Finset.Ioc 0 N,
          ‖(truncate (μ : ArithmeticFunction ℝ) U d : ℂ) *
            ∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
              * e (((d * m : ℕ) : ℝ) * α)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, (if d ≤ U then 2 * Real.log (N + 1) * (cap d + 1) else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ d ∈ Finset.Ioc 0 U, 2 * Real.log (N + 1) * (cap d + 1) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun t _ => rfl)
        ext t
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, le_trans h2 hU⟩, h2⟩
    _ = 2 * Real.log (N + 1) * (∑ d ∈ Finset.Ioc 0 U, cap d + U) := by
        have hsplit : ∀ d ∈ Finset.Ioc 0 U,
            2 * Real.log (N + 1) * (cap d + 1)
            = 2 * Real.log (N + 1) * cap d + 2 * Real.log (N + 1) := fun d _ => by ring
        rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 2 * Real.log (N + 1) *
        ((((Nat.log 2 U + 1 : ℕ) : ℝ) * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
          + 32 * U * (1 + Real.log (2 * q)) + 4 * N) + U) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        have hd := dyadic_cap_sum_le a q hq ha α hα N U
        have hsum : ∑ d ∈ Finset.Ioc 0 U, cap d
            ≤ ((Nat.log 2 U + 1 : ℕ) : ℝ) * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
              + 32 * U * (1 + Real.log (2 * q)) + 4 * N := by
          calc ∑ d ∈ Finset.Ioc 0 U, cap d
              = ∑ h ∈ Finset.Ioc 0 U,
                  (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then ((N / h : ℕ) : ℝ)
                   else min ((N / h : ℕ) : ℝ)
                     (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) := by
                apply Finset.sum_congr rfl
                intro h _
                rw [hcap]
            _ ≤ _ := hd
        linarith

/-- Pointwise subtraction for arithmetic functions (no `sub_apply` in Mathlib). -/
lemma sub_apply' (f g : ArithmeticFunction ℝ) (n : ℕ) : (f - g) n = f n - g n := by
  have h : f - g = f + -g := sub_eq_add_neg f g
  rw [h, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply]
  ring

/-- The S₄ inner factor `g = (Λ − Λ_{≤V}) ∗ ζ` is nonneg. -/
lemma tail_conv_nonneg (V m : ℕ) :
    0 ≤ ((Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ)) m := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg
  · rw [sub_apply']
    have h1 : truncate Λ V x.1 ≤ Λ x.1 := by
      rw [truncate_apply]
      split
      · exact le_refl _
      · exact vonMangoldt_nonneg
    linarith
  · rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]
    split
    · norm_num
    · norm_num

/-- The S₄ inner factor is log-bounded: `g(m) ≤ log m`. -/
lemma tail_conv_le_log (V m : ℕ) :
    ((Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ)) m ≤ Real.log m := by
  rw [ArithmeticFunction.mul_apply]
  calc ∑ x ∈ m.divisorsAntidiagonal, (Λ - truncate Λ V) x.1 * (ζ : ArithmeticFunction ℝ) x.2
      ≤ ∑ x ∈ m.divisorsAntidiagonal, Λ x.1 := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Nat.mem_divisorsAntidiagonal] at hx
        have hz : ((ζ : ArithmeticFunction ℝ) x.2) = 1 := by
          rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
            if_neg (by
              intro hc
              apply hx.2
              rw [← hx.1, hc, mul_zero])]
          norm_num
        rw [hz, mul_one, sub_apply']
        have h1 : 0 ≤ truncate Λ V x.1 := by
          rw [truncate_apply]
          split
          · exact vonMangoldt_nonneg
          · exact le_refl 0
        linarith
    _ = ∑ d ∈ m.divisors, Λ d := Nat.sum_divisorsAntidiagonal (f := fun d _ => Λ d)
    _ = Real.log m := vonMangoldt_sum

/-- The S₄ inner factor vanishes below the truncation: `g(m) = 0` for `m ≤ V`. -/
lemma tail_conv_eq_zero_of_le (V m : ℕ) (hm : m ≤ V) :
    ((Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ)) m = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Nat.mem_divisorsAntidiagonal] at hx
  have hle : x.1 ≤ V := by
    have h1 : x.1 ∣ m := ⟨x.2, hx.1.symm⟩
    have h2 : x.1 ≤ m := Nat.le_of_dvd (by omega) h1
    omega
  rw [sub_apply', truncate_apply, if_pos hle, sub_self, zero_mul]

/-- The Möbius tail vanishes below the truncation. -/
lemma moebius_tail_eq_zero_of_le (U d : ℕ) (hd : d ≤ U) :
    ((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U) d = 0 := by
  rw [sub_apply', truncate_apply, if_pos hd, sub_self]

/-- The Möbius tail is sup-bounded by 1. -/
lemma abs_moebius_tail_le_one (U d : ℕ) :
    |((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U) d| ≤ 1 := by
  rw [sub_apply', truncate_apply]
  split
  · rw [sub_self]
    norm_num
  · rw [sub_zero]
    have h := abs_moebius_le_one (n := d)
    rw [ArithmeticFunction.intCoe_apply]
    calc |((μ d : ℤ) : ℝ)| = ((|μ d| : ℤ) : ℝ) := by rw [Int.cast_abs]
      _ ≤ 1 := by exact_mod_cast h

/-- **Increasing geometric sum**: `∑_{t=t₀}^{T} (√2)^t ≤ 4·(√2)^T`. -/
lemma geom_sqrt2_up (t₀ T : ℕ) :
    ∑ t ∈ Finset.Icc t₀ T, (Real.sqrt 2) ^ t ≤ 4 * (Real.sqrt 2) ^ T := by
  have hr1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hr0 : (0 : ℝ) < Real.sqrt 2 := by linarith
  -- ∑_{Icc t₀ T} ≤ ∑_{range (T+1)}
  have hsub : ∑ t ∈ Finset.Icc t₀ T, (Real.sqrt 2) ^ t
      ≤ ∑ t ∈ Finset.range (T + 1), (Real.sqrt 2) ^ t := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro t ht
      rw [Finset.mem_Icc] at ht
      rw [Finset.mem_range]
      omega
    · intro t _ _
      positivity
  have hgeom : ∑ t ∈ Finset.range (T + 1), (Real.sqrt 2) ^ t
      = ((Real.sqrt 2) ^ (T + 1) - 1) / (Real.sqrt 2 - 1) :=
    geom_sum_eq (by linarith) (T + 1)
  rw [hgeom] at hsub
  refine hsub.trans ?_
  rw [div_le_iff₀ (by linarith)]
  have hpow : (Real.sqrt 2) ^ (T + 1) = Real.sqrt 2 * (Real.sqrt 2) ^ T := by
    rw [pow_succ]; ring
  -- need √2 ≥ 4/3 so that 3√2 - 4 ≥ 0
  have hsqrt2ge : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (4 / 3 : ℝ) = Real.sqrt ((4/3)^2) from by
      rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    norm_num
  have hpowpos : (0 : ℝ) < (Real.sqrt 2) ^ T := by positivity
  rw [hpow]
  nlinarith [hpowpos, hsqrt2ge,
    mul_nonneg hpowpos.le (show (0:ℝ) ≤ 3 * Real.sqrt 2 - 4 by nlinarith [hsqrt2ge])]

/-- **Decreasing geometric sum**: `∑_{t=t₀}^{T} (√2)⁻ᵗ ≤ 4·(√2)^(-t₀)`
    (stated as `(1/√2)^t`). -/
lemma geom_sqrt2_down (t₀ T : ℕ) :
    ∑ t ∈ Finset.Icc t₀ T, (1 / Real.sqrt 2) ^ t ≤ 4 * (1 / Real.sqrt 2) ^ t₀ := by
  have hr1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hr0 : (0 : ℝ) < Real.sqrt 2 := by linarith
  have hlt1 : (1 / Real.sqrt 2) < 1 := by
    rw [div_lt_one hr0]; exact hr1
  have hnn : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
  -- shift index: ∑_{t=t₀}^{T} r^t = r^{t₀} ∑_{k=0}^{T-t₀} r^k ≤ r^{t₀} · (1/(1-r))
  by_cases hle : t₀ ≤ T
  · have hIccIco : Finset.Icc t₀ T = Finset.Ico t₀ (T + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have hshift : ∑ t ∈ Finset.Icc t₀ T, (1 / Real.sqrt 2) ^ t
        = (1 / Real.sqrt 2) ^ t₀ * ∑ k ∈ Finset.range (T + 1 - t₀), (1 / Real.sqrt 2) ^ k := by
      rw [hIccIco, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_add]
    rw [hshift]
    have hsqrt2ge : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (4 / 3 : ℝ) = Real.sqrt ((4/3)^2) from by
        rw [Real.sqrt_sq (by norm_num)]]
      apply Real.sqrt_le_sqrt
      norm_num
    have hinvle : 1 / Real.sqrt 2 ≤ 3 / 4 := by
      rw [div_le_div_iff₀ hr0 (by norm_num)]
      linarith
    have hgeomle : ∑ k ∈ Finset.range (T + 1 - t₀), (1 / Real.sqrt 2) ^ k ≤ 4 := by
      have heq := geom_sum_eq (show (1 / Real.sqrt 2) ≠ 1 from ne_of_lt hlt1) (T + 1 - t₀)
      rw [heq]
      -- (r^n - 1)/(r - 1) = (1 - r^n)/(1 - r) ≤ 1/(1-r) ≤ 4
      have hden : (0:ℝ) < 1 - 1 / Real.sqrt 2 := by linarith
      have hrw : ((1 / Real.sqrt 2) ^ (T + 1 - t₀) - 1) / (1 / Real.sqrt 2 - 1)
          = (1 - (1 / Real.sqrt 2) ^ (T + 1 - t₀)) / (1 - 1 / Real.sqrt 2) := by
        rw [div_eq_div_iff (ne_of_lt (by linarith : 1 / Real.sqrt 2 - 1 < 0))
          (ne_of_gt hden)]; ring
      rw [hrw, div_le_iff₀ hden]
      have hp : (0:ℝ) ≤ (1 / Real.sqrt 2) ^ (T + 1 - t₀) := by positivity
      linarith
    calc (1 / Real.sqrt 2) ^ t₀ * ∑ k ∈ Finset.range (T + 1 - t₀), (1 / Real.sqrt 2) ^ k
        ≤ (1 / Real.sqrt 2) ^ t₀ * 4 :=
          mul_le_mul_of_nonneg_left hgeomle (by positivity)
      _ = 4 * (1 / Real.sqrt 2) ^ t₀ := by ring
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity

/-- `√(a+b) ≤ √a + √b`. -/
lemma sqrt_add_le' (a b : ℝ) : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h : Real.sqrt (a + b) ≤ Real.sqrt (Real.sqrt a ^ 2 + Real.sqrt b ^ 2 + 2 * (Real.sqrt a * Real.sqrt b)) := by
    apply Real.sqrt_le_sqrt
    by_cases ha : 0 ≤ a
    · by_cases hb : 0 ≤ b
      · rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
        nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
      · rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt (not_le.mp hb))]
        rw [Real.sq_sqrt ha]
        simp only [Real.sqrt_zero, mul_zero, add_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true]
        nlinarith [Real.sqrt_nonneg a]
    · have : Real.sqrt a = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt (not_le.mp ha))
      rw [this]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, mul_zero,
        add_zero, zero_mul]
      by_cases hb : 0 ≤ b
      · rw [Real.sq_sqrt hb]; nlinarith [Real.sqrt_nonneg b]
      · rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt (not_le.mp hb))]; simp; linarith
  refine h.trans (le_of_eq ?_)
  rw [show Real.sqrt a ^ 2 + Real.sqrt b ^ 2 + 2 * (Real.sqrt a * Real.sqrt b)
      = (Real.sqrt a + Real.sqrt b) ^ 2 from by ring,
    Real.sqrt_sq (by positivity)]

/-- `√(a+b+c+d) ≤ √a+√b+√c+√d`. -/
lemma sqrt_add4_le (a b c d : ℝ) :
    Real.sqrt (a + b + c + d) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d := by
  calc Real.sqrt (a + b + c + d)
      ≤ Real.sqrt (a + b + c) + Real.sqrt d := sqrt_add_le' _ _
    _ ≤ (Real.sqrt (a + b) + Real.sqrt c) + Real.sqrt d := by
        gcongr; exact sqrt_add_le' _ _
    _ ≤ ((Real.sqrt a + Real.sqrt b) + Real.sqrt c) + Real.sqrt d := by
        gcongr; exact sqrt_add_le' _ _
    _ = Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d := by ring

/-- `√(2^t) = (√2)^t`. -/
lemma sqrt_two_pow (t : ℕ) : Real.sqrt ((2 : ℝ) ^ t) = (Real.sqrt 2) ^ t := by
  rw [show ((2 : ℝ) ^ t) = ((Real.sqrt 2) ^ t) ^ 2 from by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)],
    Real.sqrt_sq (by positivity)]

/-- `(1/√2)^t = √(1/2^t)`. -/
lemma sqrt_two_pow_inv (t : ℕ) : (1 / Real.sqrt 2) ^ t = Real.sqrt (1 / (2 : ℝ) ^ t) := by
  rw [div_pow, one_pow, ← sqrt_two_pow, one_div, ← Real.sqrt_inv, one_div]

/-- `√(c·N²) = √c·N` for `N ≥ 0`, `c ≥ 0`. -/
lemma sqrt_const_mul_sq (c : ℝ) (hc : 0 ≤ c) (N : ℕ) :
    Real.sqrt (c * (N:ℝ)^2) = Real.sqrt c * N := by
  rw [Real.sqrt_mul hc, Real.sqrt_sq (by positivity)]

/-- **The tight dyadic assembly** (Type-II core): sum the per-block second-moment bounds
    across the dyadic range `[t₀, Tmax]` via `√·` splitting and geometric summation.
    Each of the four terms in the per-block bound sums to a geometric series (the `2^t`
    term increasing, the `1/2^t` term decreasing, the `q` and `N²/q` terms constant),
    giving the four-term envelope on the right. This replaces the lossy `S4_bound`
    dyadic assembly (which over-charged the `2^t` cap to `N`). -/
lemma s4_dyadic_assembly (N q V U t₀ Tmax : ℕ) (hq : 2 ≤ q) (hN1 : 1 ≤ N) (hU1 : 1 ≤ U)
    (ht0T : t₀ ≤ Tmax)
    (hUt0 : (U : ℝ) ≤ 2 * (2 : ℝ) ^ t₀)
    (hTmaxN : (2 : ℝ) ^ Tmax ≤ (N : ℝ) / (V + 1))
    (blk : ℕ → ℝ) (hblk0 : ∀ t, 0 ≤ blk t)
    (hbnd : ∀ t ∈ Finset.Icc t₀ Tmax,
        blk t ^ 2 ≤ (Real.log N) ^ 2 *
          (10 * N * (2:ℝ)^t + 32 * N^2 / q + 64 * N^2 * (1 + Real.log (2*q)) / (2:ℝ)^t
            + 36 * N * q * (1 + Real.log (2*q)))) :
    ∑ t ∈ Finset.Icc t₀ Tmax, blk t
      ≤ Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
          + Real.sqrt 32 * N * ((Tmax - t₀ + 1 : ℕ) : ℝ) / Real.sqrt q
          + 64 * N * Real.sqrt (1 + Real.log (2*q)) / Real.sqrt U
          + 6 * ((Tmax - t₀ + 1 : ℕ) : ℝ) * Real.sqrt (N * q * (1 + Real.log (2*q)))) := by
  have hqR : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hNR : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hUR : (0:ℝ) < U := by exact_mod_cast (by omega : 0 < U)
  have hlogN0 : (0:ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hL0 : (0:ℝ) ≤ 1 + Real.log (2*q) := by
    have : (0:ℝ) ≤ Real.log (2*q) := Real.log_nonneg (by
      have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
      linarith)
    linarith
  -- per-block bound
  have hper : ∀ t ∈ Finset.Icc t₀ Tmax,
      blk t ≤ Real.log N * (Real.sqrt (10 * N) * (Real.sqrt 2)^t
        + Real.sqrt (32 * N^2 / q)
        + Real.sqrt (64 * N^2 * (1 + Real.log (2*q))) * (1 / Real.sqrt 2)^t
        + Real.sqrt (36 * N * q * (1 + Real.log (2*q)))) := by
    intro t ht
    have hb := hbnd t ht
    have hsq : blk t ≤ Real.sqrt ((Real.log N) ^ 2 *
        (10 * N * (2:ℝ)^t + 32 * N^2 / q + 64 * N^2 * (1 + Real.log (2*q)) / (2:ℝ)^t
          + 36 * N * q * (1 + Real.log (2*q)))) := by
      rw [← Real.sqrt_sq (hblk0 t)]
      exact Real.sqrt_le_sqrt hb
    refine hsq.trans ?_
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hlogN0]
    apply mul_le_mul_of_nonneg_left ?_ hlogN0
    have e1 : Real.sqrt (10 * N * (2:ℝ)^t) = Real.sqrt (10 * N) * (Real.sqrt 2)^t := by
      rw [show (10 * (N:ℝ) * (2:ℝ)^t) = (10 * N) * (2:ℝ)^t from by ring,
        Real.sqrt_mul (by positivity), sqrt_two_pow]
    have e3 : Real.sqrt (64 * N^2 * (1 + Real.log (2*q)) / (2:ℝ)^t)
        = Real.sqrt (64 * N^2 * (1 + Real.log (2*q))) * (1 / Real.sqrt 2)^t := by
      rw [show (64 * (N:ℝ)^2 * (1 + Real.log (2*q)) / (2:ℝ)^t)
          = (64 * N^2 * (1 + Real.log (2*q))) * (1 / (2:ℝ)^t) from by ring,
        Real.sqrt_mul (by positivity), ← sqrt_two_pow_inv]
    calc Real.sqrt (10 * N * (2:ℝ)^t + 32 * N^2 / q
          + 64 * N^2 * (1 + Real.log (2*q)) / (2:ℝ)^t + 36 * N * q * (1 + Real.log (2*q)))
        ≤ Real.sqrt (10 * N * (2:ℝ)^t) + Real.sqrt (32 * N^2 / q)
          + Real.sqrt (64 * N^2 * (1 + Real.log (2*q)) / (2:ℝ)^t)
          + Real.sqrt (36 * N * q * (1 + Real.log (2*q))) := sqrt_add4_le _ _ _ _
      _ = Real.sqrt (10 * N) * (Real.sqrt 2)^t + Real.sqrt (32 * N^2 / q)
          + Real.sqrt (64 * N^2 * (1 + Real.log (2*q))) * (1 / Real.sqrt 2)^t
          + Real.sqrt (36 * N * q * (1 + Real.log (2*q))) := by rw [e1, e3]
  refine (Finset.sum_le_sum hper).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left ?_ hlogN0
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.sum_const,
    Nat.card_Icc, nsmul_eq_mul, nsmul_eq_mul]
  have hcard : ((Tmax + 1 - t₀ : ℕ) : ℝ) = ((Tmax - t₀ + 1 : ℕ) : ℝ) := by
    congr 1; omega
  rw [hcard]
  -- P1
  have hP1 : Real.sqrt (10 * N) * (∑ t ∈ Finset.Icc t₀ Tmax, (Real.sqrt 2)^t)
      ≤ 4 * Real.sqrt 10 * N / Real.sqrt (V + 1) := by
    refine (mul_le_mul_of_nonneg_left (geom_sqrt2_up t₀ Tmax) (Real.sqrt_nonneg _)).trans ?_
    rw [← sqrt_two_pow]
    have h2 : Real.sqrt ((2:ℝ)^Tmax) ≤ Real.sqrt ((N:ℝ)/(V+1)) := Real.sqrt_le_sqrt hTmaxN
    have hVpos : (0:ℝ) < (V:ℝ) + 1 := by positivity
    calc Real.sqrt (10 * N) * (4 * Real.sqrt ((2:ℝ)^Tmax))
        ≤ Real.sqrt (10 * N) * (4 * Real.sqrt ((N:ℝ)/(V+1))) := by
          apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by norm_num))
            (Real.sqrt_nonneg _)
      _ = 4 * Real.sqrt (10 * N * ((N:ℝ)/(V+1))) := by
          rw [show Real.sqrt (10 * N) * (4 * Real.sqrt ((N:ℝ)/(V+1)))
              = 4 * (Real.sqrt (10 * N) * Real.sqrt ((N:ℝ)/(V+1))) from by ring,
            ← Real.sqrt_mul (by positivity)]
      _ = 4 * Real.sqrt 10 * N / Real.sqrt (V + 1) := by
          rw [show (10 * (N:ℝ) * ((N:ℝ)/(V+1))) = (10 * N^2) / (V+1) from by ring,
            Real.sqrt_div (by positivity), sqrt_const_mul_sq 10 (by norm_num) N]
          ring
  -- P3
  have hP3 : Real.sqrt (64 * N^2 * (1 + Real.log (2*q))) * (∑ t ∈ Finset.Icc t₀ Tmax, (1/Real.sqrt 2)^t)
      ≤ 64 * N * Real.sqrt (1 + Real.log (2*q)) / Real.sqrt U := by
    have hs64 : Real.sqrt (64 * N^2 * (1 + Real.log (2*q)))
        = 8 * N * Real.sqrt (1 + Real.log (2*q)) := by
      rw [show (64 * (N:ℝ)^2 * (1 + Real.log (2*q))) = (8 * N)^2 * (1 + Real.log (2*q)) from by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [hs64]
    refine (mul_le_mul_of_nonneg_left (geom_sqrt2_down t₀ Tmax) (by positivity)).trans ?_
    rw [sqrt_two_pow_inv]
    have hkey : Real.sqrt (1 / (2:ℝ)^t₀) ≤ 2 / Real.sqrt U := by
      have hle : (1:ℝ) / (2:ℝ)^t₀ ≤ 4 / U := by
        rw [div_le_div_iff₀ (by positivity) hUR]
        nlinarith [hUt0]
      have h4U : Real.sqrt (4 / U) = 2 / Real.sqrt U := by
        rw [Real.sqrt_div (by norm_num), show Real.sqrt 4 = 2 from by
          rw [show (4:ℝ) = 2^2 from by norm_num, Real.sqrt_sq (by norm_num)]]
      calc Real.sqrt (1 / (2:ℝ)^t₀) ≤ Real.sqrt (4 / U) := Real.sqrt_le_sqrt hle
        _ = 2 / Real.sqrt U := h4U
    calc 8 * N * Real.sqrt (1 + Real.log (2*q)) * (4 * Real.sqrt (1 / (2:ℝ)^t₀))
        = (32 * N * Real.sqrt (1 + Real.log (2*q))) * Real.sqrt (1 / (2:ℝ)^t₀) := by ring
      _ ≤ (32 * N * Real.sqrt (1 + Real.log (2*q))) * (2 / Real.sqrt U) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 64 * N * Real.sqrt (1 + Real.log (2*q)) / Real.sqrt U := by ring
  -- T2, T4 (equalities)
  have hT2 : ((Tmax - t₀ + 1 : ℕ) : ℝ) * Real.sqrt (32 * N^2 / q)
      = Real.sqrt 32 * N * ((Tmax - t₀ + 1 : ℕ) : ℝ) / Real.sqrt q := by
    rw [show (32 * (N:ℝ)^2 / q) = (32 * N^2) / q from by ring,
      Real.sqrt_div (by positivity), sqrt_const_mul_sq 32 (by norm_num) N]
    ring
  have hT4 : ((Tmax - t₀ + 1 : ℕ) : ℝ) * Real.sqrt (36 * N * q * (1 + Real.log (2*q)))
      = 6 * ((Tmax - t₀ + 1 : ℕ) : ℝ) * Real.sqrt (N * q * (1 + Real.log (2*q))) := by
    rw [show (36 * (N:ℝ) * q * (1 + Real.log (2*q)))
        = 36 * (N * q * (1 + Real.log (2*q))) from by ring,
      Real.sqrt_mul (by norm_num), show Real.sqrt 36 = 6 from by
        rw [show (36:ℝ) = 6^2 from by norm_num, Real.sqrt_sq (by norm_num)]]
    ring
  rw [hT2, hT4]
  exact add_le_add (add_le_add (add_le_add hP1 (le_of_eq rfl)) hP3) (le_of_eq rfl)

/-- **Per-block absorption** (Type-II core algebra): the dyadic block second-moment
    envelope `D·(x+1)·(D + 2(y+1)(2D+4qL))` (with `D=2^t`, `x=⌊N/D⌋`, `y=⌊x/⌊q/2⌋⌋`)
    is dominated by the four clean geometric terms consumed by `s4_dyadic_assembly`. -/
lemma s4_block_absorb (D x y q L N : ℝ)
    (hD1 : 1 ≤ D) (hq2 : 2 ≤ q) (hL0 : 0 ≤ L) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hN0 : 0 ≤ N)
    (hDx : D * x ≤ N) (hDN : D ≤ N) (hyx : y ≤ x) (hqy : q * y ≤ 4 * x) :
    D * (x + 1) * (D + 2 * (y + 1) * (2 * D + 4 * q * L))
      ≤ 10 * N * D + 32 * N ^ 2 / q + 64 * N ^ 2 * L / D + 36 * N * q * L := by
  have hD0 : (0:ℝ) ≤ D := by linarith
  have hq0 : (0:ℝ) < q := by linarith
  have hDpos : (0:ℝ) < D := by linarith
  have hDDx : D * (D * x) ≤ D * N := mul_le_mul_of_nonneg_left hDx hD0
  have hDD : D * D ≤ D * N := mul_le_mul_of_nonneg_left hDN hD0
  have hDy : D * y ≤ N := le_trans (mul_le_mul_of_nonneg_left hyx hD0) hDx
  have hG_ND : 5 * D ^ 2 * x + 5 * D ^ 2 ≤ 10 * N * D := by nlinarith [hDDx, hDD]
  have hG_Nq : 4 * D ^ 2 * x * y + 4 * D ^ 2 * y ≤ 32 * N ^ 2 / q := by
    rw [le_div_iff₀ hq0]
    have e1 : (4 * D ^ 2 * x * y + 4 * D ^ 2 * y) * q
        = 4 * D ^ 2 * x * (q * y) + 4 * D ^ 2 * (q * y) := by ring
    rw [e1]
    have h1 : 4 * D ^ 2 * x * (q * y) ≤ 4 * D ^ 2 * x * (4 * x) :=
      mul_le_mul_of_nonneg_left hqy (by positivity)
    have h2 : 4 * D ^ 2 * (q * y) ≤ 4 * D ^ 2 * (4 * x) :=
      mul_le_mul_of_nonneg_left hqy (by positivity)
    have hDx2 : (D * x) ^ 2 ≤ N ^ 2 := by nlinarith [hDx, mul_nonneg hD0 hx0, hN0]
    have hDxN : D * (D * x) ≤ N ^ 2 := le_trans hDDx (by nlinarith [hDN, hN0])
    nlinarith [h1, h2, hDx2, hDxN, mul_nonneg (mul_nonneg hD0 hD0) hx0, hN0]
  have hG_ND2 : 8 * D * q * L * x * y ≤ 64 * N ^ 2 * L / D := by
    rw [le_div_iff₀ hDpos]
    have e1 : 8 * D * q * L * x * y * D = L * (8 * D ^ 2 * x * (q * y)) := by ring
    rw [e1]
    have h1 : 8 * D ^ 2 * x * (q * y) ≤ 8 * D ^ 2 * x * (4 * x) :=
      mul_le_mul_of_nonneg_left hqy (by positivity)
    have hDx2 : (D * x) ^ 2 ≤ N ^ 2 := by nlinarith [hDx, mul_nonneg hD0 hx0, hN0]
    have h2 : 8 * D ^ 2 * x * (4 * x) ≤ 64 * N ^ 2 := by nlinarith [hDx2]
    have h3 : 8 * D ^ 2 * x * (q * y) ≤ 64 * N ^ 2 := le_trans h1 h2
    calc L * (8 * D ^ 2 * x * (q * y)) ≤ L * (64 * N ^ 2) :=
          mul_le_mul_of_nonneg_left h3 hL0
      _ = 64 * N ^ 2 * L := by ring
  have hG_NqL : 8 * D * q * L * x + 8 * D * q * L * y + 8 * D * q * L
      ≤ 36 * N * q * L := by
    have hqL0 : (0:ℝ) ≤ q * L := mul_nonneg (le_of_lt hq0) hL0
    have t1 : 8 * D * q * L * x = 8 * (q * L) * (D * x) := by ring
    have t2 : 8 * D * q * L * y = 8 * (q * L) * (D * y) := by ring
    have t3 : 8 * D * q * L = 8 * (q * L) * D := by ring
    have b1 : 8 * (q * L) * (D * x) ≤ 8 * (q * L) * N :=
      mul_le_mul_of_nonneg_left hDx (by positivity)
    have b2 : 8 * (q * L) * (D * y) ≤ 8 * (q * L) * N :=
      mul_le_mul_of_nonneg_left hDy (by positivity)
    have b3 : 8 * (q * L) * D ≤ 8 * (q * L) * N :=
      mul_le_mul_of_nonneg_left hDN (by positivity)
    nlinarith [b1, b2, b3, t1, t2, t3, mul_nonneg hqL0 hN0]
  have hEexp : D * (x + 1) * (D + 2 * (y + 1) * (2 * D + 4 * q * L))
      = (5 * D ^ 2 * x + 5 * D ^ 2) + (4 * D ^ 2 * x * y + 4 * D ^ 2 * y)
        + (8 * D * q * L * x * y)
        + (8 * D * q * L * x + 8 * D * q * L * y + 8 * D * q * L) := by ring
  rw [hEexp]
  linarith [hG_ND, hG_Nq, hG_ND2, hG_NqL]

/-- **Per-block `hbnd`** for `s4_dyadic_assembly`: the dyadic-block sum-of-norms squared
    is dominated by the four-term geometric envelope (Cauchy–Schwarz on the block, then
    `S4_block_second_moment`, then `s4_block_absorb`). -/
lemma s4_block_hbnd (a q N V t : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (g : ℕ → ℝ) (G : ℝ)
    (hg0 : ∀ m, 0 ≤ g m) (hgG : ∀ m, g m ≤ G)
    (hN1 : 1 ≤ N) (h2tN : (2:ℕ) ^ t ≤ N) :
    (∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
        ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖) ^ 2
      ≤ G ^ 2 * (10 * N * (2:ℝ) ^ t + 32 * N ^ 2 / q
          + 64 * N ^ 2 * (1 + Real.log (2 * q)) / (2:ℝ) ^ t
          + 36 * N * q * (1 + Real.log (2 * q))) := by
  have hq2 : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t))
    (f := fun d => ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖)
  rw [Nat.card_Ico] at hcs
  have hmom := S4_block_second_moment a q hq ha α hα g G hg0 hgG N (2 ^ t) (2 ^ t + 2 ^ t) V
    (by positivity)
  have hcard : ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) = (2:ℝ) ^ t := by
    have h : (2 ^ t + 2 ^ t - 2 ^ t : ℕ) = 2 ^ t := Nat.add_sub_cancel _ _
    rw [h]; push_cast; ring
  have hL0 : (0:ℝ) ≤ 1 + Real.log (2 * q) := by
    have : (0:ℝ) ≤ Real.log (2 * q) := Real.log_nonneg (by nlinarith [hq2])
    linarith
  have hx0 : (0:ℝ) ≤ ((N / 2 ^ t : ℕ) : ℝ) := by positivity
  have hy0 : (0:ℝ) ≤ (((N / 2 ^ t) / (q / 2) : ℕ) : ℝ) := by positivity
  have hN0 : (0:ℝ) ≤ (N:ℝ) := by positivity
  have hD1 : (1:ℝ) ≤ (2:ℝ) ^ t := one_le_pow₀ (by norm_num)
  have hDx : (2:ℝ) ^ t * ((N / 2 ^ t : ℕ) : ℝ) ≤ N := by
    have hnat : (N / 2 ^ t) * 2 ^ t ≤ N := Nat.div_mul_le_self N (2 ^ t)
    calc (2:ℝ) ^ t * ((N / 2 ^ t : ℕ) : ℝ)
        = (((N / 2 ^ t) * 2 ^ t : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (N:ℝ) := by exact_mod_cast hnat
  have hDN : (2:ℝ) ^ t ≤ N := by exact_mod_cast h2tN
  have hyx : (((N / 2 ^ t) / (q / 2) : ℕ) : ℝ) ≤ ((N / 2 ^ t : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_le_self _ _
  have hqy : (q:ℝ) * (((N / 2 ^ t) / (q / 2) : ℕ) : ℝ) ≤ 4 * ((N / 2 ^ t : ℕ) : ℝ) := by
    have h2 : q ≤ 4 * (q / 2) := by omega
    have h1 : ((N / 2 ^ t) / (q / 2)) * (q / 2) ≤ N / 2 ^ t := Nat.div_mul_le_self _ _
    have hnat : q * ((N / 2 ^ t) / (q / 2)) ≤ 4 * (N / 2 ^ t) := by
      calc q * ((N / 2 ^ t) / (q / 2))
          ≤ 4 * (q / 2) * ((N / 2 ^ t) / (q / 2)) := Nat.mul_le_mul_right _ h2
        _ = 4 * (((N / 2 ^ t) / (q / 2)) * (q / 2)) := by ring
        _ ≤ 4 * (N / 2 ^ t) := Nat.mul_le_mul_left _ h1
    exact_mod_cast hnat
  have habs := s4_block_absorb ((2:ℝ) ^ t) ((N / 2 ^ t : ℕ) : ℝ)
    (((N / 2 ^ t) / (q / 2) : ℕ) : ℝ) q (1 + Real.log (2 * q)) N
    hD1 hq2 hL0 hx0 hy0 hN0 hDx hDN hyx hqy
  have hmomeq : G ^ 2 * (((N / 2 ^ t : ℕ) : ℝ) + 1) *
      (((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) + 2 * ((((N / 2 ^ t) / (q / 2) + 1 : ℕ) : ℝ))
        * (2 * ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q))))
      = G ^ 2 * ((((N / 2 ^ t : ℕ) : ℝ) + 1) * ((2:ℝ) ^ t
          + 2 * ((((N / 2 ^ t) / (q / 2) : ℕ) : ℝ) + 1)
            * (2 * (2:ℝ) ^ t + 4 * q * (1 + Real.log (2 * q))))) := by
    rw [hcard]; push_cast; ring
  calc (∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
          ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖) ^ 2
      ≤ ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) *
          ∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
            ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2 := by
        exact_mod_cast hcs
    _ = (2:ℝ) ^ t *
          ∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
            ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2 := by
        rw [hcard]
    _ ≤ (2:ℝ) ^ t * (G ^ 2 * ((((N / 2 ^ t : ℕ) : ℝ) + 1) * ((2:ℝ) ^ t
          + 2 * ((((N / 2 ^ t) / (q / 2) : ℕ) : ℝ) + 1)
            * (2 * (2:ℝ) ^ t + 4 * q * (1 + Real.log (2 * q)))))) :=
        mul_le_mul_of_nonneg_left (hmom.trans_eq hmomeq) (by positivity)
    _ = G ^ 2 * ((2:ℝ) ^ t * (((N / 2 ^ t : ℕ) : ℝ) + 1) * ((2:ℝ) ^ t
          + 2 * ((((N / 2 ^ t) / (q / 2) : ℕ) : ℝ) + 1)
            * (2 * (2:ℝ) ^ t + 4 * q * (1 + Real.log (2 * q))))) := by ring
    _ ≤ G ^ 2 * (10 * N * (2:ℝ) ^ t + 32 * N ^ 2 / q
          + 64 * N ^ 2 * (1 + Real.log (2 * q)) / (2:ℝ) ^ t
          + 36 * N * q * (1 + Real.log (2 * q))) :=
        mul_le_mul_of_nonneg_left habs (by positivity)


lemma S4_bound (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U V N : ℕ) :
    ‖∑ n ∈ Finset.Ioc 0 N,
        (((((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U)
            * ((Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ))) n : ℝ) : ℂ)
          * e ((n : ℝ) * α)‖
      ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) *
          Real.sqrt ((N : ℝ) * (Real.log N ^ 2
            * (((N / 2 ^ Nat.log 2 (U + 1) : ℕ) : ℝ) + 1)
            * ((N : ℝ) + 2 * ((((N / 2 ^ Nat.log 2 (U + 1) : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * N + 4 * q * (1 + Real.log (2 * q)))))) := by
  set c : ArithmeticFunction ℝ :=
    (μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U with hc
  set gAF : ArithmeticFunction ℝ := (Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ) with hgAF
  set ghat : ℕ → ℝ := fun m => if m ≤ N then gAF m else 0 with hghat
  set t₀ : ℕ := Nat.log 2 (U + 1) with ht₀
  set Tmax : ℕ := Nat.log 2 N with hTmax
  set Mom : ℝ := Real.log N ^ 2 * (((N / 2 ^ t₀ : ℕ) : ℝ) + 1)
      * ((N : ℝ) + 2 * ((((N / 2 ^ t₀ : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
        * (2 * N + 4 * q * (1 + Real.log (2 * q)))) with hMom
  have hL0 : (0 : ℝ) ≤ 1 + Real.log (2 * q) := by
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have : (0 : ℝ) ≤ Real.log (2 * q) := Real.log_nonneg (by linarith)
    linarith
  rcases Nat.eq_zero_or_pos N with hN0 | hN0
  · subst hN0
    simp only [Finset.Ioc_self, Finset.sum_empty, norm_zero]
    positivity
  have hMom0 : 0 ≤ Mom := by
    rw [hMom]
    have h1 : (0 : ℝ) ≤ (N : ℝ) + 2 * ((((N / 2 ^ t₀ : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
        * (2 * N + 4 * q * (1 + Real.log (2 * q))) := by
      have h2 : (0 : ℝ) ≤ 2 * N + 4 * q * (1 + Real.log (2 * q)) := by
        have := mul_nonneg (by positivity : (0:ℝ) ≤ 4 * q) hL0
        positivity
      positivity
    positivity
  have hghat0 : ∀ m, 0 ≤ ghat m := by
    intro m
    rw [hghat]
    dsimp only
    split
    · exact tail_conv_nonneg V m
    · exact le_refl 0
  have hghatG : ∀ m, ghat m ≤ Real.log N := by
    intro m
    rw [hghat]
    dsimp only
    split
    · rename_i hm
      calc gAF m ≤ Real.log m := tail_conv_le_log V m
        _ ≤ Real.log N := log_natCast_monotone hm
    · exact log_natCast_nonneg N
  -- regroup and restrict the inner sums
  rw [show c * gAF = c * gAF from rfl,
    sum_Ioc_mul_weight_eq_sum_sum c gAF (fun n => e ((n : ℝ) * α)) N]
  have hinner : ∀ d ∈ Finset.Ioc 0 N,
      ∑ m ∈ Finset.Ioc 0 (N / d), (gAF m : ℂ) * e (((d * m : ℕ) : ℝ) * α)
      = ∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α) := by
    intro d hd
    simp only [Finset.mem_Ioc] at hd
    have step1 : ∑ m ∈ Finset.Ioc 0 (N / d), (gAF m : ℂ) * e (((d * m : ℕ) : ℝ) * α)
        = ∑ m ∈ Finset.Ioc 0 (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mem_Ioc] at hm
      have hmN : m ≤ N := le_trans hm.2 (Nat.div_le_self N d)
      rw [hghat]
      dsimp only
      rw [if_pos hmN]
      congr 1
      exact congrArg e (by push_cast; ring)
    rw [step1]
    symm
    apply Finset.sum_subset
    · intro m hm
      simp only [Finset.mem_Ioc] at hm ⊢
      omega
    · intro m hm hnot
      simp only [Finset.mem_Ioc] at hm hnot
      have hmV : m ≤ V := by omega
      have hz : ghat m = 0 := by
        rw [hghat]
        dsimp only
        split
        · exact tail_conv_eq_zero_of_le V m hmV
        · rfl
      rw [hz]
      simp
  rw [Finset.sum_congr rfl (fun d hd => by rw [hinner d hd])]
  -- support restriction + triangle
  have hterm : ∀ d ∈ Finset.Ioc 0 N,
      ‖(c d : ℂ) * ∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖
      ≤ (if U < d then
          ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ else 0) := by
    intro d _
    by_cases hdU : U < d
    · rw [if_pos hdU, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := abs_moebius_tail_le_one U d
      rw [hc]
      calc |(((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U) d)| *
            ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖
          ≤ 1 * ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = _ := one_mul _
    · rw [if_neg hdU]
      have hz : c d = 0 := by
        rw [hc]
        exact moebius_tail_eq_zero_of_le U d (by omega)
      rw [hz]
      simp
  calc ‖∑ d ∈ Finset.Ioc 0 N, (c d : ℂ) *
        ∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖
      ≤ ∑ d ∈ Finset.Ioc 0 N,
          ‖(c d : ℂ) * ∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, (if U < d then
          ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ d ∈ Finset.Ioc U N,
          ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun d _ => rfl)
        ext d
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        omega
    _ ≤ ∑ t ∈ Finset.Icc t₀ Tmax, ∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
          ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ := by
        have hcover : Finset.Ioc U N ⊆
            (Finset.Icc t₀ Tmax).biUnion (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)) := by
          intro d hd
          simp only [Finset.mem_Ioc] at hd
          rw [Finset.mem_biUnion]
          refine ⟨Nat.log 2 d, ?_, ?_⟩
          · rw [Finset.mem_Icc, ht₀, hTmax]
            constructor
            · exact Nat.log_mono_right (by omega)
            · exact Nat.log_mono_right hd.2
          · rw [Finset.mem_Ico]
            constructor
            · exact Nat.pow_log_le_self 2 (by omega)
            · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) d
              rw [pow_succ] at this
              omega
        have hdisj : (↑(Finset.Icc t₀ Tmax) : Set ℕ).PairwiseDisjoint
            (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)) := by
          intro t₁ _ t₂ _ hne
          apply Finset.disjoint_left.mpr
          intro h h1 h2
          simp only [Finset.mem_Ico] at h1 h2
          rcases Nat.lt_or_ge t₁ t₂ with hlt | hge
          · have : (2 : ℕ) ^ (t₁ + 1) ≤ 2 ^ t₂ := Nat.pow_le_pow_right (by norm_num) hlt
            rw [pow_succ] at this
            omega
          · have hlt2 : t₂ < t₁ := lt_of_le_of_ne hge (Ne.symm hne)
            have : (2 : ℕ) ^ (t₂ + 1) ≤ 2 ^ t₁ := Nat.pow_le_pow_right (by norm_num) hlt2
            rw [pow_succ] at this
            omega
        calc ∑ d ∈ Finset.Ioc U N,
            ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖
            ≤ ∑ d ∈ (Finset.Icc t₀ Tmax).biUnion
                (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)),
                ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ :=
              Finset.sum_le_sum_of_subset_of_nonneg hcover (fun d _ _ => norm_nonneg _)
          _ = _ := Finset.sum_biUnion hdisj
    _ ≤ ∑ _t ∈ Finset.Icc t₀ Tmax, Real.sqrt ((N : ℝ) * Mom) := by
        apply Finset.sum_le_sum
        intro t ht
        simp only [Finset.mem_Icc] at ht
        apply Real.le_sqrt_of_sq_le
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t))
          (f := fun d => ‖∑ m ∈ Finset.Ioc V (N / d),
            (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖)
        rw [Nat.card_Ico] at hcs
        have hcard : ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) = ((2 : ℝ) ^ t) := by
          have hnat : (2 ^ t + 2 ^ t - 2 ^ t : ℕ) = 2 ^ t := Nat.add_sub_cancel _ _
          rw [hnat]
          push_cast
          ring
        have hmom := S4_block_second_moment a q hq ha α hα ghat (Real.log N)
          hghat0 hghatG N (2 ^ t) (2 ^ t + 2 ^ t) V (by positivity)
        -- monotone-in-t bounds
        have h2tN : (2 : ℕ) ^ t ≤ N := by
          calc (2 : ℕ) ^ t ≤ 2 ^ Tmax := Nat.pow_le_pow_right (by norm_num) ht.2
            _ ≤ N := by
              rw [hTmax]
              exact Nat.pow_log_le_self 2 (by omega)
        have hdivmono : (N / 2 ^ t : ℕ) ≤ (N / 2 ^ t₀ : ℕ) :=
          Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) ht.1) (by positivity)
        have hBA : ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) ≤ (N : ℝ) := by
          rw [hcard]
          exact_mod_cast h2tN
        have hdiv2 : ((((N / 2 ^ t : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
            ≤ ((((N / 2 ^ t₀ : ℕ)) / (q / 2) + 1 : ℕ) : ℝ) := by
          have : ((N / 2 ^ t : ℕ)) / (q / 2) ≤ ((N / 2 ^ t₀ : ℕ)) / (q / 2) :=
            Nat.div_le_div_right hdivmono
          exact_mod_cast Nat.add_le_add_right this 1
        have hmono : Real.log N ^ 2 * (((N / 2 ^ t : ℕ) : ℝ) + 1)
            * (((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
              + 2 * ((((N / 2 ^ t : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
                  + 4 * q * (1 + Real.log (2 * q))))
            ≤ Mom := by
          rw [hMom]
          have hf1 : (((N / 2 ^ t : ℕ) : ℝ) + 1) ≤ (((N / 2 ^ t₀ : ℕ) : ℝ) + 1) := by
            have : ((N / 2 ^ t : ℕ) : ℝ) ≤ ((N / 2 ^ t₀ : ℕ) : ℝ) := by exact_mod_cast hdivmono
            linarith
          have hf2 : (((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
              + 2 * ((((N / 2 ^ t : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q))))
              ≤ ((N : ℝ) + 2 * ((((N / 2 ^ t₀ : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * N + 4 * q * (1 + Real.log (2 * q)))) := by
            have hq4 : (0 : ℝ) ≤ 4 * q * (1 + Real.log (2 * q)) :=
              mul_nonneg (by positivity) hL0
            have hinner2 : 2 * ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
                + 4 * q * (1 + Real.log (2 * q))
                ≤ 2 * (N : ℝ) + 4 * q * (1 + Real.log (2 * q)) := by linarith
            have h2a : (0 : ℝ) ≤ 2 * ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
                + 4 * q * (1 + Real.log (2 * q)) := by positivity
            have := mul_le_mul hdiv2 hinner2 h2a (by positivity)
            nlinarith [hBA]
          have h0a : (0 : ℝ) ≤ Real.log N ^ 2 := by positivity
          have h0b : (0 : ℝ) ≤ (((N / 2 ^ t : ℕ) : ℝ) + 1) := by positivity
          have h0c : (0 : ℝ) ≤ (((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
              + 2 * ((((N / 2 ^ t : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
                  + 4 * q * (1 + Real.log (2 * q)))) := by
            have : (0 : ℝ) ≤ 4 * q * (1 + Real.log (2 * q)) :=
              mul_nonneg (by positivity) hL0
            positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hf1 h0a) hf2 h0c (by positivity)
        calc (∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
              ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖) ^ 2
            ≤ ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) *
                ∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
                  ‖∑ m ∈ Finset.Ioc V (N / d),
                    (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2 := by
              exact_mod_cast hcs
          _ ≤ ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) *
                (Real.log N ^ 2 * (((N / 2 ^ t : ℕ) : ℝ) + 1)
                  * (((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
                    + 2 * ((((N / 2 ^ t : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                      * (2 * ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
                        + 4 * q * (1 + Real.log (2 * q))))) :=
              mul_le_mul_of_nonneg_left hmom (by positivity)
          _ ≤ (N : ℝ) * Mom := by
              apply mul_le_mul hBA hmono _ (by positivity)
              have h0a : (0 : ℝ) ≤ Real.log N ^ 2 := by positivity
              have : (0 : ℝ) ≤ 4 * q * (1 + Real.log (2 * q)) :=
                mul_nonneg (by positivity) hL0
              positivity
    _ = ((Finset.Icc t₀ Tmax).card : ℝ) * Real.sqrt ((N : ℝ) * Mom) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.sqrt ((N : ℝ) * Mom) := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        have : (Finset.Icc t₀ Tmax).card ≤ Nat.log 2 N + 1 := by
          rw [Nat.card_Icc, hTmax]
          omega
        exact_mod_cast this

/-- **THE TIGHT S₄ BOUND** (Type-II, large-sieve strength): replaces the vacuous
    `S4_bound` (whose dyadic-boundary over-charge made the innermost factor `≥ N`,
    hence `‖S₄‖ ≥ N·log²N`, weaker than the trivial `ψ(N) ≈ N`) with the four-term
    geometric envelope from `s4_dyadic_assembly`. On a minor arc `P < q ≤ N/P` this is
    `≪ N·log²N/√P`, small enough to close the variance bound. -/
lemma S4_bound_tight (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U V N : ℕ)
    (hU1 : 1 ≤ U) (hN1 : 1 ≤ N) :
    ‖∑ n ∈ Finset.Ioc 0 N,
        (((((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U)
            * ((Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ))) n : ℝ) : ℂ)
          * e ((n : ℝ) * α)‖
      ≤ Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
          + Real.sqrt 32 * N
              * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ) / Real.sqrt q
          + 64 * N * Real.sqrt (1 + Real.log (2 * q)) / Real.sqrt U
          + 6 * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ)
              * Real.sqrt (N * q * (1 + Real.log (2 * q)))) := by
  set c : ArithmeticFunction ℝ :=
    (μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U with hc
  set gAF : ArithmeticFunction ℝ := (Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ) with hgAF
  set ghat : ℕ → ℝ := fun m => if m ≤ N then gAF m else 0 with hghat
  set t₀ : ℕ := Nat.log 2 (U + 1) with ht₀
  set Nmax : ℕ := N / (V + 1) with hNmax
  set Tmax : ℕ := Nat.log 2 Nmax with hTmax
  have hL0 : (0 : ℝ) ≤ 1 + Real.log (2 * q) := by
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have : (0 : ℝ) ≤ Real.log (2 * q) := Real.log_nonneg (by linarith)
    linarith
  have hN0 : 0 < N := hN1
  have hghat0 : ∀ m, 0 ≤ ghat m := by
    intro m
    rw [hghat]
    dsimp only
    split
    · exact tail_conv_nonneg V m
    · exact le_refl 0
  have hghatG : ∀ m, ghat m ≤ Real.log N := by
    intro m
    rw [hghat]
    dsimp only
    split
    · rename_i hm
      calc gAF m ≤ Real.log m := tail_conv_le_log V m
        _ ≤ Real.log N := log_natCast_monotone hm
    · exact log_natCast_nonneg N
  rw [show c * gAF = c * gAF from rfl,
    sum_Ioc_mul_weight_eq_sum_sum c gAF (fun n => e ((n : ℝ) * α)) N]
  have hinner : ∀ d ∈ Finset.Ioc 0 N,
      ∑ m ∈ Finset.Ioc 0 (N / d), (gAF m : ℂ) * e (((d * m : ℕ) : ℝ) * α)
      = ∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α) := by
    intro d hd
    simp only [Finset.mem_Ioc] at hd
    have step1 : ∑ m ∈ Finset.Ioc 0 (N / d), (gAF m : ℂ) * e (((d * m : ℕ) : ℝ) * α)
        = ∑ m ∈ Finset.Ioc 0 (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mem_Ioc] at hm
      have hmN : m ≤ N := le_trans hm.2 (Nat.div_le_self N d)
      rw [hghat]
      dsimp only
      rw [if_pos hmN]
      congr 1
      exact congrArg e (by push_cast; ring)
    rw [step1]
    symm
    apply Finset.sum_subset
    · intro m hm
      simp only [Finset.mem_Ioc] at hm ⊢
      omega
    · intro m hm hnot
      simp only [Finset.mem_Ioc] at hm hnot
      have hmV : m ≤ V := by omega
      have hz : ghat m = 0 := by
        rw [hghat]
        dsimp only
        split
        · exact tail_conv_eq_zero_of_le V m hmV
        · rfl
      rw [hz]
      simp
  rw [Finset.sum_congr rfl (fun d hd => by rw [hinner d hd])]
  have hterm : ∀ d ∈ Finset.Ioc 0 N,
      ‖(c d : ℂ) * ∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖
      ≤ (if U < d then
          ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ else 0) := by
    intro d _
    by_cases hdU : U < d
    · rw [if_pos hdU, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := abs_moebius_tail_le_one U d
      rw [hc]
      calc |(((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U) d)| *
            ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖
          ≤ 1 * ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = _ := one_mul _
    · rw [if_neg hdU]
      have hz : c d = 0 := by
        rw [hc]
        exact moebius_tail_eq_zero_of_le U d (by omega)
      rw [hz]
      simp
  calc ‖∑ d ∈ Finset.Ioc 0 N, (c d : ℂ) *
        ∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖
      ≤ ∑ d ∈ Finset.Ioc 0 N,
          ‖(c d : ℂ) * ∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, (if U < d then
          ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ d ∈ Finset.Ioc U N,
          ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun d _ => rfl)
        ext d
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        omega
    _ = ∑ d ∈ Finset.Ioc U Nmax,
          ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ := by
        refine (Finset.sum_subset
          (Finset.Ioc_subset_Ioc_right (Nat.div_le_self N (V + 1))) ?_).symm
        intro d hd hnotin
        simp only [Finset.mem_Ioc] at hd hnotin
        have hdNmax : Nmax < d := by
          by_contra hcon
          push_neg at hcon
          exact hnotin ⟨hd.1, hcon⟩
        have hd0 : 0 < d := by omega
        have hNlt : N < d * (V + 1) :=
          (Nat.div_lt_iff_lt_mul (by omega : 0 < V + 1)).mp hdNmax
        have hNdV : N / d ≤ V := by
          have : N / d < V + 1 :=
            (Nat.div_lt_iff_lt_mul hd0).mpr (by rw [Nat.mul_comm]; exact hNlt)
          omega
        have hempty : Finset.Ioc V (N / d) = ∅ := Finset.Ioc_eq_empty (by omega)
        rw [hempty, Finset.sum_empty, norm_zero]
    _ ≤ Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
          + Real.sqrt 32 * N * ((Tmax - t₀ + 1 : ℕ) : ℝ) / Real.sqrt q
          + 64 * N * Real.sqrt (1 + Real.log (2 * q)) / Real.sqrt U
          + 6 * ((Tmax - t₀ + 1 : ℕ) : ℝ) * Real.sqrt (N * q * (1 + Real.log (2 * q)))) := by
        by_cases hcase : t₀ ≤ Tmax
        · have ht0pos : 1 ≤ t₀ := by
            rw [ht₀]
            exact Nat.log_pos (by norm_num) (by omega)
          have hNmaxpos : 0 < Nmax := by
            rcases Nat.eq_zero_or_pos Nmax with h0 | h0
            · exfalso
              have hT0 : Tmax = 0 := by rw [hTmax, h0]; simp
              omega
            · exact h0
          have hUt0 : (U : ℝ) ≤ 2 * (2 : ℝ) ^ t₀ := by
            have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (U + 1)
            rw [← ht₀] at h
            have hUle : U ≤ 2 ^ (t₀ + 1) := by omega
            calc (U : ℝ) ≤ ((2 ^ (t₀ + 1) : ℕ) : ℝ) := by exact_mod_cast hUle
              _ = 2 * (2 : ℝ) ^ t₀ := by push_cast; ring
          have hTmaxN : (2 : ℝ) ^ Tmax ≤ (N : ℝ) / (V + 1) := by
            have h1 : (2 : ℕ) ^ Tmax ≤ Nmax := by
              rw [hTmax]; exact Nat.pow_log_le_self 2 (by omega)
            have hVR : (0 : ℝ) < (V : ℝ) + 1 := by positivity
            rw [le_div_iff₀ hVR]
            have h3 : Nmax * (V + 1) ≤ N := by rw [hNmax]; exact Nat.div_mul_le_self N (V + 1)
            calc (2 : ℝ) ^ Tmax * ((V : ℝ) + 1)
                ≤ (Nmax : ℝ) * ((V : ℝ) + 1) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  calc (2 : ℝ) ^ Tmax = ((2 ^ Tmax : ℕ) : ℝ) := by push_cast; ring
                    _ ≤ (Nmax : ℝ) := by exact_mod_cast h1
              _ = (((Nmax * (V + 1) : ℕ)) : ℝ) := by push_cast; ring
              _ ≤ (N : ℝ) := by exact_mod_cast h3
          have hcover : Finset.Ioc U Nmax ⊆
              (Finset.Icc t₀ Tmax).biUnion (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)) := by
            intro d hd
            simp only [Finset.mem_Ioc] at hd
            rw [Finset.mem_biUnion]
            refine ⟨Nat.log 2 d, ?_, ?_⟩
            · rw [Finset.mem_Icc, ht₀, hTmax]
              exact ⟨Nat.log_mono_right (by omega), Nat.log_mono_right hd.2⟩
            · rw [Finset.mem_Ico]
              refine ⟨Nat.pow_log_le_self 2 (by omega), ?_⟩
              have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) d
              rw [pow_succ] at this
              omega
          have hdisj : (↑(Finset.Icc t₀ Tmax) : Set ℕ).PairwiseDisjoint
              (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)) := by
            intro t₁ _ t₂ _ hne
            apply Finset.disjoint_left.mpr
            intro h h1 h2
            simp only [Finset.mem_Ico] at h1 h2
            rcases Nat.lt_or_ge t₁ t₂ with hlt | hge
            · have : (2 : ℕ) ^ (t₁ + 1) ≤ 2 ^ t₂ := Nat.pow_le_pow_right (by norm_num) hlt
              rw [pow_succ] at this; omega
            · have hlt2 : t₂ < t₁ := lt_of_le_of_ne hge (Ne.symm hne)
              have : (2 : ℕ) ^ (t₂ + 1) ≤ 2 ^ t₁ := Nat.pow_le_pow_right (by norm_num) hlt2
              rw [pow_succ] at this; omega
          calc ∑ d ∈ Finset.Ioc U Nmax,
                ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖
              ≤ ∑ d ∈ (Finset.Icc t₀ Tmax).biUnion
                  (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)),
                  ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ :=
                Finset.sum_le_sum_of_subset_of_nonneg hcover (fun d _ _ => norm_nonneg _)
            _ = ∑ t ∈ Finset.Icc t₀ Tmax, ∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
                  ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ :=
                Finset.sum_biUnion hdisj
            _ ≤ _ :=
                s4_dyadic_assembly N q V U t₀ Tmax hq hN1 hU1 hcase hUt0 hTmaxN
                  (fun t => ∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
                    ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖)
                  (fun t => Finset.sum_nonneg (fun d _ => norm_nonneg _))
                  (fun t ht => by
                    simp only [Finset.mem_Icc] at ht
                    have h2tN : (2 : ℕ) ^ t ≤ N := by
                      calc (2 : ℕ) ^ t ≤ 2 ^ Tmax := Nat.pow_le_pow_right (by norm_num) ht.2
                        _ ≤ Nmax := by rw [hTmax]; exact Nat.pow_log_le_self 2 (by omega)
                        _ ≤ N := Nat.div_le_self N (V + 1)
                    exact s4_block_hbnd a q N V t hq ha α hα ghat (Real.log N)
                      hghat0 hghatG hN1 h2tN)
        · have hle : Nmax ≤ U := by
            by_contra hcon
            push_neg at hcon
            exact hcase (by rw [ht₀, hTmax]; exact Nat.log_mono_right (by omega))
          rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
          apply mul_nonneg (Real.log_nonneg (by exact_mod_cast hN1))
          positivity

/-- **The S₃ bound**: the small Vaughan piece is at most `V·log V`. -/
lemma S3_bound (V N : ℕ) (α : ℝ) :
    ‖∑ n ∈ Finset.Ioc 0 N, ((truncate Λ V n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ (V : ℝ) * Real.log V := by
  calc ‖∑ n ∈ Finset.Ioc 0 N, ((truncate Λ V n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ ∑ n ∈ Finset.Ioc 0 N, ‖((truncate Λ V n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc 0 N, (if n ≤ V then Λ n else 0) := by
        apply Finset.sum_le_sum
        intro n _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (truncate_vonMangoldt_nonneg V n)]
        have he : ‖e ((n : ℝ) * α)‖ = 1 := by
          rw [e, Complex.norm_exp]
          have : (2 * (Real.pi : ℂ) * Complex.I * (((n : ℝ) * α : ℝ) : ℂ)).re = 0 := by
            simp [Complex.mul_re, Complex.mul_im]
          rw [this, Real.exp_zero]
        rw [he, mul_one, truncate_apply]
    _ ≤ ∑ n ∈ Finset.Ioc 0 V, Λ n := by
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
          omega
        · intro n _ _
          exact vonMangoldt_nonneg
    _ ≤ (V : ℝ) * Real.log V := sum_vonMangoldt_le V

/-- **THE VINOGRADOV SUP SKELETON**: `‖∑Λ(n)e(nα)‖ ≤ ‖S₁‖ + ‖S₂‖ + ‖S₃‖ + ‖S₄‖`
    for the truncated Vaughan pieces (each `‖Sᵢ‖` separately bounded by
    `S1_bound`/`S2_bound`/`S3_bound`/`S4_bound`). -/
lemma vinogradov_sup_skeleton (U V N : ℕ) (α : ℝ) :
    ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ ‖∑ n ∈ Finset.Ioc 0 N,
            (((truncate (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log) n : ℝ) : ℂ)
              * e ((n : ℝ) * α)‖
        + ‖∑ n ∈ Finset.Ioc 0 N,
            (((truncate (μ : ArithmeticFunction ℝ) U * truncate Λ V
                * (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
        + ‖∑ n ∈ Finset.Ioc 0 N, ((truncate Λ V n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
        + ‖∑ n ∈ Finset.Ioc 0 N,
            (((((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U)
                * ((Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ))) n : ℝ) : ℂ)
              * e ((n : ℝ) * α)‖ := by
  rw [vaughan_sum_decomposition (truncate (μ : ArithmeticFunction ℝ) U) (truncate Λ V)
    (fun n => e ((n : ℝ) * α)) N]
  have hassoc : ((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U)
      * (Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ)
      = ((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U)
      * ((Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ)) := mul_assoc _ _ _
  rw [hassoc]
  set S1 : ℂ := ∑ n ∈ Finset.Ioc 0 N,
      (((truncate (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log) n : ℝ) : ℂ)
        * e ((n : ℝ) * α) with hS1
  set S2 : ℂ := ∑ n ∈ Finset.Ioc 0 N,
      (((truncate (μ : ArithmeticFunction ℝ) U * truncate Λ V
          * (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * e ((n : ℝ) * α) with hS2
  set S3 : ℂ := ∑ n ∈ Finset.Ioc 0 N, ((truncate Λ V n : ℝ) : ℂ) * e ((n : ℝ) * α) with hS3
  set S4 : ℂ := ∑ n ∈ Finset.Ioc 0 N,
      (((((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U)
          * ((Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ))) n : ℝ) : ℂ)
        * e ((n : ℝ) * α) with hS4
  calc ‖S1 - S2 + S3 + S4‖
      ≤ ‖S1 - S2 + S3‖ + ‖S4‖ := norm_add_le _ _
    _ ≤ (‖S1 - S2‖ + ‖S3‖) + ‖S4‖ := by
        have := norm_add_le (S1 - S2) S3
        linarith
    _ ≤ ((‖S1‖ + ‖S2‖) + ‖S3‖) + ‖S4‖ := by
        have := norm_sub_le S1 S2
        linarith
    _ = ‖S1‖ + ‖S2‖ + ‖S3‖ + ‖S4‖ := by ring

/-- **THE VINOGRADOV MINOR-ARC SUP BOUND** — explicit, for any truncations `U, V`. -/
theorem vinogradov_sup (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U V N : ℕ)
    (hU : U ≤ N) (hUV : U * V ≤ N) (hUV1 : 1 ≤ U * V) :
    ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ 2 * Real.log (N + 1) *
          ((((Nat.log 2 U + 1 : ℕ) : ℝ) * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
            + 32 * U * (1 + Real.log (2 * q)) + 4 * N) + U)
        + Real.log (U * V) *
          (((Nat.log 2 (U * V) + 1 : ℕ) : ℝ)
              * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
            + 32 * (U * V) * (1 + Real.log (2 * q)) + 4 * N)
        + (V : ℝ) * Real.log V
        + ((Nat.log 2 N + 1 : ℕ) : ℝ) *
          Real.sqrt ((N : ℝ) * (Real.log N ^ 2
            * (((N / 2 ^ Nat.log 2 (U + 1) : ℕ) : ℝ) + 1)
            * ((N : ℝ) + 2 * ((((N / 2 ^ Nat.log 2 (U + 1) : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * N + 4 * q * (1 + Real.log (2 * q)))))) := by
  refine le_trans (vinogradov_sup_skeleton U V N α) ?_
  have h1 := S1_bound a q hq ha α hα U N hU
  have h2 := S2_bound a q hq ha α hα U V N hUV hUV1
  have h3 := S3_bound V N α
  have h4 := S4_bound a q hq ha α hα U V N
  linarith


lemma S2_bound_tight (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U V N : ℕ)
    (hUV : U * V ≤ N) (hUV1 : 1 ≤ U * V) :
    ‖∑ n ∈ Finset.Ioc 0 N,
        (((truncate (μ : ArithmeticFunction ℝ) U * truncate Λ V
            * (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ Real.log (U * V) *
          ((2 * (N : ℝ) / q) * (1 + Real.log (U * V))
            + ((U * V / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))) := by
  set c : ArithmeticFunction ℝ := truncate (μ : ArithmeticFunction ℝ) U * truncate Λ V with hc
  have hlogUV0 : (0 : ℝ) ≤ Real.log (U * V) := by
    apply Real.log_nonneg
    exact_mod_cast hUV1
  -- regroup + collapse ζ + normalize the e-argument
  have hre : ∑ n ∈ Finset.Ioc 0 N,
      ((c * (ζ : ArithmeticFunction ℝ)) n : ℂ) * e ((n : ℝ) * α)
      = ∑ t ∈ Finset.Ioc 0 N, (c t : ℂ) *
          ∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α)) := by
    rw [sum_Ioc_mul_weight_eq_sum_sum c (ζ : ArithmeticFunction ℝ)
      (fun n => e ((n : ℝ) * α)) N]
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    rw [sum_Ioc_zeta_mul (fun m => e (((t * m : ℕ) : ℝ) * α)) (N / t)]
    apply Finset.sum_congr rfl
    intro m _
    exact congrArg e (by push_cast; ring)
  rw [hre]
  -- cap the sum over the support
  set cap : ℕ → ℝ := fun t =>
    (if (t : ℝ) * α - round ((t : ℝ) * α) = 0 then ((N / t : ℕ) : ℝ)
     else min ((N / t : ℕ) : ℝ) (1 / (2 * |(t : ℝ) * α - round ((t : ℝ) * α)|))) with hcap
  have hcap0 : ∀ t, 0 ≤ cap t := by
    intro t
    rw [hcap]
    dsimp only
    split
    · positivity
    · exact le_min (by positivity) (by positivity)
  have hterm : ∀ t ∈ Finset.Ioc 0 N,
      ‖(c t : ℂ) * ∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α))‖
      ≤ (if t ≤ U * V then Real.log (U * V) * cap t else 0) := by
    intro t ht
    simp only [Finset.mem_Ioc] at ht
    by_cases htuv : t ≤ U * V
    · rw [if_pos htuv, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |c t| ≤ Real.log (U * V) := by
        calc |c t| ≤ Real.log t := abs_truncate_mul_le_log U V t
          _ ≤ Real.log (U * V) := by
            apply Real.log_le_log (by exact_mod_cast ht.1)
            exact_mod_cast htuv
      have h2 : ‖∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α))‖ ≤ cap t := by
        rw [hcap]
        exact exp_sum_Ioc_min_bound ((t : ℝ) * α) (N / t)
      exact mul_le_mul h1 h2 (norm_nonneg _) hlogUV0
    · rw [if_neg htuv]
      push_neg at htuv
      have hz : c t = 0 := truncate_mul_eq_zero_of_gt _ _ U V t htuv
      rw [hz]
      simp
  calc ‖∑ t ∈ Finset.Ioc 0 N, (c t : ℂ) *
        ∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α))‖
      ≤ ∑ t ∈ Finset.Ioc 0 N,
          ‖(c t : ℂ) * ∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ t ∈ Finset.Ioc 0 N, (if t ≤ U * V then Real.log (U * V) * cap t else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ t ∈ Finset.Ioc 0 (U * V), Real.log (U * V) * cap t := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun t _ => rfl)
        ext t
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, le_trans h2 hUV⟩, h2⟩
    _ = Real.log (U * V) * ∑ t ∈ Finset.Ioc 0 (U * V), cap t := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.log (U * V) *
        ((2 * (N : ℝ) / q) * (1 + Real.log (U * V))
          + ((U * V / (q / 2) + 1 : ℕ) : ℝ)
            * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))) := by
        apply mul_le_mul_of_nonneg_left _ hlogUV0
        have := min_sum_tight a q hq ha α hα N (U * V)
        rw [hcap]
        push_cast at this ⊢
        exact this

/-- `log` of a natural cast is nonneg (`log 0 = 0`). -/

lemma S1_bound_tight (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U N : ℕ) (hU : U ≤ N) :
    ‖∑ n ∈ Finset.Ioc 0 N,
        (((truncate (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log) n : ℝ) : ℂ)
          * e ((n : ℝ) * α)‖
      ≤ 2 * Real.log (N + 1) *
          (((2 * (N : ℝ) / q) * (1 + Real.log U)
            + ((U / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))) + U) := by
  have hlogN0 : (0 : ℝ) ≤ Real.log (N + 1) := by
    apply Real.log_nonneg
    push_cast
    linarith
  set cap : ℕ → ℝ := fun t =>
    (if (t : ℝ) * α - round ((t : ℝ) * α) = 0 then ((N / t : ℕ) : ℝ)
     else min ((N / t : ℕ) : ℝ) (1 / (2 * |(t : ℝ) * α - round ((t : ℝ) * α)|))) with hcap
  have hcap0 : ∀ t, 0 ≤ cap t := by
    intro t
    rw [hcap]
    dsimp only
    split
    · positivity
    · exact le_min (by positivity) (by positivity)
  -- regroup
  rw [sum_Ioc_mul_weight_eq_sum_sum (truncate (μ : ArithmeticFunction ℝ) U)
    ArithmeticFunction.log (fun n => e ((n : ℝ) * α)) N]
  -- per-d inner bound
  have hinner : ∀ d ∈ Finset.Ioc 0 N,
      ‖∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)‖
      ≤ 2 * Real.log (N + 1) * (cap d + 1) := by
    intro d hd
    simp only [Finset.mem_Ioc] at hd
    set M : ℕ := N / d with hM
    set β : ℝ := (d : ℝ) * α with hβ
    -- normalize the argument and the log
    have hstep1 : ∑ m ∈ Finset.Ioc 0 M, ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)
        = ∑ m ∈ Finset.Ioc 0 M, ((Real.log m : ℝ) : ℂ) * e ((m : ℝ) * β) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [ArithmeticFunction.log_apply]
      congr 1
      exact congrArg e (by rw [hβ]; push_cast; ring)
    -- extend Ioc 0 M to range (M+1) (the m = 0 term vanishes)
    have hstep2 : ∑ m ∈ Finset.Ioc 0 M, ((Real.log m : ℝ) : ℂ) * e ((m : ℝ) * β)
        = ∑ m ∈ Finset.range (M + 1), ((Real.log m : ℝ) : ℂ) * e ((m : ℝ) * β) := by
      apply Finset.sum_subset
      · intro m hm
        simp only [Finset.mem_Ioc] at hm
        simp only [Finset.mem_range]
        omega
      · intro m hm hnotm
        simp only [Finset.mem_range] at hm
        simp only [Finset.mem_Ioc] at hnotm
        have hm0 : m = 0 := by omega
        subst hm0
        simp
    -- the capped weight agrees with log on the range
    have hstep3 : ∑ m ∈ Finset.range (M + 1), ((Real.log m : ℝ) : ℂ) * e ((m : ℝ) * β)
        = ∑ m ∈ Finset.range (M + 1),
            ((Real.log ((min m (M + 1) : ℕ) : ℝ) : ℝ) : ℂ) * e ((m : ℝ) * β) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mem_range] at hm
      rw [min_eq_left (by omega : m ≤ M + 1)]
    have habel := abel_exp_sum (fun m => Real.log ((min m (M + 1) : ℕ) : ℝ))
      (fun m => log_natCast_nonneg _)
      (by
        intro x y h
        exact log_natCast_monotone (by omega : min x (M + 1) ≤ min y (M + 1)))
      (Real.log ((M + 1 : ℕ) : ℝ))
      (fun m => by exact log_natCast_monotone (min_le_right m (M + 1)))
      β (M + 1)
    have hlogM : Real.log ((M + 1 : ℕ) : ℝ) ≤ Real.log (N + 1) := by
      have h1 : (M : ℕ) + 1 ≤ N + 1 := by
        have : M ≤ N := hM ▸ Nat.div_le_self N d
        omega
      have := log_natCast_monotone (show (M + 1 : ℕ) ≤ (N + 1 : ℕ) from h1)
      push_cast at this ⊢
      exact this
    have hcapd : (if β - round β = 0 then ((M + 1 : ℕ) : ℝ)
        else min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|))) ≤ cap d + 1 := by
      have h1 := cap_succ_le β M
      have h2 : (if β - round β = 0 then (M : ℝ)
          else min (M : ℝ) (1 / (2 * |β - round β|))) = cap d := by
        rw [hcap, hβ, hM]
      rw [h2] at h1
      exact h1
    have hcapnn : (0 : ℝ) ≤ (if β - round β = 0 then ((M + 1 : ℕ) : ℝ)
        else min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|))) := by
      split
      · positivity
      · exact le_min (by positivity) (by positivity)
    calc ‖∑ m ∈ Finset.Ioc 0 M, ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)‖
        = ‖∑ m ∈ Finset.range (M + 1),
            ((Real.log ((min m (M + 1) : ℕ) : ℝ) : ℝ) : ℂ) * e ((m : ℝ) * β)‖ := by
          rw [hstep1, hstep2, hstep3]
      _ ≤ 2 * Real.log ((M + 1 : ℕ) : ℝ)
            * (if β - round β = 0 then ((M + 1 : ℕ) : ℝ)
               else min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|))) := by
          have := habel
          push_cast at this ⊢
          exact this
      _ ≤ 2 * Real.log (N + 1) * (cap d + 1) := by
          apply mul_le_mul
          · have : (0:ℝ) ≤ 2 := by norm_num
            nlinarith [hlogM]
          · exact hcapd
          · exact hcapnn
          · positivity
  -- support + assembly
  have hterm : ∀ d ∈ Finset.Ioc 0 N,
      ‖(truncate (μ : ArithmeticFunction ℝ) U d : ℂ) *
        ∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)‖
      ≤ (if d ≤ U then 2 * Real.log (N + 1) * (cap d + 1) else 0) := by
    intro d hd
    by_cases hdU : d ≤ U
    · rw [if_pos hdU, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |truncate (μ : ArithmeticFunction ℝ) U d| *
            ‖∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
              * e (((d * m : ℕ) : ℝ) * α)‖
          ≤ 1 * (2 * Real.log (N + 1) * (cap d + 1)) := by
            apply mul_le_mul (abs_truncate_moebius_le_one U d) (hinner d hd)
              (norm_nonneg _) (by norm_num)
        _ = 2 * Real.log (N + 1) * (cap d + 1) := one_mul _
    · rw [if_neg hdU]
      have hz : truncate (μ : ArithmeticFunction ℝ) U d = 0 := by
        rw [truncate_apply, if_neg hdU]
      rw [hz]
      simp
  calc ‖∑ d ∈ Finset.Ioc 0 N, (truncate (μ : ArithmeticFunction ℝ) U d : ℂ) *
        ∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)‖
      ≤ ∑ d ∈ Finset.Ioc 0 N,
          ‖(truncate (μ : ArithmeticFunction ℝ) U d : ℂ) *
            ∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
              * e (((d * m : ℕ) : ℝ) * α)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, (if d ≤ U then 2 * Real.log (N + 1) * (cap d + 1) else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ d ∈ Finset.Ioc 0 U, 2 * Real.log (N + 1) * (cap d + 1) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun t _ => rfl)
        ext t
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, le_trans h2 hU⟩, h2⟩
    _ = 2 * Real.log (N + 1) * (∑ d ∈ Finset.Ioc 0 U, cap d + U) := by
        have hsplit : ∀ d ∈ Finset.Ioc 0 U,
            2 * Real.log (N + 1) * (cap d + 1)
            = 2 * Real.log (N + 1) * cap d + 2 * Real.log (N + 1) := fun d _ => by ring
        rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 2 * Real.log (N + 1) *
        (((2 * (N : ℝ) / q) * (1 + Real.log U)
          + ((U / (q / 2) + 1 : ℕ) : ℝ)
            * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))) + U) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        have hd := min_sum_tight a q hq ha α hα N U
        have hsum : ∑ d ∈ Finset.Ioc 0 U, cap d
            ≤ (2 * (N : ℝ) / q) * (1 + Real.log U)
              + ((U / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))) := by
          calc ∑ d ∈ Finset.Ioc 0 U, cap d
              = ∑ h ∈ Finset.Ioc 0 U,
                  (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then ((N / h : ℕ) : ℝ)
                   else min ((N / h : ℕ) : ℝ)
                     (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) := by
                apply Finset.sum_congr rfl
                intro h _
                rw [hcap]
            _ ≤ _ := hd
        linarith

/-- Pointwise subtraction for arithmetic functions (no `sub_apply` in Mathlib). -/

theorem vinogradov_sup_tight (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U V N : ℕ)
    (hU : U ≤ N) (hUV : U * V ≤ N) (hUV1 : 1 ≤ U * V) :
    ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ 2 * Real.log (N + 1) *
          (((2 * (N : ℝ) / q) * (1 + Real.log U)
            + ((U / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))) + U)
        + Real.log (U * V) *
          ((2 * (N : ℝ) / q) * (1 + Real.log (U * V))
            + ((U * V / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))))
        + (V : ℝ) * Real.log V
        + ((Nat.log 2 N + 1 : ℕ) : ℝ) *
          Real.sqrt ((N : ℝ) * (Real.log N ^ 2
            * (((N / 2 ^ Nat.log 2 (U + 1) : ℕ) : ℝ) + 1)
            * ((N : ℝ) + 2 * ((((N / 2 ^ Nat.log 2 (U + 1) : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * N + 4 * q * (1 + Real.log (2 * q)))))) := by
  refine le_trans (vinogradov_sup_skeleton U V N α) ?_
  have h1 := S1_bound_tight a q hq ha α hα U N hU
  have h2 := S2_bound_tight a q hq ha α hα U V N hUV hUV1
  have h3 := S3_bound V N α
  have h4 := S4_bound a q hq ha α hα U V N
  linarith

/-- **THE TIGHT VINOGRADOV SUP BOUND** — with the large-sieve Type-II estimate
    (`S4_bound_tight`). The Type-II term is now the four-term geometric envelope
    `logN·(N/√(V+1) + N·k/√q + N/√U + k·√(Nq))·polylog`, small on minor arcs, rather
    than the vacuous `√(N·Mom) ≳ N·log²N` of `vinogradov_sup_tight`. -/
theorem vinogradov_sup_tight2 (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U V N : ℕ)
    (hU : U ≤ N) (hUV : U * V ≤ N) (hUV1 : 1 ≤ U * V) :
    ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ 2 * Real.log (N + 1) *
          (((2 * (N : ℝ) / q) * (1 + Real.log U)
            + ((U / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))) + U)
        + Real.log (U * V) *
          ((2 * (N : ℝ) / q) * (1 + Real.log (U * V))
            + ((U * V / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))))
        + (V : ℝ) * Real.log V
        + Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
            + Real.sqrt 32 * N
                * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ) / Real.sqrt q
            + 64 * N * Real.sqrt (1 + Real.log (2 * q)) / Real.sqrt U
            + 6 * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ)
                * Real.sqrt (N * q * (1 + Real.log (2 * q)))) := by
  have hN1 : 1 ≤ N := le_trans hUV1 hUV
  have hU1 : 1 ≤ U := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hUV1)
  refine le_trans (vinogradov_sup_skeleton U V N α) ?_
  have h1 := S1_bound_tight a q hq ha α hα U N hU
  have h2 := S2_bound_tight a q hq ha α hα U V N hUV hUV1
  have h3 := S3_bound V N α
  have h4 := S4_bound_tight a q hq ha α hα U V N hU1 hN1
  linarith

end VaughanDecomposition

end MinSum

end Principia.Common.Goldbach
