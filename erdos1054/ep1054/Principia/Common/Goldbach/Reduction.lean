/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Goldbach.Harc

/-!
# Almost-all binary Goldbach, `Reduction`: the density-zero reduction and almost-all binary Goldbach

Ported **verbatim** from the circle-method half of the comparator-certified master
`GoldbachChainMaster.lean` (PNT+ workspace, lines 31116–31712; there
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
open Principia.Common.SW (MediumPNTBound)

namespace Principia.Common.Goldbach
set_option maxHeartbeats 1000000
open Finset
open MinSum
open Finset
open MinorArc
open scoped ArithmeticFunction
open scoped ArithmeticFunction
open Finset
open MajorArcMainTerm
open Finset
open MeasureTheory
open Finset

open Finset

/-! # Almost-all Goldbach: an honest conditional reduction

`DensityZero notSumOfTwoPrimes` (the axiom `almost_all_binary_goldbach`) is reduced here to
the single analytic input of the Hardy–Littlewood circle method — a **variance bound** on the
Goldbach representation count against its main term — plus an elementary main-term lower bound.
Everything except that analytic input is proven (0 sorries; verified under
leanprover/lean4:v4.31.0 + Mathlib v4.31.0).
  #print axioms almost_all_goldbach_of_variance = [propext, Classical.choice, Quot.sound]
STATUS (updated 2026-09-26, Principia port): the section header above is the master's original
text from when the variance bound was still open. In this library the whole chain is proved.
`almost_all_binary_goldbach_of_mediumPNT` below discharges the variance bound from the ported
circle method (Vaughan, minor arcs, major arcs). Its only hypothesis, `MediumPNTBound`, is proved
by `Principia.Common.SW.mediumPNTBound` (the ported PNT+ MediumPNT). The unconditional statement is
`Principia.Erdos1054.Alt.almost_all_binary_goldbach_unconditional`. -/

namespace GoldbachReduction

/-- proof.lean's definitions, reproduced locally so the conclusion matches the axiom. -/
noncomputable def countUpTo (P : ℕ → Prop) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.range (X + 1)).filter P).card
def DensityZero (P : ℕ → Prop) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X ≥ X₀ → (countUpTo P X : ℚ) ≤ ε * X
def notSumOfTwoPrimes (n : ℕ) : Prop :=
  Even n ∧ ¬ ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- Number of primes `p ≤ n` with `n - p` also prime (ordered Goldbach representations). -/
def repCount (n : ℕ) : ℕ := ((range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime)).card

theorem repCount_eq_zero_iff (n : ℕ) :
    repCount n = 0 ↔ ¬ ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  rw [repCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · rintro h ⟨p, q, hp, hq, hpq⟩
    have hq2 := hq.two_le
    have hmem : p ∈ range (n + 1) := by rw [mem_range]; omega
    refine h hmem ⟨hp, ?_⟩
    have : n - p = q := by omega
    rw [this]; exact hq
  · rintro h p hp ⟨hpp, hnpp⟩
    rw [mem_range] at hp
    exact h ⟨p, n - p, hpp, hnpp, by omega⟩

/-! ## Brick 1 — second-moment (Chebyshev) bridge -/

theorem card_bad_le_of_sq_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ) (δ V : ℝ) (hδ : 0 < δ)
    (B : Finset ι) (hBs : B ⊆ s) (hB : ∀ i ∈ B, δ ≤ |g i|) (hV : ∑ i ∈ s, g i ^ 2 ≤ V) :
    (B.card : ℝ) * δ ^ 2 ≤ V := by
  have hsq : ∀ i ∈ B, δ ^ 2 ≤ g i ^ 2 := by
    intro i hi
    have : δ ^ 2 ≤ |g i| ^ 2 := by nlinarith [hB i hi, hδ, abs_nonneg (g i)]
    rwa [sq_abs] at this
  calc (B.card : ℝ) * δ ^ 2 = ∑ _i ∈ B, δ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ B, g i ^ 2 := Finset.sum_le_sum hsq
    _ ≤ ∑ i ∈ s, g i ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg hBs (fun i _ _ => by positivity)
    _ ≤ V := hV

/-! ## Brick 2 — dyadic density-zero criterion -/

variable (Bad : ℕ → Prop) [DecidablePred Bad]

theorem cnt_split (X : ℕ) :
    ((range (X + 1)).filter Bad).card
      = ((range (X / 2 + 1)).filter Bad).card + ((Ioc (X / 2) X).filter Bad).card := by
  have hsplit : range (X + 1) = range (X / 2 + 1) ∪ Ioc (X / 2) X := by
    ext n; simp only [mem_range, mem_union, mem_Ioc, Nat.lt_succ_iff]; omega
  have hdisj : Disjoint ((range (X / 2 + 1)).filter Bad) ((Ioc (X / 2) X).filter Bad) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]; intro n hn hn2
    simp only [mem_range, Nat.lt_succ_iff] at hn; simp only [mem_Ioc] at hn2; omega
  rw [hsplit, filter_union, Finset.card_union_of_disjoint hdisj]

theorem cnt_bound (ε : ℝ) (hε : 0 < ε) (X₀ : ℕ)
    (hblk : ∀ X, X₀ ≤ X → (((Ioc (X / 2) X).filter Bad).card : ℝ) ≤ ε * X) :
    ∀ X, (((range (X + 1)).filter Bad).card : ℝ) ≤ 2 * ε * X + (X₀ + 1) := by
  intro X
  induction X using Nat.strong_induction_on with
  | _ X IH =>
    by_cases hX : X₀ ≤ X
    · rcases Nat.eq_zero_or_pos X with hX0 | hXpos
      · subst hX0
        have hle : (((range (0 + 1)).filter Bad).card : ℝ) ≤ 1 := by
          have h := Finset.card_filter_le (range (0 + 1)) Bad
          simp only [Finset.card_range] at h
          have : (((range (0 + 1)).filter Bad).card : ℝ) ≤ ((0 : ℕ) + 1 : ℝ) := by exact_mod_cast h
          simpa using this
        push_cast; nlinarith [hle, hε]
      · have hhalf : X / 2 < X := Nat.div_lt_self hXpos (by norm_num)
        rw [cnt_split Bad X]
        have hIH := IH (X / 2) hhalf
        have hb := hblk X hX
        have hhcast : (2 : ℝ) * ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) := by
          have : 2 * (X / 2) ≤ X := by omega
          exact_mod_cast this
        push_cast; push_cast at hIH; nlinarith [hIH, hb, hε, hhcast]
    · have hle : (((range (X + 1)).filter Bad).card : ℝ) ≤ (X : ℝ) + 1 := by
        have h := Finset.card_filter_le (range (X + 1)) Bad
        simp only [Finset.card_range] at h; exact_mod_cast h
      have hXX0 : (X : ℝ) + 1 ≤ (X₀ : ℝ) + 1 := by
        have : X + 1 ≤ X₀ + 1 := by omega
        exact_mod_cast this
      have : (0 : ℝ) ≤ 2 * ε * X := by positivity
      linarith

theorem densityZero_of_block
    (h : ∀ ε : ℝ, 0 < ε → ∃ X₀, ∀ X, X₀ ≤ X →
        (((Ioc (X / 2) X).filter Bad).card : ℝ) ≤ ε * X) :
    ∀ ε : ℝ, 0 < ε → ∃ X₀, ∀ X, X₀ ≤ X →
        (((range (X + 1)).filter Bad).card : ℝ) ≤ ε * X := by
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := h (ε / 4) (by positivity)
  obtain ⟨X₁, hX₁⟩ := exists_nat_gt (2 * (X₀ + 1) / ε)
  refine ⟨max X₀ X₁, fun X hX => ?_⟩
  have hXX₁ : X₁ ≤ X := le_trans (le_max_right _ _) hX
  have hbound := cnt_bound Bad (ε / 4) (by positivity) X₀ hX₀ X
  have hXpos : (0 : ℝ) < X := by
    have : (0 : ℝ) < X₁ := lt_of_le_of_lt (by positivity) hX₁
    exact lt_of_lt_of_le this (by exact_mod_cast hXX₁)
  have hconst : ((X₀ : ℝ) + 1) ≤ ε / 2 * X := by
    have h2 : (X₁ : ℝ) ≤ X := by exact_mod_cast hXX₁
    have hle : 2 * ((X₀ : ℝ) + 1) / ε ≤ X := le_trans (le_of_lt hX₁) h2
    rw [div_le_iff₀ hε] at hle
    nlinarith [hle, hXpos, hε]
  calc (((range (X + 1)).filter Bad).card : ℝ)
      ≤ 2 * (ε / 4) * X + ((X₀ : ℝ) + 1) := hbound
    _ ≤ ε / 2 * X + ε / 2 * X := by rw [show 2 * (ε / 4) = ε / 2 by ring]; linarith [hconst]
    _ = ε * X := by ring

/-! ## The conditional reduction -/



/-! ## The WEIGHTED reduction — consuming the circle method directly -/

open ArithmeticFunction
open scoped ArithmeticFunction

/-- **Proper prime powers are rare**: the count of `m ≤ n` with `Λ(m) ≠ 0` but `m` not
    prime is at most `√n · (log₂n + 1)` — the elementary input for converting the
    Λ-weighted Goldbach count into the prime-pair count. -/
lemma card_properPrimePow_le (n : ℕ) :
    (((Finset.Ioc 0 n).filter (fun m => ¬ m.Prime ∧ Λ m ≠ 0)).card : ℝ)
      ≤ (Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) := by
  set s := (Finset.Ioc 0 n).filter (fun m => ¬ m.Prime ∧ Λ m ≠ 0) with hs
  have hcard : s.card ≤ (Nat.log 2 n + 1) * (Finset.Ioc 0 (Nat.sqrt n)).card := by
    apply Finset.card_le_mul_card_image_of_maps_to (f := Nat.minFac)
    · intro m hm
      rw [hs, Finset.mem_filter, Finset.mem_Ioc] at hm
      obtain ⟨⟨hm0, hmn⟩, hnp, hΛ⟩ := hm
      rw [ArithmeticFunction.vonMangoldt_ne_zero_iff] at hΛ
      obtain ⟨p, k, hp, hk, rfl⟩ := hΛ
      have hp' := hp.nat_prime
      have hmf : (p ^ k).minFac = p := Nat.Prime.pow_minFac hp' hk.ne'
      rw [hmf, Finset.mem_Ioc]
      have hk2 : 2 ≤ k := by
        by_contra hcon
        interval_cases k
        exact hnp (by simpa using hp')
      refine ⟨hp'.pos, ?_⟩
      rw [Nat.le_sqrt]
      calc p * p = p ^ 2 := by ring
        _ ≤ p ^ k := Nat.pow_le_pow_right hp'.pos hk2
        _ ≤ n := hmn
    · intro p _
      have hsubfiber : (s.filter (fun m => m.minFac = p)).card
          ≤ (Finset.Icc 2 (Nat.log 2 n)).card := by
        apply Finset.card_le_card_of_injOn (fun m => Nat.log p m)
        · intro m hm
          simp only [Finset.mem_coe, Finset.mem_filter] at hm
          obtain ⟨hms, hmf⟩ := hm
          rw [hs, Finset.mem_filter, Finset.mem_Ioc] at hms
          obtain ⟨⟨hm0, hmn⟩, hnp, hΛ⟩ := hms
          rw [ArithmeticFunction.vonMangoldt_ne_zero_iff] at hΛ
          obtain ⟨q, k, hq, hk, rfl⟩ := hΛ
          have hq' := hq.nat_prime
          have hqf : (q ^ k).minFac = q := Nat.Prime.pow_minFac hq' hk.ne'
          have hqp : q = p := by rw [← hqf, hmf]
          subst hqp
          have hk2 : 2 ≤ k := by
            by_contra hcon
            interval_cases k
            exact hnp (by simpa using hq')
          simp only [Finset.mem_coe, Finset.mem_Icc, Nat.log_pow hq'.one_lt]
          refine ⟨hk2, ?_⟩
          have h2k : 2 ^ k ≤ n := le_trans (Nat.pow_le_pow_left hq'.two_le k) hmn
          exact Nat.le_log_of_pow_le (by norm_num) h2k
        · intro m1 hm1 m2 hm2 heq
          simp only [Finset.mem_coe, Finset.mem_filter] at hm1 hm2
          obtain ⟨hms1, hmf1⟩ := hm1
          obtain ⟨hms2, hmf2⟩ := hm2
          rw [hs, Finset.mem_filter] at hms1 hms2
          obtain ⟨-, -, hΛ1⟩ := hms1
          obtain ⟨-, -, hΛ2⟩ := hms2
          rw [ArithmeticFunction.vonMangoldt_ne_zero_iff] at hΛ1 hΛ2
          obtain ⟨q1, k1, hq1, hk1, rfl⟩ := hΛ1
          obtain ⟨q2, k2, hq2, hk2, rfl⟩ := hΛ2
          have hq1' := hq1.nat_prime
          have hq2' := hq2.nat_prime
          have hf1 : (q1 ^ k1).minFac = q1 := Nat.Prime.pow_minFac hq1' hk1.ne'
          have hf2 : (q2 ^ k2).minFac = q2 := Nat.Prime.pow_minFac hq2' hk2.ne'
          have hq1p : q1 = p := by rw [← hf1, hmf1]
          have hq2p : q2 = p := by rw [← hf2, hmf2]
          subst hq1p
          subst hq2p
          simp only [Nat.log_pow hq1'.one_lt] at heq
          rw [heq]
      calc (s.filter (fun m => m.minFac = p)).card
          ≤ (Finset.Icc 2 (Nat.log 2 n)).card := hsubfiber
        _ ≤ Nat.log 2 n + 1 := by rw [Nat.card_Icc]; omega
  have hIoc : (Finset.Ioc 0 (Nat.sqrt n)).card = Nat.sqrt n := by
    rw [Nat.card_Ioc, Nat.sub_zero]
  rw [hIoc] at hcard
  calc (s.card : ℝ) ≤ ((Nat.log 2 n + 1) * Nat.sqrt n : ℕ) := by exact_mod_cast hcard
    _ = (Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) := by push_cast; ring

/-- **The bad-n bound**: if `n` is NOT a sum of two primes, the Λ-weighted representation
    count is supported on pairs containing a proper prime power, hence
    `≤ 2·log²n·√n·(log₂n+1)` — negligible against the main term `≍ n`. -/
lemma badRep_le (N n : ℕ) (hn : 1 ≤ n)
    (hbad : ¬ ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q) :
    ∑ pr ∈ (Finset.range N ×ˢ Finset.range N).filter (fun pr => pr.1 + pr.2 = n),
        Λ pr.1 * Λ pr.2
      ≤ 2 * Real.log n ^ 2 * ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1)) := by
  classical
  set F := (Finset.range N ×ˢ Finset.range N).filter (fun pr => pr.1 + pr.2 = n) with hF
  set F' := F.filter (fun pr => Λ pr.1 * Λ pr.2 ≠ 0) with hF'
  set PP := (Finset.Ioc 0 n).filter (fun m => ¬ m.Prime ∧ Λ m ≠ 0) with hPP
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hmem : ∀ pr ∈ F', pr.1 + pr.2 = n ∧ Λ pr.1 ≠ 0 ∧ Λ pr.2 ≠ 0 := by
    intro pr hpr
    rw [hF', Finset.mem_filter] at hpr
    obtain ⟨hprF, hne⟩ := hpr
    rw [hF, Finset.mem_filter] at hprF
    exact ⟨hprF.2, fun h => hne (by rw [h, zero_mul]),
      fun h => hne (by rw [h, mul_zero])⟩
  have hterm : ∀ pr ∈ F', Λ pr.1 * Λ pr.2 ≤ Real.log n ^ 2 := by
    intro pr hpr
    obtain ⟨hsum, h1, h2⟩ := hmem pr hpr
    have h1le : 2 ≤ pr.1 := (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h1).two_le
    have h2le : 2 ≤ pr.2 := (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h2).two_le
    have hb1 : Λ pr.1 ≤ Real.log n :=
      le_trans ArithmeticFunction.vonMangoldt_le_log
        (Real.log_le_log (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two h1le)
          (by exact_mod_cast Nat.le.intro hsum))
    have hb2 : Λ pr.2 ≤ Real.log n :=
      le_trans ArithmeticFunction.vonMangoldt_le_log
        (Real.log_le_log (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two h2le)
          (by exact_mod_cast Nat.le.intro (by omega : pr.2 + pr.1 = n)))
    calc Λ pr.1 * Λ pr.2 ≤ Real.log n * Real.log n :=
          mul_le_mul hb1 hb2 ArithmeticFunction.vonMangoldt_nonneg hlogn
      _ = Real.log n ^ 2 := (sq (Real.log n)).symm
  have hsplit : ∑ pr ∈ F', Λ pr.1 * Λ pr.2
      = (∑ pr ∈ F'.filter (fun pr => pr.1.Prime), Λ pr.1 * Λ pr.2)
        + ∑ pr ∈ F'.filter (fun pr => ¬ pr.1.Prime), Λ pr.1 * Λ pr.2 :=
    (Finset.sum_filter_add_sum_filter_not F' _ _).symm
  -- the ¬prime-first-coordinate class injects into PP via pr ↦ pr.1
  have hcardA : (F'.filter (fun pr => ¬ pr.1.Prime)).card ≤ PP.card := by
    apply Finset.card_le_card_of_injOn (fun pr => pr.1)
    · intro pr hpr
      simp only [Finset.mem_coe, Finset.mem_filter] at hpr
      obtain ⟨hprF', hnp⟩ := hpr
      obtain ⟨hsum, h1, _⟩ := hmem pr hprF'
      have h1le : 2 ≤ pr.1 := (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h1).two_le
      simp only [Finset.mem_coe, hPP, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨by omega, Nat.le.intro hsum⟩, hnp, h1⟩
    · intro p1 hp1 p2 hp2 heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hp1 hp2
      have hs1 := (hmem p1 hp1.1).1
      have hs2 := (hmem p2 hp2.1).1
      dsimp only at heq
      have : p1.2 = p2.2 := by omega
      exact Prod.ext heq this
  -- the prime-first-coordinate class: second coordinate is a proper prime power
  have hcardB : (F'.filter (fun pr => pr.1.Prime)).card ≤ PP.card := by
    apply Finset.card_le_card_of_injOn (fun pr => pr.2)
    · intro pr hpr
      simp only [Finset.mem_coe, Finset.mem_filter] at hpr
      obtain ⟨hprF', hp1⟩ := hpr
      obtain ⟨hsum, h1, h2⟩ := hmem pr hprF'
      have h2le : 2 ≤ pr.2 := (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h2).two_le
      have hnp2 : ¬ pr.2.Prime := by
        intro hp2
        exact hbad ⟨pr.1, pr.2, hp1, hp2, hsum.symm⟩
      simp only [Finset.mem_coe, hPP, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨by omega, Nat.le.intro (by omega : pr.2 + pr.1 = n)⟩, hnp2, h2⟩
    · intro p1 hp1 p2 hp2 heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hp1 hp2
      have hs1 := (hmem p1 hp1.1).1
      have hs2 := (hmem p2 hp2.1).1
      dsimp only at heq
      have : p1.1 = p2.1 := by omega
      exact Prod.ext this heq
  have hboundA : ∑ pr ∈ F'.filter (fun pr => ¬ pr.1.Prime), Λ pr.1 * Λ pr.2
      ≤ (PP.card : ℝ) * Real.log n ^ 2 := by
    calc ∑ pr ∈ F'.filter (fun pr => ¬ pr.1.Prime), Λ pr.1 * Λ pr.2
        ≤ ∑ _pr ∈ F'.filter (fun pr => ¬ pr.1.Prime), Real.log n ^ 2 :=
          Finset.sum_le_sum (fun pr hpr => hterm pr (Finset.mem_of_mem_filter pr hpr))
      _ = ((F'.filter (fun pr => ¬ pr.1.Prime)).card : ℝ) * Real.log n ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (PP.card : ℝ) * Real.log n ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcardA
  have hboundB : ∑ pr ∈ F'.filter (fun pr => pr.1.Prime), Λ pr.1 * Λ pr.2
      ≤ (PP.card : ℝ) * Real.log n ^ 2 := by
    calc ∑ pr ∈ F'.filter (fun pr => pr.1.Prime), Λ pr.1 * Λ pr.2
        ≤ ∑ _pr ∈ F'.filter (fun pr => pr.1.Prime), Real.log n ^ 2 :=
          Finset.sum_le_sum (fun pr hpr => hterm pr (Finset.mem_of_mem_filter pr hpr))
      _ = ((F'.filter (fun pr => pr.1.Prime)).card : ℝ) * Real.log n ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (PP.card : ℝ) * Real.log n ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcardB
  have hPPbound := card_properPrimePow_le n
  rw [← hPP] at hPPbound
  calc ∑ pr ∈ F, Λ pr.1 * Λ pr.2
      = ∑ pr ∈ F', Λ pr.1 * Λ pr.2 := (Finset.sum_filter_ne_zero F).symm
    _ = (∑ pr ∈ F'.filter (fun pr => pr.1.Prime), Λ pr.1 * Λ pr.2)
        + ∑ pr ∈ F'.filter (fun pr => ¬ pr.1.Prime), Λ pr.1 * Λ pr.2 := hsplit
    _ ≤ (PP.card : ℝ) * Real.log n ^ 2 + (PP.card : ℝ) * Real.log n ^ 2 :=
        add_le_add hboundB hboundA
    _ = 2 * Real.log n ^ 2 * (PP.card : ℝ) := by ring
    _ ≤ 2 * Real.log n ^ 2 * ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1)) := by
        apply mul_le_mul_of_nonneg_left hPPbound (by positivity)

/-- The Λ-weighted Goldbach representation sum over the window `{0,…,X}` — the object the
    circle method controls (`= R(n)` of `MinorArc.fourier_coeff_sq` with `N = X+1`). -/
noncomputable def repWeight (X n : ℕ) : ℝ :=
  ∑ pr ∈ (Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter (fun pr => pr.1 + pr.2 = n),
    Λ pr.1 * Λ pr.2

/-- **Almost-all Goldbach from the WEIGHTED variance bound** — the form the circle method
    actually produces. Requires: the main-term lower bound `δ` on the upper block, the
    elementary negligibility of prime-power contributions against `δ` (satisfied when
    `δ X ≫ √X log³X`, true for the HL main term `≍ X`), and the weighted variance bound. -/
theorem almost_all_goldbach_of_weighted_variance
    (m : ℕ → ℝ) (δ : ℕ → ℝ) (hδpos : ∀ X, 0 < δ X)
    (hmain : ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ n : ℕ, X / 2 < n → n ≤ X → Even n → δ X ≤ m n)
    (hnegl : ∃ X₁ : ℕ, ∀ X : ℕ, X₁ ≤ X → ∀ n : ℕ, X / 2 < n → n ≤ X →
        2 * Real.log n ^ 2 * ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1)) ≤ δ X / 2)
    (hvar : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∑ n ∈ Ioc (X / 2) X, (repWeight X n - m n) ^ 2 ≤ ε * X * δ X ^ 2) :
    DensityZero notSumOfTwoPrimes := by
  classical
  have hRform : ∀ ε : ℝ, 0 < ε → ∃ X₀, ∀ X, X₀ ≤ X →
      (((range (X + 1)).filter notSumOfTwoPrimes).card : ℝ) ≤ ε * X := by
    apply densityZero_of_block notSumOfTwoPrimes
    intro ε hε
    obtain ⟨Xm, hXm⟩ := hmain
    obtain ⟨Xn, hXn⟩ := hnegl
    obtain ⟨Xv, hXv⟩ := hvar (ε / 4) (by linarith)
    refine ⟨max Xm (max Xn Xv), fun X hX => ?_⟩
    have hXmX : Xm ≤ X := le_trans (le_max_left _ _) hX
    have hXnX : Xn ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
    have hXvX : Xv ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
    have hBbound : ∀ n ∈ (Ioc (X / 2) X).filter notSumOfTwoPrimes,
        δ X / 2 ≤ |repWeight X n - m n| := by
      intro n hn
      rw [mem_filter, mem_Ioc] at hn
      obtain ⟨⟨hn1, hn2⟩, hbad⟩ := hn
      have hRle : repWeight X n ≤ δ X / 2 := by
        unfold repWeight
        exact le_trans (badRep_le (X + 1) n (by omega) hbad.2) (hXn X hXnX n hn1 hn2)
      have hδm : δ X ≤ m n := hXm X hXmX n hn1 hn2 hbad.1
      calc δ X / 2 ≤ m n - repWeight X n := by linarith
        _ ≤ |m n - repWeight X n| := le_abs_self _
        _ = |repWeight X n - m n| := abs_sub_comm _ _
    have hcard := card_bad_le_of_sq_sum (Ioc (X / 2) X)
        (fun n => repWeight X n - m n) (δ X / 2)
        ((ε / 4) * X * δ X ^ 2) (by have := hδpos X; linarith)
        ((Ioc (X / 2) X).filter notSumOfTwoPrimes)
        (filter_subset _ _) hBbound (hXv X hXvX)
    have hδ2 : (0 : ℝ) < δ X ^ 2 := pow_pos (hδpos X) 2
    have hcard2 : ((((Ioc (X / 2) X).filter notSumOfTwoPrimes).card : ℝ)) * δ X ^ 2
        ≤ ε * X * δ X ^ 2 := by nlinarith [hcard]
    exact le_of_mul_le_mul_right hcard2 hδ2
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := hRform (ε : ℝ) (by exact_mod_cast hε)
  refine ⟨X₀, fun X hX => ?_⟩
  have hb := hX₀ X hX
  rw [countUpTo]
  have hcast : ((((range (X + 1)).filter notSumOfTwoPrimes).card : ℚ) : ℝ) ≤ (ε : ℝ) * X := by
    push_cast
    exact hb
  have hq : (((range (X + 1)).filter notSumOfTwoPrimes).card : ℚ) ≤ ε * X := by
    exact_mod_cast hcast
  simpa using hq

/-- **Phase D brick (d): the variance bound in `repWeight` / `Ioc(X/2,X]` form.**
    Repackages the abstract circle-method variance bound `hcv` (discharged by
    `RatedWindow.core_variance`, `N = X+1`) into the real-valued, upper-block form the
    reduction consumes: with `m_X n := Re (cmodel (X+1) n)`, eventually
    `∑_{n∈(X/2,X]} (repWeight X n − m_X n)² ≤ ε X³`. Bridges the complex weighted count
    `R_{X+1}(n) = (repWeight X n : ℂ)`, drops `(r−z.re)² ≤ ‖(r:ℂ)−z‖²`, and restricts
    `Ioc(X/2,X] ⊆ range(2(X+1))`; the `(X+1)³ ≤ 8X³` slack is absorbed by taking `ε/8`. -/
lemma core_variance_repWeight
    (cmodel : ℕ → ℕ → ℂ)
    (hcv : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ n ∈ Finset.range (2 * N),
        ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            ((Λ p.1 : ℝ) : ℂ) * ((Λ p.2 : ℝ) : ℂ)) - cmodel N n‖ ^ 2 ≤ ε * (N : ℝ) ^ 3)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X, (repWeight X n - (cmodel (X + 1) n).re) ^ 2 ≤ ε * (X : ℝ) ^ 3 := by
  obtain ⟨N₀, hb⟩ := hcv (ε / 8) (by linarith)
  refine ⟨max 1 N₀, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXN0 : N₀ ≤ X := le_trans (le_max_right _ _) hX
  have hXR : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX1
  have hRcast : ∀ n : ℕ,
      (∑ p ∈ (Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter (fun p => p.1 + p.2 = n),
          ((Λ p.1 : ℝ) : ℂ) * ((Λ p.2 : ℝ) : ℂ)) = ((repWeight X n : ℝ) : ℂ) := by
    intro n
    rw [repWeight, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro p _
    push_cast; ring
  have hpt : ∀ (r : ℝ) (z : ℂ), (r - z.re) ^ 2 ≤ ‖(r : ℂ) - z‖ ^ 2 := by
    intro r z
    have h1 : |((r : ℂ) - z).re| ≤ ‖(r : ℂ) - z‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    calc (r - z.re) ^ 2 = |r - z.re| ^ 2 := (sq_abs _).symm
      _ ≤ ‖(r : ℂ) - z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hbX := hb (X + 1) (by omega)
  have hsub : Finset.Ioc (X / 2) X ⊆ Finset.range (2 * (X + 1)) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_range]; omega
  calc ∑ n ∈ Finset.Ioc (X / 2) X, (repWeight X n - (cmodel (X + 1) n).re) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (X / 2) X,
          ‖(∑ p ∈ (Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter (fun p => p.1 + p.2 = n),
              ((Λ p.1 : ℝ) : ℂ) * ((Λ p.2 : ℝ) : ℂ)) - cmodel (X + 1) n‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro n _
        rw [hRcast n]
        exact hpt (repWeight X n) (cmodel (X + 1) n)
    _ ≤ ∑ n ∈ Finset.range (2 * (X + 1)),
          ‖(∑ p ∈ (Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter (fun p => p.1 + p.2 = n),
              ((Λ p.1 : ℝ) : ℂ) * ((Λ p.2 : ℝ) : ℂ)) - cmodel (X + 1) n‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n _ _; positivity
    _ ≤ ε / 8 * ((X : ℝ) + 1) ^ 3 := by
        have h := hbX
        rw [show ((X + 1 : ℕ) : ℝ) = (X : ℝ) + 1 by push_cast; ring] at h
        exact h
    _ ≤ ε * (X : ℝ) ^ 3 := by
        have hcube : ((X : ℝ) + 1) ^ 3 ≤ 8 * (X : ℝ) ^ 3 := by
          nlinarith [hXR, mul_nonneg (mul_nonneg (show (0:ℝ) ≤ (X:ℝ) by linarith)
            (show (0:ℝ) ≤ (X:ℝ) by linarith)) (show (0:ℝ) ≤ (X:ℝ) - 1 by linarith), sq_nonneg (X:ℝ)]
        nlinarith [mul_le_mul_of_nonneg_left hcube (show (0:ℝ) ≤ ε / 8 by linarith)]

/-- **Phase E brick (E0): the X-INDEXED weighted reduction.**
    Identical to `almost_all_goldbach_of_weighted_variance` except the main term is an
    X-indexed family `m : ℕ → ℕ → ℝ` (`m X n`) rather than a single `m : ℕ → ℝ`. The
    reduction processes one dyadic block `(X/2, X]` at a time, so `m` only ever appears as
    `m X n` at a fixed `X`; an X-indexed family therefore composes identically. This is what
    lets the circle method's *truncated* model `(cmodel (X+1) n).re` (whose truncation level
    `P = (log X)^9` is inherently X-dependent) serve as the main term — no globally
    X-independent singular-series main term is needed. -/
theorem almost_all_goldbach_of_weighted_variance_indexed
    (m : ℕ → ℕ → ℝ) (δ : ℕ → ℝ) (hδpos : ∀ X, 0 < δ X)
    (hmain : ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ n : ℕ, X / 2 < n → n ≤ X → Even n → δ X ≤ m X n)
    (hnegl : ∃ X₁ : ℕ, ∀ X : ℕ, X₁ ≤ X → ∀ n : ℕ, X / 2 < n → n ≤ X →
        2 * Real.log n ^ 2 * ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1)) ≤ δ X / 2)
    (hvar : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∑ n ∈ Ioc (X / 2) X, (repWeight X n - m X n) ^ 2 ≤ ε * X * δ X ^ 2) :
    DensityZero notSumOfTwoPrimes := by
  classical
  have hRform : ∀ ε : ℝ, 0 < ε → ∃ X₀, ∀ X, X₀ ≤ X →
      (((range (X + 1)).filter notSumOfTwoPrimes).card : ℝ) ≤ ε * X := by
    apply densityZero_of_block notSumOfTwoPrimes
    intro ε hε
    obtain ⟨Xm, hXm⟩ := hmain
    obtain ⟨Xn, hXn⟩ := hnegl
    obtain ⟨Xv, hXv⟩ := hvar (ε / 4) (by linarith)
    refine ⟨max Xm (max Xn Xv), fun X hX => ?_⟩
    have hXmX : Xm ≤ X := le_trans (le_max_left _ _) hX
    have hXnX : Xn ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
    have hXvX : Xv ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
    have hBbound : ∀ n ∈ (Ioc (X / 2) X).filter notSumOfTwoPrimes,
        δ X / 2 ≤ |repWeight X n - m X n| := by
      intro n hn
      rw [mem_filter, mem_Ioc] at hn
      obtain ⟨⟨hn1, hn2⟩, hbad⟩ := hn
      have hRle : repWeight X n ≤ δ X / 2 := by
        unfold repWeight
        exact le_trans (badRep_le (X + 1) n (by omega) hbad.2) (hXn X hXnX n hn1 hn2)
      have hδm : δ X ≤ m X n := hXm X hXmX n hn1 hn2 hbad.1
      calc δ X / 2 ≤ m X n - repWeight X n := by linarith
        _ ≤ |m X n - repWeight X n| := le_abs_self _
        _ = |repWeight X n - m X n| := abs_sub_comm _ _
    have hcard := card_bad_le_of_sq_sum (Ioc (X / 2) X)
        (fun n => repWeight X n - m X n) (δ X / 2)
        ((ε / 4) * X * δ X ^ 2) (by have := hδpos X; linarith)
        ((Ioc (X / 2) X).filter notSumOfTwoPrimes)
        (filter_subset _ _) hBbound (hXv X hXvX)
    have hδ2 : (0 : ℝ) < δ X ^ 2 := pow_pos (hδpos X) 2
    have hcard2 : ((((Ioc (X / 2) X).filter notSumOfTwoPrimes).card : ℝ)) * δ X ^ 2
        ≤ ε * X * δ X ^ 2 := by nlinarith [hcard]
    exact le_of_mul_le_mul_right hcard2 hδ2
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := hRform (ε : ℝ) (by exact_mod_cast hε)
  refine ⟨X₀, fun X hX => ?_⟩
  have hb := hX₀ X hX
  rw [countUpTo]
  have hcast : ((((range (X + 1)).filter notSumOfTwoPrimes).card : ℚ) : ℝ) ≤ (ε : ℝ) * X := by
    push_cast
    exact hb
  have hq : (((range (X + 1)).filter notSumOfTwoPrimes).card : ℚ) ≤ ε * X := by
    exact_mod_cast hcast
  simpa using hq

/-! ## Phase F — final composition

Assemble almost-all binary Goldbach from the pieces proven across the LeanSandbox files. The
singular-series/main-term results live in the MajorArcMainTerm segment and the circle-method
model in the RatedWindow segment. In this master file EVERY input is a proven theorem: the
`*_ax`-suffixed declarations below are proved aliases (the suffix is a historical artifact of
the per-file development, kept so downstream references are unchanged), and the major-arc L²
error `harc` is discharged by `harc_proven`. -/

section PhaseF

open scoped ArithmeticFunction
open ArithmeticFunction

/-- The truncated circle-method model coefficient, instantiated exactly as
    `core_variance` produces it. -/
noncomputable def cmodel : ℕ → ℕ → ℂ := fun N =>
  coeffModel N (Nat.floor ((Real.log N) ^ 9)) (N / Nat.floor ((Real.log N) ^ 9))

theorem core_variance_ax (hPNT : MediumPNTBound) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∑ n ∈ Finset.range (2 * N),
      ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
          ((Λ p.1 : ℝ) : ℂ) * ((Λ p.2 : ℝ) : ℂ)) - cmodel N n‖ ^ 2 ≤ ε * (N : ℝ) ^ 3 := by
  intro ε hε
  exact core_variance hPNT ε hε


theorem hmain_bound_ax : ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ n : ℕ, X / 2 < n → n ≤ X → Even n →
    ((X : ℝ) + 1) / 16 ≤ mainTerm X n := hmain_bound

theorem negl_bound_ax : ∀ c₀ : ℝ, 0 < c₀ → ∃ X₁ : ℕ, ∀ X : ℕ, X₁ ≤ X → ∀ n : ℕ,
    X / 2 < n → n ≤ X →
    2 * Real.log n ^ 2 * ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1)) ≤ c₀ * X / 2 := negl_bound

theorem hvar_of_arc_error_ax (repW cmodelRe mterm : ℕ → ℕ → ℝ)
    (hcore : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X, (repW X n - cmodelRe X n) ^ 2 ≤ ε * (X : ℝ) ^ 3)
    (harc : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X, (cmodelRe X n - mterm X n) ^ 2 ≤ ε * (X : ℝ) ^ 3) :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X, (repW X n - mterm X n) ^ 2
        ≤ ε * (X : ℝ) * (((X : ℝ) + 1) / 16) ^ 2 :=
  hvar_of_arc_error repW cmodelRe mterm hcore harc

/-- **Almost-all binary Goldbach — final assembly.** `DensityZero notSumOfTwoPrimes` (almost
    every even number is a sum of two primes) follows from the ONE remaining analytic input:
    the major-arc L² error `∑_{n∈(X/2,X]} (Re cmodel(X+1,n) − mainTerm(X,n))² ≤ εX³`. Everything
    else is proven: `hmain` (singular-series positivity `𝔖(n)≥1/4` + kernel bound), `hnegl`, and
    the variance bridge (`core_variance` → `core_variance_repWeight` → triangle). In this
    library `core_variance` also takes `MediumPNTBound` (through Siegel–Walfisz), so this
    theorem does too. -/
theorem almost_all_goldbach_final (hPNT : MediumPNTBound)
    (harc : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X, ((cmodel (X + 1) n).re - mainTerm X n) ^ 2 ≤ ε * (X : ℝ) ^ 3) :
    DensityZero notSumOfTwoPrimes := by
  apply almost_all_goldbach_of_weighted_variance_indexed mainTerm (fun X => ((X : ℝ) + 1) / 16)
  · intro X; positivity
  · exact hmain_bound_ax
  · obtain ⟨X₁, hX₁⟩ := negl_bound_ax (1 / 16) (by norm_num)
    refine ⟨X₁, fun X hX n hn1 hn2 => ?_⟩
    have h := hX₁ X hX n hn1 hn2
    have hXnn : (0 : ℝ) ≤ (X : ℝ) := by positivity
    calc 2 * Real.log n ^ 2 * ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1))
        ≤ 1 / 16 * (X : ℝ) / 2 := h
      _ ≤ ((X : ℝ) + 1) / 16 / 2 := by linarith
  · exact hvar_of_arc_error_ax repWeight (fun X n => (cmodel (X + 1) n).re) mainTerm
      (fun ε hε => core_variance_repWeight cmodel (core_variance_ax hPNT) ε hε) harc

end PhaseF

end GoldbachReduction

namespace GoldbachReduction

/-- **ALMOST-ALL BINARY GOLDBACH, from the explicit prime number theorem.** Almost every even
    number is a sum of two primes: the exceptional set has density zero. The master
    (`almost_all_binary_goldbach_proven`) is unconditional; here the one hypothesis is
    `MediumPNTBound`, which the Siegel–Walfisz port (`Principia.Common.SW`) still carries.
    Every other input is a proven theorem of this library (the circle method, minor and
    major arcs). -/
theorem almost_all_binary_goldbach_of_mediumPNT (hPNT : MediumPNTBound) :
    DensityZero notSumOfTwoPrimes := by
  apply almost_all_goldbach_final hPNT
  intro ε hε
  obtain ⟨X₀, h⟩ := harc_proven ε hε
  refine ⟨X₀, fun X hX => ?_⟩
  have hh := h X hX
  simpa only [cmodel, mainTerm, Tarithv] using hh

end GoldbachReduction

end Principia.Common.Goldbach
