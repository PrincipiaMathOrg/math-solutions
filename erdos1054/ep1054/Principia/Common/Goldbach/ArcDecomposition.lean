/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Goldbach.MinorArc

/-!
# Almost-all binary Goldbach, `ArcDecomposition`: the von Mangoldt Parseval identity and the major/minor arc decomposition

Ported **verbatim** from the circle-method half of the comparator-certified master
`GoldbachChainMaster.lean` (PNT+ workspace, lines 21552–23040; there
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
open MinSum
open Finset

namespace MinorArc
open Finset

section VonMangoldtParseval

open ArithmeticFunction
open scoped ArithmeticFunction

/-- **The Λ-weighted Parseval**: `∫₀¹ ‖∑_{n≤N} Λ(n)e(nα)‖² dα = ∑_{n≤N} Λ(n)²` —
    the variance integral's denominator. -/
lemma parseval_vonMangoldt (N : ℕ) :
    ∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ^ 2
      = ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 := by
  have hsub : Finset.Ioc 0 N ⊆ Finset.range (N + 1) := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    simp only [Finset.mem_range]
    omega
  have hzero : ∀ n ∈ Finset.range (N + 1), n ∉ Finset.Ioc 0 N →
      ((Λ n : ℝ) : ℂ) = 0 := by
    intro n hn hnot
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Ioc] at hnot
    have hn0 : n = 0 := by omega
    subst hn0
    rw [ArithmeticFunction.map_zero]
    norm_num
  have hsum_eq : ∀ α : ℝ,
      ∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)
      = ∑ n ∈ Finset.range (N + 1), ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α) := by
    intro α
    apply Finset.sum_subset hsub
    intro n hn hnot
    rw [hzero n hn hnot, zero_mul]
  calc ∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ^ 2
      = ∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.range (N + 1),
          ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro α _
        dsimp only
        rw [hsum_eq α]
    _ = ∑ n ∈ Finset.range (N + 1), ‖((Λ n : ℝ) : ℂ)‖ ^ 2 :=
        parseval (fun n => ((Λ n : ℝ) : ℂ)) (N + 1)
    _ = ∑ n ∈ Finset.range (N + 1), Λ n ^ 2 := by
        apply Finset.sum_congr rfl
        intro n _
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    _ = ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 := by
        symm
        apply Finset.sum_subset hsub
        intro n hn hnot
        simp only [Finset.mem_range] at hn
        simp only [Finset.mem_Ioc] at hnot
        have hn0 : n = 0 := by omega
        subst hn0
        rw [ArithmeticFunction.map_zero]
        norm_num

/-- The second-moment size: `∑_{n≤N} Λ(n)² ≤ N·(log N)²`. -/
lemma sum_vonMangoldt_sq_le (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 ≤ (N : ℝ) * Real.log N ^ 2 := by
  calc ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2
      ≤ ∑ _n ∈ Finset.Ioc 0 N, Real.log N ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        simp only [Finset.mem_Ioc] at hn
        have h1 : Λ n ≤ Real.log n := vonMangoldt_le_log
        have h2 : Real.log n ≤ Real.log N := by
          apply Real.log_le_log (by exact_mod_cast hn.1)
          exact_mod_cast hn.2
        have h3 : Λ n ≤ Real.log N := le_trans h1 h2
        exact pow_le_pow_left₀ vonMangoldt_nonneg h3 2
    _ = (N : ℝ) * Real.log N ^ 2 := by
        rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]

/-- The Λ-exponential sum is continuous in `α`. -/
lemma vonMangoldt_expsum_continuous (N : ℕ) :
    Continuous (fun α : ℝ => ∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) := by
  apply continuous_finsetSum
  intro n _
  unfold e
  fun_prop

/-- Any power of the Λ-exponential sum's norm is interval-integrable. -/
lemma vonMangoldt_expsum_pow_integrable (N k : ℕ) (a b : ℝ) :
    IntervalIntegrable
      (fun α : ℝ => ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ^ k)
      MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  exact ((vonMangoldt_expsum_continuous N).norm).pow k


open MeasureTheory in
/-- **Minor-arc L⁴ bound**: if the exp sum is ≤ C in sup on a measurable minor-arc set
    `m ⊆ (0,1]`, then `∫_m ‖S‖⁴ ≤ C² · ∑_{n≤N} Λ(n)²` — one factor `‖S‖²` capped by the
    sup, the other integrated out by Parseval. This is Vinogradov's fundamental trick. -/
lemma minor_arc_L4_bound (N : ℕ) (m : Set ℝ) (hm : MeasurableSet m)
    (hsub : m ⊆ Set.Ioc (0:ℝ) 1) (C : ℝ)
    (hsup : ∀ α ∈ m, ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ≤ C) :
    ∫ α in m, ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ^ 4
      ≤ C ^ 2 * ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 := by
  set S : ℝ → ℂ := fun α => ∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)
    with hS
  have hcont : Continuous S := vonMangoldt_expsum_continuous N
  have hint2 : IntegrableOn (fun α => ‖S α‖ ^ 2) (Set.Ioc (0:ℝ) 1) volume :=
    (hcont.norm.pow 2).integrableOn_Ioc
  have hint2m : IntegrableOn (fun α => ‖S α‖ ^ 2) m volume := hint2.mono_set hsub
  have hint4m : IntegrableOn (fun α => ‖S α‖ ^ 4) m volume :=
    ((hcont.norm.pow 4).integrableOn_Ioc).mono_set hsub
  rcases Set.eq_empty_or_nonempty m with hempty | ⟨α₀, hα₀⟩
  · rw [hempty]
    simp only [Measure.restrict_empty, integral_zero_measure]
    exact mul_nonneg (sq_nonneg C) (Finset.sum_nonneg fun n _ => sq_nonneg _)
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hsup α₀ hα₀)
  -- pointwise: ‖S‖⁴ ≤ C² ‖S‖² on m
  have hpt : ∀ α ∈ m, ‖S α‖ ^ 4 ≤ C ^ 2 * ‖S α‖ ^ 2 := by
    intro α hα
    have hsq : ‖S α‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hsup α hα) 2
    calc ‖S α‖ ^ 4 = ‖S α‖ ^ 2 * ‖S α‖ ^ 2 := by ring
      _ ≤ C ^ 2 * ‖S α‖ ^ 2 := mul_le_mul_of_nonneg_right hsq (by positivity)
  calc ∫ α in m, ‖S α‖ ^ 4
      ≤ ∫ α in m, C ^ 2 * ‖S α‖ ^ 2 :=
        setIntegral_mono_on hint4m (hint2m.const_mul _) hm hpt
    _ = C ^ 2 * ∫ α in m, ‖S α‖ ^ 2 := by rw [integral_const_mul]
    _ ≤ C ^ 2 * ∫ α in Set.Ioc (0:ℝ) 1, ‖S α‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply setIntegral_mono_set hint2
        · filter_upwards with α using by positivity
        · exact HasSubset.Subset.eventuallyLE hsub
    _ = C ^ 2 * ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 := by
        rw [← intervalIntegral.integral_of_le zero_le_one, parseval_vonMangoldt N]


open MeasureTheory in
/-- **The complete minor-arc variance piece**: on any minor-arc set where the Λ-exp-sum
    is ≤ Csup in sup, the L² error against ANY trig-polynomial main term is
    `≤ 2·Csup²·∑Λ(n)² + 2·∑‖c(n)‖²`. Composes L2_diff_le + minor_arc_L4_bound +
    setL2_le_circle + parseval; with `vinogradov_sup` as Csup this is the finished
    minor-arc half of the Goldbach variance bound. -/
theorem minor_arc_variance_piece (N M : ℕ) (m : Set ℝ) (hm : MeasurableSet m)
    (hsub : m ⊆ Set.Ioc (0:ℝ) 1) (c : ℕ → ℂ) (Csup : ℝ)
    (hsup : ∀ α ∈ m, ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ≤ Csup) :
    ∫ α in m, ‖(∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) ^ 2
        - ∑ n ∈ Finset.range M, c n * e ((n : ℝ) * α)‖ ^ 2
      ≤ 2 * (Csup ^ 2 * ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2)
        + 2 * ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := by
  have hS : Continuous (fun α : ℝ => ∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) :=
    vonMangoldt_expsum_continuous N
  have hCp : Continuous (fun α : ℝ => ∑ n ∈ Finset.range M, c n * e ((n : ℝ) * α)) := by
    apply continuous_finsetSum
    intro n _
    unfold e
    fun_prop
  have h1 := L2_diff_le _ _ (hS.pow 2) hCp m hm hsub
  have h2 : (∫ α in m,
      ‖(∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) ^ 2‖ ^ 2)
      ≤ Csup ^ 2 * ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 := by
    have hcongr : (∫ α in m,
        ‖(∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) ^ 2‖ ^ 2)
        = ∫ α in m, ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ^ 4 := by
      apply setIntegral_congr_fun hm
      intro α _
      dsimp only
      rw [norm_pow, ← pow_mul]
    rw [hcongr]
    exact minor_arc_L4_bound N m hm hsub Csup hsup
  have h3 : (∫ α in m, ‖∑ n ∈ Finset.range M, c n * e ((n : ℝ) * α)‖ ^ 2)
      ≤ ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := by
    calc (∫ α in m, ‖∑ n ∈ Finset.range M, c n * e ((n : ℝ) * α)‖ ^ 2)
        ≤ ∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.range M, c n * e ((n : ℝ) * α)‖ ^ 2 :=
          setL2_le_circle _ hCp m hsub
      _ = ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := parseval c M
  linarith


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


/-- **Non-unit residue classes carry negligible Λ-mass**: if `gcd(r,q) > 1`, every
    prime in the class `n ≡ r (q)` divides `q` (finitely many, ≤ q+1) and everything
    else is a proper prime power (≤ √t·(log₂t+1)); each term is ≤ log t. Hence the
    class sum is `O(√t · polylog t) = o(t)` — its Cesàro density is 0, completing
    `major_window_eval`'s hypothesis for `g = Λ` off the units. -/
lemma nonunit_class_vonMangoldt_sum_le (q r t : ℕ) (hq : 0 < q) (hd : 1 < Nat.gcd r q) :
    ∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n
      ≤ ((q : ℝ) + 1) * Real.log t
        + (Nat.sqrt t : ℝ) * (Nat.log 2 t + 1) * Real.log t := by
  classical
  set F := (Finset.range t).filter (fun n => n % q = r) with hF
  have hlogt : 0 ≤ Real.log t := Real.log_natCast_nonneg t
  have hterm : ∀ n ∈ F, Λ n ≤ Real.log t := by
    intro n hn
    rw [hF, Finset.mem_filter, Finset.mem_range] at hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simpa using hlogt
    calc Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
      _ ≤ Real.log t := Real.log_le_log (by exact_mod_cast hn0)
          (by exact_mod_cast hn.1.le)
  have hΛnn : ∀ n, 0 ≤ Λ n := fun n => ArithmeticFunction.vonMangoldt_nonneg
  rw [← Finset.sum_filter_add_sum_filter_not F (fun n => n.Prime) Λ]
  have hprime_bound : ∑ n ∈ F.filter (fun n => n.Prime), Λ n ≤ ((q : ℝ) + 1) * Real.log t := by
    have hsub : F.filter (fun n => n.Prime) ⊆ Finset.range (q + 1) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      obtain ⟨hnF, hp⟩ := hn
      rw [hF, Finset.mem_filter] at hnF
      have hgcd : Nat.gcd n q = Nat.gcd r q := by
        rw [Nat.gcd_comm n q, Nat.gcd_rec q n, hnF.2]
      have hdvd : n ∣ q := by
        have h1 : Nat.gcd n q ∣ n := Nat.gcd_dvd_left n q
        have h2 : 1 < Nat.gcd n q := by rw [hgcd]; exact hd
        rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ h1) with h | h
        · omega
        · rw [← h]
          exact Nat.gcd_dvd_right n q
      rw [Finset.mem_range]
      have := Nat.le_of_dvd hq hdvd
      omega
    calc ∑ n ∈ F.filter (fun n => n.Prime), Λ n
        ≤ ∑ _n ∈ F.filter (fun n => n.Prime), Real.log t :=
          Finset.sum_le_sum (fun n hn => hterm n (Finset.mem_of_mem_filter n hn))
      _ = ((F.filter (fun n => n.Prime)).card : ℝ) * Real.log t := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((q : ℝ) + 1) * Real.log t := by
          apply mul_le_mul_of_nonneg_right _ hlogt
          have := Finset.card_le_card hsub
          rw [Finset.card_range] at this
          exact_mod_cast this
  have hpp_bound : ∑ n ∈ F.filter (fun n => ¬ n.Prime), Λ n
      ≤ (Nat.sqrt t : ℝ) * (Nat.log 2 t + 1) * Real.log t := by
    have hdrop : ∑ n ∈ F.filter (fun n => ¬ n.Prime), Λ n
        = ∑ n ∈ (F.filter (fun n => ¬ n.Prime)).filter (fun n => Λ n ≠ 0), Λ n :=
      (Finset.sum_filter_ne_zero _).symm
    rw [hdrop]
    have hsub : (F.filter (fun n => ¬ n.Prime)).filter (fun n => Λ n ≠ 0)
        ⊆ (Finset.Ioc 0 t).filter (fun m => ¬ m.Prime ∧ Λ m ≠ 0) := by
      intro n hn
      simp only [Finset.mem_filter] at hn
      obtain ⟨⟨hnF, hnp⟩, hΛ⟩ := hn
      rw [hF, Finset.mem_filter, Finset.mem_range] at hnF
      rw [Finset.mem_filter, Finset.mem_Ioc]
      have h2 : 2 ≤ n := (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ).two_le
      exact ⟨⟨by omega, by omega⟩, hnp, hΛ⟩
    calc ∑ n ∈ (F.filter (fun n => ¬ n.Prime)).filter (fun n => Λ n ≠ 0), Λ n
        ≤ ∑ n ∈ (Finset.Ioc 0 t).filter (fun m => ¬ m.Prime ∧ Λ m ≠ 0), Λ n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hΛnn n)
      _ ≤ ∑ _n ∈ (Finset.Ioc 0 t).filter (fun m => ¬ m.Prime ∧ Λ m ≠ 0), Real.log t := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_filter, Finset.mem_Ioc] at hn
          rcases Nat.eq_zero_or_pos n with rfl | hn0
          · simpa using hlogt
          calc Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
            _ ≤ Real.log t := Real.log_le_log (by exact_mod_cast hn0)
                (by exact_mod_cast hn.1.2)
      _ = ((((Finset.Ioc 0 t).filter (fun m => ¬ m.Prime ∧ Λ m ≠ 0)).card : ℝ))
            * Real.log t := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Nat.sqrt t : ℝ) * (Nat.log 2 t + 1) * Real.log t :=
          mul_le_mul_of_nonneg_right (card_properPrimePow_le t) hlogt
  linarith


open Filter Real in
/-- **Non-unit classes have Cesàro density 0** (ℂ-cast form consumed by
    `major_window_eval`): the `O(√t·polylog)` mass bound divided by `t` vanishes. -/
lemma nonunit_class_tendsto_zero (q r : ℕ) (hq : 0 < q) (hd : 1 < Nat.gcd r q) :
    Filter.Tendsto (fun t : ℕ =>
      (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ)) / (t : ℂ))
      Filter.atTop (nhds 0) := by
  set f : ℕ → ℝ := fun t =>
    (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n) / (t : ℝ) with hf
  have hreal : Tendsto f atTop (nhds 0) := by
    set K : ℝ := 8 * ((q : ℝ) + 1) + 136 with hK
    have hg0 : Tendsto (fun t : ℕ => K * (t : ℝ) ^ (-(1/8) : ℝ)) atTop (nhds 0) := by
      have h2 : Tendsto (fun t : ℕ => ((t : ℝ)) ^ (-(1/8) : ℝ)) atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
      simpa using h2.const_mul K
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg0
    · apply Eventually.of_forall
      intro t
      apply div_nonneg (Finset.sum_nonneg fun n _ => vonMangoldt_nonneg) (Nat.cast_nonneg t)
    · filter_upwards [eventually_ge_atTop 2] with t ht
      have ht0 : (0:ℝ) < (t:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two ht
      have ht1 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast le_trans (by norm_num : (1:ℕ) ≤ 2) ht
      have hrp1 : (1:ℝ) ≤ (t:ℝ) ^ ((1/8) : ℝ) := Real.one_le_rpow ht1 (by norm_num)
      have hrpnn : (0:ℝ) ≤ (t:ℝ) ^ ((1/8) : ℝ) := by positivity
      -- log t ≤ 8 t^{1/8}
      have hlog8 : Real.log t ≤ 8 * (t:ℝ) ^ ((1/8) : ℝ) := by
        have h := Real.log_le_rpow_div (le_of_lt ht0) (show (0:ℝ) < 1/8 by norm_num)
        have h8 : (t:ℝ) ^ ((1/8) : ℝ) / (1/8) = 8 * (t:ℝ) ^ ((1/8) : ℝ) := by ring
        linarith [h, h8.le, h8.ge]
      have hlognn : (0:ℝ) ≤ Real.log t := Real.log_natCast_nonneg t
      -- Nat.log 2 t + 1 ≤ 17 t^{1/8}
      have hnlog : (Nat.log 2 t : ℝ) + 1 ≤ 17 * (t:ℝ) ^ ((1/8) : ℝ) := by
        have hpow : (2:ℕ) ^ (Nat.log 2 t) ≤ t := Nat.pow_log_le_self 2 (by omega)
        have hlogle : (Nat.log 2 t : ℝ) * Real.log 2 ≤ Real.log t := by
          have hcast : ((2:ℕ) ^ (Nat.log 2 t) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hpow
          have := Real.log_le_log (by positivity) hcast
          rwa [Real.log_pow, Nat.cast_ofNat] at this
        have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
        have hk2 : (Nat.log 2 t : ℝ) ≤ 2 * Real.log t := by
          nlinarith [hlogle, hl2, (by positivity : (0:ℝ) ≤ ((Nat.log 2 t : ℕ) : ℝ))]
        nlinarith [hlog8, hrp1]
      -- Nat.sqrt t ≤ t^{1/2}
      have hsqrt : (Nat.sqrt t : ℝ) ≤ (t:ℝ) ^ ((1/2) : ℝ) := by
        have h1 : (Nat.sqrt t : ℝ) ^ 2 ≤ (t : ℝ) := by
          exact_mod_cast Nat.sqrt_le' t
        have h4 : (Nat.sqrt t : ℝ) ≤ Real.sqrt (t:ℝ) :=
          (Real.le_sqrt (Nat.cast_nonneg _) (le_of_lt ht0)).mpr h1
        rwa [Real.sqrt_eq_rpow] at h4
      -- assemble
      have hsum := nonunit_class_vonMangoldt_sum_le q r t hq hd
      have hnum : (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
          ≤ 8 * ((q:ℝ) + 1) * (t:ℝ) ^ ((1/8) : ℝ) + 136 * (t:ℝ) ^ ((3/4) : ℝ) := by
        have hA : ((q : ℝ) + 1) * Real.log t ≤ 8 * ((q:ℝ) + 1) * (t:ℝ) ^ ((1/8) : ℝ) := by
          have hq1 : (0:ℝ) ≤ (q:ℝ) + 1 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hlog8 hq1]
        have hB : (Nat.sqrt t : ℝ) * (Nat.log 2 t + 1) * Real.log t
            ≤ 136 * (t:ℝ) ^ ((3/4) : ℝ) := by
          have hs1 : (Nat.sqrt t : ℝ) * ((Nat.log 2 t : ℝ) + 1) * Real.log t
              ≤ (t:ℝ) ^ ((1/2) : ℝ) * (17 * (t:ℝ) ^ ((1/8) : ℝ)) * (8 * (t:ℝ) ^ ((1/8) : ℝ)) := by
            apply mul_le_mul
            · apply mul_le_mul hsqrt hnlog (by positivity) (by positivity)
            · exact hlog8
            · exact hlognn
            · positivity
          have hcollect : (t:ℝ) ^ ((1/2) : ℝ) * (17 * (t:ℝ) ^ ((1/8) : ℝ))
                * (8 * (t:ℝ) ^ ((1/8) : ℝ))
              = 136 * ((t:ℝ) ^ ((1/2) : ℝ) * (t:ℝ) ^ ((1/8) : ℝ) * (t:ℝ) ^ ((1/8) : ℝ)) := by
            ring
          have hexp : (t:ℝ) ^ ((1/2) : ℝ) * (t:ℝ) ^ ((1/8) : ℝ) * (t:ℝ) ^ ((1/8) : ℝ)
              = (t:ℝ) ^ ((3/4) : ℝ) := by
            rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]
            norm_num
          rw [hcollect, hexp] at hs1
          exact hs1
        linarith
      -- divide by t and compare exponents
      rw [hf]
      have hdiv : (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n) / (t:ℝ)
          ≤ (8 * ((q:ℝ) + 1) * (t:ℝ) ^ ((1/8) : ℝ) + 136 * (t:ℝ) ^ ((3/4) : ℝ)) / (t:ℝ) := by
        gcongr
      have hsplit : (8 * ((q:ℝ) + 1) * (t:ℝ) ^ ((1/8) : ℝ) + 136 * (t:ℝ) ^ ((3/4) : ℝ)) / (t:ℝ)
          = 8 * ((q:ℝ) + 1) * (t:ℝ) ^ ((1/8 - 1) : ℝ) + 136 * (t:ℝ) ^ ((3/4 - 1) : ℝ) := by
        rw [Real.rpow_sub ht0, Real.rpow_sub ht0, Real.rpow_one]
        ring
      have hmono1 : (t:ℝ) ^ ((1/8 - 1) : ℝ) ≤ (t:ℝ) ^ (-(1/8) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
      have hmono2 : (t:ℝ) ^ ((3/4 - 1) : ℝ) ≤ (t:ℝ) ^ (-(1/8) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
      have hKnn : (0:ℝ) ≤ (t:ℝ) ^ (-(1/8) : ℝ) := by positivity
      calc (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n) / (t:ℝ)
          ≤ 8 * ((q:ℝ) + 1) * (t:ℝ) ^ ((1/8 - 1) : ℝ) + 136 * (t:ℝ) ^ ((3/4 - 1) : ℝ) := by
            rw [← hsplit]
            exact hdiv
        _ ≤ K * (t:ℝ) ^ (-(1/8) : ℝ) := by
            rw [hK]
            have hq1 : (0:ℝ) ≤ 8 * ((q:ℝ) + 1) := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hmono1 hq1,
              mul_le_mul_of_nonneg_left hmono2 (show (0:ℝ) ≤ 136 by norm_num)]
  have hcast : (fun t : ℕ =>
      (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ)) / (t : ℂ))
      = fun t => ((f t : ℝ) : ℂ) := by
    funext t
    rw [hf]
    push_cast
    ring
  rw [hcast]
  have hcomp := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp hreal
  rw [Complex.ofReal_zero] at hcomp
  exact hcomp



open Filter in
/-- **The von Mangoldt window evaluation**, conditional on EXACTLY the `WeakPNT_AP`
    statement shape (verified in PNT+ for every fixed `q`; hypothesis dischargeable at
    link time). Every Farey window evaluation of `∑Λ(n)e(nα)` against its model, with
    no uniformity in `q`. -/
theorem vonMangoldt_window_eval (q : ℕ) (hq : 0 < q)
    (hAP : ∀ r, r < q → Nat.gcd r q = 1 →
      Filter.Tendsto (fun t : ℕ =>
        (∑ n ∈ Finset.range t, if n % q = r then Λ n else 0) / (t : ℝ))
        Filter.atTop (nhds (1 / (Nat.totient q : ℝ))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ a : ℤ, ∀ β : ℝ,
      ‖(∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β)))
        - (∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
          * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖
      ≤ (q : ℝ) * ((ε * N + C) * (1 + 2 * Real.pi * N * |β|)) := by
  apply major_window_eval (fun n => ((Λ n : ℝ) : ℂ)) q hq (lambdaModel q) _ ε hε
  intro r hr
  by_cases hu : Nat.gcd r q = 1
  · -- unit class: convert WeakPNT_AP's real if-form to the ℂ filter form
    have hAPr := hAP r hr hu
    have hfun : (fun t : ℕ =>
        (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ)) / (t : ℂ))
        = fun t : ℕ =>
          (((∑ n ∈ Finset.range t, if n % q = r then Λ n else 0) / (t : ℝ) : ℝ) : ℂ) := by
      funext t
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      push_cast
      ring
    rw [hfun]
    have hmodel : lambdaModel q r = (((1 / (Nat.totient q : ℝ)) : ℝ) : ℂ) := by
      rw [lambdaModel, if_pos hu]
      push_cast
      ring
    rw [hmodel]
    exact (Complex.continuous_ofReal.tendsto _).comp hAPr
  · -- non-unit class: density zero
    have hd : 1 < Nat.gcd r q := by
      have h0 : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
      omega
    have hmodel : lambdaModel q r = 0 := by
      rw [lambdaModel, if_neg hu]
    rw [hmodel]
    exact nonunit_class_tendsto_zero q r hq hd


open ArithmeticFunction in
/-- **The model coefficient in closed form**: at a reduced fraction `a/q`, the window
    model's coefficient is `μ(q)/φ(q)` — the Hardy–Littlewood singular-series local
    factor. -/
lemma lambdaModel_coeff (a : ℤ) (q : ℕ) (hq : 0 < q) (ha : Int.gcd a q = 1) :
    ∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r
      = (ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ) := by
  calc ∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r
      = ∑ r ∈ Finset.range q,
          if Nat.gcd r q = 1 then e ((a : ℝ) * r / q) * (1 / (Nat.totient q : ℂ)) else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [lambdaModel]
        by_cases h : Nat.gcd r q = 1
        · rw [if_pos h, if_pos h]
          congr 2
          ring
        · rw [if_neg h, if_neg h, mul_zero]
    _ = ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1),
          e ((a : ℝ) * r / q) * (1 / (Nat.totient q : ℂ)) := (Finset.sum_filter _ _).symm
    _ = (∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((a : ℝ) * r / q))
          * (1 / (Nat.totient q : ℂ)) := by rw [Finset.sum_mul]
    _ = (ArithmeticFunction.moebius q : ℂ) * (1 / (Nat.totient q : ℂ)) := by
        rw [ramanujan_sum_coprime a q hq ha]
    _ = (ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ) := by ring


open ArithmeticFunction in
/-- The singular-series local factor has modulus at most 1. -/
lemma moebius_div_totient_norm_le (q : ℕ) (hq : 0 < q) :
    ‖(ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)‖ ≤ 1 := by
  have hφ : 1 ≤ Nat.totient q := (Nat.totient_pos.mpr hq)
  rw [norm_div]
  have h1 : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := q)
    calc ‖(ArithmeticFunction.moebius q : ℂ)‖
        = |(ArithmeticFunction.moebius q : ℝ)| := by
          rw [show ((ArithmeticFunction.moebius q : ℤ) : ℂ)
              = (((ArithmeticFunction.moebius q : ℤ) : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 := by exact_mod_cast this
  have h2 : (1:ℝ) ≤ ‖(Nat.totient q : ℂ)‖ := by
    rw [Complex.norm_natCast]
    exact_mod_cast hφ
  have h3 : (0:ℝ) < ‖(Nat.totient q : ℂ)‖ := lt_of_lt_of_le one_pos h2
  calc ‖(ArithmeticFunction.moebius q : ℂ)‖ / ‖(Nat.totient q : ℂ)‖
      ≤ 1 / ‖(Nat.totient q : ℂ)‖ := by
        gcongr
    _ ≤ 1 / 1 := by
        apply one_div_le_one_div_of_le one_pos h2
    _ = 1 := by norm_num

open ArithmeticFunction in
/-- Every model coefficient has modulus at most 1. -/
lemma lambdaModel_norm_le (q r : ℕ) (hq : 0 < q) : ‖lambdaModel q r‖ ≤ 1 := by
  rw [lambdaModel]
  by_cases h : Nat.gcd r q = 1
  · rw [if_pos h, norm_div, norm_one, Complex.norm_natCast]
    have hφ : (1:ℝ) ≤ (Nat.totient q : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq
    rw [div_le_one (by linarith)]
    linarith
  · rw [if_neg h, norm_zero]
    norm_num


/-- Trivial sup bound for the Λ-exponential sum: `‖S(α)‖ ≤ N·log N` everywhere. -/
lemma vonMangoldt_expsum_sup (N : ℕ) (α : ℝ) :
    ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ (N : ℝ) * Real.log N := by
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  calc ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ ∑ n ∈ Finset.Ioc 0 N, ‖((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ioc 0 N, Real.log N := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_Ioc] at hn
        rw [norm_mul, e_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        calc Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
          _ ≤ Real.log N := Real.log_le_log (by exact_mod_cast hn.1)
              (by exact_mod_cast hn.2)
    _ = (N : ℝ) * Real.log N := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.sub_zero]

end VonMangoldtParseval

section ArcDecomposition

/-- **Arc decomposition (Dirichlet approximation, reduced form)**: every real `α` has a
    reduced rational anchor `a/q` with `q ≤ Q`, `gcd(a,q) = 1`, and
    `|α − a/q| ≤ 1/(q(Q+1)) ≤ 1/q²` — assigning each point of the circle to a Farey arc.
    The `1/q²` form is exactly the hypothesis of `MinSum.vinogradov_sup`. -/
lemma arc_decomposition (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (a : ℤ) (q : ℕ), 0 < q ∧ q ≤ Q ∧ Int.gcd a q = 1 ∧
      |α - a / q| ≤ 1 / (q * (Q + 1)) ∧ |α - a / q| ≤ 1 / (q : ℝ) ^ 2 := by
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hQ
  have hqpos : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hbound : |α - (r.num : ℝ) / (r.den : ℝ)| ≤ 1 / (r.den * (Q + 1)) := by
    calc |α - (r.num : ℝ) / (r.den : ℝ)| = |α - (r : ℝ)| := by rw [Rat.cast_def]
      _ ≤ 1 / ((Q + 1) * r.den) := hr
      _ = 1 / (r.den * (Q + 1)) := by ring
  refine ⟨r.num, r.den, r.pos, hden, by simpa [Int.gcd] using r.reduced, hbound, ?_⟩
  refine le_trans hbound ?_
  apply one_div_le_one_div_of_le (by positivity)
  have hle : (r.den : ℝ) ≤ Q := by exact_mod_cast hden
  nlinarith [hqpos]


/-- **Major/minor arc dichotomy**: with cutoffs `P ≤ Q`, every `α` is either in a MAJOR
    arc (anchor denominator `q ≤ P`, tight `1/(q(Q+1))` window) or a MINOR arc
    (`P < q ≤ Q` with `|α − a/q| ≤ 1/q²` — the exact input to `MinSum.vinogradov_sup`,
    whose `2 ≤ q` hypothesis follows from `P < q` when `1 ≤ P`). -/
lemma arc_dichotomy (α : ℝ) (P Q : ℕ) (hP : 0 < P) (hPQ : P ≤ Q) :
    (∃ (a : ℤ) (q : ℕ), 0 < q ∧ q ≤ P ∧ Int.gcd a q = 1 ∧
        |α - a / q| ≤ 1 / (q * (Q + 1)))
    ∨ (∃ (a : ℤ) (q : ℕ), P < q ∧ q ≤ Q ∧ Int.gcd a q = 1 ∧
        |α - a / q| ≤ 1 / (q : ℝ) ^ 2) := by
  obtain ⟨a, q, hq0, hqQ, hgcd, hnear, hsq⟩ :=
    arc_decomposition α Q (lt_of_lt_of_le hP hPQ)
  by_cases hqP : q ≤ P
  · exact Or.inl ⟨a, q, hq0, hqP, hgcd, hnear⟩
  · exact Or.inr ⟨a, q, lt_of_not_ge hqP, hqQ, hgcd, hsq⟩



lemma measurableSet_majorArcs (P Q : ℕ) : MeasurableSet (MajorArcs P Q) := by
  apply MeasurableSet.biUnion (Set.to_countable _)
  intro q _
  apply MeasurableSet.iUnion
  intro a
  exact measurableSet_closedBall

/-- **The canonical minor set works**: every point of `(0,1] \ MajorArcs` has a reduced
    anchor with `P < q ≤ Q` and `|α − a/q| ≤ 1/q²` — `vinogradov_sup`'s hypothesis. -/
lemma minorSet_property (P Q : ℕ) (hP : 0 < P) (hPQ : P ≤ Q) (α : ℝ)
    (hα : α ∈ Set.Ioc (0:ℝ) 1 \ MajorArcs P Q) :
    ∃ (a : ℤ) (q : ℕ), P < q ∧ q ≤ Q ∧ Int.gcd a q = 1 ∧
      |α - a / q| ≤ 1 / (q : ℝ) ^ 2 := by
  obtain ⟨_, hnot⟩ := hα
  rcases arc_dichotomy α P Q hP hPQ with ⟨a, q, hq0, hqP, _, hnear⟩ | h
  · exfalso
    apply hnot
    refine Set.mem_biUnion ⟨hq0, hqP⟩ ?_
    refine Set.mem_iUnion.mpr ⟨a, ?_⟩
    rw [Metric.mem_closedBall, Real.dist_eq]
    exact hnear
  · exact h

/-- **Minor-arc anchor is a coprime natural**: the Dirichlet anchor `a : ℤ` of a point
    `α ∈ (0,1]` with `|α − a/q| ≤ 1/q²`, `gcd(a,q)=1`, `q ≥ 2` is in fact a positive
    integer, so `a.toNat` is a coprime-to-`q` natural with the same approximation — the
    exact `(a q : ℕ)` input `MinSum.vinogradov_sup_tight2` demands (its bound depends only
    on `q`, `U`, `V`, `N`, never on `a`). -/
lemma minor_anchor_nat (α : ℝ) (a : ℤ) (q : ℕ) (hq2 : 2 ≤ q) (hpos : 0 < α)
    (hgcd : Int.gcd a q = 1) (hsq : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    Nat.Coprime a.toNat q ∧ |α - (a.toNat : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    linarith
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hane : a ≠ 0 := by
    rintro rfl
    simp at hgcd
    omega
  have ha1 : 1 ≤ a := by
    rcases lt_or_ge a 1 with h | h
    · exfalso
      have hcast : (a : ℝ) ≤ -1 := by exact_mod_cast (by omega : a ≤ -1)
      have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
      have habs := abs_le.mp hsq
      have hm := mul_le_mul_of_nonneg_right habs.2 (sq_nonneg (q : ℝ))
      rw [one_div_mul_cancel (show (q : ℝ) ^ 2 ≠ 0 by positivity)] at hm
      have hlhs : (α - (a : ℝ) / q) * (q : ℝ) ^ 2 = α * (q : ℝ) ^ 2 - (a : ℝ) * q := by
        field_simp
      rw [hlhs] at hm
      nlinarith [hm, mul_le_mul_of_nonneg_right hcast (le_of_lt hqR),
        mul_pos hpos (by positivity : (0 : ℝ) < (q : ℝ) ^ 2), hq2R]
    · exact h
  have hcop : Nat.Coprime a.toNat q := by
    have h1 : a.toNat = a.natAbs := by omega
    have h2 : Int.gcd a (q : ℤ) = a.natAbs.gcd q := by simp [Int.gcd]
    unfold Nat.Coprime
    rw [h1]
    omega
  refine ⟨hcop, ?_⟩
  have hcast2 : (a.toNat : ℝ) = (a : ℝ) := by
    have : ((a.toNat : ℤ) : ℝ) = (a : ℝ) := by rw [Int.toNat_of_nonneg (by omega)]
    exact_mod_cast this
  rw [hcast2]
  exact hsq

open ArithmeticFunction
open scoped ArithmeticFunction

/-- The explicit RHS of `MinSum.vinogradov_sup_tight2` (the tight minor-arc sup bound),
    packaged as a function of `(q, U, V, N)` — the bound depends on the anchor only through
    its denominator `q`. Written verbatim so the cross-file `vinogradov_sup_tight2` axiom
    below is `rfl`-dischargeable by the real theorem at Phase-F concatenation. -/
noncomputable def tightSupRHS (q U V N : ℕ) : ℝ :=
  2 * Real.log (N + 1) *
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
            * Real.sqrt (N * q * (1 + Real.log (2 * q))))


/-- **Minor-arc uniform sup**: given a `Csup` dominating `tightSupRHS q U V N` for every
    minor modulus `P < q ≤ Q` (the envelope bound — the remaining analytic step), the
    exponential sum is `≤ Csup` uniformly on `(0,1] \ MajorArcs P Q`. Combines the arc
    decomposition, the `minor_anchor_nat` bridge, and `vinogradov_sup_tight2`. This is the
    exact `hsup` input to `minor_arc_variance_piece`. -/
lemma minor_sup_uniform (N P Q U V : ℕ) (hP : 0 < P) (hPQ : P ≤ Q)
    (hU : U ≤ N) (hUV : U * V ≤ N) (hUV1 : 1 ≤ U * V) (Csup : ℝ)
    (henv : ∀ q, P < q → q ≤ Q → tightSupRHS q U V N ≤ Csup) :
    ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q,
      ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ≤ Csup := by
  intro α hα
  obtain ⟨a, q, hPq, hqQ, hgcd, hsq⟩ := minorSet_property P Q hP hPQ α hα
  have hq2 : 2 ≤ q := by omega
  have hpos : (0 : ℝ) < α := hα.1.1
  obtain ⟨hcop, hanchor⟩ := minor_anchor_nat α a q hq2 hpos hgcd hsq
  have hb := vinogradov_sup_tight2 a.toNat q hq2 hcop α hanchor U V N hU hUV hUV1
  exact le_trans hb (henv q hPq hqQ)

/-- Envelope helper: the Type-I block factor `(U/⌊q/2⌋+1)·(4q(2+log 2q))` telescopes
    (the `q` cancels the `1/(q/2)`) to `≤ (16U+4Q)(2+log 2Q)`, uniform for `2 ≤ q ≤ Q`. -/
lemma env_natdiv_bound (U q Q : ℕ) (hq2 : 2 ≤ q) (hqQ : q ≤ Q) :
    ((U / (q / 2) + 1 : ℕ) : ℝ) * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))
      ≤ (16 * U + 4 * Q) * (2 + Real.log (2 * Q)) := by
  have hqRle : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hqR : (0 : ℝ) < (q : ℝ) := by linarith
  have hQ2 : 2 ≤ Q := le_trans hq2 hqQ
  have hQRle : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ2
  have hqQR : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
  have hlogq0 : (0 : ℝ) ≤ Real.log (2 * q) := Real.log_nonneg (by linarith)
  have hlogmono : Real.log (2 * (q : ℝ)) ≤ Real.log (2 * (Q : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hnd : ((U / (q / 2) : ℕ) : ℝ) ≤ 4 * (U : ℝ) / q := by
    have h2 : q ≤ 4 * (q / 2) := by omega
    have h1 : (U / (q / 2)) * (q / 2) ≤ U := Nat.div_mul_le_self _ _
    have hnat : q * (U / (q / 2)) ≤ 4 * U := by
      calc q * (U / (q / 2)) ≤ 4 * (q / 2) * (U / (q / 2)) := Nat.mul_le_mul_right _ h2
        _ = 4 * ((U / (q / 2)) * (q / 2)) := by ring
        _ ≤ 4 * U := Nat.mul_le_mul_left _ h1
    rw [le_div_iff₀ hqR]
    calc ((U / (q / 2) : ℕ) : ℝ) * q = ((q * (U / (q / 2)) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((4 * U : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = 4 * U := by push_cast; ring
  have hfac : (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))
      = 4 * q * (2 + Real.log (2 * q)) := by ring
  rw [hfac]
  have hcast : ((U / (q / 2) + 1 : ℕ) : ℝ) = ((U / (q / 2) : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hLog2q : (0 : ℝ) ≤ 2 + Real.log (2 * q) := by linarith
  calc (((U / (q / 2) : ℕ) : ℝ) + 1) * (4 * q * (2 + Real.log (2 * q)))
      ≤ (4 * U / q + 1) * (4 * q * (2 + Real.log (2 * q))) := by
        apply mul_le_mul_of_nonneg_right (by linarith [hnd]) (by positivity)
    _ = (16 * U + 4 * q) * (2 + Real.log (2 * q)) := by field_simp; ring
    _ ≤ (16 * U + 4 * Q) * (2 + Real.log (2 * Q)) := by
        apply mul_le_mul (by linarith) (by linarith) hLog2q (by positivity)

/-- **The envelope bound** (`henv` for `minor_sup_uniform`): the tight sup RHS is
    dominated, uniformly for `P < q ≤ Q`, by an explicit `Csup` in `N,U,V,P,Q` — the
    `q`-decreasing terms bounded via `q ≥ P`, the `q`-increasing via `q ≤ Q`, and the
    Type-I block factors telescoped by `env_natdiv_bound`. This discharges the `henv`
    hypothesis of `minor_sup_uniform` for the canonical `Csup`. -/
lemma tightSupRHS_le (N U V P Q q : ℕ)
    (hN1 : 1 ≤ N) (hP1 : 1 ≤ P) (hU1 : 1 ≤ U) (hV1 : 1 ≤ V)
    (hPq : P < q) (hqQ : q ≤ Q) :
    tightSupRHS q U V N ≤
      2 * Real.log (N + 1) * ((2 * (N : ℝ) / P) * (1 + Real.log U)
          + (16 * U + 4 * Q) * (2 + Real.log (2 * Q)) + U)
      + Real.log (U * V) * ((2 * (N : ℝ) / P) * (1 + Real.log (U * V))
          + (16 * (U * V) + 4 * Q) * (2 + Real.log (2 * Q)))
      + (V : ℝ) * Real.log V
      + Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
          + Real.sqrt 32 * N * ((Nat.log 2 N + 1 : ℕ) : ℝ) / Real.sqrt P
          + 64 * N * Real.sqrt (1 + Real.log (2 * Q)) / Real.sqrt U
          + 6 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.sqrt (N * Q * (1 + Real.log (2 * Q)))) := by
  have hq2 : 2 ≤ q := by omega
  have hqRle : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP1
  have hqR : (0 : ℝ) < (q : ℝ) := by linarith
  have hQ2 : 2 ≤ Q := le_trans hq2 hqQ
  have hQRle : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ2
  have hPqR : (P : ℝ) ≤ (q : ℝ) := by exact_mod_cast le_of_lt hPq
  have hqQR : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
  have hUV1 : 1 ≤ U * V := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hlogU0 : (0 : ℝ) ≤ Real.log U := Real.log_nonneg (by exact_mod_cast hU1)
  have hlogUV0 : (0 : ℝ) ≤ Real.log (U * V) := Real.log_nonneg (by exact_mod_cast hUV1)
  have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hlogN10 : (0 : ℝ) ≤ Real.log (↑N + 1) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith)
  have hlogmono : Real.log (2 * (q : ℝ)) ≤ Real.log (2 * (Q : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2q0 : (0 : ℝ) ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have hk : ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ)
      ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) := by
    have h := Nat.log_mono_right (b := 2) (Nat.div_le_self N (V + 1))
    exact_mod_cast (by omega :
      Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 ≤ Nat.log 2 N + 1)
  have h2NqP : (2 * (N : ℝ) / q) ≤ (2 * (N : ℝ) / P) := by
    gcongr
  unfold tightSupRHS
  have hB1 : 2 * Real.log (↑N + 1) *
        (((2 * (N : ℝ) / q) * (1 + Real.log U)
          + ((U / (q / 2) + 1 : ℕ) : ℝ) * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))))
          + U)
      ≤ 2 * Real.log (↑N + 1) * ((2 * (N : ℝ) / P) * (1 + Real.log U)
          + (16 * U + 4 * Q) * (2 + Real.log (2 * Q)) + U) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith [hlogN10])
    refine add_le_add (add_le_add ?_ (env_natdiv_bound U q Q hq2 hqQ)) (le_refl _)
    exact mul_le_mul_of_nonneg_right h2NqP (by linarith [hlogU0])
  have hB2 : Real.log (↑U * ↑V) *
        ((2 * (N : ℝ) / q) * (1 + Real.log (U * V))
          + ((U * V / (q / 2) + 1 : ℕ) : ℝ) * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))))
      ≤ Real.log (↑U * ↑V) * ((2 * (N : ℝ) / P) * (1 + Real.log (U * V))
          + (16 * (U * V) + 4 * Q) * (2 + Real.log (2 * Q))) := by
    apply mul_le_mul_of_nonneg_left _ hlogUV0
    have henv2 := env_natdiv_bound (U * V) q Q hq2 hqQ
    rw [Nat.cast_mul] at henv2
    refine add_le_add ?_ henv2
    exact mul_le_mul_of_nonneg_right h2NqP (by linarith [hlogUV0])
  have hB4 : Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
        + Real.sqrt 32 * N * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ)
            / Real.sqrt q
        + 64 * N * Real.sqrt (1 + Real.log (2 * q)) / Real.sqrt U
        + 6 * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ)
            * Real.sqrt (N * q * (1 + Real.log (2 * q))))
      ≤ Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
          + Real.sqrt 32 * N * ((Nat.log 2 N + 1 : ℕ) : ℝ) / Real.sqrt P
          + 64 * N * Real.sqrt (1 + Real.log (2 * Q)) / Real.sqrt U
          + 6 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.sqrt (N * Q * (1 + Real.log (2 * Q)))) := by
    apply mul_le_mul_of_nonneg_left _ hlogN0
    gcongr <;>
      first
      | exact hk
      | exact hPqR
      | exact hqQR
      | exact hqRle
      | exact Real.sqrt_nonneg _
      | exact Real.sqrt_pos.mpr hPR
      | positivity
      | linarith [hlogmono]
      | linarith [hlog2q0]
  linarith [hB1, hB2, hB4]


/-- **D5 — the minor-arc L⁴ variance bound**: the mean-square of `S(α)² − (model)` over the
    minor arcs `(0,1] \ MajorArcs P Q` is `≤ 2·Csup²·∑Λ(n)² + 2·∑‖c(n)‖²`, with the concrete
    `Csup = minorCsup N U V P Q`. Composes `minor_sup_uniform` (uniform sup via the anchor
    bridge + `vinogradov_sup_tight2`) discharged by `tightSupRHS_le` (envelope) into
    `minor_arc_variance_piece`. The remaining smallness (`Csup²·∑Λ² ≤ εN³` for `U=V~N^{2/5}`,
    `P=(log N)^B`, `Q=N/P`, `B≥20`) is one numeric instantiation at `hvar` closure. -/
lemma minor_variance_bound (N M P Q U V : ℕ) (hP1 : 1 ≤ P) (hPQ : P ≤ Q)
    (hN1 : 1 ≤ N) (hU1 : 1 ≤ U) (hV1 : 1 ≤ V) (hU : U ≤ N) (hUV : U * V ≤ N) (c : ℕ → ℂ) :
    ∫ α in (Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q),
        ‖(∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) ^ 2
          - ∑ n ∈ Finset.range M, c n * e ((n : ℝ) * α)‖ ^ 2
      ≤ 2 * (minorCsup N U V P Q ^ 2 * ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2)
        + 2 * ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := by
  have hUV1 : 1 ≤ U * V := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hsup : ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q,
      ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ≤ minorCsup N U V P Q :=
    minor_sup_uniform N P Q U V (by omega) hPQ hU hUV hUV1 (minorCsup N U V P Q)
      (fun q hPq hqQ => tightSupRHS_le N U V P Q q hN1 hP1 hU1 hV1 hPq hqQ)
  exact minor_arc_variance_piece N M (Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q)
    (measurableSet_Ioc.diff (measurableSet_majorArcs P Q)) Set.diff_subset c
    (minorCsup N U V P Q) hsup

/-- **D5 minor L⁴, packaged for the variance assembly**: `∫_{minor} ‖S‖⁴ ≤ minorCsup²·∑Λ²`
    with the concrete `minorCsup` — the pure-L⁴ form (no model subtraction) that feeds the
    first term of `variance_le_bessel`. Composes `minor_arc_L4_bound` with the uniform sup. -/
lemma minor_L4_tight (N P Q U V : ℕ) (hP1 : 1 ≤ P) (hPQ : P ≤ Q)
    (hN1 : 1 ≤ N) (hU1 : 1 ≤ U) (hV1 : 1 ≤ V) (hU : U ≤ N) (hUV : U * V ≤ N) :
    ∫ α in (Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q),
        ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ^ 4
      ≤ minorCsup N U V P Q ^ 2 * ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 := by
  have hUV1 : 1 ≤ U * V := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hsup : ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q,
      ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ≤ minorCsup N U V P Q :=
    minor_sup_uniform N P Q U V (by omega) hPQ hU hUV hUV1 (minorCsup N U V P Q)
      (fun q hPq hqQ => tightSupRHS_le N U V P Q q hN1 hP1 hU1 hV1 hPq hqQ)
  exact minor_arc_L4_bound N (Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q)
    (measurableSet_Ioc.diff (measurableSet_majorArcs P Q)) Set.diff_subset
    (minorCsup N U V P Q) hsup

/-- **D5 minor L⁴ in `range N` form** (the shape `variance_le_bessel` / the major-arc chain
    use): `∫_{minor} ‖(∑_{k<N} Λ(k)e(kα))²‖² ≤ (minorCsup + log N)²·∑_{k<N} Λ(k)²`. Bridges
    `∑_{range N} = ∑_{Ioc 0 N} − Λ(N)e(Nα)` (so the range-sup is `minorCsup + Λ(N) ≤
    minorCsup + log N`), then applies the general `L4_set_bound`. -/
lemma minor_L4_range (N P Q U V : ℕ) (hP1 : 1 ≤ P) (hPQ : P ≤ Q)
    (hN1 : 1 ≤ N) (hU1 : 1 ≤ U) (hV1 : 1 ≤ V) (hU : U ≤ N) (hUV : U * V ≤ N) :
    ∫ α in (Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q),
        ‖(∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) ^ 2‖ ^ 2
      ≤ (minorCsup N U V P Q + Real.log N) ^ 2 * ∑ n ∈ Finset.range N, Λ n ^ 2 := by
  have hUV1 : 1 ≤ U * V := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set f : ℝ → ℕ → ℂ := fun α n => ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α) with hf
  have hbridge : ∀ α : ℝ, ∑ n ∈ Finset.range N, f α n
      = (∑ n ∈ Finset.Ioc 0 N, f α n) - f α N := by
    intro α
    have hins : Finset.range (N + 1) = insert 0 (Finset.Ioc 0 N) := by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]; omega
    have hf0 : f α 0 = 0 := by
      simp only [hf, ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_mul]
    have e1 : ∑ n ∈ Finset.Ioc 0 N, f α n = ∑ n ∈ Finset.range (N + 1), f α n := by
      rw [hins, Finset.sum_insert (by simp), hf0, zero_add]
    have e2 : ∑ n ∈ Finset.range (N + 1), f α n = ∑ n ∈ Finset.range N, f α n + f α N :=
      Finset.sum_range_succ (f α) N
    rw [e1, e2]; ring
  have hsup : ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q,
      ‖∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ≤ minorCsup N U V P Q + Real.log N := by
    intro α hα
    have h1 := minor_sup_uniform N P Q U V (by omega) hPQ hU hUV hUV1 (minorCsup N U V P Q)
      (fun q hPq hqQ => tightSupRHS_le N U V P Q q hN1 hP1 hU1 hV1 hPq hqQ) α hα
    have hfN : ‖f α N‖ ≤ Real.log N := by
      rw [hf, norm_mul, e_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg vonMangoldt_nonneg]
      exact ArithmeticFunction.vonMangoldt_le_log
    calc ‖∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
        = ‖(∑ n ∈ Finset.Ioc 0 N, f α n) - f α N‖ := by rw [hbridge α]
      _ ≤ ‖∑ n ∈ Finset.Ioc 0 N, f α n‖ + ‖f α N‖ := norm_sub_le _ _
      _ ≤ minorCsup N U V P Q + Real.log N := by
          have := h1
          rw [show (∑ n ∈ Finset.Ioc 0 N, f α n) = ∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α) from rfl] at *
          linarith [hfN, h1]
  have hL4 := L4_set_bound (fun n => ((Λ n : ℝ) : ℂ)) N (Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q)
    (measurableSet_Ioc.diff (measurableSet_majorArcs P Q)) Set.diff_subset
    (minorCsup N U V P Q + Real.log N) hsup
  have hnorm : ∀ n : ℕ, ‖((Λ n : ℝ) : ℂ)‖ ^ 2 = Λ n ^ 2 := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc ∫ α in (Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q),
        ‖(∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) ^ 2‖ ^ 2
      ≤ (minorCsup N U V P Q + Real.log N) ^ 2 * ∑ n ∈ Finset.range N, ‖((Λ n : ℝ) : ℂ)‖ ^ 2 :=
        hL4
    _ = (minorCsup N U V P Q + Real.log N) ^ 2 * ∑ n ∈ Finset.range N, Λ n ^ 2 := by
        rw [Finset.sum_congr rfl (fun n _ => hnorm n)]


/-- `∑_{n<N} Λ(n)² ≤ N·(log N)²` (range form, from the banked `sum_vonMangoldt_sq_le`). -/
lemma sum_vonMangoldt_sq_range_le (N : ℕ) :
    ∑ n ∈ Finset.range N, Λ n ^ 2 ≤ (N : ℝ) * Real.log N ^ 2 := by
  calc ∑ n ∈ Finset.range N, Λ n ^ 2
      ≤ ∑ n ∈ Finset.range (N + 1), Λ n ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
        · intro n _ _; exact sq_nonneg _
    _ = ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 := by
        rw [show Finset.range (N + 1) = insert 0 (Finset.Ioc 0 N) from by
          ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]; omega,
          Finset.sum_insert (by simp)]
        simp [ArithmeticFunction.map_zero]
    _ ≤ (N : ℝ) * Real.log N ^ 2 := sum_vonMangoldt_sq_le N

/-- `minorCsup` is nonnegative (each of its four groups is a product/sum of nonneg factors,
    the logs being `≥ 0` since their arguments are `≥ 1`). -/
lemma minorCsup_nonneg (N P Q : ℕ) (hP2 : 2 ≤ P) (hN1 : 1 ≤ N) (hQ1 : 1 ≤ Q) :
    0 ≤ minorCsup N P P P Q := by
  have hPR : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast (show 1 ≤ P by omega)
  have hQR : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hlogP : (0 : ℝ) ≤ Real.log P := Real.log_nonneg hPR
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hNR
  have hlogN1 : (0 : ℝ) ≤ Real.log (↑N + 1) := Real.log_nonneg (by linarith)
  have hlogPP : (0 : ℝ) ≤ Real.log (↑P * ↑P) := Real.log_nonneg (by nlinarith [hPR])
  have hlog2Q : (0 : ℝ) ≤ Real.log (2 * ↑Q) := Real.log_nonneg (by linarith)
  unfold minorCsup
  have hb1 : (0 : ℝ) ≤ 2 * Real.log (↑N + 1) *
      ((2 * ↑N / ↑P) * (1 + Real.log ↑P) + (16 * ↑P + 4 * ↑Q) * (2 + Real.log (2 * ↑Q)) + ↑P) := by
    apply mul_nonneg (by linarith)
    apply add_nonneg (add_nonneg (mul_nonneg (by positivity) (by linarith))
      (mul_nonneg (by positivity) (by linarith))) (by positivity)
  have hb2 : (0 : ℝ) ≤ Real.log (↑P * ↑P) *
      ((2 * ↑N / ↑P) * (1 + Real.log (↑P * ↑P))
        + (16 * (↑P * ↑P) + 4 * ↑Q) * (2 + Real.log (2 * ↑Q))) := by
    apply mul_nonneg hlogPP
    apply add_nonneg (mul_nonneg (by positivity) (by linarith))
      (mul_nonneg (by positivity) (by linarith))
  have hb3 : (0 : ℝ) ≤ (↑P : ℝ) * Real.log ↑P := mul_nonneg (by positivity) hlogP
  have hb4 : (0 : ℝ) ≤ Real.log ↑N *
      (4 * Real.sqrt 10 * ↑N / Real.sqrt (↑P + 1)
        + Real.sqrt 32 * ↑N * ((Nat.log 2 N + 1 : ℕ) : ℝ) / Real.sqrt ↑P
        + 64 * ↑N * Real.sqrt (1 + Real.log (2 * ↑Q)) / Real.sqrt ↑P
        + 6 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.sqrt (↑N * ↑Q * (1 + Real.log (2 * ↑Q)))) := by
    apply mul_nonneg hlogN
    positivity
  linarith [hb1, hb2, hb3, hb4]

/-- **D5 minor L⁴ explicit bound** (combining the banked pieces): with `U=V=P`, `P≥2`,
    `P³≤N`, `P≤Q`, `P·Q≤N`, the minor L⁴ integral is `≤ (300·N·(log N+2)³/√P + log N)²·N·(log N)²`.
    Feeds the minor-arc smallness once `P = (log N)^B`. -/
lemma minor_L4_le_explicit (N P Q : ℕ) (hP2 : 2 ≤ P) (hPN : P ^ 3 ≤ N) (hPQcut : P ≤ Q)
    (hPQ : P * Q ≤ N) (hN1 : 1 ≤ N) (hQ1 : 1 ≤ Q) :
    ∫ α in (Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q),
        ‖(∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) ^ 2‖ ^ 2
      ≤ (300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P + Real.log N) ^ 2
          * ((N : ℝ) * Real.log N ^ 2) := by
  have hP1 : 1 ≤ P := by omega
  have hPleN : P ≤ N := le_trans (Nat.le_self_pow (by norm_num) P) hPN
  have hPP : P * P ≤ N :=
    le_trans (by rw [← pow_two]; exact Nat.pow_le_pow_right hP1 (by norm_num)) hPN
  have hL4 := minor_L4_range N P Q P P hP1 hPQcut hN1 hP1 hP1 hPleN hPP
  have hcsup := minorCsup_bound N P Q hP2 hPN hPQ
  have hcsup0 := minorCsup_nonneg N P Q hP2 hN1 hQ1
  have hsumL := sum_vonMangoldt_sq_range_le N
  have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hsq0 : (0 : ℝ) ≤ ∑ n ∈ Finset.range N, Λ n ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  refine le_trans hL4 ?_
  apply mul_le_mul _ hsumL hsq0 (by positivity)
  apply pow_le_pow_left₀ (by linarith) (by linarith) 2

/-- **Brick (a): minor-arc smallness limit.** With `P = ⌊(log N)^9⌋₊`, twice the explicit
    minor-L⁴ bound `2·(300 N (logN+2)³/√P + logN)²·N (logN)²` is `≤ ε N³` for all large `N`.
    Route (rpow-free): split into `46080000 N³/L + 4 N L⁴` (L = log N); the first `≤ εN³/2`
    once `L ≥ 92160000/ε`, the second `≤ εN³/2` once `N ≥ 32768/ε` (via `L⁴ ≤ 4096√N ≤ 4096N`,
    the nested-`√` log bound `log N ≤ 8·√√√N`). Feeds the variance assembly's minor term. -/
lemma minor_limit (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      2 * (300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt (Nat.floor ((Real.log N) ^ 9)) + Real.log N) ^ 2
          * ((N : ℝ) * Real.log N ^ 2) ≤ ε * (N : ℝ) ^ 3 := by
  refine ⟨max 8 (max (Nat.ceil (Real.exp (92160000 / ε))) (Nat.ceil (32768 / ε))), fun N hN => ?_⟩
  have hN8 : 8 ≤ N := le_trans (le_max_left _ _) hN
  have hNexp : Real.exp (92160000 / ε) ≤ N :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN))
  have hN32 : (32768 / ε) ≤ N :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN))
  have hNR : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN8
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  set L : ℝ := Real.log N with hLdef
  have hL2 : (2 : ℝ) ≤ L := by
    rw [hLdef]
    calc (2 : ℝ) ≤ Real.log 8 := by
          rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
          have h2 : (0.6931 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
          push_cast; linarith
      _ ≤ Real.log N := Real.log_le_log (by norm_num) hNR
  have hLpos : (0 : ℝ) < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hLA0 : (0 : ℝ) ≤ L := le_of_lt hLpos
  set P : ℕ := Nat.floor (L ^ 9) with hPdef
  have hL9pos : (0 : ℝ) < L ^ 9 := by positivity
  have hL9ge2 : (2 : ℝ) ≤ L ^ 9 := by
    have hLL9 : L ≤ L ^ 9 := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 9 := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ L) (by norm_num)
    linarith
  have hPR : (L ^ 9 / 2) ≤ (P : ℝ) := by
    have h := Nat.sub_one_lt_floor (L ^ 9)
    rw [← hPdef] at h
    have h2 : L ^ 9 - 1 ≤ (P : ℝ) := le_of_lt h
    linarith
  have hPpos : (0 : ℝ) < (P : ℝ) := by
    have : (0:ℝ) < L ^ 9 / 2 := by positivity
    linarith
  set sP : ℝ := Real.sqrt (P : ℝ) with hsPdef
  have hsPpos : (0 : ℝ) < sP := Real.sqrt_pos.mpr hPpos
  have hsPsq : sP ^ 2 = (P : ℝ) := Real.sq_sqrt (le_of_lt hPpos)
  set A : ℝ := 300 * (N : ℝ) * (L + 2) ^ 3 with hAdef
  have hA0 : (0 : ℝ) ≤ A := by rw [hAdef]; positivity
  have hL2p0 : (0:ℝ) ≤ L + 2 := by linarith
  have hL2p : (L + 2) ≤ 2 * L := by linarith
  have hL26 : (L + 2) ^ 6 ≤ 64 * L ^ 6 := by
    calc (L + 2) ^ 6 ≤ (2 * L) ^ 6 := pow_le_pow_left₀ hL2p0 hL2p 6
      _ = 64 * L ^ 6 := by ring
  have hA2val : A ^ 2 = 90000 * (N:ℝ) ^ 2 * (L + 2) ^ 6 := by rw [hAdef]; ring
  have hAsP : (A / sP) ^ 2 = A ^ 2 / (P : ℝ) := by rw [div_pow, hsPsq]
  have hTsq : (A / sP + L) ^ 2 ≤ 2 * (A ^ 2 / (P : ℝ)) + 2 * L ^ 2 := by
    nlinarith [sq_nonneg (A / sP - L), hAsP]
  have hL3pos : (0:ℝ) < L ^ 3 := by positivity
  have hfirst : 2 * (A ^ 2 / (P : ℝ)) ≤ 23040000 * (N:ℝ)^2 / L ^ 3 := by
    rw [show 2 * (A^2/(P:ℝ)) = 2*A^2/(P:ℝ) from by ring, div_le_div_iff₀ hPpos hL3pos, hA2val]
    nlinarith [mul_nonneg (sq_nonneg (N:ℝ)) (show (0:ℝ) ≤ (P:ℝ) - L^9/2 from by linarith [hPR]),
               mul_nonneg (mul_nonneg (sq_nonneg (N:ℝ)) (pow_pos hLpos 3).le)
                          (show (0:ℝ) ≤ 64*L^6 - (L+2)^6 from by linarith [hL26])]
  have hTsq2 : (A / sP + L) ^ 2 ≤ 23040000 * (N:ℝ)^2 / L ^ 3 + 2 * L ^ 2 := by
    linarith [hTsq, hfirst]
  have hmain : 2 * (A / sP + L) ^ 2 * ((N:ℝ) * L ^ 2)
      ≤ 46080000 * (N:ℝ)^3 / L + 4 * (N:ℝ) * L ^ 4 := by
    have hfac : 2 * (A / sP + L) ^ 2 * ((N:ℝ) * L ^ 2)
        ≤ 2 * (23040000 * (N:ℝ)^2 / L ^ 3 + 2 * L ^ 2) * ((N:ℝ) * L ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left hTsq2 (by norm_num)
    have hexp : 2 * (23040000 * (N:ℝ)^2 / L ^ 3 + 2 * L ^ 2) * ((N:ℝ) * L ^ 2)
        = 46080000 * (N:ℝ)^3 / L + 4 * (N:ℝ) * L ^ 4 := by
      field_simp
      ring
    linarith [hfac, hexp.le, hexp.ge]
  have hpart1 : 46080000 * (N:ℝ)^3 / L ≤ ε / 2 * (N:ℝ)^3 := by
    rw [div_le_iff₀ hLpos]
    have hLbig : 92160000 / ε ≤ L := by
      rw [hLdef]
      calc 92160000 / ε ≤ Real.log (Real.exp (92160000 / ε)) := by rw [Real.log_exp]
        _ ≤ Real.log N := Real.log_le_log (Real.exp_pos _) hNexp
    rw [div_le_iff₀ hε] at hLbig
    have hεL : (92160000 : ℝ) ≤ ε * L := by linarith [hLbig]
    nlinarith [mul_nonneg (pow_pos hNpos 3).le (show (0:ℝ) ≤ ε*L - 92160000 from by linarith [hεL])]
  have hpart2 : 4 * (N:ℝ) * L ^ 4 ≤ ε / 2 * (N:ℝ)^3 := by
    set s : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ))) with hsdef
    have hLs : L ≤ 8 * s := by
      rw [hLdef, hsdef]
      have e1 : Real.log (Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ)))) = Real.log N / 8 := by
        rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt (Real.sqrt_nonneg _),
            Real.log_sqrt (le_of_lt hNpos)]; ring
      have h4 : Real.log (Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ))))
          ≤ Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ))) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [e1] at h4
      linarith [h4, Real.sqrt_nonneg (Real.sqrt (Real.sqrt (N:ℝ)))]
    have hL4 : L ^ 4 ≤ 4096 * (N:ℝ) := by
      have hs4 : s ^ 4 = Real.sqrt (N:ℝ) := by
        rw [hsdef, show (Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ))))^4
              = ((Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ))))^2)^2 by ring,
            Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Real.sqrt_nonneg _)]
      have hLpow : L ^ 4 ≤ (8 * s) ^ 4 := pow_le_pow_left₀ hLA0 hLs 4
      have hsqrtN : Real.sqrt (N:ℝ) ≤ (N:ℝ) := by
        have hle : Real.sqrt (N:ℝ) ≤ Real.sqrt ((N:ℝ)^2) := Real.sqrt_le_sqrt (by nlinarith [hNR])
        rwa [Real.sqrt_sq (le_of_lt hNpos)] at hle
      calc L ^ 4 ≤ (8 * s) ^ 4 := hLpow
        _ = 4096 * s ^ 4 := by ring
        _ = 4096 * Real.sqrt (N:ℝ) := by rw [hs4]
        _ ≤ 4096 * (N:ℝ) := by linarith [hsqrtN]
    have hεN : (32768 : ℝ) ≤ ε * N := by
      rw [div_le_iff₀ hε] at hN32; linarith [hN32]
    nlinarith [mul_nonneg hNpos.le (show (0:ℝ) ≤ 4096*(N:ℝ) - L^4 from by linarith [hL4]),
               mul_nonneg (sq_nonneg (N:ℝ)) (show (0:ℝ) ≤ ε*(N:ℝ)/2 - 16384 from by linarith [hεN])]
  calc 2 * (A / sP + L) ^ 2 * ((N:ℝ) * L ^ 2)
      ≤ 46080000 * (N:ℝ)^3 / L + 4 * (N:ℝ) * L ^ 4 := hmain
    _ ≤ ε / 2 * (N:ℝ)^3 + ε / 2 * (N:ℝ)^3 := by linarith [hpart1, hpart2]
    _ = ε * (N:ℝ)^3 := by ring

/-- **Farey windows are disjoint**: distinct reduced anchors with moduli `≤ P` have
    disjoint windows once `2P² < Q+1` — the input for splitting the major-arc integral
    into per-window integrals. -/
lemma farey_disjoint (P Q : ℕ) (hPQ : 2 * P ^ 2 < Q + 1) (a a' : ℤ) (q q' : ℕ)
    (hq : 0 < q) (hq' : 0 < q') (hqP : q ≤ P) (hq'P : q' ≤ P)
    (hga : Int.gcd a q = 1) (hga' : Int.gcd a' q' = 1)
    (hne : ¬ (a = a' ∧ q = q')) :
    Disjoint (Metric.closedBall ((a : ℝ) / q) (1 / (q * (Q + 1))))
      (Metric.closedBall ((a' : ℝ) / q') (1 / (q' * (Q + 1)))) := by
  have hP0 : 0 < P := lt_of_lt_of_le hq hqP
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hq'R : (0:ℝ) < q' := by exact_mod_cast hq'
  have hQ1 : (0:ℝ) < (Q:ℝ) + 1 := by positivity
  -- the anchors are distinct rationals: |aq' − a'q| ≥ 1
  have hnum : a * (q' : ℤ) ≠ a' * (q : ℤ) := by
    intro hc
    apply hne
    have hdvd1 : (q : ℤ) ∣ (q' : ℤ) := by
      have h1 : (q : ℤ) ∣ a * q' := ⟨a', by linarith [hc]⟩
      have hco : IsCoprime (q : ℤ) a := by
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
        exact hga
      exact hco.dvd_of_dvd_mul_left h1
    have hdvd2 : (q' : ℤ) ∣ (q : ℤ) := by
      have h1 : (q' : ℤ) ∣ a' * q := ⟨a, by linarith [hc]⟩
      have hco : IsCoprime (q' : ℤ) a' := by
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
        exact hga'
      exact hco.dvd_of_dvd_mul_left h1
    have hqq : (q : ℤ) = q' := Int.dvd_antisymm (by exact_mod_cast Int.natCast_nonneg q)
      (by exact_mod_cast Int.natCast_nonneg q') hdvd1 hdvd2
    have hqq' : q = q' := by exact_mod_cast hqq
    refine ⟨?_, hqq'⟩
    subst hqq'
    have := mul_right_cancel₀ (show (q:ℤ) ≠ 0 by exact_mod_cast hq.ne') hc
    exact this
  have hdist : 1 / ((q:ℝ) * q') ≤ dist ((a : ℝ) / q) ((a' : ℝ) / q') := by
    rw [Real.dist_eq]
    have hval : (a : ℝ) / q - (a' : ℝ) / q' = ((a * q' - a' * q : ℤ) : ℝ) / ((q:ℝ) * q') := by
      push_cast
      field_simp
    rw [hval, abs_div, abs_of_pos (by positivity : (0:ℝ) < (q:ℝ) * q')]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 : (1 : ℤ) ≤ |a * q' - a' * q| :=
      Int.one_le_abs (sub_ne_zero_of_ne hnum)
    exact_mod_cast (by exact_mod_cast h1 : (1:ℝ) ≤ |((a * q' - a' * q : ℤ) : ℝ)|)
  apply Metric.closedBall_disjoint_closedBall
  calc 1 / ((q:ℝ) * (Q + 1)) + 1 / ((q':ℝ) * (Q + 1))
      ≤ 1 / ((Q:ℝ) + 1) + 1 / ((Q:ℝ) + 1) := by
        have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
        have hq'1 : (1:ℝ) ≤ (q':ℝ) := by exact_mod_cast hq'
        apply add_le_add
        · apply one_div_le_one_div_of_le hQ1
          nlinarith [hq1, hQ1]
        · apply one_div_le_one_div_of_le hQ1
          nlinarith [hq'1, hQ1]
    _ = 2 / ((Q:ℝ) + 1) := by ring
    _ < 1 / ((P:ℝ) ^ 2) := by
        rw [div_lt_div_iff₀ hQ1 (by positivity)]
        have : (2 * P ^ 2 : ℝ) < (Q:ℝ) + 1 := by exact_mod_cast hPQ
        nlinarith [this]
    _ ≤ 1 / ((q:ℝ) * q') := by
        apply one_div_le_one_div_of_le (by positivity)
        have h1 : (q:ℝ) ≤ P := by exact_mod_cast hqP
        have h2 : (q':ℝ) ≤ P := by exact_mod_cast hq'P
        nlinarith [hqR, hq'R]
    _ ≤ dist ((a : ℝ) / q) ((a' : ℝ) / q') := hdist


/-- **Finite anchor localization**: inside `(0,1]` only anchors with `−q ≤ a ≤ 2q`
    can contribute to the major arcs — the ℤ-union collapses to a finite one, enabling
    the per-window splitting of the major-arc integral. -/
lemma majorArcs_inter_Ioc_subset (P Q : ℕ) (hP : 0 < P) :
    MajorArcs P Q ∩ Set.Ioc (0:ℝ) 1
      ⊆ ⋃ q ∈ Set.Icc 1 P, ⋃ a ∈ Set.Icc (-(q:ℤ)) (2 * q),
          Metric.closedBall ((a : ℝ) / q) (1 / (q * (Q + 1))) := by
  rintro x ⟨hx, hx01⟩
  rw [MajorArcs, Set.mem_iUnion₂] at hx
  obtain ⟨q, hq, hxq⟩ := hx
  rw [Set.mem_iUnion] at hxq
  obtain ⟨a, ha⟩ := hxq
  rw [Metric.mem_closedBall, Real.dist_eq] at ha
  obtain ⟨hq1, hqP⟩ := hq
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hQR : (0:ℝ) ≤ (Q:ℝ) := Nat.cast_nonneg Q
  have hrad : 1 / ((q:ℝ) * (Q + 1)) ≤ 1 := by
    rw [div_le_one (by nlinarith)]
    nlinarith
  have hx0 : (0:ℝ) < x := hx01.1
  have hx1 : x ≤ 1 := hx01.2
  have hlow : -1 ≤ (a : ℝ) / q := by
    have : (a:ℝ)/q ≥ x - 1/((q:ℝ)*(Q+1)) := by
      have := abs_le.mp ha
      linarith [this.2]
    linarith
  have hhigh : (a : ℝ) / q ≤ 2 := by
    have : (a:ℝ)/q ≤ x + 1/((q:ℝ)*(Q+1)) := by
      have := abs_le.mp ha
      linarith [this.1]
    linarith
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have haZ : -(q:ℤ) ≤ a ∧ a ≤ 2 * q := by
    constructor
    · have : -(q:ℝ) ≤ (a:ℝ) := by
        have := mul_le_mul_of_nonneg_right hlow hqpos.le
        rw [div_mul_cancel₀ _ hqpos.ne'] at this
        linarith
      exact_mod_cast this
    · have : (a:ℝ) ≤ 2 * q := by
        have := mul_le_mul_of_nonneg_right hhigh hqpos.le
        rw [div_mul_cancel₀ _ hqpos.ne'] at this
        linarith
      exact_mod_cast this
  rw [Set.mem_iUnion₂]
  refine ⟨q, ⟨hq1, hqP⟩, ?_⟩
  rw [Set.mem_iUnion₂]
  refine ⟨a, ⟨haZ.1, haZ.2⟩, ?_⟩
  rw [Metric.mem_closedBall, Real.dist_eq]
  exact ha



/-- **Reduced coverage**: inside `(0,1]` the major arcs are covered by the windows of the
    finitely many REDUCED anchors — an unreduced `a/q` equals a reduced `a'/q'` with
    `q' ∣ q`, whose window is wider. The composition splits over `anchors P` with
    `farey_disjoint` and evaluates each window by `vonMangoldt_window_eval`. -/
lemma majorArcs_subset_reduced (P Q : ℕ) (hP : 0 < P) :
    MajorArcs P Q ∩ Set.Ioc (0:ℝ) 1
      ⊆ ⋃ pq ∈ anchors P,
          Metric.closedBall (((pq.2 : ℤ) : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1))) := by
  rintro x ⟨hx, hx01⟩
  rw [MajorArcs, Set.mem_iUnion₂] at hx
  obtain ⟨q, ⟨hq1, hqP⟩, hxq⟩ := hx
  rw [Set.mem_iUnion] at hxq
  obtain ⟨a, ha⟩ := hxq
  rw [Metric.mem_closedBall, Real.dist_eq] at ha
  -- bounds on a as before
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hQR : (0:ℝ) ≤ (Q:ℝ) := Nat.cast_nonneg Q
  have hrad : 1 / ((q:ℝ) * (Q + 1)) ≤ 1 := by
    rw [div_le_one (by nlinarith)]
    nlinarith
  have hx0 : (0:ℝ) < x := hx01.1
  have hx1 : x ≤ 1 := hx01.2
  have habs := abs_le.mp ha
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hlow : -(q:ℝ) ≤ (a:ℝ) := by
    have h1 : -1 ≤ (a:ℝ)/q := by
      have : (a:ℝ)/q ≥ x - 1/((q:ℝ)*(Q+1)) := by linarith [habs.2]
      linarith
    have := mul_le_mul_of_nonneg_right h1 hqpos.le
    rw [div_mul_cancel₀ _ hqpos.ne'] at this
    linarith
  have hhigh : (a:ℝ) ≤ 2*q := by
    have h1 : (a:ℝ)/q ≤ 2 := by
      have : (a:ℝ)/q ≤ x + 1/((q:ℝ)*(Q+1)) := by linarith [habs.1]
      linarith
    have := mul_le_mul_of_nonneg_right h1 hqpos.le
    rw [div_mul_cancel₀ _ hqpos.ne'] at this
    linarith
  -- reduce the fraction
  set g : ℕ := Int.gcd a q with hg
  have hg0 : 0 < g := by
    rw [hg]
    apply Int.gcd_pos_of_ne_zero_right
    exact_mod_cast hq1.trans_lt' Nat.zero_lt_one |>.ne'
  set a' : ℤ := a / g with ha'
  set q' : ℕ := q / g with hq'
  have hgdvd_a : (g : ℤ) ∣ a := by
    rw [hg]
    exact Int.gcd_dvd_left a (q:ℤ)
  have hgdvd_q : g ∣ q := by
    have h := Int.gcd_dvd_right a (q:ℤ)
    rw [← hg] at h
    exact_mod_cast h
  have hq'pos : 0 < q' := Nat.div_pos (Nat.le_of_dvd (by omega) hgdvd_q) hg0
  have hq'le : q' ≤ q := Nat.div_le_self q g
  have haeq : a = g * a' := (Int.mul_ediv_cancel' hgdvd_a).symm
  have hqeq : q = g * q' := (Nat.mul_div_cancel' hgdvd_q).symm
  have hgcd' : Int.gcd a' q' = 1 := by
    rw [ha', hq']
    have h := Int.gcd_div_gcd_div_gcd (i := a) (j := (q:ℤ)) (by
      rw [← hg]
      exact_mod_cast hg0)
    rw [← hg] at h
    convert h using 2
    push_cast
    rfl
  -- same center
  have hcenter : ((a : ℝ)) / q = ((a' : ℝ)) / q' := by
    rw [haeq, hqeq]
    push_cast
    rw [mul_comm ((g:ℝ)) ((a':ℝ)), mul_comm ((g:ℝ)) ((q':ℝ))]
    rw [mul_div_mul_right _ _ (by exact_mod_cast hg0.ne' : ((g:ℝ)) ≠ 0)]
  -- wider radius
  have hradle : 1 / ((q:ℝ) * (Q + 1)) ≤ 1 / ((q':ℝ) * (Q + 1)) := by
    apply one_div_le_one_div_of_le
    · have : (0:ℝ) < (q':ℝ) := by exact_mod_cast hq'pos
      nlinarith
    · have h1 : ((q':ℕ):ℝ) ≤ ((q:ℕ):ℝ) := by exact_mod_cast hq'le
      nlinarith
  -- a' bounds
  have hgRpos : (0:ℝ) < (g:ℝ) := by exact_mod_cast hg0
  have ha'low : -(q' : ℤ) ≤ a' := by
    have hR : -((q':ℕ):ℝ) ≤ ((a':ℤ):ℝ) := by
      have h1 : -((q:ℝ)) ≤ (((g:ℤ) * a' : ℤ):ℝ) := by
        rw [← haeq]
        exact hlow
      push_cast at h1
      have h2 : (q:ℝ) = (g:ℝ) * ((q':ℕ):ℝ) := by exact_mod_cast hqeq
      nlinarith
    exact_mod_cast hR
  have ha'high : a' ≤ 2 * q' := by
    have hR : ((a':ℤ):ℝ) ≤ 2 * ((q':ℕ):ℝ) := by
      have h1 : (((g:ℤ) * a' : ℤ):ℝ) ≤ 2 * (q:ℝ) := by
        rw [← haeq]
        exact hhigh
      push_cast at h1
      have h2 : (q:ℝ) = (g:ℝ) * ((q':ℕ):ℝ) := by exact_mod_cast hqeq
      nlinarith
    exact_mod_cast hR
  -- conclude
  rw [Set.mem_iUnion₂]
  refine ⟨(q', a'), ?_, ?_⟩
  · rw [anchors, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨hq'pos, le_trans hq'le hqP⟩, ?_, ?_⟩, hgcd'⟩
    · calc -(P:ℤ) ≤ -(q':ℤ) := by
            have : (q':ℤ) ≤ P := by exact_mod_cast le_trans hq'le hqP
            omega
        _ ≤ a' := ha'low
    · calc a' ≤ 2 * q' := ha'high
        _ ≤ 2 * P := by
            have : (q':ℤ) ≤ P := by exact_mod_cast le_trans hq'le hqP
            omega
  · rw [Metric.mem_closedBall, Real.dist_eq]
    calc |x - ((a':ℤ):ℝ) / (q':ℕ)| = |x - (a:ℝ)/q| := by rw [hcenter]
      _ ≤ 1 / ((q:ℝ) * (Q + 1)) := ha
      _ ≤ 1 / ((q':ℝ) * (Q + 1)) := hradle

end ArcDecomposition

end MinorArc

end Principia.Common.Goldbach
