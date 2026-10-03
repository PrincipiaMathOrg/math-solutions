/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Basic
import Principia.Erdos1054.Density
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.Nat.Squarefree

set_option autoImplicit false

/-!
# EP1054 §6 "Bounded representations and cofactor ranges": the `CoverageEta` package

Discharges twenty-two obligations of `Principia.Erdos1054.Spine` (paper
`Campaigns/Erdos-1054/collab-paper/EP1054.tex`, lines 2248–2282, 2472–2560, 2658–2670,
2719–2722).

Leaves (proved from the definitions and Mathlib alone):
* `leaf_Coverage_Fact_RtPairs` — `r_t(N)` counts the pairs `(n, j)` with `σ_j(n) = N`,
  `n ≤ tN` (lines 2257–2259): an explicit bijection `(n, j) ↦ (n/d, d)`, `d` the
  `(τ(n) − j)`-th smallest divisor of `n`.
* `leaf_Coverage_Fact_RtPosIff` — `r_t(N) > 0 ⟺ f(N) ≤ tN` on `𝓡` (lines 2259–2260).
* `leaf_Coverage_Fact_GcovSubsetRtPos` — `G_A ⊆ {r_A > 0}` (lines 2479–2484).
* `leaf_Coverage_Fact_UpperDensCompl` — `upperdens(ℕ ∖ S) = 1 − lowerdens(S)` (line 2716).
* `leaf_Coverage_Disp_CoprimeSqTail` — `(e+1) ∑_{a>1, (a,e#)=1} a⁻² ≤ (e+1)/e ≤ 3/2`
  (lines 2383–2389), by telescoping.

Links (proved from exactly the dependencies the spine names):
* the fixed-cofactor defect (`link_Coverage_Rem_SqfreeDefectPos`,
  `link_Cor_FixedCofactorDefect_pos`, `link_Eq_FixedCofactorDefect`) from `Eq_AlmostLogTail`;
* the coprime part (`link_Coverage_Step_KmodSmallPrime`, `link_Coverage_Step_GcovValuesSmallPrime`,
  `link_Coverage_Fact_GcovCoprimeNull`, `link_Coverage_Fact_CoprimeComplementDens`,
  `link_Eq_BoundedCofactorComplement`);
* the size of `δ_A` (`link_Coverage_Disp_LogPA`, `link_Eq_DeltaAAsymptotic`);
* `η_A` (`link_Prop_EtaALower_bound`, `link_Prop_EtaALower_tendsto`,
  `link_Coverage_Rem_EtaDominates`); `A L(A) → ∞` is proved here (`tendsto_mul_Lscale`);
* the reformulations of the conjecture (`link_Coverage_Rem_ConjEquivEta`,
  `link_Coverage_Rem_RoughPartBound`, `link_Coverage_Rem_ConjEquivSmallPrimePart`,
  `link_Coverage_Rem_T_iff_Conj`). `Δ(A) → 0` comes from Mathlib's
  `not_summable_one_div_on_primes`; `eq:T ⟺ tightness` is the bounded-`X` argument, computed on
  `ν_X((T, ∞])` directly (`nuX_Ioi`), and the third clause of `Prop_TightnessEquivalence` closes it.
-/

namespace Principia.Erdos1054.Proofs.CoverageEta

open Finset Filter
open scoped Topology ENNReal

/-! ## Fixed facts about `r_t`, `G_A` and the fixed-cofactor defect -/

theorem upperDensCompl : Coverage.Fact_UpperDensCompl := by
  intro S
  have h := lowerDens_add_upperDens_compl S
  linarith

theorem gcovSubsetRtPos : Coverage.Fact_GcovSubsetRtPos := by
  intro A hA N hN
  obtain ⟨e, d, he, heA, hd, rfl⟩ := hN
  show 0 < rt (A : ℝ) (F e d)
  unfold rt
  rw [Finset.card_pos]
  refine ⟨(e, d), ?_⟩
  have hdF : d ≤ F e d := F_ge e d he hd
  have h1 : (e : ℝ) ≤ A := by exact_mod_cast heA
  have h2 : (d : ℝ) ≤ (F e d : ℝ) := by exact_mod_cast hdF
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hed : ((e * d : ℕ) : ℝ) ≤ (A : ℝ) * (F e d : ℕ) := by
    push_cast
    calc (e : ℝ) * d ≤ (A : ℝ) * d := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg d)
      _ ≤ (A : ℝ) * (F e d : ℝ) := mul_le_mul_of_nonneg_left h2 hA0
  have hedn : e * d ≤ ⌊(A : ℝ) * (F e d : ℕ)⌋₊ := Nat.le_floor hed
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  exact ⟨⟨⟨he, le_trans (Nat.le_mul_of_pos_right e hd) hedn⟩,
    ⟨hd, le_trans (Nat.le_mul_of_pos_left d he) hedn⟩⟩, rfl, hed⟩

theorem rtPosIff : Coverage.Fact_RtPosIff := by
  intro t ht N hN
  constructor
  · intro hpos
    unfold rt at hpos
    obtain ⟨⟨e, d⟩, hp⟩ := Finset.card_pos.1 hpos
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨he, _⟩, ⟨hd, _⟩⟩, hF, hle⟩ := hp
    have h1 := f_le_of_F e d N he hd hF.symm
    calc (f N : ℝ) ≤ ((e * d : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ t * N := hle
  · intro hle
    obtain ⟨e, d, he, hd, hfN, hNF⟩ := f_mem_Fform N hN
    unfold rt
    rw [Finset.card_pos]
    refine ⟨(e, d), ?_⟩
    have hed : ((e * d : ℕ) : ℝ) ≤ t * N := by rw [← hfN]; exact hle
    have hedn : e * d ≤ ⌊t * N⌋₊ := Nat.le_floor hed
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨⟨he, le_trans (Nat.le_mul_of_pos_right e hd) hedn⟩,
      ⟨hd, le_trans (Nat.le_mul_of_pos_left d he) hedn⟩⟩, hNF.symm, hed⟩

/-- `N ∈ G_A ⟹ f(N) ≤ A N`. -/
theorem f_le_of_mem_Gcov {A N : ℕ} (hN : N ∈ Gcov A) : (f N : ℝ) ≤ (A : ℝ) * N := by
  obtain ⟨e, d, he, heA, hd, rfl⟩ := hN
  have h1 : (f (F e d) : ℝ) ≤ (e : ℝ) * d := by exact_mod_cast f_le_of_F e d (F e d) he hd rfl
  have h2 : (d : ℝ) ≤ (F e d : ℝ) := by exact_mod_cast F_ge e d he hd
  have h3 : (e : ℝ) ≤ A := by exact_mod_cast heA
  calc (f (F e d) : ℝ) ≤ (e : ℝ) * d := h1
    _ ≤ (A : ℝ) * d := mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg d)
    _ ≤ (A : ℝ) * (F e d : ℝ) := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg A)

/-- The large-ratio squarefree set at level `T ≥ A` misses `G_A`. -/
theorem largeRatio_subset {A : ℕ} {T : ℝ} (hAT : (A : ℝ) ≤ T) :
    {N : ℕ | N ∈ R ∧ Squarefree N ∧ T * N < (f N : ℝ)} ⊆ {N : ℕ | Squarefree N ∧ N ∉ Gcov A} := by
  rintro N ⟨_, hsq, hlt⟩
  refine ⟨hsq, fun hG => ?_⟩
  have h1 := f_le_of_mem_Gcov hG
  have h2 : (A : ℝ) * N ≤ T * N := mul_le_mul_of_nonneg_right hAT (Nat.cast_nonneg N)
  linarith

theorem Lscale_pos {T : ℝ} (hT : Real.exp (Real.exp 2) ≤ T) : 0 < Lscale T := by
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  have h1 : Real.exp 2 ≤ Real.log T := (Real.le_log_iff_exp_le hT0).2 hT
  have h1' : 0 < Real.log T := lt_of_lt_of_le (Real.exp_pos _) h1
  have h2 : 2 ≤ Real.log (Real.log T) := (Real.le_log_iff_exp_le h1').2 h1
  have h2' : 0 < Real.log (Real.log T) := by linarith
  have h3 : 0 < Real.log (Real.log (Real.log T)) := Real.log_pos (by linarith)
  show 0 < Real.log (Real.log (Real.log T)) / (Real.log T * Real.log (Real.log T))
  positivity

theorem sqfreeDefectPos (hAL : Eq_AlmostLogTail) : Coverage.Rem_SqfreeDefectPos := by
  intro A _
  have hc : 0 < Real.exp (-eulerGamma) / 4 := by positivity
  obtain ⟨T₀, hT₀⟩ := hAL (Real.exp (-eulerGamma) / 4) hc
  have hL := Lscale_pos (le_max_right (max T₀ (A : ℝ)) (Real.exp (Real.exp 2)))
  have h1 := hT₀ (max (max T₀ (A : ℝ)) (Real.exp (Real.exp 2)))
    (le_trans (le_max_left _ _) (le_max_left _ _))
  have hpos : 0 < (Real.exp (-eulerGamma) / 2 - Real.exp (-eulerGamma) / 4) *
      Lscale (max (max T₀ (A : ℝ)) (Real.exp (Real.exp 2))) := by
    apply mul_pos _ hL
    linarith
  exact lt_of_lt_of_le hpos (le_trans h1 (lowerDens_mono
    (largeRatio_subset (le_trans (le_max_right _ _) (le_max_left _ _)))))

theorem fixedCofactorDefect_pos (hAL : Eq_AlmostLogTail) : Cor_FixedCofactorDefect_pos := by
  intro A hA
  exact lt_of_lt_of_le (sqfreeDefectPos hAL A hA) (lowerDens_mono (fun N hN => hN.2))

theorem fixedCofactorDefect (hAL : Eq_AlmostLogTail) : Eq_FixedCofactorDefect := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := hAL ε hε
  refine ⟨⌈T₀⌉₊, fun A hA => ?_⟩
  have hT : T₀ ≤ (A : ℝ) := le_trans (Nat.le_ceil T₀) (by exact_mod_cast hA)
  exact le_trans (hT₀ A hT) (lowerDens_mono (largeRatio_subset le_rfl))

/-! ## The forced modulus has a small prime factor -/

theorem lcmUpTo_natCast (A : ℕ) : lcmUpTo (A : ℝ) = Nat.lcmUpto A := by
  unfold lcmUpTo Nat.lcmUpto
  rw [Nat.floor_natCast]

theorem PA_eq (A : ℕ) : Coverage.PA A = A * Nat.lcmUpto A := by
  unfold Coverage.PA
  rw [lcmUpTo_natCast]

theorem le_PA {A : ℕ} : A ≤ Coverage.PA A := by
  rw [PA_eq]
  exact Nat.le_mul_of_pos_right A (Nat.lcmUpto_pos A)

theorem Mlcm_dvd_lcmUpto {A e d : ℕ} (heA : e ≤ A) : Mlcm e d ∣ Nat.lcmUpto A := by
  unfold Mlcm Nat.lcmUpto
  apply Finset.lcm_dvd
  intro j hj
  unfold Dset at hj
  rw [Finset.mem_filter, Finset.mem_Ico] at hj
  exact Finset.dvd_lcm (Finset.mem_Icc.2 ⟨hj.1.1, by omega⟩)

theorem Csum_le {e d : ℕ} : Csum e d ≤ (e - 1) * Mlcm e d := by
  unfold Csum
  calc ∑ j ∈ Dset e d, Mlcm e d / j ≤ ∑ _j ∈ Dset e d, Mlcm e d :=
        Finset.sum_le_sum (fun j _ => Nat.div_le_self _ _)
    _ = (Dset e d).card * Mlcm e d := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (e - 1) * Mlcm e d := by
        apply Nat.mul_le_mul_right
        unfold Dset
        calc ((Finset.Ico 1 e).filter (· ∣ e * d)).card ≤ (Finset.Ico 1 e).card :=
              Finset.card_filter_le _ _
          _ = e - 1 := Nat.card_Ico 1 e

theorem kmodSmallPrime (hK : Fact_KmodGeTwo) : Coverage.Step_KmodSmallPrime := by
  intro A e d he heA hd
  obtain ⟨_, hM, _, hK2, _⟩ := hK e d he hd
  have hepos : 0 < e := by omega
  set g := Nat.gcd e (Mlcm e d) with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hepos
  have hge : g ≤ e := Nat.le_of_dvd hepos (Nat.gcd_dvd_left e (Mlcm e d))
  have hq1 : 1 ≤ e / g := Nat.div_pos hge hgpos
  have hMle : Mlcm e d ≤ Nat.lcmUpto A :=
    Nat.le_of_dvd (Nat.lcmUpto_pos A) (Mlcm_dvd_lcmUpto heA)
  have hchain : (e - 1) * Mlcm e d ≤ Coverage.PA A := by
    rw [PA_eq]
    exact Nat.mul_le_mul (by omega) hMle
  have hcase : e / g = 1 →
      Kmod e d = Csum e d ∧ 2 ≤ Csum e d ∧ Csum e d ≤ (e - 1) * Mlcm e d ∧
        (e - 1) * Mlcm e d ≤ Coverage.PA A := by
    intro h1
    have hKC : Kmod e d = Csum e d := by
      unfold Kmod
      rw [← hg, h1, one_mul]
    refine ⟨hKC, hKC ▸ hK2, Csum_le, hchain⟩
  refine ⟨?_, hcase⟩
  by_cases h1 : e / g = 1
  · obtain ⟨hKC, hC2, hCle, _⟩ := hcase h1
    have hne : Csum e d ≠ 1 := by omega
    refine ⟨(Csum e d).minFac, Nat.minFac_prime hne, ?_, ?_⟩
    · rw [hKC]; exact Nat.minFac_dvd _
    · exact le_trans (Nat.minFac_le (by omega)) (le_trans hCle hchain)
  · refine ⟨(e / g).minFac, Nat.minFac_prime h1, ?_, ?_⟩
    · have : e / g ∣ Kmod e d := by
        unfold Kmod
        rw [← hg]
        exact Dvd.intro _ rfl
      exact dvd_trans (Nat.minFac_dvd _) this
    · calc (e / g).minFac ≤ e / g := Nat.minFac_le (by omega)
        _ ≤ e := Nat.div_le_self e g
        _ ≤ A := heA
        _ ≤ Coverage.PA A := le_PA

/-! ## The tail `∑_{a > e} a⁻²` -/

theorem primorialR_natCast (n : ℕ) : primorialR (n : ℝ) = primorial n := by
  unfold primorialR
  rw [Nat.floor_natCast]

theorem lt_of_coprime_primorial {e a : ℕ} (ha : 1 < a) (hc : Nat.Coprime a (primorial e)) :
    e < a := by
  by_contra h
  push Not at h
  have hp := Nat.minFac_prime (by omega : a ≠ 1)
  have h2 : a.minFac ≤ e := le_trans (Nat.minFac_le (by omega)) h
  have h3 : a.minFac ∣ primorial e := hp.dvd_primorial_iff.2 h2
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc (Nat.minFac_dvd a) h3)

theorem tailSq_nonneg (e a : ℕ) : 0 ≤ Coverage.tailSq e a := by
  unfold Coverage.tailSq
  split_ifs <;> positivity

theorem coprimeSq_nonneg (e a : ℕ) : 0 ≤ Coverage.coprimeSq e a := by
  unfold Coverage.coprimeSq
  split_ifs <;> positivity

theorem tailSq_le (e a : ℕ) : Coverage.tailSq e a ≤ 1 / (a : ℝ) ^ 2 := by
  unfold Coverage.tailSq
  split_ifs
  · exact le_rfl
  · positivity

theorem coprimeSq_le_tailSq (e a : ℕ) : Coverage.coprimeSq e a ≤ Coverage.tailSq e a := by
  unfold Coverage.coprimeSq
  split_ifs with h
  · have hea : e < a := lt_of_coprime_primorial h.1 (by rw [← primorialR_natCast]; exact h.2)
    unfold Coverage.tailSq
    rw [if_pos hea]
  · exact tailSq_nonneg e a

theorem summable_tailSq (e : ℕ) : Summable (Coverage.tailSq e) :=
  Summable.of_nonneg_of_le (tailSq_nonneg e) (tailSq_le e)
    (Real.summable_one_div_nat_pow.mpr (by norm_num))

theorem summable_coprimeSq (e : ℕ) : Summable (Coverage.coprimeSq e) :=
  Summable.of_nonneg_of_le (coprimeSq_nonneg e) (coprimeSq_le_tailSq e) (summable_tailSq e)

theorem sum_range_tailSq_le (e : ℕ) (he : 1 ≤ e) (m : ℕ) :
    ∑ a ∈ Finset.range (e + 1 + m), Coverage.tailSq e a ≤ 1 / (e : ℝ) - 1 / ((e : ℝ) + m) := by
  induction m with
  | zero =>
    have h0 : ∑ a ∈ Finset.range (e + 1 + 0), Coverage.tailSq e a = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [Finset.mem_range] at ha
      unfold Coverage.tailSq
      rw [if_neg (by omega)]
    rw [h0]
    simp
  | succ m ih =>
    rw [show e + 1 + (m + 1) = (e + 1 + m) + 1 by ring, Finset.sum_range_succ]
    have ht : Coverage.tailSq e (e + 1 + m) = 1 / (((e : ℝ) + m) + 1) ^ 2 := by
      unfold Coverage.tailSq
      rw [if_pos (by omega)]
      push_cast
      ring_nf
    rw [ht]
    have hx : (0 : ℝ) < (e : ℝ) + m := by
      have : (1 : ℝ) ≤ e := by exact_mod_cast he
      positivity
    have key : 1 / (((e : ℝ) + m) + 1) ^ 2 ≤ 1 / ((e : ℝ) + m) - 1 / ((e : ℝ) + m + 1) := by
      have h1 : 1 / ((e : ℝ) + m) - 1 / ((e : ℝ) + m + 1) =
          1 / (((e : ℝ) + m) * ((e : ℝ) + m + 1)) := by
        field_simp
        ring
      rw [h1]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hre : (e : ℝ) + ((m + 1 : ℕ) : ℝ) = (e : ℝ) + m + 1 := by push_cast; ring
    rw [hre]
    linarith

theorem tsum_tailSq_le (e : ℕ) (he : 1 ≤ e) : ∑' a : ℕ, Coverage.tailSq e a ≤ 1 / (e : ℝ) := by
  apply Real.tsum_le_of_sum_range_le (tailSq_nonneg e)
  intro n
  have h1 : ∑ a ∈ Finset.range n, Coverage.tailSq e a ≤
      ∑ a ∈ Finset.range (e + 1 + n), Coverage.tailSq e a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun a _ _ => tailSq_nonneg e a)
  have h2 := sum_range_tailSq_le e he n
  have h3 : 0 ≤ 1 / ((e : ℝ) + n) := by positivity
  linarith

theorem coprimeSqTail : Coverage.Disp_CoprimeSqTail := by
  intro Q ρ h u e hctx
  obtain ⟨_, _, _, _, _, _, hlt, _⟩ := hctx
  have he2 : 2 < e := lt_of_le_of_lt (le_trans (le_max_left 2 h) (le_max_left _ Q)) hlt
  have he1 : 1 ≤ e := by omega
  have hepos : (0 : ℝ) < e := by exact_mod_cast (by omega : 0 < e)
  have he3 : (3 : ℝ) ≤ e := by exact_mod_cast (by omega : 3 ≤ e)
  refine ⟨fun a ha hc => lt_of_coprime_primorial ha (by rw [← primorialR_natCast]; exact hc),
    ?_, ?_, ?_⟩
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Summable.tsum_le_tsum (coprimeSq_le_tailSq e) (summable_coprimeSq e) (summable_tailSq e)
  · calc ((e : ℝ) + 1) * (∑' a : ℕ, Coverage.tailSq e a) ≤ ((e : ℝ) + 1) * (1 / (e : ℝ)) :=
          mul_le_mul_of_nonneg_left (tsum_tailSq_le e he1) (by positivity)
      _ = ((e : ℝ) + 1) / e := by rw [mul_one_div]
  · rw [div_le_iff₀ hepos]
    linarith


/-! ## The coprime part of `ℕ ∖ G_A`, the size of `δ_A`, `η_A`, and the reformulations -/

theorem F_one (d : ℕ) : F 1 d = sig d := by
  show F 1 d = ArithmeticFunction.sigma 1 d
  rw [ArithmeticFunction.sigma_one_apply, F, one_mul, Finset.filter_true_of_mem]
  intro q hq
  exact Nat.divisor_le hq

theorem isRough_of_coprime {P N : ℕ} (hc : Nat.Coprime N (primorial P)) : IsRough (P : ℝ) N := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpN := Nat.dvd_of_mem_primeFactors hp
  by_contra hle
  push Not at hle
  have hle' : p ≤ P := by exact_mod_cast hle
  exact hpp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc hpN (hpp.dvd_primorial_iff.2 hle'))

theorem gcovCoprimeNull (hstep : Coverage.Step_GcovValuesSmallPrime)
    (hsig : Lem_SigmaRangeZero) : Coverage.Fact_GcovCoprimeNull := by
  intro A hA
  apply densZero_subset (densZero_union hsig (hstep A hA))
  rintro N ⟨hc, e, d, he, heA, hd, rfl⟩
  by_cases he1 : e = 1
  · subst he1
    exact Or.inl ⟨d, hd, (F_one d).symm⟩
  · refine Or.inr ⟨⟨e, d, by omega, heA, hd, rfl⟩, ?_⟩
    have hc' : Nat.Coprime (F e d) (primorial (Coverage.PA A)) := by
      rwa [← primorialR_natCast]
    exact isRough_of_coprime hc'

theorem coprimeComplementDens (hnull : Coverage.Fact_GcovCoprimeNull)
    (hD : Notation_Delta_density) : Coverage.Fact_CoprimeComplementDens := by
  intro A hA
  have hy : (1 : ℝ) ≤ (Coverage.PA A : ℝ) := by exact_mod_cast le_trans hA le_PA
  have h2 := (hD _ hy).2.sdiff_densZero (hnull A hA)
  have hset : {N : ℕ | Nat.Coprime N (primorialR (Coverage.PA A)) ∧ N ∉ Gcov A} =
      {n : ℕ | Nat.Coprime n (primorialR (Coverage.PA A))} \
        {N : ℕ | Nat.Coprime N (primorialR (Coverage.PA A)) ∧ N ∈ Gcov A} := by
    ext N
    simp only [Set.mem_setOf_eq, Set.mem_sdiff]
    tauto
  rw [hset]
  exact h2

open Classical in
theorem cnt_union_of_disjoint {S T : Set ℕ} (h : Disjoint S T) (X : ℝ) :
    cnt (S ∪ T) X = cnt S X + cnt T X := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext n
    rw [Finset.mem_union, mem_cntFinset, mem_cntFinset, mem_cntFinset, Set.mem_union]
    tauto
  · rw [Finset.disjoint_left]
    intro n h1 h2
    rw [mem_cntFinset] at h1 h2
    exact Set.disjoint_left.1 h h1.2 h2.2

theorem upperDens_union_hasDens {S T : Set ℕ} {d : ℝ} (hS : HasDens S d) (h : Disjoint S T) :
    upperDens (S ∪ T) = d + upperDens T := by
  apply le_antisymm
  · calc upperDens (S ∪ T) ≤ upperDens S + upperDens T := upperDens_union_le S T
      _ = d + upperDens T := by rw [hS.upperDens_eq]
  · have heq : (fun n : ℕ => (cnt (S ∪ T) n : ℝ) / n) =
        (fun n : ℕ => (cnt T n : ℝ) / n) + (fun n : ℕ => (cnt S n : ℝ) / n) := by
      funext n
      simp only [Pi.add_apply]
      rw [cnt_union_of_disjoint h, Nat.cast_add, add_div, add_comm]
    have key := le_limsup_add (f := atTop) (u := fun n : ℕ => (cnt T n : ℝ) / n)
      (v := fun n : ℕ => (cnt S n : ℝ) / n) (isBoundedUnder_le_cnt_div T)
      (isCoboundedUnder_le_cnt_div T) (isBoundedUnder_le_cnt_div S)
      (isBoundedUnder_ge_cnt_div S)
    have hl : liminf (fun n : ℕ => (cnt S n : ℝ) / n) atTop = d := hS.lowerDens_eq
    have hu : limsup (fun n : ℕ => (cnt T n : ℝ) / n) atTop = upperDens T := rfl
    rw [hl, hu, ← heq] at key
    have hU : limsup (fun n : ℕ => (cnt (S ∪ T) n : ℝ) / n) atTop = upperDens (S ∪ T) := rfl
    rw [hU] at key
    linarith

theorem boundedCofactorComplement (hC : Coverage.Fact_CoprimeComplementDens)
    (hU : Coverage.Fact_UpperDensCompl) : Eq_BoundedCofactorComplement := by
  intro A hA
  rw [← hU (Gcov A)]
  have hP : 0 < primorialR (Coverage.PA A) := by
    unfold primorialR
    exact primorial_pos _
  have hset : (Gcov A)ᶜ =
      {N : ℕ | Nat.Coprime N (primorialR (Coverage.PA A)) ∧ N ∉ Gcov A} ∪
        {N : ℕ | 1 < Nat.gcd N (primorialR (Coverage.PA A)) ∧ N ∉ Gcov A} := by
    ext N
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · intro hN
      by_cases hc : Nat.Coprime N (primorialR (Coverage.PA A))
      · exact Or.inl ⟨hc, hN⟩
      · refine Or.inr ⟨?_, hN⟩
        have hpos : 0 < Nat.gcd N (primorialR (Coverage.PA A)) := Nat.gcd_pos_of_pos_right _ hP
        have hne : Nat.gcd N (primorialR (Coverage.PA A)) ≠ 1 := hc
        omega
    · rintro (h | h)
      · exact h.2
      · exact h.2
  have hdisj : Disjoint {N : ℕ | Nat.Coprime N (primorialR (Coverage.PA A)) ∧ N ∉ Gcov A}
      {N : ℕ | 1 < Nat.gcd N (primorialR (Coverage.PA A)) ∧ N ∉ Gcov A} := by
    rw [Set.disjoint_left]
    rintro N ⟨hc, _⟩ ⟨hg, _⟩
    have hc' : Nat.gcd N (primorialR (Coverage.PA A)) = 1 := hc
    omega
  rw [hset, upperDens_union_hasDens (hC A hA) hdisj]
  rfl

theorem logPA (hPNT : Std_PNT) : Coverage.Disp_LogPA := by
  have hid : ∀ A : ℕ, 1 ≤ A →
      Real.log (Coverage.PA A) = Real.log A + Chebyshev.psi A := by
    intro A hA
    have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast (by omega : A ≠ 0)
    have hL0 : (Nat.lcmUpto A : ℝ) ≠ 0 := by exact_mod_cast Nat.lcmUpto_ne_zero A
    rw [PA_eq, Nat.cast_mul, Real.log_mul hA0 hL0, Chebyshev.psi_eq_log_lcmUpto]
  refine ⟨hid, ?_⟩
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have h1' : Tendsto (fun A : ℕ => Real.log A / A) atTop (𝓝 0) :=
    h1.comp tendsto_natCast_atTop_atTop
  have h2' : Tendsto (fun A : ℕ => Chebyshev.psi A / A) atTop (𝓝 1) :=
    hPNT.comp tendsto_natCast_atTop_atTop
  have h3 := h1'.add (h2'.sub_const 1)
  rw [sub_self, add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with A hA
  rw [hid A hA]
  have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast (by omega : A ≠ 0)
  field_simp
  ring

theorem tendsto_PA : Tendsto (fun A : ℕ => (Coverage.PA A : ℝ)) atTop atTop :=
  tendsto_atTop_mono (fun A => (by exact_mod_cast le_PA : (A : ℝ) ≤ Coverage.PA A))
    tendsto_natCast_atTop_atTop

theorem deltaAAsymptotic (hlog : Coverage.Disp_LogPA) (hM3 : Std_Mertens3) :
    Eq_DeltaAAsymptotic := by
  have h1 : Tendsto (fun A : ℕ => Delta (Coverage.PA A) * Real.log (Coverage.PA A)) atTop
      (𝓝 (Real.exp (-eulerGamma))) := hM3.comp tendsto_PA
  have h2 : Tendsto (fun A : ℕ => Real.log (Coverage.PA A) / A) atTop (𝓝 1) := by
    have := hlog.2.const_add 1
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with A hA
    have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast (by omega : A ≠ 0)
    field_simp
    ring
  have h3 := h1.mul (h2.inv₀ one_ne_zero)
  rw [inv_one, mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with A hA
  have hP : (2 : ℝ) ≤ Coverage.PA A := by exact_mod_cast le_trans hA le_PA
  have hlogpos : 0 < Real.log (Coverage.PA A) := Real.log_pos (by linarith)
  have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast (by omega : A ≠ 0)
  unfold Coverage.deltaA
  field_simp

theorem deltaA_tendsto_zero (hΔ : Eq_DeltaAAsymptotic) : Tendsto Coverage.deltaA atTop (𝓝 0) := by
  have h := hΔ.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with A hA
  have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast (by omega : A ≠ 0)
  field_simp

theorem conjEquivEta (hBCC : Eq_BoundedCofactorComplement) (hΔ : Eq_DeltaAAsymptotic) :
    Coverage.Rem_ConjEquivEta := by
  have hδ := deltaA_tendsto_zero hΔ
  constructor
  · intro hC
    have h : Tendsto (fun A : ℕ => (1 : ℝ) - lowerDens (Gcov A) - Coverage.deltaA A) atTop
        (𝓝 (1 - 1 - 0)) := (tendsto_const_nhds.sub hC).sub hδ
    rw [sub_self, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with A hA
    have := hBCC A hA
    linarith
  · intro hη
    have h : Tendsto (fun A : ℕ => (1 : ℝ) - Coverage.deltaA A - Coverage.etaA A) atTop
        (𝓝 (1 - 0 - 0)) := (tendsto_const_nhds.sub hδ).sub hη
    rw [sub_zero, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with A hA
    have := hBCC A hA
    linarith

theorem etaDominates (hT : Prop_EtaALower_tendsto) (hΔ : Eq_DeltaAAsymptotic)
    (hBCC : Eq_BoundedCofactorComplement) : Coverage.Rem_EtaDominates := by
  have hpos : 0 < Real.exp (-eulerGamma) := Real.exp_pos _
  constructor
  · have h := hT.atTop_mul_pos (inv_pos.2 hpos) (hΔ.inv₀ hpos.ne')
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with A hA
    have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast (by omega : A ≠ 0)
    rw [mul_inv, div_eq_mul_inv,
      show (A : ℝ) * Coverage.etaA A * ((A : ℝ)⁻¹ * (Coverage.deltaA A)⁻¹) =
        ((A : ℝ) * (A : ℝ)⁻¹) * (Coverage.etaA A * (Coverage.deltaA A)⁻¹) by ring,
      mul_inv_cancel₀ hA0, one_mul]
  · intro hcontra
    have h := hΔ.add_atTop hT
    have h' : Tendsto (fun A : ℕ => (A : ℝ) * (1 - lowerDens (Gcov A))) atTop atTop := by
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with A hA
      rw [hBCC A hA]
      ring
    exact not_tendsto_nhds_of_tendsto_atTop h' _ hcontra

theorem tendsto_mul_Lscale : Tendsto (fun x : ℝ => x * Lscale x) atTop atTop := by
  have hlim : Tendsto (fun x : ℝ => x / Real.log x ^ 2) atTop atTop := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    have h' : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨by simpa using h, ?_⟩
      filter_upwards [eventually_gt_atTop 1] with x hx
      have := Real.log_pos hx
      show 0 < Real.log x ^ 2 / x
      positivity
    refine h'.inv_tendsto_nhdsGT_zero.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    simp only [Pi.inv_apply, inv_div]
  refine tendsto_atTop_mono' atTop ?_ hlim
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp (Real.exp 1)))] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have h1 : Real.exp (Real.exp 1) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hL1 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) h1
  have h2 : Real.exp 1 ≤ Real.log (Real.log x) := (Real.le_log_iff_exp_le hL1).2 h1
  have hL2 : 0 < Real.log (Real.log x) := lt_of_lt_of_le (Real.exp_pos _) h2
  have h3 : 1 ≤ Real.log (Real.log (Real.log x)) := (Real.le_log_iff_exp_le hL2).2 h2
  have h4 : Real.log (Real.log x) ≤ Real.log x := Real.log_le_self hL1.le
  show x / Real.log x ^ 2 ≤
    x * (Real.log (Real.log (Real.log x)) / (Real.log x * Real.log (Real.log x)))
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have hA : Real.log (Real.log x) ≤ Real.log x * Real.log (Real.log (Real.log x)) := by
    nlinarith
  calc x * (Real.log x * Real.log (Real.log x))
      = (x * Real.log x) * Real.log (Real.log x) := by ring
    _ ≤ (x * Real.log x) * (Real.log x * Real.log (Real.log (Real.log x))) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ = x * Real.log (Real.log (Real.log x)) * Real.log x ^ 2 := by ring

theorem tendsto_nat_mul_Lscale : Tendsto (fun A : ℕ => (A : ℝ) * Lscale A) atTop atTop :=
  tendsto_mul_Lscale.comp tendsto_natCast_atTop_atTop

theorem etaALower_bound (hFCD : Eq_FixedCofactorDefect) (hU : Coverage.Fact_UpperDensCompl)
    (hΔ : Eq_DeltaAAsymptotic) (hBCC : Eq_BoundedCofactorComplement) : Prop_EtaALower_bound := by
  intro ε hε
  obtain ⟨A₁, hA₁⟩ := hFCD (ε / 2) (by linarith)
  have hB : ∀ᶠ A : ℕ in atTop, (A : ℝ) * Coverage.deltaA A ≤ Real.exp (-eulerGamma) + 1 :=
    hΔ.eventually (ge_mem_nhds (by linarith))
  have hL : ∀ᶠ A : ℕ in atTop, 2 * (Real.exp (-eulerGamma) + 1) / ε ≤ (A : ℝ) * Lscale A :=
    tendsto_nat_mul_Lscale.eventually (eventually_ge_atTop _)
  obtain ⟨A₂, hA₂⟩ := eventually_atTop.1 (hB.and (hL.and (eventually_ge_atTop (max A₁ 1))))
  refine ⟨A₂, fun A hA => ?_⟩
  obtain ⟨hBA, hLA, hAA⟩ := hA₂ A hA
  have hA1 : 1 ≤ A := le_trans (le_max_right _ _) hAA
  have hAA₁ : A₁ ≤ A := le_trans (le_max_left _ _) hAA
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA1
  have hη : Coverage.etaA A = upperDens (Gcov A)ᶜ - Coverage.deltaA A := by
    have := hBCC A hA1
    rw [hU]
    linarith
  have hsub : lowerDens {N : ℕ | Squarefree N ∧ N ∉ Gcov A} ≤ upperDens (Gcov A)ᶜ :=
    le_trans (lowerDens_mono (fun N hN => hN.2)) (lowerDens_le_upperDens _)
  have hfcd := hA₁ A hAA₁
  have hδ : Coverage.deltaA A ≤ ε / 2 * Lscale A := by
    rw [div_le_iff₀ hε] at hLA
    have h1 : (A : ℝ) * Coverage.deltaA A ≤ (A : ℝ) * (ε / 2 * Lscale A) := by
      nlinarith
    exact le_of_mul_le_mul_left h1 hApos
  rw [hη]
  nlinarith

theorem etaALower_tendsto (hb : Prop_EtaALower_bound) : Prop_EtaALower_tendsto := by
  have hc : 0 < Real.exp (-eulerGamma) / 4 := by positivity
  obtain ⟨A₀, hA₀⟩ := hb (Real.exp (-eulerGamma) / 4) hc
  have h := tendsto_nat_mul_Lscale.const_mul_atTop hc
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [eventually_ge_atTop A₀] with A hA
  have h1 := hA₀ A hA
  have e2 : Real.exp (-eulerGamma) / 2 - Real.exp (-eulerGamma) / 4 =
      Real.exp (-eulerGamma) / 4 := by ring
  rw [e2] at h1
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  show Real.exp (-eulerGamma) / 4 * ((A : ℝ) * Lscale A) ≤ (A : ℝ) * Coverage.etaA A
  calc Real.exp (-eulerGamma) / 4 * ((A : ℝ) * Lscale A)
      = (A : ℝ) * (Real.exp (-eulerGamma) / 4 * Lscale A) := by ring
    _ ≤ (A : ℝ) * Coverage.etaA A := mul_le_mul_of_nonneg_left h1 hA0

theorem Delta_nonneg_nat (A : ℕ) : 0 ≤ Delta A := by
  unfold Delta
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt.le
  have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
  linarith

theorem Delta_tendsto_zero : Tendsto (fun A : ℕ => Delta A) atTop (𝓝 0) := by
  have hnn : ∀ n, 0 ≤ Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n :=
    fun n => Set.indicator_nonneg (fun m _ => by positivity) n
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).1 not_summable_one_div_on_primes
  have hS : ∀ A : ℕ, ∑ i ∈ Finset.range (A + 1),
      Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i =
      ∑ p ∈ (Finset.range (A + 1)).filter Nat.Prime, (1 : ℝ) / p := by
    intro A
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.Prime <;> simp [Set.indicator, hi]
  have hbound : ∀ A : ℕ, Delta A ≤ Real.exp (-(∑ i ∈ Finset.range (A + 1),
      Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i)) := by
    intro A
    rw [hS, ← Finset.sum_neg_distrib, Real.exp_sum]
    unfold Delta
    rw [Nat.floor_natCast]
    apply Finset.prod_le_prod
    · intro p hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt.le
      have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
      linarith
    · intro p _
      exact Real.one_sub_le_exp_neg _
  have hexp : Tendsto (fun A : ℕ => Real.exp (-(∑ i ∈ Finset.range (A + 1),
      Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hdiv.comp (tendsto_add_atTop_nat 1)))
  exact squeeze_zero Delta_nonneg_nat hbound hexp

theorem roughPartBound (hD : Notation_Delta_density) : Coverage.Rem_RoughPartBound := by
  refine ⟨fun A hA => ?_, Delta_tendsto_zero⟩
  have hy : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have h := (hD A hy).2
  rw [← h.upperDens_eq, ← upperDens_union_of_densZero {n : ℕ | Nat.Coprime n (primorialR A)}
    (densZero_of_finite (Set.finite_singleton (0 : ℕ)))]
  apply upperDens_mono
  rintro N ⟨hr, _⟩
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · exact Or.inr h0
  · left
    show Nat.Coprime N (primorialR A)
    rw [primorialR_natCast]
    apply Nat.coprime_of_dvd
    intro k hk hkN hkP
    have hmem : k ∈ N.primeFactors := Nat.mem_primeFactors.2 ⟨hk, hkN, hpos.ne'⟩
    have h1 := hr k hmem
    have h2 : k ≤ A := hk.dvd_primorial_iff.1 hkP
    have h2' : (k : ℝ) ≤ A := by exact_mod_cast h2
    linarith

theorem conjEquivSmallPrimePart (hR : Coverage.Rem_RoughPartBound)
    (hU : Coverage.Fact_UpperDensCompl) : Coverage.Rem_ConjEquivSmallPrimePart := by
  have hconj : Conj_BoundedCofactorWeak ↔
      Tendsto (fun A : ℕ => upperDens (Gcov A)ᶜ) atTop (𝓝 0) := by
    have heq : (fun A : ℕ => upperDens (Gcov A)ᶜ) = fun A => 1 - lowerDens (Gcov A) :=
      funext fun A => hU _
    rw [heq]
    constructor
    · intro h
      have h' : Tendsto (fun A : ℕ => (1 : ℝ) - lowerDens (Gcov A)) atTop (𝓝 (1 - 1)) :=
        tendsto_const_nhds.sub h
      rwa [sub_self] at h'
    · intro h
      have h' : Tendsto (fun A : ℕ => (1 : ℝ) - (1 - lowerDens (Gcov A))) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub h
      simp only [sub_sub_cancel, sub_zero] at h'
      exact h'
  unfold Coverage.Rem_ConjEquivSmallPrimePart
  rw [hconj]
  constructor
  · intro h
    exact squeeze_zero (fun A => upperDens_nonneg _) (fun A => upperDens_mono (fun N hN => hN.2)) h
  · intro h
    have h2 := h.add hR.2
    rw [add_zero] at h2
    refine squeeze_zero' (Eventually.of_forall fun A => upperDens_nonneg _) ?_ h2
    filter_upwards [eventually_ge_atTop 1] with A hA
    have hsub : (Gcov A)ᶜ ⊆ {N : ℕ | (∃ p ∈ N.primeFactors, p ≤ A) ∧ N ∉ Gcov A} ∪
        {N : ℕ | IsRough (A : ℝ) N ∧ N ∉ Gcov A} := by
      intro N hN
      by_cases hs : ∃ p ∈ N.primeFactors, p ≤ A
      · exact Or.inl ⟨hs, hN⟩
      · refine Or.inr ⟨fun p hp => ?_, hN⟩
        push Not at hs
        exact_mod_cast hs p hp
    calc upperDens (Gcov A)ᶜ ≤ upperDens ({N : ℕ | (∃ p ∈ N.primeFactors, p ≤ A) ∧ N ∉ Gcov A} ∪
          {N : ℕ | IsRough (A : ℝ) N ∧ N ∉ Gcov A}) := upperDens_mono hsub
      _ ≤ _ := upperDens_union_le _ _
      _ ≤ _ := add_le_add_right (hR.1 A hA) _

/-! ## Values of `F_e`, `2 ≤ e ≤ A`, are almost never `P_A`-rough -/

theorem Kmod_pos {e d : ℕ} (he : 2 ≤ e) : 0 < Kmod e d := by
  have hepos : 0 < e := by omega
  have h1 : 1 ∈ Dset e d := by
    unfold Dset
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨le_rfl, by omega⟩, one_dvd _⟩
  have hM : Mlcm e d ≠ 0 := by
    unfold Mlcm
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, hx, hx0⟩
    unfold Dset at hx
    rw [Finset.mem_filter, Finset.mem_Ico] at hx
    have hx0' : x = 0 := hx0
    omega
  have hC : 0 < Csum e d := by
    unfold Csum
    have h2 : Mlcm e d / 1 ≤ ∑ j ∈ Dset e d, Mlcm e d / j :=
      Finset.single_le_sum (f := fun j => Mlcm e d / j) (fun j _ => Nat.zero_le _) h1
    rw [Nat.div_one] at h2
    omega
  unfold Kmod
  have hg : 0 < Nat.gcd e (Mlcm e d) := Nat.gcd_pos_of_pos_left _ hepos
  have hq : 0 < e / Nat.gcd e (Mlcm e d) :=
    Nat.div_pos (Nat.le_of_dvd hepos (Nat.gcd_dvd_left _ _)) hg
  exact Nat.mul_pos hq hC

open Classical in
/-- Counting through a bounded-multiplicity parametrisation: if every `N ∈ T` is `φ e m` for some
`e ∈ E` and some `m ∈ B` with `m ≤ c N`, then `#(T ∩ [1, n]) ≤ #E · #(B ∩ [1, c n])`. -/
theorem cnt_le_card_mul_cnt {T B : Set ℕ} (E : Finset ℕ) (φ : ℕ → ℕ → ℕ) (c : ℕ)
    (h : ∀ N ∈ T, 1 ≤ N → ∃ e ∈ E, ∃ m, 1 ≤ m ∧ m ≤ c * N ∧ m ∈ B ∧ φ e m = N) (n : ℕ) :
    cnt T n ≤ E.card * cnt B ((c * n : ℕ) : ℝ) := by
  rw [cnt_natCast, cnt_natCast]
  calc ((Finset.Icc 1 n).filter (· ∈ T)).card
      ≤ (E.biUnion (fun e => ((Finset.Icc 1 (c * n)).filter (· ∈ B)).image (φ e))).card := by
        apply Finset.card_le_card
        intro N hN
        rw [mem_cntFinset] at hN
        obtain ⟨e, he, m, hm1, hmc, hmB, hφ⟩ := h N hN.2 hN.1.1
        rw [Finset.mem_biUnion]
        refine ⟨e, he, Finset.mem_image.2 ⟨m, ?_, hφ⟩⟩
        rw [mem_cntFinset]
        exact ⟨⟨hm1, le_trans hmc (Nat.mul_le_mul le_rfl hN.1.2)⟩, hmB⟩
    _ ≤ ∑ e ∈ E, (((Finset.Icc 1 (c * n)).filter (· ∈ B)).image (φ e)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ E, ((Finset.Icc 1 (c * n)).filter (· ∈ B)).card :=
        Finset.sum_le_sum (fun e _ => Finset.card_image_le)
    _ = E.card * ((Finset.Icc 1 (c * n)).filter (· ∈ B)).card := by
        rw [Finset.sum_const, smul_eq_mul]

theorem gcovValuesSmallPrime (hstep : Coverage.Step_KmodSmallPrime) (hfin : Fact_KmodFinite)
    (hfm : Lem_FmModulus) (hnorm : Lem_FixedModulusNormality) :
    Coverage.Step_GcovValuesSmallPrime := by
  intro A hA
  have hKfin : {K : ℕ | ∃ e d : ℕ, 2 ≤ e ∧ e ≤ A ∧ 1 ≤ d ∧ Kmod e d = K}.Finite := by
    have hsub : {K : ℕ | ∃ e d : ℕ, 2 ≤ e ∧ e ≤ A ∧ 1 ≤ d ∧ Kmod e d = K} ⊆
        ⋃ e ∈ ((Finset.Icc 2 A : Finset ℕ) : Set ℕ), {K : ℕ | ∃ d : ℕ, 1 ≤ d ∧ Kmod e d = K} := by
      rintro K ⟨e, d, he, heA, hd, rfl⟩
      rw [Set.mem_iUnion₂]
      exact ⟨e, Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨he, heA⟩), d, hd, rfl⟩
    exact Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet _)
      (fun e he => hfin e (Finset.mem_Icc.1 (Finset.mem_coe.1 he)).1)) hsub
  have hKV : ∀ e d, 2 ≤ e → e ≤ A → 1 ≤ d → Kmod e d ∣ hKfin.toFinset.lcm id := by
    intro e d he heA hd
    exact Finset.dvd_lcm ((Set.Finite.mem_toFinset hKfin).2 ⟨e, d, he, heA, hd, rfl⟩)
  have hV0 : hKfin.toFinset.lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨K, hK, hK0⟩
    rw [Set.Finite.mem_toFinset] at hK
    obtain ⟨e, d, he, _, _, rfl⟩ := hK
    exact (Kmod_pos (d := d) he).ne' hK0
  generalize hKfin.toFinset.lcm id = V at hKV hV0
  have hB := hnorm V (Nat.one_le_iff_ne_zero.2 hV0)
  have key : ∀ e d, 2 ≤ e → e ≤ A → 1 ≤ d → IsRough (Coverage.PA A : ℝ) (F e d) →
      ¬ V ∣ sig (e * d) := by
    intro e d he heA hd hrough hVdvd
    obtain ⟨⟨p, hp, hpK, hpP⟩, _⟩ := hstep A e d he heA hd
    have hcong : F e d ≡ sig (e * d) [MOD p] := ((hfm e d he hd).2.2.1).of_dvd hpK
    have hpsig : p ∣ sig (e * d) := dvd_trans hpK (dvd_trans (hKV e d he heA hd) hVdvd)
    have hpF : p ∣ F e d :=
      Nat.modEq_zero_iff_dvd.1 (hcong.trans (Nat.modEq_zero_iff_dvd.2 hpsig))
    have hF0 : F e d ≠ 0 := by
      have := F_ge e d (by omega) hd
      omega
    have hmem : p ∈ (F e d).primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpF, hF0⟩
    have h1 := hrough p hmem
    have h2 : (p : ℝ) ≤ (Coverage.PA A : ℝ) := by exact_mod_cast hpP
    linarith
  have hmap : ∀ N ∈ {N : ℕ | (∃ e d : ℕ, 2 ≤ e ∧ e ≤ A ∧ 1 ≤ d ∧ N = F e d) ∧
      IsRough (Coverage.PA A : ℝ) N}, 1 ≤ N → ∃ e ∈ Finset.Icc 2 A, ∃ m, 1 ≤ m ∧ m ≤ A * N ∧
        m ∈ {n : ℕ | ¬ V ∣ sig n} ∧ F e (m / e) = N := by
    rintro N ⟨⟨e, d, he, heA, hd, rfl⟩, hrough⟩ _
    refine ⟨e, Finset.mem_Icc.2 ⟨he, heA⟩, e * d, Nat.mul_pos (by omega) hd,
      Nat.mul_le_mul heA (F_ge e d (by omega) hd), key e d he heA hd hrough, ?_⟩
    rw [Nat.mul_div_cancel_left d (by omega : 0 < e)]
  apply densZero_iff_eventually_le.2
  intro ε hε
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hBev := densZero_iff_eventually_le.1 hB (ε / ((A : ℝ) * A)) (by positivity)
  have htend : Tendsto (fun n : ℕ => A * n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hA) tendsto_id
  filter_upwards [htend.eventually hBev] with n hn
  have hc := cnt_le_card_mul_cnt (Finset.Icc 2 A) (fun e m => F e (m / e)) A hmap n
  have hcard : ((Finset.Icc 2 A).card : ℝ) ≤ A := by
    rw [Nat.card_Icc]
    exact_mod_cast (by omega : A + 1 - 2 ≤ A)
  have hc' : (cnt {N : ℕ | (∃ e d : ℕ, 2 ≤ e ∧ e ≤ A ∧ 1 ≤ d ∧ N = F e d) ∧
      IsRough (Coverage.PA A : ℝ) N} n : ℝ) ≤
      ((Finset.Icc 2 A).card : ℝ) * (cnt {n : ℕ | ¬ V ∣ sig n} ((A * n : ℕ) : ℝ) : ℝ) := by
    exact_mod_cast hc
  have hBn : (0 : ℝ) ≤ (cnt {n : ℕ | ¬ V ∣ sig n} ((A * n : ℕ) : ℝ) : ℝ) := Nat.cast_nonneg _
  calc (cnt {N : ℕ | (∃ e d : ℕ, 2 ≤ e ∧ e ≤ A ∧ 1 ≤ d ∧ N = F e d) ∧
      IsRough (Coverage.PA A : ℝ) N} n : ℝ)
      ≤ ((Finset.Icc 2 A).card : ℝ) * (cnt {n : ℕ | ¬ V ∣ sig n} ((A * n : ℕ) : ℝ) : ℝ) := hc'
    _ ≤ (A : ℝ) * (cnt {n : ℕ | ¬ V ∣ sig n} ((A * n : ℕ) : ℝ) : ℝ) :=
        mul_le_mul_of_nonneg_right hcard hBn
    _ ≤ (A : ℝ) * (ε / ((A : ℝ) * A) * ((A * n : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hn hA0.le
    _ = ε * n := by
        push_cast
        field_simp

/-! ## `r_t(N)` counts the pairs `(n, j)` -/

theorem getD_eq {l : List ℕ} {i : ℕ} (hi : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem prefix_eq_Fdiv_getElem (n i : ℕ) (hi : i < (n.divisors.sort (· ≤ ·)).length) :
    prefixSumDivisors n (i + 1) = Fdiv n (n.divisors.sort (· ≤ ·))[i] := by
  have hidx : (i + 1) - 1 < (n.divisors.sort (· ≤ ·)).length := by omega
  have h : ((n.divisors.sort (· ≤ ·)).take (i + 1)).toFinset =
      n.divisors.filter (· ≤ (n.divisors.sort (· ≤ ·))[i]) :=
    take_sort_toFinset n (i + 1) hidx (by omega)
  rw [prefixSumDivisors, Fdiv,
    list_sum_eq_toFinset_sum ((n.divisors.sort_nodup (· ≤ ·)).take), h]
  rfl

theorem sigmaPrefix_spec {n k : ℕ} (hk : k < n.divisors.card) :
    (n.divisors.sort (· ≤ ·)).getD (n.divisors.card - 1 - k) 0 ∈ n.divisors ∧
      sigmaPrefix k n = F (n / (n.divisors.sort (· ≤ ·)).getD (n.divisors.card - 1 - k) 0)
        ((n.divisors.sort (· ≤ ·)).getD (n.divisors.card - 1 - k) 0) := by
  have hlen : (n.divisors.sort (· ≤ ·)).length = n.divisors.card := Finset.length_sort _
  have hi : n.divisors.card - 1 - k < (n.divisors.sort (· ≤ ·)).length := by omega
  rw [getD_eq hi]
  have hmem : (n.divisors.sort (· ≤ ·))[n.divisors.card - 1 - k] ∈ n.divisors := by
    rw [← Finset.mem_sort (· ≤ ·)]
    exact List.getElem_mem hi
  refine ⟨hmem, ?_⟩
  rw [F_eq_Fdiv (Nat.dvd_of_mem_divisors hmem), ← prefix_eq_Fdiv_getElem n _ hi]
  unfold sigmaPrefix
  rw [if_pos hk]
  congr 1
  omega

theorem getD_sort_inj {n i j : ℕ} (hi : i < n.divisors.card) (hj : j < n.divisors.card)
    (h : (n.divisors.sort (· ≤ ·)).getD i 0 = (n.divisors.sort (· ≤ ·)).getD j 0) : i = j := by
  have hlen : (n.divisors.sort (· ≤ ·)).length = n.divisors.card := Finset.length_sort _
  have hi' : i < (n.divisors.sort (· ≤ ·)).length := by omega
  have hj' : j < (n.divisors.sort (· ≤ ·)).length := by omega
  rw [getD_eq hi', getD_eq hj'] at h
  have hslt : (n.divisors.sort (· ≤ ·)).SortedLT := Finset.sortedLT_sort n.divisors
  have h1 := (hslt.getElem_le_getElem_iff (hi := hi') (hj := hj')).1 h.le
  have h2 := (hslt.getElem_le_getElem_iff (hi := hj') (hj := hi')).1 h.ge
  omega

theorem rtPairs : Coverage.Fact_RtPairs := by
  intro t ht N hN
  have hX0 : 0 ≤ t * N := by positivity
  unfold rt
  symm
  apply Finset.card_bij (fun q _ =>
    (q.1 / (q.1.divisors.sort (· ≤ ·)).getD (q.1.divisors.card - 1 - q.2) 0,
      (q.1.divisors.sort (· ≤ ·)).getD (q.1.divisors.card - 1 - q.2) 0))
  · rintro ⟨n, k⟩ hq
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hq
    dsimp only at hq
    obtain ⟨⟨⟨hn1, hnX⟩, _⟩, hkτ, hσ⟩ := hq
    obtain ⟨hmem, hs⟩ := sigmaPrefix_spec hkτ
    dsimp only
    generalize (n.divisors.sort (· ≤ ·)).getD (n.divisors.card - 1 - k) 0 = d at hmem hs ⊢
    have hdvd := Nat.dvd_of_mem_divisors hmem
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hmem
    have hdn : d ≤ n := Nat.divisor_le hmem
    have hed : n / d * d = n := Nat.div_mul_cancel hdvd
    have hnR : (n : ℝ) ≤ t * N := (Nat.le_floor_iff hX0).1 hnX
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨Nat.div_pos hdn hdpos, le_trans (Nat.div_le_self n d) hnX⟩,
      ⟨hdpos, le_trans hdn hnX⟩⟩, ?_, ?_⟩
    · rw [← hs]
      exact hσ
    · rw [hed]
      exact hnR
  · rintro ⟨n, k⟩ hq ⟨n', k'⟩ hq' heq
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hq hq'
    dsimp only at hq hq'
    obtain ⟨⟨⟨hn1, _⟩, _⟩, hkτ, _⟩ := hq
    obtain ⟨⟨⟨hn1', _⟩, _⟩, hkτ', _⟩ := hq'
    obtain ⟨hmem, _⟩ := sigmaPrefix_spec hkτ
    obtain ⟨hmem', _⟩ := sigmaPrefix_spec hkτ'
    dsimp only at heq
    rw [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have hnn : n = n' := by
      rw [← Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hmem),
        ← Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hmem'), h1, h2]
    subst hnn
    have hidx := getD_sort_inj (by omega) (by omega) h2
    have hkk : k = k' := by omega
    rw [hkk]
  · rintro ⟨e, d⟩ hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨he1, _⟩, ⟨hd1, _⟩⟩, hF, hle⟩ := hp
    have hn1 : 1 ≤ e * d := Nat.mul_pos he1 hd1
    have hmem : d ∈ (e * d).divisors := Nat.mem_divisors.2 ⟨dvd_mul_left d e, by omega⟩
    have hL : d ∈ (e * d).divisors.sort (· ≤ ·) := (Finset.mem_sort _).2 hmem
    obtain ⟨i, hi, hdi⟩ := List.getElem_of_mem hL
    have hlen : ((e * d).divisors.sort (· ≤ ·)).length = (e * d).divisors.card :=
      Finset.length_sort _
    have hiτ : i < (e * d).divisors.card := by omega
    have hτn : (e * d).divisors.card ≤ e * d := Nat.card_divisors_le_self _
    have hnX : e * d ≤ ⌊t * N⌋₊ := Nat.le_floor hle
    have hkτ : (e * d).divisors.card - 1 - i < (e * d).divisors.card := by omega
    have hidx : (e * d).divisors.card - 1 - ((e * d).divisors.card - 1 - i) = i := by omega
    have hD : ((e * d).divisors.sort (· ≤ ·)).getD
        ((e * d).divisors.card - 1 - ((e * d).divisors.card - 1 - i)) 0 = d := by
      rw [hidx, getD_eq hi, hdi]
    refine ⟨(e * d, (e * d).divisors.card - 1 - i), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
      obtain ⟨_, hs⟩ := sigmaPrefix_spec hkτ
      rw [hD, Nat.mul_div_cancel e hd1] at hs
      exact ⟨⟨⟨hn1, hnX⟩, by omega⟩, hkτ, hs.trans hF⟩
    · dsimp only
      rw [hD, Nat.mul_div_cancel e hd1]

/-! ## `eq:T` ⟺ tightness of `ν_X` -/

open Classical in
theorem nuX_Ioi (X : ℝ) (a : ℝ≥0∞) :
    nuX X (Set.Ioi a) =
      (Rcnt X : ℝ≥0∞)⁻¹ * (cnt {N : ℕ | N ∈ R ∧ a < ratioE N} X : ℝ≥0∞) := by
  rw [nuX, MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.finsetSum_apply, smul_eq_mul]
  congr 1
  unfold cnt
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro N _
  rw [MeasureTheory.Measure.dirac_apply' _ measurableSet_Ioi, Set.indicator_apply]
  simp only [Set.mem_Ioi, Pi.one_apply, Set.mem_setOf_eq]
  split_ifs <;> simp_all

theorem inv_mul_le_ofReal_iff {r c : ℕ} (hr : r ≠ 0) {δ : ℝ} (hδ : 0 ≤ δ) :
    (r : ℝ≥0∞)⁻¹ * (c : ℝ≥0∞) ≤ ENNReal.ofReal δ ↔ (c : ℝ) ≤ δ * r := by
  rw [ENNReal.inv_mul_le_iff (by exact_mod_cast hr) (ENNReal.natCast_ne_top r),
    ← ENNReal.ofReal_natCast r, ← ENNReal.ofReal_mul (Nat.cast_nonneg r),
    ← ENNReal.ofReal_natCast c, ENNReal.ofReal_le_ofReal_iff (by positivity), mul_comm]

/-- On `𝓡`, `r_A(N) = 0` iff the ratio `f(N)/N` exceeds `A` (for `A > 0`). -/
theorem rt_eq_zero_iff (hRt : Coverage.Fact_RtPosIff) (hER : Eq_ExactRepresentability)
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : N ∈ R) :
    rt A N = 0 ↔ ENNReal.ofReal A < ratioE N := by
  have hN1 : 1 ≤ N := by
    have h := hN
    rw [hER] at h
    exact h.1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  unfold ratioE
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hA.le, lt_div_iff₀ hNpos, ← not_le,
    ← hRt A hA N hN]
  omega

theorem big_subset_rt (hRt : Coverage.Fact_RtPosIff) (hER : Eq_ExactRepresentability)
    {A : ℝ} (hA : 0 < A) :
    {N : ℕ | N ∈ R ∧ ENNReal.ofReal A < ratioE N} ⊆ {N : ℕ | rt A N = 0} := by
  rintro N ⟨hN, hlt⟩
  exact (rt_eq_zero_iff hRt hER hA hN).2 hlt

theorem rt_subset_big (hRt : Coverage.Fact_RtPosIff) (hER : Eq_ExactRepresentability)
    {A : ℝ} (hA : 0 < A) :
    {N : ℕ | rt A N = 0} ⊆ {N : ℕ | N ∈ R ∧ ENNReal.ofReal A < ratioE N} ∪ {0, 2, 5} := by
  intro N hN
  by_cases hR : N ∈ R
  · exact Or.inl ⟨hR, (rt_eq_zero_iff hRt hER hA hR).1 hN⟩
  · right
    have h := hR
    rw [hER] at h
    simp only [Set.mem_setOf_eq, not_and_or, not_not, not_le] at h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega

theorem big_anti {A T : ℝ} (h : A ≤ T) :
    {N : ℕ | N ∈ R ∧ ENNReal.ofReal T < ratioE N} ⊆
      {N : ℕ | N ∈ R ∧ ENNReal.ofReal A < ratioE N} := by
  rintro N ⟨hN, hlt⟩
  exact ⟨hN, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal h) hlt⟩

theorem eqT_of_nuTight (hRt : Coverage.Fact_RtPosIff) (hER : Eq_ExactRepresentability)
    (hRc : Intro_RcntFormula) (hNT : Coverage.NuTight) : Eq_T := by
  have key : ∀ ε : ℝ, 0 < ε → ∀ᶠ A : ℝ in atTop, upperDens {N : ℕ | rt A N = 0} ≤ ε := by
    intro ε hε
    have h1 := (ENNReal.tendsto_nhds_zero.1 hNT) (ENNReal.ofReal (ε / 2))
      (ENNReal.ofReal_pos.2 (by linarith))
    filter_upwards [h1, eventually_ge_atTop (1 : ℝ)] with A hA hA1
    have hA0 : 0 < A := by linarith
    apply upperDens_le_of_eventually
    filter_upwards [eventually_ge_atTop (max 5 ⌈6 / ε⌉₊)] with n hn
    have hn5 : 5 ≤ n := le_trans (le_max_left _ _) hn
    have hnε : 6 / ε ≤ (n : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hn)
    have hX : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hν : nuX n (Set.Ioi (ENNReal.ofReal A)) ≤ ENNReal.ofReal (ε / 2) :=
      le_trans (le_iSup₂ (f := fun (X : ℝ) (_ : 1 ≤ X) => nuX X (Set.Ioi (ENNReal.ofReal A)))
        (n : ℝ) hX) hA
    rw [nuX_Ioi, hRc n (by exact_mod_cast hn5), Nat.floor_natCast,
      inv_mul_le_ofReal_iff (by omega) (by positivity)] at hν
    have hsub := cnt_mono (rt_subset_big hRt hER hA0) (n : ℝ)
    have hu := cnt_union_le {N : ℕ | N ∈ R ∧ ENNReal.ofReal A < ratioE N} {0, 2, 5} (n : ℝ)
    have hfin : cnt ({0, 2, 5} : Set ℕ) (n : ℝ) ≤ 3 := by
      refine le_trans (cnt_le_card_of_finite (Set.toFinite _) (n : ℝ)) ?_
      rw [Set.toFinite_toFinset, Set.toFinset_insert, Set.toFinset_insert,
        Set.toFinset_singleton]
      exact le_trans (Finset.card_insert_le _ _)
        (by rw [Finset.card_insert_of_notMem (by decide), Finset.card_singleton])
    have hcast : ((n - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 2
    have h6 : 6 ≤ ε * n := by rwa [div_le_iff₀ hε, mul_comm] at hnε
    have hall : (cnt {N : ℕ | rt A N = 0} n : ℝ) ≤
        (cnt {N : ℕ | N ∈ R ∧ ENNReal.ofReal A < ratioE N} n : ℝ) + 3 := by
      exact_mod_cast le_trans hsub (le_trans hu (Nat.add_le_add_left hfin _))
    nlinarith
  rw [Eq_T, tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall (fun A => lt_of_lt_of_le ha (upperDens_nonneg _)),
    fun a ha => ?_⟩
  filter_upwards [key (a / 2) (by linarith)] with A hA
  linarith

theorem nuTight_of_eqT (hRt : Coverage.Fact_RtPosIff) (hER : Eq_ExactRepresentability)
    (hRc : Intro_RcntFormula) (hT : Eq_T) : Coverage.NuTight := by
  unfold Coverage.NuTight
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨η, hη, hηε⟩ : ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal η ≤ ε := by
    by_cases htop : ε = ⊤
    · exact ⟨1, one_pos, by rw [htop]; exact le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' htop, by rw [ENNReal.ofReal_toReal htop]⟩
  have hev := (tendsto_order.1 hT).2 (η / 2) (by linarith)
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.1 hev
  have hAd : upperDens {N : ℕ | rt (max A₁ 1) N = 0} < η / 2 := hA₁ _ (le_max_left _ _)
  have hA0 : (0 : ℝ) < max A₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (eventually_cnt_lt_mul_of_upperDens_lt hAd)
  filter_upwards [eventually_ge_atTop (max (max A₁ 1) (∑ N ∈ Finset.range (max n₀ 5), (f N : ℝ)))]
    with T hT
  have hTA : max A₁ 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTM : ∑ N ∈ Finset.range (max n₀ 5), (f N : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  refine le_trans (iSup₂_le fun X hX => ?_) hηε
  rw [nuX_Ioi]
  by_cases hn : ⌊X⌋₊ < max n₀ 5
  · have h0 : cnt {N : ℕ | N ∈ R ∧ ENNReal.ofReal T < ratioE N} X = 0 := by
      unfold cnt
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro N hN
      rw [mem_cntFinset] at hN
      obtain ⟨⟨hN1, hNX⟩, _, hlt⟩ := hN
      have hNr : N ∈ Finset.range (max n₀ 5) := Finset.mem_range.2 (by omega)
      have hfN : (f N : ℝ) ≤ T :=
        le_trans (Finset.single_le_sum (fun i _ => Nat.cast_nonneg (f i)) hNr) hTM
      have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      have hdiv : (f N : ℝ) / N ≤ T := le_trans (div_le_self (Nat.cast_nonneg _) hN1') hfN
      have := ENNReal.ofReal_le_ofReal hdiv
      unfold ratioE at hlt
      exact absurd hlt (not_lt.2 this)
    rw [h0, Nat.cast_zero, mul_zero]
    exact zero_le
  · push Not at hn
    have hX0 : 0 ≤ X := le_trans zero_le_one hX
    have hn5 : 5 ≤ ⌊X⌋₊ := le_trans (le_max_right _ _) hn
    have hX5 : (5 : ℝ) ≤ X := le_trans (by exact_mod_cast hn5) (Nat.floor_le hX0)
    rw [hRc X hX5, inv_mul_le_ofReal_iff (by omega) hη.le]
    have h1 := cnt_mono (big_anti hTA) X
    have h2 := cnt_mono (big_subset_rt hRt hER hA0) X
    have h3 := hn₀ ⌊X⌋₊ (le_trans (le_max_left _ _) hn)
    rw [cnt_floor] at h3
    have hcast : ((⌊X⌋₊ - 2 : ℕ) : ℝ) = (⌊X⌋₊ : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hn5' : (5 : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hn5
    have h12 : (cnt {N : ℕ | N ∈ R ∧ ENNReal.ofReal T < ratioE N} X : ℝ) ≤
        (cnt {N : ℕ | rt (max A₁ 1) N = 0} X : ℝ) := by exact_mod_cast le_trans h1 h2
    rw [hcast]
    nlinarith

theorem T_iff_Conj (hRt : Coverage.Fact_RtPosIff) (hER : Eq_ExactRepresentability)
    (hTE : Prop_TightnessEquivalence) (hRc : Intro_RcntFormula) : Coverage.Rem_T_iff_Conj := by
  unfold Coverage.Rem_T_iff_Conj
  rw [hTE.2.2]
  exact ⟨nuTight_of_eqT hRt hER hRc, eqT_of_nuTight hRt hER hRc⟩

end Principia.Erdos1054.Proofs.CoverageEta

namespace Principia.Erdos1054.Proofs

/-! ## The obligations, stated by name -/

theorem leaf_Coverage_Fact_RtPairs : Principia.Erdos1054.Coverage.Fact_RtPairs :=
  CoverageEta.rtPairs

theorem leaf_Coverage_Fact_RtPosIff : Principia.Erdos1054.Coverage.Fact_RtPosIff :=
  CoverageEta.rtPosIff

theorem leaf_Coverage_Fact_GcovSubsetRtPos : Principia.Erdos1054.Coverage.Fact_GcovSubsetRtPos :=
  CoverageEta.gcovSubsetRtPos

theorem leaf_Coverage_Fact_UpperDensCompl : Principia.Erdos1054.Coverage.Fact_UpperDensCompl :=
  CoverageEta.upperDensCompl

theorem leaf_Coverage_Disp_CoprimeSqTail : Principia.Erdos1054.Coverage.Disp_CoprimeSqTail :=
  CoverageEta.coprimeSqTail

theorem link_Coverage_Rem_SqfreeDefectPos :
    Principia.Erdos1054.Spine.Link_Coverage_Rem_SqfreeDefectPos :=
  fun hAL => CoverageEta.sqfreeDefectPos hAL

theorem link_Cor_FixedCofactorDefect_pos :
    Principia.Erdos1054.Spine.Link_Cor_FixedCofactorDefect_pos :=
  fun hAL => CoverageEta.fixedCofactorDefect_pos hAL

theorem link_Eq_FixedCofactorDefect : Principia.Erdos1054.Spine.Link_Eq_FixedCofactorDefect :=
  fun hAL => CoverageEta.fixedCofactorDefect hAL

theorem link_Coverage_Step_KmodSmallPrime :
    Principia.Erdos1054.Spine.Link_Coverage_Step_KmodSmallPrime :=
  fun hK => CoverageEta.kmodSmallPrime hK

theorem link_Coverage_Step_GcovValuesSmallPrime :
    Principia.Erdos1054.Spine.Link_Coverage_Step_GcovValuesSmallPrime :=
  fun hstep hfin hfm hnorm => CoverageEta.gcovValuesSmallPrime hstep hfin hfm hnorm

theorem link_Coverage_Fact_GcovCoprimeNull :
    Principia.Erdos1054.Spine.Link_Coverage_Fact_GcovCoprimeNull :=
  fun hstep hsig => CoverageEta.gcovCoprimeNull hstep hsig

theorem link_Coverage_Fact_CoprimeComplementDens :
    Principia.Erdos1054.Spine.Link_Coverage_Fact_CoprimeComplementDens :=
  fun hnull hD => CoverageEta.coprimeComplementDens hnull hD

theorem link_Eq_BoundedCofactorComplement :
    Principia.Erdos1054.Spine.Link_Eq_BoundedCofactorComplement :=
  fun hC hU => CoverageEta.boundedCofactorComplement hC hU

theorem link_Coverage_Disp_LogPA : Principia.Erdos1054.Spine.Link_Coverage_Disp_LogPA :=
  fun hPNT => CoverageEta.logPA hPNT

theorem link_Eq_DeltaAAsymptotic : Principia.Erdos1054.Spine.Link_Eq_DeltaAAsymptotic :=
  fun hlog hM3 => CoverageEta.deltaAAsymptotic hlog hM3

theorem link_Prop_EtaALower_bound : Principia.Erdos1054.Spine.Link_Prop_EtaALower_bound :=
  fun hFCD hU hΔ hBCC => CoverageEta.etaALower_bound hFCD hU hΔ hBCC

theorem link_Prop_EtaALower_tendsto : Principia.Erdos1054.Spine.Link_Prop_EtaALower_tendsto :=
  fun hb => CoverageEta.etaALower_tendsto hb

theorem link_Coverage_Rem_EtaDominates :
    Principia.Erdos1054.Spine.Link_Coverage_Rem_EtaDominates :=
  fun hT hΔ hBCC => CoverageEta.etaDominates hT hΔ hBCC

theorem link_Coverage_Rem_ConjEquivEta :
    Principia.Erdos1054.Spine.Link_Coverage_Rem_ConjEquivEta :=
  fun hBCC hΔ => CoverageEta.conjEquivEta hBCC hΔ

theorem link_Coverage_Rem_RoughPartBound :
    Principia.Erdos1054.Spine.Link_Coverage_Rem_RoughPartBound :=
  fun hD => CoverageEta.roughPartBound hD

theorem link_Coverage_Rem_ConjEquivSmallPrimePart :
    Principia.Erdos1054.Spine.Link_Coverage_Rem_ConjEquivSmallPrimePart :=
  fun hR hU => CoverageEta.conjEquivSmallPrimePart hR hU

theorem link_Coverage_Rem_T_iff_Conj : Principia.Erdos1054.Spine.Link_Coverage_Rem_T_iff_Conj :=
  fun hRt hER hTE hRc => CoverageEta.T_iff_Conj hRt hER hTE hRc

end Principia.Erdos1054.Proofs
