/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TrompaisIBP
import Mathlib.Analysis.Fourier.PoissonSummation

set_option autoImplicit false

/-!
# `MPTC.PoissonOdd`, PROVED, via Mathlib's Poisson summation

For a continuous `g` vanishing off `(0, 1)` whose transform `ĝ(u) = ∫ g(t)e(−tu) dt` obeys
`|ĝ(u)|(2πu)² ≤ C`, and `ρ > 0`:

  `∑_{m ≤ ρ odd} g(m/ρ)e(mβ) = ∑_{j ∈ ℤ} (ρ/2)(−1)^j ĝ(ρ(j/2 − β))`  (`poisson_odd`).

Proof: Mathlib's `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable` for
`F(t) = g(t/ρ)e(tβ')` (compactly supported; `𝓕F(w) = ρĝ(ρ(w − β'))` is summable over `ℤ` from the
`C/(2πu)²` bound), at `β' = β` and at `β' = β − 1/2` (`e(−m/2) = (−1)^m`); the half-difference
keeps the odd `m`, and the even/odd `j` split reassembles the right side. `η₂` meets the
hypotheses with `C = 84` (`EtaHatIBP` + `|g| ≤ 9`, `|f̂| ≤ 48`).
-/

namespace Principia.Common.TernaryGoldbach.MPTP

open Principia.Common.Goldbach MeasureTheory Set Filter
open Principia.Common.TernaryGoldbach.MPTC Principia.Common.TernaryGoldbach.MPTI
  Principia.Common.TernaryGoldbach.MPB2
open scoped FourierTransform

/-- **`ĝ(u) = ∫ g(t)e(−tu) dt`.** -/
noncomputable def gHat (g : ℝ → ℝ) (u : ℝ) : ℂ := ∫ t, ((g t : ℝ) : ℂ) * e (-(t * u))

/-- `e(a)e(b) = e(a + b)`. -/
theorem e_mul_e (a b : ℝ) : e a * e b = e (a + b) := by
  unfold e
  rw [← Complex.exp_add]
  push_cast
  ring_nf

/-- `‖e(a)‖ = 1`. -/
theorem norm_e (a : ℝ) : ‖e a‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  simp

/-- `e(−m/2) = (−1)^m`. -/
theorem e_neg_half (m : ℕ) : e (-((m : ℝ) / 2)) = (-1 : ℂ) ^ m := by
  unfold e
  have h : 2 * (Real.pi : ℂ) * Complex.I * ((-((m : ℝ) / 2) : ℝ) : ℂ) =
      (m : ℂ) * (-(Real.pi * Complex.I)) := by
    push_cast
    ring
  rw [h, Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- The transform of `F(t) = g(t/ρ)e(tβ')`: `𝓕F(w) = ρĝ(ρ(w − β'))`. -/
theorem fourier_F (g : ℝ → ℝ) (ρ β' : ℝ) (hρ : 0 < ρ) (w : ℝ) :
    𝓕 (fun t : ℝ => ((g (t / ρ) : ℝ) : ℂ) * e (t * β')) w =
      (ρ : ℂ) * gHat g (ρ * (w - β')) := by
  rw [Real.fourier_real_eq]
  have hint : ∀ v : ℝ, Real.fourierChar (-(v * w)) • (((g (v / ρ) : ℝ) : ℂ) * e (v * β')) =
      (fun s : ℝ => ((g s : ℝ) : ℂ) * e (-(s * (ρ * (w - β'))))) (v / ρ) := by
    intro v
    rw [Circle.smul_def, Real.fourierChar_apply]
    have h1 : Complex.exp (((2 * Real.pi * -(v * w) : ℝ) : ℂ) * Complex.I) = e (-(v * w)) := by
      unfold e
      congr 1
      push_cast
      ring
    rw [h1, smul_eq_mul, mul_left_comm, e_mul_e]
    dsimp only
    congr 2
    field_simp
    ring
  simp_rw [hint]
  rw [Measure.integral_comp_div (fun s : ℝ => ((g s : ℝ) : ℂ) * e (-(s * (ρ * (w - β'))))) ρ,
    abs_of_pos hρ, Complex.real_smul]
  rfl

/-- The `F`-side of Poisson is the finite sum over `0 < n ≤ ρ`. -/
theorem tsum_F (g : ℝ → ℝ) (h0 : ∀ t, t ≤ 0 → g t = 0) (h1 : ∀ t, 1 ≤ t → g t = 0)
    (ρ β' : ℝ) (hρ : 0 < ρ) :
    ∑' n : ℤ, ((g ((n : ℝ) / ρ) : ℝ) : ℂ) * e ((n : ℝ) * β') =
      ∑ m ∈ Finset.Ioc 0 ⌊ρ⌋₊, ((g ((m : ℝ) / ρ) : ℝ) : ℂ) * e ((m : ℝ) * β') := by
  rw [tsum_eq_sum (s := (Finset.Ioc 0 ⌊ρ⌋₊).map Nat.castEmbedding), Finset.sum_map]
  · rfl
  intro n hn
  rcases le_or_gt n 0 with h | h
  · have : (n : ℝ) / ρ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) hρ.le
    rw [h0 _ this]
    simp
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h.le
    have hm : ¬ (m ∈ Finset.Ioc 0 ⌊ρ⌋₊) := by
      intro hm
      exact hn (Finset.mem_map.mpr ⟨m, hm, rfl⟩)
    rw [Finset.mem_Ioc, not_and_or] at hm
    rcases hm with hm | hm
    · exact absurd (by exact_mod_cast h) hm
    · rw [not_le] at hm
      have : ρ < (m : ℝ) := by
        have := Nat.lt_floor_add_one ρ
        have h2 : ((⌊ρ⌋₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
        push_cast at h2
        linarith
      have h3 : 1 ≤ ((m : ℤ) : ℝ) / ρ := by
        rw [le_div_iff₀ hρ, one_mul]
        push_cast
        linarith
      rw [h1 _ h3]
      simp

/-- **One Poisson summation**: `∑_{0<n≤ρ} g(n/ρ)e(nβ') = ∑_{k ∈ ℤ} ρĝ(ρ(k − β'))`. -/
theorem poisson_one (g : ℝ → ℝ) (hg : Continuous g) (h0 : ∀ t, t ≤ 0 → g t = 0)
    (h1 : ∀ t, 1 ≤ t → g t = 0) (C : ℝ) (hC : ∀ u : ℝ, ‖gHat g u‖ * (2 * Real.pi * u) ^ 2 ≤ C)
    (ρ β' : ℝ) (hρ : 0 < ρ) :
    HasSum (fun k : ℤ => (ρ : ℂ) * gHat g (ρ * ((k : ℝ) - β')))
      (∑ m ∈ Finset.Ioc 0 ⌊ρ⌋₊, ((g ((m : ℝ) / ρ) : ℝ) : ℂ) * e ((m : ℝ) * β')) := by
  set F : ℝ → ℂ := fun t => ((g (t / ρ) : ℝ) : ℂ) * e (t * β') with hF
  have hEc : Continuous fun t : ℝ => e (t * β') := by
    unfold e
    fun_prop
  have hc : Continuous F :=
    (Complex.continuous_ofReal.comp (hg.comp (continuous_id.div_const ρ))).mul hEc
  have hzero : F =ᶠ[cocompact ℝ] fun _ => (0 : ℂ) := by
    rw [EventuallyEq, Filter.eventually_iff, Filter.mem_cocompact]
    refine ⟨Icc 0 ρ, isCompact_Icc, fun t ht => ?_⟩
    rw [mem_compl_iff, mem_Icc, not_and_or, not_le, not_le] at ht
    show ((g (t / ρ) : ℝ) : ℂ) * e (t * β') = 0
    rcases ht with h | h
    · rw [h0 _ (div_nonpos_of_nonpos_of_nonneg h.le hρ.le)]; simp
    · rw [h1 _ (by rw [le_div_iff₀ hρ, one_mul]; exact h.le)]; simp
  have hf : F =O[cocompact ℝ] fun x : ℝ => |x| ^ (-(2 : ℝ)) :=
    hzero.trans_isBigO (Asymptotics.isBigO_zero _ _)
  have hpi := Real.pi_pos
  have hbound : ∀ᶠ n : ℤ in cofinite, ‖𝓕 F n‖ ≤
      C / (4 * Real.pi ^ 2 * ρ) * (1 / |(n : ℝ) + -β'| ^ (2 : ℝ)) := by
    have hfin : {n : ℤ | (n : ℝ) = β'}.Finite := by
      refine Set.Subsingleton.finite fun a ha b hb => ?_
      have : (a : ℝ) = b := by rw [mem_setOf_eq] at ha hb; rw [ha, hb]
      exact_mod_cast this
    rw [Filter.eventually_cofinite]
    refine hfin.subset fun n hn => ?_
    rw [mem_setOf_eq] at hn ⊢
    by_contra hne
    apply hn
    have hne' : (n : ℝ) - β' ≠ 0 := sub_ne_zero.mpr hne
    rw [hF, fourier_F g ρ β' hρ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ, Real.rpow_two, sq_abs, ← sub_eq_add_neg]
    have hpos : 0 < (2 * Real.pi * (ρ * ((n : ℝ) - β'))) ^ 2 := by positivity
    have hH := hC (ρ * ((n : ℝ) - β'))
    rw [← le_div_iff₀ hpos] at hH
    calc ρ * ‖gHat g (ρ * ((n : ℝ) - β'))‖
        ≤ ρ * (C / (2 * Real.pi * (ρ * ((n : ℝ) - β'))) ^ 2) :=
          mul_le_mul_of_nonneg_left hH hρ.le
      _ = C / (4 * Real.pi ^ 2 * ρ) * (1 / ((n : ℝ) - β') ^ 2) := by
          field_simp
          ring
  have hsum : Summable fun n : ℤ => 𝓕 F n :=
    Summable.of_norm_bounded_eventually
      (((Real.summable_one_div_int_add_rpow (-β') 2).mpr (by norm_num)).mul_left _) hbound
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc (by norm_num : (1 : ℝ) < 2)
    hf hsum 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at hP
  have hF' : ∀ n : ℤ, F n = ((g ((n : ℝ) / ρ) : ℝ) : ℂ) * e ((n : ℝ) * β') := fun n => rfl
  simp_rw [hF'] at hP
  rw [tsum_F g h0 h1 ρ β' hρ] at hP
  have hfun : (fun n : ℤ => 𝓕 F n) = fun k : ℤ => (ρ : ℂ) * gHat g (ρ * ((k : ℝ) - β')) :=
    funext fun n => fourier_F g ρ β' hρ n
  rw [hP, show (∑' n : ℤ, 𝓕 F n) = ∑' k : ℤ, (ρ : ℂ) * gHat g (ρ * ((k : ℝ) - β')) from
    congrArg tsum hfun]
  exact (hfun ▸ hsum).hasSum

/-- `f(m) = (1 − (−1)^m)/2` for the odd indicator. -/
theorem fOdd_half (m : ℕ) : ((MT.fOdd m : ℝ) : ℂ) = (1 - (-1 : ℂ) ^ m) / 2 := by
  rw [MT.fOdd_apply]
  rcases Nat.even_or_odd m with h | h
  · rw [if_neg (by rw [Nat.even_iff] at h; omega), h.neg_one_pow]
    norm_num
  · rw [if_pos (Nat.odd_iff.mp h), h.neg_one_pow]
    norm_num

/-- The even and odd integers are complementary. -/
theorem isCompl_even_odd :
    IsCompl (range fun k : ℤ => 2 * k) (range fun k : ℤ => 2 * k + 1) := by
  constructor
  · rw [Set.disjoint_iff]
    rintro _ ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    simp only at hb
    omega
  · rw [codisjoint_iff_le_sup]
    intro n _
    rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨k, rfl⟩

/-- **Odd-`m` Poisson summation, PROVED**:
`∑_{0<m≤ρ} f(m)g(m/ρ)e(mβ) = ∑_{j ∈ ℤ} (ρ/2)(−1)^j ĝ(ρ(j/2 − β))`. -/
theorem poisson_odd (g : ℝ → ℝ) (hg : Continuous g) (h0 : ∀ t, t ≤ 0 → g t = 0)
    (h1 : ∀ t, 1 ≤ t → g t = 0) (C : ℝ) (hC : ∀ u : ℝ, ‖gHat g u‖ * (2 * Real.pi * u) ^ 2 ≤ C)
    (ρ β : ℝ) (hρ : 0 < ρ) :
    HasSum (fun j : ℤ => ((ρ / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ j * gHat g (ρ * ((j : ℝ) / 2 - β)))
      (∑ m ∈ Finset.Ioc 0 ⌊ρ⌋₊,
        ((MT.fOdd m : ℝ) : ℂ) * (((g ((m : ℝ) / ρ) : ℝ) : ℂ) * e ((m : ℝ) * β))) := by
  have A := (poisson_one g hg h0 h1 C hC ρ β hρ).mul_left (1 / 2 : ℂ)
  have B := (poisson_one g hg h0 h1 C hC ρ (β - 1 / 2) hρ).mul_left (-(1 / 2) : ℂ)
  set f : ℤ → ℂ := fun j => ((ρ / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ j * gHat g (ρ * ((j : ℝ) / 2 - β))
  have he : HasSum (f ∘ fun k : ℤ => 2 * k) ((1 / 2 : ℂ) *
      ∑ m ∈ Finset.Ioc 0 ⌊ρ⌋₊, ((g ((m : ℝ) / ρ) : ℝ) : ℂ) * e ((m : ℝ) * β)) := by
    have hfun : (f ∘ fun k : ℤ => 2 * k) =
        fun i : ℤ => (1 / 2 : ℂ) * ((ρ : ℂ) * gHat g (ρ * ((i : ℝ) - β))) := by
      funext k
      simp only [Function.comp, f]
      have e1 : (((2 * k : ℤ) : ℝ) / 2 - β) = (k : ℝ) - β := by push_cast; ring
      rw [e1, Even.neg_one_zpow ⟨k, by ring⟩]
      push_cast
      ring
    rw [hfun]
    exact A
  have ho : HasSum (f ∘ fun k : ℤ => 2 * k + 1) (-(1 / 2 : ℂ) *
      ∑ m ∈ Finset.Ioc 0 ⌊ρ⌋₊, ((g ((m : ℝ) / ρ) : ℝ) : ℂ) * e ((m : ℝ) * (β - 1 / 2))) := by
    have hfun : (f ∘ fun k : ℤ => 2 * k + 1) =
        fun i : ℤ => (-(1 / 2) : ℂ) * ((ρ : ℂ) * gHat g (ρ * ((i : ℝ) - (β - 1 / 2)))) := by
      funext k
      simp only [Function.comp, f]
      have e1 : (((2 * k + 1 : ℤ) : ℝ) / 2 - β) = (k : ℝ) - (β - 1 / 2) := by push_cast; ring
      rw [e1, Odd.neg_one_zpow ⟨k, rfl⟩]
      push_cast
      ring
    rw [hfun]
    exact B
  have inj1 : Function.Injective fun k : ℤ => 2 * k := fun a b h => by simp only at h; omega
  have inj2 : Function.Injective fun k : ℤ => 2 * k + 1 := fun a b h => by
    simp only at h; omega
  have hall := HasSum.add_isCompl (f := f) isCompl_even_odd (inj1.hasSum_range_iff.mpr he)
      (inj2.hasSum_range_iff.mpr ho)
  convert hall using 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hE : e ((m : ℝ) * (β - 1 / 2)) = e ((m : ℝ) * β) * (-1 : ℂ) ^ m := by
    rw [← e_neg_half, e_mul_e]
    congr 1
    ring
  rw [hE, fOdd_half]
  ring

/-- `‖g(t)‖ ≤ 9` for `g = HC.wollG`. -/
theorem norm_wollG_le (t : ℝ) : ‖HC.wollG t‖ ≤ 9 := by
  unfold HC.wollG
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_sub_le (4 * e (-t / 4)) (4 * e (-t / 2))
  rw [norm_mul, norm_mul, norm_e, norm_e] at h1
  rw [norm_e]
  norm_num at h1 ⊢
  linarith

/-- `‖f̂(t)‖ ≤ 48` for `f̂ = HC.cameloFHat`. -/
theorem norm_cameloFHat_le (t : ℝ) : ‖HC.cameloFHat t‖ ≤ 48 := by
  unfold HC.cameloFHat
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 4 : ℝ)) (b := 1)
    (C := 64) (f := fun x : ℝ => (HC.cameloF x : ℂ) * e (-(x * t))) fun x hx => by
      rw [uIoc_of_le (by norm_num)] at hx
      have hx0 : (1 / 4 : ℝ) < x := hx.1
      have hsq : (1 / 16 : ℝ) ≤ x ^ 2 := by nlinarith
      have hb : 4 / x ^ 2 ≤ 64 := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
      unfold HC.cameloF
      split_ifs
      · rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4),
          abs_of_pos (by positivity)]
        exact hb
      · rw [abs_of_pos (by positivity)]
        exact hb
      · norm_num
  norm_num at h
  linarith

/-- **`|η̂₂(u)|(2πu)² ≤ 84`, PROVED** (from `EtaHatIBP`; the crude constant Poisson needs). -/
theorem etaHat_le (u : ℝ) : ‖gHat HW.eta2 u‖ * (2 * Real.pi * u) ^ 2 ≤ 84 := by
  have e := congrArg norm (etaHatIBP_holds u)
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at e
  rw [mul_comm]
  change (2 * Real.pi * u) ^ 2 * ‖etaHat u‖ ≤ 84
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [h4]
  linarith [norm_wollG_le u, norm_cameloFHat_le u]

/-- **`MPTC.PoissonOdd`, PROVED.** -/
theorem poissonOdd_holds : PoissonOdd := by
  intro x γ hx d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hP := poisson_odd HW.eta2 MPT.eta2_cont (fun t ht => MPT.eta2_le_quarter (by linarith))
    (fun t ht => HW.eta2_of_one_le ht) 84 etaHat_le (x / d) (d * γ) (by positivity)
  have hv : tmo x γ d = ∑ m ∈ Finset.Ioc 0 ⌊x / d⌋₊,
      ((MT.fOdd m : ℝ) : ℂ) *
        (((HW.eta2 ((m : ℝ) / (x / d)) : ℝ) : ℂ) * e ((m : ℝ) * (d * γ))) := by
    unfold tmo
    rw [Nat.floor_div_natCast]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold MT.wt
    congr 3
    · push_cast
      field_simp
    · push_cast
      ring
  rw [hv]
  exact hP

/-- **`MPT.TrompaisC` from `CameloSup` alone, PROVED** (Poisson and the IBP identity proved). -/
theorem trompaisC_of_sup (hS : CameloSup) : MPT.TrompaisC :=
  trompaisC_of_camelo poissonOdd_holds etaHatIBP_holds hS

/-- **`MPB2.TrompaisEta2` from `CameloSup` alone, PROVED.** -/
theorem trompaisEta2_of_sup (hS : CameloSup) : TrompaisEta2 :=
  MPT.trompaisEta2_of (trompaisC_of_sup hS)

end Principia.Common.TernaryGoldbach.MPTP
