/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfMajHaus

set_option autoImplicit false

/-!
# Partial summation over the zeros — `HM.AbelZeros` PROVED

`abelZeros_holds : HM.AbelZeros`: given the zero count `ZeroCount` (`N(T,χ) = M(T) + O*(g(T))`,
`M(T) = (T/π)log(qT/2πe)`, `g(T) = ½log qT + 17.7`, two-sided, with multiplicity), for `F ∈ C¹[1,T]`
with `F ≥ 0` and every primitive `χ`,
`∑_{1<|γ|≤T} F(|γ|) ≤ ∫_1^T F(t)(1/π)log(qt/2π)dt + F(T)g(T) + F(1)g(1) + ∫_1^T |F'|g`.

## The proof

1. **Finitely many zeros** (`zeros_finite`): `N(T) < ∞`, and every zero in `1 < |Im| ≤ T` carries
   multiplicity `≥ 1`, so the zero sum is a finite sum `∑_{s ∈ S} m_s F(|Im s|)`
   (`ENNReal.finite_const_le_of_tsum_ne_top`), and `N(u) = N(1) + ∑_{s∈S} m_s 1[|Im s| ≤ u]` on
   `[1, T]` (`zcount_split`).
2. **Abel summation for a finite family** (`abel_finite`, no zeros in it): `F(x) = F(T) − ∫_1^T
   1[x ≤ u]F'(u)du`, summed: `∑ m F(x) = F(T)(N(T) − N(1)) − ∫_1^T F'(N − N(1))`; integration by
   parts against `M` (`∫FM' = F(T)M(T) − F(1)M(1) − ∫F'M`) leaves `∫FM' + F(T)E(T) − F(1)E(1) −
   ∫F'E`, `E = N − M`, `|E| ≤ g`.
-/

namespace Principia.Common.TernaryGoldbach.HM

open MeasureTheory Set
open scoped ENNReal

/-! ## (1) Abel summation for a finite weighted family of points in `(1, T]` -/

/-- **Abel summation**: for points `x_i ∈ (1, T]` with weights `m_i ≥ 0`, a counting function
`N(u) = N₁ + ∑ m_i 1[x_i ≤ u]` on `[1, T]` within `g` of a `C¹` main term `M`, and `F ∈ C¹[1,T]`,
`F ≥ 0`: `∑ m_i F(x_i) ≤ ∫_1^T FM' + F(T)g(T) + F(1)g(1) + ∫_1^T |F'|g`. -/
theorem abel_finite {ι : Type*} (S : Finset ι) (x m : ι → ℝ) {T : ℝ} (hT : 1 ≤ T)
    (hx : ∀ i ∈ S, 1 < x i ∧ x i ≤ T) {F F' N M M' g : ℝ → ℝ} (N1 : ℝ)
    (hd : ∀ t ∈ Icc 1 T, HasDerivAt F (F' t) t) (hc : ContinuousOn F' (Icc 1 T))
    (hF0 : ∀ t ∈ Icc 1 T, 0 ≤ F t)
    (hN : ∀ u ∈ Icc 1 T, N u = N1 + ∑ i ∈ S, m i * (if x i ≤ u then 1 else 0))
    (hMd : ∀ t ∈ Icc 1 T, HasDerivAt M (M' t) t) (hMc : ContinuousOn M' (Icc 1 T))
    (hE : ∀ u ∈ Icc 1 T, |N u - M u| ≤ g u) (hgc : ContinuousOn g (Icc 1 T)) :
    ∑ i ∈ S, m i * F (x i) ≤ (∫ t in (1 : ℝ)..T, F t * M' t) + F T * g T + F 1 * g 1 +
      ∫ t in (1 : ℝ)..T, |F' t| * g t := by
  have hu : uIcc (1 : ℝ) T = Icc 1 T := uIcc_of_le hT
  have hI : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc 1 T) → IntervalIntegrable f volume 1 T :=
    fun hf => (hu ▸ hf).intervalIntegrable
  have hFc : ContinuousOn F (Icc 1 T) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hMcont : ContinuousOn M (Icc 1 T) := fun t ht => (hMd t ht).continuousAt.continuousWithinAt
  have hT1 : (1 : ℝ) ∈ Icc 1 T := ⟨le_rfl, hT⟩
  have hTT : T ∈ Icc 1 T := ⟨hT, le_rfl⟩
  -- the pieces `1[x_i ≤ u]F'(u)`
  set P : ι → ℝ → ℝ := fun i u => (Ici (x i)).indicator F' u with hP
  have hPint : ∀ i, IntervalIntegrable (P i) volume 1 T := fun i => by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact ((hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self).indicator measurableSet_Ici
  have hPval : ∀ i ∈ S, ∫ u in (1 : ℝ)..T, P i u = F T - F (x i) := fun i hi => by
    obtain ⟨h1, h2⟩ := hx i hi
    rw [intervalIntegral.integral_of_le hT, setIntegral_indicator measurableSet_Ici]
    have hset : Ioc 1 T ∩ Ici (x i) = Icc (x i) T := by
      ext u
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨_, hb⟩, hc'⟩
        exact ⟨hc', hb⟩
      · rintro ⟨ha, hb⟩
        exact ⟨⟨by linarith, hb⟩, ha⟩
    rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h2]
    have hsub : uIcc (x i) T ⊆ uIcc 1 T := by
      rw [uIcc_of_le h2, hu]
      exact Icc_subset_Icc h1.le le_rfl
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hd t (hu ▸ hsub ht)) ((hI hc).mono_set hsub)
  -- `∑ m F(x) = F(T)∑m − ∫ ∑ m P`
  have hsum : ∑ i ∈ S, m i * F (x i) =
      F T * ∑ i ∈ S, m i - ∫ u in (1 : ℝ)..T, ∑ i ∈ S, m i * P i u := by
    rw [intervalIntegral.integral_finsetSum fun i _ => (hPint i).const_mul (m i)]
    simp_rw [intervalIntegral.integral_const_mul]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hPval i hi]
    ring
  have hstep : ∀ u ∈ uIcc (1 : ℝ) T, ∑ i ∈ S, m i * P i u = F' u * (N u - N1) := fun u hu' => by
    rw [hu] at hu'
    rw [hN u hu', add_sub_cancel_left, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hP, Set.indicator_apply, Set.mem_Ici]
    split_ifs <;> ring
  have hNT : N T - N1 = ∑ i ∈ S, m i := by
    rw [hN T hTT, add_sub_cancel_left]
    exact Finset.sum_congr rfl fun i hi => by rw [if_pos (hx i hi).2, mul_one]
  have hN1 : N 1 = N1 := by
    rw [hN 1 hT1, Finset.sum_eq_zero fun i hi => by
      rw [if_neg (not_le.mpr (hx i hi).1), mul_zero], add_zero]
  -- integrability
  have hSint : IntervalIntegrable (fun u => ∑ i ∈ S, m i * P i u) volume 1 T := by
    have := IntervalIntegrable.sum S fun i _ => (hPint i).const_mul (m i)
    exact this.congr fun u _ => Finset.sum_apply u S fun i u => m i * P i u
  have hFNint : IntervalIntegrable (fun u => F' u * (N u - N1)) volume 1 T :=
    hSint.congr fun u hu' => hstep u (uIoc_subset_uIcc hu')
  have hFMint : IntervalIntegrable (fun u => F' u * (M u - N1)) volume 1 T :=
    hI (hc.mul (hMcont.sub continuousOn_const))
  have hFEint : IntervalIntegrable (fun u => F' u * (N u - M u)) volume 1 T :=
    (hFNint.sub hFMint).congr fun u _ => by ring
  have hSeq : ∫ u in (1 : ℝ)..T, ∑ i ∈ S, m i * P i u =
      ∫ u in (1 : ℝ)..T, F' u * (N u - N1) := intervalIntegral.integral_congr hstep
  -- split `N − N₁ = (N − M) + (M − N₁)`
  have hsplit : ∫ u in (1 : ℝ)..T, F' u * (N u - N1) =
      (∫ u in (1 : ℝ)..T, F' u * (N u - M u)) + ∫ u in (1 : ℝ)..T, F' u * (M u - N1) := by
    rw [← intervalIntegral.integral_add hFEint hFMint]
    exact intervalIntegral.integral_congr fun u _ => by ring
  have hF'int : ∫ u in (1 : ℝ)..T, F' u = F T - F 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hu ▸ ht)) (hI hc)
  have hMN : ∫ u in (1 : ℝ)..T, F' u * (M u - N1) =
      (∫ u in (1 : ℝ)..T, F' u * M u) - N1 * (F T - F 1) := by
    have i1 : IntervalIntegrable (fun u => F' u * M u) volume 1 T := hI (hc.mul hMcont)
    have i2 : IntervalIntegrable (fun u => N1 * F' u) volume 1 T := (hI hc).const_mul N1
    calc ∫ u in (1 : ℝ)..T, F' u * (M u - N1)
        = ∫ u in (1 : ℝ)..T, (F' u * M u - N1 * F' u) :=
          intervalIntegral.integral_congr fun u _ => by ring
      _ = (∫ u in (1 : ℝ)..T, F' u * M u) - ∫ u in (1 : ℝ)..T, N1 * F' u :=
          intervalIntegral.integral_sub i1 i2
      _ = (∫ u in (1 : ℝ)..T, F' u * M u) - N1 * (F T - F 1) := by
          rw [intervalIntegral.integral_const_mul, hF'int]
  -- integration by parts against `M`
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 1) (b := T) (u := F)
    (v := M) (u' := F') (v' := M') (fun t ht => hd t (hu ▸ ht)) (fun t ht => hMd t (hu ▸ ht))
    (hI hc) (hI hMc)
  -- the error terms
  have hB1 : F T * (N T - M T) ≤ F T * g T :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hE T hTT)) (hF0 T hTT)
  have hB2 : -(F 1 * (N 1 - M 1)) ≤ F 1 * g 1 := by
    have := mul_le_mul_of_nonneg_left ((neg_le_abs _).trans (hE 1 hT1)) (hF0 1 hT1)
    linarith
  have hB3 : -(∫ u in (1 : ℝ)..T, F' u * (N u - M u)) ≤ ∫ u in (1 : ℝ)..T, |F' u| * g u := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_mono_on hT hFEint.neg (hI (hc.abs.mul hgc)) fun u hu' => ?_
    have h1 : -(F' u * (N u - M u)) ≤ |F' u| * |N u - M u| := by
      rw [← abs_mul]
      exact neg_le_abs _
    exact h1.trans (mul_le_mul_of_nonneg_left (hE u hu') (abs_nonneg _))
  rw [hsum, hSeq, hsplit, hMN, ← hNT]
  rw [hN1] at hB2
  linarith

/-! ## (2) The zeros in `1 < |Im| ≤ T` are finitely many -/

/-- **The zero sum over `1 < |Im| ≤ T` as a finite sum**, with the counting function on `[1, T]`
expressed through the same finite family. -/
theorem zeros_finite (hZC : ZeroCount) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) :
    ∃ (S : Finset ℂ) (mr : ℂ → ℝ), (∀ s ∈ S, 1 < |s.im| ∧ |s.im| ≤ T) ∧ (∀ s, 0 ≤ mr s) ∧
      (∀ w : ℂ → ℝ≥0∞, zsum χ {s | 1 < |s.im| ∧ |s.im| ≤ T} w =
        ∑ s ∈ S, ENNReal.ofReal (mr s) * w s) ∧
      ∀ u ∈ Icc 1 T, (zcount χ u).toReal =
        (zcount χ 1).toReal + ∑ s ∈ S, mr s * (if |s.im| ≤ u then 1 else 0) := by
  set H : Set ℂ := {s | 1 < |s.im| ∧ |s.im| ≤ T} with hH
  set c : ℂ → ℝ≥0∞ := (zeroSet χ ∩ H).indicator (zmult χ) with hc
  have hcw : ∀ (A : Set ℂ), A ⊆ H → ∀ w : ℂ → ℝ≥0∞,
      zsum χ A w = ∑' s, c s * A.indicator w s := by
    intro A hA w
    rw [zsum_eq_tsum]
    congr 1
    funext s
    by_cases hz : s ∈ zeroSet χ
    · by_cases hsA : s ∈ A
      · have h1 : s ∈ zeroSet χ ∩ A := ⟨hz, hsA⟩
        have h2 : s ∈ zeroSet χ ∩ H := ⟨hz, hA hsA⟩
        simp only [hc, Set.indicator_of_mem h1, Set.indicator_of_mem h2,
          Set.indicator_of_mem hsA]
      · have h1 : s ∉ zeroSet χ ∩ A := fun h => hsA h.2
        simp only [Set.indicator_of_notMem h1, Set.indicator_of_notMem hsA, mul_zero]
    · have h1 : s ∉ zeroSet χ ∩ A := fun h => hz h.1
      have h2 : s ∉ zeroSet χ ∩ H := fun h => hz h.1
      simp only [hc, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, zero_mul]
  have hcz : ∀ s, s ∉ zeroSet χ ∩ H → c s = 0 := fun s h => by
    rw [hc, Set.indicator_of_notMem h]
  have hcm : ∀ s, s ∈ zeroSet χ ∩ H → c s = zmult χ s := fun s h => by
    rw [hc, Set.indicator_of_mem h]
  have hctop : ∀ s, c s ≠ ⊤ := fun s => by
    by_cases h : s ∈ zeroSet χ ∩ H
    · rw [hcm s h]
      exact ENNReal.natCast_ne_top _
    · rw [hcz s h]
      exact ENNReal.zero_ne_top
  have hsum_top : ∑' s, c s ≠ ⊤ := by
    have h1 : zsum χ H (fun _ => 1) ≤ zcount χ T :=
      zsum_mono_set χ (fun s hs => hs.2) (fun _ => (1 : ℝ≥0∞))
    have h2 := hcw H le_rfl (fun _ => 1)
    have h3 : ∑' s, c s = ∑' s, c s * H.indicator (fun _ => (1 : ℝ≥0∞)) s := by
      congr 1
      funext s
      by_cases hs : s ∈ H
      · rw [Set.indicator_of_mem hs, mul_one]
      · rw [Set.indicator_of_notMem hs, mul_zero, hcz s fun h => hs h.2]
    rw [h3, ← h2]
    exact ne_top_of_le_ne_top (hZC q χ hχ T hT).1 h1
  have hfin : {s | c s ≠ 0}.Finite := by
    refine (ENNReal.finite_const_le_of_tsum_ne_top hsum_top one_ne_zero).subset fun s hs => ?_
    simp only [mem_setOf_eq] at hs ⊢
    by_cases h : s ∈ zeroSet χ ∩ H
    · rw [hcm s h] at hs ⊢
      unfold zmult at hs ⊢
      exact Nat.one_le_cast.mpr (Nat.pos_of_ne_zero fun h0 => hs (by rw [h0, Nat.cast_zero]))
    · exact absurd (hcz s h) hs
  set S := hfin.toFinset with hS
  have hmem : ∀ s ∈ S, s ∈ zeroSet χ ∩ H := fun s hs => by
    rw [hS, Set.Finite.mem_toFinset] at hs
    by_contra h
    exact hs (hcz s h)
  have htsum : ∀ w : ℂ → ℝ≥0∞, ∑' s, c s * w s = ∑ s ∈ S, c s * w s := fun w =>
    tsum_eq_sum fun s hs => by
      rw [hS, Set.Finite.mem_toFinset] at hs
      simp only [mem_setOf_eq, not_not] at hs
      rw [hs, zero_mul]
  refine ⟨S, fun s => (c s).toReal, fun s hs => (hmem s hs).2, fun s => ENNReal.toReal_nonneg,
    fun w => ?_, fun u hu => ?_⟩
  · rw [hcw H le_rfl w, htsum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [ENNReal.ofReal_toReal (hctop s), Set.indicator_of_mem (hmem s hs).2]
  · have hsplit := zcount_split χ hu.1
    have hsub : {s : ℂ | 1 < |s.im| ∧ |s.im| ≤ u} ⊆ H := fun s hs => ⟨hs.1, hs.2.trans hu.2⟩
    have h1 := hcw _ hsub (fun _ => 1)
    rw [htsum] at h1
    have hind : ∀ s ∈ S, {s : ℂ | 1 < |s.im| ∧ |s.im| ≤ u}.indicator (fun _ => (1 : ℝ≥0∞)) s =
        ENNReal.ofReal (if |s.im| ≤ u then 1 else 0) := fun s hs => by
      by_cases h : |s.im| ≤ u
      · rw [Set.indicator_of_mem (show s ∈ {s : ℂ | 1 < |s.im| ∧ |s.im| ≤ u} from
          ⟨(hmem s hs).2.1, h⟩), if_pos h, ENNReal.ofReal_one]
      · rw [Set.indicator_of_notMem (show s ∉ {s : ℂ | 1 < |s.im| ∧ |s.im| ≤ u} from
          fun h' => h h'.2), if_neg h, ENNReal.ofReal_zero]
    rw [Finset.sum_congr rfl fun s hs => by rw [hind s hs]] at h1
    have h1top : zcount χ 1 ≠ ⊤ := (hZC q χ hχ 1 le_rfl).1
    have hterm : ∀ s ∈ S, c s * ENNReal.ofReal (if |s.im| ≤ u then 1 else 0) ≠ ⊤ :=
      fun s _ => ENNReal.mul_ne_top (hctop s) ENNReal.ofReal_ne_top
    have h2top : zsum χ {s | 1 < |s.im| ∧ |s.im| ≤ u} (fun _ => 1) ≠ ⊤ := by
      rw [h1]
      exact ENNReal.sum_ne_top.mpr hterm
    rw [hsplit, ENNReal.toReal_add h1top h2top, h1, ENNReal.toReal_sum hterm]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by split_ifs <;> norm_num)]

/-! ## (3) `AbelZeros` -/

/-- `M(t) = (t/π)log(qt/2πe)` has derivative `(1/π)log(qt/2π)` for `t > 0`. -/
theorem hasDerivAt_MZ {Q t : ℝ} (hQ : 0 < Q) (ht : 0 < t) :
    HasDerivAt (fun t => t / Real.pi * Real.log (Q * t / (2 * Real.pi * Real.exp 1)))
      (Real.log (Q * t / (2 * Real.pi)) / Real.pi) t := by
  have h1 : HasDerivAt (fun t => Q * t / (2 * Real.pi * Real.exp 1))
      (Q * 1 / (2 * Real.pi * Real.exp 1)) t :=
    ((hasDerivAt_id t).const_mul Q).div_const _
  have h2 := h1.log (by positivity)
  have h3 := ((hasDerivAt_id t).div_const Real.pi).mul h2
  refine h3.congr_deriv ?_
  have hQt : Real.log (Q * t / (2 * Real.pi * Real.exp 1)) =
      Real.log (Q * t / (2 * Real.pi)) - 1 := by
    rw [← div_div, Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
  simp only [id]
  rw [hQt]
  field_simp
  ring

/-- **`AbelZeros` PROVED** (from `ZeroCount`, which is its premise). -/
theorem abelZeros_holds : AbelZeros := by
  intro hZC q _ χ hχ F F' T hT hd hc hF0
  have hq0 : (0 : ℝ) < q := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    linarith
  obtain ⟨S, mr, hS, hmr, hw, hN⟩ := zeros_finite hZC hχ hT
  rw [hw]
  have hsum : ∑ s ∈ S, ENNReal.ofReal (mr s) * ENNReal.ofReal (F |s.im|) =
      ENNReal.ofReal (∑ s ∈ S, mr s * F |s.im|) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun s hs =>
      mul_nonneg (hmr s) (hF0 _ ⟨(hS s hs).1.le, (hS s hs).2⟩)]
    exact Finset.sum_congr rfl fun s hs => (ENNReal.ofReal_mul (hmr s)).symm
  rw [hsum]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpos : ∀ t ∈ Icc (1 : ℝ) T, 0 < t := fun t ht => by linarith [ht.1]
  refine abel_finite S (fun s => |s.im|) mr hT hS (zcount χ 1).toReal hd hc hF0 hN
    (M := fun t => t / Real.pi * Real.log (q * t / (2 * Real.pi * Real.exp 1)))
    (fun t ht => hasDerivAt_MZ hq0 (hpos t ht)) ?_ ?_ ?_
  · refine ContinuousOn.div_const (ContinuousOn.log (by fun_prop) fun t ht => ?_) _
    have := hpos t ht
    positivity
  · intro u hu
    exact (hZC q χ hχ u hu.1).2
  · unfold gZ
    refine (continuousOn_const.mul (ContinuousOn.log (by fun_prop) fun t ht => ?_)).add
      continuousOn_const
    have := hpos t ht
    positivity

/-- **`lem:hausierer`, corrected, from `RealSym` alone** (`CritDeriv`, `AbelZeros` discharged). -/
theorem hausierer_of_realSym (hRS : RealSym) : Hausierer :=
  hausierer_of' abelZeros_holds hRS

end Principia.Common.TernaryGoldbach.HM
