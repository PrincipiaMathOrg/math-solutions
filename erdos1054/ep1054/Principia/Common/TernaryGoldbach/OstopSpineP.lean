/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.GorshP
import Principia.Common.TernaryGoldbach.OstopSpine

set_option autoImplicit false

/-!
# The spine of `thm:ostop` at `(c05, C)`: `OP.OstopP` from its layer-2 links

`OstopSpine.lean` composes `OL.OstopL` from its layer-2 links; here the `g`-dependent half is
regenerated for `OP.OstopP c05 C`, for EVERY `(c05, C)` with `c05, C ≥ 0`
(`scratchpad/ostopp/gen_ostopspinep.py`, counted substitution of `OstopSpine.lean`). Everything
that does not see `g` is reused from `OS` as it is: Parseval, `SplitLink`, the arcs, the weighted
Minkowski step, `PalanLink`, `level_bound`, `sum_int_sharp`, `hC`, `floor_big`, the jump, the top
algebra, `I0SLink`, `EBound2`, `JgeE`, `z1_le`, `z1_assemble`, `z2_le`.

```
 gTP_nonneg      g̃ ≥ 0 on [1000, r₁]                      (c05, C ≥ 0: OP.gYP_pos)   PROVED
 top_leP         the integer top level, from GTMonoP, TopStepP                        PROVED
 z1_boundP       Z₁ ≤ |φ|₁(x/49)(M̃ + T)                                                PROVED
 ostopP_of_open : CoeurY → MinMainP → RS62Thm15 → GYMonoP → HLeGP → Austeria → GTMonoP →
                  CoprarP → EBound2 → JgeE → TopStepP → OP.OstopP c05 C η₊ η* φ
```

The only use of the constants' values is the sign `c05, C ≥ 0` behind `gTP_nonneg` (and, through
`GSP.gorshP_of_open`, behind `gtlIntP` and M2).
-/

namespace Principia.Common.TernaryGoldbach.OSP

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction
open Principia.Common.TernaryGoldbach.OS
open Principia.Common.TernaryGoldbach.OP

/-- **`g̃ ≥ 0` on `[1000, r₁(y)]`** at `(c05, C)` (generated from `OS.gTL_nonneg`). -/
theorem gTP_nonneg (c05 C : ℝ) (hc05 : 0 ≤ c05) (hC0 : 0 ≤ C) (φ : ℝ → ℝ)
    (hφ0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ φ t) (y r : ℝ) (hy : 10 ^ 25 ≤ y) (hr : 1000 ≤ r)
    (hr1 : r ≤ MinSp.r1y y) : 0 ≤ gTP c05 C φ y r := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hr0 : 0 < r := by linarith
  have hl17 := GS.log_gt y hy
  have hK0 : 0 < 1 / MinSp.kK y := by
    unfold MinSp.kK
    have : 0 < Real.log y := by linarith
    positivity
  have hK1 : 1 / MinSp.kK y ≤ 1 := by
    unfold MinSp.kK
    rw [div_le_one (by linarith)]
    linarith
  have hr1000 : 1000 / r ≤ 1 := by
    rw [div_le_one hr0]
    exact hr
  have hw1 : max (1 / MinSp.kK y) (1000 / r) ≤ 1 := max_le hK1 hr1000
  unfold gTP
  refine div_nonneg ?_ (MajSp.l1_nonneg φ)
  refine add_nonneg (add_nonneg ?_ ?_) (mul_nonneg (by norm_num) ?_)
  · refine intervalIntegral.integral_nonneg hw1 fun w hw => ?_
    have hw0 : 0 < w := lt_of_lt_of_le (lt_of_lt_of_le hK0 (le_max_left _ _)) hw.1
    have hY : 3.4e23 ≤ w * y := GS.scale_ge y w hy (le_trans (le_max_left _ _) hw.1)
    have h1000 : 1000 ≤ w * r := by
      have h := mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) hw.1) hr0.le
      rw [div_mul_cancel₀ _ hr0.ne'] at h
      exact h
    have harg := GS.arg_le_r1y y w r hy0 hw0 hr1
    rw [min_eq_left hw.2] at harg
    exact mul_nonneg (gYP_pos c05 C (w * y) (w * r) hc05 hC0 (by positivity) (by linarith)
      (le_trans harg (GS.r1y_le_third _ hY))).le (hφ0 w hw0.le)
  · refine setIntegral_nonneg measurableSet_Ioi fun w (hw : 1 < w) => ?_
    have hY : 3.4e23 ≤ w * y := by nlinarith
    have harg := GS.arg_le_r1y y w r hy0 (by linarith) hr1
    rw [min_eq_right hw.le, one_mul] at harg
    exact mul_nonneg (gYP_pos c05 C (w * y) r hc05 hC0 (by positivity) (by linarith)
      (le_trans harg (GS.r1y_le_third _ hY))).le (hφ0 w (by linarith))
  · exact intervalIntegral.integral_nonneg (le_max_left _ _) fun w _ => abs_nonneg _

/-- `g̃` at the level `r : ℕ` (generated from `OS.gN`). -/
noncomputable def gNP (c05 C : ℝ) (φ : ℝ → ℝ) (x : ℝ) (r : ℕ) : ℝ :=
  gTP c05 C φ (x / 49) r

/-- **Link [TopStepP]** — `√⌊r₁⌋·g̃(⌊r₁⌋) ≤ √r₁·g̃(r₁)` at `(c05, C)` (generated from
`OS.TopStepL`). PROVED at every `c05 ≥ 0`, `0 ≤ C ≤ 45.7575` (`MTOP.topStepP_helf`). -/
def TopStepP (c05 C : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ y : ℝ, 10 ^ 25 ≤ y →
    Real.sqrt (⌊MinSp.r1y y⌋₊ : ℝ) * gTP c05 C φ y ⌊MinSp.r1y y⌋₊ ≤
      Real.sqrt (MinSp.r1y y) * gTP c05 C φ y (MinSp.r1y y)

/-- **The top of `prop:palan`** at `(c05, C)` (generated from `OS.top_le`; `g̃` enters only as a
function: no constant is evaluated). -/
theorem top_leP (c05 C : ℝ) (φ : ℝ → ℝ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x)
    (hanti : AntitoneOn (gTP c05 C φ (x / 49)) (Set.Icc 150000 (MinSp.r1y (x / 49))))
    (hg1 : 0 ≤ gTP c05 C φ (x / 49) (MinSp.r1y (x / 49)))
    (hts : Real.sqrt (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) * gTP c05 C φ (x / 49) ⌊MinSp.r1y (x / 49)⌋₊ ≤
      Real.sqrt (MinSp.r1y (x / 49)) * gTP c05 C φ (x / 49) (MinSp.r1y (x / 49))) :
    ∑ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊, (hC x (r + 1) - hC x r) * gNP c05 C φ x (r + 1) +
        (1 - hC x ⌊MinSp.r1y (x / 49)⌋₊) * gNP c05 C φ x ⌊MinSp.r1y (x / 49)⌋₊ ≤
      2 / (Real.log x - 2 * 1.306476) * intGTP c05 C φ (x / 49) +
        OC.coefC x * gTP c05 C φ (x / 49) (MinSp.r1y (x / 49)) := by
  have hx0 := MinSp.x_pos x hx
  have hy0 : 0 < x / 49 := div_pos hx0 (by norm_num)
  have hDh := dh_pos x hx
  have hRb := floor_big x hx
  have hr10 := r1y_nonneg (x / 49) hy0.le
  have hRr1 : (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) ≤ MinSp.r1y (x / 49) := Nat.floor_le hr10
  have hr1R : MinSp.r1y (x / 49) < (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hR150 : (150001 : ℝ) ≤ (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by nlinarith
  have hRn : 150000 ≤ ⌊MinSp.r1y (x / 49)⌋₊ := by
    have h : (150000 : ℝ) ≤ (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by linarith
    exact_mod_cast h
  have e150 : ((150000 : ℕ) : ℝ) = 150000 := by norm_num
  have hantiR : AntitoneOn (gTP c05 C φ (x / 49))
      (Set.Icc ((150000 : ℕ) : ℝ) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ)) := by
    rw [e150]
    exact hanti.mono (Set.Icc_subset_Icc le_rfl hRr1)
  have hgR1 : gTP c05 C φ (x / 49) (MinSp.r1y (x / 49)) ≤
      gTP c05 C φ (x / 49) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) :=
    hanti ⟨by linarith, hRr1⟩ ⟨by linarith, le_rfl⟩ hRr1
  have hgR : 0 ≤ gTP c05 C φ (x / 49) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := le_trans hg1 hgR1
  have hsh := sum_int_sharp 150000 ⌊MinSp.r1y (x / 49)⌋₊ (by norm_num) hRn
    (gTP c05 C φ (x / 49)) hantiR
  have hext : ∫ u in ((150000 : ℕ) : ℝ)..(⌊MinSp.r1y (x / 49)⌋₊ : ℝ),
      gTP c05 C φ (x / 49) u / u ≤
      intGTP c05 C φ (x / 49) := by
    rw [e150]
    unfold intGTP
    have hint1 : IntervalIntegrable (fun u => gTP c05 C φ (x / 49) u / u) volume 150000
        (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) :=
      gdiv_int _ _ _ (by norm_num) (by linarith) (hanti.mono (Set.Icc_subset_Icc le_rfl hRr1))
    have hint2 : IntervalIntegrable (fun u => gTP c05 C φ (x / 49) u / u) volume
        (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) (MinSp.r1y (x / 49)) :=
      gdiv_int _ _ _ (by linarith) hRr1 (hanti.mono (Set.Icc_subset_Icc (by linarith) le_rfl))
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    have hnn : 0 ≤ ∫ u in (⌊MinSp.r1y (x / 49)⌋₊ : ℝ)..(MinSp.r1y (x / 49)),
        gTP c05 C φ (x / 49) u / u := by
      refine intervalIntegral.integral_nonneg hRr1 fun u hu => ?_
      have hu0 : 0 < u := by linarith [hu.1]
      exact div_nonneg (le_trans hg1 (hanti ⟨by linarith [hu.1], hu.2⟩ ⟨by linarith, le_rfl⟩
        hu.2)) hu0.le
    linarith
  have hsum : ∑ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊,
      (hC x (r + 1) - hC x r) * gNP c05 C φ x (r + 1) =
      (∑ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊,
        (Real.log ((r : ℝ) + 2) - Real.log ((r : ℝ) + 1)) * gTP c05 C φ (x / 49) ((r : ℝ) + 1)) /
        (Real.log (Real.sqrt x) - 1.306476) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold hC gNP
    have e1 : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
    have e2 : (r : ℝ) + 1 + 1 = (r : ℝ) + 2 := by ring
    rw [e1, e2]
    field_simp
    ring
  have hj : 1 - hC x ⌊MinSp.r1y (x / 49)⌋₊ ≤ OC.coefC x := by
    unfold hC
    exact jump_le_coefC_of x _ hx hr1R.le
  have hstep : 2 * (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) *
      (gTP c05 C φ (x / 49) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) -
        gTP c05 C φ (x / 49) (MinSp.r1y (x / 49))) ≤
      gTP c05 C φ (x / 49) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by
    have hs0 : 0 < Real.sqrt (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hst : Real.sqrt (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) ≤ Real.sqrt (MinSp.r1y (x / 49)) :=
      Real.sqrt_le_sqrt hRr1
    have h1 : Real.sqrt (MinSp.r1y (x / 49)) ^ 2 -
        Real.sqrt (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) ^ 2 ≤ 1 := by
      rw [Real.sq_sqrt hr10, Real.sq_sqrt (by linarith)]
      linarith
    have h := top_step_alg _ _ _ _ hs0 hst h1 hgR hts
    rwa [Real.sq_sqrt (by linarith)] at h
  have hTel := tel_bound 150000 ⌊MinSp.r1y (x / 49)⌋₊ (by norm_num) (by omega)
  have hRb' : (((150000 : ℕ) : ℝ) + 1) * (7 * (Real.log (Real.sqrt x) - 1.306476) / 30 + 1) ≤
      (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by
    rw [e150]
    norm_num
    linarith
  have hD2 : 2 / (Real.log x - 2 * 1.306476) * intGTP c05 C φ (x / 49) =
      intGTP c05 C φ (x / 49) / (Real.log (Real.sqrt x) - 1.306476) := by
    rw [Real.log_sqrt hx0.le]
    have hD : Real.log x - 2 * 1.306476 ≠ 0 := by
      have h := hDh
      rw [Real.log_sqrt hx0.le] at h
      intro h0
      linarith
    field_simp
  have hgN : gNP c05 C φ x ⌊MinSp.r1y (x / 49)⌋₊ =
      gTP c05 C φ (x / 49) (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := rfl
  rw [hsum, hD2, hgN]
  exact top_combine _ _ _ _ _ _ _ _ _ _ _ (by linarith) (by positivity) hsh hext hj
    (coefC_le x hx) hgR hgR1 hstep hTel hRb'

/-- **The level weight** at `(c05, C)` (generated from `OS.gG`). -/
noncomputable def gGP (c05 C : ℝ) (φ : ℝ → ℝ) (x : ℝ) (s : ℕ) : ℝ :=
  (gTP c05 C φ (x / 49) s + MinSp.cPhi3 φ (MinSp.kK (x / 49))) * MajSp.l1 φ * (x / 49)

/-- **`Z₁ ≤ |φ|₁(x/49)(M̃ + T)`** at `(c05, C)` (generated from `OS.z1_bound`). -/
theorem z1_boundP (c05 C : ℝ) (hc05 : 0 ≤ c05) (hC0 : 0 ≤ C) (ηp ηs φ b : ℝ → ℝ)
    (hpal : PalanLink) (hi0 : I0SLink) (hco : OC.CoeurY ηp) (hgo : GorshP c05 C ηs φ)
    (hgm : GTMonoP c05 C φ) (hcp : CoprarP c05 C ηs φ) (hts : TopStepP c05 C φ)
    (hsd : ∀ t : ℝ, ηs t = HW.mconv HW.eta2 φ (49 * t)) (hφ0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ φ t)
    (hφi : IntegrableOn φ (Set.Ioi 0)) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x)
    (hsum : Summable fun n => ‖aP ηp x n‖) (hE2 : s2Sq ηp x ≤ MinSp.eBig b x)
    (hEJ : MinSp.eBig b x ≤ x * MajSp.amaj ηp x) :
    ∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖OC.s1Sum ηp x α‖ ^ 2 ≤
      MajSp.l1 φ * x / 49 * (mMCP c05 C φ ηp b x + MinSp.tT φ ηp b x) := by
  have hx0 := MinSp.x_pos x hx
  have hy := MinSp.y_ge x hx
  have hy0 : 0 < x / 49 := div_pos hx0 (by norm_num)
  have hanti := hgm (x / 49) hy
  have hr10 := r1y_nonneg (x / 49) hy0.le
  have hRb := floor_big x hx
  have hDh := dh_pos x hx
  have hRr1 : (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) ≤ MinSp.r1y (x / 49) := Nat.floor_le hr10
  have hR150 : (150001 : ℝ) ≤ (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by nlinarith
  have hRn : 150000 + 1 ≤ ⌊MinSp.r1y (x / 49)⌋₊ := by exact_mod_cast hR150
  have hg1 : 0 ≤ gTP c05 C φ (x / 49) (MinSp.r1y (x / 49)) :=
    gTP_nonneg c05 C hc05 hC0 φ hφ0 _ _ hy (by linarith) le_rfl
  have e150 : ((150000 : ℕ) : ℝ) = 150000 := by norm_num
  have hga : 0 ≤ gTP c05 C φ (x / 49) ((150000 : ℕ) : ℝ) := by
    rw [e150]
    exact le_trans hg1 (hanti ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith))
  have hK0 : 0 ≤ 1 / MinSp.kK (x / 49) := by
    unfold MinSp.kK
    have := GS.log_gt (x / 49) hy
    positivity
  have hc3 := cPhi3_nonneg φ (MinSp.kK (x / 49)) hK0
  have hLy : 0 ≤ MajSp.l1 φ * (x / 49) := mul_nonneg (MajSp.l1_nonneg φ) hy0.le
  have hS0 := MinSp.sPr_nonneg ηp x
  have hGanti : ∀ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊,
      gGP c05 C φ x (r + 1) ≤ gGP c05 C φ x r := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have hr0 : (150000 : ℝ) ≤ r := by exact_mod_cast hr.1
    have hr1 : ((r + 1 : ℕ) : ℝ) ≤ (⌊MinSp.r1y (x / 49)⌋₊ : ℝ) := by exact_mod_cast hr.2
    have hrr : (r : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h := hanti ⟨hr0, by linarith⟩ ⟨by linarith, by linarith⟩ hrr
    unfold gGP
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith)
      (MajSp.l1_nonneg φ)) hy0.le
  have hlev : ∀ α ∈ Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ ≤
      gGP c05 C φ x ⌊MinSp.r1y (x / 49)⌋₊ + ∑ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊,
        (gGP c05 C φ x r - gGP c05 C φ x (r + 1)) *
          (Smooth.arcs 8 (r + 1) (x / 49)).indicator (fun _ => (1 : ℝ)) α := by
    intro α hα
    refine level_bound (fun s => Smooth.arcs 8 s (x / 49)) 150000 _ hRn
      (fun s s' _ h => arcs_mono_r 8 (by norm_num) s s' h _ hy0) (gGP c05 C φ x) hGanti _ α
      (fun s hs1 hs2 hsα => ?_) (fun hin => ?_)
    · have hs : (s : ℝ) ≤ MinSp.r1y (x / 49) :=
        le_trans (by exact_mod_cast hs2) hRr1
      exact hgo hsd hφ0 hφi x hx s hs1 hs α hsα
    · have hA0 : α ∈ OC.annA0 x := ⟨hα.1, hin, hα.2⟩
      have h := hcp hsd hφ0 hφi x hx α hA0
      unfold gGP
      rw [e150]
      exact h
  have hstep1 := z1_le ηp ηs x hx _ (gGP c05 C φ x) hsum hlev
  have hΦ : ∀ r ∈ Finset.Ico 150000 ⌊MinSp.r1y (x / 49)⌋₊,
      cumC ηp x r - jOne ηp x ≤ hC x r * MinSp.sPr ηp x - jOne ηp x := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have hrl : (r : ℝ) < MinSp.r1y (x / 49) :=
      lt_of_lt_of_le (by exact_mod_cast hr.2) hRr1
    exact sub_le_sub_right (hco x hx r hr.1 hrl) _
  have htop := top_leP c05 C φ x hx hanti hg1 (hts (x / 49) hy)
  have hJ := hi0 ηp b x hx hsum hE2 hEJ
  have hZ := z1_assemble hpal 150000 _ (by omega) (gGP c05 C φ x) (gNP c05 C φ x) (hC x)
    (fun r => cumC ηp x r - jOne ηp x) (MinSp.cPhi3 φ (MinSp.kK (x / 49))) (MajSp.l1 φ)
    (x / 49) (MinSp.sPr ηp x) (jOne ηp x) _ _ (OC.hR0C x) (MinSp.pJE ηp b x) (fun r => rfl)
    hGanti hΦ hstep1 htop (hC_r0 x) hJ hLy hS0 hga hc3
  refine le_trans hZ (le_of_eq ?_)
  unfold mMCP MinSp.tT gNP
  push_cast
  ring

/-- **`OP.OstopP c05 C η₊ η* φ` from its layer-2 links** (generated from `OS.ostopL_of_links`).
Generic in `(η₊, η*, φ)`; `c05, C ≥ 0`. -/
theorem ostopP_of_links (c05 C : ℝ) (hc05 : 0 ≤ c05) (hC0 : 0 ≤ C) (ηp ηs φ : ℝ → ℝ)
    (hpal : PalanLink) (hspl : SplitLink) (hi0 : I0SLink) (hco : OC.CoeurY ηp)
    (hgo : GorshP c05 C ηs φ) (hgm : GTMonoP c05 C φ) (hcp : CoprarP c05 C ηs φ)
    (heb : EBound2 ηp)
    (hs1 : ∀ t : ℝ, 0 ≤ t → |ηp t| ≤ 1.079955) (hs2 : ∀ t : ℝ, 0 ≤ t → |ηp t * t| ≤ 1.19073)
    (hjE : JgeE ηp) (hts : TopStepP c05 C φ) : OstopP c05 C ηp ηs φ := by
  intro hoh b hb x hx
  obtain ⟨hsd, -, hφ0, hφi, -, -, -⟩ := hoh
  by_cases hsum : Summable fun n => ‖aP ηp x n‖
  swap
  · have h0 : MinSp.zMin ηp ηs x = 0 := by
      unfold MinSp.zMin
      simp [smSum_eq, eSum_junk _ hsum]
    rw [h0]
    positivity
  have hηs0 : ∀ t : ℝ, 0 ≤ ηs t := etaS_nonneg ηs φ hsd hφ0
  have hmin : MeasurableSet (Smooth.minorSet x) :=
    measurableSet_Ioc.diff (measurableSet_arcs _ _ _)
  have hsubm : Smooth.minorSet x ⊆ Set.Icc 0 1 := fun α h => Set.Ioc_subset_Icc_self h.1
  have hcs : Continuous fun α => ‖Smooth.smSum ηs x α‖ := (eSum_continuous (aP ηs x)).norm
  have hE2 := heb hs1 hs2 b hb x hx
  have hZ1 := z1_boundP c05 C hc05 hC0 ηp ηs φ b hpal hi0 hco hgo hgm hcp hts hsd hφ0 hφi x hx
    hsum hE2 (hjE b hb x hx)
  have hZ2 := z2_le ηp ηs x hsum hηs0 _ hE2
  have hZ1n : 0 ≤ ∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖OC.s1Sum ηp x α‖ ^ 2 :=
    setIntegral_nonneg hmin fun α _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hZ2n : 0 ≤ ∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖s2Sum ηp x α‖ ^ 2 :=
    setIntegral_nonneg hmin fun α _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hF : ∀ α ∈ Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖Smooth.smSum ηp x α‖ ^ 2 ≤
      ‖Smooth.smSum ηs x α‖ * (‖OC.s1Sum ηp x α‖ + ‖s2Sum ηp x α‖) ^ 2 := by
    intro α _
    rw [hspl ηp x hsum α]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2) (norm_nonneg _)
  refine le_sq_of_forall_t _ _ _ (le_trans hZ1n hZ1) (le_trans hZ2n hZ2) fun t ht => ?_
  have hm := mink (Smooth.minorSet x) hmin hsubm (fun α => ‖Smooth.smSum ηs x α‖)
    (fun α => ‖OC.s1Sum ηp x α‖) (fun α => ‖s2Sum ηp x α‖)
    (fun α => ‖Smooth.smSum ηs x α‖ * ‖Smooth.smSum ηp x α‖ ^ 2) hcs (s1_cont ηp x)
    (s2_cont ηp x) (fun α => norm_nonneg _) (fun α _ => mul_nonneg (norm_nonneg _)
      (sq_nonneg _)) hF t ht
  have h1t : 0 ≤ 1 + t := by linarith
  have h2t : 0 ≤ 1 + 1 / t := by positivity
  calc MinSp.zMin ηp ηs x
      ≤ (1 + t) * (∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖OC.s1Sum ηp x α‖ ^ 2) +
        (1 + 1 / t) * ∫ α in Smooth.minorSet x,
          ‖Smooth.smSum ηs x α‖ * ‖s2Sum ηp x α‖ ^ 2 := hm
    _ ≤ (1 + t) * (MajSp.l1 φ * x / 49 * (mMCP c05 C φ ηp b x + MinSp.tT φ ηp b x)) +
        (1 + 1 / t) * (MinSp.sStar ηs x * MinSp.eBig b x) :=
      add_le_add (mul_le_mul_of_nonneg_left hZ1 h1t) (mul_le_mul_of_nonneg_left hZ2 h2t)

/-- **`OP.OstopP c05 C` on Helfgott's weights from the named layer-2 links** (generated from
`OS.ostopL_of_layer2`). Application only. -/
theorem ostopP_of_layer2 (c05 C : ℝ) (hc05 : 0 ≤ c05) (hC0 : 0 ≤ C) (hco : OC.CoeurY HW.etaPlus)
    (hgo : GorshP c05 C HW.etaStar HW.phi) (hgm : GTMonoP c05 C HW.phi)
    (hcp : CoprarP c05 C HW.etaStar HW.phi) (heb : EBound2 HW.etaPlus)
    (hjE : JgeE HW.etaPlus) (hts : TopStepP c05 C HW.phi) :
    OstopP c05 C HW.etaPlus HW.etaStar HW.phi :=
  ostopP_of_links c05 C hc05 hC0 HW.etaPlus HW.etaStar HW.phi palanLink splitLink i0sLink hco
    hgo hgm hcp heb
    EN.supN_helf.1 EN.supN_helf.2.1 hjE hts

/-- **`OP.OstopP c05 C` with `GorshP` itself composed** (`GSP.gorshP_of_open`; generated from
`OS.ostopL_of_open`). Application only. -/
theorem ostopP_of_open (c05 C : ℝ) (hc05 : 0 ≤ c05) (hC0 : 0 ≤ C) (hco : OC.CoeurY HW.etaPlus)
    (hmm : MinMainP c05 C) (h15 : GS.RS62Thm15) (hmo : GSP.GYMonoP c05 C)
    (hhl : GSP.HLeGP c05 C) (hau : GS.Austeria) (hgm : GTMonoP c05 C HW.phi)
    (hcp : CoprarP c05 C HW.etaStar HW.phi) (heb : EBound2 HW.etaPlus) (hjE : JgeE HW.etaPlus)
    (hts : TopStepP c05 C HW.phi) : OstopP c05 C HW.etaPlus HW.etaStar HW.phi :=
  ostopP_of_layer2 c05 C hc05 hC0 hco
    (GSP.gorshP_of_open c05 C hc05 hC0 HW.etaStar HW.phi hmm h15 hmo hhl hau) hgm hcp heb
    hjE hts

end Principia.Common.TernaryGoldbach.OSP
