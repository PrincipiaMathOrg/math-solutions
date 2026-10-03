/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.OstopP
import Principia.Common.TernaryGoldbach.GorshSpine

set_option autoImplicit false

/-!
# The spine of `prop:gorsh` at `(c05, C)`: `OP.GorshP` from `OP.MinMainP`

`GorshSpine.lean` composes `OL.GorshL` from `OL.MinMainL`; here the same spine is regenerated
for `OP.GorshP c05 C` from `OP.MinMainP c05 C`, for EVERY `(c05, C)` with `c05, C ≥ 0`
(`scratchpad/ostopp/gen_gorshp.py`, counted substitution of `GorshSpine.lean`). Every step that
does not see `g` is reused from `GS` (`off_arc`, `dirichlet_at`, `arg_lower`, `arg_upper`,
`rR_ge`, `r1y_le_third`, `arg_le_r1y`, G7, `mellinLe_all`, `merkel_of_rs62`, `scale_ge`,
`gtl_alg`, `fCap`, `aCap`).

```
 M2  kraw_le_gYP   krawP c05 C (Y,δ,q) ≤ gYP c05 C (Y, max(1,|δ|/8)q)·Y     (c05 ≥ 0)   PROVED
 G5/G6 scale_boundP  from MinMainP, GYMonoP, HLeGP                                   PROVED
 G8  gorsh_coreP   the integration against φ(w)dw/w                                  PROVED
     gtlIntP       gYP ≤ gCapP on the integrated arguments (c05, C ≥ 0)               PROVED
 gorshP_of_open : MinMainP → RS62Thm15 → GYMonoP → HLeGP → Austeria → GorshP c05 C η* φ
```

Where the generic compositions use the constants: ONLY their signs. `c05 ≥ 0` makes the main
term `(R log 2r + c05)√ϝ` non-negative (`kraw_le_gYP`, `gYP_le_cap`); `C ≥ 0` makes `L_t` and its
cap non-negative (`gYP_pos`, `gYP_le_cap`). No numeric value of either constant is used.
-/

namespace Principia.Common.TernaryGoldbach.GSP

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction
open Principia.Common.TernaryGoldbach.GS
open Principia.Common.TernaryGoldbach.OP

/-! ## (1) Objects and links at `(c05, C)` -/

/-- **The majorant integrated in G8** at `(c05, C)` (generated from `GS.gPiece`). -/
noncomputable def gPieceP (c05 C : ℝ) (φ : ℝ → ℝ) (y r w₁ w : ℝ) : ℝ :=
  if w ≤ w₁ then y * (1.04488 * φ w) else
    if w ≤ 1 then y * (gYP c05 C (w * y) (w * r) * φ w) else
      y * (gYP c05 C (w * y) r * φ w)

/-- **Link [GYMonoP] — `lem:vinc` at `K = 1` on `gYP c05 C`** (generated from `GS.GYMono`). -/
def GYMonoP (c05 C : ℝ) : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → AntitoneOn (gYP c05 C Y) (Set.Icc 175 (Y ^ ((1 : ℝ) / 3) / 6))

/-- **Link [HLeGP] — the second case fits under `gYP c05 C`** (generated from `GS.HLeG`). -/
def HLeGP (c05 C : ℝ) : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → hL Y ≤ gYP c05 C Y (MinSp.r1y Y) * Y

/-- **Link [GTLIntP]** — the `g`-weighted pieces of `gTP c05 C` are integrable (generated from
`GS.GTLInt`). PROVED for `c05, C ≥ 0` (`gtlIntP`). -/
def GTLIntP (c05 C : ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, IntegrableOn φ (Set.Ioi 0) → ∀ y : ℝ, 10 ^ 25 ≤ y →
    ∀ r : ℝ, 150000 ≤ r → r ≤ MinSp.r1y y →
      IntegrableOn (fun w => gYP c05 C (w * y) (w * r) * φ w)
          (Set.Ioc (max (1 / MinSp.kK y) (1000 / r)) 1) ∧
        IntegrableOn (fun w => gYP c05 C (w * y) r * φ w) (Set.Ioi 1)

/-! ## (2) M2 at `(c05, C)` -/

/-- **The `L` comparison of M2 at `C`** (generated from `GS.ltosca_le`; `C` cancels). -/
theorem ltosca_leP (C d rp : ℝ) (q : ℕ) (hq : 1 ≤ q) (hd : 2 ≤ d) (hdq : d * q = 2 * rp)
    (hqr : (q : ℝ) ≤ rp) (hF : (q : ℝ) / Nat.totient q ≤ MinSp.bigF rp) :
    lToscaP C d q ≤ lLcP C rp := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hrp0 : 0 < rp := by linarith
  have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hlog : Real.log d + Real.log q = Real.log 2 + Real.log rp := by
    rw [← Real.log_mul hd0.ne' hq0.ne', hdq, Real.log_mul two_ne_zero hrp0.ne']
  have hlq : Real.log q ≤ Real.log rp := Real.log_le_log hq0 hqr
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hld : Real.log 2 ≤ Real.log d := Real.log_le_log two_pos hd
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have e1 : Real.log (d ^ ((7 : ℝ) / 4) * (q : ℝ) ^ ((13 : ℝ) / 4)) =
      7 / 4 * Real.log d + 13 / 4 * Real.log q := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hd0 _).ne' (Real.rpow_pos_of_pos hq0 _).ne',
      Real.log_rpow hd0, Real.log_rpow hq0]
  have e2 : Real.log ((q : ℝ) ^ (13.6516 : ℝ) * d ^ (1.7984 : ℝ)) =
      13.6516 * Real.log q + 1.7984 * Real.log d := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hq0 _).ne' (Real.rpow_pos_of_pos hd0 _).ne',
      Real.log_rpow hq0, Real.log_rpow hd0]
  have hqφ : 0 ≤ (q : ℝ) / Nat.totient q := div_nonneg hq0.le hφ0.le
  have hX : 7 / 4 * Real.log d + 13 / 4 * Real.log q + 80 / 9 ≤
      7 / 4 * Real.log 2 + 13 / 4 * Real.log rp + 80 / 9 := by linarith
  have hmain : (7 / 4 * Real.log d + 13 / 4 * Real.log q + 80 / 9) /
      ((Nat.totient q : ℝ) / q) ≤
      MinSp.bigF rp * (7 / 4 * Real.log 2 + 13 / 4 * Real.log rp + 80 / 9) := by
    rw [div_div_eq_mul_div, mul_div_assoc, mul_comm (MinSp.bigF rp)]
    exact mul_le_mul hX hF hqφ (by linarith)
  unfold lToscaP lLcP
  rw [e1, e2, OL.log_two_rpow_mul _ _ rp hrp0, OL.log_two_rpow_mul _ _ rp hrp0]
  linarith

/-- **[M2] `eq:kraw` ⟹ `eq:syryza` at `(c05, C)`** (generated from `GS.kraw_le_gYL`; uses
`c05 ≥ 0`). -/
theorem kraw_le_gYP (c05 C : ℝ) (hc05 : 0 ≤ c05) (hmk : Merkel) (Y δ : ℝ) (q : ℕ)
    (hq : 1 ≤ q) (hY : 0 < Y)
    (h3 : 3 ≤ max 1 (|δ| / 8) * q) (hup : max 1 (|δ| / 8) * q ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    krawP c05 C Y δ q ≤ gYP c05 C Y (max 1 (|δ| / 8) * q) * Y := by
  obtain ⟨rp, hrp⟩ : ∃ rp : ℝ, rp = max 1 (|δ| / 8) * q := ⟨_, rfl⟩
  rw [← hrp] at h3 hup ⊢
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hdz : OC.dz δ = 2 * max 1 (|δ| / 8) := by
    unfold OC.dz
    rcases le_total 1 (|δ| / 8) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_left (by linarith)]
      norm_num
  have hdq : OC.dz δ * q = 2 * rp := by
    rw [hdz, hrp]
    ring
  have hd2 : 2 ≤ OC.dz δ := le_max_left _ _
  have hd0 : 0 < OC.dz δ := by linarith
  have hqr : (q : ℝ) ≤ rp := by
    rw [hrp]
    nlinarith [le_max_left 1 (|δ| / 8)]
  have hrp0 : 0 < rp := by linarith
  have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hF : (q : ℝ) / Nat.totient q ≤ MinSp.bigF rp := (hmk q hq rp h3 hqr).le
  have hFq : (q : ℝ) ≤ MinSp.bigF rp * Nat.totient q := (div_le_iff₀ hφ0).mp hF
  have hF0 : 0 ≤ MinSp.bigF rp := le_trans (div_nonneg hq0.le hφ0.le) hF
  have hR := rR_ge Y (2 * rp) hY (by linarith) (by linarith)
  have hlog2 : 0 ≤ Real.log (2 * rp) := Real.log_nonneg (by linarith)
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = MinSp.rR Y (2 * rp) * Real.log (2 * rp) + c05 := ⟨_, rfl⟩
  have hA : 0 ≤ A := by
    rw [hAdef]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ MinSp.rR Y (2 * rp)) hlog2
    linarith
  have hs2 : 0 < Real.sqrt (2 * rp) := Real.sqrt_pos.mpr (by linarith)
  have hsd : 0 < Real.sqrt (OC.dz δ * Nat.totient q) := Real.sqrt_pos.mpr (by positivity)
  have hkey : 1 / Real.sqrt (OC.dz δ * Nat.totient q) ≤
      Real.sqrt (MinSp.bigF rp) / Real.sqrt (2 * rp) := by
    rw [div_le_div_iff₀ hsd hs2, one_mul, ← Real.sqrt_mul hF0]
    apply Real.sqrt_le_sqrt
    rw [← hdq]
    calc OC.dz δ * q ≤ OC.dz δ * (MinSp.bigF rp * Nat.totient q) :=
          mul_le_mul_of_nonneg_left hFq hd0.le
      _ = MinSp.bigF rp * (OC.dz δ * Nat.totient q) := by ring
  have hT1 : A / Real.sqrt (OC.dz δ * Nat.totient q) * Y ≤
      A * Real.sqrt (MinSp.bigF rp) / Real.sqrt (2 * rp) * Y := by
    apply mul_le_mul_of_nonneg_right _ hY.le
    calc A / Real.sqrt (OC.dz δ * Nat.totient q)
        = A * (1 / Real.sqrt (OC.dz δ * Nat.totient q)) := by ring
      _ ≤ A * (Real.sqrt (MinSp.bigF rp) / Real.sqrt (2 * rp)) :=
          mul_le_mul_of_nonneg_left hkey hA
      _ = A * Real.sqrt (MinSp.bigF rp) / Real.sqrt (2 * rp) := by ring
  have hlt := ltosca_leP C (OC.dz δ) rp q hq hd2 hdq hqr hF
  have hT3 : 2 * Y / (2 * rp) * lToscaP C (OC.dz δ) q ≤ lLcP C rp / rp * Y := by
    rw [mul_div_mul_left Y rp two_ne_zero]
    calc Y / rp * lToscaP C (OC.dz δ) q ≤ Y / rp * lLcP C rp :=
          mul_le_mul_of_nonneg_left hlt (div_nonneg hY.le hrp0.le)
      _ = lLcP C rp / rp * Y := by ring
  have hT4 : Y ^ ((5 : ℝ) / 6) = Y ^ (-(1 : ℝ) / 6) * Y := by
    rw [← Real.rpow_add_one hY.ne']
    norm_num
  unfold krawP gYP
  rw [hdq, hT4, ← hAdef]
  calc _ ≤ A * Real.sqrt (MinSp.bigF rp) / Real.sqrt (2 * rp) * Y +
        2.5 * Y / Real.sqrt (2 * rp) + lLcP C rp / rp * Y +
        3.2 * (Y ^ (-(1 : ℝ) / 6) * Y) := by linarith
    _ = _ := by ring

/-! ## (3) G5 + G6 and G8 -/

/-- **[G5 + G6] at `(c05, C)`** (generated from `GS.scale_bound`). -/
theorem scale_boundP (c05 C : ℝ) (hc05 : 0 ≤ c05) (hmm : MinMainP c05 C) (hmk : Merkel)
    (hmo : GYMonoP c05 C) (hhl : HLeGP c05 C)
    (r : ℕ) (y : ℝ) (hy : 0 < y) (hr1 : (r : ℝ) ≤ MinSp.r1y y) (α : ℝ)
    (hα : α ∉ Smooth.arcs 8 r y) (w : ℝ) (hw : 0 < w) (hY : 3.4e23 ≤ w * y)
    (hlo : 175 ≤ min w 1 * r) :
    ‖Smooth.smSum HW.eta2 (w * y) α‖ ≤ gYP c05 C (w * y) (min w 1 * r) * (w * y) := by
  have hY0 : 0 < w * y := mul_pos hw hy
  obtain ⟨u, hu0, -, hu2, hu3⟩ := cube_rep (w * y) hY0
  have hu2' : 2 ≤ u := by
    by_contra h'
    have h := lt_of_not_ge h'
    have h8 : u ^ 3 < 2 ^ 3 := pow_lt_pow_left₀ h hu0.le (by norm_num)
    rw [← hu3] at h8
    norm_num at h8
    linarith
  have hQ : 1 ≤ 3 / 4 * (w * y) ^ ((2 : ℝ) / 3) := by
    rw [hu2]
    nlinarith
  obtain ⟨a, q, hq, hg, hqQ, hd⟩ := dirichlet_at α (w * y) hQ
  have hlow := arg_lower r y w hy hw α hα a q hq hg
  have h2α : 2 * α = a / q + w * y * (2 * α - a / q) / (w * y) := by
    rw [mul_div_cancel_left₀ _ hY0.ne']
    ring
  have hδ : |w * y * (2 * α - a / q) / (w * y)| ≤
      1 / (q * (3 / 4 * (w * y) ^ ((2 : ℝ) / 3))) := by
    rwa [mul_div_cancel_left₀ _ hY0.ne']
  obtain ⟨hsm, hlg⟩ := hmm (w * y) hY α (w * y * (2 * α - a / q)) a q hq hg h2α hqQ hδ
  have hmono := hmo (w * y) hY
  have hr1Y := r1y_le_third (w * y) hY
  by_cases hc : (q : ℝ) ≤ (w * y) ^ ((1 : ℝ) / 3) / 6
  · have hup := arg_upper (w * y) hY0 α a q hq hd hc
    have hk := kraw_le_gYP c05 C hc05 hmk (w * y) (w * y * (2 * α - a / q)) q hq hY0
      (by linarith) hup
    have hmn : gYP c05 C (w * y) (max 1 (|w * y * (2 * α - a / q)| / 8) * q) ≤
        gYP c05 C (w * y) (min w 1 * r) :=
      hmono ⟨hlo, by linarith⟩ ⟨by linarith, hup⟩ hlow
    calc ‖Smooth.smSum HW.eta2 (w * y) α‖ ≤ krawP c05 C (w * y) (w * y * (2 * α - a / q)) q :=
          hsm hc
      _ ≤ _ := hk
      _ ≤ gYP c05 C (w * y) (min w 1 * r) * (w * y) := mul_le_mul_of_nonneg_right hmn hY0.le
  · have hbig := hlg (lt_of_not_ge hc)
    have hH := hhl (w * y) hY
    have ht1 : min w 1 * r ≤ MinSp.r1y (w * y) := arg_le_r1y y w r hy hw hr1
    have hmn : gYP c05 C (w * y) (MinSp.r1y (w * y)) ≤ gYP c05 C (w * y) (min w 1 * r) :=
      hmono ⟨hlo, by linarith⟩ ⟨by linarith, hr1Y⟩ ht1
    calc ‖Smooth.smSum HW.eta2 (w * y) α‖ ≤ hL (w * y) := hbig
      _ ≤ _ := hH
      _ ≤ gYP c05 C (w * y) (min w 1 * r) * (w * y) := mul_le_mul_of_nonneg_right hmn hY0.le

/-- **[G8] The integration at `(c05, C)`** (generated from `GS.gorsh_core`). -/
theorem gorsh_coreP (c05 C : ℝ) (hc05 : 0 ≤ c05) (hmm : MinMainP c05 C) (hmk : Merkel)
    (hmo : GYMonoP c05 C) (hhl : HLeGP c05 C) (hau : Austeria) (hint : GTLIntP c05 C)
    (φ : ℝ → ℝ) (hφ0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ φ t)
    (hφi : IntegrableOn φ (Set.Ioi 0)) (y : ℝ) (hy : 10 ^ 25 ≤ y) (r : ℕ) (hr : 150000 ≤ r)
    (hr1 : (r : ℝ) ≤ MinSp.r1y y) (α : ℝ) (hα : α ∉ Smooth.arcs 8 r y) :
    ∫ w in Set.Ioi (0 : ℝ), ‖Smooth.smSum HW.eta2 (w * y) α‖ * φ w / w ≤
      (gTP c05 C φ y r + MinSp.cPhi3 φ (MinSp.kK y)) * MajSp.l1 φ * y := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hrR : (150000 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  -- the degenerate `|φ|₁ = 0`: `φ = 0` a.e. on `(0,∞)`, both sides vanish
  rcases eq_or_ne (MajSp.l1 φ) 0 with h0 | h0
  · have hab : (fun w => |φ w|) =ᵐ[volume.restrict (Set.Ioi 0)] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun w => abs_nonneg (φ w)) (Integrable.abs hφi)).mp h0
    have hz : ∫ w in Set.Ioi (0 : ℝ), ‖Smooth.smSum HW.eta2 (w * y) α‖ * φ w / w = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · filter_upwards [hab] with w hw
        have hφw : φ w = 0 := abs_eq_zero.mp hw
        simp [hφw]
    rw [hz, h0]
    simp
  have hl17 := log_gt y hy
  have hK0 : 0 < 1 / MinSp.kK y := by
    unfold MinSp.kK
    have : 0 < Real.log y := by linarith
    positivity
  have hK1 : 1 / MinSp.kK y ≤ 1 := by
    unfold MinSp.kK
    rw [div_le_one (by linarith)]
    linarith
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : ℝ, w₁ = max (1 / MinSp.kK y) (1000 / (r : ℝ)) := ⟨_, rfl⟩
  have hKw : 1 / MinSp.kK y ≤ w₁ := hw₁ ▸ le_max_left _ _
  have hrw : 1000 / (r : ℝ) ≤ w₁ := hw₁ ▸ le_max_right _ _
  have hw0 : 0 < w₁ := lt_of_lt_of_le hK0 hKw
  have hw1 : w₁ ≤ 1 := by
    rw [hw₁]
    refine max_le hK1 ?_
    rw [div_le_one hr0]
    linarith
  -- integrability of the majorant, piece by piece
  obtain ⟨hI1, hI2⟩ := hint φ hφi y hy r hrR hr1
  rw [← hw₁] at hI1
  have hφw : IntegrableOn φ (Set.Ioc 0 w₁) := hφi.mono_set Set.Ioc_subset_Ioi_self
  have hg1 : IntegrableOn (gPieceP c05 C φ y r w₁) (Set.Ioc 0 w₁) :=
    IntegrableOn.congr_fun (Integrable.const_mul hφw (y * 1.04488))
      (fun w hw => by simp only [gPieceP, if_pos hw.2]; ring) measurableSet_Ioc
  have hg2 : IntegrableOn (gPieceP c05 C φ y r w₁) (Set.Ioc w₁ 1) :=
    IntegrableOn.congr_fun (Integrable.const_mul hI1 y)
      (fun w hw => by simp only [gPieceP, if_neg (not_le.mpr hw.1), if_pos hw.2])
      measurableSet_Ioc
  have hg3 : IntegrableOn (gPieceP c05 C φ y r w₁) (Set.Ioi 1) :=
    IntegrableOn.congr_fun (Integrable.const_mul hI2 y)
      (fun w hw => by
        have h1 : ¬ w ≤ w₁ := not_le.mpr (lt_of_le_of_lt hw1 hw)
        simp only [gPieceP, if_neg h1, if_neg (not_le.mpr (show (1 : ℝ) < w from hw))])
      measurableSet_Ioi
  have hU1 : Set.Ioc w₁ 1 ∪ Set.Ioi 1 = Set.Ioi w₁ := Set.Ioc_union_Ioi_eq_Ioi hw1
  have hU0 : Set.Ioc 0 w₁ ∪ Set.Ioi w₁ = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi hw0.le
  have hg23 : IntegrableOn (gPieceP c05 C φ y r w₁) (Set.Ioi w₁) := by
    rw [← hU1]
    exact hg2.union hg3
  have hg : IntegrableOn (gPieceP c05 C φ y r w₁) (Set.Ioi 0) := by
    rw [← hU0]
    exact hg1.union hg23
  -- the pointwise bound (G7 on `(0,w₁]`, G5/G6 beyond)
  have hpt : ∀ w ∈ Set.Ioi (0 : ℝ),
      ‖Smooth.smSum HW.eta2 (w * y) α‖ * φ w / w ≤ gPieceP c05 C φ y r w₁ w := by
    intro w hw
    have hw0' : 0 < w := hw
    have hφw0 : 0 ≤ φ w := hφ0 w hw0'.le
    rcases le_or_gt w w₁ with h1 | h1
    · rw [show gPieceP c05 C φ y r w₁ w = y * (1.04488 * φ w) by simp only [gPieceP, if_pos h1]]
      exact div_bound _ _ _ _ _ hw0' hφw0
        (norm_smSum_eta2_le hau (w * y) (mul_pos hw0' hy0) α)
    · have hY : 3.4e23 ≤ w * y := scale_ge y w hy (le_trans hKw h1.le)
      rcases le_or_gt w 1 with h2 | h2
      · rw [show gPieceP c05 C φ y r w₁ w = y * (gYP c05 C (w * y) (w * r) * φ w) by
          simp only [gPieceP, if_neg (not_le.mpr h1), if_pos h2]]
        have hlo : 175 ≤ min w 1 * (r : ℝ) := by
          rw [min_eq_left h2]
          have h3 : 1000 / (r : ℝ) * r ≤ w * r :=
            mul_le_mul_of_nonneg_right (le_trans hrw h1.le) hr0.le
          rw [div_mul_cancel₀ _ hr0.ne'] at h3
          linarith
        have hb := scale_boundP c05 C hc05 hmm hmk hmo hhl r y hy0 hr1 α hα w hw0' hY hlo
        rw [min_eq_left h2] at hb
        exact div_bound _ _ _ _ _ hw0' hφw0 hb
      · rw [show gPieceP c05 C φ y r w₁ w = y * (gYP c05 C (w * y) r * φ w) by
          simp only [gPieceP, if_neg (not_le.mpr h1), if_neg (not_le.mpr h2)]]
        have hlo : 175 ≤ min w 1 * (r : ℝ) := by
          rw [min_eq_right h2.le, one_mul]
          linarith
        have hb := scale_boundP c05 C hc05 hmm hmk hmo hhl r y hy0 hr1 α hα w hw0' hY hlo
        rw [min_eq_right h2.le, one_mul] at hb
        exact div_bound _ _ _ _ _ hw0' hφw0 hb
  have hmono : ∫ w in Set.Ioi (0 : ℝ), ‖Smooth.smSum HW.eta2 (w * y) α‖ * φ w / w ≤
      ∫ w in Set.Ioi (0 : ℝ), gPieceP c05 C φ y r w₁ w :=
    integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ioi fun w hw =>
        div_nonneg (mul_nonneg (norm_nonneg _) (hφ0 w (le_of_lt hw))) (le_of_lt hw))
      hg (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  -- the integral of the majorant
  have e1 : ∫ w in Set.Ioc 0 w₁, gPieceP c05 C φ y r w₁ w =
      y * (1.04488 * ∫ w in Set.Ioc 0 w₁, φ w) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun w => y * (1.04488 * φ w))
      (fun w hw => by simp only [gPieceP, if_pos hw.2]), integral_const_mul, integral_const_mul]
  have e2 : ∫ w in Set.Ioc w₁ 1, gPieceP c05 C φ y r w₁ w =
      y * ∫ w in Set.Ioc w₁ 1, gYP c05 C (w * y) (w * r) * φ w := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (g := fun w => y * (gYP c05 C (w * y) (w * r) * φ w))
      (fun w hw => by simp only [gPieceP, if_neg (not_le.mpr hw.1), if_pos hw.2]),
      integral_const_mul]
  have e3 : ∫ w in Set.Ioi 1, gPieceP c05 C φ y r w₁ w =
      y * ∫ w in Set.Ioi 1, gYP c05 C (w * y) r * φ w := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun w => y * (gYP c05 C (w * y) r * φ w))
      (fun w hw => by
        have h1 : ¬ w ≤ w₁ := not_le.mpr (lt_of_le_of_lt hw1 hw)
        simp only [gPieceP, if_neg h1, if_neg (not_le.mpr (show (1 : ℝ) < w from hw))]),
      integral_const_mul]
  have hsplit : ∫ w in Set.Ioi (0 : ℝ), gPieceP c05 C φ y r w₁ w =
      y * (1.04488 * ∫ w in Set.Ioc 0 w₁, φ w) +
        ((y * ∫ w in Set.Ioc w₁ 1, gYP c05 C (w * y) (w * r) * φ w) +
          y * ∫ w in Set.Ioi 1, gYP c05 C (w * y) r * φ w) := by
    rw [← hU0, setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hg1 hg23, ← hU1,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hg2 hg3, e1, e2, e3]
  -- the `φ`-mass of `(0,w₁]` is `J₀ + J₁`
  have hJ : ∫ w in Set.Ioc 0 w₁, φ w =
      (∫ w in (0 : ℝ)..(1 / MinSp.kK y), |φ w|) + ∫ w in (1 / MinSp.kK y)..w₁, |φ w| := by
    rw [intervalIntegral.integral_of_le hK0.le, intervalIntegral.integral_of_le hKw,
      ← Set.Ioc_union_Ioc_eq_Ioc hK0.le hKw,
      setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (hφi.mono_set Set.Ioc_subset_Ioi_self)
        (hφi.mono_set (fun w hw => lt_trans hK0 hw.1))]
    congr 1
    · exact setIntegral_congr_fun measurableSet_Ioc
        (fun w hw => (abs_of_nonneg (hφ0 w hw.1.le)).symm)
    · exact setIntegral_congr_fun measurableSet_Ioc
        (fun w hw => (abs_of_nonneg (hφ0 w (lt_trans hK0 hw.1).le)).symm)
  have hI1 : (∫ w in w₁..1, gYP c05 C (w * y) (w * r) * φ w) =
      ∫ w in Set.Ioc w₁ 1, gYP c05 C (w * y) (w * r) * φ w := intervalIntegral.integral_of_le hw1
  rw [hJ] at hsplit
  unfold gTP MinSp.cPhi3
  rw [← hw₁, gtl_alg _ _ _ _ _ _ h0, hI1]
  linarith

/-- **`OP.GorshP c05 C` from its links** (generated from `GS.gorshL_of_links`). -/
theorem gorshP_of_links (c05 C : ℝ) (hc05 : 0 ≤ c05) (ηs φ : ℝ → ℝ) (hmm : MinMainP c05 C)
    (hmk : Merkel) (hmo : GYMonoP c05 C) (hhl : HLeGP c05 C) (hau : Austeria)
    (hme : MellinLe ηs φ) (hint : GTLIntP c05 C) : GorshP c05 C ηs φ := by
  intro hη hφ0 hφi x hx r hr hr1 α hα
  exact le_trans (hme hη hφ0 hφi x (MinSp.x_pos x hx) α)
    (gorsh_coreP c05 C hc05 hmm hmk hmo hhl hau hint φ hφ0 hφi (x / 49) (MinSp.y_ge x hx) r
      hr hr1 α hα)

/-! ## (4) `GTLIntP` PROVED -/

/-- The cap on `L_t` (`lLcP C`) for `1000 ≤ t ≤ R` (generated from `GS.lCap`). -/
noncomputable def lCapP (C R : ℝ) : ℝ :=
  fCap R * (7 / 4 * Real.log 2 + 13 / 4 * Real.log R + 80 / 9) + 1.7984 * Real.log 2 +
    13.6516 * Real.log R + C

/-- The cap on `gYP c05 C (Y,t)` (generated from `GS.gCap`). -/
noncomputable def gCapP (c05 C R : ℝ) : ℝ :=
  ((aCap R * Real.log (2 * R) + c05) * Real.sqrt (fCap R) + 2.5) / Real.sqrt 2000 +
    lCapP C R / 1000 + 3.2

/-- **`gYP c05 C (Y,t) ≤ gCapP c05 C R`** (generated from `GS.gYL_le_cap`). -/
theorem gYP_le_cap (c05 C Y t R : ℝ) (hc05 : 0 ≤ c05) (hC : 0 ≤ C) (hY : 1 ≤ Y)
    (ht : 1000 ≤ t) (htY : t ≤ Y ^ ((1 : ℝ) / 3) / 6) (htR : t ≤ R) :
    gYP c05 C Y t ≤ gCapP c05 C R := by
  have hY0 : 0 < Y := by linarith
  have ht0 : 0 < t := by linarith
  have hR0 : 0 < R := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlt : Real.exp 1 ≤ Real.log t := by
    have h1 : Real.log ((2 : ℝ) ^ 9) ≤ Real.log t :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_pow] at h1
    have := Real.log_two_gt_d9
    have := Real.exp_one_lt_d9
    push_cast at h1
    linarith
  have hlt0 : 0 < Real.log t := lt_of_lt_of_le (Real.exp_pos 1) hlt
  have hll : 1 ≤ Real.log (Real.log t) := (Real.le_log_iff_exp_le hlt0).mpr hlt
  have hlR : Real.log t ≤ Real.log R := Real.log_le_log ht0 htR
  have hllR : Real.log (Real.log t) ≤ Real.log (Real.log R) := Real.log_le_log hlt0 hlR
  have hg0 : 0 < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  -- `ϝ`
  have hF0 : 0 ≤ MinSp.bigF t := by
    unfold MinSp.bigF
    have := div_nonneg (by norm_num : (0 : ℝ) ≤ 2.50637) (by linarith : 0 ≤ Real.log (Real.log t))
    have := mul_nonneg hg0.le (by linarith : 0 ≤ Real.log (Real.log t))
    linarith
  have hF1 : MinSp.bigF t ≤ fCap R := by
    unfold MinSp.bigF fCap
    have h1 : 2.50637 / Real.log (Real.log t) ≤ 2.50637 := div_le_self (by norm_num) hll
    have h2 := mul_le_mul_of_nonneg_left hllR hg0.le
    linarith
  have hFc0 : 0 ≤ fCap R := le_trans hF0 hF1
  -- `R_{Y,2t}`
  have hRlo := rR_ge Y (2 * t) hY0 (by linarith) (by linarith)
  have hRhi : MinSp.rR Y (2 * t) ≤ aCap R := by
    unfold MinSp.rR aCap
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Y ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
    rw [← hc] at htY ⊢
    have hq : Real.exp 1 ≤ 9 * c / (2.004 * (2 * t)) := by
      rw [le_div_iff₀ (by positivity)]
      have := Real.exp_one_lt_d9
      nlinarith
    have hℓ : 1 ≤ Real.log (9 * c / (2.004 * (2 * t))) :=
      (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hq)).mpr hq
    have h8 : 0 ≤ Real.log (4 * (2 * t)) := Real.log_nonneg (by linarith)
    have h8R : Real.log (4 * (2 * t)) ≤ Real.log (8 * R) :=
      Real.log_le_log (by positivity) (by linarith)
    have hu0 : 0 ≤ Real.log (4 * (2 * t)) / (2 * Real.log (9 * c / (2.004 * (2 * t)))) :=
      div_nonneg h8 (by linarith)
    have hu : Real.log (4 * (2 * t)) / (2 * Real.log (9 * c / (2.004 * (2 * t)))) ≤
        Real.log (8 * R) / 2 := by
      calc Real.log (4 * (2 * t)) / (2 * Real.log (9 * c / (2.004 * (2 * t))))
          ≤ Real.log (4 * (2 * t)) / 2 := div_le_div_of_nonneg_left h8 (by norm_num) (by linarith)
        _ ≤ Real.log (8 * R) / 2 := by linarith
    have hlog1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 +
      Real.log (4 * (2 * t)) / (2 * Real.log (9 * c / (2.004 * (2 * t)))) by linarith)
    linarith
  -- the first term
  have hl2t : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith)
  have hl2R : Real.log (2 * t) ≤ Real.log (2 * R) := Real.log_le_log (by linarith) (by linarith)
  have ha0 : 0 ≤ aCap R := le_trans (by linarith) hRhi
  have hA : MinSp.rR Y (2 * t) * Real.log (2 * t) + c05 ≤
      aCap R * Real.log (2 * R) + c05 := by
    have := mul_le_mul hRhi hl2R hl2t ha0
    linarith
  have hA0 : 0 ≤ MinSp.rR Y (2 * t) * Real.log (2 * t) + c05 := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ MinSp.rR Y (2 * t)) hl2t
    linarith
  have hsF := Real.sqrt_le_sqrt hF1
  have hN : (MinSp.rR Y (2 * t) * Real.log (2 * t) + c05) * Real.sqrt (MinSp.bigF t) + 2.5 ≤
      (aCap R * Real.log (2 * R) + c05) * Real.sqrt (fCap R) + 2.5 := by
    have := mul_le_mul hA hsF (Real.sqrt_nonneg _) (by linarith)
    linarith
  have hN0 : 0 ≤ (aCap R * Real.log (2 * R) + c05) * Real.sqrt (fCap R) + 2.5 := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ aCap R * Real.log (2 * R) + c05)
      (Real.sqrt_nonneg (fCap R))
    linarith
  have hs2000 : 0 < Real.sqrt 2000 := Real.sqrt_pos.mpr (by norm_num)
  have hs2t : Real.sqrt 2000 ≤ Real.sqrt (2 * t) := Real.sqrt_le_sqrt (by linarith)
  have hT1 : ((MinSp.rR Y (2 * t) * Real.log (2 * t) + c05) * Real.sqrt (MinSp.bigF t) + 2.5) /
      Real.sqrt (2 * t) ≤
      ((aCap R * Real.log (2 * R) + c05) * Real.sqrt (fCap R) + 2.5) / Real.sqrt 2000 :=
    calc _ ≤ ((aCap R * Real.log (2 * R) + c05) * Real.sqrt (fCap R) + 2.5) /
          Real.sqrt (2 * t) := div_le_div_of_nonneg_right hN (Real.sqrt_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left hN0 hs2000 hs2t
  -- the `L` term
  have hL1 : lLcP C t ≤ lCapP C R := by
    unfold lLcP lCapP
    rw [OL.log_two_rpow_mul _ _ t ht0, OL.log_two_rpow_mul _ _ t ht0]
    have h1 := mul_le_mul hF1
      (show 7 / 4 * Real.log 2 + 13 / 4 * Real.log t + 80 / 9 ≤
        7 / 4 * Real.log 2 + 13 / 4 * Real.log R + 80 / 9 by linarith)
      (by linarith) hFc0
    linarith
  have hLc0 : 0 ≤ lCapP C R := by
    unfold lCapP
    have := mul_nonneg hFc0
      (show (0 : ℝ) ≤ 7 / 4 * Real.log 2 + 13 / 4 * Real.log R + 80 / 9 by linarith)
    linarith
  have hT2 : lLcP C t / t ≤ lCapP C R / 1000 :=
    calc lLcP C t / t ≤ lCapP C R / t := div_le_div_of_nonneg_right hL1 ht0.le
      _ ≤ lCapP C R / 1000 := div_le_div_of_nonneg_left hLc0 (by norm_num) ht
  have hT3 : 3.2 * Y ^ (-(1 : ℝ) / 6) ≤ 3.2 := by
    have := Real.rpow_le_one_of_one_le_of_nonpos hY (by norm_num : -(1 : ℝ) / 6 ≤ 0)
    linarith
  unfold gYP gCapP
  linarith

/-- `|gYP c05 C (Y,t)| ≤ gCapP c05 C R` (generated from `GS.norm_gYL_le`). -/
theorem norm_gYP_le (c05 C Y t R : ℝ) (hc05 : 0 ≤ c05) (hC : 0 ≤ C) (hY : 3.4e23 ≤ Y)
    (ht : 1000 ≤ t) (htY : t ≤ Y ^ ((1 : ℝ) / 3) / 6) (htR : t ≤ R) :
    ‖gYP c05 C Y t‖ ≤ gCapP c05 C R := by
  rw [Real.norm_eq_abs, abs_of_pos (gYP_pos c05 C Y t hc05 hC
    (lt_of_lt_of_le (by norm_num) hY) (by linarith) htY)]
  exact gYP_le_cap c05 C Y t R hc05 hC (le_trans (by norm_num) hY) ht htY htR

/-- **[GTLIntP] PROVED for `c05, C ≥ 0`** (generated from `GS.gtlInt`). -/
theorem gtlIntP (c05 C : ℝ) (hc05 : 0 ≤ c05) (hC : 0 ≤ C) : GTLIntP c05 C := by
  intro φ hφi y hy r hr hr1
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hr0 : 0 < r := by linarith
  have hl17 := log_gt y hy
  have hK0 : 0 < 1 / MinSp.kK y := by
    unfold MinSp.kK
    have : 0 < Real.log y := by linarith
    positivity
  have hw0 : 0 < max (1 / MinSp.kK y) (1000 / r) := lt_of_lt_of_le hK0 (le_max_left _ _)
  have hm1 : Measurable fun w : ℝ => gYP c05 C (w * y) (w * r) := by
    unfold gYP MinSp.rR lLcP MinSp.bigF
    fun_prop
  have hm2 : Measurable fun w : ℝ => gYP c05 C (w * y) r := by
    unfold gYP MinSp.rR lLcP MinSp.bigF
    fun_prop
  refine ⟨?_, ?_⟩
  · refine Integrable.bdd_mul (c := gCapP c05 C r)
      (hφi.mono_set fun w hw => lt_of_lt_of_le hw0 hw.1.le) hm1.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc fun w hw => ?_)
    have hw0' : 0 < w := lt_trans hw0 hw.1
    have hY : 3.4e23 ≤ w * y := scale_ge y w hy (le_trans (le_max_left _ _) hw.1.le)
    have h1000 : 1000 ≤ w * r := by
      have h := mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) hw.1.le) hr0.le
      rw [div_mul_cancel₀ _ hr0.ne'] at h
      exact h
    have harg := arg_le_r1y y w r hy0 hw0' hr1
    rw [min_eq_left hw.2] at harg
    exact norm_gYP_le c05 C (w * y) (w * r) r hc05 hC hY h1000
      (le_trans harg (r1y_le_third (w * y) hY)) (by nlinarith [hw.2])
  · refine Integrable.bdd_mul (c := gCapP c05 C r)
      (hφi.mono_set fun w (hw : 1 < w) => lt_trans one_pos hw) hm2.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun w hw => ?_)
    have hw1 : 1 < w := hw
    have hY : 3.4e23 ≤ w * y := by nlinarith
    have harg := arg_le_r1y y w r hy0 (lt_trans one_pos hw1) hr1
    rw [min_eq_right hw1.le, one_mul] at harg
    exact norm_gYP_le c05 C (w * y) r r hc05 hC hY (by linarith)
      (le_trans harg (r1y_le_third (w * y) hY)) le_rfl

/-! ## (5) THE HEADLINE -/

/-- **`OP.GorshP c05 C η* φ` from the published and numeric inputs**, for every `c05, C ≥ 0`
(generated from `GS.gorshL_of_open`). OPEN: `OP.MinMainP c05 C`, `RS62Thm15`, `GYMonoP c05 C`,
`HLeGP c05 C`, `Austeria`. Application only. -/
theorem gorshP_of_open (c05 C : ℝ) (hc05 : 0 ≤ c05) (hC : 0 ≤ C) (ηs φ : ℝ → ℝ)
    (hmm : MinMainP c05 C) (h15 : RS62Thm15) (hmo : GYMonoP c05 C) (hhl : HLeGP c05 C)
    (hau : Austeria) : GorshP c05 C ηs φ :=
  gorshP_of_links c05 C hc05 ηs φ hmm (merkel_of_rs62 h15) hmo hhl hau (mellinLe_all ηs φ)
    (gtlIntP c05 C hc05 hC)

end Principia.Common.TernaryGoldbach.GSP
