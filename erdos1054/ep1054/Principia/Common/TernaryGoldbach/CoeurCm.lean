/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.CoeurClosed
import Principia.Common.TernaryGoldbach.CELower

set_option autoImplicit false

/-!
# `CoeurY` at a parametric `c⁻`, and at `c⁻ = −1.39` without the `c_E` enclosure

`CY.CoeurYc` has the denominator `log √x − 1.306476`. `CY.b_le_h` needs `c_E ≥ 1.3325822` for it
only through `−1.306476 ≤ log 2 − log 28 + c_E` (`OC.cminus_le`). Generated from `CY.CoeurYc`,
`CY.b_le_h`, `CY.coeurYc_of_links` by the counted substitution `1.306476 ↦ cm` (three definition
sites, four proof sites). The enclosure becomes the hypothesis `−cm ≤ log 2 − log 28 + c_E`, plus
`cm ≤ 8` to keep the denominator positive (`OS.dh_pos`: `log √x − 1.306476 > 7`).

* `coeurYcm_iff`: `CY.CoeurYc c⁺ = CoeurYcm c⁺ 1.306476` (`Iff.rfl`), so the substitution touched
  nothing else.
* `coeurY139_closed`: `CoeurYcm 2.05315 1.39 η` for EVERY `η` from `EspagnWin 1.36` ALONE. The
  lower bound comes from `CEL.cminus_139` (`c_E ≥ 1.25`, proved), and `BellenG` from
  `PSieve.bellenG` (proved).

Its consumers (the `OstopSpine` composition, `MNumL`'s `hR0C`/`coefC`/`2/(log x − 2cm)`) carry
`1.306476` (and `coefC`'s jump constant `−3.538215 = −2(log(3/8) + c⁺ − (8/15)c⁻)` depends on
it too). Threading `cm = 1.39` through them costs `M̃ +0.0016`, taking it from `0.81849` to
`0.82010` at the corrected minarcs constants, against the weight-aware budget `0.84`.
-/

namespace Principia.Common.TernaryGoldbach.CYm

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open Principia.Common.PSieve (gQ oeArcs BellenG eS)
open Principia.Common.TernaryGoldbach.CY

/-- **`OC.CoeurY` at parametric `c⁺` and `c⁻`**: `CY.CoeurYc` with `1.306476 ↦ cm`. -/
def CoeurYcm (cplus cm : ℝ) (ηp : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ r : ℕ, 150000 ≤ r → (r : ℝ) < MinSp.r1y (x / 49) →
    ∫ α in Set.Ioc (0 : ℝ) 1 ∩ Smooth.arcs 8 (r + 1) (x / 49), ‖OC.s1Sum ηp x α‖ ^ 2 ≤
      (Real.log ((r : ℝ) + 1) + cplus) / (Real.log (Real.sqrt x) - cm) * MinSp.sPr ηp x

/-- **The pin**: `CY.CoeurYc c⁺` IS `CoeurYcm c⁺ 1.306476`. -/
theorem coeurYcm_iff (cplus : ℝ) (ηp : ℝ → ℝ) : CoeurYc cplus ηp ↔ CoeurYcm cplus 1.306476 ηp :=
  Iff.rfl

/-- **[C13] at parametric `c⁻`** (`CY.b_le_h`, `1.306476 ↦ cm`, `OC.cminus_le` + `c_E ≥ 1.3325822`
replaced by `hcmE`). -/
theorem b_le_h_cm (cp cplus cm : ℝ) (hcp0 : 0 ≤ cp) (hcp : Real.log 2 + cp ≤ cplus)
    (hcmE : -cm ≤ Real.log 2 - Real.log 28 + cE) (hcm8 : cm ≤ 8)
    (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (Q₀ : ℝ) (hQ0 : 1 ≤ Q₀) :
    (Real.log (2 * Q₀) + cp) / (Real.log (2 * Real.sqrt (x / 784)) + cE) ≤
      (Real.log Q₀ + cplus) / (Real.log (Real.sqrt x) - cm) := by
  have hx0 := MinSp.x_pos x hx
  have hD := OS.dh_pos x hx
  have hl2 := Real.log_two_gt_d9
  have hlq : 0 ≤ Real.log Q₀ := Real.log_nonneg hQ0
  rw [log_twoQ x hx0, Real.log_mul (by norm_num) (by linarith)]
  have hden : Real.log (Real.sqrt x) - cm ≤
      Real.log 2 + Real.log (Real.sqrt x) - Real.log 28 + cE := by linarith
  have hDpos : 0 < Real.log (Real.sqrt x) - cm := by linarith
  calc (Real.log 2 + Real.log Q₀ + cp) / (Real.log 2 + Real.log (Real.sqrt x) - Real.log 28 + cE)
      ≤ (Real.log 2 + Real.log Q₀ + cp) / (Real.log (Real.sqrt x) - cm) :=
        div_le_div_of_nonneg_left (by linarith) hDpos hden
    _ ≤ (Real.log Q₀ + cplus) / (Real.log (Real.sqrt x) - cm) :=
        div_le_div_of_nonneg_right (by linarith) hDpos.le

/-- **[C13] `CoeurYcm` from the links** (`CY.coeurYc_of_links`, `1.306476 ↦ cm`). -/
theorem coeurYcm_of_links (cp cplus cm : ℝ) (hcp0 : 0 ≤ cp) (hcp : Real.log 2 + cp ≤ cplus)
    (hcmE : -cm ≤ Real.log 2 - Real.log 28 + cE) (hcm8 : cm ≤ 8)
    (hbel : BellenG) (hesp : EspagnWin cp) (ηp : ℝ → ℝ) :
    CoeurYcm cplus cm ηp := by
  intro x hx r hr0 hr
  have hx0 := MinSp.x_pos x hx
  have hD := OS.dh_pos x hx
  have hl2 := Real.log_two_gt_d9
  set Q₀ : ℝ := (r : ℝ) + 1 with hQ₀
  set Q : ℝ := Real.sqrt (x / 784) with hQ
  have hr0R : (150000 : ℝ) ≤ r := by exact_mod_cast hr0
  have hQ01 : 1 ≤ Q₀ := by rw [hQ₀]; linarith
  have hQ0Q : Q₀ ≤ Q := q0_le_q x hx r hr
  have hH0 : 0 ≤ (Real.log Q₀ + cplus) / (Real.log (Real.sqrt x) - cm) :=
    div_nonneg (by linarith [Real.log_nonneg hQ01]) (by linarith)
  have hS0 := MinSp.sPr_nonneg ηp x
  have harc : Set.Ioc (0 : ℝ) 1 ∩ Smooth.arcs 8 (r + 1) (x / 49) =
      Set.Ioc (0 : ℝ) 1 ∩ oeArcs (Q₀ / (2 * Q ^ 2)) Q₀ := by
    rw [OC.arcs_y, arcs_eq_oe, ← h392 _ x hx0]
    push_cast
    rfl
  rw [harc]
  simp_rw [OS.s1Sum_eq]
  by_cases hs : Summable fun n => ‖OS.a1 ηp x n‖
  · set B := (Real.log (2 * Q₀) + cp) / (Real.log (2 * Q) + cE) with hB
    have hBle : B ≤ (Real.log Q₀ + cplus) / (Real.log (Real.sqrt x) - cm) :=
      b_le_h_cm cp cplus cm hcp0 hcp hcmE hcm8 x hx Q₀ hQ01
    have hsupp : ∀ n : ℕ, OS.a1 ηp x n ≠ 0 → ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ 2 * Q →
        Nat.Coprime n m := fun n hn m hm hmQ =>
      a1_coprime ηp x n hn m hm (le_trans hmQ (twoQ_le x))
    have hrat : ∀ q : ℕ, Even q → 1 ≤ q → (q : ℝ) ≤ 2 * Q₀ → ∀ s : ℝ, 1 ≤ s →
        s ≤ 2 * Q₀ / q → gQ q (2 * Q₀ / (s * q)) ≤ B * gQ q (2 * Q / (s * q)) := by
      intro q hqe hq1 hq2 s hs1 hs2
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
      have hsq : 0 < s * q := by positivity
      have hge : 1 ≤ 2 * Q / (s * q) := by
        rw [le_div_iff₀ hsq]
        have : s * q ≤ 2 * Q₀ := by rwa [le_div_iff₀ hq0] at hs2
        linarith
      have hG := Principia.Common.PSieve.one_le_gQ q _ hge
      have h := hesp (2 * Q₀) (2 * Q) (by linarith) (by rw [hQ₀, hQ]; exact win_t x hx r hr)
        (by rw [hQ₀, hQ]; exact win_rho x hx r hr) q hqe hq1 hq2 s hs1 hs2
      rwa [div_le_iff₀ (by linarith)] at h
    have hmain := hbel (OS.a1 ηp x) Q₀ Q B hs hQ01 hQ0Q hsupp hrat
    have hpar : ∫ α in Set.Ioc (0 : ℝ) 1, ‖eS (OS.a1 ηp x) α‖ ^ 2 = MinSp.sPr ηp x := by
      have h := OS.parseval_Ioc (OS.a1 ηp x) hs
      rw [OS.sq_a1] at h
      exact h
    have hmain' : ∫ α in Set.Ioc (0 : ℝ) 1 ∩ oeArcs (Q₀ / (2 * Q ^ 2)) Q₀,
        ‖OS.eSum (OS.a1 ηp x) α‖ ^ 2 ≤ B * MinSp.sPr ηp x := by
      rw [← hpar]
      exact hmain
    exact le_trans hmain' (mul_le_mul_of_nonneg_right hBle hS0)
  · have h0 : ∀ α, OS.eSum (OS.a1 ηp x) α = 0 := OS.eSum_junk _ hs
    simp_rw [h0, norm_zero]
    refine le_trans (le_of_eq ?_) (mul_nonneg hH0 hS0)
    simp

/-- **`CoeurY` at `c⁻ = −1.39` from `EspagnWin 1.36` ALONE**, for every weight: `BellenG` is
`PSieve.bellenG` and the enclosure is `CEL.cminus_139` (`c_E ≥ 1.25`), both proved. -/
theorem coeurY139_closed (hesp : EspagnWin 1.36) (ηp : ℝ → ℝ) : CoeurYcm 2.05315 1.39 ηp :=
  coeurYcm_of_links 1.36 2.05315 1.39 cp136_nonneg OC.cplus_ge CEL.cminus_139 (by norm_num)
    Principia.Common.PSieve.bellenG hesp ηp

end Principia.Common.TernaryGoldbach.CYm
