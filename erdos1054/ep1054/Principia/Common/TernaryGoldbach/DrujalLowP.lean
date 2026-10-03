/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.SFloor
import Principia.Common.TernaryGoldbach.DrujalSpine

set_option autoImplicit false

/-!
# The lower half of `lem:drujal` at `S(r) ≥ 6.76`: `J/x ≥ 8.57476` (`DrujalLowP`)

A GENERATED sibling of the lower half of `DrujalSpine.lean` (`scratchpad/sfloor/gen_lowp.py`:
every name and constant rewritten by counted substitution, then asserted absent). The ONLY change
is the arithmetic: `DS.sR_ge : 6.5942 ≤ S` is replaced by `SF.sR_ge_sharp : 6.76 ≤ S`, so

    J/x ≥ 2·6.76·0.6397018 − 0.0740045 − 1.8·10⁻⁸ − 10⁻⁶ = 8.5747628 ≥ 8.57476

(`jArithP`; the same `|η∘|₂² − band − tail ≥ 0.6397018` and the same aggregates). The link
`DrujalLowP` is `DS.DrujalLowD` with the floor `8.36` raised to `8.57476`, every hypothesis
unchanged; `drujalLowP_of_spine` produces it from the SAME five spine links (`DS.PerArc`,
`DS.ArcInt`, `DS.BandQ`, `DS.TailQ`, `DS.KSmall`) — application only. It is STRONGER than
`DS.DrujalLowD` (`drujalLowD_of_P`) and weaker than `MinW.DrujalLowE` (`drujalLowP_of_lowE`,
floor `8.613`).

At `J ≥ 8.57476x`, `E ≤ 8.4031·10⁻¹²x` the minor-arc floor is
`p = (√J − √E)²/x ≥ (√8.57476 − √8.4031·10⁻¹²)² = 8.5747430`, proved as `≥ 8.57474` (`je_le_p`;
`DS.je_le_d` had `8.3599`).
-/

namespace Principia.Common.TernaryGoldbach.SF

open MeasureTheory

/-- **Link [J] at `|η|₁ ≤ 0.8673`, floor `8.57476`** — `MinW.DrujalLowE` with `|η|₁ ≤ 0.8673` for
`1.2` and `J/x ≥ 8.57476` for `8.613` (every other hypothesis unchanged). IMPLIED by
`MinW.DrujalLowE` (`drujalLowP_of_lowE`); PRODUCED by the spine (`drujalLowP_of_spine`), which
uses only `|η|₁`, `|η∘|₂ ≥ 0.8`, `|η − η∘|₂`, `|η∘'''|₁` and the two `err` bounds. -/
def DrujalLowP (η ηo : ℝ → ℝ) : Prop :=
  MemLp η 1 (volume.restrict (Set.Ioi 0)) → (∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955) →
    MajSp.l1 η ≤ 0.8673 →
    (∃ S : Finset ℝ, ∀ t : ℝ, 0 ≤ t → t ∉ S → ContDiffAt ℝ 3 ηo t) →
    Integrable (iteratedDeriv 3 ηo) (volume.restrict (Set.Ioi 0)) →
    MemLp ηo 2 (volume.restrict (Set.Ioi 0)) →
    0.8 ≤ MajSp.l2 ηo → MajSp.l2 ηo ≤ 0.8002 →
    MajSp.l2 (fun t => η t - ηo t) ≤ 1.7999e-4 → MajSp.l1 (iteratedDeriv 3 ηo) ≤ 40 →
    ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → MajSp.ETBound η 600000 x 1.1377e-8 →
      MajSp.EBound η x 2.3921e-8 → 8.57476 ≤ MajSp.amaj η x

/-- **The lower arithmetic — THE NEW `J` CONSTANT**: at `S ≥ 6.76`, `|η∘|₂ ≥ 0.8`,
`|η − η∘|₂ ≤ 1.7999·10⁻⁴`, `|η∘'''|₁ ≤ 40`, `|η|₁ ≤ 0.8673`, `nagS ≤ 3.125`, `harmS ≤ 25.84`,
`K ≤ 10⁻⁶`: `2S(|η∘|₂² − band − tail) − aggregates ≥ 2·6.76·0.6397018 − 0.0740045 − … =
8.5747628 ≥ 8.57476`. -/
theorem jArithP (S lo d l3 l1 nag harm K : ℝ) (hS : 6.76 ≤ S) (hlo : 0.8 ≤ lo) (hd0 : 0 ≤ d)
    (hd : d ≤ 1.7999e-4) (hl30 : 0 ≤ l3) (hl3 : l3 ≤ 40) (hl10 : 0 ≤ l1) (hl1 : l1 ≤ 0.8673)
    (hn : nag ≤ 3.125) (hh : harm ≤ 25.84) (hK : K ≤ 1e-6) :
    8.57476 ≤ 2 * S * (lo ^ 2 - (2 * lo * d + d ^ 2) - l3 ^ 2 / (163840 * Real.pi ^ 6)) -
      (1200000 * nag * (1.1377e-8 * (2 * l1 + 1.1377e-8)) +
        1200000 * harm * (2.3921e-8) ^ 2 + K) := by
  have hpi : (3.141592 : ℝ) ^ 6 ≤ Real.pi ^ 6 :=
    pow_le_pow_left₀ (by norm_num) Real.pi_gt_d6.le 6
  have hc3 : l3 ^ 2 / (163840 * Real.pi ^ 6) ≤ 40 ^ 2 / (163840 * (3.141592 : ℝ) ^ 6) :=
    div_le_div₀ (by norm_num) (pow_le_pow_left₀ hl30 hl3 2) (by norm_num) (by linarith)
  have n3 : 40 ^ 2 / (163840 * (3.141592 : ℝ) ^ 6) ≤ 1.01579e-5 := by norm_num
  have hband : 0.64 - 1.6 * d - d ^ 2 ≤ lo ^ 2 - (2 * lo * d + d ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (by linarith : (0 : ℝ) ≤ lo + 0.8 - 2 * d)]
  have hdd : d ^ 2 ≤ (1.7999e-4) ^ 2 := pow_le_pow_left₀ hd0 hd 2
  have hg : 0.6397018 ≤ lo ^ 2 - (2 * lo * d + d ^ 2) - l3 ^ 2 / (163840 * Real.pi ^ 6) := by
    linarith
  have hmain : 2 * 6.76 * 0.6397018 ≤
      2 * S * (lo ^ 2 - (2 * lo * d + d ^ 2) - l3 ^ 2 / (163840 * Real.pi ^ 6)) :=
    mul_le_mul (by linarith) hg (by norm_num) (by linarith)
  have hT : 1.1377e-8 * (2 * l1 + 1.1377e-8) ≤ 1.1377e-8 * (2 * 0.8673 + 1.1377e-8) := by
    linarith
  have hT0 : 0 ≤ 1.1377e-8 * (2 * l1 + 1.1377e-8) := by positivity
  have h2 : nag * (1.1377e-8 * (2 * l1 + 1.1377e-8)) ≤
      3.125 * (1.1377e-8 * (2 * 0.8673 + 1.1377e-8)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) hT0]
  have h3 : harm * (2.3921e-8) ^ 2 ≤ 25.84 * (2.3921e-8) ^ 2 :=
    mul_le_mul_of_nonneg_right hh (by norm_num)
  linarith

/-- The closing step of the lower half: `|A − L| ≤ R`, `U ≤ L`, `8.57476 ≤ U − R` give
`8.57476 ≤ A`. -/
theorem lower_closeP (A L U R : ℝ) (hj : |A - L| ≤ R) (hL : U ≤ L) (ha : 8.57476 ≤ U - R) :
    8.57476 ≤ A := by
  have h := (abs_le.mp hj).1
  linarith

/-- **`DrujalLowP` FROM THE SPINE**: `eq:juto` (`PerArc`, `ArcInt`), the lower half before
`eq:marmo` (`BandQ`, `TailQ`), the `K` aggregate (`KSmall`), the proved arithmetic
(`S ≥ 6.76`, `nagS ≤ 3.125`, `harmS ≤ 25.84`; `jArithP`). Application only. -/
theorem drujalLowP_of_spine (η ηo : ℝ → ℝ) (pa : DS.PerArc η) (ai : DS.ArcInt η)
    (bq : DS.BandQ η ηo) (tq : DS.TailQ ηo) (ks : DS.KSmall η) : DrujalLowP η ηo :=
  fun _ _ hl1 _ _ _ hlo1 _ hdiff hl3 x hx hT hE =>
    lower_closeP _ _ _ _ (DS.juto η pa ai x hx (ks x hx).1 _ _ hT hE) (DS.lRD_ge η ηo bq tq)
      (jArithP DS.sR (MajSp.l2 ηo) (MajSp.l2 (fun t => η t - ηo t)) (MajSp.l1 (iteratedDeriv 3 ηo))
        (MajSp.l1 η) DS.nagS DS.harmS (DS.kAgg η x) sR_ge_sharp hlo1 (MajSp.l2_nonneg _) hdiff
        (MajSp.l1_nonneg _) hl3 (MajSp.l1_nonneg _) hl1 DS.nagS_le DS.harmS_le' (ks x hx).2)

/-- **`MinW.DrujalLowE → DrujalLowP`**: stronger `|η|₁` hypothesis, weaker conclusion. -/
theorem drujalLowP_of_lowE (η ηo : ℝ → ℝ) (h : MinW.DrujalLowE η ηo) : DrujalLowP η ηo :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 x hx hT hE =>
    le_trans (by norm_num) (h h1 h2 (le_trans h3 (by norm_num)) h4 h5 h6 h7 h8 h9 h10 x hx hT hE)

/-- **`DrujalLowP → DS.DrujalLowD`**: the same hypotheses, the higher floor `8.57476 ≥ 8.36`. -/
theorem drujalLowD_of_P (η ηo : ℝ → ℝ) (h : DrujalLowP η ηo) : DS.DrujalLowD η ηo :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 x hx hT hE =>
    le_trans (by norm_num) (h h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 x hx hT hE)

/-- **`eq:je` at the new floor**: `J ≥ 8.57476x`, `E ≤ 8.4031·10⁻¹²x` give `(√J − √E)² ≥ 8.57474x`
(`(√8.57476 − √8.4031·10⁻¹²)² = 8.5747430`). Generated from `DS.je_le_d`. -/
theorem je_le_p (J E x : ℝ) (hx : 0 ≤ x) (hJ : 8.57476 * x ≤ J) (hE : E ≤ 8.4031e-12 * x) :
    8.57474 * x ≤ (Real.sqrt J - Real.sqrt E) ^ 2 := by
  have ha := Real.sqrt_le_sqrt hJ
  have he := Real.sqrt_le_sqrt hE
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8.57476)] at ha
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8.4031e-12)] at he
  have hu0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hux : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have ha2 : Real.sqrt 8.57476 ^ 2 = 8.57476 := Real.sq_sqrt (by norm_num)
  have hc2 : Real.sqrt 8.4031e-12 ^ 2 = 8.4031e-12 := Real.sq_sqrt (by norm_num)
  have ha0 : 0 ≤ Real.sqrt 8.57476 := Real.sqrt_nonneg _
  have hc0 : 0 ≤ Real.sqrt 8.4031e-12 := Real.sqrt_nonneg _
  have ha3 : Real.sqrt 8.57476 ≤ 3 := by nlinarith
  have ha1 : 2 ≤ Real.sqrt 8.57476 := by nlinarith
  have hc3 : Real.sqrt 8.4031e-12 ≤ 3e-6 := by nlinarith
  have hd : (Real.sqrt 8.57476 - Real.sqrt 8.4031e-12) * Real.sqrt x ≤
      Real.sqrt J - Real.sqrt E := by nlinarith
  have hd0 : 0 ≤ (Real.sqrt 8.57476 - Real.sqrt 8.4031e-12) * Real.sqrt x :=
    mul_nonneg (by linarith) hu0
  have hsq := pow_le_pow_left₀ hd0 hd 2
  have hk : 8.57474 ≤ (Real.sqrt 8.57476 - Real.sqrt 8.4031e-12) ^ 2 := by nlinarith
  have hm : 8.57474 * x ≤ ((Real.sqrt 8.57476 - Real.sqrt 8.4031e-12) * Real.sqrt x) ^ 2 := by
    rw [mul_pow, hux]
    exact mul_le_mul_of_nonneg_right hk hx
  linarith

end Principia.Common.TernaryGoldbach.SF
