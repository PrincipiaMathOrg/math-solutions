/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MinPiecesII
import Principia.Common.TernaryGoldbach.TypeIISpineC

set_option autoImplicit false

/-!
# `S_{II}` at the erratum's `κ₇`: `eq:senorburns` with `0.67506 ↦ 0.76746`; `IIArithC` PROVED

`eq:passi` is false (`TypeIISpineC`), so `eq:velib` holds only additively and `κ₇ ↦ κ₇' = 0.1743`
in `eq:vinland1` / `eq:eriksaga` (`T2SC.vin1C`, `T2SC.erikC`). `eq:senorburns`' main-term factor
`√(0.30214 log δ₀q + 0.67506)` came from `κ₆ log(4t)/2 + 2κ₇ = 0.30214 log t + 0.4188549… + 0.2562`;
at `κ₇'` it is `0.30214 log t + 0.4188549… + 0.3486 ≤ 0.30214 log t + 0.76746` (`kap_leC`, slack
`5·10⁻⁶`). So:

* `bIIC` is `MT.bII` with `0.67506 ↦ 0.76746` (the lower-order `2.73908x^{5/6}` is unchanged: the
  `x/√U`, `x/√V` terms of `vin1C`/`erikC` are `vin1`/`erik`'s, so `MPII.vin1_low`/`erik_low` apply);
* `iiArithC : IIArithC` — PROVED, EXACTLY as `MPII.iiArith` (main terms compared exactly);
* `typeIIC_of : Vinland1AtC → EriksagaAtC → IIArithC → RS62Thm15 → TypeIIC` — PROVED.
-/

namespace Principia.Common.TernaryGoldbach.MPIIC

open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPII Principia.Common.TernaryGoldbach.T2SC

/-- **`eq:senorburns` at the erratum's `κ₇`**: `MT.bII` with `0.67506 ↦ 0.76746`. -/
noncomputable def bIIC (Y δ : ℝ) (q : ℕ) : ℝ :=
  Y / Real.sqrt (OC.dz δ * Nat.totient q) *
      (Real.sqrt (cXT Y (OC.dz δ * q) * (Real.log (OC.dz δ * q) + 0.002) +
          Real.log (4 * (OC.dz δ * q)) / 2) *
        Real.sqrt (0.30214 * Real.log (OC.dz δ * q) + 0.76746)) +
    2.73908 * Y ^ ((5 : ℝ) / 6)

/-- **Link [TypeIIC] — `|S_{II}| ≤ bIIC`** at the first choice. -/
def TypeIIC : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 →
    2 * α = a / q + δ / Y → (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) →
    |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) → (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
      ‖sII Y α (uA Y δ q) (vA Y)‖ ≤ bIIC Y δ q

/-- **Link [IIArithC]** — `MPc.IIArith` at `κ₇'`: `vin1C`, `erikC` are at most `bIIC`. -/
def IIArithC : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3) →
    (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
    (q : ℝ) / Nat.totient q ≤ MinSp.bigF (Y ^ ((1 : ℝ) / 3) / 6) →
      (|δ| < 8 → vin1C Y (uA Y δ q) (vA Y) q ≤ bIIC Y δ q) ∧
      (8 ≤ |δ| → erikC Y (uA Y δ q) (vA Y) (3 / 4 * Y ^ ((2 : ℝ) / 3)) δ q ≤ bIIC Y δ q)

/-- `κ₆·log(4t)/2 + 2κ₇' ≤ 0.30214·log t + 0.76746`, and it is `≥ 0`. -/
theorem kap_leC (t : ℝ) (ht : 1 ≤ t) :
    kap6 * (Real.log (4 * t) / 2) + 2 * kap7C ≤ 0.30214 * Real.log t + 0.76746 ∧
      0 ≤ kap6 * (Real.log (4 * t) / 2) + 2 * kap7C := by
  have hl2 := Real.log_two_lt_d9
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht
  have e : Real.log (4 * t) = 2 * Real.log 2 + Real.log t := by
    rw [Real.log_mul (by norm_num) (by linarith), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]; push_cast; ring
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold kap6 kap7C
  rw [e]
  constructor <;> nlinarith


/-- **`eq:vinland1`'s main term ≤ `eq:senorburns`'s** (`|δ| < 8`, `δ₀ = 2`). -/
theorem vin1_mainC (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (h8 : |δ| < 8) :
    Y / Real.sqrt (2 * Nat.totient q) *
        Real.sqrt ((Real.log (Y / (uA Y δ q * vA Y)) + Real.log (2 * q) *
            Real.log (1 + Real.log (Y / (uA Y δ q * vA Y)) / Real.log (vA Y / (2 * q)))) *
          (kap6 * Real.log (Y / (uA Y δ q * vA Y)) + 2 * kap7C)) ≤
      Y / Real.sqrt (OC.dz δ * Nat.totient q) *
        (Real.sqrt (cXT Y (OC.dz δ * q) * (Real.log (OC.dz δ * q) + 0.002) +
            Real.log (4 * (OC.dz δ * q)) / 2) *
          Real.sqrt (0.30214 * Real.log (OC.dz δ * q) + 0.76746)) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hdz : OC.dz δ = 2 := max_eq_left (by linarith)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hC0 := cXT_nonneg' Y δ q hY hq hdq hy
  have htx : OC.dz δ * q ≤ Y ^ ((1 : ℝ) / 3) / 3 := dz_q_le δ _ q hdq hy
  rw [logxUV Y δ q hY0 hq]
  rw [hdz] at hC0 htx ⊢
  have hc : 0 < Y ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hY0 _
  set t := (2 : ℝ) * q with ht_def
  have ht1 : 1 ≤ t := by rw [ht_def]; linarith
  -- the `log(1 + ·)` factor
  have hD : 9 * Y ^ ((1 : ℝ) / 3) / (2.004 * t) ≤ vA Y / (2 * q) := by
    unfold vA
    rw [← ht_def, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hlp := log1p_le Y t _ hY0 ht1 htx hD
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlog2q : Real.log (2 * q) = Real.log t := by rw [ht_def]
  have hl4 : 0 ≤ Real.log (4 * t) := Real.log_nonneg (by linarith)
  have hlog1p0 : 0 ≤ Real.log (1 + Real.log (4 * t) / 2 / Real.log (vA Y / (2 * q))) := by
    apply Real.log_nonneg
    have : 0 < Real.log (vA Y / (2 * q)) := by
      have h13 : 13.47 ≤ 9 * Y ^ ((1 : ℝ) / 3) / (2.004 * t) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      exact Real.log_pos (by linarith)
    have := div_nonneg (div_nonneg hl4 (by norm_num : (0 : ℝ) ≤ 2)) this.le
    linarith
  have hA : Real.log (4 * t) / 2 + Real.log (2 * q) *
      Real.log (1 + Real.log (4 * t) / 2 / Real.log (vA Y / (2 * q))) ≤
      cXT Y t * (Real.log t + 0.002) + Real.log (4 * t) / 2 := by
    rw [hlog2q]
    nlinarith [mul_le_mul_of_nonneg_left hlp hlt]
  have hA0 : 0 ≤ Real.log (4 * t) / 2 + Real.log (2 * q) *
      Real.log (1 + Real.log (4 * t) / 2 / Real.log (vA Y / (2 * q))) := by
    rw [hlog2q]; positivity
  obtain ⟨hB, hB0⟩ := kap_leC t ht1
  rw [Real.sqrt_mul hA0]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)


/-- **`eq:eriksaga`'s main term ≤ `eq:senorburns`'s** (`|δ| ≥ 8`, `δ₀ = |δ|/4`). -/
theorem erik_mainC (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (h8 : 8 ≤ |δ|) :
    2 * Y / Real.sqrt (|δ| * Nat.totient q) *
        Real.sqrt (Real.log (Y / (uA Y δ q * vA Y)) +
          Real.log (|δ| * q * (1 + Y / (2 * uA Y δ q * (3 / 4 * Y ^ ((2 : ℝ) / 3)))) / 4) *
            Real.log (1 + Real.log (Y / (uA Y δ q * vA Y)) /
              Real.log (4 * vA Y / (|δ| * (1 + Y / (2 * uA Y δ q * (3 / 4 * Y ^ ((2 : ℝ) / 3)))) *
                q)))) *
        Real.sqrt (kap6 * Real.log (Y / (uA Y δ q * vA Y)) + 2 * kap7C) ≤
      Y / Real.sqrt (OC.dz δ * Nat.totient q) *
        (Real.sqrt (cXT Y (OC.dz δ * q) * (Real.log (OC.dz δ * q) + 0.002) +
            Real.log (4 * (OC.dz δ * q)) / 2) *
          Real.sqrt (0.30214 * Real.log (OC.dz δ * q) + 0.76746)) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hdz : OC.dz δ = |δ| / 4 := max_eq_right (by linarith)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hC0 := cXT_nonneg' Y δ q hY hq hdq hy
  have htx : OC.dz δ * q ≤ Y ^ ((1 : ℝ) / 3) / 3 := dz_q_le δ _ q hdq hy
  obtain ⟨he0, he⟩ := eps1_le Y δ q hY hq hdq hy
  have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  rw [logxUV Y δ q hY0 hq]
  rw [hdz] at hC0 htx ⊢
  set e1 := Y / (2 * uA Y δ q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) with he1_def
  set t := |δ| / 4 * q with ht_def
  have ht2 : 2 ≤ t := by rw [ht_def]; nlinarith
  have ht1 : 1 ≤ t := by linarith
  have hc : 0 < Y ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hY0 _
  -- the prefactor: `2x/√(|δ|φ) = x/√((|δ|/4)φ)`
  have hpre : 2 * Y / Real.sqrt (|δ| * Nat.totient q) =
      Y / Real.sqrt (|δ| / 4 * Nat.totient q) := by
    have e : |δ| * Nat.totient q = 4 * (|δ| / 4 * Nat.totient q) := by ring
    rw [e, Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    have : 0 < Real.sqrt (|δ| / 4 * Nat.totient q) := Real.sqrt_pos.mpr (by positivity)
    field_simp
  rw [hpre]
  -- the arguments, in terms of `t`
  have harg1 : |δ| * q * (1 + e1) / 4 = t * (1 + e1) := by rw [ht_def]; ring
  have harg2 : 4 * vA Y / (|δ| * (1 + e1) * q) = vA Y / (t * (1 + e1)) := by
    rw [ht_def]; field_simp
  rw [harg1, harg2]
  have hD : 9 * Y ^ ((1 : ℝ) / 3) / (2.004 * t) ≤ vA Y / (t * (1 + e1)) := by
    unfold vA
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hct : 0 ≤ Y ^ ((1 : ℝ) / 3) * t := by positivity
    have := mul_le_mul_of_nonneg_left he hct
    nlinarith
  have hlp := log1p_le Y t _ hY0 ht1 htx hD
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hl4 : 0 ≤ Real.log (4 * t) := Real.log_nonneg (by linarith)
  have hlte : Real.log (t * (1 + e1)) ≤ Real.log t + 0.002 := by
    rw [Real.log_mul (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + e1 by linarith)
    linarith
  have hlte0 : 0 ≤ Real.log (t * (1 + e1)) := Real.log_nonneg (by nlinarith)
  have hlog1p0 : 0 ≤ Real.log (1 + Real.log (4 * t) / 2 / Real.log (vA Y / (t * (1 + e1)))) := by
    apply Real.log_nonneg
    have : 0 < Real.log (vA Y / (t * (1 + e1))) := by
      have h13 : 13.47 ≤ 9 * Y ^ ((1 : ℝ) / 3) / (2.004 * t) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      exact Real.log_pos (by linarith)
    have := div_nonneg (div_nonneg hl4 (by norm_num : (0 : ℝ) ≤ 2)) this.le
    linarith
  have hA : Real.log (4 * t) / 2 + Real.log (t * (1 + e1)) *
      Real.log (1 + Real.log (4 * t) / 2 / Real.log (vA Y / (t * (1 + e1)))) ≤
      cXT Y t * (Real.log t + 0.002) + Real.log (4 * t) / 2 := by
    have h1 := mul_le_mul hlte hlp hlog1p0 (by linarith)
    nlinarith
  obtain ⟨hB, hB0⟩ := kap_leC t ht1
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

/-- **`IIArithC`, PROVED** (`MPII.iiArith` at `κ₇'`). -/
theorem iiArithC : IIArithC := by
  intro Y hY δ q hq hdq hy hF
  constructor
  · intro h8
    have hm := vin1_mainC Y δ q hY hq hdq hy h8
    have hl := vin1_low Y δ q hY hq hdq hy hF h8
    unfold vin1C bIIC
    linarith
  · intro h8
    have hm := erik_mainC Y δ q hY hq hdq hy h8
    have hl := erik_low Y δ q hY hq hdq hy hF h8
    unfold erikC bIIC
    linarith

/-- **`TypeIIC` from its links, PROVED** (`MPc.typeII_of` at `κ₇'`; `lem:merkel` from
`GS.merkel_of_rs62`). -/
theorem typeIIC_of (hv : Vinland1AtC) (he : EriksagaAtC) (ha : IIArithC) (h15 : GS.RS62Thm15) :
    TypeIIC := by
  intro Y hY α δ a q hq hg h2 hQ hδ hy
  have hY0 : (0 : ℝ) < Y := by linarith
  have hdq := adm_dq Y δ q hY0 hq hδ
  have hF : (q : ℝ) / Nat.totient q ≤ MinSp.bigF (Y ^ ((1 : ℝ) / 3) / 6) :=
    (GS.merkel_of_rs62 h15 q hq _ (y_ge Y hY) hy).le
  obtain ⟨hs, hl⟩ := ha Y hY δ q hq hdq hy hF
  rcases lt_or_ge |δ| 8 with h8 | h8
  · exact (hv Y hY α δ a q hq hg h2 hQ hδ hy).trans (hs h8)
  · exact (he Y hY α δ a q hq hg h2 hQ hδ hy h8).trans (hl h8)

end Principia.Common.TernaryGoldbach.MPIIC
