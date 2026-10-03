/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MinPiecesArith
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

/-!
# `MPc.I1Arith` PROVED: the Totals algebra of `S_{I,1}`

`MPc.Bostb1At` bounds `|S_{I,1}|` by the CORRECTED `eq:cupcake2 + eq:kuche2` of `lem:bostb1` at the
first choice `D = U = x^{2/3}/(9√(qδ₀))`. `i1Arith` proves that this, with the three cited μ-sum
bounds, is at most `MMP.bI1W` (`eq:therwald` with `min(1, 4c₀'/δ²)`), for every admissible
`(x, δ, q)`:

* **main term** (`i1_main`): `(x/2q)·min(1, c₀/(πδ)²)·|s₁| + (x/2q)·min(2 − log 4, …)·|s₀|
  ≤ (x/q)·min(1, 4c₀'/δ²)·(q/φ(q))·(7/4·log δ₀q + 6.11676)`, split on `ℓ = log(U/(2q²)) ≥ 1.6`
  (`eq:ronsard` applies) or not (`eq:grara`), with `log(x/U) = ℓ/2 + log 9√18 + log q
  + (3/4)log δ₀q` (`lYU_eq`); the corrected `x/2q` meets `2q/φ(2q) ≤ 2q/φ(q)` (`R2_le`). It
  closes with slack: `0.875·log δ₀q + 4.28` against `1.75·log δ₀q + 6.117`.
* **lower order** (`i1_low`): with `u = x^{1/6}`, `λ = log u`, `s = √(δ₀q)`: every `eq:kuche2` and
  `O*` term is bounded by an explicit polynomial in `u, λ`; `(3c₁/2)(x/q)log⁺(D/(c₂x/q))log(q/c₂)`
  VANISHES at the first choice (`D q/(c₂x) < 1`), and `max(1, log(c₀e³q²/(4π|η'|₁x))) = 1`.

Scoped max ratio of the whole `I1Arith` left side to `bI1W`: `0.519`
(`scratchpad/minpieces/i1arith.py`).
-/

namespace Principia.Common.TernaryGoldbach.MPI1

open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPA

/-! ## (1) Constants -/

theorem pi_sq_bounds : 9.8696 < Real.pi ^ 2 ∧ Real.pi ^ 2 < 9.869607 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  constructor <;> nlinarith

theorem sqrt_c0 : 5.61435 ≤ Real.sqrt c0 ∧ Real.sqrt c0 ≤ 5.61436 := by
  unfold c0
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

theorem c2_bounds : 0.6714 ≤ c2 ∧ c2 ≤ 0.6715 := by
  obtain ⟨h1, h2⟩ := sqrt_c0
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  unfold c2
  constructor
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

theorem eta1_bounds : 5.5451 ≤ eta1 ∧ eta1 ≤ 5.5452 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  unfold eta1
  constructor <;> linarith

/-- `min(1, c₀/(πδ)²) ≤ min(1, 4c₀'/δ²)`: `c₀/π² ≤ 4·0.798437`. -/
theorem cap1_le (δ : ℝ) : capM (c0 / Real.pi ^ 2) δ ≤ capM (4 * 0.798437) δ := by
  obtain ⟨h1, -⟩ := pi_sq_bounds
  apply MMP.capM_mono _ _ δ (by unfold c0; positivity)
  unfold c0
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **`min(2 − log 4, 96 log 2/(π²δ²)) ≤ 2.1111·min(1, 4c₀'/δ²)`** (`c₃,I = c₀''/c₀'`). -/
theorem capL_le (δ : ℝ) :
    (2 - Real.log 4) * capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ ≤
      2.1111 * capM (4 * 0.798437) δ := by
  obtain ⟨hp1, -⟩ := pi_sq_bounds
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have ha : 0.6137 ≤ 2 - Real.log 4 := by rw [hl4]; linarith
  have ha' : 2 - Real.log 4 ≤ 0.6138 := by rw [hl4]; linarith
  set a := 2 - Real.log 4 with ha_def
  set c' := 96 * Real.log 2 / Real.pi ^ 2 with hc'
  have hc'le : c' ≤ 6.74214 := by
    rw [hc', div_le_iff₀ (by positivity)]; nlinarith
  have hc'0 : 0 < c' := by rw [hc']; positivity
  have hca : 0 < c' / a := div_pos hc'0 (by linarith)
  unfold capM
  have hm1 : 0 < max (c' / a) (δ ^ 2) := lt_of_lt_of_le hca (le_max_left _ _)
  have hm2 : 0 < max (4 * 0.798437) (δ ^ 2) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  rcases le_total (δ ^ 2) (4 * 0.798437) with h | h
  · rw [max_eq_left h]
    have : c' / a / max (c' / a) (δ ^ 2) ≤ 1 := div_le_one_of_le₀ (le_max_left _ _) hm1.le
    have hpos : 0 ≤ c' / a / max (c' / a) (δ ^ 2) := div_nonneg hca.le hm1.le
    have e : 2.1111 * (4 * 0.798437 / (4 * 0.798437)) = (2.1111 : ℝ) := by norm_num
    rw [e]
    nlinarith
  · rw [max_eq_right h]
    have e1 : a * (c' / a / max (c' / a) (δ ^ 2)) = c' / max (c' / a) (δ ^ 2) := by
      field_simp
    rw [e1]
    have hd : 0 < δ ^ 2 := lt_of_lt_of_le (by norm_num) h
    calc c' / max (c' / a) (δ ^ 2) ≤ c' / δ ^ 2 :=
          div_le_div_of_nonneg_left hc'0.le hd (le_max_right _ _)
      _ ≤ 2.1111 * (4 * 0.798437 / δ ^ 2) := by
          rw [← mul_div_assoc]
          exact div_le_div_of_nonneg_right (by linarith) hd.le

/-- `2q/φ(2q) ≤ 2·(q/φ(q))` (`φ(q) ∣ φ(2q)`). -/
theorem R2_le (q : ℕ) (hq : 1 ≤ q) :
    ((2 * q : ℕ) : ℝ) / Nat.totient (2 * q) ≤ 2 * ((q : ℝ) / Nat.totient q) := by
  have hφ : Nat.totient q ≤ Nat.totient (2 * q) :=
    Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) (Nat.totient_dvd_of_dvd (dvd_mul_left q 2))
  have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφR : (Nat.totient q : ℝ) ≤ Nat.totient (2 * q) := by exact_mod_cast hφ
  push_cast
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_left (by positivity) hφ0 hφR

/-- `q/φ(q) ≥ 1`. -/
theorem r_ge_one (q : ℕ) (hq : 1 ≤ q) : 1 ≤ (q : ℝ) / Nat.totient q := by
  have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  rw [le_div_iff₀ hφ0, one_mul]
  exact_mod_cast Nat.totient_le q

/-! ## (2) The main term -/

/-- **The main-term algebra, abstractly.** -/
theorem i1_main (Y q r R2 cap1 capL cap4 lYU ell logt s0 s1 : ℝ) (hY : 0 ≤ Y) (hq : 0 < q)
    (hr1 : 1 ≤ r) (hR2 : R2 ≤ 2 * r) (hc1 : 0 ≤ cap1) (hc14 : cap1 ≤ cap4)
    (hcL4 : capL ≤ 2.1111 * cap4) (hlt : 0 ≤ logt)
    (hlYU : lYU ≤ ell / 2 + 3.6425 + 1.75 * logt) (hlYU0 : 0 ≤ lYU) (hs0 : |s0| ≤ 1)
    (hron : 1.6 ≤ ell → |s0| ≤ 4 / 5 * R2 / ell) (hmep : |s1 - lYU * s0| ≤ 1.00303 * R2) :
    Y / (2 * q) * cap1 * |s1| + Y / (2 * q) * capL * |s0| ≤
      Y / q * cap4 * r * (7 / 4 * logt + 6.11676) := by
  have hs1 : |s1| ≤ lYU * |s0| + 1.00303 * R2 := by
    have h1 : |s1| ≤ |s1 - lYU * s0| + |lYU * s0| := by
      have := abs_add_le (s1 - lYU * s0) (lYU * s0)
      rwa [sub_add_cancel] at this
    rw [abs_mul, abs_of_nonneg hlYU0] at h1
    linarith
  have hc40 : 0 ≤ cap4 := le_trans hc1 hc14
  have hs00 : 0 ≤ |s0| := abs_nonneg s0
  -- `X := (lYU + 2.1111)|s0| + 1.00303R2 ≤ 2r(7/4 logt + 6.11676)`
  have hX : (lYU + 2.1111) * |s0| + 1.00303 * R2 ≤ 2 * r * (7 / 4 * logt + 6.11676) := by
    have hR2' : 1.00303 * R2 ≤ 2.00606 * r := by linarith
    by_cases hell : 1.6 ≤ ell
    · have hb := hron hell
      have hell0 : 0 < ell := by linarith
      have hb' : |s0| ≤ 1.6 * r / ell := by
        refine hb.trans ?_
        rw [div_le_div_iff_of_pos_right hell0]
        linarith
      have hY1 : (lYU + 2.1111) * |s0| ≤ (ell / 2 + 5.7536 + 1.75 * logt) * (1.6 * r / ell) :=
        mul_le_mul (by linarith) hb' hs00 (by linarith)
      have e : (ell / 2 + 5.7536 + 1.75 * logt) * (1.6 * r / ell) =
          0.8 * r + (5.7536 + 1.75 * logt) * r * (1.6 / ell) := by
        field_simp
        ring
      have h16 : 1.6 / ell ≤ 1 := by rw [div_le_one hell0]; exact hell
      have h16' : 0 ≤ 1.6 / ell := by positivity
      have hp : (5.7536 + 1.75 * logt) * r * (1.6 / ell) ≤ (5.7536 + 1.75 * logt) * r :=
        mul_le_of_le_one_right (by positivity) h16
      nlinarith
    · have hell' : ell < 1.6 := lt_of_not_ge hell
      have hY1 : (lYU + 2.1111) * |s0| ≤ lYU + 2.1111 :=
        mul_le_of_le_one_right (by linarith) hs0
      nlinarith
  have hq2 : 0 ≤ Y / (2 * q) := by positivity
  have e1 : Y / (2 * q) * cap1 * |s1| ≤ Y / (2 * q) * cap4 * (lYU * |s0| + 1.00303 * R2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hc14 hq2) hs1 (abs_nonneg _) (by positivity)
  have e2 : Y / (2 * q) * capL * |s0| ≤ Y / (2 * q) * (2.1111 * cap4) * |s0| :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcL4 hq2) hs00
  have e3 : Y / (2 * q) * cap4 * ((lYU + 2.1111) * |s0| + 1.00303 * R2) ≤
      Y / (2 * q) * cap4 * (2 * r * (7 / 4 * logt + 6.11676)) :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have e4 : Y / (2 * q) * cap4 * (2 * r * (7 / 4 * logt + 6.11676)) =
      Y / q * cap4 * r * (7 / 4 * logt + 6.11676) := by
    field_simp
  nlinarith

/-- **`log(x/U) = ℓ/2 + log 9 + (1/2)log 18 + log q + (3/4)log t`**, `ℓ = log(U/q/(2q))`,
`t = δ₀q`, `U = x^{2/3}/(9√t)`. -/
theorem lYU_eq (Y δ : ℝ) (q : ℕ) (hY0 : 0 < Y) (hq : 1 ≤ q) :
    Real.log (Y / uA Y δ q) = Real.log (uA Y δ q / q / ((2 * q : ℕ) : ℝ)) / 2 +
      Real.log 9 + Real.log 18 / 2 + Real.log q + 3 / 4 * Real.log (OC.dz δ * q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hd := dz_ge δ
  have ht : 0 < OC.dz δ * q := by positivity
  have hU := uA_pos Y δ q hY0 hq
  have hlU : Real.log (uA Y δ q) = 2 / 3 * Real.log Y - Real.log 9 -
      Real.log (OC.dz δ * q) / 2 := by
    unfold uA
    rw [Real.log_div (Real.rpow_pos_of_pos hY0 _).ne' (by positivity), Real.log_rpow hY0,
      Real.log_mul (by norm_num) (Real.sqrt_pos.mpr ht).ne', Real.log_sqrt ht.le]
    ring
  have h18 : Real.log 18 = Real.log 2 + Real.log 9 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [Real.log_div hY0.ne' hU.ne', Real.log_div (div_pos hU hqR).ne' (by positivity),
    Real.log_div hU.ne' hqR.ne', hlU, h18, Real.log_mul (by positivity) (by positivity)]
  push_cast
  rw [Real.log_mul (by norm_num) hqR.ne']
  ring

/-- `log(x/U) ≤ ℓ/2 + 3.6425 + 1.75·log t`, and `log(x/U) ≥ 0`. -/
theorem lYU_le (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    Real.log (Y / uA Y δ q) ≤ Real.log (uA Y δ q / q / ((2 * q : ℕ) : ℝ)) / 2 + 3.6425 +
      1.75 * Real.log (OC.dz δ * q) ∧ 0 ≤ Real.log (Y / uA Y δ q) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd := dz_ge δ
  have hl3 := MN.log3_le
  have hl2 := Real.log_two_lt_d9
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h18 : Real.log 18 = Real.log 2 + 2 * Real.log 3 := by
    rw [show (18 : ℝ) = 2 * 3 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; norm_num
  have hlq : Real.log q ≤ Real.log (OC.dz δ * q) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hqR
  constructor
  · rw [lYU_eq Y δ q hY0 hq, h9, h18]
    linarith
  · have hU1 : uA Y δ q ≤ Y := by
      have h1 := uA_mul_vA Y δ q hY hq hdq hy
      have hU := uA_pos Y δ q hY0 hq
      have hV : 1 ≤ vA Y := by
        unfold vA
        obtain ⟨-, -, e13, -, -⟩ := rpow_facts Y hY0
        have hu := u_ge Y hY
        rw [e13]; nlinarith
      nlinarith
    exact Real.log_nonneg (by rw [le_div_iff₀ (uA_pos Y δ q hY0 hq)]; linarith)

/-! ## (3) The lower-order terms -/

/-- `c₁(x, U) ≤ 1.000001` at the first choice. -/
theorem c1_le (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    1 ≤ c1 Y (uA Y δ q) ∧ c1 Y (uA Y δ q) ≤ 1.000001 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hU := uA_pos Y δ q hY0 hq
  obtain ⟨-, he⟩ := eta1_bounds
  have he0 : 0 < eta1 := by unfold eta1; have := Real.log_two_gt_d9; linarith
  have hUV := uA_mul_vA Y δ q hY hq hdq hy
  have hV : 100000000 ≤ vA Y := by
    unfold vA
    obtain ⟨-, -, e13, -, -⟩ := rpow_facts Y hY0
    have hu := u_ge Y hY
    rw [e13]; nlinarith
  have hUY : uA Y δ q / Y ≤ 0.00000001 := by
    rw [div_le_iff₀ hY0]; nlinarith
  unfold c1
  constructor
  · have : 0 ≤ eta1 * uA Y δ q / Y := by positivity
    linarith
  · have : eta1 * uA Y δ q / Y ≤ 5.5452 * 0.00000001 := by
      rw [mul_div_assoc]
      exact mul_le_mul he hUY (by positivity) (by norm_num)
    linarith

/-- `2√(c₀c₁)/π ≤ 3.5743` for `c₁ ≤ 1.000001`. -/
theorem k_coef (c : ℝ) (hc : c ≤ 1.000001) : 2 * Real.sqrt (c0 * c) / Real.pi ≤ 3.5743 := by
  have p1 := Real.pi_gt_d6
  have hs : Real.sqrt (c0 * c) ≤ 5.61436 := by
    rw [Real.sqrt_le_left (by norm_num)]
    unfold c0; nlinarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `√e ≤ 1.6488`, `e³ ≤ 20.1`, `1/e ≤ 0.36788`. -/
theorem e_facts : Real.sqrt (Real.exp 1) ≤ 1.6488 ∧ Real.exp 3 ≤ 20.1 ∧
    1 / Real.exp 1 ≤ 0.36788 := by
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_one_gt_d9
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.sqrt_le_left (by norm_num)]; linarith
  · have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (by positivity) h1.le 3
    linarith
  · rw [div_le_iff₀ (Real.exp_pos 1)]; linarith

/-- **The first-choice data in `u`-coordinates**: `u = x^{1/6} ≥ 8000`, `λ = log u ≥ 8.3`,
`s = √(δ₀q) ∈ [1, u]`, `s² ≥ 2`, `U = u⁴/(9s)`, `log U = 4λ − log 9 − log s`,
`0 ≤ log s ≤ λ − 1/2`, `λ ≤ 8.011 + u/8000`, `λ² ≤ 0.5414u`. -/
theorem u_data (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    8000 ≤ Y ^ ((1 : ℝ) / 6) ∧ 8.3 ≤ Real.log (Y ^ ((1 : ℝ) / 6)) ∧
      1 ≤ Real.sqrt (OC.dz δ * q) ∧ Real.sqrt (OC.dz δ * q) ≤ Y ^ ((1 : ℝ) / 6) ∧
      2 ≤ Real.sqrt (OC.dz δ * q) ^ 2 ∧
      Real.log (uA Y δ q) = 4 * Real.log (Y ^ ((1 : ℝ) / 6)) - Real.log 9 -
        Real.log (Real.sqrt (OC.dz δ * q)) ∧
      0 ≤ Real.log (Real.sqrt (OC.dz δ * q)) ∧
      Real.log (Real.sqrt (OC.dz δ * q)) ≤ Real.log (Y ^ ((1 : ℝ) / 6)) - 1 / 2 ∧
      Real.log (Y ^ ((1 : ℝ) / 6)) ≤ 8.011 + Y ^ ((1 : ℝ) / 6) / 8000 ∧
      Real.log (Y ^ ((1 : ℝ) / 6)) ^ 2 ≤ 0.5414 * Y ^ ((1 : ℝ) / 6) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, -, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  obtain ⟨hsq1, hsqu⟩ := sqrt_dq Y δ q hY hq hdq hy
  have hUe := uA_eq Y δ q hY0
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd := dz_ge δ
  have htx : OC.dz δ * q ≤ Y ^ ((1 : ℝ) / 3) / 3 := dz_q_le δ _ q hdq hy
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set s := Real.sqrt (OC.dz δ * q) with hs_def
  rw [e13] at htx
  have hu0 : 0 < u := by linarith
  have hs0 : 0 < s := by linarith
  have hss : s ^ 2 = OC.dz δ * q := Real.sq_sqrt (by positivity)
  obtain ⟨hlam1, -, -, -⟩ := w_facts u hu
  have hl3' : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]; have := Real.exp_one_lt_d9; linarith
  refine ⟨hu, hlam1, hsq1, hsqu, by rw [hss]; nlinarith, ?_, Real.log_nonneg hsq1, ?_, ?_, ?_⟩
  · rw [hUe, Real.log_div (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (by norm_num) hs0.ne']
    push_cast; ring
  · have h1 : Real.log (s ^ 2) ≤ Real.log (u ^ 2 / 3) := Real.log_le_log (by positivity)
      (by rw [hss]; exact htx)
    rw [Real.log_pow, Real.log_div (by positivity) (by norm_num), Real.log_pow] at h1
    push_cast at h1
    linarith
  · have h1 := Real.log_le_sub_one_of_pos (show 0 < u / 8000 by positivity)
    rw [Real.log_div hu0.ne' (by norm_num)] at h1
    have h2 : Real.log 8000 ≤ Real.log ((2 : ℝ) ^ 13) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h2
    push_cast at h2
    have := Real.log_two_lt_d9
    linarith
  · have h1 := log_le_div_e (Real.sqrt u) (Real.sqrt_pos.mpr hu0)
    rw [Real.log_sqrt hu0.le] at h1
    have h2 : Real.log u ≤ 0.73576 * Real.sqrt u := by linarith
    have h3 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
    have hl0 : 0 ≤ Real.log u := by linarith
    nlinarith

/-- **(k1)** `2√(c₀c₁)/π·U·log(ex/U) ≤ (u⁴/s)(1.1915λ + 1.0713)`. -/
theorem k1_le (c U Y u s lam ls : ℝ) (hc : c ≤ 1.000001) (hU : U = u ^ 4 / (9 * s))
    (hs : 0 < s) (hu : 0 < u) (hY : 0 < Y) (hlogY : Real.log Y = 6 * lam)
    (hlogU : Real.log U = 4 * lam - Real.log 9 - ls) (hls : ls ≤ lam - 1 / 2)
    (hls0 : 0 ≤ ls) (hlam : 8.3 ≤ lam) :
    2 * Real.sqrt (c0 * c) / Real.pi * U * Real.log (Real.exp 1 * Y / U) ≤
      u ^ 4 / s * (1.1915 * lam + 1.0713) := by
  have hkc := k_coef c hc
  have hl3 := MN.log3_le
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h90 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hU0 : 0 < U := by rw [hU]; positivity
  have hlog : Real.log (Real.exp 1 * Y / U) = 1 + 6 * lam - Real.log U := by
    rw [Real.log_div (by positivity) hU0.ne', Real.log_mul (Real.exp_pos 1).ne' hY.ne',
      Real.log_exp, hlogY]
  have hlog0 : 0 ≤ Real.log (Real.exp 1 * Y / U) := by rw [hlog, hlogU]; linarith
  have hlogle : Real.log (Real.exp 1 * Y / U) ≤ 3 * lam + 2.6973 := by
    rw [hlog, hlogU, h9]; linarith
  have hk0 : 0 ≤ 2 * Real.sqrt (c0 * c) / Real.pi := by positivity
  calc 2 * Real.sqrt (c0 * c) / Real.pi * U * Real.log (Real.exp 1 * Y / U)
      ≤ 3.5743 * U * (3 * lam + 2.6973) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hkc hU0.le) hlogle hlog0 (by positivity)
    _ = u ^ 4 / s * (3.5743 / 9 * (3 * lam + 2.6973)) := by rw [hU]; field_simp
    _ ≤ u ^ 4 / s * (1.1915 * lam + 1.0713) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith

/-- **(k2) vanishes**: `log⁺(D/(c₂x/q)) = 0` at the first choice (`Uq ≤ c₂x`). -/
theorem k2_eq (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) (c : ℝ) :
    3 * c / 2 * (Y / q) * logp (uA Y δ q / (c2 * Y / q)) * Real.log (q / c2) = 0 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨hu, -, hsq1, -, -⟩ := u_data Y δ q hY hq hdq hy
  obtain ⟨hc2a, -⟩ := c2_bounds
  have hUe := uA_eq Y δ q hY0
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set u := Y ^ ((1 : ℝ) / 6)
  set s := Real.sqrt (OC.dz δ * q)
  rw [e13] at hy
  have hu0 : 0 < u := by linarith
  have hr : uA Y δ q / (c2 * Y / q) ≤ 1 := by
    rw [div_le_one (by positivity), hUe, eY, div_le_iff₀ (by positivity)]
    have h1 : (q : ℝ) * u ^ 4 ≤ u ^ 2 / 6 * u ^ 4 := mul_le_mul_of_nonneg_right hy (by positivity)
    have h6 : 0 < u ^ 6 := by positivity
    have e : c2 * u ^ 6 / q * (9 * s) = 9 * c2 * s * u ^ 6 / q := by ring
    rw [e, le_div_iff₀ hqR]
    have : u ^ 2 / 6 * u ^ 4 = u ^ 6 / 6 := by ring
    nlinarith [mul_le_mul hc2a hsq1 (by norm_num) (by linarith)]
  have hl : logp (uA Y δ q / (c2 * Y / q)) = 0 := by
    unfold logp
    have hpos : 0 ≤ uA Y δ q / (c2 * Y / q) := by
      have := uA_pos Y δ q hY0 hq; positivity
    exact max_eq_right (Real.log_nonpos hpos hr)
  rw [hl, mul_zero, zero_mul]

/-- `max(1, log(c₀e³q²/(4π|η'|₁x))) = 1` at the first choice. -/
theorem k3_max (Y : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y))) = 1 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  obtain ⟨he1a, -⟩ := eta1_bounds
  obtain ⟨-, he3, -⟩ := e_facts
  have p1 := Real.pi_gt_d6
  rw [e13] at hy
  set u := Y ^ ((1 : ℝ) / 6)
  have hu0 : 0 < u := by linarith
  have hden : 0 < 4 * Real.pi * eta1 * Y := by
    have : 0 < eta1 := by linarith
    have := Real.pi_pos
    positivity
  apply max_eq_left
  have harg : c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y) ≤ 1 := by
    rw [div_le_one hden]
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hq2 : (q : ℝ) ^ 2 ≤ (u ^ 2 / 6) ^ 2 := pow_le_pow_left₀ hq0 hy 2
    have h1 : c0 * Real.exp 3 * (q : ℝ) ^ 2 ≤ 31.521 * 20.1 * (u ^ 2 / 6) ^ 2 := by
      unfold c0
      exact mul_le_mul (mul_le_mul_of_nonneg_left he3 (by norm_num)) hq2 (by positivity)
        (by norm_num)
    have h2 : 69 ≤ 4 * Real.pi * eta1 := by nlinarith
    have h3 : 69 * u ^ 6 ≤ 4 * Real.pi * eta1 * u ^ 6 :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have hu6 : 64000000 * u ^ 4 ≤ u ^ 6 := by
      have : 64000000 ≤ u ^ 2 := by nlinarith
      have e : u ^ 6 = u ^ 2 * u ^ 4 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right this (by positivity)
    rw [eY]
    have e2 : 31.521 * 20.1 * (u ^ 2 / 6) ^ 2 = 17.599225 * u ^ 4 := by ring
    nlinarith [pow_pos hu0 4]
  have hpos : 0 ≤ c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y) := by
    apply div_nonneg _ hden.le
    unfold c0; positivity
  exact (Real.log_nonpos hpos harg).trans (by norm_num)

/-- `log⁺(U/(q/2)) ≤ 4λ` and `0 ≤ log(q/c₂) ≤ 2λ + 0.49` at the first choice. -/
theorem k3_logs (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    logp (uA Y δ q / (q / 2)) ≤ 4 * Real.log (Y ^ ((1 : ℝ) / 6)) ∧
      0 ≤ logp (uA Y δ q / (q / 2)) ∧
      Real.log (q / c2) ≤ 2 * Real.log (Y ^ ((1 : ℝ) / 6)) + 0.49 ∧ 0 ≤ Real.log (q / c2) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, -, -⟩ := rpow_facts Y hY0
  obtain ⟨hu, hlam1, hsq1, -, -, -, -, -, -, -⟩ := u_data Y δ q hY hq hdq hy
  obtain ⟨hc2a, hc2b⟩ := c2_bounds
  have hUe := uA_eq Y δ q hY0
  have hU0 := uA_pos Y δ q hY0 hq
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  rw [e13] at hy
  set u := Y ^ ((1 : ℝ) / 6)
  set s := Real.sqrt (OC.dz δ * q)
  have hu0 : 0 < u := by linarith
  refine ⟨?_, le_max_right _ _, ?_, ?_⟩
  · unfold logp
    apply max_le _ (by linarith)
    have hpos : 0 < uA Y δ q / (q / 2) := by positivity
    have h1 : uA Y δ q / (q / 2) ≤ u ^ 4 := by
      rw [div_le_iff₀ (by positivity), hUe, div_le_iff₀ (by positivity)]
      have h9 : 1 ≤ (q : ℝ) / 2 * (9 * s) := by nlinarith
      have := mul_le_mul_of_nonneg_left h9 (by positivity : (0 : ℝ) ≤ u ^ 4)
      linarith
    calc Real.log (uA Y δ q / (q / 2)) ≤ Real.log (u ^ 4) := Real.log_le_log hpos h1
      _ = 4 * Real.log u := by rw [Real.log_pow]; push_cast; ring
  · rw [Real.log_div (by linarith) (by linarith)]
    have h1 : Real.log q ≤ Real.log (u ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_pow] at h1
    have h2 : -Real.log c2 ≤ 1 / c2 - 1 := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 / c2 by positivity)
      rw [Real.log_div (by norm_num) (by linarith), Real.log_one] at this
      linarith
    have h3 : 1 / c2 ≤ 1.4895 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    push_cast at h1
    linarith
  · exact Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)

/-- **(k3)** the `q`-proportional terms of `eq:kuche2`. -/
theorem k3_le (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) (c : ℝ)
    (hc : c ≤ 1.000001) :
    (2 * eta1 / Real.pi *
          max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * Y))) *
          Real.log Y +
        2 * Real.sqrt (c0 * c) / Real.pi * (Real.sqrt 3 + logp (uA Y δ q / (q / 2)) / 2) *
          Real.log (q / c2)) * q ≤
      Y ^ ((1 : ℝ) / 3) * (2.383 * Real.log (Y ^ ((1 : ℝ) / 6)) ^ 2 +
        6.18 * Real.log (Y ^ ((1 : ℝ) / 6)) + 0.506) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, -, eL⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  obtain ⟨hlam1, -, -, -⟩ := w_facts _ hu
  obtain ⟨-, he1b⟩ := eta1_bounds
  have hkc := k_coef c hc
  have hmax := k3_max Y q hY hy
  obtain ⟨hlp, hlp0, hlqc, hlqc0⟩ := k3_logs Y δ q hY hq hdq hy
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have p1 := Real.pi_gt_d6
  rw [e13] at hy ⊢
  rw [hmax]
  set u := Y ^ ((1 : ℝ) / 6)
  set lam := Real.log u
  have hlam0 : 0 ≤ lam := by linarith
  have hA : 2 * eta1 / Real.pi * 1 * Real.log Y ≤ 21.1812 * lam := by
    rw [eL, mul_one, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  have hs3 : Real.sqrt 3 ≤ 1.7321 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs30 : 0 ≤ Real.sqrt 3 + logp (uA Y δ q / (q / 2)) / 2 := by
    have := Real.sqrt_nonneg 3; linarith
  have hk0 : 0 ≤ 2 * Real.sqrt (c0 * c) / Real.pi := by
    have := Real.pi_pos; have := Real.sqrt_nonneg (c0 * c); positivity
  have hB : 2 * Real.sqrt (c0 * c) / Real.pi * (Real.sqrt 3 + logp (uA Y δ q / (q / 2)) / 2) *
      Real.log (q / c2) ≤ 3.5743 * (1.7321 + 2 * lam) * (2 * lam + 0.49) :=
    mul_le_mul (mul_le_mul hkc (by linarith) hs30 (by norm_num)) hlqc hlqc0 (by positivity)
  have hsum0 : 0 ≤ 21.1812 * lam + 3.5743 * (1.7321 + 2 * lam) * (2 * lam + 0.49) := by
    positivity
  calc _ ≤ (21.1812 * lam + 3.5743 * (1.7321 + 2 * lam) * (2 * lam + 0.49)) * (u ^ 2 / 6) :=
        mul_le_mul (by linarith) hy (by linarith) hsum0
    _ ≤ u ^ 2 * (2.383 * lam ^ 2 + 6.18 * lam + 0.506) := by
        nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) hlam0]

/-- **(k4) + (k5)** the `√x` terms of `eq:kuche2`. -/
theorem k45_le (Y c : ℝ) (hY : 3.4e23 ≤ Y) (hc : c ≤ 1.000001) :
    3 * c / 2 * Real.sqrt (2 * Y / c2) * Real.log (2 * Y / c2) +
      20 * c0 * c2 ^ ((3 : ℝ) / 2) / (3 * Real.pi ^ 2) * Real.sqrt (2 * Y) *
        Real.log (2 * Real.sqrt (Real.exp 1) * Y / c2) ≤
      Y ^ ((1 : ℝ) / 2) * (136.9 * Real.log (Y ^ ((1 : ℝ) / 6)) + 84.3) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, eL⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  obtain ⟨hc2a, hc2b⟩ := c2_bounds
  obtain ⟨hse, -, -⟩ := e_facts
  obtain ⟨hp1, -⟩ := pi_sq_bounds
  obtain ⟨hlam1, -, -, -⟩ := w_facts _ hu
  have h12 : Y ^ ((1 : ℝ) / 2) = (Y ^ ((1 : ℝ) / 6)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]; norm_num
  set u := Y ^ ((1 : ℝ) / 6)
  set lam := Real.log u
  rw [h12]
  have hu0 : 0 < u := by linarith
  have hsY : Real.sqrt Y = u ^ 3 := by
    rw [eY, show u ^ 6 = (u ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have h4a : Real.sqrt (2 * Y / c2) ≤ 1.7260 * u ^ 3 := by
    rw [show 2 * Y / c2 = (2 / c2) * Y by ring, Real.sqrt_mul (by positivity), hsY]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by linarith)]
    nlinarith
  have h4b : Real.log (2 * Y / c2) ≤ 6 * lam + 1.98 := by
    rw [show 2 * Y / c2 = (2 / c2) * Y by ring, Real.log_mul (by positivity) hY0.ne', eL]
    have := Real.log_le_sub_one_of_pos (show 0 < 2 / c2 by positivity)
    have h3 : 2 / c2 ≤ 2.979 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have h4c : 0 ≤ Real.log (2 * Y / c2) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; nlinarith)
  have h4 : 3 * c / 2 * Real.sqrt (2 * Y / c2) * Real.log (2 * Y / c2) ≤
      1.5000015 * (1.7260 * u ^ 3) * (6 * lam + 1.98) := by
    rcases le_or_gt 0 c with hc0 | hc0
    · apply mul_le_mul (mul_le_mul (by linarith) h4a (Real.sqrt_nonneg _) (by norm_num)) h4b h4c
      positivity
    · have : 3 * c / 2 * Real.sqrt (2 * Y / c2) * Real.log (2 * Y / c2) ≤ 0 := by
        have h1 : 3 * c / 2 * Real.sqrt (2 * Y / c2) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _)
        exact mul_nonpos_of_nonpos_of_nonneg h1 h4c
      have : 0 ≤ 1.5000015 * (1.7260 * u ^ 3) * (6 * lam + 1.98) := by
        have : 0 ≤ lam := by linarith
        positivity
      linarith
  have hc32 : c2 ^ ((3 : ℝ) / 2) ≤ 0.6715 := by
    have h1 : c2 ^ ((3 : ℝ) / 2) ≤ c2 ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) (by norm_num)
    rw [Real.rpow_one] at h1; linarith
  have hc5 : 20 * c0 * c2 ^ ((3 : ℝ) / 2) / (3 * Real.pi ^ 2) ≤ 14.3 := by
    rw [div_le_iff₀ (by positivity)]
    unfold c0
    nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ c2 by linarith) ((3 : ℝ) / 2)]
  have hc50 : 0 ≤ 20 * c0 * c2 ^ ((3 : ℝ) / 2) / (3 * Real.pi ^ 2) := by
    unfold c0
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ c2 by linarith) ((3 : ℝ) / 2)
    positivity
  have h5a : Real.sqrt (2 * Y) ≤ 1.41422 * u ^ 3 := by
    rw [Real.sqrt_mul (by norm_num), hsY]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hpos : 0 < 2 * Real.sqrt (Real.exp 1) / c2 := by
    have := Real.sqrt_pos.mpr (Real.exp_pos 1)
    have : 0 < c2 := by linarith
    positivity
  have h5b : Real.log (2 * Real.sqrt (Real.exp 1) * Y / c2) ≤ 6 * lam + 3.912 := by
    rw [show 2 * Real.sqrt (Real.exp 1) * Y / c2 = (2 * Real.sqrt (Real.exp 1) / c2) * Y by ring,
      Real.log_mul hpos.ne' hY0.ne', eL]
    have := Real.log_le_sub_one_of_pos hpos
    have h3 : 2 * Real.sqrt (Real.exp 1) / c2 ≤ 4.912 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [Real.sqrt_nonneg (Real.exp 1)]
    linarith
  have h5c : 0 ≤ Real.log (2 * Real.sqrt (Real.exp 1) * Y / c2) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith)]
    have : 1 ≤ Real.sqrt (Real.exp 1) :=
      Real.one_le_sqrt.mpr (by have := Real.exp_one_gt_d9; linarith)
    nlinarith
  have h5 : 20 * c0 * c2 ^ ((3 : ℝ) / 2) / (3 * Real.pi ^ 2) * Real.sqrt (2 * Y) *
      Real.log (2 * Real.sqrt (Real.exp 1) * Y / c2) ≤
      14.3 * (1.41422 * u ^ 3) * (6 * lam + 3.912) := by
    apply mul_le_mul (mul_le_mul hc5 h5a (Real.sqrt_nonneg _) (by norm_num)) h5b h5c
    positivity
  have : 0 ≤ lam := by linarith
  nlinarith [pow_pos hu0 3]

/-- **(err)** the `O*` term of `eq:cupcake2`. -/
theorem err_le (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    errI1 Y q (uA Y δ q) ≤
      Y ^ ((1 : ℝ) / 3) * (0.0434 * Real.log (Y ^ ((1 : ℝ) / 6)) + 0.0318) + 3.45 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, eY, eL⟩ := rpow_facts Y hY0
  obtain ⟨hu, hlam1, hsq1, -, hs2, hlogU, hls0, hls, -, -⟩ := u_data Y δ q hY hq hdq hy
  obtain ⟨-, -, hie⟩ := e_facts
  obtain ⟨hp1, hp2⟩ := pi_sq_bounds
  have hUe := uA_eq Y δ q hY0
  have hU0 := uA_pos Y δ q hY0 hq
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hl3 := MN.log3_le
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [e13]
  set u := Y ^ ((1 : ℝ) / 6)
  set s := Real.sqrt (OC.dz δ * q)
  set lam := Real.log u
  have hu0 : 0 < u := by linarith
  have hs0 : 0 < s := by linarith
  have hcoef : c0 * (1 / 2 - 2 / Real.pi ^ 2) ≤ 9.374 := by
    have : 0.202642 ≤ 2 / Real.pi ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
    unfold c0; nlinarith
  have hA : uA Y δ q ^ 2 / (4 * q * Y) ≤ u ^ 2 / 648 := by
    have e : uA Y δ q ^ 2 / (4 * q * Y) = u ^ 2 / (324 * (s ^ 2 * q)) := by
      rw [hUe, eY]; field_simp; ring
    rw [e]
    apply div_le_div_of_nonneg_left (sq_nonneg u) (by norm_num)
    nlinarith
  have hA0 : 0 ≤ uA Y δ q ^ 2 / (4 * q * Y) := by positivity
  have hlogeq : Real.log (Real.sqrt (Real.exp 1) * Y / uA Y δ q) =
      1 / 2 + 6 * lam - Real.log (uA Y δ q) := by
    rw [Real.log_div (by positivity) hU0.ne',
      Real.log_mul (Real.sqrt_pos.mpr (Real.exp_pos 1)).ne' hY0.ne', Real.log_sqrt
      (Real.exp_pos 1).le, Real.log_exp, eL]
  have hlog : Real.log (Real.sqrt (Real.exp 1) * Y / uA Y δ q) ≤ 3 * lam + 2.1973 := by
    rw [hlogeq, hlogU, h9]; linarith
  have hlog0 : 0 ≤ Real.log (Real.sqrt (Real.exp 1) * Y / uA Y δ q) := by
    rw [hlogeq, hlogU]
    have : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
    linarith
  unfold errI1
  have hin : uA Y δ q ^ 2 / (4 * q * Y) * Real.log (Real.sqrt (Real.exp 1) * Y / uA Y δ q) +
      1 / Real.exp 1 ≤ u ^ 2 / 648 * (3 * lam + 2.1973) + 0.36788 := by
    have := mul_le_mul hA hlog hlog0 (by positivity)
    linarith
  have hin0 : 0 ≤ uA Y δ q ^ 2 / (4 * q * Y) * Real.log (Real.sqrt (Real.exp 1) * Y / uA Y δ q) +
      1 / Real.exp 1 := by
    have := Real.exp_pos 1
    positivity
  have := mul_le_mul hcoef hin hin0 (by norm_num)
  have hlam0 : 0 ≤ lam := by linarith
  nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) hlam0]

/-- **Combining the lower-order bounds** (abstract). -/
theorem low_combine (u s lam K1 K3 K45 E : ℝ) (hu : 8000 ≤ u) (hs : 0 < s) (hlam1 : 8.3 ≤ lam)
    (hlamt : lam ≤ 8.011 + u / 8000) (hlams : lam ^ 2 ≤ 0.5414 * u)
    (hK1 : K1 ≤ u ^ 4 / s * (1.1915 * lam + 1.0713))
    (hK3 : K3 ≤ u ^ 2 * (2.383 * lam ^ 2 + 6.18 * lam + 0.506))
    (hK45 : K45 ≤ u ^ 3 * (136.9 * lam + 84.3))
    (hE : E ≤ u ^ 2 * (0.0434 * lam + 0.0318) + 3.45) :
    E + (K1 + K3 + K45) ≤ u ^ 4 / s * (0.67845 * (6 * lam) - 1.20818) + 0.37864 * u ^ 4 := by
  have hu0 : 0 < u := by linarith
  have hlam0 : 0 ≤ lam := by linarith
  have hu4s : 0 ≤ u ^ 4 / s := by positivity
  have hmain : u ^ 4 / s * (1.1915 * lam + 1.0713) ≤
      u ^ 4 / s * (0.67845 * (6 * lam) - 1.20818) :=
    mul_le_mul_of_nonneg_left (by linarith) hu4s
  have hr1 : u ^ 2 * (2.383 * lam ^ 2 + 6.18 * lam + 0.506) ≤
      u ^ 2 * (1.291 * u + 49.51 + 0.000773 * u + 0.506) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg u)
  have hr2 : u ^ 3 * (136.9 * lam + 84.3) ≤ u ^ 3 * (1181.1 + 0.017113 * u) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have hr3 : u ^ 2 * (0.0434 * lam + 0.0318) ≤ u ^ 2 * (0.3796 + 0.0000055 * u) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg u)
  have hu3 : 1181.1 * u ^ 3 ≤ 0.1477 * u ^ 4 := by nlinarith [pow_pos hu0 3]
  have hu2 : 51 * u ^ 2 ≤ 0.00001 * u ^ 4 := by nlinarith [pow_pos hu0 2]
  have hu2' : 1.3 * u ^ 3 ≤ 0.0002 * u ^ 4 := by nlinarith [pow_pos hu0 3]
  have hu1 : 3.45 ≤ 0.00001 * u ^ 4 := by nlinarith [pow_pos hu0 4]
  nlinarith [hK1, hK3, hK45, hE, hmain, hr1, hr2, hr3, hu3, hu2, hu2', hu1]

/-- **The lower-order terms of `lem:bostb1` at the first choice ≤ those of `eq:therwald`.** -/
theorem i1_low (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    errI1 Y q (uA Y δ q) + kuche2 Y q (uA Y δ q) ≤
      Y ^ ((2 : ℝ) / 3) / Real.sqrt (OC.dz δ * q) * (0.67845 * Real.log Y - 1.20818) +
        0.37864 * Y ^ ((2 : ℝ) / 3) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, -, e13, -, eL⟩ := rpow_facts Y hY0
  obtain ⟨hu, hlam1, hsq1, -, -, hlogU, hls0, hls, hlamt, hlams⟩ := u_data Y δ q hY hq hdq hy
  obtain ⟨-, hc1b⟩ := c1_le Y δ q hY hq hdq hy
  have hk1 := k1_le (c1 Y (uA Y δ q)) (uA Y δ q) Y _ _ _ _ hc1b (uA_eq Y δ q hY0)
    (by linarith) (by linarith) hY0 eL hlogU hls hls0 hlam1
  have hk2 := k2_eq Y δ q hY hq hdq hy (c1 Y (uA Y δ q))
  have hk3 := k3_le Y δ q hY hq hdq hy (c1 Y (uA Y δ q)) hc1b
  have hk45 := k45_le Y (c1 Y (uA Y δ q)) hY hc1b
  have herr := err_le Y δ q hY hq hdq hy
  have h12 : Y ^ ((1 : ℝ) / 2) = (Y ^ ((1 : ℝ) / 6)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]; norm_num
  rw [e13] at hk3 herr
  rw [h12] at hk45
  have hc := low_combine _ _ _ _ _ _ _ hu (by linarith) hlam1 hlamt hlams hk1 hk3 hk45 herr
  have hRHS : Y ^ ((2 : ℝ) / 3) / Real.sqrt (OC.dz δ * q) * (0.67845 * Real.log Y - 1.20818) +
      0.37864 * Y ^ ((2 : ℝ) / 3) = (Y ^ ((1 : ℝ) / 6)) ^ 4 / Real.sqrt (OC.dz δ * q) *
        (0.67845 * (6 * Real.log (Y ^ ((1 : ℝ) / 6))) - 1.20818) +
        0.37864 * (Y ^ ((1 : ℝ) / 6)) ^ 4 := by
    rw [e23, eL]
  unfold kuche2
  linarith [hk2, hc, hRHS]

/-! ## (4) `I1Arith` -/

/-- **`MPc.I1Arith`, PROVED.** -/
theorem i1Arith : I1Arith := by
  intro Y hY δ q hq hdq hy s0 s1 hs0 hron hmep
  have hY0 : (0 : ℝ) < Y := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hd := dz_ge δ
  obtain ⟨hlYU, hlYU0⟩ := lYU_le Y δ q hY hq hdq hy
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlt : 0 ≤ Real.log (OC.dz δ * q) := Real.log_nonneg (by nlinarith)
  have hm := i1_main Y q ((q : ℝ) / Nat.totient q) (((2 * q : ℕ) : ℝ) / Nat.totient (2 * q))
    (capM (c0 / Real.pi ^ 2) δ)
    ((2 - Real.log 4) * capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ)
    (capM (4 * 0.798437) δ) (Real.log (Y / uA Y δ q))
    (Real.log (uA Y δ q / q / ((2 * q : ℕ) : ℝ))) (Real.log (OC.dz δ * q)) s0 s1 hY0.le hqR
    (r_ge_one q hq) (R2_le q hq) (capM_nonneg _ δ (by unfold c0; positivity)) (cap1_le δ)
    (capL_le δ) hlt hlYU hlYU0 hs0
    (fun hell => by
      have hpos : 0 < Real.log (uA Y δ q / q / ((2 * q : ℕ) : ℝ)) := by linarith
      have hgt : ((2 * q : ℕ) : ℝ) < uA Y δ q / q := by
        have h1 := Real.exp_log (show 0 < uA Y δ q / q / ((2 * q : ℕ) : ℝ) by
          have := uA_pos Y δ q hY0 hq; positivity)
        have h2 : 1 < uA Y δ q / q / ((2 * q : ℕ) : ℝ) := by
          rw [← h1]; exact Real.one_lt_exp_iff.mpr hpos
        rwa [one_lt_div (by positivity)] at h2
      exact hron hgt)
    hmep
  have hl := i1_low Y δ q hY hq hdq hy
  unfold MMP.bI1W
  linarith

end Principia.Common.TernaryGoldbach.MPI1
