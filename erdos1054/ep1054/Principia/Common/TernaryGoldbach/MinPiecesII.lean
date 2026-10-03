/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MinPiecesI1

set_option autoImplicit false

/-!
# `MPc.IIArith` PROVED: the Totals algebra of `S_{II}`

`MPc.Vinland1At` / `MPc.EriksagaAt` bound `|S_{II}|` by `eq:vinland1` (`|δ| < 8`) and
`eq:eriksaga` (`|δ| ≥ 8`) at the first choice. `iiArith` proves each is at most `MT.bII`
(`eq:senorburns`) for every admissible `(x, δ, q)`, given `lem:merkel`'s `q/φ(q) ≤ ϝ(x^{1/3}/6)`.

* **Main term — EXACT, not lossy.** With `t = δ₀q`, `x/(UV) = 2√t` (`xUV`), so
  `log(x/UV) = log(4t)/2`, and `κ₆·log(x/UV) + 2κ₇ = 0.30214·log 4t + 0.2562 ≤ 0.30214·log t +
  0.67506` (slack `5·10⁻⁶`: `0.30214·log 4 = 0.4188549`). The `log(1 + ·)` factor is `C_{x,t}`'s
  because `V/(t(1 + ε₁)) ≥ 9x^{1/3}/(2.004t)` iff `1 + ε₁ ≤ 1.002`, and `ε₁ = 6√t/x^{1/3}
  ≤ 3.47/x^{1/6}`. The scoped ratio `vinland1|eriksaga : bII` reaches `0.999998` at `x = 10¹⁰⁰⁰`
  (`scratchpad/minpieces/iiarith.py`): the book's `eq:senorburns` IS its main term, and only an
  exact comparison closes it.
* **Lower order.** `κ₉x/√V = 1.84254x^{5/6}` and the `x/√U` term `≤ 0.886x^{5/6}` (`|δ| < 8`) or
  `≤ 0.890x^{5/6}` (`|δ| ≥ 8`), inside `2.73908x^{5/6}`, from `ϝ(x^{1/3}/6)·(1.5041 + 2 log u)
  ≤ 0.0385u` (`u = x^{1/6}`; `ϝ ≤ 2.2421 + 0.5451 log u`, `u ≥ 8000(1 + d + d²/2)`).
-/

namespace Principia.Common.TernaryGoldbach.MPII

open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPA Principia.Common.TernaryGoldbach.MPI1

/-! ## (1) Geometry of the first choice -/

/-- `x/(UV) = 2√(δ₀q)`. -/
theorem xUV (Y δ : ℝ) (q : ℕ) (hY0 : 0 < Y) (hq : 1 ≤ q) :
    Y / (uA Y δ q * vA Y) = 2 * Real.sqrt (OC.dz δ * q) := by
  obtain ⟨-, -, e13, eY, -⟩ := rpow_facts Y hY0
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs : 0 < Real.sqrt (OC.dz δ * q) := Real.sqrt_pos.mpr (by nlinarith [dz_ge δ])
  have hu : 0 < Y ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hY0 _
  rw [uA_eq Y δ q hY0]
  unfold vA
  rw [e13]
  nth_rw 1 [eY]
  field_simp

/-- `log(x/(UV)) = log(4t)/2`, `t = δ₀q`. -/
theorem logxUV (Y δ : ℝ) (q : ℕ) (hY0 : 0 < Y) (hq : 1 ≤ q) :
    Real.log (Y / (uA Y δ q * vA Y)) = Real.log (4 * (OC.dz δ * q)) / 2 := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have ht : 0 < OC.dz δ * q := by nlinarith [dz_ge δ]
  rw [xUV Y δ q hY0 hq, Real.log_mul (by norm_num) (Real.sqrt_pos.mpr ht).ne',
    Real.log_sqrt ht.le, Real.log_mul (by norm_num) ht.ne',
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

/-- `κ₆·log(4t)/2 + 2κ₇ ≤ 0.30214·log t + 0.67506`, and it is `≥ 0`. -/
theorem kap_le (t : ℝ) (ht : 1 ≤ t) :
    kap6 * (Real.log (4 * t) / 2) + 2 * kap7 ≤ 0.30214 * Real.log t + 0.67506 ∧
      0 ≤ kap6 * (Real.log (4 * t) / 2) + 2 * kap7 := by
  have hl2 := Real.log_two_lt_d9
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht
  have e : Real.log (4 * t) = 2 * Real.log 2 + Real.log t := by
    rw [Real.log_mul (by norm_num) (by linarith), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]; push_cast; ring
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold kap6 kap7
  rw [e]
  constructor <;> nlinarith

/-- **The `log(1 + ·)` comparison**: `a/log D ≤ log(4t)/(2 log(9x^{1/3}/(2.004t)))` for
`a = log(4t)/2` and `D ≥ 9x^{1/3}/(2.004t) ≥ 13.47`, so `log(1 + a/log D) ≤ C_{x,t}`. -/
theorem log1p_le (Y t D : ℝ) (hY0 : 0 < Y) (ht : 1 ≤ t) (htx : t ≤ Y ^ ((1 : ℝ) / 3) / 3)
    (hD : 9 * Y ^ ((1 : ℝ) / 3) / (2.004 * t) ≤ D) :
    Real.log (1 + Real.log (4 * t) / 2 / Real.log D) ≤ cXT Y t := by
  have hc : 0 < Y ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hY0 _
  have h13 : 13.47 ≤ 9 * Y ^ ((1 : ℝ) / 3) / (2.004 * t) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hl0 : 0 < Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * t)) :=
    Real.log_pos (by linarith)
  have hlD : Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * t)) ≤ Real.log D :=
    Real.log_le_log (by linarith) hD
  have hN : 0 ≤ Real.log (4 * t) := Real.log_nonneg (by linarith)
  have hq : Real.log (4 * t) / 2 / Real.log D ≤
      Real.log (4 * t) / (2 * Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * t))) := by
    rw [div_div]
    apply div_le_div_of_nonneg_left hN (by positivity)
    linarith
  have hq0 : 0 ≤ Real.log (4 * t) / 2 / Real.log D :=
    div_nonneg (by linarith) (by linarith)
  unfold cXT
  exact Real.log_le_log (by linarith) (by linarith)

/-- `0 ≤ C_{x,t}` in the first case. -/
theorem cXT_nonneg' (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    0 ≤ cXT Y (OC.dz δ * q) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  exact (cXT_bounds Y _ hY0 (by nlinarith [dz_ge δ]) (dz_q_le δ _ q hdq hy)).1

/-! ## (2) The main terms, exactly -/

/-- **`eq:vinland1`'s main term ≤ `eq:senorburns`'s** (`|δ| < 8`, `δ₀ = 2`). -/
theorem vin1_main (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (h8 : |δ| < 8) :
    Y / Real.sqrt (2 * Nat.totient q) *
        Real.sqrt ((Real.log (Y / (uA Y δ q * vA Y)) + Real.log (2 * q) *
            Real.log (1 + Real.log (Y / (uA Y δ q * vA Y)) / Real.log (vA Y / (2 * q)))) *
          (kap6 * Real.log (Y / (uA Y δ q * vA Y)) + 2 * kap7)) ≤
      Y / Real.sqrt (OC.dz δ * Nat.totient q) *
        (Real.sqrt (cXT Y (OC.dz δ * q) * (Real.log (OC.dz δ * q) + 0.002) +
            Real.log (4 * (OC.dz δ * q)) / 2) *
          Real.sqrt (0.30214 * Real.log (OC.dz δ * q) + 0.67506)) := by
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
  obtain ⟨hB, hB0⟩ := kap_le t ht1
  rw [Real.sqrt_mul hA0]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

/-- `ε₁ = x/(2UQ) ≤ 0.0005` at the first choice. -/
theorem eps1_le (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    0 ≤ Y / (2 * uA Y δ q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) ∧
      Y / (2 * uA Y δ q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) ≤ 0.0005 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, -, -, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨hu, -, hsq1, hsqu, -, -, -, -, -, -⟩ := u_data Y δ q hY hq hdq hy
  have hUe := uA_eq Y δ q hY0
  have hU0 := uA_pos Y δ q hY0 hq
  constructor
  · positivity
  · rw [hUe, e23]
    nth_rw 1 [eY]
    set u := Y ^ ((1 : ℝ) / 6)
    set s := Real.sqrt (OC.dz δ * q)
    have hu0 : 0 < u := by linarith
    have hs0 : 0 < s := by linarith
    have e : u ^ 6 / (2 * (u ^ 4 / (9 * s)) * (3 / 4 * u ^ 4)) = 6 * s / u ^ 2 := by
      field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have htx : OC.dz δ * q ≤ Y ^ ((1 : ℝ) / 3) / 3 := dz_q_le δ _ q hdq hy
    obtain ⟨-, -, e13', -, -⟩ := rpow_facts Y hY0
    rw [e13'] at htx
    have hss : s ^ 2 = OC.dz δ * q := Real.sq_sqrt (by nlinarith [dz_ge δ])
    have hsu : s ≤ 0.57736 * u := by nlinarith
    nlinarith

/-- **`eq:eriksaga`'s main term ≤ `eq:senorburns`'s** (`|δ| ≥ 8`, `δ₀ = |δ|/4`). -/
theorem erik_main (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (h8 : 8 ≤ |δ|) :
    2 * Y / Real.sqrt (|δ| * Nat.totient q) *
        Real.sqrt (Real.log (Y / (uA Y δ q * vA Y)) +
          Real.log (|δ| * q * (1 + Y / (2 * uA Y δ q * (3 / 4 * Y ^ ((2 : ℝ) / 3)))) / 4) *
            Real.log (1 + Real.log (Y / (uA Y δ q * vA Y)) /
              Real.log (4 * vA Y / (|δ| * (1 + Y / (2 * uA Y δ q * (3 / 4 * Y ^ ((2 : ℝ) / 3)))) *
                q)))) *
        Real.sqrt (kap6 * Real.log (Y / (uA Y δ q * vA Y)) + 2 * kap7) ≤
      Y / Real.sqrt (OC.dz δ * Nat.totient q) *
        (Real.sqrt (cXT Y (OC.dz δ * q) * (Real.log (OC.dz δ * q) + 0.002) +
            Real.log (4 * (OC.dz δ * q)) / 2) *
          Real.sqrt (0.30214 * Real.log (OC.dz δ * q) + 0.67506)) := by
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
  obtain ⟨hB, hB0⟩ := kap_le t ht1
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

/-! ## (3) `ϝ` and the lower-order terms -/

/-- **`ϝ(x^{1/3}/6) ≤ 0.00291u` and `ϝ(x^{1/3}/6)·(1.512 + 2λ) ≤ 0.0385u`**, `u = x^{1/6}`,
`λ = log u`. -/
theorem bigF_small (u : ℝ) (hu : 8000 ≤ u) :
    MinSp.bigF (u ^ 2 / 6) ≤ 0.00291 * u ∧
      MinSp.bigF (u ^ 2 / 6) * (1.512 + 2 * Real.log u) ≤ 0.0385 * u := by
  obtain ⟨hlu, hw, hw4, -⟩ := w_facts u hu
  have hFw := bigF_le_w u hu
  have hu0 : 0 < u := by linarith
  set lam := Real.log u
  set w := Real.sqrt (Real.sqrt lam)
  have hw3 : 4.8268 ≤ w ^ 3 := by nlinarith [sq_nonneg w]
  have hwl : w ≤ lam / 4.8268 := by
    rw [le_div_iff₀ (by norm_num), ← hw4]
    have : w * 4.8268 ≤ w * w ^ 3 := mul_le_mul_of_nonneg_left hw3 (by linarith)
    nlinarith
  have hFl : MinSp.bigF (u ^ 2 / 6) ≤ 2.2421 + 0.5452 * lam := by nlinarith
  -- `u ≥ 8000(1 + d + d²/2)`, `d = λ − log 8000`
  have hl8 : Real.log 8000 ≤ 9.011 := by
    have h2 : Real.log 8000 ≤ Real.log ((2 : ℝ) ^ 13) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h2; push_cast at h2
    have := Real.log_two_lt_d9; linarith
  set d := lam - Real.log 8000 with hd_def
  have hd0 : 0 ≤ d := by
    rw [hd_def]; linarith [Real.log_le_log (by norm_num) hu]
  have hud : 8000 * (1 + d + d ^ 2 / 2) ≤ u := by
    have h1 := Real.quadratic_le_exp_of_nonneg hd0
    have h2 : Real.exp d = u / 8000 := by
      rw [hd_def, Real.exp_sub, Real.exp_log hu0, Real.exp_log (by norm_num)]
    rw [h2] at h1
    linarith
  have hlamd : lam ≤ 9.011 + d := by rw [hd_def]; linarith
  have hlam0 : 0 ≤ lam := by linarith
  have hF0 : 0 ≤ MinSp.bigF (u ^ 2 / 6) := by
    have := MN.exp_gamma_le
    have hr : 3 ≤ u ^ 2 / 6 := by nlinarith
    exact (GS.bigF_gt _ hr).le.trans' (by norm_num)
  constructor
  · nlinarith
  · have h1 : MinSp.bigF (u ^ 2 / 6) * (1.512 + 2 * lam) ≤
        (2.2421 + 0.5452 * lam) * (1.512 + 2 * lam) :=
      mul_le_mul_of_nonneg_right hFl (by linarith)
    nlinarith [sq_nonneg d]

/-- `κ₉x/√V ≤ 1.84254u⁵` (`V = (9/2)x^{1/3}`). -/
theorem kap9_le (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    kap9 * (Y / Real.sqrt (vA Y)) ≤ 1.84254 * Y ^ ((5 : ℝ) / 6) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, e56, e13, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  have hu0 : 0 < Y ^ ((1 : ℝ) / 6) := by linarith
  unfold vA
  rw [e13, e56]
  nth_rw 1 [eY]
  set u := Y ^ ((1 : ℝ) / 6)
  have hs : Real.sqrt (9 / 2 * u ^ 2) = Real.sqrt 4.5 * u := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hu0.le]; norm_num
  have h45 : 2.12132 ≤ Real.sqrt 4.5 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  rw [hs]
  have e : u ^ 6 / (Real.sqrt 4.5 * u) = u ^ 5 / Real.sqrt 4.5 := by
    field_simp
  rw [e]
  unfold kap9
  rw [mul_div_assoc', div_le_iff₀ (by linarith)]
  nlinarith [pow_pos hu0 5]

/-- **`√(K)·(x/√U) ≤ c·u⁵`** from `K·x²/U ≤ c²u¹⁰` (`x²/U = 9√(δ₀q)u⁸`). -/
theorem sqrt_xU_le (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (K c : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hKc : K * (9 * 0.57736) * (Y ^ ((1 : ℝ) / 6)) ^ 9 ≤ c ^ 2 * (Y ^ ((1 : ℝ) / 6)) ^ 10) :
    Real.sqrt K * (Y / Real.sqrt (uA Y δ q)) ≤ c * (Y ^ ((1 : ℝ) / 6)) ^ 5 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨hu, -, hsq1, -, -, -, -, -, -, -⟩ := u_data Y δ q hY hq hdq hy
  have hUe := uA_eq Y δ q hY0
  have hU0 := uA_pos Y δ q hY0 hq
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have htx : OC.dz δ * q ≤ Y ^ ((1 : ℝ) / 3) / 3 := dz_q_le δ _ q hdq hy
  rw [e13] at htx
  set u := Y ^ ((1 : ℝ) / 6)
  set s := Real.sqrt (OC.dz δ * q)
  have hu0 : 0 < u := by linarith
  have hs0 : 0 < s := by linarith
  have hss : s ^ 2 = OC.dz δ * q := Real.sq_sqrt (by nlinarith [dz_ge δ])
  have hsu : s ≤ 0.57736 * u := by nlinarith
  apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
  have hsU : Real.sqrt (uA Y δ q) ^ 2 = uA Y δ q := Real.sq_sqrt hU0.le
  have hsK : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK
  have e : (Real.sqrt K * (Y / Real.sqrt (uA Y δ q))) ^ 2 = K * (9 * s * u ^ 8) := by
    rw [mul_pow, div_pow, hsK, hsU, hUe, eY]
    field_simp
  rw [e]
  have h1 : K * (9 * s * u ^ 8) ≤ K * (9 * (0.57736 * u) * u ^ 8) :=
    mul_le_mul_of_nonneg_left (by nlinarith [pow_pos hu0 8]) hK
  nlinarith [pow_pos hu0 8]

/-- `x/(2Uq) = 9u²√(2q)/(2q)` for `δ₀ = 2`, and `log 2q ≤ 2·log(x/(2Uq))`, `log(x/(2Uq)) > 0`. -/
theorem vin1_ratio (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6) (h8 : |δ| < 8) :
    Real.log (2 * q) / Real.log (Y / (2 * uA Y δ q * q)) ≤ 2 ∧
      0 ≤ Real.log (2 * q) / Real.log (Y / (2 * uA Y δ q * q)) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, e13, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  have hdz : OC.dz δ = 2 := max_eq_left (by linarith)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hUe := uA_eq Y δ q hY0
  rw [hdz] at hUe
  have hs0 : 0 < Real.sqrt (2 * (q : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt (2 * (q : ℝ)) ^ 2 = 2 * q := Real.sq_sqrt (by linarith)
  have hu0 : 0 < Y ^ ((1 : ℝ) / 6) := by linarith
  rw [e13] at hy
  have e : Y / (2 * uA Y δ q * q) =
      9 * (Y ^ ((1 : ℝ) / 6)) ^ 2 * Real.sqrt (2 * q) / (2 * q) := by
    rw [hUe]
    nth_rw 1 [eY]
    field_simp
  rw [e]
  set u := Y ^ ((1 : ℝ) / 6)
  set z := 9 * u ^ 2 * Real.sqrt (2 * q) / (2 * q) with hz
  have hz2 : z ^ 2 = 81 * u ^ 4 / (2 * q) := by
    rw [hz, div_pow, mul_pow, mul_pow, hs2]
    field_simp
    ring
  have h2q : 2 * (q : ℝ) ≤ z ^ 2 := by
    rw [hz2, le_div_iff₀ (by linarith)]
    nlinarith
  have hz1 : 1 < z := by
    rw [hz, one_lt_div (by linarith)]
    have h1 : 1 ≤ Real.sqrt (2 * (q : ℝ)) := Real.one_le_sqrt.mpr (by linarith)
    nlinarith
  have hlz : 0 < Real.log z := Real.log_pos hz1
  have h3 : Real.log (2 * q) ≤ Real.log (z ^ 2) := Real.log_le_log (by linarith) h2q
  rw [Real.log_pow] at h3
  push_cast at h3
  constructor
  · rw [div_le_iff₀ hlz]; linarith
  · exact div_nonneg (Real.log_nonneg (by linarith)) hlz.le

/-- **`eq:vinland1`'s lower-order terms `≤ 2.73908x^{5/6}`.** -/
theorem vin1_low (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (hF : (q : ℝ) / Nat.totient q ≤ MinSp.bigF (Y ^ ((1 : ℝ) / 3) / 6)) (h8 : |δ| < 8) :
    Real.sqrt 2 * kap2 * Real.sqrt ((q : ℝ) / Nat.totient q) *
        (1 + 1.15 * Real.sqrt (Real.log (2 * q) / Real.log (Y / (2 * uA Y δ q * q)))) *
        (Y / Real.sqrt (uA Y δ q)) + kap9 * (Y / Real.sqrt (vA Y)) ≤
      2.73908 * Y ^ ((5 : ℝ) / 6) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, e56, e13, -, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hk9 := kap9_le Y hY
  obtain ⟨hFs, -⟩ := bigF_small _ hu
  obtain ⟨hratio, hratio0⟩ := vin1_ratio Y δ q hY hq hy h8
  have hsx := sqrt_xU_le Y δ q hY hq hdq hy ((q : ℝ) / Nat.totient q) 0.123 (by positivity)
    (by norm_num) (by
      rw [e13] at hF
      have hK : (q : ℝ) / Nat.totient q ≤ 0.00291 * Y ^ ((1 : ℝ) / 6) := hF.trans hFs
      have hu0 : 0 < Y ^ ((1 : ℝ) / 6) := by linarith
      have h1 := mul_le_mul_of_nonneg_right hK
        (by positivity : (0 : ℝ) ≤ 9 * 0.57736 * (Y ^ ((1 : ℝ) / 6)) ^ 9)
      nlinarith [pow_pos hu0 10])
  have hsr : Real.sqrt (Real.log (2 * q) / Real.log (Y / (2 * uA Y δ q * q))) ≤ 1.41422 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hfac : 1 + 1.15 * Real.sqrt (Real.log (2 * q) / Real.log (Y / (2 * uA Y δ q * q))) ≤
      2.62636 := by linarith
  have hfac0 : 0 ≤ 1 + 1.15 * Real.sqrt (Real.log (2 * q) / Real.log (Y / (2 * uA Y δ q * q))) := by
    have := Real.sqrt_nonneg (Real.log (2 * q) / Real.log (Y / (2 * uA Y δ q * q)))
    linarith
  have hk2 : Real.sqrt 2 * kap2 ≤ 2.74031 := by
    have : Real.sqrt 2 ≤ 1.41422 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    unfold kap2; nlinarith
  have hsx0 : 0 ≤ Real.sqrt ((q : ℝ) / Nat.totient q) * (Y / Real.sqrt (uA Y δ q)) := by
    positivity
  have hT2 : Real.sqrt 2 * kap2 * (1 + 1.15 * Real.sqrt (Real.log (2 * q) /
        Real.log (Y / (2 * uA Y δ q * q)))) *
      (Real.sqrt ((q : ℝ) / Nat.totient q) * (Y / Real.sqrt (uA Y δ q))) ≤
      2.74031 * 2.62636 * (0.123 * (Y ^ ((1 : ℝ) / 6)) ^ 5) :=
    mul_le_mul (mul_le_mul hk2 hfac hfac0 (by norm_num)) hsx hsx0 (by norm_num)
  have hP : Real.sqrt 2 * kap2 * Real.sqrt ((q : ℝ) / Nat.totient q) *
      (1 + 1.15 * Real.sqrt (Real.log (2 * q) / Real.log (Y / (2 * uA Y δ q * q)))) *
      (Y / Real.sqrt (uA Y δ q)) =
      Real.sqrt 2 * kap2 * (1 + 1.15 * Real.sqrt (Real.log (2 * q) /
        Real.log (Y / (2 * uA Y δ q * q)))) *
        (Real.sqrt ((q : ℝ) / Nat.totient q) * (Y / Real.sqrt (uA Y δ q))) := by ring
  rw [hP, e56]
  rw [e56] at hk9
  have hu5 : 0 < (Y ^ ((1 : ℝ) / 6)) ^ 5 := by positivity
  nlinarith

/-- `log 6.75 ≥ 1.9`. -/
theorem log675_ge : 1.9 ≤ Real.log 6.75 := by
  have h := MN.le_log_series 6.75 0.15625 3 10 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **`eq:eriksaga`'s lower-order terms `≤ 2.73908x^{5/6}`.** -/
theorem erik_low (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hdq : |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3)) (hy : (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6)
    (hF : (q : ℝ) / Nat.totient q ≤ MinSp.bigF (Y ^ ((1 : ℝ) / 3) / 6)) (h8 : 8 ≤ |δ|) :
    kap2 * Real.sqrt (2 * q / Nat.totient q) *
        Real.sqrt (Real.log (vA Y) / Real.log (2 * vA Y / (|δ| * q))) *
        (Y / Real.sqrt (uA Y δ q)) + kap9 * (Y / Real.sqrt (vA Y)) ≤
      2.73908 * Y ^ ((5 : ℝ) / 6) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, e56, e13, eY, eL⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hk9 := kap9_le Y hY
  obtain ⟨-, hFl⟩ := bigF_small _ hu
  rw [e13] at hF hy hdq
  set u := Y ^ ((1 : ℝ) / 6)
  have hu0 : 0 < u := by linarith
  have hF0 : 0 ≤ MinSp.bigF (u ^ 2 / 6) := le_trans (by positivity) hF
  -- `log V ≤ 1.5041 + 2 log u`, `log(2V/|δ|q) ≥ log 6.75 ≥ 1.9`
  have hV : vA Y = 4.5 * u ^ 2 := by unfold vA; rw [e13]; norm_num
  have hlV : Real.log (vA Y) ≤ 1.512 + 2 * Real.log u := by
    rw [hV, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have : Real.log 4.5 ≤ 1.512 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4.5 / 4 by norm_num)
      rw [Real.log_div (by norm_num) (by norm_num)] at h
      have h4 := log4_le
      linarith
    push_cast; linarith
  have hlV0 : 0 ≤ Real.log (vA Y) := Real.log_nonneg (by rw [hV]; nlinarith)
  have hd0 : 0 < |δ| * q := by nlinarith
  have hl675 : 1.9 ≤ Real.log (2 * vA Y / (|δ| * q)) := by
    refine log675_ge.trans (Real.log_le_log (by norm_num) ?_)
    rw [hV, le_div_iff₀ hd0]; nlinarith
  have hlpos : 0 < Real.log (2 * vA Y / (|δ| * q)) := by linarith
  have hrat : Real.log (vA Y) / Real.log (2 * vA Y / (|δ| * q)) ≤
      0.5264 * (1.512 + 2 * Real.log u) := by
    rw [div_le_iff₀ hlpos]
    have hlu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
    have h1 := mul_le_mul_of_nonneg_left hl675
      (by positivity : (0 : ℝ) ≤ 0.5264 * (1.512 + 2 * Real.log u))
    nlinarith
  -- `√(2q/φ)·√(ratio)·(x/√U) ≤ 0.4595u⁵`
  have hK : 2 * (q : ℝ) / Nat.totient q *
      (Real.log (vA Y) / Real.log (2 * vA Y / (|δ| * q))) ≤ 0.0405328 * u := by
    have e : 2 * (q : ℝ) / Nat.totient q = 2 * ((q : ℝ) / Nat.totient q) := by ring
    rw [e]
    have h1 := mul_le_mul (by linarith : 2 * ((q : ℝ) / Nat.totient q) ≤
      2 * MinSp.bigF (u ^ 2 / 6)) hrat (div_nonneg hlV0 hlpos.le) (by positivity)
    have h2 : 2 * MinSp.bigF (u ^ 2 / 6) * (0.5264 * (1.512 + 2 * Real.log u)) =
        1.0528 * (MinSp.bigF (u ^ 2 / 6) * (1.512 + 2 * Real.log u)) := by ring
    linarith
  have hK0 : 0 ≤ 2 * (q : ℝ) / Nat.totient q *
      (Real.log (vA Y) / Real.log (2 * vA Y / (|δ| * q))) :=
    mul_nonneg (by positivity) (div_nonneg hlV0 hlpos.le)
  have hsx := sqrt_xU_le Y δ q hY hq (by rw [e13]; exact hdq) (by rw [e13]; exact hy)
    (2 * (q : ℝ) / Nat.totient q * (Real.log (vA Y) / Real.log (2 * vA Y / (|δ| * q))))
    0.4595 hK0 (by norm_num) (by
      have h2 := mul_le_mul_of_nonneg_right hK
        (by positivity : (0 : ℝ) ≤ 9 * 0.57736 * u ^ 9)
      nlinarith [pow_pos hu0 10])
  have hP : kap2 * Real.sqrt (2 * q / Nat.totient q) *
      Real.sqrt (Real.log (vA Y) / Real.log (2 * vA Y / (|δ| * q))) *
      (Y / Real.sqrt (uA Y δ q)) =
      kap2 * (Real.sqrt (2 * (q : ℝ) / Nat.totient q *
        (Real.log (vA Y) / Real.log (2 * vA Y / (|δ| * q)))) * (Y / Real.sqrt (uA Y δ q))) := by
    rw [Real.sqrt_mul (by positivity)]; ring
  rw [hP, e56]
  rw [e56] at hk9
  have hfin : kap2 * (Real.sqrt (2 * (q : ℝ) / Nat.totient q *
      (Real.log (vA Y) / Real.log (2 * vA Y / (|δ| * q)))) * (Y / Real.sqrt (uA Y δ q))) ≤
      1.93768 * (0.4595 * u ^ 5) := by
    unfold kap2
    exact mul_le_mul_of_nonneg_left hsx (by norm_num)
  have hu5 : 0 < u ^ 5 := by positivity
  linarith [hfin, hk9]

/-! ## (4) `IIArith` -/

/-- **`MPc.IIArith`, PROVED.** -/
theorem iiArith : IIArith := by
  intro Y hY δ q hq hdq hy hF
  constructor
  · intro h8
    have hm := vin1_main Y δ q hY hq hdq hy h8
    have hl := vin1_low Y δ q hY hq hdq hy hF h8
    unfold vin1 bII
    linarith
  · intro h8
    have hm := erik_main Y δ q hY hq hdq hy h8
    have hl := erik_low Y δ q hY hq hdq hy hF h8
    unfold erik bII
    linarith

/-! ## (5) The Main Theorem from the OPEN links only -/

/-- **`OP.MinMainP 0.811 45.7575` from the links still open.** `MPc.minMainP_of_links` with its
three proved NUMERIC links supplied: `MPI1.i1Arith`, `iiArith`, `MPA.coexistArith`. Open:
`Bostb1At`, `Bosta2Eta2`, `I2Arith`, `Vinland1At`, `EriksagaAt`, `SecI1At`, `SecI2At`, `SecIIAt`
(analytic or numeric), `Grara`, `Ronsard`, `Meproz` (cited literature), `GS.RS62Thm15`. -/
theorem minMainP_of_open (hb1 : Bostb1At) (hgr : Grara) (hro : Ronsard) (hme : Meproz)
    (hb2 : Bosta2Eta2) (hA2 : I2Arith) (hv1 : Vinland1At) (her : EriksagaAt) (hs1 : SecI1At)
    (hs2 : SecI2At) (hs3 : SecIIAt) (h15 : GS.RS62Thm15) : OP.MinMainP 0.811 45.7575 :=
  minMainP_of_links hb1 hgr hro hme i1Arith hb2 hA2 hv1 her iiArith hs1 hs2 hs3 coexistArith h15

end Principia.Common.TernaryGoldbach.MPII
