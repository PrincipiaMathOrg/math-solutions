/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.SplitCheb
import Principia.Common.TernaryGoldbach.OstopL
import Principia.Common.TernaryGoldbach.DrujalLowP

set_option autoImplicit false

/-!
# HelfMaj RETYPED (`HelfMajR`): the major-arc inputs at constants their proofs establish

**`HelfMajR` IS OPEN (it is HelfMaj's analysis). This file proves the ATTACHMENT and the
REGENERATION.** `RT.HelfMajFull` (`MajSp.Malpor`, `Coprar`, `Malheur`) transcribes HelfMaj's
PRINTED constants, which an adversarial referee (2026-09-30, LEAN-PROGRESS "THE HELFMAJ PAPER
SPINE") found NOT established by the printed proofs: F1 (a `√π` in `lem:hausierer`), F2 (zero
symmetry assumed for complex `χ`), F4 (a factor `2` dropped in Prop 1.5), N1 (`lem:garmola` drops
`f(T₀)g(T₀)`, so the zero tails grow `×5`–`8.6`). The referee's RETYPES, each judged TRUE for the
corrected proof, are `MalporR`, `CoprarR`, `MalheurR`, and `HelfMajR` bundles them under
`RT.PlattFull`. `helfMajR_of_full` proves the restatement ATTACHES (it is WEAKER).

## Every consumer on the `ep1054_ostopL` route, regenerated (exact rationals: `price_majr.py`)

| constant | old → new | direction | margin |
|---|---|---|---|
| `ET₊` (`et_plusR`) | `1.1377e-8 → 1.4490e-8` | up | `4.73e-13` |
| `E₊` (`eb_plusR`, `plus_numR`) | `2.3921e-8 → 4.2813e-8` | up | `5.73e-13` |
| `49E*` (`eb_starR`, `star_numR`) | `1.3353e-7 → 2.1941e-7` | up | `5.24e-12` |
| `err*(0)` (`et0_starR`) | `1.71973e-8` KEPT (true `4.19538e-9`) | up | `1.30e-8` |
| `Z₊`, felipa slope (`zplusR`, `felipaR`) | `0.640209 → 0.640212` | up | `1.00e-6` |
| `J` floor (`jArithPR`) | `8.57476 → 8.55451` | down | `3.45e-6` |
| `p₀` (`floor_854R`) | `8.54` kept | — | `1.45e-2` |
| major `c_maj'` (`arith_close_c0R`) | `1.0563699 → 1.0563578` | down | `1.01e-6` |
| split (`helfAt_smooth_chebR`) | `K = 2.0516868e-4 ≥ 0.000205` | — | `1.69e-7` |
| minor `c_min`, `cM` (`close_cheb`) | `1.0154`, `0.8095` kept | — | unchanged |
| `A ≤ 100` (`aArithR`) | sum `63.67 → 63.69` | — | `36.3` |

`E₊`: the conductor-`≥ 2` branch dominates (`6.18e-11 + 1.14e-9/√2 + (900000 + 52·547.7226)/√x`);
bounding `1.14e-9/q` at `q = 1` instead would give `4.3146e-8`. `err*(0)` is kept at `1.71973e-8`
so `MajSp.zstar_holds`, `MinSp.hex_le` and the `η*` side of `thm:ostop` apply unchanged.
`RW.NefumoW` takes its `E` bounds as ARGUMENTS: its statement is unchanged, its instantiation in
`majorAt_c0R` moves. `DS.PerArc`, `DS.ArcInt`, `DS.KSmall` are generic in `ET`, `E`.
`DS.DrujalE100`, `OC.DrujalLowP` carry `ET`/`E` in their STATEMENTS and are regenerated
(`DrujalE100R`, `DrujalLowPR`), each STRONGER than its original (`drujalE100_of_R`,
`drujalLowP_of_R`).
`OL.FelipaAt 0.6406` is now DERIVED (`felipaAt_6406R`: `0.640212 ≤ 0.6406`), so F4 no longer costs
the headline a hypothesis.

## Generation

Every copied block is a COUNTED substitution of its source (`MajSp`, `RT`, `MinSp`, `OL`, `OC`,
`SF`, `DS`, `MC0`, `SC`) by `scratchpad/majr/gen_majr.py`, which asserts every replacement count
and asserts the stale constants (`2.3921e-8`, `1.1377e-8`, `1.3353e-7`, `0.640209`, `8.57476`,
`1.0563699`, `0.0409699`, `251100`, `499100`, `380600`, `4.269e-14`, `310.84`) ABSENT from the
generated code. Docstrings are rewritten; proofs are the originals'.
-/

namespace Principia.Common.TernaryGoldbach.MR

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction
open Principia.Erdos1054 (helfgottX)
open Principia.Erdos1054.Proofs.BalancedK (HelfgottAt)

/-! ## (1) HelfMaj RETYPED -/

section Retype

open Principia.Common.TernaryGoldbach.MajSp

/-- **HelfMaj Thm 1.4 RETYPED** (`thm:malpor`; generated from `MajSp.Malpor`, constants only): the
referee's `MalporR`. The tails are ×10 (`6.18e-11`, `1.14e-9`; N1: `lem:garmola` drops
`f(T₀)g(T₀)`); the main term `900000` covers complex `χ` at norm `0.83` (F1, F2; needs `763900`);
at `q = 1`, `320000` (needs `276168`). OPEN; weight-specific (`η₊`). -/
def MalporR (η : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 10 ^ 12 ≤ x → ∀ q : ℕ, 1 ≤ q → (Odd q → q ≤ 150000) → (Even q → q ≤ 300000) →
    ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → ∀ δ : ℝ,
      |δ| ≤ 600000 * (Nat.gcd q 2 : ℝ) / q →
        ‖err η χ δ x‖ ≤ 6.18e-11 / Real.sqrt q + 1.14e-9 / q +
            (900000 / Real.sqrt q + 52) / Real.sqrt x ∧
          (q = 1 → ‖err η χ δ x‖ ≤ 3.34e-11 + 320000 / Real.sqrt x)

/-- **HelfMaj Cor 1.3 RETYPED** (`cor:coprar`; generated from `MajSp.Coprar`): the referee's
`CoprarR`, `3e-13/q + (650000/√q + 80)/√x` (needs `513958` in the main term; the tail is
`≈ 2.15e-13/q`), for the UNSCALED base `φ ∗_M η₂` of `η*`. OPEN; weight-specific. -/
def CoprarR (η : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 10 ^ 8 ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ 300000 →
    ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → ∀ δ : ℝ, |δ| ≤ 4 * 300000 / q →
      ‖err η χ δ x‖ ≤ 3e-13 / q + (650000 / Real.sqrt q + 80) / Real.sqrt x

/-- **HelfMaj Prop 1.5 RETYPED, at one scale** (`prop:malheur`; generated from `MajSp.MalheurAt`):
the referee's `MalheurR`, `(5·10⁻⁶ + 500/√x)` for `(2·10⁻⁶ + 310.84/√x)` (F4: a factor `2` dropped
in the cross term; needs `3.91·10⁻⁶ + 347/√x`). The main terms `0.640206`, `0.021095` are kept. -/
def MalheurAtR (η : ℝ → ℝ) (x : ℝ) : Prop :=
  |∑' n : ℕ, Λ n * Real.log n * η ((n : ℝ) / x) ^ 2 - (0.640206 * x * Real.log x - 0.021095 * x)|
    ≤ (5e-6 + 500 / Real.sqrt x) * x * Real.log x

/-- `MalheurAtR` at every `x ≥ 10¹²` (generated from `MajSp.Malheur`). -/
def MalheurR (η : ℝ → ℝ) : Prop := ∀ x : ℝ, 10 ^ 12 ≤ x → MalheurAtR η x

end Retype

/-- **HelfMaj RETYPED, conditional on Platt's own statement** (generated from `RT.HelfMajFull`):
`MalporR` for `ηp`, `CoprarR` for the base `ηc` of `η*`, `MalheurR` for `ηp`. OPEN; WEAKER than
`RT.HelfMajFull` (`helfMajR_of_full`), so it ATTACHES. -/
def HelfMajR (ηp ηc : ℝ → ℝ) : Prop :=
  RT.PlattFull → MalporR ηp ∧ CoprarR ηc ∧ MalheurR ηp

/-! ## (2) The restatement ATTACHES: the printed constants imply the retyped ones -/

/-- **`MajSp.Malpor → MalporR`**: every retyped coefficient is at least the printed one
(`6.18e-12 ≤ 6.18e-11`, `1.14e-10 ≤ 1.14e-9`, `499100 ≤ 900000`; at `q = 1`, `251100 ≤ 320000`). -/
theorem malporR_of_malpor (η : ℝ → ℝ) (h : MajSp.Malpor η) : MalporR η := by
  intro x hx q hq1 hodd hev χ hχ δ hδ
  obtain ⟨h1, h2⟩ := h x hx q hq1 hodd hev χ hχ δ hδ
  have hs := Real.sqrt_nonneg (q : ℝ)
  have hq0 := Nat.cast_nonneg (α := ℝ) q
  have hw := Real.sqrt_nonneg x
  have a1 : 6.18e-12 / Real.sqrt q ≤ 6.18e-11 / Real.sqrt q :=
    div_le_div_of_nonneg_right (by norm_num) hs
  have a2 : 1.14e-10 / (q : ℝ) ≤ 1.14e-9 / q := div_le_div_of_nonneg_right (by norm_num) hq0
  have a3 : 499100 / Real.sqrt q ≤ 900000 / Real.sqrt q :=
    div_le_div_of_nonneg_right (by norm_num) hs
  have a4 : (499100 / Real.sqrt q + 52) / Real.sqrt x ≤
      (900000 / Real.sqrt q + 52) / Real.sqrt x :=
    div_le_div_of_nonneg_right (by linarith) hw
  have a5 : 251100 / Real.sqrt x ≤ 320000 / Real.sqrt x :=
    div_le_div_of_nonneg_right (by norm_num) hw
  exact ⟨by linarith, fun h1q => by linarith [h2 h1q]⟩

/-- **`MajSp.Coprar → CoprarR`** (`4.269e-14 ≤ 3e-13`, `380600 ≤ 650000`, `76 ≤ 80`). -/
theorem coprarR_of_coprar (η : ℝ → ℝ) (h : MajSp.Coprar η) : CoprarR η := by
  intro x hx q hq1 hq χ hχ δ hδ
  have h1 := h x hx q hq1 hq χ hχ δ hδ
  have hs := Real.sqrt_nonneg (q : ℝ)
  have hq0 := Nat.cast_nonneg (α := ℝ) q
  have hw := Real.sqrt_nonneg x
  have a1 : 4.269e-14 / (q : ℝ) ≤ 3e-13 / q := div_le_div_of_nonneg_right (by norm_num) hq0
  have a2 : 380600 / Real.sqrt q ≤ 650000 / Real.sqrt q :=
    div_le_div_of_nonneg_right (by norm_num) hs
  have a3 : (380600 / Real.sqrt q + 76) / Real.sqrt x ≤
      (650000 / Real.sqrt q + 80) / Real.sqrt x :=
    div_le_div_of_nonneg_right (by linarith) hw
  linarith

/-- **`MajSp.MalheurAt → MalheurAtR`** at every `x ≥ 1`:
`(2·10⁻⁶ + 310.84/√x)·x log x ≤ (5·10⁻⁶ + 500/√x)·x log x`. -/
theorem malheurAtR_of_at (η : ℝ → ℝ) (x : ℝ) (hx : 1 ≤ x) (h : MajSp.MalheurAt η x) :
    MalheurAtR η x := by
  unfold MajSp.MalheurAt at h
  unfold MalheurAtR
  have hL := Real.log_nonneg hx
  have hxL : 0 ≤ x * Real.log x := mul_nonneg (by linarith) hL
  have a1 : 310.84 / Real.sqrt x ≤ 500 / Real.sqrt x :=
    div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg x)
  have a2 : (2e-6 + 310.84 / Real.sqrt x) * x * Real.log x ≤
      (5e-6 + 500 / Real.sqrt x) * x * Real.log x := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hxL
  linarith

/-- **`MajSp.Malheur → MalheurR`**. -/
theorem malheurR_of_malheur (η : ℝ → ℝ) (h : MajSp.Malheur η) : MalheurR η :=
  fun x hx => malheurAtR_of_at η x (le_trans (by norm_num) hx) (h x hx)

/-- **THE RESTATEMENT ATTACHES: `RT.HelfMajFull → HelfMajR`.** The printed constants are
stronger, so `HelfMajR` is implied by the old link and a headline taking it is no stronger. -/
theorem helfMajR_of_full (ηp ηc : ℝ → ℝ) (h : RT.HelfMajFull ηp ηc) : HelfMajR ηp ηc :=
  fun pf => ⟨malporR_of_malpor ηp (h pf).1, coprarR_of_coprar ηc (h pf).2.1,
    malheurR_of_malheur ηp (h pf).2.2⟩

/-! ## (3) The quantities of `prop:nefumo` and `thm:ostop` at `HelfMajR` -/

section Derive

open Principia.Common.TernaryGoldbach.MajSp

/-- The arithmetic of `eq:zakone2` at `MalporR` (generated from `MajSp.plus_num`), conductor
`c = s² ≥ 2`: `s·(6.18e-11/s + 1.14e-9/c + (900000/s + 52)/√x) ≤ 4.2813e-8` (`4.2812427e-8`). -/
theorem plus_numR (c s w : ℝ) (hcs : s * s = c) (hs1 : 1.41421 ≤ s) (hs2 : s ≤ 547.7226)
    (hw : 22135943 * 10 ^ 6 ≤ w) :
    s * (6.18e-11 / s + 1.14e-9 / c + (900000 / s + 52) / w) ≤ 4.2813e-8 := by
  subst hcs
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs1
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have key : s * (6.18e-11 / s + 1.14e-9 / (s * s) + (900000 / s + 52) / w) =
      6.18e-11 + 1.14e-9 / s + (900000 + 52 * s) / w := by
    field_simp
  rw [key]
  have t1 : 1.14e-9 / s ≤ 1.14e-9 / 1.41421 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs1
  have t2 : (900000 + 52 * s) / w ≤ (900000 + 52 * 547.7226) / (22135943 * 10 ^ 6) := by
    rw [div_le_div_iff₀ hw0 (by norm_num)]
    nlinarith
  have t3 : (6.18e-11 : ℝ) + 1.14e-9 / 1.41421 +
      (900000 + 52 * 547.7226) / (22135943 * 10 ^ 6) ≤ 4.2813e-8 := by norm_num
  linarith

/-- The arithmetic of `eq:fabienne` at `CoprarR`, with the corrected `√49` (generated from
`MajSp.star_num`), conductor `c = s² ≥ 1`:
`s·((3e-13/c + (650000/s + 80)/(√x/7))/49) ≤ 2.1941e-7/49` (`2.1940477e-7`). -/
theorem star_numR (c s w : ℝ) (hcs : s * s = c) (hs1 : 1 ≤ s) (hs2 : s ≤ 547.7226)
    (hw : 22135943 * 10 ^ 6 ≤ w) :
    s * ((3e-13 / c + (650000 / s + 80) / (w / 7)) / 49) ≤ 2.1941e-7 / 49 := by
  subst hcs
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs1
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have key : s * ((3e-13 / (s * s) + (650000 / s + 80) / (w / 7)) / 49) =
      (3e-13 / s + 7 * (650000 + 80 * s) / w) / 49 := by
    field_simp
  rw [key]
  have t1 : 3e-13 / s ≤ 3e-13 := div_le_self (by norm_num) hs1
  have t2 : 7 * (650000 + 80 * s) / w ≤ 7 * (650000 + 80 * 547.7226) / (22135943 * 10 ^ 6) := by
    rw [div_le_div_iff₀ hw0 (by norm_num)]
    nlinarith
  have t3 : (3e-13 : ℝ) + 7 * (650000 + 80 * 547.7226) / (22135943 * 10 ^ 6) ≤ 2.1941e-7 := by
    norm_num
  have t4 : 3e-13 / s + 7 * (650000 + 80 * s) / w ≤ 2.1941e-7 := by linarith
  exact div_le_div_of_nonneg_right t4 (by norm_num)

/-- **`E_{η₊,150000,8} ≤ 4.2813e-8`** (`eq:zakone2`) from `MalporR`, over every character on every
arc, through its conductor (generated from `MajSp.eb_plus`; the printed chain has `2.3921e-8`).
PROVED. -/
theorem eb_plusR (ηp : ℝ → ℝ) (h : MalporR ηp) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    EBound ηp x 4.2813e-8 := by
  intro q hq1 hqr χ δ hδ
  haveI : NeZero q := ⟨by omega⟩
  have hc1 : 1 ≤ χ.conductor := Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
  obtain ⟨hodd, hev, hg⟩ := cond_ok q χ.conductor χ.conductor_dvd_level hq1 hqr
  have hδ' := delta_ok q χ.conductor hq1 hc1 hg δ hδ
  have hb := h x (le_trans (by norm_num) hx) χ.conductor hc1 hodd hev χ.primitiveCharacter
    χ.primitiveCharacter_isPrimitive δ hδ'
  have hw := sqrt_x_ge x hx
  by_cases h1 : χ.conductor = 1
  · have hc : Real.sqrt (χ.conductor : ℝ) = 1 := by rw [h1, Nat.cast_one, Real.sqrt_one]
    rw [hc, one_mul]
    have h2 : 320000 / Real.sqrt x ≤ 320000 / (22135943 * 10 ^ 6) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hw
    have h3 := hb.2 h1
    have h4 : (3.34e-11 : ℝ) + 320000 / (22135943 * 10 ^ 6) ≤ 4.2813e-8 := by norm_num
    linarith
  · have hc2 : 2 ≤ χ.conductor := by omega
    have hc3 : χ.conductor ≤ 300000 := by
      rcases Nat.even_or_odd χ.conductor with he | ho
      · exact hev he
      · exact le_trans (hodd ho) (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hb.1 (Real.sqrt_nonneg _))
      (plus_numR _ _ _ (Real.mul_self_sqrt (Nat.cast_nonneg _)) (sqrt_c_ge _ hc2)
        (sqrt_c_le _ hc3) hw)

/-- **`E_{η*,150000,8} ≤ 2.1941e-7/49`** from `CoprarR` for the base `ηc` and `η*(t) = ηc(49t)`
(generated from `MajSp.eb_star`; was `1.3353e-7/49`). PROVED. -/
theorem eb_starR (ηs ηc : ℝ → ℝ) (sc : StarScale ηs ηc) (h : CoprarR ηc) (x : ℝ)
    (hx : 49 * 10 ^ 25 ≤ x) : EBound ηs x (2.1941e-7 / 49) := by
  intro q hq1 hqr χ δ hδ
  haveI : NeZero q := ⟨by omega⟩
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hc1 : 1 ≤ χ.conductor := Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
  have hcq : χ.conductor ≤ q := Nat.le_of_dvd (by omega) χ.conductor_dvd_level
  have hg2 : Nat.gcd q 2 ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right q 2)
  have hq3 : q ≤ 300000 := by omega
  have hδ' : |δ / 49| ≤ 4 * 300000 / (χ.conductor : ℝ) := by
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
    have hc0 : (0 : ℝ) < χ.conductor := Nat.cast_pos.mpr (by omega)
    have hgR : (Nat.gcd q 2 : ℝ) ≤ 2 := by exact_mod_cast hg2
    have hcqR : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hcq
    have e1 : |δ / 49| ≤ |δ| := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 49)]
      exact div_le_self (abs_nonneg δ) (by norm_num)
    have e2 : (Nat.gcd q 2 : ℝ) * 600000 / q ≤ 4 * 300000 / (χ.conductor : ℝ) := by
      rw [div_le_div_iff₀ hq0 hc0]
      nlinarith
    linarith
  have hy : 10 ^ 8 ≤ x / 49 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hb := h (x / 49) hy χ.conductor hc1 (by omega) χ.primitiveCharacter
    χ.primitiveCharacter_isPrimitive (δ / 49) hδ'
  rw [sqrt_div49 x hx0.le] at hb
  rw [err_scale ηs ηc sc χ.primitiveCharacter δ x hx0.ne', norm_div, Complex.norm_ofNat]
  have hc3 : χ.conductor ≤ 300000 := by omega
  have hs1 : 1 ≤ Real.sqrt (χ.conductor : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity), one_pow]
    exact_mod_cast hc1
  calc Real.sqrt (χ.conductor : ℝ) * (‖err ηc χ.primitiveCharacter (δ / 49) (x / 49)‖ / 49)
      ≤ Real.sqrt (χ.conductor : ℝ) * ((3e-13 / (χ.conductor : ℝ) +
          (650000 / Real.sqrt (χ.conductor : ℝ) + 80) / (Real.sqrt x / 7)) / 49) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb (by norm_num))
          (Real.sqrt_nonneg _)
    _ ≤ 2.1941e-7 / 49 :=
        star_numR _ _ _ (Real.mul_self_sqrt (Nat.cast_nonneg _)) hs1 (sqrt_c_le _ hc3)
          (sqrt_x_ge x hx)

/-- **`ET_{η₊,600000} ≤ 1.4490e-8`** (`eq:zakone1`) from `MalporR` at `q = 1` (generated from
`MajSp.et_plus`; was `1.1377e-8`). PROVED. -/
theorem et_plusR (ηp : ℝ → ℝ) (h : MalporR ηp) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    ETBound ηp 600000 x 1.4490e-8 := by
  intro δ hδ
  have hδ' : |δ| ≤ 600000 * (Nat.gcd 1 2 : ℝ) / ((1 : ℕ) : ℝ) := by
    simp only [Nat.gcd_one_left, Nat.cast_one, mul_one, div_one]
    exact hδ
  have hb := (h x (le_trans (by norm_num) hx) 1 le_rfl (fun _ => by norm_num)
    (fun _ => by norm_num) 1 DirichletCharacter.isPrimitive_one_level_one δ hδ').2 rfl
  have h2 : 320000 / Real.sqrt x ≤ 320000 / (22135943 * 10 ^ 6) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (sqrt_x_ge x hx)
  have h4 : (3.34e-11 : ℝ) + 320000 / (22135943 * 10 ^ 6) ≤ 1.4490e-8 := by norm_num
  linarith

/-- **`|err_{η*,χ_T}(0,x)| ≤ 1.71973e-8`** from `CoprarR` at `q = 1` and the scaling (generated
from `MajSp.et0_star`). PROVED. `CoprarR` gives `4.19538e-9`; the constant `1.71973e-8` is KEPT, so
`MajSp.zstar_holds` and `MinSp.hex_le` apply unchanged. -/
theorem et0_starR (ηs ηc : ℝ → ℝ) (sc : StarScale ηs ηc) (h : CoprarR ηc) (x : ℝ)
    (hx : 49 * 10 ^ 25 ≤ x) : ‖err ηs (1 : DirichletCharacter ℂ 1) 0 x‖ ≤ 1.71973e-8 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hy : 10 ^ 8 ≤ x / 49 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hb := h (x / 49) hy 1 le_rfl (by norm_num) 1 DirichletCharacter.isPrimitive_one_level_one
    0 (by rw [abs_zero]; positivity)
  simp only [sqrt_div49 x hx0.le, Nat.cast_one, Real.sqrt_one, div_one] at hb
  rw [err_scale ηs ηc sc 1 0 x hx0.ne', zero_div, norm_div, Complex.norm_ofNat]
  have h2 : (650000 + 80) / (Real.sqrt x / 7) ≤ (650000 + 80) / (22135943 * 10 ^ 6 / 7) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [sqrt_x_ge x hx])
  have h3 : ((3e-13 : ℝ) + (650000 + 80) / (22135943 * 10 ^ 6 / 7)) / 49 ≤ 1.71973e-8 := by
    norm_num
  have h4 := div_le_div_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 49)
  linarith

/-- **`Z_{η₊²,2}(x) ≤ 0.640212 log x`** (`eq:malavita`) from `MalheurAtR` and `Λ(n) ≤ log n`
(generated from `MajSp.zplus`: `0.640206 + 5·10⁻⁶ + 500/√x ≤ 0.640212`). PROVED; `MalheurAtR` is
two-sided, so it also forces the summability junk would hide. -/
theorem zplusR (η : ℝ → ℝ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hm : MalheurAtR η x) :
    zk (fun t => η t ^ 2) 2 x ≤ 0.640212 * Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hL := log_ge_one x hx
  have hu : 500 / Real.sqrt x ≤ 500 / (22135943 * 10 ^ 6) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (sqrt_x_ge x hx)
  have hP : x ≤ x * Real.log x := by nlinarith
  have hPu : 500 / Real.sqrt x * (x * Real.log x) ≤
      500 / (22135943 * 10 ^ 6) * (x * Real.log x) :=
    mul_le_mul_of_nonneg_right hu (by linarith)
  unfold MalheurAtR at hm
  have hgf : ∀ n : ℕ, (Λ n) ^ 2 * η ((n : ℝ) / x) ^ 2 ≤
      Λ n * Real.log n * η ((n : ℝ) / x) ^ 2 := fun n => by
    have h1 : (Λ n) ^ 2 ≤ Λ n * Real.log n := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left vonMangoldt_le_log vonMangoldt_nonneg
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hfs : Summable (fun n : ℕ => Λ n * Real.log n * η ((n : ℝ) / x) ^ 2) := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at hm
    have h1 := (abs_le.mp hm).1
    linarith
  have hgs := Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hgf hfs
  have hle := hgs.tsum_le_tsum hgf hfs
  have hup := (abs_le.mp hm).2
  unfold zk
  change (∑' n : ℕ, (Λ n) ^ 2 * η ((n : ℝ) / x) ^ 2) / x ≤ _
  rw [div_le_iff₀ hx0]
  linarith

/-- **Line 3 of `eq:opus111` at the `Z₊` slope `0.640212`** (generated from `MajSp.line3_le`): at
most `61 (log x)² x ≤ 4.41·10⁻¹¹ x²` (the coefficient is `60.467`). -/
theorem line3_leR (x Zp Zs : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hZp : Zp ≤ 0.640212 * Real.log x)
    (hZs0 : 0 ≤ Zs) (hZs : Zs ≤ 0.0362 * Real.log x) :
    (2 * Zp * (24.32 * Real.log x + 0.57) +
        4 * Real.sqrt (Zp * Zs) * (18.57 * Real.log x + 28.39)) * x ≤
      61 * 16 / (22135943 * 10 ^ 6) * x ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hL1 := log_ge_one x hx
  have hL0 : 0 ≤ Real.log x := by linarith
  have hZZ : Zp * Zs ≤ (0.15224 * Real.log x) ^ 2 :=
    calc Zp * Zs ≤ (0.640212 * Real.log x) * (0.0362 * Real.log x) :=
          mul_le_mul hZp hZs hZs0 (by linarith)
      _ = 0.0231756744 * Real.log x ^ 2 := by ring
      _ ≤ 0.0231770176 * Real.log x ^ 2 :=
          mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
      _ = (0.15224 * Real.log x) ^ 2 := by ring
  have hsZ : Real.sqrt (Zp * Zs) ≤ 0.15224 * Real.log x := by
    calc Real.sqrt (Zp * Zs) ≤ Real.sqrt ((0.15224 * Real.log x) ^ 2) := Real.sqrt_le_sqrt hZZ
      _ = 0.15224 * Real.log x := Real.sqrt_sq (by linarith)
  have h3a : 2 * Zp * (24.32 * Real.log x + 0.57) ≤
      2 * (0.640212 * Real.log x) * (24.32 * Real.log x + 0.57) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h3b : 4 * Real.sqrt (Zp * Zs) * (18.57 * Real.log x + 28.39) ≤
      4 * (0.15224 * Real.log x) * (18.57 * Real.log x + 28.39) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hLL : Real.log x ≤ Real.log x ^ 2 := by nlinarith only [hL1]
  have h3c : 2 * (0.640212 * Real.log x) * (24.32 * Real.log x + 0.57) +
      4 * (0.15224 * Real.log x) * (18.57 * Real.log x + 28.39) ≤ 61 * Real.log x ^ 2 := by
    linarith
  have h3x : (2 * Zp * (24.32 * Real.log x + 0.57) +
      4 * Real.sqrt (Zp * Zs) * (18.57 * Real.log x + 28.39)) * x ≤
      61 * Real.log x ^ 2 * x := mul_le_mul_of_nonneg_right (by linarith) hx0.le
  have h3y : 61 * Real.log x ^ 2 * x ≤ 61 * (16 * Real.sqrt x) * x :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (log_sq_le x hx0 hL0) (by norm_num))
      hx0.le
  have h3e : Real.sqrt x * x * (22135943 * 10 ^ 6) ≤ x ^ 2 := by
    have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hsx0 : 0 ≤ Real.sqrt x * x := mul_nonneg (Real.sqrt_nonneg x) hx0.le
    calc Real.sqrt x * x * (22135943 * 10 ^ 6) ≤ Real.sqrt x * x * Real.sqrt x :=
          mul_le_mul_of_nonneg_left (sqrt_x_ge x hx) hsx0
      _ = x * (Real.sqrt x * Real.sqrt x) := by ring
      _ = x ^ 2 := by rw [hsx, sq]
  have h3z : 61 * (16 * Real.sqrt x) * x ≤ 61 * 16 / (22135943 * 10 ^ 6) * x ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
    linarith
  linarith

/-- **`MalheurR` rejects `η₊ = 0`** (generated from `MajSp.malheur_zero`): it is still a two-sided
asymptotic, `≈ 0.64 x log x`, and at `x = 10¹²` the error `5.05·10⁸ log x` cannot absorb it. -/
theorem malheurR_zero : ¬ MalheurR 0 := by
  intro h
  have hm := h (10 ^ 12) le_rfl
  unfold MalheurAtR at hm
  have h0 : (∑' n : ℕ, Λ n * Real.log n * (0 : ℝ → ℝ) ((n : ℝ) / 10 ^ 12) ^ 2) = 0 := by simp
  have hs : Real.sqrt ((10 : ℝ) ^ 12) = 10 ^ 6 := by
    rw [show (10 : ℝ) ^ 12 = (10 ^ 6) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hL : 1 ≤ Real.log ((10 : ℝ) ^ 12) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    have h12 : (2.7182818286 : ℝ) ≤ 10 ^ 12 := by norm_num
    linarith
  have hc1 : (5e-6 + 500 / 10 ^ 6 : ℝ) * 10 ^ 12 = 505000000 := by norm_num
  have hc2 : (0.640206 : ℝ) * 10 ^ 12 = 640206000000 := by norm_num
  have hc3 : (0.021095 : ℝ) * 10 ^ 12 = 21095000000 := by norm_num
  rw [h0, hs, hc1, hc2, hc3] at hm
  have h1 := (abs_le.mp hm).1
  linarith

end Derive

/-- **`HelfMajR` rejects `η₊ = 0` exactly as far as Platt holds** (generated from
`RT.helfMajFull_zero`): the retype is not vacuous. -/
theorem helfMajR_zero (ηc : ℝ → ℝ) (h : HelfMajR 0 ηc) : ¬ RT.PlattFull :=
  fun pf => malheurR_zero (h pf).2.2

section MinorQ

open Principia.Common.TernaryGoldbach.MinSp

open Classical in
/-- **`eq:felipa` from `MalheurAtR`** (generated from `MinSp.felipa`): `S ≤ ∑Λ(n) log n η₊²(n/x)
≤ 0.640212 x log x − 0.021095 x` for `x ≥ 4.9·10²⁶`. -/
theorem felipaR (η : ℝ → ℝ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hm : MalheurAtR η x) :
    sPr η x ≤ (0.640212 * Real.log x - 0.021095) * x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hL := MajSp.log_ge_one x hx
  have hu : 500 / Real.sqrt x ≤ 500 / (22135943 * 10 ^ 6) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (MajSp.sqrt_x_ge x hx)
  have hP : x ≤ x * Real.log x := by nlinarith
  have hPu : 500 / Real.sqrt x * (x * Real.log x) ≤
      500 / (22135943 * 10 ^ 6) * (x * Real.log x) :=
    mul_le_mul_of_nonneg_right hu (by linarith)
  unfold MalheurAtR at hm
  have hfs : Summable (fun n : ℕ => Λ n * Real.log n * η ((n : ℝ) / x) ^ 2) := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at hm
    have h1 := (abs_le.mp hm).1
    linarith
  have hterm : ∀ n : ℕ, (if n.Prime ∧ Real.sqrt x < (n : ℝ) then
      Real.log n ^ 2 * η ((n : ℝ) / x) ^ 2 else 0) ≤ Λ n * Real.log n * η ((n : ℝ) / x) ^ 2 := by
    intro n
    split_ifs with h
    · rw [vonMangoldt_apply_prime h.1]
      exact le_of_eq (by ring)
    · exact mul_nonneg (mul_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)) (sq_nonneg _)
  have hnn : ∀ n : ℕ, 0 ≤ (if n.Prime ∧ Real.sqrt x < (n : ℝ) then
      Real.log n ^ 2 * η ((n : ℝ) / x) ^ 2 else 0) := by
    intro n
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · exact le_refl 0
  have hss := Summable.of_nonneg_of_le hnn hterm hfs
  have hle := hss.tsum_le_tsum hterm hfs
  have hup := (abs_le.mp hm).2
  unfold sPr
  linarith

/-- **`S_{η*}(0,x) ≤ (√(π/2)/49 + 1.71973·10⁻⁸)x` from `CoprarR`** (generated from
`MinSp.sstar_le`, through `et0_starR`; the constant is unchanged). -/
theorem sstar_leR (ηs ηc : ℝ → ℝ) (sc : MajSp.StarScale ηs ηc) (cp : CoprarR ηc)
    (h0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ ηs t ∧ ηs t ≤ 1.414)
    (hl1 : MajSp.l1 ηs = Real.sqrt (Real.pi / 2) / 49) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    sStar ηs x ≤ (1.2533143 / 49 + 1.71973e-8) * x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hT := et0_starR ηs ηc sc cp x hx
  obtain ⟨-, hs2⟩ := MajSp.sqrt_pi_half
  have he0 : ∀ y : ℝ, y = 0 → e y = 1 := fun y hy => by
    rw [hy]
    simp [e]
  have htw : MajSp.twSum ηs (1 : DirichletCharacter ℂ 1) x (0 / x) =
      ((∑' n : ℕ, Λ n * ηs ((n : ℝ) / x) : ℝ) : ℂ) := by
    rw [zero_div, Complex.ofReal_tsum]
    unfold MajSp.twSum
    congr 1
    funext n
    rw [MulChar.one_apply (isUnit_of_subsingleton _), he0 _ (mul_zero _), Complex.ofReal_mul]
    ring
  have hft : MajSp.mainFT ηs 0 = ((MajSp.l1 ηs : ℝ) : ℂ) := by
    unfold MajSp.mainFT MajSp.l1
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [he0 _ (zero_mul t), mul_one, abs_of_nonneg (h0 t (le_of_lt ht)).1]
  have herr : MajSp.err ηs (1 : DirichletCharacter ℂ 1) 0 x =
      (((∑' n : ℕ, Λ n * ηs ((n : ℝ) / x)) / x - MajSp.l1 ηs : ℝ) : ℂ) := by
    unfold MajSp.err
    rw [htw, hft, if_pos (rfl : (1 : ℕ) = 1), Complex.ofReal_sub, Complex.ofReal_div]
  rw [herr, Complex.norm_real, Real.norm_eq_abs] at hT
  have hT' := (abs_le.mp hT).2
  have hl1up : MajSp.l1 ηs ≤ 1.2533143 / 49 := by
    rw [hl1]
    exact div_le_div_of_nonneg_right hs2 (by norm_num)
  have h1 : (∑' n : ℕ, Λ n * ηs ((n : ℝ) / x)) / x ≤ 1.2533143 / 49 + 1.71973e-8 := by linarith
  exact (div_le_iff₀ hx0).mp h1

end MinorQ

/-! ## (4) `lem:drujal` at the new `ET`/`E` -/

section Drujal

open Principia.Common.TernaryGoldbach.DS

/-- **Link [A] at cap `100`, at the RETYPED `ET`/`E`** (generated from `DS.DrujalE100`:
`ETBound 1.1377e-8 ↦ 1.4490e-8`, `EBound 2.3921e-8 ↦ 4.2813e-8`, all else unchanged). PRODUCED by
the spine (`drujalE100R_of_spine`); STRONGER than `DS.DrujalE100` (`drujalE100_of_R`). -/
def DrujalE100R (η : ℝ → ℝ) : Prop :=
  MemLp η 1 (volume.restrict (Set.Ioi 0)) → (∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955) →
    MajSp.l1 η ≤ 1.2 → MajSp.l2 η ≤ 0.81 →
      ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → MajSp.ETBound η 600000 x 1.4490e-8 →
        MajSp.EBound η x 4.2813e-8 → MajSp.amaj η x ≤ 100

/-- **The upper arithmetic at the new `ET`/`E`** (generated from `DS.aArith`): the sum is
`63.69 ≤ 100`. -/
theorem aArithR (S l2 l1 nag harm K : ℝ) (hS : S ≤ 48.44) (hl20 : 0 ≤ l2)
    (hl2 : l2 ≤ 0.81) (hl10 : 0 ≤ l1) (hl1 : l1 ≤ 1.2) (hn : nag ≤ 3.125) (hh : harm ≤ 25.84)
    (hK : K ≤ 1e-6) :
    2 * S * l2 ^ 2 + (1200000 * nag * (1.4490e-8 * (2 * l1 + 1.4490e-8)) +
      1200000 * harm * (4.2813e-8) ^ 2 + K) ≤ 100 := by
  have hl2s : l2 ^ 2 ≤ 0.81 ^ 2 := pow_le_pow_left₀ hl20 hl2 2
  have h1 : S * l2 ^ 2 ≤ 48.44 * 0.81 ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hS) (sq_nonneg l2)]
  have hT : 1.4490e-8 * (2 * l1 + 1.4490e-8) ≤ 1.4490e-8 * (2 * 1.2 + 1.4490e-8) := by linarith
  have hT0 : 0 ≤ 1.4490e-8 * (2 * l1 + 1.4490e-8) := by positivity
  have h2 : nag * (1.4490e-8 * (2 * l1 + 1.4490e-8)) ≤
      3.125 * (1.4490e-8 * (2 * 1.2 + 1.4490e-8)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) hT0]
  have h3 : harm * (4.2813e-8) ^ 2 ≤ 25.84 * (4.2813e-8) ^ 2 :=
    mul_le_mul_of_nonneg_right hh (by norm_num)
  linarith

/-- **`DrujalE100R` FROM THE SPINE** (generated from `DS.drujalE100_of_spine`): the same four
links (`PerArc`, `ArcInt`, `MardiQ`, `KSmall`), arithmetic `aArithR`. Application only. -/
theorem drujalE100R_of_spine (η : ℝ → ℝ) (pa : PerArc η) (ai : ArcInt η) (mq : MardiQ η)
    (ks : KSmall η) : DrujalE100R η := fun _ _ hl1 hl2 x hx hT hE =>
  upper_close _ _ _ _ (juto η pa ai x hx (ks x hx).1 _ _ hT hE) (lRD_le η mq)
    (aArithR sR (MajSp.l2 η) (MajSp.l1 η) nagS harmS (kAgg η x) sR_le (MajSp.l2_nonneg _) hl2
      (MajSp.l1_nonneg _) hl1 nagS_le harmS_le' (ks x hx).2)

end Drujal

/-- **Link [J] at a parametric floor `J₀`, at the RETYPED `ET`/`E`** (generated from
`OC.DrujalLowP`: `ETBound 1.1377e-8 ↦ 1.4490e-8`, `EBound 2.3921e-8 ↦ 4.2813e-8`). STRONGER than
`OC.DrujalLowP J₀` (`drujalLowP_of_R`); PRODUCED at `J₀ = 8.55451` (`drujalLowPR_of_spine`). -/
def DrujalLowPR (J₀ : ℝ) (η ηo : ℝ → ℝ) : Prop :=
  MemLp η 1 (volume.restrict (Set.Ioi 0)) → (∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955) →
    MajSp.l1 η ≤ 0.8673 →
    (∃ S : Finset ℝ, ∀ t : ℝ, 0 ≤ t → t ∉ S → ContDiffAt ℝ 3 ηo t) →
    Integrable (iteratedDeriv 3 ηo) (volume.restrict (Set.Ioi 0)) →
    MemLp ηo 2 (volume.restrict (Set.Ioi 0)) →
    0.8 ≤ MajSp.l2 ηo → MajSp.l2 ηo ≤ 0.8002 →
    MajSp.l2 (fun t => η t - ηo t) ≤ 1.7999e-4 → MajSp.l1 (iteratedDeriv 3 ηo) ≤ 40 →
    ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → MajSp.ETBound η 600000 x 1.4490e-8 →
      MajSp.EBound η x 4.2813e-8 → J₀ ≤ MajSp.amaj η x

section DrujalLow

open Principia.Common.TernaryGoldbach.SF

/-- **THE NEW `J` FLOOR** (generated from `SF.jArithP`): at `ET = 1.4490·10⁻⁸`, `E = 4.2813·10⁻⁸`,
`2·6.76·0.6397018 − 0.0942538 − 5.68·10⁻⁸ − 10⁻⁶ = 8.5545135 ≥ 8.55451` (margin `3.45·10⁻⁶`; it
was `8.57476` at the printed `ET`/`E`). -/
theorem jArithPR (S lo d l3 l1 nag harm K : ℝ) (hS : 6.76 ≤ S) (hlo : 0.8 ≤ lo) (hd0 : 0 ≤ d)
    (hd : d ≤ 1.7999e-4) (hl30 : 0 ≤ l3) (hl3 : l3 ≤ 40) (hl10 : 0 ≤ l1) (hl1 : l1 ≤ 0.8673)
    (hn : nag ≤ 3.125) (hh : harm ≤ 25.84) (hK : K ≤ 1e-6) :
    8.55451 ≤ 2 * S * (lo ^ 2 - (2 * lo * d + d ^ 2) - l3 ^ 2 / (163840 * Real.pi ^ 6)) -
      (1200000 * nag * (1.4490e-8 * (2 * l1 + 1.4490e-8)) +
        1200000 * harm * (4.2813e-8) ^ 2 + K) := by
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
  have hT : 1.4490e-8 * (2 * l1 + 1.4490e-8) ≤ 1.4490e-8 * (2 * 0.8673 + 1.4490e-8) := by
    linarith
  have hT0 : 0 ≤ 1.4490e-8 * (2 * l1 + 1.4490e-8) := by positivity
  have h2 : nag * (1.4490e-8 * (2 * l1 + 1.4490e-8)) ≤
      3.125 * (1.4490e-8 * (2 * 0.8673 + 1.4490e-8)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) hT0]
  have h3 : harm * (4.2813e-8) ^ 2 ≤ 25.84 * (4.2813e-8) ^ 2 :=
    mul_le_mul_of_nonneg_right hh (by norm_num)
  linarith

/-- The closing step of the lower half at the floor `8.55451` (generated from `SF.lower_closeP`). -/
theorem lower_closePR (A L U R : ℝ) (hj : |A - L| ≤ R) (hL : U ≤ L) (ha : 8.55451 ≤ U - R) :
    8.55451 ≤ A := by
  have h := (abs_le.mp hj).1
  linarith

/-- **`DrujalLowPR 8.55451` FROM THE SPINE** (generated from `SF.drujalLowP_of_spine`): the same
five links (`PerArc`, `ArcInt`, `BandQ`, `TailQ`, `KSmall`), arithmetic `jArithPR`. -/
theorem drujalLowPR_of_spine (η ηo : ℝ → ℝ) (pa : DS.PerArc η) (ai : DS.ArcInt η)
    (bq : DS.BandQ η ηo) (tq : DS.TailQ ηo) (ks : DS.KSmall η) : DrujalLowPR 8.55451 η ηo :=
  fun _ _ hl1 _ _ _ hlo1 _ hdiff hl3 x hx hT hE =>
    lower_closePR _ _ _ _ (DS.juto η pa ai x hx (ks x hx).1 _ _ hT hE) (DS.lRD_ge η ηo bq tq)
      (jArithPR DS.sR (MajSp.l2 ηo) (MajSp.l2 (fun t => η t - ηo t))
        (MajSp.l1 (iteratedDeriv 3 ηo))
        (MajSp.l1 η) DS.nagS DS.harmS (DS.kAgg η x) sR_ge_sharp hlo1 (MajSp.l2_nonneg _) hdiff
        (MajSp.l1_nonneg _) hl3 (MajSp.l1_nonneg _) hl1 DS.nagS_le DS.harmS_le' (ks x hx).2)

end DrujalLow

/-! ## (4c) The regenerated `lem:drujal` links are STRONGER than the originals at the same floor

They ask for the same conclusion under WEAKER `err` hypotheses (the larger `ET`, `E`), and they are
produced from the same spine links; so the regeneration moved an obligation from `HelfMaj` to
nothing. -/

/-- `ETBound` weakens as the bound grows. -/
theorem etBound_mono (η : ℝ → ℝ) (s x T T' : ℝ) (hT : T ≤ T') (h : MajSp.ETBound η s x T) :
    MajSp.ETBound η s x T' :=
  fun δ hδ => le_trans (h δ hδ) hT

/-- `EBound` weakens as the bound grows. -/
theorem eBound_mono (η : ℝ → ℝ) (x E E' : ℝ) (hE : E ≤ E') (h : MajSp.EBound η x E) :
    MajSp.EBound η x E' :=
  fun q h1 h2 χ δ hδ => le_trans (h q h1 h2 χ δ hδ) hE

/-- **`DrujalE100R → DS.DrujalE100`**. -/
theorem drujalE100_of_R (η : ℝ → ℝ) (h : DrujalE100R η) : DS.DrujalE100 η :=
  fun h1 h2 h3 h4 x hx hT hE => h h1 h2 h3 h4 x hx
    (etBound_mono η 600000 x _ _ (by norm_num) hT) (eBound_mono η x _ _ (by norm_num) hE)

/-- **`DrujalLowPR J₀ → OC.DrujalLowP J₀`**. -/
theorem drujalLowP_of_R (J₀ : ℝ) (η ηo : ℝ → ℝ) (h : DrujalLowPR J₀ η ηo) :
    OC.DrujalLowP J₀ η ηo :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 x hx hT hE => h h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 x hx
    (etBound_mono η 600000 x _ _ (by norm_num) hT) (eBound_mono η x _ _ (by norm_num) hE)

/-! ## (5) The major arcs at `1.0563578`, the split at `0.000205` -/

section Major

open Principia.Common.TernaryGoldbach.EN

/-- **Line 2 of `eq:opus111` at `A ≤ 100` and the RETYPED `E*`, `E₊`** (generated from
`DS.line2_le_d100`): at most `2.1941e-7/49·100 + 4.2813e-8·1.6812·(10 + 1.6812·0.81)·0.20204`. -/
theorem line2_le_d100R (A lp ls : ℝ) (hA : A ≤ 100) (hlp : lp ≤ 0.81) (hls0 : 0 ≤ ls)
    (hls : ls ^ 2 ≤ 2 / 49) :
    2.1941e-7 / 49 * A + 4.2813e-8 * 1.6812 * (Real.sqrt A + 1.6812 * lp) * ls ≤
      2.1941e-7 / 49 * 100 + 4.2813e-8 * 1.6812 * ((10 + 1.6812 * 0.81) * 0.20204) := by
  have hsA : Real.sqrt A ≤ 10 := by
    refine le_trans (Real.sqrt_le_sqrt hA) ?_
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hls' : ls ≤ 0.20204 := by nlinarith
  have hB' : Real.sqrt A + 1.6812 * lp ≤ 10 + 1.6812 * 0.81 := by linarith
  have hBl : (Real.sqrt A + 1.6812 * lp) * ls ≤ (10 + 1.6812 * 0.81) * 0.20204 :=
    mul_le_mul hB' hls' hls0 (by norm_num)
  linarith

/-- **The major arithmetic at `C₀ ≥ 1.3198`, `A ≤ 100`, at `HelfMajR`** (generated from
`MC0.arith_close_c0`): net `1.0563588113… ≥ 1.0563578` (margin `1.01·10⁻⁶`, units `x²/49`); the
retyped `E*`, `E₊` cost `1.2161·10⁻⁵` in line 2 (the net was `1.0563709718…`). -/
theorem arith_close_c0R (x s C0 Cc lo l3 lp ls A Zp Zs : ℝ) (I : ℂ)
    (hx : 49 * 10 ^ 25 ≤ x) (hs1 : 1.2533139 ≤ s) (hs2 : s ≤ 1.2533143)
    (hC0 : 1.3198 ≤ C0) (hCc : (s * lo ^ 2 - 0.000914) / 49 ≤ Cc)
    (hlo1 : 0.8 ≤ lo) (hlo2 : lo ≤ 0.8002) (hl3 : 0 ≤ l3) (hl3' : l3 ≤ 40)
    (hlp : lp ≤ 0.81) (hls0 : 0 ≤ ls) (hls : ls ^ 2 ≤ 2 / 49)
    (hA : A ≤ 100) (hZp : Zp ≤ 0.640212 * Real.log x)
    (hZs0 : 0 ≤ Zs) (hZs : Zs ≤ 0.0362 * Real.log x)
    (hI : ‖I - ((C0 * Cc * x ^ 2 : ℝ) : ℂ)‖ ≤
      (2.82643 * lo ^ 2 * (2 + 2.25e-4) * 2.25e-4 +
          (4.31004 * lo ^ 2 + 0.0012 * l3 ^ 2 / 8 ^ 5) / 150000) * (s / 49) * x ^ 2 +
        (2.1941e-7 / 49 * A + 4.2813e-8 * 1.6812 * (Real.sqrt A + 1.6812 * lp) * ls) * x ^ 2 +
        (2 * Zp * (24.32 * Real.log x + 0.57) +
          4 * Real.sqrt (Zp * Zs) * (18.57 * Real.log x + 28.39)) * x) :
    1.0563578 * x ^ 2 / 49 ≤ I.re := by
  have hX : 0 ≤ x ^ 2 := sq_nonneg x
  have hm := mul_le_mul_of_nonneg_right (MC0.main_ge_c0 s C0 Cc lo hs1 hC0 hCc hlo1) hX
  have h1 := mul_le_mul_of_nonneg_right (line1_le_b27 s lo l3 hs1 hs2 hlo1 hlo2 hl3 hl3') hX
  have h2 := mul_le_mul_of_nonneg_right (line2_le_d100R A lp ls hA hlp hls0 hls) hX
  have h3 := line3_leR x Zp Zs hx hZp hZs0 hZs
  have habs := Complex.abs_re_le_norm (I - ((C0 * Cc * x ^ 2 : ℝ) : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re] at habs
  have hlow := (abs_le.mp (le_trans habs hI)).1
  linarith only [hlow, hm, h1, h2, h3, hX]

/-- **(7.25) at `1.0563578` from `HelfMajR`** (generated from `MC0.majorAt_c0`; application only).
`RW.NefumoW` takes its `E` bounds as ARGUMENTS, so its statement is unchanged; its instantiation
moves to `E₊ = 4.2813e-8`, `E* = 2.1941e-7/49`. `A ≤ 100` comes from `DrujalE100R`. -/
theorem majorAt_c0R (ηp ηs ηo ηc : ℝ → ℝ) (hm : HelfMajR ηp ηc)
    (sc : MajSp.StarScale ηs ηc) (rg : RW.RegW ηp ηs ηo) (nf : RW.NefumoW ηp ηs ηo)
    (dj : DrujalE100R ηp) (cl : CLowerE ηo ηs) (nm : NormsB27 ηp ηs ηo)
    (sn : MajSp.SupN ηp ηs) (pf : RT.PlattFull) : RT.MajorLowerAt 1.0563578 ηp ηs := by
  intro N hodd hN
  obtain ⟨mp, cp, mh⟩ := hm pf
  obtain ⟨hlo1, hlo2, hdiff, hl3, hld, hl1s, hls, hl1p, hl2p⟩ := nm
  have hx := MajSp.helfX_big N hN
  have hEp := eb_plusR ηp mp (helfgottX N) hx
  have hEs := eb_starR ηs ηc sc cp (helfgottX N) hx
  have hET := et_plusR ηp mp (helfgottX N) hx
  have hT0 := et0_starR ηs ηc sc cp (helfgottX N) hx
  have hZp := zplusR ηp (helfgottX N) hx (mh (helfgottX N) (MajSp.x12_le _ hx))
  have hZs := MajSp.zstar_holds ηs sn.2.2.1 sn.2.2.2.2 hl1s (helfgottX N) hx hT0
  have hA := dj rg.1 sn.1 hl1p hl2p (helfgottX N) hx hET hEp
  obtain ⟨hLp, hLs⟩ := MajSp.ls_link ηp ηs sn (helfgottX N) hx
  have hlt := eps_lt_b27 _ _ hdiff hlo1
  have hnef := nf rg 2.25e-4 eps_nonneg_b27 hlt N (MajSp.N_one N hN) (helfgottX N) hx
    4.2813e-8 (2.1941e-7 / 49) hEp hEs (18.57 * Real.log (helfgottX N) + 28.39)
    (24.32 * Real.log (helfgottX N) + 0.57) hLp hLs
  rw [hl1s] at hnef
  have hC := cl hld N hodd hN
  obtain ⟨hs1, hs2⟩ := MajSp.sqrt_pi_half
  have hC0 := SSP.sing3_ge_P N hodd
  exact arith_close_c0R (helfgottX N) (Real.sqrt (Real.pi / 2)) (SingularSeries.sing3 N)
    (MajSp.ccon ηo ηs ((N : ℝ) / helfgottX N)) (MajSp.l2 ηo) (MajSp.l1 (iteratedDeriv 3 ηo))
    (MajSp.l2 ηp) (MajSp.l2 ηs) (MajSp.amaj ηp (helfgottX N))
    (MajSp.zk (fun t => ηp t ^ 2) 2 (helfgottX N)) (MajSp.zk (fun t => ηs t ^ 2) 2 (helfgottX N))
    _ hx hs1 hs2 hC0 hC hlo1 hlo2 (MajSp.l1_nonneg _) hl3 hl2p (MajSp.l2_nonneg _)
    hls hA hZp (MajSp.zk_sq_nonneg _ _ (MajSp.x_nonneg _ hx)) hZs hnef

/-- **THE CHEBYSHEV SPLIT at `c_maj' = 1.0563578`** (generated from `SC.helfAt_smooth_cheb`):
`(0.0409578)(490/989)²/49 − 13.73·10⁻⁹ = 2.0516868·10⁻⁴ ≥ 0.000205` (margin `1.69·10⁻⁷`), so the
minor target `1.0154` is KEPT. -/
theorem helfAt_smooth_chebR (ηp ηs : ℝ → ℝ) (sb : Smooth.SupBounds ηp ηs)
    (mj : RT.MajorLowerAt 1.0563578 ηp ηs) (mn : RT.MinorUpperAt 1.0154 ηp ηs) :
    HelfgottAt 0.000205 := by
  have sm := RT.summ_of_majorAt (by norm_num) ηp ηs mj
  have ci := SmCI.circleId_of_summ ηp ηs sm
  refine (RT.helfgottAt_iff 0.000205).mpr fun H hodd hH => ⟨ηp, ηs, sb.1, sb.2, ?_⟩
  have hW := RT.weighted_lower_at 1.0563578 1.0154 ηp ηs sm ci mj mn H hodd hH
  have hc : (1.0563578 - 1.0154 : ℝ) = 0.0409578 := by norm_num
  rw [hc] at hW
  have hP := SmPP.pp_crude ηp ηs sb H hodd hH
  have hH0 : (0 : ℝ) ≤ (490 : ℝ) / 989 * H := by positivity
  have hx2 : ((490 : ℝ) / 989 * H) ^ 2 ≤ helfgottX H ^ 2 :=
    pow_le_pow_left₀ hH0 (Smooth.helfX_ge H) 2
  have hx2' : (490 : ℝ) ^ 2 / 989 ^ 2 * (H : ℝ) ^ 2 ≤ helfgottX H ^ 2 :=
    le_of_eq_of_le (by ring) hx2
  have hE := SmPP.ppErr_le H hH
  have hH2 : (0 : ℝ) ≤ (H : ℝ) ^ 2 := sq_nonneg _
  linarith

/-- **`HelfgottAt 0.000205` from `HelfMajR`** (generated from `SC.helfgottAt_cheb`): the minor
side is the single hypothesis `RT.MinorUpperAt 1.0154 η₊ η*`. -/
theorem helfgottAt_chebR (pf : RT.PlattFull)
    (hm : HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (rg : RW.RegW HW.etaPlus HW.etaStar HW.etaCirc)
    (nf : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc) (dj : DrujalE100R HW.etaPlus)
    (cl : CLowerE HW.etaCirc HW.etaStar) (hb : BandSharp27)
    (mn : RT.MinorUpperAt 1.0154 HW.etaPlus HW.etaStar) : HelfgottAt 0.000205 :=
  helfAt_smooth_chebR HW.etaPlus HW.etaStar BL.supBounds_helf
    (majorAt_c0R HW.etaPlus HW.etaStar HW.etaCirc (HW.mconv HW.eta2 HW.phi) hm
      RT.starScale_helf rg nf dj cl (normsB27_helf hb) supN_helf pf) mn

end Major

/-! ## (6) The minor arcs at `1.0154`, `FelipaAt` derived -/

section MinorL

open Principia.Common.TernaryGoldbach.MinSp
open Principia.Common.TernaryGoldbach.OL

/-- **`HelfMajR` supplies `FelipaAt 0.640212`** (generated from `OL.felipaAt_helf`): `MalheurR` at
every `x ≥ 10¹²`, through `felipaR`. -/
theorem felipaAt_helfR (ηp ηc : ℝ → ℝ) (hpf : RT.PlattFull) (hm : HelfMajR ηp ηc) :
    FelipaAt 0.640212 ηp :=
  fun x hx => felipaR ηp x hx ((hm hpf).2.2 x (MajSp.x12_le _ hx))

/-- **`FelipaAt 0.6406 η₊` DERIVED from `HelfMajR`** (generated from `OL.felipaAt_6406_of_helf`:
`0.640212 ≤ 0.6406`, slack `3.88·10⁻⁴`). The retype repairs F4, so `FelipaAt` leaves the headline.
-/
theorem felipaAt_6406R (hpf : RT.PlattFull)
    (hm : HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi)) : FelipaAt 0.6406 HW.etaPlus :=
  felipaAt_mono 0.640212 0.6406 (by norm_num) HW.etaPlus (felipaAt_helfR _ _ hpf hm)

/-- **THE SPINE of (7.48) on the corrected `L`, at `HelfMajR`** (generated from
`OL.minor_of_mnum_L`): `RT.HelfMajFull ↦ HelfMajR`, `OC.DrujalLowP ↦ DrujalLowPR`, and the
`ET`/`E`/`S_{η*}(0,x)` inputs from `et_plusR`, `eb_plusR`, `sstar_leR`. Application only. -/
theorem minor_of_mnum_LR (c cM J₀ p₀ fs : ℝ)
    (hc : (Real.sqrt (1.2533143 * (cM + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤ c)
    (hcM : 0 ≤ cM + 3.7e-4) (hJ0 : 8.4031e-12 ≤ J₀)
    (hp : p₀ ≤ (Real.sqrt J₀ - Real.sqrt 8.4031e-12) ^ 2) (hp0 : 8.3599 ≤ p₀)
    (ηp ηs ηo ηc φ : ℝ → ℝ) (hm : HelfMajR ηp ηc)
    (hpf : RT.PlattFull) (hsc : MajSp.StarScale ηs ηc) (hrg : RW.RegW ηp ηs ηo)
    (hnm : EN.NormsB27 ηp ηs ηo) (hsn : MajSp.SupN ηp ηs) (hoh : OstopHyp ηp ηs φ)
    (hfe : FelipaAt fs ηp) (hos : OstopL ηp ηs φ) (hdl : DrujalLowPR J₀ ηp ηo)
    (hl1 : MajSp.l1 ηp ≤ 0.8673) (hdu : Dubistdie ηp) (hpl : PhiL1 φ)
    (hla : LamberNumL φ fs) (hmn : MNumL φ p₀ cM fs) : RT.MinorUpperAt c ηp ηs := by
  intro N _ hN
  obtain ⟨mp, cp, -⟩ := hm hpf
  obtain ⟨hlo1, hlo2, hdiff, hl3, -, hl1s, -, -, -⟩ := hnm
  have hx := MajSp.helfX_big N hN
  have hx0 := x_pos (helfgottX N) hx
  obtain ⟨b, hb⟩ := exists_supFn ηp hoh.2.2.2.2.1
  have hZ := hos hoh b hb (helfgottX N) hx
  have hS := hfe (helfgottX N) hx
  have hS0 := sPr_nonneg ηp (helfgottX N)
  have hE := hdu hsn.1 hsn.2.1 b hb (helfgottX N) hx
  have hA := hdl hrg.1 hsn.1 hl1 hrg.2.2.2.2.1 hrg.2.2.2.2.2.1 hrg.2.2.2.2.2.2
    hlo1 hlo2 hdiff hl3 (helfgottX N) hx (et_plusR ηp mp _ hx) (eb_plusR ηp mp _ hx)
  have hP := OC.pje_le_p J₀ p₀ ηp b (helfgottX N) hx0.le hJ0 hp hA hE
  have hM := m_le_L φ ηp b p₀ cM fs (helfgottX N) hx hmn hS0 hS hP
  have hT := t_le_L φ ηp b fs (helfgottX N) hx hla hS
    (le_trans (mul_le_mul_of_nonneg_right hp0 hx0.le) hP)
  have hSt := sstar_leR ηs ηc hsc cp hsn.2.2.1 hl1s (helfgottX N) hx
  have hSE := hex_le _ _ (helfgottX N) hx0.le (sStar_nonneg ηs hsn.2.2.1 _ hx0) hSt hE
  exact DS.z_close_d _ _ _ _ _ _ c cM hZ (MajSp.l1_nonneg φ) (phi_l1_le φ hpl) hx0.le
    (DS.mt_le_d _ _ cM _ hM hT) hcM hSE hc

/-- **`RT.MinorUpperAt c η₊ η*` on Helfgott's weights at `HelfMajR`**, generic in
`(c, cM, J₀, p₀, fs)` (generated from `OL.minorAt_ostopL_helf`). Application only. -/
theorem minorAt_ostopL_helfR (c cM J₀ p₀ fs : ℝ)
    (hc : (Real.sqrt (1.2533143 * (cM + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤ c)
    (hcM : 0 ≤ cM + 3.7e-4) (hJ0 : 8.4031e-12 ≤ J₀)
    (hp : p₀ ≤ (Real.sqrt J₀ - Real.sqrt 8.4031e-12) ^ 2) (hp0 : 8.3599 ≤ p₀)
    (pf : RT.PlattFull) (hm : HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (hfe : FelipaAt fs HW.etaPlus) (hos : OstopL HW.etaPlus HW.etaStar HW.phi)
    (hdl : DrujalLowPR J₀ HW.etaPlus HW.etaCirc) (hla : LamberNumL HW.phi fs)
    (hmn : MNumL HW.phi p₀ cM fs) : RT.MinorUpperAt c HW.etaPlus HW.etaStar :=
  minor_of_mnum_LR c cM J₀ p₀ fs hc hcM hJ0 hp hp0 HW.etaPlus HW.etaStar HW.etaCirc
    (HW.mconv HW.eta2 HW.phi) HW.phi hm pf RT.starScale_helf RW.regW_helf
    (EN.normsB27_helf BS.band_sharp) EN.supN_helf RW.ostopHyp_helf_full hfe hos hdl
    DS.l1_etaPlus_sharp (DB.dubistdie_all HW.etaPlus) RW.phiL1_helf hla hmn

/-- `8.4031·10⁻¹² ≤ 8.55451` (generated from `OL.hJ0_8574`). -/
theorem hJ0_8545 : (8.4031e-12 : ℝ) ≤ 8.55451 := by norm_num

/-- **`J/x ≥ 8.55451` still gives the floor `8.54`**: `(√8.55451 − √8.4031·10⁻¹²)² = 8.5544930`
(margin `1.45·10⁻²`; generated from `OL.floor_854`). -/
theorem floor_854R : (8.54 : ℝ) ≤ (Real.sqrt 8.55451 - Real.sqrt 8.4031e-12) ^ 2 := by
  have ha2 : Real.sqrt 8.55451 ^ 2 = 8.55451 := Real.sq_sqrt (by norm_num)
  have hc2 : Real.sqrt 8.4031e-12 ^ 2 = 8.4031e-12 := Real.sq_sqrt (by norm_num)
  have ha0 : 0 ≤ Real.sqrt 8.55451 := Real.sqrt_nonneg _
  have hc0 : 0 ≤ Real.sqrt 8.4031e-12 := Real.sqrt_nonneg _
  have ha3 : Real.sqrt 8.55451 ≤ 3 := by nlinarith
  have hc3 : Real.sqrt 8.4031e-12 ≤ 3e-6 := by nlinarith
  have hac : Real.sqrt 8.55451 * Real.sqrt 8.4031e-12 ≤ 3 * 3e-6 :=
    mul_le_mul ha3 hc3 hc0 (by norm_num)
  nlinarith

/-- **`RT.MinorUpperAt 1.0154 η₊ η*` at `HelfMajR`** (generated from `OL.minorAt_ostopL_cheb`):
`cM = 0.8095`, `fs = 0.6406`, `J₀ = 8.55451`, `p₀ = 8.54`. `FelipaAt 0.6406` is DERIVED
(`felipaAt_6406R`), no longer a hypothesis. OPEN: `RT.PlattFull`, `HelfMajR`, `OL.OstopL`,
`DrujalLowPR 8.55451`, `OL.MNumL HW.phi 8.54 0.8095 0.6406`. Application only. -/
theorem minorAt_ostopL_chebR (pf : RT.PlattFull)
    (hm : HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (hos : OstopL HW.etaPlus HW.etaStar HW.phi)
    (hdl : DrujalLowPR 8.55451 HW.etaPlus HW.etaCirc)
    (hmn : MNumL HW.phi 8.54 0.8095 0.6406) : RT.MinorUpperAt 1.0154 HW.etaPlus HW.etaStar :=
  minorAt_ostopL_helfR 1.0154 0.8095 8.55451 8.54 0.6406 close_cheb cM_cheb hJ0_8545
    floor_854R hp0_854 pf hm (felipaAt_6406R pf hm) hos hdl lamberNumL_helf hmn

end MinorL

end Principia.Common.TernaryGoldbach.MR
