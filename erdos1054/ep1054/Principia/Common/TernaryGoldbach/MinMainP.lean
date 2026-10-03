/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MinMainTotals
import Principia.Common.TernaryGoldbach.OstopP

set_option autoImplicit false

/-!
# The Totals reach `OP.MinMainP 0.811 45.7575`: the attachment check of the new constants

`MinMainTotals.lean` typechecks the book's Totals (A0-A10) to `MT.MinMain1At 0.811 45.7575` over
the three named piece bounds, and fences the typed `(0.5, 22.7538)` (`MT.not_arith_typed`). Here:

* `krawP_eq` : `OP.krawP c05 C = MT.krawAt c05 C` BY `rfl` — the parametric `eq:kraw` of
  `OstopP.lean` IS the object the Totals bound (and `lToscaP_eq` for `L`);
* `minMainP_iff` : `OP.MinMainP c05 C ↔ MT.MinMain1At c05 C ∧ MT.MinMain2L` (generated from
  `MT.minMainL_iff`);
* **`minMainP_of_pieces`** : `TypeI1 → TypeI2 → TypeII → MinMain2L → OP.MinMainP 0.811 45.7575`.
  So the constants `OstopP` is instantiated at are EXACTLY the ones the book's route delivers.

## The verifier's `c₀'` flag, typechecked

The verifier flagged that `lem:bostb1`'s main term carries `min(1, 4c₀'/δ²)`, where `MT.bI1`
types `min(1, c₀'/δ²)` (`MT.capM 0.798437`). `bI1W` is `MT.bI1` with `capM (4·0.798437)`; since
`capM` grows in its constant (`capM_mono`), `bI1 ≤ bI1W` and `TypeI1W` is the WEAKER hypothesis
(`typeI1W_of`). The A9 step `min(1, 4c₀'/δ²) ≤ 2/δ₀` still holds (`capM_le_W`, from `MT.capM_le`:
`4c₀' = 3.193748 ≤ 64`; pointwise it is `c₀' ≤ 8δ₀`, `c0p_le`), and the whole Totals arithmetic
closes at the same `(0.811, 45.7575)` with `bI1W` (`arith_811W`, generated from `MT.arith_811`),
so `minMainP_of_piecesW` reaches `OP.MinMainP 0.811 45.7575` from `TypeI1W`: CONFIRMED.
-/

namespace Principia.Common.TernaryGoldbach.MMP

open ArithmeticFunction Principia.Common.Goldbach
open scoped ArithmeticFunction
open Principia.Common.TernaryGoldbach.MT

/-! ## (1) The attachment -/

/-- **`OP.lToscaP C` IS `MT.lToscaAt C`**, by `rfl`. -/
theorem lToscaP_eq (C : ℝ) : OP.lToscaP C = MT.lToscaAt C :=
  rfl

/-- **`OP.krawP c05 C` IS `MT.krawAt c05 C`**, by `rfl`: `OstopP`'s `eq:kraw` is the Totals'. -/
theorem krawP_eq (c05 C : ℝ) : OP.krawP c05 C = MT.krawAt c05 C :=
  rfl

/-- **`OP.MinMainP c05 C` IS its first case `MT.MinMain1At c05 C` and `MT.MinMain2L`**
(generated from `MT.minMainL_iff`). -/
theorem minMainP_iff (c05 C : ℝ) : OP.MinMainP c05 C ↔ MinMain1At c05 C ∧ MinMain2L := by
  constructor
  · intro h
    exact ⟨fun Y hY α δ a q hq hg h2 hQ hδ hy => (h Y hY α δ a q hq hg h2 hQ hδ).1 hy,
      fun Y hY α δ a q hq hg h2 hQ hδ hy => (h Y hY α δ a q hq hg h2 hQ hδ).2 hy⟩
  · rintro ⟨h1, h2⟩ Y hY α δ a q hq hg h2α hQ hδ
    exact ⟨h1 Y hY α δ a q hq hg h2α hQ hδ, h2 Y hY α δ a q hq hg h2α hQ hδ⟩

/-- **THE ATTACHMENT: the Totals reach `OP.MinMainP 0.811 45.7575`** from the three named piece
bounds (`MT.minMainL1c_of_pieces`) and the second case. Application only. -/
theorem minMainP_of_pieces (h1 : MT.TypeI1) (h2 : MT.TypeI2) (h3 : MT.TypeII)
    (h4 : MT.MinMain2L) : OP.MinMainP 0.811 45.7575 :=
  (minMainP_iff 0.811 45.7575).2 ⟨MT.minMainL1c_of_pieces h1 h2 h3, h4⟩

/-- **The new hypothesis is WEAKER than the old**: `OL.MinMainL` (at `(0.5, 22.7538)`) gives
`OP.MinMainP 0.811 45.7575` (`MT.minMain1At_mono`: `krawAt` grows with both constants). -/
theorem minMainP_of_L (h : OL.MinMainL) : OP.MinMainP 0.811 45.7575 :=
  (minMainP_iff 0.811 45.7575).2
    ⟨MT.minMain1At_mono 0.5 0.811 22.7538 45.7575 (by norm_num) (by norm_num)
      (MT.minMainL_iff.1 h).1, (MT.minMainL_iff.1 h).2⟩

/-! ## (2) The verifier's `min(1, 4c₀'/δ²)`: CONFIRMED -/

/-- **`capM` grows in its constant**: `min(1, c/δ²) ≤ min(1, c'/δ²)` for `0 < c ≤ c'`. -/
theorem capM_mono (c c' δ : ℝ) (hc0 : 0 < c) (hcc : c ≤ c') : MT.capM c δ ≤ MT.capM c' δ := by
  unfold MT.capM
  have hc'0 : 0 < c' := lt_of_lt_of_le hc0 hcc
  have hm : 0 < max c (δ ^ 2) := lt_of_lt_of_le hc0 (le_max_left _ _)
  have hm' : 0 < max c' (δ ^ 2) := lt_of_lt_of_le hc'0 (le_max_left _ _)
  rw [div_le_div_iff₀ hm hm']
  rcases le_total (δ ^ 2) c with h | h
  · rw [max_eq_left h, max_eq_left (le_trans h hcc)]
    nlinarith
  · rw [max_eq_right h]
    rcases le_total (δ ^ 2) c' with h' | h'
    · rw [max_eq_left h']
      nlinarith [mul_le_mul_of_nonneg_left h hc'0.le]
    · rw [max_eq_right h']
      nlinarith [mul_le_mul_of_nonneg_right hcc (sq_nonneg δ)]

/-- **The A9 step at `4c₀'`**: `min(1, 4c₀'/δ²) ≤ 2/δ₀` (`MT.capM_le`, `4·0.798437 ≤ 64`). -/
theorem capM_le_W (δ : ℝ) : MT.capM (4 * 0.798437) δ ≤ 2 / OC.dz δ :=
  MT.capM_le _ δ (by norm_num) (by norm_num)

/-- **The verifier's condition `c₀' ≤ 8δ₀`** (`δ₀ = max(2, |δ|/4) ≥ 2`). -/
theorem c0p_le (δ : ℝ) : (0.798437 : ℝ) ≤ 8 * OC.dz δ := by
  have h := MT.dz_ge δ
  linarith

/-- **`bI1` with `lem:bostb1`'s `min(1, 4c₀'/δ²)`** (generated from `MT.bI1`:
`capM 0.798437 ↦ capM (4·0.798437)`). -/
noncomputable def bI1W (Y δ : ℝ) (q : ℕ) : ℝ :=
  Y / q * capM (4 * 0.798437) δ * ((q : ℝ) / Nat.totient q) *
      (7 / 4 * Real.log (OC.dz δ * q) + 6.11676) +
    Y ^ ((2 : ℝ) / 3) / Real.sqrt (OC.dz δ * q) * (0.67845 * Real.log Y - 1.20818) +
    0.37864 * Y ^ ((2 : ℝ) / 3)

/-- **Link A1 at `4c₀'`** (generated from `MT.TypeI1`: `bI1 ↦ bI1W`). -/
def TypeI1W : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 →
    2 * α = a / q + δ / Y → (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) →
    |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) → (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
      ‖sI1 Y α (uA Y δ q)‖ ≤ bI1W Y δ q

/-- `bI1 ≤ bI1W` (`capM_mono`). -/
theorem bI1_le_bI1W (Y δ : ℝ) (q : ℕ) (hY : 0 ≤ Y) (hq : 1 ≤ q) : MT.bI1 Y δ q ≤ bI1W Y δ q := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hd2 := MT.dz_ge δ
  have hl : 0 ≤ 7 / 4 * Real.log (OC.dz δ * q) + 6.11676 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ OC.dz δ * q by nlinarith)
    linarith
  have hc := capM_mono 0.798437 (4 * 0.798437) δ (by norm_num) (by norm_num)
  have hYq : 0 ≤ Y / q := div_nonneg hY (by linarith)
  have hqφ : 0 ≤ (q : ℝ) / Nat.totient q := div_nonneg (by linarith) hφ0.le
  have k : Y / q * MT.capM 0.798437 δ * ((q : ℝ) / Nat.totient q) *
        (7 / 4 * Real.log (OC.dz δ * q) + 6.11676) ≤
      Y / q * MT.capM (4 * 0.798437) δ * ((q : ℝ) / Nat.totient q) *
        (7 / 4 * Real.log (OC.dz δ * q) + 6.11676) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hYq) hqφ) hl
  unfold MT.bI1 bI1W
  linarith

/-- **`TypeI1 → TypeI1W`**: the verifier's reading is the WEAKER hypothesis. -/
theorem typeI1W_of (h : MT.TypeI1) : TypeI1W := fun Y hY α δ a q hq hg h2 hQ hδ hy =>
  (h Y hY α δ a q hq hg h2 hQ hδ hy).trans (bI1_le_bI1W Y δ q (by linarith) hq)

/-- **The Totals arithmetic with `bI1W`** (generated from `MT.ArithAt`). -/
def ArithAtW (m cL : ℝ) : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → |δ| * q ≤ 4 / 3 * Y ^ ((1 : ℝ) / 3) →
    (q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 →
      bI1W Y δ q + bI2 Y δ q + bII Y δ q + 3 * (Real.log Y + 1) ≤ krawAt m cL Y δ q

/-- **Link A9 with `4c₀'`** (generated from `MT.lterms_le`: `capM 0.798437 ↦ capM (4·0.798437)`;
`MT.capM_le` still applies, `4·0.798437 ≤ 64`). -/
theorem lterms_leW (Y δ : ℝ) (q : ℕ) (hY0 : 0 < Y) (hq : 1 ≤ q) :
    Y / q * capM (4 * 0.798437) δ * ((q : ℝ) / Nat.totient q) *
        (7 / 4 * Real.log (OC.dz δ * q) + 6.11676) +
      capM (4 * 0.798437) δ * (Y / Nat.totient q) * (3 / 2 * Real.log q + 2.74107) +
      (3.59676 * Real.log (OC.dz δ) + 27.3032 * Real.log q + 91.515) * (Y / (q * OC.dz δ)) ≤
    2 * Y / (OC.dz δ * q) * lToscaAt 45.7575 (OC.dz δ) q := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hφ1 : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφ0 : (0 : ℝ) < Nat.totient q := by linarith
  have hd2 := dz_ge δ
  have hd0 : 0 < OC.dz δ := by linarith
  have hld : 0 ≤ Real.log (OC.dz δ) := Real.log_nonneg (by linarith)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hqR
  have hldq : Real.log (OC.dz δ * q) = Real.log (OC.dz δ) + Real.log q :=
    Real.log_mul hd0.ne' hq0.ne'
  have hlt1 : Real.log (OC.dz δ ^ ((7 : ℝ) / 4) * (q : ℝ) ^ ((13 : ℝ) / 4)) =
      7 / 4 * Real.log (OC.dz δ) + 13 / 4 * Real.log q := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hd0 _).ne' (Real.rpow_pos_of_pos hq0 _).ne',
      Real.log_rpow hd0, Real.log_rpow hq0]
  have hlt2 : Real.log ((q : ℝ) ^ (13.6516 : ℝ) * OC.dz δ ^ (1.7984 : ℝ)) =
      13.6516 * Real.log q + 1.7984 * Real.log (OC.dz δ) := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hq0 _).ne' (Real.rpow_pos_of_pos hd0 _).ne',
      Real.log_rpow hq0, Real.log_rpow hd0]
  have hc1 := capM_le (4 * 0.798437) δ (by norm_num) (by norm_num)
  have hc2 := capM_le (4 * 0.798437) δ (by norm_num) (by norm_num)
  have hYφ : 0 ≤ Y / Nat.totient q := div_nonneg hY0.le hφ0.le
  have e1 : Y / q * capM (4 * 0.798437) δ * ((q : ℝ) / Nat.totient q) *
      (7 / 4 * Real.log (OC.dz δ * q) + 6.11676) =
      capM (4 * 0.798437) δ * (Y / Nat.totient q) *
        (7 / 4 * Real.log (OC.dz δ) + 7 / 4 * Real.log q + 6.11676) := by
    rw [hldq]
    field_simp
  have h1 : Y / q * capM (4 * 0.798437) δ * ((q : ℝ) / Nat.totient q) *
      (7 / 4 * Real.log (OC.dz δ * q) + 6.11676) ≤
      2 / OC.dz δ * (Y / Nat.totient q) *
        (7 / 4 * Real.log (OC.dz δ) + 7 / 4 * Real.log q + 6.11676) := by
    rw [e1]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc1 hYφ) (by linarith)
  have h2 : capM (4 * 0.798437) δ * (Y / Nat.totient q) * (3 / 2 * Real.log q + 2.74107) ≤
      2 / OC.dz δ * (Y / Nat.totient q) * (3 / 2 * Real.log q + 2.74107) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 hYφ) (by linarith)
  have eR : 2 * Y / (OC.dz δ * q) * lToscaAt 45.7575 (OC.dz δ) q =
      2 / OC.dz δ * (Y / Nat.totient q) *
          (7 / 4 * Real.log (OC.dz δ) + 13 / 4 * Real.log q + 80 / 9) +
        2 * (Y / (q * OC.dz δ)) *
          (13.6516 * Real.log q + 1.7984 * Real.log (OC.dz δ) + 45.7575) := by
    unfold lToscaAt
    rw [hlt1, hlt2]
    field_simp
    ring
  have hP : 0 ≤ 2 / OC.dz δ * (Y / Nat.totient q) :=
    mul_nonneg (div_nonneg (by norm_num) hd0.le) hYφ
  have hQ : 0 ≤ Y / (q * OC.dz δ) := div_nonneg hY0.le (mul_nonneg hq0.le hd0.le)
  rw [eR]
  nlinarith [mul_nonneg hQ hld, hP, h1, h2]

/-- **THE ARITHMETIC with `bI1W`, PROVED at `(0.811, 45.7575)`** (generated from
`MT.arith_811`). -/
theorem arith_811W : ArithAtW 0.811 45.7575 := by
  intro Y hY δ q hq hdq hqy
  have hY0 : (0 : ℝ) < Y := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have htx : OC.dz δ * q ≤ Y ^ ((1 : ℝ) / 3) / 3 := dz_q_le δ _ q hdq hqy
  have hdq1 : (1 : ℝ) ≤ OC.dz δ * q := by nlinarith [dz_ge δ]
  have hs : 1 ≤ Real.sqrt (OC.dz δ * q) := Real.one_le_sqrt.mpr hdq1
  have hM := main_le Y δ q hY0 hq htx
  have hN : 2.49157 * Y / Real.sqrt (OC.dz δ * q) ≤ 2.5 * Y / Real.sqrt (OC.dz δ * q) :=
    div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have hL := lterms_leW Y δ q hY0 hq
  have hE := low_le Y (Real.sqrt (OC.dz δ * q)) hY hs
  unfold bI1W bI2 bII krawAt
  linarith

/-- **The Totals spine with `TypeI1W`** (generated from `MT.minMain1_of_arith`). -/
theorem minMain1_of_arithW (m cL : ℝ) (hA : ArithAtW m cL) (h1 : TypeI1W) (h2 : TypeI2)
    (h3 : TypeII) : MinMain1At m cL := by
  intro Y hY α δ a q hq hg h2α hqQ hδ hqy
  have hY0 : (0 : ℝ) < Y := by linarith
  have hdq := adm_dq Y δ q hY0 hq hδ
  have hsplit := vaughan_split Y α (uA Y δ q) (vA Y) hY0
  rw [s0i_eq_zero Y α (vA Y) hY0 (vA_lt Y hY), add_zero] at hsplit
  have e1 := h1 Y hY α δ a q hq hg h2α hqQ hδ hqy
  have e2 := h2 Y hY α δ a q hq hg h2α hqQ hδ hqy
  have e3 := h3 Y hY α δ a q hq hg h2α hqQ hδ hqy
  have e4 := s02_norm_le Y α (by linarith)
  have hk := hA Y hY δ q hq hdq hqy
  rw [hsplit]
  have n1 := norm_add_le (sI1 Y α (uA Y δ q) - sI2 Y α (uA Y δ q) (vA Y) +
    sII Y α (uA Y δ q) (vA Y)) (s02 Y α)
  have n2 := norm_add_le (sI1 Y α (uA Y δ q) - sI2 Y α (uA Y δ q) (vA Y))
    (sII Y α (uA Y δ q) (vA Y))
  have n3 := norm_sub_le (sI1 Y α (uA Y δ q)) (sI2 Y α (uA Y δ q) (vA Y))
  linarith

/-- **THE ATTACHMENT under the verifier's reading**: `TypeI1W → TypeI2 → TypeII → MinMain2L →
OP.MinMainP 0.811 45.7575`. Application only. -/
theorem minMainP_of_piecesW (h1 : TypeI1W) (h2 : MT.TypeI2) (h3 : MT.TypeII)
    (h4 : MT.MinMain2L) : OP.MinMainP 0.811 45.7575 :=
  (minMainP_iff 0.811 45.7575).2 ⟨minMain1_of_arithW 0.811 45.7575 arith_811W h1 h2 h3, h4⟩

/-- **`minMainP_of_pieces` factors through the `W` form** (`typeI1W_of`). -/
theorem minMainP_of_pieces' (h1 : MT.TypeI1) (h2 : MT.TypeI2) (h3 : MT.TypeII)
    (h4 : MT.MinMain2L) : OP.MinMainP 0.811 45.7575 :=
  minMainP_of_piecesW (typeI1W_of h1) h2 h3 h4

end Principia.Common.TernaryGoldbach.MMP
