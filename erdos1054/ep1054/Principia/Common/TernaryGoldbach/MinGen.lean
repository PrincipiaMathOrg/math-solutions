/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MinPiecesI2

set_option autoImplicit false

/-!
# `Bostb1At`, `SecI1At`, `SecI2At` from two source-level lemmas (spine)

Three of the ten open links of `MPI2.minMainP_of_ten` are the book's Type I lemmas applied at a
particular choice of parameters: `Bostb1At` is `lem:bostb1` at the first choice, `SecI1At` is
`lem:bostb1` at the second choice plus the Totals algebra, and `SecI2At` is `lem:bogus` at the
second choice plus the Totals algebra (Helfgott, arXiv:1501.05438: `typeI.tex` 1153-1222,
1496-1560; `minarctotals.tex` 58-145, 1857-1975). This file states the two lemmas for `η₂` with
the book's own hypotheses, and proves the three links from them — the attachment is a typing fact:

```
 Bostb1Eta2 ─── bostb1At_of_gen ─────────────────────────────────── Bostb1At
     └──── + Grara, Ronsard, Meproz, RS62Thm15, SecI1Arith ─────── SecI1At
 BogusEta2  ─── + SecI2Arith ────────────────────────────────────── SecI2At
 minMainP_of_spined : OP.MinMainP 0.811 45.7575 from the spined links      PROVED
```

## The links

* **`Bostb1Eta2`** — `lem:bostb1` for `η₂` with `ρ₀ = 4` (`minarctotals.tex` 61), in the
  `eq:kuche2` branch (`|δ| ≤ 1/2c₂` or `D ≤ Q₀/2`), main term CORRECTED as in `MPc.mainI1` (T6:
  `x/2q`, `-δ/2`, `(m, 2q) = 1`). Owed: the generic proof (`typeI.tex` 1223-1478, via
  `lem:bosta1`; its trigonometric sums `lem:gotog`, `lem:couscous`, `lem:thina` are PROVED in
  `Principia/Common/TrigSums.lean`), `eq:puella` for `η₂` (`eq:cloclo`; needs its own proof) and
  `c₀ = 31.521` (`lem:octet`).
* **`BogusEta2`** — `lem:bogus` for `η₂`, both branches, verbatim (`eq:cupcake3`,
  `eq:piececake`, `eq:tvorog`). The book prints its main term with `x/2q` and `c₀/(πδ)²`
  already. Owed: its generic proof.
* **`SecI1Arith`, `SecI2Arith`** — NUMERIC: the Totals algebra at the second choice
  (`U = 500√6x^{1/3}`, `V = x^{1/3}/3`, `Q = x/U`). A grid scan (`x ∈ [3.4·10²³, e^{1000}]`,
  `q` from `y` to `Q`, the free μ-sums at their extremes, `q/φ(q)` at `ϝ(Q)`) gives worst ratios
  `0.910` and `0.953`, both at `x = 3.4·10²³` (`scratchpad/trig/sec_check.py`).

`SecI1At`'s `2.4719` needs the corrected main term (the book's printed `x/q` gives `4.94`):
with `x/2q` the log-term halves while the `q/φ(q)` term is unchanged for odd `q`, since
`2q/φ(2q) = 2q/φ(q)` there. `SecI1Arith` therefore carries `q/φ(q) ≤ ϝ(Q)`, which
`secI1At_of` discharges from `RS62Thm15` (`GS.merkel_of_rs62`).
-/

namespace Principia.Common.TernaryGoldbach.MPG

open ArithmeticFunction Principia.Common.Goldbach
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc

/-! ## (1) The source lemmas -/

/-- **Link [Bostb1Eta2] — `lem:bostb1` for `η₂`** (`ρ₀ = 4`), the `eq:kuche2` branch, main term
CORRECTED (`mainI1`): for `2α = a/q + δ/x`, `(a, q) = 1`, `|δ/x| ≤ 1/(qQ₀)`, `q ≤ Q₀`,
`Q₀ ≥ max(16, 2√x)`, `√3 ≤ D ≤ x/4` and (`|δ| ≤ 1/2c₂` or `D ≤ Q₀/2`), there is
`M ∈ [min(Q₀/2, D), D]` with `|S_{I,1}| ≤ eq:cupcake2 + eq:kuche2`. -/
def Bostb1Eta2 : Prop :=
  ∀ x α δ Q0 D : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 16 ≤ Q0 → 2 * Real.sqrt x ≤ Q0 →
    Real.sqrt 3 ≤ D → D ≤ x / 4 → (|δ| ≤ 1 / (2 * c2) ∨ D ≤ Q0 / 2) →
      ∃ M : ℝ, min (Q0 / 2) D ≤ M ∧ M ≤ D ∧
        ‖sI1 x α D‖ ≤ mainI1 x δ q M + errI1 x q D + kuche2 x q D

/-- `c₄ = 1.03884` (`lem:bogus`). -/
noncomputable def c4 : ℝ := 1.03884

/-- `c₁ = 1 + |η'|₁/(2x/D)` of `lem:bogus`. -/
noncomputable def c1b (x D : ℝ) : ℝ := 1 + eta1 * D / (2 * x)

/-- **`eq:cupcake3`**, `D = UV`, with its `O*` term at full size. -/
noncomputable def cupcake3 (x δ : ℝ) (q : ℕ) (U V : ℝ) : ℝ :=
  x / (2 * q) * capM (c0 / Real.pi ^ 2) δ * Real.log (V * q) +
    (1 / 4 - 1 / Real.pi ^ 2) * c0 *
      ((U * V) ^ 2 * Real.log V / (2 * q * x) + 3 * c4 / 2 * (U * V ^ 2 / x) +
        (U + 1) ^ 2 * V / (2 * x) * Real.log q)

/-- **`eq:piececake`**, `D = UV`. -/
noncomputable def piececake (x : ℝ) (q : ℕ) (U V : ℝ) : ℝ :=
  2 * Real.sqrt (c0 * c1b x (U * V)) / Real.pi *
      (U * V * Real.log (U * V / Real.sqrt (Real.exp 1)) +
        q * (Real.sqrt 3 * Real.log (c2 * x / q) +
          Real.log (U * V) / 2 * logp (U * V / (q / 2)))) +
    3 * c1b x (U * V) / 2 * (x / q) * Real.log (U * V) * logp (U * V / (c2 * x / q)) +
    2 * eta1 / Real.pi * q *
      max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * Real.pi * eta1 * x))) *
      Real.log (q / 2) +
    3 * c1b x (U * V) / (2 * Real.sqrt (2 * c2)) * Real.sqrt x * Real.log (c2 * x / 2) +
    25 * c0 / (4 * Real.pi ^ 2) * (2 * c2) ^ ((3 : ℝ) / 2) * Real.sqrt x * Real.log x

/-- **`eq:tvorog`**, `D = UV`, `ε ∈ (0, 1]`. -/
noncomputable def tvorog (x δ : ℝ) (q : ℕ) (U V ε : ℝ) : ℝ :=
  2 * Real.sqrt (c0 * c1b x (U * V)) / Real.pi * (U * V) * Real.log (U * V / Real.exp 1) +
    2 * Real.sqrt (c0 * c1b x (U * V)) / Real.pi * (1 + ε) * (x / (|δ| * q) + 1) *
      ((Real.sqrt (3 + 2 * ε) - 1) * Real.log ((x / (|δ| * q) + 1) / Real.sqrt 2) +
        Real.log (U * V) / 2 * logp (Real.exp 2 * (U * V) / (x / (|δ| * q)))) +
    (3 * c1b x (U * V) / 2 * (1 / 2 + 3 * (1 + ε) / (16 * ε) * Real.log x) +
      20 * c0 / (3 * Real.pi ^ 2) * (2 * c2) ^ ((3 : ℝ) / 2)) * Real.sqrt x * Real.log x

/-- **Link [BogusEta2] — `lem:bogus` for `η₂`**, verbatim: for `2α = a/q + δ/x`, `(a, q) = 1`,
`|δ/x| ≤ 1/(qQ₀)`, `q ≤ Q₀`, `Q₀ ≥ max(2e, 2√x)`, `x ≥ e²c₂/2`, `U, V ≥ 1`,
`UV + (19/18)Q₀ ≤ x/5.6`: `|S_{I,2}| ≤ eq:cupcake3 + eq:piececake` if `|δ| ≤ 1/2c₂` or
`UV ≤ Q₀/2`, and `≤ eq:cupcake3 + eq:tvorog(ε)` for `ε ∈ (0, 1]` if `|δ| ≥ 1/2c₂`. -/
def BogusEta2 : Prop :=
  ∀ x α δ Q0 U V : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 2 * Real.exp 1 ≤ Q0 → 2 * Real.sqrt x ≤ Q0 →
    Real.exp 1 ^ 2 * c2 / 2 ≤ x → 1 ≤ U → 1 ≤ V → U * V + 19 / 18 * Q0 ≤ x / 5.6 →
      ((|δ| ≤ 1 / (2 * c2) ∨ U * V ≤ Q0 / 2) →
        ‖sI2 x α U V‖ ≤ cupcake3 x δ q U V + piececake x q U V) ∧
      (1 / (2 * c2) ≤ |δ| → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ‖sI2 x α U V‖ ≤ cupcake3 x δ q U V + tvorog x δ q U V ε)

/-- **Link [SecI1Arith] — NUMERIC: `S_{I,1}` at the second choice** (`minarctotals.tex`
1857-1901): for any `s₀, s₁` obeying `eq:grara`, `eq:ronsard`, `eq:meproz` at modulus `2q`,
`N = U/q`, the corrected `lem:bostb1` bound at `D = U` is at most
`2.4719x^{2/3}log x + 0.00289x^{2/3}(log x)²`. -/
def SecI1Arith : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ q2 Y → |δ| * q ≤ u2 Y →
    (Y ^ ((1 : ℝ) / 3) / 6 < q ∨ 4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ| * q) →
    (q : ℝ) / Nat.totient q ≤ MinSp.bigF (q2 Y) → ∀ s0 s1 : ℝ, |s0| ≤ 1 →
    (((2 * q : ℕ) : ℝ) < u2 Y / q →
      |s0| ≤ 4 / 5 * (((2 * q : ℕ) : ℝ) / Nat.totient (2 * q)) /
        Real.log (u2 Y / q / ((2 * q : ℕ) : ℝ))) →
    |s1 - Real.log (Y / u2 Y) * s0| ≤ 1.00303 * (((2 * q : ℕ) : ℝ) / Nat.totient (2 * q)) →
      Y / (2 * q) * capM (c0 / Real.pi ^ 2) δ * |s1| +
          Y / (2 * q) *
              ((2 - Real.log 4) * capM (96 * Real.log 2 / Real.pi ^ 2 / (2 - Real.log 4)) δ) *
            |s0| +
          errI1 Y q (u2 Y) + kuche2 Y q (u2 Y) ≤
        2.4719 * Y ^ ((2 : ℝ) / 3) * Real.log Y + 0.00289 * Y ^ ((2 : ℝ) / 3) * Real.log Y ^ 2

/-- **Link [SecI2Arith] — NUMERIC: `S_{I,2}` at the second choice** (`minarctotals.tex`
1905-1975, `eq:octet`, `eq:tvorog` at `ε = 0.01`). -/
def SecI2Arith : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ q2 Y → |δ| * q ≤ u2 Y →
    (Y ^ ((1 : ℝ) / 3) / 6 < q ∨ 4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ| * q) →
      (|δ| ≤ 1 / (2 * c2) →
        cupcake3 Y δ q (u2 Y) (v2 Y) + piececake Y q (u2 Y) (v2 Y) ≤
          1230.9 * Y ^ ((2 : ℝ) / 3) * Real.log Y +
            0.0006406 * Y ^ ((2 : ℝ) / 3) * Real.log Y ^ 2) ∧
      (1 / (2 * c2) < |δ| →
        cupcake3 Y δ q (u2 Y) (v2 Y) + tvorog Y δ q (u2 Y) (v2 Y) 0.01 ≤
          1230.9 * Y ^ ((2 : ℝ) / 3) * Real.log Y +
            0.0006406 * Y ^ ((2 : ℝ) / 3) * Real.log Y ^ 2)

/-! ## (2) The parameters -/

/-- `c₂ ≤ 1`. -/
theorem c2_le_one : c2 ≤ 1 := by
  have hs : (5.61 : ℝ) ≤ Real.sqrt c0 := by
    rw [Real.le_sqrt (by norm_num) (by unfold c0; norm_num)]; unfold c0; norm_num
  have hpi := Real.pi_lt_d2
  unfold c2
  rw [div_le_one (by positivity)]
  nlinarith

/-- `0 < c₂`. -/
theorem c2_pos : 0 < c2 := by
  unfold c2; have := Real.pi_pos; have : 0 < Real.sqrt c0 := by unfold c0; positivity
  positivity

/-- `√x = u³` for `u = x^{1/6}`. -/
theorem sqrt_eq_u3 (Y : ℝ) (hY0 : 0 < Y) : Real.sqrt Y = (Y ^ ((1 : ℝ) / 6)) ^ 3 := by
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  have hu0 : 0 < Y ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hY0 _
  conv_lhs => rw [eY]
  rw [show (Y ^ ((1 : ℝ) / 6)) ^ 6 = ((Y ^ ((1 : ℝ) / 6)) ^ 3) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

/-- `√6 ∈ [2.449, 2.45]`. -/
theorem sqrt6_bounds : 2.449 ≤ Real.sqrt 6 ∧ Real.sqrt 6 ≤ 2.45 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- **The second choice in `u = x^{1/6}`**: `U = 500√6u²`, `V = u²/3`, `Q = u⁴/(500√6)`. -/
theorem sec_eqs (Y : ℝ) (hY0 : 0 < Y) :
    u2 Y = 500 * Real.sqrt 6 * (Y ^ ((1 : ℝ) / 6)) ^ 2 ∧
      v2 Y = (Y ^ ((1 : ℝ) / 6)) ^ 2 / 3 ∧
      q2 Y = (Y ^ ((1 : ℝ) / 6)) ^ 4 / (500 * Real.sqrt 6) := by
  obtain ⟨-, -, e13, eY, -⟩ := rpow_facts Y hY0
  have hs : 0 < Real.sqrt 6 := by positivity
  refine ⟨by unfold u2; rw [e13], by unfold v2; rw [e13], ?_⟩
  unfold q2 u2
  rw [e13]
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := Real.rpow_pos_of_pos hY0 _
  rw [eY]
  field_simp

/-- `2u³ ≤ u⁴/(500√6)` for `u ≥ 8000`. -/
theorem u_sqrt_le (u : ℝ) (hu : 8000 ≤ u) : 2 * u ^ 3 ≤ u ^ 4 / (500 * Real.sqrt 6) := by
  obtain ⟨-, hs2⟩ := sqrt6_bounds
  have hu0 : 0 < u := by linarith
  have hS : 0 < 500 * Real.sqrt 6 := by positivity
  rw [le_div_iff₀ hS]
  have hu3 : (8000 : ℝ) * u ^ 3 ≤ u ^ 4 := by
    have := mul_le_mul_of_nonneg_right hu (pow_pos hu0 3).le
    nlinarith
  nlinarith [pow_pos hu0 3]

/-- `500√6u² ≤ (u⁴/(500√6))/2` for `u ≥ 8000`. -/
theorem u_uq_le (u : ℝ) (hu : 8000 ≤ u) :
    500 * Real.sqrt 6 * u ^ 2 ≤ u ^ 4 / (500 * Real.sqrt 6) / 2 := by
  have hu0 : 0 < u := by linarith
  have hS : 0 < 500 * Real.sqrt 6 := by positivity
  have h66 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
  have hu2' : (8000 : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by norm_num) hu 2
  rw [le_div_iff₀ (by norm_num), le_div_iff₀ hS]
  have e : 500 * Real.sqrt 6 * u ^ 2 * 2 * (500 * Real.sqrt 6) =
      500 * 500 * 2 * (Real.sqrt 6 * Real.sqrt 6) * u ^ 2 := by ring
  rw [e, h66]
  have : (8000 : ℝ) ^ 2 * u ^ 2 ≤ u ^ 2 * u ^ 2 :=
    mul_le_mul_of_nonneg_right hu2' (pow_pos hu0 2).le
  nlinarith [pow_pos hu0 2]

/-- `UV + (19/18)Q ≤ x/5.6` in `u`. -/
theorem u_uv_le (u : ℝ) (hu : 8000 ≤ u) :
    500 * Real.sqrt 6 * u ^ 2 * (u ^ 2 / 3) + 19 / 18 * (u ^ 4 / (500 * Real.sqrt 6)) ≤
      u ^ 6 / 5.6 := by
  obtain ⟨hs1, hs2⟩ := sqrt6_bounds
  have hu0 : 0 < u := by linarith
  have hS : 0 < 500 * Real.sqrt 6 := by positivity
  have hu2' : (8000 : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by norm_num) hu 2
  have e2 : 19 / 18 * (u ^ 4 / (500 * Real.sqrt 6)) ≤ u ^ 4 / 1000 := by
    rw [show 19 / 18 * (u ^ 4 / (500 * Real.sqrt 6)) = (19 / 18 * u ^ 4) / (500 * Real.sqrt 6)
      by ring, div_le_div_iff₀ hS (by norm_num)]
    nlinarith [pow_pos hu0 4]
  have e1 : 500 * Real.sqrt 6 * u ^ 2 * (u ^ 2 / 3) = 500 * Real.sqrt 6 / 3 * u ^ 4 := by ring
  have h408 : 500 * Real.sqrt 6 / 3 ≤ 408.34 := by linarith
  have k1 : 500 * Real.sqrt 6 / 3 * u ^ 4 ≤ 408.34 * u ^ 4 :=
    mul_le_mul_of_nonneg_right h408 (pow_pos hu0 4).le
  have k2 : 408.34 * u ^ 4 + u ^ 4 / 1000 ≤ u ^ 6 / 5.6 := by
    rw [show u ^ 6 = u ^ 2 * u ^ 4 by ring, le_div_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right hu2' (pow_pos hu0 4).le, pow_pos hu0 4]
  linarith

/-- **The hypotheses of `lem:bostb1` and `lem:bogus` at the second choice.** -/
theorem sec_hyps (Y : ℝ) (hY : 3.4e23 ≤ Y) :
    16 ≤ q2 Y ∧ 2 * Real.exp 1 ≤ q2 Y ∧ 2 * Real.sqrt Y ≤ q2 Y ∧ Real.sqrt 3 ≤ u2 Y ∧
      u2 Y ≤ Y / 4 ∧ u2 Y ≤ q2 Y / 2 ∧ Real.exp 1 ^ 2 * c2 / 2 ≤ Y ∧ 1 ≤ u2 Y ∧
      1 ≤ v2 Y ∧ u2 Y * v2 Y + 19 / 18 * q2 Y ≤ Y / 5.6 ∧ 3 ≤ q2 Y := by
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨-, -, -, eY, -⟩ := rpow_facts Y hY0
  obtain ⟨hu2, hv2, hq2⟩ := sec_eqs Y hY0
  have hsq := sqrt_eq_u3 Y hY0
  have hu := u_ge Y hY
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := by linarith
  obtain ⟨hs1, hs2⟩ := sqrt6_bounds
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hc2 := c2_le_one
  have hc20 := c2_pos
  have h3 : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hu2' : (8000 : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by norm_num) hu 2
  have hu4 : (8000 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have hS : 0 < 500 * Real.sqrt 6 := by positivity
  have hQ : (8000 : ℝ) ^ 4 / 1225 ≤ u ^ 4 / (500 * Real.sqrt 6) := by
    rw [div_le_div_iff₀ (by norm_num) hS]; nlinarith
  have hE : Real.exp 1 ^ 2 ≤ 8 := by nlinarith
  have hY8 : (8 : ℝ) ≤ Y := by linarith
  have hU4 : 500 * Real.sqrt 6 * u ^ 2 ≤ u ^ 6 / 4 := by
    rw [show u ^ 6 = u ^ 2 * u ^ 4 by ring, le_div_iff₀ (by norm_num)]
    nlinarith [pow_pos hu0 4, pow_pos hu0 2]
  rw [hu2, hv2, hq2]
  refine ⟨by linarith, by linarith, by rw [hsq]; exact u_sqrt_le u hu, by nlinarith,
    by rw [eY]; exact hU4, u_uq_le u hu, by nlinarith, by nlinarith, by
    rw [le_div_iff₀ (by norm_num)]; nlinarith, by rw [eY]; exact u_uv_le u hu, by linarith⟩

/-- `|δ|q ≤ U` from `|δ/x| ≤ 1/(qQ)`, `Q = x/U`. -/
theorem dq_le_u2 (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hq : 1 ≤ q)
    (hδ : |δ / Y| ≤ 1 / (q * q2 Y)) : |δ| * q ≤ u2 Y := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hU : 0 < u2 Y := by unfold u2; positivity
  have hQ : 0 < q2 Y := by unfold q2; positivity
  rw [abs_div, abs_of_pos hY0, div_le_div_iff₀ hY0 (by positivity), one_mul] at hδ
  have e : q * q2 Y = q * Y / u2 Y := by unfold q2; ring
  rw [e] at hδ
  have := mul_le_mul_of_nonneg_left hδ hU.le
  have e2 : u2 Y * (|δ| * (q * Y / u2 Y)) = |δ| * q * Y := by field_simp
  rw [e2] at this
  nlinarith

/-! ## (3) The three links from the source lemmas -/

/-- **`Bostb1At` from `lem:bostb1`, PROVED** (`Q₀ = (3/4)x^{2/3}`, `D = U ≤ Q₀/2`, so `M = U`). -/
theorem bostb1At_of_gen (hb : Bostb1Eta2) : Bostb1At := by
  intro Y hY α δ a q hq hg h2 hQ hδ hy
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, -, e13, eY, -⟩ := rpow_facts Y hY0
  have hu := u_ge Y hY
  have hdq := adm_dq Y δ q hY0 hq hδ
  obtain ⟨hs1, hs2⟩ := sqrt_dq Y δ q hY hq hdq hy
  have hUe := uA_eq Y δ q hY0
  have hUV := uA_mul_vA Y δ q hY hq hdq hy
  have hsq := sqrt_eq_u3 Y hY0
  have hvA : vA Y = 9 / 2 * (Y ^ ((1 : ℝ) / 6)) ^ 2 := by unfold vA; rw [e13]
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  have hu0 : 0 < u := by linarith
  have hsp : 0 < Real.sqrt (OC.dz δ * q) := by linarith
  have h16 : (16 : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) := by
    rw [e23]; nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8000) hu 4]
  have hsqQ : 2 * Real.sqrt Y ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) := by
    rw [hsq, e23]; nlinarith [pow_pos hu0 3]
  have h3 : Real.sqrt 3 ≤ uA Y δ q := by
    have h32 : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    rw [hUe, le_div_iff₀ (by positivity)]
    nlinarith [pow_pos hu0 3, mul_le_mul_of_nonneg_left hs2 (by norm_num : (0 : ℝ) ≤ 18)]
  have hU4 : uA Y δ q ≤ Y / 4 := by
    have hV4 : (4 : ℝ) ≤ vA Y := by rw [hvA]; nlinarith
    have hU0 : 0 < uA Y δ q := uA_pos Y δ q hY0 hq
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hUQ : uA Y δ q ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) / 2 := by
    rw [hUe, e23, div_le_iff₀ (by positivity)]
    nlinarith [pow_pos hu0 4]
  obtain ⟨M, hM1, hM2, hbd⟩ := hb Y α δ (3 / 4 * Y ^ ((2 : ℝ) / 3)) (uA Y δ q) a q hq hg h2 hδ
    hQ h16 hsqQ h3 hU4 (Or.inr hUQ)
  rw [min_eq_right hUQ] at hM1
  have hM : M = uA Y δ q := le_antisymm hM2 hM1
  rw [hM] at hbd
  exact hbd

/-- **`SecI1At` from `lem:bostb1`, PROVED**: `Bostb1Eta2` at `Q₀ = x/U`, `D = U = 500√6x^{1/3}`
(`U ≤ Q₀/2`, so `M = U`), `eq:grara`, `eq:ronsard`, `eq:meproz` at modulus `2q`, `lem:merkel`
from `RS62Thm15`, and `SecI1Arith`. -/
theorem secI1At_of (hb : Bostb1Eta2) (hg : Grara) (hr : Ronsard) (hm : Meproz)
    (h15 : GS.RS62Thm15) (ha : SecI1Arith) : SecI1At := by
  intro Y hY α δ a q ⟨hq, hga, h2, hQ, hδ, hA⟩
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨h16, -, hsqQ, h3, hU4, hUQ, -, -, -, -, h3Q⟩ := sec_hyps Y hY
  have hdq := dq_le_u2 Y δ q hY hq hδ
  have hF : (q : ℝ) / Nat.totient q ≤ MinSp.bigF (q2 Y) :=
    (GS.merkel_of_rs62 h15 q hq (q2 Y) h3Q hQ).le
  obtain ⟨M, hM1, hM2, hbd⟩ := hb Y α δ (q2 Y) (u2 Y) a q hq hga h2 hδ hQ h16 hsqQ h3 hU4
    (Or.inr hUQ)
  rw [min_eq_right hUQ] at hM1
  have hM : M = u2 Y := le_antisymm hM2 hM1
  rw [hM] at hbd
  refine hbd.trans ?_
  have hU : 0 < u2 Y := by unfold u2; positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h2q : 1 ≤ 2 * q := by omega
  unfold mainI1
  refine ha Y hY δ q hq hQ hdq hA hF (muS (2 * q) (u2 Y / q))
    (muL (2 * q) (u2 Y / q) (Y / q)) (hg _ _ h2q) (fun hlt => hr _ _ h2q hlt) ?_
  have hs := muL_split (2 * q) (u2 Y / q) (Y / q) (div_pos hU hqR) (div_pos hY0 hqR)
  have e : Y / q / (u2 Y / q) = Y / u2 Y := div_div_div_cancel_right₀ hqR.ne' Y _
  rw [e] at hs
  rw [hs, add_sub_cancel_left]
  exact hm _ _ h2q

/-- **`SecI2At` from `lem:bogus`, PROVED**: `BogusEta2` at `Q₀ = x/U`, `U = 500√6x^{1/3}`,
`V = x^{1/3}/3`, the `|δ| ≤ 1/2c₂` branch or `eq:tvorog` at `ε = 0.01`, and `SecI2Arith`. -/
theorem secI2At_of (hb : BogusEta2) (ha : SecI2Arith) : SecI2At := by
  intro Y hY α δ a q ⟨hq, hga, h2, hQ, hδ, hA⟩
  obtain ⟨-, h2e, hsqQ, -, -, -, he2, hU1, hV1, hUV, -⟩ := sec_hyps Y hY
  have hdq := dq_le_u2 Y δ q hY hq hδ
  obtain ⟨hk, ht⟩ := hb Y α δ (q2 Y) (u2 Y) (v2 Y) a q hq hga h2 hδ hQ h2e hsqQ he2 hU1 hV1
    hUV
  obtain ⟨hak, hat⟩ := ha Y hY δ q hq hQ hdq hA
  rcases le_or_gt |δ| (1 / (2 * c2)) with hd | hd
  · exact (hk (Or.inl hd)).trans (hak hd)
  · exact (ht hd.le 0.01 (by norm_num) (by norm_num)).trans (hat hd)

/-! ## (4) The Main Theorem on the spined links -/

/-- **`OP.MinMainP 0.811 45.7575` from the spined links** (`MPI2.minMainP_of_ten` with
`Bostb1At`, `SecI1At`, `SecI2At` replaced by `Bostb1Eta2`, `BogusEta2`, `SecI1Arith`,
`SecI2Arith`). Application only. -/
theorem minMainP_of_spined (hb1 : Bostb1Eta2) (hbg : BogusEta2) (hgr : Grara) (hro : Ronsard)
    (hme : Meproz) (hb2 : Bosta2Eta2) (hv1 : Vinland1At) (her : EriksagaAt)
    (hs1 : SecI1Arith) (hs2 : SecI2Arith) (hs3 : SecIIAt) (h15 : GS.RS62Thm15) :
    OP.MinMainP 0.811 45.7575 :=
  MPI2.minMainP_of_ten (bostb1At_of_gen hb1) hgr hro hme hb2 hv1 her
    (secI1At_of hb1 hgr hro hme h15 hs1) (secI2At_of hbg hs2) hs3 h15

end Principia.Common.TernaryGoldbach.MPG
