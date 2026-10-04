/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.BogusSpine
import Principia.Common.TernaryGoldbach.SecI2Arith

set_option autoImplicit false

/-!
# `lem:bogus` with `eq:tvorog` CORRECTED (the missing factor `2`), and `SecI2At` from it

**Finding (adjudication of `eq:tvorog`).** The printed `eq:tvorog` (`minarcs.tex` 2238-2251, book
`typeI.tex` 1546-1559) has, in its second line, `(1/2) log D · log⁺(e²D/(x/|δ|q))`. Its own proof
(`eq:iulia`, `minarcs.tex` 2434-2445) delivers `(1/2) log D · log⁺(e²D/((Q + 1)/2))` with
`Q = ⌊x/|δq|⌋`. Since `Q + 1 > x/|δ|q`, the source proves the argument `2e²D/(x/|δ|q)` and NOT
`e²D/(x/|δ|q)`: the factor `2` of `(Q + 1)/2` was dropped when `Q + 1` was replaced by
`x/|δ|q + 1` (the sister lemma `lem:bosta1` performs the same replacement correctly,
`log⁺(2D/(x/|δ|q))`). So `MPG.BogusEta2`'s second branch, stated VERBATIM, is not derivable from
the source proof; it is not refuted either (the omitted quantity is a proof-artefact, and the
true sum is far below either bound), but no link may rest on it.

**The corrected link.** `tvorogC` is `eq:tvorog` with `log⁺(2e²D/(x/|δ|q))`; `BogusEta2C`
and `EsthelBogusEta2C` are the corresponding statements. `bogusC_of_verbatim` shows the
corrected link is IMPLIED by the verbatim one (it is strictly weaker), so nothing that holds
`BogusEta2` is lost.

**It still closes.** At the second choice the extra `log 2` costs at most
`k(1.01)(K + 1)(log UV/2)log 2 ≤ u⁴(40.7λ + 61.5)`, i.e. `≤ 0.64%` of the `SecI2At` budget
(`scratchpad/tvorog/t.py`); `secI2ArithC` re-proves the arithmetic with
`eq:tvorog` replaced by `tvorogC`: `≤ u⁴(6310.5λ + 8004.3)` against `u⁴(7385.4λ)` for `λ ≥ 8.3`.

```
 SecI2At ← BogusEta2C ← TrompaisEta2, MainBogusEta2, EsthelBogusEta2C
          (secI2At_of_genC; bogusEta2C_of; secI2ArithC PROVED)
```
-/

namespace Principia.Common.TernaryGoldbach.MPBC

open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPG Principia.Common.TernaryGoldbach.MPB2
  Principia.Common.TernaryGoldbach.MPT Principia.Common.TernaryGoldbach.MPBG
  Principia.Common.TernaryGoldbach.MPS2 Principia.Common.TernaryGoldbach.MPI1
  Principia.Common.TernaryGoldbach.MPS1

/-! ## (1) The corrected `eq:tvorog` -/

/-- **`eq:tvorog` CORRECTED**, `D = UV`, `ε ∈ (0, 1]`: the `log⁺` argument is
`2e²D/(x/|δ|q)` (the source's `e²D/((Q + 1)/2)`, `Q + 1 > x/|δ|q`). -/
noncomputable def tvorogC (x δ : ℝ) (q : ℕ) (U V ε : ℝ) : ℝ :=
  2 * Real.sqrt (c0 * c1b x (U * V)) / Real.pi * (U * V) * Real.log (U * V / Real.exp 1) +
    2 * Real.sqrt (c0 * c1b x (U * V)) / Real.pi * (1 + ε) * (x / (|δ| * q) + 1) *
      ((Real.sqrt (3 + 2 * ε) - 1) * Real.log ((x / (|δ| * q) + 1) / Real.sqrt 2) +
        Real.log (U * V) / 2 * logp (2 * (Real.exp 2 * (U * V)) / (x / (|δ| * q)))) +
    (3 * c1b x (U * V) / 2 * (1 / 2 + 3 * (1 + ε) / (16 * ε) * Real.log x) +
      20 * c0 / (3 * Real.pi ^ 2) * (2 * c2) ^ ((3 : ℝ) / 2)) * Real.sqrt x * Real.log x

/-- `log⁺ z ≤ log⁺ (2z)` for `z ≥ 0`. -/
theorem logp_le_two_mul (z : ℝ) (hz : 0 ≤ z) : logp z ≤ logp (2 * z) := by
  unfold logp
  rcases hz.lt_or_eq with h | h
  · exact max_le_max (Real.log_le_log h (by linarith)) le_rfl
  · rw [← h, mul_zero]

/-- **The verbatim `eq:tvorog` is at most the corrected one**, PROVED. -/
theorem tvorog_le_tvorogC (x δ : ℝ) (q : ℕ) (U V ε : ℝ) (hx : 0 ≤ x) (hD : 1 ≤ U * V)
    (hε : 0 ≤ ε) : tvorog x δ q U V ε ≤ tvorogC x δ q U V ε := by
  unfold tvorog tvorogC
  set K := x / (|δ| * q) with hK_def
  have hK : 0 ≤ K := by rw [hK_def]; positivity
  have hz : 0 ≤ Real.exp 2 * (U * V) / K := by positivity
  have hl : logp (Real.exp 2 * (U * V) / K) ≤ logp (2 * (Real.exp 2 * (U * V)) / K) := by
    rw [mul_div_assoc (2 : ℝ)]; exact logp_le_two_mul _ hz
  have hL : 0 ≤ Real.log (U * V) / 2 := by have := Real.log_nonneg hD; positivity
  have hk : 0 ≤ 2 * Real.sqrt (c0 * c1b x (U * V)) / Real.pi * (1 + ε) * (K + 1) := by
    positivity
  have h1 := mul_le_mul_of_nonneg_left hl hL
  have h2 := mul_le_mul_of_nonneg_left
    (add_le_add_left h1 ((Real.sqrt (3 + 2 * ε) - 1) * Real.log ((K + 1) / Real.sqrt 2))) hk
  linarith

/-! ## (2) The corrected links and their composition -/

/-- **Link [BogusEta2C] — `lem:bogus` for `η₂`, `eq:tvorog` CORRECTED**: as `MPG.BogusEta2`,
with `tvorogC` in place of `tvorog` in the `|δ| ≥ 1/2c₂` branch. -/
def BogusEta2C : Prop :=
  ∀ x α δ Q0 U V : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 2 * Real.exp 1 ≤ Q0 → 2 * Real.sqrt x ≤ Q0 →
    Real.exp 1 ^ 2 * c2 / 2 ≤ x → 1 ≤ U → 1 ≤ V → U * V + 19 / 18 * Q0 ≤ x / 5.6 →
      ((|δ| ≤ 1 / (2 * c2) ∨ U * V ≤ Q0 / 2) →
        ‖sI2 x α U V‖ ≤ cupcake3 x δ q U V + piececake x q U V) ∧
      (1 / (2 * c2) ≤ |δ| → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ‖sI2 x α U V‖ ≤ cupcake3 x δ q U V + tvorogC x δ q U V ε)

/-- **Link [EsthelBogusEta2C] — `eq:esthel3` of `lem:bogus`, `eq:tvorog` CORRECTED**: as
`MPBG.EsthelBogusEta2`, with `tvorogC` in the `|δ| ≥ 1/2c₂` branch. OPEN. -/
def EsthelBogusEta2C : Prop :=
  ∀ x α δ Q0 U V : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 → 2 * α = a / q + δ / x →
    |δ / x| ≤ 1 / (q * Q0) → (q : ℝ) ≤ Q0 → 2 * Real.exp 1 ≤ Q0 → 2 * Real.sqrt x ≤ Q0 →
    Real.exp 1 ^ 2 * c2 / 2 ≤ x → 1 ≤ U → 1 ≤ V → U * V + 19 / 18 * Q0 ≤ x / 5.6 →
    ∀ T : ℕ → ℝ, TromB x α T →
      ((|δ| ≤ 1 / (2 * c2) ∨ U * V ≤ Q0 / 2) →
        ∑ d ∈ (Finset.Ioc 0 ⌊U * V⌋₊).filter
            (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ mR x δ q (U * V))), Real.log d * T d ≤
          piececake x q U V) ∧
      (1 / (2 * c2) ≤ |δ| → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∑ d ∈ (Finset.Ioc 0 ⌊U * V⌋₊).filter
            (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ mR x δ q (U * V))), Real.log d * T d ≤
          tvorogC x δ q U V ε)

/-- `x > 0` under `lem:bogus`'s hypothesis `x ≥ e²c₂/2`. -/
theorem x_pos_of (x : ℝ) (hx : Real.exp 1 ^ 2 * c2 / 2 ≤ x) : 0 < x := by
  have := c2_pos
  have : 0 < Real.exp 1 ^ 2 * c2 / 2 := by positivity
  linarith

/-- **The verbatim link implies the corrected one**, PROVED. -/
theorem bogusC_of_verbatim (h : BogusEta2) : BogusEta2C := by
  intro x α δ Q0 U V a q hq hg h2α hδ hqQ h2e hsq hx hU hV hUV
  obtain ⟨hb, ht⟩ := h x α δ Q0 U V a q hq hg h2α hδ hqQ h2e hsq hx hU hV hUV
  have hD : 1 ≤ U * V := by nlinarith
  exact ⟨hb, fun hc ε hε hε1 => (ht hc ε hε hε1).trans (add_le_add le_rfl
    (tvorog_le_tvorogC x δ q U V ε (x_pos_of x hx).le hD hε.le))⟩

/-- **The verbatim `EsthelBogusEta2` implies the corrected one**, PROVED. -/
theorem esthelC_of_esthel (h : EsthelBogusEta2) : EsthelBogusEta2C := by
  intro x α δ Q0 U V a q hq hg h2α hδ hqQ h2e hsq hx hU hV hUV T hT
  obtain ⟨hb, ht⟩ := h x α δ Q0 U V a q hq hg h2α hδ hqQ h2e hsq hx hU hV hUV T hT
  have hD : 1 ≤ U * V := by nlinarith
  exact ⟨hb, fun hc ε hε hε1 => (ht hc ε hε hε1).trans
    (tvorog_le_tvorogC x δ q U V ε (x_pos_of x hx).le hD hε.le)⟩

/-- **`BogusEta2C` from its three links, PROVED** (application, `M = mR`). -/
theorem bogusEta2C_of (h1 : TrompaisEta2) (h2 : MainBogusEta2) (h3 : EsthelBogusEta2C) :
    BogusEta2C := by
  intro x α δ Q0 U V a q hq hg h2α hδ hqQ h2e hsq hx hU hV hUV
  have hx0 := x_pos_of x hx
  have hT : TromB x α (fun d => ‖tmo x α d‖) := fun d hd => ⟨norm_nonneg _, h1 x α hx0 d hd⟩
  have hmain := h2 x α δ Q0 U V a q hq hg h2α hδ hqQ h2e hsq hx hU hV hUV
  obtain ⟨hb, ht⟩ := h3 x α δ Q0 U V a q hq hg h2α hδ hqQ h2e hsq hx hU hV hUV _ hT
  have hQ0 : 0 ≤ Q0 := by linarith [Real.exp_pos 1]
  have h56 : x / 5.6 ≤ x := by rw [div_le_iff₀ (by norm_num)]; nlinarith
  have hDx : U * V ≤ x := by linarith
  have hle := sI2_le x α U V (by linarith) (by linarith)
    (fun d => q ∣ d ∧ (d : ℝ) ≤ mR x δ q (U * V)) hDx
  exact ⟨fun hc => hle.trans (add_le_add hmain (hb hc)),
    fun hc ε hε hε1 => hle.trans (add_le_add hmain (ht hc ε hε hε1))⟩

/-- **`BogusEta2C` on `TrompaisC`, `MainBogusEta2`, `EsthelBogusEta2C`, PROVED.** -/
theorem bogusEta2C_of_C (h1 : TrompaisC) (h2 : MainBogusEta2) (h3 : EsthelBogusEta2C) :
    BogusEta2C :=
  bogusEta2C_of (trompaisEta2_of h1) h2 h3

/-! ## (3) The arithmetic at the second choice with `tvorogC` -/

/-- The arithmetic core of (T2C): as `MPS2.tv2_core` with `R = log⁺(2e²UV/K)`. -/
theorem tv2C_core (k s L K P R u lam : ℝ) (hk0 : 0 ≤ k) (hk : k ≤ 3.5744) (hs0 : 1 ≤ s)
    (hs : s ≤ 1.73782) (hL : L ≤ 4 * lam + 6.04)
    (hP : (K + 1) * P ≤ 8.059 * u ^ 4 * (4 * lam + 1.8)) (hR0 : 0 ≤ (K + 1) * R)
    (hR : (K + 1) * R ≤ 8.059 * u ^ 4 * 6.66 + 9869) (hu : 8000 ≤ u) (hl : 8.3 ≤ lam) :
    k * (1 + 0.01) * (K + 1) * ((s - 1) * P + L / 2 * R) ≤ u ^ 4 * (473.5 * lam + 624.5) := by
  have hu4 : (8000 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have hu0 : 0 ≤ u ^ 4 := by positivity
  have hl0 : 0 ≤ lam := by linarith
  have hul : 0 ≤ u ^ 4 * lam := mul_nonneg hu0 hl0
  have hul8 : (8000 : ℝ) ^ 4 * lam ≤ u ^ 4 * lam := mul_le_mul_of_nonneg_right hu4 hl0
  have e : k * (1 + 0.01) * (K + 1) * ((s - 1) * P + L / 2 * R) =
      k * (1 + 0.01) * ((s - 1) * ((K + 1) * P) + L / 2 * ((K + 1) * R)) := by ring
  rw [e]
  have hB : 0 ≤ 8.059 * u ^ 4 * (4 * lam + 1.8) := mul_nonneg (by positivity) (by linarith)
  have i1 : (s - 1) * ((K + 1) * P) ≤ 0.73782 * (8.059 * u ^ 4 * (4 * lam + 1.8)) :=
    (mul_le_mul_of_nonneg_left hP (by linarith)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hB)
  have i2 : L / 2 * ((K + 1) * R) ≤ (4 * lam + 6.04) / 2 * (8.059 * u ^ 4 * 6.66 + 9869) :=
    mul_le_mul (by linarith) hR hR0 (by linarith)
  have hI2 : 0 ≤ (4 * lam + 6.04) / 2 * (8.059 * u ^ 4 * 6.66 + 9869) :=
    mul_nonneg (by linarith) (by positivity)
  have hk1 : k * (1 + 0.01) ≤ 3.5744 * 1.01 := by linarith
  have hk10 : 0 ≤ k * (1 + 0.01) := mul_nonneg hk0 (by norm_num)
  have e2 : 3.5744 * 1.01 * (0.73782 * (8.059 * u ^ 4 * (4 * lam + 1.8)) +
      (4 * lam + 6.04) / 2 * (8.059 * u ^ 4 * 6.66 + 9869)) =
      3.5744 * 1.01 * (0.73782 * 8.059 * 4 + 2 * 8.059 * 6.66) * (u ^ 4 * lam) +
        3.5744 * 1.01 * (0.73782 * 8.059 * 1.8 + 3.02 * 8.059 * 6.66) * u ^ 4 +
        3.5744 * 1.01 * (2 * 9869) * lam + 3.5744 * 1.01 * (3.02 * 9869) := by ring
  calc _ ≤ k * (1 + 0.01) * (0.73782 * (8.059 * u ^ 4 * (4 * lam + 1.8)) +
          (4 * lam + 6.04) / 2 * (8.059 * u ^ 4 * 6.66 + 9869)) :=
        mul_le_mul_of_nonneg_left (add_le_add i1 i2) hk10
    _ ≤ 3.5744 * 1.01 * (0.73782 * (8.059 * u ^ 4 * (4 * lam + 1.8)) +
          (4 * lam + 6.04) / 2 * (8.059 * u ^ 4 * 6.66 + 9869)) :=
        mul_le_mul_of_nonneg_right hk1 (add_nonneg (mul_nonneg (by norm_num) hB) hI2)
    _ ≤ u ^ 4 * (473.5 * lam + 624.5) := by rw [e2]; linarith

/-- **(T2C)** the `K`-terms of `tvorogC` at `ε = 0.01`: `≤ u⁴(473.5λ + 624.5)`. -/
theorem tvC_T2 (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hdq : |δ| * q ≤ u2 Y)
    (hD : (Y ^ ((1 : ℝ) / 6)) ^ 2 / (12 * c2) ≤ |δ| * q) :
    2 * Real.sqrt (c0 * c1b Y (u2 Y * v2 Y)) / Real.pi * (1 + 0.01) * (Y / (|δ| * q) + 1) *
        ((Real.sqrt (3 + 2 * 0.01) - 1) * Real.log ((Y / (|δ| * q) + 1) / Real.sqrt 2) +
          Real.log (u2 Y * v2 Y) / 2 *
            logp (2 * (Real.exp 2 * (u2 Y * v2 Y)) / (Y / (|δ| * q)))) ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 * (473.5 * Real.log (Y ^ ((1 : ℝ) / 6)) + 624.5) := by
  obtain ⟨hD0, hKlo, hKhi⟩ := K_bounds Y (|δ| * q) hY hdq hD
  obtain ⟨hUV, -, hc1, -, -⟩ := sdata Y hY
  obtain ⟨hlS3, -, -, -⟩ := logs_S
  have hlS3' := logS3_ge
  obtain ⟨hK8, hK24a, hK24b⟩ := logs_K
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hk := kb_coef _ hc1
  have hu := u_ge Y hY
  have l2 := Real.log_two_lt_d9
  have l2' := Real.log_two_gt_d9
  set k := 2 * Real.sqrt (c0 * c1b Y (u2 Y * v2 Y)) / Real.pi with hk_def
  set u := Y ^ ((1 : ℝ) / 6) with hu_def
  set lam := Real.log u with hlam_def
  set K := Y / (|δ| * q) with hK_def
  have hu0 : 0 < u := by linarith
  have hk0 : 0 ≤ k := by rw [hk_def]; positivity
  have hu4 : (8000 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hKlo
  have hsq : Real.sqrt (3 + 2 * 0.01) ≤ 1.73782 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hsq1 : 1 ≤ Real.sqrt (3 + 2 * 0.01) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hlUV : Real.log (u2 Y * v2 Y) = Real.log (500 * Real.sqrt 6 / 3) + 4 * lam := by
    rw [hUV, Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  -- (A) `(K + 1)log((K + 1)/√2) ≤ 8.059u⁴(4λ + 1.8)`
  have hK1 : K + 1 ≤ 8.059 * u ^ 4 := by linarith
  have hlg8 : Real.log (8.059 * u ^ 4 / Real.sqrt 2) =
      Real.log (8.059 / Real.sqrt 2) + 4 * lam := by
    rw [show 8.059 * u ^ 4 / Real.sqrt 2 = 8.059 / Real.sqrt 2 * u ^ 4 by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have hlg80 : 0 ≤ Real.log (8.059 * u ^ 4 / Real.sqrt 2) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    have : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  have hTA := tlogc_mono (K + 1) (8.059 * u ^ 4) (Real.sqrt 2) (by positivity) (by linarith)
    hK1 hlg80
  have hTA' : (K + 1) * Real.log ((K + 1) / Real.sqrt 2) ≤ 8.059 * u ^ 4 * (4 * lam + 1.8) := by
    refine hTA.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [hlg8]; linarith
  -- (B) `(K + 1)log⁺(A/K) ≤ 8.059u⁴·6.66 + 9869`, `A = 2e²UV`
  set A := 2 * (Real.exp 2 * (u2 Y * v2 Y)) with hA_def
  have hA0 : 0 < A := by rw [hA_def, hUV]; positivity
  have hAK : A / (8.058 * u ^ 4) = Real.exp 2 * (2 * (500 * Real.sqrt 6 / 24.174)) := by
    rw [hA_def, hUV, div_eq_iff (by positivity)]; ring
  have hlAK : Real.log (A / (8.058 * u ^ 4)) =
      2 + (Real.log 2 + Real.log (500 * Real.sqrt 6 / 24.174)) := by
    rw [hAK, Real.log_mul (by positivity) (by positivity), Real.log_exp,
      Real.log_mul (by norm_num) (by positivity)]
  have hkl := klog_le A K (8.058 * u ^ 4) hK0 hKhi (by rw [hlAK]; linarith) hA0
  have hKK : 8.058 * u ^ 4 / K ≤ 9870 := by
    rw [div_le_iff₀ hK0]
    have h1 := mul_le_mul_of_nonneg_left hKlo (by norm_num : (0 : ℝ) ≤ 9870)
    have e : 9870 * (u ^ 4 / 1224.745) = 9870 / 1224.745 * u ^ 4 := by ring
    have h2 : 8.058 * u ^ 4 ≤ 9870 / 1224.745 * u ^ 4 :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    linarith
  have hlogK : 0 ≤ Real.log (A / K) := by
    have h1 : A / (8.058 * u ^ 4) ≤ A / K := div_le_div_of_nonneg_left hA0.le hK0 hKhi
    have h2 := Real.log_le_log (by positivity) h1
    rw [hlAK] at h2; linarith
  have hlp : logp (A / K) = Real.log (A / K) := max_eq_left hlogK
  have hTB : (K + 1) * logp (A / K) ≤ 8.059 * u ^ 4 * 6.66 + 9869 := by
    rw [hlp]
    have h3 : (8.058 * u ^ 4 + 1) * Real.log (A / (8.058 * u ^ 4)) ≤ 8.059 * u ^ 4 * 6.66 := by
      rw [hlAK]
      exact mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
    linarith
  have hTB0 : 0 ≤ (K + 1) * logp (A / K) := mul_nonneg (by linarith) (le_max_right _ _)
  exact tv2C_core k _ _ K _ _ u lam hk0 hk hsq1 hsq (by rw [hlUV]; linarith) hTA' hTB0 hTB hu
    hl1

/-- **`tvorogC` at the second choice, `ε = 0.01`**: `≤ u⁴(6310.5λ + 8004.3)`. -/
theorem tvoC_le (Y δ : ℝ) (q : ℕ) (hY : 3.4e23 ≤ Y) (hdq : |δ| * q ≤ u2 Y)
    (hD : (Y ^ ((1 : ℝ) / 6)) ^ 2 / (12 * c2) ≤ |δ| * q) :
    tvorogC Y δ q (u2 Y) (v2 Y) 0.01 ≤
      (Y ^ ((1 : ℝ) / 6)) ^ 4 * (6310.5 * Real.log (Y ^ ((1 : ℝ) / 6)) + 8004.3) := by
  have h1 := tv_T1 Y hY
  have h2 := tvC_T2 Y δ q hY hdq hD
  have h3 := tv_T3 Y hY
  unfold tvorogC
  linarith

/-- The final comparison for `|δ| > 1/2c₂` with `tvorogC`. -/
theorem fin2C (u lam C T : ℝ) (hu4 : 0 ≤ u ^ 4) (hl : 8.3 ≤ lam)
    (hC : C ≤ u ^ 4 * (18 * lam - 23.88))
    (hT : T ≤ u ^ 4 * (6310.5 * lam + 8004.3)) :
    C + T ≤ 1230.9 * u ^ 4 * (6 * lam) + 0.0006406 * u ^ 4 * (6 * lam) ^ 2 := by
  have h : 0 ≤ u ^ 4 * (0.0230616 * lam ^ 2 + 1056.9 * lam - 7980.42) :=
    mul_nonneg hu4 (by nlinarith [sq_nonneg lam])
  linarith

/-- **Link [SecI2ArithC] — NUMERIC: `S_{I,2}` at the second choice with `eq:tvorog`
CORRECTED** (`MPG.SecI2Arith` with `tvorogC` in the `|δ| > 1/2c₂` branch). -/
def SecI2ArithC : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ δ : ℝ, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ q2 Y → |δ| * q ≤ u2 Y →
    (Y ^ ((1 : ℝ) / 3) / 6 < q ∨ 4 / 3 * Y ^ ((1 : ℝ) / 3) < |δ| * q) →
      (|δ| ≤ 1 / (2 * c2) →
        cupcake3 Y δ q (u2 Y) (v2 Y) + piececake Y q (u2 Y) (v2 Y) ≤
          1230.9 * Y ^ ((2 : ℝ) / 3) * Real.log Y +
            0.0006406 * Y ^ ((2 : ℝ) / 3) * Real.log Y ^ 2) ∧
      (1 / (2 * c2) < |δ| →
        cupcake3 Y δ q (u2 Y) (v2 Y) + tvorogC Y δ q (u2 Y) (v2 Y) 0.01 ≤
          1230.9 * Y ^ ((2 : ℝ) / 3) * Real.log Y +
            0.0006406 * Y ^ ((2 : ℝ) / 3) * Real.log Y ^ 2)

/-- **`SecI2ArithC`, PROVED.** -/
theorem secI2ArithC : SecI2ArithC := by
  intro Y hY δ q hq hQ hdq hA
  have hY0 : (0 : ℝ) < Y := by linarith
  obtain ⟨e23, -, -, -, eL⟩ := rpow_facts Y hY0
  obtain ⟨-, -, -, hl1, -, -⟩ := kdata Y hY
  have hc := cup_le Y δ q hY hq hQ hA
  have hu4 : (0 : ℝ) ≤ (Y ^ ((1 : ℝ) / 6)) ^ 4 := by positivity
  refine ⟨(secI2Arith Y hY δ q hq hQ hdq hA).1, fun hd => ?_⟩
  rw [e23, eL]
  exact fin2C _ _ _ _ hu4 hl1 hc (tvoC_le Y δ q hY hdq (dq_lower Y δ q hY hA hd))

/-! ## (4) `SecI2At` from the corrected `lem:bogus` -/

/-- **`MPc.SecI2At` from `BogusEta2C` and `SecI2ArithC`, PROVED.** -/
theorem secI2At_ofC (hb : BogusEta2C) (ha : SecI2ArithC) : SecI2At := by
  intro Y hY α δ a q ⟨hq, hga, h2, hQ, hδ, hA⟩
  obtain ⟨-, h2e, hsqQ, -, -, -, he2, hU1, hV1, hUV, -⟩ := sec_hyps Y hY
  have hdq := dq_le_u2 Y δ q hY hq hδ
  obtain ⟨hk, ht⟩ := hb Y α δ (q2 Y) (u2 Y) (v2 Y) a q hq hga h2 hδ hQ h2e hsqQ he2 hU1 hV1
    hUV
  obtain ⟨hak, hat⟩ := ha Y hY δ q hq hQ hdq hA
  rcases le_or_gt |δ| (1 / (2 * c2)) with hd | hd
  · exact (hk (Or.inl hd)).trans (hak hd)
  · exact (ht hd.le 0.01 (by norm_num) (by norm_num)).trans (hat hd)

/-- **`MPc.SecI2At` from the corrected `lem:bogus` alone, PROVED.** -/
theorem secI2At_of_genC (hb : BogusEta2C) : SecI2At :=
  secI2At_ofC hb secI2ArithC

/-- **`OP.MinMainP 0.811 45.7575` with `SecI2At` from the CORRECTED `lem:bogus`**:
`MPS1.minMainP_of_nine` with `SecI2At` supplied by `BogusEta2C`. Application only. -/
theorem minMainP_of_genC (hb1 : Bostb1Eta2) (hbg : BogusEta2C) (hgr : Grara) (hro : Ronsard)
    (hme : Meproz) (hb2 : Bosta2Eta2) (hv1 : Vinland1At) (her : EriksagaAt) (hs3 : SecIIAt)
    (h15 : GS.RS62Thm15) : OP.MinMainP 0.811 45.7575 :=
  minMainP_of_nine hb1 hgr hro hme hb2 hv1 her (secI2At_of_genC hbg) hs3 h15

end Principia.Common.TernaryGoldbach.MPBC
