/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.BogusEsthelE
import Principia.Common.TernaryGoldbach.Bosta2Main

set_option autoImplicit false

/-!
# `MPBD.MainBogusEta2C` spined: the Poisson assembly PROVED, two coefficient sums named

The main term of `lem:bogus` (book `typeI.tex` 1576-1660): for `d = uv ≤ M`, `q ∣ d`, `d` odd,
Poisson (`MPBM.tmo_main`, from `MPTC.EtaHatBound`) writes `T_{d,∘} = (x/2d)(−1)^{(d/q)a}η̂₂(−δ/2)`
up to `(c₀d/2π²x)(π² − 4)`. So `eq:hoho` splits into exactly two statements about the coefficient
`c = μ_{≤U} ∗ Λ_{≤V}` (`MPBG.cUV`), each a NAMED link with no analysis in it:

* `CoefMainBound` -- `|∑_{d ≤ M, q ∣ d} c(d)f(d)/d| ≤ (log q + log V)/q` (book: the `v`-`u`
  regrouping, `eq:grara` for the `u`-sums, `eq:rala` for `∑ Λ(v)/v`);
* `CoefErrBound` -- `∑_{d ≤ M, q ∣ d} |c(d)|f(d)d ≤ M² log V/4q + (3c₄/4)MV + (3/8)(U + 1)²V log q`
  (book `eq:etoile`, CORRECTED: the last term is `(3/8)`, from `∑_{p^α ≤ V} p^α ≤ (3/2)V`, where
  the book's false `eq:etoile` has `1/4`; `eq:rala`, `eq:trado2`).

```
 MainBogusEta2C ← EtaHatBound (← HC.CameloGridCited, HC.WollustCited), CoefMainBound,
                  CoefErrBound          (mainBogusEta2C_of, PROVED)
 SecI2At ← HC.CameloGridCited, HC.WollustCited, CoefMainBound, CoefErrBound
                                        (secI2At_of_coef, PROVED)
```

Both coefficient links are true for every real `M` (the derivation never uses `M ≤ UV`).
`RalaOdd` (`∑_{n ≤ V odd} Λ(n)/n ≤ log V`) is the odd-`n` half of the book's `eq:rala`
(`notprem.tex` 309, "derived from [RS62, (3.23)] supplemented by a quick calculation"); it is
stated here for the provers of the two links and consumed by nothing yet.
-/

namespace Principia.Common.TernaryGoldbach.MPMB

open ArithmeticFunction Principia.Common.Goldbach
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPG Principia.Common.TernaryGoldbach.MPB2
  Principia.Common.TernaryGoldbach.MPBG Principia.Common.TernaryGoldbach.MPBD
  Principia.Common.TernaryGoldbach.MPTC

/-! ## (1) The named links -/

/-- **Link [CoefMainBound] — the main-term coefficient sum of `lem:bogus`** (`eq:hoho`, first
part): `|∑_{d ≤ M, q ∣ d} c(d)f(d)/d| ≤ (log q + log V)/q` for `c = μ_{≤U} ∗ Λ_{≤V}`. OPEN. -/
def CoefMainBound : Prop :=
  ∀ (U V M : ℝ) (q : ℕ), 1 ≤ q → 1 ≤ U → 1 ≤ V →
    |∑ d ∈ (Finset.Icc 1 ⌊M⌋₊).filter (fun d => q ∣ d), cUV U V d * fOdd d / d| ≤
      (Real.log q + Real.log V) / q

/-- **Link [CoefErrBound] — the error coefficient sum of `lem:bogus`** (`eq:billy`,
`eq:etoile` CORRECTED): `∑_{d ≤ M, q ∣ d} |c(d)|f(d)d ≤ M² log V/4q + (3c₄/4)MV
+ (3/8)(U + 1)²V log q`. OPEN. -/
def CoefErrBound : Prop :=
  ∀ (U V M : ℝ) (q : ℕ), 1 ≤ q → 1 ≤ U → 1 ≤ V → 0 ≤ M →
    ∑ d ∈ (Finset.Icc 1 ⌊M⌋₊).filter (fun d => q ∣ d), |cUV U V d| * fOdd d * d ≤
      M ^ 2 * Real.log V / (4 * q) + 3 * c4 / 4 * M * V + 3 / 8 * (U + 1) ^ 2 * V * Real.log q

/-- **`eq:rala`, odd `n`** (Helfgott, `notprem.tex` 309: from [RS62, (3.23)] and a computation
for the prime powers `p < 32`): `∑_{n ≤ V, n odd} Λ(n)/n ≤ log V`. For the provers of the
coefficient links; NOT consumed by any theorem of this file. -/
def RalaOdd : Prop :=
  ∀ V : ℝ, 1 ≤ V → ∑ n ∈ (Finset.Icc 1 ⌊V⌋₊).filter Odd, ArithmeticFunction.vonMangoldt n / n ≤
      Real.log V

/-! ## (2) The assembly -/

/-- The terms `d ≤ ⌊x⌋`, `q ∣ d`, `d ≤ M` are the `d ∈ [1, ⌊M⌋]` with `q ∣ d` (`0 ≤ M ≤ x`). -/
theorem filter_eq (x M : ℝ) (q : ℕ) (hM0 : 0 ≤ M) (hMx : M ≤ x) :
    (Finset.Ioc 0 ⌊x⌋₊).filter (fun d => q ∣ d ∧ (d : ℝ) ≤ M) =
      (Finset.Icc 1 ⌊M⌋₊).filter (fun d => q ∣ d) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h0, -⟩, hq, hM⟩
    exact ⟨⟨h0, Nat.le_floor hM⟩, hq⟩
  · rintro ⟨⟨h1, h2⟩, hq⟩
    have hdM : (d : ℝ) ≤ M := (Nat.le_floor_iff hM0).mp h2
    exact ⟨⟨h1, Nat.le_floor (hdM.trans hMx)⟩, hq, hdM⟩

set_option maxHeartbeats 800000 in
-- the assembly of `MPBM.mainOddEta2_of` with the `lem:bogus` coefficient
/-- **`MPBD.MainBogusEta2C` from `EtaHatBound` and the two coefficient links, PROVED.** -/
theorem mainBogusEta2C_of (hB : EtaHatBound) (hA : CoefMainBound) (hE : CoefErrBound) :
    MainBogusEta2C := by
  intro x β δ Q0 U V a q hq _ h2β hδ hqQ h16 _ _ hU hV hUV
  have hx : 0 < x := by
    have h56 : (0 : ℝ) < x / 5.6 := by nlinarith
    linarith [show x / 5.6 * 5.6 = x by ring]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpi := Real.pi_pos
  have hc0 : (0 : ℝ) ≤ c0 := by unfold c0; norm_num
  have hD1 : 1 ≤ U * V := by nlinarith
  have hDx : U * V ≤ x := by
    have : U * V ≤ x / 5.6 := by linarith
    have h56 : x / 5.6 ≤ x := by rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  set M := mR x δ q (U * V) with hMdef
  have hMge := mR_ge x δ q (U * V) Q0 hx hq (by linarith) hδ
  have hM0 : 0 < M := lt_of_lt_of_le (lt_min (by linarith) (by linarith)) hMge
  have hMD : M ≤ U * V := mR_le x δ q (U * V)
  have hMx : M ≤ x := hMD.trans hDx
  have hy : ∀ d : ℕ, (d : ℝ) ≤ M → |(d : ℝ) * δ / x| ≤ 1 / 2 := by
    intro d hd
    by_cases h0 : δ = 0
    · rw [h0]; simp
    · have hdM : (d : ℝ) ≤ x / (2 * |δ| * q) := by
        have : M = min (x / (2 * |δ| * q)) (U * V) := by rw [hMdef]; unfold mR; rw [if_neg h0]
        rw [this] at hd
        exact hd.trans (min_le_left _ _)
      have hδ0 : 0 < |δ| := abs_pos.mpr h0
      rw [abs_div, abs_mul, Nat.abs_cast, abs_of_pos hx, div_le_iff₀ hx]
      rw [le_div_iff₀ (by positivity)] at hdM
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith
  set K : ℝ := c0 / (2 * Real.pi ^ 2 * x) * (Real.pi ^ 2 - 4) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ Real.pi ^ 2 - 4 := by nlinarith [Real.pi_gt_three]
    positivity
  set Mn : ℕ → ℂ := fun d => ((x / d / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ (((d / q : ℕ) : ℤ) * a) *
    etaHat (-δ / 2) with hMn
  have hper : ∀ d ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun d => q ∣ d ∧ (d : ℝ) ≤ M),
      ‖tmo x β d - Mn d‖ ≤ K * d := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Ioc] at hd
    obtain ⟨⟨hd0, _⟩, ⟨k, rfl⟩, hdM⟩ := hd
    have hkq : q * k / q = k := Nat.mul_div_cancel_left k (by omega)
    have hj0 : ((((q * k / q : ℕ) : ℤ) * a : ℤ) : ℝ) / 2 - ((q * k : ℕ) : ℝ) * β =
        -(((q * k : ℕ) : ℝ) * δ / x) / 2 := by
      have e2 : β = (a / q + δ / x) / 2 := by linarith
      rw [hkq, e2]
      push_cast
      field_simp
      ring
    have := MPBM.tmo_main hB x β hx (q * k) (by omega) _ _ (hy (q * k) hdM) hj0
    have harg : x / ((q * k : ℕ) : ℝ) * (-(((q * k : ℕ) : ℝ) * δ / x) / 2) = -δ / 2 := by
      field_simp
    rw [harg] at this
    calc ‖tmo x β (q * k) - Mn (q * k)‖
        ≤ c0 * ((q * k : ℕ) : ℝ) / (2 * Real.pi ^ 2 * x) * (Real.pi ^ 2 - 4) := this
      _ = K * ((q * k : ℕ) : ℝ) := by rw [hK]; ring
  set S := (Finset.Ioc 0 ⌊x⌋₊).filter (fun d => q ∣ d ∧ (d : ℝ) ≤ M) with hS
  have hSeq : S = (Finset.Icc 1 ⌊M⌋₊).filter (fun d => q ∣ d) := filter_eq x M q hM0.le hMx
  set cf : ℕ → ℝ := fun d => cUV U V d * fOdd d with hcf
  have hsplit : ∑ d ∈ S, ((cf d : ℝ) : ℂ) * tmo x β d =
      ∑ d ∈ S, ((cf d : ℝ) : ℂ) * Mn d + ∑ d ∈ S, ((cf d : ℝ) : ℂ) * (tmo x β d - Mn d) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  -- the error part
  have herr : ‖∑ d ∈ S, ((cf d : ℝ) : ℂ) * (tmo x β d - Mn d)‖ ≤
      K * (M ^ 2 * Real.log V / (4 * q) + 3 * c4 / 4 * M * V +
        3 / 8 * (U + 1) ^ 2 * V * Real.log q) := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ d ∈ S, ‖((cf d : ℝ) : ℂ) * (tmo x β d - Mn d)‖ ≤
        K * (|cUV U V d| * fOdd d * d) := by
      intro d hd
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hc : |cf d| = |cUV U V d| * fOdd d := by
        rw [hcf]; simp only; rw [abs_mul, abs_of_nonneg (fOdd_nonneg d)]
      rw [hc]
      calc |cUV U V d| * fOdd d * ‖tmo x β d - Mn d‖ ≤ |cUV U V d| * fOdd d * (K * d) :=
            mul_le_mul_of_nonneg_left (hper d hd)
              (mul_nonneg (abs_nonneg _) (fOdd_nonneg d))
        _ = K * (|cUV U V d| * fOdd d * d) := by ring
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum, hSeq]
    exact mul_le_mul_of_nonneg_left (hE U V M q hq hU hV hM0.le) hK0
  -- the main part: the sign `(−1)^{(d/q)a}` is `(−1)^a` whenever `f(d) ≠ 0`
  have hmain : ∑ d ∈ S, ((cf d : ℝ) : ℂ) * Mn d = ((x / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ a *
      etaHat (-δ / 2) * ((∑ d ∈ S, cf d / d : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [hS, Finset.mem_filter, Finset.mem_Ioc] at hd
    obtain ⟨⟨hd0, _⟩, ⟨k, hk⟩, _⟩ := hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hkq : d / q = k := by rw [hk]; exact Nat.mul_div_cancel_left k (by omega)
    simp only [hcf, hMn]
    rw [hkq]
    rcases Nat.even_or_odd k with he | ho
    · have h0 : fOdd d = 0 := by
        rw [hk, MPBM.fOdd_mul, fOdd_apply k, if_neg (by rw [Nat.even_iff] at he; omega),
          mul_zero]
      rw [h0]
      push_cast
      ring
    · have hs : (-1 : ℂ) ^ ((k : ℤ) * a) = (-1 : ℂ) ^ a := by
        rw [zpow_mul, Odd.neg_one_zpow (by exact_mod_cast ho)]
      rw [hs]
      push_cast
      field_simp
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hlV : 0 ≤ Real.log V := Real.log_nonneg hV
  have hmn : ‖∑ d ∈ S, ((cf d : ℝ) : ℂ) * Mn d‖ ≤
      x / (2 * q) * capM (c0 / Real.pi ^ 2) δ * Real.log (V * q) := by
    rw [hmain, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      norm_neg_one_zpow, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h3 := MPBM.etaHat_capM hB δ
    have hcap : 0 ≤ capM (c0 / Real.pi ^ 2) δ := (norm_nonneg _).trans h3
    have hA' : |∑ d ∈ S, cf d / d| ≤ (Real.log q + Real.log V) / q := by
      rw [hSeq]; exact hA U V M q hq hU hV
    have elog : Real.log (V * q) = Real.log q + Real.log V := by
      rw [Real.log_mul (by linarith) hqR.ne']; ring
    calc x / 2 * ‖etaHat (-δ / 2)‖ * |∑ d ∈ S, cf d / d|
        ≤ x / 2 * capM (c0 / Real.pi ^ 2) δ * ((Real.log q + Real.log V) / q) := by
          gcongr
      _ = x / (2 * q) * capM (c0 / Real.pi ^ 2) δ * Real.log (V * q) := by
          rw [elog]; field_simp
  -- the error part against `cupcake3C`
  have hMM : M ^ 2 * Real.log V / (4 * q) ≤ (U * V) ^ 2 * Real.log V / (4 * q) := by
    have : M ^ 2 ≤ (U * V) ^ 2 := pow_le_pow_left₀ hM0.le hMD 2
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hlV) (by positivity)
  have hMV : 3 * c4 / 4 * M * V ≤ 3 * c4 / 4 * (U * V) * V := by
    have : (0 : ℝ) ≤ 3 * c4 / 4 := by unfold c4; norm_num
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMD this) (by linarith)
  have herr2 : K * (M ^ 2 * Real.log V / (4 * q) + 3 * c4 / 4 * M * V +
      3 / 8 * (U + 1) ^ 2 * V * Real.log q) ≤
      K * ((U * V) ^ 2 * Real.log V / (4 * q) + 3 * c4 / 4 * (U * V) * V +
        3 / 8 * (U + 1) ^ 2 * V * Real.log q) :=
    mul_le_mul_of_nonneg_left (by linarith) hK0
  have hKe : K * ((U * V) ^ 2 * Real.log V / (4 * q) + 3 * c4 / 4 * (U * V) * V +
      3 / 8 * (U + 1) ^ 2 * V * Real.log q) =
      (1 / 4 - 1 / Real.pi ^ 2) * c0 *
        ((U * V) ^ 2 * Real.log V / (2 * q * x) + 3 * c4 / 2 * (U * V ^ 2 / x) +
          3 / 4 * ((U + 1) ^ 2 * V / x) * Real.log q) := by
    rw [hK]
    field_simp
    ring
  unfold cupcake3C
  linarith

/-- **`MPBD.MainBogusEta2C` from the two cited computer checks and the coefficient links.** -/
theorem mainBogusC_of_cited (hG : HC.CameloGridCited) (hW : HC.WollustCited)
    (hA : CoefMainBound) (hE : CoefErrBound) : MainBogusEta2C :=
  mainBogusEta2C_of (etaHatBound_of MPTI.etaHatIBP_holds (MPTS.cameloSup_of hG hW)) hA hE

/-- **`MPc.SecI2At` from the two cited computer checks and the two coefficient links, PROVED**
(`MPBE.secI2At_of_mainD`). -/
theorem secI2At_of_coef (hG : HC.CameloGridCited) (hW : HC.WollustCited)
    (hA : CoefMainBound) (hE : CoefErrBound) : SecI2At :=
  MPBE.secI2At_of_mainD hG hW (mainBogusC_of_cited hG hW hA hE)

end Principia.Common.TernaryGoldbach.MPMB
