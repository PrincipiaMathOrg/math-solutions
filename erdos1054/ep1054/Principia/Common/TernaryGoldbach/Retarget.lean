/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfWeights
import Principia.Common.TernaryGoldbach.MajorSpine
import Principia.Common.TernaryGoldbach.MajorFromPlatt
import Principia.Erdos1054.Proofs.BalancedK

set_option autoImplicit false

/-!
# Helfgott's chain RETARGETED to `K = 0.00032`, citing Platt's own statement

**EVERY LINK NAMED BELOW IS OPEN except where a theorem says otherwise. This file proves the
COMPOSITION.** Nothing here proves Helfgott's major- or minor-arc analysis, Platt's verification,
or ternary Goldbach.

## Why the target moved

EP1054 consumes Helfgott's weighted lower bound only through `BalancedNoRS.balanced_of_theta_le`
at `c = 1.3863`, which needs `K > W(3c²/30000 + 3·250047/(5·10²⁶)) = 0.000316939…`
(`Proofs.BalancedK`). At `K = 0.00032` the major arcs need only `1.049·x²/49`, not
`1.058259·x²/49`, and that frees enough slack that the singular-series link `C0Lower`
(`C₀ ≥ 1.3203236`, a 7-digit certification of the twin-prime constant) is replaced by the
library theorem `SingularSeries.sing3_ge_sharp` (`C₀ ≥ 1.31`). **No `C₀` link remains.**

## Why the Platt input changed

`Spine.PlattGRH` is GRH for primitive `χ` of conductor `q ≤ 300000` up to height `10⁸/q`. The
proof of HelfMaj Thm 1.4 (`majarcs.tex` 4855–4864) uses, for EVEN `q ≤ 300000`, the height
`T_q ≥ 200 + 7.5·10⁷/q`, which exceeds `10⁸/q` once `q > 125000` (at `q = 300000`: `450` against
`333.3`, `height_300000`). Platt verified that (arXiv:1305.3087, abstract, verbatim: *"primitive
characters of modulus q ≤ 400,000. For even q, we check to height t0 = max(1e8/q, 7.5e7/q + 200)
and for odd q to height t0 = max(1e8/q, 3.75e7/q + 200)"*). So the input cited here is Platt's
statement itself, `PlattFull`, with `plattHeight` his `t0`; `plattGRH_of_full` shows it implies
`Spine.PlattGRH`, and `even_height` that it covers the height Thm 1.4 uses.
`HelfMajFull` is `MajSp.HelfMaj` with `PlattFull` as its premise — WEAKER than `HelfMaj`
(`helfMajFull_of_helfMaj`), i.e. easier to discharge, and the honest shape of Thm 1.4.

## The chain

```
 PlattFull ─► HelfMajFull η₊ ηc ─┐  StarScale (rfl on HW)  Reg  Nefumo  Drujal  CLower  Norms  SupN
                                 ▼
  majorAt_of_links (C₀ ≥ 1.31 from sing3_ge_sharp; Z*, LS discharged) :  MajorLowerAt 1.049
                                 │                      MinorUpperAt 0.9845  (◄ MinorUpperSmooth)
  summ_of_majorAt ─► Summ ─► SmCI.circleId_of_summ ─► weighted_lower_at : 0.0645·x²/49 ≤ tripleW
                                 │   SmPP.pp_crude (13.73·H²/10⁹),  x ≥ (490/989)H
                                 ▼
  helfgottAt_of_smooth :  BalancedK.HelfgottAt 0.00032          (0.00032311 ≥ 0.00032)
                                 ▼   on Helfgott's weights (HW), BandUniform ⇒ SupBounds
  helfgottAt_of_links
```

## Arithmetic (exact rationals, re-verified)

* Major arcs at `C₀ ≥ 1.31` (`arith_close_131`): main `1.31·(1.2533139·0.8001287² − 0.000834)`,
  minus lines 1–3 exactly as in `MajSp.arith_close` (corrected `E*`): net `1.0499843/49 ≥ 1.049/49`,
  margin `9.8·10⁻⁴` (units `x²/49`).
* The composition (`helfgottAt_of_smooth`): `(1.049 − 0.9845)·(490/989)²/49 − 13.73/10⁹ =
  0.00032311 ≥ 0.00032`, margin `3.1·10⁻⁶`.
* The minor constant: Helfgott's `0.97392` (`Smooth.MinorUpperSmooth`) is `MinorUpperAt 0.97392`
  (`minorUpper_iff`, by `Iff.rfl`); `minorUpper_mono` weakens it to `0.9845`, so the retargeted link
  is IMPLIED by the original one and leaves `1.058·10⁻²` of room for a cheaper minor-arc bound.

## THE REMAINING WORK LIST, on Helfgott's own weights (`helfgottAt_of_links`)

`PlattFull` (a numerical certification, never a Lean theorem); `HW.BandUniform`
(`|h_200 − h| ≤ 0.13`, the band-limiting analysis); `HelfMajFull η₊ (η₂ ∗_M φ)` (HelfMaj
Thm 1.4, Cor 1.3, Prop 1.5); `Reg`, `Nefumo` (`prop:nefumo`), `Drujal` (`lem:drujal`),
`CLower` (`eq:barbar`), `Norms`, `SupN` (the numerical norms of `η₊`, `η*`, `η∘`);
`MinorUpperAt 0.9845 η₊ η*` (the minor arcs). Discharged here: `StarScale` (`rfl`), `C0Lower`
(gone), `ZStar`, `LSLink`, `CircleIdSmooth`, `Summ`, `PrimePowerSmooth` (all theorems of the
library), and `SupBounds` from `BandUniform`.

## Every new `Prop` constrains

* `PlattFull` implies `Spine.PlattGRH` (`plattGRH_of_full`), hence a piece of RH for `ζ`
  (`zeta_of_plattFull`), so it is neither free nor vacuous; it says strictly more than
  `Spine.PlattGRH` at `q = 300000` (`height_300000`).
* `HelfMajFull 0 ηc` refutes `PlattFull` (`helfMajFull_zero`: Prop 1.5 is a two-sided asymptotic).
* `MajorLowerAt c` with `c > 0` rejects every weight pair whose `smSum` vanishes at one scale
  (`major_fails_at`), and is met by the zero weights for `c ≤ 0` (`majorLowerAt_zero`).
* `MinorUpperAt c` is FALSE for every weight pair when `c < 0` (`minorUpperAt_neg`), is met by the
  zero weights for `c ≥ 0` (`minorUpperAt_zero`), and is implied by `MinorUpperSmooth` at `0.9845`.
-/

namespace Principia.Common.TernaryGoldbach.RT

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction
open Principia.Erdos1054 (helfgottX)
open Principia.Erdos1054.Proofs.BalancedK (HelfgottAt)

/-! ## (a) Platt's statement, verbatim -/

/-- **Platt's verified height** `t0` (arXiv:1305.3087, abstract): `max(10⁸/q, 3.75·10⁷/q + 200)` for
odd `q`, `max(10⁸/q, 7.5·10⁷/q + 200)` for even `q`. -/
noncomputable def plattHeight (q : ℕ) : ℝ :=
  if Odd q then max (10 ^ 8 / (q : ℝ)) (3.75e7 / (q : ℝ) + 200)
  else max (10 ^ 8 / (q : ℝ)) (7.5e7 / (q : ℝ) + 200)

/-- **Platt's finite GRH verification, as he states it** (arXiv:1305.3087): for every primitive
`χ` of modulus `q ≤ 400000`, every non-trivial zero of `L(s,χ)` with `|Im s| ≤ t0(q)` has
`Re s = 1/2`. The encoding is `Spine.PlattGRH`'s exactly ("non-trivial" as `0 < Re s < 1`), with
`300000` → `400000` and `10⁸/q` → `plattHeight q`. *NUMERICAL*: an obligation someone else owes. -/
def PlattFull : Prop :=
  ∀ (q : ℕ) [NeZero q], q ≤ 400000 → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ plattHeight q → s.re = 1 / 2

/-- Platt's height is at least `10⁸/q` at every modulus. -/
theorem height_ge (q : ℕ) : 10 ^ 8 / (q : ℝ) ≤ plattHeight q := by
  unfold plattHeight
  split_ifs
  · exact le_max_left _ _
  · exact le_max_left _ _

/-- **`PlattFull → Spine.PlattGRH`**: a larger modulus range and a larger height. -/
theorem plattGRH_of_full (h : PlattFull) : Spine.PlattGRH := by
  intro q _ hq χ hχ s hs h0 h1 him
  exact h q (le_trans hq (by norm_num)) χ hχ s hs h0 h1 (le_trans him (height_ge q))

/-- **The height Helfgott's Thm 1.4 uses for even `q`** (`majarcs.tex` 4855–4864):
`200 + 7.5·10⁷/q ≤ t0(q)`. (No `0 < q` is needed: at `q = 0` both sides are junk-consistent.) -/
theorem even_height (q : ℕ) (he : Even q) : 200 + 7.5e7 / (q : ℝ) ≤ plattHeight q := by
  have hno : ¬ Odd q := Nat.not_odd_iff_even.mpr he
  unfold plattHeight
  rw [if_neg hno, add_comm (200 : ℝ)]
  exact le_max_right _ _

/-- The odd-`q` counterpart: `200 + 3.75·10⁷/q ≤ t0(q)`. -/
theorem odd_height (q : ℕ) (ho : Odd q) : 200 + 3.75e7 / (q : ℝ) ≤ plattHeight q := by
  unfold plattHeight
  rw [if_pos ho, add_comm (200 : ℝ)]
  exact le_max_right _ _

/-- **`PlattFull` says strictly more than `Spine.PlattGRH`**: at `q = 300000` Platt's height is
`450`, while `Spine.PlattGRH` covers only `10⁸/300000 = 333.3…`. -/
theorem height_300000 : plattHeight 300000 = 450 ∧ (10 : ℝ) ^ 8 / 300000 < 450 := by
  have he : ¬ Odd 300000 := by decide
  refine ⟨?_, by norm_num⟩
  unfold plattHeight
  rw [if_neg he, max_eq_right] <;> norm_num

/-- **`PlattFull` is not vacuous**: it implies that every zero of `ζ` in the critical strip up to
height `10⁸` is on the critical line (through `MajorPlatt.plattGRH_implies_zeta_zeros_on_line`). -/
theorem zeta_of_plattFull (pf : PlattFull) (s : ℂ) (hz : riemannZeta s = 0) (h0 : 0 < s.re)
    (h1 : s.re < 1) (hT : |s.im| ≤ 10 ^ 8) : s.re = 1 / 2 :=
  MajorPlatt.plattGRH_implies_zeta_zeros_on_line (plattGRH_of_full pf) s hz h0 h1 hT

/-! ## (b) HelfMaj, conditional on Platt's own statement -/

/-- **HelfMaj with Platt's full statement as premise**: Thm 1.4 for `ηp`, Cor 1.3 for the base `ηc`
of `η*`, Prop 1.5 for `ηp` (`MajSp.Malpor`, `Coprar`, `Malheur`, verbatim). OPEN. -/
def HelfMajFull (ηp ηc : ℝ → ℝ) : Prop :=
  PlattFull → MajSp.Malpor ηp ∧ MajSp.Coprar ηc ∧ MajSp.Malheur ηp

/-- `HelfMajFull` is WEAKER than `MajSp.HelfMaj` (its premise is stronger), so replacing one by the
other in a spine can only make the spine easier to discharge. -/
theorem helfMajFull_of_helfMaj (ηp ηc : ℝ → ℝ) (h : MajSp.HelfMaj ηp ηc) :
    HelfMajFull ηp ηc := fun pf => h (plattGRH_of_full pf)

/-- **`HelfMajFull` rejects `η₊ = 0` exactly as far as Platt holds**: Prop 1.5 is a two-sided
asymptotic (`MajSp.malheur_zero`). -/
theorem helfMajFull_zero (ηc : ℝ → ℝ) (h : HelfMajFull 0 ηc) : ¬ PlattFull :=
  fun pf => MajSp.malheur_zero (h pf).2.2

/-! ## (c) The major arcs at `C₀ ≥ 1.31` -/

/-- `C₀ ≥ 1.31` for odd `N`, from the library's `SingularSeries.sing3_ge_sharp` (`131/100`). -/
theorem c0_131 (N : ℕ) (hN : Odd N) : (1.31 : ℝ) ≤ SingularSeries.sing3 N :=
  le_of_eq_of_le (by norm_num) (SingularSeries.sing3_ge_sharp N hN)

/-- **The main term at `C₀ ≥ 1.31`**: `MajSp.main_ge` with `1.3203236` replaced by `1.31`. -/
theorem main_ge_131 (s C0 Cc lo : ℝ) (hs1 : 1.2533139 ≤ s) (hC0 : 1.31 ≤ C0)
    (hCc : (s * lo ^ 2 - 0.000834) / 49 ≤ Cc) (hlo1 : 0.8001287 ≤ lo) :
    1.31 * ((1.2533139 * 0.8001287 ^ 2 - 0.000834) / 49) ≤ C0 * Cc := by
  have hlo2' : 0.8001287 ^ 2 ≤ lo ^ 2 := pow_le_pow_left₀ (by norm_num) hlo1 2
  have hslo : 1.2533139 * 0.8001287 ^ 2 ≤ s * lo ^ 2 :=
    mul_le_mul hs1 hlo2' (by norm_num) (by linarith)
  have hCc' : (1.2533139 * 0.8001287 ^ 2 - 0.000834) / 49 ≤ Cc :=
    le_trans (div_le_div_of_nonneg_right (by linarith) (by norm_num)) hCc
  exact mul_le_mul hC0 hCc' (by norm_num) (by linarith)

/-- **`MajSp.arith_close` at `C₀ ≥ 1.31`**: the same `prop:nefumo` bound with Helfgott's numbers
(and the corrected `E*`) forces `Re ∫_𝔐 ≥ 1.049 x²/49`. Net `1.0499843`, margin `9.8·10⁻⁴`. -/
theorem arith_close_131 (x s C0 Cc lo l3 lp ls A Zp Zs : ℝ) (I : ℂ)
    (hx : 49 * 10 ^ 25 ≤ x) (hs1 : 1.2533139 ≤ s) (hs2 : s ≤ 1.2533143)
    (hC0 : 1.31 ≤ C0) (hCc : (s * lo ^ 2 - 0.000834) / 49 ≤ Cc)
    (hlo1 : 0.8001287 ≤ lo) (hlo2 : lo ≤ 0.8001288) (hl3 : 0 ≤ l3) (hl3' : l3 ≤ 32.5023)
    (hlp : lp ≤ 0.800132) (hls0 : 0 ≤ ls) (hls : ls ^ 2 ≤ 1.77082 / 49)
    (hA : A ≤ 8.7806) (hZp : Zp ≤ 0.640209 * Real.log x)
    (hZs0 : 0 ≤ Zs) (hZs : Zs ≤ 0.0362 * Real.log x)
    (hI : ‖I - ((C0 * Cc * x ^ 2 : ℝ) : ℂ)‖ ≤
      (2.82643 * lo ^ 2 * (2 + 3.0371e-6) * 3.0371e-6 +
          (4.31004 * lo ^ 2 + 0.0012 * l3 ^ 2 / 8 ^ 5) / 150000) * (s / 49) * x ^ 2 +
        (1.3353e-7 / 49 * A + 2.3921e-8 * 1.6812 * (Real.sqrt A + 1.6812 * lp) * ls) * x ^ 2 +
        (2 * Zp * (24.32 * Real.log x + 0.57) +
          4 * Real.sqrt (Zp * Zs) * (18.57 * Real.log x + 28.39)) * x) :
    1.049 * x ^ 2 / 49 ≤ I.re := by
  have hX : 0 ≤ x ^ 2 := sq_nonneg x
  have hm := mul_le_mul_of_nonneg_right (main_ge_131 s C0 Cc lo hs1 hC0 hCc hlo1) hX
  have h1 := mul_le_mul_of_nonneg_right (MajSp.line1_le s lo l3 hs1 hs2 hlo1 hlo2 hl3 hl3') hX
  have h2 := mul_le_mul_of_nonneg_right (MajSp.line2_le A lp ls hA hlp hls0 hls) hX
  have h3 := MajSp.line3_le x Zp Zs hx hZp hZs0 hZs
  have habs := Complex.abs_re_le_norm (I - ((C0 * Cc * x ^ 2 : ℝ) : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re] at habs
  have hlow := (abs_le.mp (le_trans habs hI)).1
  linarith only [hlow, hm, h1, h2, h3, hX]

/-- **The major-arc lower bound at constant `c`**: `(7.25)` with `1.058259` replaced by `c` and
WITHOUT Platt inside (the chain below takes `PlattFull` as its own hypothesis). -/
def MajorLowerAt (c : ℝ) (ηp ηs : ℝ → ℝ) : Prop :=
  ∀ N : ℕ, Odd N → 10 ^ 27 ≤ N →
    c * helfgottX N ^ 2 / 49 ≤
      (∫ α in Smooth.majorSet (helfgottX N), Smooth.kernS ηp ηs N (helfgottX N) α).re

/-- **THE SPINE of (7.25) at `1.049`, with NO `C₀` link.** `MajSp.majorLower_lz` (nine links) with
`C0Lower` replaced by `SingularSeries.sing3_ge_sharp` (via `c0_131`), `ZStar`/`LSLink` by
`MajSp.zstar_holds`/`MajSp.ls_link`, `HelfMaj` by `HelfMajFull` and `PlattGRH` by `PlattFull`. The
proof is `MajSp.majorLower_of_links`'s, application only; its arithmetic is `arith_close_131`. -/
theorem majorAt_of_links (ηp ηs ηo ηc : ℝ → ℝ) (hm : HelfMajFull ηp ηc)
    (sc : MajSp.StarScale ηs ηc) (rg : MajSp.Reg ηp ηs ηo) (nf : MajSp.Nefumo ηp ηs ηo)
    (dj : MajSp.Drujal ηp) (cl : MajSp.CLower ηo ηs) (nm : MajSp.Norms ηp ηs ηo)
    (sn : MajSp.SupN ηp ηs) (pf : PlattFull) :
    ∀ N : ℕ, Odd N → 10 ^ 27 ≤ N → 1.049 * helfgottX N ^ 2 / 49 ≤
      (∫ α in Smooth.majorSet (helfgottX N), Smooth.kernS ηp ηs N (helfgottX N) α).re := by
  intro N hodd hN
  obtain ⟨mp, cp, mh⟩ := hm pf
  obtain ⟨hlo1, hlo2, hdiff, hl3, hld, hl1s, hls, hl1p, hl2p⟩ := nm
  have hx := MajSp.helfX_big N hN
  have hEp := MajSp.eb_plus ηp mp (helfgottX N) hx
  have hEs := MajSp.eb_star ηs ηc sc cp (helfgottX N) hx
  have hET := MajSp.et_plus ηp mp (helfgottX N) hx
  have hT0 := MajSp.et0_star ηs ηc sc cp (helfgottX N) hx
  have hZp := MajSp.zplus ηp (helfgottX N) hx (mh (helfgottX N) (MajSp.x12_le _ hx))
  have hZs := MajSp.zstar_holds ηs sn.2.2.1 sn.2.2.2.2 hl1s (helfgottX N) hx hT0
  have hA := dj rg.2.2.1 sn.1 hl1p hl2p (helfgottX N) hx hET hEp
  obtain ⟨hLp, hLs⟩ := MajSp.ls_link ηp ηs sn (helfgottX N) hx
  have hlt := MajSp.eps_lt _ _ hdiff hlo1
  have hnef := nf rg 3.0371e-6 MajSp.eps_nonneg hlt N (MajSp.N_one N hN) (helfgottX N) hx
    2.3921e-8 (1.3353e-7 / 49) hEp hEs (18.57 * Real.log (helfgottX N) + 28.39)
    (24.32 * Real.log (helfgottX N) + 0.57) hLp hLs
  rw [hl1s] at hnef
  have hC := cl hld N hodd hN
  obtain ⟨hs1, hs2⟩ := MajSp.sqrt_pi_half
  exact arith_close_131 (helfgottX N) (Real.sqrt (Real.pi / 2)) (SingularSeries.sing3 N)
    (MajSp.ccon ηo ηs ((N : ℝ) / helfgottX N)) (MajSp.l2 ηo) (MajSp.l1 (iteratedDeriv 3 ηo))
    (MajSp.l2 ηp) (MajSp.l2 ηs) (MajSp.amaj ηp (helfgottX N))
    (MajSp.zk (fun t => ηp t ^ 2) 2 (helfgottX N)) (MajSp.zk (fun t => ηs t ^ 2) 2 (helfgottX N))
    _ hx hs1 hs2 (c0_131 N hodd) hC hlo1 hlo2 (MajSp.l1_nonneg _) hl3 hl2p (MajSp.l2_nonneg _) hls
    hA hZp (MajSp.zk_sq_nonneg _ _ (MajSp.x_nonneg _ hx)) hZs hnef

/-! ## (d) The smoothed composition at constants -/

/-- **The minor-arc upper bound at constant `c`**: `(7.48)` with `0.97392` replaced by `c`. -/
def MinorUpperAt (c : ℝ) (ηp ηs : ℝ → ℝ) : Prop :=
  ∀ N : ℕ, Odd N → 10 ^ 27 ≤ N →
    (∫ α in Smooth.minorSet (helfgottX N),
        ‖Smooth.smSum ηs (helfgottX N) α‖ * ‖Smooth.smSum ηp (helfgottX N) α‖ ^ 2) ≤
      c * helfgottX N ^ 2 / 49

/-- `Smooth.MinorUpperSmooth` IS the `c = 0.97392` case, by `Iff.rfl`. -/
theorem minorUpper_iff (ηp ηs : ℝ → ℝ) :
    Smooth.MinorUpperSmooth ηp ηs ↔ MinorUpperAt 0.97392 ηp ηs :=
  Iff.rfl

/-- `MinorUpperAt` is monotone in the constant. -/
theorem minorUpper_le {c c' : ℝ} (hc : c ≤ c') (ηp ηs : ℝ → ℝ) (h : MinorUpperAt c ηp ηs) :
    MinorUpperAt c' ηp ηs := by
  intro N hodd hN
  have hx2 : 0 ≤ helfgottX N ^ 2 / 49 := div_nonneg (sq_nonneg _) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hc hx2
  have hh := h N hodd hN
  rw [mul_div_assoc] at hh ⊢
  exact le_trans hh hmul

/-- **The retargeted minor-arc link is IMPLIED by Helfgott's**: `0.97392 ≤ 0.9845`. -/
theorem minorUpper_mono (ηp ηs : ℝ → ℝ) (h : Smooth.MinorUpperSmooth ηp ηs) :
    MinorUpperAt 0.9845 ηp ηs :=
  minorUpper_le (by norm_num) ηp ηs ((minorUpper_iff ηp ηs).mp h)

/-- `MinorUpperAt c` is FALSE for every weight pair when `c < 0`: the integrand is nonnegative. -/
theorem minorUpperAt_neg {c : ℝ} (hc : c < 0) (ηp ηs : ℝ → ℝ) : ¬ MinorUpperAt c ηp ηs := by
  intro h
  have hh := h (10 ^ 27 + 1) ⟨5 * 10 ^ 26, by norm_num⟩ (by norm_num)
  have h0 : 0 ≤ ∫ α in Smooth.minorSet (helfgottX (10 ^ 27 + 1)),
      ‖Smooth.smSum ηs (helfgottX (10 ^ 27 + 1)) α‖ *
        ‖Smooth.smSum ηp (helfgottX (10 ^ 27 + 1)) α‖ ^ 2 :=
    integral_nonneg fun α => mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hx := Smooth.helfX_pos (10 ^ 27 + 1) (by norm_num)
  have hneg : c * helfgottX (10 ^ 27 + 1) ^ 2 / 49 < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hc (pow_pos hx 2)) (by norm_num)
  exact lt_irrefl (0 : ℝ) (lt_of_le_of_lt (le_trans h0 hh) hneg)

/-- `MinorUpperAt c` is met by the zero weights for `c ≥ 0`. -/
theorem minorUpperAt_zero {c : ℝ} (hc : 0 ≤ c) : MinorUpperAt c 0 0 := by
  intro N _ _
  simp only [Smooth.smSum_zero, norm_zero, zero_mul, integral_zero]
  exact div_nonneg (mul_nonneg hc (sq_nonneg _)) (by norm_num)

/-- `MajorLowerAt c` is met by the zero weights for `c ≤ 0`. -/
theorem majorLowerAt_zero {c : ℝ} (hc : c ≤ 0) : MajorLowerAt c 0 0 := by
  intro N _ _
  have hk : ∀ α, Smooth.kernS 0 0 N (helfgottX N) α = 0 := fun α => by
    simp [Smooth.kernS, Smooth.smSum_zero]
  simp only [hk, integral_zero, Complex.zero_re]
  nlinarith [sq_nonneg (helfgottX N)]

/-- **For `c > 0`, `MajorLowerAt c` rejects any weight whose `smSum` vanishes at one scale** —
`Smooth.major_fails` at constant `c`, with no Platt premise. -/
theorem major_fails_at {c : ℝ} (hc : 0 < c) (ηp ηs : ℝ → ℝ) (N : ℕ) (hodd : Odd N)
    (hN : 10 ^ 27 ≤ N)
    (h0 : (∀ α, Smooth.smSum ηp (helfgottX N) α = 0) ∨
      (∀ α, Smooth.smSum ηs (helfgottX N) α = 0)) :
    ¬ MajorLowerAt c ηp ηs := by
  intro mj
  have hk : ∀ α, Smooth.kernS ηp ηs N (helfgottX N) α = 0 := by
    intro α
    rcases h0 with h | h <;> simp [Smooth.kernS, h α]
  have hmaj := mj N hodd hN
  simp only [hk, integral_zero, Complex.zero_re] at hmaj
  have hx : 0 < helfgottX N := Smooth.helfX_pos N (lt_of_lt_of_le (by norm_num) hN)
  have hpos : 0 < c * helfgottX N ^ 2 / 49 := div_pos (mul_pos hc (pow_pos hx 2)) (by norm_num)
  linarith

/-- **`Summ` from the major-arc link at ANY positive constant** — `Smooth.summ_of_major`'s argument:
a non-summable weight makes `smSum` junk `0`, hence the major-arc integral `0 < c·x²/49`. -/
theorem summ_of_majorAt {c : ℝ} (hc : 0 < c) (ηp ηs : ℝ → ℝ) (mj : MajorLowerAt c ηp ηs) :
    Smooth.Summ ηp ηs := by
  intro N hodd hN
  constructor
  · by_contra hns
    exact major_fails_at hc ηp ηs N hodd hN (Or.inl (Smooth.smSum_junk ηp _ hns)) mj
  · by_contra hns
    exact major_fails_at hc ηp ηs N hodd hN (Or.inr (Smooth.smSum_junk ηs _ hns)) mj

/-- **`Smooth.weighted_lower` at constants**: from (7.49), the major-arc bound at `cM` and the
minor-arc bound at `cm`, `tripleW ≥ (cM − cm)·x²/49`. -/
theorem weighted_lower_at (cM cm : ℝ) (ηp ηs : ℝ → ℝ) (sm : Smooth.Summ ηp ηs)
    (ci : Smooth.CircleIdSmooth ηp ηs) (mj : MajorLowerAt cM ηp ηs) (mn : MinorUpperAt cm ηp ηs)
    (N : ℕ) (hodd : Odd N) (hN : 10 ^ 27 ≤ N) :
    (cM - cm) * helfgottX N ^ 2 / 49 ≤ Smooth.tripleW ηp ηs N (helfgottX N) := by
  have hint : IntegrableOn (Smooth.kernS ηp ηs N (helfgottX N)) (Set.Ioc (0 : ℝ) 1) :=
    (Smooth.continuous_kernS ηp ηs N _ (sm N hodd hN).1 (sm N hodd hN).2).integrableOn_Ioc
  have hsplit := integral_inter_add_sdiff (Smooth.measurableSet_maj (helfgottX N)) hint
  have heq : ((Smooth.tripleW ηp ηs N (helfgottX N) : ℝ) : ℂ) =
      (∫ α in Smooth.majorSet (helfgottX N), Smooth.kernS ηp ηs N (helfgottX N) α) +
        ∫ α in Smooth.minorSet (helfgottX N), Smooth.kernS ηp ηs N (helfgottX N) α := by
    rw [ci N hodd hN, Smooth.majorSet, Smooth.minorSet]
    exact hsplit.symm
  have hre : Smooth.tripleW ηp ηs N (helfgottX N) =
      (∫ α in Smooth.majorSet (helfgottX N), Smooth.kernS ηp ηs N (helfgottX N) α).re +
        (∫ α in Smooth.minorSet (helfgottX N), Smooth.kernS ηp ηs N (helfgottX N) α).re := by
    simpa using congrArg Complex.re heq
  have hmaj := mj N hodd hN
  have h1 := norm_integral_le_integral_norm
    (μ := volume.restrict (Smooth.minorSet (helfgottX N))) (Smooth.kernS ηp ηs N (helfgottX N))
  simp only [Smooth.norm_kernS] at h1
  have hnorm := le_trans h1 (mn N hodd hN)
  have hmin := (abs_le.mp (le_trans (Complex.abs_re_le_norm _) hnorm)).1
  have hlin : (cM - cm) * helfgottX N ^ 2 / 49 =
      cM * helfgottX N ^ 2 / 49 - cm * helfgottX N ^ 2 / 49 := by ring
  linarith

/-- `BalancedK.HelfgottAt K` is, definitionally, the statement with `Smooth.citeSum` as its body
(the attachment check of `Smooth.cite_iff`, at constant `K`). -/
theorem helfgottAt_iff (K : ℝ) : HelfgottAt K ↔
    ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H →
      ∃ ηp ηs : ℝ → ℝ, (∀ u : ℝ, |ηp u| ≤ 1.079955) ∧ (∀ u : ℝ, |ηs u| ≤ 1.414) ∧
        K * (H : ℝ) ^ 2 ≤ Smooth.citeSum ηp ηs H :=
  Iff.rfl

/-- **THE SMOOTHED COMPOSITION AT `K = 0.00032`**: the sup norms, the major arcs at `1.049` and
the minor arcs at `0.9845` give `HelfgottAt 0.00032`. `Summ` comes from the major-arc link
(`summ_of_majorAt`), the circle identity from `SmCI.circleId_of_summ`, prime powers from
`SmPP.pp_crude`; arithmetic `(1.049 − 0.9845)(490/989)²/49 − 13.73/10⁹ = 0.00032311`. -/
theorem helfgottAt_of_smooth (ηp ηs : ℝ → ℝ) (sb : Smooth.SupBounds ηp ηs)
    (mj : MajorLowerAt 1.049 ηp ηs) (mn : MinorUpperAt 0.9845 ηp ηs) : HelfgottAt 0.00032 := by
  have sm := summ_of_majorAt (by norm_num) ηp ηs mj
  have ci := SmCI.circleId_of_summ ηp ηs sm
  refine (helfgottAt_iff 0.00032).mpr fun H hodd hH => ⟨ηp, ηs, sb.1, sb.2, ?_⟩
  have hW := weighted_lower_at 1.049 0.9845 ηp ηs sm ci mj mn H hodd hH
  have hc : (1.049 - 0.9845 : ℝ) = 0.0645 := by norm_num
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

/-! ## (e) On Helfgott's own weights -/

/-- **`η* = (η₂ ∗_M φ)(49·)` by definition**: `StarScale` holds by `rfl` for Helfgott's `η*` and
its unscaled base `η₂ ∗_M φ`. -/
theorem starScale_helf : MajSp.StarScale HW.etaStar (HW.mconv HW.eta2 HW.phi) := fun _ => rfl

/-- **`HelfgottAt 0.00032` on Helfgott's own weights** `η₊ = HW.etaPlus`, `η* = HW.etaStar`,
`η∘ = HW.etaCirc`, base `ηc = η₂ ∗_M φ`. Every hypothesis is an OPEN link, and together they are
the campaign's remaining work list for EP1054's last input: Platt's statement, `BandUniform`
(which gives `SupBounds`), HelfMaj on Platt's statement, the regularity/analysis/norm links of
`prop:nefumo`, and the minor arcs at `0.9845`. No `C₀`, `StarScale`, `ZStar`, `LSLink`,
circle-identity, summability or prime-power link remains. -/
theorem helfgottAt_of_links (pf : PlattFull) (hb : HW.BandUniform)
    (hm : HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (rg : MajSp.Reg HW.etaPlus HW.etaStar HW.etaCirc)
    (nf : MajSp.Nefumo HW.etaPlus HW.etaStar HW.etaCirc) (dj : MajSp.Drujal HW.etaPlus)
    (cl : MajSp.CLower HW.etaCirc HW.etaStar) (nm : MajSp.Norms HW.etaPlus HW.etaStar HW.etaCirc)
    (sn : MajSp.SupN HW.etaPlus HW.etaStar) (mn : MinorUpperAt 0.9845 HW.etaPlus HW.etaStar) :
    HelfgottAt 0.00032 :=
  helfgottAt_of_smooth HW.etaPlus HW.etaStar (HW.supBounds_band hb)
    (majorAt_of_links HW.etaPlus HW.etaStar HW.etaCirc (HW.mconv HW.eta2 HW.phi) hm starScale_helf
      rg nf dj cl nm sn pf) mn

end Principia.Common.TernaryGoldbach.RT
