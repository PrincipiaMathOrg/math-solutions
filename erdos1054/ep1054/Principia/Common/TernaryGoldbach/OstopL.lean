/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.OstopC

set_option autoImplicit false

/-!
# `thm:ostop` with Helfgott's `L` CORRECTED (`OstopL`): the restatement, layer 1 composed

**`OstopL`, `MNumL`, `FelipaAt 0.6406` and the layer-2 links are OPEN. This file proves the
COMPOSITION and the `T` link.** `OstopC.lean` states the F6/F7-repaired `thm:ostop`, but its
`ℓ^∞` function `OC.gY` carries `MinSp.lL`, the constant `L` of `minarcs.tex` `eq:kraw` /
`ternvin.tex` `eq:veror` as printed, and that constant is WRONG (LEAN-PROGRESS 2026-09-30,
"HELFGOTT'S `L` CONSTANT IS WRONG"; `scratchpad/spines/minmain_spine.md` H1-H3, H6-H7). Every
`g`-carrying object is restated here with the corrected `L`; `OstopC.lean` is NOT edited (a
running round imports it). The chain is composed to `RT.MinorUpperAt 1.0154`, the minor target of
the Chebyshev split (`K = 0.000205`).

## The slip and its correction (`minarcs.tex` 4081-4100, 5082-5100, 5270-5286)

* 5085 prints `3.30386 log δq³ + 16.4137`: that is the `c_ε` of `ε = 0.05` inside an `ε = 0.07`
  application of `lem:bosta2` (5082), and 5100 then turns `q³` into `q²`.
* Consistently at `ε = 0.07` the `1/q` part of `L` is `log q^A δ₀^B + C`, with `κ = c_ε c₁₄/2`,
  `κ' = c_ε(c₁₄ log 3√2 + c₁₅)`, `c_ε = 1.07·√3.14`, `c₁₄ = 3.57422`, `c₁₅ = 3.71301`,
  `c₂ = 6π/(5√31.521)`:
  `A = 6c₂κ = 13.65155938`, `B = κ/(e log 2) = 1.79837370`, `C = 2c₂κ' + 0.146575 = 22.75370958`
  (mpmath at 30 digits, `scratchpad/ostopl/`; the coordinator's `mtilde_L.py` agrees). The printed
  `80/9, 16/9, 111/5` are the values at `(q², ε = 0.05)` (`8.87386, 1.75348, 22.1894`).
* **They are used ROUNDED UP: `13.6516, 1.7984, 22.7538`.** `L` increases in each (`log q ≥ 0`,
  `log δ₀ ≥ log 2 > 0`), so rounding up only WEAKENS `MinMainL` (the claim to be proved from
  minarcs) and only ENLARGES `gTL`, hence makes `MNumL` harder: no rounding makes an open link
  easier.
* The `q/φ(q)` summand keeps `80/9`, since
  `7/4 log δ₀q + 6.11676 + 3/2 log q + 2.74107 ≤ log δ₀^{7/4}q^{13/4} + 80/9`
  (`6.11676 + 2.74107 = 8.85783 ≤ 8.8889`).
* `OC.lTosca`'s second `min` branch `(5/6) log x + 50/9` is DROPPED (H2): `eq:therwald` 5030-5037
  loses the factor `q/φ(q)` on `c_{4,I}` (`eq:dikaiopolis` 4983 has it), so the branch is not
  established, and `ternvin` `eq:veror` never uses it. `lToscaL` is the first branch only.
* At the scale of `eq:syryza` (`δ₀q = 2r`, `δ₀ ≥ 2`, and `δ₀^b q^a ≤ 2^b r^a` for `b < a`) the
  `1/q` part becomes `log 2^{1.7984} r^{13.6516} + 22.7538`. That is `lLc`, and `gYL` is `OC.gY`
  with `lLc` in place of `MinSp.lL` and NOTHING else changed: both are `gYAt` of their `L`, by
  `rfl` (`gY_eq_at`, `gYL_eq_at`); `lLc_eq` pins that `lLc` and `MinSp.lL` differ only in the
  `1/q` summand, and `lL_lt_lLc` that the correction is an increase.

## `MinMainL` (layer 2), restated

* It is required at EVERY scale `Y ≥ 3.4·10²³` (not `2.16·10²⁰`): `GorshL` applies it only at
  `Y = wy ≥ y/K ≥ 3.47·10²³`, and the `x^{2/3}` absorptions have slack there (H7). A larger
  threshold is a WEAKER claim.
* The case `q > Y^{1/3}/6` is LOOSENED to `1.25 h`, i.e.
  `0.3409 Y^{5/6}(log Y)^{3/2} + 1522.5 Y^{2/3} log Y` (`1.25·0.2727 = 0.340875`, rounded up;
  `1.25·1218 = 1522.5`). The printed second-case constants are unreliable (H3: `0.272652` is not
  reproduced, `1217.35` recomputes to about `1219.2`), and `GorshL` consumes `h` only through
  `h(Y) ≤ g_Y(Y,·)`, where the ratio is `≥ 1.62` on `Y ≥ 3.47·10²³`.

## The felipa slope is a parameter (F4)

`FelipaAt fs η` is the `S/x` bound the composition consumes, `S ≤ (fs log x − 0.021095)x`, in the
shape `MinSp.felipa` delivers it. `felipaAt_helf`: the existing chain (`RT.HelfMajFull`'s
`Malheur`, through `MinSp.felipa`) supplies `FelipaAt 0.640209`, and `felipaAt_mono` lifts it to
every larger slope (`felipaAt_6406_of_helf`), so the new statement ATTACHES. It is a HYPOTHESIS of
the composition because F4 (HelfMaj 4955-5005) breaks the typed `0.640209` (the referee: `≥
0.6402109` is needed; our `BandSharp` bound gives about `0.64045`); the instance takes `0.6406`.
`RT.HelfMajFull` is still GENUINELY needed: its `Malpor` feeds `DrujalLowP`'s `ET`/`EB` bounds
(`MajSp.et_plus`, `MajSp.eb_plus`) and its `Coprar` feeds `S_{η*}(0,x)` (`sstar_le`); only its
`Malheur` use is replaced by `FelipaAt`.

`LamberNumL φ fs`, the `T` link at slope `fs` (floor `8.3599`, constant `3.7·10⁻⁴`), is PROVED at
`fs = 0.6406` (`lamberNumL_helf`) by `LW.lamber_at` with the slope substituted (`lamber_atL`):
the remaining cubic in `w = log(x/49) ≥ 57.558` has worst ratio `0.9767`.

## The spine

```
 OC.gY = gYAt MinSp.lL,  gYL = gYAt lLc                        (rfl: only L differs)
 gTL, intGTL, mMCL = OC.gT, OC.intGT, OC.mMC with gY ↦ gYL     (generated)
 OstopL = OC.OstopAt … mMCL                                    (ostopL_iff_at)
 FelipaAt fs ──► S ≤ (fs log x − 0.021095)x
 MNumL φ p₀ cM fs ──► m_le_L : M̃ ≤ cM·x        LamberNumL φ fs ──► t_le_L : T ≤ 3.7·10⁻⁴x
 minor_of_mnum_L : RT.MinorUpperAt c  whenever (√(1.2533143(cM + 3.7·10⁻⁴)) + √1.0532·10⁻¹¹)² ≤ c
 minorAt_ostopL_cheb : PlattFull → HelfMajFull → FelipaAt 0.6406 → OstopL →
   OC.DrujalLowP 8.57476 → MNumL φ 8.54 0.8095 0.6406 → RT.MinorUpperAt 1.0154
```

## Numerics (the coordinator's `scratchpad/minsp/mtilde_L.py`, NOT the Lean agent's)

At `x = 4.9·10²⁶`, slope `0.640209`, the corrected `M̃` is `0.7917294` at floor `8.54` and
`0.7902465` at `8.57474`; the slope `0.6406` adds about `0.0007`. So
`MNumL HW.phi 8.54 0.8095 0.6406` is TRUE with a margin of about `0.017`; it is STATED here and
proved in a later round. The closing test is
`(√(1.2533143·0.80987) + √1.0532·10⁻¹¹)² = 1.0150282 ≤ 1.0154` (`close_cheb`), and the floor is
`(√8.57476 − √8.4031·10⁻¹²)² = 8.5747430 ≥ 8.54` (`floor_854`).

## Open here

`OstopL` (layer 2: `PalanLink`, `OC.CoeurY` (unchanged: neither involves `g`), `GorshL`,
`GTMonoL`, `CoprarL`, `MinMainL`), `MNumL HW.phi 8.54 0.8095 0.6406`, `FelipaAt 0.6406 HW.etaPlus`
(F4), `OC.DrujalLowP 8.57476` (supplied in `Alt7` by `SF.drujalLowP_of_spine`), `RT.PlattFull`,
`RT.HelfMajFull`.

## Generation

Every block marked "generated" is a COUNTED substitution of its source (`OstopC.lean`; `MinSp.lL`,
`DS.LamberNumD`, `DS.t_le_d`, `LW.lamber_at`, `LD.lamberNumD_helf`) by
`scratchpad/ostopl/gen_ostopl.py`, which asserts every replacement count and asserts the stale
constants (`16/9`, `111/5`, `80/9` in the `1/q` summand, the `min` branch, `2.16e20`, `0.2727`,
`1218`, the typed slope `0.640209`) ABSENT from the generated code.
-/

namespace Principia.Common.TernaryGoldbach.OL

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction
open Principia.Erdos1054 (helfgottX)
open Principia.Common.TernaryGoldbach.MinSp

/-! ## (1) The corrected quantities -/

/-- **The corrected `L_t`** (`ternvin.tex` `eq:veror` with `minarcs.tex` `eq:kraw` redone at
`ε = 0.07`): `ϝ(t)(log 2^{7/4}t^{13/4} + 80/9) + log 2^{1.7984}t^{13.6516} + 22.7538`, the
exponents and constant ROUNDED UP from `B = 1.79837370`, `A = 13.65155938`, `C = 22.75370958`
(generated from `MinSp.lL`: `16/9 ↦ 1.7984`, `80/9 ↦ 13.6516` in the `1/q` summand only,
`111/5 ↦ 22.7538`). -/
noncomputable def lLc (t : ℝ) : ℝ :=
  MinSp.bigF t * (Real.log (2 ^ ((7 : ℝ) / 4) * t ^ ((13 : ℝ) / 4)) + 80 / 9) +
    Real.log (2 ^ (1.7984 : ℝ) * t ^ (13.6516 : ℝ)) + 22.7538

/-- **`g_Y(r)` with its `L` function a parameter** (generated from `OC.gY`, `MinSp.lL ↦ lf`): the
pins `gY_eq_at`, `gYL_eq_at` show `OC.gY` and `gYL` are its two instances. -/
noncomputable def gYAt (lf : ℝ → ℝ) (Y r : ℝ) : ℝ :=
  ((MinSp.rR Y (2 * r) * Real.log (2 * r) + 0.5) * Real.sqrt (MinSp.bigF r) + 2.5) /
      Real.sqrt (2 * r) + lf r / r + 3.2 * Y ^ (-(1 : ℝ) / 6)

/-- **`g_Y(r)` with the CORRECTED `L`** (`eq:syryza` 1951-1953): `OC.gY` with `lLc` for
`MinSp.lL` (generated; `gYL_eq_at`). -/
noncomputable def gYL (Y r : ℝ) : ℝ :=
  ((MinSp.rR Y (2 * r) * Real.log (2 * r) + 0.5) * Real.sqrt (MinSp.bigF r) + 2.5) /
      Real.sqrt (2 * r) + lLc r / r + 3.2 * Y ^ (-(1 : ℝ) / 6)

/-- **`g̃_{y,φ}(r)` on the corrected `L`**: `OC.gT` (the F7-corrected `prop:gorsh` average with
the cutoff `w₁ = max(1/K, 1000/r)` and the trivial sliver) with `gY ↦ gYL` (generated). -/
noncomputable def gTL (φ : ℝ → ℝ) (y r : ℝ) : ℝ :=
  ((∫ w in (max (1 / MinSp.kK y) (1000 / r))..1, gYL (w * y) (w * r) * φ w) +
      (∫ w in Set.Ioi (1 : ℝ), gYL (w * y) r * φ w) +
      1.04488 * ∫ w in (1 / MinSp.kK y)..(max (1 / MinSp.kK y) (1000 / r)), |φ w|) /
    MajSp.l1 φ

/-- **`∫_{r₀}^{r₁} g̃(r)/r dr`** on the corrected `L` (generated from `OC.intGT`). -/
noncomputable def intGTL (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ r in (150000 : ℝ)..MinSp.r1y y, gTL φ y r / r

/-- **`M̃` on the corrected `L`**: `OC.mMC` with `gT ↦ gTL`, `intGT ↦ intGTL`; `H̃(r₀)`, `c⁻`,
`coefC`, `S`, `J`, `E` exactly as in `OC` (generated). -/
noncomputable def mMCL (φ η b : ℝ → ℝ) (x : ℝ) : ℝ :=
  gTL φ (x / 49) 150000 * (OC.hR0C x * MinSp.sPr η x - MinSp.pJE η b x) +
    (2 / (Real.log x - 2 * 1.306476) * intGTL φ (x / 49) +
      OC.coefC x * gTL φ (x / 49) (MinSp.r1y (x / 49))) * MinSp.sPr η x

/-! ## (2) The links -/

/-- **Link [felipa] at slope `fs`**: `S = ∑_{p>√x}(log p)²η(p/x)² ≤ (fs log x − 0.021095)x` for
every `x ≥ 4.9·10²⁶`, in the shape `MinSp.felipa` gives and the composition consumes. At
`fs = 0.640209` it follows from `RT.HelfMajFull` (`felipaAt_helf`); F4 breaks that slope, so the
composition takes it as a hypothesis. OPEN at `0.6406`; weight-specific. -/
def FelipaAt (fs : ℝ) (η : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → sPr η x ≤ (fs * Real.log x - 0.021095) * x

/-- **Link [ostopL] — the corrected `thm:ostop` on the corrected `L`**: `OC.OstopC` with
`mMC ↦ mMCL` (generated; `ostopL_iff_at`). OPEN; its layer 2 is section (5) with `OC.CoeurY` and
`PalanLink` unchanged. -/
def OstopL (ηp ηs φ : ℝ → ℝ) : Prop :=
  MinSp.OstopHyp ηp ηs φ → ∀ b : ℝ → ℝ, MinSp.SupFn ηp b → ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
    MinSp.zMin ηp ηs x ≤ (Real.sqrt (MajSp.l1 φ * x / 49 * (mMCL φ ηp b x + MinSp.tT φ ηp b x)) +
      Real.sqrt (MinSp.sStar ηs x * MinSp.eBig b x)) ^ 2

/-- **Link [M̃] on the corrected `L` at slope `fs`**: `OC.MNumC` with `gT ↦ gTL`,
`intGT ↦ intGTL` and the felipa slope `0.640209 ↦ fs` (generated). On `φ = HW.phi` at
`(p₀, c, fs) = (8.54, 0.8095, 0.6406)` the supremum is about `0.7924` (module docstring). OPEN;
numerics about `eq:syryza` with `lLc`. -/
def MNumL (φ : ℝ → ℝ) (p₀ c fs : ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s p : ℝ, 0 ≤ s → s ≤ fs * Real.log x - 0.021095 →
    p₀ ≤ p →
      gTL φ (x / 49) 150000 * (OC.hR0C x * s - p) +
          (2 / (Real.log x - 2 * 1.306476) * intGTL φ (x / 49) +
            OC.coefC x * gTL φ (x / 49) (MinSp.r1y (x / 49))) * s ≤ c

/-- **Link [T] at slope `fs`** — `DS.LamberNumD` with `0.640209 ↦ fs` (generated;
`lamberNumL_iff`). PROVED on `HW.phi` at `fs = 0.6406` (`lamberNumL_helf`). -/
def LamberNumL (φ : ℝ → ℝ) (fs : ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s p : ℝ, s ≤ fs * Real.log x - 0.021095 → 8.3599 ≤ p →
    cPhi3 φ (kK (x / 49)) * (s - p) ≤ 3.7e-4

/-! ## (3a) The pins, the attachment of `FelipaAt`, the monotonicities -/

/-- **`OC.gY` IS `gYAt MinSp.lL`**, by `rfl`. -/
theorem gY_eq_at : OC.gY = gYAt MinSp.lL :=
  rfl

/-- **`gYL` IS `gYAt lLc`**, by `rfl`: with `gY_eq_at`, `gYL` and `OC.gY` differ in the `L`
function and in nothing else. -/
theorem gYL_eq_at : gYL = gYAt lLc :=
  rfl

/-- **`lLc` differs from `MinSp.lL` only in the `1/q` summand**: `log 2^{16/9}t^{80/9} + 111/5`
is replaced by `log 2^{1.7984}t^{13.6516} + 22.7538`; the `q/φ(q)` summand is untouched. -/
theorem lLc_eq (t : ℝ) :
    lLc t = MinSp.lL t - (Real.log (2 ^ ((16 : ℝ) / 9) * t ^ ((80 : ℝ) / 9)) + 111 / 5) +
      (Real.log (2 ^ (1.7984 : ℝ) * t ^ (13.6516 : ℝ)) + 22.7538) := by
  unfold lLc MinSp.lL
  ring

/-- **`OstopL` IS `OC.OstopAt … mMCL`**, by `Iff.rfl`: with `OC.ostop_iff_at` and
`OC.ostopC_iff_at`, `OstopL`, `OC.OstopC` and `MinSp.Ostop` differ in `M` and nowhere else. -/
theorem ostopL_iff_at (ηp ηs φ : ℝ → ℝ) : OstopL ηp ηs φ ↔ OC.OstopAt ηp ηs φ (mMCL φ ηp) :=
  Iff.rfl

/-- **`LamberNumL φ 0.640209` IS `DS.LamberNumD φ`**, by `Iff.rfl`: the generated copy is
faithful. -/
theorem lamberNumL_iff (φ : ℝ → ℝ) : LamberNumL φ 0.640209 ↔ DS.LamberNumD φ :=
  Iff.rfl

/-- **The existing chain supplies `FelipaAt 0.640209`**: `RT.HelfMajFull`'s `Malheur` at every
`x ≥ 10¹²`, through `MinSp.felipa`, exactly as `OC.minor_of_mnum_c` obtains its `hS`. So
`FelipaAt` attaches to what the chain already produced. -/
theorem felipaAt_helf (ηp ηc : ℝ → ℝ) (hpf : RT.PlattFull) (hm : RT.HelfMajFull ηp ηc) :
    FelipaAt 0.640209 ηp :=
  fun x hx => felipa ηp x hx ((hm hpf).2.2 x (MajSp.x12_le _ hx))

/-- **`FelipaAt` weakens as the slope grows** (`log x ≥ 1` on `x ≥ 4.9·10²⁶`). -/
theorem felipaAt_mono (fs fs' : ℝ) (hf : fs ≤ fs') (η : ℝ → ℝ) (h : FelipaAt fs η) :
    FelipaAt fs' η := by
  intro x hx
  have hL := MajSp.log_ge_one x hx
  have hx0 := x_pos x hx
  have h1 : fs * Real.log x ≤ fs' * Real.log x := mul_le_mul_of_nonneg_right hf (by linarith)
  have h2 : (fs * Real.log x - 0.021095) * x ≤ (fs' * Real.log x - 0.021095) * x :=
    mul_le_mul_of_nonneg_right (by linarith) hx0.le
  exact le_trans (h x hx) h2

/-- **`FelipaAt 0.6406 η₊` on the existing chain** (`felipaAt_helf`, `felipaAt_mono`): the
instance slope attaches. It rests on `Malheur`'s typed slope, which F4 breaks, so the headline
keeps `FelipaAt 0.6406` as a hypothesis rather than using this. -/
theorem felipaAt_6406_of_helf (hpf : RT.PlattFull)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi)) : FelipaAt 0.6406 HW.etaPlus :=
  felipaAt_mono 0.640209 0.6406 (by norm_num) HW.etaPlus (felipaAt_helf _ _ hpf hm)

/-- `MNumL` at a floor implies it at every HIGHER floor (generated from
`OC.mnumC_floor_mono`). -/
theorem mnumL_floor_mono (φ : ℝ → ℝ) (p₀ p₁ c fs : ℝ) (h01 : p₀ ≤ p₁)
    (h : MNumL φ p₀ c fs) : MNumL φ p₁ c fs :=
  fun x hx s p hs0 hs hp => h x hx s p hs0 hs (le_trans h01 hp)

/-- `MNumL` at a constant implies it at every larger constant (generated from
`OC.mnumC_const_mono`). -/
theorem mnumL_const_mono (φ : ℝ → ℝ) (p₀ c c' fs : ℝ) (hc : c ≤ c')
    (h : MNumL φ p₀ c fs) : MNumL φ p₀ c' fs :=
  fun x hx s p hs0 hs hp => le_trans (h x hx s p hs0 hs hp) hc

/-- `MNumL` at a slope implies it at every SMALLER slope (the range of `s` shrinks). -/
theorem mnumL_slope_mono (φ : ℝ → ℝ) (p₀ c fs fs' : ℝ) (hf : fs' ≤ fs) (h : MNumL φ p₀ c fs) :
    MNumL φ p₀ c fs' := by
  intro x hx s p hs0 hs hp
  have hL := MajSp.log_ge_one x hx
  have h1 : fs' * Real.log x ≤ fs * Real.log x := mul_le_mul_of_nonneg_right hf (by linarith)
  exact h x hx s p hs0 (by linarith) hp

/-! ## (3b) The `T` link at slope `0.6406`, PROVED -/

/-- **`eq:lamber` at any slope `fs`, floor `p₀` and constant `c`**, given the one cubic
inequality in `w = log(x/49) ≥ 57.558` it reduces to (generated from `LW.lamber_at`,
`0.640209 ↦ fs`). -/
theorem lamber_atL (fs p₀ c : ℝ) (hc : 0 ≤ c)
    (hkey : ∀ w L : ℝ, 57.558 ≤ w → 0 ≤ L → L ≤ 3.8955 →
      0.278 * (fs * (w + L) - 0.021095 - p₀) ≤ c * (w / 2) ^ 3) :
    ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s p : ℝ, s ≤ fs * Real.log x - 0.021095 → p₀ ≤ p →
      MinSp.cPhi3 HW.phi (MinSp.kK (x / 49)) * (s - p) ≤ c := by
  intro x hx s p hs hp
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hlogx := LW.log_ge_of x hx
  have h49 := LW.log_49_le
  have h49' : 0 ≤ Real.log 49 := Real.log_nonneg (by norm_num)
  have hK : MinSp.kK (x / 49) = (Real.log x - Real.log 49) / 2 := by
    rw [MinSp.kK, Real.log_div hx0.ne' (by norm_num : (49 : ℝ) ≠ 0)]
  have hKpos : 0 < MinSp.kK (x / 49) := by
    rw [hK]
    linarith
  have hc3 := LW.cPhi3_le _ hKpos
  have hc0 := LW.cPhi3_nonneg _ hKpos
  rcases le_or_gt (s - p) 0 with hsp | hsp
  · have h0 := mul_le_mul_of_nonneg_left hsp hc0
    rw [mul_zero] at h0
    linarith
  · have hN : s - p ≤ fs * Real.log x - 0.021095 - p₀ := by linarith
    have hw : 57.558 ≤ Real.log x - Real.log 49 := by linarith
    have hk := hkey (Real.log x - Real.log 49) (Real.log 49) hw h49' h49
    have e : Real.log x - Real.log 49 + Real.log 49 = Real.log x := by ring
    rw [e] at hk
    calc MinSp.cPhi3 HW.phi (MinSp.kK (x / 49)) * (s - p)
        ≤ 0.278 / MinSp.kK (x / 49) ^ 3 * (s - p) := mul_le_mul_of_nonneg_right hc3 hsp.le
      _ ≤ 0.278 / MinSp.kK (x / 49) ^ 3 * (fs * Real.log x - 0.021095 - p₀) :=
          mul_le_mul_of_nonneg_left hN (div_nonneg (by norm_num) (pow_pos hKpos 3).le)
      _ ≤ c := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hKpos 3), hK]
          linarith

/-- **`LamberNumL HW.phi 0.6406`** — `eq:lamber` at slope `0.6406`, `p ≥ 8.3599`, `3.7·10⁻⁴`:
PROVED (generated from `LD.lamberNumD_helf`; the cubic's worst ratio is `0.9767`). -/
theorem lamberNumL_helf : LamberNumL HW.phi 0.6406 := by
  refine lamber_atL 0.6406 8.3599 3.7e-4 (by norm_num) fun w L hw hL0 hL => ?_
  have hd := sub_nonneg.2 hw
  nlinarith [mul_nonneg hd hd, mul_nonneg (mul_nonneg hd hd) hd]

/-! ## (3c) THE COMPOSITION (generated from `OC`'s minor spine) -/

/-- **`M̃ ≤ cM·x`** from `MNumL φ p₀ cM fs`, `S ∈ [0, fs log x − 0.021095]·x` and
`(√J − √E)² ≥ p₀x` (generated from `OC.m_le_c`). -/
theorem m_le_L (φ η b : ℝ → ℝ) (p₀ cM fs x : ℝ) (hx : 49 * 10 ^ 25 ≤ x)
    (hmn : MNumL φ p₀ cM fs)
    (hS0 : 0 ≤ sPr η x) (hS : sPr η x ≤ (fs * Real.log x - 0.021095) * x)
    (hP : p₀ * x ≤ pJE η b x) : mMCL φ η b x ≤ cM * x := by
  have hx0 := x_pos x hx
  unfold mMCL
  refine m_scale _ _ _ _ _ _ _ _ x cM hx0 (hmn x hx _ _ (div_nonneg hS0 hx0.le) ?_ ?_)
  · rw [div_le_iff₀ hx0]
    exact hS
  · rw [le_div_iff₀ hx0]
    exact hP

/-- **`T ≤ 3.7·10⁻⁴ x`** from `LamberNumL φ fs` (generated from `DS.t_le_d`). -/
theorem t_le_L (φ η b : ℝ → ℝ) (fs x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hla : LamberNumL φ fs)
    (hS : sPr η x ≤ (fs * Real.log x - 0.021095) * x)
    (hP : 8.3599 * x ≤ pJE η b x) : tT φ η b x ≤ 3.7e-4 * x := by
  have hx0 := x_pos x hx
  unfold tT
  refine t_scale _ _ _ x _ hx0 (hla x hx _ _ ?_ ?_)
  · rw [div_le_iff₀ hx0]
    exact hS
  · rw [le_div_iff₀ hx0]
    exact hP

/-- **THE SPINE of (7.48) on the corrected `L`**, generic in the constant `c`, `cM`, the `J`
floor `J₀`, the `p` floor `p₀` and the felipa slope `fs`: `OC.minor_of_mnum_c` with
`OstopC ↦ OstopL`, `MNumC φ p₀ ↦ MNumL φ p₀ · fs`, `DS.LamberNumD ↦ LamberNumL φ fs`, and the
`S` bound taken from the NEW hypothesis `FelipaAt fs ηp` instead of `Malheur` (generated).
`RT.HelfMajFull` stays: its `Malpor` and `Coprar` are consumed. Application only. -/
theorem minor_of_mnum_L (c cM J₀ p₀ fs : ℝ)
    (hc : (Real.sqrt (1.2533143 * (cM + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤ c)
    (hcM : 0 ≤ cM + 3.7e-4) (hJ0 : 8.4031e-12 ≤ J₀)
    (hp : p₀ ≤ (Real.sqrt J₀ - Real.sqrt 8.4031e-12) ^ 2) (hp0 : 8.3599 ≤ p₀)
    (ηp ηs ηo ηc φ : ℝ → ℝ) (hm : RT.HelfMajFull ηp ηc)
    (hpf : RT.PlattFull) (hsc : MajSp.StarScale ηs ηc) (hrg : RW.RegW ηp ηs ηo)
    (hnm : EN.NormsB27 ηp ηs ηo) (hsn : MajSp.SupN ηp ηs) (hoh : OstopHyp ηp ηs φ)
    (hfe : FelipaAt fs ηp) (hos : OstopL ηp ηs φ) (hdl : OC.DrujalLowP J₀ ηp ηo)
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
    hlo1 hlo2 hdiff hl3 (helfgottX N) hx (MajSp.et_plus ηp mp _ hx) (MajSp.eb_plus ηp mp _ hx)
  have hP := OC.pje_le_p J₀ p₀ ηp b (helfgottX N) hx0.le hJ0 hp hA hE
  have hM := m_le_L φ ηp b p₀ cM fs (helfgottX N) hx hmn hS0 hS hP
  have hT := t_le_L φ ηp b fs (helfgottX N) hx hla hS
    (le_trans (mul_le_mul_of_nonneg_right hp0 hx0.le) hP)
  have hSt := sstar_le ηs ηc hsc cp hsn.2.2.1 hl1s (helfgottX N) hx
  have hSE := hex_le _ _ (helfgottX N) hx0.le (sStar_nonneg ηs hsn.2.2.1 _ hx0) hSt hE
  exact DS.z_close_d _ _ _ _ _ _ c cM hZ (MajSp.l1_nonneg φ) (phi_l1_le φ hpl) hx0.le
    (DS.mt_le_d _ _ cM _ hM hT) hcM hSE hc

/-- **`RT.MinorUpperAt c η₊ η*` on Helfgott's weights**, generic in `(c, cM, J₀, p₀, fs)`: every
cheap link discharged exactly as in `OC.minorAt_ostopC_helf` (`RT.starScale_helf`,
`RW.regW_helf`, `EN.normsB27_helf BS.band_sharp`, `EN.supN_helf`, `RW.ostopHyp_helf_full`,
`DS.l1_etaPlus_sharp`, `DB.dubistdie_all`, `RW.phiL1_helf`). OPEN: `RT.PlattFull`,
`RT.HelfMajFull`, `FelipaAt fs`, `OstopL`, `OC.DrujalLowP J₀`, `LamberNumL φ fs`,
`MNumL φ p₀ cM fs`. Application only. -/
theorem minorAt_ostopL_helf (c cM J₀ p₀ fs : ℝ)
    (hc : (Real.sqrt (1.2533143 * (cM + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤ c)
    (hcM : 0 ≤ cM + 3.7e-4) (hJ0 : 8.4031e-12 ≤ J₀)
    (hp : p₀ ≤ (Real.sqrt J₀ - Real.sqrt 8.4031e-12) ^ 2) (hp0 : 8.3599 ≤ p₀)
    (pf : RT.PlattFull) (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (hfe : FelipaAt fs HW.etaPlus) (hos : OstopL HW.etaPlus HW.etaStar HW.phi)
    (hdl : OC.DrujalLowP J₀ HW.etaPlus HW.etaCirc) (hla : LamberNumL HW.phi fs)
    (hmn : MNumL HW.phi p₀ cM fs) : RT.MinorUpperAt c HW.etaPlus HW.etaStar :=
  minor_of_mnum_L c cM J₀ p₀ fs hc hcM hJ0 hp hp0 HW.etaPlus HW.etaStar HW.etaCirc
    (HW.mconv HW.eta2 HW.phi) HW.phi hm pf RT.starScale_helf RW.regW_helf
    (EN.normsB27_helf BS.band_sharp) EN.supN_helf RW.ostopHyp_helf_full hfe hos hdl
    DS.l1_etaPlus_sharp (DB.dubistdie_all HW.etaPlus) RW.phiL1_helf hla hmn

/-! ## (3d) The Chebyshev instance: `c = 0.8095`, `c_target = 1.0154`, `fs = 0.6406`,
`J₀ = 8.57476`, `p₀ = 8.54` -/

/-- `8.4031·10⁻¹² ≤ 8.57476` (generated from `OC.hJ0_8587`). -/
theorem hJ0_8574 : (8.4031e-12 : ℝ) ≤ 8.57476 := by norm_num

/-- `8.3599 ≤ 8.54`: the `T` link's floor lies below (generated from `OC.hp0_8587`). -/
theorem hp0_854 : (8.3599 : ℝ) ≤ 8.54 := by norm_num

/-- **`J/x ≥ 8.57476` gives the floor `8.54`**: `(√8.57476 − √8.4031·10⁻¹²)² = 8.5747430`
(generated from `OC.floor_8587`; the `floor_8574` arithmetic of `Alt7.FromCorrected`). -/
theorem floor_854 : (8.54 : ℝ) ≤ (Real.sqrt 8.57476 - Real.sqrt 8.4031e-12) ^ 2 := by
  have ha2 : Real.sqrt 8.57476 ^ 2 = 8.57476 := Real.sq_sqrt (by norm_num)
  have hc2 : Real.sqrt 8.4031e-12 ^ 2 = 8.4031e-12 := Real.sq_sqrt (by norm_num)
  have ha0 : 0 ≤ Real.sqrt 8.57476 := Real.sqrt_nonneg _
  have hc0 : 0 ≤ Real.sqrt 8.4031e-12 := Real.sqrt_nonneg _
  have ha3 : Real.sqrt 8.57476 ≤ 3 := by nlinarith
  have hc3 : Real.sqrt 8.4031e-12 ≤ 3e-6 := by nlinarith
  have hac : Real.sqrt 8.57476 * Real.sqrt 8.4031e-12 ≤ 3 * 3e-6 :=
    mul_le_mul ha3 hc3 hc0 (by norm_num)
  nlinarith

/-- **The corrected route closes at the Chebyshev split's minor target**:
`(√(1.2533143·0.80987) + √1.0532·10⁻¹¹)² = 1.0150282 ≤ 1.0154` (exact rationals; generated from
`OC.close_mnum_c`). -/
theorem close_cheb : (Real.sqrt (1.2533143 * (0.8095 + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤
    1.0154 :=
  close_num _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `cM + 3.7·10⁻⁴ ≥ 0` at `cM = 0.8095` (generated from `OC.cM_mnum_c`). -/
theorem cM_cheb : (0 : ℝ) ≤ 0.8095 + 3.7e-4 := by norm_num

/-- **`RT.MinorUpperAt 1.0154 η₊ η*` on the CORRECTED `L`** — the minor hypothesis the
Chebyshev split (`K = 0.000205`) consumes — at `cM = 0.8095`, `fs = 0.6406`, `J₀ = 8.57476`,
`p₀ = 8.54`, with the `T` link discharged (`lamberNumL_helf`). OPEN: `RT.PlattFull`,
`RT.HelfMajFull`, `FelipaAt 0.6406`, `OstopL`, `OC.DrujalLowP 8.57476`,
`MNumL HW.phi 8.54 0.8095 0.6406`. Application only. -/
theorem minorAt_ostopL_cheb (pf : RT.PlattFull)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (hfe : FelipaAt 0.6406 HW.etaPlus) (hos : OstopL HW.etaPlus HW.etaStar HW.phi)
    (hdl : OC.DrujalLowP 8.57476 HW.etaPlus HW.etaCirc)
    (hmn : MNumL HW.phi 8.54 0.8095 0.6406) : RT.MinorUpperAt 1.0154 HW.etaPlus HW.etaStar :=
  minorAt_ostopL_helf 1.0154 0.8095 8.57476 8.54 0.6406 close_cheb cM_cheb hJ0_8574 floor_854
    hp0_854 pf hm hfe hos hdl lamberNumL_helf hmn

/-! ## (4) Every new `Prop` constrains, and the correction is not vacuous -/

/-- **`OstopL` is met by `η₊ = 0`**: a quantitative upper bound, like `OC.OstopC`
(generated from `OC.ostopC_zero`). -/
theorem ostopL_zero (ηs φ : ℝ → ℝ) : OstopL 0 ηs φ := by
  intro _ b _ x _
  have hz : zMin 0 ηs x = 0 := by simp [zMin, Smooth.smSum_zero]
  rw [hz]
  exact sq_nonneg _

/-- **`MNumL` forces `gTL(r₀) ≥ 0`** at every floor, for every slope `fs ≥ 0.021095` (so that
`s = 0` is in range): the link is not met by an arbitrary function in place of `gTL` (generated
from `OC.mnumC_nonneg`; the new binder `hfs` replaces the typed slope's `felipa(x) ≥ 0`). -/
theorem mnumL_nonneg (φ : ℝ → ℝ) (p₀ c fs : ℝ) (hfs : 0.021095 ≤ fs)
    (h : MNumL φ p₀ c fs) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 0 ≤ gTL φ (x / 49) 150000 := by
  by_contra hneg
  have hlt : gTL φ (x / 49) 150000 < 0 := not_le.mp hneg
  set g0 := gTL φ (x / 49) 150000
  have hg : g0 ≠ 0 := hlt.ne
  have hL := MajSp.log_ge_one x hx
  have hfl : fs * 1 ≤ fs * Real.log x := mul_le_mul_of_nonneg_left hL (by linarith)
  have hs0 : (0 : ℝ) ≤ fs * Real.log x - 0.021095 := by linarith
  have hq : 0 ≤ (|c| + 1) / (-g0) := div_nonneg (by positivity) (by linarith)
  have h1 := h x hx 0 (|p₀| + (|c| + 1) / (-g0)) le_rfl hs0 (by linarith [le_abs_self p₀])
  have e : g0 * (OC.hR0C x * 0 - (|p₀| + (|c| + 1) / (-g0))) +
      (2 / (Real.log x - 2 * 1.306476) * intGTL φ (x / 49) +
        OC.coefC x * gTL φ (x / 49) (r1y (x / 49))) * 0 = -(|p₀| * g0) + (|c| + 1) := by
    field_simp
    ring
  rw [e] at h1
  have h2 := le_abs_self c
  have h3 : 0 ≤ -(|p₀| * g0) := by nlinarith [abs_nonneg p₀]
  linarith

/-- `log(2^a t^b) = a log 2 + b log t` for `t > 0`. -/
theorem log_two_rpow_mul (a b t : ℝ) (ht : 0 < t) :
    Real.log (2 ^ a * t ^ b) = a * Real.log 2 + b * Real.log t := by
  rw [Real.log_mul (Real.rpow_pos_of_pos two_pos a).ne' (Real.rpow_pos_of_pos ht b).ne',
    Real.log_rpow two_pos, Real.log_rpow ht]

/-- **The correction is an INCREASE**: `MinSp.lL r < lLc r` for `r ≥ 175`
(`(1.7984 − 16/9) log 2 + (13.6516 − 80/9) log r + (22.7538 − 111/5) > 0`). -/
theorem lL_lt_lLc (r : ℝ) (hr : 175 ≤ r) : MinSp.lL r < lLc r := by
  have hr0 : 0 < r := by linarith
  have hlr : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  have hl2 := Real.log_two_gt_d9
  rw [lLc_eq, log_two_rpow_mul _ _ r hr0, log_two_rpow_mul _ _ r hr0]
  linarith

/-- **Non-vacuity: `gYL Y r > 0` on `lem:vinc`'s range `175 ≤ r ≤ Y^{1/3}/6`**, where every
logarithm in `g_Y` is genuine: `log log r > 0`, and `9Y^{1/3}/(2.004·2r) > 1` so `R_{Y,2r} ≥
0.41415`. -/
theorem gYL_pos (Y r : ℝ) (hY : 0 < Y) (hr : 175 ≤ r) (hrY : r ≤ Y ^ ((1 : ℝ) / 3) / 6) :
    0 < gYL Y r := by
  have hr0 : 0 < r := by linarith
  have hc : 0 < Y ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hY _
  have hl2 := Real.log_two_gt_d9
  have hlr1 : 1 < Real.log r := by
    rw [Real.lt_log_iff_exp_lt hr0]
    linarith [Real.exp_one_lt_d9]
  have hll : 0 < Real.log (Real.log r) := Real.log_pos hlr1
  have hF : 0 < MinSp.bigF r := by
    unfold MinSp.bigF
    have h1 := mul_pos (Real.exp_pos Real.eulerMascheroniConstant) hll
    have h2 := div_pos (by norm_num : (0 : ℝ) < 2.50637) hll
    linarith
  have hR : 0.41415 ≤ MinSp.rR Y (2 * r) := by
    unfold MinSp.rR
    have h4 : 0 < Real.log (4 * (2 * r)) := Real.log_pos (by linarith)
    have hq : 1 < 9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * r)) := by
      rw [one_lt_div (by linarith : (0 : ℝ) < 2.004 * (2 * r))]
      linarith
    have hl : 0 < Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * r))) := Real.log_pos hq
    have hfr : 0 ≤ Real.log (4 * (2 * r)) /
        (2 * Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * r)))) :=
      div_nonneg h4.le (by linarith)
    have hlg : 0 ≤ Real.log (1 + Real.log (4 * (2 * r)) /
        (2 * Real.log (9 * Y ^ ((1 : ℝ) / 3) / (2.004 * (2 * r))))) :=
      Real.log_nonneg (by linarith)
    linarith
  have hlog2r : 0 < Real.log (2 * r) := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt (2 * r) := Real.sqrt_pos.2 (by linarith)
  have hA : 0 ≤ (MinSp.rR Y (2 * r) * Real.log (2 * r) + 0.5) * Real.sqrt (MinSp.bigF r) :=
    mul_nonneg (add_nonneg (mul_nonneg (by linarith) hlog2r.le) (by norm_num))
      (Real.sqrt_nonneg _)
  have hL : 0 < lLc r := by
    unfold lLc
    rw [log_two_rpow_mul _ _ r hr0, log_two_rpow_mul _ _ r hr0]
    have hX : 0 < (7 : ℝ) / 4 * Real.log 2 + (13 : ℝ) / 4 * Real.log r + 80 / 9 := by
      linarith
    have hP := mul_pos hF hX
    linarith
  have h1 : 0 < ((MinSp.rR Y (2 * r) * Real.log (2 * r) + 0.5) * Real.sqrt (MinSp.bigF r) +
      2.5) / Real.sqrt (2 * r) := div_pos (by linarith) hs
  have h2 : 0 < lLc r / r := div_pos hL hr0
  have h3 : 0 < 3.2 * Y ^ (-(1 : ℝ) / 6) := mul_pos (by norm_num) (Real.rpow_pos_of_pos hY _)
  unfold gYL
  exact add_pos (add_pos h1 h2) h3

/-! ## (5) LAYER 2 on the corrected `L` — the obligations inside `OstopL` (stated; NOT composed)

`OC.CoeurY` and `PalanLink` involve no `g` and carry over unchanged; `OC.annA0`, `OC.dz`,
`OC.arcs_y` and `OC.minorSet_split` are reused as they are. -/

/-- **`L_{δ,q}` corrected** (minarcs `eq:tosca` 196-202, redone): the `q/φ(q)` branch
`(log δ^{7/4}q^{13/4} + 80/9)·q/φ(q)` only (the `min` with `(5/6)log x + 50/9` is DROPPED, H2),
plus `log q^{13.6516}δ^{1.7984} + 22.7538` (generated from `OC.lTosca`; `x` is no longer an
argument). -/
noncomputable def lToscaL (δ : ℝ) (q : ℕ) : ℝ :=
  (Real.log (δ ^ ((7 : ℝ) / 4) * (q : ℝ) ^ ((13 : ℝ) / 4)) + 80 / 9) /
      ((Nat.totient q : ℝ) / q) +
    Real.log ((q : ℝ) ^ (13.6516 : ℝ) * δ ^ (1.7984 : ℝ)) + 22.7538

/-- **The right side of minarcs `eq:kraw`** (189-195) with the corrected `L`, at `δ₀ = OC.dz δ`
(generated from `OC.kraw`). -/
noncomputable def krawL (x δ : ℝ) (q : ℕ) : ℝ :=
  (MinSp.rR x (OC.dz δ * q) * Real.log (OC.dz δ * q) + 0.5) /
      Real.sqrt (OC.dz δ * Nat.totient q) * x +
    2.5 * x / Real.sqrt (OC.dz δ * q) + 2 * x / (OC.dz δ * q) * lToscaL (OC.dz δ) q +
    3.2 * x ^ ((5 : ℝ) / 6)

/-- **Layer 2 [MinMainL] — the minarcs Main Theorem** (`minarcs.tex` 182-212) for `η₂` with the
corrected `L`, at EVERY scale `Y ≥ 3.4·10²³` (`GorshL` uses it at `Y = wy ≥ y/K ≥ 3.47·10²³`):
for `2α = a/q + δ/Y`, `(a,q) = 1`, `q ≤ Q = (3/4)Y^{2/3}`, `|δ/Y| ≤ 1/(qQ)`: `krawL` if
`q ≤ Y^{1/3}/6`, and the LOOSENED `1.25h`, `0.3409Y^{5/6}(log Y)^{3/2} + 1522.5Y^{2/3} log Y`,
otherwise (generated from `OC.MinMain`). OPEN; a published theorem with its `L` repaired,
weight-specific (`η₂`). -/
def MinMainL : Prop :=
  ∀ Y : ℝ, 3.4e23 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 →
    2 * α = a / q + δ / Y → (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) →
    |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) →
      ((q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 → ‖Smooth.smSum HW.eta2 Y α‖ ≤ krawL Y δ q) ∧
      (Y ^ ((1 : ℝ) / 3) / 6 < q → ‖Smooth.smSum HW.eta2 Y α‖ ≤
        0.3409 * Y ^ ((5 : ℝ) / 6) * Real.log Y ^ ((3 : ℝ) / 2) +
          1522.5 * Y ^ ((2 : ℝ) / 3) * Real.log Y)

/-- **Layer 2 [GorshL] — the corrected `prop:gorsh` on the corrected `L`**, in the form
`eq:bertru` consumes: `OC.GorshC` with `gT ↦ gTL` (generated). From `MinMainL`, `lem:merkel`,
the per-`w` Dirichlet re-approximation (H6), `GTMonoL`-type monotonicity of `gYL` on
`[175, Y^{1/3}/6]`, and `h(Y) ≤ g_Y` for the second case (H3). OPEN. -/
def GorshL (ηs φ : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, ηs t = HW.mconv HW.eta2 φ (49 * t)) → (∀ t : ℝ, 0 ≤ t → 0 ≤ φ t) →
    MeasureTheory.IntegrableOn φ (Set.Ioi 0) →
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ r : ℕ, 150000 ≤ r → (r : ℝ) ≤ MinSp.r1y (x / 49) →
    ∀ α : ℝ, α ∉ Smooth.arcs 8 r (x / 49) →
      ‖Smooth.smSum ηs x α‖ ≤
        (gTL φ (x / 49) r + MinSp.cPhi3 φ (MinSp.kK (x / 49))) * MajSp.l1 φ * (x / 49)

/-- **Layer 2 [GTMonoL] — `gTL(y, ·)` is non-increasing on `[r₀, r₁]`** (`prop:palan`'s `g`
must be non-increasing; generated from `OC.GTMono`). OPEN; numerics. -/
def GTMonoL (φ : ℝ → ℝ) : Prop :=
  ∀ y : ℝ, 10 ^ 25 ≤ y → AntitoneOn (gTL φ y) (Set.Icc 150000 (MinSp.r1y y))

/-- **Layer 2 [CoprarL] — the annulus `A₀`** on the corrected `L`: `OC.CoprarY` with
`gT ↦ gTL` (generated). OPEN. -/
def CoprarL (ηs φ : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, ηs t = HW.mconv HW.eta2 φ (49 * t)) → (∀ t : ℝ, 0 ≤ t → 0 ≤ φ t) →
    MeasureTheory.IntegrableOn φ (Set.Ioi 0) →
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ α : ℝ, α ∈ OC.annA0 x →
    ‖Smooth.smSum ηs x α‖ ≤
      (gTL φ (x / 49) 150000 + MinSp.cPhi3 φ (MinSp.kK (x / 49))) * MajSp.l1 φ * (x / 49)

end Principia.Common.TernaryGoldbach.OL
