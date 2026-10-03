/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.LamberD
import Principia.Common.TernaryGoldbach.Dubistdie

set_option autoImplicit false

/-!
# The CORRECTED `thm:ostop` (`OstopC`): the F6/F7 repair, layer 1 — statements and composition

**`OstopC` IS OPEN, AND SO ARE `MNumC` AND `DrujalLowP`. This file proves the COMPOSITION.** It
states what the REPAIRED proof of Helfgott's `thm:ostop` (`ternvin.tex` 3697–3994) establishes,
and composes it — by application and exact arithmetic only — into the exact minor-side target
`RT.MinorUpperAt 0.9924888 η₊ η*` that `Alt7.FromC0.ep1054_from_c0` names (`C₀ ≥ 1.3198`).

## Why `MinSp.Ostop` is not what the proof gives (LEAN-PROGRESS "F6 REFEREED")

* **F6 (two arc families).** `prop:palan` (3610) needs its `ℓ²` input `eq:qewer` and its `ℓ^∞`
  input `eq:rien` on ONE family `𝔐_{δ₀,r}`. The proof gets `eq:rien` (`eq:bertru`, 3822) only off
  the `y`-scale arcs, "`y` is used instead of `x`" (3761), `y = x/49`: those are the `x`-scale
  arcs at `δ₀ = 392` (`arcs_y`). It takes `eq:qewer` from `cor:coeur` at `δ₀ = 8` (3900). REPAIR:
  `cor:coeur` (3418–3439, second form) at `δ₀ = 392`, whose own constants give
  `c⁺ = log 2 + 1.36 ≤ 2.05315` (`cplus_ge`) and `c⁻ = log(1/√784) + log 2 + c_E`; the annulus
  `A₀ = 𝔐^{(y)}_{8,r₀} ∖ 𝔐^{(x)}_{8,r₀}` (`annA0`, `minorSet_split`) by majarcs Cor. `coprar`.
* **F7 (`prop:gorsh`, 2086–2193).** Its proof applies the Main Theorem at scale `wx` with the
  `δ`-parameter unscaled; at scale `wy` the argument is `≥ w·r` for `w < 1` (and `≥ r` for
  `w ≥ 1`, since `α` is off the `y`-arcs at level `r`). The corrected `ℓ^∞` function is `gT`.

## THE `c⁻` OF THE BRIEF IS NOT A LOWER BOUND — this file uses `c⁻ = −1.306476`

`c⁻ = log 2 − log 28 + c_E` with `c_E = γ + Σ_p log p/(p(p−1)) = 1.33258227573` (computed:
`scratchpad/ostopc/consts.py`, prime-zeta series) is `−1.30647505388`. The brief's `−1.306475`
EXCEEDS it by `5.4·10⁻⁸`, so `H(r) = (log(r+1) + c⁺)/(log √x + c⁻)` would be SMALLER than what
`cor:coeur` gives — not a consequence of it. `−1.306476` is below the truth by `9.5·10⁻⁷`, and
below `cor:coeur`'s own printed truncation `c_E = 1.3325822` too (`cminus_le`, kernel-checked).
The effect on `M̃` is `≈ 3·10⁻⁸`. The jump constant of `eq:gypo` (3749, derivation 3905–3916) is
`−2(log(3/8) + c⁺ − (8/15)c⁻)`; at `(2.05315, −1.306476)` it is `−3.53821589`, used rounded UP
as `−3.538215` (`jump_le`), and `jump_le_coefC` proves `coefC` dominates the exact jump
`1 − H(r₁⁻)` for every `x ≥ 4.9·10²⁶`. (`−2.14938` is the value at the printed `2.3912, 0.6294`.)

## The spine

```
 MinSp.Ostop  (Helfgott's statement: gB, c⁺ = 2.3912, c⁻ = 0.6294)      -- NOT consumed
 OstopC = MinSp.Ostop with M ↦ M̃ = mMC   (ostop_iff_at, ostopC_iff_at: ONLY M differs)
   M̃ = gT(r₀)(H̃(r₀)S − (√J−√E)²) + (2/(log x + 2c⁻)·∫_{r₀}^{r₁} gT/r + coefC·gT(r₁))·S
 DrujalLowP J₀ ─► pje_le_p : (√J − √E)² ≥ p₀x   whenever p₀ ≤ (√J₀ − √8.4031·10⁻¹²)²
 MNumC φ p₀ cM ─► m_le_c : M̃ ≤ cM·x          DS.LamberNumD (p ≥ 8.3599 ≤ p₀) ─► T ≤ 3.7·10⁻⁴x
   ▼  DS.z_close_d (eq:rozoj)
 minor_of_mnum_c : RT.MinorUpperAt c   whenever (√(1.2533143(cM + 3.7·10⁻⁴)) + √1.0532·10⁻¹¹)² ≤ c
 minorAt_mnum_c  : RT.MinorUpperAt 0.9924888  at cM = 0.791 (close_mnum_c: 0.9918418 ≤ 0.9924888)
 minorAt_ostopC_helf / _8587 : on Helfgott's weights, every cheap link discharged as in
   Alt7.FromDrujal.minorAt_drujal (LD.lamberNumD_helf supplies the T link)
```

`m_le_c`, `minor_of_mnum_c`, `close_mnum_c`, `cM_mnum_c`, `minorAt_mnum_c`, `DrujalLowP`,
`amaj_junk_p`, `mnumC_nonneg` are GENERATED from `DS` (`DrujalSpine.lean`) by counted
substitution (`scratchpad/ostopc/gen_ostopc.py`, stale constants asserted absent).
`drujalLowP_iff` pins the copy: `DrujalLowP 8.36 = DS.DrujalLowD`, by `Iff.rfl`.

## Numerics (the Lean agent's own code: `scratchpad/ostopc/mnumc.py`, `mnumc_fast.py`)

Two independent quadratures (mpmath adaptive, 20 digits; float64 Gauss–Legendre) agree to
`10⁻¹⁰`. At `x = 4.9·10²⁶`: `gT/gB = 1.030530` at `r₀`, `1.017080` at `r₁` (and `gT > gB` on all
of `[r₀, r₁]` at every `x` sampled). `sup M̃` over `x ≥ 4.9·10²⁶`, `0 ≤ s ≤ felipa`, `p ≥ p₀` is at
the threshold (146-point grid to `10³⁰⁰`, `M̃` non-increasing along it):

| floor `p₀` | `8.6129` | `8.5887` | `8.42553` | `8.3599` |
|---|---|---|---|---|
| `sup M̃` | `0.7830809` | `0.7841037` | `0.791` | `0.7937738` |

`MNumC φ p₀ 0.791` is TRUE exactly for `p₀ ≥ 8.42553` (`dM̃/dp₀ = −gT(r₀) = −0.0422644`), i.e.
`J₀ ≥ 8.4255468`, i.e. (through `DS.jArith`'s constants) `S(r₀) ≥ 6.643371` (exact
`6.6433703`). The proved `S ≥ 6.5942` gives `p₀ = 8.36262`, `M̃ = 0.79366`: it does NOT
close. The closing test is `(√(1.2533143·0.79137) + √1.0532·10⁻¹¹)² = 0.9918418 ≤ 0.9924888`
(`M ≤ 0.7915162` is the edge).

## LAYER 2 — the obligations inside `OstopC` (none is composed here)

* `MinMain` — minarcs Main Theorem (`minarcs.tex` 182–212, `eq:kraw`, `eq:tosca`) for `η₂` at
  every scale `Y ≥ 2.16·10²⁰` (it is used at every `Y = wy ≥ y/K ≥ 3.4·10²³`). STATED.
* `GorshC` — the corrected `prop:gorsh` as `eq:bertru` consumes it: off the `y`-arcs at level
  `r ∈ [r₀, r₁]`, `|S_{η*}(α,x)| ≤ (gT(r) + C_{φ,3}(K))|φ|₁y`. From `MinMain`, `lem:merkel`, a
  `lem:convet`/`lem:gosia` analogue (the `q > (wy)^{1/3}/6` case needs `h(wy) ≤ gY(wy, ·)`), and
  the three cases of 3765–3827 redone per `w`. STATED.
* `GTMono` — `gT(y,·)` non-increasing on `[r₀, r₁]` (`prop:palan` needs `g` non-increasing; the
  `lem:vinc` analogue for `gT`; true on every grid sampled). STATED — a sixth obligation the brief
  did not name.
* `CoprarY` — on `A₀`, `|S_{η*}(α,x)| ≤ (gT(r₀) + C_{φ,3}(K))|φ|₁y`, which merges `A₀` into the
  `r₀` level of `prop:palan` with `I₀` over the `x`-arcs (hence `J` over the `x`-arcs). The
  referee's Cor. `coprar` at scale `y` gives `≤ 0.045y` (the level is `0.0530y`). STATED.
* `CoeurY` — `cor:coeur` at `δ₀ = 392`, `Q₀ = r + 1`, for `S_{1,η₊}`: `eq:qewer` with
  `H(r) = (log(r+1) + 2.05315)/(log √x − 1.306476)` for `r₀ ≤ r < r₁`. Side conditions
  `(20000Q₀)² ≤ x/784`, `2Q₀ ≤ (2Q)^{0.6}` hold on `r < r₁`, `x ≥ 4.9·10²⁶`. STATED.
* `PalanLink` — `prop:palan` (3610–3690) with `lem:jardinbota` (3554–3605): generic summation by
  parts over the level sets `𝔐_{392,r+1} ∖ 𝔐_{392,r}`. LISTED, not stated: its printed hypothesis
  "`H` continuous" fails for the `H` of `thm:ostop`, which jumps to `1` at `r₁` (the jump is what
  `coefC` prices), so the consumer form should be designed with the layer-2 composition.
* Unchanged pieces of `thm:ostop`'s proof, also layer 2: the split `S_{η₊} = S_{1,η₊} + S_{2,η₊}`
  (3829–3853), the `E` bound (Rosser–Schoenfeld Thms 12–13, 3855–3888), `I₀S ≥ (√J − √E)²`
  (3942–3962), and the `C_{φ,3}` tail of `prop:gorsh` (`T`).

## Junk values

`gT` divides by `|φ|₁` (junk `0` at `φ = 0`, which `MinSp.PhiL1` rejects). Its integrals are
genuine for `φ = HW.phi` and every `y ≥ 10²⁵`, `r ≥ r₀`:
- the Main-Theorem part runs over `w ≥ w₁ ≥ 1000/r`, where `gY(wy, wr)` is continuous, since
  `wr ≥ 1000 > e`;
- `gY(wy, r)φ(w)` is bounded times a Gaussian on `[1, ∞)`;
- the trivial sliver is `∫|φ|` over a compact interval.

An earlier version integrated `gY(wy, wr)` down to `w = 1/K`, through a non-integrable pole at
`wr = e` once `y ≥ e^{110364}`. The verifier of `0be77e2b` found it, and the cutoff `w₁` removes it.
Junk would LOWER `M̃`, making `OstopC` harder and `MNumC` easier, which is why `MNumC` must be
proved on the real `gT`.
-/

namespace Principia.Common.TernaryGoldbach.OC

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction
open Principia.Erdos1054 (helfgottX)
open Principia.Common.TernaryGoldbach.MinSp

/-! ## (1) The corrected quantities -/

/-- **`g_Y(r)`, the Main Theorem's `ℓ^∞` function at scale `Y`** (`ternvin.tex` `eq:syryza`
1951–1953, with `R_{Y,t}`, `L_t` of `eq:veror` 1955–1966 and `ϝ` of `eq:koop` 1929): `MinSp.gB`
without the `K`-interpolation of `R` and with `Y^{−1/6}` for `K^{1/6}y^{−1/6}`. -/
noncomputable def gY (Y r : ℝ) : ℝ :=
  ((MinSp.rR Y (2 * r) * Real.log (2 * r) + 0.5) * Real.sqrt (MinSp.bigF r) + 2.5) /
      Real.sqrt (2 * r) + MinSp.lL r / r + 3.2 * Y ^ (-(1 : ℝ) / 6)

/-- **`g̃_{y,φ}(r)`, the `prop:gorsh`-CORRECTED `ℓ^∞` function** (F7). With `K = (log y)/2`
(`MinSp.kK`) and the cutoff `w₁ = max(1/K, 1000/r)`, it is
`|φ|₁⁻¹(∫_{w₁}^1 g_{wy}(wr)φ(w)dw + ∫_1^∞ g_{wy}(r)φ(w)dw + 1.04488·∫_{1/K}^{w₁}|φ|)`.
- The Main Theorem at scale `wy` sees `δ`-parameter `wδ`, so for `w < 1` its argument is `≥ wr`.
  Helfgott's 2086–2193 keeps `r`.
- The range `w < 1/K` is the `C_{φ,3}` term (`T`).
- The sliver `w ∈ [1/K, w₁]` is bounded TRIVIALLY (`|S_{η₂}(α,wy)| ≤ 1.04488·wy`, Cor. austeria), as
  Helfgott bounds `w < 1/K`. Without it, `gY(wy, wr)` would be integrated through its pole at
  `wr = e`, where `log log(wr) = 0`, whenever `K > r/e`, i.e. for `y ≥ e^{110364}`. The interval
  integral would then be junk `0` (verifier of `0be77e2b`).
- The sliver is EMPTY for `y < e^{300}` (`K < 150 ≤ r/1000`), so every recorded numeric is
  unchanged. Beyond that its `φ`-mass is `≤ (1000/r)³/3 ≈ 10⁻⁷`.
- `wr ≥ 1000` keeps the Main Theorem's part inside the range where `g` decreases (`lem:vinc`,
  `r ≥ 175`). -/
noncomputable def gT (φ : ℝ → ℝ) (y r : ℝ) : ℝ :=
  ((∫ w in (max (1 / MinSp.kK y) (1000 / r))..1, gY (w * y) (w * r) * φ w) +
      (∫ w in Set.Ioi (1 : ℝ), gY (w * y) r * φ w) +
      1.04488 * ∫ w in (1 / MinSp.kK y)..(max (1 / MinSp.kK y) (1000 / r)), |φ w|) /
    MajSp.l1 φ

/-- **`∫_{r₀}^{r₁} g̃(r)/r dr`**, `r₀ = 150000`, `r₁ = (3/8)y^{4/15}` (`eq:gypo`, with `gT`). -/
noncomputable def intGT (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ r in (150000 : ℝ)..MinSp.r1y y, gT φ y r / r

/-- **`H̃(r₀) = (log(r₀+1) + c⁺)/(log √x + c⁻)`** with `cor:coeur`'s constants at `δ₀ = 392`:
`c⁺ = 2.05315 ≥ log 2 + 1.36` (`cplus_ge`), `c⁻ = −1.306476 ≤ log 2 − log 28 + c_E`
(`cminus_le`). -/
noncomputable def hR0C (x : ℝ) : ℝ :=
  (Real.log 150001 + 2.05315) / (Real.log (Real.sqrt x) - 1.306476)

/-- **The corrected `g(r₁)` coefficient** `7/15 + (−3.538215 + (8/15) log κ)/(log x + 2c⁻)`,
`κ = 49`, `c⁻ = −1.306476`: the jump constant `−2(log(3/8) + c⁺ − (8/15)c⁻)` of 3905–3916
RECOMPUTED (`jump_le`). NOT `MinSp.coefC` (which carries `−2.14938`, `c⁻ = 0.6294`). -/
noncomputable def coefC (x : ℝ) : ℝ :=
  7 / 15 + (-3.538215 + 8 / 15 * Real.log 49) / (Real.log x - 2 * 1.306476)

/-- **`M̃`** — `MinSp.mM` (`eq:gypo`) with every `g ↦ gT`, `H(r₀) ↦ H̃(r₀)`, `c⁻ ↦ −1.306476`,
`coefC` recomputed; `S`, `J`, `E` exactly as in `MinSp` (`J` over the `x`-arcs `𝔐_{8,r₀}`). -/
noncomputable def mMC (φ η b : ℝ → ℝ) (x : ℝ) : ℝ :=
  gT φ (x / 49) 150000 * (hR0C x * MinSp.sPr η x - MinSp.pJE η b x) +
    (2 / (Real.log x - 2 * 1.306476) * intGT φ (x / 49) +
      coefC x * gT φ (x / 49) (MinSp.r1y (x / 49))) * MinSp.sPr η x

/-! ## (2) The links -/

/-- **`thm:ostop`'s conclusion as a function of `M`**: `MinSp.Ostop` with `mM` abstracted. Used
only to pin that `OstopC` and `MinSp.Ostop` differ in `M` and nowhere else. -/
def OstopAt (ηp ηs φ : ℝ → ℝ) (m : (ℝ → ℝ) → ℝ → ℝ) : Prop :=
  MinSp.OstopHyp ηp ηs φ → ∀ b : ℝ → ℝ, MinSp.SupFn ηp b → ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
    MinSp.zMin ηp ηs x ≤ (Real.sqrt (MajSp.l1 φ * x / 49 * (m b x + MinSp.tT φ ηp b x)) +
      Real.sqrt (MinSp.sStar ηs x * MinSp.eBig b x)) ^ 2

/-- **Link [ostopC] — the CORRECTED `thm:ostop`** (F6 + F7): `Z_{r₀}` over the SAME `x`-scale
minor arcs `(0,1] ∖ 𝔐_{8,r₀}` as `MinSp.Ostop` (and `RT.MinorUpperAt`), with the same `S`, `T`,
`J` (over the `x`-arcs), `E`, `S_{η*}(0,x)`, and `M ↦ M̃ = mMC`. OPEN; generic in `η₊, φ` under
`MinSp.OstopHyp`. It is what the repaired proof gives (layer 2 in the module docstring). -/
def OstopC (ηp ηs φ : ℝ → ℝ) : Prop :=
  MinSp.OstopHyp ηp ηs φ → ∀ b : ℝ → ℝ, MinSp.SupFn ηp b → ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
    MinSp.zMin ηp ηs x ≤ (Real.sqrt (MajSp.l1 φ * x / 49 * (mMC φ ηp b x + MinSp.tT φ ηp b x)) +
      Real.sqrt (MinSp.sStar ηs x * MinSp.eBig b x)) ^ 2

/-- **Link [M̃] — `eq:bustier` for the corrected `M`, jointly in `x`, floor `p₀`**: `DS.MNumD`'s
shape with `gB ↦ gT`, `hR0 ↦ hR0C`, `c⁻ ↦ −1.306476`, `coefC` recomputed, and `8.3599 ↦ p₀`. On
`φ = HW.phi` its supremum is at `x = 4.9·10²⁶`, `s = felipa`, `p = p₀`: TRUE at `(8.5887, 0.791)`
(`sup = 0.7841037`), FALSE below `p₀ = 8.42553`. OPEN; numerics about `eq:syryza`. -/
def MNumC (φ : ℝ → ℝ) (p₀ c : ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s p : ℝ, 0 ≤ s → s ≤ 0.640209 * Real.log x - 0.021095 →
    p₀ ≤ p →
      gT φ (x / 49) 150000 * (hR0C x * s - p) +
          (2 / (Real.log x - 2 * 1.306476) * intGT φ (x / 49) +
            coefC x * gT φ (x / 49) (MinSp.r1y (x / 49))) * s ≤ c

/-- **Link [J] at a PARAMETRIC floor `J₀`** — `DS.DrujalLowD` with its conclusion
`J/x ≥ 8.36` replaced by `J/x ≥ J₀` (generated; `drujalLowP_iff`: `J₀ = 8.36` IS
`DS.DrujalLowD`). The spine's `DS.jArith` gives `J/x ≥ 2S(r₀)·0.6397018 − 0.0740055`, so a
certified `S(r₀) ≥ 6.77091` produces `J₀ = 8.58872` (floor `8.5887`), and `MNumC · 0.791`
needs `S(r₀) ≥ 6.643371` (exact `6.6433703`). OPEN; generic (the lower half of `lem:drujal`). -/
def DrujalLowP (J₀ : ℝ) (η ηo : ℝ → ℝ) : Prop :=
  MemLp η 1 (volume.restrict (Set.Ioi 0)) → (∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955) →
    MajSp.l1 η ≤ 0.8673 →
    (∃ S : Finset ℝ, ∀ t : ℝ, 0 ≤ t → t ∉ S → ContDiffAt ℝ 3 ηo t) →
    Integrable (iteratedDeriv 3 ηo) (volume.restrict (Set.Ioi 0)) →
    MemLp ηo 2 (volume.restrict (Set.Ioi 0)) →
    0.8 ≤ MajSp.l2 ηo → MajSp.l2 ηo ≤ 0.8002 →
    MajSp.l2 (fun t => η t - ηo t) ≤ 1.7999e-4 → MajSp.l1 (iteratedDeriv 3 ηo) ≤ 40 →
    ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → MajSp.ETBound η 600000 x 1.1377e-8 →
      MajSp.EBound η x 2.3921e-8 → J₀ ≤ MajSp.amaj η x

/-! ## (3a) Discharged: the pins, the monotonicities, the constants -/

/-- **`MinSp.Ostop` IS `OstopAt … mM`**, by `Iff.rfl`: the abstraction is faithful. -/
theorem ostop_iff_at (ηp ηs φ : ℝ → ℝ) :
    MinSp.Ostop ηp ηs φ ↔ OstopAt ηp ηs φ (MinSp.mM φ ηp) :=
  Iff.rfl

/-- **`OstopC` IS `OstopAt … mMC`**, by `Iff.rfl`: with `ostop_iff_at`, `OstopC` and Helfgott's
`MinSp.Ostop` differ in `M` and in nothing else. -/
theorem ostopC_iff_at (ηp ηs φ : ℝ → ℝ) : OstopC ηp ηs φ ↔ OstopAt ηp ηs φ (mMC φ ηp) :=
  Iff.rfl

/-- **`OstopAt` weakens as `M` grows** (on `x ≥ 4.9·10²⁶`). No comparison of `mM` with `mMC` is
claimed here; this only says how one would transfer. -/
theorem ostopAt_mono (ηp ηs φ : ℝ → ℝ) (m m' : (ℝ → ℝ) → ℝ → ℝ)
    (hmm : ∀ b : ℝ → ℝ, ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → m b x ≤ m' b x)
    (h : OstopAt ηp ηs φ m) : OstopAt ηp ηs φ m' := by
  intro hoh b hb x hx
  refine le_trans (h hoh b hb x hx) ?_
  have hx0 : 0 ≤ MajSp.l1 φ * x / 49 :=
    div_nonneg (mul_nonneg (MajSp.l1_nonneg φ) (x_pos x hx).le) (by norm_num)
  have h1 : Real.sqrt (MajSp.l1 φ * x / 49 * (m b x + MinSp.tT φ ηp b x)) ≤
      Real.sqrt (MajSp.l1 φ * x / 49 * (m' b x + MinSp.tT φ ηp b x)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith [hmm b x hx]) hx0)
  have h0 : 0 ≤ Real.sqrt (MajSp.l1 φ * x / 49 * (m b x + MinSp.tT φ ηp b x)) +
      Real.sqrt (MinSp.sStar ηs x * MinSp.eBig b x) := by positivity
  exact pow_le_pow_left₀ h0 (by linarith) 2

/-- **`DrujalLowP 8.36` IS `DS.DrujalLowD`**, by `Iff.rfl`: the generated copy is faithful. -/
theorem drujalLowP_iff (η ηo : ℝ → ℝ) : DrujalLowP 8.36 η ηo ↔ DS.DrujalLowD η ηo :=
  Iff.rfl

/-- `DrujalLowP` at a floor implies it at every lower floor. -/
theorem drujalLowP_mono (J₀ J₁ : ℝ) (h10 : J₁ ≤ J₀) (η ηo : ℝ → ℝ) (h : DrujalLowP J₀ η ηo) :
    DrujalLowP J₁ η ηo :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10' x hx hT hE =>
    le_trans h10 (h h1 h2 h3 h4 h5 h6 h7 h8 h9 h10' x hx hT hE)

/-- `MNumC` at a floor implies it at every HIGHER floor (the range of `p` shrinks). -/
theorem mnumC_floor_mono (φ : ℝ → ℝ) (p₀ p₁ c : ℝ) (h01 : p₀ ≤ p₁) (h : MNumC φ p₀ c) :
    MNumC φ p₁ c :=
  fun x hx s p hs0 hs hp => h x hx s p hs0 hs (le_trans h01 hp)

/-- `MNumC` at a constant implies it at every larger constant. -/
theorem mnumC_const_mono (φ : ℝ → ℝ) (p₀ c c' : ℝ) (hc : c ≤ c') (h : MNumC φ p₀ c) :
    MNumC φ p₀ c' :=
  fun x hx s p hs0 hs hp => le_trans (h x hx s p hs0 hs hp) hc

/-- **`c⁺ = 2.05315` is `≥ log 2 + 1.36`**, `cor:coeur`'s numerator constant (`log 2Q₀ + 1.36`
with `Q₀ = r + 1`). -/
theorem cplus_ge : Real.log 2 + 1.36 ≤ 2.05315 := by
  have h := Real.log_two_lt_d9
  linarith

set_option exponentiation.threshold 3000 in
/-- **`c⁻ = −1.306476` is `≤ log(1/√784) + log 2 + c_E`** with `cor:coeur`'s printed
`c_E = 1.3325822` (`log(1/√784) = −log 28`), from `28⁵⁷¹ ≤ 2²⁷⁴⁵` and `log 2 < 0.6931471808`.
(The brief's `−1.306475` fails this, and fails it against the true `c_E` too.) -/
theorem cminus_le : (-1.306476 : ℝ) ≤ Real.log 2 - Real.log 28 + 1.3325822 := by
  have h1 : (28 : ℝ) ^ 571 ≤ 2 ^ 2745 := by norm_num
  have g1 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow, Real.log_pow] at g1
  push_cast at g1
  have hl2 := Real.log_two_lt_d9
  have hl1 := Real.log_two_gt_d9
  linarith

set_option exponentiation.threshold 2000 in
/-- **The recomputed jump constant, rounded UP**: `−2(log(3/8) + c⁺ − (8/15)c⁻) ≤ −3.538215` at
`c⁺ = 2.05315`, `c⁻ = −1.306476` (exact `−3.53821589`), from `2¹⁰⁵⁴ ≤ 3⁶⁶⁵` and
`log 2 < 0.6931471808`. -/
theorem jump_le :
    -2 * (Real.log (3 / 8) + 2.05315 - 8 / 15 * (-1.306476)) ≤ (-3.538215 : ℝ) := by
  have h1 : (2 : ℝ) ^ 1054 ≤ 3 ^ 665 := by norm_num
  have g1 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow, Real.log_pow] at g1
  push_cast at g1
  have h8 : Real.log (3 / 8) = Real.log 3 - 3 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num,
      Real.log_pow]
    push_cast
    ring
  have hl2 := Real.log_two_lt_d9
  have hl1 := Real.log_two_gt_d9
  rw [h8]
  linarith

/-- The algebra of the jump: `D − 2A ≤ (7/15)D + B` and `D > 0` give
`1 − A/(D/2) ≤ 7/15 + B/D`. -/
theorem jump_alg (A B D : ℝ) (hD : 0 < D) (h : D - 2 * A ≤ 7 / 15 * D + B) :
    1 - A / (D / 2) ≤ 7 / 15 + B / D := by
  have hD' : D ≠ 0 := hD.ne'
  have e1 : 1 - A / (D / 2) = (D - 2 * A) / D := by
    rw [sub_div, div_self hD', div_div_eq_mul_div, mul_comm A 2]
  have e2 : 7 / 15 + B / D = (7 / 15 * D + B) / D := by
    rw [add_div, mul_div_assoc, div_self hD', mul_one]
  rw [e1, e2]
  exact div_le_div_of_nonneg_right h hD.le

/-- **`coefC` dominates the exact jump of `H` at `r₁`** (3905–3916 with `cor:coeur`'s constants):
`1 − (log(r₁+1) + c⁺)/(log √x + c⁻) ≤ coefC x` for every `x ≥ 4.9·10²⁶`. -/
theorem jump_le_coefC (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    1 - (Real.log (MinSp.r1y (x / 49) + 1) + 2.05315) / (Real.log (Real.sqrt x) - 1.306476) ≤
      coefC x := by
  have hx0 : 0 < x := x_pos x hx
  have hL : 3 ≤ Real.log x := by
    have he := Real.exp_one_lt_d9
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h4 : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 3
    have h5 : (2.7182818286 : ℝ) ^ 3 ≤ 49 * 10 ^ 25 := by norm_num
    have h6 : Real.exp 3 ≤ x := by linarith
    have h7 := Real.log_le_log (Real.exp_pos 3) h6
    rwa [Real.log_exp] at h7
  have hy0 : 0 < x / 49 := div_pos hx0 (by norm_num)
  have hr1 : 0 < MinSp.r1y (x / 49) := by
    unfold MinSp.r1y
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hy0 _)
  have hlr : Real.log (MinSp.r1y (x / 49)) =
      Real.log (3 / 8) + 4 / 15 * (Real.log x - Real.log 49) := by
    unfold MinSp.r1y
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hy0 _).ne', Real.log_rpow hy0,
      Real.log_div hx0.ne' (by norm_num)]
  have hmono : Real.log (MinSp.r1y (x / 49)) ≤ Real.log (MinSp.r1y (x / 49) + 1) :=
    Real.log_le_log hr1 (by linarith)
  have hj := jump_le
  have hD : 0 < Real.log x - 2 * 1.306476 := by linarith
  have hsq : Real.log (Real.sqrt x) - 1.306476 = (Real.log x - 2 * 1.306476) / 2 := by
    rw [Real.log_sqrt hx0.le]
    ring
  rw [hsq]
  unfold coefC
  refine jump_alg _ _ _ hD ?_
  rw [hlr] at hmono
  linarith

/-- **`eq:je` at a parametric floor**: `J ≥ J₀x`, `E ≤ 8.4031·10⁻¹²x` give `(√J − √E)² ≥ p₀x`
whenever `p₀ ≤ (√J₀ − √8.4031·10⁻¹²)²` (`J₀ = 8.36` recovers `DS.je_le_d`'s `8.3599`). -/
theorem je_le_p (J₀ p₀ J E x : ℝ) (hx : 0 ≤ x) (hJ0 : 8.4031e-12 ≤ J₀)
    (hp : p₀ ≤ (Real.sqrt J₀ - Real.sqrt 8.4031e-12) ^ 2) (hJ : J₀ * x ≤ J)
    (hE : E ≤ 8.4031e-12 * x) : p₀ * x ≤ (Real.sqrt J - Real.sqrt E) ^ 2 := by
  have ha : Real.sqrt J₀ * Real.sqrt x ≤ Real.sqrt J := by
    rw [← Real.sqrt_mul' _ hx]
    exact Real.sqrt_le_sqrt hJ
  have he : Real.sqrt E ≤ Real.sqrt 8.4031e-12 * Real.sqrt x := by
    rw [← Real.sqrt_mul' _ hx]
    exact Real.sqrt_le_sqrt hE
  have hc : Real.sqrt 8.4031e-12 ≤ Real.sqrt J₀ := Real.sqrt_le_sqrt hJ0
  have hd0 : 0 ≤ (Real.sqrt J₀ - Real.sqrt 8.4031e-12) * Real.sqrt x :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg x)
  have hd : (Real.sqrt J₀ - Real.sqrt 8.4031e-12) * Real.sqrt x ≤
      Real.sqrt J - Real.sqrt E := by
    rw [sub_mul]
    linarith
  have hsq := pow_le_pow_left₀ hd0 hd 2
  have hm : p₀ * x ≤ ((Real.sqrt J₀ - Real.sqrt 8.4031e-12) * Real.sqrt x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hx]
    exact mul_le_mul_of_nonneg_right hp hx
  linarith

/-- `je_le_p` on the defined quantities: `J = x·A_{η₊}`, `A_{η₊} ≥ J₀`. -/
theorem pje_le_p (J₀ p₀ : ℝ) (η b : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x) (hJ0 : 8.4031e-12 ≤ J₀)
    (hp : p₀ ≤ (Real.sqrt J₀ - Real.sqrt 8.4031e-12) ^ 2) (hA : J₀ ≤ MajSp.amaj η x)
    (hE : eBig b x ≤ 8.4031e-12 * x) : p₀ * x ≤ pJE η b x := by
  unfold pJE
  refine je_le_p J₀ p₀ _ _ x hx hJ0 hp ?_ hE
  rw [mul_comm x]
  exact mul_le_mul_of_nonneg_right hA hx

/-! ## (3b) THE COMPOSITION (GENERATED from `DS`'s minor spine) -/

/-- **`M̃ ≤ cM·x`** from `MNumC φ p₀ cM`, `S ∈ [0, felipa]` and `(√J − √E)² ≥ p₀x`
(generated from `DS.m_le_d`). -/
theorem m_le_c (φ η b : ℝ → ℝ) (p₀ cM x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hmn : MNumC φ p₀ cM)
    (hS0 : 0 ≤ sPr η x) (hS : sPr η x ≤ (0.640209 * Real.log x - 0.021095) * x)
    (hP : p₀ * x ≤ pJE η b x) : mMC φ η b x ≤ cM * x := by
  have hx0 := x_pos x hx
  unfold mMC
  refine m_scale _ _ _ _ _ _ _ _ x cM hx0 (hmn x hx _ _ (div_nonneg hS0 hx0.le) ?_ ?_)
  · rw [div_le_iff₀ hx0]
    exact hS
  · rw [le_div_iff₀ hx0]
    exact hP

/-- **THE SPINE of (7.48) on the CORRECTED `thm:ostop`**, generic in the constant, the `J`
floor `J₀` and the `p` floor `p₀`: `DS.minor_of_mnum_d` with `Ostop ↦ OstopC`,
`DrujalLowD ↦ DrujalLowP J₀`, `MNumD ↦ MNumC φ p₀` (generated). The `T` link stays
`DS.LamberNumD` (floor `8.3599 ≤ p₀`). Application only. -/
theorem minor_of_mnum_c (c cM J₀ p₀ : ℝ)
    (hc : (Real.sqrt (1.2533143 * (cM + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤ c)
    (hcM : 0 ≤ cM + 3.7e-4) (hJ0 : 8.4031e-12 ≤ J₀)
    (hp : p₀ ≤ (Real.sqrt J₀ - Real.sqrt 8.4031e-12) ^ 2) (hp0 : 8.3599 ≤ p₀)
    (ηp ηs ηo ηc φ : ℝ → ℝ) (hm : RT.HelfMajFull ηp ηc)
    (hpf : RT.PlattFull) (hsc : MajSp.StarScale ηs ηc) (hrg : RW.RegW ηp ηs ηo)
    (hnm : EN.NormsB27 ηp ηs ηo) (hsn : MajSp.SupN ηp ηs) (hoh : OstopHyp ηp ηs φ)
    (hos : OstopC ηp ηs φ) (hdl : DrujalLowP J₀ ηp ηo) (hl1 : MajSp.l1 ηp ≤ 0.8673)
    (hdu : Dubistdie ηp) (hpl : PhiL1 φ)
    (hla : DS.LamberNumD φ) (hmn : MNumC φ p₀ cM) : RT.MinorUpperAt c ηp ηs := by
  intro N _ hN
  obtain ⟨mp, cp, mh⟩ := hm hpf
  obtain ⟨hlo1, hlo2, hdiff, hl3, -, hl1s, -, -, -⟩ := hnm
  have hx := MajSp.helfX_big N hN
  have hx0 := x_pos (helfgottX N) hx
  obtain ⟨b, hb⟩ := exists_supFn ηp hoh.2.2.2.2.1
  have hZ := hos hoh b hb (helfgottX N) hx
  have hS := felipa ηp (helfgottX N) hx (mh (helfgottX N) (MajSp.x12_le _ hx))
  have hS0 := sPr_nonneg ηp (helfgottX N)
  have hE := hdu hsn.1 hsn.2.1 b hb (helfgottX N) hx
  have hA := hdl hrg.1 hsn.1 hl1 hrg.2.2.2.2.1 hrg.2.2.2.2.2.1 hrg.2.2.2.2.2.2
    hlo1 hlo2 hdiff hl3 (helfgottX N) hx (MajSp.et_plus ηp mp _ hx) (MajSp.eb_plus ηp mp _ hx)
  have hP := pje_le_p J₀ p₀ ηp b (helfgottX N) hx0.le hJ0 hp hA hE
  have hM := m_le_c φ ηp b p₀ cM (helfgottX N) hx hmn hS0 hS hP
  have hT := DS.t_le_d φ ηp b (helfgottX N) hx hla hS
    (le_trans (mul_le_mul_of_nonneg_right hp0 hx0.le) hP)
  have hSt := sstar_le ηs ηc hsc cp hsn.2.2.1 hl1s (helfgottX N) hx
  have hSE := hex_le _ _ (helfgottX N) hx0.le (sStar_nonneg ηs hsn.2.2.1 _ hx0) hSt hE
  exact DS.z_close_d _ _ _ _ _ _ c cM hZ (MajSp.l1_nonneg φ) (phi_l1_le φ hpl) hx0.le
    (DS.mt_le_d _ _ cM _ hM hT) hcM hSE hc

/-- **The corrected route closes at `C₀ ≥ 1.3198`'s minor target**:
`(√(1.2533143·0.79137) + √1.0532·10⁻¹¹)² = 0.9918418 ≤ 0.9924888` (exact rationals;
`M ≤ 0.7915162` is the edge). -/
theorem close_mnum_c : (Real.sqrt (1.2533143 * (0.791 + 3.7e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤
    0.9924888 :=
  close_num _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `cM + 3.7·10⁻⁴ ≥ 0` at `cM = 0.791`. -/
theorem cM_mnum_c : (0 : ℝ) ≤ 0.791 + 3.7e-4 := by norm_num

/-- **`RT.MinorUpperAt 0.9924888` — `Alt7.FromC0`'s minor target — on the CORRECTED
`thm:ostop`**, `MNumC φ p₀ 0.791`, `J` floor `J₀`. Application only. -/
theorem minorAt_mnum_c (J₀ p₀ : ℝ) (hJ0 : 8.4031e-12 ≤ J₀)
    (hp : p₀ ≤ (Real.sqrt J₀ - Real.sqrt 8.4031e-12) ^ 2) (hp0 : 8.3599 ≤ p₀)
    (ηp ηs ηo ηc φ : ℝ → ℝ) (hm : RT.HelfMajFull ηp ηc)
    (hpf : RT.PlattFull) (hsc : MajSp.StarScale ηs ηc) (hrg : RW.RegW ηp ηs ηo)
    (hnm : EN.NormsB27 ηp ηs ηo) (hsn : MajSp.SupN ηp ηs) (hoh : OstopHyp ηp ηs φ)
    (hos : OstopC ηp ηs φ) (hdl : DrujalLowP J₀ ηp ηo) (hl1 : MajSp.l1 ηp ≤ 0.8673)
    (hdu : Dubistdie ηp) (hpl : PhiL1 φ)
    (hla : DS.LamberNumD φ) (hmn : MNumC φ p₀ 0.791) :
    RT.MinorUpperAt 0.9924888 ηp ηs :=
  minor_of_mnum_c 0.9924888 0.791 J₀ p₀ close_mnum_c cM_mnum_c hJ0 hp hp0 ηp ηs ηo ηc φ hm hpf
    hsc hrg hnm hsn hoh hos hdl hl1 hdu hpl hla hmn

/-! ## (3c) The instance at `p₀ = 8.5887` (`J₀ = 8.58872`, i.e. `S(r₀) ≥ 6.77091`) -/

/-- `8.4031·10⁻¹² ≤ 8.58872`. -/
theorem hJ0_8587 : (8.4031e-12 : ℝ) ≤ 8.58872 := by norm_num

/-- `8.3599 ≤ 8.5887` (the `T` link's floor lies below). -/
theorem hp0_8587 : (8.3599 : ℝ) ≤ 8.5887 := by norm_num

/-- **`J/x ≥ 8.58872` gives the floor `8.5887`**: `(√8.58872 − √8.4031·10⁻¹²)² = 8.5887030`. -/
theorem floor_8587 : (8.5887 : ℝ) ≤ (Real.sqrt 8.58872 - Real.sqrt 8.4031e-12) ^ 2 := by
  have ha2 : Real.sqrt 8.58872 ^ 2 = 8.58872 := Real.sq_sqrt (by norm_num)
  have hc2 : Real.sqrt 8.4031e-12 ^ 2 = 8.4031e-12 := Real.sq_sqrt (by norm_num)
  have ha0 : 0 ≤ Real.sqrt 8.58872 := Real.sqrt_nonneg _
  have hc0 : 0 ≤ Real.sqrt 8.4031e-12 := Real.sqrt_nonneg _
  have ha3 : Real.sqrt 8.58872 ≤ 3 := by nlinarith
  have hc3 : Real.sqrt 8.4031e-12 ≤ 3e-6 := by nlinarith
  have hac : Real.sqrt 8.58872 * Real.sqrt 8.4031e-12 ≤ 3 * 3e-6 :=
    mul_le_mul ha3 hc3 hc0 (by norm_num)
  nlinarith

/-! ## (3d) On Helfgott's weights: the EXACT minor target of `Alt7.FromC0` -/

/-- **`RT.MinorUpperAt 0.9924888 η₊ η*` from the CORRECTED `thm:ostop`**: `minorAt_mnum_c` on
Helfgott's weights, every cheap link discharged exactly as in `Alt7.FromDrujal.minorAt_drujal`
(`RW.regW_helf`, `EN.normsB27_helf BS.band_sharp`, `EN.supN_helf`, `RW.ostopHyp_helf_full`,
`DS.l1_etaPlus_sharp`, `DB.dubistdie_all`, `RW.phiL1_helf`) and the `T` link by
`LD.lamberNumD_helf`. OPEN: `RT.PlattFull`, `RT.HelfMajFull`, `OstopC`, `DrujalLowP J₀`,
`MNumC φ p₀ 0.791`. Application only. -/
theorem minorAt_ostopC_helf (J₀ p₀ : ℝ) (hJ0 : 8.4031e-12 ≤ J₀)
    (hp : p₀ ≤ (Real.sqrt J₀ - Real.sqrt 8.4031e-12) ^ 2) (hp0 : 8.3599 ≤ p₀)
    (pf : RT.PlattFull) (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (hos : OstopC HW.etaPlus HW.etaStar HW.phi) (hdl : DrujalLowP J₀ HW.etaPlus HW.etaCirc)
    (hmn : MNumC HW.phi p₀ 0.791) : RT.MinorUpperAt 0.9924888 HW.etaPlus HW.etaStar :=
  minorAt_mnum_c J₀ p₀ hJ0 hp hp0 HW.etaPlus HW.etaStar HW.etaCirc (HW.mconv HW.eta2 HW.phi)
    HW.phi hm pf RT.starScale_helf RW.regW_helf (EN.normsB27_helf BS.band_sharp) EN.supN_helf
    RW.ostopHyp_helf_full hos hdl DS.l1_etaPlus_sharp (DB.dubistdie_all HW.etaPlus)
    RW.phiL1_helf LD.lamberNumD_helf hmn

/-- **The instance at `p₀ = 8.5887`** (`J₀ = 8.58872`): `MNumC HW.phi 8.5887 0.791` has
`sup = 0.7841037` (`+0.88 %`). -/
theorem minorAt_ostopC_8587 (pf : RT.PlattFull)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (hos : OstopC HW.etaPlus HW.etaStar HW.phi)
    (hdl : DrujalLowP 8.58872 HW.etaPlus HW.etaCirc) (hmn : MNumC HW.phi 8.5887 0.791) :
    RT.MinorUpperAt 0.9924888 HW.etaPlus HW.etaStar :=
  minorAt_ostopC_helf 8.58872 8.5887 hJ0_8587 floor_8587 hp0_8587 pf hm hos hdl hmn

/-! ## (4) Every new `Prop` constrains -/

/-- **`OstopC` is met by `η₊ = 0`** (then `Z = 0` and the right side is a square): like
`MinSp.Ostop` (`MinSp.ostop_zero`), a quantitative upper bound. -/
theorem ostopC_zero (ηs φ : ℝ → ℝ) : OstopC 0 ηs φ := by
  intro _ b _ x _
  have hz : zMin 0 ηs x = 0 := by simp [zMin, Smooth.smSum_zero]
  rw [hz]
  exact sq_nonneg _

/-- `amaj` of a junk weight is `0`, so `DrujalLowP J₀`'s conclusion is FALSE for it at every
`J₀ > 0`: the link is never met by junk (generated from `DS.amaj_junk_d`). -/
theorem amaj_junk_p (J₀ : ℝ) (hJ : 0 < J₀) (η : ℝ → ℝ) (x : ℝ)
    (h : ∀ α, Smooth.smSum η x α = 0) : ¬ J₀ ≤ MajSp.amaj η x := by
  have h0 : MajSp.amaj η x = 0 := by simp [MajSp.amaj, h]
  rw [h0]
  exact not_le.mpr hJ

/-- **`MNumC` forces `gT(r₀) ≥ 0`** (a true property: `gT` averages a bound on absolute
values), at every floor `p₀`: the link is not met by an arbitrary function in place of `gT`
(generated from `DS.mnumD_nonneg`, `8.3599 ↦ |p₀|`). -/
theorem mnumC_nonneg (φ : ℝ → ℝ) (p₀ c : ℝ) (h : MNumC φ p₀ c) (x : ℝ)
    (hx : 49 * 10 ^ 25 ≤ x) : 0 ≤ gT φ (x / 49) 150000 := by
  by_contra hneg
  have hlt : gT φ (x / 49) 150000 < 0 := not_le.mp hneg
  set g0 := gT φ (x / 49) 150000
  have hg : g0 ≠ 0 := hlt.ne
  have hL := MajSp.log_ge_one x hx
  have hs0 : (0 : ℝ) ≤ 0.640209 * Real.log x - 0.021095 := by linarith
  have hq : 0 ≤ (|c| + 1) / (-g0) := div_nonneg (by positivity) (by linarith)
  have h1 := h x hx 0 (|p₀| + (|c| + 1) / (-g0)) le_rfl hs0 (by linarith [le_abs_self p₀])
  have e : g0 * (hR0C x * 0 - (|p₀| + (|c| + 1) / (-g0))) +
      (2 / (Real.log x - 2 * 1.306476) * intGT φ (x / 49) +
        coefC x * gT φ (x / 49) (r1y (x / 49))) * 0 = -(|p₀| * g0) + (|c| + 1) := by
    field_simp
    ring
  rw [e] at h1
  have h2 := le_abs_self c
  have h3 : 0 ≤ -(|p₀| * g0) := by nlinarith [abs_nonneg p₀]
  linarith

/-! ## (5) LAYER 2 — the arcs, and the obligations inside `OstopC` (stated; NOT composed here) -/

/-- **The `y`-family IS the `x`-scale family at `δ₀ = 392`**: `𝔐_{8,r}(x/49) = 𝔐_{392,r}(x)`
(`eq:majdef`, 730): "`y` is used instead of `x`" (3761) means `cor:coeur` must be taken at
`δ₀ = 8·49`. -/
theorem arcs_y (r : ℕ) (x : ℝ) : Smooth.arcs 8 r (x / 49) = Smooth.arcs 392 r x := by
  have h1 : ∀ q : ℕ, (8 : ℝ) * r / (2 * q * (x / 49)) = 392 * r / (2 * q * x) := fun q => by
    ring
  have h2 : ∀ q : ℕ, (8 : ℝ) * r / (q * (x / 49)) = 392 * r / (q * x) := fun q => by
    ring
  simp only [Smooth.arcs, h1, h2]

/-- `𝔐_{δ,r}(x)` grows with `δ` (`x > 0`). -/
theorem arcs_mono_delta (δ δ' : ℝ) (hδ : δ ≤ δ') (r : ℕ) (x : ℝ) (hx : 0 < x) :
    Smooth.arcs δ r x ⊆ Smooth.arcs δ' r x := by
  intro α hα
  simp only [Smooth.arcs, Set.mem_union, Set.mem_iUnion, Set.mem_Ioo] at hα ⊢
  rcases hα with ⟨q, hq, ho, a, ha, h1, h2⟩ | ⟨q, hq, he, a, ha, h1, h2⟩
  · have hw : δ * r / (2 * q * x) ≤ δ' * r / (2 * q * x) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg r))
        (by positivity)
    exact Or.inl ⟨q, hq, ho, a, ha, by linarith, by linarith⟩
  · have hw : δ * r / (q * x) ≤ δ' * r / (q * x) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg r))
        (by positivity)
    exact Or.inr ⟨q, hq, he, a, ha, by linarith, by linarith⟩

/-- **`𝔐^{(x)}_{8,r} ⊆ 𝔐^{(y)}_{8,r}`**: the `y`-arcs are `49` times wider. -/
theorem arcs_x_sub_y (r : ℕ) (x : ℝ) (hx : 0 < x) :
    Smooth.arcs 8 r x ⊆ Smooth.arcs 8 r (x / 49) := by
  rw [arcs_y]
  exact arcs_mono_delta 8 392 (by norm_num) r x hx

/-- **The annulus `A₀ = 𝔐^{(y)}_{8,r₀} ∖ 𝔐^{(x)}_{8,r₀}`**, `r₀ = 150000`, on `(0,1]`: minor for
`Z_{r₀}` (and `RT.MinorUpperAt`), major for the `y`-family on which `eq:bertru` holds. -/
def annA0 (x : ℝ) : Set ℝ :=
  Set.Ioc (0 : ℝ) 1 ∩ (Smooth.arcs 8 150000 (x / 49) \ Smooth.arcs 8 150000 x)

/-- **The minor arcs of `Z_{r₀}` split** into the `y`-minor arcs (`prop:palan` with
`GorshC`, `CoeurY`) and the annulus `A₀` (`CoprarY`). -/
theorem minorSet_split (x : ℝ) (hx : 0 < x) :
    Smooth.minorSet x = (Set.Ioc (0 : ℝ) 1 \ Smooth.arcs 8 150000 (x / 49)) ∪ annA0 x := by
  have hsub := arcs_x_sub_y 150000 x hx
  ext α
  simp only [Smooth.minorSet, Smooth.majArcs, annA0, Set.mem_sdiff, Set.mem_union,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h3 : α ∈ Smooth.arcs 8 150000 (x / 49)
    · exact Or.inr ⟨h1, h3, h2⟩
    · exact Or.inl ⟨h1, h3⟩
  · rintro (⟨h1, h3⟩ | ⟨h1, -, h2⟩)
    · exact ⟨h1, fun h => h3 (hsub h)⟩
    · exact ⟨h1, h2⟩

/-- **`δ₀ = max(2, |δ|/4)`** (minarcs `eq:tosca`, 196). -/
noncomputable def dz (δ : ℝ) : ℝ := max 2 (|δ| / 4)

/-- **`L_{x,δ,q}`** (minarcs `eq:tosca`, 196–202). -/
noncomputable def lTosca (x δ : ℝ) (q : ℕ) : ℝ :=
  min ((Real.log (δ ^ ((7 : ℝ) / 4) * (q : ℝ) ^ ((13 : ℝ) / 4)) + 80 / 9) /
      ((Nat.totient q : ℝ) / q)) (5 / 6 * Real.log x + 50 / 9) +
    Real.log ((q : ℝ) ^ ((80 : ℝ) / 9) * δ ^ ((16 : ℝ) / 9)) + 111 / 5

/-- **The right side of minarcs `eq:kraw`** (189–195) at `δ₀ = dz δ`. -/
noncomputable def kraw (x δ : ℝ) (q : ℕ) : ℝ :=
  (MinSp.rR x (dz δ * q) * Real.log (dz δ * q) + 0.5) / Real.sqrt (dz δ * Nat.totient q) * x +
    2.5 * x / Real.sqrt (dz δ * q) + 2 * x / (dz δ * q) * lTosca x (dz δ) q +
    3.2 * x ^ ((5 : ℝ) / 6)

/-- **Layer 2 [MinMain] — the minarcs Main Theorem** (`minarcs.tex` 182–212) for `η₂`, at EVERY
scale `Y ≥ x₀ = 2.16·10²⁰` (the corrected `prop:gorsh` uses it at every `Y = wy`, `w ≥ 1/K`):
for `2α = a/q + δ/Y`, `(a,q) = 1`, `q ≤ Q = (3/4)Y^{2/3}`, `|δ/Y| ≤ 1/(qQ)`: `eq:kraw` if
`q ≤ Y^{1/3}/6`, and `0.2727Y^{5/6}(log Y)^{3/2} + 1218Y^{2/3} log Y` otherwise. OPEN; a
published theorem, weight-specific (`η₂`). -/
def MinMain : Prop :=
  ∀ Y : ℝ, 2.16e20 ≤ Y → ∀ α δ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q → Int.gcd a q = 1 →
    2 * α = a / q + δ / Y → (q : ℝ) ≤ 3 / 4 * Y ^ ((2 : ℝ) / 3) →
    |δ / Y| ≤ 1 / (q * (3 / 4 * Y ^ ((2 : ℝ) / 3))) →
      ((q : ℝ) ≤ Y ^ ((1 : ℝ) / 3) / 6 → ‖Smooth.smSum HW.eta2 Y α‖ ≤ kraw Y δ q) ∧
      (Y ^ ((1 : ℝ) / 3) / 6 < q → ‖Smooth.smSum HW.eta2 Y α‖ ≤
        0.2727 * Y ^ ((5 : ℝ) / 6) * Real.log Y ^ ((3 : ℝ) / 2) +
          1218 * Y ^ ((2 : ℝ) / 3) * Real.log Y)

/-- **Layer 2 [GorshC] — the CORRECTED `prop:gorsh`, in the form `eq:bertru` (3822) consumes**:
for every level `r ∈ [r₀, r₁]` and every `α` off the `y`-arcs `𝔐_{8,r}(x/49)`,
`|S_{η*}(α,x)| ≤ (gT(r) + C_{φ,3}(K))·|φ|₁·y`. It is `MinMain` pushed through `η* = η₂ ∗_M φ`
(`eq:chemdames`) with the argument `≥ wr` for `w < 1` (F7), `lem:merkel`, and the three cases of
3765–3827 per `w`. For `w > 1` the scale-`y` approximation need not satisfy the Main Theorem's
`|δ/Y| ≤ 1/(q·(3/4)Y^{2/3})` at `Y = wy`. A per-`w` Dirichlet re-approximation restores it, and
since `α` is off the `y`-arcs at level `r` it still gives argument `≥ r`; the same latent gap is
in Helfgott's prop:gorsh (verifier of `0be77e2b`). Stated under `thm:ostop`'s own hypotheses on
`(η*, φ)`: `η* = (η₂ ∗_M φ)(49·)` and `φ ≥ 0` integrable. Without them it is false for an arbitrary
pair. OPEN. -/
def GorshC (ηs φ : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, ηs t = HW.mconv HW.eta2 φ (49 * t)) → (∀ t : ℝ, 0 ≤ t → 0 ≤ φ t) →
    MeasureTheory.IntegrableOn φ (Set.Ioi 0) →
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ r : ℕ, 150000 ≤ r → (r : ℝ) ≤ MinSp.r1y (x / 49) →
    ∀ α : ℝ, α ∉ Smooth.arcs 8 r (x / 49) →
      ‖Smooth.smSum ηs x α‖ ≤
        (gT φ (x / 49) r + MinSp.cPhi3 φ (MinSp.kK (x / 49))) * MajSp.l1 φ * (x / 49)

/-- **Layer 2 [GTMono] — `gT(y, ·)` is non-increasing on `[r₀, r₁]`**: `prop:palan` needs its
`g` non-increasing (`lem:jardinbota`); for `gB` this is `lem:vinc`. Not named in the brief;
true on every grid sampled (`scratchpad/ostopc/gtshape.py`). OPEN; numerics. -/
def GTMono (φ : ℝ → ℝ) : Prop :=
  ∀ y : ℝ, 10 ^ 25 ≤ y → AntitoneOn (gT φ y) (Set.Icc 150000 (MinSp.r1y y))

/-- **Layer 2 [CoprarY] — the annulus `A₀`**: there `|S_{η*}(α,x)|` is at most the `r₀` level
of `prop:palan`, `(gT(r₀) + C_{φ,3}(K))·|φ|₁·y`, so `A₀` merges into that level with `I₀` over
the `x`-arcs — which is why `J` stays over the `x`-arcs. The referee's majarcs Cor. `coprar` at
scale `y` gives `≤ 0.045y` there (the level is `0.0530y` on Helfgott's weights). Stated under
`thm:ostop`'s hypotheses on `(η*, φ)`, as `GorshC` is. OPEN. -/
def CoprarY (ηs φ : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, ηs t = HW.mconv HW.eta2 φ (49 * t)) → (∀ t : ℝ, 0 ≤ t → 0 ≤ φ t) →
    MeasureTheory.IntegrableOn φ (Set.Ioi 0) →
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ α : ℝ, α ∈ annA0 x →
    ‖Smooth.smSum ηs x α‖ ≤
      (gT φ (x / 49) 150000 + MinSp.cPhi3 φ (MinSp.kK (x / 49))) * MajSp.l1 φ * (x / 49)

open Classical in
/-- **`S_{1,η₊}(α,x) = ∑_{p > √x} (log p) e(αp) η₊(p/x)`** (thm:ostop's proof, 3829–3835): the
prime part `prop:palan` is applied to; `∑|a_n|² = MinSp.sPr`. -/
noncomputable def s1Sum (η : ℝ → ℝ) (x α : ℝ) : ℂ :=
  ∑' n : ℕ, if n.Prime ∧ Real.sqrt x < (n : ℝ) then
    ((Real.log n : ℝ) : ℂ) * ((η ((n : ℝ) / x) : ℝ) : ℂ) * e ((n : ℝ) * α) else 0

/-- **Layer 2 [CoeurY] — `cor:coeur` (3418–3439, second form) at `δ₀ = 392`, `Q₀ = r + 1`**, for
`S_{1,η₊}`: `eq:qewer` on the `y`-family with `H(r) = (log(r+1) + c⁺)/(log √x + c⁻)`,
`c⁺ = 2.05315`, `c⁻ = −1.306476`, for `r₀ ≤ r < r₁`. Its side conditions `Q₀ ≥ 10⁵`,
`(20000Q₀)² ≤ x/784`, `2Q₀ ≤ (2Q)^{0.6}` (`Q = √(x/784)`) hold there for `x ≥ 4.9·10²⁶`. OPEN;
generic large sieve (Helfgott's own). -/
def CoeurY (ηp : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ r : ℕ, 150000 ≤ r → (r : ℝ) < MinSp.r1y (x / 49) →
    ∫ α in Set.Ioc (0 : ℝ) 1 ∩ Smooth.arcs 8 (r + 1) (x / 49), ‖s1Sum ηp x α‖ ^ 2 ≤
      (Real.log ((r : ℝ) + 1) + 2.05315) / (Real.log (Real.sqrt x) - 1.306476) *
        MinSp.sPr ηp x

end Principia.Common.TernaryGoldbach.OC
