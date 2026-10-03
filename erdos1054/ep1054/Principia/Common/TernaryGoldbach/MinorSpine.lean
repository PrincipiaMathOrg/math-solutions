/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.Retarget
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false

/-!
# The spine of Helfgott's (7.48): the minor-arc upper bound as a composition of named links

**EVERY LINK BELOW IS OPEN except those marked DISCHARGED. This file proves the COMPOSITION.**
Nothing here proves Helfgott's minor-arc analysis, his large sieve, Platt's verification, or
ternary Goldbach.

The target is the retargeted link of `Retarget.lean`, `RT.MinorUpperAt 0.9845 η₊ η*`
(`∫_{𝔪} |S_{η*}||S_{η₊}|² ≤ 0.9845·x²/49`, `𝔪 = (0,1] ∖ 𝔐_{8,150000}`, `x = helfgottX N`), and, as
a check, Helfgott's own `0.97392` (`Smooth.MinorUpperSmooth`, `ternvin.tex` (7.48) = `eq:rozoj`).
The source is `ternvin.tex` (arXiv:1312.7748) `thm:ostop` (3697–3994) and §7.4's explicit version
(4867–5311), and `minarcs.tex` (arXiv:1205.5252), whose Main Theorem is the sup bound `g(r)`.

## The spine

```
 HelfMajFull (◄ PlattFull) ─┬─ Malheur ─► felipa   S ≤ .640209 x log x − .021095 x   (DISCHARGED)
                            ├─ Malpor ─► ET, E ─► DrujalLow ─► J ≥ 8.6298 x ─┐
                            └─ Coprar ─► S*(0,x) ≤ (√(π/2)/49 + 1.72e-8) x    │  (DISCHARGED)
 SupN ─► Dubistdie  E ≤ 8.4031e-12 x ──────────────── je_le: (√J − √E)² ≥ 8.6297 x
 RousselNum · ComradeNum · Byrne  ─► mnum_of_terms ─► MNum : M ≤ cM·x      (M of eq:gypo)
 LamberNum ─► T ≤ 3.5776e-4 x      hex_le: S*(0,x)·E ≤ 1.0532e-11 x²/49 (eq:hexelor)
 OstopHyp ─► Ostop (thm:ostop):  Z ≤ (√(|φ|₁ x/κ (M+T)) + √(S*(0,x) E))²       PhiL1: |φ|₁ = √(π/2)
                                  ▼  z_close (eq:rozoj)
             minor_of_mnum :  MinorUpperAt c
                 whenever (√(1.2533143(cM + 3.5776e-4)) + √1.0532e-11)² ≤ c
```

`minorAt_of_links` is the instance at `0.9845`, `minorSmooth_of_links` the check at `0.97392`,
`minorAt_of_mnum` the joint route (one numeric link `MNum φ 0.785`), `minorAt_helf` the instance on
Helfgott's own weights, and `helfgottAt_minsp` threads it through `RT.helfgottAt_of_links`.

## THE FINDING: Helfgott's minor-arc arithmetic drops a `log 2`, and his own inputs do not close

* **`eq:roussel` computes with `13.6164`** (5006) for the numerator `log(r₀+1) + c⁺` of `M`
  (`eq:gypo`), while `thm:ostop` prints `c⁺ = 2.3912` (3753, 3900, 5003):
  `log 150001 + 2.3912 = 14.3096`. The gap is `0.69320 = log 2` to four digits (`roussel_slip`
  certifies `0.69 < gap < 0.70`): the explicit computation used `c₊ = 1.698` (the `G₂` constant of
  `eq:charpas`) where `cor:coeur`'s bound for `𝔐_{δ₀,Q₀}` has `log 2Q₀` (the arcs `eq:majdef` take
  even `q ≤ 2r`). `cor:coeur` as printed (`c₊ = 1.36`) supports `c⁺ = log 2 + 1.36 = 2.0531`.
* **With the numerator restored, Helfgott's own term bounds give `M ≤ 0.81313 x`, `Z ≤ 1.01956
  x²/49`**: the composition closes at neither `0.97392` nor `0.9845` (with `cor:coeur`'s `2.0531`:
  `M ≤ 0.79536`, `Z ≤ 0.99729`, still not). `0.9845` needs `M ≤ 0.7851543`. No single input of his
  uniform assembly can be moved alone to close it with values that are true (`slack_minor.py`).
* **The conclusion survives, because his `g(r₁)` and `∫g/r` bounds are lossy.** With `g` evaluated
  EXACTLY from `eq:basia` (mpmath, 40 digits) the per-term suprema over `x ≥ 4.9·10²⁶` are
  roussel `0.3820374` (at the threshold), comrade `0.2805546` (threshold; his bound `0.30386`),
  `∫_{r₀}^{r₁}g/r ≤ 0.0836174` (at `y ≈ 10^{33.7}`; his `0.086918`); jointly in `x` the true
  `max M = 0.742233` (at the threshold), i.e. `Z ≤ 0.93071 x²/49`. So the spine's numeric links are
  stated as COUPLED numeric facts (`RousselNum`, `ComradeNum`, `Byrne`, or one `MNum`), at constants
  that are true with margin and close: `0.3850 / 0.2880 / 0.086918` at `0.9845` (margins over the
  exact suprema `+0.78% / +2.65% / +3.95%`), `0.3835 / 0.2830 / 0.0850` at `0.97392`.

## Other corrections found while transcribing (each checked against the source)

1. **`η₊ ≥ 0` fails for Helfgott's own `η₊`.** `thm:ostop` assumes `η₊ : [0,∞) → [0,∞)`, but
   `η₊ = h₂₀₀(t)·t·e^{−t²/2}` takes negative values: `h₂₀₀(2.0004) = −1.1380·10⁻⁵`,
   `η₊(2.0004) = −3.08·10⁻⁶` (mpmath; `h₂₀₀(3) < 0` too). The proof uses `η₊` only through `η₊²`
   and a non-increasing majorant `sup_{r≥t} η₊(r)`, so it goes through verbatim with `|η₊|`;
   `OstopHyp` drops the sign condition and `E` is built from `sup_{r≥t}|η₊(r)|` (`SupFn`).
2. **`T`'s `C_{φ,3}` is at `K = ½ log(x/κ)`, not `log x`.** The statement prints
   `C_{φ,3}(log x)`; the proof (`eq:bertru`, `eq:lili`) and the explicit `eq:lamber` use
   `K = (log y)/2`. `C_{φ,3}` decreases in `K`, so the printed form is the STRONGER, unproved one;
   `tT` uses the proof's.
3. **The minor arcs consume Platt, through `J` and `S`.** `minarcs.tex`'s Main Theorem uses nothing
   about `L`-functions (its §1: "uses nothing at all about other `L`-functions"; its only
   numerical tool is Platt's interval-ARITHMETIC package, not his GRH verification), and neither
   does `thm:ostop` (Rosser–Schoenfeld Thms 12–13, `cor:coeur`, `prop:gorsh`). But the explicit
   total needs `(√J − √E)² ≥ 8.6297x`, the LOWER half of `lem:drujal` (`eq:chetvyorg`), whose
   error terms are `ET_{η₊}` and `E_{η₊,r,δ₀}` from HelfMaj Thm 1.4 (all `q ≤ 300000`), and `S`
   from Prop 1.5. Without `J` (`(√J−√E)² ≥ 0` only) the roussel term alone is `≈ 0.736x`. So
   `minor_of_mnum` takes `RT.HelfMajFull` and `RT.PlattFull`.
4. **`J` enters only through its LOWER bound**, so `MajSp.Drujal` (the upper half, `A ≤ 8.7806`) is
   not what the minor arcs consume; `DrujalLow` is new. It reuses `MajSp.amaj`
   (`J = x·A_{η₊}`), `MajSp.ETBound`, `MajSp.EBound` (conductor-weighted: `MajorSpine`
   correction 1).
5. **A scale mismatch in the proof of `thm:ostop`, for adjudication.** The `ℓ^∞` input
   (`eq:bertru`) is proved for `α ∉ 𝔐_{8,r}` "with `y = x/κ` used instead of `x`" (3761), i.e. off
   arcs `κ = 49` times WIDER than the `𝔐_{8,r}(x)` of the `ℓ²` input (`cor:coeur` at
   `Q = √(x/16)`) and of `Z_{r₀}` itself; `prop:palan` needs one family. On the ring
   `𝔐_{8,r}(x/κ) ∖ 𝔐_{8,r}(x)` Prop `gorsh` gives only `g(r/κ)`. A plausible repair bounds
   `S_{η*}` there by HelfMaj Cor 1.3 (its `δ`-range `4·300000/q` at scale `x/κ` covers the ring),
   which would make the ring a Platt consumer too. `Ostop` transcribes the STATEMENT (arcs at `x`,
   as `Z_{r₀}` and (7.48) need); whether its proof covers the ring is the open question.
6. Minor: `C_{η₊,2}` is `0.51942|η₊|²_∞` in the statement and `0.51941` in 4892; either way
   `E ≤ 8.40281·10⁻¹² x < 8.4031·10⁻¹² x` (`Dubistdie` holds with the printed `0.51942`).
   `eq:roussel` computes `g(r₀) ≤ 0.041014` and then multiplies by `0.041061` (the consumed value).
   `S` is printed `∑_{p>√x}(log p)² η₊²(n/x)`: `n` is `p`.

## Links (all `def … : Prop`), and which are generic

* `OstopHyp η₊ η* φ` — `thm:ostop`'s hypotheses: `η* = (η₂ ∗_M φ)(49t)`, `φ ≥ 0` continuous `L¹`,
  `η₊` bounded, piecewise differentiable, `→ 0` (correction 1). Weight-specific facts.
  `ostopHyp_helf` reduces it on Helfgott's weights to `BandUniform` + two facts about `η₊`.
* `Ostop η₊ η* φ` — `thm:ostop` at `κ = 49`, `r₀ = 150000`, `δ₀ = 8`, `x ≥ 4.9·10²⁶`,
  `c⁺ = 2.3912`, `c⁻ = 0.6294`, `g = g_{x/κ,φ}` (`eq:basia`, defined here exactly). GENERIC in
  `η₊`, `φ` under `OstopHyp`. The only link carrying Helfgott's large sieve and `minarcs.tex`.
* `DrujalLow η₊ η∘` — the lower half of `lem:drujal` at Helfgott's numbers (`eq:celine`):
  `A_{η₊} ≥ 8.6298`. GENERIC under its hypotheses (those of `MajSp.Drujal`, `Reg`, `Norms`).
* `Dubistdie η₊` — `eq:malus` + `eq:dubistdie`: `E ≤ 8.4031·10⁻¹²x` for EVERY `η` with
  `|η| ≤ 1.079955`, `|η·t| ≤ 1.19073`. Weight-FREE real analysis (three integrals, one
  monotonicity).
* `PhiL1 φ` (`|φ|₁ = √(π/2)`), `LamberNum φ` (`eq:lamber`), `RousselNum φ c`, `ComradeNum φ c`,
  `Byrne φ c`, `MNum φ c` — numerics about explicit elementary functions of `x`; they depend on
  `φ` only through `|φ|₁` and `C_{φ,2,K}` (VNODE-LP: `≤ 0.093426`; exact `0.0934250`).
* Shared with the major spine (same weights): `RT.HelfMajFull`, `RT.PlattFull`, `MajSp.StarScale`,
  `MajSp.Reg`, `MajSp.Norms`, `MajSp.SupN`.

## Junk values (Mathlib: a non-summable `tsum` / non-integrable integral is `0`, `log 0 = 0`)

* `zMin` (`Z`): junk `0` only if `smSum` is junk, and then `MinorUpperAt` is junk-true as well
  (as in `Smoothed`: the major link carries non-degeneracy). Under summability the integrand is
  continuous, so the integral over `𝔪 ⊆ (0,1]` is genuine.
* `sPr` (`S`), `sStar` (`S*(0,x)`), `cE0`, `cE1` (`C_{η₊,0/1}`, hence `E`): junk `0` makes the
  right side of `Ostop` SMALLER (`M`, `T` increase with `S` and with `E ≤ J`), so junk makes
  `Ostop` harder, never vacuous. `felipa` does not rely on it (Prop 1.5 is two-sided, so it forces
  summability).
* `amaj` (`J/x`): junk `0` makes `DrujalLow`'s conclusion FALSE (`amaj_junk`): never vacuous.
* `intG` (`∫g/r`): `g` is continuous on `[r₀, r₁]` for `y ≥ 10²⁵`, so genuine; junk would lower
  `M` (harder).
* Sup quantities (`E`'s inner `sup_{r≥t}|η₊|`, `|η₊|_∞`) are FORALL-characterised (`SupFn`:
  `IsLUB`), never `sSup` in a statement.

## Arithmetic (exact rationals; `slack_minor.py`, `joint_minor.py`, `sups.py`)

`M ≤ cR + cC + 1.280418·cB` (`2S/(log x + 2c⁻) ≤ 1.280418x`), `T ≤ 3.5776·10⁻⁴`,
`S*·E ≤ 1.0532·10⁻¹¹/49`, `|φ|₁ ≤ 1.2533143`. Budget: `M ≤ 0.7851543` at `0.9845`, `M ≤ 0.7767128`
at `0.97392`. Links at `(0.3850, 0.2880, 0.086918)`: `M ≤ 0.7842914`, `Z ≤ 0.98342`. At
`(0.3835, 0.2830, 0.0850)`: `M ≤ 0.7753355`, `Z ≤ 0.97219`. Joint `MNum φ 0.785`: `Z ≤ 0.98431`.
-/

namespace Principia.Common.TernaryGoldbach.MinSp

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction
open Principia.Erdos1054 (helfgottX)

/-! ## (1) The quantities of `thm:ostop` and `eq:basia` -/

/-- **`ϝ(r) = e^γ log log r + 2.50637/log log r`** (`eq:koop`). -/
noncomputable def bigF (r : ℝ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * Real.log (Real.log r) +
    2.50637 / Real.log (Real.log r)

/-- **`R_{z,t} = 0.27125 log(1 + log 4t/(2 log(9z^{1/3}/(2.004t)))) + 0.41415`** (`eq:veror`). -/
noncomputable def rR (z t : ℝ) : ℝ :=
  0.27125 * Real.log (1 + Real.log (4 * t) /
    (2 * Real.log (9 * z ^ ((1 : ℝ) / 3) / (2.004 * t)))) + 0.41415

/-- **`L_t = ϝ(t)(log 2^{7/4}t^{13/4} + 80/9) + log 2^{16/9}t^{80/9} + 111/5`** (`eq:veror`). -/
noncomputable def lL (t : ℝ) : ℝ :=
  bigF t * (Real.log (2 ^ ((7 : ℝ) / 4) * t ^ ((13 : ℝ) / 4)) + 80 / 9) +
    Real.log (2 ^ ((16 : ℝ) / 9) * t ^ ((80 : ℝ) / 9)) + 111 / 5

/-- **`C_{φ,2,K} = −∫_{1/K}^1 φ(w) log w dw`** (`eq:cecidad`). -/
noncomputable def cPhi2 (φ : ℝ → ℝ) (K : ℝ) : ℝ := -∫ w in (1 / K)..1, φ w * Real.log w

/-- **`C_{φ,3}(K) = (1.04488/|φ|₁) ∫_0^{1/K} |φ(w)| dw`** (`eq:malus`). -/
noncomputable def cPhi3 (φ : ℝ → ℝ) (K : ℝ) : ℝ :=
  1.04488 / MajSp.l1 φ * ∫ w in (0 : ℝ)..(1 / K), |φ w|

/-- **`K = (log y)/2`** (`thm:ostop`: "`g(r) = g_{x/κ,φ}(r)` with `K = log(x/κ)/2`"). -/
noncomputable def kK (y : ℝ) : ℝ := Real.log y / 2

/-- **`R_{y,K,φ,t} = R_{y,t} + (R_{y/K,t} − R_{y,t})·(C_{φ,2,K}/|φ|₁)/log K`** (`eq:basia`). -/
noncomputable def rRK (φ : ℝ → ℝ) (y t : ℝ) : ℝ :=
  rR y t + (rR (y / kK y) t - rR y t) * (cPhi2 φ (kK y) / MajSp.l1 φ / Real.log (kK y))

/-- **`g_{y,φ}(r)`** (`eq:basia`, `K = (log y)/2`): the `ℓ^∞` bound on the minor arcs, from
`minarcs.tex`'s Main Theorem through `prop:gorsh`. Here `y = x/κ`. -/
noncomputable def gB (φ : ℝ → ℝ) (y r : ℝ) : ℝ :=
  ((rRK φ y (2 * r) * Real.log (2 * r) + 0.5) * Real.sqrt (bigF r) + 2.5) / Real.sqrt (2 * r) +
    lL r / r + 3.2 * kK y ^ ((1 : ℝ) / 6) * y ^ (-(1 : ℝ) / 6)

/-- **`r₁ = (3/8) y^{4/15}`**, `y = x/κ` (`thm:ostop`). -/
noncomputable def r1y (y : ℝ) : ℝ := 3 / 8 * y ^ ((4 : ℝ) / 15)

/-- **`∫_{r₀}^{r₁} g(r)/r dr`**, `r₀ = 150000` (`eq:gypo`, bounded in `eq:byrne`). -/
noncomputable def intG (φ : ℝ → ℝ) (y : ℝ) : ℝ := ∫ r in (150000 : ℝ)..r1y y, gB φ y r / r

/-- **`H(r₀) = (log(r₀+1) + c⁺)/(log √x + c⁻)`**, `c⁺ = 2.3912`, `c⁻ = 0.6294`, as `thm:ostop`
prints them (`eq:gypo`). `eq:roussel` computes with `13.6164` here (`roussel_slip`). -/
noncomputable def hR0 (x : ℝ) : ℝ :=
  (Real.log 150001 + 2.3912) / (Real.log (Real.sqrt x) + 0.6294)

/-- **The `g(r₁)` coefficient** `7/15 + (−2.14938 + (8/15) log κ)/(log x + 2c⁻)` (`eq:gypo`). -/
noncomputable def coefC (x : ℝ) : ℝ :=
  7 / 15 + (-2.14938 + 8 / 15 * Real.log 49) / (Real.log x + 2 * 0.6294)

open Classical in
/-- **`S = ∑_{p > √x} (log p)² η₊(p/x)²`** (`eq:georgic`; printed `η₊²(n/x)`). -/
noncomputable def sPr (η : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, if n.Prime ∧ Real.sqrt x < (n : ℝ) then Real.log n ^ 2 * η ((n : ℝ) / x) ^ 2 else 0

/-- **`S_{η*}(0,x) = ∑ Λ(n) η*(n/x)`** (`thm:ostop`). -/
noncomputable def sStar (η : ℝ → ℝ) (x : ℝ) : ℝ := ∑' n : ℕ, Λ n * η ((n : ℝ) / x)

/-- **`b` is the sup function `b(t) = sup_{r ≥ t} |η(r)|` on `t ≥ 0`**, FORALL-characterised
(`IsLUB`). With `|η|` for `η` (correction 1). -/
def SupFn (η b : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → IsLUB ((fun r => |η r|) '' Set.Ici t) (b t)

/-- **`C_{η₊,0} = 0.7131 ∫_0^∞ t^{−1/2} (sup_{r≥t}|η₊(r)|)² dt`** (`eq:malus`). -/
noncomputable def cE0 (b : ℝ → ℝ) : ℝ := 0.7131 * ∫ t in Set.Ioi (0 : ℝ), b t ^ 2 / Real.sqrt t

/-- **`C_{η₊,1} = 0.7131 ∫_1^∞ (log t/√t) (sup_{r≥t}|η₊(r)|)² dt`** (`eq:malus`). -/
noncomputable def cE1 (b : ℝ → ℝ) : ℝ :=
  0.7131 * ∫ t in Set.Ioi (1 : ℝ), Real.log t / Real.sqrt t * b t ^ 2

/-- **`E = ((C_{η₊,0} + C_{η₊,2}) log x + (2C_{η₊,0} + C_{η₊,1}))·√x`** (`eq:georgic`), with
`C_{η₊,2} = 0.51942 |η₊|²_∞ = 0.51942 b(0)²`. -/
noncomputable def eBig (b : ℝ → ℝ) (x : ℝ) : ℝ :=
  ((cE0 b + 0.51942 * b 0 ^ 2) * Real.log x + (2 * cE0 b + cE1 b)) * Real.sqrt x

/-- **`(√J − √E)²`**, with `J = ∫_{𝔐_{8,r₀}}|S_{η₊}|² = x·A_{η₊}` (`MajSp.amaj`). -/
noncomputable def pJE (η b : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Real.sqrt (x * MajSp.amaj η x) - Real.sqrt (eBig b x)) ^ 2

/-- **`M`** (`eq:gypo`) at `κ = 49`, `r₀ = 150000`, `c⁺ = 2.3912`, `c⁻ = 0.6294`. -/
noncomputable def mM (φ η b : ℝ → ℝ) (x : ℝ) : ℝ :=
  gB φ (x / 49) 150000 * (hR0 x * sPr η x - pJE η b x) +
    (2 / (Real.log x + 2 * 0.6294) * intG φ (x / 49) +
      coefC x * gB φ (x / 49) (r1y (x / 49))) * sPr η x

/-- **`T = C_{φ,3}(½ log(x/κ))·(S − (√J − √E)²)`** (`eq:georgic`, with the proof's `K`:
correction 2). -/
noncomputable def tT (φ η b : ℝ → ℝ) (x : ℝ) : ℝ :=
  cPhi3 φ (kK (x / 49)) * (sPr η x - pJE η b x)

/-- **`Z_{r₀} = ∫_{(ℝ/ℤ)∖𝔐_{8,r₀}} |S_{η*}(α,x)| |S_{η₊}(α,x)|² dα`**, `r₀ = 150000`: the
integral of `RT.MinorUpperAt`. -/
noncomputable def zMin (ηp ηs : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ α in Smooth.minorSet x, ‖Smooth.smSum ηs x α‖ * ‖Smooth.smSum ηp x α‖ ^ 2

/-! ## (2) The links -/

/-- **The hypotheses of `thm:ostop`** (3703–3710): `η* = (η₂ ∗_M φ)(κt)`, `κ = 49`;
`φ : [0,∞) → [0,∞)` continuous and in `L¹`; `η₊` bounded, piecewise differentiable (as
"differentiable off a finite set", a restriction) with `η₊(t) → 0`. The printed `η₊ ≥ 0` is
DROPPED (correction 1: Helfgott's own `η₊` is negative at `t = 2.0004`). OPEN; weight-specific. -/
def OstopHyp (ηp ηs φ : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, ηs t = HW.mconv HW.eta2 φ (49 * t)) ∧ ContinuousOn φ (Set.Ici 0) ∧
    (∀ t : ℝ, 0 ≤ t → 0 ≤ φ t) ∧ IntegrableOn φ (Set.Ioi 0) ∧
    BddAbove ((fun t => |ηp t|) '' Set.Ici 0) ∧
    (∃ S : Finset ℝ, ∀ t : ℝ, 0 ≤ t → t ∉ S → DifferentiableAt ℝ ηp t) ∧
    Filter.Tendsto ηp Filter.atTop (nhds 0)

/-- **Link [ostop] — `thm:ostop`** at `κ = 49`, `δ₀ = 8`, `r₀ = 150000`, `x ≥ 10²⁵κ`:
`Z_{r₀} ≤ (√(|φ|₁ x/κ (M + T)) + √(S_{η*}(0,x)·E))²`, with `S, T, J, E, M` as defined above
(`E` through the sup function `b`, FORALL-characterised). OPEN; generic in `η₊, φ`. It is
Helfgott's large sieve (`cor:coeur`) + `prop:palan` + `minarcs.tex` (via `prop:gorsh`); no
`L`-function input. See correction 5 for the arcs its proof covers. -/
def Ostop (ηp ηs φ : ℝ → ℝ) : Prop :=
  OstopHyp ηp ηs φ → ∀ b : ℝ → ℝ, SupFn ηp b → ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
    zMin ηp ηs x ≤ (Real.sqrt (MajSp.l1 φ * x / 49 * (mM φ ηp b x + tT φ ηp b x)) +
      Real.sqrt (sStar ηs x * eBig b x)) ^ 2

/-- **Link [J] — the LOWER half of `lem:drujal`** (`eq:bfpink` with `eq:chetvyorg`) at Helfgott's
numbers, `eq:celine`: `J ≥ (8.70524 − 0.00007 − 0.075272)x ≥ 8.6298x`. Hypotheses: those of the
lemma (`η ∈ L¹ ∩ L^∞`, `η∘` thrice differentiable off finitely many points, `η∘''' ∈ L¹`, the
implicit `η∘ ∈ L²`) and the numbers it consumes (`eq:lopez` both sides, `eq:sanchez`, `eq:halr`,
`eq:sazar`, and `ET`, `E` from HelfMaj Thm 1.4 — the Platt consumers). OPEN; generic. -/
def DrujalLow (η ηo : ℝ → ℝ) : Prop :=
  MemLp η 1 (volume.restrict (Set.Ioi 0)) → (∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955) →
    MajSp.l1 η ≤ 1.062319 →
    (∃ S : Finset ℝ, ∀ t : ℝ, 0 ≤ t → t ∉ S → ContDiffAt ℝ 3 ηo t) →
    Integrable (iteratedDeriv 3 ηo) (volume.restrict (Set.Ioi 0)) →
    MemLp ηo 2 (volume.restrict (Set.Ioi 0)) →
    0.8001287 ≤ MajSp.l2 ηo → MajSp.l2 ηo ≤ 0.8001288 →
    MajSp.l2 (fun t => η t - ηo t) ≤ 2.43e-6 → MajSp.l1 (iteratedDeriv 3 ηo) ≤ 32.5023 →
    ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → MajSp.ETBound η 600000 x 1.1377e-8 →
      MajSp.EBound η x 2.3921e-8 → 8.6298 ≤ MajSp.amaj η x

/-- **Link [E] — `eq:malus` and `eq:dubistdie`**: for every `η` with `|η| ≤ 1.079955` and
`|η(t)·t| ≤ 1.19073` on `t ≥ 0` (`eq:sazar`, `eq:muthit`), `E ≤ 8.4031·10⁻¹²x` at
`x ≥ 4.9·10²⁶` (`sup_{r≥t}|η(r)| ≤ min(1.079955, 1.19073/t)`, so `C₀ ≤ 2.33742`,
`C₁ ≤ 0.44936`, `C₂ ≤ 0.60580`; with that majorant `E/x = 8.40281·10⁻¹²` at the threshold).
OPEN; weight-FREE real analysis. -/
def Dubistdie (η : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955) → (∀ t : ℝ, 0 ≤ t → |η t * t| ≤ 1.19073) →
    ∀ b : ℝ → ℝ, SupFn η b → ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → eBig b x ≤ 8.4031e-12 * x

/-- **Link [φ₁] — `|φ|₁ = √(π/2)`** (`eq:rozoj`, 5311). OPEN here; for `φ = HW.phi` it is a
Gaussian moment. Weight-specific. -/
def PhiL1 (φ : ℝ → ℝ) : Prop := MajSp.l1 φ = Real.sqrt (Real.pi / 2)

/-- **Link [T] — `eq:lamber`**: `C_{φ,3}(½ log(x/κ))·(S − (√J−√E)²) ≤ 3.5776·10⁻⁴ x`, in the form
the composition consumes: at every `s = S/x ≤ felipa` and `p = (√J−√E)²/x ≥ 8.6297`. Helfgott:
`C_{φ,3}(K) ≤ 0.2779/K³` from `φ(t) ≤ t²`, which gives `3.57740·10⁻⁴` at the threshold. OPEN;
`φ`-specific numerics. -/
def LamberNum (φ : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s p : ℝ, s ≤ 0.640209 * Real.log x - 0.021095 → 8.6297 ≤ p →
    cPhi3 φ (kK (x / 49)) * (s - p) ≤ 3.5776e-4

/-- **Link [roussel] — `eq:roussel` with the `log 2` restored**: `g(r₀)·(H(r₀)·s − p) ≤ c` at
every `s ≤ felipa`, `p ≥ 8.6297` (`s = S/x`, `p = (√J−√E)²/x`), `g = g_{x/κ,φ}` EXACTLY.
Helfgott's printed `0.36155` is FALSE with `thm:ostop`'s `c⁺` (the exact supremum is
`0.3820374`, at the threshold). OPEN; numerics about `eq:basia`. -/
def RousselNum (φ : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s p : ℝ, s ≤ 0.640209 * Real.log x - 0.021095 → 8.6297 ≤ p →
    gB φ (x / 49) 150000 * (hR0 x * s - p) ≤ c

/-- **Link [comrade] — `eq:comrade`**: `(7/15 + …)·g(r₁)·s ≤ c` at every `s ≤ felipa`. Helfgott's
`0.30386` is true but lossy (his `g(r₁) ≤ 0.30782 log y √(log log y)/y^{2/15}` is `8%` over);
the exact supremum is `0.2805546`, at the threshold. OPEN; numerics about `eq:basia`. -/
def ComradeNum (φ : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s : ℝ, s ≤ 0.640209 * Real.log x - 0.021095 →
    coefC x * gB φ (x / 49) (r1y (x / 49)) * s ≤ c

/-- **Link [byrne] — `eq:byrne`**: `∫_{r₀}^{r₁} g(r)/r dr ≤ c` for `y ≥ 10²⁵`. Helfgott:
`0.086918` (`f₀ + f₁ + f₂`, bisection with interval arithmetic over `y ∈ [10²⁵, 10¹⁵⁰]`); the
exact supremum is `0.0836174` (at `y ≈ 10^{33.7}`). OPEN; the hardest numeric link. -/
def Byrne (φ : ℝ → ℝ) (c : ℝ) : Prop := ∀ y : ℝ, 10 ^ 25 ≤ y → intG φ y ≤ c

/-- **Link [M] — `eq:bustier`, jointly in `x`**: `M/x ≤ c` at every admissible `s ∈ [0, felipa]`,
`p ≥ 8.6297`. Implied by the three term links (`mnum_of_terms`); its own exact supremum is
`0.742233` (at the threshold), which is where the real slack is (`5.8%` on all three `g`-quantities
jointly at `0.9845`). OPEN; numerics about `eq:basia`. -/
def MNum (φ : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s p : ℝ, 0 ≤ s → s ≤ 0.640209 * Real.log x - 0.021095 →
    8.6297 ≤ p →
      gB φ (x / 49) 150000 * (hR0 x * s - p) +
          (2 / (Real.log x + 2 * 0.6294) * intG φ (x / 49) +
            coefC x * gB φ (x / 49) (r1y (x / 49))) * s ≤ c

/-! ## (3a) The discharged pieces -/

/-- The sup function exists for every bounded `|η|` (`sSup` of a bounded nonempty set). -/
theorem exists_supFn (η : ℝ → ℝ) (hb : BddAbove ((fun t => |η t|) '' Set.Ici 0)) :
    ∃ b : ℝ → ℝ, SupFn η b := by
  refine ⟨fun t => sSup ((fun r => |η r|) '' Set.Ici t), fun t ht => ?_⟩
  exact isLUB_csSup ⟨|η t|, t, Set.self_mem_Ici, rfl⟩
    (hb.mono (Set.image_mono (Set.Ici_subset_Ici.mpr ht)))

/-- `S ≥ 0`. -/
theorem sPr_nonneg (η : ℝ → ℝ) (x : ℝ) : 0 ≤ sPr η x := by
  unfold sPr
  refine tsum_nonneg fun n => ?_
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · exact le_refl 0

open Classical in
/-- **`eq:felipa`, DISCHARGED from HelfMaj Prop 1.5**: `S ≤ ∑Λ(n) log n η₊²(n/x) ≤
0.640209 x log x − 0.021095 x` for `x ≥ 4.9·10²⁶`. Prop 1.5 is two-sided, so it forces the
summability junk would hide. -/
theorem felipa (η : ℝ → ℝ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hm : MajSp.MalheurAt η x) :
    sPr η x ≤ (0.640209 * Real.log x - 0.021095) * x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hL := MajSp.log_ge_one x hx
  have hu : 310.84 / Real.sqrt x ≤ 310.84 / (22135943 * 10 ^ 6) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (MajSp.sqrt_x_ge x hx)
  have hP : x ≤ x * Real.log x := by nlinarith
  have hPu : 310.84 / Real.sqrt x * (x * Real.log x) ≤
      310.84 / (22135943 * 10 ^ 6) * (x * Real.log x) :=
    mul_le_mul_of_nonneg_right hu (by linarith)
  unfold MajSp.MalheurAt at hm
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

/-- `S_{η*}(0,x) ≥ 0` for `η* ≥ 0`. -/
theorem sStar_nonneg (ηs : ℝ → ℝ) (h0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ ηs t ∧ ηs t ≤ 1.414) (x : ℝ)
    (hx : 0 < x) : 0 ≤ sStar ηs x :=
  tsum_nonneg fun n =>
    mul_nonneg vonMangoldt_nonneg (h0 _ (div_nonneg (Nat.cast_nonneg n) hx.le)).1

/-- **`S_{η*}(0,x) = (|η*|₁ + O*(ET_{η*,0}))x`, DISCHARGED** (`eq:fabienne`, `eq:marldoro`):
`S_{η*}(0,x) ≤ (√(π/2)/49 + 1.71973·10⁻⁸)x` from Cor 1.3 at `q = 1` (`MajSp.et0_star`), `η* ≥ 0`
and `|η*|₁ = √(π/2)/49`. -/
theorem sstar_le (ηs ηc : ℝ → ℝ) (sc : MajSp.StarScale ηs ηc) (cp : MajSp.Coprar ηc)
    (h0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ ηs t ∧ ηs t ≤ 1.414)
    (hl1 : MajSp.l1 ηs = Real.sqrt (Real.pi / 2) / 49) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    sStar ηs x ≤ (1.2533143 / 49 + 1.71973e-8) * x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hT := MajSp.et0_star ηs ηc sc cp x hx
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

/-- **`eq:je`**: `J ≥ 8.6298x` and `E ≤ 8.4031·10⁻¹²x` give `(√J − √E)² ≥ 8.6297x`. -/
theorem je_le (J E x : ℝ) (hx : 0 ≤ x) (hJ : 8.6298 * x ≤ J) (hE : E ≤ 8.4031e-12 * x) :
    8.6297 * x ≤ (Real.sqrt J - Real.sqrt E) ^ 2 := by
  have ha := Real.sqrt_le_sqrt hJ
  have he := Real.sqrt_le_sqrt hE
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8.6298)] at ha
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8.4031e-12)] at he
  have hu0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hux : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have ha2 : Real.sqrt 8.6298 ^ 2 = 8.6298 := Real.sq_sqrt (by norm_num)
  have hc2 : Real.sqrt 8.4031e-12 ^ 2 = 8.4031e-12 := Real.sq_sqrt (by norm_num)
  have ha0 : 0 ≤ Real.sqrt 8.6298 := Real.sqrt_nonneg _
  have hc0 : 0 ≤ Real.sqrt 8.4031e-12 := Real.sqrt_nonneg _
  have ha3 : Real.sqrt 8.6298 ≤ 3 := by nlinarith
  have ha1 : 2 ≤ Real.sqrt 8.6298 := by nlinarith
  have hc3 : Real.sqrt 8.4031e-12 ≤ 3e-6 := by nlinarith
  have hd : (Real.sqrt 8.6298 - Real.sqrt 8.4031e-12) * Real.sqrt x ≤
      Real.sqrt J - Real.sqrt E := by nlinarith
  have hd0 : 0 ≤ (Real.sqrt 8.6298 - Real.sqrt 8.4031e-12) * Real.sqrt x :=
    mul_nonneg (by linarith) hu0
  have hsq := pow_le_pow_left₀ hd0 hd 2
  have hk : 8.6297 ≤ (Real.sqrt 8.6298 - Real.sqrt 8.4031e-12) ^ 2 := by nlinarith
  have hm : 8.6297 * x ≤ ((Real.sqrt 8.6298 - Real.sqrt 8.4031e-12) * Real.sqrt x) ^ 2 := by
    rw [mul_pow, hux]
    exact mul_le_mul_of_nonneg_right hk hx
  linarith

/-- `je_le` on the defined quantities: `J = x·A_{η₊}`, `A_{η₊} ≥ 8.6298`. -/
theorem pje_le (η b : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x) (hA : 8.6298 ≤ MajSp.amaj η x)
    (hE : eBig b x ≤ 8.4031e-12 * x) : 8.6297 * x ≤ pJE η b x := by
  unfold pJE
  refine je_le _ _ x hx ?_ hE
  rw [mul_comm x]
  exact mul_le_mul_of_nonneg_right hA hx

/-- **`eq:hexelor`**: `S_{η*}(0,x)·E ≤ (1.2533143/49 + 1.71973·10⁻⁸)·8.4031·10⁻¹²·x² ≤
1.0532·10⁻¹¹·x²/49` (the product is `1.05317·10⁻¹¹`). -/
theorem hex_le (S E x : ℝ) (hx : 0 ≤ x) (hS0 : 0 ≤ S)
    (hS : S ≤ (1.2533143 / 49 + 1.71973e-8) * x) (hE : E ≤ 8.4031e-12 * x) :
    S * E ≤ 1.0532e-11 * x ^ 2 / 49 := by
  have h1 : S * E ≤ S * (8.4031e-12 * x) := mul_le_mul_of_nonneg_left hE hS0
  have h2 : S * (8.4031e-12 * x) ≤ (1.2533143 / 49 + 1.71973e-8) * x * (8.4031e-12 * x) :=
    mul_le_mul_of_nonneg_right hS (by positivity)
  have h3 : (1.2533143 / 49 + 1.71973e-8) * x * (8.4031e-12 * x) ≤ 1.0532e-11 * x ^ 2 / 49 := by
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith
  linarith

/-- `x ≥ 4.9·10²⁶ ⇒ x > 0`. -/
theorem x_pos (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 0 < x := lt_of_lt_of_le (by norm_num) hx

/-- `x/κ ≥ 10²⁵`. -/
theorem y_ge (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 10 ^ 25 ≤ x / 49 := by
  rw [le_div_iff₀ (by norm_num)]
  linarith

/-- `|φ|₁ ≤ 1.2533143` from `PhiL1`. -/
theorem phi_l1_le (φ : ℝ → ℝ) (hpl : PhiL1 φ) : MajSp.l1 φ ≤ 1.2533143 := by
  have h : MajSp.l1 φ = Real.sqrt (Real.pi / 2) := hpl
  rw [h]
  exact MajSp.sqrt_pi_half.2

/-! ## (3b) The arithmetic of `eq:gypo`, `eq:lamber`, `eq:rozoj` -/

/-- Scaling `M`: a bound on `M/x` at `s = S/x`, `p = P/x` is a bound on `M`. -/
theorem m_scale (g0 H0 c1 Ig cf g1 S P x c : ℝ) (hx : 0 < x)
    (h : g0 * (H0 * (S / x) - P / x) + (c1 * Ig + cf * g1) * (S / x) ≤ c) :
    g0 * (H0 * S - P) + (c1 * Ig + cf * g1) * S ≤ c * x := by
  have hx' : x ≠ 0 := hx.ne'
  have e : g0 * (H0 * S - P) + (c1 * Ig + cf * g1) * S =
      x * (g0 * (H0 * (S / x) - P / x) + (c1 * Ig + cf * g1) * (S / x)) := by
    field_simp
  rw [e, mul_comm c x]
  exact mul_le_mul_of_nonneg_left h hx.le

/-- Scaling `T`. -/
theorem t_scale (C S P x c : ℝ) (hx : 0 < x) (h : C * (S / x - P / x) ≤ c) :
    C * (S - P) ≤ c * x := by
  have hx' : x ≠ 0 := hx.ne'
  have e : C * (S - P) = x * (C * (S / x - P / x)) := by
    field_simp
  rw [e, mul_comm c x]
  exact mul_le_mul_of_nonneg_left h hx.le

/-- **`M ≤ cM·x`** from `MNum`, `S ∈ [0, felipa]` and `(√J − √E)² ≥ 8.6297x`. -/
theorem m_le (φ η b : ℝ → ℝ) (cM x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hmn : MNum φ cM)
    (hS0 : 0 ≤ sPr η x) (hS : sPr η x ≤ (0.640209 * Real.log x - 0.021095) * x)
    (hP : 8.6297 * x ≤ pJE η b x) : mM φ η b x ≤ cM * x := by
  have hx0 := x_pos x hx
  unfold mM
  refine m_scale _ _ _ _ _ _ _ _ x cM hx0 (hmn x hx _ _ (div_nonneg hS0 hx0.le) ?_ ?_)
  · rw [div_le_iff₀ hx0]
    exact hS
  · rw [le_div_iff₀ hx0]
    exact hP

/-- **`T ≤ 3.5776·10⁻⁴ x`** from `LamberNum`. -/
theorem t_le (φ η b : ℝ → ℝ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hla : LamberNum φ)
    (hS : sPr η x ≤ (0.640209 * Real.log x - 0.021095) * x)
    (hP : 8.6297 * x ≤ pJE η b x) : tT φ η b x ≤ 3.5776e-4 * x := by
  have hx0 := x_pos x hx
  unfold tT
  refine t_scale _ _ _ x _ hx0 (hla x hx _ _ ?_ ?_)
  · rw [div_le_iff₀ hx0]
    exact hS
  · rw [le_div_iff₀ hx0]
    exact hP

/-- **`eq:casbah`, the uniform factor**: `2s/(log x + 2c⁻) ≤ 1.280418` for `s ≤ felipa`. -/
theorem cas_le (x s : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hs : s ≤ 0.640209 * Real.log x - 0.021095) :
    2 / (Real.log x + 2 * 0.6294) * s ≤ 1.280418 := by
  have hL := MajSp.log_ge_one x hx
  have hden : 0 < Real.log x + 2 * 0.6294 := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  linarith

/-- `log x + 2c⁻ > 0`. -/
theorem den_pos (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 0 < Real.log x + 2 * 0.6294 := by
  have hL := MajSp.log_ge_one x hx
  linarith

/-- **`eq:bustier` from the three terms**: `RousselNum cR`, `ComradeNum cC`, `Byrne cB` give
`MNum (cR + cC + 1.280418·cB)`. -/
theorem mnum_of_terms (φ : ℝ → ℝ) (cR cC cB : ℝ) (hR : RousselNum φ cR) (hC : ComradeNum φ cC)
    (hB : Byrne φ cB) (hcB : 0 ≤ cB) : MNum φ (cR + cC + 1.280418 * cB) := by
  intro x hx s p hs0 hs hp
  have h1 := hR x hx s p hs hp
  have h2 := hC x hx s hs
  have h3 := hB (x / 49) (y_ge x hx)
  have hq0 : 0 ≤ 2 / (Real.log x + 2 * 0.6294) * s :=
    mul_nonneg (div_nonneg (by norm_num) (den_pos x hx).le) hs0
  have hq1 := cas_le x s hx hs
  have h4 : 2 / (Real.log x + 2 * 0.6294) * intG φ (x / 49) * s ≤ 1.280418 * cB := by
    calc 2 / (Real.log x + 2 * 0.6294) * intG φ (x / 49) * s
        = (2 / (Real.log x + 2 * 0.6294) * s) * intG φ (x / 49) := by ring
      _ ≤ (2 / (Real.log x + 2 * 0.6294) * s) * cB := mul_le_mul_of_nonneg_left h3 hq0
      _ ≤ 1.280418 * cB := mul_le_mul_of_nonneg_right hq1 hcB
  have e : (2 / (Real.log x + 2 * 0.6294) * intG φ (x / 49) +
      coefC x * gB φ (x / 49) (r1y (x / 49))) * s =
      2 / (Real.log x + 2 * 0.6294) * intG φ (x / 49) * s +
        coefC x * gB φ (x / 49) (r1y (x / 49)) * s := by ring
  rw [e]
  linarith

/-- **The closing test, exact**: `(√A + √h)² ≤ c` iff (for `c − A − h ≥ 0`)
`4Ah ≤ (c − A − h)²`. -/
theorem close_num (A h c : ℝ) (hA : 0 ≤ A) (hh : 0 ≤ h) (hd : 0 ≤ c - A - h)
    (hq : 4 * (A * h) ≤ (c - A - h) ^ 2) : (Real.sqrt A + Real.sqrt h) ^ 2 ≤ c := by
  have e : (Real.sqrt A + Real.sqrt h) ^ 2 = A + h + 2 * Real.sqrt (A * h) := by
    rw [Real.sqrt_mul hA, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hh]
    ring
  have hs : Real.sqrt (A * h) ≤ (c - A - h) / 2 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  rw [e]
  linarith

/-- **`eq:rozoj`, the last step**: `Z ≤ (√(|φ|₁ x/49 (M+T)) + √(S*E))²` with `|φ|₁ ≤ 1.2533143`,
`M + T ≤ (cM + 3.5776·10⁻⁴)x`, `S*E ≤ 1.0532·10⁻¹¹x²/49` gives `Z ≤ c·x²/49` whenever
`(√(1.2533143(cM + 3.5776·10⁻⁴)) + √(1.0532·10⁻¹¹))² ≤ c`. -/
theorem z_close (Z a M T SE x c cM : ℝ)
    (hZ : Z ≤ (Real.sqrt (a * x / 49 * (M + T)) + Real.sqrt SE) ^ 2)
    (ha0 : 0 ≤ a) (ha : a ≤ 1.2533143) (hx : 0 ≤ x) (hMT : M + T ≤ (cM + 3.5776e-4) * x)
    (hcM : 0 ≤ cM + 3.5776e-4) (hSE : SE ≤ 1.0532e-11 * x ^ 2 / 49)
    (hc : (Real.sqrt (1.2533143 * (cM + 3.5776e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤ c) :
    Z ≤ c * x ^ 2 / 49 := by
  have hx7 : 0 ≤ x / 7 := div_nonneg hx (by norm_num)
  have h1 : a * x / 49 * (M + T) ≤ 1.2533143 * (cM + 3.5776e-4) * (x / 7) ^ 2 := by
    have hx49 : 0 ≤ a * x / 49 := div_nonneg (mul_nonneg ha0 hx) (by norm_num)
    calc a * x / 49 * (M + T) ≤ a * x / 49 * ((cM + 3.5776e-4) * x) :=
          mul_le_mul_of_nonneg_left hMT hx49
      _ = a * ((cM + 3.5776e-4) * (x / 7) ^ 2) := by ring
      _ ≤ 1.2533143 * ((cM + 3.5776e-4) * (x / 7) ^ 2) :=
          mul_le_mul_of_nonneg_right ha (mul_nonneg hcM (sq_nonneg _))
      _ = 1.2533143 * (cM + 3.5776e-4) * (x / 7) ^ 2 := by ring
  have h2 : SE ≤ 1.0532e-11 * (x / 7) ^ 2 := le_of_le_of_eq hSE (by ring)
  have hs1 : Real.sqrt (a * x / 49 * (M + T)) ≤
      Real.sqrt (1.2533143 * (cM + 3.5776e-4)) * (x / 7) := by
    calc Real.sqrt (a * x / 49 * (M + T))
        ≤ Real.sqrt (1.2533143 * (cM + 3.5776e-4) * (x / 7) ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (1.2533143 * (cM + 3.5776e-4)) * (x / 7) := by
          rw [Real.sqrt_mul (mul_nonneg (by norm_num) hcM), Real.sqrt_sq hx7]
  have hs2 : Real.sqrt SE ≤ Real.sqrt 1.0532e-11 * (x / 7) := by
    calc Real.sqrt SE ≤ Real.sqrt (1.0532e-11 * (x / 7) ^ 2) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt 1.0532e-11 * (x / 7) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hx7]
  have hsum0 : 0 ≤ Real.sqrt (a * x / 49 * (M + T)) + Real.sqrt SE :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsum : Real.sqrt (a * x / 49 * (M + T)) + Real.sqrt SE ≤
      (Real.sqrt (1.2533143 * (cM + 3.5776e-4)) + Real.sqrt 1.0532e-11) * (x / 7) := by
    linarith
  have hsq := pow_le_pow_left₀ hsum0 hsum 2
  calc Z ≤ (Real.sqrt (a * x / 49 * (M + T)) + Real.sqrt SE) ^ 2 := hZ
    _ ≤ ((Real.sqrt (1.2533143 * (cM + 3.5776e-4)) + Real.sqrt 1.0532e-11) * (x / 7)) ^ 2 := hsq
    _ = (Real.sqrt (1.2533143 * (cM + 3.5776e-4)) + Real.sqrt 1.0532e-11) ^ 2 * (x ^ 2 / 49) := by
        ring
    _ ≤ c * (x ^ 2 / 49) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = c * x ^ 2 / 49 := by ring

/-- `M + T ≤ (cM + 3.5776·10⁻⁴)x`. -/
theorem mt_le (M T cM x : ℝ) (hM : M ≤ cM * x) (hT : T ≤ 3.5776e-4 * x) :
    M + T ≤ (cM + 3.5776e-4) * x :=
  le_of_le_of_eq (add_le_add hM hT) (by ring)

/-! ## (3c) THE COMPOSITION -/

/-- **THE SPINE of (7.48), generic in the constant.** `thm:ostop` (`Ostop`) with the explicit
inputs of §7.4: `S` from Prop 1.5 (`felipa`), `J` from the lower half of `lem:drujal`
(`DrujalLow`, fed by Thm 1.4 through `eb_plus`/`et_plus`), `E` (`Dubistdie`), `S*(0,x)` from
Cor 1.3 (`sstar_le`), `M` (`MNum`), `T` (`LamberNum`), `|φ|₁` (`PhiL1`). Application only: every
numeric step is a named lemma above. -/
theorem minor_of_mnum (c cM : ℝ)
    (hc : (Real.sqrt (1.2533143 * (cM + 3.5776e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤ c)
    (hcM : 0 ≤ cM + 3.5776e-4) (ηp ηs ηo ηc φ : ℝ → ℝ) (hm : RT.HelfMajFull ηp ηc)
    (hpf : RT.PlattFull) (hsc : MajSp.StarScale ηs ηc) (hrg : MajSp.Reg ηp ηs ηo)
    (hnm : MajSp.Norms ηp ηs ηo) (hsn : MajSp.SupN ηp ηs) (hoh : OstopHyp ηp ηs φ)
    (hos : Ostop ηp ηs φ) (hdl : DrujalLow ηp ηo) (hdu : Dubistdie ηp) (hpl : PhiL1 φ)
    (hla : LamberNum φ) (hmn : MNum φ cM) : RT.MinorUpperAt c ηp ηs := by
  intro N _ hN
  obtain ⟨mp, cp, mh⟩ := hm hpf
  obtain ⟨hlo1, hlo2, hdiff, hl3, -, hl1s, -, hl1p, -⟩ := hnm
  have hx := MajSp.helfX_big N hN
  have hx0 := x_pos (helfgottX N) hx
  obtain ⟨b, hb⟩ := exists_supFn ηp hoh.2.2.2.2.1
  have hZ := hos hoh b hb (helfgottX N) hx
  have hS := felipa ηp (helfgottX N) hx (mh (helfgottX N) (MajSp.x12_le _ hx))
  have hS0 := sPr_nonneg ηp (helfgottX N)
  have hE := hdu hsn.1 hsn.2.1 b hb (helfgottX N) hx
  have hA := hdl hrg.2.2.1 hsn.1 hl1p hrg.2.2.2.2.2.2.1 hrg.2.2.2.2.2.2.2.1 hrg.2.2.2.2.2.2.2.2
    hlo1 hlo2 hdiff hl3 (helfgottX N) hx (MajSp.et_plus ηp mp _ hx) (MajSp.eb_plus ηp mp _ hx)
  have hP := pje_le ηp b (helfgottX N) hx0.le hA hE
  have hM := m_le φ ηp b cM (helfgottX N) hx hmn hS0 hS hP
  have hT := t_le φ ηp b (helfgottX N) hx hla hS hP
  have hSt := sstar_le ηs ηc hsc cp hsn.2.2.1 hl1s (helfgottX N) hx
  have hSE := hex_le _ _ (helfgottX N) hx0.le (sStar_nonneg ηs hsn.2.2.1 _ hx0) hSt hE
  exact z_close _ _ _ _ _ _ c cM hZ (MajSp.l1_nonneg φ) (phi_l1_le φ hpl) hx0.le
    (mt_le _ _ cM _ hM hT) hcM hSE hc

/-- The numbers of the `0.9845` instance close: `M ≤ 0.3850 + 0.2880 + 1.280418·0.086918`. -/
theorem close_9845 : (Real.sqrt (1.2533143 * (0.385 + 0.288 + 1.280418 * 0.086918 + 3.5776e-4)) +
    Real.sqrt 1.0532e-11) ^ 2 ≤ 0.9845 :=
  close_num _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The numbers of the `0.97392` instance close: `M ≤ 0.3835 + 0.2830 + 1.280418·0.0850`. -/
theorem close_97392 : (Real.sqrt (1.2533143 * (0.3835 + 0.283 + 1.280418 * 0.085 + 3.5776e-4)) +
    Real.sqrt 1.0532e-11) ^ 2 ≤ 0.97392 :=
  close_num _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The numbers of the joint route close: `M ≤ 0.785`. -/
theorem close_mnum : (Real.sqrt (1.2533143 * (0.785 + 3.5776e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤
    0.9845 :=
  close_num _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `0 ≤ 0.086918`. -/
theorem cB_9845 : (0 : ℝ) ≤ 0.086918 := by norm_num

/-- `0 ≤ 0.0850`. -/
theorem cB_97392 : (0 : ℝ) ≤ 0.085 := by norm_num

/-- `cM + 3.5776·10⁻⁴ ≥ 0` at the `0.9845` constants. -/
theorem cM_9845 : (0 : ℝ) ≤ 0.385 + 0.288 + 1.280418 * 0.086918 + 3.5776e-4 := by norm_num

/-- `cM + 3.5776·10⁻⁴ ≥ 0` at the `0.97392` constants. -/
theorem cM_97392 : (0 : ℝ) ≤ 0.3835 + 0.283 + 1.280418 * 0.085 + 3.5776e-4 := by norm_num

/-- `cM + 3.5776·10⁻⁴ ≥ 0` at the joint constant. -/
theorem cM_mnum : (0 : ℝ) ≤ 0.785 + 3.5776e-4 := by norm_num

/-- **THE SPINE of the retargeted minor-arc link**: `RT.MinorUpperAt 0.9845` from the OPEN links,
with the coupled numeric links at `0.3850 / 0.2880 / 0.086918` (`Byrne` at Helfgott's printed
constant; the other two restore his `log 2`). Application only. -/
theorem minorAt_of_links (ηp ηs ηo ηc φ : ℝ → ℝ) (hm : RT.HelfMajFull ηp ηc)
    (hpf : RT.PlattFull) (hsc : MajSp.StarScale ηs ηc) (hrg : MajSp.Reg ηp ηs ηo)
    (hnm : MajSp.Norms ηp ηs ηo) (hsn : MajSp.SupN ηp ηs) (hoh : OstopHyp ηp ηs φ)
    (hos : Ostop ηp ηs φ) (hdl : DrujalLow ηp ηo) (hdu : Dubistdie ηp) (hpl : PhiL1 φ)
    (hla : LamberNum φ) (hro : RousselNum φ 0.385) (hco : ComradeNum φ 0.288)
    (hby : Byrne φ 0.086918) : RT.MinorUpperAt 0.9845 ηp ηs :=
  minor_of_mnum 0.9845 _ close_9845 cM_9845 ηp ηs ηo ηc φ hm hpf hsc hrg hnm hsn hoh hos hdl hdu
    hpl hla (mnum_of_terms φ _ _ _ hro hco hby cB_9845)

/-- **The check at Helfgott's `0.97392`** (`Smooth.MinorUpperSmooth`, by `RT.minorUpper_iff`):
the same spine closes there too, but only with all three numeric links tightened to
`0.3835 / 0.2830 / 0.0850` (`+0.38% / +0.87% / +1.65%` over the exact suprema). -/
theorem minorSmooth_of_links (ηp ηs ηo ηc φ : ℝ → ℝ) (hm : RT.HelfMajFull ηp ηc)
    (hpf : RT.PlattFull) (hsc : MajSp.StarScale ηs ηc) (hrg : MajSp.Reg ηp ηs ηo)
    (hnm : MajSp.Norms ηp ηs ηo) (hsn : MajSp.SupN ηp ηs) (hoh : OstopHyp ηp ηs φ)
    (hos : Ostop ηp ηs φ) (hdl : DrujalLow ηp ηo) (hdu : Dubistdie ηp) (hpl : PhiL1 φ)
    (hla : LamberNum φ) (hro : RousselNum φ 0.3835) (hco : ComradeNum φ 0.283)
    (hby : Byrne φ 0.085) : Smooth.MinorUpperSmooth ηp ηs :=
  (RT.minorUpper_iff ηp ηs).mpr (minor_of_mnum 0.97392 _ close_97392 cM_97392 ηp ηs ηo ηc φ hm
    hpf hsc hrg hnm hsn hoh hos hdl hdu hpl hla (mnum_of_terms φ _ _ _ hro hco hby cB_97392))

/-- **The joint route**: one numeric link `MNum φ 0.785` (true supremum `0.742233`) instead of
three. Application only. -/
theorem minorAt_of_mnum (ηp ηs ηo ηc φ : ℝ → ℝ) (hm : RT.HelfMajFull ηp ηc)
    (hpf : RT.PlattFull) (hsc : MajSp.StarScale ηs ηc) (hrg : MajSp.Reg ηp ηs ηo)
    (hnm : MajSp.Norms ηp ηs ηo) (hsn : MajSp.SupN ηp ηs) (hoh : OstopHyp ηp ηs φ)
    (hos : Ostop ηp ηs φ) (hdl : DrujalLow ηp ηo) (hdu : Dubistdie ηp) (hpl : PhiL1 φ)
    (hla : LamberNum φ) (hmn : MNum φ 0.785) : RT.MinorUpperAt 0.9845 ηp ηs :=
  minor_of_mnum 0.9845 0.785 close_mnum cM_mnum ηp ηs ηo ηc φ hm hpf hsc hrg hnm hsn hoh hos
    hdl hdu hpl hla hmn

/-! ## (3d) On Helfgott's own weights -/

/-- **`φ = t²e^{−t²/2}` is in `L¹(0,∞)`** (from Mathlib's Gaussian moments). -/
theorem phi_integrableOn : IntegrableOn HW.phi (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 2)
    (by norm_num)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [HW.phi]
  rw [Real.rpow_two]
  ring_nf

/-- **`OstopHyp` on Helfgott's weights, reduced**: `η* = (η₂ ∗_M φ)(49t)` is `rfl`, `φ` is
continuous, nonnegative and integrable (proved), `η₊` is bounded by `BandUniform`
(`HW.etaPlusSup_of_band`); what remains is that `η₊ = h₂₀₀(t)te^{−t²/2}` is differentiable off a
finite set and tends to `0`. -/
theorem ostopHyp_helf (hb : HW.BandUniform)
    (hd : ∃ S : Finset ℝ, ∀ t : ℝ, 0 ≤ t → t ∉ S → DifferentiableAt ℝ HW.etaPlus t)
    (ht : Filter.Tendsto HW.etaPlus Filter.atTop (nhds 0)) :
    OstopHyp HW.etaPlus HW.etaStar HW.phi := by
  refine ⟨fun t => rfl, HW.continuous_phi.continuousOn, fun t _ => HW.phi_nonneg t,
    phi_integrableOn, ⟨1.079955, ?_⟩, hd, ht⟩
  rintro _ ⟨t, _, rfl⟩
  exact HW.etaPlusSup_of_band hb t

/-- **The minor-arc link on Helfgott's weights**: `RT.MinorUpperAt 0.9845 η₊ η*` from the OPEN
links, with `η∘ = HW.etaCirc`, base `η₂ ∗_M φ`, `φ = HW.phi`; `StarScale` is `rfl`. -/
theorem minorAt_helf (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (hpf : RT.PlattFull) (hrg : MajSp.Reg HW.etaPlus HW.etaStar HW.etaCirc)
    (hnm : MajSp.Norms HW.etaPlus HW.etaStar HW.etaCirc) (hsn : MajSp.SupN HW.etaPlus HW.etaStar)
    (hoh : OstopHyp HW.etaPlus HW.etaStar HW.phi) (hos : Ostop HW.etaPlus HW.etaStar HW.phi)
    (hdl : DrujalLow HW.etaPlus HW.etaCirc) (hdu : Dubistdie HW.etaPlus) (hpl : PhiL1 HW.phi)
    (hla : LamberNum HW.phi) (hro : RousselNum HW.phi 0.385) (hco : ComradeNum HW.phi 0.288)
    (hby : Byrne HW.phi 0.086918) : RT.MinorUpperAt 0.9845 HW.etaPlus HW.etaStar :=
  minorAt_of_links HW.etaPlus HW.etaStar HW.etaCirc (HW.mconv HW.eta2 HW.phi) HW.phi hm hpf
    RT.starScale_helf hrg hnm hsn hoh hos hdl hdu hpl hla hro hco hby

/-- **EP1054's last Helfgott input with the minor-arc link replaced by its spine**:
`RT.helfgottAt_of_links` with `MinorUpperAt 0.9845` supplied by `minorAt_helf`. Every hypothesis
is OPEN; together they are the work list. -/
theorem helfgottAt_minsp (hpf : RT.PlattFull) (hb : HW.BandUniform)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (hrg : MajSp.Reg HW.etaPlus HW.etaStar HW.etaCirc)
    (hnf : MajSp.Nefumo HW.etaPlus HW.etaStar HW.etaCirc) (hdj : MajSp.Drujal HW.etaPlus)
    (hcl : MajSp.CLower HW.etaCirc HW.etaStar)
    (hnm : MajSp.Norms HW.etaPlus HW.etaStar HW.etaCirc) (hsn : MajSp.SupN HW.etaPlus HW.etaStar)
    (hoh : OstopHyp HW.etaPlus HW.etaStar HW.phi) (hos : Ostop HW.etaPlus HW.etaStar HW.phi)
    (hdl : DrujalLow HW.etaPlus HW.etaCirc) (hdu : Dubistdie HW.etaPlus) (hpl : PhiL1 HW.phi)
    (hla : LamberNum HW.phi) (hro : RousselNum HW.phi 0.385) (hco : ComradeNum HW.phi 0.288)
    (hby : Byrne HW.phi 0.086918) : Principia.Erdos1054.Proofs.BalancedK.HelfgottAt 0.00032 :=
  RT.helfgottAt_of_links hpf hb hm hrg hnf hdj hcl hnm hsn
    (minorAt_helf hm hpf hrg hnm hsn hoh hos hdl hdu hpl hla hro hco hby)

/-! ## (4) The `log 2`, certified -/

set_option exponentiation.threshold 6000 in
/-- **`eq:roussel`'s numerator is short by `log 2`**: `log 150001 + 2.3912 − 13.6164 ∈ (0.69,
0.70)` (the truth is `0.69320`; `log 2 = 0.69315`). From `150001³⁰⁰ ≥ 2⁵¹⁵⁸`, `150001¹⁰ ≤ 2¹⁷²`
and `log 2 ∈ (0.6931471803, 0.6931471808)`. -/
theorem roussel_slip :
    0.69 < Real.log 150001 + 2.3912 - 13.6164 ∧ Real.log 150001 + 2.3912 - 13.6164 < 0.7 := by
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have h1 : (2 : ℝ) ^ 5158 ≤ 150001 ^ 300 := by norm_num
  have h2 : (150001 : ℝ) ^ 10 ≤ 2 ^ 172 := by norm_num
  have g1 := Real.log_le_log (by positivity) h1
  have g2 := Real.log_le_log (by positivity) h2
  rw [Real.log_pow, Real.log_pow] at g1 g2
  push_cast at g1 g2
  constructor <;> linarith

/-! ## (5) Every new `Prop` constrains, and what the zero weights do -/

/-- `amaj` of a junk weight is `0`: then `DrujalLow`'s conclusion is FALSE, so the link is never
met by junk. -/
theorem amaj_junk (η : ℝ → ℝ) (x : ℝ) (h : ∀ α, Smooth.smSum η x α = 0) :
    ¬ 8.6298 ≤ MajSp.amaj η x := by
  have h0 : MajSp.amaj η x = 0 := by simp [MajSp.amaj, h]
  rw [h0]
  norm_num

/-- **`Ostop` is met by `η₊ = 0`** (then `Z = 0` and the right side is a square): like
`Smooth.MinorUpperSmooth`, it is an upper bound whose content is quantitative. -/
theorem ostop_zero (ηs φ : ℝ → ℝ) : Ostop 0 ηs φ := by
  intro _ b _ x _
  have hz : zMin 0 ηs x = 0 := by simp [zMin, Smooth.smSum_zero]
  rw [hz]
  exact sq_nonneg _

/-- **`Dubistdie` is met by `η = 0`** (its sup function vanishes, so `E = 0`); it is a
statement about EVERY weight with the two sup bounds, i.e. weight-free real analysis. -/
theorem dubistdie_zero : Dubistdie 0 := by
  intro _ _ b hb x hx
  have hb0 : ∀ t : ℝ, 0 ≤ t → b t = 0 := fun t ht => by
    have hs : ((fun r => |(0 : ℝ → ℝ) r|) '' Set.Ici t) = {0} := by
      ext y
      simp only [Pi.zero_apply, abs_zero, Set.mem_image, Set.mem_Ici, Set.mem_singleton_iff]
      exact ⟨fun ⟨_, _, h⟩ => h.symm, fun h => ⟨t, le_refl t, h.symm⟩⟩
    have := hb t ht
    rw [hs] at this
    exact this.unique isLUB_singleton
  have hc0 : cE0 b = 0 := by
    unfold cE0
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ))
      (fun t ht => by simp [hb0 t (le_of_lt ht)])]
    simp
  have hc1 : cE1 b = 0 := by
    unfold cE1
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ))
      (fun t ht => by simp [hb0 t (le_trans zero_le_one (le_of_lt ht))])]
    simp
  have hE : eBig b x = 0 := by
    simp [eBig, hc0, hc1, hb0 0 (le_refl 0)]
  rw [hE]
  exact mul_nonneg (by norm_num) (x_pos x hx).le

/-- **`OstopHyp` is satisfiable**: `η₊ = 0`, `φ = 0` and `η* = (η₂ ∗_M 0)(49t)`. (On Helfgott's
weights it reduces to two open facts about `η₊`: `ostopHyp_helf`.) -/
theorem ostopHyp_zero : OstopHyp 0 (fun t => HW.mconv HW.eta2 0 (49 * t)) 0 := by
  refine ⟨fun t => rfl, continuousOn_const, fun t _ => le_refl 0, integrableOn_zero,
    ⟨0, ?_⟩, ⟨∅, fun t _ _ => differentiableAt_const 0⟩, tendsto_const_nhds⟩
  rintro _ ⟨t, _, rfl⟩
  simp

/-- **`PhiL1` rejects `φ = 0`** (`√(π/2) > 0`). -/
theorem phiL1_zero : ¬ PhiL1 0 := by
  intro h
  have h' : MajSp.l1 0 = Real.sqrt (Real.pi / 2) := h
  have h0 : MajSp.l1 0 = 0 := by simp [MajSp.l1]
  rw [h0] at h'
  have hp : 0 < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.mpr (by positivity)
  linarith

/-- **`RousselNum` forces `g(r₀) ≥ 0`** (a true property of `eq:basia`: `g` bounds a supremum of
absolute values): at `p → ∞` a negative `g(r₀)` would make the left side unbounded. So the link is
not met by an arbitrary function in place of `g`. -/
theorem roussel_nonneg (φ : ℝ → ℝ) (c : ℝ) (hR : RousselNum φ c) (x : ℝ)
    (hx : 49 * 10 ^ 25 ≤ x) : 0 ≤ gB φ (x / 49) 150000 := by
  by_contra hneg
  have hlt : gB φ (x / 49) 150000 < 0 := not_le.mp hneg
  set g0 := gB φ (x / 49) 150000
  set s := 0.640209 * Real.log x - 0.021095
  have hg : g0 ≠ 0 := hlt.ne
  have h := hR x hx s (8.6297 + (|c| + |g0 * (hR0 x * s)| + 1) / (-g0)) (le_refl s)
    (by
      have : 0 ≤ (|c| + |g0 * (hR0 x * s)| + 1) / (-g0) :=
        div_nonneg (by positivity) (by linarith)
      linarith)
  have e : g0 * (hR0 x * s - (8.6297 + (|c| + |g0 * (hR0 x * s)| + 1) / (-g0))) =
      g0 * (hR0 x * s) - 8.6297 * g0 + (|c| + |g0 * (hR0 x * s)| + 1) := by
    field_simp
    ring
  rw [e] at h
  have h1 := le_abs_self c
  have h2 := neg_abs_le (g0 * (hR0 x * s))
  linarith

end Principia.Common.TernaryGoldbach.MinSp
