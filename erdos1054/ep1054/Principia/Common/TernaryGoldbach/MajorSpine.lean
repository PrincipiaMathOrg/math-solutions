/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.Smoothed
import Principia.Common.TernaryGoldbach.SingularSeries

set_option autoImplicit false

/-!
# The spine of Helfgott's (7.25): the major-arc lower bound as a composition of named links

**EVERY LINK BELOW IS OPEN except the two marked DISCHARGED (`LSLink`, `ZStar`; the `Z₊` half of
`[Z]` is a theorem too). This file proves the COMPOSITION.** Nothing here proves Helfgott's
major-arc analysis, Platt's verification, or ternary Goldbach. The strongest form is
`majorLower_lz`: nine OPEN links → `Smooth.MajorLowerSmooth`.

`Smooth.MajorLowerSmooth ηp ηs` is `ternvin.tex` (7.25) = `eq:juventud`:
`PlattGRH → ∀ N odd ≥ 10^27, 1.058259·x²/49 ≤ Re ∫_{𝔐_{8,150000}} S_{η₊}² S_{η*} e(−Nα)`,
`x = helfgottX N`. Per the SPINE RULE it gets a spine before anyone attacks it: Helfgott's own
argument (`ternvin.tex` 4458–4865, `prop:nefumo` 1612–1676, `lem:drujal` 1412–1453, and
HelfMaj = arXiv:1305.2897 Thms 1.4, Cor 1.3, Prop 1.5) as named `Prop`s, composed by
`majorLower_of_links`, whose proof is application plus the arithmetic of `ternvin.tex` 4772–4865.

## The spine

```
 PlattGRH ─► HelfMaj ηp ηc  (Thm 1.4 for η₊, Cor 1.3 for the base ηc of η*, Prop 1.5 for η₊)
               │  eb_plus / eb_star / et_plus / et0_star / zplus   (PROVED: aggregation, scaling)
               ▼
   E₊ ≤ 2.3921e-8, E* ≤ 1.3353e-7/49, ET₊ ≤ 1.1377e-8, |err*(0)| ≤ 1.71973e-8, Z₊ ≤ .640209 log x
               │
  Drujal ─► A₊ ≤ 8.7806   ZStar ─► Z* ≤ .0362 log x   LSLink ─► LS₊, LS*   (both DISCHARGED
               │                     ▲ SupN, Norms            ▲ SupN          from SupN, Norms)
  Reg ─► Nefumo (prop:nefumo at δ₀=8, r=150000, x ≥ 4.9e26) :  |∫_𝔐 − C₀·C·x²| ≤ err
               │
  C0Lower (C₀ ≥ 1.3203236) · CLower (C ≥ (√(π/2)|η∘|₂² − .000834)/49) · Norms
               ▼
   arith_close :  1.058259·x²/49 ≤ Re ∫_𝔐      ⇒      majorLower_of_links
```

Links (all `def … : Prop`), and which are weight-generic:
* `HelfMaj ηp ηc` — **the only Platt consumer** (`PlattGRH → Malpor ηp ∧ Coprar ηc ∧ Malheur ηp`),
  HelfMaj's statements transcribed verbatim. Weight-SPECIFIC (they are theorems about η₊, φ∗η₂).
* `StarScale ηs ηc` — `η*(t) = ηc(49t)`, the definition of η* (`ternvin.tex` 4432). Weight def.
* `Reg` — the regularity hypotheses of `prop:nefumo`, verbatim. Weight-SPECIFIC facts.
* `Nefumo` — `prop:nefumo` at Helfgott's instance. GENERIC in the weights (under `Reg`).
* `Drujal` — `lem:drujal` (upper half, `eq:mardi`) at Helfgott's numbers. GENERIC in the weight.
* `ZStar` — `eq:bavette`/`eq:julie`. GENERIC; **DISCHARGED** by `zstar_holds` (its hypotheses
  name every input: `η* ≥ 0`, two sup norms, `|η*|₁`, and HelfMaj's `err_{η*,χ_T}(0,x)`).
* `LSLink` — `eq:alisa`. GENERIC; **DISCHARGED** by `ls_link` from `SupN`.
* `C0Lower` — `eq:arnar`, `C₀ ≥ 1.3203236` on odd `N`. Weight-FREE (the twin-prime constant).
* `CLower` — `eq:barbar`. Weight-SPECIFIC (uses `η* = (η₂∗φ)(49t)` and `supp η∘ ⊆ [0,2]`).
* `Norms`, `SupN` — the numerical norms (`eq:lopez`, `sanchez`, `halr`, `melancho`, `marldoro`,
  `sazar`, `macadam`, `muthit`, 4744, 4798–4812). Weight-SPECIFIC.
The Z₊ half of `[Z]` is **DISCHARGED** (`zplus`, from `Malheur` and `Λ(n) ≤ log n`).

`majorLower_of_links` contains no context-consuming tactic (its arithmetic lives in `arith_close`
and five one-line helpers), so `check_unused_hypotheses.py` EXAMINES it rather than skipping it:
every one of its eleven link binders is used.

## CORRECTIONS TO THE SOURCE, found while transcribing (each checked against `ternvin.tex`)

1. **`E` must be weighted by `√(conductor)`, not `√q`.** `eq:vulgato`/`eq:sreda` define
   `E_{η,r,δ₀} = max_{χ mod q} √q·|err_{η,χ*}|`. For `χ` principal mod `q = 300000`, `χ* = χ_T`
   and `√q·|err_{η₊,χ_T}| ≤ 547.7·1.1377e-8 = 6.2e-6`, so the printed `E_{η₊} ≤ 2.3921e-8`
   (`eq:zakone2`) does NOT follow from Thm 1.4 under the printed definition. It does follow for
   `√q*` (`q*` the conductor), which is also all the proofs of `prop:nefumo` and `lem:drujal` use
   (their `√q` bounds `|τ(χ̄)| = |μ(q/q*)|·√q*`). `EBound` is the `√q*` version. **So `Nefumo` and
   `Drujal` are STRONGER than the literal statements** (by that one Gauss-sum step); this needs
   adjudication by whoever discharges them.
2. **`E_{η*}` is off by `√κ = 7` in the source.** `eq:fabienne` bounds `E_{η*,r,8}` by
   `(1/κ)(4.269e-14 + (380600 + 76√300000)/√x₊) = 1.9075e-8/κ`, saying the scaling
   `η*(t) = (η₂∗φ)(κt)` "in effect divides x by κ". Dividing `x` by `κ` turns `1/√x` into
   `√κ/√x`: Cor 1.3 at scale `x/49` gives `1.33520e-7/κ`, SEVEN times more. `err_scale` proves the
   scaling identity, `eb_star` derives `E* ≤ 1.3353e-7/49` from Cor 1.3 verbatim. (7.25) STILL
   CLOSES: the margin drops from `1.367e-6` to `3.62e-7` (units `x²/49`); `arith_close` uses the
   corrected constant. (`eq:julie`'s `|err_{η*,χ_T}(0,x)| ≤ 1.71973e-8` has the opposite slip —
   it drops the `1/κ` too — and is merely conservative: the truth is `2.457e-9`, `et0_star`.)
3. **`[Z]` is a Platt consumer.** `Z_{η₊²,2}` comes from HelfMaj Prop 1.5, proved from zeros of
   `ζ` up to height 450 (`majarcs.tex` 4942–5005), and `Z_{η*²,2}` from Cor 1.3 at `χ_T`. Both
   enter `ZStar`/`zplus` as hypotheses supplied by `HelfMaj`, so only `HelfMaj` takes `PlattGRH`.
4. **`LS_η` needs `|η|`.** `eq:vulgato` writes `∑_α η(p^α/x)`; the `O*` in `eq:beatit` it bounds
   needs `∑_α |η(p^α/x)|` (a signed η could cancel). `LSBound` uses `|η|`; `eq:alisa`'s bound
   holds for it unchanged (its proof already goes through `|η|_∞`, `|η·t|_∞`).
5. Minor, recorded so nobody re-derives them: `eq:opus111`'s first error line is printed without
   `O*` (its derivation `eq:stev` makes it an error term); `eq:teresa` prints the `δ`-range as
   `gcd(q,2)δ₀r/q` (the arcs and `eq:vulgato` give `/2q`); 4823 cites `A ≤ 8.8013` but computes
   with `8.7806`; line 3 of `eq:opus111` uses `log r` where `∑_{p|q} log p ≤ log 2r` for even `q`
   (irrelevant at `10⁻²⁰`).

## Restrictions (each makes the link WEAKER than the source, i.e. still implied by it)

* `Nefumo` is stated at `δ₀ = 8`, `r = 150000`, `x ≥ 4.9·10²⁶`, `N ≥ 1` (source: any `δ₀, r, x ≥ 1,
  N ≥ 0`). At Helfgott's instance the arcs are disjoint; for small `x` they overlap and the
  printed proof (a sum over arcs) does not literally apply. `N ≥ 1` is where `sing3_vulgo` pins
  `SingularSeries.sing3` to `eq:vulgo`.
* "η∘ thrice differentiable outside finitely many points" is transcribed as `ContDiffAt ℝ 3`
  there, and the implicit `η∘ ∈ L²` is made explicit. True of Helfgott's η∘ (smooth off {0,2}).

## Junk values (Mathlib's `tsum`/integral of a non-summable/non-integrable function is `0`)

* `twSum`, hence `err`: junk `0`, so `err = −mainFT` (q = 1) or `0` (q > 1). The `q > 1` part of
  `Malpor`/`Coprar`/`EBound` is then vacuous for a junk weight, but the `q = 1` part is not
  (`‖mainFT η 0‖ = |∫η|`), and `Nefumo` must then hold with the smaller error: UNPROVABLE for
  junk weights, never vacuous. Tolerable.
* `amaj` (A), `zk` (Z): junk `0` only through `smSum`/`tsum` junk; the upper-bound links `Drujal`,
  `ZStar` become easier, `Nefumo` harder. Tolerable. `zplus` does not rely on it: `Malheur` is a
  two-sided asymptotic, so it forces summability (`hfs` in its proof).
* `LSBound` carries `Summable` explicitly, so it is never junk-vacuous.
* `l1`, `l2`: junk `0`. The equalities/lower bounds (`l1 ηs = √(π/2)/49`, `l2 η∘ ≥ .8001287`)
  force integrability; the upper bounds do not, but `Reg` supplies `L¹ ∩ L²` wherever `Nefumo`
  consumes them. Tolerable.
* `ccon` (C): junk `0`; `CLower` then fails (`C ≥ 0.01636 > 0`), so it forces integrability.
* Sup-type quantities (`E`, `ET`, `LS`, sup norms) are all FORALL-bound `Prop`s, never `sSup`.

## Arithmetic (`arith_close`; exact rationals, re-verified in mpmath)

`π ∈ (3.141592, 3.141593)` gives `√(π/2) ∈ [1.2533139, 1.2533143]`. With `ε₀ = 3.0371e-6`
(`|η₊−η∘|₂ ≤ 2.43e-6 < ε₀·0.8001287`): line 1 `≤ 2.9387e-5·|η*|₁`; line 2 `≤ 2.78652e-6/49`
(corrected E*); line 3 `≤ 61(log x)²x ≤ 976·x²/√x ≤ 4.41e-11·x²`; main
`≥ 1.3203236·(1.2533139·0.8001287² − 0.000834)/49`. Net `1.0582591590/49 ≥ 1.058259/49`,
margin `1.59e-7` (the exact-π margin is `3.62e-7`).
**Smallest `C₀` that still closes**: `1.3203231` with the corrected `E*` (`1.3203219` with
Helfgott's printed `E*`); the true `2·C₂ = 1.32032363`, so the certified `C₀` needs ~7 digits.
Relaxed to `1.05816`: `1.3201996` (corrected) / `1.3201984` (printed).

## The adversarial pass

* **Zero weights** (`zero_rest`) satisfy `Nefumo` (vacuously: `|0−0|₂ < ε₀|0|₂` is false),
  `Drujal`, `ZStar`, `CLower`, `SupN`, `StarScale`, `Malpor`, `Coprar`. Only `Norms`
  (`norms_zero_o`: `|η∘|₂ ≥ 0.8001287`) and `HelfMaj` through Prop 1.5 (`malheur_zero`: it is a
  two-sided asymptotic) reject them. Nondegeneracy lives where the numbers live; the analytic
  links constrain only jointly, as in `Smoothed`.
* **Every OPEN link is used.** A scratch probe (not in the library) restated
  `majorLower_of_links` with each of the nine OPEN links replaced by `_`: nine errors
  `don't know how to synthesize placeholder for argument` (`hm`, `sc`, `rg`, `nf`, `dj`, `c0`,
  `cl`, `nm`, `sn`);
  the control, and the version with `zstar_holds`/`ls_link` in place of `zs`/`ls`, compile;
  `(hm _).1 : Malpor ηp` fails on `⊢ Spine.PlattGRH`.
* **Satisfiable by something real**: `LSLink` and `ZStar` hold for EVERY weight (theorems);
  `StarScale (fun t => ηc (49 * t)) ηc` holds by `rfl`. `Reg`, `Norms`, `SupN`, `CLower` need
  Helfgott's actual weights (the HelfWeights front); `HelfMaj` needs Platt; `C0Lower` needs the
  twin-prime constant certified to 7 digits (the library has `1.31`); `Nefumo`, `Drujal` are
  Helfgott's analysis.
-/

namespace Principia.Common.TernaryGoldbach.MajSp

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction
open Principia.Erdos1054 (helfgottX)

/-! ## The quantities of `prop:nefumo` -/

/-- **The twisted sum** `S_{η,χ}(β,x) = ∑_n Λ(n) χ(n) e(βn) η(n/x)` (`eq:shangh`). A `tsum`: junk
`0` when not summable. For `χ` the trivial character mod `1` it is `Smooth.smSum`. -/
noncomputable def twSum (η : ℝ → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (x β : ℝ) : ℂ :=
  ∑' n : ℕ, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((η ((n : ℝ) / x) : ℝ) : ℂ) * e ((n : ℝ) * β)

/-- **The main term** `∫_0^∞ η(t) e(δt) dt = η̂(−δ)` of `eq:glenkin` (after `t ↦ t/x`). Weights
live on `[0,∞)` in the source, hence `Ioi 0`. -/
noncomputable def mainFT (η : ℝ → ℝ) (δ : ℝ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), ((η t : ℝ) : ℂ) * e (δ * t)

/-- **`err_{η,χ}(δ,x)`** (`eq:glenkin`, `eq:brahms`): `S_{η,χ}(δ/x,x)/x` minus the main term, which
is present only for the trivial character (modulus `1`). -/
noncomputable def err (η : ℝ → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (δ x : ℝ) : ℂ :=
  twSum η χ x (δ / x) / x - if q = 1 then mainFT η δ else 0

/-- **`E_{η,r,δ₀} ≤ E`** at `r = 150000`, `δ₀ = 8` (`eq:vulgato`), as a FORALL bound: every `χ` mod
`q ≤ r·gcd(q,2)`, every `|δ| ≤ gcd(q,2)δ₀r/(2q)`. Weighted by `√(conductor)`: correction 1. -/
def EBound (η : ℝ → ℝ) (x E : ℝ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → q ≤ 150000 * Nat.gcd q 2 → ∀ χ : DirichletCharacter ℂ q, ∀ δ : ℝ,
    |δ| ≤ (Nat.gcd q 2 : ℝ) * 600000 / q →
      Real.sqrt (χ.conductor : ℝ) * ‖err η χ.primitiveCharacter δ x‖ ≤ E

/-- **`ET_{η,s} ≤ T`** (`eq:sreda`): the trivial character, `|δ| ≤ s`. -/
def ETBound (η : ℝ → ℝ) (s x T : ℝ) : Prop :=
  ∀ δ : ℝ, |δ| ≤ s → ‖err η (1 : DirichletCharacter ℂ 1) δ x‖ ≤ T

/-- `|η|₁` on `(0,∞)`. Junk `0` if not integrable. -/
noncomputable def l1 (η : ℝ → ℝ) : ℝ := ∫ t in Set.Ioi (0 : ℝ), |η t|

/-- `|η|₂` on `(0,∞)`. Junk `0` if not square-integrable. -/
noncomputable def l2 (η : ℝ → ℝ) : ℝ := Real.sqrt (∫ t in Set.Ioi (0 : ℝ), η t ^ 2)

/-- **`A_η = (1/x)∫_𝔐 |S_η(α,x)|² dα`** (`eq:vulgato`), `𝔐 = 𝔐_{8,150000}` on `(0,1]`. -/
noncomputable def amaj (η : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ α in Smooth.majorSet x, ‖Smooth.smSum η x α‖ ^ 2) / x

/-- **`Z_{η,k}(x) = (1/x)∑_n Λ^k(n) η(n/x)`** (`eq:vulgato`). -/
noncomputable def zk (η : ℝ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (∑' n : ℕ, (Λ n) ^ k * η ((n : ℝ) / x)) / x

/-- **`LS_η(x,r) ≤ L`** at `r = 150000` (`eq:vulgato`), with `|η|` (correction 4) and the
summability explicit, so the bound is never met by junk. -/
def LSBound (η : ℝ → ℝ) (x L : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ 150000 →
    Summable (fun k : ℕ => |η ((p : ℝ) ^ (k + 1) / x)|) ∧
      Real.log 150000 * ∑' k : ℕ, |η ((p : ℝ) ^ (k + 1) / x)| ≤ L

/-- **`C_{η∘,η*}(y) = ∫_0^∞∫_0^∞ η∘(t₁)η∘(t₂)η*(y − (t₁+t₂))`** (`eq:vulgo`), `y = N/x`. `η*` is a
function on `[0,∞)` in the source, so it is extended by `0` (the indicator). -/
noncomputable def ccon (ηo ηs : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ t₁ in Set.Ioi (0 : ℝ), ∫ t₂ in Set.Ioi (0 : ℝ),
    ηo t₁ * ηo t₂ * Set.indicator (Set.Ici 0) ηs (y - (t₁ + t₂))

/-! ## HelfMaj, verbatim: the ONLY place `PlattGRH` enters -/

/-- **HelfMaj Thm 1.4** (`thm:malpor`, `majarcs.tex` 276–304) for the weight `η` (Helfgott's
`η₊`). -/
def Malpor (η : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 10 ^ 12 ≤ x → ∀ q : ℕ, 1 ≤ q → (Odd q → q ≤ 150000) → (Even q → q ≤ 300000) →
    ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → ∀ δ : ℝ,
      |δ| ≤ 600000 * (Nat.gcd q 2 : ℝ) / q →
        ‖err η χ δ x‖ ≤ 6.18e-12 / Real.sqrt q + 1.14e-10 / q +
            (499100 / Real.sqrt q + 52) / Real.sqrt x ∧
          (q = 1 → ‖err η χ δ x‖ ≤ 3.34e-11 + 251100 / Real.sqrt x)

/-- **HelfMaj Cor 1.3** (`cor:coprar`, `majarcs.tex` 214–230) for the weight `η` (Helfgott's
`φ ∗_M η₂`, the UNSCALED base of `η*`). -/
def Coprar (η : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 10 ^ 8 ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ 300000 →
    ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → ∀ δ : ℝ, |δ| ≤ 4 * 300000 / q →
      ‖err η χ δ x‖ ≤ 4.269e-14 / q + (380600 / Real.sqrt q + 76) / Real.sqrt x

/-- **HelfMaj Prop 1.5** (`prop:malheur`, `majarcs.tex` 317–333) at one scale `x`:
`∑ Λ(n) log n η²(n/x) = 0.640206 x log x − 0.021095 x + O*((2·10⁻⁶ + 310.84/√x) x log x)`. -/
def MalheurAt (η : ℝ → ℝ) (x : ℝ) : Prop :=
  |∑' n : ℕ, Λ n * Real.log n * η ((n : ℝ) / x) ^ 2 - (0.640206 * x * Real.log x - 0.021095 * x)|
    ≤ (2e-6 + 310.84 / Real.sqrt x) * x * Real.log x

/-- HelfMaj Prop 1.5 at every `x ≥ 10¹²`. -/
def Malheur (η : ℝ → ℝ) : Prop := ∀ x : ℝ, 10 ^ 12 ≤ x → MalheurAt η x

/-- **Link [E] — HelfMaj, the ONLY Platt consumer.** Thm 1.4 for `ηp`, Cor 1.3 for the base `ηc` of
`η*`, Prop 1.5 for `ηp`, all conditional on Platt's verification (Prop 1.5 uses `ζ`'s zeros up to
height `450`, inside `PlattGRH` at `q = 1`: correction 3). OPEN; weight-specific. -/
def HelfMaj (ηp ηc : ℝ → ℝ) : Prop := Spine.PlattGRH → Malpor ηp ∧ Coprar ηc ∧ Malheur ηp

/-- **`η*(t) = ηc(49t)`** (`ternvin.tex` 4432, `κ = 49`): the definition of `η*` from its base. -/
def StarScale (ηs ηc : ℝ → ℝ) : Prop := ∀ t : ℝ, ηs t = ηc (49 * t)

/-! ## The analytic links -/

/-- **The regularity hypotheses of `prop:nefumo`, verbatim** (1614–1618): `η₊ ∈ C²`, `η₊'' ∈ L²`,
`η₊, η* ∈ L¹ ∩ L²`, `η∘` thrice differentiable outside finitely many points (as `ContDiffAt ℝ 3`,
a restriction), `η∘''' ∈ L¹`, and the implicit `η∘ ∈ L²`. OPEN; weight-specific facts. -/
def Reg (ηp ηs ηo : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 ηp (Set.Ici 0) ∧
    MemLp (iteratedDeriv 2 ηp) 2 (volume.restrict (Set.Ioi 0)) ∧
    MemLp ηp 1 (volume.restrict (Set.Ioi 0)) ∧ MemLp ηp 2 (volume.restrict (Set.Ioi 0)) ∧
    MemLp ηs 1 (volume.restrict (Set.Ioi 0)) ∧ MemLp ηs 2 (volume.restrict (Set.Ioi 0)) ∧
    (∃ S : Finset ℝ, ∀ t : ℝ, 0 ≤ t → t ∉ S → ContDiffAt ℝ 3 ηo t) ∧
    Integrable (iteratedDeriv 3 ηo) (volume.restrict (Set.Ioi 0)) ∧
    MemLp ηo 2 (volume.restrict (Set.Ioi 0))

/-- **Link [nefumo] — `prop:nefumo` (`eq:opus111`) at `δ₀ = 8`, `r = 150000`, `x ≥ 4.9·10²⁶`.**
`∫_𝔐 S_{η₊}²S_{η*}e(−Nα) = C₀C_{η∘,η*}x² + O*(line 1 + line 2 + line 3)`, every sup-type quantity
entering through a FORALL bound (`E`, `LS`), the rest as defined quantities. OPEN; generic in the
weights under `Reg`. Stronger than the printed statement by correction 1 (`√q*` for `√q`). -/
def Nefumo (ηp ηs ηo : ℝ → ℝ) : Prop :=
  Reg ηp ηs ηo → ∀ ε₀ : ℝ, 0 ≤ ε₀ → l2 (fun t => ηp t - ηo t) < ε₀ * l2 ηo →
    ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
      ∀ Ep Es : ℝ, EBound ηp x Ep → EBound ηs x Es →
        ∀ Lp Ls : ℝ, LSBound ηp x Lp → LSBound ηs x Ls →
          ‖(∫ α in Smooth.majorSet x, Smooth.kernS ηp ηs N x α) -
              ((SingularSeries.sing3 N * ccon ηo ηs (N / x) * x ^ 2 : ℝ) : ℂ)‖ ≤
            (2.82643 * l2 ηo ^ 2 * (2 + ε₀) * ε₀ +
                (4.31004 * l2 ηo ^ 2 + 0.0012 * l1 (iteratedDeriv 3 ηo) ^ 2 / 8 ^ 5) / 150000) *
              l1 ηs * x ^ 2 +
            (Es * amaj ηp x + Ep * 1.6812 * (Real.sqrt (amaj ηp x) + 1.6812 * l2 ηp) * l2 ηs) *
              x ^ 2 +
            (2 * zk (fun t => ηp t ^ 2) 2 x * Ls +
                4 * Real.sqrt (zk (fun t => ηp t ^ 2) 2 x * zk (fun t => ηs t ^ 2) 2 x) * Lp) * x

/-- **Link [A] — `lem:drujal` (`eq:bfpink` with `eq:mardi`) at Helfgott's numbers, `eq:celine`.**
For `η ∈ L¹ ∩ L^∞` with `|η|_∞ ≤ 1.079955`, `|η|₁ ≤ 1.062319`, `|η|₂ ≤ 0.800132` and the two
`err`-bounds of `eq:zakone1/2`: `A_η(x) ≤ 8.7806`. Only the upper half of the lemma is used, so
`η∘` does not appear. OPEN; generic in the weight. -/
def Drujal (η : ℝ → ℝ) : Prop :=
  MemLp η 1 (volume.restrict (Set.Ioi 0)) → (∀ t : ℝ, 0 ≤ t → |η t| ≤ 1.079955) →
    l1 η ≤ 1.062319 → l2 η ≤ 0.800132 →
      ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ETBound η 600000 x 1.1377e-8 → EBound η x 2.3921e-8 →
        amaj η x ≤ 8.7806

/-- **Link [Z*] — `eq:bavette`, `eq:julie`**: `Z_{η*²,2}(x) ≤ 0.0362 log x`, from `η* ≥ 0`,
`|η*|_∞ ≤ 1.414`, `|η*(t) log⁺(49t)|_∞ ≤ 0.732513`, `|η*|₁ = √(π/2)/49` and the Cor 1.3 bound on
`err_{η*,χ_T}(0,x)`. OPEN; generic in the weight. -/
def ZStar (ηs : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → 0 ≤ ηs t ∧ ηs t ≤ 1.414) →
    (∀ t : ℝ, 0 ≤ t → ηs t * max 0 (Real.log (49 * t)) ≤ 0.732513) →
      l1 ηs = Real.sqrt (Real.pi / 2) / 49 →
        ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ‖err ηs (1 : DirichletCharacter ℂ 1) 0 x‖ ≤ 1.71973e-8 →
          zk (fun t => ηs t ^ 2) 2 x ≤ 0.0362 * Real.log x

/-- **The sup norms** (`eq:sazar`, `eq:muthit`, `eq:macadam`, 4744, 4723–4727):
`|η₊|_∞ ≤ 1.079955`, `|η₊·t|_∞ ≤ 1.19073`, `0 ≤ η* ≤ 1.414`, `|η*·t|_∞ ≤ 3^{3/2}e^{−3/2}/49`,
`|η*(t) log⁺(49t)|_∞ ≤ 0.732513`, all on `t ≥ 0`. OPEN; weight-specific. -/
def SupN (ηp ηs : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → |ηp t| ≤ 1.079955) ∧ (∀ t : ℝ, 0 ≤ t → |ηp t * t| ≤ 1.19073) ∧
    (∀ t : ℝ, 0 ≤ t → 0 ≤ ηs t ∧ ηs t ≤ 1.414) ∧
    (∀ t : ℝ, 0 ≤ t → ηs t * t ≤ 3 * Real.sqrt 3 * Real.exp (-3 / 2) / 49) ∧
    (∀ t : ℝ, 0 ≤ t → ηs t * max 0 (Real.log (49 * t)) ≤ 0.732513)

/-- **Link [LS] — `eq:alisa`**: `LS_{η₊} ≤ 18.57 log x + 28.39`, `LS_{η*} ≤ 24.32 log x + 0.57`,
from the sup norms. Generic. **DISCHARGED** (`ls_link`). -/
def LSLink (ηp ηs : ℝ → ℝ) : Prop :=
  SupN ηp ηs → ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
    LSBound ηp x (18.57 * Real.log x + 28.39) ∧ LSBound ηs x (24.32 * Real.log x + 0.57)

/-- **Link [C₀] — `eq:arnar`**: `C₀ ≥ 2∏_{p>2}(1 − 1/(p−1)²) ≥ 1.3203236` on odd `N`. `C₀` is
`SingularSeries.sing3` (`sing3_vulgo` pins it to `eq:vulgo`). OPEN; weight-free. The library has
only `sing3_ge_sharp` (`1.31`); `1.3203236` is the twin-prime constant to 8 digits. -/
def C0Lower : Prop := ∀ N : ℕ, Odd N → 1.3203236 ≤ SingularSeries.sing3 N

/-- **Link [C] — `eq:barbar`** (from `lem:gosor`, `eq:jaram`, `eq:karlmarx`, `eq:sasa`, `c₁ =
(9/4)/√(2π)`): `C_{η∘,η*}(N/x) ≥ (|φ|₁|η∘|₂² − 0.000834)/κ`, `|φ|₁ = √(π/2)`, at `x = helfgottX N`
(so `N/x = 2 + c₁/49`). Its one numerical input `|η∘'|₂² = 2.7375292…` (`eq:melancho`) is explicit.
OPEN; weight-specific. -/
def CLower (ηo ηs : ℝ → ℝ) : Prop :=
  l2 (deriv ηo) ^ 2 ≤ 2.7375293 → ∀ N : ℕ, Odd N → 10 ^ 27 ≤ N →
    (Real.sqrt (Real.pi / 2) * l2 ηo ^ 2 - 0.000834) / 49 ≤ ccon ηo ηs ((N : ℝ) / helfgottX N)

/-- **Link [N] — the `L¹`/`L²` norms** (`eq:lopez`, `eq:sanchez` as used at 4776, `eq:halr`,
`eq:melancho`, `eq:marldoro`, 4798–4812, `eq:sazar`). OPEN; weight-specific. -/
def Norms (ηp ηs ηo : ℝ → ℝ) : Prop :=
  0.8001287 ≤ l2 ηo ∧ l2 ηo ≤ 0.8001288 ∧ l2 (fun t => ηp t - ηo t) ≤ 2.43e-6 ∧
    l1 (iteratedDeriv 3 ηo) ≤ 32.5023 ∧ l2 (deriv ηo) ^ 2 ≤ 2.7375293 ∧
    l1 ηs = Real.sqrt (Real.pi / 2) / 49 ∧ l2 ηs ^ 2 ≤ 1.77082 / 49 ∧
    l1 ηp ≤ 1.062319 ∧ l2 ηp ≤ 0.800132

/-! ## `C₀` is `eq:vulgo` -/

/-- **`SingularSeries.sing3` IS Helfgott's `C₀`** (`eq:vulgo`/`eq:ausbeuter`):
`∏_{p|N}(1 − 1/(p−1)²)·∏_{p∤N}(1 + 1/(p−1)³)`, for `N ≥ 1`. -/
theorem sing3_vulgo (N : ℕ) (hN : 1 ≤ N) :
    SingularSeries.sing3 N = ∏' p : Nat.Primes,
      (if (p : ℕ) ∣ N then 1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2
        else 1 + 1 / (((p : ℕ) : ℝ) - 1) ^ 3) := by
  rw [SingularSeries.sing3_eq_prod N hN]
  refine tprod_congr fun p => ?_
  split_ifs with h
  · exact SingularSeries.one_add_sing3Local_prime_dvd p N p.2 h
  · exact SingularSeries.one_add_sing3Local_prime_not_dvd p N p.2 h

/-! ## Elementary facts at `x ≥ 4.9·10²⁶` -/

/-- `√x ≥ 22135943·10⁶` (the square is `4.8999997·10²⁶`). -/
theorem sqrt_x_ge (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 22135943 * 10 ^ 6 ≤ Real.sqrt x := by
  rw [Real.le_sqrt (by norm_num) (le_trans (by norm_num) hx)]
  exact le_trans (by norm_num) hx

/-- `log x ≥ 1`. -/
theorem log_ge_one (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (by norm_num) hx)]
  linarith [Real.exp_one_lt_d9]

/-- `(log x)² ≤ 16√x`, from `log x = 4 log x^{1/4} ≤ 4 x^{1/4}`. -/
theorem log_sq_le (x : ℝ) (hx : 0 < x) (hL : 0 ≤ Real.log x) :
    Real.log x ^ 2 ≤ 16 * Real.sqrt x := by
  have hu : 0 < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hx)
  have h1 : Real.log x = 4 * Real.log (Real.sqrt (Real.sqrt x)) := by
    rw [Real.log_sqrt (Real.sqrt_nonneg x), Real.log_sqrt hx.le]
    ring
  have h2 := Real.log_le_sub_one_of_pos hu
  have h3 : Real.sqrt (Real.sqrt x) ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg x)
  have h4 : Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by linarith
  calc Real.log x ^ 2 ≤ (4 * Real.sqrt (Real.sqrt x)) ^ 2 := pow_le_pow_left₀ hL h4 2
    _ = 16 * Real.sqrt x := by rw [mul_pow, h3]; norm_num

/-- `helfgottX N ≥ 4.9·10²⁶` for `N ≥ 10^27`. -/
theorem helfX_big (N : ℕ) (hN : 10 ^ 27 ≤ N) : 49 * 10 ^ 25 ≤ helfgottX N := by
  have h := Smooth.helfX_ge N
  have hN' : (10 : ℝ) ^ 27 ≤ N := by exact_mod_cast hN
  linarith

/-- `√(π/2) ∈ [1.2533139, 1.2533143]`, from `π ∈ (3.141592, 3.141593)`. -/
theorem sqrt_pi_half :
    1.2533139 ≤ Real.sqrt (Real.pi / 2) ∧ Real.sqrt (Real.pi / 2) ≤ 1.2533143 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith [Real.pi_gt_d6]
  · rw [Real.sqrt_le_left (by norm_num)]
    linarith [Real.pi_lt_d6]

/-! ## From HelfMaj to the quantities of `prop:nefumo` (all PROVED) -/

/-- **The `κ`-scaling, exactly**: if `η*(t) = ηc(49t)` then
`err_{η*,χ}(δ,x) = err_{ηc,χ}(δ/49, x/49)/49`. This is correction 2's mechanism: Cor 1.3 is then
applied at scale `x/49`, where `1/√(x/49) = 7/√x`. -/
theorem err_scale (ηs ηc : ℝ → ℝ) (sc : StarScale ηs ηc) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (δ x : ℝ) (hx : x ≠ 0) : err ηs χ δ x = err ηc χ (δ / 49) (x / 49) / 49 := by
  have sc' : ∀ t : ℝ, ηs t = ηc (49 * t) := sc
  have h1 : ∀ n : ℕ, 49 * ((n : ℝ) / x) = (n : ℝ) / (x / 49) := fun n => by
    field_simp
  have h2 : δ / 49 / (x / 49) = δ / x := by
    field_simp
  have htw : twSum ηs χ x (δ / x) = twSum ηc χ (x / 49) (δ / 49 / (x / 49)) := by
    simp only [twSum, sc', h1, h2]
  have hc := integral_comp_mul_left_Ioi
    (fun u : ℝ => ((ηc u : ℝ) : ℂ) * e (δ / 49 * u)) 0 (by norm_num : (0 : ℝ) < 49)
  simp only [mul_zero] at hc
  have hft : mainFT ηs δ = mainFT ηc (δ / 49) / 49 := by
    unfold mainFT
    calc (∫ t in Set.Ioi (0 : ℝ), ((ηs t : ℝ) : ℂ) * e (δ * t))
        = ∫ t in Set.Ioi (0 : ℝ), ((ηc (49 * t) : ℝ) : ℂ) * e (δ / 49 * (49 * t)) := by
          congr 1
          funext t
          rw [sc', show δ / 49 * (49 * t) = δ * t by ring]
      _ = (49 : ℝ)⁻¹ • ∫ t in Set.Ioi (0 : ℝ), ((ηc t : ℝ) : ℂ) * e (δ / 49 * t) := hc
      _ = (∫ t in Set.Ioi (0 : ℝ), ((ηc t : ℝ) : ℂ) * e (δ / 49 * t)) / 49 := by
          rw [Complex.real_smul]
          push_cast
          ring
  unfold err
  rw [htw, hft]
  generalize twSum ηc χ (x / 49) (δ / 49 / (x / 49)) = T
  generalize mainFT ηc (δ / 49) = F
  split_ifs <;> push_cast <;> ring

/-- `gcd(n,2)` is `1` on odd `n` and `2` on even `n`. -/
theorem gcd_two (n : ℕ) : (Odd n ∧ Nat.gcd n 2 = 1) ∨ (Even n ∧ Nat.gcd n 2 = 2) := by
  rcases Nat.even_or_odd n with h | h
  · exact Or.inr ⟨h, Nat.gcd_eq_right (even_iff_two_dvd.mp h)⟩
  · exact Or.inl ⟨h, Nat.coprime_two_right.mpr h⟩

/-- The conductor `c | q` of a character on an arc of `𝔐_{8,150000}` lies in Thm 1.4's range, and
`gcd(q,2)/q ≤ gcd(c,2)/c` (an odd `c` dividing an even `q` has `q ≥ 2c`). -/
theorem cond_ok (q c : ℕ) (hcq : c ∣ q) (hq : 1 ≤ q)
    (hqr : q ≤ 150000 * Nat.gcd q 2) :
    (Odd c → c ≤ 150000) ∧ (Even c → c ≤ 300000) ∧ Nat.gcd q 2 * c ≤ Nat.gcd c 2 * q := by
  obtain ⟨m, rfl⟩ := hcq
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hq
      omega
    · exact h
  have hcm : c ≤ c * m := Nat.le_mul_of_pos_right c hm
  rcases gcd_two c with ⟨hco, hgc⟩ | ⟨hce, hgc⟩ <;>
    rcases gcd_two (c * m) with ⟨hqo, hgq⟩ | ⟨hqe, hgq⟩
  · rw [hgc, hgq]
    rw [hgq] at hqr
    generalize c * m = P at hqr hcm ⊢
    exact ⟨fun _ => by omega, fun _ => by omega, by omega⟩
  · rw [hgc, hgq]
    rw [hgq] at hqr
    have hme : Even m := by
      rcases Nat.even_mul.mp hqe with h | h
      · exact absurd h (Nat.not_even_iff_odd.mpr hco)
      · exact h
    have hm2 : 2 ≤ m := by
      obtain ⟨k, hk⟩ := hme
      omega
    have h2c : c * 2 ≤ c * m := Nat.mul_le_mul_left c hm2
    generalize c * m = P at hqr hcm h2c ⊢
    exact ⟨fun _ => by omega, fun _ => by omega, by omega⟩
  · exact absurd (Nat.even_mul.mpr (Or.inl hce)) (Nat.not_even_iff_odd.mpr hqo)
  · rw [hgc, hgq]
    rw [hgq] at hqr
    generalize c * m = P at hqr hcm ⊢
    exact ⟨fun h => absurd hce (Nat.not_even_iff_odd.mpr h), fun _ => by omega, by omega⟩

/-- The `δ`-range of an arc of modulus `q` lies inside Thm 1.4's range for its conductor `c`. -/
theorem delta_ok (q c : ℕ) (hq : 1 ≤ q) (hc : 1 ≤ c) (hg : Nat.gcd q 2 * c ≤ Nat.gcd c 2 * q)
    (δ : ℝ) (hδ : |δ| ≤ (Nat.gcd q 2 : ℝ) * 600000 / q) :
    |δ| ≤ 600000 * (Nat.gcd c 2 : ℝ) / c := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hc0 : (0 : ℝ) < c := Nat.cast_pos.mpr (by omega)
  have hgR : (Nat.gcd q 2 : ℝ) * c ≤ (Nat.gcd c 2 : ℝ) * q := by exact_mod_cast hg
  refine le_trans hδ ?_
  rw [div_le_div_iff₀ hq0 hc0]
  linarith

/-- `√c ≤ 547.7226` for `c ≤ 300000`. -/
theorem sqrt_c_le (c : ℕ) (hc : c ≤ 300000) : Real.sqrt (c : ℝ) ≤ 547.7226 := by
  have h : (c : ℝ) ≤ 300000 := by exact_mod_cast hc
  rw [Real.sqrt_le_left (by norm_num)]
  linarith [show (300000 : ℝ) ≤ 547.7226 ^ 2 by norm_num]

/-- `√c ≥ 1.41421` for `c ≥ 2`. -/
theorem sqrt_c_ge (c : ℕ) (hc : 2 ≤ c) : 1.41421 ≤ Real.sqrt (c : ℝ) := by
  have h : (2 : ℝ) ≤ c := by exact_mod_cast hc
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  linarith [show (1.41421 : ℝ) ^ 2 ≤ 2 by norm_num]

/-- The arithmetic of `eq:zakone2` for conductor `c = s² ≥ 2`:
`s·(6.18e-12/s + 1.14e-10/c + (499100/s + 52)/√x) ≤ 2.3921e-8` (`2.3920497e-8`). -/
theorem plus_num (c s w : ℝ) (hcs : s * s = c) (hs1 : 1.41421 ≤ s) (hs2 : s ≤ 547.7226)
    (hw : 22135943 * 10 ^ 6 ≤ w) :
    s * (6.18e-12 / s + 1.14e-10 / c + (499100 / s + 52) / w) ≤ 2.3921e-8 := by
  subst hcs
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs1
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have key : s * (6.18e-12 / s + 1.14e-10 / (s * s) + (499100 / s + 52) / w) =
      6.18e-12 + 1.14e-10 / s + (499100 + 52 * s) / w := by
    field_simp
  rw [key]
  have t1 : 1.14e-10 / s ≤ 1.14e-10 / 1.41421 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs1
  have t2 : (499100 + 52 * s) / w ≤ (499100 + 52 * 547.7226) / (22135943 * 10 ^ 6) := by
    rw [div_le_div_iff₀ hw0 (by norm_num)]
    nlinarith
  have t3 : (6.18e-12 : ℝ) + 1.14e-10 / 1.41421 +
      (499100 + 52 * 547.7226) / (22135943 * 10 ^ 6) ≤ 2.3921e-8 := by norm_num
  linarith

/-- The arithmetic of `eq:fabienne`, CORRECTED (correction 2), for conductor `c = s² ≥ 1`:
`s·((4.269e-14/c + (380600/s + 76)/(√x/7))/49) ≤ 1.3353e-7/49` (`1.33520e-7`). -/
theorem star_num (c s w : ℝ) (hcs : s * s = c) (hs1 : 1 ≤ s) (hs2 : s ≤ 547.7226)
    (hw : 22135943 * 10 ^ 6 ≤ w) :
    s * ((4.269e-14 / c + (380600 / s + 76) / (w / 7)) / 49) ≤ 1.3353e-7 / 49 := by
  subst hcs
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs1
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have key : s * ((4.269e-14 / (s * s) + (380600 / s + 76) / (w / 7)) / 49) =
      (4.269e-14 / s + 7 * (380600 + 76 * s) / w) / 49 := by
    field_simp
  rw [key]
  have t1 : 4.269e-14 / s ≤ 4.269e-14 := div_le_self (by norm_num) hs1
  have t2 : 7 * (380600 + 76 * s) / w ≤ 7 * (380600 + 76 * 547.7226) / (22135943 * 10 ^ 6) := by
    rw [div_le_div_iff₀ hw0 (by norm_num)]
    nlinarith
  have t3 : (4.269e-14 : ℝ) + 7 * (380600 + 76 * 547.7226) / (22135943 * 10 ^ 6) ≤ 1.3353e-7 := by
    norm_num
  have t4 : 4.269e-14 / s + 7 * (380600 + 76 * s) / w ≤ 1.3353e-7 := by linarith
  exact div_le_div_of_nonneg_right t4 (by norm_num)

/-- **`E_{η₊,150000,8} ≤ 2.3921e-8`** (`eq:zakone2`) from Thm 1.4, over every character on every
arc, through its conductor. PROVED. -/
theorem eb_plus (ηp : ℝ → ℝ) (h : Malpor ηp) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    EBound ηp x 2.3921e-8 := by
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
    have h2 : 251100 / Real.sqrt x ≤ 251100 / (22135943 * 10 ^ 6) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hw
    have h3 := hb.2 h1
    have h4 : (3.34e-11 : ℝ) + 251100 / (22135943 * 10 ^ 6) ≤ 2.3921e-8 := by norm_num
    linarith
  · have hc2 : 2 ≤ χ.conductor := by omega
    have hc3 : χ.conductor ≤ 300000 := by
      rcases Nat.even_or_odd χ.conductor with he | ho
      · exact hev he
      · exact le_trans (hodd ho) (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hb.1 (Real.sqrt_nonneg _))
      (plus_num _ _ _ (Real.mul_self_sqrt (Nat.cast_nonneg _)) (sqrt_c_ge _ hc2)
        (sqrt_c_le _ hc3) hw)

/-- `√(x/49) = √x/7`. -/
theorem sqrt_div49 (x : ℝ) (hx : 0 ≤ x) : Real.sqrt (x / 49) = Real.sqrt x / 7 := by
  rw [Real.sqrt_div hx, show (49 : ℝ) = 7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **`E_{η*,150000,8} ≤ 1.3353e-7/49`** from Cor 1.3 for the base `ηc` and `η*(t) = ηc(49t)`.
PROVED. Helfgott prints `1.9075e-8/49` (`eq:fabienne`), which misses the factor `√49 = 7`. -/
theorem eb_star (ηs ηc : ℝ → ℝ) (sc : StarScale ηs ηc) (h : Coprar ηc) (x : ℝ)
    (hx : 49 * 10 ^ 25 ≤ x) : EBound ηs x (1.3353e-7 / 49) := by
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
      ≤ Real.sqrt (χ.conductor : ℝ) * ((4.269e-14 / (χ.conductor : ℝ) +
          (380600 / Real.sqrt (χ.conductor : ℝ) + 76) / (Real.sqrt x / 7)) / 49) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb (by norm_num))
          (Real.sqrt_nonneg _)
    _ ≤ 1.3353e-7 / 49 :=
        star_num _ _ _ (Real.mul_self_sqrt (Nat.cast_nonneg _)) hs1 (sqrt_c_le _ hc3)
          (sqrt_x_ge x hx)

/-- **`ET_{η₊,600000} ≤ 1.1377e-8`** (`eq:zakone1`) from Thm 1.4 at `q = 1`. PROVED. -/
theorem et_plus (ηp : ℝ → ℝ) (h : Malpor ηp) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) :
    ETBound ηp 600000 x 1.1377e-8 := by
  intro δ hδ
  have hδ' : |δ| ≤ 600000 * (Nat.gcd 1 2 : ℝ) / ((1 : ℕ) : ℝ) := by
    simp only [Nat.gcd_one_left, Nat.cast_one, mul_one, div_one]
    exact hδ
  have hb := (h x (le_trans (by norm_num) hx) 1 le_rfl (fun _ => by norm_num)
    (fun _ => by norm_num) 1 DirichletCharacter.isPrimitive_one_level_one δ hδ').2 rfl
  have h2 : 251100 / Real.sqrt x ≤ 251100 / (22135943 * 10 ^ 6) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (sqrt_x_ge x hx)
  have h4 : (3.34e-11 : ℝ) + 251100 / (22135943 * 10 ^ 6) ≤ 1.1377e-8 := by norm_num
  linarith

/-- **`|err_{η*,χ_T}(0,x)| ≤ 1.71973e-8`** (`eq:julie`'s input) from Cor 1.3 at `q = 1` and the
scaling. PROVED, with room: the truth is `2.457e-9` (Helfgott's figure drops the `1/κ`). -/
theorem et0_star (ηs ηc : ℝ → ℝ) (sc : StarScale ηs ηc) (h : Coprar ηc) (x : ℝ)
    (hx : 49 * 10 ^ 25 ≤ x) : ‖err ηs (1 : DirichletCharacter ℂ 1) 0 x‖ ≤ 1.71973e-8 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hy : 10 ^ 8 ≤ x / 49 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hb := h (x / 49) hy 1 le_rfl (by norm_num) 1 DirichletCharacter.isPrimitive_one_level_one
    0 (by rw [abs_zero]; positivity)
  simp only [sqrt_div49 x hx0.le, Nat.cast_one, Real.sqrt_one, div_one] at hb
  rw [err_scale ηs ηc sc 1 0 x hx0.ne', zero_div, norm_div, Complex.norm_ofNat]
  have h2 : (380600 + 76) / (Real.sqrt x / 7) ≤ (380600 + 76) / (22135943 * 10 ^ 6 / 7) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [sqrt_x_ge x hx])
  have h3 : ((4.269e-14 : ℝ) + (380600 + 76) / (22135943 * 10 ^ 6 / 7)) / 49 ≤ 1.71973e-8 := by
    norm_num
  have h4 := div_le_div_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 49)
  linarith

/-- **`Z_{η₊²,2}(x) ≤ 0.640209 log x`** (`eq:malavita`) from Prop 1.5 and `Λ(n) ≤ log n`.
DISCHARGED. Prop 1.5 is two-sided, so it also forces the summability junk would hide. -/
theorem zplus (η : ℝ → ℝ) (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hm : MalheurAt η x) :
    zk (fun t => η t ^ 2) 2 x ≤ 0.640209 * Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hL := log_ge_one x hx
  have hu : 310.84 / Real.sqrt x ≤ 310.84 / (22135943 * 10 ^ 6) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (sqrt_x_ge x hx)
  have hP : x ≤ x * Real.log x := by nlinarith
  have hPu : 310.84 / Real.sqrt x * (x * Real.log x) ≤
      310.84 / (22135943 * 10 ^ 6) * (x * Real.log x) :=
    mul_le_mul_of_nonneg_right hu (by linarith)
  unfold MalheurAt at hm
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

/-! ## The closing arithmetic -/

/-- `0 ≤ |η|₁`. -/
theorem l1_nonneg (η : ℝ → ℝ) : 0 ≤ l1 η := integral_nonneg fun _ => abs_nonneg _

/-- `0 ≤ |η|₂`. -/
theorem l2_nonneg (η : ℝ → ℝ) : 0 ≤ l2 η := Real.sqrt_nonneg _

/-- `0 ≤ Z_{η²,2}(x)` for `x ≥ 0`. -/
theorem zk_sq_nonneg (η : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ zk (fun t => η t ^ 2) 2 x :=
  div_nonneg (tsum_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hx

/-- **The main term, from below**: `C₀·C ≥ 1.3203236·(1.2533139·0.8001287² − 0.000834)/49`. -/
theorem main_ge (s C0 Cc lo : ℝ) (hs1 : 1.2533139 ≤ s) (hC0 : 1.3203236 ≤ C0)
    (hCc : (s * lo ^ 2 - 0.000834) / 49 ≤ Cc) (hlo1 : 0.8001287 ≤ lo) :
    1.3203236 * ((1.2533139 * 0.8001287 ^ 2 - 0.000834) / 49) ≤ C0 * Cc := by
  have hlo2' : 0.8001287 ^ 2 ≤ lo ^ 2 := pow_le_pow_left₀ (by norm_num) hlo1 2
  have hslo : 1.2533139 * 0.8001287 ^ 2 ≤ s * lo ^ 2 :=
    mul_le_mul hs1 hlo2' (by norm_num) (by linarith)
  have hCc' : (1.2533139 * 0.8001287 ^ 2 - 0.000834) / 49 ≤ Cc :=
    le_trans (div_le_div_of_nonneg_right (by linarith) (by norm_num)) hCc
  exact mul_le_mul hC0 hCc' (by norm_num) (by linarith)

/-- **Line 1 of `eq:opus111`** at `ε₀ = 3.0371e-6`: at most `2.9387e-5·|η*|₁` (the source's
`2.9387e-5`, `ternvin.tex` 4787; exactly `2.9386952e-5`). -/
theorem line1_le (s lo l3 : ℝ) (hs1 : 1.2533139 ≤ s) (hs2 : s ≤ 1.2533143)
    (hlo1 : 0.8001287 ≤ lo) (hlo2 : lo ≤ 0.8001288) (hl3 : 0 ≤ l3) (hl3' : l3 ≤ 32.5023) :
    (2.82643 * lo ^ 2 * (2 + 3.0371e-6) * 3.0371e-6 +
        (4.31004 * lo ^ 2 + 0.0012 * l3 ^ 2 / 8 ^ 5) / 150000) * (s / 49) ≤
      2.9387e-5 * (1.2533143 / 49) := by
  have hlo2sq : lo ^ 2 ≤ 0.8001288 ^ 2 := pow_le_pow_left₀ (by linarith) hlo2 2
  have hl3sq : l3 ^ 2 ≤ 32.5023 ^ 2 := pow_le_pow_left₀ hl3 hl3' 2
  have hK : 2.82643 * lo ^ 2 * (2 + 3.0371e-6) * 3.0371e-6 +
      (4.31004 * lo ^ 2 + 0.0012 * l3 ^ 2 / 8 ^ 5) / 150000 ≤ 2.9387e-5 := by
    linarith
  exact mul_le_mul hK (div_le_div_of_nonneg_right hs2 (by norm_num))
    (div_nonneg (by linarith) (by norm_num)) (by norm_num)

/-- **Line 2 of `eq:opus111`** with the CORRECTED `E*` (correction 2): at most `2.78652e-6/49`
(Helfgott's printed `E*` gives `1.7815e-6/49`, `ternvin.tex` 4822). -/
theorem line2_le (A lp ls : ℝ) (hA : A ≤ 8.7806) (hlp : lp ≤ 0.800132) (hls0 : 0 ≤ ls)
    (hls : ls ^ 2 ≤ 1.77082 / 49) :
    1.3353e-7 / 49 * A + 2.3921e-8 * 1.6812 * (Real.sqrt A + 1.6812 * lp) * ls ≤
      1.3353e-7 / 49 * 8.7806 +
        2.3921e-8 * 1.6812 * ((2.96321 + 1.6812 * 0.800132) * 0.19011) := by
  have hsA : Real.sqrt A ≤ 2.96321 := by
    refine le_trans (Real.sqrt_le_sqrt hA) ?_
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hls' : ls ≤ 0.19011 := by nlinarith
  have hB' : Real.sqrt A + 1.6812 * lp ≤ 2.96321 + 1.6812 * 0.800132 := by linarith
  have hBl : (Real.sqrt A + 1.6812 * lp) * ls ≤ (2.96321 + 1.6812 * 0.800132) * 0.19011 :=
    mul_le_mul hB' hls' hls0 (by norm_num)
  linarith

/-- **Line 3 of `eq:opus111`** (`ternvin.tex` 4826–4835): at most `61 (log x)² x`, which is
`≤ 976 x^{3/2} ≤ 4.41·10⁻¹¹ x²` at `x ≥ 4.9·10²⁶`. -/
theorem line3_le (x Zp Zs : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hZp : Zp ≤ 0.640209 * Real.log x)
    (hZs0 : 0 ≤ Zs) (hZs : Zs ≤ 0.0362 * Real.log x) :
    (2 * Zp * (24.32 * Real.log x + 0.57) +
        4 * Real.sqrt (Zp * Zs) * (18.57 * Real.log x + 28.39)) * x ≤
      61 * 16 / (22135943 * 10 ^ 6) * x ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hL1 := log_ge_one x hx
  have hL0 : 0 ≤ Real.log x := by linarith
  have hZZ : Zp * Zs ≤ (0.15224 * Real.log x) ^ 2 :=
    calc Zp * Zs ≤ (0.640209 * Real.log x) * (0.0362 * Real.log x) :=
          mul_le_mul hZp hZs hZs0 (by linarith)
      _ = 0.0231755658 * Real.log x ^ 2 := by ring
      _ ≤ 0.0231770176 * Real.log x ^ 2 :=
          mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
      _ = (0.15224 * Real.log x) ^ 2 := by ring
  have hsZ : Real.sqrt (Zp * Zs) ≤ 0.15224 * Real.log x := by
    calc Real.sqrt (Zp * Zs) ≤ Real.sqrt ((0.15224 * Real.log x) ^ 2) := Real.sqrt_le_sqrt hZZ
      _ = 0.15224 * Real.log x := Real.sqrt_sq (by linarith)
  have h3a : 2 * Zp * (24.32 * Real.log x + 0.57) ≤
      2 * (0.640209 * Real.log x) * (24.32 * Real.log x + 0.57) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h3b : 4 * Real.sqrt (Zp * Zs) * (18.57 * Real.log x + 28.39) ≤
      4 * (0.15224 * Real.log x) * (18.57 * Real.log x + 28.39) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hLL : Real.log x ≤ Real.log x ^ 2 := by nlinarith only [hL1]
  have h3c : 2 * (0.640209 * Real.log x) * (24.32 * Real.log x + 0.57) +
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

/-- **The arithmetic of `ternvin.tex` 4772–4865**, on real variables: the `prop:nefumo` bound with
Helfgott's numbers (and the corrected `E*`) forces `Re ∫_𝔐 ≥ 1.058259 x²/49`. Margin `1.59e-7`. -/
theorem arith_close (x s C0 Cc lo l3 lp ls A Zp Zs : ℝ) (I : ℂ)
    (hx : 49 * 10 ^ 25 ≤ x) (hs1 : 1.2533139 ≤ s) (hs2 : s ≤ 1.2533143)
    (hC0 : 1.3203236 ≤ C0) (hCc : (s * lo ^ 2 - 0.000834) / 49 ≤ Cc)
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
    1.058259 * x ^ 2 / 49 ≤ I.re := by
  have hX : 0 ≤ x ^ 2 := sq_nonneg x
  have hm := mul_le_mul_of_nonneg_right (main_ge s C0 Cc lo hs1 hC0 hCc hlo1) hX
  have h1 := mul_le_mul_of_nonneg_right (line1_le s lo l3 hs1 hs2 hlo1 hlo2 hl3 hl3') hX
  have h2 := mul_le_mul_of_nonneg_right (line2_le A lp ls hA hlp hls0 hls) hX
  have h3 := line3_le x Zp Zs hx hZp hZs0 hZs
  have habs := Complex.abs_re_le_norm (I - ((C0 * Cc * x ^ 2 : ℝ) : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re] at habs
  have hlow := (abs_le.mp (le_trans habs hI)).1
  linarith only [hlow, hm, h1, h2, h3, hX]

/-! ## THE COMPOSITION -/

/-! The five facts below are split out so that `majorLower_of_links` contains no context-consuming
tactic: `check_unused_hypotheses.py` skips any proof that does, and the composition is the one
proof whose binders it must see. -/

/-- `x ≥ 10¹²`. -/
theorem x12_le (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : (10 : ℝ) ^ 12 ≤ x := le_trans (by norm_num) hx

/-- `x ≥ 0`. -/
theorem x_nonneg (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 0 ≤ x := le_trans (by norm_num) hx

/-- `N ≥ 1`. -/
theorem N_one (N : ℕ) (hN : 10 ^ 27 ≤ N) : 1 ≤ N := le_trans (by norm_num) hN

/-- `ε₀ = 3.0371e-6 ≥ 0`. -/
theorem eps_nonneg : (0 : ℝ) ≤ 3.0371e-6 := by norm_num

/-- `|η₊ − η∘|₂ ≤ 2.43e-6` and `|η∘|₂ ≥ 0.8001287` give the strict `|η₊ − η∘|₂ < ε₀|η∘|₂` that
`prop:nefumo` asks for, at `ε₀ = 3.0371e-6` (`3.0371e-6·0.8001287 = 2.4300709e-6`). -/
theorem eps_lt (a b : ℝ) (ha : a ≤ 2.43e-6) (hb : 0.8001287 ≤ b) : a < 3.0371e-6 * b := by
  linarith

/-- **The target, pinned**: `Smooth.MajorLowerSmooth` is, by `Iff.rfl`, (7.25) with the constant
`1.058259` and `κ = 49`, so the composition below cannot have drifted to a weaker constant. -/
theorem major_iff (ηp ηs : ℝ → ℝ) : Smooth.MajorLowerSmooth ηp ηs ↔
    (Spine.PlattGRH → ∀ N : ℕ, Odd N → 10 ^ 27 ≤ N →
      1.058259 * helfgottX N ^ 2 / 49 ≤
        (∫ α in Smooth.majorSet (helfgottX N), Smooth.kernS ηp ηs N (helfgottX N) α).re) :=
  Iff.rfl

/-- **THE SPINE of (7.25).** Helfgott's major-arc total, `ternvin.tex` 4458–4865, as function
application: HelfMaj (the only Platt consumer) gives the `err`-bounds and `Z₊`, `Drujal` gives
`A₊`, `ZStar` gives `Z*`, `LSLink` gives `LS`, `Nefumo` turns them into an error bound on
`∫_𝔐 − C₀C x²`, and `C0Lower`, `CLower`, `Norms` feed `arith_close`. -/
theorem majorLower_of_links (ηp ηs ηo ηc : ℝ → ℝ) (hm : HelfMaj ηp ηc)
    (sc : StarScale ηs ηc) (rg : Reg ηp ηs ηo) (nf : Nefumo ηp ηs ηo) (dj : Drujal ηp)
    (zs : ZStar ηs) (ls : LSLink ηp ηs) (c0 : C0Lower) (cl : CLower ηo ηs)
    (nm : Norms ηp ηs ηo) (sn : SupN ηp ηs) : Smooth.MajorLowerSmooth ηp ηs := by
  intro grh N hodd hN
  obtain ⟨mp, cp, mh⟩ := hm grh
  obtain ⟨hlo1, hlo2, hdiff, hl3, hld, hl1s, hls, hl1p, hl2p⟩ := nm
  have hx := helfX_big N hN
  have hEp := eb_plus ηp mp (helfgottX N) hx
  have hEs := eb_star ηs ηc sc cp (helfgottX N) hx
  have hET := et_plus ηp mp (helfgottX N) hx
  have hT0 := et0_star ηs ηc sc cp (helfgottX N) hx
  have hZp := zplus ηp (helfgottX N) hx (mh (helfgottX N) (x12_le _ hx))
  have hZs := zs sn.2.2.1 sn.2.2.2.2 hl1s (helfgottX N) hx hT0
  have hA := dj rg.2.2.1 sn.1 hl1p hl2p (helfgottX N) hx hET hEp
  obtain ⟨hLp, hLs⟩ := ls sn (helfgottX N) hx
  have hlt := eps_lt _ _ hdiff hlo1
  have hnef := nf rg 3.0371e-6 eps_nonneg hlt N (N_one N hN) (helfgottX N) hx
    2.3921e-8 (1.3353e-7 / 49) hEp hEs (18.57 * Real.log (helfgottX N) + 28.39)
    (24.32 * Real.log (helfgottX N) + 0.57) hLp hLs
  rw [hl1s] at hnef
  have hC := cl hld N hodd hN
  obtain ⟨hs1, hs2⟩ := sqrt_pi_half
  exact arith_close (helfgottX N) (Real.sqrt (Real.pi / 2)) (SingularSeries.sing3 N)
    (ccon ηo ηs ((N : ℝ) / helfgottX N)) (l2 ηo) (l1 (iteratedDeriv 3 ηo)) (l2 ηp) (l2 ηs)
    (amaj ηp (helfgottX N)) (zk (fun t => ηp t ^ 2) 2 (helfgottX N))
    (zk (fun t => ηs t ^ 2) 2 (helfgottX N)) _ hx hs1 hs2 (c0 N hodd) hC hlo1 hlo2
    (l1_nonneg _) hl3 hl2p (l2_nonneg _) hls hA hZp
    (zk_sq_nonneg _ _ (x_nonneg _ hx)) hZs hnef

/-! ## Link [LS], DISCHARGED -/

/-- `|η(t)| ≤ M'/t` from `|η(t)·t| ≤ M'`, `t > 0`. -/
theorem abs_le_div (η : ℝ → ℝ) (M' t : ℝ) (ht : 0 < t) (hM' : |η t * t| ≤ M') :
    |η t| ≤ M' / t := by
  rw [le_div_iff₀ ht]
  calc |η t| * t = |η t * t| := by rw [abs_mul, abs_of_pos ht]
    _ ≤ M' := hM'

/-- **`eq:alisa`, one prime**: `∑_{α≥1} |η(p^α/x)| ≤ (log x/log p)|η|_∞ + 2|η·t|_∞`, summable.
The `⌊log x/log p⌋` terms with `p^α < x` cost `|η|_∞` each; the rest form a geometric tail. -/
theorem ls_sum (η : ℝ → ℝ) (M M' x : ℝ) (p : ℕ) (hp : p.Prime) (hx : 1 ≤ x)
    (hM : ∀ t : ℝ, 0 ≤ t → |η t| ≤ M) (hM' : ∀ t : ℝ, 0 ≤ t → |η t * t| ≤ M') :
    Summable (fun k : ℕ => |η ((p : ℝ) ^ (k + 1) / x)|) ∧
      ∑' k : ℕ, |η ((p : ℝ) ^ (k + 1) / x)| ≤ Real.log x / Real.log p * M + 2 * M' := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hx0 : 0 < x := by linarith
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 le_rfl)
  have hM'0 : 0 ≤ M' := le_trans (abs_nonneg _) (hM' 0 le_rfl)
  set K := ⌊Real.log x / Real.log p⌋₊ with hK
  have hKle : (K : ℝ) ≤ Real.log x / Real.log p := Nat.floor_le (div_nonneg hlx hlp.le)
  have hKlt : Real.log x / Real.log p < K + 1 := Nat.lt_floor_add_one _
  have hpK : x ≤ (p : ℝ) ^ (K + 1) := by
    rw [← Real.log_le_log_iff hx0 (by positivity), Real.log_pow]
    have h := (div_lt_iff₀ hlp).mp hKlt
    push_cast
    linarith
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : (1 : ℝ) / p < 1 := by
    rw [div_lt_one hp0]
    linarith
  have hq1 : x / (p : ℝ) ^ (K + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hpK
  have htail : ∀ j : ℕ, |η ((p : ℝ) ^ (j + K + 1) / x)| ≤
      M' * (x / (p : ℝ) ^ (K + 1)) * (1 / (p : ℝ)) ^ j := by
    intro j
    have ht : 0 < (p : ℝ) ^ (j + K + 1) / x := by positivity
    refine le_trans (abs_le_div η M' _ ht (hM' _ ht.le)) (le_of_eq ?_)
    rw [pow_add, pow_add, one_div_pow]
    field_simp
    ring
  have hgeo : Summable (fun j : ℕ => M' * (x / (p : ℝ) ^ (K + 1)) * (1 / (p : ℝ)) ^ j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hts : Summable (fun j : ℕ => |η ((p : ℝ) ^ (j + K + 1) / x)|) :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) htail hgeo
  have hs : Summable (fun k : ℕ => |η ((p : ℝ) ^ (k + 1) / x)|) :=
    (summable_nat_add_iff (f := fun k : ℕ => |η ((p : ℝ) ^ (k + 1) / x)|) K).mp hts
  refine ⟨hs, ?_⟩
  have hhead : ∑ i ∈ Finset.range K, |η ((p : ℝ) ^ (i + 1) / x)| ≤ K * M := by
    calc ∑ i ∈ Finset.range K, |η ((p : ℝ) ^ (i + 1) / x)| ≤ ∑ _i ∈ Finset.range K, M :=
          Finset.sum_le_sum fun i _ => hM _ (by positivity)
      _ = K * M := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hinv : (1 - 1 / (p : ℝ))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    have : 1 / (p : ℝ) ≤ 1 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
    linarith
  have hinv0 : 0 ≤ (1 - 1 / (p : ℝ))⁻¹ := inv_nonneg.mpr (by linarith)
  have htl : ∑' j : ℕ, |η ((p : ℝ) ^ (j + K + 1) / x)| ≤ 2 * M' := by
    calc ∑' j : ℕ, |η ((p : ℝ) ^ (j + K + 1) / x)|
        ≤ ∑' j : ℕ, M' * (x / (p : ℝ) ^ (K + 1)) * (1 / (p : ℝ)) ^ j :=
          hts.tsum_le_tsum htail hgeo
      _ = M' * (x / (p : ℝ) ^ (K + 1)) * (1 - 1 / (p : ℝ))⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      _ ≤ M' * 1 * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hq1 hM'0) hinv hinv0 (by linarith)
      _ = 2 * M' := by ring
  have hKM : (K : ℝ) * M ≤ Real.log x / Real.log p * M := mul_le_mul_of_nonneg_right hKle hM0
  calc ∑' k : ℕ, |η ((p : ℝ) ^ (k + 1) / x)|
      = ∑ i ∈ Finset.range K, |η ((p : ℝ) ^ (i + 1) / x)| +
          ∑' j : ℕ, |η ((p : ℝ) ^ (j + K + 1) / x)| := (hs.sum_add_tsum_nat_add K).symm
    _ ≤ K * M + 2 * M' := add_le_add hhead htl
    _ ≤ Real.log x / Real.log p * M + 2 * M' := by linarith

set_option exponentiation.threshold 4000 in
/-- `log 150000 ≤ 11.91858`, from `150000¹⁹⁵ ≤ 2³³⁵³` and `log 2 < 0.6931471808`. (`norm_num` will
not expand `2³³⁵³` under the default exponent threshold `256`; hence the option.) -/
theorem log_r_le : Real.log 150000 ≤ 11.91858 := by
  have h1 : (150000 : ℝ) ^ 195 ≤ 2 ^ 3353 := by norm_num
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow, Real.log_pow] at h2
  have h3 := Real.log_two_lt_d9
  norm_num at h2
  linarith

/-- `e^{−3/2} ≤ 0.2232`, from `e^3 ≥ 2.7182818283³`. -/
theorem exp_neg_le : Real.exp (-3 / 2) ≤ 0.2232 := by
  have he := Real.exp_one_gt_d9
  have h3 : Real.exp (3 / 2) * Real.exp (3 / 2) = Real.exp 1 ^ 3 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    norm_num
  have he3 : (20.0855 : ℝ) ≤ Real.exp 1 ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) he.le 3
    linarith [show (20.0855 : ℝ) ≤ 2.7182818283 ^ 3 by norm_num]
  have hpos : 0 < Real.exp (3 / 2) := Real.exp_pos _
  have h4 : 4.4803 ≤ Real.exp (3 / 2) := by
    by_contra hlt
    have hlt' := not_le.mp hlt
    have := mul_lt_mul'' hlt' hlt' hpos.le hpos.le
    linarith
  rw [show (-3 / 2 : ℝ) = -(3 / 2) by norm_num, Real.exp_neg, inv_le_comm₀ hpos (by norm_num)]
  linarith [show (0.2232 : ℝ)⁻¹ ≤ 4.4803 by norm_num]

/-- **Link [LS] is a theorem**: `eq:alisa` from the sup norms, for every pair of weights. -/
theorem ls_link (ηp ηs : ℝ → ℝ) : LSLink ηp ηs := by
  intro sn x hx
  obtain ⟨hp1, hp2, hs1, hs2, -⟩ := sn
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hr := log_r_le
  have hl2 := Real.log_two_gt_d9
  have key : ∀ (η : ℝ → ℝ) (M M' : ℝ), (∀ t : ℝ, 0 ≤ t → |η t| ≤ M) →
      (∀ t : ℝ, 0 ≤ t → |η t * t| ≤ M') → ∀ p : ℕ, p.Prime →
      Summable (fun k : ℕ => |η ((p : ℝ) ^ (k + 1) / x)|) ∧
        Real.log 150000 * ∑' k : ℕ, |η ((p : ℝ) ^ (k + 1) / x)| ≤
          11.91858 * (Real.log x * 1.4426951 * M + 2 * M') := by
    intro η M M' hM hM' p hp
    obtain ⟨hsm, hle⟩ := ls_sum η M M' x p hp hx1 hM hM'
    refine ⟨hsm, ?_⟩
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 le_rfl)
    have hlp : Real.log 2 ≤ Real.log p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
    have hlp0 : 0 < Real.log p := by linarith
    have hq : Real.log x / Real.log p ≤ Real.log x * 1.4426951 := by
      rw [div_le_iff₀ hlp0]
      have h1 : 1 ≤ 1.4426951 * Real.log p := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hL
      linarith
    have hS0 : 0 ≤ ∑' k : ℕ, |η ((p : ℝ) ^ (k + 1) / x)| := tsum_nonneg fun _ => abs_nonneg _
    have e1 : ∑' k : ℕ, |η ((p : ℝ) ^ (k + 1) / x)| ≤ Real.log x * 1.4426951 * M + 2 * M' :=
      le_trans hle (by linarith [mul_le_mul_of_nonneg_right hq hM0])
    calc Real.log 150000 * ∑' k : ℕ, |η ((p : ℝ) ^ (k + 1) / x)|
        ≤ 11.91858 * ∑' k : ℕ, |η ((p : ℝ) ^ (k + 1) / x)| :=
          mul_le_mul_of_nonneg_right hr hS0
      _ ≤ 11.91858 * (Real.log x * 1.4426951 * M + 2 * M') :=
          mul_le_mul_of_nonneg_left e1 (by norm_num)
  constructor
  · intro p hp _
    obtain ⟨hsm, hle⟩ := key ηp 1.079955 1.19073 hp1 hp2 p hp
    exact ⟨hsm, by linarith⟩
  · intro p hp _
    have hM : ∀ t : ℝ, 0 ≤ t → |ηs t| ≤ 1.414 := fun t ht => by
      rw [abs_of_nonneg (hs1 t ht).1]
      exact (hs1 t ht).2
    have hM' : ∀ t : ℝ, 0 ≤ t → |ηs t * t| ≤ 3 * Real.sqrt 3 * Real.exp (-3 / 2) / 49 :=
      fun t ht => by
        rw [abs_of_nonneg (mul_nonneg (hs1 t ht).1 ht)]
        exact hs2 t ht
    obtain ⟨hsm, hle⟩ := key ηs 1.414 _ hM hM' p hp
    refine ⟨hsm, ?_⟩
    have hsq : Real.sqrt 3 ≤ 1.7321 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have h0 : 0 ≤ Real.exp (-3 / 2) := (Real.exp_pos _).le
    have hc0 := mul_le_mul hsq exp_neg_le h0 (by norm_num)
    have hc : 3 * Real.sqrt 3 * Real.exp (-3 / 2) / 49 ≤ 3 * 1.7321 * 0.2232 / 49 := by
      linarith
    linarith

/-- **The spine with [LS] discharged**: ten links instead of eleven. -/
theorem majorLower_ls (ηp ηs ηo ηc : ℝ → ℝ) (hm : HelfMaj ηp ηc)
    (sc : StarScale ηs ηc) (rg : Reg ηp ηs ηo) (nf : Nefumo ηp ηs ηo) (dj : Drujal ηp)
    (zs : ZStar ηs) (c0 : C0Lower) (cl : CLower ηo ηs) (nm : Norms ηp ηs ηo)
    (sn : SupN ηp ηs) : Smooth.MajorLowerSmooth ηp ηs :=
  majorLower_of_links ηp ηs ηo ηc hm sc rg nf dj zs (ls_link ηp ηs) c0 cl nm sn

/-! ## Link [Z*], DISCHARGED -/

/-- **Link [Z*] is a theorem** (`eq:bavette`, `eq:julie`), for every weight obeying its
hypotheses: `Λ²η*² ≤ Λη*·(η* log n)`, `η*(n/x) log n ≤ 0.732513 + 1.414 log(x/49)`, and
`∑Λ(n)η*(n/x) = x(|η*|₁ + err_{η*,χ_T}(0,x))` for `η* ≥ 0`. The `err`-bound also forces the
summability that junk would hide (else `err = −|η*|₁`). -/
theorem zstar_holds (ηs : ℝ → ℝ) : ZStar ηs := by
  intro h0 hlog hl1 x hx hT
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hL1 := log_ge_one x hx
  obtain ⟨hs1, hs2⟩ := sqrt_pi_half
  have he0 : ∀ y : ℝ, y = 0 → e y = 1 := fun y hy => by
    rw [hy]
    simp [e]
  have htw : twSum ηs (1 : DirichletCharacter ℂ 1) x (0 / x) =
      ((∑' n : ℕ, Λ n * ηs ((n : ℝ) / x) : ℝ) : ℂ) := by
    rw [zero_div, Complex.ofReal_tsum]
    unfold twSum
    congr 1
    funext n
    rw [MulChar.one_apply (isUnit_of_subsingleton _), he0 _ (mul_zero _), Complex.ofReal_mul]
    ring
  have hft : mainFT ηs 0 = ((l1 ηs : ℝ) : ℂ) := by
    unfold mainFT l1
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [he0 _ (zero_mul t), mul_one, abs_of_nonneg (h0 t (le_of_lt ht)).1]
  have herr : err ηs (1 : DirichletCharacter ℂ 1) 0 x =
      (((∑' n : ℕ, Λ n * ηs ((n : ℝ) / x)) / x - l1 ηs : ℝ) : ℂ) := by
    unfold err
    rw [htw, hft, if_pos (rfl : (1 : ℕ) = 1), Complex.ofReal_sub, Complex.ofReal_div]
  rw [herr, Complex.norm_real, Real.norm_eq_abs] at hT
  have hT' := abs_le.mp hT
  have hl1lo : 1.2533139 / 49 ≤ l1 ηs := by
    rw [hl1]
    exact div_le_div_of_nonneg_right hs1 (by norm_num)
  have hl1up : l1 ηs ≤ 1.2533143 / 49 := by
    rw [hl1]
    exact div_le_div_of_nonneg_right hs2 (by norm_num)
  have has : Summable (fun n : ℕ => Λ n * ηs ((n : ℝ) / x)) := by
    by_contra hns
    have h1 := hT'.1
    rw [tsum_eq_zero_of_not_summable hns, zero_div] at h1
    linarith
  have hlog49 : 1 ≤ Real.log 49 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hxl : Real.log (x / 49) ≤ Real.log x - 1 := by
    rw [Real.log_div hx0.ne' (by norm_num)]
    linarith
  have hxl0 : 0 ≤ Real.log (x / 49) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hterm : ∀ n : ℕ, Λ n ^ 2 * ηs ((n : ℝ) / x) ^ 2 ≤
      (0.732513 + 1.414 * (Real.log x - 1)) * (Λ n * ηs ((n : ℝ) / x)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · have ht : 0 < (n : ℝ) / x := div_pos (Nat.cast_pos.mpr hn) hx0
      obtain ⟨hη0, hη1⟩ := h0 _ ht.le
      have hΛ : Λ n ≤ Real.log n := vonMangoldt_le_log
      have hΛ0 : 0 ≤ Λ n := vonMangoldt_nonneg
      have h49 : (49 : ℝ) * ((n : ℝ) / x) * (x / 49) = n := by
        field_simp
      have hsplit : Real.log n = Real.log (49 * ((n : ℝ) / x)) + Real.log (x / 49) := by
        rw [← Real.log_mul (mul_pos (by norm_num) ht).ne' (div_pos hx0 (by norm_num)).ne', h49]
      have hA : ηs ((n : ℝ) / x) * Real.log (49 * ((n : ℝ) / x)) ≤ 0.732513 :=
        le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hη0) (hlog _ ht.le)
      have hB : ηs ((n : ℝ) / x) * Real.log (x / 49) ≤ 1.414 * (Real.log x - 1) :=
        le_trans (mul_le_mul_of_nonneg_right hη1 hxl0)
          (mul_le_mul_of_nonneg_left hxl (by norm_num))
      have hηlog : ηs ((n : ℝ) / x) * Real.log n ≤ 0.732513 + 1.414 * (Real.log x - 1) := by
        rw [hsplit, mul_add]
        linarith
      have hΛη : Λ n * ηs ((n : ℝ) / x) ≤ ηs ((n : ℝ) / x) * Real.log n := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hΛ hη0
      have hprod0 : 0 ≤ Λ n * ηs ((n : ℝ) / x) := mul_nonneg hΛ0 hη0
      calc Λ n ^ 2 * ηs ((n : ℝ) / x) ^ 2
          = (Λ n * ηs ((n : ℝ) / x)) * (Λ n * ηs ((n : ℝ) / x)) := by ring
        _ ≤ (Λ n * ηs ((n : ℝ) / x)) * (0.732513 + 1.414 * (Real.log x - 1)) :=
            mul_le_mul_of_nonneg_left (le_trans hΛη hηlog) hprod0
        _ = (0.732513 + 1.414 * (Real.log x - 1)) * (Λ n * ηs ((n : ℝ) / x)) := by ring
  have hC0 : 0 ≤ 0.732513 + 1.414 * (Real.log x - 1) := by linarith
  have hbs : Summable (fun n : ℕ => Λ n ^ 2 * ηs ((n : ℝ) / x) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hterm
      (has.mul_left _)
  have hle : ∑' n : ℕ, Λ n ^ 2 * ηs ((n : ℝ) / x) ^ 2 ≤
      (0.732513 + 1.414 * (Real.log x - 1)) * ∑' n : ℕ, Λ n * ηs ((n : ℝ) / x) := by
    rw [← tsum_mul_left]
    exact hbs.tsum_le_tsum hterm (has.mul_left _)
  have hsum : ∑' n : ℕ, Λ n * ηs ((n : ℝ) / x) ≤ (1.2533143 / 49 + 1.71973e-8) * x := by
    have h1 : (∑' n : ℕ, Λ n * ηs ((n : ℝ) / x)) / x ≤ 1.2533143 / 49 + 1.71973e-8 := by
      linarith [hT'.2]
    exact (div_le_iff₀ hx0).mp h1
  have hfin := mul_le_mul_of_nonneg_left hsum hC0
  have hLx : 0 ≤ Real.log x * x := mul_nonneg (by linarith) hx0.le
  unfold zk
  change (∑' n : ℕ, Λ n ^ 2 * ηs ((n : ℝ) / x) ^ 2) / x ≤ _
  rw [div_le_iff₀ hx0]
  linarith

/-- **The spine with [LS] and [Z*] discharged**: nine links. -/
theorem majorLower_lz (ηp ηs ηo ηc : ℝ → ℝ) (hm : HelfMaj ηp ηc)
    (sc : StarScale ηs ηc) (rg : Reg ηp ηs ηo) (nf : Nefumo ηp ηs ηo) (dj : Drujal ηp)
    (c0 : C0Lower) (cl : CLower ηo ηs) (nm : Norms ηp ηs ηo) (sn : SupN ηp ηs) :
    Smooth.MajorLowerSmooth ηp ηs :=
  majorLower_ls ηp ηs ηo ηc hm sc rg nf dj (zstar_holds ηs) c0 cl nm sn

/-! ## THE ADVERSARIAL PASS: what the zero weights satisfy -/

/-- `|0|₂ = 0`. -/
theorem l2_zero : l2 0 = 0 := by simp [l2]

/-- `err_{0,χ} ≡ 0`. -/
theorem err_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (δ x : ℝ) : err 0 χ δ x = 0 := by
  simp [err, twSum, mainFT]

/-- **Zero weights pass eight of the links**: `Nefumo` (vacuously: `|0 − 0|₂ < ε₀·|0|₂` is false),
`Drujal`, `ZStar`, `CLower`, `SupN`, `StarScale`, and Thm 1.4 / Cor 1.3. So none of these forces
the weights to be nondegenerate. -/
theorem zero_rest : Nefumo 0 0 0 ∧ Drujal 0 ∧ ZStar 0 ∧ CLower 0 0 ∧ SupN 0 0 ∧
    StarScale 0 0 ∧ Malpor 0 ∧ Coprar 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun t => rfl, ?_, ?_⟩
  · intro _ ε₀ _ hlt
    simp [l2] at hlt
  · intro _ _ _ _ x _ _ _
    have h : amaj 0 x = 0 := by simp [amaj, Smooth.smSum_zero]
    rw [h]
    norm_num
  · intro _ _ _ x hx _
    have h : zk (fun t => (0 : ℝ → ℝ) t ^ 2) 2 x = 0 := by simp [zk]
    rw [h]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (le_trans (by norm_num) hx))
  · intro _ N _ _
    have h : ccon 0 0 ((N : ℝ) / helfgottX N) = 0 := by simp [ccon]
    rw [h, l2_zero]
    norm_num
  · refine ⟨fun t _ => by norm_num, fun t _ => by norm_num, fun t _ => by norm_num,
      fun t _ => ?_, fun t _ => by norm_num⟩
    simp only [Pi.zero_apply, zero_mul]
    positivity
  · intro x _ q _ _ _ χ _ δ _
    rw [err_zero, norm_zero]
    exact ⟨by positivity, fun _ => by positivity⟩
  · intro x _ q _ _ χ _ δ _
    rw [err_zero, norm_zero]
    positivity

/-- **`Norms` rejects `η∘ = 0`** (`|η∘|₂ ≥ 0.8001287`). -/
theorem norms_zero_o (ηp ηs : ℝ → ℝ) : ¬ Norms ηp ηs 0 := by
  intro h
  have h1 := h.1
  rw [l2_zero] at h1
  norm_num at h1

/-- **HelfMaj Prop 1.5 rejects `η₊ = 0`**: it is a two-sided asymptotic, `≈ 0.64 x log x`. So,
under Platt, `HelfMaj 0 _` fails too; `Norms` and `HelfMaj` are where nondegeneracy lives. -/
theorem malheur_zero : ¬ Malheur 0 := by
  intro h
  have hm := h (10 ^ 12) le_rfl
  unfold MalheurAt at hm
  have h0 : (∑' n : ℕ, Λ n * Real.log n * (0 : ℝ → ℝ) ((n : ℝ) / 10 ^ 12) ^ 2) = 0 := by simp
  have hs : Real.sqrt ((10 : ℝ) ^ 12) = 10 ^ 6 := by
    rw [show (10 : ℝ) ^ 12 = (10 ^ 6) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hL : 1 ≤ Real.log ((10 : ℝ) ^ 12) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    have h12 : (2.7182818286 : ℝ) ≤ 10 ^ 12 := by norm_num
    linarith
  have hc1 : (2e-6 + 310.84 / 10 ^ 6 : ℝ) * 10 ^ 12 = 312840000 := by norm_num
  have hc2 : (0.640206 : ℝ) * 10 ^ 12 = 640206000000 := by norm_num
  have hc3 : (0.021095 : ℝ) * 10 ^ 12 = 21095000000 := by norm_num
  rw [h0, hs, hc1, hc2, hc3] at hm
  have h1 := (abs_le.mp hm).1
  linarith

end Principia.Common.TernaryGoldbach.MajSp
