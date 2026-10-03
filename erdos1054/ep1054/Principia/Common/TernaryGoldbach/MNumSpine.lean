/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.LamberW

set_option autoImplicit false

/-!
# The spine of `MinW.MNumW HW.phi 0.785` (`eq:bustier` on Helfgott's `φ`), at the floor `p ≥ 8.36`

**This file proves the COMPOSITION. Every link of the envelope route (`mnumAt_of_links2`) is
DISCHARGED in `MNumProofs.lean`: `MN.mnumW_proved : MinW.MNumW HW.phi 0.785`, no hypotheses.**
Only `T1Anti` (exact monotonicity of `t1`, used by the first route `mnumAt_of_links`) is unproved,
and nothing depends on it.

`MinW.MNumW φ 0.785` asks for `M ≤ 0.785` at every `x ≥ 4.9·10²⁶`, `0 ≤ s ≤ felipa(x)`,
`p ≥ 8.6129`, where (`y = x/49`, `g = gB φ y`, `eq:basia`)
`M = g(r₀)·(H(r₀)·s − p) + (2/(log x + 2c⁻)·∫_{r₀}^{r₁} g/r + coefC(x)·g(r₁))·s`.
It is stated here at the floor `p ≥ 8.36` (`MNumAt 8.36 0.785`), which implies the `8.6129`
statement (`mnumW_of_at`): the in-flight `lem:drujal` round may lower the floor to about `8.36`.

## The route (`scratchpad/minsp/mn_design.py`, `mn_consts.py`, `mn_check2.py`; `g` exact)

1. **Affine reduction (DISCHARGED, `mnumAt_of_felipa`).** `M` is affine in `p` with coefficient
   `−g(r₀) ≤ 0` (`G0Nonneg`) and affine in `s`, so on `s ∈ [0, felipa]` it is at most
   `max(M(0), M(felipa))`, and `M(0, p₀) = −g(r₀)p₀ ≤ 0`. What remains is a function of `x`:
   `g(r₀)(hs(x) − p₀) + t1(x) + cas(x)·∫g/r`.
2. **Partition** `y ∈ [10²⁵, 3·10²⁵], [3·10²⁵, 10²⁶], [10²⁶, 2·10²⁶]` and the tail `y ≥ 2·10²⁶`
   (`x = 49y`). On a block `[x_a, x_b]`: `g(r₀) ≤ G` (`G0Env`), `hs ≤ hs(x_b)` (`hs` increases,
   DISCHARGED), `t1 ≤ t1(x_a)` (`T1Anti`), `cas ≤ cas(x_b)` (DISCHARGED), `∫g/r ≤ I` (`IGBlk`).
   On the tail `hs ≤ 1.280418·(log 150001 + 2.3912) ≤ 18.323` and `cas ≤ 1.280418` (DISCHARGED).

| region `y` | `G` | `hs(x_b)` | `T` | `cas(x_b)` | `I` | bound on `M` | exact `M` at the ends |
|---|---|---|---|---|---|---|---|
| `[1e25, 3e25]` | `0.0412` | `17.952` | `0.2865` | `1.2546` | `0.074` | `0.774531` | `0.75329` |
| `[3e25, 1e26]` | `0.0409` | `17.9585` | `0.2565` | `1.2551` | `0.0785` | `0.747604` | `0.72460` |
| `[1e26, 2e26]` | `0.0406` | `17.9625` | `0.227` | `1.2554` | `0.080` | `0.717294` | `0.69630` |
| `≥ 2e26` | `0.0404` | `18.323` | `0.2115` | `1.280418` | `0.115` | `0.761253` | — |

Exact values on Helfgott's `φ` (mpmath, 40 digits): `g(r₀)` at `y = 10²⁵, 3·10²⁵, 10²⁶, 2·10²⁶`
is `0.0410123, 0.0406521, 0.0402912, 0.0400978`; `t1` at the four left ends
`0.2805546, 0.2507148, 0.2215798, 0.2063369`; `sup ∫g/r` on the blocks `≤ 0.066936, 0.070114,
0.071704`, and `≈ 0.0820` on the tail.

**A correction to the brief.** Its tail bound `sup(hs) < 14.20840·2·0.640209` misreads
`log 150001 + 2.3912 = 14.30960`; the supremum of `hs` is `1.280418·14.30960 = 18.32227`. The
tail still closes (`0.761253`).

## The level-2 sub-links, each true on Helfgott's `φ`

* `RKBnd y_a t_b ρ` (`R_{y,K,φ,t} ≤ ρ` for `y ≥ y_a`, `1 ≤ t ≤ t_b`) from the generic `RKMono`
  (`R` increases in `t` and decreases in `z`; `y/K` increases; the mixing weight
  `C_{φ,2,K}/(|φ|₁ log K)` lies in `[0, (1/9)/(|φ|₁ log K)]`) and the numeric `RKCeil`.
* `EnvPt`: `g(y,r) ≤ envQ ρ r + f₂(y)` for `r ≥ r₀`, `R_{y,K,φ,2r} ≤ ρ`. `√F` by a tangent,
  `log log r` by its tangent at `11.9184`, `2.50637/log log r` at `r₀`, `e^γ ≤ 1.7881`,
  `1/√2 ≤ 0.70711`. On a grid, `max g/(envQ + f₂) = 0.99857` at `ρ = R_{y,K,φ,2r}` exactly.
* `EnvDeriv`: `PhiQ ρ` is an antiderivative of `envQ ρ r / r` (closed form). `F2Anti`: `f₂`
  decreases.
* Numerics: `RKCeil`, `G0Num`, `T1EnvNum`, `R1Le`, `IBlkNum`, `F2Tail`, `ITailNum`; margins are in
  their docstrings and in `MNumProofs.lean`.
* `T1Anti` (`t1` decreases; `t1_rates.py`) and `RKTail` (`R_{y,K,φ,2r} ≤ 0.72` on the tail; the
  sampled max is `0.71391`).
* **The envelope route for `T₁`** (`mnumAt_of_links2`): `T1Reg` on the three blocks and `T1Far` on
  `x ≥ 9.8·10²⁷`, from `EnvAnti` (`envQ ρ` decreases in `r`), `coefC·felipa` increasing, and
  `T1BNum` (block values `0.29309, 0.26303, 0.22922, 0.23045`), plus a crude `K`-power bound
  (`0.20368`) for `x ≥ 4.9·10²⁸`. It replaces `T1Anti` + `T1Num`; the closing arithmetic becomes
  `0.783530, 0.757602, 0.722794, 0.784753 ≤ 0.785`.
-/

namespace Principia.Common.TernaryGoldbach.MN

open MinSp Finset

/-! ## (1) The quantities -/

/-- **`felipa(x) = 0.640209 log x − 0.021095`** (the range of `s = S/x`). -/
noncomputable def fel (x : ℝ) : ℝ := 0.640209 * Real.log x - 0.021095

/-- **`H(r₀)·felipa(x)`**: the coefficient of `g(r₀)` at `s = felipa(x)`. -/
noncomputable def hs (x : ℝ) : ℝ := hR0 x * fel x

/-- **`2 felipa(x)/(log x + 2c⁻)`** (`eq:casbah`'s factor at `s = felipa(x)`). -/
noncomputable def cas (x : ℝ) : ℝ := 2 / (Real.log x + 2 * 0.6294) * fel x

/-- **`T₁(x) = coefC(x)·g(r₁)·felipa(x)`** (`eq:comrade` at `s = felipa(x)`). -/
noncomputable def t1 (x : ℝ) : ℝ := coefC x * gB HW.phi (x / 49) (r1y (x / 49)) * fel x

/-- **`f₂(y) = 3.2 K^{1/6} y^{−1/6}`**, the last term of `g` (`eq:basia`), `K = (log y)/2`. -/
noncomputable def f2 (y : ℝ) : ℝ := 3.2 * kK y ^ ((1 : ℝ) / 6) * y ^ (-(1 : ℝ) / 6)

/-- The quadratic `P(ℓ) = (ρ(0.6931471808 + ℓ) + ½)(1.949682 + 0.032156ℓ) + 5/2`: the numerator
of `g`'s first term with `log 2r ≤ 0.6931471808 + ℓ`, `R ≤ ρ` and `√F ≤ 1.949682 + 0.032156ℓ`. -/
noncomputable def pA (ρ l : ℝ) : ℝ :=
  (ρ * (0.6931471808 + l) + 0.5) * (1.949682 + 0.032156 * l) + 2.5

/-- `P′(ℓ)`. -/
noncomputable def dpA (ρ l : ℝ) : ℝ :=
  ρ * (1.949682 + 0.032156 * l) + (ρ * (0.6931471808 + l) + 0.5) * 0.032156

/-- `P″`. -/
noncomputable def ddpA (ρ : ℝ) : ℝ := 2 * ρ * 0.032156

/-- The quadratic `Q(ℓ)`: `L_r` (`eq:veror`) with `F ≤ 3.6544 + 0.15003ℓ`,
`log 2 ≤ 0.6931471808`. -/
noncomputable def qA (l : ℝ) : ℝ :=
  (3.6544 + 0.15003 * l) * (7 / 4 * 0.6931471808 + 13 / 4 * l + 80 / 9) +
    16 / 9 * 0.6931471808 + 80 / 9 * l + 111 / 5

/-- `Q′(ℓ)`. -/
noncomputable def dqA (l : ℝ) : ℝ :=
  0.15003 * (7 / 4 * 0.6931471808 + 13 / 4 * l + 80 / 9) +
    (3.6544 + 0.15003 * l) * (13 / 4) + 80 / 9

/-- `Q″`. -/
noncomputable def ddqA : ℝ := 2 * 0.15003 * (13 / 4)

/-- **The envelope of `g(y, ·)` less `f₂`**: `0.70711·P(log r)/√r + Q(log r)/r`
(`1/√2 ≤ 0.70711`). -/
noncomputable def envQ (ρ r : ℝ) : ℝ :=
  0.70711 * pA ρ (Real.log r) / Real.sqrt r + qA (Real.log r) / r

/-- **Its antiderivative against `dr/r`**: `−2·0.70711·(P + 2P′ + 4P″)/√r − (Q + Q′ + Q″)/r`
(`d/dr` of it is `envQ ρ r / r`: `EnvDeriv`). -/
noncomputable def PhiQ (ρ r : ℝ) : ℝ :=
  -(2 * 0.70711) * (pA ρ (Real.log r) + 2 * dpA ρ (Real.log r) + 4 * ddpA ρ) / Real.sqrt r -
    (qA (Real.log r) + dqA (Real.log r) + ddqA) / r

/-- **The block ceiling of `R_{y,K,φ,t}`** (`eq:basia`): `R_{y_a,t_b} + c_max(R_{y_a/K_a,t_b} −
R_{y_a,t_b})`, `c_max = (1/9)/(|φ|₁ log K_a)`, `|φ|₁ = √(π/2)`. -/
noncomputable def rKB (ya tb : ℝ) : ℝ :=
  rR ya tb + 1 / 9 / (Real.sqrt (Real.pi / 2) * Real.log (kK ya)) *
    (rR (ya / kK ya) tb - rR ya tb)

/-! ## (2) The target -/

/-- **`eq:bustier` on Helfgott's `φ` at the floor `p₀`**: `MinW.MNumW HW.phi c` with `8.6129`
replaced by `p₀`. -/
def MNumAt (p0 c : ℝ) : Prop :=
  ∀ x : ℝ, 49 * 10 ^ 25 ≤ x → ∀ s p : ℝ, 0 ≤ s → s ≤ 0.640209 * Real.log x - 0.021095 →
    p0 ≤ p →
      gB HW.phi (x / 49) 150000 * (hR0 x * s - p) +
          (2 / (Real.log x + 2 * 0.6294) * intG HW.phi (x / 49) +
            coefC x * gB HW.phi (x / 49) (r1y (x / 49))) * s ≤ c

/-! ## (3) The level-1 links -/

/-- **[G0Nonneg] `g(r₀) ≥ 0`** for `y ≥ 10²⁵` (`g` bounds a supremum of absolute values; `MNumW`
itself forces it, `MinW.mnumW_nonneg`). -/
def G0Nonneg : Prop := ∀ y : ℝ, 10 ^ 25 ≤ y → 0 ≤ gB HW.phi y 150000

/-- **[G0Env] `g(y, r₀) ≤ G` for every `y ≥ y_a`** (a monotone envelope; `g(y, r₀)` decreases from
`0.0410123` at `10²⁵`). Instances `(10²⁵, 0.0412)`, `(3·10²⁵, 0.0409)`, `(10²⁶, 0.0406)`,
`(2·10²⁶, 0.0404)`. Reduced to `RKBnd`, `EnvPt`, `F2Anti`, `G0Num`. -/
def G0Env (ya G : ℝ) : Prop := ∀ y : ℝ, ya ≤ y → gB HW.phi y 150000 ≤ G

/-- **[T1Anti] `t1` decreases on `x ≥ 4.9·10²⁶`** (`t1_rates.py`: in `v = log y` every term's
log-derivative is `≤ −0.0987`; the growing numerator's is `≤ 0.0347 < 2/15`). -/
def T1Anti : Prop := ∀ x x' : ℝ, 49 * 10 ^ 25 ≤ x → x ≤ x' → t1 x' ≤ t1 x

/-- **[T1Num] `t1(x_a) ≤ T`**. Instances (exact value): `(4.9·10²⁶, 0.2865)` (`0.2805546`),
`(1.47·10²⁷, 0.2565)` (`0.2507148`), `(4.9·10²⁷, 0.227)` (`0.2215798`), `(9.8·10²⁷, 0.2115)`
(`0.2063369`). Reduced to `RKBnd`, `EnvPt`, `R1Le`, `T1EnvNum`. -/
def T1Num (xa T : ℝ) : Prop := t1 xa ≤ T

/-- **[IGBlk] `∫_{r₀}^{r₁(y)} g(y,r)/r dr ≤ I` for `y ∈ [y_a, y_b]`.** Instances (exact sup):
`(10²⁵, 3·10²⁵, 0.074)` (`0.066936`), `(3·10²⁵, 10²⁶, 0.0785)` (`0.070114`),
`(10²⁶, 2·10²⁶, 0.080)` (`0.071704`). Reduced to `RKBnd`, `EnvPt`, `EnvDeriv`, `F2Anti`, `R1Le`,
`IBlkNum`. -/
def IGBlk (ya yb I : ℝ) : Prop := ∀ y : ℝ, ya ≤ y → y ≤ yb → intG HW.phi y ≤ I

/-- **[IGTail] `∫_{r₀}^{r₁(y)} g/r ≤ I` for every `y ≥ y_a`.** Instance `(2·10²⁶, 0.115)` (the exact
supremum over `y ≥ 2·10²⁶` is `≈ 0.0820`, near `y = 10³⁵`). Reduced to `RKTail`, `EnvPt`,
`EnvDeriv`, `F2Tail`, `ITailNum`. -/
def IGTail (ya I : ℝ) : Prop := ∀ y : ℝ, ya ≤ y → intG HW.phi y ≤ I

/-- **[T1Reg] `t1(x) ≤ T` on `[x_a, x_b]`** — the envelope route for `T₁`, which replaces
`T1Anti` + `T1Num` (`t1Reg_of_anti` shows the old pair implies it). Instances (envelope value):
`(4.9·10²⁶, 1.47·10²⁷, 0.2955)` (`0.29307`), `(1.47·10²⁷, 4.9·10²⁷, 0.2665)` (`0.26301`),
`(4.9·10²⁷, 9.8·10²⁷, 0.2325)` (`0.22921`), `(9.8·10²⁷, 4.9·10²⁸, 0.235)` (`0.23044`). -/
def T1Reg (xa xb T : ℝ) : Prop := ∀ x : ℝ, xa ≤ x → x ≤ xb → t1 x ≤ T

/-- **[T1Far] `t1(x) ≤ T` for every `x ≥ x_a`.** Instances `(4.9·10²⁸, 0.235)` (crude
`K`-power bound `0.2036`) and, with the block before it, `(9.8·10²⁷, 0.235)`. -/
def T1Far (xa T : ℝ) : Prop := ∀ x : ℝ, xa ≤ x → t1 x ≤ T

/-! ## (4) The level-2 links -/

/-- **[RKBnd] `R_{y,K,φ,t} ≤ ρ` for every `y ≥ y_a` and `1 ≤ t ≤ t_b`** (`eq:basia`,
`K = (log y)/2`). -/
def RKBnd (ya tb ρ : ℝ) : Prop :=
  ∀ y t : ℝ, ya ≤ y → 1 ≤ t → t ≤ tb → rRK HW.phi y t ≤ ρ

/-- **[RKCeil] the numeric ceiling at `(y_a, t_b)`**: `2.004 t_b < 9(y_a/K_a)^{1/3}` (every
logarithm inside `R` is then positive on the range) and `rKB y_a t_b ≤ ρ`. -/
def RKCeil (ya tb ρ : ℝ) : Prop :=
  2.004 * tb < 9 * (ya / kK ya) ^ ((1 : ℝ) / 3) ∧ rKB ya tb ≤ ρ

/-- **[RKNum] the numeric half of `RKCeil`**: `rKB y_a t_b ≤ ρ`. (The other half,
`2.004 t_b < 9(y_a/K_a)^{1/3}`, holds for every `y_a ≥ 10²⁵`, `t_b ≤ 8.9·10⁶`: `MN.pre_ok`.)
Instances (`rKB` exactly; margin): `(10²⁵, 3·10⁵, 0.5845)` (`0.5839195`, `5.8·10⁻⁴`),
`(3·10²⁵, 3·10⁵, 0.579)` (`0.5783680`), `(10²⁶, 3·10⁵, 0.5735)` (`0.5726981`),
`(2·10²⁶, 3·10⁵, 0.5705)` (`0.5696127`); `(10²⁵, 4.68·10⁶, 0.672)` (`0.6713041`),
`(3·10²⁵, 6.44·10⁶, 0.674)` (`0.6729772`), `(10²⁶, 7.74·10⁶, 0.669)` (`0.6681350`);
`(10²⁵, 3481200, 0.66)` (`0.6594718`), `(3·10²⁵, 4666200, 0.661)` (`0.6602212`),
`(10²⁶, 6432800, 0.6615)` (`0.6610183`), `(2·10²⁶, 7738800, 0.662)` (`0.6614659`). -/
def RKNum (ya tb ρ : ℝ) : Prop := rKB ya tb ≤ ρ

/-- **[RKMono] the block ceiling is a ceiling** (generic analysis of `eq:veror`, `eq:basia`):
`R_{z,t}` increases in `t` and decreases in `z` while `9z^{1/3} > 2.004t`; `y/K(y)` increases;
`R_{y,K,φ,t} = (1 − c)R_{y,t} + c R_{y/K,t}` with `0 ≤ c ≤ (1/9)/(|φ|₁ log K) ≤ c_max(y_a)`
(`C_{φ,2,K} ≤ ∫₀¹ w²(−log w) dw = 1/9` since `φ(w) ≤ w²`). -/
def RKMono : Prop :=
  ∀ ya tb ρ : ℝ, 10 ^ 25 ≤ ya → 1 ≤ tb → RKCeil ya tb ρ → RKBnd ya tb ρ

/-- **[RKTail] `R_{y,K,φ,2r} ≤ ρ` for `y ≥ y_a`, `r₀ ≤ r ≤ r₁(y)`.** Instance `(2·10²⁶, 0.72)`:
`R_{y,2r} ≤ 0.27125 log 3 + 0.41415 = 0.71215` for `r ≤ r₁(y)`, and `R_{y/K,2r}` stays below
`0.72` (its ratio exceeds `2` past `y = e^{188}` but peaks near `2.02`; sampled max `0.71391`). -/
def RKTail (ya ρ : ℝ) : Prop :=
  ∀ y r : ℝ, ya ≤ y → 150000 ≤ r → r ≤ r1y y → rRK HW.phi y (2 * r) ≤ ρ

/-- **[EnvPt] the pointwise envelope**: `g(y,r) ≤ envQ ρ r + f₂(y)` whenever `r ≥ r₀`, `ρ ≥ 0` and
`R_{y,K,φ,2r} ≤ ρ` (tangent lines of `√·` and of `log`, `e^γ ≤ 1.7881`, `1/√2 ≤ 0.70711`). -/
def EnvPt : Prop :=
  ∀ ρ y r : ℝ, 0 ≤ ρ → 150000 ≤ r → rRK HW.phi y (2 * r) ≤ ρ →
    gB HW.phi y r ≤ envQ ρ r + f2 y

/-- **[EnvDeriv] the closed form**: `PhiQ ρ` has derivative `envQ ρ r / r` at every `r > 0`. -/
def EnvDeriv : Prop := ∀ ρ r : ℝ, 0 < r → HasDerivAt (PhiQ ρ) (envQ ρ r / r) r

/-- **[F2Anti] `f₂(y) = 3.2(K/y)^{1/6}` decreases** (`K/y = log y/(2y)` does, for `y ≥ e`). -/
def F2Anti : Prop := ∀ y y' : ℝ, 10 ^ 25 ≤ y → y ≤ y' → f2 y' ≤ f2 y

/-- **[G0Num] `envQ ρ r₀ + f₂(y_a) ≤ G`**. Instances (value): `(10²⁵, 0.5845, 0.0412)`
(`0.0411077`), `(3·10²⁵, 0.579, 0.0409)` (`0.0407494`), `(10²⁶, 0.5735, 0.0406)` (`0.0403969`),
`(2·10²⁶, 0.5705, 0.0404)` (`0.0402076`). -/
def G0Num (ya ρ G : ℝ) : Prop := envQ ρ 150000 + f2 ya ≤ G

/-- **[T1EnvNum] `coefC(x_a)(envQ ρ r₁(y_a) + f₂(y_a)) felipa(x_a) ≤ T`** (the envelope `EnvPt` at
`r = r₁(y_a)`). Instances (value at `ρ = 0.660, 0.661, 0.6615, 0.662`): `0.2836335 ≤ 0.2865`,
`0.2538629 ≤ 0.2565`, `0.2245949 ≤ 0.227`, `0.2093329 ≤ 0.2115` (margins `≈ 1.0 %`). -/
def T1EnvNum (xa ρ T : ℝ) : Prop :=
  coefC xa * (envQ ρ (r1y (xa / 49)) + f2 (xa / 49)) * fel xa ≤ T

/-- **[R1Le] `r₁(y) = (3/8)y^{4/15} ≤ R`.** -/
def R1Le (y R : ℝ) : Prop := r1y y ≤ R

/-- **[IBlkNum] `PhiQ ρ R − PhiQ ρ r₀ + f₂(y_a)(log R − log r₀) ≤ I`**. Instances (value):
`(10²⁵, 0.672, 2.34·10⁶, 0.074)` (`0.0731150`), `(3·10²⁵, 0.674, 3.22·10⁶, 0.0785)`
(`0.0772457`), `(10²⁶, 0.669, 3.87·10⁶, 0.080)` (`0.0787129`). -/
def IBlkNum (ya ρ R I : ℝ) : Prop :=
  PhiQ ρ R - PhiQ ρ 150000 + f2 ya * (Real.log R - Real.log 150000) ≤ I

/-- **[F2Tail] `f₂(y)·log(r₁(y)/r₀) ≤ B` for `y ≥ y_a`.** Instance `(2·10²⁶, 0.0039)`
(`log(r₁/r₀) ≤ (8/15)K`, and `K^{7/6}y^{−1/6}` decreases: `0.0037728`; the true sup is
`0.00076`). -/
def F2Tail (ya B : ℝ) : Prop :=
  ∀ y : ℝ, ya ≤ y → f2 y * (Real.log (r1y y) - Real.log 150000) ≤ B

/-- **[ITailNum] `−PhiQ ρ r₀ + B ≤ I`.** Instance `(0.72, 0.0039, 0.115)` (value `0.1127`). -/
def ITailNum (ρ B I : ℝ) : Prop := -PhiQ ρ 150000 + B ≤ I

/-- **[EnvAnti] `envQ ρ` decreases on `r ≥ r₀`** for every `ρ ≥ 0`: in `ℓ = log r` it is
`cP(ℓ)e^{−ℓ/2} + Q(ℓ)e^{−ℓ}`, with derivative `c(P′ − P/2)e^{−ℓ/2} + (Q′ − Q)e^{−ℓ} ≤ 0`
for `ℓ ≥ 11`. -/
def EnvAnti : Prop :=
  ∀ ρ r r' : ℝ, 0 ≤ ρ → 150000 ≤ r → r ≤ r' → envQ ρ r' ≤ envQ ρ r

/-- **[T1BNum] the block value of the `T₁` envelope**: `coefC(x_b)(envQ ρ r₁(y_a) + f₂(y_a))
felipa(x_b) ≤ T` (`coefC·felipa` increases in `x`; `envQ ρ` and `f₂` decrease). -/
def T1BNum (xb ya ρ T : ℝ) : Prop := coefC xb * (envQ ρ (r1y ya) + f2 ya) * fel xb ≤ T

/-! ## (5) DISCHARGED: logarithms by the series of `log(1 − x)`; `hs` and `cas` -/

/-- **`log q` from above**, for `q ≤ 2^k(1 − x)`, `|x| < 1`: `n` terms of the series of
`log(1 − x)` and its geometric tail (`Real.abs_log_sub_add_sum_range_le`). -/
theorem log_le_series (q x : ℝ) (k n : ℕ) (hq0 : 0 < q) (hq : q ≤ 2 ^ k * (1 - x))
    (hx : |x| < 1) :
    Real.log q ≤ k * 0.6931471808 - (∑ i ∈ range n, x ^ (i + 1) / (i + 1)) +
      |x| ^ (n + 1) / (1 - |x|) := by
  have h1x : 0 < 1 - x := by linarith [le_abs_self x]
  have hl := Real.log_le_log hq0 hq
  rw [Real.log_mul (by positivity) h1x.ne', Real.log_pow] at hl
  have hs := (abs_le.mp (Real.abs_log_sub_add_sum_range_le hx n)).2
  have h2 := Real.log_two_lt_d9
  have hk : (k : ℝ) * Real.log 2 ≤ k * 0.6931471808 :=
    mul_le_mul_of_nonneg_left h2.le (Nat.cast_nonneg k)
  linarith

/-- **`log q` from below**, for `2^k(1 − x) ≤ q`, `|x| < 1`. -/
theorem le_log_series (q x : ℝ) (k n : ℕ) (hq : 2 ^ k * (1 - x) ≤ q) (hx : |x| < 1) :
    k * 0.6931471803 - (∑ i ∈ range n, x ^ (i + 1) / (i + 1)) -
      |x| ^ (n + 1) / (1 - |x|) ≤ Real.log q := by
  have h1x : 0 < 1 - x := by linarith [le_abs_self x]
  have hl := Real.log_le_log (by positivity) hq
  rw [Real.log_mul (by positivity) h1x.ne', Real.log_pow] at hl
  have hs := (abs_le.mp (Real.abs_log_sub_add_sum_range_le hx n)).1
  have h2 := Real.log_two_gt_d9
  have hk : (k : ℝ) * 0.6931471803 ≤ k * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2.le (Nat.cast_nonneg k)
  linarith

/-- `log 150001 ≤ 11.91841` (truth `11.9183972`): `150001 = 2¹⁷(1 + 18929/131072)`. -/
theorem log_150001_le : Real.log 150001 ≤ 11.91841 := by
  have h := log_le_series 150001 (-18929 / 131072) 17 12 (by norm_num) (by norm_num)
    (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log 150001 ≥ 11.7835`, from `150001 ≥ 2¹⁷`. -/
theorem log_150001_ge : 11.7835 ≤ Real.log 150001 := by
  have h := Real.log_le_log (by norm_num) (show (2 : ℝ) ^ 17 ≤ 150001 by norm_num)
  rw [Real.log_pow] at h
  have := Real.log_two_gt_d9
  push_cast at h
  linarith

/-- `log(1.47·10²⁷) ≤ 62.5552` (truth `62.555053`): `1.47·10²⁷ ≤ 2⁹⁰·19/16`. -/
theorem log_147e25_le : Real.log (147 * 10 ^ 25) ≤ 62.5552 := by
  have h := log_le_series (147 * 10 ^ 25) (-3 / 16) 90 8 (by norm_num) (by norm_num)
    (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log(4.9·10²⁷) ≤ 63.7592` (truth `63.759024`): `4.9·10²⁷ ≤ 2⁹²·95/96`. -/
theorem log_49e26_le : Real.log (49 * 10 ^ 26) ≤ 63.7592 := by
  have h := log_le_series (49 * 10 ^ 26) (1 / 96) 92 6 (by norm_num) (by norm_num)
    (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `log(9.8·10²⁷) ≤ 64.4523` (truth `64.452171`): `9.8·10²⁷ ≤ 2⁹³·95/96`. -/
theorem log_98e26_le : Real.log (98 * 10 ^ 26) ≤ 64.4523 := by
  have h := log_le_series (98 * 10 ^ 26) (1 / 96) 93 6 (by norm_num) (by norm_num)
    (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- **`hs` in closed form**: `(log 150001 + 2.3912)·(0.640209L − 0.021095)/(L/2 + 0.6294)`,
`L = log x`. -/
theorem hs_eq (x : ℝ) (hx : 0 ≤ x) :
    hs x = (Real.log 150001 + 2.3912) *
      ((0.640209 * Real.log x - 0.021095) / (Real.log x / 2 + 0.6294)) := by
  unfold hs hR0 fel
  rw [Real.log_sqrt hx]
  ring

/-- **`cas` in closed form**: `2(0.640209L − 0.021095)/(L + 1.2588)`. -/
theorem cas_eq (x : ℝ) :
    cas x = 2 * (0.640209 * Real.log x - 0.021095) / (Real.log x + 2 * 0.6294) := by
  unfold cas fel
  ring

/-- `(aL − b)/(L/2 + c)` increases in `L` (for `L ≥ 1`). -/
theorem frac_mono (L L' : ℝ) (hL : 1 ≤ L) (h : L ≤ L') :
    (0.640209 * L - 0.021095) / (L / 2 + 0.6294) ≤
      (0.640209 * L' - 0.021095) / (L' / 2 + 0.6294) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `2(aL − b)/(L + 2c)` increases in `L` (for `L ≥ 1`). -/
theorem cfrac_mono (L L' : ℝ) (hL : 1 ≤ L) (h : L ≤ L') :
    2 * (0.640209 * L - 0.021095) / (L + 2 * 0.6294) ≤
      2 * (0.640209 * L' - 0.021095) / (L' + 2 * 0.6294) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **`hs` increases in `x`** (DISCHARGED). -/
theorem hs_mono (x x' : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (h : x ≤ x') : hs x ≤ hs x' := by
  have hx0 := x_pos x hx
  have hL := MajSp.log_ge_one x hx
  have hLL := Real.log_le_log hx0 h
  have hN : 0 ≤ Real.log 150001 + 2.3912 := by linarith [log_150001_ge]
  rw [hs_eq x hx0.le, hs_eq x' (hx0.le.trans h)]
  exact mul_le_mul_of_nonneg_left (frac_mono _ _ hL hLL) hN

/-- **`hs ≥ 8.36`** on `x ≥ 4.9·10²⁶` (it is `≥ 17.7`; DISCHARGED). -/
theorem hs_ge (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 8.36 ≤ hs x := by
  have hx0 := x_pos x hx
  have hL := LW.log_ge_of x hx
  have hN := log_150001_ge
  have hf : 1.25 ≤ (0.640209 * Real.log x - 0.021095) / (Real.log x / 2 + 0.6294) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  rw [hs_eq x hx0.le]
  nlinarith

/-- **`hs ≤ 18.323`** on `x ≥ 4.9·10²⁶`: `(aL − b)/(L/2 + c) ≤ 2a = 1.280418` and
`log 150001 + 2.3912 ≤ 14.30961` (DISCHARGED). -/
theorem hs_le_tail (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : hs x ≤ 18.323 := by
  have hx0 := x_pos x hx
  have hL := MajSp.log_ge_one x hx
  have hN := log_150001_le
  have hN0 := log_150001_ge
  have hf : (0.640209 * Real.log x - 0.021095) / (Real.log x / 2 + 0.6294) ≤ 1.280418 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hf0 : 0 ≤ (0.640209 * Real.log x - 0.021095) / (Real.log x / 2 + 0.6294) :=
    div_nonneg (by linarith) (by linarith)
  rw [hs_eq x hx0.le]
  calc (Real.log 150001 + 2.3912) *
        ((0.640209 * Real.log x - 0.021095) / (Real.log x / 2 + 0.6294))
      ≤ 14.30961 * 1.280418 := mul_le_mul (by linarith) hf hf0 (by norm_num)
    _ ≤ 18.323 := by norm_num

/-- `hs x ≤ N_u(aL_u − b)/(L_u/2 + c)` from `log x ≤ L_u`. -/
theorem hs_le_of (x Lu : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hLu : Real.log x ≤ Lu) :
    hs x ≤ 14.30961 * ((0.640209 * Lu - 0.021095) / (Lu / 2 + 0.6294)) := by
  have hx0 := x_pos x hx
  have hL := MajSp.log_ge_one x hx
  have hN := log_150001_le
  have hN0 := log_150001_ge
  have hf := frac_mono _ _ hL hLu
  have hf0 : 0 ≤ (0.640209 * Real.log x - 0.021095) / (Real.log x / 2 + 0.6294) :=
    div_nonneg (by linarith) (by linarith)
  rw [hs_eq x hx0.le]
  exact mul_le_mul (by linarith) hf hf0 (by norm_num)

/-- **`cas` increases in `x`** (DISCHARGED). -/
theorem cas_mono (x x' : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (h : x ≤ x') : cas x ≤ cas x' := by
  have hx0 := x_pos x hx
  have hL := MajSp.log_ge_one x hx
  rw [cas_eq, cas_eq]
  exact cfrac_mono _ _ hL (Real.log_le_log hx0 h)

/-- **`cas ≥ 0`** on `x ≥ 4.9·10²⁶` (DISCHARGED). -/
theorem cas_nonneg (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : 0 ≤ cas x := by
  have hL := MajSp.log_ge_one x hx
  rw [cas_eq]
  exact div_nonneg (by linarith) (by linarith)

/-- **`cas ≤ 1.280418`** (`MinSp.cas_le` at `s = felipa`; DISCHARGED). -/
theorem cas_le_tail (x : ℝ) (hx : 49 * 10 ^ 25 ≤ x) : cas x ≤ 1.280418 :=
  cas_le x (fel x) hx le_rfl

/-- `cas x ≤ 2(aL_u − b)/(L_u + 2c)` from `log x ≤ L_u`. -/
theorem cas_le_of (x Lu : ℝ) (hx : 49 * 10 ^ 25 ≤ x) (hLu : Real.log x ≤ Lu) :
    cas x ≤ 2 * (0.640209 * Lu - 0.021095) / (Lu + 2 * 0.6294) := by
  have hL := MajSp.log_ge_one x hx
  rw [cas_eq]
  exact cfrac_mono _ _ hL hLu

/-- **The partition points** (DISCHARGED): `hs ≤ 17.952 / 17.9585 / 17.9625` and
`cas ≤ 1.2546 / 1.2551 / 1.2554` at `x = 1.47·10²⁷, 4.9·10²⁷, 9.8·10²⁷` (truth `17.951378 /
17.958246 / 17.962086` and `1.254499 / 1.254979 / 1.255247`). -/
theorem hs_147 : hs (147 * 10 ^ 25) ≤ 17.952 :=
  (hs_le_of _ _ (by norm_num) log_147e25_le).trans (by norm_num)

/-- `hs(4.9·10²⁷) ≤ 17.9585`. -/
theorem hs_49e26 : hs (49 * 10 ^ 26) ≤ 17.9585 :=
  (hs_le_of _ _ (by norm_num) log_49e26_le).trans (by norm_num)

/-- `hs(9.8·10²⁷) ≤ 17.9625`. -/
theorem hs_98e26 : hs (98 * 10 ^ 26) ≤ 17.9625 :=
  (hs_le_of _ _ (by norm_num) log_98e26_le).trans (by norm_num)

/-- `cas(1.47·10²⁷) ≤ 1.2546`. -/
theorem cas_147 : cas (147 * 10 ^ 25) ≤ 1.2546 :=
  (cas_le_of _ _ (by norm_num) log_147e25_le).trans (by norm_num)

/-- `cas(4.9·10²⁷) ≤ 1.2551`. -/
theorem cas_49e26 : cas (49 * 10 ^ 26) ≤ 1.2551 :=
  (cas_le_of _ _ (by norm_num) log_49e26_le).trans (by norm_num)

/-- `cas(9.8·10²⁷) ≤ 1.2554`. -/
theorem cas_98e26 : cas (98 * 10 ^ 26) ≤ 1.2554 :=
  (cas_le_of _ _ (by norm_num) log_98e26_le).trans (by norm_num)

/-! ## (6) DISCHARGED: the affine reduction and the block arithmetic -/

/-- **The affine step, on atoms**: `g ≥ 0`, `p ≥ p₀ ≥ 0`, `0 ≤ s ≤ F`, `c ≥ 0` and the bound at
`(F, p₀)` give the bound at `(s, p)`. -/
theorem affine_step (g H A F s p p0 c : ℝ) (hg0 : 0 ≤ g) (hp0 : 0 ≤ p0) (hs0 : 0 ≤ s)
    (hs1 : s ≤ F) (hp : p0 ≤ p) (hc : 0 ≤ c) (h1 : g * (H * F - p0) + A * F ≤ c) :
    g * (H * s - p) + A * s ≤ c := by
  have e2 : g * (H * s - p) + A * s = (g * H + A) * s - g * p := by ring
  have e1 : g * (H * F - p0) + A * F = (g * H + A) * F - g * p0 := by ring
  rw [e2]
  rw [e1] at h1
  have hgp : g * p0 ≤ g * p := mul_le_mul_of_nonneg_left hp hg0
  have hgp0 : 0 ≤ g * p0 := mul_nonneg hg0 hp0
  rcases le_or_gt 0 (g * H + A) with hb | hb
  · have := mul_le_mul_of_nonneg_left hs1 hb
    linarith
  · have := mul_le_mul_of_nonneg_right hb.le hs0
    rw [zero_mul] at this
    linarith

/-- **The affine reduction**: `MNumAt p₀ c` from `g(r₀) ≥ 0`, `c ≥ 0`, `p₀ ≥ 0` and the bound at
`s = felipa(x)`, `p = p₀`. `M` is affine in `p` with coefficient `−g(r₀) ≤ 0`, and affine in `s`,
so on `[0, felipa]` it is at most `max(M(0,p₀), M(felipa,p₀))` with `M(0,p₀) = −g(r₀)p₀ ≤ 0`. -/
theorem mnumAt_of_felipa (p0 c : ℝ) (hp0 : 0 ≤ p0) (hc : 0 ≤ c) (hg : G0Nonneg)
    (hM : ∀ x : ℝ, 49 * 10 ^ 25 ≤ x →
      gB HW.phi (x / 49) 150000 * (hs x - p0) + t1 x + cas x * intG HW.phi (x / 49) ≤ c) :
    MNumAt p0 c := by
  intro x hx s p hs0 hs1 hp
  refine affine_step _ _ _ _ s p p0 c (hg (x / 49) (y_ge x hx)) hp0 hs0 hs1 hp hc ?_
  have e : gB HW.phi (x / 49) 150000 * (hs x - p0) + t1 x + cas x * intG HW.phi (x / 49) =
      gB HW.phi (x / 49) 150000 * (hR0 x * (0.640209 * Real.log x - 0.021095) - p0) +
        (2 / (Real.log x + 2 * 0.6294) * intG HW.phi (x / 49) +
          coefC x * gB HW.phi (x / 49) (r1y (x / 49))) *
          (0.640209 * Real.log x - 0.021095) := by
    unfold hs t1 cas fel
    ring
  rw [← e]
  exact hM x hx

/-- **One region**: `g ∈ [0, G]`, `h ∈ [p₀, H]`, `t ≤ T`, `κ ∈ [0, k]`, `∫ ≤ I` give
`g(h − p₀) + t + κ∫ ≤ G(H − p₀) + T + kI`. -/
theorem blk (p0 c G H T k I g h t ca ig : ℝ) (hg0 : 0 ≤ g) (hg : g ≤ G) (hh0 : p0 ≤ h)
    (hh : h ≤ H) (ht : t ≤ T) (hca0 : 0 ≤ ca) (hca : ca ≤ k) (hig : ig ≤ I) (hI : 0 ≤ I)
    (hc : G * (H - p0) + T + k * I ≤ c) : g * (h - p0) + t + ca * ig ≤ c := by
  have h1 : g * (h - p0) ≤ G * (H - p0) :=
    mul_le_mul hg (by linarith) (by linarith) (le_trans hg0 hg)
  have h2 : ca * ig ≤ k * I :=
    le_trans (mul_le_mul_of_nonneg_left hig hca0) (mul_le_mul_of_nonneg_right hca hI)
  linarith

/-- `x ≥ 49c ⇒ x/49 ≥ c`. -/
theorem y_ge_of (x c : ℝ) (h : 49 * c ≤ x) : c ≤ x / 49 := by
  rw [le_div_iff₀ (by norm_num)]
  linarith

/-- `x ≤ 49c ⇒ x/49 ≤ c`. -/
theorem y_le_of (x c : ℝ) (h : x ≤ 49 * c) : x / 49 ≤ c := by
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-! ## (7) THE COMPOSITION -/

/-- **THE SPINE of `MNumAt 8.36 0.785`**: the level-1 links on the partition
`y ∈ [10²⁵, 3·10²⁵] ∪ [3·10²⁵, 10²⁶] ∪ [10²⁶, 2·10²⁶] ∪ [2·10²⁶, ∞)`, closed by the region
arithmetic (`0.774531, 0.747604, 0.717294, 0.761253 ≤ 0.785`). Application and arithmetic only:
`mnumAt_of_felipa`, `blk`, and the DISCHARGED facts about `hs` and `cas`. -/
theorem mnumAt_of_links (g0 : G0Nonneg) (e1 : G0Env (10 ^ 25) 0.0412)
    (e2 : G0Env (3 * 10 ^ 25) 0.0409) (e3 : G0Env (10 ^ 26) 0.0406)
    (e4 : G0Env (2 * 10 ^ 26) 0.0404) (ta : T1Anti) (n1 : T1Num (49 * 10 ^ 25) 0.2865)
    (n2 : T1Num (147 * 10 ^ 25) 0.2565) (n3 : T1Num (49 * 10 ^ 26) 0.227)
    (n4 : T1Num (98 * 10 ^ 26) 0.2115) (i1 : IGBlk (10 ^ 25) (3 * 10 ^ 25) 0.074)
    (i2 : IGBlk (3 * 10 ^ 25) (10 ^ 26) 0.0785) (i3 : IGBlk (10 ^ 26) (2 * 10 ^ 26) 0.08)
    (i4 : IGTail (2 * 10 ^ 26) 0.115) : MNumAt 8.36 0.785 := by
  refine mnumAt_of_felipa 8.36 0.785 (by norm_num) (by norm_num) g0 fun x hx => ?_
  have hg0 := g0 (x / 49) (y_ge x hx)
  have hh0 := hs_ge x hx
  have hca0 := cas_nonneg x hx
  rcases le_or_gt x (147 * 10 ^ 25) with hb1 | hb1
  · refine blk 8.36 0.785 0.0412 17.952 0.2865 1.2546 0.074 _ _ _ _ _ hg0
      (e1 _ (y_ge x hx)) hh0 ((hs_mono x _ hx hb1).trans hs_147)
      ((ta _ x le_rfl hx).trans n1) hca0 ((cas_mono x _ hx hb1).trans cas_147)
      (i1 _ (y_ge x hx) (y_le_of x _ (by linarith))) (by norm_num) (by norm_num)
  rcases le_or_gt x (49 * 10 ^ 26) with hb2 | hb2
  · have hx1 : 147 * 10 ^ 25 ≤ x := hb1.le
    refine blk 8.36 0.785 0.0409 17.9585 0.2565 1.2551 0.0785 _ _ _ _ _ hg0
      (e2 _ (y_ge_of x _ (by linarith))) hh0 ((hs_mono x _ hx hb2).trans hs_49e26)
      ((ta _ x (by norm_num) hx1).trans n2) hca0 ((cas_mono x _ hx hb2).trans cas_49e26)
      (i2 _ (y_ge_of x _ (by linarith)) (y_le_of x _ (by linarith))) (by norm_num)
      (by norm_num)
  rcases le_or_gt x (98 * 10 ^ 26) with hb3 | hb3
  · have hx2 : 49 * 10 ^ 26 ≤ x := hb2.le
    refine blk 8.36 0.785 0.0406 17.9625 0.227 1.2554 0.08 _ _ _ _ _ hg0
      (e3 _ (y_ge_of x _ (by linarith))) hh0 ((hs_mono x _ hx hb3).trans hs_98e26)
      ((ta _ x (by norm_num) hx2).trans n3) hca0 ((cas_mono x _ hx hb3).trans cas_98e26)
      (i3 _ (y_ge_of x _ (by linarith)) (y_le_of x _ (by linarith))) (by norm_num)
      (by norm_num)
  · have hx3 : 98 * 10 ^ 26 ≤ x := hb3.le
    refine blk 8.36 0.785 0.0404 18.323 0.2115 1.280418 0.115 _ _ _ _ _ hg0
      (e4 _ (y_ge_of x _ (by linarith))) hh0 (hs_le_tail x hx)
      ((ta _ x (by norm_num) hx3).trans n4) hca0 (cas_le_tail x hx)
      (i4 _ (y_ge_of x _ (by linarith))) (by norm_num) (by norm_num)

/-- **`MNumAt 8.36 c → MinW.MNumW HW.phi c`**: the floor `p ≥ 8.6129` is inside `p ≥ 8.36`. -/
theorem mnumW_of_atc (c : ℝ) (h : MNumAt 8.36 c) : MinW.MNumW HW.phi c :=
  fun x hx s p hs0 hs1 hp => h x hx s p hs0 hs1 (le_trans (by norm_num) hp)

/-- **`MNumAt 8.36 0.785 → MinW.MNumW HW.phi 0.785`**. -/
theorem mnumW_of_at (h : MNumAt 8.36 0.785) : MinW.MNumW HW.phi 0.785 := mnumW_of_atc 0.785 h

/-- **`MinW.MNumW HW.phi 0.785` from the level-1 links.** Application only. -/
theorem mnumW_of_links (g0 : G0Nonneg) (e1 : G0Env (10 ^ 25) 0.0412)
    (e2 : G0Env (3 * 10 ^ 25) 0.0409) (e3 : G0Env (10 ^ 26) 0.0406)
    (e4 : G0Env (2 * 10 ^ 26) 0.0404) (ta : T1Anti) (n1 : T1Num (49 * 10 ^ 25) 0.2865)
    (n2 : T1Num (147 * 10 ^ 25) 0.2565) (n3 : T1Num (49 * 10 ^ 26) 0.227)
    (n4 : T1Num (98 * 10 ^ 26) 0.2115) (i1 : IGBlk (10 ^ 25) (3 * 10 ^ 25) 0.074)
    (i2 : IGBlk (3 * 10 ^ 25) (10 ^ 26) 0.0785) (i3 : IGBlk (10 ^ 26) (2 * 10 ^ 26) 0.08)
    (i4 : IGTail (2 * 10 ^ 26) 0.115) : MinW.MNumW HW.phi 0.785 :=
  mnumW_of_at (mnumAt_of_links g0 e1 e2 e3 e4 ta n1 n2 n3 n4 i1 i2 i3 i4)

/-- **THE SPINE on the envelope route for `T₁`**: `mnumAt_of_links` with `T1Anti` + `T1Num`
replaced by region bounds `T1Reg`/`T1Far` (regions `0.783530, 0.757602, 0.722794, 0.784753 ≤
0.785`). Application and arithmetic only. -/
theorem mnumAt_of_links2 (g0 : G0Nonneg) (e1 : G0Env (10 ^ 25) 0.0412)
    (e2 : G0Env (3 * 10 ^ 25) 0.0409) (e3 : G0Env (10 ^ 26) 0.0406)
    (e4 : G0Env (2 * 10 ^ 26) 0.0404) (w1 : T1Reg (49 * 10 ^ 25) (147 * 10 ^ 25) 0.2955)
    (w2 : T1Reg (147 * 10 ^ 25) (49 * 10 ^ 26) 0.2665)
    (w3 : T1Reg (49 * 10 ^ 26) (98 * 10 ^ 26) 0.2325) (w4 : T1Far (98 * 10 ^ 26) 0.235)
    (i1 : IGBlk (10 ^ 25) (3 * 10 ^ 25) 0.074) (i2 : IGBlk (3 * 10 ^ 25) (10 ^ 26) 0.0785)
    (i3 : IGBlk (10 ^ 26) (2 * 10 ^ 26) 0.08) (i4 : IGTail (2 * 10 ^ 26) 0.115) :
    MNumAt 8.36 0.785 := by
  refine mnumAt_of_felipa 8.36 0.785 (by norm_num) (by norm_num) g0 fun x hx => ?_
  have hg0 := g0 (x / 49) (y_ge x hx)
  have hh0 := hs_ge x hx
  have hca0 := cas_nonneg x hx
  rcases le_or_gt x (147 * 10 ^ 25) with hb1 | hb1
  · refine blk 8.36 0.785 0.0412 17.952 0.2955 1.2546 0.074 _ _ _ _ _ hg0
      (e1 _ (y_ge x hx)) hh0 ((hs_mono x _ hx hb1).trans hs_147) (w1 x hx hb1) hca0
      ((cas_mono x _ hx hb1).trans cas_147)
      (i1 _ (y_ge x hx) (y_le_of x _ (by linarith))) (by norm_num) (by norm_num)
  rcases le_or_gt x (49 * 10 ^ 26) with hb2 | hb2
  · have hx1 : 147 * 10 ^ 25 ≤ x := hb1.le
    refine blk 8.36 0.785 0.0409 17.9585 0.2665 1.2551 0.0785 _ _ _ _ _ hg0
      (e2 _ (y_ge_of x _ (by linarith))) hh0 ((hs_mono x _ hx hb2).trans hs_49e26)
      (w2 x hx1 hb2) hca0 ((cas_mono x _ hx hb2).trans cas_49e26)
      (i2 _ (y_ge_of x _ (by linarith)) (y_le_of x _ (by linarith))) (by norm_num)
      (by norm_num)
  rcases le_or_gt x (98 * 10 ^ 26) with hb3 | hb3
  · have hx2 : 49 * 10 ^ 26 ≤ x := hb2.le
    refine blk 8.36 0.785 0.0406 17.9625 0.2325 1.2554 0.08 _ _ _ _ _ hg0
      (e3 _ (y_ge_of x _ (by linarith))) hh0 ((hs_mono x _ hx hb3).trans hs_98e26)
      (w3 x hx2 hb3) hca0 ((cas_mono x _ hx hb3).trans cas_98e26)
      (i3 _ (y_ge_of x _ (by linarith)) (y_le_of x _ (by linarith))) (by norm_num)
      (by norm_num)
  · have hx3 : 98 * 10 ^ 26 ≤ x := hb3.le
    refine blk 8.36 0.785 0.0404 18.323 0.235 1.280418 0.115 _ _ _ _ _ hg0
      (e4 _ (y_ge_of x _ (by linarith))) hh0 (hs_le_tail x hx) (w4 x hx3) hca0
      (cas_le_tail x hx) (i4 _ (y_ge_of x _ (by linarith))) (by norm_num) (by norm_num)

/-- **The old route implies the new**: `T1Anti` and `t1(x_a) ≤ T` give `T1Reg x_a x_b T`. -/
theorem t1Reg_of_anti (xa xb T : ℝ) (hxa : 49 * 10 ^ 25 ≤ xa) (ta : T1Anti) (hn : T1Num xa T) :
    T1Reg xa xb T := fun x hx _ => (ta xa x hxa hx).trans hn

/-- `T1Anti` and `t1(x_a) ≤ T` give `T1Far x_a T`. -/
theorem t1Far_of_anti (xa T : ℝ) (hxa : 49 * 10 ^ 25 ≤ xa) (ta : T1Anti) (hn : T1Num xa T) :
    T1Far xa T := fun x hx => (ta xa x hxa hx).trans hn

/-! ## (8) Every link constrains -/

/-- **`MNumAt` forces `g(r₀) ≥ 0`** (as `MinW.mnumW_nonneg` does for `MNumW`), so `G0Nonneg` is
not an extra assumption on the target: it is implied by it. -/
theorem g0Nonneg_of_at (c : ℝ) (h : MNumAt 8.36 c) : G0Nonneg := by
  intro y hy
  have hx : 49 * 10 ^ 25 ≤ 49 * y := by linarith
  have e : 49 * y / 49 = y := by ring
  have := MinW.mnumW_nonneg HW.phi c (mnumW_of_atc c h) (49 * y) hx
  rwa [e] at this

end Principia.Common.TernaryGoldbach.MN
