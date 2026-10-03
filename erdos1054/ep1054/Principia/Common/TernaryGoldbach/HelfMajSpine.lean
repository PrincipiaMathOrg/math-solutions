/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MajorR
import Principia.Common.TernaryGoldbach.PlattCite
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.Order

set_option autoImplicit false

/-!
# HelfMaj Thm 1.4 / Cor 1.3 / Prop 1.5 at the RETYPED constants, from named links

**`helfMajR_of_links` PROVES `MR.HelfMajR η₊ (η₂ ∗_M φ)` FROM NINETEEN NAMED LINKS. THE LINKS ARE
OPEN.** Nothing here proves the explicit formula, the zero count, the saddle-point analysis of
majarcs §3, or any norm of Helfgott's weights; it proves that they COMPOSE to the referee's retyped
constants (`MajorR.lean`, LEAN-PROGRESS "THE HELFMAJ PAPER SPINE"), with every correction the
referee found (F1, F2, F4, N1) and three more (F6, F8, F10) encoded in the link statements, and it
typechecks the closing arithmetic against the RETYPED numbers. Source: `majarcs.tex` (arXiv
1305.2897 v4); line numbers are that file's.

## The spine (application only)

```
 ExplicitFormula (lem:agamon) ─┐     ZeroCount (eq:melos) ─► Hausierer, GarmolaDecr
                               ▼
 err_le_of_zero_sums : |err| ≤ Tb + Hb/√x + R/x      [split at T, GRH below T, x^{Re ρ} ≤ x above]
   Hb ← Hausierer (low zeros, corrected)   Tb ← GarmolaDecr + <w>Decay + <w>TailInt (high zeros)
   R  ← <w>Norms
       ├─ η₊  : plus_err  (prop:unease)   ─► malpor_gen_arith / malpor_one_arith ─► malporR_of_links
       ├─ φ   : phi_err   (prop:magoma)   ─► coprar_w ─► kolona_transfer (Kolona, Eta2Moments)
       │                                         ─► coprar_close ─► coprarR_of_links
       └─ η₊,₂: mal_err   (prop:konechno) ─► MalMain, malheur_close ─► malheurR_of_links
 RT.PlattFull enters ONLY through grh_of_platt (GRH to T ≤ plattHeight q): heights 200 + 250r/q
 (Thm 1.4, RT.odd_height / RT.even_height), 4.2·10⁷ (Thm 1.4, q = 1), 10⁸/q (Cor 1.3,
 RT.height_ge), 450 (Prop 1.5).
```

## The nineteen links

| link | source | regime | note |
|---|---|---|---|
| `ExplicitFormula` | lem:agamon 2884–3189 | DEEP | `(log q + 8)` for the printed `6.01` (F6) |
| `ZeroCount` | eq:melos 3342–3350 | CITED | Rosser/McCurley/Trudgian — **OWNER QUESTION** |
| `Hausierer` | lem:hausierer 3389–3524 | ELEM given ZeroCount | corrected F1, F2, F8 |
| `GarmolaDecr` | lem:garmola 3306–3380 | ELEM given ZeroCount | corrected F2, N1 |
| `PlusReg`, `PlusNorms` | 4389–4410, App. B 5935–6120 | NUM | Helfgott's `|η₊·log|₂ ≤ 0.83` |
| `PlusDecay` | lem:schastya 4231–4256 | MELLIN | cor:amanita1 `k = 1`, §3, App. A |
| `PlusTailInt` | 4262–4336 | ELEM | twice the printed form, `+10 %` |
| `PhiReg`, `PhiNorms` | eq:drachcat 4000–4014 | ELEM | Gaussian moments |
| `PhiDecay` | cor:amanita1 752–769 | MELLIN | `k = 2` |
| `PhiTailInt` | 3860–3981 | ELEM | twice the printed form, `+10 %` |
| `Kolona` | eq:chemdames, eq:braca 4074–4168 | ELEM | Fubini |
| `Eta2Moments` | 4157–4163 | ELEM | four moments of `η₂` |
| `MalReg`, `MalNorms` | 4466–4569 | NUM | F13 corrected; rests on `eq:dalida`, `eq:gobmark` |
| `MalDecay` | 4594–4685 | MELLIN + CITED | DLMF 5.6.9, 5.11.2; weakened to `e^{−0.7(T−400)}` |
| `MalTailInt` | 4687–4747 | ELEM | |
| `MalMain` | 4957–4997 | NUM + MELLIN | F4 corrected; rests on `eq:impath` and VNODE-LP |

**Citations beyond Platt** (owner questions, none cited as proved): `ZeroCount` (Rosser 1941 Thms
17–19, McCurley 1984 Thm 2.1, Trudgian 2015 Thm 1: proofs whose constants the paper does not
derive); `MalDecay` (DLMF 5.6.9 explicit Stirling, DLMF 5.11.2 digamma asymptotic); `MalMain`
(VNODE-LP rigorous integrals `∫η∘² log xt`); `PlusNorms`/`PlusDecay` (App. A/B interval bisection).

## The arithmetic at the RETYPED constants (all PROVED; margins exact for the Lean bounds)

| target | established here | retyped | margin |
|---|---|---|---|
| Thm 1.4 main | `(769334 + 11.19)/√q + 100.15` | `900000/√q + 52` | `11 %` at `q = 3·10⁵` |
| Thm 1.4 tail, exp. | `3.286·10⁻¹¹/√q` | `6.18·10⁻¹¹/√q` | `1.88×` |
| Thm 1.4 tail, Gauss. | `2.583·10⁻¹⁰/q + 2.50·10⁻¹⁵` | `1.14·10⁻⁹/q` | `11.5 %` at `q = 3·10⁵` |
| Thm 1.4, `q = 1` | `10⁻¹³ + (295807 + 5.6)/√x` | `3.34·10⁻¹¹ + 320000/√x` | `7.6 %` |
| Cor 1.3 main | `523162/√q + 148.25` | `650000/√q + 80` | `13 %` at `q = 3·10⁵` |
| Cor 1.3 tail | `2.374·10⁻¹³/q` | `3·10⁻¹³/q` | `20 %` |
| Prop 1.5 | `3.948·10⁻⁶ + 391/√x` (`× x log x`) | `5·10⁻⁶ + 500/√x` | `21 %`, `22 %` |

## FINDINGS (typechecked, not prose)

1. **The retyped ADDITIVE constants `52` (Thm 1.4) and `80` (Cor 1.3) are each SMALLER than the
   corrected proof's constant term** (`100.15`, `148.25`): F2 puts `√2` on the `g(1)` boundary term,
   F8 adds the `g(T₀)` boundary term. `malpor_gen_arith`/`coprar_close` close only by absorbing the
   excess into the `1/√q` term, which needs `√q ≤ 2477` (resp. `1862`) — true for `q ≤ 3·10⁵`, the
   only range the retypes quantify over. Every consumer is unaffected.
2. **F6 quantified**: `eq:peanuts` bounds the complex `|log(3/2 − iτ)|` by `log|3/2 − iτ|`; with the
   argument `π/2` restored, agamon's `√(226.844/2π) = 6.01` becomes `7.573` (mpmath,
   `scratchpad/hmsp/f6.py`). Stated as `8`.
3. **At `q = 1` Helfgott's height is too tight to reuse**: at `T = 200 + 1.2·10⁷π` the Gaussian tail
   alone is `3.333·10⁻¹¹` of the `3.34·10⁻¹¹`. This spine uses `T = 4.2·10⁷` (inside Platt's
   `10⁸`), where the tail is `≤ 10⁻¹³` and the corrected main term is `295807 ≤ 320000`.
4. **An encoding hazard, closed**: `Gm` is the Lebesgue Mellin integral; `lem:agamon`'s `σ`-range
   `⊇ [1/2, 3/2]` would let an off-line zero with `Re ρ` below the convergence abscissa enter
   `∑_ρ` as junk `0`, making the link claim more than the lemma. `AgamonReg` asks `a ≤ 0`.

## Encoding

`zsum χ A w = ∑'_{ρ ∈ zeroSet χ ∩ A} mult(ρ)·w(ρ)` in `ℝ≥0∞` (never junk: divergence is `∞`),
`mult = analyticOrderNatAt (LFunction χ)`, `zeroSet` = `L(s,χ) = 0 ∧ 0 < Re s < 1` (the encoding of
`RT.PlattFull`). Tails and moments are `lintegral`s (no integrability junk). Numerals: `π` via
`Real.pi_gt_d6`/`pi_lt_d6`, `e` via `Real.exp_one_gt_d9`/`lt_d9` (`exp_neg_le`, `log_le_nat`).
-/

namespace Principia.Common.TernaryGoldbach.HM

open MeasureTheory Set Principia.Common.Goldbach
open scoped ENNReal

/-! ## (1) Objects -/

section Objects

variable {q : ℕ} [NeZero q]

/-- The non-trivial zeros of `L(s,χ)`, encoded exactly as `RT.PlattFull` encodes them:
`L(s,χ) = 0` with `0 < Re s < 1`. -/
def zeroSet (χ : DirichletCharacter ℂ q) : Set ℂ :=
  {s | DirichletCharacter.LFunction χ s = 0 ∧ 0 < s.re ∧ s.re < 1}

/-- The multiplicity of a zero: the order of vanishing of `L(s,χ)` at `s`. -/
noncomputable def zmult (χ : DirichletCharacter ℂ q) (s : ℂ) : ℝ≥0∞ :=
  (analyticOrderNatAt (DirichletCharacter.LFunction χ) s : ℝ≥0∞)

/-- **A sum over the non-trivial zeros in `A`, with multiplicity**, of a weight `w ≥ 0`, in `ℝ≥0∞`
(so it is never Mathlib's junk `0`: a divergent sum is `∞`). -/
noncomputable def zsum (χ : DirichletCharacter ℂ q) (A : Set ℂ) (w : ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' ρ : ↥(zeroSet χ ∩ A), zmult χ ρ * w ρ

/-- **`N(T,χ)`**: the number of non-trivial zeros with `|Im ρ| ≤ T`, with multiplicity. -/
noncomputable def zcount (χ : DirichletCharacter ℂ q) (T : ℝ) : ℝ≥0∞ :=
  zsum χ {s | |s.im| ≤ T} (fun _ => 1)

/-- **GRH to height `T`** for one character: every non-trivial zero with `|Im ρ| ≤ T` is on the
critical line. -/
def GRHTo (χ : DirichletCharacter ℂ q) (T : ℝ) : Prop :=
  ∀ s ∈ zeroSet χ, |s.im| ≤ T → s.re = 1 / 2

/-- A real character: `χ(a)` is real for every `a`. -/
def IsRealChar (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ a : ZMod q, starRingEnd ℂ (χ a) = χ a

end Objects

/-- **`G_δ(s)`**: the Mellin transform of `η(t) e(δt)` (majarcs 2889, `eq:guason` 3784). -/
noncomputable def Gm (η : ℝ → ℝ) (δ : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => ((η t : ℝ) : ℂ) * e (δ * t)) s

/-- `t ↦ (log t) η(t)`. -/
noncomputable def llog (η : ℝ → ℝ) (t : ℝ) : ℝ := Real.log t * η t

/-- `|η(t)/√t|₁` on `(0,∞)`. -/
noncomputable def n1h (η : ℝ → ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), |η t| / Real.sqrt t

/-- `|η(t)√t|₁` on `(0,∞)`. -/
noncomputable def n1s (η : ℝ → ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), |η t| * Real.sqrt t

/-- **`c₀`** of `eq:marenostrum` (2909–2912), the bound for the residue term `R` when `η(0) = 0`. -/
noncomputable def c0 (η : ℝ → ℝ) (δ : ℝ) : ℝ :=
  2 / 3 * (n1h (deriv η) + n1s (deriv η) + 2 * Real.pi * |δ| * (n1h η + n1s η))

/-- **`g_χ(T) = 0.5 log qT + 17.7`** (`eq:ertr` 3330–3332), the error of the zero count. -/
noncomputable def gZ (q T : ℝ) : ℝ := 0.5 * Real.log (q * T) + 17.7

/-- The density weight of the two-sided zero count plus its error:
`max((1/π) log(qt/2π), 0) + 1/(2t)` (the `1/(2t)` is `g_χ'`). -/
noncomputable def gw (q t : ℝ) : ℝ :=
  max (Real.log (q * t / (2 * Real.pi)) / Real.pi) 0 + 1 / (2 * t)

/-! ## (2) The weight-generic links -/

/-- **LINK [ZeroCount] — `eq:melos` (majarcs 3342–3350), CITED**: for every primitive `χ` mod
`q ≥ 1` and `T ≥ 1`, `N(T,χ)` is finite and `|N(T,χ) − (T/π) log(qT/2πe)| ≤ 0.5 log qT + 17.7`.
Helfgott cites Rosser 1941 Thms 17–19, McCurley 1984 Thm 2.1 and Trudgian (Math. Comp. 84, 2015)
Thm 1, and derives none of the constants. **A citation beyond Platt: an OWNER question.** -/
def ZeroCount : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ T : ℝ, 1 ≤ T →
    zcount χ T ≠ ⊤ ∧
      |(zcount χ T).toReal - T / Real.pi * Real.log (q * T / (2 * Real.pi * Real.exp 1))| ≤
        gZ q T

/-- The regularity hypotheses of `lem:agamon` (2884–2893): `η ∈ C¹[0,∞)`, `η, η' ∈ L²`,
`η t^{σ−1}, η' t^{σ−1} ∈ L¹` for `σ` in an open interval `(a, b)` containing `[1/2, 3/2]` —
**STRENGTHENED to `a ≤ 0`**, so the interval also contains the whole critical strip: `Gm` is the
Lebesgue Mellin integral, not its analytic continuation, and at a zero with `Re ρ ≤ a` it would be
Mathlib's junk `0`, making `ExplicitFormula` claim MORE than Helfgott's lemma (an off-line zero
would silently drop out of `∑_ρ`). The strengthening makes `ExplicitFormula` weaker; it holds for
all three weights (`η₊ t^σ ∈ L¹` for `σ > −2`, `eq:paytoplay`; `η₊' t^σ` for `σ > −1`, `eq:uzsu`;
`φ`, `φ'` vanish at `0`). -/
def AgamonReg (η : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 η (Ici 0) ∧ MemLp η 2 (volume.restrict (Ioi 0)) ∧
    MemLp (deriv η) 2 (volume.restrict (Ioi 0)) ∧
    ∃ a b : ℝ, a ≤ 0 ∧ 3 / 2 < b ∧ ∀ σ ∈ Ioo a b,
      IntegrableOn (fun t => η t * t ^ (σ - 1)) (Ioi 0) ∧
        IntegrableOn (fun t => deriv η t * t ^ (σ - 1)) (Ioi 0)

/-- **LINK [ExplicitFormula] — `lem:agamon` (majarcs 2884–3189), DEEP**, in absolute-value form and
for `η(0) = 0` (all three weights; then `|R| ≤ c₀`, 2909–2912, 2993–3001):
`x·|err_{η,χ}(δ,x)| ≤ ∑_ρ |G_δ(ρ)| x^{Re ρ} + c₀ + (log q + 8)(|η'|₂ + 2π|δ||η|₂) x^{−1/2}`.
**The printed constant is `6.01`**; it is `√(226.844/2π)` built from `eq:peanuts` (3100–3125), which
bounds the complex `|log(3/2 − iτ)|` by `log|3/2 − iτ|`, dropping `|arg| ≤ π/2` (flag F6). With
`π/2` restored the constant is `7.5730` (mpmath, `scratchpad/hmsp/f6.py`); `8` is stated. -/
def ExplicitFormula : Prop :=
  ∀ η : ℝ → ℝ, AgamonReg η → η 0 = 0 →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ δ x : ℝ, 0 < x →
      ENNReal.ofReal (x * ‖MajSp.err η χ δ x‖) ≤
        zsum χ univ (fun ρ => ENNReal.ofReal (‖Gm η δ ρ‖ * x ^ ρ.re)) +
          ENNReal.ofReal (c0 η δ + (Real.log q + 8) *
            (MajSp.l2 (deriv η) + 2 * Real.pi * |δ| * MajSp.l2 η) / Real.sqrt x)

/-- The hypotheses of `lem:hausierer` (3389–3393): `η, (log t)η ∈ L¹ ∩ L²`, `η/√t ∈ L¹`; plus
`η t^{σ−1} ∈ L¹` near `σ = 1/2` (so `G_δ` is analytic across the critical line and
`G_δ' = M((log t)η e(δt))`, which the proof differentiates, 3431–3440). -/
def HausiererReg (η : ℝ → ℝ) : Prop :=
  MemLp η 1 (volume.restrict (Ioi 0)) ∧ MemLp η 2 (volume.restrict (Ioi 0)) ∧
    MemLp (llog η) 1 (volume.restrict (Ioi 0)) ∧ MemLp (llog η) 2 (volume.restrict (Ioi 0)) ∧
    IntegrableOn (fun t => η t / Real.sqrt t) (Ioi 0) ∧
    ∃ a b : ℝ, a < 1 / 2 ∧ 1 / 2 < b ∧ ∀ σ ∈ Ioo a b,
      IntegrableOn (fun t => η t * t ^ (σ - 1)) (Ioi 0)

/-- The CORRECTED `lem:hausierer` bound for a general (complex) `χ`, two-sided count only:
`√(2/π)|η|₂√T(log(qT/2πe) + 1/2) + √(2π)|η·log|₂√T(½ log qT + 17.21) + |η/√t|₁(N(1)-part +
√2 g(1) + √2 g(T))`, every constant rounded UP (`0.7979 ≥ √(2/π)`, `2.5067 ≥ √(2π)`,
`2.3378 ≤ log 2π√e`, `1.4143 ≥ √2`). -/
noncomputable def hbC (q T n2 nl n1 : ℝ) : ℝ :=
  0.7979 * n2 * Real.sqrt T * (Real.log (q * T) - 2.3378) +
    2.5067 * nl * Real.sqrt T * (0.5 * Real.log (q * T) + 17.21) +
    n1 * (0.819 * Real.log q + 16.8 + 1.4143 * (0.5 * Real.log q + 17.7) +
      1.4143 * (0.5 * Real.log (q * T) + 17.7))

/-- The CORRECTED `lem:hausierer` bound for a REAL `χ` (zeros pair `ρ ↔ ρ̄`):
`(1/√π)|η|₂√T(log(qT/2πe) + 1/2) + √π|η·log|₂√T(½ log qT + 17.21) + |η/√t|₁(N(1)-part + g(1) +
g(T))`, rounded up (`0.5642 ≥ 1/√π`, `1.7725 ≥ √π`). -/
noncomputable def hbR (q T n2 nl n1 : ℝ) : ℝ :=
  0.5642 * n2 * Real.sqrt T * (Real.log (q * T) - 2.3378) +
    1.7725 * nl * Real.sqrt T * (0.5 * Real.log (q * T) + 17.21) +
    n1 * (1.319 * Real.log q + 0.5 * Real.log (q * T) + 52.2)

/-- **LINK [Hausierer] — `lem:hausierer` (majarcs 3389–3524), CORRECTED; ELEM given the zero count
and Mellin–Plancherel.** For `T ≥ 1`, `qT ≥ 37` and GRH to `T`:
`∑_{|Im ρ| ≤ T} |G_δ(ρ)| ≤ hbC` for every primitive `χ`, and `≤ hbR` for a real one.
Printed: `(|η|₂ + |η·log|₂)√T log qT + (17.21|η·log|₂ − log(2π√e)|η|₂)√T + |η/√t|₁(1.32 log q +
34.5)`, i.e. coefficients `(1, 1)`. Corrections: F1 (the Cauchy–Schwarz at 3481–3486 is short by
`√π` on the `|η·log|₂` term and `√π` too large on the `|η|₂` term); F2 (3453–3454 assumes
`|G_δ(½+iτ)| = |G_δ(½−iτ)|`, false for `δ ≠ 0`, and zeros symmetric, false for complex `χ`);
F8 (the truncated `f` jumps at `T`, so a boundary term `f(T)g(T)` is owed). -/
def Hausierer : Prop :=
  ZeroCount → ∀ η : ℝ → ℝ, HausiererReg η →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ δ T : ℝ, 1 ≤ T →
      37 ≤ (q : ℝ) * T → GRHTo χ T →
        zsum χ {s | |s.im| ≤ T} (fun ρ => ENNReal.ofReal ‖Gm η δ ρ‖) ≤
            ENNReal.ofReal (hbC q T (MajSp.l2 η) (MajSp.l2 (llog η)) (n1h η)) ∧
          (IsRealChar χ → zsum χ {s | |s.im| ≤ T} (fun ρ => ENNReal.ofReal ‖Gm η δ ρ‖) ≤
            ENNReal.ofReal (hbR q T (MajSp.l2 η) (MajSp.l2 (llog η)) (n1h η)))

/-- **LINK [GarmolaDecr] — `lem:garmola` (majarcs 3306–3380) for a decreasing weight, CORRECTED;
ELEM given the zero count.** For `F ≥ 0` measurable and antitone on `[y,∞)`, `y ≥ 1`:
`∑_{|Im ρ| > y} F(|Im ρ|) ≤ ∫_y^∞ F(t)(max((1/π)log(qt/2π), 0) + 1/(2t)) dt + 2F(y)g(y)`.
Printed (3325–3327): `(1/2π)∫F log(qT/2π) + (1/4)∫F/T` for the sum over `Im ρ > y` only, via the
one-sided `N⁺ = N/2` (F2: false for complex `χ`) and without the second `F(y)g(y)` (N1:
`F(y)g(y) − ∫F'g = 2F(y)g(y) + ∫Fg'`, 3367–3379). Two-sided, every primitive `χ`. -/
def GarmolaDecr : Prop :=
  ZeroCount → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ (F : ℝ → ℝ) (y : ℝ), 1 ≤ y → Measurable F → AntitoneOn F (Ici y) →
      (∀ t, y ≤ t → 0 ≤ F t) →
        zsum χ {s | y < |s.im|} (fun ρ => ENNReal.ofReal (F |ρ.im|)) ≤
          (∫⁻ t in Ioi y, ENNReal.ofReal (F t * gw q t)) + ENNReal.ofReal (2 * F y * gZ q y)

/-! ## (3) The weight-specific links -/

section Plus

open HW

/-- **The pointwise decay of `G_δ` for `η₊`** (`lem:schastya` 4238–4256, `eq:saintsze`):
`9.062·(√u e^{−0.1598u} + (u/2π|δ|) e^{−0.1065(u/πδ)²})`, `u = |τ| − H`, `H = 200`;
`9.062 ≥ |Mh|₁ c₁/2π = 16.1939176·3.516/2π = 9.06193`. At `δ = 0` the Gaussian term is `0`
(`u/0 = 0`), which is the `δ = 0` case of `cor:amanita1`. -/
noncomputable def fplus (δ τ : ℝ) : ℝ :=
  9.062 * (Real.sqrt (τ - 200) * Real.exp (-0.1598 * (τ - 200)) +
    (τ - 200) / (2 * Real.pi * |δ|) * Real.exp (-0.1065 * ((τ - 200) / (Real.pi * δ)) ^ 2))

/-- **LINK [PlusReg]** — `η₊` satisfies the hypotheses of `lem:agamon` and `lem:hausierer`
(`prop:unease` 4389–4398, from `eq:mastodon`, `eq:pamiatka`, `eq:miran`, `eq:paytoplay`,
`eq:uzsu`). NUM/MELLIN; weight-specific. -/
def PlusReg : Prop := AgamonReg etaPlus ∧ HausiererReg etaPlus

/-- **LINK [PlusNorms]** — the norms of `η₊` (App. B: `eq:mastodon` 5935 `|η₊|₂ ≤ 0.800129 +
274.8569/H^{7/2} = 0.8001314`; `eq:pamiatka` 5975 `|η₊·log|₂ ≤ 0.8299818`; `eq:paytoplay` 6010 at
`σ = −1/2`: `1.062319·√Γ(3/2) = 1.0000632`; `eq:miran` 6067; `c₀` at 4401–4410 from
`eq:paytoplay`, `eq:uzsu`: `6.5362311 + 9.3195779|δ|`). NUM; weight-specific. -/
def PlusNorms : Prop :=
  MajSp.l2 etaPlus ≤ 0.80044 ∧ MajSp.l2 (llog etaPlus) ≤ 0.83 ∧ n1h etaPlus ≤ 1.00007 ∧
    MajSp.l2 (deriv etaPlus) ≤ 10.845789 ∧ ∀ δ : ℝ, c0 etaPlus δ ≤ 6.5363 + 9.3196 * |δ|

/-- **LINK [PlusDecay]** — `|G_δ(ρ)| ≤ fplus δ |Im ρ|` in the critical strip for
`|Im ρ| ≥ H + max(100, 4π²|δ|)` (`lem:schastya` 4231–4256: `G_δ(s) = (1/2π)∫_{−H}^{H} Mh(ir)
F_δ(s+1−ir) dr` by the band limit `eq:dirich2`/M1, then `cor:amanita1` with `k = 1`, `c₁ = 3.516`,
used INDIVIDUALLY — which is what the flag F2 forces — and `|Mh|₁ ≤ 16.1939176`, `eq:marpales`).
MELLIN; rests on §3 (the saddle point, 658–2788; F3 repaired, `c₁` survives) and App. B. -/
def PlusDecay : Prop :=
  ∀ (δ : ℝ) (s : ℂ), 0 < s.re → s.re < 1 → 300 ≤ |s.im| → 200 + 4 * Real.pi ^ 2 * |δ| ≤ |s.im| →
    ‖Gm etaPlus δ s‖ ≤ fplus δ |s.im|

/-- **LINK [PlusTailInt]** — the integral of `lem:schastya` (4262–4336, `eq:sibenize`,
`eq:sibabita`) with the two-sided density (F2) and a `10 %` margin over twice Helfgott's one-sided
closed form (F10: his combination of `log(q/2π)` is invalid for `q ≤ 6` at `T − H = 100`; slack at
`T − H ≥ 250`, so the range is restricted to `T ≥ 450`). ELEM (calculus). Checked in mpmath
(`scratchpad/hmsp/tails.py`): the worst ratio of the integral to the right side is `0.8814`. -/
def PlusTailInt : Prop :=
  ∀ q : ℕ, 1 ≤ q → q ≤ 400000 → ∀ δ T : ℝ, 450 ≤ T → 200 + 4 * Real.pi ^ 2 * |δ| ≤ T →
    ∫⁻ t in Ioi T, ENNReal.ofReal (fplus δ t * gw q t) ≤
      ENNReal.ofReal (2.2 * (9.462 * Real.sqrt (T - 200) * Real.exp (-0.1598 * (T - 200)) +
        11.287 * |δ| * Real.exp (-0.1065 * ((T - 200) / (Real.pi * δ)) ^ 2)) *
          Real.log (q * T / (2 * Real.pi)))

end Plus

section Phi

open HW

/-- **The pointwise decay of `G_δ` for `φ(t) = t²e^{−t²/2}`** (`lem:festavign` 3800–3998; here
`G_δ(s) = F_δ(s+2)`, `cor:amanita1` with `k = 2`, `c₂ = 3.262`, individually):
`3.262·(τ e^{−0.1598τ} + (τ/2π|δ|)² e^{−0.1065(τ/πδ)²})`. At `δ = 0` the Gaussian term is `0`. -/
noncomputable def fphi (δ τ : ℝ) : ℝ :=
  3.262 * (τ * Real.exp (-0.1598 * τ) +
    (τ / (2 * Real.pi * |δ|)) ^ 2 * Real.exp (-0.1065 * (τ / (Real.pi * δ)) ^ 2))

/-- `e^{−0.1065 (T/πδ)²}`, set to `0` at `δ = 0` (its limit), where Lean's `T/0 = 0` would give
`1`. -/
noncomputable def gq (T δ : ℝ) : ℝ :=
  if δ = 0 then 0 else Real.exp (-0.1065 * (T / (Real.pi * δ)) ^ 2)

/-- **LINK [PhiReg]** — `φ` satisfies the hypotheses of `lem:agamon` and `lem:hausierer`. ELEM. -/
def PhiReg : Prop := AgamonReg phi ∧ HausiererReg phi

/-- **LINK [PhiNorms]** — `eq:drachcat` (4000–4014): `|φ|₂² = 3√π/8` (`0.8152731`),
`|φ'|₂² = 7√π/16` (`0.8805956`), `|φ·log|₂² ≤ 0.16364` (`0.4045245`), `|φ/√t|₁ ≤ 1.07791`, and
`c₀ = (2/3)(|φ'/√t|₁ + |φ'√t|₁ + 2π|δ|(|φ/√t|₁ + |φ√t|₁)) ≤ 2.1375867 + 10.9896681|δ|` from
`1.48469, 1.72169, 1.07791, 1.54568`. ELEM (Gaussian moments); weight-specific. -/
def PhiNorms : Prop :=
  MajSp.l2 phi ≤ 0.81528 ∧ MajSp.l2 (llog phi) ≤ 0.40453 ∧ n1h phi ≤ 1.07791 ∧
    MajSp.l2 (deriv phi) ≤ 0.88060 ∧ ∀ δ : ℝ, c0 phi δ ≤ 2.1376 + 10.99 * |δ|

/-- **LINK [PhiDecay]** — `|G_δ(ρ)| ≤ fphi δ |Im ρ|` in the critical strip for
`|Im ρ| ≥ max(100, 4π²|δ|)` (`cor:amanita1`, `k = 2`, 752–769). MELLIN; rests on §3. -/
def PhiDecay : Prop :=
  ∀ (δ : ℝ) (s : ℂ), 0 < s.re → s.re < 1 → 100 ≤ |s.im| → 4 * Real.pi ^ 2 * |δ| ≤ |s.im| →
    ‖Gm phi δ s‖ ≤ fphi δ |s.im|

/-- **LINK [PhiTailInt]** — the integral of `lem:festavign` (3860–3981) with the two-sided density
and a `10 %` margin over twice the printed closed form `T log(qT/2π)(3.5e^{−0.1598T} +
0.64e^{−0.1065(T/πδ)²})` (F10: `~1 %` short at `T = 100`; the range is restricted to
`T ≥ 333`). ELEM. mpmath (`scratchpad/hmsp/tails2.py`): worst ratio `0.8981`. -/
def PhiTailInt : Prop :=
  ∀ q : ℕ, 1 ≤ q → q ≤ 400000 → ∀ δ T : ℝ, 333 ≤ T → 4 * Real.pi ^ 2 * |δ| ≤ T →
    ∫⁻ t in Ioi T, ENNReal.ofReal (fphi δ t * gw q t) ≤
      ENNReal.ofReal (2.2 * T * Real.log (q * T / (2 * Real.pi)) *
        (3.5 * Real.exp (-0.1598 * T) + 0.64 * gq T δ))

/-- **LINK [Kolona] — `eq:chemdames`/`eq:braca` (4074–4085, 4128–4168), ELEM (Fubini)**:
`err_{η₂∗_Mφ,χ}(δ,x) = ∫_{1/4}^{1} err_{φ,χ}(δw, wx) η₂(w) dw`, in absolute value. -/
def Kolona : Prop :=
  ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (δ x : ℝ), 0 < x →
    ENNReal.ofReal ‖MajSp.err (mconv eta2 phi) χ δ x‖ ≤
      ∫⁻ w in Icc (1 / 4 : ℝ) 1,
        ENNReal.ofReal (‖MajSp.err phi χ (δ * w) (w * x)‖ * eta2 w)

/-- **LINK [Eta2Moments]** — `∫η₂ = 1`, `∫w^{−1/2}η₂ ≤ 1.37259`, `∫w^{−1}η₂ = 4(log 2)² ≤
1.92182`, `∫w^{−3/2}η₂ ≤ 2.74517` (4157–4163; mpmath `1.3725830`, `1.9218121`, `2.7451660`).
ELEM (antiderivatives of `w^{−k} log w`). -/
def Eta2Moments : Prop :=
  (∫⁻ w in Icc (1 / 4 : ℝ) 1, ENNReal.ofReal (eta2 w)) ≤ ENNReal.ofReal 1 ∧
    (∫⁻ w in Icc (1 / 4 : ℝ) 1, ENNReal.ofReal (eta2 w / Real.sqrt w)) ≤
      ENNReal.ofReal 1.37259 ∧
    (∫⁻ w in Icc (1 / 4 : ℝ) 1, ENNReal.ofReal (eta2 w / w)) ≤ ENNReal.ofReal 1.92182 ∧
    (∫⁻ w in Icc (1 / 4 : ℝ) 1, ENNReal.ofReal (eta2 w / (w * Real.sqrt w))) ≤
      ENNReal.ofReal 2.74517

end Phi

section Mal

open HW

/-- **`η₊,₂(t) = η₊(t)² log(xt)`** (`prop:konechno` 4453–4457), the weight of Prop 1.5. -/
noncomputable def eta2x (x t : ℝ) : ℝ := etaPlus t ^ 2 * Real.log (x * t)

/-- **The pointwise decay of `M η₊,₂`, weakened to a pure exponential**: `10(log x + 10)
e^{−0.7(T−400)}`. Implied by `eq:cajun` (4675–4685) `8.39(log x + ½ log T)√(T/2 − H)
e^{−π(T−2H)/4}` after its flag F12 is repaired (the complex `|log s|` owes `+π/4`, and the max over
`|r| ≤ 2H` sits at `log(T + 2H)`): at `T = 450` the ratio is `≈ 17`, and it grows with `T`. -/
noncomputable def fmal (x T : ℝ) : ℝ := 10 * (Real.log x + 10) * Real.exp (-0.7 * (T - 400))

/-- **LINK [MalReg]** — `η₊,₂` satisfies the hypotheses of `lem:agamon` and `lem:hausierer` at every
`x ≥ 10¹²` (4466–4509). NUM; rests on the sup norms `eq:malgache`, `eq:dalida`, `eq:gobmark`. -/
def MalReg : Prop := ∀ x : ℝ, 10 ^ 12 ≤ x → AgamonReg (eta2x x) ∧ HausiererReg (eta2x x)

/-- **LINK [MalNorms]** — the norms of `η₊,₂` (`eq:cuahcer` 4560, `eq:sansan` 4548–4556 CORRECTED
by F13: `0.40742·(0.80044, 0.82999) = (0.32612, 0.33816)`, printed `(0.32396, 0.33592)`;
`eq:jostume` 4564–4569; `eq:comor` with `6.01|η₊,₂'|₂ ≤ 162.56 log x + 59.325`, 4536–4543, i.e.
`|η₊,₂'|₂ ≤ 27.049 log x + 9.8711`; `c₀ ≤ 18.15014 log x + 7.84532`, 4521–4535). NUM. -/
def MalNorms : Prop :=
  ∀ x : ℝ, 10 ^ 12 ≤ x →
    MajSp.l2 (eta2x x) ≤ 0.99811 * Real.log x + 0.32612 ∧
      MajSp.l2 (llog (eta2x x)) ≤ 0.32612 * Real.log x + 0.33816 ∧
      n1h (eta2x x) ≤ 1.24703 * Real.log x + 0.40745 ∧
      MajSp.l2 (deriv (eta2x x)) ≤ 27.05 * Real.log x + 9.872 ∧
      c0 (eta2x x) 0 ≤ 18.15014 * Real.log x + 7.84532

/-- **LINK [MalDecay]** — `|Mη₊,₂(ρ)| ≤ fmal x |Im ρ|` in the critical strip for `|Im ρ| ≥ 450`
(4594–4685: `eq:moses`, `eq:langosta` `|M(h_H²)|₁ ≤ 41.73727`, explicit Stirling DLMF 5.6.9 and the
digamma asymptotic DLMF 5.11.2 — CITED classical bounds, not in Mathlib). MELLIN + CITED. -/
def MalDecay : Prop :=
  ∀ x : ℝ, 10 ^ 12 ≤ x → ∀ s : ℂ, 0 < s.re → s.re < 1 → 450 ≤ |s.im| →
    ‖Gm (eta2x x) 0 s‖ ≤ fmal x |s.im|

/-- **LINK [MalTailInt]** — `∫_{450}^∞ fmal x t · gw 1 t dt ≤ 10⁻¹² log x` (mpmath: `≈ 4.6·10⁻¹³`
at `x = 10¹²`, i.e. `1.7·10⁻¹⁴ log x`). ELEM. -/
def MalTailInt : Prop :=
  ∀ x : ℝ, 10 ^ 12 ≤ x →
    ∫⁻ t in Ioi (450 : ℝ), ENNReal.ofReal (fmal x t * gw 1 t) ≤
      ENNReal.ofReal (1e-12 * Real.log x)

/-- **LINK [MalMain] — the main term of Prop 1.5** (4957–4997, CORRECTED by F4):
`|∫_0^∞ η₊²(t) log(xt) dt − (0.640206 log x − 0.021095)| ≤ 3.9·10⁻⁶ log x + 1.3·10⁻⁶`.
From VNODE-LP `∫η∘² log xt = 0.64020599736635 log x − 0.021094778698867 + O(10⁻¹⁴)`, the cross term
`2∫(η₊ − η∘)η∘ log xt` WITH its factor `2` (printed without it: `eq:kokord` `O*(1.95·10⁻⁶)`),
Cauchy–Schwarz and `eq:impath` `|η₊ − η∘|₂ ≤ 274.86/H^{7/2}` (NOT proved here; our `BandSharp`
gives only `≈ 1.5·10⁻⁴`). Exact total `3.8915·10⁻⁶ log x + 1.2613·10⁻⁶`. NUM + MELLIN. -/
def MalMain : Prop :=
  ∀ x : ℝ, 10 ^ 12 ≤ x →
    |(∫ t in Ioi (0 : ℝ), etaPlus t ^ 2 * Real.log (x * t)) -
        (0.640206 * Real.log x - 0.021095)| ≤ 3.9e-6 * Real.log x + 1.3e-6

end Mal

/-! ## (4) The algebra of the explicit formula (PROVED) -/

section Generic

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- A pointwise-larger weight gives a larger zero sum. -/
theorem zsum_mono {A : Set ℂ} {w w' : ℂ → ℝ≥0∞} (h : ∀ ρ ∈ zeroSet χ ∩ A, w ρ ≤ w' ρ) :
    zsum χ A w ≤ zsum χ A w' :=
  ENNReal.tsum_le_tsum fun ρ => mul_le_mul' le_rfl (h ρ ρ.2)

/-- A larger set of zeros gives a larger zero sum. -/
theorem zsum_mono_set {A B : Set ℂ} (h : A ⊆ B) (w : ℂ → ℝ≥0∞) : zsum χ A w ≤ zsum χ B w :=
  ENNReal.tsum_mono_subtype (fun ρ => zmult χ ρ * w ρ) (inter_subset_inter_right _ h)

/-- The zero sum is subadditive in the set. -/
theorem zsum_union (A B : Set ℂ) (w : ℂ → ℝ≥0∞) :
    zsum χ (A ∪ B) w ≤ zsum χ A w + zsum χ B w := by
  unfold zsum
  rw [inter_union_distrib_left]
  exact ENNReal.tsum_union_le (fun ρ => zmult χ ρ * w ρ) _ _

/-- Constants come out of the zero sum. -/
theorem zsum_const_mul (A : Set ℂ) (c : ℝ≥0∞) (w : ℂ → ℝ≥0∞) :
    zsum χ A (fun ρ => c * w ρ) = c * zsum χ A w := by
  unfold zsum
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext ρ
  ring

/-- **The split at height `T`**: all zeros = the low ones (`|Im ρ| ≤ T`) + the high ones. -/
theorem zsum_split (T : ℝ) (w : ℂ → ℝ≥0∞) :
    zsum χ univ w ≤ zsum χ {s | |s.im| ≤ T} w + zsum χ {s | T < |s.im|} w := by
  refine le_trans (zsum_mono_set χ (fun s _ => ?_) w) (zsum_union χ _ _ w)
  rcases le_or_gt |s.im| T with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **Where GRH enters**: below the verified height every zero has `Re ρ = 1/2`, so
`x^{Re ρ} = √x`. -/
theorem zsum_low (G : ℂ → ℂ) {T x : ℝ} (hgrh : GRHTo χ T) :
    zsum χ {s | |s.im| ≤ T} (fun ρ => ENNReal.ofReal (‖G ρ‖ * x ^ ρ.re)) ≤
      ENNReal.ofReal (Real.sqrt x) * zsum χ {s | |s.im| ≤ T} (fun ρ => ENNReal.ofReal ‖G ρ‖) := by
  rw [← zsum_const_mul]
  refine zsum_mono χ fun ρ hρ => le_of_eq ?_
  rw [hgrh ρ hρ.1 hρ.2, ← Real.sqrt_eq_rpow, ENNReal.ofReal_mul (norm_nonneg _), mul_comm]

/-- **Above the verified height a zero may lie anywhere in the strip**: `x^{Re ρ} ≤ x`. -/
theorem zsum_high (G : ℂ → ℂ) {T x : ℝ} (hx : 1 ≤ x) :
    zsum χ {s | T < |s.im|} (fun ρ => ENNReal.ofReal (‖G ρ‖ * x ^ ρ.re)) ≤
      ENNReal.ofReal x * zsum χ {s | T < |s.im|} (fun ρ => ENNReal.ofReal ‖G ρ‖) := by
  rw [← zsum_const_mul]
  refine zsum_mono χ fun ρ hρ => ?_
  rw [← ENNReal.ofReal_mul (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : x ^ ρ.re ≤ x :=
    calc x ^ ρ.re ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hρ.1.2.2.le
      _ = x := Real.rpow_one x
  have h2 := mul_le_mul_of_nonneg_left h1 (norm_nonneg (G ρ))
  linarith

omit [NeZero q] in
/-- `|η/√t|₁ ≥ 0`. -/
theorem n1h_nonneg (η : ℝ → ℝ) : 0 ≤ n1h η :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

omit [NeZero q] in
/-- `|η√t|₁ ≥ 0`. -/
theorem n1s_nonneg (η : ℝ → ℝ) : 0 ≤ n1s η :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

omit [NeZero q] in
/-- `c₀ ≥ 0`. -/
theorem c0_nonneg (η : ℝ → ℝ) (δ : ℝ) : 0 ≤ c0 η δ := by
  unfold c0
  have h1 := n1h_nonneg (deriv η)
  have h2 := n1s_nonneg (deriv η)
  have h3 : 0 ≤ 2 * Real.pi * |δ| * (n1h η + n1s η) :=
    mul_nonneg (mul_nonneg (by positivity) (abs_nonneg δ))
      (add_nonneg (n1h_nonneg η) (n1s_nonneg η))
  linarith

/-- **The explicit formula, assembled**: `lem:agamon` + the split at `T` + GRH below `T` + a bound
`Hb` on the low zeros + a bound `Tb` on the high zeros give
`|err| ≤ Tb + Hb/√x + R/x` (the shape of `prop:unease`, `prop:magoma`, `prop:konechno`). -/
theorem err_le_of_zero_sums (hEF : ExplicitFormula) {η : ℝ → ℝ} (hreg : AgamonReg η)
    (h0 : η 0 = 0) {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {δ x T Hb Tb R : ℝ}
    (hx : 1 ≤ x) (hgrh : GRHTo χ T) (hHb : 0 ≤ Hb) (hTb : 0 ≤ Tb)
    (hH : zsum χ {s | |s.im| ≤ T} (fun ρ => ENNReal.ofReal ‖Gm η δ ρ‖) ≤ ENNReal.ofReal Hb)
    (hT : zsum χ {s | T < |s.im|} (fun ρ => ENNReal.ofReal ‖Gm η δ ρ‖) ≤ ENNReal.ofReal Tb)
    (hR : c0 η δ + (Real.log q + 8) * (MajSp.l2 (deriv η) + 2 * Real.pi * |δ| * MajSp.l2 η) /
      Real.sqrt x ≤ R) :
    ‖MajSp.err η χ δ x‖ ≤ Tb + Hb / Real.sqrt x + R / x := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hA : 0 ≤ (Real.log q + 8) * (MajSp.l2 (deriv η) + 2 * Real.pi * |δ| * MajSp.l2 η) /
      Real.sqrt x := by
    have : 0 ≤ MajSp.l2 (deriv η) + 2 * Real.pi * |δ| * MajSp.l2 η :=
      add_nonneg (MajSp.l2_nonneg _)
        (mul_nonneg (mul_nonneg (by positivity) (abs_nonneg δ)) (MajSp.l2_nonneg _))
    exact div_nonneg (mul_nonneg (by linarith) this) hs0.le
  have hR0 : 0 ≤ R := le_trans (add_nonneg (c0_nonneg η δ) hA) hR
  have e := hEF η hreg h0 q χ hχ δ x hx0
  have hsplit := zsum_split χ T (fun ρ => ENNReal.ofReal (‖Gm η δ ρ‖ * x ^ ρ.re))
  have hlow := zsum_low χ (Gm η δ) (x := x) hgrh
  have hhigh := zsum_high χ (Gm η δ) (T := T) hx
  have key : ENNReal.ofReal (x * ‖MajSp.err η χ δ x‖) ≤
      ENNReal.ofReal (Hb * Real.sqrt x + Tb * x + R) := by
    calc ENNReal.ofReal (x * ‖MajSp.err η χ δ x‖)
        ≤ zsum χ univ (fun ρ => ENNReal.ofReal (‖Gm η δ ρ‖ * x ^ ρ.re)) + ENNReal.ofReal R :=
          le_trans e (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hR))
      _ ≤ (ENNReal.ofReal (Real.sqrt x) * ENNReal.ofReal Hb +
            ENNReal.ofReal x * ENNReal.ofReal Tb) + ENNReal.ofReal R :=
          add_le_add (le_trans hsplit (add_le_add (le_trans hlow (mul_le_mul' le_rfl hH))
            (le_trans hhigh (mul_le_mul' le_rfl hT)))) le_rfl
      _ = ENNReal.ofReal (Hb * Real.sqrt x + Tb * x + R) := by
          rw [← ENNReal.ofReal_mul hs0.le, ← ENNReal.ofReal_mul hx0.le,
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) hR0, mul_comm (Real.sqrt x), mul_comm x]
  have key2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp key
  calc ‖MajSp.err η χ δ x‖ = (x * ‖MajSp.err η χ δ x‖) / x := by field_simp
    _ ≤ (Hb * Real.sqrt x + Tb * x + R) / x := div_le_div_of_nonneg_right key2 hx0.le
    _ = Tb + Hb / Real.sqrt x + R / x := by
        rw [add_div, add_div, mul_div_assoc, Real.sqrt_div_self', mul_div_cancel_right₀ _ hx0.ne']
        ring

end Generic

/-! ## (5) Elementary facts: monotone decay, certified `exp` and `log` (PROVED) -/

section Elem

/-- `√u e^{−cu}` is non-increasing on `u ≥ 1/(2c)`. -/
theorem sqrt_exp_anti {c u v : ℝ} (hc : 0 < c) (hv : 1 ≤ 2 * c * v) (huv : v ≤ u) :
    Real.sqrt u * Real.exp (-c * u) ≤ Real.sqrt v * Real.exp (-c * v) := by
  have hv0 : 0 < v := by nlinarith
  have h1 : u ≤ v * Real.exp (c * (u - v)) ^ 2 := by
    have e : Real.exp (c * (u - v)) ^ 2 = Real.exp (2 * c * (u - v)) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [e]
    have h2 := Real.add_one_le_exp (2 * c * (u - v))
    have h3 : u - v ≤ v * (2 * c * (u - v)) := by nlinarith [mul_nonneg (sub_nonneg.2 huv) hc.le]
    nlinarith [mul_le_mul_of_nonneg_left h2 hv0.le]
  have h4 : Real.sqrt u ≤ Real.sqrt v * Real.exp (c * (u - v)) := by
    calc Real.sqrt u ≤ Real.sqrt (v * Real.exp (c * (u - v)) ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt v * Real.exp (c * (u - v)) := by
          rw [Real.sqrt_mul hv0.le, Real.sqrt_sq (Real.exp_pos _).le]
  calc Real.sqrt u * Real.exp (-c * u)
      ≤ Real.sqrt v * Real.exp (c * (u - v)) * Real.exp (-c * u) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = Real.sqrt v * Real.exp (-c * v) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- `u e^{−cu}` is non-increasing on `u ≥ 1/c`. -/
theorem lin_exp_anti {c u v : ℝ} (hc : 0 < c) (hv : 1 ≤ c * v) (huv : v ≤ u) :
    u * Real.exp (-c * u) ≤ v * Real.exp (-c * v) := by
  have hv0 : 0 < v := by nlinarith
  have h1 : u ≤ v * Real.exp (c * (u - v)) := by
    have h2 := Real.add_one_le_exp (c * (u - v))
    have h3 : u - v ≤ v * (c * (u - v)) := by nlinarith [mul_nonneg (sub_nonneg.2 huv) hc.le]
    nlinarith [mul_le_mul_of_nonneg_left h2 hv0.le]
  calc u * Real.exp (-c * u) ≤ v * Real.exp (c * (u - v)) * Real.exp (-c * u) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = v * Real.exp (-c * v) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- `u e^{−cu²}` is non-increasing on `u ≥ 1/√(2c)`. -/
theorem lin_gauss_anti {c u v : ℝ} (hc : 0 < c) (hv0 : 0 < v) (hv : 1 ≤ 2 * c * v ^ 2)
    (huv : v ≤ u) : u * Real.exp (-c * u ^ 2) ≤ v * Real.exp (-c * v ^ 2) := by
  have h1 : u ≤ v * Real.exp (c * (u ^ 2 - v ^ 2)) := by
    have h2 := Real.add_one_le_exp (c * (u ^ 2 - v ^ 2))
    have h4 : 1 ≤ c * v * (u + v) := by
      nlinarith [mul_nonneg (mul_nonneg hc.le hv0.le) (sub_nonneg.2 huv)]
    have h3 : u - v ≤ v * (c * (u ^ 2 - v ^ 2)) := by
      nlinarith [mul_le_mul_of_nonneg_left h4 (sub_nonneg.2 huv)]
    nlinarith [mul_le_mul_of_nonneg_left h2 hv0.le]
  calc u * Real.exp (-c * u ^ 2) ≤ v * Real.exp (c * (u ^ 2 - v ^ 2)) * Real.exp (-c * u ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = v * Real.exp (-c * v ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- `u² e^{−cu²}` is non-increasing on `u ≥ 1/√c`. -/
theorem sq_gauss_anti {c u v : ℝ} (hv0 : 0 < v) (hv : 1 ≤ c * v ^ 2)
    (huv : v ≤ u) : u ^ 2 * Real.exp (-c * u ^ 2) ≤ v ^ 2 * Real.exp (-c * v ^ 2) := by
  have huv2 : v ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hv0.le huv 2
  have h1 : u ^ 2 ≤ v ^ 2 * Real.exp (c * (u ^ 2 - v ^ 2)) := by
    have h2 := Real.add_one_le_exp (c * (u ^ 2 - v ^ 2))
    have h3 : u ^ 2 - v ^ 2 ≤ v ^ 2 * (c * (u ^ 2 - v ^ 2)) := by
      nlinarith [mul_le_mul_of_nonneg_left hv (sub_nonneg.2 huv2)]
    nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg v)]
  calc u ^ 2 * Real.exp (-c * u ^ 2)
      ≤ v ^ 2 * Real.exp (c * (u ^ 2 - v ^ 2)) * Real.exp (-c * u ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = v ^ 2 * Real.exp (-c * v ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- `e^n ≥ 2.7182818283ⁿ`. -/
theorem exp_nat_ge (n : ℕ) : (2.7182818283 : ℝ) ^ n ≤ Real.exp n := by
  rw [show (n : ℝ) = n * 1 by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n

/-- `e^n ≤ 2.7182818286ⁿ`. -/
theorem exp_nat_le (n : ℕ) : Real.exp n ≤ (2.7182818286 : ℝ) ^ n := by
  rw [show (n : ℝ) = n * 1 by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n

/-- `log y ≤ n` once `y ≤ 2.7182818283ⁿ`. -/
theorem log_le_nat (n : ℕ) {y : ℝ} (hy : 0 < y) (h : y ≤ (2.7182818283 : ℝ) ^ n) :
    Real.log y ≤ n := by
  rw [Real.log_le_iff_le_exp hy]
  exact h.trans (exp_nat_ge n)

/-- `n ≤ log y` once `2.7182818286ⁿ ≤ y`. -/
theorem nat_le_log (n : ℕ) {y : ℝ} (h : (2.7182818286 : ℝ) ^ n ≤ y) : (n : ℝ) ≤ Real.log y := by
  have hy : 0 < y := lt_of_lt_of_le (by positivity) h
  rw [Real.le_log_iff_exp_le hy]
  exact (exp_nat_le n).trans h

/-- **A certified upper bound for `e^{−(n+d)}`**: it suffices that
`B·2.7182818283ⁿ·(1 + d) ≥ 1` (`e^d ≥ 1 + d`). -/
theorem exp_neg_le (n : ℕ) {d B : ℝ} (hd : -1 ≤ d)
    (hB : 1 ≤ B * ((2.7182818283 : ℝ) ^ n * (d + 1))) : Real.exp (-(n + d)) ≤ B := by
  have h0 : (0 : ℝ) ≤ (2.7182818283 : ℝ) ^ n * (d + 1) := mul_nonneg (by positivity) (by linarith)
  have h1 : (2.7182818283 : ℝ) ^ n * (d + 1) ≤ Real.exp (n + d) := by
    rw [Real.exp_add]
    exact mul_le_mul (exp_nat_ge n) (by linarith [Real.add_one_le_exp d]) (by linarith)
      (Real.exp_pos _).le
  have hBpos : 0 < B := by
    by_contra hc
    push Not at hc
    nlinarith
  have hpos : 0 < Real.exp (n + d) := Real.exp_pos _
  have h2 : 1 ≤ B * Real.exp (n + d) := le_trans hB (mul_le_mul_of_nonneg_left h1 hBpos.le)
  rw [Real.exp_neg]
  calc (Real.exp (n + d))⁻¹ ≤ (Real.exp (n + d))⁻¹ * (B * Real.exp (n + d)) :=
        le_mul_of_one_le_right (inv_nonneg.mpr hpos.le) h2
    _ = B := by field_simp

/-- `e^{−39.95} ≤ 4.48·10⁻¹⁸` (truth `4.466·10⁻¹⁸`). -/
theorem exp_3995 : Real.exp (-39.95) ≤ 4.48e-18 := by
  have e : (-39.95 : ℝ) = -(((40 : ℕ) : ℝ) + -0.05) := by norm_num
  rw [e]
  exact exp_neg_le 40 (by norm_num) (by norm_num)

/-- `e^{−42.14} ≤ 5.1·10⁻¹⁹` (truth `5.04·10⁻¹⁹`). -/
theorem exp_4214 : Real.exp (-42.14) ≤ 5.1e-19 := by
  have e : (-42.14 : ℝ) = -(((42 : ℕ) : ℝ) + 0.14) := by norm_num
  rw [e]
  exact exp_neg_le 42 (by norm_num) (by norm_num)

/-- **The Gaussian terms at `u ≥ w₀π|δ|`**: with `e^{−0.1065w₀²} ≤ B`,
`|δ|e^{−0.1065(u/πδ)²} ≤ |δ|B` and `(u/2π|δ|)e^{−0.1065(u/πδ)²} ≤ (w₀/2)B`; both sides are `0`
at `δ = 0`. -/
theorem gauss_le {δ u w0 B : ℝ} (hw0 : 0 < w0) (hw1 : 1 ≤ 2 * 0.1065 * w0 ^ 2)
    (hB : Real.exp (-0.1065 * w0 ^ 2) ≤ B) (hu : w0 * (Real.pi * |δ|) ≤ u) :
    |δ| * Real.exp (-0.1065 * (u / (Real.pi * δ)) ^ 2) ≤ |δ| * B ∧
      u / (2 * Real.pi * |δ|) * Real.exp (-0.1065 * (u / (Real.pi * δ)) ^ 2) ≤ w0 / 2 * B := by
  have hB0 : 0 ≤ B := le_trans (Real.exp_pos _).le hB
  rcases eq_or_ne δ 0 with h | h
  · subst h
    simp only [abs_zero, zero_mul, mul_zero, div_zero, le_refl, true_and]
    positivity
  have hd : 0 < |δ| := abs_pos.mpr h
  have hpd : 0 < Real.pi * |δ| := mul_pos Real.pi_pos hd
  have hsq : (u / (Real.pi * δ)) ^ 2 = (u / (Real.pi * |δ|)) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]
  have hw : w0 ≤ u / (Real.pi * |δ|) := by rw [le_div_iff₀ hpd]; exact hu
  have hE : Real.exp (-0.1065 * (u / (Real.pi * δ)) ^ 2) ≤ B := by
    rw [hsq]
    refine le_trans (Real.exp_le_exp.mpr ?_) hB
    have := pow_le_pow_left₀ hw0.le hw 2
    linarith
  refine ⟨mul_le_mul_of_nonneg_left hE hd.le, ?_⟩
  have e : u / (2 * Real.pi * |δ|) = u / (Real.pi * |δ|) / 2 := by
    rw [div_div, mul_comm (Real.pi * |δ|) 2, mul_assoc]
  rw [e, hsq, div_mul_eq_mul_div]
  have h1 := lin_gauss_anti (c := 0.1065) (by norm_num) hw0 hw1 hw
  have h2 : w0 * Real.exp (-0.1065 * w0 ^ 2) ≤ w0 * B := mul_le_mul_of_nonneg_left hB hw0.le
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith

/-- **The squared Gaussian term**: `(u/2π|δ|)²e^{−0.1065(u/πδ)²} ≤ (w₀/2)²B` for
`u ≥ w₀π|δ|`, `0.1065 w₀² ≥ 1`, `e^{−0.1065w₀²} ≤ B`; both sides `0` at `δ = 0`. -/
theorem gauss_sq_le {δ u w0 B : ℝ} (hw0 : 0 < w0) (hw1 : 1 ≤ 0.1065 * w0 ^ 2)
    (hB : Real.exp (-0.1065 * w0 ^ 2) ≤ B) (hu : w0 * (Real.pi * |δ|) ≤ u) :
    (u / (2 * Real.pi * |δ|)) ^ 2 * Real.exp (-0.1065 * (u / (Real.pi * δ)) ^ 2) ≤
      (w0 / 2) ^ 2 * B := by
  have hB0 : 0 ≤ B := le_trans (Real.exp_pos _).le hB
  rcases eq_or_ne δ 0 with h | h
  · subst h
    simp only [abs_zero, mul_zero, div_zero]
    norm_num
    positivity
  have hd : 0 < |δ| := abs_pos.mpr h
  have hpd : 0 < Real.pi * |δ| := mul_pos Real.pi_pos hd
  have hsq : (u / (Real.pi * δ)) ^ 2 = (u / (Real.pi * |δ|)) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]
  have hw : w0 ≤ u / (Real.pi * |δ|) := by rw [le_div_iff₀ hpd]; exact hu
  have e : u / (2 * Real.pi * |δ|) = u / (Real.pi * |δ|) / 2 := by
    rw [div_div, mul_comm (Real.pi * |δ|) 2, mul_assoc]
  rw [e, hsq, div_pow]
  have h1 := sq_gauss_anti (c := 0.1065) hw0 hw1 hw
  have h2 : w0 ^ 2 * Real.exp (-0.1065 * w0 ^ 2) ≤ w0 ^ 2 * B :=
    mul_le_mul_of_nonneg_left hB (sq_nonneg _)
  have h3 : (u / (Real.pi * |δ|)) ^ 2 / 2 ^ 2 * Real.exp (-0.1065 * (u / (Real.pi * |δ|)) ^ 2) =
      1 / 4 * ((u / (Real.pi * |δ|)) ^ 2 * Real.exp (-0.1065 * (u / (Real.pi * |δ|)) ^ 2)) := by
    ring
  have h4 : (w0 / 2) ^ 2 * B = 1 / 4 * (w0 ^ 2 * B) := by ring
  rw [h3, h4]
  linarith

/-- `hbC` is monotone in the three norms (its coefficients are `≥ 0` once `qT ≥ 37`). -/
theorem hbC_mono {q T n2 nl n1 m2 ml m1 : ℝ} (hq : 1 ≤ q) (hqT : 37 ≤ q * T)
    (h2 : n2 ≤ m2) (hl : nl ≤ ml) (h1 : n1 ≤ m1) : hbC q T n2 nl n1 ≤ hbC q T m2 ml m1 := by
  have hL : (3 : ℝ) ≤ Real.log (q * T) := by
    have h := nat_le_log 3 (y := q * T) (le_trans (by norm_num) hqT)
    push_cast at h
    exact h
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hs := Real.sqrt_nonneg T
  have hA : 0 ≤ 0.7979 * Real.sqrt T * (Real.log (q * T) - 2.3378) :=
    mul_nonneg (mul_nonneg (by norm_num) hs) (by linarith)
  have hB : 0 ≤ 2.5067 * Real.sqrt T * (0.5 * Real.log (q * T) + 17.21) :=
    mul_nonneg (mul_nonneg (by norm_num) hs) (by linarith)
  have hC : 0 ≤ 0.819 * Real.log q + 16.8 + 1.4143 * (0.5 * Real.log q + 17.7) +
      1.4143 * (0.5 * Real.log (q * T) + 17.7) := by linarith
  have e : ∀ a b c : ℝ, hbC q T a b c = 0.7979 * Real.sqrt T * (Real.log (q * T) - 2.3378) * a +
      2.5067 * Real.sqrt T * (0.5 * Real.log (q * T) + 17.21) * b +
      (0.819 * Real.log q + 16.8 + 1.4143 * (0.5 * Real.log q + 17.7) +
        1.4143 * (0.5 * Real.log (q * T) + 17.7)) * c := fun a b c => by unfold hbC; ring
  rw [e, e]
  linarith [mul_le_mul_of_nonneg_left h2 hA, mul_le_mul_of_nonneg_left hl hB,
    mul_le_mul_of_nonneg_left h1 hC]

/-- `hbR` is monotone in the three norms. -/
theorem hbR_mono {q T n2 nl n1 m2 ml m1 : ℝ} (hq : 1 ≤ q) (hqT : 37 ≤ q * T)
    (h2 : n2 ≤ m2) (hl : nl ≤ ml) (h1 : n1 ≤ m1) : hbR q T n2 nl n1 ≤ hbR q T m2 ml m1 := by
  have hL : (3 : ℝ) ≤ Real.log (q * T) := by
    have h := nat_le_log 3 (y := q * T) (le_trans (by norm_num) hqT)
    push_cast at h
    exact h
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hs := Real.sqrt_nonneg T
  have hA : 0 ≤ 0.5642 * Real.sqrt T * (Real.log (q * T) - 2.3378) :=
    mul_nonneg (mul_nonneg (by norm_num) hs) (by linarith)
  have hB : 0 ≤ 1.7725 * Real.sqrt T * (0.5 * Real.log (q * T) + 17.21) :=
    mul_nonneg (mul_nonneg (by norm_num) hs) (by linarith)
  have hC : 0 ≤ 1.319 * Real.log q + 0.5 * Real.log (q * T) + 52.2 := by linarith
  have e : ∀ a b c : ℝ, hbR q T a b c = 0.5642 * Real.sqrt T * (Real.log (q * T) - 2.3378) * a +
      1.7725 * Real.sqrt T * (0.5 * Real.log (q * T) + 17.21) * b +
      (1.319 * Real.log q + 0.5 * Real.log (q * T) + 52.2) * c := fun a b c => by unfold hbR; ring
  rw [e, e]
  linarith [mul_le_mul_of_nonneg_left h2 hA, mul_le_mul_of_nonneg_left hl hB,
    mul_le_mul_of_nonneg_left h1 hC]

/-- `hbC ≥ 0` at nonnegative norms. -/
theorem hbC_nonneg {q T n2 nl n1 : ℝ} (hq : 1 ≤ q) (hqT : 37 ≤ q * T) (h2 : 0 ≤ n2) (hl : 0 ≤ nl)
    (h1 : 0 ≤ n1) : 0 ≤ hbC q T n2 nl n1 := by
  have h := hbC_mono hq hqT h2 hl h1
  have e : hbC q T 0 0 0 = 0 := by unfold hbC; ring
  linarith

/-- `hbR ≥ 0` at nonnegative norms. -/
theorem hbR_nonneg {q T n2 nl n1 : ℝ} (hq : 1 ≤ q) (hqT : 37 ≤ q * T) (h2 : 0 ≤ n2) (hl : 0 ≤ nl)
    (h1 : 0 ≤ n1) : 0 ≤ hbR q T n2 nl n1 := by
  have h := hbR_mono hq hqT h2 hl h1
  have e : hbR q T 0 0 0 = 0 := by unfold hbR; ring
  linarith

/-- `g_χ(T) ≥ 0` for `qT ≥ 1`. -/
theorem gZ_nonneg {q T : ℝ} (h : 1 ≤ q * T) : 0 ≤ gZ q T := by
  unfold gZ
  have := Real.log_nonneg h
  linarith

/-- `log(qT/2π) ≥ 0` for `qT ≥ 8`. -/
theorem log2pi_nonneg {q T : ℝ} (h : 8 ≤ q * T) : 0 ≤ Real.log (q * T / (2 * Real.pi)) := by
  refine Real.log_nonneg ((one_le_div (by positivity)).mpr ?_)
  linarith [Real.pi_lt_four]

end Elem

/-! ## (6) The `η₊` chain: `prop:unease`, corrected (PROVED from the links) -/

section PlusChain

open HW

/-- `fplus δ` is continuous. -/
theorem continuous_fplus (δ : ℝ) : Continuous (fplus δ) := by
  unfold fplus
  fun_prop

/-- `fplus δ ≥ 0` on `τ ≥ 200`. -/
theorem fplus_nonneg (δ : ℝ) {τ : ℝ} (hτ : 200 ≤ τ) : 0 ≤ fplus δ τ := by
  unfold fplus
  have h1 : 0 ≤ (τ - 200) / (2 * Real.pi * |δ|) := div_nonneg (by linarith) (by positivity)
  exact mul_nonneg (by norm_num) (add_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) (mul_nonneg h1 (Real.exp_pos _).le))

/-- **`fplus δ` is non-increasing on `[T,∞)`** for `T ≥ 450`, `T ≥ 200 + 4π²|δ|` — what
`lem:garmola`'s decreasing form needs (`lem:schastya` 4251–4252). -/
theorem fplus_antitoneOn {δ T : ℝ} (hT : 450 ≤ T) (hTd : 200 + 4 * Real.pi ^ 2 * |δ| ≤ T) :
    AntitoneOn (fplus δ) (Ici T) := by
  intro a ha b _ hab
  have ha' : T ≤ a := ha
  unfold fplus
  have h1 := sqrt_exp_anti (c := 0.1598) (u := b - 200) (v := a - 200) (by norm_num)
    (by linarith) (by linarith)
  have h2 : (b - 200) / (2 * Real.pi * |δ|) *
        Real.exp (-0.1065 * ((b - 200) / (Real.pi * δ)) ^ 2) ≤
      (a - 200) / (2 * Real.pi * |δ|) *
        Real.exp (-0.1065 * ((a - 200) / (Real.pi * δ)) ^ 2) := by
    rcases eq_or_ne δ 0 with h | h
    · subst h
      simp
    have hd : 0 < |δ| := abs_pos.mpr h
    have hpd : 0 < Real.pi * |δ| := mul_pos Real.pi_pos hd
    have hsq : ∀ u : ℝ, (u / (Real.pi * δ)) ^ 2 = (u / (Real.pi * |δ|)) ^ 2 := fun u => by
      rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]
    have e : ∀ u : ℝ, u / (2 * Real.pi * |δ|) = u / (Real.pi * |δ|) / 2 := fun u => by
      rw [div_div, mul_comm (Real.pi * |δ|) 2, mul_assoc]
    rw [hsq, hsq, e, e]
    have e4 : 4 * Real.pi * (Real.pi * |δ|) = 4 * Real.pi ^ 2 * |δ| := by ring
    have hwa : 4 * Real.pi ≤ (a - 200) / (Real.pi * |δ|) := by
      rw [le_div_iff₀ hpd]
      linarith
    have hpi := Real.pi_gt_three
    have hw0 : 0 < (a - 200) / (Real.pi * |δ|) := by linarith
    have hsq4 := pow_le_pow_left₀ (by positivity) hwa 2
    have hw1 : 1 ≤ 2 * 0.1065 * ((a - 200) / (Real.pi * |δ|)) ^ 2 := by nlinarith
    have key := lin_gauss_anti (c := 0.1065) (by norm_num) hw0 hw1
      (div_le_div_of_nonneg_right (by linarith : a - 200 ≤ b - 200) hpd.le)
    linarith [key]
  have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num : (0 : ℝ) ≤ 9.062)
  linarith

/-- **The corrected `lem:schastya` bound** for `η₊` above `T`: twice Helfgott's closed form with a
`10 %` margin (`PlusTailInt`) plus the boundary term `2·fplus(T)·g(T)` the printed lemma drops
(N1). -/
noncomputable def tailP (q T δ : ℝ) : ℝ :=
  2.2 * (9.462 * Real.sqrt (T - 200) * Real.exp (-0.1598 * (T - 200)) +
    11.287 * |δ| * Real.exp (-0.1065 * ((T - 200) / (Real.pi * δ)) ^ 2)) *
      Real.log (q * T / (2 * Real.pi)) + 2 * fplus δ T * gZ q T

/-- The residue-and-`x^{−3/2}` numerator of `prop:unease` for `η₊` at `PlusNorms`. -/
noncomputable def Rplus (q δ x : ℝ) : ℝ :=
  6.5363 + 9.3196 * |δ| +
    (Real.log q + 8) * (10.845789 + 2 * Real.pi * |δ| * 0.80044) / Real.sqrt x

/-- `tailP ≥ 0`. -/
theorem tailP_nonneg {q T δ : ℝ} (hq : 1 ≤ q) (hT : 450 ≤ T) : 0 ≤ tailP q T δ := by
  have hqT : 450 ≤ q * T := by nlinarith
  have h1 := log2pi_nonneg (q := q) (T := T) (by linarith)
  have h2 := gZ_nonneg (q := q) (T := T) (by linarith)
  have h3 := fplus_nonneg δ (τ := T) (by linarith)
  have h4 : 0 ≤ 9.462 * Real.sqrt (T - 200) * Real.exp (-0.1598 * (T - 200)) +
      11.287 * |δ| * Real.exp (-0.1065 * ((T - 200) / (Real.pi * δ)) ^ 2) := by positivity
  unfold tailP
  have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2.2) h4) h1
  have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h3) h2
  linarith

/-- **The high zeros of `η₊`, corrected `lem:schastya`** (`PlusDecay` pointwise, `GarmolaDecr`,
`PlusTailInt`). PROVED from the links. -/
theorem plus_high (hZC : ZeroCount) (hG : GarmolaDecr) (pd : PlusDecay) (pt : PlusTailInt)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : q ≤ 400000)
    {δ T : ℝ} (hT : 450 ≤ T) (hTd : 200 + 4 * Real.pi ^ 2 * |δ| ≤ T) :
    zsum χ {s | T < |s.im|} (fun ρ => ENNReal.ofReal ‖Gm etaPlus δ ρ‖) ≤
      ENNReal.ofReal (tailP q T δ) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqT : 450 ≤ (q : ℝ) * T := by nlinarith
  have hb1 := log2pi_nonneg (q := (q : ℝ)) (T := T) (by linarith)
  have hb2 := gZ_nonneg (q := (q : ℝ)) (T := T) (by linarith)
  have hb3 := fplus_nonneg δ (τ := T) (by linarith)
  have hc0 : 0 ≤ 2.2 * (9.462 * Real.sqrt (T - 200) * Real.exp (-0.1598 * (T - 200)) +
      11.287 * |δ| * Real.exp (-0.1065 * ((T - 200) / (Real.pi * δ)) ^ 2)) *
        Real.log (q * T / (2 * Real.pi)) := by positivity
  have hc1 : 0 ≤ 2 * fplus δ T * gZ q T := by positivity
  calc zsum χ {s | T < |s.im|} (fun ρ => ENNReal.ofReal ‖Gm etaPlus δ ρ‖)
      ≤ zsum χ {s | T < |s.im|} (fun ρ => ENNReal.ofReal (fplus δ |ρ.im|)) := by
        refine zsum_mono χ fun ρ hρ => ENNReal.ofReal_le_ofReal ?_
        have hlt : T < |ρ.im| := hρ.2
        exact pd δ ρ hρ.1.2.1 hρ.1.2.2 (by linarith) (by linarith)
    _ ≤ (∫⁻ t in Ioi T, ENNReal.ofReal (fplus δ t * gw q t)) +
          ENNReal.ofReal (2 * fplus δ T * gZ q T) :=
        hG hZC q χ hχ (fplus δ) T (by linarith) (continuous_fplus δ).measurable
          (fplus_antitoneOn hT hTd) (fun t ht => fplus_nonneg δ (by linarith))
    _ ≤ ENNReal.ofReal (2.2 * (9.462 * Real.sqrt (T - 200) * Real.exp (-0.1598 * (T - 200)) +
          11.287 * |δ| * Real.exp (-0.1065 * ((T - 200) / (Real.pi * δ)) ^ 2)) *
            Real.log (q * T / (2 * Real.pi))) + ENNReal.ofReal (2 * fplus δ T * gZ q T) :=
        add_le_add (pt q hq1 hq δ T hT hTd) le_rfl
    _ = ENNReal.ofReal (tailP q T δ) := by
        rw [← ENNReal.ofReal_add hc0 hc1]
        rfl

/-- **`prop:unease`, CORRECTED, for every primitive `χ`** (and the sharper real-`χ` form): at any
`T ≥ 450` with `T ≥ 200 + 4π²|δ|` and GRH to `T`,
`|err_{η₊,χ}(δ,x)| ≤ tailP + hbC(q,T; 0.80044, 0.83, 1.00007)/√x + Rplus/x`.
PROVED from `ExplicitFormula`, `ZeroCount`, `Hausierer`, `GarmolaDecr` and the four `η₊` links. -/
theorem plus_err (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer) (hG : GarmolaDecr)
    (pr : PlusReg) (pn : PlusNorms) (pd : PlusDecay) (pt : PlusTailInt)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : q ≤ 400000)
    {δ x T : ℝ} (hx : 1 ≤ x) (hT : 450 ≤ T) (hTd : 200 + 4 * Real.pi ^ 2 * |δ| ≤ T)
    (hgrh : GRHTo χ T) :
    ‖MajSp.err etaPlus χ δ x‖ ≤
        tailP q T δ + hbC q T 0.80044 0.83 1.00007 / Real.sqrt x + Rplus q δ x / x ∧
      (IsRealChar χ → ‖MajSp.err etaPlus χ δ x‖ ≤
        tailP q T δ + hbR q T 0.80044 0.83 1.00007 / Real.sqrt x + Rplus q δ x / x) := by
  obtain ⟨n2, nl, n1, nd, nc⟩ := pn
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqT : 37 ≤ (q : ℝ) * T := by nlinarith
  have hH := hHs hZC etaPlus pr.2 q χ hχ δ T (by linarith) hqT hgrh
  have hTail := plus_high hZC hG pd pt hχ hq hT hTd
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hlq : 0 ≤ Real.log q + 8 := by linarith [Real.log_nonneg hq1']
  have hR : c0 etaPlus δ + (Real.log q + 8) *
      (MajSp.l2 (deriv etaPlus) + 2 * Real.pi * |δ| * MajSp.l2 etaPlus) / Real.sqrt x ≤
        Rplus q δ x := by
    unfold Rplus
    have hpd : 0 ≤ 2 * Real.pi * |δ| := by positivity
    have h1 : MajSp.l2 (deriv etaPlus) + 2 * Real.pi * |δ| * MajSp.l2 etaPlus ≤
        10.845789 + 2 * Real.pi * |δ| * 0.80044 :=
      add_le_add nd (mul_le_mul_of_nonneg_left n2 hpd)
    have h2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hlq) hs0.le
    linarith [nc δ]
  have h0 : etaPlus 0 = 0 := etaPlus_of_nonpos le_rfl
  have hTb := tailP_nonneg (q := (q : ℝ)) (δ := δ) hq1' hT
  refine ⟨err_le_of_zero_sums hEF pr.1 h0 hχ hx hgrh
    (hbC_nonneg hq1' hqT (by norm_num) (by norm_num) (by norm_num)) hTb
    (le_trans hH.1 (ENNReal.ofReal_le_ofReal (hbC_mono hq1' hqT n2 nl n1))) hTail hR,
    fun hr => err_le_of_zero_sums hEF pr.1 h0 hχ hx hgrh
      (hbR_nonneg hq1' hqT (by norm_num) (by norm_num) (by norm_num)) hTb
      (le_trans (hH.2 hr) (ENNReal.ofReal_le_ofReal (hbR_mono hq1' hqT n2 nl n1))) hTail hR⟩

end PlusChain

/-! ## (7) Thm 1.4 at the RETYPED constants: the arithmetic (PROVED) -/

section MalporArith

/-- `√Q ≥ 1` for `Q ≥ 1`. -/
theorem one_le_sqrt' {Q : ℝ} (hQ : 1 ≤ Q) : 1 ≤ Real.sqrt Q :=
  (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)

/-- `√Q ≤ Q` for `Q ≥ 1`. -/
theorem sqrt_le_self' {Q : ℝ} (hQ : 1 ≤ Q) : Real.sqrt Q ≤ Q :=
  (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)

/-- `√x ≥ 10⁶` for `x ≥ 10¹²`. -/
theorem sqrt_x_ge' {x : ℝ} (hx : 10 ^ 12 ≤ x) : 1000000 ≤ Real.sqrt x :=
  (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)

/-- The arcs condition of `lem:schastya` at Helfgott's height: `|δ| ≤ 4r/Q` gives
`200 + 4π²|δ| ≤ 200 + 250r/Q` (`16π² ≤ 250`). -/
theorem Td_ok {Q r δ : ℝ} (hQ : 0 < Q) (hr : 0 ≤ r) (hδ : |δ| ≤ 4 * r / Q) :
    200 + 4 * Real.pi ^ 2 * |δ| ≤ 200 + 250 * r / Q := by
  have hpi : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have h1 := mul_le_mul_of_nonneg_left hδ (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2)
  have h2 : 4 * Real.pi ^ 2 * (4 * r / Q) ≤ 250 * r / Q := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hQ.le
  linarith

/-- `w₀ = 250/(4π) = 19.894…`: the Gaussian constants at Helfgott's `(T − H)/(π|δ|) ≥ 250/4π`. -/
theorem w0_facts : (0 : ℝ) < 250 / (4 * Real.pi) ∧ 250 / (4 * Real.pi) ≤ 19.9 ∧
    1 ≤ 2 * 0.1065 * (250 / (4 * Real.pi)) ^ 2 ∧
    Real.exp (-0.1065 * (250 / (4 * Real.pi)) ^ 2) ≤ 5.1e-19 := by
  have hw0 : (0 : ℝ) < 250 / (4 * Real.pi) := by positivity
  have hw0b : 19.894 ≤ 250 / (4 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_d6]
  have hw0c : 250 / (4 * Real.pi) ≤ 19.9 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_d6]
  have hsq : (19.894 : ℝ) ^ 2 ≤ (250 / (4 * Real.pi)) ^ 2 := pow_le_pow_left₀ (by norm_num) hw0b 2
  refine ⟨hw0, hw0c, by nlinarith, le_trans (Real.exp_le_exp.mpr (by nlinarith)) exp_4214⟩

/-- Helfgott's height `T = 200 + 250r/Q` (4866–4870): `T − 200 ≥ 250`, `450 ≤ QT ≤ 1.35·10⁸`,
`√(T − 200) ≤ 8661/√Q`, `log(QT/2π) ≤ 17`, `g(T) ≤ 27.2`. -/
theorem plusT_facts {Q r : ℝ} (hQ : 1 ≤ Q) (hr : r ≤ 300000) (hQr : Q ≤ r) :
    250 ≤ 250 * r / Q ∧ 450 ≤ Q * (200 + 250 * r / Q) ∧ Q * (200 + 250 * r / Q) ≤ 1.35e8 ∧
      Real.sqrt (250 * r / Q) ≤ 8661 / Real.sqrt Q ∧
      Real.log (Q * (200 + 250 * r / Q) / (2 * Real.pi)) ≤ 17 ∧
      gZ Q (200 + 250 * r / Q) ≤ 27.2 := by
  have hQ0 : 0 < Q := by linarith
  have hr0 : 0 < r := by linarith
  have hu : 250 ≤ 250 * r / Q := by rw [le_div_iff₀ hQ0]; nlinarith
  have hQT : Q * (200 + 250 * r / Q) = 200 * Q + 250 * r := by field_simp
  have hQT1 : Q * (200 + 250 * r / Q) ≤ 1.35e8 := by rw [hQT]; nlinarith
  have hQT2 : 450 ≤ Q * (200 + 250 * r / Q) := by rw [hQT]; nlinarith
  have hA0 : Real.sqrt (250 * r / Q) ≤ 8661 / Real.sqrt Q := by
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 250 * r) Q]
    exact div_le_div_of_nonneg_right ((Real.sqrt_le_left (by norm_num)).mpr (by nlinarith))
      (Real.sqrt_nonneg Q)
  have hL : Real.log (Q * (200 + 250 * r / Q) / (2 * Real.pi)) ≤ 17 := by
    have h := log_le_nat 17 (y := Q * (200 + 250 * r / Q) / (2 * Real.pi)) (by positivity) (by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three])
    push_cast at h
    exact h
  have hg : gZ Q (200 + 250 * r / Q) ≤ 27.2 := by
    have h := log_le_nat 19 (y := Q * (200 + 250 * r / Q)) (by positivity) (by linarith)
    push_cast at h
    unfold gZ
    linarith
  exact ⟨hu, hQT2, hQT1, hA0, hL, hg⟩

/-- The closing arithmetic of the `η₊` tail, over abstract atoms (`u = 1/√q`, `v = 1/q`). -/
theorem tail_close {L g A G1 G2 u v : ℝ} (hL : L ≤ 17) (hL0 : 0 ≤ L) (hg : g ≤ 27.2)
    (hg0 : 0 ≤ g) (hA : A ≤ 8661 * u * 4.48e-18) (hG1 : G1 ≤ 1.2e6 * v * 5.1e-19)
    (hG2 : G2 ≤ 9.95 * 5.1e-19) (hu : 0 ≤ u) (hv : 1 / 300000 ≤ v) :
    2.2 * (9.462 * A + 11.287 * G1) * L + 2 * (9.062 * (A + G2)) * g ≤
      6.18e-11 * u + 1.14e-9 * v := by
  have P1 : 9.462 * A + 11.287 * G1 ≤
      9.462 * (8661 * u * 4.48e-18) + 11.287 * (1.2e6 * v * 5.1e-19) := by linarith
  have P2 : A + G2 ≤ 8661 * u * 4.48e-18 + 9.95 * 5.1e-19 := by linarith
  have Q1 := mul_le_mul (mul_le_mul_of_nonneg_left P1 (by norm_num : (0 : ℝ) ≤ 2.2)) hL hL0
    (by positivity)
  have Q2 := mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left P2
    (by norm_num : (0 : ℝ) ≤ 9.062)) (by norm_num : (0 : ℝ) ≤ 2)) hg hg0 (by positivity)
  linarith only [Q1, Q2, hu, hv]

/-- **The high zeros of `η₊` at `T = 200 + 250r/Q`** (4866–4912, corrected; `q ≤ r ≤ 3·10⁵`,
`|δ| ≤ 4r/q`): `tailP ≤ 6.18·10⁻¹¹/√q + 1.14·10⁻⁹/q`, the RETYPED tail. The exponential part is
`≤ 3.284·10⁻¹¹/√q` (`1.371` of it the doubled closed form, `1.913` the boundary term N1); the
Gaussian part is `≤ 2.583·10⁻¹⁰/q` plus an absolute `2.50·10⁻¹⁵` from the boundary term — the
tightest place: at `q = 3·10⁵` the Gaussian total is `1.012·10⁻⁹/q` against `1.14·10⁻⁹/q`. -/
theorem tailP_le {Q r δ : ℝ} (hQ : 1 ≤ Q) (hr : r ≤ 300000) (hQr : Q ≤ r)
    (hδ : |δ| ≤ 4 * r / Q) :
    tailP Q (200 + 250 * r / Q) δ ≤ 6.18e-11 / Real.sqrt Q + 1.14e-9 / Q := by
  have hQ0 : 0 < Q := by linarith
  obtain ⟨hu, hQT2, -, hA0, hL, hg⟩ := plusT_facts hQ hr hQr
  obtain ⟨hw0, hw0c, hw1, hB⟩ := w0_facts
  have hT2 : 200 + 250 * r / Q - 200 = 250 * r / Q := by ring
  have hu' : 250 / (4 * Real.pi) * (Real.pi * |δ|) ≤ 200 + 250 * r / Q - 200 := by
    have e : 250 / (4 * Real.pi) * (Real.pi * |δ|) = 62.5 * |δ| := by
      field_simp
      ring
    rw [e, hT2]
    have := mul_le_mul_of_nonneg_left hδ (by norm_num : (0 : ℝ) ≤ 62.5)
    have e2 : 62.5 * (4 * r / Q) = 250 * r / Q := by ring
    linarith
  obtain ⟨hG1, hG2⟩ := gauss_le hw0 hw1 hB hu'
  have hδ' : |δ| ≤ 1.2e6 / Q := hδ.trans (div_le_div_of_nonneg_right (by linarith) hQ0.le)
  have hE : Real.exp (-0.1598 * (200 + 250 * r / Q - 200)) ≤ 4.48e-18 :=
    le_trans (Real.exp_le_exp.mpr (by linarith)) exp_3995
  have hA : Real.sqrt (200 + 250 * r / Q - 200) * Real.exp (-0.1598 * (200 + 250 * r / Q - 200)) ≤
      8661 * (1 / Real.sqrt Q) * 4.48e-18 := by
    have e : 8661 * (1 / Real.sqrt Q) = 8661 / Real.sqrt Q := by ring
    rw [e]
    rw [hT2] at hE ⊢
    exact mul_le_mul hA0 hE (Real.exp_pos _).le (by positivity)
  have hG1' : |δ| * Real.exp (-0.1065 * ((200 + 250 * r / Q - 200) / (Real.pi * δ)) ^ 2) ≤
      1.2e6 * (1 / Q) * 5.1e-19 := by
    have e : 1.2e6 * (1 / Q) = 1.2e6 / Q := by ring
    rw [e]
    exact hG1.trans (mul_le_mul_of_nonneg_right hδ' (by norm_num))
  have hG2' : (200 + 250 * r / Q - 200) / (2 * Real.pi * |δ|) *
      Real.exp (-0.1065 * ((200 + 250 * r / Q - 200) / (Real.pi * δ)) ^ 2) ≤ 9.95 * 5.1e-19 :=
    hG2.trans (mul_le_mul_of_nonneg_right (by linarith) (by norm_num))
  have hinvQ : 1 / 300000 ≤ 1 / Q := one_div_le_one_div_of_le hQ0 (by linarith)
  have key := tail_close hL (log2pi_nonneg (by linarith)) hg (gZ_nonneg (by linarith)) hA
    hG1' hG2' (by positivity) hinvQ
  calc tailP Q (200 + 250 * r / Q) δ = 2.2 * (9.462 * (Real.sqrt (200 + 250 * r / Q - 200) *
          Real.exp (-0.1598 * (200 + 250 * r / Q - 200))) + 11.287 * (|δ| *
          Real.exp (-0.1065 * ((200 + 250 * r / Q - 200) / (Real.pi * δ)) ^ 2))) *
          Real.log (Q * (200 + 250 * r / Q) / (2 * Real.pi)) +
        2 * (9.062 * (Real.sqrt (200 + 250 * r / Q - 200) *
          Real.exp (-0.1598 * (200 + 250 * r / Q - 200)) +
          (200 + 250 * r / Q - 200) / (2 * Real.pi * |δ|) *
          Real.exp (-0.1065 * ((200 + 250 * r / Q - 200) / (Real.pi * δ)) ^ 2))) *
          gZ Q (200 + 250 * r / Q) := by
        unfold tailP fplus
        ring
    _ ≤ 6.18e-11 * (1 / Real.sqrt Q) + 1.14e-9 * (1 / Q) := key
    _ = 6.18e-11 / Real.sqrt Q + 1.14e-9 / Q := by ring

/-- `log Q ≤ 13` for `Q ≤ 3·10⁵`. -/
theorem logQ_le {Q : ℝ} (hQ : 1 ≤ Q) (hQr : Q ≤ 300000) : Real.log Q ≤ 13 := by
  have h := log_le_nat 13 (y := Q) (by linarith) (by linarith)
  push_cast at h
  exact h

/-- `2π·0.80044 ≤ 5.0294`. -/
theorem twopi_plus : 2 * Real.pi * 0.80044 ≤ 5.0294 := by nlinarith [Real.pi_lt_d6]

/-- The closing arithmetic of `hbC_plus_le`, over abstract atoms (`S = √T`, `L = log qT`,
`lq = log q`, `u = 1/√q`). -/
theorem hbC_close {S L lq u : ℝ} (hS : S ≤ 11619 * u) (hS0 : 0 ≤ S) (hL19 : L ≤ 19) (hL3 : 3 ≤ L)
    (hlq : lq ≤ 13) :
    0.7979 * 0.80044 * S * (L - 2.3378) + 2.5067 * 0.83 * S * (0.5 * L + 17.21) +
      1.00007 * (0.819 * lq + 16.8 + 1.4143 * (0.5 * lq + 17.7) + 1.4143 * (0.5 * L + 17.7)) ≤
        769400 * u + 100.2 := by
  have hA : S * (L - 2.3378) ≤ 11619 * u * 16.6622 :=
    mul_le_mul hS (by linarith) (by linarith) (by linarith)
  have hB : S * (0.5 * L + 17.21) ≤ 11619 * u * 26.71 :=
    mul_le_mul hS (by linarith) (by linarith) (by linarith)
  linarith

/-- **The low zeros of `η₊` at `T = 200 + 250r/Q`, every primitive `χ`, Helfgott's norm `0.83`**
(4906–4910 corrected by F1, F2, F8): `hbC ≤ 769400/√Q + 100.2` (`66.2133·11619 = 769333`, with
`log(1.35·10⁸) ≤ 19`; the referee's `763,900` uses `18.72`). -/
theorem hbC_plus_le {Q r : ℝ} (hQ : 1 ≤ Q) (hr : r ≤ 300000) (hQr : Q ≤ r) :
    hbC Q (200 + 250 * r / Q) 0.80044 0.83 1.00007 ≤ 769400 * (1 / Real.sqrt Q) + 100.2 := by
  have hQ0 : 0 < Q := by linarith
  obtain ⟨-, hQT2, hQT1, -, -, -⟩ := plusT_facts hQ hr hQr
  have hsT : Real.sqrt (200 + 250 * r / Q) ≤ 11619 * (1 / Real.sqrt Q) := by
    have e : 200 + 250 * r / Q = Q * (200 + 250 * r / Q) / Q := by field_simp
    have e2 : 11619 * (1 / Real.sqrt Q) = 11619 / Real.sqrt Q := by ring
    rw [e2, e, Real.sqrt_div (by linarith) Q]
    exact div_le_div_of_nonneg_right ((Real.sqrt_le_left (by norm_num)).mpr (by linarith))
      (Real.sqrt_nonneg Q)
  have hL19 : Real.log (Q * (200 + 250 * r / Q)) ≤ 19 := by
    have h := log_le_nat 19 (y := Q * (200 + 250 * r / Q)) (by linarith) (by linarith)
    push_cast at h
    exact h
  have hL3 : 3 ≤ Real.log (Q * (200 + 250 * r / Q)) := by
    have h := nat_le_log 3 (y := Q * (200 + 250 * r / Q)) (le_trans (by norm_num) hQT2)
    push_cast at h
    exact h
  exact hbC_close hsT (Real.sqrt_nonneg _) hL19 hL3 (logQ_le hQ (by linarith))

/-- The residue and `x^{−3/2}` terms of `η₊` over `x`: `Rplus/x ≤ (6.6·10⁻⁶ + 11.19/√q)/√x`
(`|δ| ≤ 1.2·10⁶/q`, `x ≥ 10¹²`; the printed chain's `9 + 11|δ|` and `(log q)(11 + 6|δ|)`, with the
F6-corrected `8` in place of `6.01`). -/
theorem Rplus_le {Q r δ x : ℝ} (hQ : 1 ≤ Q) (hr : r ≤ 300000) (hQr : Q ≤ r)
    (hδ : |δ| ≤ 4 * r / Q) (hx : 10 ^ 12 ≤ x) :
    Rplus Q δ x / x ≤ (6.6e-6 + 11.19 * (1 / Real.sqrt Q)) / Real.sqrt x := by
  have hQ0 : 0 < Q := by linarith
  have hsx := sqrt_x_ge' hx
  have hsx0 : 0 < Real.sqrt x := by linarith
  have hδ' : |δ| ≤ 1.2e6 * (1 / Q) := by
    have e : 1.2e6 * (1 / Q) = 1.2e6 / Q := by ring
    rw [e]
    exact hδ.trans (div_le_div_of_nonneg_right (by linarith) hQ0.le)
  have hlq := logQ_le hQ (by linarith)
  have hlq0 : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hv : 0 ≤ 1 / Q := by positivity
  have h1 : 10.845789 + 2 * Real.pi * |δ| * 0.80044 ≤ 10.845789 + 5.0294 * (1.2e6 * (1 / Q)) := by
    have := mul_le_mul twopi_plus hδ' (abs_nonneg δ) (by norm_num)
    linarith
  have hN : (Real.log Q + 8) * (10.845789 + 2 * Real.pi * |δ| * 0.80044) ≤
      21 * (10.845789 + 5.0294 * (1.2e6 * (1 / Q))) :=
    mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
  have hN2 : (Real.log Q + 8) * (10.845789 + 2 * Real.pi * |δ| * 0.80044) / Real.sqrt x ≤
      21 * (10.845789 + 5.0294 * (1.2e6 * (1 / Q))) / 1000000 :=
    div_le_div₀ (by positivity) hN (by norm_num) hsx
  have hR : Rplus Q δ x ≤ 6.5363 + 9.3196 * (1.2e6 * (1 / Q)) +
      21 * (10.845789 + 5.0294 * (1.2e6 * (1 / Q))) / 1000000 := by
    unfold Rplus
    linarith
  have hQs : 1 / Q ≤ 1 / Real.sqrt Q :=
    one_div_le_one_div_of_le (by positivity) (sqrt_le_self' hQ)
  have hxx : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt (by linarith)).symm
  have hR2 : Rplus Q δ x / Real.sqrt x ≤ 6.6e-6 + 11.19 * (1 / Real.sqrt Q) := by
    have := div_le_div₀ (by positivity) hR (by norm_num : (0 : ℝ) < 1000000) hsx
    have e : (6.5363 + 9.3196 * (1.2e6 * (1 / Q)) +
        21 * (10.845789 + 5.0294 * (1.2e6 * (1 / Q))) / 1000000) / 1000000 =
        6.5363e-6 + 11.183520 * (1 / Q) + 2.27761569e-10 + 126.74088 * (1 / Q) / 1000000 := by
      ring
    rw [e] at this
    linarith
  calc Rplus Q δ x / x = Rplus Q δ x / Real.sqrt x / Real.sqrt x := by
        rw [div_div, ← hxx]
    _ ≤ (6.6e-6 + 11.19 * (1 / Real.sqrt Q)) / Real.sqrt x :=
        div_le_div_of_nonneg_right hR2 hsx0.le

/-- **Thm 1.4 for general `q`, RETYPED — the arithmetic** (4866–4912): at `T = 200 + 250r/q`,
`tailP + hbC/√x + Rplus/x ≤ 6.18·10⁻¹¹/√q + 1.14·10⁻⁹/q + (900000/√q + 52)/√x`. The main term
`769400/√q + 100.2 + 11.19/√q` fits `900000/√q + 52` because `48.21 ≤ 130589/√q` for `√q ≤ 548`. -/
theorem malpor_gen_arith {Q r δ x : ℝ} (hQ : 1 ≤ Q) (hr : r ≤ 300000) (hQr : Q ≤ r)
    (hδ : |δ| ≤ 4 * r / Q) (hx : 10 ^ 12 ≤ x) :
    tailP Q (200 + 250 * r / Q) δ +
        hbC Q (200 + 250 * r / Q) 0.80044 0.83 1.00007 / Real.sqrt x + Rplus Q δ x / x ≤
      6.18e-11 / Real.sqrt Q + 1.14e-9 / Q + (900000 / Real.sqrt Q + 52) / Real.sqrt x := by
  have h1 := tailP_le hQ hr hQr hδ
  have h2 := hbC_plus_le hQ hr hQr
  have h3 := Rplus_le hQ hr hQr hδ hx
  have hsx0 : 0 < Real.sqrt x := by linarith [sqrt_x_ge' hx]
  have hs548 : Real.sqrt Q ≤ 548 := (Real.sqrt_le_left (by norm_num)).mpr (by nlinarith)
  have hu : 1 / 548 ≤ 1 / Real.sqrt Q :=
    one_div_le_one_div_of_le (by linarith [one_le_sqrt' hQ]) hs548
  have h4 := div_le_div_of_nonneg_right h2 hsx0.le
  have h5 : (769400 * (1 / Real.sqrt Q) + 100.2) / Real.sqrt x +
      (6.6e-6 + 11.19 * (1 / Real.sqrt Q)) / Real.sqrt x ≤
        (900000 * (1 / Real.sqrt Q) + 52) / Real.sqrt x := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hsx0.le
  have e : (900000 / Real.sqrt Q + 52) / Real.sqrt x =
      (900000 * (1 / Real.sqrt Q) + 52) / Real.sqrt x := by ring
  rw [e]
  linarith

/-- The `q = 1` height of this spine, `T = 4.2·10⁷` (inside Platt's `10⁸`; Helfgott uses
`200 + 1.2·10⁷π ≈ 3.77·10⁷`, 4914–4940): `√(T − 200), √T ≤ 6481`, `e^{−0.1598(T−200)} ≤ 4·10⁻⁴⁴`,
`log(T/2π) ≤ 17`, `3 ≤ log T ≤ 18`, `g(T) ≤ 26.7`. -/
theorem oneT_facts : Real.sqrt (42000000 - 200) ≤ 6481 ∧ Real.sqrt 42000000 ≤ 6481 ∧
    Real.exp (-0.1598 * (42000000 - 200)) ≤ 4e-44 ∧
    Real.log (1 * 42000000 / (2 * Real.pi)) ≤ 17 ∧ Real.log (1 * 42000000) ≤ 18 ∧
    3 ≤ Real.log (1 * 42000000) ∧ gZ 1 42000000 ≤ 26.7 := by
  have hs1 : Real.sqrt (42000000 - 200) ≤ 6481 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have hs2 : Real.sqrt 42000000 ≤ 6481 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have hE : Real.exp (-0.1598 * (42000000 - 200)) ≤ 4e-44 := by
    have h := exp_neg_le 100 (d := 0) (B := 4e-44) (by norm_num) (by norm_num)
    have e : -(((100 : ℕ) : ℝ) + 0) = -100 := by norm_num
    rw [e] at h
    exact le_trans (Real.exp_le_exp.mpr (by norm_num)) h
  have hL : Real.log (1 * 42000000 / (2 * Real.pi)) ≤ 17 := by
    have h := log_le_nat 17 (y := 1 * 42000000 / (2 * Real.pi)) (by positivity) (by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three])
    push_cast at h
    exact h
  have hL18 : Real.log (1 * 42000000) ≤ 18 := by
    have h := log_le_nat 18 (y := 1 * 42000000) (by norm_num) (by norm_num)
    push_cast at h
    exact h
  have hL3 : 3 ≤ Real.log (1 * 42000000) := by
    have h := nat_le_log 3 (y := 1 * 42000000) (by norm_num)
    push_cast at h
    exact h
  refine ⟨hs1, hs2, hE, hL, hL18, hL3, ?_⟩
  have h := mul_le_mul_of_nonneg_left hL18 (by norm_num : (0 : ℝ) ≤ 0.5)
  unfold gZ
  linarith

/-- The `η₊` tail at `q = 1`, `T = 4.2·10⁷`, `|δ| ≤ 6·10⁵`: `tailP ≤ 10⁻¹³` (the Gaussian part is
`e^{−0.1065·22.28²} ≈ 10⁻²³`-small: the height buys the whole `3.34·10⁻¹¹`). -/
theorem tail_one_le {δ : ℝ} (hδ : |δ| ≤ 600000) : tailP 1 42000000 δ ≤ 1e-13 := by
  obtain ⟨hs1, -, hE, hL, -, -, hg⟩ := oneT_facts
  have hw1 : 1 ≤ 2 * 0.1065 * (22 : ℝ) ^ 2 := by norm_num
  have hB : Real.exp (-0.1065 * (22 : ℝ) ^ 2) ≤ 7.2e-23 := by
    have h := exp_neg_le 51 (d := 0) (B := 7.2e-23) (by norm_num) (by norm_num)
    have e : -(((51 : ℕ) : ℝ) + 0) = -51 := by norm_num
    rw [e] at h
    exact le_trans (Real.exp_le_exp.mpr (by norm_num)) h
  have hu' : 22 * (Real.pi * |δ|) ≤ 42000000 - 200 := by
    have := mul_le_mul_of_nonneg_left hδ (by positivity : (0 : ℝ) ≤ 22 * Real.pi)
    nlinarith [Real.pi_lt_d6]
  obtain ⟨hG1, hG2⟩ := gauss_le (by norm_num) hw1 hB hu'
  have hG1' : |δ| * Real.exp (-0.1065 * ((42000000 - 200) / (Real.pi * δ)) ^ 2) ≤ 4.32e-17 := by
    have := mul_le_mul_of_nonneg_right hδ (by norm_num : (0 : ℝ) ≤ 7.2e-23)
    linarith
  have hA : Real.sqrt (42000000 - 200) * Real.exp (-0.1598 * (42000000 - 200)) ≤ 6481 * 4e-44 :=
    mul_le_mul hs1 hE (Real.exp_pos _).le (by norm_num)
  have hL0 := log2pi_nonneg (q := 1) (T := 42000000) (by norm_num)
  have hg0 := gZ_nonneg (q := 1) (T := 42000000) (by norm_num)
  have P1 : 9.462 * (Real.sqrt (42000000 - 200) * Real.exp (-0.1598 * (42000000 - 200))) +
      11.287 * (|δ| * Real.exp (-0.1065 * ((42000000 - 200) / (Real.pi * δ)) ^ 2)) ≤
        9.462 * (6481 * 4e-44) + 11.287 * 4.32e-17 := by linarith
  have P2 : Real.sqrt (42000000 - 200) * Real.exp (-0.1598 * (42000000 - 200)) +
      (42000000 - 200) / (2 * Real.pi * |δ|) *
        Real.exp (-0.1065 * ((42000000 - 200) / (Real.pi * δ)) ^ 2) ≤
          6481 * 4e-44 + 22 / 2 * 7.2e-23 := by linarith
  have Q1 := mul_le_mul (mul_le_mul_of_nonneg_left P1 (by norm_num : (0 : ℝ) ≤ 2.2)) hL hL0
    (by norm_num)
  have Q2 := mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left P2
    (by norm_num : (0 : ℝ) ≤ 9.062)) (by norm_num : (0 : ℝ) ≤ 2)) hg hg0 (by norm_num)
  have e : tailP 1 42000000 δ = 2.2 * (9.462 * (Real.sqrt (42000000 - 200) *
      Real.exp (-0.1598 * (42000000 - 200))) + 11.287 * (|δ| *
      Real.exp (-0.1065 * ((42000000 - 200) / (Real.pi * δ)) ^ 2))) *
      Real.log (1 * 42000000 / (2 * Real.pi)) + 2 * (9.062 * (Real.sqrt (42000000 - 200) *
      Real.exp (-0.1598 * (42000000 - 200)) + (42000000 - 200) / (2 * Real.pi * |δ|) *
      Real.exp (-0.1065 * ((42000000 - 200) / (Real.pi * δ)) ^ 2))) * gZ 1 42000000 := by
    unfold tailP fplus
    ring
  rw [e]
  linarith

/-- The closing arithmetic of `hbR_one_le`, over abstract atoms (`S = √T`, `L = log T`). -/
theorem hbR_one_close {S L : ℝ} (hS : S ≤ 6481) (hL18 : L ≤ 18) (hL3 : 3 ≤ L) :
    0.5642 * 0.80044 * S * (L - 2.3378) + 1.7725 * 0.83 * S * (0.5 * L + 17.21) +
      1.00007 * (1.319 * 0 + 0.5 * L + 52.2) ≤ 295900 := by
  have hA : S * (L - 2.3378) ≤ 6481 * 15.6622 :=
    mul_le_mul hS (by linarith) (by linarith) (by norm_num)
  have hB : S * (0.5 * L + 17.21) ≤ 6481 * 26.21 :=
    mul_le_mul hS (by linarith) (by linarith) (by norm_num)
  linarith

/-- The low zeros of `η₊` at `q = 1`, `T = 4.2·10⁷`, real `χ`: `hbR ≤ 295900` (truth of this
bound `295806.6`). -/
theorem hbR_one_le : hbR 1 42000000 0.80044 0.83 1.00007 ≤ 295900 := by
  obtain ⟨-, hs2, -, -, hL18, hL3, -⟩ := oneT_facts
  unfold hbR
  rw [Real.log_one]
  exact hbR_one_close hs2 hL18 hL3

/-- The residue terms of `η₊` at `q = 1`, `|δ| ≤ 6·10⁵`: `Rplus/x ≤ 5.6/√x` for `x ≥ 10¹²`. -/
theorem Rplus_one_le {δ x : ℝ} (hδ : |δ| ≤ 600000) (hx : 10 ^ 12 ≤ x) :
    Rplus 1 δ x / x ≤ 5.6 / Real.sqrt x := by
  have hsx := sqrt_x_ge' hx
  have hsx0 : 0 < Real.sqrt x := by linarith
  have h1 : 10.845789 + 2 * Real.pi * |δ| * 0.80044 ≤ 10.845789 + 5.0294 * 600000 := by
    have := mul_le_mul twopi_plus hδ (abs_nonneg δ) (by norm_num)
    linarith
  have hN : (0 + 8) * (10.845789 + 2 * Real.pi * |δ| * 0.80044) / Real.sqrt x ≤
      8 * (10.845789 + 5.0294 * 600000) / 1000000 :=
    div_le_div₀ (by norm_num) (by linarith) (by norm_num) hsx
  have hR1 : Rplus 1 δ x ≤ 5591800 := by
    unfold Rplus
    rw [Real.log_one]
    linarith
  have hxx : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt (by linarith)).symm
  have hR2 : Rplus 1 δ x / Real.sqrt x ≤ 5.6 := by
    have h0 : Rplus 1 δ x / Real.sqrt x ≤ 5591800 / Real.sqrt x :=
      div_le_div_of_nonneg_right hR1 hsx0.le
    have h2 : 5591800 / Real.sqrt x ≤ 5591800 / 1000000 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsx
    linarith
  calc Rplus 1 δ x / x = Rplus 1 δ x / Real.sqrt x / Real.sqrt x := by rw [div_div, ← hxx]
    _ ≤ 5.6 / Real.sqrt x := div_le_div_of_nonneg_right hR2 hsx0.le

/-- **Thm 1.4 at `q = 1`, RETYPED — the arithmetic**: at `T = 4.2·10⁷`,
`tailP + hbR/√x + Rplus/x ≤ 3.34·10⁻¹¹ + 320000/√x` (`10⁻¹³ + (295900 + 5.6)/√x`; the referee's
`276,168` used Helfgott's `T ≈ 3.77·10⁷`, whose tail is `3.33·10⁻¹¹`). -/
theorem malpor_one_arith {δ x : ℝ} (hδ : |δ| ≤ 600000) (hx : 10 ^ 12 ≤ x) :
    tailP 1 42000000 δ + hbR 1 42000000 0.80044 0.83 1.00007 / Real.sqrt x + Rplus 1 δ x / x ≤
      3.34e-11 + 320000 / Real.sqrt x := by
  have hsx0 : 0 < Real.sqrt x := by linarith [sqrt_x_ge' hx]
  have h1 := tail_one_le hδ
  have h2 := div_le_div_of_nonneg_right hbR_one_le hsx0.le
  have h3 := Rplus_one_le hδ hx
  have h5 : 295900 / Real.sqrt x + 5.6 / Real.sqrt x ≤ 320000 / Real.sqrt x := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) hsx0.le
  linarith

end MalporArith

/-! ## (8) Thm 1.4 RETYPED, from the links (PROVED) -/

section MalporR

open HW

/-- **Where Platt enters**: `RT.PlattFull` is GRH to `plattHeight q` for every primitive `χ` of
conductor `q ≤ 400000`, hence GRH to any smaller height `T`. -/
theorem grh_of_platt (pf : RT.PlattFull) {q : ℕ} [NeZero q] (hq : q ≤ 400000)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {T : ℝ} (hT : T ≤ RT.plattHeight q) :
    GRHTo χ T :=
  fun s hs hTs => pf q hq χ hχ s hs.1 hs.2.1 hs.2.2 (hTs.trans hT)

/-- The trivial character mod `1` is real. -/
theorem isRealChar_one (χ : DirichletCharacter ℂ 1) : IsRealChar χ := fun a => by
  rw [Subsingleton.elim a 1, MulChar.map_one, map_one]

/-- **Thm 1.4's general clause at one conductor**, from the links and GRH to Helfgott's height
`T = 200 + 250r/q` (4854–4912; `r = 150000` odd, `300000` even). -/
theorem malpor_general (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer)
    (hG : GarmolaDecr) (pr : PlusReg) (pn : PlusNorms) (pd : PlusDecay) (pt : PlusTailInt)
    (pf : RT.PlattFull) {x : ℝ} (hx : 10 ^ 12 ≤ x) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq4 : q ≤ 400000) {r δ : ℝ}
    (hr : r ≤ 300000) (hqr : (q : ℝ) ≤ r) (hT : 200 + 250 * r / q ≤ RT.plattHeight q)
    (hδ : |δ| ≤ 4 * r / q) :
    ‖MajSp.err etaPlus χ δ x‖ ≤
      6.18e-11 / Real.sqrt q + 1.14e-9 / q + (900000 / Real.sqrt q + 52) / Real.sqrt x := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hQ0 : (0 : ℝ) < q := by linarith
  have hTge : 450 ≤ 200 + 250 * r / q := by
    have : 250 ≤ 250 * r / q := by rw [le_div_iff₀ hQ0]; nlinarith
    linarith
  have hb := (plus_err hEF hZC hHs hG pr pn pd pt hχ hq4 (le_trans (by norm_num) hx) hTge
    (Td_ok hQ0 (by linarith) hδ) (grh_of_platt pf hq4 hχ hT)).1
  exact hb.trans (malpor_gen_arith hq1 hr hqr hδ hx)

/-- **`MR.MalporR η₊` — HelfMaj Thm 1.4 at the RETYPED constants — FROM THE LINKS.** General `q`:
Helfgott's height `200 + 250r/q` (inside `RT.plattHeight`, `RT.odd_height`/`RT.even_height`);
`q = 1`: the height `4.2·10⁷` (inside Platt's `10⁸`), where the real-`χ` Hausierer applies. -/
theorem malporR_of_links (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer)
    (hG : GarmolaDecr) (pr : PlusReg) (pn : PlusNorms) (pd : PlusDecay) (pt : PlusTailInt)
    (pf : RT.PlattFull) : MR.MalporR etaPlus := by
  intro x hx q hq1 hodd hev χ hχ δ hδ
  haveI : NeZero q := ⟨by omega⟩
  have hQ0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  refine ⟨?_, fun h1 => ?_⟩
  · rcases MajSp.gcd_two q with ⟨ho, hg⟩ | ⟨he, hg⟩
    · have hqr := hodd ho
      rw [hg, Nat.cast_one, mul_one] at hδ
      have hδ' : |δ| ≤ 4 * 150000 / (q : ℝ) := by
        rw [show (4 : ℝ) * 150000 = 600000 by norm_num]
        exact hδ
      have hT : 200 + 250 * 150000 / (q : ℝ) ≤ RT.plattHeight q := by
        rw [show (250 : ℝ) * 150000 = 3.75e7 by norm_num]
        exact RT.odd_height q ho
      exact malpor_general hEF hZC hHs hG pr pn pd pt pf hx hχ (by omega) (by norm_num)
        (by exact_mod_cast hqr) hT hδ'
    · have hqr := hev he
      rw [hg] at hδ
      have hδ' : |δ| ≤ 4 * 300000 / (q : ℝ) := by
        have e : (600000 : ℝ) * ((2 : ℕ) : ℝ) = 4 * 300000 := by norm_num
        rw [← e]
        exact hδ
      have hT : 200 + 250 * 300000 / (q : ℝ) ≤ RT.plattHeight q := by
        rw [show (250 : ℝ) * 300000 = 7.5e7 by norm_num]
        exact RT.even_height q he
      exact malpor_general hEF hZC hHs hG pr pn pd pt pf hx hχ (by omega) (by norm_num)
        (by exact_mod_cast hqr) hT hδ'
  · subst h1
    have hδ1 : |δ| ≤ 600000 := by
      have e : (600000 : ℝ) * ((Nat.gcd 1 2 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) = 600000 := by norm_num
      rw [e] at hδ
      exact hδ
    have hT : (42000000 : ℝ) ≤ RT.plattHeight 1 := by
      rw [PC.plattHeight_one]
      norm_num
    have hTd : 200 + 4 * Real.pi ^ 2 * |δ| ≤ 42000000 := by
      have hpi : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
      have := mul_le_mul hpi hδ1 (abs_nonneg δ) (by norm_num)
      nlinarith
    have hb := (plus_err hEF hZC hHs hG pr pn pd pt hχ (by norm_num) (le_trans (by norm_num) hx)
      (by norm_num) hTd (grh_of_platt pf (by norm_num) hχ hT)).2 (isRealChar_one χ)
    rw [Nat.cast_one] at hb
    exact hb.trans (malpor_one_arith hδ1 hx)

end MalporR

/-! ## (9) The `φ` chain, `prop:magoma` corrected, and Cor 1.3 RETYPED (PROVED from the links) -/

section PhiChain

open HW

/-- `fphi δ` is continuous. -/
theorem continuous_fphi (δ : ℝ) : Continuous (fphi δ) := by
  unfold fphi
  fun_prop

/-- `fphi δ ≥ 0` on `τ ≥ 0`. -/
theorem fphi_nonneg (δ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ fphi δ τ := by
  unfold fphi
  exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hτ (Real.exp_pos _).le)
    (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))

/-- **`fphi δ` is non-increasing on `[T,∞)`** for `T ≥ 333`, `T ≥ 4π²|δ|` (`lem:festavign`). -/
theorem fphi_antitoneOn {δ T : ℝ} (hT : 333 ≤ T) (hTd : 4 * Real.pi ^ 2 * |δ| ≤ T) :
    AntitoneOn (fphi δ) (Ici T) := by
  intro a ha b _ hab
  have ha' : T ≤ a := ha
  unfold fphi
  have h1 := lin_exp_anti (c := 0.1598) (u := b) (v := a) (by norm_num) (by linarith) hab
  have h2 : (b / (2 * Real.pi * |δ|)) ^ 2 * Real.exp (-0.1065 * (b / (Real.pi * δ)) ^ 2) ≤
      (a / (2 * Real.pi * |δ|)) ^ 2 * Real.exp (-0.1065 * (a / (Real.pi * δ)) ^ 2) := by
    rcases eq_or_ne δ 0 with h | h
    · subst h
      simp
    have hd : 0 < |δ| := abs_pos.mpr h
    have hpd : 0 < Real.pi * |δ| := mul_pos Real.pi_pos hd
    have hsq : ∀ u : ℝ, (u / (Real.pi * δ)) ^ 2 = (u / (Real.pi * |δ|)) ^ 2 := fun u => by
      rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]
    have e : ∀ u : ℝ, u / (2 * Real.pi * |δ|) = u / (Real.pi * |δ|) / 2 := fun u => by
      rw [div_div, mul_comm (Real.pi * |δ|) 2, mul_assoc]
    rw [hsq, hsq, e, e]
    have e4 : 4 * Real.pi * (Real.pi * |δ|) = 4 * Real.pi ^ 2 * |δ| := by ring
    have hwa : 4 * Real.pi ≤ a / (Real.pi * |δ|) := by
      rw [le_div_iff₀ hpd]
      linarith
    have hpi := Real.pi_gt_three
    have hw0 : 0 < a / (Real.pi * |δ|) := by linarith
    have hsq4 := pow_le_pow_left₀ (by positivity) hwa 2
    have hw1 : 1 ≤ 0.1065 * (a / (Real.pi * |δ|)) ^ 2 := by nlinarith
    have key := sq_gauss_anti (c := 0.1065) hw0 hw1
      (div_le_div_of_nonneg_right hab hpd.le)
    linarith [key]
  have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num : (0 : ℝ) ≤ 3.262)
  linarith

/-- **The corrected `lem:festavign` bound** for `φ` above `T`: twice the printed closed form with a
`10 %` margin (`PhiTailInt`) plus the boundary term `2·fphi(T)·g(T)` (N1). -/
noncomputable def tailF (q T δ : ℝ) : ℝ :=
  2.2 * T * Real.log (q * T / (2 * Real.pi)) * (3.5 * Real.exp (-0.1598 * T) + 0.64 * gq T δ) +
    2 * fphi δ T * gZ q T

/-- The residue-and-`x^{−3/2}` numerator of `prop:magoma` at `PhiNorms`. -/
noncomputable def Rphi (q δ x : ℝ) : ℝ :=
  2.1376 + 10.99 * |δ| + (Real.log q + 8) * (0.88060 + 2 * Real.pi * |δ| * 0.81528) / Real.sqrt x

/-- `gq ≥ 0`. -/
theorem gq_nonneg (T δ : ℝ) : 0 ≤ gq T δ := by
  unfold gq
  split_ifs
  · exact le_refl 0
  · exact (Real.exp_pos _).le

/-- `tailF ≥ 0`. -/
theorem tailF_nonneg {q T δ : ℝ} (hq : 1 ≤ q) (hT : 333 ≤ T) : 0 ≤ tailF q T δ := by
  have hqT : 333 ≤ q * T := by nlinarith
  have h1 := log2pi_nonneg (q := q) (T := T) (by linarith)
  have h2 := gZ_nonneg (q := q) (T := T) (by linarith)
  have h3 := fphi_nonneg δ (τ := T) (by linarith)
  have h4 : 0 ≤ 3.5 * Real.exp (-0.1598 * T) + 0.64 * gq T δ := by
    have := gq_nonneg T δ
    positivity
  unfold tailF
  have := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2.2)
    (by linarith : (0 : ℝ) ≤ T)) h1) h4
  have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h3) h2
  linarith

/-- **The high zeros of `φ`, corrected `lem:festavign`** (`PhiDecay`, `GarmolaDecr`,
`PhiTailInt`). PROVED from the links. -/
theorem phi_high (hZC : ZeroCount) (hG : GarmolaDecr) (fd : PhiDecay) (ft : PhiTailInt)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : q ≤ 400000)
    {δ T : ℝ} (hT : 333 ≤ T) (hTd : 4 * Real.pi ^ 2 * |δ| ≤ T) :
    zsum χ {s | T < |s.im|} (fun ρ => ENNReal.ofReal ‖Gm phi δ ρ‖) ≤
      ENNReal.ofReal (tailF q T δ) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqT : 333 ≤ (q : ℝ) * T := by nlinarith
  have hb1 := log2pi_nonneg (q := (q : ℝ)) (T := T) (by linarith)
  have hb2 := gZ_nonneg (q := (q : ℝ)) (T := T) (by linarith)
  have hb3 := fphi_nonneg δ (τ := T) (by linarith)
  have hb4 : 0 ≤ 3.5 * Real.exp (-0.1598 * T) + 0.64 * gq T δ := by
    have := gq_nonneg T δ
    positivity
  have hc0 : 0 ≤ 2.2 * T * Real.log (q * T / (2 * Real.pi)) *
      (3.5 * Real.exp (-0.1598 * T) + 0.64 * gq T δ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hb1) hb4
  have hc1 : 0 ≤ 2 * fphi δ T * gZ q T := by positivity
  calc zsum χ {s | T < |s.im|} (fun ρ => ENNReal.ofReal ‖Gm phi δ ρ‖)
      ≤ zsum χ {s | T < |s.im|} (fun ρ => ENNReal.ofReal (fphi δ |ρ.im|)) := by
        refine zsum_mono χ fun ρ hρ => ENNReal.ofReal_le_ofReal ?_
        have hlt : T < |ρ.im| := hρ.2
        exact fd δ ρ hρ.1.2.1 hρ.1.2.2 (by linarith) (by linarith)
    _ ≤ (∫⁻ t in Ioi T, ENNReal.ofReal (fphi δ t * gw q t)) +
          ENNReal.ofReal (2 * fphi δ T * gZ q T) :=
        hG hZC q χ hχ (fphi δ) T (by linarith) (continuous_fphi δ).measurable
          (fphi_antitoneOn hT hTd) (fun t ht => fphi_nonneg δ (by linarith))
    _ ≤ ENNReal.ofReal (2.2 * T * Real.log (q * T / (2 * Real.pi)) *
          (3.5 * Real.exp (-0.1598 * T) + 0.64 * gq T δ)) +
          ENNReal.ofReal (2 * fphi δ T * gZ q T) :=
        add_le_add (ft q hq1 hq δ T hT hTd) le_rfl
    _ = ENNReal.ofReal (tailF q T δ) := by
        rw [← ENNReal.ofReal_add hc0 hc1]
        rfl

/-- **`prop:magoma`, CORRECTED, for every primitive `χ`**: at `T ≥ 333`, `T ≥ 4π²|δ|` and GRH to
`T`, `|err_{φ,χ}(δ,x)| ≤ tailF + hbC(q,T; 0.81528, 0.40453, 1.07791)/√x + Rphi/x`. PROVED from
`ExplicitFormula`, `ZeroCount`, `Hausierer`, `GarmolaDecr` and the four `φ` links. -/
theorem phi_err (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer) (hG : GarmolaDecr)
    (fr : PhiReg) (fn : PhiNorms) (fd : PhiDecay) (ft : PhiTailInt)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : q ≤ 400000)
    {δ x T : ℝ} (hx : 1 ≤ x) (hT : 333 ≤ T) (hTd : 4 * Real.pi ^ 2 * |δ| ≤ T)
    (hgrh : GRHTo χ T) :
    ‖MajSp.err phi χ δ x‖ ≤
      tailF q T δ + hbC q T 0.81528 0.40453 1.07791 / Real.sqrt x + Rphi q δ x / x := by
  obtain ⟨n2, nl, n1, nd, nc⟩ := fn
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqT : 37 ≤ (q : ℝ) * T := by nlinarith
  have hH := hHs hZC phi fr.2 q χ hχ δ T (by linarith) hqT hgrh
  have hTail := phi_high hZC hG fd ft hχ hq hT hTd
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hlq : 0 ≤ Real.log q + 8 := by linarith [Real.log_nonneg hq1']
  have hR : c0 phi δ + (Real.log q + 8) *
      (MajSp.l2 (deriv phi) + 2 * Real.pi * |δ| * MajSp.l2 phi) / Real.sqrt x ≤ Rphi q δ x := by
    unfold Rphi
    have hpd : 0 ≤ 2 * Real.pi * |δ| := by positivity
    have h1 : MajSp.l2 (deriv phi) + 2 * Real.pi * |δ| * MajSp.l2 phi ≤
        0.88060 + 2 * Real.pi * |δ| * 0.81528 :=
      add_le_add nd (mul_le_mul_of_nonneg_left n2 hpd)
    have h2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hlq) hs0.le
    linarith [nc δ]
  have h0 : phi 0 = 0 := by simp [phi]
  exact err_le_of_zero_sums hEF fr.1 h0 hχ hx hgrh
    (hbC_nonneg hq1' hqT (by norm_num) (by norm_num) (by norm_num)) (tailF_nonneg hq1' hT)
    (le_trans hH.1 (ENNReal.ofReal_le_ofReal (hbC_mono hq1' hqT n2 nl n1))) hTail hR

end PhiChain

section CoprarArith

open HW

/-- The height of Cor 1.3, `T = 10⁸/Q` (4817): `T ≥ 333.3`, `QT = 10⁸`, `√T = 10⁴/√Q`,
`log(QT/2π) ≤ 17`, `3 ≤ log QT ≤ 19`, `g(T) ≤ 27.2`. -/
theorem coprT_facts {Q : ℝ} (hQ : 1 ≤ Q) (hQr : Q ≤ 300000) :
    333.33 ≤ 1e8 / Q ∧ Q * (1e8 / Q) = 1e8 ∧ Real.sqrt (1e8 / Q) = 10000 * (1 / Real.sqrt Q) ∧
      Real.log (Q * (1e8 / Q) / (2 * Real.pi)) ≤ 17 ∧ Real.log (Q * (1e8 / Q)) ≤ 19 ∧
      3 ≤ Real.log (Q * (1e8 / Q)) ∧ gZ Q (1e8 / Q) ≤ 27.2 := by
  have hQ0 : 0 < Q := by linarith
  have hT : 333.33 ≤ 1e8 / Q := by rw [le_div_iff₀ hQ0]; nlinarith
  have hQT : Q * (1e8 / Q) = 1e8 := by field_simp
  have hs : Real.sqrt (1e8 / Q) = 10000 * (1 / Real.sqrt Q) := by
    rw [Real.sqrt_div (by norm_num) Q, show (1e8 : ℝ) = 10000 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    ring
  have hL : Real.log (Q * (1e8 / Q) / (2 * Real.pi)) ≤ 17 := by
    rw [hQT]
    have h := log_le_nat 17 (y := 1e8 / (2 * Real.pi)) (by positivity) (by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three])
    push_cast at h
    exact h
  have hL19 : Real.log (Q * (1e8 / Q)) ≤ 19 := by
    rw [hQT]
    have h := log_le_nat 19 (y := 1e8) (by norm_num) (by norm_num)
    push_cast at h
    exact h
  have hL3 : 3 ≤ Real.log (Q * (1e8 / Q)) := by
    rw [hQT]
    have h := nat_le_log 3 (y := 1e8) (by norm_num)
    push_cast at h
    exact h
  refine ⟨hT, hQT, hs, hL, hL19, hL3, ?_⟩
  have h := mul_le_mul_of_nonneg_left hL19 (by norm_num : (0 : ℝ) ≤ 0.5)
  unfold gZ
  linarith

/-- `e^{−53.26} ≤ 7.7·10⁻²⁴` (truth `7.65·10⁻²⁴`). -/
theorem exp_5326 : Real.exp (-53.26) ≤ 7.7e-24 := by
  have e : (-53.26 : ℝ) = -(((53 : ℕ) : ℝ) + 0.26) := by norm_num
  rw [e]
  exact exp_neg_le 53 (by norm_num) (by norm_num)

/-- `e^{−74} ≤ 7.5·10⁻³³` (truth `7.28·10⁻³³`). -/
theorem exp_74 : Real.exp (-74) ≤ 7.5e-33 := by
  have e : (-74 : ℝ) = -(((74 : ℕ) : ℝ) + 0) := by norm_num
  rw [e]
  exact exp_neg_le 74 (by norm_num) (by norm_num)

/-- The closing arithmetic of the `φ` tail, over abstract atoms (`v = 1/q`). -/
theorem tailF_close {L g E G1 G2 v : ℝ} (hL : L ≤ 17) (hg : g ≤ 27.2)
    (hg0 : 0 ≤ g) (hE : E ≤ 7.7e-24) (hE0 : 0 ≤ E) (hG1 : G1 ≤ 7.5e-33) (hG10 : 0 ≤ G1)
    (hG2 : G2 ≤ 13.25 ^ 2 * 7.5e-33) (hG20 : 0 ≤ G2) (hv : 1 / 300000 ≤ v) :
    2.2 * (1e8 * v) * L * (3.5 * E + 0.64 * G1) + 2 * (3.262 * (1e8 * v * E + G2)) * g ≤
      2.5e-13 * v := by
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv
  have P1 : 3.5 * E + 0.64 * G1 ≤ 3.5 * 7.7e-24 + 0.64 * 7.5e-33 := by linarith
  have P1' : 1e8 * v * L ≤ 1e8 * v * 17 := mul_le_mul_of_nonneg_left hL (by positivity)
  have Q1 := mul_le_mul P1' P1 (by positivity) (by positivity)
  have hvE : v * E ≤ v * 7.7e-24 := mul_le_mul_of_nonneg_left hE hv0
  have P2 : 1e8 * v * E + G2 ≤ 1e8 * v * 7.7e-24 + 13.25 ^ 2 * 7.5e-33 := by nlinarith
  have P2n : 0 ≤ 1e8 * v * E + G2 := by positivity
  have Q2 := mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left P2
    (by norm_num : (0 : ℝ) ≤ 3.262)) (by norm_num : (0 : ℝ) ≤ 2)) hg hg0 (by positivity)
  nlinarith

/-- **The high zeros of `φ` at `T = 10⁸/Q`** (4817–4822, corrected; `|δ| ≤ 1.2·10⁶/Q`):
`tailF ≤ 2.5·10⁻¹³/Q` (`2.374·10⁻¹³/Q`: `1.008` the doubled closed form, `1.366` the boundary
term N1; the Gaussian part is `≈ 10⁻²⁸`). -/
theorem tailF_le {Q δ : ℝ} (hQ : 1 ≤ Q) (hQr : Q ≤ 300000) (hδ : |δ| ≤ 1.2e6 / Q) :
    tailF Q (1e8 / Q) δ ≤ 2.5e-13 * (1 / Q) := by
  have hQ0 : 0 < Q := by linarith
  obtain ⟨hT, -, -, hL, -, -, hg⟩ := coprT_facts hQ hQr
  have hE : Real.exp (-0.1598 * (1e8 / Q)) ≤ 7.7e-24 :=
    le_trans (Real.exp_le_exp.mpr (by nlinarith)) exp_5326
  have hB : Real.exp (-0.1065 * (26.5 : ℝ) ^ 2) ≤ 7.5e-33 :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) exp_74
  have hu : 26.5 * (Real.pi * |δ|) ≤ 1e8 / Q := by
    have h1 := mul_le_mul_of_nonneg_left hδ (by positivity : (0 : ℝ) ≤ 26.5 * Real.pi)
    have h2 : 26.5 * Real.pi * (1.2e6 / Q) ≤ 1e8 / Q := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_lt_d6]) hQ0.le
    nlinarith
  have hG1 : gq (1e8 / Q) δ ≤ 7.5e-33 := by
    unfold gq
    split_ifs with h
    · norm_num
    · have hd : 0 < |δ| := abs_pos.mpr h
      have := (gauss_le (by norm_num) (by norm_num) hB hu).1
      exact le_of_mul_le_mul_left this hd
  have hG2 := gauss_sq_le (by norm_num) (by norm_num) hB hu
  have hL0 := log2pi_nonneg (q := Q) (T := 1e8 / Q) (by rw [coprT_facts hQ hQr |>.2.1]; norm_num)
  have hg0 := gZ_nonneg (q := Q) (T := 1e8 / Q) (by rw [coprT_facts hQ hQr |>.2.1]; norm_num)
  have hinvQ : 1 / 300000 ≤ 1 / Q := one_div_le_one_div_of_le hQ0 hQr
  have hG2' : (1e8 / Q / (2 * Real.pi * |δ|)) ^ 2 *
      Real.exp (-0.1065 * (1e8 / Q / (Real.pi * δ)) ^ 2) ≤ 13.25 ^ 2 * 7.5e-33 := by
    have e2 : (26.5 / 2 : ℝ) ^ 2 * 7.5e-33 = 13.25 ^ 2 * 7.5e-33 := by norm_num
    rw [← e2]
    exact hG2
  have hG20 : 0 ≤ (1e8 / Q / (2 * Real.pi * |δ|)) ^ 2 *
      Real.exp (-0.1065 * (1e8 / Q / (Real.pi * δ)) ^ 2) := by positivity
  have e : tailF Q (1e8 / Q) δ = 2.2 * (1e8 * (1 / Q)) * Real.log (Q * (1e8 / Q) / (2 * Real.pi)) *
      (3.5 * Real.exp (-0.1598 * (1e8 / Q)) + 0.64 * gq (1e8 / Q) δ) + 2 * (3.262 *
      (1e8 * (1 / Q) * Real.exp (-0.1598 * (1e8 / Q)) +
      (1e8 / Q / (2 * Real.pi * |δ|)) ^ 2 *
        Real.exp (-0.1065 * (1e8 / Q / (Real.pi * δ)) ^ 2))) * gZ Q (1e8 / Q) := by
    unfold tailF fphi
    ring
  rw [e]
  exact tailF_close hL hg hg0 hE (Real.exp_pos _).le hG1 (gq_nonneg _ _) hG2' hG20 hinvQ

/-- **The low zeros of `φ` at `T = 10⁸/Q`, every primitive `χ`** (4833–4838 corrected by F1, F2,
F8, F9): `hbC ≤ 379300/√Q + 108` (`37.924·10⁴`; the referee's complex-`χ` `513,958` is `1.37259`
times this after the `η₂` transfer). -/
theorem hbC_phi_close {S L lq u : ℝ} (hS : S = 10000 * u) (hu : 0 ≤ u) (hL19 : L ≤ 19)
    (hL3 : 3 ≤ L) (hlq : lq ≤ 13) :
    0.7979 * 0.81528 * S * (L - 2.3378) + 2.5067 * 0.40453 * S * (0.5 * L + 17.21) +
      1.07791 * (0.819 * lq + 16.8 + 1.4143 * (0.5 * lq + 17.7) + 1.4143 * (0.5 * L + 17.7)) ≤
        379300 * u + 108 := by
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hA : S * (L - 2.3378) ≤ 10000 * u * 16.6622 :=
    mul_le_mul (le_of_eq hS) (by linarith) (by linarith) (by positivity)
  have hB : S * (0.5 * L + 17.21) ≤ 10000 * u * 26.71 :=
    mul_le_mul (le_of_eq hS) (by linarith) (by linarith) (by positivity)
  linarith

/-- `hbC` for `φ` at `T = 10⁸/Q`: `≤ 379300/√Q + 108`. -/
theorem hbC_phi_le {Q : ℝ} (hQ : 1 ≤ Q) (hQr : Q ≤ 300000) :
    hbC Q (1e8 / Q) 0.81528 0.40453 1.07791 ≤ 379300 * (1 / Real.sqrt Q) + 108 := by
  obtain ⟨-, -, hs, -, hL19, hL3, -⟩ := coprT_facts hQ hQr
  exact hbC_phi_close hs (by positivity) hL19 hL3 (logQ_le hQ hQr)

/-- `2π·0.81528 ≤ 5.1226`. -/
theorem twopi_phi : 2 * Real.pi * 0.81528 ≤ 5.1226 := by nlinarith [Real.pi_lt_d6]

/-- **Cor 1.3, RETYPED — the closing arithmetic** over abstract atoms: with `u = 1/√q`,
`v = 1/q ≤ u`, `sx = √x ≥ 10⁴`, the `η₂`-averaged bound
`2.5·10⁻¹³v + 1.37259·(379300u + 108)/sx + 1.92182·(2.1376 + 10.99|δ|)/x +
2.74517·21·(0.8806 + 5.1226|δ|)/(x·sx)` is at most `3·10⁻¹³v + (650000u + 80)/sx`. -/
theorem coprar_close {u v sx d : ℝ} (hv : v ≤ u) (hv0 : 0 ≤ v) (hu : 1 / 548 ≤ u)
    (hsx : 10000 ≤ sx) (hd : d ≤ 1.2e6 * v) :
    2.5e-13 * v + 1.37259 * ((379300 * u + 108) / sx) +
        1.92182 * ((2.1376 + 10.99 * d) / (sx * sx)) +
        2.74517 * (21 * (0.88060 + 5.1226 * d) / (sx * sx * sx)) ≤
      3e-13 * v + (650000 * u + 80) / sx := by
  have hsx0 : 0 < sx := by linarith
  have h2 : (2.1376 + 10.99 * d) / (sx * sx) ≤ (2.1376 + 10.99 * (1.2e6 * v)) / 10000 / sx := by
    rw [div_div]
    exact div_le_div₀ (by positivity) (by linarith) (by positivity) (by nlinarith)
  have h3 : 21 * (0.88060 + 5.1226 * d) / (sx * sx * sx) ≤
      21 * (0.88060 + 5.1226 * (1.2e6 * v)) / 100000000 / sx := by
    rw [div_div]
    exact div_le_div₀ (by positivity) (by nlinarith) (by positivity) (by nlinarith)
  have h4 : 1.37259 * ((379300 * u + 108) / sx) +
      1.92182 * ((2.1376 + 10.99 * (1.2e6 * v)) / 10000 / sx) +
      2.74517 * (21 * (0.88060 + 5.1226 * (1.2e6 * v)) / 100000000 / sx) =
        (1.37259 * (379300 * u + 108) + 1.92182 * ((2.1376 + 10.99 * (1.2e6 * v)) / 10000) +
          2.74517 * (21 * (0.88060 + 5.1226 * (1.2e6 * v)) / 100000000)) / sx := by ring
  have h5 : (1.37259 * (379300 * u + 108) + 1.92182 * ((2.1376 + 10.99 * (1.2e6 * v)) / 10000) +
      2.74517 * (21 * (0.88060 + 5.1226 * (1.2e6 * v)) / 100000000)) / sx ≤
        (650000 * u + 80) / sx :=
    div_le_div_of_nonneg_right (by linarith) hsx0.le
  linarith

end CoprarArith

section CoprarR

open HW

/-- `η₂` is measurable. -/
theorem measurable_eta2 : Measurable eta2 := by
  unfold eta2
  exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const

/-- **The `η₂`-transfer, algebra**: a bound `C₀ + C₁w^{−1/2} + C₂w^{−1} + C₃w^{−3/2}` for
`|err_{φ,χ}(δw, wx)|` on `[1/4, 1]` gives `C₀ + 1.37259C₁ + 1.92182C₂ + 2.74517C₃` for
`|err_{η₂∗_Mφ,χ}(δ,x)|` (`Kolona`, `Eta2Moments`; the step `eq:braca` ⇒ `eq:monte`, 4157–4168). -/
theorem kolona_transfer (ko : Kolona) (mo : Eta2Moments) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {δ x C0 C1 C2 C3 : ℝ} (hx : 0 < x) (h0 : 0 ≤ C0) (h1 : 0 ≤ C1) (h2 : 0 ≤ C2) (h3 : 0 ≤ C3)
    (hb : ∀ w ∈ Icc (1 / 4 : ℝ) 1, ‖MajSp.err phi χ (δ * w) (w * x)‖ ≤
      C0 + C1 * (1 / Real.sqrt w) + C2 * (1 / w) + C3 * (1 / (w * Real.sqrt w))) :
    ‖MajSp.err (mconv eta2 phi) χ δ x‖ ≤ C0 + 1.37259 * C1 + 1.92182 * C2 + 2.74517 * C3 := by
  obtain ⟨m0, m1, m2, m3⟩ := mo
  have hpt : ∀ w ∈ Icc (1 / 4 : ℝ) 1,
      ENNReal.ofReal (‖MajSp.err phi χ (δ * w) (w * x)‖ * eta2 w) ≤
        ENNReal.ofReal C0 * ENNReal.ofReal (eta2 w) +
          ENNReal.ofReal C1 * ENNReal.ofReal (eta2 w / Real.sqrt w) +
          ENNReal.ofReal C2 * ENNReal.ofReal (eta2 w / w) +
          ENNReal.ofReal C3 * ENNReal.ofReal (eta2 w / (w * Real.sqrt w)) := by
    intro w hw
    have he := eta2_nonneg w
    have hw0 : 0 < w := by linarith [hw.1]
    have hs0 := Real.sqrt_nonneg w
    have a0 : 0 ≤ eta2 w / Real.sqrt w := div_nonneg he hs0
    have a1 : 0 ≤ eta2 w / w := div_nonneg he hw0.le
    have a2 : 0 ≤ eta2 w / (w * Real.sqrt w) := div_nonneg he (mul_nonneg hw0.le hs0)
    rw [← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2,
      ← ENNReal.ofReal_mul h3, ← ENNReal.ofReal_add (mul_nonneg h0 he) (mul_nonneg h1 a0),
      ← ENNReal.ofReal_add (by positivity) (mul_nonneg h2 a1),
      ← ENNReal.ofReal_add (by positivity) (mul_nonneg h3 a2)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb' := mul_le_mul_of_nonneg_right (hb w hw) he
    have e : (C0 + C1 * (1 / Real.sqrt w) + C2 * (1 / w) + C3 * (1 / (w * Real.sqrt w))) *
        eta2 w = C0 * eta2 w + C1 * (eta2 w / Real.sqrt w) + C2 * (eta2 w / w) +
          C3 * (eta2 w / (w * Real.sqrt w)) := by ring
    linarith
  have hm0 : Measurable (fun w : ℝ => ENNReal.ofReal C0 * ENNReal.ofReal (eta2 w)) := by
    have := measurable_eta2
    fun_prop
  have hm1 : Measurable (fun w : ℝ => ENNReal.ofReal C1 * ENNReal.ofReal (eta2 w / Real.sqrt w)) :=
    by
    have := measurable_eta2
    fun_prop
  have hm2 : Measurable (fun w : ℝ => ENNReal.ofReal C2 * ENNReal.ofReal (eta2 w / w)) := by
    have := measurable_eta2
    fun_prop
  have hm3 : Measurable
      (fun w : ℝ => ENNReal.ofReal C3 * ENNReal.ofReal (eta2 w / (w * Real.sqrt w))) := by
    have := measurable_eta2
    fun_prop
  have key : ENNReal.ofReal ‖MajSp.err (mconv eta2 phi) χ δ x‖ ≤
      ENNReal.ofReal (C0 + 1.37259 * C1 + 1.92182 * C2 + 2.74517 * C3) := by
    calc ENNReal.ofReal ‖MajSp.err (mconv eta2 phi) χ δ x‖
        ≤ ∫⁻ w in Icc (1 / 4 : ℝ) 1,
            ENNReal.ofReal (‖MajSp.err phi χ (δ * w) (w * x)‖ * eta2 w) := ko q χ δ x hx
      _ ≤ ∫⁻ w in Icc (1 / 4 : ℝ) 1, (ENNReal.ofReal C0 * ENNReal.ofReal (eta2 w) +
            ENNReal.ofReal C1 * ENNReal.ofReal (eta2 w / Real.sqrt w) +
            ENNReal.ofReal C2 * ENNReal.ofReal (eta2 w / w) +
            ENNReal.ofReal C3 * ENNReal.ofReal (eta2 w / (w * Real.sqrt w))) :=
          setLIntegral_mono' measurableSet_Icc hpt
      _ = ENNReal.ofReal C0 * (∫⁻ w in Icc (1 / 4 : ℝ) 1, ENNReal.ofReal (eta2 w)) +
            ENNReal.ofReal C1 * (∫⁻ w in Icc (1 / 4 : ℝ) 1,
              ENNReal.ofReal (eta2 w / Real.sqrt w)) +
            ENNReal.ofReal C2 * (∫⁻ w in Icc (1 / 4 : ℝ) 1, ENNReal.ofReal (eta2 w / w)) +
            ENNReal.ofReal C3 * (∫⁻ w in Icc (1 / 4 : ℝ) 1,
              ENNReal.ofReal (eta2 w / (w * Real.sqrt w))) := by
          rw [lintegral_add_right _ hm3, lintegral_add_right _ hm2, lintegral_add_right _ hm1,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal C0 * ENNReal.ofReal 1 + ENNReal.ofReal C1 * ENNReal.ofReal 1.37259 +
            ENNReal.ofReal C2 * ENNReal.ofReal 1.92182 +
            ENNReal.ofReal C3 * ENNReal.ofReal 2.74517 := by
          gcongr
      _ = ENNReal.ofReal (C0 + 1.37259 * C1 + 1.92182 * C2 + 2.74517 * C3) := by
          rw [← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2,
            ← ENNReal.ofReal_mul h3, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp key

/-- **`prop:magoma` (corrected) at the scaled point `(δw, wx)`, `w ∈ [1/4,1]`**, bounded in the
shape the `η₂`-transfer consumes: `C₀ + C₁w^{−1/2} + C₂w^{−1} + C₃w^{−3/2}` with
`C₀ = 2.5·10⁻¹³/q`, `C₁ = (379300/√q + 108)/√x`, `C₂ = (2.1376 + 10.99|δ|)/x`,
`C₃ = (log q + 8)(0.8806 + 5.1226|δ|)/(x√x)`. GRH to `10⁸/q` from `RT.PlattFull`. -/
theorem coprar_w (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer) (hG : GarmolaDecr)
    (fr : PhiReg) (fn : PhiNorms) (fd : PhiDecay) (ft : PhiTailInt) (pf : RT.PlattFull)
    {x : ℝ} (hx : 10 ^ 8 ≤ x) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : q ≤ 300000) {δ : ℝ} (hδ : |δ| ≤ 4 * 300000 / q) (w : ℝ)
    (hw : w ∈ Icc (1 / 4 : ℝ) 1) :
    ‖MajSp.err phi χ (δ * w) (w * x)‖ ≤ 2.5e-13 * (1 / q) +
      (379300 * (1 / Real.sqrt q) + 108) / Real.sqrt x * (1 / Real.sqrt w) +
      (2.1376 + 10.99 * |δ|) / x * (1 / w) +
      (Real.log q + 8) * (0.88060 + 5.1226 * |δ|) / (x * Real.sqrt x) *
        (1 / (w * Real.sqrt w)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqr : (q : ℝ) ≤ 300000 := by exact_mod_cast hq
  have hQ0 : (0 : ℝ) < q := by linarith
  have hw0 : 0 < w := by linarith [hw.1]
  have hw1 : w ≤ 1 := hw.2
  have hx0 : 0 < x := by linarith
  obtain ⟨hT, -, -, -, -, -, -⟩ := coprT_facts hq1 hqr
  have hδ1 : |δ| ≤ 1.2e6 / q := by
    rw [show (1.2e6 : ℝ) = 4 * 300000 by norm_num]
    exact hδ
  have hδw : |δ * w| ≤ |δ| := by
    rw [abs_mul, abs_of_pos hw0]
    exact mul_le_of_le_one_right (abs_nonneg δ) hw1
  have hδw1 : |δ * w| ≤ 1.2e6 / q := hδw.trans hδ1
  have hTd : 4 * Real.pi ^ 2 * |δ * w| ≤ 1e8 / q := by
    have hpi : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have h1 := mul_le_mul_of_nonneg_left hδw1 (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2)
    have h2 : 4 * Real.pi ^ 2 * (1.2e6 / q) ≤ 1e8 / q := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (by nlinarith) hQ0.le
    linarith
  have hTh : (1e8 : ℝ) / q ≤ RT.plattHeight q := by
    rw [show (1e8 : ℝ) = 10 ^ 8 by norm_num]
    exact RT.height_ge q
  have hgrh := grh_of_platt pf (by omega) hχ hTh
  have hwx : 1 ≤ w * x := by nlinarith [hw.1]
  have hb := phi_err hEF hZC hHs hG fr fn fd ft hχ (by omega) hwx (by linarith) hTd hgrh
  have h1 := tailF_le hq1 hqr hδw1
  have h2 := hbC_phi_le hq1 hqr
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw0
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hswx : Real.sqrt (w * x) = Real.sqrt w * Real.sqrt x := Real.sqrt_mul hw0.le x
  have hH : hbC q (1e8 / q) 0.81528 0.40453 1.07791 / Real.sqrt (w * x) ≤
      (379300 * (1 / Real.sqrt q) + 108) / Real.sqrt x * (1 / Real.sqrt w) := by
    rw [hswx]
    have e : (379300 * (1 / Real.sqrt q) + 108) / Real.sqrt x * (1 / Real.sqrt w) =
        (379300 * (1 / Real.sqrt q) + 108) / (Real.sqrt w * Real.sqrt x) := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  have hlq : 0 ≤ Real.log q + 8 := by linarith [Real.log_nonneg hq1]
  have hRn : Rphi q (δ * w) (w * x) ≤ 2.1376 + 10.99 * |δ| +
      (Real.log q + 8) * (0.88060 + 5.1226 * |δ|) / (Real.sqrt w * Real.sqrt x) := by
    unfold Rphi
    rw [hswx]
    have ha : 2 * Real.pi * |δ * w| * 0.81528 ≤ 5.1226 * |δ| := by
      have := mul_le_mul twopi_phi hδw (abs_nonneg _) (by norm_num)
      linarith
    have hb2 : (Real.log q + 8) * (0.88060 + 2 * Real.pi * |δ * w| * 0.81528) ≤
        (Real.log q + 8) * (0.88060 + 5.1226 * |δ|) :=
      mul_le_mul_of_nonneg_left (by linarith) hlq
    have hb3 := div_le_div_of_nonneg_right hb2 (by positivity : 0 ≤ Real.sqrt w * Real.sqrt x)
    have hb4 := mul_le_mul_of_nonneg_left hδw (by norm_num : (0 : ℝ) ≤ 10.99)
    linarith
  have hR : Rphi q (δ * w) (w * x) / (w * x) ≤ (2.1376 + 10.99 * |δ|) / x * (1 / w) +
      (Real.log q + 8) * (0.88060 + 5.1226 * |δ|) / (x * Real.sqrt x) *
        (1 / (w * Real.sqrt w)) := by
    have e : (2.1376 + 10.99 * |δ|) / x * (1 / w) +
        (Real.log q + 8) * (0.88060 + 5.1226 * |δ|) / (x * Real.sqrt x) *
          (1 / (w * Real.sqrt w)) = (2.1376 + 10.99 * |δ| +
        (Real.log q + 8) * (0.88060 + 5.1226 * |δ|) / (Real.sqrt w * Real.sqrt x)) / (w * x) := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right hRn (by positivity)
  linarith

/-- **`MR.CoprarR (η₂ ∗_M φ)` — HelfMaj Cor 1.3 at the RETYPED constants — FROM THE LINKS**:
`prop:magoma` (corrected) at every `(δw, wx)`, `w ∈ [1/4,1]`, at the height `10⁸/q`
(`RT.height_ge`), transferred by `Kolona` + `Eta2Moments`, closed by `coprar_close`. -/
theorem coprarR_of_links (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer)
    (hG : GarmolaDecr) (fr : PhiReg) (fn : PhiNorms) (fd : PhiDecay) (ft : PhiTailInt)
    (ko : Kolona) (mo : Eta2Moments) (pf : RT.PlattFull) : MR.CoprarR (mconv eta2 phi) := by
  intro x hx q hq1 hq χ hχ δ hδ
  haveI : NeZero q := ⟨by omega⟩
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqr : (q : ℝ) ≤ 300000 := by exact_mod_cast hq
  have hQ0 : (0 : ℝ) < q := by linarith
  have hx0 : 0 < x := by linarith
  have hsx := Real.sqrt_pos.mpr hx0
  have hlq : 0 ≤ Real.log q + 8 := by linarith [Real.log_nonneg hq1']
  have hb := kolona_transfer ko mo χ (δ := δ) hx0 (by positivity) (by positivity) (by positivity)
    (by positivity) (coprar_w hEF hZC hHs hG fr fn fd ft pf hx hχ hq hδ)
  have hsx4 : 10000 ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have hs548 : Real.sqrt q ≤ 548 := (Real.sqrt_le_left (by norm_num)).mpr (by nlinarith)
  have hu : 1 / 548 ≤ 1 / Real.sqrt q :=
    one_div_le_one_div_of_le (by linarith [one_le_sqrt' hq1']) hs548
  have hvu : 1 / (q : ℝ) ≤ 1 / Real.sqrt q :=
    one_div_le_one_div_of_le (by linarith [one_le_sqrt' hq1']) (sqrt_le_self' hq1')
  have hd : |δ| ≤ 1.2e6 * (1 / q) := by
    have e : 1.2e6 * (1 / (q : ℝ)) = 4 * 300000 / q := by ring
    rw [e]
    exact hδ
  have key := coprar_close hvu (by positivity) hu hsx4 hd
  have hxx : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0.le).symm
  have hC2 : (2.1376 + 10.99 * |δ|) / x = (2.1376 + 10.99 * |δ|) / (Real.sqrt x * Real.sqrt x) := by
    rw [← hxx]
  have hC3 : (Real.log q + 8) * (0.88060 + 5.1226 * |δ|) / (x * Real.sqrt x) ≤
      21 * (0.88060 + 5.1226 * |δ|) / (Real.sqrt x * Real.sqrt x * Real.sqrt x) := by
    rw [← hxx]
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
      (by positivity)
    linarith [logQ_le hq1' hqr]
  have e1 : 3e-13 * (1 / (q : ℝ)) + (650000 * (1 / Real.sqrt q) + 80) / Real.sqrt x =
      3e-13 / q + (650000 / Real.sqrt q + 80) / Real.sqrt x := by ring
  have hC3' := mul_le_mul_of_nonneg_left hC3 (by norm_num : (0 : ℝ) ≤ 2.74517)
  rw [← e1]
  linarith

end CoprarR

/-! ## (10) Prop 1.5 RETYPED, from the links (PROVED) -/

section MalheurR

open HW ArithmeticFunction
open scoped ArithmeticFunction

/-- `η₊,₂(0) = 0`. -/
theorem eta2x_zero (x : ℝ) : eta2x x 0 = 0 := by
  unfold eta2x
  rw [etaPlus_of_nonpos le_rfl]
  ring

/-- `fmal x` is continuous. -/
theorem continuous_fmal (x : ℝ) : Continuous (fmal x) := by
  unfold fmal
  fun_prop

/-- `fmal x ≥ 0` for `x ≥ 1`. -/
theorem fmal_nonneg {x : ℝ} (hx : 1 ≤ x) (T : ℝ) : 0 ≤ fmal x T := by
  unfold fmal
  have := Real.log_nonneg hx
  have : 0 ≤ Real.log x + 10 := by linarith
  positivity

/-- `fmal x` is non-increasing (everywhere) for `x ≥ 1`. -/
theorem fmal_antitoneOn {x : ℝ} (hx : 1 ≤ x) (s : Set ℝ) : AntitoneOn (fmal x) s := by
  intro a _ b _ hab
  unfold fmal
  have h0 : 0 ≤ 10 * (Real.log x + 10) := by linarith [Real.log_nonneg hx]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) h0

/-- **The high zeros of `ζ` for `η₊,₂`, corrected `eq:kolmo`** (`MalDecay`, `GarmolaDecr`,
`MalTailInt`; F5: the printed tail uses the one-sided density for a two-sided sum). -/
theorem mal_high (hZC : ZeroCount) (hG : GarmolaDecr) (md : MalDecay) (mt : MalTailInt)
    {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    zsum (1 : DirichletCharacter ℂ 1) {s | 450 < |s.im|}
        (fun ρ => ENNReal.ofReal ‖Gm (eta2x x) 0 ρ‖) ≤
      ENNReal.ofReal (1e-12 * Real.log x + 2 * fmal x 450 * gZ 1 450) := by
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have hL0 : 0 ≤ 1e-12 * Real.log x := mul_nonneg (by norm_num) (Real.log_nonneg hx1)
  have hg0 := gZ_nonneg (q := 1) (T := 450) (by norm_num)
  have hc1 : 0 ≤ 2 * fmal x 450 * gZ 1 450 :=
    mul_nonneg (mul_nonneg (by norm_num) (fmal_nonneg hx1 450)) hg0
  have hgar := hG hZC 1 1 DirichletCharacter.isPrimitive_one_level_one (fmal x) 450
    (by norm_num) (continuous_fmal x).measurable (fmal_antitoneOn hx1 _)
    (fun t _ => fmal_nonneg hx1 t)
  simp only [Nat.cast_one] at hgar
  calc zsum (1 : DirichletCharacter ℂ 1) {s | 450 < |s.im|}
        (fun ρ => ENNReal.ofReal ‖Gm (eta2x x) 0 ρ‖)
      ≤ zsum (1 : DirichletCharacter ℂ 1) {s | 450 < |s.im|}
          (fun ρ => ENNReal.ofReal (fmal x |ρ.im|)) := by
        refine zsum_mono _ fun ρ hρ => ENNReal.ofReal_le_ofReal ?_
        have hlt : 450 < |ρ.im| := hρ.2
        exact md x hx ρ hρ.1.2.1 hρ.1.2.2 hlt.le
    _ ≤ (∫⁻ t in Ioi (450 : ℝ), ENNReal.ofReal (fmal x t * gw 1 t)) +
          ENNReal.ofReal (2 * fmal x 450 * gZ 1 450) := hgar
    _ ≤ ENNReal.ofReal (1e-12 * Real.log x) + ENNReal.ofReal (2 * fmal x 450 * gZ 1 450) :=
        add_le_add (mt x hx) le_rfl
    _ = ENNReal.ofReal (1e-12 * Real.log x + 2 * fmal x 450 * gZ 1 450) :=
        (ENNReal.ofReal_add hL0 hc1).symm

/-- The residue numerator of `prop:konechno` at `MalNorms` (`q = 1`, `δ = 0`). -/
noncomputable def Rmal (x : ℝ) : ℝ :=
  18.15014 * Real.log x + 7.84532 + 8 * (27.05 * Real.log x + 9.872) / Real.sqrt x

/-- **`prop:konechno`, CORRECTED**: `|err_{η₊,₂,χ_T}(0,x)| ≤ tail + hbR(1,450; norms)/√x + Rmal/x`
at `x ≥ 10¹²`, with ζ-RH to `450` from `RT.PlattFull`. PROVED from the links. -/
theorem mal_err (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer) (hG : GarmolaDecr)
    (mr : MalReg) (mn : MalNorms) (md : MalDecay) (mt : MalTailInt) (pf : RT.PlattFull)
    {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    ‖MajSp.err (eta2x x) (1 : DirichletCharacter ℂ 1) 0 x‖ ≤
      (1e-12 * Real.log x + 2 * fmal x 450 * gZ 1 450) +
        hbR 1 450 (0.99811 * Real.log x + 0.32612) (0.32612 * Real.log x + 0.33816)
          (1.24703 * Real.log x + 0.40745) / Real.sqrt x + Rmal x / x := by
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have hL0 := Real.log_nonneg hx1
  obtain ⟨n2, nl, n1, nd, nc⟩ := mn x hx
  have hT : (450 : ℝ) ≤ RT.plattHeight 1 := by
    rw [PC.plattHeight_one]
    norm_num
  have hgrh := grh_of_platt pf (by norm_num) DirichletCharacter.isPrimitive_one_level_one hT
  have hH := (hHs hZC (eta2x x) (mr x hx).2 1 1 DirichletCharacter.isPrimitive_one_level_one 0 450
    (by norm_num) (by norm_num) hgrh).2 (isRealChar_one 1)
  simp only [Nat.cast_one] at hH
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hR : c0 (eta2x x) 0 + (Real.log ((1 : ℕ) : ℝ) + 8) *
      (MajSp.l2 (deriv (eta2x x)) + 2 * Real.pi * |(0 : ℝ)| * MajSp.l2 (eta2x x)) /
        Real.sqrt x ≤ Rmal x := by
    unfold Rmal
    rw [Nat.cast_one, Real.log_one, abs_zero, mul_zero, zero_mul, add_zero, zero_add]
    have h2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left nd (by norm_num : (0 : ℝ) ≤ 8)) hs0.le
    linarith
  have hHb : 0 ≤ hbR 1 450 (0.99811 * Real.log x + 0.32612) (0.32612 * Real.log x + 0.33816)
      (1.24703 * Real.log x + 0.40745) :=
    hbR_nonneg (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity)
  have hTb : 0 ≤ 1e-12 * Real.log x + 2 * fmal x 450 * gZ 1 450 := by
    have := fmal_nonneg hx1 450
    have := gZ_nonneg (q := 1) (T := 450) (by norm_num)
    positivity
  exact err_le_of_zero_sums hEF (mr x hx).1 (eta2x_zero x)
    DirichletCharacter.isPrimitive_one_level_one hx1 hgrh hHb hTb
    (le_trans hH (ENNReal.ofReal_le_ofReal (hbR_mono (by norm_num) (by norm_num) n2 nl n1)))
    (mal_high hZC hG md mt hx) hR

/-- The `q = 1`, `T = 450` constants of `prop:konechno`: `√450 ≤ 21.214`, `3 ≤ log 450 ≤ 7`,
`g(450) ≤ 21.2`, `e^{−35} ≤ 6.4·10⁻¹⁶`. -/
theorem malT_facts : Real.sqrt 450 ≤ 21.214 ∧ Real.log (1 * 450) ≤ 7 ∧ 3 ≤ Real.log (1 * 450) ∧
    gZ 1 450 ≤ 21.2 ∧ Real.exp (-0.7 * (450 - 400)) ≤ 6.4e-16 := by
  have hs : Real.sqrt 450 ≤ 21.214 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have hL7 : Real.log (1 * 450) ≤ 7 := by
    have h := log_le_nat 7 (y := 1 * 450) (by norm_num) (by norm_num)
    push_cast at h
    exact h
  have hL3 : 3 ≤ Real.log (1 * 450) := by
    have h := nat_le_log 3 (y := 1 * 450) (by norm_num)
    push_cast at h
    exact h
  have hE : Real.exp (-0.7 * (450 - 400)) ≤ 6.4e-16 := by
    have h := exp_neg_le 35 (d := 0) (B := 6.4e-16) (by norm_num) (by norm_num)
    have e : -(((35 : ℕ) : ℝ) + 0) = -0.7 * (450 - 400) := by norm_num
    rw [e] at h
    exact h
  refine ⟨hs, hL7, hL3, ?_, hE⟩
  have h := mul_le_mul_of_nonneg_left hL7 (by norm_num : (0 : ℝ) ≤ 0.5)
  unfold gZ
  linarith

/-- The closing arithmetic of `hbR(1, 450)` at the `MalNorms` bounds, over abstract atoms
(`S = √450`, `L = log 450`, `ℓ = log x ≥ 27`): `≤ 391ℓ` (the printed `310.84` after F1 and F13,
with `log 450 ≤ 7`; the referee's `≈ 346.9` uses `log 450 = 6.11`). -/
theorem hbR_mal_close {S L ℓ : ℝ} (hS : S ≤ 21.214) (hS0 : 0 ≤ S) (hL7 : L ≤ 7) (hL3 : 3 ≤ L)
    (hℓ : 27 ≤ ℓ) :
    0.5642 * (0.99811 * ℓ + 0.32612) * S * (L - 2.3378) +
        1.7725 * (0.32612 * ℓ + 0.33816) * S * (0.5 * L + 17.21) +
      (1.24703 * ℓ + 0.40745) * (1.319 * 0 + 0.5 * L + 52.2) ≤ 391 * ℓ := by
  have hA : S * (L - 2.3378) ≤ 21.214 * 4.6622 := mul_le_mul hS (by linarith) (by linarith)
    (by norm_num)
  have hB : S * (0.5 * L + 17.21) ≤ 21.214 * 20.71 := mul_le_mul hS (by linarith) (by linarith)
    (by norm_num)
  have hA0 : 0 ≤ S * (L - 2.3378) := mul_nonneg hS0 (by linarith)
  have hB0 : 0 ≤ S * (0.5 * L + 17.21) := mul_nonneg hS0 (by linarith)
  have hn2 : 0 ≤ 0.99811 * ℓ + 0.32612 := by linarith
  have hnl : 0 ≤ 0.32612 * ℓ + 0.33816 := by linarith
  have hn1 : 0 ≤ 1.24703 * ℓ + 0.40745 := by linarith
  have p1 := mul_le_mul_of_nonneg_left hA hn2
  have p2 := mul_le_mul_of_nonneg_left hB hnl
  have p3 : (1.24703 * ℓ + 0.40745) * (1.319 * 0 + 0.5 * L + 52.2) ≤
      (1.24703 * ℓ + 0.40745) * 55.7 := mul_le_mul_of_nonneg_left (by linarith) hn1
  have e1 : 0.5642 * (0.99811 * ℓ + 0.32612) * S * (L - 2.3378) =
      0.5642 * ((0.99811 * ℓ + 0.32612) * (S * (L - 2.3378))) := by ring
  have e2 : 1.7725 * (0.32612 * ℓ + 0.33816) * S * (0.5 * L + 17.21) =
      1.7725 * ((0.32612 * ℓ + 0.33816) * (S * (0.5 * L + 17.21))) := by ring
  rw [e1, e2]
  nlinarith

/-- The closing arithmetic of Prop 1.5, over abstract atoms (`X = x`, `sx = √x`, `ℓ = log x`). -/
theorem malheur_close {ℓ sx X E Tm H R D : ℝ} (hℓ : 27 ≤ ℓ) (hsx : 1000000 ≤ sx)
    (hX : X = sx * sx) (hE : E ≤ Tm + H / sx + R / X) (hTm : Tm ≤ 1.4e-12 * ℓ)
    (hH : H ≤ 391 * ℓ) (hR : R ≤ 18.5 * ℓ) (hD : D ≤ 3.9e-6 * ℓ + 1.3e-6) :
    X * E + X * D ≤ (5e-6 + 500 / sx) * X * ℓ := by
  have hsx0 : 0 < sx := by linarith
  have hX0 : 0 < X := by rw [hX]; positivity
  have e1 : X * (H / sx) = sx * H := by
    rw [hX]
    field_simp
  have e2 : X * (R / X) = R := by field_simp
  have e3 : (5e-6 + 500 / sx) * X * ℓ = 5e-6 * X * ℓ + 500 * sx * ℓ := by
    rw [hX]
    field_simp
  have p0 := mul_le_mul_of_nonneg_left hE hX0.le
  have p1 := mul_le_mul_of_nonneg_left hTm hX0.le
  have p2 := mul_le_mul_of_nonneg_left hH hsx0.le
  have p3 : R ≤ 18.5e-6 * sx * ℓ := by nlinarith
  have p4 := mul_le_mul_of_nonneg_left hD hX0.le
  have p5 : X * 1.3e-6 ≤ X * (1.3e-6 / 27 * ℓ) :=
    mul_le_mul_of_nonneg_left (by linarith) hX0.le
  have p6 : 0 ≤ sx * ℓ := by positivity
  rw [e3]
  have e4 : X * (Tm + H / sx + R / X) = X * Tm + X * (H / sx) + X * (R / X) := by ring
  nlinarith

/-- **`MR.MalheurAtR η₊ x` — HelfMaj Prop 1.5 at the RETYPED constants, one scale — FROM THE
LINKS.** `∑Λ(n) log n η₊²(n/x) − x∫η₊² log xt = x·err_{η₊,₂,χ_T}(0,x)` (the weight of
`prop:konechno`), then `MalMain` for the integral. -/
theorem malheurAt_of_links (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer)
    (hG : GarmolaDecr) (mr : MalReg) (mn : MalNorms) (md : MalDecay) (mt : MalTailInt)
    (mm : MalMain) (pf : RT.PlattFull) (x : ℝ) (hx : 10 ^ 12 ≤ x) : MR.MalheurAtR etaPlus x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have he0 : ∀ y : ℝ, y = 0 → e y = 1 := fun y hy => by
    rw [hy]
    simp [e]
  have htw : MajSp.twSum (eta2x x) (1 : DirichletCharacter ℂ 1) x (0 / x) =
      ((∑' n : ℕ, Λ n * Real.log n * etaPlus ((n : ℝ) / x) ^ 2 : ℝ) : ℂ) := by
    rw [zero_div, Complex.ofReal_tsum]
    unfold MajSp.twSum
    congr 1
    funext n
    have hxn : x * ((n : ℝ) / x) = n := by field_simp
    rw [MulChar.one_apply (isUnit_of_subsingleton _), he0 _ (mul_zero _)]
    unfold eta2x
    rw [hxn]
    push_cast
    ring
  have hft : MajSp.mainFT (eta2x x) 0 =
      ((∫ t in Ioi (0 : ℝ), etaPlus t ^ 2 * Real.log (x * t) : ℝ) : ℂ) := by
    unfold MajSp.mainFT
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [he0 _ (zero_mul t), mul_one]
    rfl
  have herr : MajSp.err (eta2x x) (1 : DirichletCharacter ℂ 1) 0 x =
      ((((∑' n : ℕ, Λ n * Real.log n * etaPlus ((n : ℝ) / x) ^ 2) / x -
        ∫ t in Ioi (0 : ℝ), etaPlus t ^ 2 * Real.log (x * t) : ℝ)) : ℂ) := by
    unfold MajSp.err
    rw [htw, hft, if_pos (rfl : (1 : ℕ) = 1), Complex.ofReal_sub, Complex.ofReal_div]
  have hb := mal_err hEF hZC hHs hG mr mn md mt pf hx
  rw [herr, Complex.norm_real, Real.norm_eq_abs] at hb
  have hm := mm x hx
  obtain ⟨hs450, hL7, hL3, hg, hE⟩ := malT_facts
  have hℓ : 27 ≤ Real.log x := by
    have h := nat_le_log 27 (y := x) (le_trans (by norm_num) hx)
    push_cast at h
    exact h
  have hsx : 1000000 ≤ Real.sqrt x := sqrt_x_ge' hx
  have hTm : 1e-12 * Real.log x + 2 * fmal x 450 * gZ 1 450 ≤ 1.4e-12 * Real.log x := by
    unfold fmal
    have h1 : Real.exp (-0.7 * (450 - 400)) * gZ 1 450 ≤ 6.4e-16 * 21.2 :=
      mul_le_mul hE hg (gZ_nonneg (by norm_num)) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * 10 * (Real.log x + 10))
    have e : 2 * (10 * (Real.log x + 10) * Real.exp (-0.7 * (450 - 400))) * gZ 1 450 =
        2 * 10 * (Real.log x + 10) * (Real.exp (-0.7 * (450 - 400)) * gZ 1 450) := by ring
    rw [e]
    nlinarith
  have hH : hbR 1 450 (0.99811 * Real.log x + 0.32612) (0.32612 * Real.log x + 0.33816)
      (1.24703 * Real.log x + 0.40745) ≤ 391 * Real.log x := by
    unfold hbR
    rw [Real.log_one]
    exact hbR_mal_close hs450 (Real.sqrt_nonneg _) hL7 hL3 hℓ
  have hR : Rmal x ≤ 18.5 * Real.log x := by
    unfold Rmal
    have h1 : 8 * (27.05 * Real.log x + 9.872) / Real.sqrt x ≤
        8 * (27.05 * Real.log x + 9.872) / 1000000 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hsx
    linarith
  have key := malheur_close hℓ hsx (Real.mul_self_sqrt hx0.le).symm hb hTm hH hR hm
  unfold MR.MalheurAtR
  have e1 : ∑' n : ℕ, Λ n * Real.log n * etaPlus ((n : ℝ) / x) ^ 2 -
      (0.640206 * x * Real.log x - 0.021095 * x) =
        x * ((∑' n : ℕ, Λ n * Real.log n * etaPlus ((n : ℝ) / x) ^ 2) / x -
          ∫ t in Ioi (0 : ℝ), etaPlus t ^ 2 * Real.log (x * t)) +
        x * ((∫ t in Ioi (0 : ℝ), etaPlus t ^ 2 * Real.log (x * t)) -
          (0.640206 * Real.log x - 0.021095)) := by
    field_simp
    ring
  rw [e1]
  calc |x * ((∑' n : ℕ, Λ n * Real.log n * etaPlus ((n : ℝ) / x) ^ 2) / x -
          ∫ t in Ioi (0 : ℝ), etaPlus t ^ 2 * Real.log (x * t)) +
        x * ((∫ t in Ioi (0 : ℝ), etaPlus t ^ 2 * Real.log (x * t)) -
          (0.640206 * Real.log x - 0.021095))|
      ≤ |x * ((∑' n : ℕ, Λ n * Real.log n * etaPlus ((n : ℝ) / x) ^ 2) / x -
          ∫ t in Ioi (0 : ℝ), etaPlus t ^ 2 * Real.log (x * t))| +
        |x * ((∫ t in Ioi (0 : ℝ), etaPlus t ^ 2 * Real.log (x * t)) -
          (0.640206 * Real.log x - 0.021095))| := abs_add_le _ _
    _ = x * |(∑' n : ℕ, Λ n * Real.log n * etaPlus ((n : ℝ) / x) ^ 2) / x -
          ∫ t in Ioi (0 : ℝ), etaPlus t ^ 2 * Real.log (x * t)| +
        x * |(∫ t in Ioi (0 : ℝ), etaPlus t ^ 2 * Real.log (x * t)) -
          (0.640206 * Real.log x - 0.021095)| := by
        rw [abs_mul, abs_mul, abs_of_pos hx0]
    _ ≤ (5e-6 + 500 / Real.sqrt x) * x * Real.log x := key

/-- **`MR.MalheurR η₊` FROM THE LINKS.** -/
theorem malheurR_of_links (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer)
    (hG : GarmolaDecr) (mr : MalReg) (mn : MalNorms) (md : MalDecay) (mt : MalTailInt)
    (mm : MalMain) (pf : RT.PlattFull) : MR.MalheurR etaPlus :=
  fun x hx => malheurAt_of_links hEF hZC hHs hG mr mn md mt mm pf x hx

end MalheurR

/-! ## (11) THE HEADLINE -/

/-- **`MR.HelfMajR η₊ (η₂ ∗_M φ)` FROM NAMED LINKS** — HelfMaj Thm 1.4, Cor 1.3 and Prop 1.5 at the
referee's RETYPED constants, conditional on Platt's statement `RT.PlattFull`, from nineteen named
links: four weight-generic (`ExplicitFormula` DEEP, `ZeroCount` CITED, `Hausierer` and
`GarmolaDecr` ELEM given the zero count) and fifteen about the fixed weights `η₊`, `φ`, `η₂`,
`η₊,₂`. The composition is application only. -/
theorem helfMajR_of_links (hEF : ExplicitFormula) (hZC : ZeroCount) (hHs : Hausierer)
    (hG : GarmolaDecr) (pr : PlusReg) (pn : PlusNorms) (pd : PlusDecay) (pt : PlusTailInt)
    (fr : PhiReg) (fn : PhiNorms) (fd : PhiDecay) (ft : PhiTailInt) (ko : Kolona)
    (mo : Eta2Moments) (mr : MalReg) (mn : MalNorms) (md : MalDecay) (mt : MalTailInt)
    (mm : MalMain) : MR.HelfMajR HW.etaPlus (HW.mconv HW.eta2 HW.phi) :=
  fun pf => ⟨malporR_of_links hEF hZC hHs hG pr pn pd pt pf,
    coprarR_of_links hEF hZC hHs hG fr fn fd ft ko mo pf,
    malheurR_of_links hEF hZC hHs hG mr mn md mt mm pf⟩

end Principia.Common.TernaryGoldbach.HM
