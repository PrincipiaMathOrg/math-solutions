/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Defs
import Principia.Erdos1054.Statements.Inputs
import Principia.Erdos1054.Statements.S6_Coverage
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) §7 "Witness measures and limiting laws", lines 2726–3177

**Statements only.** Every result of `Campaigns/Erdos-1054/collab-paper/EP1054.tex`, lines 2726–3177,
is a `def … : Prop` here; nothing is asserted. Each `-- deps:` comment records what the paper's proof
of that statement consumes (paper results of this or other `Statements` modules, by their Lean
names, and the inputs of `Principia.Erdos1054.Statements.Inputs`).

## Contents, in paper order

* lines 2729–2748 — `cRes` (`c_e(a)`), the Davenport law `davenportLaw` (`𝒟`) and the progression
  laws `progLaw e a` (`ν_{a,e}`), with `Fact_DaddDavenportLaw`, `Fact_DaddProgressionLaws` and
  `Eq_DaddProgressionDomination` (`eq:dadd:progression-domination`);
* lines 2752–2829 — `wE`, `Wfun`, `WstarFun` and `Prop_DaddWitnessMeans`
  (`prop:dadd:witness-means`), with the proof steps `Step_DaddWitnessIdentity`,
  `Step_DaddWitnessJointLimit`, `Step_DaddWitnessSupport`, `Step_DaddWitnessCount`,
  `Step_DaddWitnessCofactorTail`, `Step_DaddWitnessPieceBounds`;
* lines 2831–2833 — `Rem_DaddWitnessMeanGrowth`;
* lines 2839–2938 — `Thm_DaddUniversalSingularity` (`thm:dadd:universal-singularity`), built from
  `_Carrier`, `_FinitePart`, `_Tight`; the witness measure `witnessMeasure` (`𝒲`), the carrier
  `witnessCarrier` (`𝒵`), the empirical witness measure `empWitness` (`𝒲_X`) and the proof steps
  `Step_DaddSingularCarrier`, `Step_DaddWitnessMeasureMass`, `Step_DaddWitnessCarrier`,
  `Step_DaddEmpiricalWitnessVague`, `Step_DaddWitnessDomination`, `Step_DaddLimitDomination`,
  `Step_DaddCountDomination`;
* lines 2942–3026 — the unlabeled corollary `Cor_DaddHeavyTails`, built from
  `Eq_DaddSubsequentialTail` (`eq:dadd:subsequential-tail`) and five further assertions, with the
  proof steps `Step_DaddXoverR` and `Step_DaddLowerTailUniform`;
* lines 3032–3072 — `KX` (`K_X(t)`), `Eq_DaddCollisionCriterion` (`eq:dadd:collision-criterion`)
  and `Prop_DaddCollisionCriterion` (`prop:dadd:collision-criterion`), with
  `Step_DaddCollisionSupport`;
* lines 3076–3174 — the unlabeled proposition `Prop_DaddCollisionLowerBound`
  (`liminf K_X(t) > 1/9`), `Eq_DaddCollisionAffine` (`eq:dadd:collision-affine`), the law `nuQ`
  (`ν_Q`) and the proof steps `Step_DaddCollisionWitness`, `Step_DaddCollisionCores`,
  `Step_DaddCollisionH`, `Step_DaddCollisionFirstMoment`, `Step_DaddCollisionFirstMomentLaw`,
  `Step_DaddCollisionSourceIntensity`,
  `Step_DaddCollisionCylinder`, `Step_DaddCollisionPerCore`, `Step_DaddCollisionCombine`,
  `Step_DaddCollisionArithmetic`, `Step_DaddCollisionExplicit`.

## Encoding conventions for this section

* **The ratio space is `[0, ∞] = ℝ≥0∞`** (Borel), as the paper says ("weak subsequential limit `ν`
  of `ν_X` on `[0, ∞]`", line 2843). The `h`-space of the laws `𝒟`, `ν_{a,e}` is `ℝ`.
* **Weak convergence** of measures on `ℝ≥0∞` is written out with bounded continuous test functions
  `φ : ℝ≥0∞ →ᵇ ℝ` — exactly Mathlib's characterisation of the topology of `ProbabilityMeasure`
  (`MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`). Stating it on bare
  `Measure`s avoids having to *prove* `IsProbabilityMeasure (ν_X)` inside a statement.
* **The laws `𝒟` and `ν_{a,e}` are pinned by their distribution functions** (`IsDavenportLaw`,
  `IsProgLaw`); a finite measure on `ℝ` is determined by its values on the `Iic u`
  (`MeasureTheory.Measure.ext_of_Iic`), so `davenportLaw`/`progLaw` (a `Classical.choose`, junk `0`
  if none exists) are *the* paper objects as soon as `Fact_DaddDavenportLaw` /
  `Fact_DaddProgressionLaws` hold. Statements about them are only meaningful together with those two
  existence facts, which is why both are separate named results.
* **Shared objects are imported, not copied.** The empirical measures `ν_X`, `R(X)` and the ratio
  `f(N)/N` are `nuX`, `Rcnt`, `ratioE` of `Statements.S1_Main`, and `eq:tightness-criterion`
  (line 2678) is `Eq_TightnessCriterion` of `Statements.S6_Coverage`; this module imports
  `S6_Coverage` (which imports `S1_Main`) and uses them directly. Until 2026-09-25 it carried
  verbatim local copies `Limits.nuX`, `Limits.Rcnt`, `Limits.ratioE`, `Limits.tightnessCriterion`,
  because those modules were unbuilt. All section-local helper objects live in
  `Principia.Erdos1054.Limits` so that no helper name can collide with another `Statements`
  module; the paper results live in `Principia.Erdos1054`.
-/

namespace Principia.Erdos1054

open Filter MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction

namespace Limits

/-! ## §7 preamble objects (lines 2729–2748) -/

/-- **`c_e(a)`**, EP1054.tex lines 2729–2732: "For a residue class `a (mod Λ(e))`, put
`c_e(a)=\sum_{\substack{1\leq j<e\\j\mid a}}\frac1j`."
Encoding: `a` is a natural representative. Every `j < e` divides `Λ(e)`, so `j ∣ a` depends only on
the class of `a`; for `e ≤ 1` the sum is empty (`c_1 = 0`). -/
noncomputable def cRes (e a : ℕ) : ℝ := ∑ j ∈ (Finset.Ico 1 e).filter (· ∣ a), (1 : ℝ) / j

/-- **`𝒟`, "the statistical law of `h(n) = σ(n)/n`"** (EP1054.tex lines 2733–2734), as a predicate:
`μ` is a probability measure on `ℝ` whose distribution function is the natural density of
`{n : h(n) ≤ u}` at every `u`. This is exactly the hypothesis shape of `Cite_Erdos_singular`. -/
def IsDavenportLaw (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ u : ℝ, HasDens {n : ℕ | abundancy n ≤ u} (μ.real (Set.Iic u))

open Classical in
/-- The Davenport law `𝒟` (a chosen `μ` with `IsDavenportLaw μ`; junk `0` if none exists; unique
when it exists, by `Measure.ext_of_Iic`). -/
noncomputable def davenportLaw : Measure ℝ :=
  if h : ∃ μ : Measure ℝ, IsDavenportLaw μ then h.choose else 0

/-- **The progression law `ν_{a,e}`** (EP1054.tex lines 2734–2743), as a predicate: `μ` is a finite
measure on `ℝ` whose distribution function at every `u` is the density of
`{n ≡ a (mod Λ(e)) : h(n) ≤ u}`. The paper characterises `ν_{a,e}` through all continuity sets
`B`; the half-lines `Iic u` are among them (atomlessness), and they already determine a finite
measure. The continuity-set form itself is asserted in `Fact_DaddProgressionLaws`. -/
def IsProgLaw (e a : ℕ) (μ : Measure ℝ) : Prop :=
  IsFiniteMeasure μ ∧ ∀ u : ℝ,
    HasDens {n : ℕ | n % lcmUpTo e = a % lcmUpTo e ∧ abundancy n ≤ u} (μ.real (Set.Iic u))

open Classical in
/-- The progression law `ν_{a,e}` (a chosen `μ` with `IsProgLaw e a μ`; junk `0` if none exists). -/
noncomputable def progLaw (e a : ℕ) : Measure ℝ :=
  if h : ∃ μ : Measure ℝ, IsProgLaw e a μ then h.choose else 0

/-- The residues `a (mod Λ(e))` with `e ∣ a` (well defined since `e ∣ Λ(e)`), as `0 ≤ a < Λ(e)`. -/
noncomputable def witnessResidues (e : ℕ) : Finset ℕ :=
  (Finset.range (lcmUpTo e)).filter (e ∣ ·)

/-! ## Objects of `prop:dadd:witness-means` (lines 2752–2771) -/

/-- **`w_e(t)`**, EP1054.tex lines 2764–2767:
`w_e(t)=\sum_{\substack{a\bmod \Lambda(e)\\e\mid a}}\int_{h-c_e(a)\geq1/t}\frac{d\nu_{a,e}(h)}{h-c_e(a)}`.
Bochner integral over the set `{h : 1/t ≤ h − c_e(a)}`; for `t > 0` the integrand is `≤ t` there and
`ν_{a,e}` is finite, so the integral is a genuine one. -/
noncomputable def wE (e : ℕ) (t : ℝ) : ℝ :=
  ∑ a ∈ witnessResidues e,
    ∫ h in {h : ℝ | 1 / t ≤ h - cRes e a}, 1 / (h - cRes e a) ∂(progLaw e a)

/-- **`W(t) = ∑_{e ≥ 1} w_e(t)`** (EP1054.tex line 2762), as a `tsum` (the paper's convergence
claim is the separate `HasSum` conjunct of `Prop_DaddWitnessMeans`). -/
noncomputable def Wfun (t : ℝ) : ℝ := ∑' e : ℕ, wE (e + 1) t

/-- **`W*(t) = ∑_{e ≥ 2} w_e(t)`** (EP1054.tex line 2763). -/
noncomputable def WstarFun (t : ℝ) : ℝ := ∑' e : ℕ, wE (e + 2) t

open Classical in
/-- The cofactor-tail pair count of the proof of `prop:dadd:witness-means` (EP1054.tex lines
2818–2820): `#{(e, d) : e > E, F_e(d) = N, e d ≤ t N}` with `e, d ≥ 1` (both are `≤ e d ≤ t N`). -/
noncomputable def rtTail (t E : ℝ) (N : ℕ) : ℕ :=
  (((Finset.Icc 1 ⌊t * N⌋₊) ×ˢ (Finset.Icc 1 ⌊t * N⌋₊)).filter
    (fun p => E < (p.1 : ℝ) ∧ F p.1 p.2 = N ∧ ((p.1 * p.2 : ℕ) : ℝ) ≤ t * N)).card

/-! ## Objects of `thm:dadd:universal-singularity` (lines 2839–2938) -/

/-- `ψ_c(h) = 1/(h − c)` (EP1054.tex lines 2863–2866), sent into `[0, ∞]` (only used on `h > c`,
where it is a point of `(0, ∞)`). -/
noncomputable def psiE (c h : ℝ) : ℝ≥0∞ := ENNReal.ofReal (1 / (h - c))

/-- One summand `(ψ_{c_e(a)})_* (1_{h > c_e(a)} ψ_{c_e(a)}(h) dν_{a,e}(h))` of `𝒲`
(EP1054.tex lines 2869–2875). -/
noncomputable def witnessPiece (e a : ℕ) : Measure ℝ≥0∞ :=
  Measure.map (psiE (cRes e a))
    (((progLaw e a).restrict (Set.Ioi (cRes e a))).withDensity
      (fun h => ENNReal.ofReal (1 / (h - cRes e a))))

/-- **The positive witness measure `𝒲`**, EP1054.tex lines 2867–2875:
`\mathcal{W}=\sum_{e\geq1}\sum_{\substack{a\bmod \Lambda(e)\\e\mid a}}(\psi_{c_e(a)})_*
\bigl(\boldsymbol1_{\{h>c_e(a)\}}\psi_{c_e(a)}(h)\,d\nu_{a,e}(h)\bigr)`, a measure on `[0, ∞]`
(countable sum over `e = e' + 1 ≥ 1`). -/
noncomputable def witnessMeasure : Measure ℝ≥0∞ :=
  Measure.sum (fun e' : ℕ => ∑ a ∈ witnessResidues (e' + 1), witnessPiece (e' + 1) a)

/-- **The carrier `𝒵` built from a set `K`**, EP1054.tex lines 2882–2890:
`\mathcal{Z}=\bigcup_{e\geq1}\bigcup_{\substack{a\bmod \Lambda(e)\\e\mid a}}\bigcup_{j\geq1}
\psi_{c_e(a)}\bigl(K\cap[c_e(a)+1/j,j]\bigr)` (a subset of `ℝ`; `e = e' + 1`, `j = j' + 1`). -/
def witnessCarrier (K : Set ℝ) : Set ℝ :=
  ⋃ e' : ℕ, ⋃ a ∈ witnessResidues (e' + 1), ⋃ j' : ℕ,
    (fun h : ℝ => 1 / (h - cRes (e' + 1) a)) ''
      (K ∩ Set.Icc (cRes (e' + 1) a + 1 / ((j' : ℝ) + 1)) ((j' : ℝ) + 1))

/-- **The empirical witness measure `𝒲_X`**, EP1054.tex lines 2894–2900:
`\mathcal{W}_X=\frac1X\sum_{N\leq X}\sum_{\substack{e,d\geq1\\F_e(d)=N}}\delta_{ed/N}`.
Encoding: the inner sum is a countable `Measure.sum` over pairs `(e, d)` (it can be infinite — e.g.
`F_e(1) = 1` for every `e` — but it is finite on bounded ratio intervals, as the paper notes). -/
noncomputable def empWitness (X : ℝ) : Measure ℝ≥0∞ :=
  ENNReal.ofReal (1 / X) • ∑ N ∈ Finset.Icc 1 ⌊X⌋₊,
    Measure.sum (fun p : ℕ × ℕ =>
      if 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ F p.1 p.2 = N then
        Measure.dirac (ENNReal.ofReal (((p.1 * p.2 : ℕ) : ℝ) / (N : ℝ)))
      else 0)

/-- `φ ∈ C_c((0, ∞))`, transported to `[0, ∞]` by extension by zero: continuous, and vanishing
outside some `[a, b]` with `0 < a` and `b < ∞`. -/
def IsCcPos (φ : ℝ≥0∞ → ℝ) : Prop :=
  Continuous φ ∧ ∃ a b : ℝ, 0 < a ∧
    ∀ x : ℝ≥0∞, φ x ≠ 0 → ENNReal.ofReal a ≤ x ∧ x ≤ ENNReal.ofReal b

/-- **`ν_{X_j} ⇒ ν` weakly on `[0, ∞]` along the sequence `X_j → ∞`** (the paper's "weakly
convergent subsequence", lines 2910, 2969): `X_j → ∞` and `∫ φ dν_{X_j} → ∫ φ dν` for every
bounded continuous `φ` (Mathlib's weak topology, written out). -/
def WeakConvAlong (X : ℕ → ℝ) (ν : Measure ℝ≥0∞) : Prop :=
  Tendsto X atTop atTop ∧
    ∀ φ : ℝ≥0∞ →ᵇ ℝ, Tendsto (fun j : ℕ => ∫ x, φ x ∂(nuX (X j))) atTop (𝓝 (∫ x, φ x ∂ν))

/-- **`ν` is a weak subsequential limit of `ν_X` on `[0, ∞]`** ("compactified subsequential law",
lines 2842–2843, 2943). The conjunct `IsProbabilityMeasure ν` is automatic (test `φ = 1`), so it
does not restrict the class of limits; it is recorded for convenience. -/
def IsWeakSubseqLimit (ν : Measure ℝ≥0∞) : Prop :=
  IsProbabilityMeasure ν ∧ ∃ X : ℕ → ℝ, WeakConvAlong X ν

/-- The finite part of a law on `[0, ∞]`: its restriction to `[0, ∞)`, transported to `ℝ` by
`toReal` (injective off `⊤`). "Its restriction to `[0, ∞)`" (line 2849). -/
noncomputable def finitePart (ν : Measure ℝ≥0∞) : Measure ℝ :=
  (ν.restrict {⊤}ᶜ).map ENNReal.toReal

/-! ## Objects of the heavy-tail corollary (lines 2942–3026) -/

/-- `log⁺ x` on `[0, ∞]`, valued in `[0, ∞]`: `log⁺ ∞ = ∞`, and `log⁺ x = max(0, log x)` otherwise
(`ENNReal.ofReal` clamps negatives; `x = 0` gives `log 0 = 0`). -/
noncomputable def logPosE (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = ⊤ then ⊤ else ENNReal.ofReal (Real.log x.toReal)

/-- `log⁻ x` on `[0, ∞]`, valued in `[0, ∞]`: `log⁻ 0 = ∞`, and `log⁻ x = max(0, −log x)` otherwise
(`x = ∞` has `toReal = 0`, `log 0 = 0`, so `log⁻ ∞ = 0`). -/
noncomputable def logNegE (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = 0 then ⊤ else ENNReal.ofReal (-Real.log x.toReal)

/-! ## Objects of the collision results (lines 3032–3174) -/

/-- **`K_X(t)`**, EP1054.tex lines 3034–3037: `K_X(t)=\frac1X\sum_{N\leq X}(r_t^*(N)-1)_+`.
Truncated `ℕ` subtraction `r − 1` is *exactly* the positive part `(r − 1)_+`; `N` runs over
`1 ≤ N ≤ ⌊X⌋`. -/
noncomputable def KX (X t : ℝ) : ℝ :=
  (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ((rtStar t N - 1 : ℕ) : ℝ)

/-- The four cores `𝒞 = {2, 4, 8, 10}` (EP1054.tex lines 3085–3086). -/
def collisionCores : Finset ℕ := {2, 4, 8, 10}

/-- `H = 8π²/75 − 1` (EP1054.tex line 3104). -/
noncomputable def collisionH : ℝ := 8 * Real.pi ^ 2 / 75 - 1

/-- **`ν_Q`**, EP1054.tex lines 3098–3099: "Let `ν_Q` be the unnormalized Davenport law restricted
to `gcd(u,Q)=1`, of total mass `Δ(5)`" (`Q = 5# = 30`).
Encoding: the sum of the progression laws `ν_{a,5}` (modulus `Λ(5) = 60`) over the classes
`0 ≤ a < 60` with `gcd(a, 30) = 1`. Since `30 ∣ 60`, `gcd(u, 30) = 1` depends only on `u mod 60`,
and as `60` and `30` have the same prime factors these are exactly the `φ(60) = 16` reduced
classes, each of mass `1/60`; so `ν_Q(B)` is the density of `{u : gcd(u,30)=1, h(u) ∈ B}` on
continuity sets (by `Fact_DaddProgressionLaws`), of total mass `16/60 = 4/15 = Δ(5)` (asserted in
`Step_DaddCollisionFirstMomentLaw`). If the progression laws were the junk `0`, so would be `ν_Q`,
and the statements about it below would be *false* (they assert positive mass), not vacuous. -/
noncomputable def nuQ : Measure ℝ :=
  ∑ a ∈ (Finset.range (lcmUpTo 5)).filter (fun a : ℕ => Nat.Coprime a 30), progLaw 5 a

/-- **`r_D(N)`**, EP1054.tex lines 3138–3139: "the number of parameters `u` giving `N` in
(eq:dadd:collision-affine)", i.e. `#{u ≥ 1 : gcd(u, 30) = 1, s(D u) = N}`. Every such `u` has
`u ≤ D u / 2 ≤ s(D u) = N` (`D` even), so the range `1 ≤ u ≤ N` loses no solution. -/
def rCore (D N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun u => Nat.Coprime u 30 ∧ aliquot (D * u) = N)).card

end Limits

open Limits

/-! ## §7 preamble: `𝒟`, `ν_{a,e}`, `eq:dadd:progression-domination` (lines 2729–2748) -/

-- deps: Cite_PollackAP at `Q = 1`, `a = 0` (= Cite_Davenport, a derived input: the distribution
--       function `D(u)`: continuous, `→ 1`, densities exist);
--       the Stieltjes-measure construction (Mathlib `StieltjesFunction.measure`) of `D`, monotone
--       since it is a limit of monotone counting ratios, `D(−∞) = 0` since `h(n) ≥ 1`;
--       uniqueness from `MeasureTheory.Measure.ext_of_Iic`; atomless from continuity of `D`.
/-- **The Davenport law `𝒟`** — unlabeled, EP1054.tex lines 2733–2736: "Write `𝒟` for the
statistical law of `h(n)=σ(n)/n`. The Davenport theorem … gives an atomless measure …".
Encoding: the law exists (`IsDavenportLaw davenportLaw`), is unique among measures with that
distribution function (so the choice in `davenportLaw` is immaterial), and has no atoms. -/
def Fact_DaddDavenportLaw : Prop :=
  IsDavenportLaw davenportLaw ∧
    (∀ μ : Measure ℝ, IsDavenportLaw μ → μ = davenportLaw) ∧
    NoAtoms davenportLaw

-- deps: Cite_PollackAP (with `Q = Λ(e)`: continuous distribution functions `D_{a,Q}/Q`, limit
--       `1/Q`); Stieltjes construction and `Measure.ext_of_Iic` as in Fact_DaddDavenportLaw;
--       for the continuity-set clause, the portmanteau theorem (Mathlib
--       `MeasureTheory.tendsto_measure_of_null_frontier`) applied to the normalised empirical
--       measures `(Λ(e)/Y) ∑_{n≤Y, n≡a} δ_{h(n)}`, whose distribution functions converge everywhere.
/-- **The progression laws `ν_{a,e}`** — unlabeled, EP1054.tex lines 2734–2743:
"The Davenport theorem [Davenport] and its version for arithmetic progressions by Pollack
[PollackPalindromes, Lemma 2] gives an atomless measure `ν_{a,e}` characterized by
```
\nu_{a,e}(B) =\lim_{Y\to\infty}\frac1Y \#\{n\leq Y:n\equiv a\pmod{\Lambda(e)},\ h(n)\in B\}
```
for every continuity set `B`. In particular, each `ν_{a,e}` has total mass `1/Λ(e)`".
Encoding: for every `e ≥ 1` and every natural representative `a`: existence
(`IsProgLaw e a (progLaw e a)`), uniqueness ("characterized by"), no atoms, total mass
`Λ(e)⁻¹`, and the continuity-set limit for every Borel `B` with `ν_{a,e}(∂B) = 0` (the `lim` is
`HasDens`, i.e. along the integers; `n ≥ 1`). -/
def Fact_DaddProgressionLaws : Prop :=
  ∀ e : ℕ, 1 ≤ e → ∀ a : ℕ,
    IsProgLaw e a (progLaw e a) ∧
    (∀ μ : Measure ℝ, IsProgLaw e a μ → μ = progLaw e a) ∧
    NoAtoms (progLaw e a) ∧
    progLaw e a Set.univ = ((lcmUpTo e : ℕ) : ℝ≥0∞)⁻¹ ∧
    ∀ B : Set ℝ, MeasurableSet B → progLaw e a (frontier B) = 0 →
      HasDens {n : ℕ | n % lcmUpTo e = a % lcmUpTo e ∧ abundancy n ∈ B} ((progLaw e a).real B)

-- deps: Fact_DaddDavenportLaw, Fact_DaddProgressionLaws (distribution functions add up over the
--       `Λ(e)` classes, which partition `ℕ`; `Measure.ext_of_Iic`); `ν_{a,e} ≤ 𝒟` from the sum
--       (all summands are measures).
/-- **`eq:dadd:progression-domination`**, EP1054.tex lines 2744–2748:
```
\sum_{a\bmod \Lambda(e)}\nu_{a,e}=\mathcal{D}, \quad 0\leq\nu_{a,e}\leq\mathcal{D}.
```
Encoding: the classes are `a ∈ {0, …, Λ(e) − 1}`; `≤` is the order on measures (setwise);
`0 ≤ ν_{a,e}` is automatic for a `Measure`. Meaningful together with the two existence facts above
(both sides are junk `0` otherwise). `e ≥ 1`. -/
def Eq_DaddProgressionDomination : Prop :=
  ∀ e : ℕ, 1 ≤ e →
    (∑ a ∈ Finset.range (lcmUpTo e), progLaw e a) = davenportLaw ∧
    ∀ a : ℕ, progLaw e a ≤ davenportLaw

/-! ## `prop:dadd:witness-means` (lines 2752–2829) -/

-- deps: Eq_Reflection (S2: `F_e(d) = e d g_e(e d)`, with `d = n/e`); `g_e(n) = h(n) − ∑_{r∣n,r<e} 1/r`
--       and `r < e ⟹ r ∣ Λ(e)`, so `r ∣ n ⟺ r ∣ a`; Disp_FinalDivisor (S2: `F_e(d) ≥ d`, giving
--       `g_e(n) ≥ 1/e`).
/-- **Proof step of `prop:dadd:witness-means`** — EP1054.tex lines 2774–2781: "For
`n ≡ a (mod Λ(e))` with `e ∣ a`, complementary divisors give the exact identities
`F_e(n/e)=n g_e(n), g_e(n)=h(n)-c_e(a)`. In particular `g_e(n) ≥ 1/e`."
Encoding: `e, n ≥ 1`; `e ∣ a` and `n ≡ a (mod Λ(e))` give `e ∣ n` (as `e ∣ Λ(e)`), so `n / e` is
exact. -/
def Step_DaddWitnessIdentity : Prop :=
  ∀ e n a : ℕ, 1 ≤ e → 1 ≤ n → n % lcmUpTo e = a % lcmUpTo e → e ∣ a →
    (F e (n / e) : ℝ) = n * g e n ∧ g e n = abundancy n - cRes e a ∧ 1 / (e : ℝ) ≤ g e n

-- deps: Fact_DaddProgressionLaws (the rectangle counts: on `(α, β] × B` subtract the progression
--       counts at `βX` and `αX`; tightness of `ν_{a,e}` for rectangle approximation); Mathlib's
--       product-measure API (`MeasureTheory.Measure.prod`) and a π-system/rectangle argument.
/-- **Proof step of `prop:dadd:witness-means`** (the joint limit) — EP1054.tex lines 2787–2797:
"For completeness, the progression theorem also yields the joint limit
```
\frac1X\sum_{\substack{n\leq tX\\n\equiv a\pmod{\Lambda(e)}}} \delta_{(n/X,h(n))}
 \ \Longrightarrow\ \boldsymbol1_{[0,t]}(u)\,du\,d\nu_{a,e}(h).
```
Indeed, on a rectangle `(α,β]×B` the assertion follows by subtracting the progression counts at
`βX` and `αX`. The limiting law in `h` is tight, so rectangle approximation proves the joint weak
convergence."
Encoding: weak convergence of finite measures on `ℝ × ℝ` written out with bounded continuous test
functions `φ : ℝ × ℝ →ᵇ ℝ`, as real `X → ∞`; `n` runs over `1 ≤ n ≤ ⌊tX⌋`; the limit is the
product of Lebesgue measure on `[0, t]` with `ν_{a,e}`. Hypotheses: `e ≥ 1`, `t > 0`, and **every**
class `a` — the printed display has no `e ∣ a`, and the rectangle argument never uses it. The
collision proof needs exactly this generality: its "radial partition argument" (lines 3109–3111)
applies the joint limit at `e = 5` to the 16 classes `a` mod `Λ(5) = 60` coprime to `30`, none of
which is divisible by `5` (until 2026-09-25 the statement carried `e ∣ a`, which made it unusable
there). -/
def Step_DaddWitnessJointLimit : Prop :=
  ∀ e a : ℕ, 1 ≤ e → ∀ t : ℝ, 0 < t → ∀ φ : ℝ × ℝ →ᵇ ℝ,
    Tendsto (fun X : ℝ => (1 / X) *
        ∑ n ∈ (Finset.Icc 1 ⌊t * X⌋₊).filter (fun n : ℕ => n % lcmUpTo e = a % lcmUpTo e),
          φ ((n : ℝ) / X, abundancy n))
      atTop (𝓝 (∫ p, φ p ∂((volume.restrict (Set.Icc 0 t)).prod (progLaw e a))))

-- deps: Step_DaddWitnessIdentity (every source `n ≡ a` has `h(n) − c_e(a) = g_e(n) ≥ 1/e`);
--       Fact_DaddProgressionLaws (the continuity-set clause on the open set
--       `B = {h < c_e(a) + 1/e}`, whose frontier `{c_e(a) + 1/e}` is null by atomlessness: its
--       density is that of the empty set of sources, `0`).
/-- **Proof step of `prop:dadd:witness-means`** (the support condition) — EP1054.tex lines
2801–2803: "The support condition `h-c_e(a)\geq1/e` holds for `ν_{a,e}` because it holds for every
source in the progression. We may therefore pass to the limit in the witness condition."
Encoding: `ν_{a,e}` gives no mass to `{h : h − c_e(a) < 1/e}`, for `e ≥ 1`, `e ∣ a`. This is what
makes the region where `1/(h − c_e(a))` is unbounded or negative `ν_{a,e}`-null. -/
def Step_DaddWitnessSupport : Prop :=
  ∀ e a : ℕ, 1 ≤ e → e ∣ a → progLaw e a {h : ℝ | h - cRes e a < 1 / (e : ℝ)} = 0

-- deps: Step_DaddWitnessIdentity (the witness condition in terms of `h(n)`);
--       Step_DaddWitnessJointLimit (joint weak convergence to `1_{[0,t]}(u) du dν_{a,e}(h)`);
--       Step_DaddWitnessSupport (the passage to the limit in the witness condition);
--       Fact_DaddProgressionLaws (atomlessness: the region's boundary is product-null); portmanteau
--       (Mathlib `MeasureTheory.tendsto_measure_of_null_frontier`); Tonelli (Mathlib
--       `MeasureTheory.lintegral_prod`).
/-- **Proof step of `prop:dadd:witness-means`** (the Tonelli display) — EP1054.tex lines 2782–2814:
"A witness with target at most `X` and ratio at most `t` is characterized by `g_e(n) ≥ 1/t,
n g_e(n) ≤ X`. … Tonelli's theorem gives
```
\lim_{X\to\infty}\frac1X \#\{n\equiv a\pmod{\Lambda(e)}: g_e(n)\geq1/t,\ n g_e(n)\leq X\}
 =\int_0^t\nu_{a,e}\{h:h-c_e(a)\geq1/t,\ h-c_e(a)\leq1/u\}\,du
 =\int_{h-c_e(a)\geq1/t} \frac{d\nu_{a,e}(h)}{h-c_e(a)}.
```"
Encoding: `e ≥ 1`, `e ∣ a`, `t > 0`; the counted `n` satisfy `n ≤ t X` (from `g_e(n) ≥ 1/t` and
`n g_e(n) ≤ X`), so they are enumerated in `[1, ⌊t X⌋]`. The middle (Tonelli) expression is proof,
not restated. -/
def Step_DaddWitnessCount : Prop :=
  ∀ e a : ℕ, 1 ≤ e → e ∣ a → ∀ t : ℝ, 0 < t →
    Tendsto (fun X : ℝ => (1 / X) *
        ((((Finset.Icc 1 ⌊t * X⌋₊).filter (fun n : ℕ =>
          n % lcmUpTo e = a % lcmUpTo e ∧ 1 / t ≤ g e n ∧ (n : ℝ) * g e n ≤ X)).card : ℕ) : ℝ))
      atTop (𝓝 (∫ h in {h : ℝ | 1 / t ≤ h - cRes e a}, 1 / (h - cRes e a) ∂(progLaw e a)))

-- deps: Lem_Moment (S2, eq:moment at `Z = t X`, `k ≥ 2`); Eq_Reflection (a pair `(e, d)` with
--       `F_e(d) = N`, `e d ≤ t N` is a divisor `e` of `n = e d ≤ t X` with `g_e(n) = N/n ≥ 1/t`,
--       so it contributes `≤ t^k g_e(n)^k`).
/-- **Proof step of `prop:dadd:witness-means`** (the cofactor tail) — EP1054.tex lines 2815–2824:
"For the cofactor tail, Lemma lem:moment counts witnessing pairs themselves:
```
\frac1X\sum_{N\leq X} \#\{(e,d):e>E,\ F_e(d)=N,\ ed\leq tN\}
 \leq\frac{t^k}{X} \sum_{n\leq tX}\sum_{\substack{e\mid n\\e>E}}g_e(n)^k
 \leq C_kt^{k+1}E^{1-k}.
```"
Encoding: for each `k ≥ 2` one constant `C` (the `C_k` of `lem:moment`), uniform in `t > 0`,
`E ≥ 1`, `X ≥ 1` (for `t X < 1` the left side is `0`). -/
def Step_DaddWitnessCofactorTail : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ E : ℝ, 1 ≤ E → ∀ X : ℝ, 1 ≤ X →
    (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rtTail t E N : ℝ) ≤
      C * t ^ (k + 1) * E ^ (1 - (k : ℝ))

-- deps: Fact_DaddProgressionLaws (atomlessness: the moving boundary `{h − c_e(a) = 1/t}` is null,
--       so the integrand converges a.e. as `t' → t`; dominated by `2t` on `{h − c_e(a) ≥ 1/(2t)}`,
--       Mathlib `MeasureTheory.continuousOn_of_dominated`); the integrand is `≤ t` on its domain.
/-- **Proof step of `prop:dadd:witness-means`** (each `w_e`) — EP1054.tex lines 2826–2827: "Each
fixed `w_e(t)` is continuous by atomlessness, and tends to zero with `t` since its integrand is
bounded by `t` on its domain."
Encoding: for each `e ≥ 1`: `w_e` is continuous on `(0, ∞)`; `w_e(t) ≤ t · ∑_a ν_{a,e}(ℝ)` for
every `t > 0` (the integrand `1/(h − c_e(a)) ≤ t` on `{h − c_e(a) ≥ 1/t}`), and `w_e(t) → 0` as
`t → 0⁺`. -/
def Step_DaddWitnessPieceBounds : Prop :=
  ∀ e : ℕ, 1 ≤ e →
    ContinuousOn (wE e) (Set.Ioi 0) ∧
      (∀ t : ℝ, 0 < t → wE e t ≤ t * ∑ a ∈ witnessResidues e, (progLaw e a).real Set.univ) ∧
      Tendsto (wE e) (𝓝[>] 0) (𝓝 0)

-- deps: Step_DaddWitnessIdentity, Step_DaddWitnessCount (each fixed cofactor `e`, summed over the
--       finitely many classes `a`; this carries Step_DaddWitnessJointLimit and
--       Step_DaddWitnessSupport), Step_DaddWitnessCofactorTail (uniform tail in `e > E`, via
--       Lem_Moment); Step_DaddWitnessPieceBounds (each `w_e` continuous and `→ 0` as `t ↓ 0`);
--       Mathlib `TendstoUniformlyOn.continuousOn` for the continuity of the sums.
/-- **Proposition `prop:dadd:witness-means`**, EP1054.tex lines 2752–2771:
"For each `t>0` the limits
```
W(t)=\lim_{X\to\infty}\frac1X\sum_{N\leq X}r_t(N), \quad
W^*(t)=\lim_{X\to\infty}\frac1X\sum_{N\leq X}r_t^*(N)
```
exist, are finite, and are continuous. More explicitly,
```
W(t)=\sum_{e\geq1}w_e(t),\quad W^*(t)=\sum_{e\geq2}w_e(t), \quad
w_e(t) =\sum_{\substack{a\bmod \Lambda(e)\\e\mid a}} \int_{h-c_e(a)\geq1/t}
 \frac{d\nu_{a,e}(h)}{h-c_e(a)}.
```
Both series converge uniformly for `0<t≤T`, for every fixed `T>0`, and `W(t)→0` as `t↓0`."
Encoding: (i) for each `t > 0`, the averages (over real `X → ∞`, `N ∈ [1, ⌊X⌋]`) tend to `Wfun t`,
resp. `WstarFun t`, and the two series have those sums (`HasSum`, so the `tsum`s are genuine);
(ii) `W`, `W*` are continuous on `(0, ∞)`; (iii) the partial sums converge uniformly on `(0, T]`;
(iv) `W(t) → 0` as `t → 0⁺` (`𝓝[>] 0`). "Finite" is automatic for real limits. -/
def Prop_DaddWitnessMeans : Prop :=
  (∀ t : ℝ, 0 < t →
    Tendsto (fun X : ℝ => (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rt t N : ℝ)) atTop
        (𝓝 (Wfun t)) ∧
      Tendsto (fun X : ℝ => (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rtStar t N : ℝ)) atTop
        (𝓝 (WstarFun t)) ∧
      HasSum (fun e : ℕ => wE (e + 1) t) (Wfun t) ∧
      HasSum (fun e : ℕ => wE (e + 2) t) (WstarFun t)) ∧
  ContinuousOn Wfun (Set.Ioi 0) ∧ ContinuousOn WstarFun (Set.Ioi 0) ∧
  (∀ T : ℝ, 0 < T →
    TendstoUniformlyOn (fun (E : ℕ) (t : ℝ) => ∑ e ∈ Finset.range E, wE (e + 1) t) Wfun atTop
        (Set.Ioc 0 T) ∧
      TendstoUniformlyOn (fun (E : ℕ) (t : ℝ) => ∑ e ∈ Finset.range E, wE (e + 2) t) WstarFun
        atTop (Set.Ioc 0 T)) ∧
  Tendsto Wfun (𝓝[>] 0) (𝓝 0)

-- deps: Prop_ClassFirstMoment (S6, prop:class-first-moment with `Q = 1`: its lower class mean is
--       the average of `r_A(N)`, whose limit is `W(A)` by Prop_DaddWitnessMeans);
--       Fact_DaddProgressionLaws, Fact_DaddDavenportLaw (`w_1(t) = ∫_{h≥1/t} d𝒟(h)/h ≤ 1`, as
--       `Λ(1) = 1`, `c_1 = 0`, `h ≥ 1` on the support); `W* = W − w_1`.
/-- **Growth of the witness means** — unlabeled, EP1054.tex lines 2831–2833: "Proposition
prop:class-first-moment with `Q=1` also shows that `W(t)\gg t/(\log t)^2` as `t\to\infty`. Since
`w_1(t)\leq1`, the same lower bound holds for `W^*(t)`."
Encoding: `≫ … as t → ∞` is `∃ c > 0, ∃ t₀, ∀ t ≥ t₀, c t/(log t)² ≤ W(t)`; the `W*` bound gets its
own constant (the printed "same lower bound" is up to the implied constant); `w_1(t) ≤ 1` for every
`t > 0` is the middle conjunct. -/
def Rem_DaddWitnessMeanGrowth : Prop :=
  (∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → c * t / (Real.log t) ^ 2 ≤ Wfun t) ∧
  (∀ t : ℝ, 0 < t → wE 1 t ≤ 1) ∧
  (∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → c * t / (Real.log t) ^ 2 ≤ WstarFun t)

/-! ## `thm:dadd:universal-singularity` (lines 2839–2938) and its proof steps -/

-- deps: Cite_Erdos_singular (applied to `davenportLaw`, via Fact_DaddDavenportLaw);
--       inner regularity of finite measures on `ℝ` (Mathlib `MeasurableSet.exists_isCompact_diff_lt`
--       family) to replace the null set carrying `𝒟` by a σ-compact one; `h(n) ≥ 1`.
/-- **Proof step of `thm:dadd:universal-singularity`** — EP1054.tex lines 2858–2862: "Erdős's
singularity theorem asserts that the continuous Davenport law `𝒟` is purely Lebesgue singular …
By regularity there is a `σ`-compact Lebesgue-null set `K ⊂ [1,∞)` with `𝒟(K)=1`."
Encoding: `𝒟(K) = 1` is written as printed, `davenportLaw K = 1`. This is the junk-safe form: if
`davenportLaw` were the junk `0` it is *false*, whereas the complement form `𝒟(Kᶜ) = 0` would hold
trivially with `K = ∅`. -/
def Step_DaddSingularCarrier : Prop :=
  ∃ K : Set ℝ, K ⊆ Set.Ici 1 ∧ IsSigmaCompact K ∧ volume K = 0 ∧ davenportLaw K = 1

-- deps: Prop_DaddWitnessMeans (the value `W(t)` and its finiteness); the definition of
--       `witnessMeasure` (the pushforward of `1_{h>c} ψ_c dν_{a,e}` gives `(0, t]` the mass
--       `∫_{h−c≥1/t} dν_{a,e}/(h−c)`, summed = `W(t)`); Fact_DaddProgressionLaws (atomless:
--       `ψ_c` is injective on `h > c`).
/-- **Proof step of `thm:dadd:universal-singularity`** — EP1054.tex lines 2876–2881:
"Proposition prop:dadd:witness-means gives `\mathcal{W}((0,t])=W(t)<\infty\quad(t>0)`, so `𝒲` is
locally finite and atomless."
Encoding: `(0, t]` is `Set.Ioc 0 (ofReal t)` in `[0, ∞]`; atomless is `∀ x, 𝒲{x} = 0` (including
`x = 0` and `x = ∞`, which carry no mass by construction). -/
def Step_DaddWitnessMeasureMass : Prop :=
  (∀ t : ℝ, 0 < t → witnessMeasure (Set.Ioc 0 (ENNReal.ofReal t)) = ENNReal.ofReal (Wfun t)) ∧
  ∀ x : ℝ≥0∞, witnessMeasure {x} = 0

-- deps: Fact_DaddDavenportLaw (`𝒟` is a probability measure, so `𝒟(K) = 1` gives `𝒟(Kᶜ) = 0`;
--       `K` is measurable, being σ-compact: Mathlib `IsCompact.measurableSet`,
--       `MeasurableSet.iUnion`); Eq_DaddProgressionDomination (`ν_{a,e} ≤ 𝒟`, so every `ν_{a,e}`
--       is carried by `K`); σ-compactness of continuous images and countable unions (Mathlib
--       `IsSigmaCompact.image`, `isSigmaCompact_iUnion`); `ψ_c` is `j²`-Lipschitz on
--       `[c + 1/j, ∞)`, and Lipschitz images of null sets are null (Mathlib
--       `LipschitzOnWith.hausdorffMeasure_image_le` with `MeasureTheory.hausdorffMeasure_real`:
--       `μH[1] = volume` on `ℝ`).
/-- **Proof step of `thm:dadd:universal-singularity`** — EP1054.tex lines 2880–2892: "By
(eq:dadd:progression-domination), every `ν_{a,e}` is carried by `K`. Therefore `𝒲` is carried by
`𝒵 = …`. Each map in the last display is Lipschitz on its indicated set. Thus `𝒵` is `σ`-compact
and Lebesgue null."
Encoding: for every `K` as in `Step_DaddSingularCarrier` (the same four conditions, including
`𝒟(K) = 1` as printed, so the two steps compose by application), `𝒵 = witnessCarrier K` lies in
`(0, ∞)`, is σ-compact and Lebesgue-null, and `𝒲` gives no mass to the points of `[0, ∞]` outside
`𝒵` (`0`, `∞`, and finite `x` with `x ∉ 𝒵`). -/
def Step_DaddWitnessCarrier : Prop :=
  ∀ K : Set ℝ, K ⊆ Set.Ici 1 → IsSigmaCompact K → volume K = 0 → davenportLaw K = 1 →
    witnessCarrier K ⊆ Set.Ioi 0 ∧ IsSigmaCompact (witnessCarrier K) ∧
      volume (witnessCarrier K) = 0 ∧
      witnessMeasure {x : ℝ≥0∞ | x = 0 ∨ x = ⊤ ∨ x.toReal ∉ witnessCarrier K} = 0

-- deps: Prop_DaddWitnessMeans (convergence of `𝒲_X((0, t])` to `W(t)` for every `t > 0`, i.e. of
--       the distribution functions on `(0, ∞)`), continuity of `W` (so every `t` is a continuity
--       point), Step_DaddWitnessMeasureMass; approximation of `φ ∈ C_c((0,∞))` by step functions.
/-- **Proof step of `thm:dadd:universal-singularity`** — EP1054.tex lines 2901–2903: "On every
bounded ratio interval it is finite. Proposition prop:dadd:witness-means and continuity of `W` show
that `\mathcal{W}_X\to\mathcal{W}` vaguely on `(0,\infty)`."
Encoding: for every `φ ∈ C_c((0, ∞))` (`IsCcPos`), `∫ φ d𝒲_X → ∫ φ d𝒲` as real `X → ∞`. -/
def Step_DaddEmpiricalWitnessVague : Prop :=
  ∀ φ : ℝ≥0∞ → ℝ, IsCcPos φ →
    Tendsto (fun X : ℝ => ∫ x, φ x ∂(empWitness X)) atTop (𝓝 (∫ x, φ x ∂witnessMeasure))

-- deps: f_mem_Fform (Basic) (for `N ∈ 𝓡`, `f(N) = e d` for a pair with `F_e(d) = N`, so
--       `δ_{f(N)/N}` is one of the Dirac masses of `𝒲_X` at `N`), `φ ≥ 0`.
/-- **Proof step of `thm:dadd:universal-singularity`** — EP1054.tex lines 2904–2909: "For every
nonnegative `φ ∈ C_c((0,∞))`, choosing a minimizing witness separately for each represented
target gives `\int\varphi\,d\nu_X \leq\frac X{R(X)}\int\varphi\,d\mathcal{W}_X`."
Encoding: lower Lebesgue integrals of `ofReal ∘ φ` (so no integrability side condition), `X ≥ 1`
(where `R(X) ≥ 1`). -/
def Step_DaddWitnessDomination : Prop :=
  ∀ φ : ℝ≥0∞ → ℝ, IsCcPos φ → (∀ x, 0 ≤ φ x) → ∀ X : ℝ, 1 ≤ X →
    ∫⁻ x, ENNReal.ofReal (φ x) ∂(nuX X) ≤
      ENNReal.ofReal (X / (Rcnt X : ℝ)) * ∫⁻ x, ENNReal.ofReal (φ x) ∂(empWitness X)

-- deps: Step_DaddWitnessDomination, Step_DaddEmpiricalWitnessVague, `X/R(X) → 1`
--       (Eq_ExactRepresentability, S1); Riesz/regularity: a Radon measure on `(0, ∞)` dominated on
--       `C_c⁺` is dominated setwise.
/-- **Proof step of `thm:dadd:universal-singularity`** — EP1054.tex lines 2910–2916: "Along any
weakly convergent subsequence `\nu_{X_j}\Rightarrow\nu`, pass to the limit to obtain
`\int\varphi\,d\nu\leq\int\varphi\,d\mathcal{W}`. Hence `\nu|_{(0,\infty)}\leq\mathcal{W}`."
Encoding: `(0, ∞)` is `Set.Ioo 0 ⊤` in `[0, ∞]`; `≤` is the setwise order on measures. -/
def Step_DaddLimitDomination : Prop :=
  ∀ ν : Measure ℝ≥0∞, IsWeakSubseqLimit ν → ν.restrict (Set.Ioo 0 ⊤) ≤ witnessMeasure

-- deps: f_mem_Fform (Basic) (for `N ∈ 𝓡` with `f(N)/N < t`, `f(N) = e d` with `F_e(d) = N`, so
--       `δ_{f(N)/N}` is one of the Dirac masses of `𝒲_X` at `N` lying in `[0, t)`); for the second
--       conjunct, `e, d ≤ e d < t N` (so the pair is enumerated by `rt t N`).
/-- **Proof step of `thm:dadd:universal-singularity`** (witness domination near `0`) — EP1054.tex
lines 2918–2924: "Finally, the same witness domination and portmanteau give, for every `t>0`,
`\nu(\{0\}) \leq\nu([0,t)) \leq\liminf_{j\to\infty}\nu_{X_j}([0,t)) \leq W(t)`."
The printed domination (`Step_DaddWitnessDomination`) is for `φ ∈ C_c((0,∞))`, which vanishes near
`0` and so cannot see `[0, t)`; this is the same minimizing-witness argument applied to the
indicator of `[0, t)`, which is what the last inequality of the display uses.
Encoding: for `t > 0`, `X ≥ 1`: `ν_X([0,t)) ≤ (X/R(X)) 𝒲_X([0,t))` and
`𝒲_X([0,t)) ≤ (1/X) ∑_{N≤X} r_t(N)` (whose limit is `W(t)` by `Prop_DaddWitnessMeans`); `[0, t)`
is `Set.Iio (ofReal t)` in `[0, ∞]`; values in `ℝ≥0∞` (no `toReal` junk). -/
def Step_DaddCountDomination : Prop :=
  ∀ t : ℝ, 0 < t → ∀ X : ℝ, 1 ≤ X →
    nuX X (Set.Iio (ENNReal.ofReal t)) ≤
        ENNReal.ofReal (X / (Rcnt X : ℝ)) * empWitness X (Set.Iio (ENNReal.ofReal t)) ∧
      empWitness X (Set.Iio (ENNReal.ofReal t)) ≤
        ENNReal.ofReal ((1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rt t N : ℝ))

-- deps: Step_DaddSingularCarrier, Step_DaddWitnessCarrier (the set `𝒵 = witnessCarrier K`),
--       Step_DaddLimitDomination (no mass off `𝒵` in `(0, ∞)`; no finite positive atoms, via
--       Step_DaddWitnessMeasureMass); for `ν{0} = 0`: portmanteau (open-set direction, Mathlib
--       `MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto`) on the open set
--       `[0, t)` of `[0, ∞]`, Step_DaddCountDomination (`ν_X([0,t)) ≤ (X/R(X)) (1/X)∑ r_t(N)`),
--       Eq_ExactRepresentability (S1: `X/R(X) → 1`) and Prop_DaddWitnessMeans (the average of
--       `r_t` tends to `W(t)`, and `W(t) → 0` as `t ↓ 0`); for `0 ∈ supp ν`: Thm_SmallValues (S1)
--       and portmanteau (closed-set direction,
--       `MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`) on `[0, δ]`;
--       EmpiricalMeasures_isProbability (S1: both portmanteau directions are stated for
--       `ProbabilityMeasure`, and `nuX` is a bare `Measure`).
/-- **Theorem `thm:dadd:universal-singularity`, main display** — EP1054.tex lines 2839–2848:
"There is a fixed `σ`-compact, Lebesgue-null set `\mathcal{Z}\subset(0,\infty)` such that every
weak subsequential limit `ν` of `ν_X` on `[0,∞]` satisfies
```
0\in\operatorname{supp}(\nu),\quad \nu(\{0\})=0,\\
\nu\bigl((0,\infty)\setminus\mathcal{Z}\bigr)=0,\quad \nu(\{x\})=0\quad(0<x<\infty).
```"
Encoding: `𝒵 ⊆ ℝ`, `𝒵 ⊆ (0, ∞)`, `IsSigmaCompact`, `volume 𝒵 = 0`, quantified **before** `ν`
("a fixed set" for all limits). `supp` is Mathlib's `Measure.support`; `(0, ∞) ∖ 𝒵` is the set of
`x ∈ [0, ∞]` with `x ≠ 0`, `x ≠ ∞` and `x.toReal ∉ 𝒵`. -/
def Thm_DaddUniversalSingularity_Carrier : Prop :=
  ∃ Z : Set ℝ, Z ⊆ Set.Ioi 0 ∧ IsSigmaCompact Z ∧ volume Z = 0 ∧
    ∀ ν : Measure ℝ≥0∞, IsWeakSubseqLimit ν →
      (0 : ℝ≥0∞) ∈ ν.support ∧ ν {0} = 0 ∧
      ν {x : ℝ≥0∞ | x ≠ 0 ∧ x ≠ ⊤ ∧ x.toReal ∉ Z} = 0 ∧
      ∀ x : ℝ≥0∞, x ≠ 0 → x ≠ ⊤ → ν {x} = 0

-- deps: Thm_DaddUniversalSingularity_Carrier (carrier `𝒵` null ⟹ `⟂ₘ volume`; atoms excluded at
--       `0` and at every finite `x > 0`; `0 ∈ supp ν` ⟹ `ν([0, δ]) > 0` ⟹ the finite part is `≠ 0`).
/-- **Theorem `thm:dadd:universal-singularity`, first consequence** — EP1054.tex lines 2849–2850:
"Hence its restriction to `[0,∞)` is a nonzero singular continuous measure."
Encoding: `finitePart ν` (the restriction to `[0, ∞)`, carried to `ℝ` by `toReal`) is nonzero,
has no atoms, and is mutually singular with Lebesgue measure (`⟂ₘ volume`). -/
def Thm_DaddUniversalSingularity_FinitePart : Prop :=
  ∀ ν : Measure ℝ≥0∞, IsWeakSubseqLimit ν →
    finitePart ν ≠ 0 ∧ NoAtoms (finitePart ν) ∧ finitePart ν ⟂ₘ volume

-- deps: Prop_TightnessEquivalence (S6: Eq_TightnessCriterion ⟹ `Coverage.NuTight`, i.e.
--       `lim_T sup_{X≥1} ν_X((T,∞]) = 0`); portmanteau, OPEN-set direction (Mathlib
--       `MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto`) on the open sets
--       `(T, ∞]`: `ν{∞} ≤ ν((T,∞]) ≤ liminf_j ν_{X_j}((T,∞]) ≤ sup_X ν_X((T,∞]) → 0`;
--       Thm_DaddUniversalSingularity_FinitePart; Radon–Nikodym (a measure with a Lebesgue density
--       is `≪ volume`, Mathlib `MeasureTheory.withDensity_absolutelyContinuous`, incompatible with
--       `⟂ₘ volume` for a nonzero measure); EmpiricalMeasures_isProbability (S1: portmanteau is
--       stated for `ProbabilityMeasure`, and `nuX` is a bare `Measure`).
/-- **Theorem `thm:dadd:universal-singularity`, conditional clause** — EP1054.tex lines 2850–2854:
"If (eq:tightness-criterion) holds, every subsequential limit is a singular continuous probability
law on `[0,∞)`; in particular, none admits a Lebesgue density. Neither uniqueness of the limit nor
tightness is asserted unconditionally."
Encoding: under `Eq_TightnessCriterion` (`S6_Coverage`), every compactified limit has no mass at
`∞`, its finite part is a probability measure, atomless, singular, and is `volume.withDensity ρ`
for **no** `ρ : ℝ → ℝ≥0∞` (measurable or not). The last sentence of the theorem asserts
nothing. -/
def Thm_DaddUniversalSingularity_Tight : Prop :=
  Eq_TightnessCriterion → ∀ ν : Measure ℝ≥0∞, IsWeakSubseqLimit ν →
    ν {⊤} = 0 ∧ IsProbabilityMeasure (finitePart ν) ∧ NoAtoms (finitePart ν) ∧
      finitePart ν ⟂ₘ volume ∧ ¬ ∃ ρ : ℝ → ℝ≥0∞, finitePart ν = volume.withDensity ρ

-- deps: Thm_DaddUniversalSingularity_Carrier, Thm_DaddUniversalSingularity_FinitePart,
--       Thm_DaddUniversalSingularity_Tight.
/-- **Theorem `thm:dadd:universal-singularity`** (EP1054.tex lines 2839–2855), the whole theorem
environment:
"There is a fixed `σ`-compact, Lebesgue-null set `𝒵 ⊂ (0,∞)` such that every weak subsequential
limit `ν` of `ν_X` on `[0,∞]` satisfies `0 ∈ supp(ν)`, `ν({0}) = 0`, `ν((0,∞) ∖ 𝒵) = 0`,
`ν({x}) = 0 (0<x<∞)`. Hence its restriction to `[0,∞)` is a nonzero singular continuous measure.
If (eq:tightness-criterion) holds, every subsequential limit is a singular continuous probability
law on `[0,∞)`; in particular, none admits a Lebesgue density." -/
def Thm_DaddUniversalSingularity : Prop :=
  Thm_DaddUniversalSingularity_Carrier ∧ Thm_DaddUniversalSingularity_FinitePart ∧
    Thm_DaddUniversalSingularity_Tight

/-! ## The heavy-tail corollary (lines 2940–3026) -/

-- deps: Eq_ExactRepresentability (S1: `R(X) = ⌊X⌋ − 2` for `X ≥ 5`); the finitely many `X < 5`
--       by hand (`R(X) ≥ 1`, and `R(X) ≥ 2`, `3` on `[3, 4)`, `[4, 5)`).
/-- **Proof step of the heavy-tail corollary** — EP1054.tex line 3001: "the bound `X/R(X)\leq3`",
for `X ≥ 1` (where `ν_X` is defined). -/
def Step_DaddXoverR : Prop :=
  ∀ X : ℝ, 1 ≤ X → X ≤ 3 * (Rcnt X : ℝ)

-- deps: Thm_SmallUpper_doubleExp (S1, at `δ = e^{−u}`, so `(1/δ)^c = e^{cu}`); Step_DaddXoverR.
/-- **Proof step of the heavy-tail corollary** — EP1054.tex lines 3001–3006: "Theorem
thm:small-upper and the bound `X/R(X)\leq3` give, for some `c>0` and all sufficiently large `u`,
`\sup_X\nu_X([0,e^{-u}]) \ll\exp\bigl(-\exp(e^{cu})\bigr)`."
Encoding: `c > 0`, the implied constant `C` and the threshold `u₀` are absolute, quantified before
`u` and `X`; `sup_X` over `X ≥ 1`; `[0, e^{−u}]` is `Set.Iic (ofReal (exp (−u)))` in `[0, ∞]`. -/
def Step_DaddLowerTailUniform : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∃ u₀ : ℝ, ∀ u : ℝ, u₀ ≤ u → ∀ X : ℝ, 1 ≤ X →
    (nuX X).real (Set.Iic (ENNReal.ofReal (Real.exp (-u)))) ≤
      C * Real.exp (-Real.exp (Real.exp (c * u)))

-- deps: Eq_AlmostLogTail (S1, thm:almost-log-tail: the lower density of `{f(N) > TN}` bounds
--       `liminf_X ν_X((T, ∞])` from below, using `R(X) ≤ X`); portmanteau, closed-set direction
--       (Mathlib `MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`) on
--       `[T, ∞]`; Thm_DaddUniversalSingularity_Carrier (no atom at `T`, so `ν([T,∞]) = ν((T,∞])`);
--       EmpiricalMeasures_isProbability (S1: portmanteau is stated for `ProbabilityMeasure`).
/-- **`eq:dadd:subsequential-tail`** (inside the unlabeled corollary, EP1054.tex lines 2942–2950):
"Every compactified subsequential law `ν` satisfies, as `T\to\infty`,
```
\nu((T,\infty]) \geq\left(\frac{e^{-\gamma}}2-o(1)\right)
 \frac{\log\log\log T}{(\log T)(\log\log T)}.
```"
Encoding: `∀ ν, ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀` (the `o(1)` is allowed to depend on `ν`, as printed; the
proof in fact gives a `T₀` uniform in `ν` — not asserted); `(T, ∞]` is `Set.Ioi (ofReal T)` in
`[0, ∞]`; `ν.real` is finite-valued since `ν` is a probability measure; the scale is `Lscale T`. -/
def Eq_DaddSubsequentialTail : Prop :=
  ∀ ν : Measure ℝ≥0∞, IsWeakSubseqLimit ν → ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (Real.exp (-eulerGamma) / 2 - ε) * Lscale T ≤ ν.real (Set.Ioi (ENNReal.ofReal T))

-- deps: Eq_AlmostLogTail (S1; `∫ x^s dν_X ≥ T^s ν_X((T, ∞])`, then `liminf_X`, then `T → ∞`);
--       Eq_DaddSubsequentialTail (the same for `ν`).
/-- **Heavy-tail corollary, positive moments** — EP1054.tex lines 2951–2956: "Moreover, for every
`s>0`, `\lim_{X\to\infty}\int x^s\,d\nu_X(x)=\infty, \quad \int_{[0,\infty]}x^s\,d\nu(x)=\infty`."
Encoding: `x^s` is `ENNReal.rpow` (`∞^s = ∞`); lower Lebesgue integrals on `[0, ∞]`; the limit is
along real `X → ∞` in `ℝ≥0∞` (`𝓝 ⊤`); `ν` ranges over compactified subsequential laws. -/
def Cor_DaddHeavyTails_PosMoments : Prop :=
  ∀ s : ℝ, 0 < s →
    Tendsto (fun X : ℝ => ∫⁻ x, x ^ s ∂(nuX X)) atTop (𝓝 ⊤) ∧
      ∀ ν : Measure ℝ≥0∞, IsWeakSubseqLimit ν → ∫⁻ x, x ^ s ∂ν = ⊤

-- deps: layer cake (Mathlib `MeasureTheory.lintegral_eq_lintegral_meas_lt`) and Fatou
--       (`MeasureTheory.lintegral_liminf_le`) with Eq_AlmostLogTail (S1) for `log⁺`, giving
--       `≥ (e^{−γ}/4 − o(1))(log log log B)²`; Eq_DaddSubsequentialTail for `ν`;
--       Step_DaddLowerTailUniform (uniform bound on `∫ log⁻ dν_X`), weak convergence against
--       `min(M, log⁻ x)` and `M → ∞` (monotone convergence) for `∫ log⁻ dν < ∞`.
/-- **Heavy-tail corollary, logarithmic means** — EP1054.tex lines 2957–2962: "The logarithmic
means also satisfy `\lim_{X\to\infty}\int\log x\,d\nu_X(x)=\infty, \quad
\int_{[0,\infty]}\log x\,d\nu(x)=\infty`."
Encoding: for `ν_X` (finitely many atoms, all in `(0, ∞)`) the log-mean is a genuine Bochner
integral of `log (x.toReal)` and tends to `+∞` (`atTop`). For `ν` on `[0, ∞]` the extended
integral `∫ log dν = +∞` is stated as its meaning: `∫ log⁺ dν = ∞` and `∫ log⁻ dν < ∞`
(`logPosE`, `logNegE`, with `log⁺ ∞ = ∞`, `log⁻ 0 = ∞`). -/
def Cor_DaddHeavyTails_LogMeans : Prop :=
  Tendsto (fun X : ℝ => ∫ x, Real.log x.toReal ∂(nuX X)) atTop atTop ∧
    ∀ ν : Measure ℝ≥0∞, IsWeakSubseqLimit ν →
      ∫⁻ x, logPosE x ∂ν = ⊤ ∧ ∫⁻ x, logNegE x ∂ν < ⊤

-- deps: Step_DaddLowerTailUniform and layer cake (`sup_X ∫_{x<1} x^{−s} dν_X ≤ 1 + s ∫_0^∞ e^{su}
--       sup_X ν_X([0, e^{−u}]) du < ∞`); weak convergence against the continuous bounded
--       truncations `min(M, x^{−s})` on `[0, ∞]`, then `M → ∞`.
/-- **Heavy-tail corollary, inverse moments** — EP1054.tex lines 2963–2969: "In contrast, for every
`s>0`, `\sup_{X\geq1}\int x^{-s}\,d\nu_X(x)<\infty, \quad \int x^{-s}\,d\nu(x)<\infty`, where
`\infty^{-s}=0`."
Encoding: `x^{−s}` is `ENNReal.rpow` with exponent `−s < 0`, which gives exactly `∞^{−s} = 0`
(`ENNReal.top_rpow_of_neg`) and `0^{−s} = ∞`; `sup` is `⨆` over real `X ≥ 1`. -/
def Cor_DaddHeavyTails_InvMoments : Prop :=
  ∀ s : ℝ, 0 < s →
    (⨆ (X : ℝ) (_ : 1 ≤ X), ∫⁻ x, x ^ (-s) ∂(nuX X)) < ⊤ ∧
      ∀ ν : Measure ℝ≥0∞, IsWeakSubseqLimit ν → ∫⁻ x, x ^ (-s) ∂ν < ⊤

-- deps: Cor_DaddHeavyTails_InvMoments applied with `2s` (uniform integrability of `x^{−s}`);
--       weak convergence against `min(M, x^{−s})` (continuous bounded on `[0, ∞]`); Mathlib
--       `MeasureTheory.tendsto_integral_of_dominated_convergence`-type truncation removal.
/-- **Heavy-tail corollary, convergence of inverse moments** — EP1054.tex lines 2969–2970: "Along
every weakly convergent subsequence, the inverse moments converge to those of the limiting law."
Encoding: for every sequence `X_j → ∞` with `ν_{X_j} ⇒ ν` (`WeakConvAlong`, `ν` a probability
measure) and every `s > 0`, `∫ x^{−s} dν_{X_j} → ∫ x^{−s} dν` in `ℝ≥0∞`. -/
def Cor_DaddHeavyTails_InvMomentConv : Prop :=
  ∀ (ν : Measure ℝ≥0∞) (X : ℕ → ℝ), IsProbabilityMeasure ν → WeakConvAlong X ν →
    ∀ s : ℝ, 0 < s →
      Tendsto (fun j : ℕ => ∫⁻ x, x ^ (-s) ∂(nuX (X j))) atTop (𝓝 (∫⁻ x, x ^ (-s) ∂ν))

open Classical in
-- deps: Cor_DaddHeavyTails_LogMeans (the geometric mean is `exp ∫ log x dν_X`).
/-- **Heavy-tail corollary, geometric means** — EP1054.tex lines 2971–2972: "In particular, the
geometric means of `f(N)/N` tend to infinity".
Encoding: the geometric mean over the represented `N ≤ X` is
`(∏_{N≤X, N∈𝓡} f(N)/N)^{1/R(X)}` (real `rpow` of a positive product), and it tends to `+∞` as
real `X → ∞`. -/
def Cor_DaddHeavyTails_GeomMean : Prop :=
  Tendsto (fun X : ℝ =>
      (∏ N ∈ (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ R), ((f N : ℝ) / N)) ^ (1 / (Rcnt X : ℝ)))
    atTop atTop

-- deps: Thm_DaddUniversalSingularity_Tight (`ν{∞} = 0` under the criterion),
--       Cor_DaddHeavyTails_PosMoments, Cor_DaddHeavyTails_LogMeans.
/-- **Heavy-tail corollary, the tight case** — EP1054.tex lines 2972–2973: "even assuming
tightness, every subsequential probability law has infinite logarithmic mean and infinite moments
of all positive orders."
Encoding: "assuming tightness" is `Eq_TightnessCriterion` (`S6_Coverage`; equivalent to tightness
by `prop:tightness-equivalence`); then every compactified limit has `ν{∞} = 0` (so it is a law on
`[0, ∞)`), infinite log-mean (as in `Cor_DaddHeavyTails_LogMeans`) and `∫ x^s dν = ∞` for all
`s > 0`. -/
def Cor_DaddHeavyTails_Tight : Prop :=
  Eq_TightnessCriterion → ∀ ν : Measure ℝ≥0∞, IsWeakSubseqLimit ν →
    ν {⊤} = 0 ∧ (∫⁻ x, logPosE x ∂ν = ⊤ ∧ ∫⁻ x, logNegE x ∂ν < ⊤) ∧
      ∀ s : ℝ, 0 < s → ∫⁻ x, x ^ s ∂ν = ⊤

-- deps: Eq_DaddSubsequentialTail, Cor_DaddHeavyTails_PosMoments, Cor_DaddHeavyTails_LogMeans,
--       Cor_DaddHeavyTails_InvMoments, Cor_DaddHeavyTails_InvMomentConv,
--       Cor_DaddHeavyTails_GeomMean, Cor_DaddHeavyTails_Tight.
/-- **The heavy-tail corollary** — unlabeled corollary environment, EP1054.tex lines 2942–2974
(the whole environment: `eq:dadd:subsequential-tail`, positive moments, logarithmic means, inverse
moments and their convergence, geometric means, and the tight case). -/
def Cor_DaddHeavyTails : Prop :=
  Eq_DaddSubsequentialTail ∧ Cor_DaddHeavyTails_PosMoments ∧ Cor_DaddHeavyTails_LogMeans ∧
    Cor_DaddHeavyTails_InvMoments ∧ Cor_DaddHeavyTails_InvMomentConv ∧
    Cor_DaddHeavyTails_GeomMean ∧ Cor_DaddHeavyTails_Tight

/-! ## `prop:dadd:collision-criterion` (lines 3028–3072) -/

open Classical in
-- deps: Lem_SigmaRangeZero (S2: targets represented only with `e = 1` lie in `σ(ℕ)`, density 0);
--       Eq_ExactRepresentability (S1: `R(X) = X + O(1)`); `f(N) ≤ tN ⟺ r_t(N) > 0` on `𝓡`
--       (line 2260).
/-- **Proof step of `prop:dadd:collision-criterion`** — EP1054.tex lines 3050–3057: "A represented
target absent from the support of `r_t^*` can only be represented at threshold `t` using cofactor
`e=1`; such a target belongs to `range(σ)`. Lemma lem:sigma-range-zero therefore shows that
`\nu_X([0,t]) =\frac1X\#\{N\leq X:r_t^*(N)>0\}+o(1)`."
Encoding: fixed `t > 0`; `[0, t]` is `Set.Iic (ofReal t)` in `[0, ∞]`; the difference tends to `0`
as real `X → ∞`. -/
def Step_DaddCollisionSupport : Prop :=
  ∀ t : ℝ, 0 < t →
    Tendsto (fun X : ℝ => (nuX X).real (Set.Iic (ENNReal.ofReal t)) -
        (1 / X) * (((Finset.Icc 1 ⌊X⌋₊).filter (fun N : ℕ => 0 < rtStar t N)).card : ℝ))
      atTop (𝓝 0)

-- deps: Step_DaddCollisionSupport; the identity `1_{r>0} = r − (r−1)_+` for `r ∈ ℕ`;
--       Prop_DaddWitnessMeans (the average of `r_t^*` tends to `W*(t)`).
/-- **`eq:dadd:collision-criterion`**, EP1054.tex lines 3038–3042: "For every fixed `t>0`,
`\nu_X([0,t])=W^*(t)-K_X(t)+o(1).`"
Encoding: `ν_X([0, t]) − (W*(t) − K_X(t)) → 0` as real `X → ∞`, for each fixed `t > 0`. -/
def Eq_DaddCollisionCriterion : Prop :=
  ∀ t : ℝ, 0 < t →
    Tendsto (fun X : ℝ => (nuX X).real (Set.Iic (ENNReal.ofReal t)) - (WstarFun t - KX X t))
      atTop (𝓝 0)

-- deps: Eq_DaddCollisionCriterion; Eq_ExactRepresentability (S1: `R(X)/X → 1`, so the threshold
--       density exists iff `ν_X([0, t])` converges); Thm_DaddUniversalSingularity_Carrier (no
--       finite atoms: two compactified subsequential laws agreeing on every `[0, t]`, `t ∈ ℚ_{>0}`,
--       agree on `[0, ∞)`, hence everywhere); compactness of the probability measures on `[0, ∞]`
--       (Mathlib `Mathlib.MeasureTheory.Measure.Prokhorov` / compact metrizable `ℝ≥0∞`); portmanteau
--       (`MeasureTheory.tendsto_measure_of_null_frontier`) for the converse;
--       EmpiricalMeasures_isProbability (S1: compactness and portmanteau are stated for
--       `ProbabilityMeasure`, and `nuX` is a bare `Measure`).
/-- **Proposition `prop:dadd:collision-criterion`**, EP1054.tex lines 3032–3047:
"Put `K_X(t)=\frac1X\sum_{N\leq X}(r_t^*(N)-1)_+`. For every fixed `t>0`,
(eq:dadd:collision-criterion) `\nu_X([0,t])=W^*(t)-K_X(t)+o(1).` Consequently, the threshold
density exists if and only if the genuine proper-witness collision surplus `K_X(t)` converges.
The whole sequence `ν_X` converges weakly on `[0,∞]` if and only if `K_X(t)` converges for every
positive rational `t`."
Encoding: (i) `Eq_DaddCollisionCriterion`; (ii) for each `t > 0`, the natural density of
`{N ∈ 𝓡 : f(N) ≤ t N}` (the "threshold density"; `N ∈ 𝓡` conjoined because of the junk `f = 0`)
exists iff `K_X(t)` has a real limit as `X → ∞`; (iii) there is a probability measure `ν` on
`[0, ∞]` with `ν_X ⇒ ν` along real `X → ∞` iff `K_X(t)` converges for every rational `t > 0`. -/
def Prop_DaddCollisionCriterion : Prop :=
  Eq_DaddCollisionCriterion ∧
  (∀ t : ℝ, 0 < t →
    ((∃ d : ℝ, HasDens {N : ℕ | N ∈ R ∧ (f N : ℝ) ≤ t * N} d) ↔
      ∃ L : ℝ, Tendsto (fun X : ℝ => KX X t) atTop (𝓝 L))) ∧
  ((∃ ν : Measure ℝ≥0∞, IsProbabilityMeasure ν ∧
      ∀ φ : ℝ≥0∞ →ᵇ ℝ, Tendsto (fun X : ℝ => ∫ x, φ x ∂(nuX X)) atTop (𝓝 (∫ x, φ x ∂ν))) ↔
    ∀ t : ℚ, 0 < t → ∃ L : ℝ, Tendsto (fun X : ℝ => KX X (t : ℝ)) atTop (𝓝 L))

/-! ## The collision lower bound `liminf K_X(t) > 1/9` (lines 3074–3174) -/

-- deps: multiplicativity of `σ` (Mathlib `ArithmeticFunction.isMultiplicative_sigma`) with
--       `gcd(D, u) = 1` (the primes of `D ∈ 𝒞` are `2, 5`, and `gcd(u, 30) = 1`).
/-- **`eq:dadd:collision-affine`**, EP1054.tex lines 3087–3094: "For `D ∈ 𝒞` and `gcd(u,Q)=1`,
consider the canonical cofactor-two witness
```
N=s(Du)=\sigma(D)\sigma(u)-Du =u\bigl(s(D)+\sigma(D)(h(u)-1)\bigr).
```"
Encoding: `𝒞 = {2, 4, 8, 10}`, `Q = 30`, `u ≥ 1`. The first equality is stated additively in `ℕ`
(`s(Du) + Du = σ(D)σ(u)`, no truncated subtraction); the second in `ℝ` with `h(u) = abundancy u`. -/
def Eq_DaddCollisionAffine : Prop :=
  ∀ D : ℕ, D ∈ collisionCores → ∀ u : ℕ, 1 ≤ u → Nat.Coprime u 30 →
    aliquot (D * u) + D * u = sig D * sig u ∧
      (aliquot (D * u) : ℝ) = u * ((aliquot D : ℝ) + sig D * (abundancy u - 1))

-- deps: eq:F2-aliquot (S6, `F_2(d) = s(2d)`), `D u` even; `D u / 2` is a proper divisor of `D u`.
/-- **Proof step of the collision lower bound** — EP1054.tex lines 3095–3096: "Its source `n=Du` is
even, so `N=s(n)\geq n/2` and its source-to-target ratio is at most `2\leq t`."
Encoding: the witness is the cofactor-two pair `(2, Du/2)`: `F_2(Du/2) = s(Du)`, and
`Du ≤ 2 s(Du)` (ratio `≤ 2`). -/
def Step_DaddCollisionWitness : Prop :=
  ∀ D : ℕ, D ∈ collisionCores → ∀ u : ℕ, 1 ≤ u → Nat.Coprime u 30 →
    F 2 (D * u / 2) = aliquot (D * u) ∧ D * u ≤ 2 * aliquot (D * u)

-- deps: none (finite computation: `decide`/`norm_num` on the divisor sums; `Δ(5) = (1/2)(2/3)(4/5)`).
/-- **Proof step of the collision lower bound** — EP1054.tex lines 3084, 3157–3160: "`Δ(5)=φ(Q)/Q
=4/15`" and "`(D,s(D),\sigma(D)) \in\{(2,1,3),(4,3,7),(8,7,15),(10,8,18)\}`". -/
def Step_DaddCollisionCores : Prop :=
  aliquot 2 = 1 ∧ sig 2 = 3 ∧ aliquot 4 = 3 ∧ sig 4 = 7 ∧ aliquot 8 = 7 ∧ sig 8 = 15 ∧
    aliquot 10 = 8 ∧ sig 10 = 18 ∧ Delta 5 = 4 / 15

-- deps: hasSum_zeta_two (Mathlib; `ζ(2) = π²/6`) and the Euler factors at `2, 3, 5`
--       (`∑_{(d,30)=1} d^{−2} = ζ(2)(1−1/4)(1−1/9)(1−1/25)`); Real.pi_lt_d4 (Mathlib;
--       `π < 3.1416 < 22/7`) for `H < 197/3675`.
/-- **Proof step of the collision lower bound** — EP1054.tex lines 3102–3105 and 3156:
"`\sum_{\substack{d\geq1\\\gcd(d,Q)=1}}\frac1{d^2}-1 =\frac{8\pi^2}{75}-1=:H`" and "`\pi<22/7` gives
`H<197/3675`."
Encoding: the series over `d ∈ ℕ` with `gcd(d, 30) = 1` (so `d = 0` is excluded automatically)
has sum `8π²/75`; `collisionH = 8π²/75 − 1 < 197/3675`. -/
def Step_DaddCollisionH : Prop :=
  HasSum (fun d : ℕ => if Nat.Coprime d 30 then (1 : ℝ) / (d : ℝ) ^ 2 else 0)
      (8 * Real.pi ^ 2 / 75) ∧
    collisionH < 197 / 3675

-- deps: `h(u) − 1 = ∑_{d∣u, d>1} 1/d`, the density `Δ(5)/d` of `{u : (u,30)=1, d ∣ u}` for
--       `(d, 30) = 1`, dominated interchange (`∑ 1/d² < ∞`), Step_DaddCollisionH,
--       Step_DaddCollisionCores (`Δ(5) = 4/15`).
/-- **Proof step of the collision lower bound** (the divisor-sum expansion, empirical form) —
EP1054.tex lines 3099–3105: "Expanding `h(u)` as a divisor sum gives
`\frac1{\Delta(5)}\int(h-1)\,d\nu_Q(h) =\sum_{\gcd(d,Q)=1}\frac1{d^2}-1 =\frac{8\pi^2}{75}-1=:H`."
Encoding: this node is what the divisor-sum expansion computes *before* the passage to `ν_Q`, the
empirical first moment `(1/X) ∑_{u≤X, (u,30)=1} (h(u) − 1) → Δ(5) H`. The paper's identity for
the law itself is `Step_DaddCollisionFirstMomentLaw`. -/
def Step_DaddCollisionFirstMoment : Prop :=
  Tendsto (fun X : ℝ => (1 / X) *
      ∑ u ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ => Nat.Coprime u 30), (abundancy u - 1))
    atTop (𝓝 (Delta 5 * collisionH))

-- deps: Fact_DaddProgressionLaws at `e = 5` (each `ν_{a,5}` has mass `1/Λ(5) = 1/60`, and the
--       empirical laws `(1/X)∑_{u≤X, (u,30)=1} δ_{h(u)}` converge weakly to `ν_Q`, summing the 16
--       reduced classes mod 60), Step_DaddCollisionCores (`16/60 = 4/15 = Δ(5)`);
--       Step_DaddCollisionFirstMoment (the empirical first moment); Lem_KovacMoment (S4a, `q = 3`,
--       read through Notation_sigmaPrefix_zero (S1: `σ₀ = σ`, so the `j = 0` term of
--       `prefixMoment 3 n` is `h(n)³`): uniformly bounded second moment of `h(u)`, hence uniform
--       integrability of `h − 1`, so the
--       first moment passes to the weak limit — needed for the equality; the inequality
--       `∫ (h−1) dν_Q ≤ Δ(5) H`, which is all Step_DaddCollisionSourceIntensity's Jensen step needs,
--       already follows by lower semicontinuity of `∫ φ` for nonnegative continuous `φ` under weak
--       convergence, without Lem_KovacMoment).
/-- **Proof step of the collision lower bound** (the first moment of the law) — EP1054.tex lines
3098–3108: "Let `ν_Q` be the unnormalized Davenport law restricted to `gcd(u,Q)=1`, of total mass
`Δ(5)`. Expanding `h(u)` as a divisor sum gives
```
\frac1{\Delta(5)}\int(h-1)\,d\nu_Q(h) =\sum_{\substack{d\geq1\\\gcd(d,Q)=1}}\frac1{d^2}-1
 =\frac{8\pi^2}{75}-1=:H.
```
The passage to this first moment is justified by the uniformly bounded second moment of `h(u)`,
which follows from Lemma lem:kovac-moment with `q=3`."
Encoding: `ν_Q = nuQ`; (i) total mass `Δ(5)`; (ii) `h − 1` is `ν_Q`-integrable (so the Bochner
integral is a genuine one, not the junk `0`); (iii) the printed identity, with the middle series
identified with `8π²/75` in `Step_DaddCollisionH`. -/
def Step_DaddCollisionFirstMomentLaw : Prop :=
  nuQ Set.univ = ENNReal.ofReal (Delta 5) ∧
    Integrable (fun h : ℝ => h - 1) nuQ ∧
    (1 / Delta 5) * ∫ h, (h - 1) ∂nuQ = collisionH

-- deps: Eq_DaddCollisionAffine (`s(Du) ≤ X ⟺ u/X ≤ 1/(s(D) + σ(D)(h(u) − 1))`); the radial
--       partition argument of Prop_DaddWitnessMeans (as in Step_DaddWitnessCount, via
--       Step_DaddWitnessJointLimit summed over the 16 reduced classes mod `Λ(5) = 60` of
--       Fact_DaddProgressionLaws: joint weak limit `1_{[0,1]}(u) du dν_Q(h)`, null boundary by
--       atomlessness, Tonelli); Step_DaddCollisionFirstMomentLaw (`ν_Q` has mass `Δ(5)`, and
--       `∫ (h−1) dν_Q ≤ Δ(5) H` — the `≤` half suffices) and Jensen's inequality for the
--       probability measure `ν_Q/Δ(5)` (`x ↦ 1/(s + σ x)` convex and decreasing on `x ≥ 0`;
--       Mathlib `ConvexOn.map_integral_le`).
/-- **Proof step of the collision lower bound** (source intensity) — EP1054.tex lines 3109–3118:
"The radial partition argument from Proposition prop:dadd:witness-means gives the source intensity
```
W_D :=\lim_{X\to\infty}\frac1X \#\{u:\gcd(u,Q)=1,\ s(Du)\leq X\}
 =\int\frac{d\nu_Q(h)}{s(D)+\sigma(D)(h-1)} \geq\frac{\Delta(5)}{s(D)+\sigma(D)H},
```
where the last inequality is Jensen's inequality."
Encoding: for each `D ∈ 𝒞`: the limit `W_D` exists, equals the integral against `ν_Q = nuQ` (the
radial-partition identity), and is `≥ Δ(5)/(s(D) + σ(D) H)` (Jensen). `ν_Q` lives on `[1, ∞)`
(`h ≥ 1`), where the denominator is `≥ s(D) ≥ 1`, so the integrand is a.e. bounded by `1` and the
Bochner integral is a genuine one; were it the junk `0`, the lower bound would fail. The counted `u`
satisfy `u ≤ s(Du) ≤ X`, so they are enumerated in `[1, ⌊X⌋]`. -/
def Step_DaddCollisionSourceIntensity : Prop :=
  ∀ D : ℕ, D ∈ collisionCores → ∃ WD : ℝ,
    Tendsto (fun X : ℝ => (1 / X) *
        ((((Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ =>
          Nat.Coprime u 30 ∧ (aliquot (D * u) : ℝ) ≤ X)).card : ℕ) : ℝ)) atTop (𝓝 WD) ∧
      WD = ∫ h, 1 / ((aliquot D : ℝ) + sig D * (h - 1)) ∂nuQ ∧
      Delta 5 / ((aliquot D : ℝ) + sig D * collisionH) ≤ WD

-- deps: Lem_FixedModulusNormality (S2, with `V = q = 2⁴·3·5² = 1200`: outside `o(X)` sources
--       `n ≤ 2X`, `v_p(σ(n)) > v_p(D) = v_p(n)` for `p = 2, 3, 5`); then `v_p(σ(n) − n) = v_p(D)`;
--       complete periods mod `30 D` for the density of `𝒯_D`.
/-- **Proof step of the collision lower bound** (the cylinder) — EP1054.tex lines 3120–3136:
"Choose the fixed modulus `q=2^4\cdot3\cdot5^2`. Lemma lem:fixed-modulus-normality implies that,
apart from `o(X)` sources `n\leq2X`, one has `v_p(\sigma(n))>v_p(D)=v_p(n)\ (p=2,3,5)`. For every
remaining target … `v_p(N)=v_p(D)`. Thus, up to `o(X)` exceptions, its image is contained in the
cylinder `\mathcal{T}_D=\{Dv:\gcd(v,30)=1\}, \ \textup{d}(\mathcal{T}_D)=\frac{\Delta(5)}{D}`."
Encoding: for each `D ∈ 𝒞`, (i) the number of parameters `u` (coprime to 30) whose target
`s(Du) ≤ X` falls outside `𝒯_D` is `o(X)`; (ii) `𝒯_D` has natural density `Δ(5)/D`. -/
def Step_DaddCollisionCylinder : Prop :=
  ∀ D : ℕ, D ∈ collisionCores →
    Tendsto (fun X : ℝ => (1 / X) *
        ((((Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ =>
          Nat.Coprime u 30 ∧ (aliquot (D * u) : ℝ) ≤ X ∧
            ¬ (D ∣ aliquot (D * u) ∧ Nat.Coprime (aliquot (D * u) / D) 30))).card : ℕ) : ℝ))
      atTop (𝓝 0) ∧
    HasDens {N : ℕ | D ∣ N ∧ Nat.Coprime (N / D) 30} (Delta 5 / D)

-- deps: Step_DaddCollisionSourceIntensity, Step_DaddCollisionCylinder (the `W_D X` sources land,
--       up to `o(X)`, in a set of `≤ (Δ(5)/D + o(1)) X` targets; `∑ (r − 1)_+ ≥ ∑ r − #{r > 0}`).
/-- **Proof step of the collision lower bound** (per core) — EP1054.tex lines 3137–3145: "If
`r_D(N)` denotes the number of parameters `u` giving `N` in (eq:dadd:collision-affine), it follows
that
```
\liminf_{X\to\infty}\frac1X \sum_{N\leq X}(r_D(N)-1)_+
 \geq\Delta(5)\left( \frac1{s(D)+\sigma(D)H}-\frac1D\right).
```"
Encoding: `liminf ≥ c` as `∀ ε > 0, ∃ X₀, ∀ X ≥ X₀, c − ε ≤ …`; `(r − 1)_+` is truncated `ℕ`
subtraction; `r_D = rCore D`. -/
def Step_DaddCollisionPerCore : Prop :=
  ∀ D : ℕ, D ∈ collisionCores → ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    Delta 5 * (1 / ((aliquot D : ℝ) + sig D * collisionH) - 1 / (D : ℝ)) - ε ≤
      (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ((rCore D N - 1 : ℕ) : ℝ)

-- deps: Step_DaddCollisionWitness (each `(D, u)` gives the proper witness `(2, Du/2)` counted by
--       `r_t^*(N)` when `t ≥ 2`); distinct valuation vectors of the cores at `2, 3, 5` (so the maps
--       `(D, u) ↦ Du` are jointly injective); `∑ (a_i − 1)_+ ≤ (∑ a_i − 1)_+` in `ℕ`.
/-- **Proof step of the collision lower bound** (combining the cores) — EP1054.tex lines
3146–3154: "The four cores have distinct valuation vectors at `2,3,5`, whereas `u` is coprime to
`30`. Thus their source families, and hence their cofactor-two witnessing pairs, are disjoint. The
elementary inequality
```
\sum_{D\in\mathcal{C}}(r_D(N)-1)_+ \leq\left(\sum_{D\in\mathcal{C}}r_D(N)-1\right)_+
 \leq(r_t^*(N)-1)_+
```
therefore allows the four lower bounds to be added."
Encoding: for `t ≥ 2` and every `N`, the outer inequality in `ℕ` (truncated subtraction = `(·)_+`). -/
def Step_DaddCollisionCombine : Prop :=
  ∀ t : ℝ, 2 ≤ t → ∀ N : ℕ,
    ∑ D ∈ collisionCores, (rCore D N - 1) ≤ rtStar t N - 1

-- deps: none (exact rational arithmetic, `norm_num`).
/-- **Proof step of the collision lower bound** (the arithmetic) — EP1054.tex lines 3161–3170:
"`\frac4{15}\sum_{(D,s,B)}\left(\frac1{s+197B/3675}-\frac1D\right)
=\frac{3492203725711}{31001587618275} >\frac19`."
Encoding: in `ℚ`, the four terms written out for `(D, s, B) = (2,1,3), (4,3,7), (8,7,15),
(10,8,18)`. (Re-checked with exact `Fraction` arithmetic, 2026-09-25.) -/
def Step_DaddCollisionArithmetic : Prop :=
  (4 / 15 : ℚ) *
      ((1 / (1 + 197 * 3 / 3675) - 1 / 2) + (1 / (3 + 197 * 7 / 3675) - 1 / 4) +
        (1 / (7 + 197 * 15 / 3675) - 1 / 8) + (1 / (8 + 197 * 18 / 3675) - 1 / 10)) =
      3492203725711 / 31001587618275 ∧
    (1 / 9 : ℚ) < 3492203725711 / 31001587618275

-- deps: Step_DaddCollisionPerCore, Step_DaddCollisionCombine, Step_DaddCollisionCores,
--       Step_DaddCollisionH (`H < 197/3675`, so each `1/(s + σH) > 1/(s + 197σ/3675)`, all four
--       terms positive), Step_DaddCollisionArithmetic.
/-- **Proof step of the collision lower bound** (explicit form) — EP1054.tex lines 3161–3170:
"`\liminf_{X\to\infty}K_X(t) > \frac4{15}\sum_{(D,s,B)}(\ldots) =\frac{3492203725711}{31001587618275}`".
Encoding: for each `t ≥ 2`, `liminf K_X(t) > r` as `∃ c > r, eventually K_X(t) ≥ c` (`K_X ≥ 0`). -/
def Step_DaddCollisionExplicit : Prop :=
  ∀ t : ℝ, 2 ≤ t → ∃ c : ℝ, (3492203725711 / 31001587618275 : ℝ) < c ∧
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → c ≤ KX X t

-- deps: Step_DaddCollisionExplicit, Step_DaddCollisionArithmetic (`> 1/9`); through them
--       Eq_DaddCollisionAffine, Step_DaddCollisionWitness, Step_DaddCollisionCores,
--       Step_DaddCollisionH (hasSum_zeta_two, Real.pi_lt_d4), Step_DaddCollisionFirstMoment,
--       Step_DaddCollisionFirstMomentLaw (Lem_KovacMoment, S4a), Step_DaddCollisionSourceIntensity
--       (Prop_DaddWitnessMeans' radial argument via Step_DaddWitnessJointLimit,
--       Fact_DaddProgressionLaws / Cite_PollackAP), Step_DaddCollisionCylinder
--       (Lem_FixedModulusNormality, S2),
--       Step_DaddCollisionPerCore, Step_DaddCollisionCombine.
/-- **The collision lower bound** — unlabeled proposition, EP1054.tex lines 3076–3081:
"For every `t\geq2`, `\liminf_{X\to\infty}K_X(t)>\frac19.`"
Encoding: `liminf_{X→∞} K_X(t) > 1/9` as `∃ c > 1/9, ∃ X₀, ∀ X ≥ X₀, c ≤ K_X(t)` — equivalent
(`K_X(t) ≥ 0`), and immune to Mathlib's junk `liminf` of unbounded functions; `c` may depend on `t`
(as printed; the proof's constant does not). Real `X → ∞`. -/
def Prop_DaddCollisionLowerBound : Prop :=
  ∀ t : ℝ, 2 ≤ t → ∃ c : ℝ, 1 / 9 < c ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → c ≤ KX X t

end Principia.Erdos1054
