/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) §1, lines 1–349 — the headline theorems, as named `Prop`s

**Statements only.** Every result of `Campaigns/Erdos-1054/collab-paper/EP1054.tex`, lines 1–349
(abstract, §1 Introduction, §1 Notation) is stated here as a `def … : Prop`. Nothing is asserted:
the proofs live in the later sections, and each `-- deps:` comment names the paper results and the
`Statements.Inputs` inputs the paper's proof of that statement uses, so the spine can be read off.
(Those input names occur only in comments, so `Statements.Inputs` is deliberately not imported: no
body here uses it, and importing it would only couple this module's rebuilds to it.)

**Owner of the shared §1 objects.** `Rcnt`, `ratioE`, `nuX`, `smallRatioSet`, `largeRatioSet` and
`Eq_ExactRepresentability` are defined here and only here. The later modules import this one and
use them directly (`S3_Repr` names `Thm_FraitureRepresentability` as an `abbrev` of
`Eq_ExactRepresentability`; `S4a_SmallUpper`, `S6_Coverage`, `S7_Limits` use `smallRatioSet`,
`nuX`, `Rcnt`); the local copies they carried while this module was unbuilt were removed on
2026-09-25.

Contents:

* The intro objects `Rcnt` (`R(X)`), `ratioE` (`f(N)/N ∈ [0, ∞]`) and the empirical measures
  `nuX` (`ν_X`, `eq:empirical-measures`), plus the two ratio sets `smallRatioSet δ` and
  `largeRatioSet T` that every tail statement is about (both conjoin `N ∈ 𝓡`, because `f` has the
  junk value `0` off `𝓡`).
* `thm:small-upper` (Thm 1.1), `thm:small-values` (Thm 1.2), `thm:almost-log-tail` (Thm 1.3) with
  both of its consequences, `thm:subexp-growth` (Thm 1.4) with both assertions, and the numbered
  displays `eq:exact-representability`, `eq:almost-log-tail`, `eq:subexp-growth`,
  `eq:positive-moment-growth`, `eq:empirical-measures`.
* The unlabeled assertions of the introduction and notation section (the `liminf = 0` remark,
  `R(X) = ⌊X⌋ − 2`, the density reading of the Theorems 1.1/1.2, the answers to Erdős's questions
  — plain failure of `f(N) = o(N)`, its failure for almost all `N`, and the "strong sense" of the
  abstract (`Intro_LittleO_onlyOnDensityZero`) — the density meaning of `Δ(y)`, `σ₀ = σ`), each
  with its line number.

**Not restated here** (they are intro *previews* of results stated and proved later; they belong
to the modules for those sections): the tightness/coverage equivalence (lines 241–246 =
`prop:tightness-equivalence`, line 2675, and `conj:bounded-cofactor-weak`, line 2650); the
singularity of subsequential laws (lines 249–257 = `thm:dadd:universal-singularity`, line 2840);
the witness mean `W*(t)` and the surplus identity (lines 259–268 = `prop:dadd:witness-means`,
line 2753, and `prop:dadd:collision-criterion`, line 3033).
-/

namespace Principia.Erdos1054

open Finset Filter
open scoped Topology ENNReal

/-! ## Intro objects: `R(X)`, the ratio sets, and the empirical measures `ν_X` -/

/-- `R(X) := #(𝓡 ∩ [1, X])`, EP1054.tex line 225 (inside `eq:empirical-measures`).
It is `cnt R X`, i.e. the number of represented `N` with `1 ≤ N ≤ ⌊X⌋`. -/
noncomputable def Rcnt (X : ℝ) : ℕ := cnt R X

/-- The small-ratio set `{N ∈ 𝓡 : f(N) ≤ δ N}` of Theorems 1.1 and 1.2 (lines 145, 163).
The conjunct `N ∈ R` is essential: `f` is `0` off `𝓡`, so without it every unrepresented `N`
would count. -/
def smallRatioSet (δ : ℝ) : Set ℕ := {N : ℕ | N ∈ R ∧ (f N : ℝ) ≤ δ * N}

/-- The large-ratio set `{N ∈ 𝓡 : f(N) > T N}` of Theorem 1.3 (line 184). -/
def largeRatioSet (T : ℝ) : Set ℕ := {N : ℕ | N ∈ R ∧ T * N < (f N : ℝ)}

/-- The ratio `f(N)/N` as a point of `[0, ∞] = ℝ≥0∞`. For `N ∈ 𝓡` one has `N ≥ 1` and `f N ≥ 1`,
so this is `ENNReal.ofReal` of a finite positive real, i.e. a point of `(0, ∞)`, as the paper
requires ("`δ_x` is unit mass at `x ∈ (0, ∞)`", line 227). -/
noncomputable def ratioE (N : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((f N : ℝ) / N)

open Classical in
/-- **The empirical measures `ν_X`** — `eq:empirical-measures`, EP1054.tex line 222:
```
\nu_X:=\frac1{R(X)} \sum_{\substack{N\leq X\\N\in\Rcal}}\delta_{f(N)/N},
\quad R(X):=\#(\Rcal\cap[1,X]),\quad X\geq1,
```
"where `δ_x` is unit mass at `x ∈ (0, ∞)`."

Encoding choices.
* **Ambient space `[0, ∞] = ℝ≥0∞`** (Borel σ-algebra, `ENNReal.measurableSpace`). The paper's
  commented-out line 228 and §6–7 (lines 2262–2267, 2843: "weak subsequential limit `ν` of `ν_X`
  on `[0, ∞]`", "`ν_X((T, ∞])`") regard `ν_X` as a measure on the compactified half-line, so that
  subsequential limits exist without tightness; each `ν_X` itself gives `{∞}` mass `0`.
* The sum runs over `N ∈ [1, ⌊X⌋]` with `N ∈ 𝓡` (the same index set that `Rcnt X` counts).
* Normalisation `(R(X))⁻¹` in `ℝ≥0∞`. The paper only defines `ν_X` for `X ≥ 1`, where
  `R(X) ≥ 1` (since `1 = d₁(1) ∈ 𝓡`). For `X < 1` the sum is empty and `ν_X = 0` (`∞ • 0 = 0`);
  this junk value is never used. That `ν_X` is a probability measure for `X ≥ 1` is the separate
  statement `EmpiricalMeasures_isProbability`.

**Warning — do not state tightness with Mathlib's `IsTightMeasureSet` on this space.** `ℝ≥0∞` is
compact (`compactSpace_of_completeLinearOrder`, Mathlib `Topology/Order/Compact.lean`), and every
set of measures on a compact space is tight (`MeasureTheory.IsTightMeasureSet.of_compactSpace`,
`MeasureTheory/Measure/Tight.lean`). So `IsTightMeasureSet {nuX X | X ≥ 1}` is trivially true, and
any equivalence built on it would be vacuous. The paper's "tight on `[0, ∞)`" (line 241) is defined
at lines 2264–2267 as `lim_{T→∞} sup_{X≥1} ν_X((T, ∞]) = 0` with finite `T`; use that
definition, which `Statements/S6_Coverage.lean` states as `Coverage.NuTight`. -/
noncomputable def nuX (X : ℝ) : MeasureTheory.Measure ℝ≥0∞ :=
  (Rcnt X : ℝ≥0∞)⁻¹ •
    ∑ N ∈ (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ R), MeasureTheory.Measure.dirac (ratioE N)

-- deps: `1 ∈ 𝓡` (d₁(1) = 1; `mem_R_iff_exists_F` with e = d = 1), so `Rcnt X ≥ 1` for `X ≥ 1`;
--       then `ν_X` is a normalised sum of `Rcnt X` Dirac masses.
-- used by: the §7 steps that apply portmanteau or Prokhorov compactness to `ν_X` (Mathlib states
--          these for `ProbabilityMeasure`, and `nuX` is a bare `Measure`):
--          Thm_DaddUniversalSingularity_Carrier, Thm_DaddUniversalSingularity_Tight,
--          Eq_DaddSubsequentialTail, Prop_DaddCollisionCriterion (S7).
/-- **`ν_X` is a probability measure** (EP1054.tex line 221: "the empirical probability measures
(eq:empirical-measures)", defined for `X ≥ 1`, line 225). Unlabeled; a well-definedness check of
`nuX`, stated so that later modules may consume it by name. -/
def EmpiricalMeasures_isProbability : Prop :=
  ∀ X : ℝ, 1 ≤ X → MeasureTheory.IsProbabilityMeasure (nuX X)

/-! ## Exact representability (`eq:exact-representability`) -/

-- deps: proved as thm:fraiture-representability (line 678; S3_Repr, where
--       Thm_FraitureRepresentability is an `abbrev` of this Prop). Its proof (lines 955–966) uses
--       Prop_FraitureFinite (line 727), Prop_FraitureTail (line 903), Step_FraitureSmallCases;
--       through them Lem_FraiturePrimeWindow (line 691), Lem_FraitureExtension (line 711) and the
--       inputs Comp_Verifier_small, Comp_Verifier_window1, Comp_Verifier_largeSeed,
--       Cite_Dusart_Thm69, and (via Lem_FraitureBalancedGoldbach) Cite_Helfgott_weighted,
--       Cite_RosserSchoenfeld_psi (Rem_FraitureCheckUsage, first conjunct).
--       NOT Lem_AnalyticOddRepresentability: the remark at line 971 says the analytic lemma is
--       independent of the exact classification.
/-- `eq:exact-representability`, EP1054.tex line 114 (posed as the OEIS A167485 question, proved
as `thm:fraiture-representability`, line 678; reused at line 2695):
```
\Rcal=\N\setminus\{2,5\}.
```
Encoding: the paper's `ℕ` is the positive integers, so `ℕ ∖ {2, 5}` is `{N : 1 ≤ N, N ≠ 2, 5}`.
(`0 ∉ R` holds definitionally-by-proof, since a nonempty divisor prefix has positive sum.) -/
def Eq_ExactRepresentability : Prop :=
  R = {N : ℕ | 1 ≤ N ∧ N ≠ 2 ∧ N ≠ 5}

-- deps: Eq_ExactRepresentability (count `{1, …, ⌊X⌋} ∖ {2, 5}`).
/-- **`R(X) = ⌊X⌋ − 2` for `X ≥ 5`** — unlabeled, EP1054.tex line 230: "Since we will see that
`R(X) = ⌊X⌋ − 2` for `X ≥ 5`, the normalization by `R(X)` is asymptotically equivalent to the one
by `X`." Natural subtraction is harmless: `⌊X⌋₊ ≥ 5`. -/
def Intro_RcntFormula : Prop :=
  ∀ X : ℝ, 5 ≤ X → Rcnt X = ⌊X⌋₊ - 2

/-! ## Unlabeled remarks of the introduction (lines 105–109) -/

-- deps: `sig n = F 1 n` (definition of F; all divisors of n are ≤ n) and f_le_of_F (Basic)
--       with e = 1, d = n.
/-- **`f(σ(n)) ≤ n`** — unlabeled, EP1054.tex line 105: "The obvious inequality `f(σ(n)) ≤ n` …".
Includes `σ(n) ∈ 𝓡` (the full divisor list is a prefix), which the paper leaves implicit and which
is needed for the inequality to be about the real `f` rather than its junk value. `n ≥ 1`. -/
def Intro_f_sigma_le : Prop :=
  ∀ n : ℕ, 1 ≤ n → sig n ∈ R ∧ f (sig n) ≤ n

-- deps: Intro_f_sigma_le; unboundedness of `σ(n)/n` (Mathlib: `Nat.Primes.not_summable_one_div`,
--       via `σ(∏_{p≤z} p)/∏_{p≤z} p = ∏_{p≤z}(1 + 1/p)`); `σ(n) → ∞`.
/-- **`liminf_{N → ∞, N ∈ 𝓡} f(N)/N = 0`** — unlabeled, EP1054.tex lines 105–107: "The obvious
inequality `f(σ(n)) ≤ n`, together with the well-known unboundedness of `σ(n)/n`, gives
`\liminf_{N\to\infty,\,N\in\Rcal}f(N)/N=0`."
Encoding: the ratios are nonnegative, so `liminf = 0` along `𝓡` is: for every `ε > 0`, the ratio
drops below `ε` at arbitrarily large represented `N`. -/
def Intro_LiminfZero : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ N ∈ R ∧ (f N : ℝ) / N < ε

/-! ## Theorem 1.1 (`thm:small-upper`) -/

-- deps: Lem_KovacMoment (lem:kovac-moment, line 990; its proof uses Std_Mertens2 for
--       `∑_{p≤q} 1/p ≪ log log q`); f_mem_Fform (Basic) + divisor reflection, to write
--       `N = σ_j(n)` with `n = f(N) ≤ δX` and `σ_j(n)/n ≥ 1/δ` (lines 1125–1127); Markov's
--       inequality; the choice `q = ⌊exp((1/δ)^c)⌋` (lines 1134–1145). Proof: lines 1118–1148.
--       Proof steps (S4a_SmallUpper): SmallUpper_emptyCase (δX < 1), SmallUpper_markov,
--       SmallUpper_momentStep (from SmallUpper_markov and Lem_KovacMoment),
--       SmallUpper_paramChoice.
/-- **Theorem 1.1, first assertion** (`thm:small-upper`, EP1054.tex line 140):
"There is an absolute constant `c > 0` such that, for all sufficiently small `δ > 0` and every
`X ≥ 1`,
```
\#\{N\leq X:N\in\Rcal,\ f(N)\leq\delta N\} \ll X\exp\{-\exp((1/\delta)^c)\}.
```"
Encoding: `c`, the implied constant `C` and the smallness threshold `δ₀` are all absolute (line 336:
"All implied constants are absolute unless their dependence is indicated"), so all three are
quantified *before* `δ` and `X`: the bound is uniform in `δ ∈ (0, δ₀]` and `X ≥ 1`.
`(1/δ)^c` is the real power. The count is `cnt (smallRatioSet δ) X`, which conjoins `N ∈ 𝓡`. -/
def Thm_SmallUpper_doubleExp : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ X : ℝ, 1 ≤ X →
      (cnt (smallRatioSet δ) X : ℝ) ≤ C * X * Real.exp (-Real.exp ((1 / δ) ^ c))

-- deps: Thm_SmallUpper_doubleExp (`exp(-exp(x^c)) ≤ C_M x^{-M}` for `x ≥ 1/δ₀`; line 1146);
--       that elementary decay is SmallUpper_doubleExpPower (S4a_SmallUpper).
/-- **Theorem 1.1, second assertion** (`thm:small-upper`, EP1054.tex lines 148–149):
"In particular, for every fixed `M > 0` this counting function is `O_M(δ^M X)`, uniformly in `X`."
Encoding: the δ-range is the theorem's ("for all sufficiently small `δ`"), with the same absolute
`δ₀` for every `M`, quantified first; the constant `C` may depend on `M` (`O_M`) and is uniform in
`δ ∈ (0, δ₀]` and `X ≥ 1`. (Since the count is `≤ X`, the bound in fact extends to all `δ > 0`;
that extension is *not* asserted here, to keep the paper's hypothesis.) -/
def Thm_SmallUpper_fixedPower : Prop :=
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ M : ℝ, 0 < M → ∃ C : ℝ,
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ X : ℝ, 1 ≤ X →
      (cnt (smallRatioSet δ) X : ℝ) ≤ C * δ ^ M * X

-- deps: Thm_SmallUpper_doubleExp, Thm_SmallUpper_fixedPower (the two assertions).
/-- **Theorem 1.1** (`thm:small-upper`, EP1054.tex line 140), the whole theorem environment:
the double-exponential bound together with its fixed-power corollary. -/
def Thm_SmallUpper : Prop :=
  Thm_SmallUpper_doubleExp ∧ Thm_SmallUpper_fixedPower

-- deps: Thm_SmallUpper_doubleExp (divide by `X`, take `limsup`).
/-- **Asymptotic form of Theorem 1.1** — unlabeled display, EP1054.tex lines 152–154:
"An immediate asymptotic consequence of Theorem thm:small-upper is
```
\upperdens\big(\{N\in\Rcal : f(N)\leq\delta N\}\big) \ll \exp\{-\exp((1/\delta)^c)\}
```
for all sufficiently small `δ > 0`."
Encoding: as in `Thm_SmallUpper_doubleExp` — absolute `c`, `C`, `δ₀` quantified before `δ`. The
`c` is existentially re-quantified (the display uses the theorem's `c`; any valid `c` suffices). -/
def Thm_SmallUpper_upperDens : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    upperDens (smallRatioSet δ) ≤ C * Real.exp (-Real.exp ((1 / δ) ^ c))

/-! ## Theorem 1.2 (`thm:small-values`) -/

-- deps: Eq_SvBasic (eq:sv-basic, line 1212: `f(s(n)) ≤ n`, n ≥ 2); Eq_SvD (line 1226, the
--       abundant factor D, existence via `Nat.Primes.not_summable_one_div`); Lem_SvA0 (the
--       unlabeled lemma at line 1245: Lem_SvA0Count `#𝒜₀(X) ≫_δ X`, Lem_SvA0Unique,
--       Eq_SvTwoSided line 1253, Lem_SvA0QLarge) — all four in S4a_SmallUpper;
--       Lem_SvRegular (line 1394, the regular family 𝒜(X)); Lem_SvClasses (line 1486, the classes
--       𝒜_d(X), d ∈ 𝒟_X, and `∑_{d∈𝒟_X} 1/d ≫ log Y`); Prop_SvSecondMoment (line 1531, the
--       collision bound `∑_u R_d(u)^2`); Cauchy–Schwarz (Mathlib
--       `Finset.sum_mul_sq_le_sq_mul_sq`); disjointness of the images s(𝒜_d(X)).
--       Proof: lines 1862–1884 (monotone in δ for δ > 1). Proof steps (S4b_SmallValues):
--       Claim_SvCauchySchwarz, Claim_SvClassImage, Claim_SvImageCount, Claim_SvWitness, which give
--       SvFamilyTarget (S4a_SmallUpper); then rescaling `X`.
/-- **Theorem 1.2** (`thm:small-values`, EP1054.tex line 159):
"For every `δ > 0` there is `c_δ > 0` such that
```
\#\{N\leq X:N\in\Rcal,\ f(N)\leq\delta N\} \geq c_\delta X
```
for all sufficiently large `X`."
Encoding: `∀ δ > 0, ∃ c > 0, ∃ X₀, ∀ X ≥ X₀` (both `c` and `X₀` may depend on `δ`). -/
def Thm_SmallValues : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    c * X ≤ (cnt (smallRatioSet δ) X : ℝ)

-- deps: Thm_SmallValues (limsup of `cnt/X` is `≥ c_δ`).
/-- **Asymptotic form of Theorem 1.2, as printed** — unlabeled display, EP1054.tex lines 169–171:
"This time, the asymptotic variant of Theorem thm:small-values reads
```
\upperdens\big(\{N\in\Rcal : f(N)\leq\delta N\}\big) > 0
```
for every `δ > 0`."
Transcribed verbatim (upper density). Note: Theorem 1.2 actually gives the stronger *lower*-density
statement `Thm_SmallValues_lowerDens`, which is what the abstract (line 79) claims; the printed
`\upperdens` is presumably a slip — flagged, not corrected here. -/
def Thm_SmallValues_upperDens : Prop :=
  ∀ δ : ℝ, 0 < δ → 0 < upperDens (smallRatioSet δ)

-- deps: Thm_SmallValues (liminf of `cnt/X` is `≥ c_δ`).
/-- **Small ratios on a set of positive lower density** — the abstract, EP1054.tex line 79:
"Arbitrarily small and arbitrarily large ratios `f(N)/N` each occur on sets of positive lower
density." (The small-ratio half; the large-ratio half is `Thm_AlmostLogTail_posLowerDens`.) -/
def Thm_SmallValues_lowerDens : Prop :=
  ∀ δ : ℝ, 0 < δ → 0 < lowerDens (smallRatioSet δ)

/-! ## Theorem 1.3 (`thm:almost-log-tail`) -/

-- deps: Prop_FmEnvelope (prop:fm-envelope, line 2002) at A = E; Cor_FmEnvelopeTail
--       (cor:fm-envelope-tail, line 2025); Lem_Moment (lem:moment, line 565, in the form
--       Eq_LargeCount, line 578, with k = j, A = T); Lem_AnalyticOddRepresentability
--       (lem:analytic-odd-representability, line 652; V_E consists of odd E-rough integers);
--       `∑_{p>E} 1/p^2 ≪ 1/E` (elementary); `L(E) = (1/b_j + o(1)) L(T)` for
--       `E = ⌈T^{b_j}(log T)^{3/(j−1)}⌉` (elementary asymptotics); then T → ∞, j → ∞.
--       Proof: lines 2066–2107. Independent of the finite representability computation.
--       Proof steps (S5_UpperTails): UpperTails.Claim_AlmostLogTail_fixedJ (the fixed-`j` form,
--       from UpperTails.Claim_AlmostLogTail_main and UpperTails.Claim_LscaleRatio); then `j → ∞`.
/-- **Theorem 1.3, main display** (`eq:almost-log-tail`, inside `thm:almost-log-tail`,
EP1054.tex lines 176–183): "As `T → ∞`,
```
\lowerdens(\{N\in\Rcal:N\text{ squarefree},\ f(N)>TN\})
 \geq\left(\frac{e^{-\gamma}}2-o(1)\right) \frac{\log\log\log T}{(\log T)(\log\log T)}.
```"
Encoding: the `o(1)` is `∀ ε > 0, ∃ T₀, ∀ T ≥ T₀`; the scale is `Lscale T =
log₃ T / (log T · log₂ T)` (`Defs.Lscale`, with `logIt` the iterated natural log); `γ` is
`eulerGamma`. The set conjoins `N ∈ 𝓡` and `Squarefree N`; the density is the paper's
`liminf_{X→∞}` of `#(S ∩ [1, X])/X` (`lowerDens`). -/
def Eq_AlmostLogTail : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (Real.exp (-eulerGamma) / 2 - ε) * Lscale T ≤
      lowerDens {N : ℕ | N ∈ R ∧ Squarefree N ∧ T * N < (f N : ℝ)}

-- deps: Eq_AlmostLogTail (take T' ≥ max(T, T₀) with a positive right-hand side; the set for T'
--       is contained in `largeRatioSet T`, and `lowerDens` is monotone).
/-- **Theorem 1.3, first consequence** (`thm:almost-log-tail`, EP1054.tex lines 184–185):
"Consequently, `{N ∈ 𝓡 : f(N) > TN}` has positive lower density for every fixed `T > 0`". -/
def Thm_AlmostLogTail_posLowerDens : Prop :=
  ∀ T : ℝ, 0 < T → 0 < lowerDens (largeRatioSet T)

-- deps: Thm_AlmostLogTail_posLowerDens (a set of positive lower density is infinite).
/-- **Theorem 1.3, second consequence** (`thm:almost-log-tail`, EP1054.tex lines 185–188):
```
\limsup_{\substack{N\to\infty\\N\in\Rcal}}\frac{f(N)}N=\infty.
```
Encoding: `limsup = ∞` along `𝓡` means that for every bound `B` the ratio exceeds `B` at
arbitrarily large represented `N` (real division; `N ∈ 𝓡` forces `N ≥ 1`). This settles Erdős's
third question (line 109, line 191). -/
def Thm_AlmostLogTail_limsup : Prop :=
  ∀ B : ℝ, ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ N ∈ R ∧ B < (f N : ℝ) / N

-- deps: Eq_AlmostLogTail, Thm_AlmostLogTail_posLowerDens, Thm_AlmostLogTail_limsup.
/-- **Theorem 1.3** (`thm:almost-log-tail`, EP1054.tex line 176), the whole theorem environment:
the main display `eq:almost-log-tail` and both consequences. -/
def Thm_AlmostLogTail : Prop :=
  Eq_AlmostLogTail ∧ Thm_AlmostLogTail_posLowerDens ∧ Thm_AlmostLogTail_limsup

/-! ## Theorem 1.4 (`thm:subexp-growth`) -/

open Classical in
-- deps: Lem_SigmaRate (lem:sigma-rate, line 508, via eq:sharp-bad-source-count line 2138, incl.
--       its `B_2(y) ≪ √y` part); Lem_FmModulus (lem:fm-modulus, line 406, `R = (n/L) C`);
--       Lem_KernelTails (lem:kernel-tails, line 1898, eq:moving-kernel-tail line 1922);
--       Lem_Moment (lem:moment, line 565, eq:large-count, with k fixed, (k+1)ε > 2);
--       Lem_AnalyticOddRepresentability (line 652); Std_Mertens3 (eq:sharp-rough-target-count
--       line 2124, `Δ(P) ≍ 1/J`, and `∏_{p≤F}(1 − 1/p)^{-1} ≪ log F`); Chebyshev from Mathlib
--       (`primorial_le_four_pow`: `log(P#) ≪ P`; `Chebyshev.psi_eq_log_lcmUpto` +
--       `Chebyshev.psi_le_const_mul_self`: `log Λ(F) ≪ F`); complete periods mod `P#` (CRT);
--       `∑_{p>P} 1/p^2 ≪ 1/P`. Proof: lines 2111–2233. Independent of the finite computation.
--       Proof steps (S5_UpperTails): UpperTails.Claim_SubexpCore (the count at threshold `t`)
--       and UpperTails.Claim_SubexpThreshold (`t` versus the `N`-dependent threshold).
/-- **Theorem 1.4, first assertion** (`eq:subexp-growth`, inside `thm:subexp-growth`, EP1054.tex
lines 196–208): "For every fixed `η > 0` there is `c_η > 0` such that, for all sufficiently large
`X`,
```
\#\biggl\{ \frac X2<N\leq X:N\in\Rcal,\ N\text{ squarefree},
 \frac{f(N)}N> \exp\biggl[\left(\frac1{\sqrt2}-\eta\right)
 \sqrt{(\log\log\log N)(\log\log\log\log N)}\biggr]\biggr\}
 \geq c_\eta\frac X{\log\log\log X}.
```"
Encoding: `∀ η > 0, ∃ c > 0, ∃ X₀, ∀ X ≥ X₀`. The integers `X/2 < N ≤ X` are exactly
`N ∈ (⌊X/2⌋₊, ⌊X⌋₊]` (`Finset.Ioc`), valid for `X ≥ 0`. The threshold uses the iterated logs *of
`N`* (`logIt 3 N`, `logIt 4 N`), as printed, and the right-hand side `log₃ X` of `X`. `√` is
`Real.sqrt` (its junk value `0` on negatives only matters for `N < e^{e^e}`, excluded for `X`
large since `N > X/2`). The ratio is real division; `N ∈ 𝓡` and `Squarefree N` are conjoined. -/
def Eq_SubexpGrowth : Prop :=
  ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    c * X / logIt 3 X ≤
      ((((Finset.Ioc ⌊X / 2⌋₊ ⌊X⌋₊).filter (fun N : ℕ =>
          N ∈ R ∧ Squarefree N ∧
            Real.exp ((1 / Real.sqrt 2 - η) *
                Real.sqrt (logIt 3 (N : ℝ) * logIt 4 (N : ℝ))) < (f N : ℝ) / N)).card : ℕ) : ℝ)

open Classical in
-- deps: Eq_SubexpGrowth (with an auxiliary smaller η; drop the other terms, all ≥ 0; raise to
--       the power s; `log₄ X = o(√(log₃ X · log₄ X))` absorbs the factor `c_η/log₃ X`).
--       Proof: lines 2235–2243.
/-- **Theorem 1.4, second assertion** (`eq:positive-moment-growth`, inside `thm:subexp-growth`,
EP1054.tex lines 209–216): "For every fixed `s > 0` and `η > 0`, we have
```
\frac1X\sum_{\substack{N\leq X\\N\in\Rcal}} \left(\frac{f(N)}N\right)^s
 \geq\exp\biggl[\left(\frac{s}{\sqrt2}-\eta\right)
 \sqrt{(\log\log\log X)(\log\log\log\log X)}\biggr]
```
for all sufficiently large `X`."
Encoding: `∀ s > 0, ∀ η > 0, ∃ X₀, ∀ X ≥ X₀`; the sum runs over `N ∈ [1, ⌊X⌋₊]` with `N ∈ 𝓡`
(so `f N ≥ 1` and the real power `(f N / N)^s` has a positive base); normalisation by `X`, not by
`R(X)`, as printed. -/
def Eq_PositiveMomentGrowth : Prop :=
  ∀ s : ℝ, 0 < s → ∀ η : ℝ, 0 < η → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    Real.exp ((s / Real.sqrt 2 - η) * Real.sqrt (logIt 3 X * logIt 4 X)) ≤
      (1 / X) * ∑ N ∈ (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ R), ((f N : ℝ) / N) ^ s

-- deps: Eq_SubexpGrowth, Eq_PositiveMomentGrowth.
/-- **Theorem 1.4** (`thm:subexp-growth`, EP1054.tex line 196), the whole theorem environment:
both assertions. -/
def Thm_SubexpGrowth : Prop :=
  Eq_SubexpGrowth ∧ Eq_PositiveMomentGrowth

/-! ## The answers to Erdős's questions (lines 79, 108–109, 152–155, 191–192) -/

-- deps: Thm_AlmostLogTail_limsup (or Thm_SmallUpper: most `N` have `f(N) > δN`).
/-- **`f(N) = o(N)` fails** — unlabeled; EP1054.tex line 108 ("Erdős asked whether `f(N) = o(N)`
holds as `N → ∞`"). Encoding: the negation of `∀ ε > 0, eventually (N ∈ 𝓡 → f(N) ≤ εN)`; the
conjunct `N ∈ 𝓡` keeps the junk value `f = 0` off `𝓡` from making the `o(N)` statement trivially
true there.
This is **plain** failure only. The abstract (line 79) says `f(N) = o(N)` "fails in a strong
sense"; that stronger claim is `Intro_LittleO_onlyOnDensityZero` (from `Thm_SmallUpper_upperDens`),
which, given that `𝓡` has positive lower density (e.g. `Thm_AlmostLogTail_posLowerDens`, since
`largeRatioSet T ⊆ 𝓡`), implies this def and `Intro_ErdosAlmostAllLittleO_fails`. -/
def Intro_ErdosLittleO_fails : Prop :=
  ¬ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → N ∈ R → (f N : ℝ) ≤ ε * N

-- deps: Thm_AlmostLogTail_posLowerDens at T = 1 (if `S` had density one and `f(N)/N → 0` on
--       `S ∩ 𝓡`, then `largeRatioSet 1 ⊆ (ℕ ∖ S) ∪ [0, N₀)` would have density zero).
--       Alternatively Intro_LittleO_onlyOnDensityZero (via Thm_SmallUpper_upperDens) together with
--       Thm_AlmostLogTail_posLowerDens (so `𝓡 ⊇ largeRatioSet 1` has positive lower density).
/-- **`f(N) = o(N)` fails even for almost all `N`** — unlabeled; EP1054.tex lines 108–109 ("whether
this might at least hold for almost all `N` (in an unspecified sense)"), line 155 ("This fact
already strongly refutes Erdős's intuition that `f(N)` is typically much smaller than `N`") and
line 192. Encoding of "almost all": the standard reading, along a set `S` of natural density one.
The negation says no density-one set carries `f(N)/N → 0` on its represented members.
This is the weakest refutation among the natural readings of "almost all" (`HasDens S 1` is the
most demanding hypothesis on `S`). The paper proves much more: `Intro_LittleO_onlyOnDensityZero`
says every set carrying `f(N) = o(N)` has represented part of density zero, which (since `𝓡` has
positive lower density) also refutes the variant with `upperDens S = 1`. -/
def Intro_ErdosAlmostAllLittleO_fails : Prop :=
  ¬ ∃ S : Set ℕ, HasDens S 1 ∧
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → N ∈ S → N ∈ R → (f N : ℝ) ≤ ε * N

-- deps: Thm_SmallUpper_upperDens. If `f(N) ≤ εN` eventually on `S ∩ 𝓡` for every `ε > 0`, then
--       for every `δ ∈ (0, δ₀]` one has `(S ∩ 𝓡) ∩ [N₀(δ), ∞) ⊆ smallRatioSet δ`; `upperDens`
--       is monotone and ignores finite sets, so `upperDens (S ∩ 𝓡) ≤ C·exp(-exp((1/δ)^c))` for
--       every small `δ`, which tends to `0` as `δ → 0`; with `cnt ≥ 0` this gives density zero.
--       Independent of the finite representability computation.
/-- **`f(N) = o(N)` fails in a strong sense** — the abstract, EP1054.tex line 79 ("we show that
`f(N)=o(N)` fails in a strong sense"), supported by the upper-density display of lines 152–155
("This fact already strongly refutes Erdős's intuition that `f(N)` is typically much smaller
than `N`") and line 192.
Encoding: the paper does not quantify "strong sense"; the reading chosen is what the display of
lines 152–155 yields: *along any set `S` on which `f(N) = o(N)` holds, the represented members form
a set of density zero*. The hypothesis is the `o(N)` statement restricted to `S ∩ 𝓡` (the junk value
`f = 0` off `𝓡` forces the conjunct); the conclusion is about `S ∩ 𝓡`, so it does not use
`Eq_ExactRepresentability`. Density zero cannot be improved to finiteness: `Intro_LiminfZero`
yields infinite such `S`. -/
def Intro_LittleO_onlyOnDensityZero : Prop :=
  ∀ S : Set ℕ,
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → N ∈ S → N ∈ R → (f N : ℝ) ≤ ε * N) →
      DensZero {N : ℕ | N ∈ S ∧ N ∈ R}

/-! ## Notation facts asserted in §1 "Notation" (lines 306–346) -/

-- deps: complete periods modulo `y#` (the indicator of `gcd(n, y#) = 1` is `y#`-periodic with
--       `φ(y#)` hits per period) and `φ(y#)/y# = ∏_{p≤y}(1 − 1/p)` (Mathlib
--       `Nat.totient_mul_prod_primeFactors`, `Nat.totient_eq_prod_factorization`, with
--       `(y#).primeFactors = {p ≤ ⌊y⌋ prime}`).
/-- **`Δ(y)` is the density of integers coprime to `y#`** — unlabeled, EP1054.tex lines 323–330:
"For real `y, u ≥ 1`, set `\Delta(y):=\frac{\varphi(y\#)}{y\#}=\prod_{p\leq y}(1-\frac1p)` … Thus
`Δ(y)` is the natural density of integers coprime to `y#`." Used later as "complete periods modulo
`P#`" (e.g. lines 2123–2126, 2192–2196). Both identifications are stated: the product formula
(`Delta` in `Defs` is the product) equals `φ(y#)/y#`, and it is the natural density. -/
def Notation_Delta_density : Prop :=
  ∀ y : ℝ, 1 ≤ y →
    Delta y = ((primorialR y).totient : ℝ) / (primorialR y : ℝ) ∧
      HasDens {n : ℕ | Nat.Coprime n (primorialR y)} (Delta y)

-- deps: `sigmaPrefix 0 n = prefixSumDivisors n τ(n)` (definition) = sum of all divisors
--       (Basic: `prefixSumDivisors_eq_Fdiv` / `list_sum_eq_toFinset_sum`).
-- used by: Step_DaddCollisionFirstMomentLaw (S7: the `j = 0` term of `S4a.prefixMoment 3 n` is
--          `(σ(n)/n)³`, which is how lem:kovac-moment at `q = 3` bounds `∑ h(n)³`).
/-- **`σ₀ = σ`** — EP1054.tex line 346: "We interpret `σ_0` as `σ`." Here a consistency statement
about `Defs.sigmaPrefix` (the prefix sum of all but the `j` largest divisors), for `n ≥ 1`. -/
def Notation_sigmaPrefix_zero : Prop :=
  ∀ n : ℕ, 1 ≤ n → sigmaPrefix 0 n = sig n

end Principia.Erdos1054
