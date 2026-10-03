/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Defs
import Principia.Erdos1054.Statements.Inputs
import Principia.Erdos1054.Statements.S1_Main
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Dirac

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) §6 "Bounded representations and cofactor ranges" — statements only

Paper lines 2248–2725 of `Campaigns/Erdos-1054/collab-paper/EP1054.tex` (`\label{sec:tightness}`).
Every result is a `def … : Prop`; **nothing is asserted here**. Each `-- deps:` comment records
what the paper's proof of that statement consumes (paper results, by their Lean names in this or
the other `Statements` modules, and the named inputs of `Principia.Erdos1054.Statements.Inputs`).

## Two statements that are NOT claimed

* `Eq_T` (`eq:T`, line 2273) is a **question** the paper poses ("The associated density-one
  question is"), not a result.
* `Conj_BoundedCofactorWeak` (`conj:bounded-cofactor-weak`, line 2650) is a **conjecture**.

The paper *does* prove that each is equivalent to tightness of `{ν_X}`
(`Prop_TightnessEquivalence`, `Coverage.Rem_T_iff_Conj`); those equivalences are claimed.

## Contents, in paper order

* lines 2250–2268 — `rt`/`rtStar` (in `Defs`), `Coverage.Fact_RtPairs`, `Coverage.Fact_RtPosIff`,
  and tightness `Coverage.NuTight` of `ν_X` (`nuX`, from `S1_Main`);
* line 2273 — `Eq_T` (question);
* lines 2283–2441 — `Coverage.lamLower` (`λ_{Q,ρ}(A)`), `prop:class-first-moment`, and its proof
  displays `eq:h-gcd`, `eq:u-class`, `eq:He`, `eq:representing-ratio`, `eq:class-lower`, with the
  unlabeled proof steps (`Coverage.ClassCtx`, `Se`, `deltaE`, `He`, `Ge`; the mean-value chain
  `Step_HeRatio`, `Step_SeMultiplesDens`, `Disp_HeMean` — the one limit/sum interchange —
  `Disp_CoprimeSqTail`, `Step_GeLowerDens`; and `Step_DistinctPairs`);
* lines 2443–2470 — the prime-cofactor corollary (`%\label{cor:fm-prime-ceiling}`, commented out
  in the source) as `Cor_FmPrimeCeiling`;
* lines 2472–2536 — `G_A ⊆ {r_A > 0}`, the squarefree lead-in `Coverage.Rem_SqfreeDefectPos`
  (line 2486), the fixed-cofactor corollary with `eq:fixed-cofactor-defect`, `δ_A`, `η_A`, `P_A`,
  the coprime-part facts (`Step_KmodSmallPrime`, `Step_GcovValuesSmallPrime`,
  `Fact_GcovCoprimeNull`, `Fact_CoprimeComplementDens`), `eq:bounded-cofactor-complement`,
  `Coverage.Disp_LogPA`, `eq:delta-A-asymptotic`;
* lines 2537–2562 — the `η_A` proposition (`Prop_EtaALower`) and the remark that `η_A` dominates;
* lines 2564–2645 — `θ₂`, `prop:theta-two` with `eq:F2-aliquot`, `eq:F2-odd-negligible`,
  `eq:odd-untouchables`, `Coverage.Step_EvenUntouchables`, `Coverage.Disp_F2Count`, and the `η₂`
  corollary (`Cor_EtaTwo`);
* lines 2647–2670 — `conj:bounded-cofactor-weak` (conjecture) and the remarks that reformulate it;
* lines 2672–2722 — `prop:tightness-equivalence` with `eq:tightness-criterion`, its two proof
  inequalities, and the closing equivalence `eq:T ⟺ conjecture`.

## Encoding conventions

* **Cofactor bounds `A`, `E` of `G_A`, `P_A`, `δ_A`, `η_A` are natural numbers** (line 2474: "For a
  positive integer `A`"); `G_A` is `Defs.Gcov A`. "As `A → ∞`" is along `ℕ`. The threshold `t` of
  `r_t` is real (line 2251: "For `t > 0`"), so `eq:T` and `λ_{Q,ρ}(A)` take real `A`.
* `f` has the junk value `0` off `𝓡`, so every statement about `f` conjoins `N ∈ R`.
* Densities are `lowerDens`/`upperDens`/`HasDens`/`DensZero` of `Defs` (counting from `1`). They
  are Mathlib `liminf`/`limsup` of sequences in `[0, 1]`, hence the genuine values. The one
  unbounded-looking `liminf`, `λ_{Q,ρ}(A)`, is of a sequence bounded for fixed `A` (by
  `lem:moment`), so Mathlib's `liminf` is the genuine one there too; see `Coverage.lamLower`.
* `ν_X` is `nuX` of `S1_Main`, which this module imports (for `nuX` alone). Until 2026-09-25 a
  verbatim local copy `Coverage.nuX` stood in for it, because `S1_Main` was unbuilt.
* Section-local objects and unlabeled claims live in the sub-namespace `Coverage` (as
  `S5_UpperTails` does with `UpperTails`), so they cannot collide with other sections' names.
-/

namespace Principia.Erdos1054

open Finset Filter
open scoped Topology ENNReal

/-! ## The multiplicities `r_t`, `r_t^*` (lines 2250–2260)

`r_t(N)` and `r*_t(N)` are `Defs.rt` and `Defs.rtStar` (EP1054.tex lines 2253–2256):
```
 r_t(N)&=\#\{(e,d)\in\N^2:F_e(d)=N,\ ed\leq tN\},\\
 r_t^*(N)&=\#\{(e,d)\in\N^2:e\geq2,\ F_e(d)=N,\ ed\leq tN\}.
```
with `e, d ≥ 1` (the paper's `ℕ`); the boxes `Icc 1 ⌊tN⌋₊` are harmless since `ed ≤ tN` forces
`e, d ≤ ⌊tN⌋₊`. -/

open Classical in
-- deps: Basic divisor-prefix correspondence — `isRep_iff_exists_divisor`,
--       `prefixSumDivisors_eq_Fdiv`, `Fdiv_eq_prefixSumDivisors`, `F_eq_Fdiv`: the map
--       `(e, d) ↦ (e d, #{r ∣ e d : r > d})` is a bijection from `{(e, d) : e, d ≥ 1}` onto
--       `{(n, j) : n ≥ 1, j < τ(n)}` with `F e d = σ_j(e d)` (`σ_j` drops the `j` largest divisors).
/-- **`r_t(N)` counts the pairs `(n, j)`** — unlabeled, EP1054.tex lines 2257–2259:
"The second multiplicity counts proper divisor-prefix sums, excluding the full divisor sum.
Equivalently, `$r_t(N)$` counts the pairs `$(n,j)$` for which `$N=\sigma_j(n)$` and `$n\leq tN$`."

Encoding: for `t > 0` and `N ≥ 1` (line 2251: "For `$t>0$` and `$N\geq1$`"), `rt t N` equals the
number of `(n, j)` with `1 ≤ n ≤ ⌊tN⌋₊`, `j < τ(n)` and `sigmaPrefix j n = N`. The index box
`j < ⌊tN⌋₊` loses nothing: `j < τ(n) ≤ n ≤ ⌊tN⌋₊`. The conjunct `j < τ(n)` is automatic for
`N ≥ 1` (`σ_j(n) = 0` for `j ≥ τ(n)`) and is kept to match the paper's range of `σ_j`. -/
def Coverage.Fact_RtPairs : Prop :=
  ∀ t : ℝ, 0 < t → ∀ N : ℕ, 1 ≤ N →
    rt t N = (((Finset.Icc 1 ⌊t * N⌋₊) ×ˢ (Finset.range ⌊t * N⌋₊)).filter
      (fun q : ℕ × ℕ => q.2 < q.1.divisors.card ∧ sigmaPrefix q.2 q.1 = N)).card

-- deps: f_le_of_F (Basic) (a pair `(e, d)` with `F e d = N` gives `f N ≤ e d ≤ tN`);
--       f_mem_Fform (Basic) (`f N = e d` with `F e d = N`, `e, d ≥ 1`, then `e, d ≤ ⌊tN⌋₊`).
/-- **`r_t(N) > 0 ⟺ f(N) ≤ tN` on `𝓡`** — unlabeled, EP1054.tex lines 2259–2260:
"Thus, on the represented set `$\Rcal$`, one has `$r_t(N)>0$` if and only if `$f(N)\leq tN$`."

Encoding: `t > 0` real, `N ∈ R` (so `f N` is the genuine least representing integer); `f N ≤ tN`
is read in `ℝ`. Reused at lines 2719–2720 ("`r_A(N) > 0` is equivalent, apart from the two
unrepresented integers, to `f(N) ≤ AN`"). -/
def Coverage.Fact_RtPosIff : Prop :=
  ∀ t : ℝ, 0 < t → ∀ N : ℕ, N ∈ R → (0 < rt t N ↔ (f N : ℝ) ≤ t * N)

/-! ## The empirical measures and tightness (lines 2262–2268)

EP1054.tex line 2262: "Recall the empirical measures `$\nu_X$` and the normalization `$R(X)$` from
\eqref{eq:empirical-measures}. A mass at `$\infty$` in a compactified subsequential limit records
escape to infinity." The measures are `nuX` of `S1_Main` (`eq:empirical-measures`, line 222), on
the ambient space `[0, ∞] = ℝ≥0∞` (Borel): the paper's `(T, ∞]` (line 2267) and "compactified
subsequential limit" (line 2263) live there. Junk value `0` for `X < 1`. -/

namespace Coverage

/-- **Tightness of `{ν_X : X ≥ 1}` on the finite half-line** — the paper's own definition,
EP1054.tex lines 2264–2268: "Tightness on the finite half-line means
```
 \lim_{T\to\infty}\sup_{X\geq1}\nu_X((T,\infty])=0.
```"
Encoding: `(T, ∞]` is `Set.Ioi (ENNReal.ofReal T)` in `ℝ≥0∞`; the supremum is the `ℝ≥0∞`-valued
`⨆` over real `X ≥ 1` (always defined); the limit is `T → ∞` along `ℝ`. This is the sense of "form
a tight family on `[0,∞)`" in `prop:tightness-equivalence` (line 2676); it is *defined* by this
limit in the paper, not through compact sets, and is transcribed as such. -/
def NuTight : Prop :=
  Tendsto (fun T : ℝ => ⨆ (X : ℝ) (_ : 1 ≤ X), nuX X (Set.Ioi (ENNReal.ofReal T))) atTop (𝓝 0)

end Coverage

/-! ## The density-one question `eq:T` (lines 2270–2281) -/

-- deps: NONE — this is a QUESTION, not a result, and is never asserted. The paper proves only that
--       it is equivalent to Conj_BoundedCofactorWeak (Coverage.Rem_T_iff_Conj, lines 2719–2722).
/-- **`eq:T` — the density-one question. NOT CLAIMED** (it is open; the paper shows it equivalent
to the conjecture `Conj_BoundedCofactorWeak`). EP1054.tex lines 2270–2278: "The associated
density-one question is
```
 \lim_{A\to\infty}\limsup_{X\to\infty}
 \frac1X\#\{N\leq X:r_A(N)=0\}=0.
```
The order of the limits matters: `$A$` is fixed before `$X\to\infty$`."

Encoding: the inner `limsup_{X → ∞} (1/X) #{N ≤ X : r_A(N) = 0}` is `upperDens {N | rt A N = 0}`
(`N ≥ 1`; along the integers, equal to the limsup along the reals since the count depends only on
`⌊X⌋`); `A` is real (`r_t` has a real threshold) and tends to `∞` along `ℝ` only *after* the
`X`-limit, as the paper insists. `2, 5 ∉ 𝓡` have `r_A = 0` for every `A`; being finitely many,
they do not affect the density. -/
def Eq_T : Prop :=
  Tendsto (fun A : ℝ => upperDens {N : ℕ | rt A N = 0}) atTop (𝓝 0)

/-! ## A first moment in every residue class (lines 2283–2441) -/

namespace Coverage

/-- **The lower class mean** `\underline{\lambda}_{Q,\rho}(A)`, EP1054.tex lines 2285–2290: "For
fixed `$Q\geq1$` and `$\rho\pmod Q$`, put
```
 \underline{\lambda}_{Q,\rho}(A)
 =\liminf_{X\to\infty}\frac QX
 \sum_{\substack{N\leq X\\N\equiv\rho\pmod Q}}r_A(N).
```"
Encoding: the residue class is given by a natural representative `ρ` (`N % Q = ρ % Q`); `N` runs
over `1 ≤ N ≤ X`; `X → ∞` along `ℕ` (the summand depends on `⌊X⌋` only, and `X/⌊X⌋ → 1`); `A` is
real. **Mathlib-`liminf` caveat:** Mathlib's `liminf` of a real sequence is the genuine one when the
sequence is bounded. It is: for fixed `A`, `∑_{N ≤ X} r_A(N) ≤ X + C_k A^{k+1} X` (the pairs with
`e = 1` number `≤ X`; those with `e ≥ 2` are bounded by `eq:moment` with `E = 1`, since
`ed ≤ A F_e(d)` means `g_e(ed) ≥ 1/A`, which is `eq:reflection`). A proof of any statement about
`lamLower` therefore owes this boundedness (from `Lem_Moment` and `Eq_Reflection`), which is
true. -/
noncomputable def lamLower (Q ρ : ℕ) (A : ℝ) : ℝ :=
  liminf (fun X : ℕ => (Q : ℝ) / X *
    ∑ N ∈ (Finset.Icc 1 X).filter (fun N : ℕ => N % Q = ρ % Q), (rt A N : ℝ)) atTop

end Coverage

-- deps: Eq_ClassLower (applied with the `h` of Eq_HGcd); Coverage.Disp_MertensCoprimeQ
--       (from Std_Mertens3); Coverage.Disp_ClassPrimeSum (from Std_PNT_AP by partial summation,
--       Mathlib `sum_mul_eq_sub_integral_mul`); Lem_Moment (boundedness of the sequence in
--       `Coverage.lamLower`, so that Mathlib's `liminf` is the genuine one).
/-- **`prop:class-first-moment`, main bound**, EP1054.tex lines 2292–2299: "For every fixed
`$Q\geq1$` and every residue class `$\rho\pmod Q$`,
```
 \underline{\lambda}_{Q,\rho}(A)
 \gg_{Q,\rho}\frac{A}{(\log A)^2}
 \quad(A\to\infty).
```"
Encoding: `∀ Q ≥ 1, ∀ ρ, ∃ c > 0, ∃ A₀, ∀ A ≥ A₀` (`A` real), `c · A/(log A)² ≤ λ_{Q,ρ}(A)`; the
constant and the threshold depend on `(Q, ρ)` only (`≫_{Q,ρ}`), so they follow `Q, ρ` and precede
`A`. -/
def Prop_ClassFirstMoment_bound : Prop :=
  ∀ Q : ℕ, 1 ≤ Q → ∀ ρ : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A →
    c * (A / Real.log A ^ 2) ≤ Coverage.lamLower Q ρ A

-- deps: Prop_ClassFirstMoment_bound (`A/(log A)² → ∞`).
/-- **`prop:class-first-moment`, consequence**, EP1054.tex lines 2300–2301: "In particular, this
lower class mean tends to infinity in every residue class." -/
def Prop_ClassFirstMoment_tendsto : Prop :=
  ∀ Q : ℕ, 1 ≤ Q → ∀ ρ : ℕ, Tendsto (Coverage.lamLower Q ρ) atTop atTop

-- deps: Prop_ClassFirstMoment_bound, Prop_ClassFirstMoment_tendsto.
/-- **Proposition `prop:class-first-moment`**, EP1054.tex lines 2292–2302, the whole environment:
"For every fixed `$Q\geq1$` and every residue class `$\rho\pmod Q$`,
`$\underline{\lambda}_{Q,\rho}(A)\gg_{Q,\rho}\frac{A}{(\log A)^2}$` `$(A\to\infty)$`. In particular,
this lower class mean tends to infinity in every residue class."
The paper's Remark (lines 2436–2441) stresses that this counts representation *pairs* and does
**not** by itself imply `eq:T`; no implication to `Eq_T` is claimed. Reused with `Q = 1` at
line 2831 (`W(t) ≫ t/(log t)²`). -/
def Prop_ClassFirstMoment : Prop :=
  Prop_ClassFirstMoment_bound ∧ Prop_ClassFirstMoment_tendsto

-- deps: Dirichlet (Mathlib `Nat.forall_exists_prime_gt_and_modEq`) for distinct auxiliary primes
--       `q_ℓ ≡ 1` modulo every prime of `Q` (and `≡ 1 (mod 4)` for `ℓ = 2`); lifting the exponent
--       (Mathlib `padicValNat.pow_sub_pow`, `Nat.two_pow_sub_pow`) for `v_ℓ(σ(q^{ℓ^k−1})) = k`;
--       `σ(q^a) ≡ a + 1 (mod r)` for `q ≡ 1 (mod r)`; multiplicativity of `σ`
--       (`ArithmeticFunction.isMultiplicative_sigma`).
/-- **`eq:h-gcd`**, EP1054.tex lines 2305–2321: "Fix `$Q$` and `$\rho$`, and set
`$d_0=\gcd(\rho,Q)$`. We first choose a fixed integer `$h$` satisfying
```
 \gcd(\sigma(h),Q)=d_0.
```"
Encoding: the *existence* of such `h ≥ 1` for every `Q ≥ 1` and residue `ρ` (natural
representative; `gcd(ρ, Q)` depends only on `ρ mod Q`). The explicit construction
`h = ∏_{ℓ^k ∥ d₀} q_ℓ^{ℓ^k − 1}` (lines 2310–2318) is the proof. -/
def Eq_HGcd : Prop :=
  ∀ Q : ℕ, 1 ≤ Q → ∀ ρ : ℕ, ∃ h : ℕ, 1 ≤ h ∧ Nat.gcd (sig h) Q = Nat.gcd ρ Q

-- deps: none beyond elementary number theory — the solvability criterion for a linear congruence
--       (`a x ≡ b (mod Q)` is solvable iff `gcd(a, Q) ∣ b`), prime-power-wise division by the common
--       valuation, and the Chinese remainder theorem (Mathlib `Nat.chineseRemainder`) to glue units.
/-- **`eq:u-class`**, EP1054.tex lines 2323–2330: "The elementary criterion for a linear congruence
now gives a unit `$u_\rho\pmod Q$` for which
```
 \sigma(h)u_\rho\equiv\rho\pmod Q.
```
This includes the class `$\rho=0$`."
Encoding: for any `h` satisfying `eq:h-gcd` (the only property of `h` the step uses), there is
`u` coprime to `Q` with `σ(h) u ≡ ρ (mod Q)`. -/
def Eq_UClass : Prop :=
  ∀ Q : ℕ, 1 ≤ Q → ∀ ρ h : ℕ, Nat.gcd (sig h) Q = Nat.gcd ρ Q →
    ∃ u : ℕ, Nat.Coprime u Q ∧ sig h * u ≡ ρ [MOD Q]

namespace Coverage

/-- **The fixed context of the proof of `prop:class-first-moment`** (EP1054.tex lines 2304–2336):
`Q ≥ 1`; `h ≥ 1` with `gcd(σ(h), Q) = gcd(ρ, Q)` (`eq:h-gcd`); `u = u_ρ` a unit mod `Q` with
`σ(h) u ≡ ρ (mod Q)` (`eq:u-class`); and a prime `e` with "`$e>\max\{2,h,Q\}$`,
`$e\equiv-1\pmod Q$`" (lines 2332–2335). Every proof-local step below is stated under this whole
context, so no hypothesis the paper has in force is dropped. -/
def ClassCtx (Q ρ h u e : ℕ) : Prop :=
  1 ≤ Q ∧ 1 ≤ h ∧ Nat.gcd (sig h) Q = Nat.gcd ρ Q ∧ Nat.Coprime u Q ∧ sig h * u ≡ ρ [MOD Q] ∧
    e.Prime ∧ max (max 2 h) Q < e ∧ e % Q = (Q - 1) % Q

/-- `𝒮_e(u_ρ)`, EP1054.tex lines 2336–2340: "For each such prime `$e$`, define
`\[ \mathcal{S}_e(u_\rho)=\{t\geq1:t\equiv u_\rho\pmod Q,\ \gcd(t,e\#)=1\}. \]`"
`e#` is `primorialR e` (`= primorial e`). -/
def Se (Q u e : ℕ) : Set ℕ :=
  {t : ℕ | 1 ≤ t ∧ t % Q = u % Q ∧ Nat.Coprime t (primorialR e)}

/-- `δ_e`, EP1054.tex lines 2341–2345: "this periodic set has density
`\[ \delta_e=\frac1Q \prod_{\substack{p\leq e\\p\nmid Q}}\left(1-\frac1p\right). \]`" -/
noncomputable def deltaE (Q e : ℕ) : ℝ :=
  (1 / (Q : ℝ)) *
    ∏ p ∈ (Finset.range (e + 1)).filter (fun p : ℕ => p.Prime ∧ ¬ p ∣ Q), (1 - 1 / (p : ℝ))

/-- `H_e(t) = t + (e+1) s(t)`, EP1054.tex line 2352 (inside `eq:He`). The other form
`(e+1)σ(t) − et` is the second conjunct of `Eq_He`. `aliquot t = σ(t) − t` (no truncation,
`σ(t) ≥ t`). -/
def He (e t : ℕ) : ℕ := t + (e + 1) * aliquot t

/-- `𝒢_e`, EP1054.tex lines 2391–2393: "`\[ \mathcal{G}_e=\{t\in\mathcal{S}_e(u_\rho):H_e(t)\leq6t\} \]`". -/
def Ge (Q u e : ℕ) : Set ℕ := {t : ℕ | t ∈ Se Q u e ∧ He e t ≤ 6 * t}

end Coverage

-- deps: CRT (Mathlib `Nat.chineseRemainder`) and the density `φ(m)/m` of residues coprime to `m`
--       in a complete period modulo `Q · ∏_{p ≤ e, p ∤ Q} p` (`u` a unit, and every prime of `Q` is
--       `< e`, so the `p ∣ Q` coprimality is automatic).
/-- **Density of `𝒮_e(u_ρ)`** — unlabeled, EP1054.tex lines 2341–2346: "The Chinese
remainder theorem shows that this periodic set has density `$\delta_e$` … Every prime factor of
`$t\in\mathcal{S}_e(u_\rho)$` is larger than `$e$`."
Encoding: under the proof context `ClassCtx`, `HasDens (Se Q u e) (deltaE Q e)`, and every
`t ∈ Se Q u e` is `e`-rough (`IsRough e t`). -/
def Coverage.Step_SeDensity : Prop :=
  ∀ Q ρ h u e : ℕ, Coverage.ClassCtx Q ρ h u e →
    HasDens (Coverage.Se Q u e) (Coverage.deltaE Q e) ∧
      ∀ t ∈ Coverage.Se Q u e, IsRough (e : ℝ) t

-- deps: the divisor involution `r ↦ n/r` (as in Eq_Reflection / Eq_FmReflection:
--       `F_e(d) = σ(n) − n ∑_{j ∣ n, j < e} 1/j` for `n = e d`); `j ∣ e h t, j < e ⟹ j ∣ h`
--       (`t` is `e`-rough, `e` prime, `h < e`); `σ` multiplicative on the coprime `e, h, t`
--       (`ArithmeticFunction.isMultiplicative_sigma`), `σ(e) = e + 1`; Coverage.Step_SeDensity
--       (roughness of `t`).
/-- **`eq:He`**, EP1054.tex lines 2348–2353: "For `$t\in\mathcal{S}_e(u_\rho)$`, the divisors of
`$eht$` below `$e$` are exactly the divisors of `$h$`. Complementary divisors therefore give
```
 F_e(ht)=\sigma(h)H_e(t),
 \quad H_e(t)=(e+1)\sigma(t)-et=t+(e+1)s(t),
```
where `$s(t)=\sigma(t)-t$`."
Encoding: under `ClassCtx`, for `t ∈ 𝒮_e(u_ρ)`: `F e (h t) = σ(h) · He e t` with
`He e t = t + (e+1) s(t)`, and `He e t + e t = (e+1) σ(t)` (the form `(e+1)σ(t) − et`, written
additively to avoid truncated subtraction). -/
def Eq_He : Prop :=
  ∀ Q ρ h u e : ℕ, Coverage.ClassCtx Q ρ h u e → ∀ t ∈ Coverage.Se Q u e,
    F e (h * t) = sig h * Coverage.He e t ∧ Coverage.He e t + e * t = (e + 1) * sig t

-- deps: Eq_He (`H_e(t) = t + (e+1) s(t) ≡ t (mod Q)` since `Q ∣ e + 1`); `t ≡ u (mod Q)`;
--       eq:u-class (in Coverage.ClassCtx).
/-- **The represented value lies in the class `ρ`** — unlabeled, EP1054.tex lines 2354–2358:
"Since `$Q\mid e+1$`, equations \eqref{eq:u-class} and \eqref{eq:He} give
`\[ F_e(ht)\equiv\sigma(h)t\equiv\rho\pmod Q. \]`" -/
def Coverage.Step_ClassResidue : Prop :=
  ∀ Q ρ h u e : ℕ, Coverage.ClassCtx Q ρ h u e → ∀ t ∈ Coverage.Se Q u e,
    F e (h * t) ≡ sig h * t [MOD Q] ∧ F e (h * t) ≡ ρ [MOD Q]

-- deps: Eq_He (`F_e(ht) = σ(h) H_e(t)` and `H_e(t) ≥ t`); `σ(h) ≥ 1`.
/-- **`eq:representing-ratio`**, EP1054.tex lines 2359–2362: "The corresponding representing integer
is `$n=eht$`. Since `$H_e(t)\geq t$`,
```
 \frac{n}{F_e(ht)}\leq\frac{eh}{\sigma(h)}\leq eh.
```"
Encoding: under `ClassCtx`, for `t ∈ 𝒮_e(u_ρ)`; real division (`F_e(ht) ≥ ht ≥ 1`, `σ(h) ≥ 1`). -/
def Eq_RepresentingRatio : Prop :=
  ∀ Q ρ h u e : ℕ, Coverage.ClassCtx Q ρ h u e → ∀ t ∈ Coverage.Se Q u e,
    ((e * h * t : ℕ) : ℝ) / (F e (h * t) : ℝ) ≤ ((e * h : ℕ) : ℝ) / (sig h : ℝ) ∧
      ((e * h : ℕ) : ℝ) / (sig h : ℝ) ≤ ((e * h : ℕ) : ℝ)

namespace Coverage

/-- The summand of `∑_{a>1, gcd(a, e#)=1} a^{-2}` (EP1054.tex lines 2380, 2385), extended by `0`
to all of `ℕ` so that the sum is a `tsum` over `ℕ`. `e#` is `primorialR e` (`= primorial e`). -/
noncomputable def coprimeSq (e a : ℕ) : ℝ :=
  if 1 < a ∧ Nat.Coprime a (primorialR e) then 1 / (a : ℝ) ^ 2 else 0

/-- The summand of `∑_{a>e} a^{-2}` (EP1054.tex line 2386), extended by `0` to all of `ℕ`. -/
noncomputable def tailSq (e a : ℕ) : ℝ := if e < a then 1 / (a : ℝ) ^ 2 else 0

end Coverage

-- deps: Eq_He (`H_e(t) = t + (e+1) s(t)`); `σ(t)/t = ∑_{a ∣ t} 1/a` (complementary divisors
--       `r ↦ t/r`, Mathlib `Nat.sum_div_divisors` / `Nat.sum_divisors_eq_sum_properDivisors_add_self`).
/-- **`H_e(t)/t` as a divisor sum** — unlabeled proof display, EP1054.tex lines 2364–2368: "We next
bound the represented value. Complementary divisors give
```
 \frac{H_e(t)}t
 =1+(e+1)\sum_{\substack{a\mid t\\a>1}}\frac1a.
```"
Encoding: under `ClassCtx`, for `t ∈ 𝒮_e(u_ρ)` (so `t ≥ 1`), in `ℝ`. (The identity holds for every
`t ≥ 1`; it is stated in the paper's context.) -/
def Coverage.Step_HeRatio : Prop :=
  ∀ Q ρ h u e : ℕ, Coverage.ClassCtx Q ρ h u e → ∀ t ∈ Coverage.Se Q u e,
    (Coverage.He e t : ℝ) / t =
      1 + ((e : ℝ) + 1) * (∑ a ∈ t.divisors.filter (1 < ·), 1 / (a : ℝ))

-- deps: CRT (Mathlib `Nat.chineseRemainder`): `a` is coprime to `e#`, hence (every prime of `Q` is
--       `≤ Q < e`) to `Q`, so the conditions `a ∣ t`, `t ≡ u (mod Q)`, `gcd(t, e#) = 1` are
--       independent in a period `a Q ∏_{p ≤ e, p ∤ Q} p`; as in Coverage.Step_SeDensity.
/-- **Multiples of `a` in `𝒮_e(u_ρ)` have density `δ_e/a`** — unlabeled, EP1054.tex lines 2369–2371:
"For a fixed integer `$a>1$` with `$\gcd(a,e\#)=1$`, the Chinese remainder theorem shows that the
set of `$t\in\mathcal{S}_e(u_\rho)$` divisible by `$a$` has density `$\delta_e/a$`."
Encoding: under `ClassCtx`, for every natural `a > 1` coprime to `e#`. -/
def Coverage.Step_SeMultiplesDens : Prop :=
  ∀ Q ρ h u e : ℕ, Coverage.ClassCtx Q ρ h u e →
    ∀ a : ℕ, 1 < a → Nat.Coprime a (primorialR e) →
      HasDens {t : ℕ | t ∈ Coverage.Se Q u e ∧ a ∣ t} (Coverage.deltaE Q e / a)

open Classical in
-- deps: Coverage.Step_HeRatio (expand `H_e(t)/t`, swap the finite sums: `∑_{t ≤ T, t ∈ 𝒮_e} H_e(t)/t
--       = #(𝒮_e ∩ [1,T]) + (e+1) ∑_{a > 1} a^{-1} #{t ≤ T : t ∈ 𝒮_e, a ∣ t}`, only `a` coprime to
--       `e#` contributing); Coverage.Step_SeDensity (the term `1`); Coverage.Step_SeMultiplesDens
--       (each `a`); dominated interchange of `lim_T` and `∑_a` — the `a`-th term is
--       `≤ a^{-1} · (T/a)/T = a^{-2}`, summable (Mathlib `Real.summable_one_div_nat_pow`,
--       `tendsto_tsum_of_dominated_convergence`); Coverage.Disp_CoprimeSqTail (the final `≤ 3δ_e`,
--       via `δ_e (1 + 3/2) ≤ 3 δ_e`, `δ_e ≥ 0`).
/-- **The mean of `H_e(t)/t` over `𝒮_e(u_ρ)`** — unlabeled proof display, EP1054.tex lines
2372–2382: "Thus `$\sum_{a\geq1}a^{-2}<\infty$` justifies interchanging the limit and the divisor
sum. Therefore
```
 \lim_{T\to\infty}\frac1T
 \sum_{\substack{t\leq T\\t\in\mathcal{S}_e(u_\rho)}}\frac{H_e(t)}t
 &=\delta_e\bigg(1+(e+1)
 \sum_{\substack{a>1\\\gcd(a,e\#)=1}}\frac1{a^2}\bigg)\\
 &\leq3\delta_e.
```"
Encoding: under `ClassCtx`: (i) the series `∑_{a>1, gcd(a,e#)=1} a^{-2}` converges (`Summable`, so
the `tsum` below is its genuine value, not Mathlib's junk `0`); (ii) the limit exists and equals the
printed value, `T → ∞` along `ℕ` (the sum depends on `⌊T⌋` only and `T/⌊T⌋ → 1`); (iii) that value
is `≤ 3δ_e`. This is the one limit/sum interchange in the proof of `prop:class-first-moment`. -/
def Coverage.Disp_HeMean : Prop :=
  ∀ Q ρ h u e : ℕ, Coverage.ClassCtx Q ρ h u e →
    Summable (Coverage.coprimeSq e) ∧
      Tendsto (fun T : ℕ => (1 / (T : ℝ)) *
          ∑ t ∈ (Finset.Icc 1 T).filter (· ∈ Coverage.Se Q u e), (Coverage.He e t : ℝ) / t)
        atTop
        (𝓝 (Coverage.deltaE Q e * (1 + ((e : ℝ) + 1) * (∑' a : ℕ, Coverage.coprimeSq e a)))) ∧
      Coverage.deltaE Q e * (1 + ((e : ℝ) + 1) * (∑' a : ℕ, Coverage.coprimeSq e a)) ≤
        3 * Coverage.deltaE Q e

-- deps: a prime factor of `a > 1` coprime to `e#` exceeds `e`, so `a > e` (Mathlib
--       `Nat.Prime.dvd_primorial_iff`: `p ∣ e# ↔ p ≤ e`; `Nat.minFac`); termwise comparison of nonnegative
--       summable series (`Summable.tsum_le_tsum`); `∑_{a > e} a^{-2} ≤ ∑_{a > e} 1/(a(a−1)) = 1/e`
--       (telescoping); `e ≥ 3` (`e > max{2,h,Q}` in Coverage.ClassCtx) for `(e+1)/e ≤ 3/2`.
/-- **The tail bound `(e+1) ∑ a^{-2} ≤ 3/2`** — unlabeled proof display, EP1054.tex lines
2383–2389: "Every integer `$a>1$` coprime to `$e\#$` exceeds `$e$`. Hence
```
 (e+1)\sum_{\substack{a>1\\\gcd(a,e\#)=1}}\frac1{a^2}
 \leq(e+1)\sum_{a>e}\frac1{a^2}
 \leq\frac{e+1}{e}\leq\frac32,
```
which proves the last inequality."
Encoding: under `ClassCtx`, the sentence and the three printed inequalities as four conjuncts; the
sums are `tsum`s of `Coverage.coprimeSq e` and `Coverage.tailSq e` (both summable; summability of
the first is part of `Coverage.Disp_HeMean`). -/
def Coverage.Disp_CoprimeSqTail : Prop :=
  ∀ Q ρ h u e : ℕ, Coverage.ClassCtx Q ρ h u e →
    (∀ a : ℕ, 1 < a → Nat.Coprime a (primorialR e) → e < a) ∧
      ((e : ℝ) + 1) * (∑' a : ℕ, Coverage.coprimeSq e a) ≤
        ((e : ℝ) + 1) * (∑' a : ℕ, Coverage.tailSq e a) ∧
      ((e : ℝ) + 1) * (∑' a : ℕ, Coverage.tailSq e a) ≤ ((e : ℝ) + 1) / e ∧
      ((e : ℝ) + 1) / e ≤ 3 / 2

-- deps: Coverage.Step_SeDensity (`𝒮_e` has density `δ_e`); Coverage.Disp_HeMean (mean of
--       `H_e(t)/t` is `≤ 3δ_e`); Markov's inequality (`#{t ≤ T : t ∈ 𝒮_e, H_e(t) > 6t} ≤
--       (1/6) ∑_{t ≤ T, t ∈ 𝒮_e} H_e(t)/t`, so `𝒮_e ∖ 𝒢_e` has upper density `≤ δ_e/2`).
/-- **Markov step: `𝒢_e` has lower density `≥ δ_e/2`** — unlabeled, EP1054.tex lines 2389–2394:
"Markov's inequality shows that
`\[ \mathcal{G}_e=\{t\in\mathcal{S}_e(u_\rho):H_e(t)\leq6t\} \]` has lower density at least
`$\delta_e/2$`." (The mean-value display it applies to, lines 2376–2382, is `Coverage.Disp_HeMean`.)
Encoding: under `ClassCtx`, `δ_e/2 ≤ lowerDens 𝒢_e`. -/
def Coverage.Step_GeLowerDens : Prop :=
  ∀ Q ρ h u e : ℕ, Coverage.ClassCtx Q ρ h u e →
    Coverage.deltaE Q e / 2 ≤ lowerDens (Coverage.Ge Q u e)

-- deps: `e ∣ e' h t'` with `e < e'` prime and `h < e` forces `e ∣ t'` (Mathlib
--       `Nat.Prime.dvd_mul`); `t' ∈ 𝒮_{e'}` is coprime to `e'#` and `e ∣ e'#`
--       (`Nat.Prime.dvd_primorial_iff`), contradiction; for `e = e'` cancel `e h ≥ 1`
--       (`Nat.eq_of_mul_eq_mul_left`).
/-- **Distinct pairs `(e, t)` give distinct representing integers** — unlabeled, EP1054.tex lines
2403–2406: "Distinct pairs `$(e,t)$` give distinct representing integers. Indeed, if `$e<e'$` and
`$eht=e'ht'$`, then `$e\mid t'$`, contrary to the fact that every prime factor of `$t'$` exceeds
`$e'$`. If `$e=e'$`, equality of the representing integers forces `$t=t'$`."
Encoding: for two eligible primes `e, e'` sharing the context `(Q, ρ, h, u)` (each under `ClassCtx`,
as in the paper's sum over `e`), `t ∈ 𝒮_e(u_ρ)`, `t' ∈ 𝒮_{e'}(u_ρ)`: `e h t = e' h t'` forces
`e = e'` and `t = t'`. (The bound `e ≤ A/h` is not used.) -/
def Coverage.Step_DistinctPairs : Prop :=
  ∀ Q ρ h u e e' t t' : ℕ, Coverage.ClassCtx Q ρ h u e → Coverage.ClassCtx Q ρ h u e' →
    t ∈ Coverage.Se Q u e → t' ∈ Coverage.Se Q u e' → e * h * t = e' * h * t' →
      e = e' ∧ t = t'

-- deps: Eq_HGcd/Eq_UClass (via the hypotheses; `u` from Eq_UClass); Dirichlet
--       (`Nat.forall_exists_prime_gt_and_modEq`) only for non-emptiness; for each eligible prime
--       `e`: Coverage.Step_GeLowerDens, Eq_He, Coverage.Step_ClassResidue,
--       Eq_RepresentingRatio (the pair `(e, h t)` is counted by `r_A(F_e(ht))` since
--       `e h t ≤ e h F_e(ht)/σ(h) ≤ A F_e(ht)` when `e ≤ A/h`); `F_e(ht) ≤ X` when
--       `t ≤ X/(6σ(h))` and `t ∈ 𝒢_e`; Coverage.Step_DistinctPairs (distinct `(e, t)` give
--       distinct representing integers, hence distinct counted pairs); finite
--       sum of liminfs ≤ liminf of the sum; Lem_Moment with Eq_Reflection (boundedness, see
--       Coverage.lamLower: the bound counts witnessing pairs, so it is eq:moment plus reflection,
--       not eq:large-count, which counts distinct `N`).
/-- **`eq:class-lower`**, EP1054.tex lines 2396–2417: "For a fixed `$A$`, restrict to primes `$e$`
satisfying `$\max\{2,h,Q\}<e\leq A/h$`, `$e\equiv-1\pmod Q$`. … Multiplying by `$Q/X$` and summing
over `$e$` gives
```
 \underline{\lambda}_{Q,\rho}(A)
 \geq\frac1{12\sigma(h)}
 \sum_{\substack{\max\{2,h,Q\}<e\leq A/h\\
 e\text{ prime}\\e\equiv-1\pmod Q}}
 \prod_{\substack{p\leq e\\p\nmid Q}}\left(1-\frac1p\right).
```"
Encoding: for every `Q ≥ 1`, residue `ρ`, and `h ≥ 1` satisfying `eq:h-gcd` (the proof uses no
other property of `h`), and every real `A > 0`. `e ≤ A/h` is `e ≤ ⌊A/h⌋₊` (`A/h > 0`);
`e ≡ −1 (mod Q)` is `e % Q = (Q − 1) % Q` (vacuous for `Q = 1`). If no prime is eligible the sum is
`0`. -/
def Eq_ClassLower : Prop :=
  ∀ Q : ℕ, 1 ≤ Q → ∀ ρ h : ℕ, 1 ≤ h → Nat.gcd (sig h) Q = Nat.gcd ρ Q → ∀ A : ℝ, 0 < A →
    1 / (12 * (sig h : ℝ)) *
        ∑ e ∈ (Finset.range (⌊A / h⌋₊ + 1)).filter
            (fun e : ℕ => e.Prime ∧ max (max 2 h) Q < e ∧ e % Q = (Q - 1) % Q),
          ∏ p ∈ (Finset.range (e + 1)).filter (fun p : ℕ => p.Prime ∧ ¬ p ∣ Q),
            (1 - 1 / (p : ℝ))
      ≤ Coverage.lamLower Q ρ A

-- deps: Std_Mertens3 (`Δ(y) log y → e^{−γ}`) and finite algebra: `∏_{p ≤ y, p ∤ Q}(1 − 1/p)
--       = Δ(y) ∏_{p ∣ Q}(1 − 1/p)^{−1}` for `y ≥ Q`, and `∏_{p ∣ Q}(1 − 1/p) = φ(Q)/Q`
--       (Mathlib `Nat.totient_mul_prod_primeFactors`).
/-- **Mertens' product with `p ∤ Q` removed** — unlabeled proof display, EP1054.tex lines
2418–2423: "Mertens' product theorem gives
```
 \prod_{\substack{p\leq e\\p\nmid Q}}
 \left(1-\frac1p\right)
 \sim\frac Q{\varphi(Q)}\frac{e^{-\gamma}}{\log e}.
```"
Encoding: for every fixed `Q ≥ 1`, `(∏_{p ≤ y, p ∤ Q}(1 − 1/p)) · log y → (Q/φ(Q)) e^{−γ}` as the
real `y → ∞` (the paper applies it at primes `e`, a subsequence). -/
def Coverage.Disp_MertensCoprimeQ : Prop :=
  ∀ Q : ℕ, 1 ≤ Q →
    Tendsto (fun y : ℝ =>
        (∏ p ∈ (Finset.Iic ⌊y⌋₊).filter (fun p : ℕ => p.Prime ∧ ¬ p ∣ Q), (1 - 1 / (p : ℝ))) *
          Real.log y)
      atTop (𝓝 ((Q : ℝ) / (Q.totient : ℝ) * Real.exp (-eulerGamma)))

-- deps: Std_PNT_AP (class `−1`, fixed modulus) and partial summation (Mathlib
--       `sum_mul_eq_sub_integral_mul`, `AbelSummation`).
/-- **The prime sum in the class `−1`** — unlabeled proof display, EP1054.tex lines 2424–2430:
"For `$Z\geq2$`, the prime number theorem in arithmetic progressions, followed by partial
summation, gives, as `$Z\to\infty$`,
```
 \sum_{\substack{e\leq Z\\e\text{ prime}\\e\equiv-1\pmod Q}}
 \frac1{\log e}
 \sim\frac{Z}{\varphi(Q)(\log Z)^2}.
```"
Encoding: for every fixed `Q ≥ 1`, the ratio of the two sides tends to `1` as the real `Z → ∞`. -/
def Coverage.Disp_ClassPrimeSum : Prop :=
  ∀ Q : ℕ, 1 ≤ Q →
    Tendsto (fun Z : ℝ =>
        (∑ e ∈ (Finset.Iic ⌊Z⌋₊).filter (fun e : ℕ => e.Prime ∧ e % Q = (Q - 1) % Q),
            1 / Real.log e) /
          (Z / ((Q.totient : ℝ) * Real.log Z ^ 2)))
      atTop (𝓝 1)

/-! ## Prime cofactor ranges (lines 2443–2470) -/

-- deps: Lem_FmModulus (Eq_FmCongruence at `e = p`), with `p ∣ Kmod p d`: every `j ∈ Dset p d` is
--       `< p`, so `p ∤ Mlcm p d`, `gcd(p, M) = 1` and `p ∣ (p/1) C = K_{p,d}`
--       (`Nat.ModEq.of_dvd`).
/-- **Prime-cofactor corollary, congruence** (`%\label{cor:fm-prime-ceiling}`, commented out in the
source), EP1054.tex lines 2448–2450: "Let `$p$` be prime. Then `$F_p(d)\equiv\sigma(pd)\pmod p$` for
every `$d\geq1$`". -/
def Cor_FmPrimeCeiling_congr : Prop :=
  ∀ p : ℕ, p.Prime → ∀ d : ℕ, 1 ≤ d → F p d ≡ sig (p * d) [MOD p]

-- deps: Cor_FmPrimeCeiling_congr; Disp_FinalDivisor (`d ≤ F_p(d)`, so `p d ≤ p N ≤ p X`);
--       `(p, d)` determines `N = F_p(d)` (distinct `N` have distinct sources `p d`);
--       Lem_FixedModulusNormality at `V = p` (`#{n ≤ pX : p ∤ σ(n)} = o_p(X)`); the multiples of
--       `p` up to `X` number `≤ X/p`.
/-- **Prime-cofactor corollary, count**, EP1054.tex lines 2451–2454:
```
 \#\bigl(F_p(\N)\cap[1,X]\bigr)\leq\frac Xp+o_p(X)
```
Encoding: `F_p(ℕ)` is `Defs.Frange p`; `o_p(X)` is `∀ ε > 0, ∃ X₀, ∀ X ≥ X₀` (all depending on the
fixed `p`, line 2470: "the error term `$o_p(X)$` is asserted only with `$p$` fixed"), real `X`. -/
def Cor_FmPrimeCeiling_count : Prop :=
  ∀ p : ℕ, p.Prime → ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    (cnt (Frange p) X : ℝ) ≤ X / p + ε * X

-- deps: Cor_FmPrimeCeiling_count (divide by `X`, take `limsup`).
/-- **Prime-cofactor corollary, density**, EP1054.tex line 2455:
"so `\[ \upperdens\bigl(F_p(\N)\bigr)\leq\frac1p . \]`" -/
def Cor_FmPrimeCeiling_upperDens : Prop :=
  ∀ p : ℕ, p.Prime → upperDens (Frange p) ≤ 1 / p

-- deps: Cor_FmPrimeCeiling_congr, Cor_FmPrimeCeiling_count, Cor_FmPrimeCeiling_upperDens.
/-- **Corollary (prime cofactor ceiling)**, EP1054.tex lines 2448–2457 (label
`cor:fm-prime-ceiling` commented out in the source), the whole environment:
"Let `$p$` be prime. Then `$F_p(d)\equiv\sigma(pd)\pmod p$` for every `$d\geq1$`, and
`\[ \#\bigl(F_p(\N)\cap[1,X]\bigr)\leq\frac Xp+o_p(X), \quad\text{so}\quad
\upperdens\bigl(F_p(\N)\bigr)\leq\frac1p . \]`" -/
def Cor_FmPrimeCeiling : Prop :=
  Cor_FmPrimeCeiling_congr ∧ Cor_FmPrimeCeiling_count ∧ Cor_FmPrimeCeiling_upperDens

/-! ## Bounded cofactors (lines 2472–2536) -/

-- deps: Disp_FinalDivisor / F_ge (Basic) (`F_e(d) ≥ d`, so `ed ≤ A d ≤ A F_e(d)` for `e ≤ A`).
/-- **`G_A ⊆ {N : r_A(N) > 0}`** — unlabeled, EP1054.tex lines 2479–2484: "Every `$N=F_e(d)$` with
`$e\leq A$` has a representing integer `$n=ed\leq AN$`, because `$F_e(d)\geq d$`. Thus
`\[ G_A\subseteq\{N:r_A(N)>0\}. \]`"
Encoding: `A` a positive integer (line 2474), `G_A = Gcov A`, `r_A = rt (A : ℝ)`. -/
def Coverage.Fact_GcovSubsetRtPos : Prop :=
  ∀ A : ℕ, 1 ≤ A → Gcov A ⊆ {N : ℕ | 0 < rt (A : ℝ) N}

-- deps: Eq_AlmostLogTail (S1, thm:almost-log-tail) at ONE fixed `T ≥ A` large enough that its
--       right-hand side `(e^{−γ}/2 − ε) L(T)` is positive (proof, lines 2504–2505); the inclusion
--       `{N ∈ 𝓡 : N squarefree, f(N) > TN} ⊆ {N : N squarefree, N ∉ G_T} ⊆ {N squarefree, N ∉ G_A}`
--       (f_le_of_F + F_ge (Basic): `N = F_e(d)`, `e ≤ T` ⟹ `f(N) ≤ ed ≤ TN`; `G_A ⊆ G_T`);
--       monotonicity of `lowerDens`.
/-- **Every fixed `G_A` misses a positive-density set of squarefree integers** — unlabeled lead-in
sentence, EP1054.tex line 2486: "The upper-tail estimate shows that every fixed union of cofactor
ranges misses a positive-density set, even among squarefree targets."
Encoding: for every positive integer `A`, `0 < lowerDens {N : N squarefree, N ∉ G_A}`. "Positive
density" is read as positive *lower* density, the sense of the corollary it introduces and the
sense the proof delivers (Theorem `thm:almost-log-tail` bounds a lower density). "Every fixed union
of cofactor ranges" is encoded through `G_A = ⋃_{e ≤ A} F_e(ℕ)`; any finite union of ranges lies in
some `G_A`, so the general form follows by monotonicity. For fixed `A` this is strictly more than
`Cor_FixedCofactorDefect_pos` (which drops "squarefree") and is not implied by
`Eq_FixedCofactorDefect` (which is asymptotic in `A`). -/
def Coverage.Rem_SqfreeDefectPos : Prop :=
  ∀ A : ℕ, 1 ≤ A → 0 < lowerDens {N : ℕ | Squarefree N ∧ N ∉ Gcov A}

-- deps: Eq_AlmostLogTail (S1, thm:almost-log-tail) at `T = A'` for a fixed large `A' ≥ A` with a
--       positive right-hand side; f_le_of_F + F_ge (Basic) (`N ∈ 𝓡`, `f(N) > A'N` ⟹
--       `N ∉ G_{A'} ⊇ G_A`); monotonicity of `lowerDens`. (Equivalently: Coverage.Rem_SqfreeDefectPos,
--       then drop "squarefree" by monotonicity — the same argument.)
/-- **Fixed-cofactor corollary, first assertion** (unlabeled corollary, EP1054.tex lines
2488–2491): "For every fixed `$A\geq1$`, `\[ \lowerdens(\N\setminus G_A)>0. \]`"
Encoding: `A : ℕ`, `A ≥ 1`; `ℕ ∖ G_A` is `{N | N ∉ Gcov A}` (counted from `1`). -/
def Cor_FixedCofactorDefect_pos : Prop :=
  ∀ A : ℕ, 1 ≤ A → 0 < lowerDens {N : ℕ | N ∉ Gcov A}

-- deps: Eq_AlmostLogTail (S1) with `T = A`; the inclusion
--       `{N ∈ 𝓡 : N squarefree, f(N) > AN} ⊆ {N : N squarefree, N ∉ G_A}` (f_le_of_F,
--       F_ge (Basic): `N = F_e(d)`, `e ≤ A` ⟹ `f(N) ≤ ed ≤ AN`); monotonicity of `lowerDens`.
/-- **`eq:fixed-cofactor-defect`** (inside the unlabeled fixed-cofactor corollary), EP1054.tex
lines 2492–2498: "More precisely, as `$A\to\infty$`,
```
 \lowerdens\{N:N\text{ squarefree},\ N\notin G_A\}
 \geq\left(\frac{e^{-\gamma}}2-o(1)\right)
 \frac{\log\log\log A}{(\log A)(\log\log A)}.
```"
Encoding: `o(1)` is `∀ ε > 0, ∃ A₀, ∀ A ≥ A₀` (`A : ℕ`, the positive integer of `G_A`); the scale
is `Defs.Lscale A = log₃ A/(log A · log₂ A)`; the set does **not** conjoin `N ∈ 𝓡` (as printed). -/
def Eq_FixedCofactorDefect : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A₀ : ℕ, ∀ A : ℕ, A₀ ≤ A →
    (Real.exp (-eulerGamma) / 2 - ε) * Lscale A ≤
      lowerDens {N : ℕ | Squarefree N ∧ N ∉ Gcov A}

-- deps: Cor_FixedCofactorDefect_pos, Eq_FixedCofactorDefect.
/-- **Fixed-cofactor corollary** (unlabeled), EP1054.tex lines 2488–2499, the whole environment:
"For every fixed `$A\geq1$`, `$\lowerdens(\N\setminus G_A)>0$`. More precisely, as `$A\to\infty$`,
\eqref{eq:fixed-cofactor-defect}." -/
def Cor_FixedCofactorDefect : Prop :=
  Cor_FixedCofactorDefect_pos ∧ Eq_FixedCofactorDefect

namespace Coverage

/-- `P_A = A Λ(A)`, EP1054.tex line 2477: "`$\Lambda(A)=\lcm(1,\ldots,A),\quad P_A=A\Lambda(A)$`"
(`Λ` is `Defs.lcmUpTo`; for `A : ℕ`, `lcmUpTo A = lcm(1, …, A)`). -/
noncomputable def PA (A : ℕ) : ℕ := A * lcmUpTo A

/-- `δ_A = Δ(P_A)`, EP1054.tex line 2510. -/
noncomputable def deltaA (A : ℕ) : ℝ := Delta (PA A)

/-- `η_A = \upperdens\{N:\gcd(N,P_A\#)>1,\ N\notin G_A\}`, EP1054.tex line 2511.
`P_A#` is `primorialR (PA A)`. -/
noncomputable def etaA (A : ℕ) : ℝ :=
  upperDens {N : ℕ | 1 < Nat.gcd N (primorialR (PA A)) ∧ N ∉ Gcov A}

end Coverage

-- deps: Fact_KmodGeTwo (S2: `e/g = 1 ⟹ C ≥ M ≥ e ≥ 2`); `e/g ∣ K_{e,d}` (definition of Kmod);
--       `C = ∑_{j ∈ D} M/j ≤ #D · M ≤ (e−1) M`; `M = lcm(D) ∣ Λ(e−1) ∣ Λ(A)`, so
--       `(e−1) M ≤ A Λ(A)`; any prime factor of `e/g > 1` is `≤ e ≤ A ≤ P_A`.
/-- **Every forced modulus has a prime factor `≤ P_A`** — unlabeled, EP1054.tex lines 2513–2516:
"For `$2\leq e\leq A$`, every forced modulus `$K_{e,d}$` has a prime factor at most `$P_A$`. Indeed,
if `$e/g>1$`, use a prime factor of `$e/g$`; otherwise `$K_{e,d}=C$`, where
`$2\leq C\leq(e-1)M\leq P_A$`."
Encoding: `g = Nat.gcd e (Mlcm e d)`; the chain for the case `e/g = 1` is recorded as a second
conjunct (with `2 ≤ C` from `Fact_KmodGeTwo`). -/
def Coverage.Step_KmodSmallPrime : Prop :=
  ∀ A e d : ℕ, 2 ≤ e → e ≤ A → 1 ≤ d →
    (∃ p : ℕ, p.Prime ∧ p ∣ Kmod e d ∧ p ≤ Coverage.PA A) ∧
      (e / Nat.gcd e (Mlcm e d) = 1 →
        Kmod e d = Csum e d ∧ 2 ≤ Csum e d ∧ Csum e d ≤ (e - 1) * Mlcm e d ∧
          (e - 1) * Mlcm e d ≤ Coverage.PA A)

-- deps: Coverage.Step_KmodSmallPrime; Fact_KmodFinite (S2: finitely many moduli for `e ≤ A`);
--       Lem_FmModulus (Eq_FmCongruence: `N = F_e(d) ≡ σ(ed) (mod K_{e,d})`); for `N` with no prime
--       factor `≤ P_A`, the prime `p ∣ K_{e,d}` with `p ≤ P_A` does not divide `N`, hence
--       `p ∤ σ(ed)` and `K_{e,d} ∤ σ(ed)`; Lem_FixedModulusNormality (at the lcm of the finitely
--       many moduli; sources `ed ≤ AX` since `d ≤ F_e(d)`, F_ge (Basic); each source `n` yields at
--       most `A` values `F_e(n/e)`, one per `e ≤ A`).
/-- **All but `o_A(X)` values of `F_e`, `2 ≤ e ≤ A`, have a prime factor `≤ P_A`** — unlabeled,
EP1054.tex lines 2516–2519: "There are only finitely many such moduli. Lemma \ref{lem:fm-modulus}
and fixed-modulus normality therefore imply that all but `$o_A(X)$` values `$F_e(d)\leq X$` have a
prime factor at most `$P_A$`: their sources satisfy `$ed\leq AX$`, and a fixed source contributes at
most `$A$` values."
Encoding: `e` ranges over `2 ≤ e ≤ A` (the range of the preceding sentence, line 2513; `e = 1` is
the separate case of line 2520); "values `F_e(d) ≤ X`" are counted as integers `N ≤ X` (a set, not
pairs); "has no prime factor at most `P_A`" is `IsRough P_A N`. `o_A(X)` is `DensZero` for each
fixed `A ≥ 1`. (`N = 1 = F_e(1)` is rough; a single element does not affect the density.) -/
def Coverage.Step_GcovValuesSmallPrime : Prop :=
  ∀ A : ℕ, 1 ≤ A →
    DensZero {N : ℕ | (∃ e d : ℕ, 2 ≤ e ∧ e ≤ A ∧ 1 ≤ d ∧ N = F e d) ∧
      IsRough (Coverage.PA A : ℝ) N}

-- deps: Coverage.Step_GcovValuesSmallPrime (cofactors `2 ≤ e ≤ A`; `N` coprime to `P_A#` has no
--       prime factor `≤ P_A`, Mathlib `Nat.Prime.dvd_primorial_iff`); Lem_SigmaRangeZero (the case
--       `e = 1`, `F_1(d) = σ(d)`); a union of two density-zero sets has density zero.
/-- **`G_A` is null among integers coprime to `P_A#`** — unlabeled display, EP1054.tex lines
2516–2523: "… all but `$o_A(X)$` values `$F_e(d)\leq X$` have a prime factor at most `$P_A$` … The
case `$e=1$` is covered by Lemma \ref{lem:sigma-range-zero}. Hence
```
 \#\{N\leq X:\gcd(N,P_A\#)=1,\ N\in G_A\}=o_A(X).
```"
Encoding: `A ≥ 1` a positive integer; `o_A(X)` is `DensZero` of the set, for each fixed `A`. -/
def Coverage.Fact_GcovCoprimeNull : Prop :=
  ∀ A : ℕ, 1 ≤ A →
    DensZero {N : ℕ | Nat.Coprime N (primorialR (Coverage.PA A)) ∧ N ∈ Gcov A}

-- deps: Coverage.Fact_GcovCoprimeNull; Notation_Delta_density (S1: `Δ(y)` is the density of
--       integers coprime to `y#`); density of a set difference with a null set.
/-- **The coprime part of `ℕ ∖ G_A` has density `δ_A`** — unlabeled, EP1054.tex lines 2524–2526:
"Thus `$G_A$` has density zero among the integers coprime to `$P_A\#$`. Hence the coprime part of
`$\N\setminus G_A$` has density `$\delta_A$`." -/
def Coverage.Fact_CoprimeComplementDens : Prop :=
  ∀ A : ℕ, 1 ≤ A →
    HasDens {N : ℕ | Nat.Coprime N (primorialR (Coverage.PA A)) ∧ N ∉ Gcov A}
      (Coverage.deltaA A)

-- deps: Coverage.Fact_CoprimeComplementDens; Coverage.Fact_UpperDensCompl
--       (`1 − lowerDens(G_A) = upperDens(ℕ ∖ G_A)`); `upperDens (S ∪ S') = d + upperDens S'` for
--       disjoint `S` having density `d` (the coprime and non-coprime parts).
/-- **`eq:bounded-cofactor-complement`**, EP1054.tex lines 2526–2529: "Since the coprime and
noncoprime parts are disjoint,
```
 1-\lowerdens(G_A)=\delta_A+\eta_A.
```"
Encoding: for every positive integer `A`. -/
def Eq_BoundedCofactorComplement : Prop :=
  ∀ A : ℕ, 1 ≤ A → 1 - lowerDens (Gcov A) = Coverage.deltaA A + Coverage.etaA A

-- deps: Std_PNT (`ψ(x)/x → 1`); Mathlib `Chebyshev.psi_eq_log_lcmUpto` (`ψ n = log (lcmUpto n)`;
--       `Defs.lcmUpTo A` has the body of `Nat.lcmUpto A`); `Real.log_mul` (`A, Λ(A) ≥ 1`);
--       `log A = o(A)` (Mathlib `Real.isLittleO_log_id_atTop`).
/-- **`log P_A = log A + ψ(A) = A + o(A)`** — unlabeled proof display, EP1054.tex lines 2530–2532:
"Moreover, Mertens' theorem and the prime number theorem, in the form `$\psi(A)=A+o(A)$`, give
`$\log P_A=\log A+\psi(A)=A+o(A)$`".
Encoding: (i) the identity `log P_A = log A + ψ(A)` for every positive integer `A` (`ψ` is Mathlib's
`Chebyshev.psi`, the paper's `ψ`); (ii) `(log P_A − A)/A → 0` as `A → ∞` through `ℕ` (the `o(A)`).
This is the step that feeds Mertens' theorem into `Eq_DeltaAAsymptotic`. -/
def Coverage.Disp_LogPA : Prop :=
  (∀ A : ℕ, 1 ≤ A → Real.log (Coverage.PA A) = Real.log A + Chebyshev.psi A) ∧
    Tendsto (fun A : ℕ => (Real.log (Coverage.PA A) - A) / A) atTop (𝓝 0)

-- deps: Std_Mertens3 (`Δ(y) log y → e^{−γ}`, applied at `y = P_A → ∞`); Coverage.Disp_LogPA
--       (`log P_A = A + o(A)`, so `log P_A / A → 1` and `P_A → ∞`).
/-- **`eq:delta-A-asymptotic`**, EP1054.tex lines 2530–2535: "Moreover, Mertens' theorem and the
prime number theorem, in the form `$\psi(A)=A+o(A)$`, give `$\log P_A=\log A+\psi(A)=A+o(A)$` and
hence
```
 \delta_A=\frac{e^{-\gamma}+o(1)}A.
```"
Encoding: `A δ_A → e^{−γ}` as `A → ∞` through the positive integers (equivalent to the display). -/
def Eq_DeltaAAsymptotic : Prop :=
  Tendsto (fun A : ℕ => (A : ℝ) * Coverage.deltaA A) atTop (𝓝 (Real.exp (-eulerGamma)))

/-! ## `η_A` dominates (lines 2537–2562) -/

-- deps: Eq_FixedCofactorDefect (and `lowerDens {sqfree, ∉ G_A} ≤ lowerDens (ℕ ∖ G_A) ≤
--       upperDens (ℕ ∖ G_A) = 1 − lowerDens(G_A)`, Coverage.Fact_UpperDensCompl);
--       Eq_DeltaAAsymptotic with `A L(A) → ∞` (so `δ_A = o(L(A))`);
--       Eq_BoundedCofactorComplement (subtract).
/-- **`η_A` proposition, main bound** (unlabeled proposition), EP1054.tex lines 2543–2547:
"As `$A\to\infty$`, `\[ \eta_A\geq\Bigl(\frac{e^{-\gamma}}2-o(1)\Bigr)L(A), \]`" with
`$L(A)=\frac{\log\log\log A}{(\log A)(\log\log A)}$` (line 2540, `Defs.Lscale`).
Encoding: `∀ ε > 0, ∃ A₀, ∀ A ≥ A₀` (`A : ℕ`). -/
def Prop_EtaALower_bound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A₀ : ℕ, ∀ A : ℕ, A₀ ≤ A →
    (Real.exp (-eulerGamma) / 2 - ε) * Lscale A ≤ Coverage.etaA A

-- deps: Prop_EtaALower_bound; `A L(A) → ∞` (elementary: `A/(log A · log₂ A) → ∞`).
/-- **`η_A` proposition, consequence**, EP1054.tex line 2547: "so `$A\eta_A\to\infty$`." -/
def Prop_EtaALower_tendsto : Prop :=
  Tendsto (fun A : ℕ => (A : ℝ) * Coverage.etaA A) atTop atTop

-- deps: Prop_EtaALower_bound, Prop_EtaALower_tendsto.
/-- **Proposition (`η_A` lower bound)** — unlabeled, EP1054.tex lines 2543–2549, the whole
environment: "As `$A\to\infty$`, `\[ \eta_A\geq\Bigl(\frac{e^{-\gamma}}2-o(1)\Bigr)L(A), \quad
\text{so}\quad A\eta_A\to\infty . \]`" -/
def Prop_EtaALower : Prop :=
  Prop_EtaALower_bound ∧ Prop_EtaALower_tendsto

-- deps: Prop_EtaALower_tendsto and Eq_DeltaAAsymptotic (`η_A/δ_A = A η_A/(A δ_A)`,
--       `A δ_A → e^{−γ} > 0`); Eq_BoundedCofactorComplement for the second conjunct
--       (`A(1 − lowerDens G_A) = A δ_A + A η_A → ∞`).
/-- **`η_A` dominates `δ_A`** — unlabeled remark, EP1054.tex lines 2537–2538 ("The two terms in
\eqref{eq:bounded-cofactor-complement} are of different orders, and it is `$\eta_A$` that
dominates") and lines 2559–2562: "One might guess that coprimality to `$P_A\#$` is asymptotically
the only obstruction, so that `$1-\lowerdens(G_A)\sim e^{-\gamma}/A$`. The proposition rules this
out. The integers missed by `$G_A$` for other reasons outnumber the coprime ones by a factor that
tends to infinity."
Encoding: `η_A/δ_A → ∞` (`δ_A > 0`), and `A (1 − lowerDens G_A) ↛ e^{−γ}`. -/
def Coverage.Rem_EtaDominates : Prop :=
  Tendsto (fun A : ℕ => Coverage.etaA A / Coverage.deltaA A) atTop atTop ∧
    ¬ Tendsto (fun A : ℕ => (A : ℝ) * (1 - lowerDens (Gcov A))) atTop
        (𝓝 (Real.exp (-eulerGamma)))

/-! ## The cofactor-two range (lines 2564–2645) -/

namespace Coverage

/-- `θ₂ = \upperdens\bigl(F_2(\N)\bigr)`, EP1054.tex lines 2564–2567. -/
noncomputable def theta2 : ℝ := upperDens (Frange 2)

/-- The untouchable numbers `𝒰 = ℕ ∖ s(ℕ)`, EP1054.tex lines 2582–2585: "Write
`\[ \mathcal{U}=\N\setminus s(\N). \]`" Encoding: `{N : aliquot m ≠ N for every m ≥ 1}` — the same
set as in the input `Cite_ChenZhao`, so that input reads `0.0602757 ≤ lowerDens untouchable` by
`rfl`. (`0 = s(1)` is excluded, and `cnt` counts from `1` anyway.) -/
def untouchable : Set ℕ := {N : ℕ | ∀ m : ℕ, 1 ≤ m → aliquot m ≠ N}

end Coverage

-- deps: none beyond the definition of `F`: the divisors of `2d` that exceed `d` are exactly `2d`
--       (a divisor `r > d` of `2d` has cofactor `2d/r < 2`), so `F_2(d) = σ(2d) − 2d`.
/-- **`eq:F2-aliquot`**, EP1054.tex lines 2577–2580: "The only divisor of `$2d$` exceeding `$d$` is
`$2d$`, and hence
```
 F_2(d)=\sigma(2d)-2d=s(2d).
```"
Encoding: `d ≥ 1`; `aliquot (2d) = σ(2d) − 2d` (no truncation). -/
def Eq_F2Aliquot : Prop :=
  ∀ d : ℕ, 1 ≤ d → F 2 d = aliquot (2 * d)

-- deps: Eq_F2Aliquot; Std_sigma_odd_iff (`s(n)` odd for even `n` iff `σ(n)` odd iff `n` is a square
--       or twice a square); `s(n) ≥ 1 + n/2` for even `n ≥ 4` (so `s(n) ≤ X ⟹ n < 2X`, apart
--       from `n = 2`); the count of squares and twice-squares below `2X` is `O(√X)`.
/-- **`eq:F2-odd-negligible`**, EP1054.tex lines 2587–2594: "… Thus `$s(n)\leq X$` implies
`$n<2X$`, apart from at most this one value. Consequently,
```
 \#\{N\leq X:N\text{ odd},\ N\in F_2(\N)\}=O(\sqrt X).
```"
Encoding: absolute `C`, quantified before `X`; real `X ≥ 1`. -/
def Eq_F2OddNegligible : Prop :=
  ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X → (cnt {N : ℕ | Odd N ∧ N ∈ Frange 2} X : ℝ) ≤ C * Real.sqrt X

-- deps: Cite_MV_exceptional (even `n ≤ X` not a sum of two primes: `O(X^{1−κ})`); the diagonal
--       `N − 1 = 2p` contributes `≤ π(X) = O(X/log X)` (Mathlib Chebyshev bound,
--       `Chebyshev.pi_le_log4_mul_div` or density zero of the primes); the identity
--       `s(pq) = 1 + p + q` for distinct primes `p, q`.
/-- **`eq:odd-untouchables`**, EP1054.tex lines 2596–2605: "Almost all untouchable numbers are
even. Indeed, let `$N$` be odd. If `$N-1=p+q$` with distinct primes `$p$` and `$q$`, then the
proper divisors of `$pq$` are `$1,p,q$`, and therefore `$s(pq)=N$`. … Hence
```
 \#\{N\leq X:N\text{ odd},\ N\in\mathcal{U}\}=o(X).
```"
Encoding: `DensZero` of the odd untouchables. -/
def Eq_OddUntouchables : Prop :=
  DensZero {N : ℕ | Odd N ∧ N ∈ Coverage.untouchable}

-- deps: Cite_ChenZhao (`lowerDens 𝒰 ≥ 0.0602757`; `Coverage.untouchable` is its set verbatim);
--       Eq_OddUntouchables (subtract the `o(X)` odd untouchables); `cnt` along real `X` vs `⌊X⌋`.
/-- **Even untouchables have lower density `≥ 0.0602757`** — unlabeled, EP1054.tex lines
2610–2612: "By \eqref{eq:odd-untouchables}, the number of even untouchables not exceeding `$X$` is at
least `$(0.0602757+o(1))X$`."
Encoding: `(0.0602757 + o(1)) X ≤ count` as `∀ ε > 0, ∃ X₀, ∀ X ≥ X₀` (real `X`),
`(0.0602757 − ε) X ≤ #{N ≤ X : N even, N ∈ 𝒰}`. -/
def Coverage.Step_EvenUntouchables : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    (0.0602757 - ε) * X ≤ (cnt {N : ℕ | Even N ∧ N ∈ Coverage.untouchable} X : ℝ)

-- deps: Eq_F2Aliquot (`F_2(ℕ) ⊆ s(ℕ)`, so `F_2(ℕ) ∩ 𝒰 = ∅`); Eq_F2OddNegligible (all but
--       `O(√X)` elements of `F_2(ℕ) ∩ [1, X]` are even); Coverage.Step_EvenUntouchables;
--       `X/2 + O(1)` even integers up to `X` (so `#(even, ∉ 𝒰, ≤ X) ≤ X/2 + O(1) − #(even ∈ 𝒰)`).
/-- **The count of `F_2(ℕ)` up to `X`** — unlabeled proof display, EP1054.tex lines 2612–2619:
"There are `$X/2+O(1)$` even integers up to `$X$`, and by \eqref{eq:F2-odd-negligible} all but
`$O(\sqrt X)$` elements of `$F_2(\N)\cap[1,X]$` are even. Since \eqref{eq:F2-aliquot} shows that this
range misses every member of `$\mathcal{U}$`, we obtain
```
 \#\bigl(F_2(\N)\cap[1,X]\bigr)
 \leq\frac X2-0.0602757X+o(X).
```"
Encoding: `o(X)` is `∀ ε > 0, ∃ X₀, ∀ X ≥ X₀` (real `X`), with error `ε X`. -/
def Coverage.Disp_F2Count : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    (cnt (Frange 2) X : ℝ) ≤ X / 2 - 0.0602757 * X + ε * X

-- deps: Coverage.Disp_F2Count ("Taking the upper limit proves the proposition", line 2620: divide
--       by `X`, take `limsup` along `ℕ`), which rests on Eq_F2Aliquot, Eq_F2OddNegligible,
--       Eq_OddUntouchables, Cite_ChenZhao via Coverage.Step_EvenUntouchables; the printed
--       arithmetic `1/2 − 0.0602757 = 0.4397243` is `norm_num`.
/-- **Proposition `prop:theta-two`**, EP1054.tex lines 2569–2574: "One has
```
 \theta_2\leq\frac12-0.0602757=0.4397243.
```"
Encoding: `θ₂ ≤ 1/2 − 0.0602757`, together with the printed arithmetic
`1/2 − 0.0602757 = 0.4397243` (exact decimals in `ℝ`). -/
def Prop_ThetaTwo : Prop :=
  Coverage.theta2 ≤ 1 / 2 - 0.0602757 ∧ (1 / 2 - 0.0602757 : ℝ) = 0.4397243

-- deps: none beyond the definitions: `F 1 d = σ(d)` (every divisor of `d` is `≤ d`).
/-- **`G₂ = σ(ℕ) ∪ F₂(ℕ)`** — unlabeled proof display, EP1054.tex lines 2631–2634: "Since
`$F_1(d)=\sigma(d)$`, `\[ G_2=\sigma(\N)\cup F_2(\N). \]`"
Encoding: `σ(ℕ) = {N : ∃ n ≥ 1, σ(n) = N}` (as in `Lem_SigmaRangeZero`). -/
def Coverage.Step_G2Decomp : Prop :=
  Gcov 2 = {N : ℕ | ∃ n : ℕ, 1 ≤ n ∧ sig n = N} ∪ Frange 2

-- deps: Coverage.Step_G2Decomp; Lem_SigmaRangeZero (S2); subadditivity of `upperDens`.
/-- **`upperdens(G₂) ≤ θ₂`** — unlabeled, EP1054.tex lines 2635–2636: "Lemma
\ref{lem:sigma-range-zero} implies that `$\sigma(\N)$` has density zero, and therefore
`$\upperdens(G_2)\leq\theta_2$`." -/
def Coverage.Step_UpperDensG2 : Prop :=
  upperDens (Gcov 2) ≤ Coverage.theta2

-- deps: none — finite computation: `lcm(1, 2) = 2`, `P₂ = 2 · 2 = 4`, `4# = 2 · 3 = 6`,
--       `Δ(4) = (1 − 1/2)(1 − 1/3) = 1/3`.
/-- **The values at `A = 2`** — unlabeled, EP1054.tex lines 2636–2637: "Moreover, `$\Lambda(2)=2$`,
`$P_2=4$`, `$P_2\#=6$`, and so `$\delta_2=1/3$`." -/
def Coverage.Step_P2Values : Prop :=
  lcmUpTo 2 = 2 ∧ Coverage.PA 2 = 4 ∧ primorialR (Coverage.PA 2) = 6 ∧ Coverage.deltaA 2 = 1 / 3

-- deps: Eq_BoundedCofactorComplement at `A = 2`; Coverage.Step_P2Values (`δ₂ = 1/3`);
--       `lowerDens ≤ upperDens`; Coverage.Step_UpperDensG2; Prop_ThetaTwo.
/-- **Corollary (`η₂` lower bound)** — unlabeled, EP1054.tex lines 2623–2628: "For the residual
density defined above,
```
 \eta_2\geq\frac23-0.4397243>0.2269.
```"
Encoding: both inequalities, the second being the printed arithmetic. -/
def Cor_EtaTwo : Prop :=
  (2 / 3 - 0.4397243 : ℝ) ≤ Coverage.etaA 2 ∧ (0.2269 : ℝ) < 2 / 3 - 0.4397243

/-! ## The weak bounded-cofactor conjecture (lines 2647–2670) -/

-- deps: NONE — a CONJECTURE, never asserted. (It is shown equivalent to Coverage.NuTight by
--       Prop_TightnessEquivalence, and to η_A = o(1) by Coverage.Rem_ConjEquivEta.)
/-- **`conj:bounded-cofactor-weak` — CONJECTURE, NOT CLAIMED.** EP1054.tex lines 2647–2656: "We
conjecture that bounded cofactors cover sets of lower density tending to one as the cofactor bound
grows.
```
\begin{conjecture}
\label{conj:bounded-cofactor-weak}
As $A\to\infty$ through the positive integers,
\[
 \lowerdens(G_A)\longrightarrow1.
\]
Equivalently, $\eta_A=o(1)$.
\end{conjecture}
```"
Encoding: `lowerDens (Gcov A) → 1` along `A ∈ ℕ`. The "Equivalently" clause is the separate,
*proved* equivalence `Coverage.Rem_ConjEquivEta`. -/
def Conj_BoundedCofactorWeak : Prop :=
  Tendsto (fun A : ℕ => lowerDens (Gcov A)) atTop (𝓝 1)

-- deps: Eq_BoundedCofactorComplement (`1 − lowerDens G_A = δ_A + η_A`, `A ≥ 1`);
--       Eq_DeltaAAsymptotic (`δ_A → 0`).
/-- **The conjecture is equivalent to `η_A = o(1)`** — EP1054.tex line 2655 ("Equivalently,
`$\eta_A=o(1)$`") and lines 2658–2660: "The equivalence in Conjecture
\ref{conj:bounded-cofactor-weak} follows from \eqref{eq:bounded-cofactor-complement} and
\eqref{eq:delta-A-asymptotic}." A *proved* equivalence (neither side is claimed). -/
def Coverage.Rem_ConjEquivEta : Prop :=
  Conj_BoundedCofactorWeak ↔ Tendsto Coverage.etaA atTop (𝓝 0)

-- deps: Notation_Delta_density (S1: the `A`-rough integers — those coprime to `A#` — have density
--       `Δ(A)`; a subset has upper density at most that); `Δ(A) → 0` (Std_Mertens3, or the
--       divergence `Nat.Primes.not_summable_one_div`).
/-- **The `A`-rough part of `ℕ ∖ G_A` is small** — unlabeled remark, EP1054.tex lines 2662–2666:
"… The set `$V_A$` consists of `$A$`-rough integers, so the forced congruences say nothing about
integers with a prime factor at most `$A$` that are missed by `$G_A$`. The `$A$`-rough part of
`$\N\setminus G_A$` has upper density at most `$\Delta(A)$`, which tends to zero."
Encoding: `A ≥ 1` a positive integer; `A`-rough is `Defs.IsRough A` (`1` is rough). The claim about
`V_A` is `UpperTails.Claim_VA_rough` of `S5_UpperTails` and is not restated. -/
def Coverage.Rem_RoughPartBound : Prop :=
  (∀ A : ℕ, 1 ≤ A → upperDens {N : ℕ | IsRough (A : ℝ) N ∧ N ∉ Gcov A} ≤ Delta A) ∧
    Tendsto (fun A : ℕ => Delta A) atTop (𝓝 0)

-- deps: Coverage.Rem_RoughPartBound; Coverage.Fact_UpperDensCompl; subadditivity and
--       monotonicity of `upperDens` (`ℕ ∖ G_A` = rough part ∪ small-prime part).
/-- **The conjecture concerns only the small-prime part** — unlabeled remark, EP1054.tex lines
2667–2670: "Conjecture \ref{conj:bounded-cofactor-weak} is therefore equivalent to the assertion
that the part of `$\N\setminus G_A$` with a prime factor at most `$A$` has upper density tending to
zero. Every element of that part satisfies some forced congruence and is nevertheless not a value."
Encoding: the equivalence (a proved claim). The last sentence is explanatory (each such `N` is
divisible by a prime `p ≤ A`, and `p = K_{p,1} ∈ 𝒦_A`) and is not separately stated. -/
def Coverage.Rem_ConjEquivSmallPrimePart : Prop :=
  Conj_BoundedCofactorWeak ↔
    Tendsto (fun A : ℕ => upperDens {N : ℕ | (∃ p ∈ N.primeFactors, p ≤ A) ∧ N ∉ Gcov A})
      atTop (𝓝 0)

/-! ## Tightness ⟺ coverage (lines 2672–2722) -/

-- deps: none — `cnt Sᶜ X + cnt S X = X` for natural `X`, and `limsup (1 − u) = 1 − liminf u` for a
--       bounded real sequence (Mathlib `limsup_const_sub`-type lemmas, root namespace, in
--       `Mathlib.Topology.Algebra.Order.LiminfLimsup`; bounded by `[0, 1]`).
/-- **`upperdens(ℕ ∖ S) = 1 − lowerdens(S)`** — unlabeled, EP1054.tex line 2716: "Finally,
`$\upperdens(\N\setminus G_E)=1-\lowerdens(G_E)$` identically." Stated for every `S ⊆ ℕ` (the
identity the paper invokes, at `S = G_E`; also used for `eq:bounded-cofactor-complement`). -/
def Coverage.Fact_UpperDensCompl : Prop :=
  ∀ S : Set ℕ, upperDens Sᶜ = 1 - lowerDens S

-- deps: NONE — a criterion, never asserted on its own (one side of Prop_TightnessEquivalence;
--       equivalent to Conj_BoundedCofactorWeak via Coverage.Fact_UpperDensCompl).
/-- **`eq:tightness-criterion`**, EP1054.tex lines 2678–2680:
```
 \lim_{E\to\infty}\upperdens(\N\setminus G_E)=0.
```
Encoding: `E → ∞` through `ℕ` (`G_E` depends on `⌊E⌋` only). A *criterion*, not asserted: it is
one side of `Prop_TightnessEquivalence` and is equivalent to the conjecture. -/
def Eq_TightnessCriterion : Prop :=
  Tendsto (fun E : ℕ => upperDens {N : ℕ | N ∉ Gcov E}) atTop (𝓝 0)

-- deps: F_ge + f_le_of_F (Basic) (`N ∈ G_E ⟹ N ∈ 𝓡 ∧ f(N) ≤ ed ≤ EN`, so
--       `{N ∈ 𝓡 : f(N) > EN} ⊆ ℕ ∖ G_E`); Eq_ExactRepresentability (S1) to replace `R(X)` by
--       `X + O(1)` (Intro_RcntFormula).
/-- **Tail ≤ complement** — unlabeled proof display, EP1054.tex lines 2689–2700: "`\[ N\in
G_E\quad\Longrightarrow\quad f(N)\leq ed\leq EN \quad\text{for some }e\leq E. \]` Using
\eqref{eq:exact-representability} to replace the normalization by `$X+O(1)$`, we obtain
```
 \limsup_{X\to\infty}\nu_X((E,\infty])
 \leq\upperdens(\N\setminus G_E).
```"
Encoding: `E ≥ 1` natural; `(E, ∞]` is `Set.Ioi (E : ℝ≥0∞)`; the `limsup` is in `ℝ≥0∞` over real
`X → ∞`; the right side is `ENNReal.ofReal` of the (nonnegative) upper density. -/
def Coverage.Disp_TailLeCompl : Prop :=
  ∀ E : ℕ, 1 ≤ E →
    limsup (fun X : ℝ => nuX X (Set.Ioi (E : ℝ≥0∞))) atTop ≤
      ENNReal.ofReal (upperDens {N : ℕ | N ∉ Gcov E})

-- deps: Lem_Moment (S2, Eq_LargeCount with `A = T`: represented `N ∉ G_E` with `f(N) ≤ TN` have a
--       witnessing cofactor `e > E`, so lie in `largeCofactorSet T E`); f_mem_Fform (Basic);
--       Eq_ExactRepresentability (S1: only `2, 5` unrepresented; `R(X) = X + O(1)`).
/-- **Complement ≤ tail + large cofactors** — unlabeled proof display, EP1054.tex lines 2706–2713:
"Conversely, fix `$T\geq1$` and an integer `$k\geq2$`. Every represented `$N\notin G_E$` with
`$f(N)\leq TN$` has a witnessing cofactor `$e>E$`. Lemma \ref{lem:moment} therefore gives
```
 \upperdens(\N\setminus G_E)
 \leq\limsup_{X\to\infty}\nu_X((T,\infty])
 +C_kT^{k+1}E^{1-k}.
```"
Encoding: `∀ k ≥ 2, ∃ C` (the `C_k` of `lem:moment`, depending on `k` only, so before `T, E`),
`∀ T ≥ 1` real, `∀ E ≥ 1` natural; the inequality is read in `ℝ≥0∞` (`ENNReal.ofReal` of the real
quantities). -/
def Coverage.Disp_ComplLeTail : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T → ∀ E : ℕ, 1 ≤ E →
    ENNReal.ofReal (upperDens {N : ℕ | N ∉ Gcov E}) ≤
      limsup (fun X : ℝ => nuX X (Set.Ioi (ENNReal.ofReal T))) atTop +
        ENNReal.ofReal (C * T ^ (k + 1) * (E : ℝ) ^ (1 - (k : ℝ)))

-- deps: Coverage.Disp_TailLeCompl (criterion ⟹ uniformly small tail for large `X`) and, for `X` in
--       a bounded interval, finiteness of the represented targets (a common finite bound on
--       `f(N)/N`); Coverage.Disp_ComplLeTail (tight ⟹ criterion: let `E → ∞`, then `T → ∞`);
--       Coverage.Fact_UpperDensCompl (the "Equivalently" clause); Lem_Moment,
--       Eq_ExactRepresentability via those displays; monotonicity of `E ↦ G_E` and of
--       `T ↦ ν_X((T, ∞])`.
/-- **Proposition `prop:tightness-equivalence`**, EP1054.tex lines 2674–2687: "The empirical
measures `$\nu_X$` form a tight family on `$[0,\infty)$` if and only if
```
 \lim_{E\to\infty}\upperdens(\N\setminus G_E)=0.
```
Equivalently, `\[ \lim_{E\to\infty}\lowerdens(G_E)=1. \]` Thus Conjecture
\ref{conj:bounded-cofactor-weak} is exactly the assertion that the family `$\{\nu_X\}$` is tight."
Encoding: three equivalences — (i) `NuTight ↔ eq:tightness-criterion`, (ii) the criterion
`↔ lowerDens (Gcov E) → 1`, (iii) `Conj_BoundedCofactorWeak ↔ NuTight`. Tightness is the paper's
definition (`Coverage.NuTight`, lines 2264–2268). Neither side of any equivalence is claimed. -/
def Prop_TightnessEquivalence : Prop :=
  (Coverage.NuTight ↔ Eq_TightnessCriterion) ∧
    (Eq_TightnessCriterion ↔ Tendsto (fun E : ℕ => lowerDens (Gcov E)) atTop (𝓝 1)) ∧
    (Conj_BoundedCofactorWeak ↔ Coverage.NuTight)

-- deps: Coverage.Fact_RtPosIff (on 𝓡, `r_A(N) > 0 ⟺ f(N) ≤ AN`); Eq_ExactRepresentability (S1:
--       only `2, 5` unrepresented, and `rt A N = 0` off 𝓡); Prop_TightnessEquivalence (tightness
--       is `lim_A limsup_X ν_X((A, ∞]) = 0` given the bounded-`X` argument); Intro_RcntFormula
--       (S1: `R(X) = ⌊X⌋ − 2`, normalisation by `X` vs `R(X)`); monotonicity in `A` (real vs
--       integer `A`).
/-- **`eq:T` is equivalent to the conjecture** — unlabeled closing remark, EP1054.tex lines
2719–2722: "Since `$r_A(N)>0$` is equivalent, apart from the two unrepresented integers, to
`$f(N)\leq AN$`, Proposition \ref{prop:tightness-equivalence} also shows that the density-one
statement \eqref{eq:T} is equivalent to the weak bounded-cofactor conjecture."
A *proved* equivalence; neither `Eq_T` nor `Conj_BoundedCofactorWeak` is claimed. -/
def Coverage.Rem_T_iff_Conj : Prop :=
  Eq_T ↔ Conj_BoundedCofactorWeak

end Principia.Erdos1054
