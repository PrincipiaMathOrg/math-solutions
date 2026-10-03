/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Defs
import Principia.Erdos1054.Statements.Inputs

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) §5 "Upper tails" — statements only

Source: `Campaigns/Erdos-1054/collab-paper/EP1054.tex`, lines 1888–2247: `lem:kernel-tails`, the
periodic obstruction `𝒦_A, V_A, W_A`, `prop:fm-envelope`, `cor:fm-envelope-tail`, and the
intermediate claims inside the proofs of Theorems 1.3 (`thm:almost-log-tail`) and 1.4
(`thm:subexp-growth`). **Nothing here is asserted**: every result is a `def … : Prop`, and every
`-- deps:` comment records what the paper's *proof* of it uses, for the spine.

## Layout

* Paper-labelled results live in `Principia.Erdos1054` and are named from their label
  (`lem:kernel-tails ↦ Lem_KernelTails`, `eq:… ↦ Eq_…`).
* Section-local objects (`S(y,H)`, `𝒦_A`, `V_A`, `W_A`, `d(V_A)`, the Theorem 1.4 parameters, …)
  and unlabelled intermediate claims (`Claim_…`) live in the sub-namespace
  `Principia.Erdos1054.UpperTails`, so they cannot collide with other sections' modules.
* `L(A)` (line 1983) is `Lscale` from `Defs`; it is not redefined.
* Theorems 1.3 and 1.4 themselves are stated at lines 177–217 and belong to the §1 statements
  module; the claims below are the links of their proofs. The two final limiting steps of those
  proofs (`j → ∞` in Theorem 1.3, line 2103; `eq:positive-moment-growth` from `eq:subexp-growth`,
  lines 2235–2243) are consumer steps of those theorems and are not restated here.

## Encoding conventions used throughout

* "`X` sufficiently large" is `∃ X₀, ∀ X ≥ X₀`; `o(·)` is `∀ ε > 0, ∃ X₀, ∀ X ≥ X₀, … ≤ ε · …`.
* Mathlib's `Real.log x` is `Real.log |x|` (and `Real.log 0 = 0`), so iterated logs of small
  arguments are junk (e.g. `logIt 3 E` for `e < E < e^e` is `log |log log E|`, not `0`); every
  statement below is about the regime where the paper's logarithms are defined and positive, which
  the `X₀`/`A₀`/`T₀`/`J₀` thresholds guarantee.
* `f` has junk value `0` off `𝓡`, so every set of the form `{f(N) > t N}` conjoins `N ∈ R`.
* "`P`-rough" is `IsRough (P : ℝ) N`; `gcd(N, P#) = 1` is `Nat.Coprime N (primorial P)`.
  (For `N ≥ 1` these agree.)
-/

namespace Principia.Erdos1054

open Finset Filter
open scoped Topology

/-! ## §5.1 Divisor tails of a least common multiple (lines 1896–1977) -/

namespace UpperTails

-- deps: (definition)
/-- The primes `p ≤ y`, as a `Finset` (the index set of `∏_{p≤y}` and `∑_{p≤y}`). -/
noncomputable def primesLE (y : ℝ) : Finset ℕ := (Finset.Iic ⌊y⌋₊).filter Nat.Prime

-- deps: (definition)
/-- `lem:kernel-tails`, EP1054.tex line 1900. "For `y,H ≥ 2`, put
`S(y,H):=\sum_{\substack{L\mid \Lambda(y)\\L>H}}\frac{\tau(L)}L`."

Encoding: `Λ(y) = lcmUpTo y`; `τ(L) = L.divisors.card`; the sum is over the divisors `L` of `Λ(y)`
with `H < L` (real comparison). Defined for all real `y, H`; the paper uses it for `y, H ≥ 2`. -/
noncomputable def Skernel (y H : ℝ) : ℝ :=
  ∑ L ∈ (lcmUpTo y).divisors.filter (fun L : ℕ => H < (L : ℝ)), (L.divisors.card : ℝ) / L

-- deps: (definition)
/-- `lem:kernel-tails`, EP1054.tex lines 1905–1908. "`P:=\left\lfloor
E^{\,1+(2+(\log\log\log E)^{-1/2})\log\log E/\log\log\log E}\right\rfloor`".

Encoding: `(log log log E)^{-1/2} = 1/√(logIt 3 E)` (equal wherever `logIt 3 E > 0`, which is the
regime `E → ∞` of the lemma); natural floor. The same `P` (with `E = A`) is used in the proof of
`cor:fm-envelope-tail` (line 2036). -/
noncomputable def Pfix (E : ℝ) : ℕ :=
  ⌊E ^ (1 + (2 + 1 / Real.sqrt (logIt 3 E)) * logIt 2 E / logIt 3 E)⌋₊

-- deps: (definition)
/-- `lem:kernel-tails`, EP1054.tex line 1918: "`W=\sqrt{\frac{J\log J}{2}}`". Also the `W` of the
proof of Theorem 1.4 (line 2118), with `J = log P`. -/
noncomputable def Wmov (J : ℝ) : ℝ := Real.sqrt (J * Real.log J / 2)

-- deps: (definition)
/-- `lem:kernel-tails`, EP1054.tex line 1919: "`F=\lfloor e^W\rfloor`". Also the `F` of the proof of
Theorem 1.4 (line 2119). (Named `Fmov` because `F` is the divisor-prefix function of `Defs`.) -/
noncomputable def Fmov (J : ℝ) : ℕ := ⌊Real.exp (Wmov J)⌋₊

end UpperTails

open UpperTails

-- deps: Rankin's trick (`1_{L>H} ≤ (L/H)^α`), multiplicativity of `τ` and the Euler product over
--       the `y`-smooth integers (every `L ∣ Λ(y)` is `y`-smooth); the geometric identity
--       `∑_{a≥0} (a+1) x^a = (1-x)^{-2}` for `x = p^{α-1} < 1`.
/-- `eq:rankin-kernel`, EP1054.tex lines 1929–1938 (inside the proof of `lem:kernel-tails`).
"For `0<\alpha\leq1/4`, Rankin's inequality and the Euler product for the divisor function give
`S(y,H) \leq H^{-\alpha} \prod_{p\leq y}\sum_{a\geq0} \frac{a+1}{p^{a(1-\alpha)}}
=H^{-\alpha} \prod_{p\leq y}(1-p^{-1+\alpha})^{-2}`."

Encoding: the closed form (right-most side) only; the middle series is the Euler-factor identity.
`y, H ≥ 2` is the lemma's standing range. Real powers are `Real.rpow`. -/
def Eq_RankinKernel : Prop :=
  ∀ y H : ℝ, 2 ≤ y → 2 ≤ H → ∀ α : ℝ, 0 < α → α ≤ 1 / 4 →
    Skernel y H ≤ H ^ (-α) * ∏ p ∈ primesLE y, ((1 - (p : ℝ) ^ (α - 1)) ^ 2)⁻¹

-- deps: Std_Mertens2 (Mertens' `∑_{p≤y} 1/p`); Chebyshev's bound (Mathlib
--       `Chebyshev.theta_le_log4_mul_x`); partial summation (Mathlib `sum_mul_eq_sub_integral_mul`).
/-- `eq:sharp-prime-sum`, EP1054.tex lines 1940–1948 (inside the proof of `lem:kernel-tails`).
"Mertens' estimate for `\sum_{p\leq y}1/p`, Chebyshev's bound, and partial summation show that,
when `z=\alpha\log y\to\infty`,
`\sum_{p\leq y}p^{-1+\alpha} =\log\log y+ O\left(\int_0^z\frac{e^u-1}{u}\,du\right)
=\log\log y+O\left(\frac{e^z}{z}\right)`."

Encoding: the final (two-sided) form; the implied constant `C` is absolute and uniform over all
`y ≥ 2`, `0 < α ≤ 1/4` (the standing range of the proof, line 1929) with `z = α log y ≥ z₀`
("`z → ∞`" read as "`z` sufficiently large"). The middle `∫` form is not restated. -/
def Eq_SharpPrimeSum : Prop :=
  ∃ C z₀ : ℝ, ∀ y α : ℝ, 2 ≤ y → 0 < α → α ≤ 1 / 4 → z₀ ≤ α * Real.log y →
    |∑ p ∈ primesLE y, (p : ℝ) ^ (α - 1) - Real.log (Real.log y)| ≤
      C * (Real.exp (α * Real.log y) / (α * Real.log y))

-- deps: `-log(1-x) = x + O(x^2)` for `0 ≤ x ≤ 2^{-3/4}`, and `∑_p p^{-3/2} < ∞`.
/-- Unlabelled claim, EP1054.tex lines 1949–1950 (inside the proof of `lem:kernel-tails`).
"The higher terms in the logarithm of the Euler product in \eqref{eq:rankin-kernel} are `O(1)`
uniformly for `\alpha\leq1/4`."

Encoding: `|log ∏_{p≤y}(1-p^{α-1})^{-2} - 2∑_{p≤y} p^{α-1}| ≤ C` with `C` absolute, for all
`y ≥ 2`, `0 < α ≤ 1/4`. -/
def UpperTails.Claim_EulerHigherTerms : Prop :=
  ∃ C : ℝ, ∀ y α : ℝ, 2 ≤ y → 0 < α → α ≤ 1 / 4 →
    |Real.log (∏ p ∈ primesLE y, ((1 - (p : ℝ) ^ (α - 1)) ^ 2)⁻¹) -
        2 * ∑ p ∈ primesLE y, (p : ℝ) ^ (α - 1)| ≤ C

-- deps: Eq_RankinKernel (with α = log log log E / log E), Eq_SharpPrimeSum (z = log log log E),
--       UpperTails.Claim_EulerHigherTerms.
/-- `eq:fixed-kernel-tail`, EP1054.tex lines 1904–1915 (first assertion of `lem:kernel-tails`).
"If `E\to\infty` and `P:=\lfloor E^{\,1+(2+(\log\log\log E)^{-1/2})\log\log E/\log\log\log E}
\rfloor`, then `\log S(E,P/E) \leq-\frac{\log\log E}{\sqrt{\log\log\log E}}
+O\left(\frac{\log\log E}{\log\log\log E}\right)`."

Encoding: `∃ C, ∃ E₀, ∀ E ≥ E₀, S(E, P/E) ≤ exp(−log log E/√(log log log E) + C log log E/
log log log E)`. The paper's `log S ≤ RHS` presupposes `S > 0` (line 134: logarithms are "used only
where they are defined"); the exponentiated form is equivalent when `S > 0` and does not depend on
Mathlib's junk value `log 0 = 0`. `E` is real (the corollary takes `E = A` real). -/
def Eq_FixedKernelTail : Prop :=
  ∃ C : ℝ, ∃ E₀ : ℝ, ∀ E : ℝ, E₀ ≤ E →
    Skernel E ((Pfix E : ℝ) / E) ≤
      Real.exp (-(logIt 2 E / Real.sqrt (logIt 3 E)) + C * (logIt 2 E / logIt 3 E))

-- deps: Eq_RankinKernel (with α = W/J), Eq_SharpPrimeSum (z = α log F = ½ log J + o(1)),
--       UpperTails.Claim_EulerHigherTerms.
/-- `eq:moving-kernel-tail`, EP1054.tex lines 1916–1925 (second assertion of `lem:kernel-tails`).
"If instead `J\to\infty`, `W=\sqrt{\frac{J\log J}{2}}, \quad F=\lfloor e^W\rfloor`, then, for every
fixed `C>0`, `S\left(F,\frac{e^J}{CW}\right) \leq\exp\{-W+o(W)\}`."

Encoding: `∀ C > 0, ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, S(F, e^J/(C W)) ≤ exp(−W + ε W)`; the `o(W)` is an
upper-bound error, so only its positive part matters. `C` is fixed before `J → ∞`. -/
def Eq_MovingKernelTail : Prop :=
  ∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∃ J₀ : ℝ, ∀ J : ℝ, J₀ ≤ J →
    Skernel (Fmov J) (Real.exp J / (C * Wmov J)) ≤ Real.exp (-Wmov J + ε * Wmov J)

-- deps: Eq_FixedKernelTail, Eq_MovingKernelTail (the lemma is exactly their conjunction).
/-- `lem:kernel-tails`, EP1054.tex lines 1898–1926. "For `y,H\geq2`, put `S(y,H):=\sum_{L\mid
\Lambda(y), L>H}\frac{\tau(L)}L`. If `E\to\infty` and `P:=\lfloor\cdots\rfloor`, then
\eqref{eq:fixed-kernel-tail}. If instead `J\to\infty`, `W=\sqrt{J\log J/2}`, `F=\lfloor e^W\rfloor`,
then, for every fixed `C>0`, \eqref{eq:moving-kernel-tail}."

Encoding: the conjunction of the two displayed assertions. -/
def Lem_KernelTails : Prop :=
  Eq_FixedKernelTail ∧ Eq_MovingKernelTail

/-! ## §5.2 Periodic obstructions for bounded cofactors (lines 1979–2062) -/

namespace UpperTails

-- deps: (definition)
/-- EP1054.tex lines 1989–1990. "For `A\geq2` let `\mathcal{K}_A` be the set of moduli `K_{e,d}` with
`2\leq e\leq A` and `d\geq1`".

Encoding: the faithful `Set`; `K_{e,d} = Kmod e d` from `Defs`. `A` is real. -/
def KA (A : ℝ) : Set ℕ := {k | ∃ e d : ℕ, 2 ≤ e ∧ (e : ℝ) ≤ A ∧ 1 ≤ d ∧ k = Kmod e d}

-- deps: (definition)
/-- A `Finset` presentation of `𝒦_A`, used only to write `W_A = lcm(𝒦_A)` and the
inclusion–exclusion sum. It restricts `d` to `1 ≤ d ≤ Λ(A)`; that this loses nothing
(for `A ≥ 2`) is the claim `UpperTails.Claim_KA_finite` — the paper's "it is finite by
Section 2" (line 1990–1991). Justification (from the proof of `lem:fm-modulus`, lines 434–437):
`d₀ = M/g` has the same set `D` as `d`, hence the same `K`, and `M/g ≤ M ∣ Λ(e-1) ∣ Λ(A)`. -/
noncomputable def KAfin (A : ℝ) : Finset ℕ :=
  ((Finset.Icc 2 ⌊A⌋₊) ×ˢ (Finset.Icc 1 (lcmUpTo A))).image (fun q : ℕ × ℕ => Kmod q.1 q.2)

-- deps: (definition)
/-- EP1054.tex line 1993. "`V_A=\{N\in\N:k\nmid N\ \text{for every }k\in\mathcal{K}_A\}`." -/
def VA (A : ℝ) : Set ℕ := {N | ∀ k ∈ KA A, ¬ k ∣ N}

-- deps: (definition)
/-- EP1054.tex line 1995. "`W_A=\lcm(\mathcal{K}_A)`" — via the `Finset` presentation `KAfin`
(correct by `UpperTails.Claim_KA_finite`). -/
noncomputable def WA (A : ℝ) : ℕ := (KAfin A).lcm id

open Classical in
-- deps: (definition)
/-- EP1054.tex lines 1996–2001. "By inclusion and exclusion the density is the rational number
`\textup{d}(V_A)=1-\sum_{\varnothing\neq I\subseteq\mathcal{K}_A}\frac{(-1)^{|I|+1}}{\lcm(I)}`."

Encoding: `d(V_A)` is *defined* as this inclusion–exclusion number (over the `Finset`
presentation `KAfin`); that it is the natural density of `V_A` is the claim
`UpperTails.Claim_VA_density`. Every later mention of `d(V_A)` (`prop:fm-envelope`,
`cor:fm-envelope-tail`, the proof of Theorem 1.3) uses this `dV`. -/
noncomputable def dV (A : ℝ) : ℝ :=
  1 - ∑ I ∈ (KAfin A).powerset.filter (fun I => I.Nonempty),
    (-1 : ℝ) ^ (I.card + 1) / ((I.lcm id : ℕ) : ℝ)

end UpperTails

-- deps: the remark before lem:fm-modulus (lines 399–405: `D` depends only on `d` modulo
--       `lcm{j/gcd(j,e)}`) and the proof of Lem_FmModulus (lines 434–437: `d₀ = M/g` has the same `D`).
/-- Unlabelled claim, EP1054.tex lines 1989–1991: "`\mathcal{K}_A` … is finite by
Section \ref{sec:arithmetic-preliminaries}."

Encoding: finiteness in the precise form used to define `W_A` and `d(V_A)`: for `A ≥ 2` the
`Finset` `KAfin A` (moduli with `d ≤ Λ(A)`) is all of `𝒦_A`. -/
def UpperTails.Claim_KA_finite : Prop :=
  ∀ A : ℝ, 2 ≤ A → ((KAfin A : Finset ℕ) : Set ℕ) = KA A

-- deps: UpperTails.Claim_KA_finite (every `k ∈ 𝒦_A` divides `W_A`).
/-- Unlabelled claim, EP1054.tex line 1995: "This is a union of residue classes modulo
`W_A=\lcm(\mathcal{K}_A)`".

Encoding: membership in `V_A` depends only on the residue modulo `W_A`. -/
def UpperTails.Claim_VA_periodic : Prop :=
  ∀ A : ℝ, 2 ≤ A → ∀ N M : ℕ, N ≡ M [MOD WA A] → (N ∈ VA A ↔ M ∈ VA A)

-- deps: UpperTails.Claim_KA_finite, UpperTails.Claim_VA_periodic; inclusion–exclusion over the
--       finite family of multiples of `k ∈ 𝒦_A`; `K_{e,d} ≥ 2` (line 393), so every `N` coprime to
--       `W_A` lies in `V_A`.
/-- Unlabelled claims, EP1054.tex lines 1995–2001: "… so it has a natural density, and
`\textup{d}(V_A)\geq\varphi(W_A)/W_A>0`. By inclusion and exclusion the density is the rational
number `\textup{d}(V_A)=1-\sum_{\varnothing\neq I\subseteq\mathcal{K}_A}\frac{(-1)^{|I|+1}}{\lcm(I)}`."

Encoding: `V_A` has natural density equal to the inclusion–exclusion number `dV A`, and
`0 < φ(W_A)/W_A ≤ dV A`; for every `A ≥ 2`. -/
def UpperTails.Claim_VA_density : Prop :=
  ∀ A : ℝ, 2 ≤ A →
    HasDens (VA A) (dV A) ∧ ((WA A).totient : ℝ) / (WA A : ℝ) ≤ dV A ∧
      0 < ((WA A).totient : ℝ) / (WA A : ℝ)

-- deps: Lem_SigmaRangeZero (lem:sigma-range-zero: the `F_1 = σ` values), Eq_FmCongruence
--       (lem:fm-modulus: `F_e(d) ≡ σ(ed) mod K_{e,d}`), Lem_FixedModulusNormality
--       (lem:fixed-modulus-normality with `V = W_A`), UpperTails.Claim_KA_finite,
--       UpperTails.Claim_VA_density (for the "consequently").
/-- `prop:fm-envelope`, EP1054.tex lines 2002–2008. "Fix `A\geq2`. All but `o_A(X)` of the integers
`N\leq X` in `G_A` are divisible by some `k\in\mathcal{K}_A`. Consequently
`1-\lowerdens(G_A)\geq \textup{d}(V_A)`."

Encoding: `G_A = ⋃_{1≤e≤A} F_e(ℕ)` is `Gcov ⌊A⌋₊` (for real `A`, `e ≤ A ↔ e ≤ ⌊A⌋`). "All but
`o_A(X)` of the `N ≤ X` in `G_A` are divisible by some `k ∈ 𝒦_A`" is `DensZero (G_A ∩ V_A)`
(counting along integer `X` is equivalent, since `cnt S X` depends only on `⌊X⌋`). `d(V_A)` is
`dV A` (see `UpperTails.dV`). -/
def Prop_FmEnvelope : Prop :=
  ∀ A : ℝ, 2 ≤ A →
    DensZero (Gcov ⌊A⌋₊ ∩ VA A) ∧ dV A ≤ 1 - lowerDens (Gcov ⌊A⌋₊)

-- deps: direct computation of `K_{p,1}` (`D = {1}`, `M = C = g = 1`).
/-- Unlabelled claim, EP1054.tex lines 2032–2034 (proof of `cor:fm-envelope-tail`), reused in the
proof of Theorem 1.3 (line 2080: "`V_E` consists of `E`-rough integers") and at line 2663.
"Every prime `p\leq A` lies in `\mathcal{K}_A`: with `e=p` and `d=1` one has `D=\{1\}`,
`M=C=g=1` and `K_{p,1}=p`. So `V_A` consists of `A`-rough integers".

Encoding: both sentences, for every `A ≥ 2`. `IsRough A N` = every prime factor of `N` exceeds
`A` (vacuous for `N = 0, 1`; `0 ∉ V_A` anyway since `2 ∈ 𝒦_A`). -/
def UpperTails.Claim_VA_rough : Prop :=
  ∀ A : ℝ, 2 ≤ A →
    (∀ p : ℕ, p.Prime → (p : ℝ) ≤ A → p ∈ KA A) ∧ ∀ N ∈ VA A, IsRough A N

-- deps: Std_Mertens3 (Mertens' product theorem, `Δ(P) ∼ e^{-γ}/log P`); the definition of `P`.
/-- Unlabelled claim, EP1054.tex lines 2036–2041 (proof of `cor:fm-envelope-tail`). "let `P` be the
parameter of Lemma \ref{lem:kernel-tails} with `E=A`. Then
`\log P=(2+o(1))(\log A)(\log\log A)/\log\log\log A`, and Mertens' theorem gives
`\Delta(P)=\Bigl(\frac{e^{-\gamma}}2+o(1)\Bigr)L(A)`."

Encoding: both `o(1)` statements, relative to the main terms, as `A → ∞`. -/
def UpperTails.Claim_DeltaPfix : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A →
    |Real.log (Pfix A) - 2 * (logIt 1 A * logIt 2 A / logIt 3 A)| ≤
        ε * (logIt 1 A * logIt 2 A / logIt 3 A) ∧
      |Delta (Pfix A) - Real.exp (-eulerGamma) / 2 * Lscale A| ≤ ε * Lscale A

-- deps: Lem_FmModulus (the shape `K_{e,d} = (e/g) C`, `C ≥ M ≥ e`, `C ≤ (e-1) M`),
--       UpperTails.Claim_KA_finite (finitely many moduli, so the union bound is a finite sum),
--       Notation_Delta_density (S1_Main: `P`-rough integers have density `Δ(P)`, whence the
--       density `Δ(P)/C` of the `P`-rough multiples of a `P`-rough `C`); `A < Pfix A` for large
--       `A` (definition of `P`; gives `e/g ≤ A < P` and `M > P/A`).
/-- Unlabelled display, EP1054.tex lines 2045–2061 (proof of `cor:fm-envelope-tail`), with `E = A`:
"Let `N` be `P`-rough and divisible by `k=K_{e,d}` for some `2\leq e\leq A`. Then `k` is `P`-rough.
… `e/g=1`, … `k=C`. … `C>P` … `M>P/A`. … So at most `\tau(M)` moduli `k` share a given `M` …
Since `M\mid\Lambda(A)` and `M>P/A`,
`\textup{d}\{N:N\ \text{$P$-rough},\ N\notin V_A\} \leq\Delta(P)\sum_{M\mid\Lambda(A), M>P/A}
\frac{\tau(M)}M =\Delta(P)\,S(A,P/A)`."

Encoding: the displayed inequality, for all sufficiently large `A` (the argument needs `P > A`).
The set is periodic, so its density exists; we bound its `upperDens`, which is what the display
asserts. The trailing `= o(Δ(P))` is `Eq_FixedKernelTail` and is not restated. -/
def UpperTails.Claim_RoughNotVA : Prop :=
  ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A →
    upperDens {N : ℕ | IsRough (Pfix A) N ∧ N ∉ VA A} ≤
      Delta (Pfix A) * Skernel A ((Pfix A : ℝ) / A)

-- deps: UpperTails.Claim_VA_rough (upper bound), UpperTails.Claim_VA_density,
--       Notation_Delta_density (S1_Main: `A`-rough integers have density `Δ(A)` for the upper
--       bound; `P`-rough integers have density `Δ(P)`, so `d(V_A) ≥ Δ(P) − d{P-rough ∖ V_A}`),
--       UpperTails.Claim_DeltaPfix, UpperTails.Claim_RoughNotVA, Eq_FixedKernelTail (E = A).
/-- `cor:fm-envelope-tail`, EP1054.tex lines 2025–2030. "As `A\to\infty`,
`\Bigl(\frac{e^{-\gamma}}2-o(1)\Bigr)L(A)\leq \textup{d}(V_A)\leq\Delta(A)`."

Encoding: lower bound `∀ ε > 0, ∃ A₀, ∀ A ≥ A₀, (e^{-γ}/2 − ε) L(A) ≤ d(V_A)`; upper bound for all
sufficiently large `A`, literally as stated ("as `A → ∞`"). The proof (lines 2032–2034) in fact gives
the upper bound for every `A ≥ 2`; that stronger form follows from `UpperTails.Claim_VA_rough` and
`UpperTails.Claim_VA_density`. `L(A) = Lscale A`, `d(V_A) = dV A`, `γ = eulerGamma`. -/
def Cor_FmEnvelopeTail : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A →
      (Real.exp (-eulerGamma) / 2 - ε) * Lscale A ≤ dV A) ∧
    ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → dV A ≤ Delta A

/-! ## §5.3 Fixed upper levels — the proof of Theorem 1.3 (lines 2064–2107) -/

namespace UpperTails

-- deps: (definition)
/-- EP1054.tex line 2069: "`b_j=\frac{j+1}{j-1}`". -/
noncomputable def bj (j : ℕ) : ℝ := ((j : ℝ) + 1) / ((j : ℝ) - 1)

-- deps: (definition)
/-- EP1054.tex line 2070: "`E=\left\lceil T^{b_j}(\log T)^{3/(j-1)}\right\rceil`" (natural
ceiling; real powers). -/
noncomputable def Ej (j : ℕ) (T : ℝ) : ℕ :=
  ⌈T ^ bj j * (Real.log T) ^ ((3 : ℝ) / ((j : ℝ) - 1))⌉₊

end UpperTails

-- deps: the definitions of `b_j` and `E` only (`E^{j-1} ≥ T^{j+1}(log T)^3`).
/-- Unlabelled display, EP1054.tex lines 2075–2079 (proof of Theorem 1.3). "Lemma \ref{lem:moment}
bounds the targets with a representation `n\leq TN` and cofactor greater than `E` by
`C_jT^{j+1}E^{1-j}X\leq\frac{C_jX}{(\log T)^3}`."

Encoding: the arithmetic content of the displayed inequality, `T^{j+1} E^{1-j} ≤ (log T)^{-3}`, for
each `j ≥ 3` and all sufficiently large `T` (the proof's standing assumption, line 2067). The count
bound itself is `Eq_LargeCount` (lem:moment) with `A = T`, `E = E`, `k = j`. -/
def UpperTails.Claim_AlmostLogTail_momentArith : Prop :=
  ∀ j : ℕ, 3 ≤ j → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    T ^ (j + 1) * (Ej j T : ℝ) ^ (1 - (j : ℝ)) ≤ 1 / (Real.log T) ^ 3

-- deps: `N` nonsquarefree and `y`-rough ⟹ `p² ∣ N` for some prime `p > y`; `∑_{p>y} p^{-2} ≪ 1/y`.
/-- Unlabelled display, used twice: EP1054.tex lines 2080–2084 (proof of Theorem 1.3, `y = E`) "`V_E`
consists of `E`-rough integers. Its nonsquarefree members up to `X` therefore number at most
`X\sum_{p>E}\frac1{p^2}\ll\frac XE`", and lines 2130–2133 (proof of Theorem 1.4, `y = P`) "The
nonsquarefree members of this interval number at most `X\sum_{p>P}\frac1{p^2}\ll\frac XP`".

Encoding: the common underlying bound, with an absolute constant, uniformly in `y ≥ 2` and
`X ≥ 1`: `#{N ≤ X : N y-rough, N not squarefree} ≤ C X / y`. -/
def UpperTails.Claim_RoughNonsquarefree : Prop :=
  ∃ C : ℝ, ∀ y : ℝ, 2 ≤ y → ∀ X : ℝ, 1 ≤ X →
    (cnt {N : ℕ | IsRough y N ∧ ¬ Squarefree N} X : ℝ) ≤ C * X / y

-- deps: Prop_FmEnvelope (A = E), Eq_LargeCount (lem:moment, k = j, A = T),
--       UpperTails.Claim_AlmostLogTail_momentArith, UpperTails.Claim_VA_rough,
--       UpperTails.Claim_RoughNonsquarefree (y = E), Lem_AnalyticOddRepresentability
--       (V_E is odd), UpperTails.Claim_VA_density, f_mem_Fform (Basic.lean: the least
--       representation is an F-form witness, so no witness with e*d ≤ T N forces f N > T N).
/-- Unlabelled display, EP1054.tex lines 2086–2092 (proof of Theorem 1.3). "Every target surviving
these deletions is represented, squarefree, and satisfies `f(N)>TN`. Consequently
`\lowerdens\{N\in\Rcal:N\text{ squarefree},\ f(N)>TN\} \geq \textup{d}(V_E)-\frac{C_j}{(\log T)^3}
-O(E^{-1})`."

Encoding: `∃ C` (the absolute `O(E^{-1})` constant) before `∀ j ≥ 3`; then `∃ C_j` (the constant of
`lem:moment` with `k = j`) and `∃ T₀` ("for sufficiently large `T`", line 2067). `N ∈ R` is
conjoined (junk `f = 0` off `𝓡`); `d(V_E) = dV E`. -/
def UpperTails.Claim_AlmostLogTail_main : Prop :=
  ∃ C : ℝ, ∀ j : ℕ, 3 ≤ j → ∃ Cj : ℝ, ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    dV (Ej j T) - Cj / (Real.log T) ^ 3 - C / (Ej j T : ℝ) ≤
      lowerDens {N : ℕ | N ∈ R ∧ Squarefree N ∧ T * (N : ℝ) < (f N : ℝ)}

-- deps: the definitions of `E`, `b_j` and `L` (`log E = (b_j + o(1)) log T`).
/-- Unlabelled display, EP1054.tex lines 2093–2096 (proof of Theorem 1.3).
"`L(E)=\left(\frac1{b_j}+o(1)\right)L(T) \quad(T\to\infty)`."

Encoding: for each fixed `j ≥ 3`, `|L(E) − L(T)/b_j| ≤ ε L(T)` for all sufficiently large `T`. -/
def UpperTails.Claim_LscaleRatio : Prop :=
  ∀ j : ℕ, 3 ≤ j → ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |Lscale (Ej j T) - Lscale T / bj j| ≤ ε * Lscale T

-- deps: UpperTails.Claim_AlmostLogTail_main, Cor_FmEnvelopeTail (lower bound, A = E),
--       UpperTails.Claim_LscaleRatio.
/-- Unlabelled display, EP1054.tex lines 2093–2104 (proof of Theorem 1.3). "Corollary
\ref{cor:fm-envelope-tail} and [`L(E)=(1/b_j+o(1))L(T)`] show that the right-hand side is at least
`\left(\frac{e^{-\gamma}}{2b_j}-o(1)\right) \frac{\log\log\log T}{(\log T)(\log\log T)}`. Here both
error terms are `o(L(T))` for each fixed `j`."

Encoding: the fixed-`j` form of `eq:almost-log-tail`: for each `j ≥ 3`,
`∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (e^{-γ}/(2 b_j) − ε) L(T) ≤ lowerdens{N ∈ 𝓡 : N squarefree, f(N) > TN}`.
Letting `j → ∞` (line 2104) gives Theorem 1.3; that step is the theorem's own. -/
def UpperTails.Claim_AlmostLogTail_fixedJ : Prop :=
  ∀ j : ℕ, 3 ≤ j → ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (Real.exp (-eulerGamma) / (2 * bj j) - ε) * Lscale T ≤
      lowerDens {N : ℕ | N ∈ R ∧ Squarefree N ∧ T * (N : ℝ) < (f N : ℝ)}

/-! ## §5.4 Growing upper levels — the proof of Theorem 1.4 (lines 2109–2244) -/

namespace UpperTails

-- deps: (definition)
/-- EP1054.tex line 2116: "`P=\left\lfloor\rho\frac{\log\log X}{\log\log\log X}\right\rfloor`". -/
noncomputable def subP (ρ X : ℝ) : ℕ := ⌊ρ * logIt 2 X / logIt 3 X⌋₊

-- deps: (definition)
/-- EP1054.tex line 2117: "`J=\log P`". -/
noncomputable def subJ (ρ X : ℝ) : ℝ := Real.log (subP ρ X)

-- deps: (definition)
/-- EP1054.tex line 2118: "`W=\sqrt{\frac{J\log J}{2}}`" (= `Wmov J`, the `W` of `lem:kernel-tails`). -/
noncomputable def subW (ρ X : ℝ) : ℝ := Wmov (subJ ρ X)

-- deps: (definition)
/-- EP1054.tex line 2119: "`F=\lfloor e^W\rfloor`" (= `Fmov J`, the `F` of `lem:kernel-tails`). -/
noncomputable def subF (ρ X : ℝ) : ℕ := Fmov (subJ ρ X)

-- deps: (definition)
/-- EP1054.tex line 2120: "`t=e^{(1-\varepsilon)W}`". -/
noncomputable def subT (ε ρ X : ℝ) : ℝ := Real.exp ((1 - ε) * subW ρ X)

open Classical in
-- deps: (definition)
/-- `#\{X/2 < N \leq X : N ∈ S\}` (the dyadic window of Theorem 1.4). For `X ≥ 0` and natural `N`,
`X/2 < N ↔ ⌊X/2⌋ < N` and `N ≤ X ↔ N ≤ ⌊X⌋`. -/
noncomputable def cntHalf (S : Set ℕ) (X : ℝ) : ℕ :=
  ((Finset.Ioc ⌊X / 2⌋₊ ⌊X⌋₊).filter (· ∈ S)).card

-- deps: (definition)
/-- The "bad sources" of EP1054.tex lines 2135–2137: "sources `n` for which some prime `p\leq P`
fails to divide `\sigma(n)`". -/
def badSrc (P : ℕ) : Set ℕ := {n | ∃ p : ℕ, p.Prime ∧ p ≤ P ∧ ¬ p ∣ sig n}

open Classical in
-- deps: (definition)
/-- The remaining low-cofactor witnesses of EP1054.tex lines 2155–2207: pairs `(e, d)` (so
`n = e d`) with `2 ≤ e ≤ F`, `n ≤ t X`, `F_e(d)` `P`-rough, and `n` not a bad source (every prime
`p ≤ P` divides `σ(n)`). The paper's witnesses have `n ≤ tN ≤ tX` for a target `N ≤ X`; the
paper's bound (via `n = L u`, `u ≤ tX/L`) counts exactly these pairs, so no target range is
imposed. `d ≤ ⌊tX⌋` is implied by `e d ≤ tX` and only makes the index set finite. -/
noncomputable def lowWitness (ε ρ X : ℝ) : ℕ :=
  (((Finset.Icc 2 (subF ρ X)) ×ˢ (Finset.Icc 1 ⌊subT ε ρ X * X⌋₊)).filter (fun q : ℕ × ℕ =>
    ((q.1 * q.2 : ℕ) : ℝ) ≤ subT ε ρ X * X ∧ IsRough (subP ρ X) (F q.1 q.2) ∧
      ∀ p : ℕ, p.Prime → p ≤ subP ρ X → p ∣ sig (q.1 * q.2))).card

end UpperTails

-- deps: the definitions (`F ≤ e^W = P^{o(1)}` since `W = o(J) = o(log P)`).
/-- Unlabelled claim, EP1054.tex line 2122 (proof of Theorem 1.4). "In particular `F<P` for all
sufficiently large `X`."

Encoding: for every fixed `ρ > 0` (smallness of `ρ` is not needed here). -/
def UpperTails.Claim_SubexpFltP : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → subF ρ X < subP ρ X

-- deps: complete periods modulo `P#` (`#{coprime to Q in an interval of length ℓ} = ℓ φ(Q)/Q + O(Q)`);
--       Notation_Delta_density (S1: `φ(P#)/P# = Δ(P)`, not definitional since `Defs.Delta` is the
--       product); Std_Mertens3 (`Δ(P) ≍ 1/J`); Chebyshev (Mathlib `primorial_le_four_pow`:
--       `P# = e^{O(P)}`).
/-- `eq:sharp-rough-target-count`, EP1054.tex lines 2122–2129 (proof of Theorem 1.4). "Complete
periods modulo `P\#` and Mertens' theorem give
`\#\{X/2<N\leq X:\gcd(N,P\#)=1\} =\frac X2\Delta(P)+O(P\#) \asymp\frac X{\log\log\log X}`,
because `P\#=\exp(O(P))=X^{o(1)}` and `\Delta(P)\asymp1/J`."

Encoding: all three implied constants are absolute (line 336: "All implied constants are absolute
unless their dependence is indicated", and none is indicated here), so `∃ C c₁ c₂` precede `ρ`;
only the threshold `X₀` depends on `ρ`. (For each fixed `ρ`, `J = (1+o(1)) log log log X`, so
the count times `log log log X / X` tends to `e^{-γ}/2` whatever `ρ` is.) -/
def Eq_SharpRoughTargetCount : Prop :=
  ∃ C c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ ρ : ℝ, 0 < ρ → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    |(cntHalf {N : ℕ | Nat.Coprime N (primorial (subP ρ X))} X : ℝ) -
        X / 2 * Delta (subP ρ X)| ≤ C * (primorial (subP ρ X) : ℝ) ∧
      c₁ * X / logIt 3 X ≤ (cntHalf {N : ℕ | Nat.Coprime N (primorial (subP ρ X))} X : ℝ) ∧
      (cntHalf {N : ℕ | Nat.Coprime N (primorial (subP ρ X))} X : ℝ) ≤ c₂ * X / logIt 3 X

-- deps: Lem_SigmaRate (lem:sigma-rate: `B_q(y) ≪ y exp(-c₁ log log y/q)` for `3 ≤ q ≤ c₀ log log y/
--       log log log y`, and `B_2(y) ≪ √y`), the union bound over primes `p ≤ P`.
/-- `eq:sharp-bad-source-count`, EP1054.tex lines 2135–2144 (proof of Theorem 1.4). "Write `Y=tX`.
Lemma \ref{lem:sigma-rate} and the union bound show that the number of sources `n\leq Y` for which
some prime `p\leq P` fails to divide `\sigma(n)` is at most
`O(\sqrt Y)+O\left( Y\pi(P)\exp\left[-c_1\frac{\log\log Y}{P}\right] \right)`. The first term treats
`p=2`. The chosen range of `P` is permitted by Lemma \ref{lem:sigma-rate} after decreasing `\rho`
if necessary."

Encoding: `∃ c₁ > 0` (the constant of `lem:sigma-rate`) and an absolute `C`, then `∃ ρ₀ > 0` (the
"decreasing `ρ` if necessary") and the bound for every `0 < ρ ≤ ρ₀`, every `0 < ε < 1` (which fixes
`t`), and all sufficiently large `X`. `π(P) = Nat.primeCounting P`. -/
def Eq_SharpBadSourceCount : Prop :=
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ C : ℝ, ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      (cnt (badSrc (subP ρ X)) (subT ε ρ X * X) : ℝ) ≤
        C * (Real.sqrt (subT ε ρ X * X) +
          subT ε ρ X * X * (Nat.primeCounting (subP ρ X) : ℝ) *
            Real.exp (-(c₁ * logIt 2 (subT ε ρ X * X) / (subP ρ X : ℝ))))

-- deps: Eq_SharpBadSourceCount, Eq_SharpRoughTargetCount (`Δ(P) ≍ 1/log log log X`), the sizes
--       `F t = e^{(2-ε)W} = (log log X)^{o(1)}` and `π(P) ≤ P ≤ log log X`.
/-- Unlabelled claim, EP1054.tex lines 2145–2153 (proof of Theorem 1.4). "Since
`Ft=e^{(2-\varepsilon)W}=(\log\log X)^{o(1)}`, `\exp\left[-c_1\frac{\log\log Y}{P}\right]
=(\log\log X)^{-c_1/\rho+o(1)}`, we may also ensure `c_1/\rho>3`. Multiplying
\eqref{eq:sharp-bad-source-count} by the at most `F` possible cofactors per source gives
`o(X\Delta(P))` target--cofactor pairs."

Encoding: `∃ ρ₀ > 0` (this is where `c₁/ρ > 3` is ensured), then for `0 < ρ ≤ ρ₀`, `0 < ε < 1`:
`F · #{bad sources n ≤ tX} = o(X Δ(P))`. -/
def UpperTails.Claim_SubexpBadPairs : Prop :=
  ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ η : ℝ, 0 < η → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      (subF ρ X : ℝ) * (cnt (badSrc (subP ρ X)) (subT ε ρ X * X) : ℝ) ≤
        η * X * Delta (subP ρ X)

-- deps: `F_1(d) = σ(d)` and `2 ∣ σ(d)` for a good source (`p = 2 ≤ P`), against `N` being `P`-rough.
/-- Unlabelled claim, EP1054.tex lines 2155–2156 (proof of Theorem 1.4). "Consider a remaining
`P`-rough target `N` admitting a witness `N=F_e(n/e)` with `n\leq tN` and `e\leq F`. Again `e=1` is
impossible."

Encoding: deterministic, for any `P ≥ 2`: a `P`-rough `N = F_1(d) = σ(d)` (`d ≥ 1`) cannot come
from a good source (one with every prime `p ≤ P` dividing `σ(d)`). The context hypotheses
`n ≤ tN`, `e ≤ F` are not used and are omitted. -/
def UpperTails.Claim_SubexpCofactorOne : Prop :=
  ∀ P N d : ℕ, 2 ≤ P → 1 ≤ d → N = F 1 d → IsRough P N →
    ¬ ∀ p : ℕ, p.Prime → p ≤ P → p ∣ sig d

-- deps: Eq_FmReflection (lem:fm-modulus, with `M = L`: the divisors of `L` below `e` are those of
--       `n`), the `P`-roughness of `R = σ(n) − N` (every `p ≤ P` divides `σ(n)` but not `N`),
--       `e ≤ F < P`, and `C = ∑_{j∈D} L/j` being a sum of distinct divisors of `L`; `L ∣ n` since
--       every `r ∈ D` divides `n` (Mathlib `Finset.lcm_dvd`).
/-- Unlabelled claims, EP1054.tex lines 2157–2181 (proof of Theorem 1.4). "For `e\geq2`, put
`L=\lcm\bigl(\{r:r\mid n,\ r<e\}\bigr),\quad C=\sum_{r\mid L, r<e}\frac Lr,\quad R=\sigma(n)-N`.
The divisors of `L` below `e` are exactly the divisors of `n` below `e`. By Lemma
\ref{lem:fm-modulus}, `R=\frac nL C`. Since every prime `p\leq P` divides `\sigma(n)` but not `N`,
the integer `R=(n/L)C` is `P`-rough. Writing `u=n/L`, both `u` and `C` are therefore `P`-rough.
Since `e\leq F<P` and `e\mid n=Lu`, every prime-power divisor of `e` already divides `L`.
Consequently `n=Lu,\quad \gcd(u,P\#)=1,\quad \gcd(C,P\#)=1, \quad e\mid L\mid \Lambda(F)`. As before
`C\geq L\geq2`, so `C>P`. On the other hand, `C\leq\sigma(L) \leq L\prod_{p\leq F}(1-\frac1p)^{-1}
\ll L\log F`."

Encoding: deterministic, for arbitrary naturals `P > F` (in the proof `P = subP ρ X`,
`F = subF ρ X`, and `F < P` is `UpperTails.Claim_SubexpFltP`), a cofactor `2 ≤ e ≤ F`, `d ≥ 1`,
`n = e d`, a `P`-rough target `N = F_e(d)`, and a good source `n`. With `L = Mlcm e d` and
`C = Csum e d` (`Defs`: `Dset e d` is exactly `{r ∣ n : r < e}`), the conclusions are: `L ∣ n`
(the paper's `n = L u`: with it, `u := n / L` below is an exact cofactor, `n = L · (n / L)`, not a
truncated `ℕ`-quotient), `σ(n) = N + (n/L) C` (i.e. `R = (n/L) C`, no truncated subtraction),
`gcd(n/L, P#) = 1`, `gcd(C, P#) = 1`, `e ∣ L`, `L ∣ Λ(F)`, `P < C`, `C ≤ σ(L)`. The last
`≪ L log F` step is folded into `Eq_MovingKernelLowerBound`. The context hypothesis `n ≤ tN` is not
used and is omitted. -/
def UpperTails.Claim_SubexpWitnessStructure : Prop :=
  ∀ P Fb N e d : ℕ, Fb < P → 2 ≤ e → e ≤ Fb → 1 ≤ d → N = F e d → IsRough P N →
    (∀ p : ℕ, p.Prime → p ≤ P → p ∣ sig (e * d)) →
      Mlcm e d ∣ e * d ∧
        sig (e * d) = N + e * d / Mlcm e d * Csum e d ∧
        Nat.Coprime (e * d / Mlcm e d) (primorial P) ∧
        Nat.Coprime (Csum e d) (primorial P) ∧
        e ∣ Mlcm e d ∧ Mlcm e d ∣ lcmUpTo Fb ∧
        P < Csum e d ∧ Csum e d ≤ sig (Mlcm e d)

-- deps: UpperTails.Claim_SubexpWitnessStructure, UpperTails.Claim_SubexpFltP, Std_Mertens3
--       (`∏_{p≤F}(1-1/p)^{-1} ≪ log F`), `log F ≤ W`.
/-- `eq:moving-kernel-lower-bound`, EP1054.tex lines 2176–2185 (proof of Theorem 1.4). "As before
`C\geq L\geq2`, so `C>P`. On the other hand, `C\leq\sigma(L) \leq L\prod_{p\leq F}\left(1-\frac1p
\right)^{-1} \ll L\log F`. There is therefore an absolute constant `C_0>0` such that
`L>\frac P{C_0W}`."

Encoding: `∃ C₀ > 0` (absolute, so before `ρ`); for every `ρ > 0` and all sufficiently large `X`,
every configuration of `UpperTails.Claim_SubexpWitnessStructure` with `P = subP ρ X`,
`F = subF ρ X` has `P/(C₀ W) < L = Mlcm e d`. Smallness of `ρ` and the context hypothesis
`n ≤ tN` are not used and are omitted. -/
def Eq_MovingKernelLowerBound : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ρ : ℝ, 0 < ρ → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    ∀ N e d : ℕ, 2 ≤ e → e ≤ subF ρ X → 1 ≤ d → N = F e d → IsRough (subP ρ X) N →
      (∀ p : ℕ, p.Prime → p ≤ subP ρ X → p ∣ sig (e * d)) →
        (subP ρ X : ℝ) / (C₀ * subW ρ X) < (Mlcm e d : ℝ)

-- deps: Chebyshev (Mathlib `Chebyshev.psi_eq_log_lcmUpto`, `Chebyshev.psi_le_const_mul_self`:
--       `log Λ(F) ≪ F`; `primorial_le_four_pow`: `log P# ≪ P`); `F, P = o(log X)`; complete periods
--       modulo `P#`, with Notation_Delta_density (S1: `φ(P#)/P# = Δ(P)`).
/-- Unlabelled claims, EP1054.tex lines 2187–2197 (proof of Theorem 1.4). "Uniformly for
`L\mid \Lambda(F)`, `\log L\leq\log \Lambda(F)\ll F=o(\log X), \quad \log(P\#)\ll P=o(\log X)`. It
follows that `tX/L\geq P\#` for all sufficiently large `X`. Complete periods modulo `P\#`
consequently give `\#\{u\leq tX/L:\gcd(u,P\#)=1\} \leq\frac{2tX\Delta(P)}{L}`."

Encoding: for every `ρ > 0`, `0 < ε < 1`, all sufficiently large `X` and every `L ∣ Λ(F)`
(so `L ≥ 1`): `P# ≤ tX/L` and `#{1 ≤ u ≤ tX/L : gcd(u, P#) = 1} ≤ 2 t X Δ(P)/L`. -/
def UpperTails.Claim_SubexpCoprimeCount : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    ∀ L : ℕ, L ∣ lcmUpTo (subF ρ X) →
      (primorial (subP ρ X) : ℝ) ≤ subT ε ρ X * X / L ∧
        (cnt {u : ℕ | Nat.Coprime u (primorial (subP ρ X))} (subT ε ρ X * X / L) : ℝ) ≤
          2 * subT ε ρ X * X * Delta (subP ρ X) / L

-- deps: UpperTails.Claim_SubexpWitnessStructure (`n = L u`, `e ∣ L ∣ Λ(F)`, `u` coprime to `P#`),
--       Eq_MovingKernelLowerBound (`L > P/(C₀W)`), UpperTails.Claim_SubexpCoprimeCount,
--       UpperTails.Claim_SubexpFltP; at most `τ(L)` cofactors `e ∣ L` per `L`.
/-- Unlabelled display (first half), EP1054.tex lines 2198–2204 (proof of Theorem 1.4). "For each
fixed `L`, the admissible cofactors satisfy `e\mid L`, so there are at most `\tau(L)` possibilities.
Hence \eqref{eq:moving-kernel-lower-bound} and Lemma \ref{lem:kernel-tails} bound the entire
remaining low-cofactor witness count by `2tX\Delta(P) \sum_{L\mid \Lambda(F), L>P/(C_0W)}
\frac{\tau(L)}L`".

Encoding: `∃ C₀ > 0` (the constant of `eq:moving-kernel-lower-bound`), then for every `ρ > 0`,
`0 < ε < 1` and all sufficiently large `X`: `lowWitness ≤ 2 t X Δ(P) · S(F, P/(C₀ W))` (the sum is
`Skernel`). -/
def UpperTails.Claim_SubexpLowCofactorSum : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      (lowWitness ε ρ X : ℝ) ≤
        2 * subT ε ρ X * X * Delta (subP ρ X) *
          Skernel (subF ρ X) ((subP ρ X : ℝ) / (C₀ * subW ρ X))

-- deps: UpperTails.Claim_SubexpLowCofactorSum, Eq_MovingKernelTail (with `J = log P`, `e^J = P`,
--       `C = C₀`); `J → ∞` as `X → ∞`.
/-- Unlabelled display (second half), EP1054.tex lines 2202–2207 (proof of Theorem 1.4).
"`2tX\Delta(P) \sum_{L\mid \Lambda(F), L>P/(C_0W)}\frac{\tau(L)}L
\leq X\Delta(P)\exp\{-\varepsilon W+o(W)\} =o(X\Delta(P))`."

Encoding: the sharper middle form: for every `ρ > 0`, `0 < ε < 1`, `η > 0` and all sufficiently
large `X`, `lowWitness ≤ X Δ(P) exp(−εW + ηW)`; `o(XΔ(P))` follows since `W → ∞`. -/
def UpperTails.Claim_SubexpLowCofactor : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ η : ℝ, 0 < η →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      (lowWitness ε ρ X : ℝ) ≤
        X * Delta (subP ρ X) * Real.exp (-(ε * subW ρ X) + η * subW ρ X)

-- deps: the definitions (`t^{k+1} F^{1-k} = e^{[2-(k+1)ε+o(1)]W}`), Std_Mertens3 (`Δ(P) ≍ 1/J`),
--       `log J = o(W)`. The count bound it is applied to is Eq_LargeCount (lem:moment, `A = t`,
--       `E = F`).
/-- Unlabelled display, EP1054.tex lines 2209–2218 (proof of Theorem 1.4). "Choose a fixed integer
`k\geq2` so large that `(k+1)\varepsilon>2`. Lemma \ref{lem:moment} bounds the targets with a
witness `n\leq tN` and cofactor `e>F` by `C_kt^{k+1}F^{1-k}X`. After division by `X\Delta(P)`, this
is at most `O_k\left(J\exp\{[2-(k+1)\varepsilon+o(1)]W\}\right)=o(1)`."

Encoding: the analytic content `t^{k+1} F^{1-k} / Δ(P) → 0` (the fixed factor `C_k` is absorbed in
`η`), for every `ρ > 0`, `0 < ε < 1`, and every integer `k ≥ 2` with `(k+1) ε > 2`. -/
def UpperTails.Claim_SubexpLargeCofactor : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ, 2 ≤ k → 2 < ((k : ℝ) + 1) * ε →
    ∀ η : ℝ, 0 < η → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      subT ε ρ X ^ (k + 1) * (subF ρ X : ℝ) ^ (1 - (k : ℝ)) ≤ η * Delta (subP ρ X)

-- deps: Eq_SharpRoughTargetCount, UpperTails.Claim_RoughNonsquarefree (y = P),
--       UpperTails.Claim_SubexpBadPairs, UpperTails.Claim_SubexpCofactorOne,
--       UpperTails.Claim_SubexpLowCofactor, UpperTails.Claim_SubexpLargeCofactor with
--       Eq_LargeCount (lem:moment), Lem_AnalyticOddRepresentability (P-rough targets are odd),
--       f_mem_Fform (Basic.lean: the least representation is an F-form witness, so no witness
--       with e*d ≤ t N forces f N > t N).
/-- Unlabelled claim, EP1054.tex lines 2219–2224 (proof of Theorem 1.4). "Thus a positive proportion
of the squarefree targets in \eqref{eq:sharp-rough-target-count} has no representation with
`n\leq tN`. These targets are odd. Lemma \ref{lem:analytic-odd-representability} discards only
`o(X/\log\log\log X)=o(X\Delta(P))` further targets as unrepresented. Consequently a positive
proportion still survives, without any use of the finite representability computation."

Encoding: `∃ ρ₀ > 0` (the fixed small `ρ` of line 2113, depending only on `lem:sigma-rate`), then
for every `0 < ρ ≤ ρ₀` and every `0 < ε < 1`: `∃ c > 0, ∃ X₀, ∀ X ≥ X₀`,
`#{X/2 < N ≤ X : N ∈ 𝓡, N squarefree, f(N) > t N} ≥ c X / log log log X`. (The survivors are also
`P`-rough; that is not needed downstream and is dropped.) -/
def UpperTails.Claim_SubexpCore : Prop :=
  ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      c * X / logIt 3 X ≤
        (cntHalf {N : ℕ | N ∈ R ∧ Squarefree N ∧ subT ε ρ X * (N : ℝ) < (f N : ℝ)} X : ℝ)

-- deps: the definitions (`log t = (1-ε)W`, `J = (1+o(1)) log log log X`,
--       `log J = (1+o(1)) log log log log X`).
/-- Unlabelled display, EP1054.tex lines 2224–2229 (proof of Theorem 1.4). "Finally,
`\log t =\left(\frac{1-\varepsilon}{\sqrt2}+o(1)\right) \sqrt{(\log\log\log X)(\log\log\log\log X)}`."

Encoding: relative `o(1)`: for every `ρ > 0`, `0 < ε < 1`, `η > 0`, eventually
`|log t − (1-ε)/√2 · √(log₃X · log₄X)| ≤ η √(log₃X · log₄X)`. -/
def UpperTails.Claim_SubexpLogT : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ η : ℝ, 0 < η →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      |Real.log (subT ε ρ X) - (1 - ε) / Real.sqrt 2 * Real.sqrt (logIt 3 X * logIt 4 X)| ≤
        η * Real.sqrt (logIt 3 X * logIt 4 X)

-- deps: UpperTails.Claim_SubexpLogT; `log_k N = log_k X + o(1)` uniformly for `X/2 < N ≤ X`.
/-- Unlabelled claim, EP1054.tex lines 2230–2233 (proof of Theorem 1.4). "Choose `\varepsilon`
sufficiently small in terms of `\eta`. For `X/2<N\leq X`, replacing `X` by `N` in these iterated
logarithms changes the right-hand side by `o(1)` relative to its main term. This proves
\eqref{eq:subexp-growth}."

Encoding: the threshold comparison that converts `f(N) > tN` into the `N`-dependent threshold of
`eq:subexp-growth`: `∀ η > 0, ∃ ε₀ ∈ (0,1), ∀ 0 < ε ≤ ε₀, ∀ ρ > 0`, eventually in `X`, every natural
`N` with `X/2 < N ≤ X` has `exp[(1/√2 − η) √(log₃N · log₄N)] ≤ t`. -/
def UpperTails.Claim_SubexpThreshold : Prop :=
  ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ ρ : ℝ, 0 < ρ → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ N : ℕ, X / 2 < (N : ℝ) → (N : ℝ) ≤ X →
        Real.exp ((1 / Real.sqrt 2 - η) * Real.sqrt (logIt 3 (N : ℝ) * logIt 4 (N : ℝ))) ≤
          subT ε ρ X

end Principia.Erdos1054
