/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

/-!
# Erdős Problem 1054 — the objects of the collaboration paper `EP1054.tex`

This module fixes the definitions every other `Principia.Erdos1054` module states its results
about. Source: `Campaigns/Erdos-1054/collab-paper/EP1054.tex` (Chae, Fraiture, Hou, Kovač, Kudeba,
Shakov, Vidal), Overleaf export of 2026-09-25.

**The core objects are verbatim copies** of the ones in the comparator-certified masters
(`Erdos1054_3rdMomentProof.lean`, namespace `Represented`): `F`, `g`, `prefixSumDivisors`, `IsRep`,
`R`, `f`. Keeping the bodies identical is what lets a later bridge to those masters be `rfl`.

## Junk values — read before stating anything about `f`

`f N := sInf {m | 1 ≤ m ∧ IsRep N m}` is `0` when `N ∉ R` (the paper's `f` is only defined on `R`).
So every counting or density statement about `f` must conjoin `N ∈ R`; otherwise a set such as
`{N | f N ≤ δ N}` silently contains every unrepresented `N`.

## Counting convention

`cnt S X` counts `1 ≤ N ≤ ⌊X⌋` in `S`. The paper's lower/upper densities are the `liminf`/`limsup`
of `cnt S X / X` along the integers; the sequence lies in `[0, 1]`, so both are well defined.
-/

namespace Principia.Erdos1054

open Finset Filter Real
open scoped Topology

/-! ## The divisor-prefix objects (verbatim from the masters) -/

/-- `F e d`: the sum of the divisors of `e * d` that are `≤ d` — the divisor-prefix sum of `e * d`
whose final divisor is `d`. The integer `e` is the *cofactor* of `d` in `n = e * d`. -/
def F (e d : ℕ) : ℕ := ∑ q ∈ (e * d).divisors.filter (· ≤ d), q

/-- `g e n = ∑_{r ∣ n, r ≥ e} 1 / r`, the complementary reciprocal sum. -/
noncomputable def g (e n : ℕ) : ℝ := ∑ r ∈ n.divisors.filter (e ≤ ·), (1 : ℝ) / r

/-- Sum of the `k` smallest divisors of `m`. -/
noncomputable def prefixSumDivisors (m k : ℕ) : ℕ :=
  ((m.divisors.sort (· ≤ ·)).take k).sum

/-- `N` is a divisor-prefix sum of `m`: the sum of the first `k` divisors, `1 ≤ k ≤ τ(m)`. -/
def IsRep (N m : ℕ) : Prop :=
  ∃ k, 1 ≤ k ∧ k ≤ m.divisors.card ∧ N = prefixSumDivisors m k

/-- The set `𝓡` of represented integers. -/
def R : Set ℕ := {N | ∃ m, 1 ≤ m ∧ IsRep N m}

/-- `f N` = least `m` representing `N`. **Junk value `0` off `R`** — see the module docstring. -/
noncomputable def f (N : ℕ) : ℕ := sInf {m | 1 ≤ m ∧ IsRep N m}

/-! ## Arithmetic functions -/

/-- `σ(n)`, the sum of the divisors of `n`. -/
abbrev sig (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

/-- `s(n) = σ(n) − n`, the sum of the proper divisors (truncated subtraction; `σ n ≥ n`). -/
abbrev aliquot (n : ℕ) : ℕ := sig n - n

/-- `σ_j(n)`: the prefix sum of all but the `j` largest divisors of `n` (`0` once `j ≥ τ(n)`). -/
noncomputable def sigmaPrefix (j n : ℕ) : ℕ :=
  if j < n.divisors.card then prefixSumDivisors n (n.divisors.card - j) else 0

/-- `h(n) = σ(n)/n`, the abundancy index. -/
noncomputable def abundancy (n : ℕ) : ℝ := (sig n : ℝ) / n

/-! ## Counting and densities -/

open Classical in
/-- `cnt S X = #{1 ≤ N ≤ X : N ∈ S}`. -/
noncomputable def cnt (S : Set ℕ) (X : ℝ) : ℕ := ((Finset.Icc 1 ⌊X⌋₊).filter (· ∈ S)).card

/-- Lower asymptotic density `liminf_{X → ∞} #(S ∩ [1, X]) / X`. -/
noncomputable def lowerDens (S : Set ℕ) : ℝ :=
  liminf (fun X : ℕ => (cnt S X : ℝ) / X) atTop

/-- Upper asymptotic density `limsup_{X → ∞} #(S ∩ [1, X]) / X`. -/
noncomputable def upperDens (S : Set ℕ) : ℝ :=
  limsup (fun X : ℕ => (cnt S X : ℝ) / X) atTop

/-- `S` has natural density `d`. -/
def HasDens (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun X : ℕ => (cnt S X : ℝ) / X) atTop (𝓝 d)

/-- `#(S ∩ [1, X]) = o(X)`: density zero, stated without any limit object. -/
def DensZero (S : Set ℕ) : Prop := HasDens S 0

/-! ## Prime-product notation (paper, §1 "Notation") -/

/-- `y`-smooth: every prime factor is `≤ y` (so `1` is smooth). -/
def IsSmooth (y : ℝ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, (p : ℝ) ≤ y

/-- `y`-rough: every prime factor is `> y` (so `1` is rough). -/
def IsRough (y : ℝ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, y < (p : ℝ)

/-- `y#`, the product of the primes `≤ y`. -/
noncomputable def primorialR (y : ℝ) : ℕ := primorial ⌊y⌋₊

/-- `Δ(y) = ∏_{p ≤ y} (1 − 1/p)`, the density of integers coprime to `y#`. -/
noncomputable def Delta (y : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

/-- `Λ(u) = lcm(1, …, ⌊u⌋)`. -/
noncomputable def lcmUpTo (u : ℝ) : ℕ := (Finset.Icc 1 ⌊u⌋₊).lcm id

/-- Euler's constant `γ`. -/
noncomputable abbrev eulerGamma : ℝ := Real.eulerMascheroniConstant

/-- The `k`-fold iterated logarithm `log_k`. -/
noncomputable def logIt (k : ℕ) (x : ℝ) : ℝ := Real.log^[k] x

/-- The upper-tail scale `L(A) = log log log A / (log A · log log A)`. -/
noncomputable def Lscale (A : ℝ) : ℝ := logIt 3 A / (logIt 1 A * logIt 2 A)

/-! ## The exact forced modulus (paper §2, before `lem:fm-modulus`) -/

/-- `D = {j : 1 ≤ j < e, j ∣ e d}`, the divisors of `n = e d` below `e`. -/
def Dset (e d : ℕ) : Finset ℕ := (Finset.Ico 1 e).filter (· ∣ e * d)

/-- `M = lcm(D)`. -/
def Mlcm (e d : ℕ) : ℕ := (Dset e d).lcm id

/-- `C = ∑_{j ∈ D} M / j`. -/
def Csum (e d : ℕ) : ℕ := ∑ j ∈ Dset e d, Mlcm e d / j

/-- `K_{e,d} = (e / gcd(e, M)) · C`, the exact forced modulus. -/
def Kmod (e d : ℕ) : ℕ := e / Nat.gcd e (Mlcm e d) * Csum e d

/-! ## Cofactor ranges and representation counts -/

/-- `F_e(ℕ) = {F e d : d ≥ 1}`. -/
def Frange (e : ℕ) : Set ℕ := {N | ∃ d, 1 ≤ d ∧ N = F e d}

/-- `G_E = ⋃_{1 ≤ e ≤ E} F_e(ℕ)`. -/
def Gcov (E : ℕ) : Set ℕ := {N | ∃ e d, 1 ≤ e ∧ e ≤ E ∧ 1 ≤ d ∧ N = F e d}

open Classical in
/-- `r_t(N) = #{(e, d) ∈ ℕ² : F_e(d) = N, e d ≤ t N}` (with `e, d ≥ 1`). -/
noncomputable def rt (t : ℝ) (N : ℕ) : ℕ :=
  (((Finset.Icc 1 ⌊t * N⌋₊) ×ˢ (Finset.Icc 1 ⌊t * N⌋₊)).filter
    (fun p => F p.1 p.2 = N ∧ ((p.1 * p.2 : ℕ) : ℝ) ≤ t * N)).card

open Classical in
/-- `r*_t(N)`: as `r_t(N)` but with cofactor `e ≥ 2` (proper divisor-prefix sums only). -/
noncomputable def rtStar (t : ℝ) (N : ℕ) : ℕ :=
  (((Finset.Icc 2 ⌊t * N⌋₊) ×ˢ (Finset.Icc 1 ⌊t * N⌋₊)).filter
    (fun p => F p.1 p.2 = N ∧ ((p.1 * p.2 : ℕ) : ℝ) ≤ t * N)).card

end Principia.Erdos1054
