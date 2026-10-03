/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MinorArcBound
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

/-!
# The spine of Helfgott's OWN route: §7.4 with the smoothings kept

**EVERY LINK BELOW IS OPEN. This file proves the COMPOSITION only.** Nothing here proves any part
of ternary Goldbach, of `Principia.Erdos1054.Cite_Helfgott_weighted`, or of
`TernaryLogCountLower`; every theorem that concludes `Cite_Helfgott_weighted` carries the six
links as hypotheses.

## Why this file exists

`Spine.lean` reduced the target to constant weights and sharp cutoffs. Two of its links are now
measured infeasible at `10^27`: with sharp cutoffs Platt's verified height covers only
`q ≤ ~800–3800` of the `q ≤ 300000` needed, and the minor arc at the chain cutoffs is `≥ 133×`
short. Helfgott avoids both by **smoothing**, and `Cite_Helfgott_weighted` quantifies its weights
**existentially**, so his smoothing is admissible. This file is the spine of *his* route,
arXiv:1312.7748 §7.4 (`ternvin.tex` 5313–5402), with every analytic step a named `Prop` and the
weights `ηp` (his `η₊`) and `ηs` (his `η_*`) left as parameters.

```
  PlattGRH ──► MajorLowerSmooth (7.25)      MinorUpperSmooth (7.48)
                   │  ≥ 1.058259 x²/49          │  ≤ 0.97392 x²/49
  CircleIdSmooth ──┼── arc split (PROVED, needs Summ) ──┤
     (7.49)        ▼                                     ▼
          weighted_lower :  0.084339 x²/49 ≤ tripleW          (the major − minor margin)
                   │  PrimePowerSmooth (7.50):  citeSum ≥ tripleW − 7.3306 N^{3/2} log N
                   ▼  x ≥ (490/989)N (from π > 3.14), N^{3/2} log N ≤ N²/10¹¹ (log_le_rt32)
          cite_of_smooth :  Principia.Erdos1054.Cite_Helfgott_weighted
```

## The constants, all re-verified (mpmath, 40 digits; exact rationals where stated)

* `x = helfgottX N = N/(2 + 9/(196√(2π)))`, `x/N = 0.495461871935…`. The file uses only
  `√(2π) ≥ 5/2` (from `Real.pi_gt_d2 : 3.14 < π`), i.e. `x ≥ (490/989) N`, `490/989 = 0.495450…`.
* `1.058259 − 0.97392 = 0.084339` exactly (Helfgott prints `≥ 0.08433`).
* `0.084339 · (490/989)² / 49 = 4132611/9781210000 = 0.000422505…`: margin `5.05·10⁻⁷` over
  `0.000422`. (With `x/N ≥ 0.4954` it is `0.00042242`, margin `4.2·10⁻⁷`.)
* The (7.50) error is `7.3306 · log N/√N = 1.44·10⁻¹¹` in units of `N²` at `N = 10^27`
  (`log N/√N = 1.97·10⁻¹²`); `err_le` proves it is `≤ 7.3306·10⁻¹¹`, via `log N ≤ 9.01 N^{1/32}`
  and `2.64^30 = 4.45·10¹² ≥ 9.01·10¹¹`. Margin left: `5.05·10⁻⁷ − 7.33·10⁻¹¹ > 0`.
* `3 · 1.079955² · 1.414 · (1.4263 · 1.03883) = 7.330597 ≤ 7.3306`; `4(log 2)²(2/e) = 1.413990 ≤
  1.414`; `1 + 2.06440727(1 + (4/π) log 200)/200 = 1.0799548 ≤ 1.079955`.

## THE LINKS, AND HOW FAR THE LIBRARY REACHES EACH

* `SupBounds` — (7.3), (7.19). Statements about Helfgott's two functions; not deep (map §2.4).
* `Summ` — absolute summability of `Λ(n)η(n/x)` at the scales used. **Derivable**: see below.
* `CircleIdSmooth` — (7.49). *Plausibly within reach.* `CircleMethod.circleMethodIdentity_holds`
  is its sharp-weight analogue, and **half of it transfers verbatim**: the orthogonality step
  (`MinorArc.integral_e`) and the reindexing (`CircleMethod.sum_third`, `double_sum_eq`, whose two
  vanishing mechanisms — `Λ 0 = 0` and the guard `p + q < N` — are untouched by weights). **The
  other half does not**: `smSum` is an *infinite* sum (neither `η₊` nor `η_*` is compactly
  supported: `h_H` is Mellin-band-limited, `η_*` has a Gaussian tail), so the finite
  `sum_cube`/`integral_finsetSum` steps must be replaced by a Cauchy product of absolutely
  summable series and an interchange of `tsum` and integral under `Summ`. New Lean, standard
  mathematics. (7.49) is TRUE under `Summ` (absolute convergence justifies the interchange) and
  can FAIL without it: a non-summable weight makes `smSum` junk `0` (`smSum_junk`), so the right
  side is `0` while `tripleW` need not be.
* `MajorLowerSmooth` — (7.25). **This IS Helfgott's major-arc paper** (arXiv:1305.2897, with
  Platt's verification), the only link that uses `PlattGRH`, which is therefore a premise *inside*
  it. The analysis in `MajorFromPlatt`/`FareyKernel`/`KernelLinks` is built on the sharp-cutoff
  `Spine.expSum` and does not transfer; its Platt interface (`PlattGRHAt`, `ZeroFreeBoxAbove`,
  `zeroBoxes_of_plattGRHAt`, `AdmissibleHeight`) is weight-agnostic and does.
* `MinorUpperSmooth` — (7.48). **This IS Helfgott's minor-arc paper** (arXiv:1205.5252) plus §5–§6
  of the ternary paper (Ramaré's large sieve, the ℓ²-over-arcs bound). Uses no `L`-function
  information. Nothing in the library is close (map §4.3, §4.6).
* `PrimePowerSmooth` — (7.50). *Plausibly within reach, but not in the stated form.* The transfer
  from `PrimePower.primePowerRemoval_ten` is exact up to one step: on the same index set,
  `tripleW − citeSum` is the sum over the *bad* triples of `ΛΛΛ·w` with `|w| ≤ 1.079955²·1.414`,
  and `lambdaTriple − ternaryLogCount` is the sum of `ΛΛΛ` over the same triples, so
  `tripleW − citeSum ≤ 1.649153·(lambdaTriple − ternaryLogCount)` and
  `PrimePower.lambdaTriple_sub_le` finishes. But the library's `ψ − θ ≤ 2√x log x` (Mathlib) carries
  an extra `log`, giving `≈ 13.7 N^{3/2}(log N)²` (`≈ 1.7·10⁻⁹ N²`, still far inside the
  `5·10⁻⁷` margin). The stated `7.3306 N^{3/2} log N` is Helfgott's arithmetic with
  Rosser–Schoenfeld: it needs `ψ(N) ≤ 1.03883 N` (RS Thm 12 — in this chain only as the cited
  input `Cite_RosserSchoenfeld_psi`; Mathlib's `log 4 = 1.386` pushes the constant to `≈ 9.8`) and
  a log-free `ψ − θ < 1.4262√N` (RS Thm 13; not in Mathlib, though derivable in principle from
  `θ(y) ≤ y log 4` through `ψ − θ = ∑_{k≥2} θ(x^{1/k})`). So a `(log N)²` variant of this link is
  dischargeable from the library today; the stated one is not.

## What `Summ` is, and why it is the weakest possible

`smSum` is a `tsum`, and a `tsum` of a non-summable family is junk `0` in Mathlib. `Summ` asks for
absolute summability of `Λ(n)η(n/x)` **only at the scales `x = helfgottX N` the links use**.

1. It is exactly what makes `smSum` Helfgott's object: without it `smSum ≡ 0` (`smSum_junk`).
2. It makes the integrands continuous (`continuous_smSum`, by `continuous_tsum`), so every integral
   in the links is a genuine Lebesgue integral of a continuous function on `(0,1]`.
3. The composition uses it exactly once: the major/minor split `∫_{(0,1]} = ∫_𝔐 + ∫_𝔪` needs the
   integrand integrable (`MeasureTheory.integral_inter_add_sdiff`).
4. **It is redundant given the other links.** `summ_of_major` proves
   `PlattGRH → MajorLowerSmooth ηp ηs → Summ ηp ηs`: a non-summable weight makes the major-arc
   integral `0 < 1.058259 x²/49`. So the weakest side condition the composition needs is **none**,
   and `cite_no_summ` is the composition without it. `Summ` stays in `cite_of_smooth` because the
   brief asked for it and because it names what the analytic links will consume.

## THE ADVERSARIAL PASS — every new `Prop` must constrain

(a) **Zero weights.** `zero_rest` proves `SupBounds 0 0`, `Summ 0 0`, `CircleIdSmooth 0 0`,
    `MinorUpperSmooth 0 0` and `PrimePowerSmooth 0 0` — **five of the six links are satisfied by
    the zero weights**. Only `MajorLowerSmooth` rejects them (`major_zero`), and exactly as far as
    Platt holds: `major_zero_iff : MajorLowerSmooth 0 0 ↔ ¬ PlattGRH`. So all of the content sits
    in the major-arc link, and the links are not jointly satisfiable by junk (zero or
    non-summable: `major_fails` covers both).
(b) **The minor set is not trivial.** `minor_nonempty` exhibits `α = 10⁻⁶ ∈ (0,1] ∖ 𝔐_{8,r₀}` for
    every `x ≥ 10^26`, and — quantitatively — `vol_major_le` bounds the major arcs' total measure
    on `(0,1]` by `1.44·10¹²/x`, so `minor_large` gives `vol(minorSet x) ≥ 1 − 1.44·10⁻¹⁴`: (7.48)
    integrates over all but a `10⁻¹⁴` sliver of the circle. `one_mem_major` shows the major set is
    nonempty, so (7.25) is not a statement about an empty integral either. Unlike `Spine`'s
    `MajorArcs P Q`, the arcs here have **no free cutoff**: `majArcs` is Helfgott's `𝔐_{8,150000}`
    verbatim, so the "choose cutoffs that make the split buy nothing" attack of
    `Spine.minorSet_one_one` has no surface.
(c) **Platt is not a free rider.** `cite_of_smooth` does not compile with `grh` deleted. A scratch
    probe (not kept in the library) tried four ways and got four errors: the verbatim proof with
    the binder deleted (`Unknown identifier grh`); `grh := _` (`don't know how to synthesize
    placeholder for argument grh`, goal `Spine.PlattGRH`); `grh := by assumption` (`assumption`
    failed); and `mj N hodd hN` used as if Platt were not inside the link (`Application type
    mismatch: N has type ℕ but is expected to have type Spine.PlattGRH`). A positive control with
    `grh` restored compiled. The full transcript is in `GateSmoothed.lean`. Honest caveat, as in
    `Spine`: because `MajorLowerSmooth` *is* `PlattGRH → …`, supplying it together with `grh` is
    equivalent to supplying the Platt-free bound. The reduction to Platt becomes real only when
    `MajorLowerSmooth` itself is proved.

## Faithfulness notes

* `majArcs x` is `ternvin.tex` `eq:majdef` with `δ₀ = 8`, `r = r₀ = 150000`: odd `q ≤ r` with
  half-width `δ₀r/(2qx)`, even `q ≤ 2r` with half-width `δ₀r/(qx)`, `(a,q) = 1`, OPEN intervals,
  `a` ranging over `ℤ` (so the set is 1-periodic, and it is intersected with `Set.Ioc 0 1`, the
  convention of `Spine.majorSet`). `q = 0` is excluded explicitly (`q ∈ Set.Icc 1 _`).
* `MajorLowerSmooth` bounds the **real part**. The integral is real (the arcs are symmetric under
  `α ↦ −α` and `S_η(−α) = conj S_η(α)` for real `η`), so this is no weakening in substance.
* `tripleW` puts the weights at `nᵢ/x`. Helfgott's printed (7.49)/(7.50) omit the `/x`; that is a
  typo (map §2.5), and `Inputs.lean` already corrects it.
* `citeSum` is the body of `Cite_Helfgott_weighted` **copied verbatim**, and `cite_iff` checks the
  copy by `Iff.rfl`: if one character of the copy diverged, that proof would not typecheck.
-/

namespace Principia.Common.TernaryGoldbach.Smooth

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction
open Principia.Erdos1054 (helfgottX Cite_Helfgott_weighted)

/-! ## The objects -/

/-- **Helfgott's smoothed exponential sum** `S_η(α, x) = ∑_n Λ(n) η(n/x) e(nα)` (`ternvin.tex`
line 707), an **infinite** sum over `n : ℕ`. The `n = 0` term vanishes because `Λ 0 = 0`. It is
Helfgott's object only when `Λ(n)η(n/x)` is summable; otherwise Mathlib's `tsum` is junk `0`
(`smSum_junk`), which is why `Summ` exists. -/
noncomputable def smSum (η : ℝ → ℝ) (x α : ℝ) : ℂ :=
  ∑' n : ℕ, ((Λ n : ℝ) : ℂ) * ((η ((n : ℝ) / x) : ℝ) : ℂ) * e ((n : ℝ) * α)

/-- **The major arcs `𝔐_{δ₀,r}`** (`ternvin.tex` `eq:majdef`, line 730), as a 1-periodic subset
of `ℝ`: open intervals of half-width `δ₀r/(2qx)` about `a/q` for odd `q ≤ r`, and of half-width
`δ₀r/(qx)` for even `q ≤ 2r`, with `(a,q) = 1`. -/
def arcs (δ₀ : ℝ) (r : ℕ) (x : ℝ) : Set ℝ :=
  (⋃ q ∈ Set.Icc 1 r, ⋃ (_ : Odd q), ⋃ a : ℤ, ⋃ (_ : Int.gcd a q = 1),
      Set.Ioo ((a : ℝ) / q - δ₀ * r / (2 * q * x)) ((a : ℝ) / q + δ₀ * r / (2 * q * x))) ∪
    (⋃ q ∈ Set.Icc 1 (2 * r), ⋃ (_ : Even q), ⋃ a : ℤ, ⋃ (_ : Int.gcd a q = 1),
      Set.Ioo ((a : ℝ) / q - δ₀ * r / (q * x)) ((a : ℝ) / q + δ₀ * r / (q * x)))

/-- Helfgott's choice: `𝔐_{8, r₀}`, `r₀ = 150000` (§7.4). -/
def majArcs (x : ℝ) : Set ℝ := arcs 8 150000 x

/-- The major arcs on the fundamental domain `(0,1]`. -/
def majorSet (x : ℝ) : Set ℝ := Set.Ioc (0 : ℝ) 1 ∩ majArcs x

/-- The minor arcs `(ℝ/ℤ) ∖ 𝔐_{8,r₀}`, on the fundamental domain `(0,1]`. -/
def minorSet (x : ℝ) : Set ℝ := Set.Ioc (0 : ℝ) 1 \ majArcs x

/-- **The circle-method integrand** `S_{η₊}(α,x)² S_{η_*}(α,x) e(−Nα)` of (7.49). -/
noncomputable def kernS (ηp ηs : ℝ → ℝ) (N : ℕ) (x α : ℝ) : ℂ :=
  smSum ηp x α ^ 2 * smSum ηs x α * e (-(N : ℝ) * α)

/-- **The full Λ-weighted triple sum** `∑_{n₁+n₂+n₃=N, nᵢ ≥ 1} Λ(n₁)Λ(n₂)Λ(n₃) η₊(n₁/x)
η₊(n₂/x) η_*(n₃/x)`, the left side of (7.49). A FINITE sum, in the shape of `Spine.lambdaTriple`:
ordered pairs over `Finset.range N`, the third coordinate the natural `N − p − q`, which is `≥ 1`
exactly when `p + q < N`; `nᵢ = 0` contributes nothing because `Λ 0 = 0`. -/
noncomputable def tripleW (ηp ηs : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N,
    if p + q < N then Λ p * Λ q * Λ (N - p - q) *
      ηp ((p : ℝ) / x) * ηp ((q : ℝ) / x) * ηs (((N - p - q : ℕ) : ℝ) / x) else 0

open Classical in
/-- **The weighted sum of `Cite_Helfgott_weighted`, copied VERBATIM** from
`Principia/Erdos1054/Statements/Inputs.lean` (the body of the `def` at line 307, same binder names,
same `open Classical in`). `cite_iff` proves the copy exact by `Iff.rfl`. -/
noncomputable def citeSum (ηp ηs : ℝ → ℝ) (H : ℕ) : ℝ :=
        ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H,
          if p + q < H ∧ p.Prime ∧ q.Prime ∧ (H - p - q).Prime ∧ Odd p ∧ Odd q ∧ Odd (H - p - q)
          then Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ) *
            ηp ((p : ℝ) / helfgottX H) * ηp ((q : ℝ) / helfgottX H) *
              ηs (((H - p - q : ℕ) : ℝ) / helfgottX H)
          else 0

/-- **The attachment check.** `Cite_Helfgott_weighted` is, *definitionally*, the statement with
`citeSum` in place of its body. Proved by `Iff.rfl`, so the verbatim copy above cannot drift. -/
theorem cite_iff : Cite_Helfgott_weighted ↔
    ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H →
      ∃ ηp ηs : ℝ → ℝ, (∀ u : ℝ, |ηp u| ≤ 1.079955) ∧ (∀ u : ℝ, |ηs u| ≤ 1.414) ∧
        0.000422 * (H : ℝ) ^ 2 ≤ citeSum ηp ηs H :=
  Iff.rfl

/-! ## THE LINKS — every one of them OPEN -/

/-- **Link 0 — the sup norms** (7.3), (7.19): `|η₊|_∞ ≤ 1.079955`, `|η_*|_∞ ≤ 1.414`. The exact
conjuncts of `Cite_Helfgott_weighted`. OPEN (for Helfgott's functions; not deep, map §2.4). -/
def SupBounds (ηp ηs : ℝ → ℝ) : Prop :=
  (∀ u : ℝ, |ηp u| ≤ 1.079955) ∧ (∀ u : ℝ, |ηs u| ≤ 1.414)

/-- **The side condition** — absolute summability of `Λ(n)η(n/x)` at the scales the links use.
The weakest condition that makes `smSum` a genuine sum (`smSum_junk`) and the integrals genuine
(`continuous_smSum`); and it is DERIVABLE from `PlattGRH` and `MajorLowerSmooth`
(`summ_of_major`). OPEN for Helfgott's functions (Gaussian decay makes it easy). -/
def Summ (ηp ηs : ℝ → ℝ) : Prop :=
  ∀ N : ℕ, Odd N → 10 ^ 27 ≤ N →
    Summable (fun n : ℕ => Λ n * |ηp ((n : ℝ) / helfgottX N)|) ∧
      Summable (fun n : ℕ => Λ n * |ηs ((n : ℝ) / helfgottX N)|)

/-- **Link 1 — the circle-method identity (7.49)** (`eq:masd`), at `x = helfgottX N`:
`∑_{n₁+n₂+n₃=N} ΛΛΛ η₊η₊η_* = ∫_{ℝ/ℤ} S_{η₊}(α,x)² S_{η_*}(α,x) e(−Nα) dα`. OPEN; plausibly within
reach (see the module docstring for exactly how far `CircleMethod` transfers). True under `Summ`,
false without it for nonzero weights. -/
def CircleIdSmooth (ηp ηs : ℝ → ℝ) : Prop :=
  ∀ N : ℕ, Odd N → 10 ^ 27 ≤ N →
    ((tripleW ηp ηs N (helfgottX N) : ℝ) : ℂ) =
      ∫ α in Set.Ioc (0 : ℝ) 1, kernS ηp ηs N (helfgottX N) α

/-- **Link 2 — the major arcs (7.25)** (`eq:juventud`): `Re ∫_{𝔐_{8,r₀}} S_{η₊}²S_{η_*}e(−Nα) ≥
1.058259 x²/ϰ`, `ϰ = 49`. OPEN, and it IS Helfgott's major-arc paper. **`PlattGRH` is a premise
inside this `Prop`**: it is the only link that uses Platt (map §3.4). -/
def MajorLowerSmooth (ηp ηs : ℝ → ℝ) : Prop :=
  Spine.PlattGRH → ∀ N : ℕ, Odd N → 10 ^ 27 ≤ N →
    1.058259 * helfgottX N ^ 2 / 49 ≤
      (∫ α in majorSet (helfgottX N), kernS ηp ηs N (helfgottX N) α).re

/-- **Link 3 — the minor arcs (7.48)** (`eq:rozoj`): `∫_{(ℝ/ℤ)∖𝔐_{8,r₀}} |S_{η_*}||S_{η₊}|² ≤
0.97392 x²/ϰ`. OPEN, and it IS Helfgott's minor-arc paper plus §5–§6 of the ternary paper. No
`L`-function input. -/
def MinorUpperSmooth (ηp ηs : ℝ → ℝ) : Prop :=
  ∀ N : ℕ, Odd N → 10 ^ 27 ≤ N →
    (∫ α in minorSet (helfgottX N),
        ‖smSum ηs (helfgottX N) α‖ * ‖smSum ηp (helfgottX N) α‖ ^ 2) ≤
      0.97392 * helfgottX N ^ 2 / 49

/-- **Link 4 — removal of even and non-prime `nᵢ` (7.50)** (`eq:duke`), in the form the
composition needs: the weighted sum of `Cite_Helfgott_weighted` over odd primes is at least
`tripleW − 7.3306 N^{3/2} log N`. OPEN; the stated constant needs `ψ(N) ≤ 1.03883 N` (RS Thm 12,
here only the cited `Cite_RosserSchoenfeld_psi`) and a log-free `ψ − θ ≤ 1.4262√N` (RS Thm 13),
neither in Mathlib, while a `(log N)²` variant is within reach of `PrimePower` today. -/
def PrimePowerSmooth (ηp ηs : ℝ → ℝ) : Prop :=
  ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H →
    tripleW ηp ηs H (helfgottX H) - 7.3306 * ((H : ℝ) * Real.sqrt (H : ℝ)) * Real.log (H : ℝ)
      ≤ citeSum ηp ηs H

/-! ## Arithmetic at the threshold -/

/-- `√(2π) ≥ 5/2`, from `π > 3.14`. -/
theorem sqrt_two_pi_ge : (5 : ℝ) / 2 ≤ Real.sqrt (2 * Real.pi) := by
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  nlinarith [Real.pi_gt_d2]

/-- `helfgottX H ≥ (490/989)·H`. The truth is `0.4954618…·H`; `490/989 = 0.4954499…`. -/
theorem helfX_ge (H : ℕ) : (490 : ℝ) / 989 * H ≤ helfgottX H := by
  have hs := sqrt_two_pi_ge
  have hc0 : (0 : ℝ) < 2 + 9 / (196 * Real.sqrt (2 * Real.pi)) := by positivity
  have h1 : 9 / (196 * Real.sqrt (2 * Real.pi)) ≤ 9 / 490 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hc : 2 + 9 / (196 * Real.sqrt (2 * Real.pi)) ≤ 989 / 490 := by linarith
  rw [Principia.Erdos1054.helfgottX, le_div_iff₀ hc0]
  calc (490 : ℝ) / 989 * H * (2 + 9 / (196 * Real.sqrt (2 * Real.pi)))
      ≤ (490 : ℝ) / 989 * H * (989 / 490) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = H := by ring

/-- `helfgottX H > 0` for `H > 0`. -/
theorem helfX_pos (H : ℕ) (hH : 0 < H) : 0 < helfgottX H := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  exact lt_of_lt_of_le (mul_pos (by norm_num) hHR) (helfX_ge H)

/-- **The (7.50) error is negligible**: `H·√H·log H ≤ H²/10¹¹` for `H ≥ 10^27`. Via
`MinorArcBound.log_le_rt32` (`log H ≤ 9.01·H^{1/32}`, lossy by `1.1 %`), `√H = w³²`, `H = w⁶⁴` with
`w = H^{1/64} ≥ 2.64`, and `2.64³⁰ = 4.45·10¹² ≥ 9.01·10¹¹`. The truth at the threshold is
`1.97·10⁻¹² H²`. (`Spine.log_le_sqrt_div` would give only `H²/10⁴`, which is useless here.) -/
theorem err_le (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    (H : ℝ) * Real.sqrt (H : ℝ) * Real.log (H : ℝ) ≤ (H : ℝ) ^ 2 / 10 ^ 11 := by
  have hlog := MinorArcBound.log_le_rt32 H hH
  have hw0 : 0 ≤ MinorArcBound.rt64 H := MinorArcBound.rt64_nonneg H
  have hwge : (264 : ℝ) / 100 ≤ MinorArcBound.rt64 H := MinorArcBound.rt64_ge H hH
  have hsq : Real.sqrt (H : ℝ) = MinorArcBound.rt64 H ^ 32 := (MinorArcBound.rt64_pow32 H).symm
  have hHw : (H : ℝ) = MinorArcBound.rt64 H ^ 64 := (MinorArcBound.rt64_pow64 H).symm
  have h30 : (901 : ℝ) / 100 * 10 ^ 11 ≤ MinorArcBound.rt64 H ^ 30 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hwge 30)
  have hw98 : (0 : ℝ) ≤ MinorArcBound.rt64 H ^ 98 := pow_nonneg hw0 98
  have hHs : (0 : ℝ) ≤ (H : ℝ) * Real.sqrt (H : ℝ) := by positivity
  calc (H : ℝ) * Real.sqrt (H : ℝ) * Real.log (H : ℝ)
      ≤ (H : ℝ) * Real.sqrt (H : ℝ) * ((901 : ℝ) / 100 * MinorArcBound.rt64 H ^ 2) :=
        mul_le_mul_of_nonneg_left hlog hHs
    _ = (901 : ℝ) / 100 * MinorArcBound.rt64 H ^ 98 := by rw [hsq, hHw]; ring
    _ ≤ MinorArcBound.rt64 H ^ 30 / 10 ^ 11 * MinorArcBound.rt64 H ^ 98 :=
        mul_le_mul_of_nonneg_right (by linarith) hw98
    _ = (H : ℝ) ^ 2 / 10 ^ 11 := by rw [hHw]; ring

/-! ## The analytic facts the composition needs (all proved) -/

/-- The size of one term of `smSum`: `‖Λ(n) η(n/x) e(nα)‖ = Λ(n)|η(n/x)|`. -/
theorem norm_term (η : ℝ → ℝ) (x α : ℝ) (n : ℕ) :
    ‖((Λ n : ℝ) : ℂ) * ((η ((n : ℝ) / x) : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      = Λ n * |η ((n : ℝ) / x)| := by
  rw [norm_mul, norm_mul, e_norm, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]

/-- **Junk, made explicit**: without absolute summability `smSum ≡ 0`. (`ℂ` is finite-dimensional,
so summability of the complex family would force summability of its norms.) -/
theorem smSum_junk (η : ℝ → ℝ) (x : ℝ)
    (hns : ¬ Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) (α : ℝ) : smSum η x α = 0 := by
  unfold smSum
  refine tsum_eq_zero_of_not_summable fun hs => hns ?_
  exact (summable_norm_iff.mpr hs).congr fun n => norm_term η x α n

/-- Under absolute summability, `α ↦ S_η(α,x)` is continuous (Weierstrass M-test). -/
theorem continuous_smSum (η : ℝ → ℝ) (x : ℝ)
    (hs : Summable (fun n : ℕ => Λ n * |η ((n : ℝ) / x)|)) : Continuous (smSum η x) := by
  unfold smSum
  refine continuous_tsum (fun n => ?_) hs (fun n α => le_of_eq (norm_term η x α n))
  exact continuous_const.mul (Spine.continuous_e.comp (continuous_const.mul continuous_id))

/-- The integrand of (7.49) is continuous under absolute summability. -/
theorem continuous_kernS (ηp ηs : ℝ → ℝ) (N : ℕ) (x : ℝ)
    (hp : Summable (fun n : ℕ => Λ n * |ηp ((n : ℝ) / x)|))
    (hs : Summable (fun n : ℕ => Λ n * |ηs ((n : ℝ) / x)|)) :
    Continuous (kernS ηp ηs N x) := by
  unfold kernS
  exact (((continuous_smSum ηp x hp).pow 2).mul (continuous_smSum ηs x hs)).mul
    (Spine.continuous_e.comp (continuous_const.mul continuous_id))

/-- `‖S_{η₊}² S_{η_*} e(−Nα)‖ = |S_{η_*}| |S_{η₊}|²`: the integrand of (7.48). -/
theorem norm_kernS (ηp ηs : ℝ → ℝ) (N : ℕ) (x α : ℝ) :
    ‖kernS ηp ηs N x α‖ = ‖smSum ηs x α‖ * ‖smSum ηp x α‖ ^ 2 := by
  rw [kernS, norm_mul, norm_mul, norm_pow, e_norm, mul_one, mul_comm]

/-- The major arcs are open (a union of open intervals), hence measurable. -/
theorem isOpen_arcs (δ₀ : ℝ) (r : ℕ) (x : ℝ) : IsOpen (arcs δ₀ r x) := by
  unfold arcs
  refine IsOpen.union ?_ ?_ <;>
    exact isOpen_biUnion fun q _ => isOpen_iUnion fun _ => isOpen_iUnion fun a =>
      isOpen_iUnion fun _ => isOpen_Ioo

/-- `𝔐_{8,r₀}` is measurable, so the major/minor split of the integral is legitimate. -/
theorem measurableSet_maj (x : ℝ) : MeasurableSet (majArcs x) :=
  (isOpen_arcs 8 150000 x).measurableSet

/-! ## THE SPINE -/

/-- **The circle-method half: the major − minor margin.** From (7.49), (7.25) and (7.48):
`tripleW ≥ (1.058259 − 0.97392)·x²/49 = 0.084339·x²/49`. Uses `Summ` exactly once, for the
additivity of the integral over the split `(0,1] = 𝔐 ⊔ 𝔪`. -/
theorem weighted_lower (ηp ηs : ℝ → ℝ) (grh : Spine.PlattGRH) (sm : Summ ηp ηs)
    (ci : CircleIdSmooth ηp ηs) (mj : MajorLowerSmooth ηp ηs) (mn : MinorUpperSmooth ηp ηs)
    (N : ℕ) (hodd : Odd N) (hN : 10 ^ 27 ≤ N) :
    0.084339 * helfgottX N ^ 2 / 49 ≤ tripleW ηp ηs N (helfgottX N) := by
  have hint : IntegrableOn (kernS ηp ηs N (helfgottX N)) (Set.Ioc (0 : ℝ) 1) :=
    (continuous_kernS ηp ηs N _ (sm N hodd hN).1 (sm N hodd hN).2).integrableOn_Ioc
  have hsplit := integral_inter_add_sdiff (measurableSet_maj (helfgottX N)) hint
  have heq : ((tripleW ηp ηs N (helfgottX N) : ℝ) : ℂ) =
      (∫ α in majorSet (helfgottX N), kernS ηp ηs N (helfgottX N) α) +
        ∫ α in minorSet (helfgottX N), kernS ηp ηs N (helfgottX N) α := by
    rw [ci N hodd hN, majorSet, minorSet]
    exact hsplit.symm
  have hre : tripleW ηp ηs N (helfgottX N) =
      (∫ α in majorSet (helfgottX N), kernS ηp ηs N (helfgottX N) α).re +
        (∫ α in minorSet (helfgottX N), kernS ηp ηs N (helfgottX N) α).re := by
    simpa using congrArg Complex.re heq
  have hmaj := mj grh N hodd hN
  have h1 := norm_integral_le_integral_norm
    (μ := volume.restrict (minorSet (helfgottX N))) (kernS ηp ηs N (helfgottX N))
  simp only [norm_kernS] at h1
  have hnorm := le_trans h1 (mn N hodd hN)
  have hmin := (abs_le.mp (le_trans (Complex.abs_re_le_norm _) hnorm)).1
  linarith

/-- **THE SPINE.** Helfgott's §7.4, as a composition: the six links deliver the EP1054 chain's
last trusted input, with witnesses `ηp := η₊`, `ηs := η_*`. The proof is function application
(`weighted_lower`, the links) plus the arithmetic of step 4 of map §2.3:
`0.084339·(490/989)²/49 − 7.3306/10¹¹ ≥ 0.000422`. -/
theorem cite_of_smooth (ηp ηs : ℝ → ℝ) (grh : Spine.PlattGRH) (sb : SupBounds ηp ηs)
    (sm : Summ ηp ηs) (ci : CircleIdSmooth ηp ηs) (mj : MajorLowerSmooth ηp ηs)
    (mn : MinorUpperSmooth ηp ηs) (pp : PrimePowerSmooth ηp ηs) :
    Cite_Helfgott_weighted := by
  refine cite_iff.mpr fun H hodd hH => ⟨ηp, ηs, sb.1, sb.2, ?_⟩
  have hW := weighted_lower ηp ηs grh sm ci mj mn H hodd hH
  have hP := pp H hodd hH
  have hH0 : (0 : ℝ) ≤ (490 : ℝ) / 989 * H := by positivity
  have hx2 : ((490 : ℝ) / 989 * H) ^ 2 ≤ helfgottX H ^ 2 := pow_le_pow_left₀ hH0 (helfX_ge H) 2
  have hx2' : (490 : ℝ) ^ 2 / 989 ^ 2 * (H : ℝ) ^ 2 ≤ helfgottX H ^ 2 :=
    le_of_eq_of_le (by ring) hx2
  have hE : 7.3306 * ((H : ℝ) * Real.sqrt (H : ℝ)) * Real.log (H : ℝ)
      ≤ 7.3306 * ((H : ℝ) ^ 2 / 10 ^ 11) :=
    le_of_eq_of_le (by ring) (mul_le_mul_of_nonneg_left (err_le H hH) (by norm_num))
  have hH2 : (0 : ℝ) ≤ (H : ℝ) ^ 2 := sq_nonneg _
  linarith

/-- **The existential form the campaign will eventually discharge**: one pair of weights
satisfying all six links, for every `N` at once (Helfgott's `η₊`, `η_*` are fixed once for all
`N`, which is stronger than `Cite_Helfgott_weighted` needs). Named `…_ex` rather than `…_exists`
so that its `#print axioms` line stays inside the `120`-column render. -/
theorem cite_of_smooth_ex (grh : Spine.PlattGRH)
    (links : ∃ ηp ηs : ℝ → ℝ, SupBounds ηp ηs ∧ Summ ηp ηs ∧ CircleIdSmooth ηp ηs ∧
      MajorLowerSmooth ηp ηs ∧ MinorUpperSmooth ηp ηs ∧ PrimePowerSmooth ηp ηs) :
    Cite_Helfgott_weighted := by
  obtain ⟨ηp, ηs, sb, sm, ci, mj, mn, pp⟩ := links
  exact cite_of_smooth ηp ηs grh sb sm ci mj mn pp

/-! ## `Summ` is derivable, so the composition needs no side condition -/

/-- **The major-arc link rejects any weight whose `smSum` vanishes identically** at some scale it
uses — zero weights and non-summable (junk) weights alike — as long as Platt holds. -/
theorem major_fails (ηp ηs : ℝ → ℝ) (grh : Spine.PlattGRH) (N : ℕ) (hodd : Odd N)
    (hN : 10 ^ 27 ≤ N)
    (h0 : (∀ α, smSum ηp (helfgottX N) α = 0) ∨ (∀ α, smSum ηs (helfgottX N) α = 0)) :
    ¬ MajorLowerSmooth ηp ηs := by
  intro mj
  have hk : ∀ α, kernS ηp ηs N (helfgottX N) α = 0 := by
    intro α
    rcases h0 with h | h <;> simp [kernS, h α]
  have hmaj := mj grh N hodd hN
  simp only [hk, integral_zero, Complex.zero_re] at hmaj
  have hx : 0 < helfgottX N := helfX_pos N (lt_of_lt_of_le (by norm_num) hN)
  have hx2 : 0 < helfgottX N ^ 2 := pow_pos hx 2
  linarith

/-- **`Summ` follows from Platt and the major-arc link.** A non-summable weight makes `smSum`
junk `0` (`smSum_junk`), hence the major-arc integral `0`, contradicting `1.058259 x²/49 > 0`. -/
theorem summ_of_major (ηp ηs : ℝ → ℝ) (grh : Spine.PlattGRH) (mj : MajorLowerSmooth ηp ηs) :
    Summ ηp ηs := by
  intro N hodd hN
  constructor
  · by_contra hns
    exact major_fails ηp ηs grh N hodd hN (Or.inl (smSum_junk ηp _ hns)) mj
  · by_contra hns
    exact major_fails ηp ηs grh N hodd hN (Or.inr (smSum_junk ηs _ hns)) mj

/-- **The composition with no side condition at all**: `Summ` is supplied by `summ_of_major`. -/
theorem cite_no_summ (ηp ηs : ℝ → ℝ) (grh : Spine.PlattGRH) (sb : SupBounds ηp ηs)
    (ci : CircleIdSmooth ηp ηs) (mj : MajorLowerSmooth ηp ηs) (mn : MinorUpperSmooth ηp ηs)
    (pp : PrimePowerSmooth ηp ηs) : Cite_Helfgott_weighted :=
  cite_of_smooth ηp ηs grh sb (summ_of_major ηp ηs grh mj) ci mj mn pp

/-! ## THE ADVERSARIAL PASS, as theorems -/

/-- The zero weight has zero exponential sum. -/
theorem smSum_zero (x α : ℝ) : smSum 0 x α = 0 := by simp [smSum]

/-- The zero weights have zero triple sum. -/
theorem tripleW_zero (N : ℕ) (x : ℝ) : tripleW 0 0 N x = 0 := by simp [tripleW]

/-- The zero weights have zero `Cite_Helfgott_weighted` sum. -/
theorem citeSum_zero (H : ℕ) : citeSum 0 0 H = 0 := by simp [citeSum]

/-- **(a) Zero weights fail the major-arc link**, given Platt. -/
theorem major_zero (grh : Spine.PlattGRH) : ¬ MajorLowerSmooth 0 0 :=
  major_fails 0 0 grh (10 ^ 27 + 1) ⟨5 * 10 ^ 26, by norm_num⟩ (by norm_num)
    (Or.inl fun α => smSum_zero _ α)

/-- **(a), exactly**: for zero weights the major-arc link holds iff Platt's verification FAILS.
So it constrains precisely as far as `PlattGRH` is true, which is the honest reading of a link
with `PlattGRH` inside it. -/
theorem major_zero_iff : MajorLowerSmooth 0 0 ↔ ¬ Spine.PlattGRH :=
  ⟨fun h grh => major_zero grh h, fun h grh => absurd grh h⟩

/-- **(a), the other five links: all satisfied by the zero weights.** So `MajorLowerSmooth` is the
ONLY link that forces the weights to be nondegenerate. The others are identities and *upper*
bounds, which small weights meet trivially; `MinorUpperSmooth` in particular carries its (very
large) content only jointly with the major-arc link, through the margin `1.058259 − 0.97392`. -/
theorem zero_rest : SupBounds 0 0 ∧ Summ 0 0 ∧ CircleIdSmooth 0 0 ∧ MinorUpperSmooth 0 0 ∧
    PrimePowerSmooth 0 0 := by
  refine ⟨⟨fun u => by norm_num, fun u => by norm_num⟩, fun N _ _ => ⟨by simp, by simp⟩,
    fun N _ _ => by simp [tripleW, kernS, smSum], fun N _ _ => ?_, fun H _ _ => ?_⟩
  · simp only [smSum_zero, norm_zero, zero_mul, integral_zero]
    positivity
  · rw [tripleW_zero, citeSum_zero]
    have h : (0 : ℝ) ≤ 7.3306 * ((H : ℝ) * Real.sqrt (H : ℝ)) * Real.log (H : ℝ) := by
      positivity
    linarith

/-- A point `10⁻⁶` is outside every arc about `a/q`, `1 ≤ q ≤ 300000`, of radius `ρ` with
`ρq ≤ 10⁻⁷`. (`a ≤ 0`: the arc lies below `ρ ≤ 10⁻⁷`; `a ≥ 1`: it lies above
`1/q − ρ ≥ 3.3·10⁻⁶ − 10⁻⁷`.) -/
theorem far_from_arcs (q : ℕ) (hq1 : 1 ≤ q) (hq2 : q ≤ 300000) (a : ℤ) (ρ : ℝ)
    (hρ : ρ * q ≤ 1 / 10 ^ 7) :
    (1 / 10 ^ 6 : ℝ) ∉ Set.Ioo ((a : ℝ) / q - ρ) ((a : ℝ) / q + ρ) := by
  rintro ⟨h1, h2⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hq' : (q : ℝ) ≤ 300000 := by exact_mod_cast hq2
  have hqpos : (0 : ℝ) < q := by linarith
  have hdiv : (a : ℝ) / q * q = a := div_mul_cancel₀ _ (ne_of_gt hqpos)
  rcases le_or_gt a 0 with ha | ha
  · have ha' : (a : ℝ) ≤ 0 := by exact_mod_cast ha
    have hq0 : (a : ℝ) / q ≤ 0 := div_nonpos_of_nonpos_of_nonneg ha' hqpos.le
    have hρpos : 1 / 10 ^ 6 < ρ := by linarith
    have hρq : ρ * 1 ≤ ρ * q := mul_le_mul_of_nonneg_left hq (by linarith)
    linarith
  · have ha1 : (1 : ℤ) ≤ a := ha
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hmul := mul_lt_mul_of_pos_right h1 hqpos
    have hexp : ((a : ℝ) / q - ρ) * q = a - ρ * q := by rw [sub_mul, hdiv]
    rw [hexp] at hmul
    linarith

/-- **(b) The minor set is not empty**: `10⁻⁶ ∈ (0,1] ∖ 𝔐_{8,r₀}` for every `x ≥ 10^26`. The arcs
have half-width at most `8·150000/(qx) ≤ 1.2·10⁻²⁰/q`, while `10⁻⁶` is at distance `≥ 10⁻⁶` from
`0` and `≥ 1/q − 10⁻⁶ ≥ 2.3·10⁻⁶` from every other `a/q` with `q ≤ 300000`. -/
theorem minor_nonempty (x : ℝ) (hx : 10 ^ 26 ≤ x) : (1 / 10 ^ 6 : ℝ) ∈ minorSet x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  intro hmem
  simp only [majArcs, arcs, Set.mem_union, Set.mem_iUnion] at hmem
  rcases hmem with ⟨q, ⟨hq1, hq2⟩, _, a, _, hin⟩ | ⟨q, ⟨hq1, hq2⟩, _, a, _, hin⟩
  · have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
    refine far_from_arcs q hq1 (by omega) a _ ?_ hin
    have hρ : (8 : ℝ) * ((150000 : ℕ) : ℝ) / (2 * q * x) * q = 600000 / x := by
      push_cast
      field_simp
      ring
    rw [hρ, div_le_div_iff₀ hx0 (by norm_num)]
    linarith
  · have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
    refine far_from_arcs q hq1 (by omega) a _ ?_ hin
    have hρ : (8 : ℝ) * ((150000 : ℕ) : ℝ) / (q * x) * q = 1200000 / x := by
      push_cast
      field_simp
      ring
    rw [hρ, div_le_div_iff₀ hx0 (by norm_num)]
    linarith

/-- **(b), the other side: the major set is not empty either** (`α = 1 = 1/1` is the centre of the
principal arc), so `MajorLowerSmooth` is not a statement about an empty integral. -/
theorem one_mem_major (x : ℝ) (hx : 0 < x) : (1 : ℝ) ∈ majorSet x := by
  refine ⟨⟨by norm_num, le_refl 1⟩, Or.inl ?_⟩
  simp only [Set.mem_iUnion]
  have hρ : (0 : ℝ) < 8 * ((150000 : ℕ) : ℝ) / (2 * ((1 : ℕ) : ℝ) * x) := by positivity
  refine ⟨1, ⟨le_refl 1, by norm_num⟩, odd_one, 1, by norm_num, ?_⟩
  constructor
  · push_cast at hρ ⊢
    linarith
  · push_cast at hρ ⊢
    linarith

/-! ## (b), quantitatively: the arcs are few and narrow

Nonemptiness would leave `MinorUpperSmooth` nearly vacuous if the minor set were a null set. It is
not: the major arcs have total measure at most `1.44·10¹²/x ≤ 1.44·10⁻¹⁴` on `(0,1]`, so the
minor-arc integral in (7.48) runs over all but `1.44·10⁻¹⁴` of the circle. -/

/-- One arc of `𝔐_{8,r₀}` meeting `(0,1]` has its centre `a/q` with `0 ≤ a ≤ q`, and it sits inside
the arc of the larger radius `8·150000/(qx)`. -/
theorem arc_cover (q : ℕ) (hq1 : 1 ≤ q) (a : ℤ) (ρ α x : ℝ) (hx : 10 ^ 26 ≤ x)
    (hρ : ρ ≤ 1200000 / (q * x)) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (hin : α ∈ Set.Ioo ((a : ℝ) / q - ρ) ((a : ℝ) / q + ρ)) :
    a ∈ Finset.Icc (0 : ℤ) q ∧
      α ∈ Set.Ioo ((a : ℝ) / q - 1200000 / (q * x)) ((a : ℝ) / q + 1200000 / (q * x)) := by
  obtain ⟨hα0, hα1⟩ := hα
  obtain ⟨h1, h2⟩ := hin
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < q := by linarith
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hdiv : (a : ℝ) / q * q = a := div_mul_cancel₀ _ hqpos.ne'
  have hρq : ρ * q ≤ 1200000 / x := by
    calc ρ * q ≤ 1200000 / (q * x) * q := mul_le_mul_of_nonneg_right hρ hqpos.le
      _ = 1200000 / x := by field_simp
  have hsmall : 1200000 / x ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hx0 (by norm_num)]
    linarith
  refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ⟨by linarith, by linarith⟩⟩
  · have h4 := mul_lt_mul_of_pos_right (show (0 : ℝ) < (a : ℝ) / q + ρ by linarith) hqpos
    have h5 : ((a : ℝ) / q + ρ) * q = a + ρ * q := by rw [add_mul, hdiv]
    rw [h5, zero_mul] at h4
    have h6 : ((-1 : ℤ) : ℝ) < a := by push_cast; linarith
    have h7 : (-1 : ℤ) < a := by exact_mod_cast h6
    omega
  · have h4 := mul_lt_mul_of_pos_right (show (a : ℝ) / q - ρ < 1 by linarith) hqpos
    have h5 : ((a : ℝ) / q - ρ) * q = a - ρ * q := by rw [sub_mul, hdiv]
    rw [h5, one_mul] at h4
    have h6 : (a : ℝ) < ((q + 1 : ℤ) : ℝ) := by push_cast; linarith
    have h7 : a < (q + 1 : ℤ) := by exact_mod_cast h6
    omega

/-- The arcs about the `q + 1` centres `a/q`, `0 ≤ a ≤ q`, have total length at most `4.8·10⁶/x`. -/
theorem vol_one_q (q : ℕ) (hq1 : 1 ≤ q) (x : ℝ) (hx0 : 0 < x) :
    volume (⋃ a ∈ Finset.Icc (0 : ℤ) q,
        Set.Ioo ((a : ℝ) / q - 1200000 / (q * x)) ((a : ℝ) / q + 1200000 / (q * x)))
      ≤ ENNReal.ofReal (4800000 / x) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < q := by linarith
  have hreal : ((q + 1 : ℕ) : ℝ) * (2 * (1200000 / (q * x))) ≤ 4800000 / x := by
    have e1 : ((q + 1 : ℕ) : ℝ) * (2 * (1200000 / (q * x))) = 2400000 / x * ((q + 1) / q) := by
      push_cast
      field_simp
      norm_num
    have e2 : ((q : ℝ) + 1) / q ≤ 2 := by
      rw [div_le_iff₀ hqpos]
      linarith
    rw [e1]
    calc 2400000 / x * (((q : ℝ) + 1) / q) ≤ 2400000 / x * 2 :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = 4800000 / x := by ring
  calc _ ≤ ∑ a ∈ Finset.Icc (0 : ℤ) q, volume
        (Set.Ioo ((a : ℝ) / q - 1200000 / (q * x)) ((a : ℝ) / q + 1200000 / (q * x))) :=
        measure_biUnion_finset_le _ _
    _ = ∑ a ∈ Finset.Icc (0 : ℤ) q, ENNReal.ofReal (2 * (1200000 / (q * x))) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Real.volume_Ioo]
        congr 1
        ring
    _ = (q + 1) • ENNReal.ofReal (2 * (1200000 / (q * x))) := by
        rw [Finset.sum_const, Int.card_Icc]
        congr 1
    _ = ENNReal.ofReal ((q + 1) • (2 * (1200000 / (q * x)))) := ENNReal.ofReal_nsmul.symm
    _ ≤ ENNReal.ofReal (4800000 / x) := by
        apply ENNReal.ofReal_le_ofReal
        rw [nsmul_eq_mul]
        exact hreal

/-- **The major arcs are narrow**: `vol((0,1] ∩ 𝔐_{8,r₀}) ≤ 1.44·10¹²/x` for `x ≥ 10^26`
(`300000` moduli, at most `q + 1` centres each, half-width `≤ 1.2·10⁶/(qx)`). -/
theorem vol_major_le (x : ℝ) (hx : 10 ^ 26 ≤ x) :
    volume (majorSet x) ≤ ENNReal.ofReal (1440000000000 / x) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hcov : majorSet x ⊆ ⋃ q ∈ Finset.Icc (1 : ℕ) 300000, ⋃ a ∈ Finset.Icc (0 : ℤ) q,
      Set.Ioo ((a : ℝ) / q - 1200000 / (q * x)) ((a : ℝ) / q + 1200000 / (q * x)) := by
    rintro α ⟨hα, hmem⟩
    simp only [majArcs, arcs, Set.mem_union, Set.mem_iUnion] at hmem
    simp only [Set.mem_iUnion]
    rcases hmem with ⟨q, ⟨hq1, hq2⟩, _, a, _, hin⟩ | ⟨q, ⟨hq1, hq2⟩, _, a, _, hin⟩
    · have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
      have hρ : (8 : ℝ) * ((150000 : ℕ) : ℝ) / (2 * q * x) ≤ 1200000 / (q * x) := by
        have e : (8 : ℝ) * ((150000 : ℕ) : ℝ) / (2 * q * x) = 600000 / (q * x) := by
          push_cast
          field_simp
          ring
        rw [e]
        exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
      obtain ⟨ha, hα'⟩ := arc_cover q hq1 a _ α x hx hρ hα hin
      exact ⟨q, Finset.mem_Icc.mpr ⟨hq1, by omega⟩, a, ha, hα'⟩
    · have hρ : (8 : ℝ) * ((150000 : ℕ) : ℝ) / (q * x) ≤ 1200000 / (q * x) := by
        push_cast
        norm_num
      obtain ⟨ha, hα'⟩ := arc_cover q hq1 a _ α x hx hρ hα hin
      exact ⟨q, Finset.mem_Icc.mpr ⟨hq1, hq2⟩, a, ha, hα'⟩
  calc volume (majorSet x) ≤ _ := measure_mono hcov
    _ ≤ ∑ q ∈ Finset.Icc (1 : ℕ) 300000, volume (⋃ a ∈ Finset.Icc (0 : ℤ) q,
          Set.Ioo ((a : ℝ) / q - 1200000 / (q * x)) ((a : ℝ) / q + 1200000 / (q * x))) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ Finset.Icc (1 : ℕ) 300000, ENNReal.ofReal (4800000 / x) :=
        Finset.sum_le_sum fun q hq => vol_one_q q (Finset.mem_Icc.mp hq).1 x hx0
    _ = ENNReal.ofReal (1440000000000 / x) := by
        rw [Finset.sum_const, Nat.card_Icc, ← ENNReal.ofReal_nsmul, nsmul_eq_mul]
        congr 1
        push_cast
        ring

/-- **(b), the verdict: `MinorUpperSmooth` integrates over almost the whole circle.**
`vol((0,1] ∖ 𝔐_{8,r₀}) ≥ 1 − 1.44·10¹²/x`, i.e. `≥ 1 − 1.44·10⁻¹⁴` at `x ≥ 10^26` (and
`helfgottX N ≥ 4.95·10^26` for `N ≥ 10^27`). -/
theorem minor_large (x : ℝ) (hx : 10 ^ 26 ≤ x) :
    1 ≤ volume (minorSet x) + ENNReal.ofReal (1440000000000 / x) := by
  have hunion : Set.Ioc (0 : ℝ) 1 ⊆ majorSet x ∪ minorSet x := fun α hα => by
    by_cases h : α ∈ majArcs x
    · exact Or.inl ⟨hα, h⟩
    · exact Or.inr ⟨hα, h⟩
  calc (1 : ENNReal) = volume (Set.Ioc (0 : ℝ) 1) := by simp [Real.volume_Ioc]
    _ ≤ volume (majorSet x ∪ minorSet x) := measure_mono hunion
    _ ≤ volume (majorSet x) + volume (minorSet x) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (1440000000000 / x) + volume (minorSet x) :=
        add_le_add_left (vol_major_le x hx) _
    _ = volume (minorSet x) + ENNReal.ofReal (1440000000000 / x) := add_comm _ _

end Principia.Common.TernaryGoldbach.Smooth
