/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.Spine
import Principia.Common.Goldbach.MajorArc

set_option autoImplicit false

/-!
# The major-arc half, reduced to Platt's finite GRH verification

`Spine.lean` leaves four links open; this file attacks one of them,
`Spine.MajorArcLower P Q (1/2)`, and reduces it — **at a concrete pair of Farey cutoffs** — to

* `PlattGRHAt T`, a *height-parameterized* form of Helfgott's one numerical input,
* `FareyDecomposition`, the measure-theoretic split of the major set into Farey windows,
* `WindowApproxUnder cW σ T`, the per-modulus analytic estimate, which **consumes the zero
  information as a hypothesis on each character**, and
* `KernelTailBound cK`, the truncation loss of the window integrals against `H²/2`,

together with `SingularSeriesLower (5/4)`, which the sibling `SingularSeries.lean` already all
but discharges (`sing3_ge` proves `𝔖₃ ≥ 13/10` for odd `H`; only a *uniform* truncation tail
remains). The headline is `majorArcLower_of_chain`; composed with the spine,
`ternaryLogCountLower_of_platt_chain` and `cite_Helfgott_weighted_of_platt_chain`.

## The cutoffs, and why these

`Spine.MajorArcLower` is parametric in `P Q : ℕ → ℕ`, and
`Spine.majorLower_at_one_one_is_whole_target` proves that at `P = Q = 1` the arc split delivers
nothing. So a chain that does not *name* its
cutoffs has not reduced anything. Helfgott's dissection (`ternvin.tex` `eq:majdef`, `δ₀ = 8`,
`r₀ = 150000`) is

```
𝔐 = ⋃_{q ≤ r₀ odd} ⋃_{(a,q)=1} |α − a/q| ≤ δ₀r₀/(2qx)
  ∪ ⋃_{q ≤ 2r₀ even} ⋃_{(a,q)=1} |α − a/q| ≤ δ₀r₀/(qx)
```

The library's `Goldbach.MajorArcs P Q` carries **one** width `1/(q(Q+1))` for all `q ≤ P`, so
Helfgott's dissection transcribes into it by taking the even-`q` width for every `q`:

  `P = 2r₀ = 300000`,  `1/(q(Q+1)) = δ₀r₀/(qx) = 1.2·10⁶/(qH)`,  i.e. `Q + 1 = H/1.2·10⁶`.

Hence `Pcut H = 300000` and `Qcut H = H/1200000` (natural division, so the windows are a hair
narrower than Helfgott's even-`q` ones and wider than his odd-`q` ones). `300000` is *exactly* the
conductor range Platt certifies, which is not a coincidence: `ternvin.tex` 141–146 says the arcs
are forced to be few and narrow "because of the kind of L-function bounds we will rely upon".

**The cutoffs are certified non-degenerate, as theorems.** `cutoff_separation` proves
`2·Pcut H < Qcut H + 1`, which is exactly the Farey separation condition
`q + q' < Q + 1` that makes distinct windows disjoint — so `FareyDecomposition` is a statement about
a genuine partition, not about an overlapping cover. `minorSet_nonempty_at_cutoffs` exhibits
`1/600001` in the minor set, which is the direct converse of `Spine.minorSet_one_one`: at these
cutoffs the split is **not** vacuous.

## The budget

```
Re ∫_𝔐 S³e(−Hα)  ≥  𝔖₃(H,P)·H²/2  −  ‖∫_𝔐 − 𝔖₃(H,P)H²/2‖  ≥  cSing·H²/2  −  cErr·H²
```
so the side condition is `cMaj + cErr ≤ cSing/2`, with the reassembly error split across **two
different scales**:

  `cErr = cW/10⁴ + cK`,  `cW·H^{3/2}(log H)² ≤ cW·H²/10⁴` (`Spine.pp_slack`)  +  `cK·H²`.

`cW` is the *analytic* error of `WindowApproxUnder` — the explicit formula's `H^{1/2+ε}` — and `cK`
is the *geometric* truncation of the window integrals in `KernelTailBound`, which is `Θ(H²)` and
**not** on the `H^{3/2}` scale; see that link's docstring for why conflating them is a scale error
and not a constant error. Instantiated at `cMaj = 1/2` (what the spine's main instantiation wants),
`cSing = 5/4` (`SingularSeries.sing3_ge`'s `13/10` minus a `1/20` truncation tail), `cW = 1000` and
`cK = 10⁻⁵`: `0.5 + 0.10001 = 0.60001 ≤ 0.625`. The true infimum of `𝔖₃` over odd `H` is
`1.3203236744`, the singular-series tail at `R = 3·10⁵` is `≈5·10⁻⁵`, the window truncation at
`W = 1.2·10⁶` is `3.01·10⁻⁷·H²`, and `1000·H^{3/2}(log H)² = 1.22·10⁻⁷·H²` at the threshold (all
recomputed two ways) — so every constant is carried with orders of magnitude to spare. The margin
is `0.025·H²`.

## What makes Platt load-bearing, and what would make him idle

The zero information enters as `ZeroFreeBoxAbove q χ (T q) σ` — *every non-trivial zero of `L(·,χ)`
up to height `T q` has `Re ≤ σ`* — supplied **per character** to `WindowApproxUnder`. Four
theorems pin down where the content sits, and none of them is prose:

* `zeroFreeBox_vacuous_of_one_le` : at `σ ≥ 1` the hypothesis is *free* (every non-trivial zero has
  `Re < 1`). So `WindowApproxUnder cW 1 T` **is** the unconditional statement.
* `windowApproxUnder_antitone_sigma` : from `σ ≤ τ`, `WindowApproxUnder cW τ T` gives
  `WindowApproxUnder cW σ T`. The unconditional form therefore *implies* the `σ = 1/2` form:
  assuming Platt is assuming strictly less. **That gap is the entire content of the reduction**,
  and it is measured, not asserted.
* `majorArcLower_of_unconditional` : the chain runs with `σ = 1` and **no `PlattGRHAt` in its
  signature at all** — the exact analogue of `Spine.spine_needs_grh`. Read together with the
  previous item: Platt is doing work precisely to the extent that `σ = 1/2` is weaker than `σ = 1`.
* `zeroFreeBox_vacuous_of_neg` and `windowApproxUnder_mono_height` : the *height* is load-bearing
  too. At `T q < 0` the box hypothesis is vacuous, and the Prop weakens monotonically as `T` grows.
  So `PlattGRHAt` must be quoted **with its height**, which is why the height is a parameter here
  and not baked in.

And `PlattGRH` is not vacuous: `plattGRH_implies_zeta_zeros_on_line` proves that it *implies* that
every zero of `riemannZeta` in the critical strip up to height `10⁸` is on the critical line — a
piece of the Riemann hypothesis. (Modulus `1` is inside `q ≤ 300000`, the trivial character mod `1`
is primitive, and `DirichletCharacter.LFunction_modOne_eq` identifies its `L`-function with `ζ`.)
So the hypothesis cannot be discharged cheaply, and it is not satisfiable by an empty zero set.

## THE MEASUREMENT: a sharp cutoff cannot use Platt's height at `H = 10²⁷`

This is the file's main finding, and it **qualifies `Spine.lean`'s own docstring**, which records
that the `Reduction.lean` sandwich puts Helfgott's smoothings "off the critical path". They are off
the critical path for the *statement*. They are not off the critical path for the *proof at Platt's
verified height*, and here is the number.

With a **sharp** cutoff the explicit formula for a primitive `χ` mod `q` carries a tail from the
zeros above the verified height (Montgomery–Vaughan, *Multiplicative Number Theory I*, Thm 12.5):

  `ψ(x,χ) = δ_χ x − ∑_{|γ| ≤ T} x^ρ/ρ + O(x T⁻¹ log²(qx) + x^{1/4} log x)`,

so the **relative** tail is `log²(qx)/T`. At Platt's height `T_q = 10⁸/q` this is `q log²(qH)/10⁸`,
and at `H = 10²⁷`:

| `q` | `1` | `10²` | `1500` | `10⁴` | `10⁵` | `3·10⁵` |
|---|---|---|---|---|---|---|
| `q log²(qH)/10⁸` | `3.9·10⁻⁵` | `4.5·10⁻³` | `7.2·10⁻²` | `0.51` | `5.43` | **`16.78`** |

The affordable *relative* major-arc error here is `~7.5 %` (the `0.05·H²` margin against the
`0.66·H²` main term is `7.6 %`; Helfgott's own affordable figure inside §7.4 is `3.06 %`). So:

* Platt's verified height suffices, with a sharp cutoff, only for **`q ≤ 1551`** (`q ≤ 649` at
  Helfgott's `3.06 %`) — not for `q ≤ 3·10⁵`.
* At the top modulus the tail **exceeds the budget by `224×`**.
* Stated as the requirement on the verification: the sharp-cutoff route needs
  `q·T_q ≥ 2.24·10¹⁰` uniformly on `q ≤ 3·10⁵`, against Platt's `q·T_q = 10⁸` — a **`224×`
  extension in height** (`548×` at Helfgott's tolerance), hence `~250×` more zeros:
  `≈1.4·10¹⁶` instead of `≈5.5·10¹³`.

Two Lean-checked numbers back this up: `platt_tail_ok_at_1500` and
`platt_tail_exceeds_at_top_modulus`. They are arithmetic facts about `Real.log`; that they *are*
the explicit-formula tail is prose, not a kernel-checked claim.

**Consequence for the programme.** `WindowApproxUnder 1000 (1/2) (fun q => 10⁸/q)` — the chain
instantiated at Platt's actual height — is stated here and composed, but by the above it is
**probably false**, and the honest reading of `majorArcLower_of_chain_platt` is a true theorem with
a hypothesis this file measures as out of reach. Two repairs, both visible in the signature
because the height is a parameter:

1. `majorArcLower_of_chain_extended` — the same chain at `T q = 2.24·10¹⁰/q`, i.e. **ask Platt (or
   a successor computation) for 224× the height**. Nothing else in the chain changes.
2. Reinstate a smoothing, whose Mellin transform kills the zeros above `T` — Helfgott §4. That is
   *not* expressible against `Spine.expSum`, so it would require reopening `Reduction.lean`'s
   sandwich at the level of the proof rather than the statement.

## Can `PlattGRHAt` itself be discharged in Lean?

No, and not by a kernel certificate. Recomputed here independently of
`HELFGOTT-PROOF-MAP.md` §3.5 and agreeing with it:

* **`1.663·10¹⁰` primitive characters** of conductor `q ≤ 3·10⁵` (`∑ φ*(q)`, `φ* = μ ⋆ φ`, by
  sieve; `∑ φ(q) = 2.736·10¹⁰` for comparison).
* **`5.50·10¹³` zeros** in the verified boxes (`(T_q/π)·log(qT_q/2πe) = 4.96·10⁸/q` per character).
  At 16 bytes per zero that is **0.88 PB**, so a table is out of the question, and the `224×`
  extension above would make it `≈1.4·10¹⁶` zeros / `≈220 PB`.
* **It is the wrong *kind* of object for a certificate.** `PlattGRHAt` is a *negative* statement
  about a continuum — no zero anywhere in `{0 < Re s < 1, Re s ≠ 1/2, |Im s| ≤ T_q}` — established
  by rigorous zero-counting (Turing's method) over interval-arithmetic `L(s,χ)` evaluation. A
  certificate would have to carry the *counting argument*, not a list.
* **Closest existing capability, measured:** `Common/KernelCert/` (`Bits`, `Prime`, `Seed`, `Sieve`,
  `SubsetSum`, 1350 lines) is kernel-checked bignum arithmetic — `Nat.gcd` primality against a
  balanced product tree, a segmented sieve, subset-sum DP — with no `native_decide`. It is over
  `ℕ`. There is **no interval arithmetic over `ℝ` or `ℂ` anywhere in the library**, no rigorous
  special-function evaluator, and Mathlib has no argument-principle zero count for
  `DirichletCharacter.LFunction`. The gap is not a bigger certificate; it is an entire verified
  rigorous-numerics stack (complex interval arithmetic → a certified `L(s,χ)` evaluator with error
  bounds → a certified `S(T)`/Turing zero count → a certified isolation argument). **This is a
  multi-year formalization project of a different kind from anything in this repository, and it is
  an obligation someone else owes** — which is why it is a hypothesis here and never a `sorry`.

## What is NOT claimed

Nothing here proves any part of ternary Goldbach, and nothing here proves `MajorArcLower`.
`FareyDecomposition`, `WindowApproxUnder`, `KernelTailBound` and `CharacterDecomposition` are
`def … : Prop` and unproved; `PlattGRHAt` is a computation. `CharacterDecomposition` is the one
declaration in this file that is **stated and not composed** — it is the exact orthogonality
identity `WindowApproxUnder` starts from, transcribed so the next round has it, with the Mathlib
entry point named. It is marked as such at its definition; it carries no weight in any theorem
below, and saying so is cheaper than pretending otherwise.
-/

namespace Principia.Common.TernaryGoldbach.MajorPlatt

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open Principia.Common.Goldbach.MajorArcMainTerm
open Principia.Common.TernaryGoldbach.Spine
open scoped ArithmeticFunction

/-! ## The cutoffs -/

/-- **The modulus cutoff**, `P = 2r₀ = 300000` — Helfgott's `r₀ = 150000` doubled for the even
moduli, and exactly the conductor range Platt certifies. -/
def Pcut (_ : ℕ) : ℕ := 300000

/-- **The window cutoff**, `Q + 1 = H/(δ₀r₀) = H/1.2·10⁶`, so the Farey window of modulus `q` has
half-width `1/(q(Q+1)) ≈ 1.2·10⁶/(qH)` — Helfgott's even-`q` width, taken for every `q`. -/
def Qcut (H : ℕ) : ℕ := H / 1200000

theorem Pcut_apply (H : ℕ) : Pcut H = 300000 := rfl

theorem Pcut_pos (H : ℕ) : 0 < Pcut H := by norm_num [Pcut]

/-- **The Farey separation certificate.** Distinct reduced fractions `a/q ≠ a'/q'` with
`q, q' ≤ P` are `≥ 1/(qq')` apart, while the two windows have total width
`(q + q')/(qq'(Q+1))`; so the windows are pairwise disjoint as soon as `q + q' < Q + 1`, and
`2P < Q + 1` gives it uniformly. At `H = 10²⁷` the two sides are `6·10⁵` and `8.3·10²⁰`. **This is
the design condition `Spine.minorSet_one_one` shows no type can enforce**, discharged here for
these cutoffs. -/
theorem cutoff_separation (H : ℕ) (hH : 10 ^ 27 ≤ H) : 2 * Pcut H < Qcut H + 1 := by
  have h1 : 600000 * 1200000 ≤ H := le_trans (by norm_num) hH
  have h2 : 600000 ≤ Qcut H := (Nat.le_div_iff_mul_le (by norm_num)).mpr h1
  simp only [Pcut]
  omega

/-! ## The objects

All of them are concretely defined in terms of `Spine.kern`, `Spine.expSum`,
`SingularSeries.localTerm` and `MajorArcMainTerm.cRam`, so no link below has a function, measure
or witness to instantiate degenerately: each is simply true or false. -/

/-- The half-width of the Farey window of modulus `q` at level `Q`, i.e. the radius of the balls in
`Goldbach.MajorArcs P Q`. -/
noncomputable def halfWidth (q Q : ℕ) : ℝ := 1 / ((q : ℝ) * ((Q : ℝ) + 1))

/-- `U(β) = ∑_{0 < n ≤ H} e(nβ)`, the unweighted companion of `Spine.expSum`. Its cube integrated
over the whole circle against `e(−Hβ)` is the number of ordered triples from `[1,H]` summing to
`H`, i.e. `(H−1)(H−2)/2`; that is where the `H²/2` below comes from. -/
noncomputable def plainSum (H : ℕ) (β : ℝ) : ℂ := ∑ n ∈ Finset.Ioc 0 H, e ((n : ℝ) * β)

/-- One Farey window's contribution to the major-arc integral,
`∫_{|β| ≤ w} S(a/q + β)³ e(−H(a/q+β)) dβ`. -/
noncomputable def windowIntegral (H q Q a : ℕ) : ℂ :=
  ∫ β in Set.Icc (-halfWidth q Q) (halfWidth q Q), kern H ((a : ℝ) / (q : ℝ) + β)

/-- The same with the model integrand `U(β)³e(−Hβ)` — Helfgott's truncated kernel integral. Its
distance from `H²/2` is the truncation loss that `KernelTailBound` charges. -/
noncomputable def kernelIntegral (H q Q : ℕ) : ℂ :=
  ∫ β in Set.Icc (-halfWidth q Q) (halfWidth q Q), (plainSum H β) ^ 3 * e (-(H : ℝ) * β)

/-- The modulus-`q` arc sum: the window integrals over the reduced residues `a` mod `q`, indexed
**exactly** as `MajorArcMainTerm.ramSum` indexes its own sum, so that `ramSum_neg` collapses the
sum over `a` into `cRam q H` without any re-indexing. -/
noncomputable def arcSum (H q Q : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1), windowIntegral H q Q a

/-- **The ternary singular-series local term** `T₃(q) = μ(q)³c_q(H)/φ(q)³`, written character for
character as `SingularSeries.sing3Local q H` (the cube of `μ`, not the square, is what makes the
Euler factor at `p ∤ H` positive). The `cRam` layer it is built from is
`MajorArcMainTerm`'s and is campaign-agnostic. -/
noncomputable def localTerm (q H : ℕ) : ℝ :=
  (ArithmeticFunction.moebius q : ℝ) ^ 3 * (cRam q H : ℝ) / (Nat.totient q : ℝ) ^ 3

/-- The truncated ternary singular series `𝔖₃(H,P) = ∑_{1 ≤ q ≤ P} T₃(q)`, i.e.
`SingularSeries.sing3Trunc H P`. -/
noncomputable def singSeriesTrunc (H P : ℕ) : ℝ := ∑ q ∈ Finset.Icc 1 P, localTerm q H

/-- The major-arc main term `𝔖₃(H, P)·H²/2`, with `𝔖₃(H,P) = ∑_{q ≤ P} μ(q)³c_q(H)/φ(q)³` the
sibling file's `SingularSeries.sing3Trunc`. -/
noncomputable def mainTerm (H P : ℕ) : ℝ := singSeriesTrunc H P * (H : ℝ) ^ 2 / 2

/-- **The singular-series input, as this file needs it.** *DISCHARGED 2026-09-29 —
`SingularBridge.singularSeriesLower_holds : SingularSeriesLower (5/4)` with no hypotheses, and in
fact `SingularSeriesLower (32/25)`.* What closed it was an **effective** tail:
`sqfree_totient_strong`
gives `μ(q)²/φ(q)² ≤ 8q^{-3/2}` for every `q`, whose tail is `≤ 16/√R` — an `R^{-1/2}` rate, so
`16/√(3·10⁵) = 0.0292` and `131/100 − 0.0292 = 1.2808`. The two modules' truncations were checked to
be the same object first (`SingularBridge.singSeriesTrunc_eq`, by `rfl`), which is where this could
have gone silently wrong. Original note retained: `SingularSeries.sing3_ge` proves `𝔖₃(H) ≥ 13/10`
for every odd `H`, and
`SingularSeries.sing3Trunc_ge_of_tail` turns that into exactly this statement given a *uniform*
truncation tail `ε` at level `3·10⁵`; so the bridge is
`fun H hodd _ => SingularSeries.sing3Trunc_ge_of_tail 300000 ε ht H (Pcut H) hodd le_rfl`,
one line, and the only mathematics it still needs is the uniform tail. It is stated here rather
than imported because that file was being edited when this one landed; `localTerm` and
`singSeriesTrunc` are its `sing3Local` and `sing3Trunc` character for character. Numerically
`inf_{H odd} 𝔖₃ = 1.3203236744` and the tail at `3·10⁵` is `≈5·10⁻⁵`, so `cSing = 5/4` is carried
with `5.6 %` to spare. -/
def SingularSeriesLower (cSing : ℝ) : Prop :=
  ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H → cSing ≤ singSeriesTrunc H (Pcut H)

/-- **The error scale the budget can afford**, `H^{3/2}(log H)²`: the size of the major-arc error
in a sharp-cutoff treatment with the low zeros on the critical line. `Spine.pp_slack` proves it is
`≤ H²/10⁴`, and at `H = 10²⁷` it is `1.22·10⁻⁶·H²/10⁴` — six orders of slack. -/
noncomputable def errScale (H : ℕ) : ℝ := (H : ℝ) * Real.sqrt (H : ℝ) * Real.log (H : ℝ) ^ 2

theorem errScale_le_sq (H : ℕ) (hH : 10 ^ 27 ≤ H) : errScale H ≤ (H : ℝ) ^ 2 / 10 ^ 4 := by
  unfold errScale
  exact pp_slack H hH

theorem errScale_nonneg (H : ℕ) : 0 ≤ errScale H := by
  unfold errScale; positivity

/-! ## Elementary facts that support the links

`kern_periodic` is what makes `FareyDecomposition` true: the windows of `MajorArcs P Q` about
`a/q` and about `a/q + 1` carry the same integral, so summing `a` over one period of reduced
residues is the whole of the major set. `ramSum_neg` is what turns the sum over `a` into the
singular-series local term. -/

theorem e_natCast_eq_one (n : ℕ) : e (n : ℝ) = 1 :=
  (e_eq_one_iff (n : ℝ)).mpr ⟨(n : ℤ), by push_cast; ring⟩

theorem e_negNatCast_eq_one (n : ℕ) : e (-(n : ℝ)) = 1 :=
  (e_eq_one_iff (-(n : ℝ))).mpr ⟨-(n : ℤ), by push_cast; ring⟩

/-- `S(α + 1) = S(α)`: the exponential sum is `1`-periodic because its frequencies are integers. -/
theorem expSum_periodic (H : ℕ) (α : ℝ) : expSum H (α + 1) = expSum H α := by
  unfold expSum
  refine Finset.sum_congr rfl (fun n _ => ?_)
  congr 1
  rw [show (n : ℝ) * (α + 1) = (n : ℝ) * α + (n : ℝ) by ring, ← e_add, e_natCast_eq_one, mul_one]

/-- **The circle-method integrand is `1`-periodic.** This is the fact that makes
`FareyDecomposition` a statement about a genuine cover: a window centred at `a/q + k` contributes
the same as the one centred at `a/q`, so reduced residues in `[0, q)` exhaust the major set. -/
theorem kern_periodic (H : ℕ) (α : ℝ) : kern H (α + 1) = kern H α := by
  unfold kern
  rw [expSum_periodic]
  congr 1
  rw [show -(H : ℝ) * (α + 1) = -(H : ℝ) * α + -(H : ℝ) by ring, ← e_add, e_negNatCast_eq_one,
    mul_one]

/-- **The Ramanujan collapse, in the sign the kernel needs.** `∑_{a mod q}^* e(−Ha/q) = c_q(H)`,
the conjugate of `MajorArcMainTerm.ramSum_eq_cRam`; `c_q(H)` is an integer, so conjugation fixes
it. This is why `arcSum` is indexed over `(range q).filter (gcd · q = 1)`: no re-indexing is
needed between the analytic sum over arcs and the arithmetic local term. -/
theorem ramSum_neg (q n : ℕ) (hq : 0 < q) :
    ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1), e (-((n : ℝ) * a / q))
      = (cRam q n : ℂ) := by
  have hstar : ∀ a : ℕ, e (-((n : ℝ) * a / q)) = (starRingEnd ℂ) (e ((n : ℝ) * a / q)) :=
    fun a => (e_conj _).symm
  calc ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1), e (-((n : ℝ) * a / q))
      = ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          (starRingEnd ℂ) (e ((n : ℝ) * a / q)) :=
        Finset.sum_congr rfl (fun a _ => hstar a)
    _ = (starRingEnd ℂ) (ramSum q n) := by rw [ramSum, map_sum]
    _ = (starRingEnd ℂ) ((cRam q n : ℂ)) := by rw [ramSum_eq_cRam q n hq]
    _ = (cRam q n : ℂ) := by simp

/-! ## The numerical input, with its verified height as a parameter

`Spine.PlattGRH` bakes in Platt's height `10⁸/q`. The measurement in this file's header is
precisely about that number, so the height has to be visible: `PlattGRHAt T` is the same statement
with the height a parameter, and `plattGRHAt_platt` identifies the two. -/

/-- **Platt's finite GRH verification at a parametric height.** For every primitive `χ` of
conductor `q ≤ 3·10⁵`, every non-trivial zero of `L(s,χ)` with `|Im s| ≤ T q` is on the critical
line. `T q = 10⁸/q` is what Platt certified; see the header for what the sharp-cutoff route
actually needs. *NUMERICAL.* -/
def PlattGRHAt (T : ℕ → ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], q ≤ 300000 → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T q → s.re = 1 / 2

/-- `PlattGRHAt` at Platt's own height **is** `Spine.PlattGRH`, definitionally. -/
theorem plattGRHAt_platt : PlattGRHAt (fun q => 10 ^ 8 / (q : ℝ)) ↔ PlattGRH := Iff.rfl

/-- **A higher verified height is a stronger statement.** Antitone in `T`, so quoting
`PlattGRHAt` without its height says nothing. -/
theorem plattGRHAt_antitone {T T' : ℕ → ℝ} (hT : ∀ q, T' q ≤ T q) (h : PlattGRHAt T) :
    PlattGRHAt T' := by
  intro q _ hq χ hχ s hs h0 h1 hT'
  exact h q hq χ hχ s hs h0 h1 (le_trans hT' (hT q))

/-- **`PlattGRH` is not vacuous: it implies a piece of the Riemann hypothesis.** Modulus `1` is
inside `q ≤ 3·10⁵`, the character mod `1` is primitive, and its `L`-function is `ζ`
(`DirichletCharacter.LFunction_modOne_eq`), so the verification asserts that every zero of `ζ` in
the critical strip up to height `10⁸` lies on the critical line. Hence the hypothesis is neither
provable for free nor satisfiable by an empty zero set — the two ways a numerical input could turn
out to be a free rider. -/
theorem plattGRH_implies_zeta_zeros_on_line (grh : PlattGRH) (s : ℂ)
    (hz : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) (hT : |s.im| ≤ 10 ^ 8) :
    s.re = 1 / 2 := by
  have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = 0 := by
    simpa [DirichletCharacter.LFunction_modOne_eq] using hz
  refine grh 1 (by norm_num) 1 DirichletCharacter.isPrimitive_one_level_one s hL h0 h1 ?_
  simpa using hT

/-! ## How the zero information is consumed

`ZeroFreeBoxAbove` is what the analysis actually charges: not `Re ρ = 1/2` but `Re ρ ≤ σ`. That is
a small finding in its own right — Platt proves an equality, and a *one-sided* verification ("no
zero to the right of the critical line up to height `T`") would suffice. -/

/-- **The box hypothesis**: every non-trivial zero of `L(·,χ)` up to height `T` has `Re ≤ σ`. -/
def ZeroFreeBoxAbove (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T σ : ℝ) : Prop :=
  ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 → |s.im| ≤ T → s.re ≤ σ

/-- The box hypothesis for every primitive character in Platt's conductor range. -/
def ZeroBoxes (T : ℕ → ℝ) (σ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], q ≤ 300000 → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ZeroFreeBoxAbove q χ (T q) σ

/-- **Platt supplies the boxes at `σ = 1/2`** — and only `≤` is used. -/
theorem zeroBoxes_of_plattGRHAt {T : ℕ → ℝ} (h : PlattGRHAt T) : ZeroBoxes T (1 / 2) := by
  intro q _ hq χ hχ s hs h0 h1 hT
  exact le_of_eq (h q hq χ hχ s hs h0 h1 hT)

/-- Weaker `σ` is a weaker box. -/
theorem zeroFreeBoxAbove_mono {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {T σ τ : ℝ}
    (hστ : σ ≤ τ) (h : ZeroFreeBoxAbove q χ T σ) : ZeroFreeBoxAbove q χ T τ :=
  fun s hs h0 h1 hT => le_trans (h s hs h0 h1 hT) hστ

/-- **Adversarial check on `σ`: at `σ ≥ 1` the box is free.** Every non-trivial zero has `Re < 1`
by the definition of "non-trivial". So `ZeroBoxes T 1` holds outright, and any statement
conditioned on it is unconditional. -/
theorem zeroFreeBoxAbove_vacuous_of_one_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {T σ : ℝ} (hσ : 1 ≤ σ) : ZeroFreeBoxAbove q χ T σ :=
  fun _ _ _ h1 _ => le_trans (le_of_lt h1) hσ

theorem zeroBoxes_vacuous_of_one_le {T : ℕ → ℝ} {σ : ℝ} (hσ : 1 ≤ σ) : ZeroBoxes T σ :=
  fun _ _ _ _ _ => zeroFreeBoxAbove_vacuous_of_one_le hσ

/-- **Adversarial check on the height: at a negative height the box is free.** `|Im s| ≥ 0`, so no
zero is in the box at all. Together with `windowApproxUnder_mono_height` this is why the height
cannot be left implicit. -/
theorem zeroFreeBoxAbove_vacuous_of_neg {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {T σ : ℝ} (hT : T < 0) : ZeroFreeBoxAbove q χ T σ := by
  intro s _ _ _ hs
  exact absurd (le_trans (abs_nonneg s.im) hs) (not_le.mpr hT)

/-- The `ZeroBoxes` form of the same degeneracy: at a negative height *every* box is empty, so the
whole family of box hypotheses is free. -/
theorem zeroBoxes_vacuous_of_neg {T : ℕ → ℝ} {σ : ℝ} (hT : ∀ q, T q < 0) : ZeroBoxes T σ :=
  fun q _ _ _ _ => zeroFreeBoxAbove_vacuous_of_neg (hT q)

/-! ## THE FREE-RIDER TRAP, AND THE GUARD THAT CLOSES IT

**The defect, found by audit and reproduced here as a theorem.** `PlattGRHAt T` is a hypothesis
about a *box*, and a box at a negative height contains nothing. So `PlattGRHAt` is **provable** at
`T = −1` (`plattGRHAt_vacuous_of_neg`), and any theorem that quantifies over `T` with `PlattGRHAt T`
as a slot can be instantiated there with the numerical input discharged for free —
`SingularBridge.majorArcLower_no_platt_at_vacuous_height` exhibits exactly that, with no
`PlattGRHAt` anywhere in its signature. A `PlattGRHAt T` slot under an unconstrained `T` therefore
reduces **nothing** to Platt, however prominently the docstring names him.

**What the audit's diagnosis got half right.** The proposed repair was "make the downstream `Prop`
consume the zero information". It already does: `WindowApproxUnder cW σ T` is *literally*
`ZeroBoxes T σ → …`, so the boxes are a premise of the analytic link and not an ornament beside it.
The hole was never the consumption; it was that **nothing constrained `T`**, and the cheapest `T`
empties the box that the link consumes. Hence the guard below rather than a re-plumbing.

**The guard, and why it is bundled.** `PlattGRHAtLeast T` is `AdmissibleHeight T ∧ PlattGRHAt T` —
one hypothesis, so nothing in the signature is inert. `plattGRHAtLeast_refuses_neg` proves the
degenerate instance is now *refused by the kernel*, and `plattGRH_of_plattGRHAtLeast` proves that at
**every** admissible height the slot implies `PlattGRH`, hence (with
`plattGRH_implies_zeta_zeros_on_line`) a piece of the Riemann hypothesis. That is the repair
demonstrated rather than asserted: the free instance no longer typechecks, and no other free
instance exists, because every admissible one carries RH information.

The height stays a *parameter* — pinning it to Platt's own value would look tidier and would be
wrong: `majorArcLower_of_chain_extended` needs the chain at `224×` the height, and
`windowApproxUnder_mono_height` shows the analytic link at a *higher* height is *weaker*, so a
chain whose window link were nailed to `10⁸/q` could not express the repair at all. -/

/-- **The height guard**: the quoted height is at least the one Platt certified, on the whole
conductor range. `q = 0` is included and says `0 ≤ T 0` (natural division by zero), which is
harmless — `PlattGRHAt` quantifies over `[NeZero q]`. -/
def AdmissibleHeight (T : ℕ → ℝ) : Prop := ∀ q : ℕ, q ≤ 300000 → 10 ^ 8 / (q : ℝ) ≤ T q

/-- **Platt's verification, quoted at an admissible height.** Bundled with the guard so that a
chain consuming it has **no inert slot**: the conjunction is used, and the component that blocks the
degenerate instantiation travels with the component that does the work. -/
def PlattGRHAtLeast (T : ℕ → ℝ) : Prop := AdmissibleHeight T ∧ PlattGRHAt T

theorem admissibleHeight_platt : AdmissibleHeight (fun q => 10 ^ 8 / (q : ℝ)) :=
  fun _ _ => le_rfl

/-- The `224×` extended height is admissible: `10⁸/q ≤ 2.24·10¹⁰/q`. -/
theorem admissibleHeight_extended : AdmissibleHeight (fun q => 2.24 * 10 ^ 10 / (q : ℝ)) := by
  intro q _
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · norm_num
  · have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    rw [div_le_div_iff₀ hqR hqR]
    nlinarith [hqR]

/-- **THE TRAP, IN LEAN.** At a negative height the zero-box is empty (`|Im s| ≥ 0 > T q`), so the
numerical input is *provable*. This is a theorem and not a remark so that the degeneracy can never
be rediscovered by audit: any chain whose `PlattGRHAt` slot is not guarded can be run through this
term. -/
theorem plattGRHAt_vacuous_of_neg : PlattGRHAt (fun _ => -1) := by
  intro q _ _ χ _ s _ _ _ hs
  have h0 : (0 : ℝ) ≤ |s.im| := abs_nonneg s.im
  exact absurd (le_trans h0 hs) (by norm_num)

/-- **The guard refuses exactly that instance** — the repair, demonstrated by the kernel rather than
promised in prose. -/
theorem admissibleHeight_refuses_neg : ¬ AdmissibleHeight (fun _ => -1) := by
  intro h
  have h1 := h 1 (by norm_num)
  norm_num at h1

theorem plattGRHAtLeast_refuses_neg : ¬ PlattGRHAtLeast (fun _ => -1) :=
  fun h => admissibleHeight_refuses_neg h.1

/-- **At every admissible height the slot implies `PlattGRH`.** So there is no *other* free instance
either: composed with `plattGRH_implies_zeta_zeros_on_line`, any `PlattGRHAtLeast T` implies that
every zero of `ζ` in the critical strip up to height `10⁸` is on the critical line. -/
theorem plattGRH_of_plattGRHAtLeast {T : ℕ → ℝ} (grh : PlattGRHAtLeast T) : PlattGRH :=
  fun q _ hq χ hχ s hs h0 h1 hT => grh.2 q hq χ hχ s hs h0 h1 (le_trans hT (grh.1 q hq))

/-- The RH content of the guarded slot, spelled out. -/
theorem zeta_zeros_on_line_of_plattGRHAtLeast {T : ℕ → ℝ} (grh : PlattGRHAtLeast T) (s : ℂ)
    (hz : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) (hT : |s.im| ≤ 10 ^ 8) :
    s.re = 1 / 2 :=
  plattGRH_implies_zeta_zeros_on_line (plattGRH_of_plattGRHAtLeast grh) s hz h0 h1 hT

theorem plattGRHAtLeast_platt (grh : PlattGRH) : PlattGRHAtLeast (fun q => 10 ^ 8 / (q : ℝ)) :=
  ⟨admissibleHeight_platt, plattGRHAt_platt.mpr grh⟩

/-! ## THE LINKS -/

/-- **Link M1 — the Farey decomposition.** *REACHABLE.*

`∫_𝔐 S³e(−Hα) dα = ∑_{q ≤ P} ∑_{a mod q}^* ∫_{|β| ≤ 1/(q(Q+1))} S(a/q+β)³e(−H(a/q+β)) dβ`.

Pure measure theory plus Farey separation, and both ingredients are discharged here:
`cutoff_separation` gives the disjointness (`2P < Q+1`), `kern_periodic` gives that reduced
residues in `[0,q)` exhaust the major set, and the windows of *non-reduced* `a/q` are contained in
the wider window of the reduced form (whose modulus is smaller, hence still `≤ P`). The library
side is `Goldbach.MinorArc.measurableSet_majorArcs` and
`MeasureTheory.integral_iUnion` / `integral_finset_biUnion`. Fiddly (endpoints of `(0,1]` are
identified only through `kern_periodic`), not deep. **Pointwise** in `H`. -/
def FareyDecomposition : Prop :=
  ∀ H : ℕ, 10 ^ 27 ≤ H →
    majorIntegral H (Pcut H) (Qcut H) = ∑ q ∈ Finset.Icc 1 (Pcut H), arcSum H q (Qcut H)

/-- **Link M2 — the window approximation, under the box hypothesis.** *HARD.* This is the analytic
heart of Helfgott §3 + §7.1–§7.2 and it is where the zero information is spent.

Given that every primitive character of every conductor `q ≤ 3·10⁵` has its zeros up to height
`T q` to the left of `σ`, the total over all moduli of `‖arcSum − T₃(q)·(kernel integral)‖` is
`cW·H^{3/2}(log H)²`. That shape is the classical GRH-conditional major-arc error for the ternary
problem (`𝔖₃(H)H²/2 + O(H^{3/2+ε})`), which is why `errScale` is the right scale here — unlike
`KernelTailBound`, whose loss really is `Θ(H²)`.

* **Route:** `CharacterDecomposition` below splits `S(a/q+β)` over the characters mod `q`; the
  principal character's Gauss sum is `c_q(a) = μ(q)`, giving the main term `(μ(q)/φ(q))U(β)`; every
  other character's twisted sum is bounded by the explicit formula, whose zero sum is
  `O(H^σ log²(qT))` under the box hypothesis and whose tail above `T` is `O(H log²(qH)/T)`.
* **`σ` is the whole content:** `zeroFreeBoxAbove_vacuous_of_one_le` makes this Prop unconditional
  at `σ = 1`, and `windowApproxUnder_antitone_sigma` proves the `σ = 1` form implies the `σ = 1/2`
  form.
* **Why aggregate rather than per-modulus.** The first draft charged each modulus
  `cW·errScale H/P` separately. That is **wrong**: the error from modulus `q` falls off like
  `√q/φ(q)`, so `q = 1` alone carries a constant fraction of the total, not `1/P` of it — the
  per-modulus form was demanding `errScale/300` at `q = 1`, about `300×` below the GRH truth. An
  aggregate statement has no such hidden distributional assumption, and the composition is shorter.
* **The constant `1000` is a budget ceiling, not a claim.** `Spine.pp_slack` charges
  `errScale H` as `H²/10⁴` although the truth at the threshold is `1.22·10⁻¹⁰·H²`, so the budget
  admits `cW ≤ 1000` and no more. If the analysis needs a larger constant the repair is a sharper
  slack lemma: `errScale H ≤ H²/10⁹` is true for `H ≥ 10²⁷` (`log²H = 3865` against
  `√H/10⁹ = 3.16·10⁴`, `8.2×` of room) and would admit `cW ≤ 10⁸`. `10¹⁰` is *false* at the
  threshold, so `10⁹` is the ceiling of that repair. **Pointwise** in `H`.
* **MEASURED 2026-09-29: `cW = 1000` is a ceiling nobody can meet.** In *relative* terms
  `cW·errScale H/(0.66H²)` at `H = 10²⁷` is `1.85·10⁻⁷·(cW/1000)`, so `cW = 1000` asserts a
  major-arc error five orders below the `3.06 %` Helfgott's own §7.4 operates at — and the entire
  admissible range of the `pp_slack` conversion (`cW ≤ 1250`) lies inside that. The reassembly
  budget is *not* the constraint: `0.125H²` is `18.9 %` relative, which contains Helfgott four times
  over. The conversion is. `SingularBridge.errScale_le_sq_sharp` proves `errScale H ≤ H²/10⁸` and
  lifts the ceiling to `cW ≤ 1.25·10⁷` (`0.23 %` relative); `10⁹` is the hard ceiling of this scale
  and gives `cW ≤ 1.25·10⁸` (`2.3 %`), which brackets `3.06 %` only just. Two independent
  triangle-inequality estimates of the aggregate error (agreeing to `1.03×`) put the *crude*
  requirement at `cW ≈ 2.5·10¹⁴`, which this scale meets only from `H ≥ 2.5·10³⁸` — so the crude
  route does not fit at this threshold at all and only a Helfgott-precision treatment can.
  **CAUTION, added 2026-09-29: the companion claim that `cW = 1000` is itself FALSE has been
  RETRACTED** — it compared `cW` against the `3.06 %` Helfgott's analysis BUDGETS for, which is an
  upper bound on affordable loss and so cannot bound the true error from below. `cW = 1000` is
  unproved and of unknown truth. The crude two-estimate figure `cW ≈ 2.5·10¹⁴` quoted just above is
  a requirement of a CRUDE route, not a lower bound on the truth either. Parameterising is still
  right, because it stops the chain depending on one unproved constant:
  `SingularBridge.majorArcLower_of_chain_param` carries `cW`, `cK` and the slack scale as parameters
  with the budget as a visible side condition. `WindowApproxUnder` itself is unchanged — it was
  always parametric in `cW`, and it is the *instantiation* at `1000` that the numbers refuse. -/
def WindowApproxUnder (cW σ : ℝ) (T : ℕ → ℝ) : Prop :=
  ZeroBoxes T σ → ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H →
    ∑ q ∈ Finset.Icc 1 (Pcut H),
        ‖arcSum H q (Qcut H) - ((localTerm q H : ℝ) : ℂ) * kernelIntegral H q (Qcut H)‖
      ≤ cW * errScale H

/-- **Link M3 — the kernel truncation loss.** *REACHABLE, and it is where the window *width* is
the design parameter.*

`∑_{q ≤ P} ‖T₃(q)·(∫_{|β| ≤ w_q} U³e(−Hβ) − H²/2)‖ ≤ cK·H²`.

Over the whole circle `∫₀¹ U(β)³e(−Hβ) dβ` is the ordered-triple count `(H−1)(H−2)/2`; truncating
to `|β| ≤ w_q = W/(qH)` loses at most `∫_{w_q < |β| ≤ 1/2}|U|³ ≤ 1/(8w_q²) = q²H²/(8W²)` because
`|U(β)| ≤ 1/(2‖β‖)`. Weighted by `|T₃(q)| ≤ q/φ(q)³` and summed over `q ≤ 3·10⁵`, the loss is
`≈ 1.6619·10⁵·H²/W²` (**corrected 2026-09-29 from `4.33·10⁵`, which was wrong; recomputed twice,
by the round-5 audit's SPF sieve and independently by the coordinator**); at Helfgott's `W =
δ₀r₀ = 1.2·10⁶` that is `3.01·10⁻⁷·H²`, inside the `cK =
10⁻⁵` charged here by `87×` (was quoted as `33×` with the wrong coefficient) and inside the
whole `0.125·H²` budget by `4.2·10⁵`. It meets the full
budget as soon as `W ≳ 1.9·10³` and the `cK = 10⁻⁵` charged here as soon as **`W ≳ 2.1·10⁵`**, so
this link is comfortable *at these cutoffs* and would fail at a narrow dissection — the second half
of the "few and narrow" trade, the first half being `Spine.MinorSupBound`. The library side is
`Goldbach.MinSum.exp_sum_le_sin`
(`‖∑ e(nα)‖ ≤ 1/|sin πα|`).

**Why `H²` and not `errScale`.** This was charged against `H^{3/2}(log H)²` in the first draft of
this file, and that is **wrong — it is a scale error, not a constant error.** The window half-width
is `W/(qH)` with `W` a *constant*, so the tail `1/(8w_q²)` is `Θ(H²)`: the ratio to
`H^{3/2}(log H)²` grows without bound, and already at `H = 10²⁷` the true loss `3.0·10⁴⁷` exceeds
`100·errScale = 1.22·10⁴⁶` by `24.6×`. Only the *analytic* error (`WindowApproxUnder`) lives on the
`H^{3/2}` scale; the geometric truncation does not, and mixing them silently would have produced a
chain whose hypotheses were unsatisfiable for a reason invisible in the prose.
**Pointwise** in `H`. -/
def KernelTailBound (cK : ℝ) : Prop :=
  ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H →
    ∑ q ∈ Finset.Icc 1 (Pcut H),
        ‖((localTerm q H : ℝ) : ℂ) * (kernelIntegral H q (Qcut H) - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ))‖
      ≤ cK * (H : ℝ) ^ 2

/-- **The reassembled major-arc integral.** What M1–M3 deliver, and what the budget consumes. -/
def MajorReassembly (cErr : ℝ) : Prop :=
  ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H →
    ‖majorIntegral H (Pcut H) (Qcut H) - ((mainTerm H (Pcut H) : ℝ) : ℂ)‖ ≤ cErr * (H : ℝ) ^ 2

/-! ## The monotonicity theorems — where the content of the GRH hypothesis sits -/

/-- **A stronger box gives a weaker link.** `σ ≤ τ` means the `τ`-conditional statement implies the
`σ`-conditional one, so `WindowApproxUnder cW 1 T` (unconditional, by
`zeroFreeBoxAbove_vacuous_of_one_le`) implies `WindowApproxUnder cW (1/2) T`. **The reduction to
Platt is exactly this gap and nothing more**, which is the honest answer to "would the chain
compose with the verification replaced by `True`": it would, with a strictly stronger hypothesis,
and here is the implication that proves which is stronger. -/
theorem windowApproxUnder_antitone_sigma {cW σ τ : ℝ} {T : ℕ → ℝ} (hστ : σ ≤ τ)
    (h : WindowApproxUnder cW τ T) : WindowApproxUnder cW σ T := by
  intro zb
  exact h (fun q _ hq χ hχ => zeroFreeBoxAbove_mono hστ (zb q hq χ hχ))

/-- **A higher verified height gives a weaker link**, for the same reason. So the pair
(`plattGRHAt_antitone`, this) fixes the geometry: the input strengthens and the link weakens as
`T` grows, and the two must be quoted at the same height. -/
theorem windowApproxUnder_mono_height {cW σ : ℝ} {T T' : ℕ → ℝ} (hT : ∀ q, T q ≤ T' q)
    (h : WindowApproxUnder cW σ T) : WindowApproxUnder cW σ T' := by
  intro zb
  exact h (fun q _ hq χ hχ s hs h0 h1 hs' => zb q hq χ hχ s hs h0 h1 (le_trans hs' (hT q)))

/-! ## The reassembly, proved -/

/-- `𝔖₃(H,P)·H²/2`, expanded over the moduli. -/
theorem ofReal_mainTerm (H P : ℕ) :
    ((mainTerm H P : ℝ) : ℂ)
      = ∑ q ∈ Finset.Icc 1 P, ((localTerm q H : ℝ) : ℂ) * (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ) := by
  have h1 : mainTerm H P = ∑ q ∈ Finset.Icc 1 P, localTerm q H * ((H : ℝ) ^ 2 / 2) := by
    rw [mainTerm, singSeriesTrunc, ← Finset.sum_mul]; ring
  rw [h1, Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun q _ => by push_cast; ring)

/-- **M1 + M2 + M3 ⇒ the reassembly.** Function application, one triangle inequality per modulus,
and `Spine.pp_slack` to bring the analytic `H^{3/2}(log H)²` charge onto the `H²` scale the budget
speaks. Both M2 and M3 are stated as sums over `Finset.Icc 1 (Pcut H)`, so the two aggregate
errors simply add. -/
theorem majorReassembly_of_chain {cW cK σ : ℝ} {T : ℕ → ℝ} (hcW : 0 ≤ cW)
    (zb : ZeroBoxes T σ) (fd : FareyDecomposition) (wa : WindowApproxUnder cW σ T)
    (kt : KernelTailBound cK) :
    MajorReassembly (cW / 10 ^ 4 + cK) := by
  intro H hodd hH
  have hstep : ∀ q ∈ Finset.Icc 1 (Pcut H),
      ‖arcSum H q (Qcut H) - ((localTerm q H : ℝ) : ℂ) * (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ)‖
        ≤ ‖arcSum H q (Qcut H) - ((localTerm q H : ℝ) : ℂ) * kernelIntegral H q (Qcut H)‖
          + ‖((localTerm q H : ℝ) : ℂ)
              * (kernelIntegral H q (Qcut H) - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ))‖ := by
    intro q _
    have hsplit : arcSum H q (Qcut H) - ((localTerm q H : ℝ) : ℂ) * (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ)
        = (arcSum H q (Qcut H) - ((localTerm q H : ℝ) : ℂ) * kernelIntegral H q (Qcut H))
          + ((localTerm q H : ℝ) : ℂ)
              * (kernelIntegral H q (Qcut H) - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ)) := by ring
    rw [hsplit]
    exact norm_add_le _ _
  rw [fd H hH, ofReal_mainTerm, ← Finset.sum_sub_distrib]
  calc ‖∑ q ∈ Finset.Icc 1 (Pcut H),
          (arcSum H q (Qcut H) - ((localTerm q H : ℝ) : ℂ) * (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ))‖
      ≤ ∑ q ∈ Finset.Icc 1 (Pcut H),
          ‖arcSum H q (Qcut H) - ((localTerm q H : ℝ) : ℂ) * (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 (Pcut H),
          (‖arcSum H q (Qcut H) - ((localTerm q H : ℝ) : ℂ) * kernelIntegral H q (Qcut H)‖
            + ‖((localTerm q H : ℝ) : ℂ)
                * (kernelIntegral H q (Qcut H) - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ))‖) :=
        Finset.sum_le_sum hstep
    _ = (∑ q ∈ Finset.Icc 1 (Pcut H),
            ‖arcSum H q (Qcut H) - ((localTerm q H : ℝ) : ℂ) * kernelIntegral H q (Qcut H)‖)
          + ∑ q ∈ Finset.Icc 1 (Pcut H), ‖((localTerm q H : ℝ) : ℂ)
              * (kernelIntegral H q (Qcut H) - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ))‖ :=
        Finset.sum_add_distrib
    _ ≤ cW * errScale H + cK * (H : ℝ) ^ 2 := add_le_add (wa zb H hodd hH) (kt H hodd hH)
    _ ≤ cW * ((H : ℝ) ^ 2 / 10 ^ 4) + cK * (H : ℝ) ^ 2 := by
        have h3 : cW * errScale H ≤ cW * ((H : ℝ) ^ 2 / 10 ^ 4) :=
          mul_le_mul_of_nonneg_left (errScale_le_sq H hH) hcW
        linarith
    _ = (cW / 10 ^ 4 + cK) * (H : ℝ) ^ 2 := by ring

/-! ## The budget, and the headline theorem -/

/-- **The arithmetic half, and it is all of the remaining work.** `Re` of a complex number is at
least its real approximant minus the norm of the difference; the main term is `𝔖₃(H,P)H²/2`; and
the reassembly's error is charged on the `H²` scale. The side condition `cMaj + cErr ≤ cSing/2`
is the whole budget; at the instantiated constants it leaves `0.025·H²` of margin. -/
theorem majorArcLower_of_reassembly {cErr cSing cMaj : ℝ}
    (hbudget : cMaj + cErr ≤ cSing / 2)
    (ss : SingularSeriesLower cSing) (mr : MajorReassembly cErr) :
    MajorArcLower Pcut Qcut cMaj := by
  intro H hodd hH
  have hH2 : (0 : ℝ) ≤ (H : ℝ) ^ 2 := sq_nonneg _
  have h1 := mr H hodd hH
  have h2 := ss H hodd hH
  have h3 : |(majorIntegral H (Pcut H) (Qcut H)).re - mainTerm H (Pcut H)|
      ≤ cErr * (H : ℝ) ^ 2 := by
    have h4 := Complex.abs_re_le_norm
      (majorIntegral H (Pcut H) (Qcut H) - ((mainTerm H (Pcut H) : ℝ) : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at h4
    exact le_trans h4 h1
  have h5 : mainTerm H (Pcut H) - cErr * (H : ℝ) ^ 2
      ≤ (majorIntegral H (Pcut H) (Qcut H)).re := by
    have := (abs_le.mp h3).1
    linarith
  have h6 : cSing * ((H : ℝ) ^ 2 / 2) ≤ mainTerm H (Pcut H) := by
    rw [mainTerm, show singSeriesTrunc H (Pcut H) * (H : ℝ) ^ 2 / 2
      = singSeriesTrunc H (Pcut H) * ((H : ℝ) ^ 2 / 2) by ring]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have h8 : cMaj * (H : ℝ) ^ 2 ≤ cSing * ((H : ℝ) ^ 2 / 2) - cErr * (H : ℝ) ^ 2 := by
    nlinarith [hbudget, hH2]
  linarith

/-- **THE HEADLINE.** `MajorArcLower Pcut Qcut (1/2)` — the major-arc link the spine's main
instantiation wants — from Platt's verification at an **admissible** height `T`, the Farey
decomposition, the per-modulus window approximation and the kernel truncation, plus the singular
series' truncation tail (now discharged: `SingularBridge.singularSeriesLower_holds`).

**REPAIRED 2026-09-29 (free rider).** The numerical slot was `PlattGRHAt T` with `T` unconstrained,
and was therefore a *free rider*: instantiating `T = fun _ => −1` discharges it outright
(`plattGRHAt_vacuous_of_neg`), so the theorem reduced nothing to Platt. It is now
`PlattGRHAtLeast T = AdmissibleHeight T ∧ PlattGRHAt T`, one hypothesis with no inert component;
`plattGRHAtLeast_refuses_neg` proves the degenerate instance is refused, and
`plattGRH_of_plattGRHAtLeast` proves every admissible instance carries `PlattGRH` — hence a piece of
RH — so no free instance survives. See the guard section above for why the height stays a parameter.

**THE CONSTANT `1000` IS MEASURED AS OUT OF REACH, and this is the second defect of this theorem.**
`cW = 1000` asserts a major-arc error of `1000·errScale H = 1.22·10⁻⁷·H²` at `H = 10²⁷`, i.e. a
**relative** error of `1.85·10⁻⁷` against the `0.66H²` main term — five orders of magnitude tighter
than the `3.06 %` Helfgott's own §7.4 operates at. Nothing in this file's route, and nothing in the
literature, delivers that. The fault is *not* the budget: the reassembly is allowed `0.125H²`, i.e.
`18.9 %` relative, which comfortably contains Helfgott. The fault is the conversion — `pp_slack`
charges `errScale` as `H²/10⁴` and so caps `cW ≤ 1250` no matter how much budget there is. Since a
chain resting on a false hypothesis is *vacuous*, the constant must not be baked in:
`SingularBridge.majorArcLower_of_chain_param` is this theorem with `cW`, `cK` and the slack
**scale**
as parameters and the budget as a visible side condition, and
`SingularBridge.errScale_le_sq_sharp` lifts the ceiling to `cW ≤ 1.25·10⁷`. The hard ceiling of the
`H^{3/2}(log H)²` scale at this threshold is `10⁹` (`errScale ≤ H²/10¹⁰` is *false* at `H = 10²⁷`),
i.e. `cW ≤ 1.25·10⁸` = `2.3 %` relative — which brackets Helfgott's `3.06 %` only just. **So the
scale itself has about one order of slack at `10²⁷`, and this instantiation spends five it does not
have.** Kept at `1000` here because it is what the spine's instantiation and the two height variants
below quote; read it as a placeholder whose honest form is the parametric theorem. -/
theorem majorArcLower_of_chain {T : ℕ → ℝ} (grh : PlattGRHAtLeast T) (fd : FareyDecomposition)
    (wa : WindowApproxUnder 1000 (1 / 2) T) (kt : KernelTailBound (1 / 10 ^ 5))
    (ss : SingularSeriesLower (5 / 4)) :
    MajorArcLower Pcut Qcut (1 / 2) :=
  majorArcLower_of_reassembly (by norm_num) ss
    (majorReassembly_of_chain (by norm_num) (zeroBoxes_of_plattGRHAt grh.2) fd wa kt)

/-- The same at **Platt's actual verified height** `T_q = 10⁸/q`. True as a theorem; the header's
measurement says `wa` is out of reach at this height for `q` beyond `≈1.5·10³`, and
`majorArcLower_of_chain_extended` is the repair. -/
theorem majorArcLower_of_chain_platt (grh : PlattGRH) (fd : FareyDecomposition)
    (wa : WindowApproxUnder 1000 (1 / 2) (fun q => 10 ^ 8 / (q : ℝ)))
    (kt : KernelTailBound (1 / 10 ^ 5)) (ss : SingularSeriesLower (5 / 4)) :
    MajorArcLower Pcut Qcut (1 / 2) :=
  majorArcLower_of_chain (plattGRHAtLeast_platt grh) fd wa kt ss

/-- **The repair, stated: 224× Platt's height.** Identical chain at `T_q = 2.24·10¹⁰/q`, the height
at which the sharp-cutoff explicit-formula tail `log²(qH)/T_q` is inside the `7.5 %` budget for
every `q ≤ 3·10⁵`. Nothing else in the chain moves; the cost is `≈250×` more zeros
(`≈1.4·10¹⁶` against Platt's `5.5·10¹³`). -/
theorem majorArcLower_of_chain_extended
    (grh : PlattGRHAt (fun q => 2.24 * 10 ^ 10 / (q : ℝ))) (fd : FareyDecomposition)
    (wa : WindowApproxUnder 1000 (1 / 2) (fun q => 2.24 * 10 ^ 10 / (q : ℝ)))
    (kt : KernelTailBound (1 / 10 ^ 5)) (ss : SingularSeriesLower (5 / 4)) :
    MajorArcLower Pcut Qcut (1 / 2) :=
  majorArcLower_of_chain ⟨admissibleHeight_extended, grh⟩ fd wa kt ss

/-- **Attack: let Platt be a free rider.** With `σ = 1` the box hypothesis is free
(`zeroFreeBoxAbove_vacuous_of_one_le`), so the chain runs with **no** `PlattGRHAt` in its
signature. Read with `windowApproxUnder_antitone_sigma` — which proves this `σ = 1` hypothesis
*implies* the `σ = 1/2` one — this is the measurement of what assuming Platt buys: exactly the gap
between the two, and nothing else. The analogue of `Spine.spine_needs_grh`. -/
theorem majorArcLower_of_unconditional {T : ℕ → ℝ} (fd : FareyDecomposition)
    (wa : WindowApproxUnder 1000 1 T) (kt : KernelTailBound (1 / 10 ^ 5))
    (ss : SingularSeriesLower (5 / 4)) :
    MajorArcLower Pcut Qcut (1 / 2) :=
  majorArcLower_of_reassembly (by norm_num) ss
    (majorReassembly_of_chain (T := T) (σ := 1) (by norm_num)
      (zeroBoxes_vacuous_of_one_le (le_refl 1)) fd wa kt)

/-! ## Composition with the spine -/

/-- **The spine, with the major-arc half reduced to Platt.** What remains open is the
circle-method identity, the minor-arc sup bound, the prime-power removal (the other three spine
links, each owned by a sibling file this round), and inside the major arcs: the Farey
decomposition, the window approximation, the kernel truncation and the singular-series tail. -/
theorem ternaryLogCountLower_of_platt_chain (grh : PlattGRH) (fd : FareyDecomposition)
    (wa : WindowApproxUnder 1000 (1 / 2) (fun q => 10 ^ 8 / (q : ℝ)))
    (kt : KernelTailBound (1 / 10 ^ 5)) (ss : SingularSeriesLower (5 / 4))
    (cm : CircleMethodIdentity) (mn : MinorSupBound Pcut Qcut (3 / 10))
    (pp : PrimePowerRemoval 10) :
    TernaryLogCountLower :=
  ternaryLogCountLower_of_links_main Pcut Qcut cm
    (majorArcLower_of_chain_platt grh fd wa kt ss) mn pp

/-- …and on to the EP1054 chain's one trusted input. -/
theorem cite_Helfgott_weighted_of_platt_chain (grh : PlattGRH) (fd : FareyDecomposition)
    (wa : WindowApproxUnder 1000 (1 / 2) (fun q => 10 ^ 8 / (q : ℝ)))
    (kt : KernelTailBound (1 / 10 ^ 5)) (ss : SingularSeriesLower (5 / 4))
    (cm : CircleMethodIdentity) (mn : MinorSupBound Pcut Qcut (3 / 10))
    (pp : PrimePowerRemoval 10) :
    Principia.Erdos1054.Cite_Helfgott_weighted :=
  cite_Helfgott_weighted_of_logCount
    (ternaryLogCountLower_of_platt_chain grh fd wa kt ss cm mn pp)

/-! ## The character decomposition — STATED, NOT COMPOSED

The one ingredient of `WindowApproxUnder` that is worth transcribing exactly and is *not* used by
any theorem above. It is recorded so the next round has the correct normalization in Lean rather
than in prose, and because Mathlib now has what it needs: `DirichletCharacter.Orthogonality`
supplies the `Fintype (DirichletCharacter R n)` instance and
`DirichletCharacter.sum_char_inv_mul_char_eq : ∑ χ, χ a⁻¹ * χ b = if a = b then φ(n) else 0`.
Saying "not composed" out loud is cheaper than pretending a Prop carries weight it does not. -/

/-- `∑_{0 < n ≤ H, (n,q)=1} Λ(n)e(nα)` — `Spine.expSum` with the divisors of `q` removed. -/
noncomputable def coprimeExpSum (H q : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Ioc 0 H).filter (fun n => Nat.gcd n q = 1), ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)

/-- **Transcription probe.** At `q = 1` nothing is removed, so `coprimeExpSum` is `Spine.expSum`
character for character. If this compiles, the object is the right one. -/
theorem coprimeExpSum_one (H : ℕ) (α : ℝ) : coprimeExpSum H 1 α = expSum H α := by
  rw [coprimeExpSum, expSum, Finset.filter_true_of_mem]
  intro n _
  exact Nat.gcd_one_right n

/-- `∑_{0 < n ≤ H} Λ(n)χ(n)e(nβ)`, the character-twisted exponential sum. `χ` vanishes off the
units, so the coprimality restriction is automatic. -/
noncomputable def twistedSum (H q : ℕ) (χ : DirichletCharacter ℂ q) (β : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 H, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * e ((n : ℝ) * β)

/-- `τ(χ̄, a) = ∑_{b mod q}^* χ(b⁻¹)e(ab/q)`, the Gauss sum in the normalization
`DirichletCharacter.sum_char_inv_mul_char_eq` uses. At the principal character it is the Ramanujan
sum `c_q(a) = μ(q)` for `(a,q) = 1`, which is where `μ(q)/φ(q)` in the main term comes from. -/
noncomputable def gaussTwist (q : ℕ) (χ : DirichletCharacter ℂ q) (a : ℕ) : ℂ :=
  ∑ b ∈ (Finset.range q).filter (fun b => Nat.gcd b q = 1),
    χ ((b : ZMod q)⁻¹) * e ((a : ℝ) * b / q)

/-- **The character decomposition.** *REACHABLE; stated, not composed.*

`φ(q)·∑_{n ≤ H, (n,q)=1} Λ(n)e(n(a/q+β)) = ∑_{χ mod q} τ(χ̄,a)·∑_{n ≤ H} Λ(n)χ(n)e(nβ)`.

An **exact** identity, from character orthogonality: expanding the right side and summing over `χ`
first gives `φ(q)` when `n ≡ b` mod `q` and `0` otherwise, and `e(ab/q) = e(an/q)` for `n ≡ b`.
This is the first step of Helfgott §3, and the step at which the major-arc analysis becomes a
statement about `L`-functions at all. -/
def CharacterDecomposition : Prop :=
  ∀ (H q : ℕ), 0 < q → ∀ a : ℕ, Nat.gcd a q = 1 → ∀ β : ℝ,
    (Nat.totient q : ℂ) * coprimeExpSum H q ((a : ℝ) / (q : ℝ) + β)
      = ∑ χ : DirichletCharacter ℂ q, gaussTwist q χ a * twistedSum H q χ β

/-! ## THE MEASUREMENT, as kernel-checked arithmetic

Two numbers behind the header's finding. They are facts about `Real.log`; the claim that they *are*
the sharp-cutoff explicit-formula tail `log²(qH)/T_q` at Platt's height `T_q = 10⁸/q` is prose, and
is labelled as such. Both are proved from `Real.log_two_lt_d9` / `Real.log_two_gt_d9` by bracketing
`q·10²⁷` between powers of two. -/

/-- **Platt's height is enough at `q = 1500`**: `q log²(qH)/10⁸ ≤ 3/40 = 7.5 %` there, via
`1.5·10³⁰ ≤ 2¹⁰¹` and `101 log 2 ≤ 70.01`. -/
theorem platt_tail_ok_at_1500 :
    1500 * Real.log ((1500 : ℝ) * 10 ^ 27) ^ 2 / 10 ^ 8 ≤ 3 / 40 := by
  have hpow : Real.log ((2 : ℝ) ^ (101 : ℕ)) = 101 * Real.log 2 := by
    rw [Real.log_pow]; norm_num
  have hmono : Real.log ((1500 : ℝ) * 10 ^ 27) ≤ Real.log ((2 : ℝ) ^ (101 : ℕ)) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [hpow] at hmono
  have hscale : 101 * Real.log 2 ≤ 101 * 0.6931471808 :=
    mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_lt_d9) (by norm_num)
  have hnum : (101 : ℝ) * 0.6931471808 ≤ 70.01 := by norm_num
  have hlb : (0 : ℝ) ≤ Real.log ((1500 : ℝ) * 10 ^ 27) := Real.log_nonneg (by norm_num)
  have hub2 : Real.log ((1500 : ℝ) * 10 ^ 27) ≤ 70.01 :=
    le_trans (le_trans hmono hscale) hnum
  have hsq : Real.log ((1500 : ℝ) * 10 ^ 27) ^ 2 ≤ 5000 := by nlinarith [hlb, hub2]
  have hfin : (1500 : ℝ) * Real.log ((1500 : ℝ) * 10 ^ 27) ^ 2 / 10 ^ 8
      ≤ 1500 * 5000 / 10 ^ 8 := by gcongr
  linarith

/-- **Platt's height is not enough at the top modulus**: `q log²(qH)/10⁸ ≥ 16` at `q = 3·10⁵`,
against an affordable `3/40`, via `2¹⁰⁷ ≤ 3·10³²` and `107 log 2 ≥ 74.16`. The truth is `16.78`,
i.e. the budget is exceeded by `224×` — the file's headline finding, and the reason
`majorArcLower_of_chain_extended` exists. -/
theorem platt_tail_exceeds_at_top_modulus :
    (16 : ℝ) ≤ 300000 * Real.log ((300000 : ℝ) * 10 ^ 27) ^ 2 / 10 ^ 8 := by
  have hpow : Real.log ((2 : ℝ) ^ (107 : ℕ)) = 107 * Real.log 2 := by
    rw [Real.log_pow]; norm_num
  have hmono : Real.log ((2 : ℝ) ^ (107 : ℕ)) ≤ Real.log ((300000 : ℝ) * 10 ^ 27) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [hpow] at hmono
  have hscale : 107 * (0.6931471803 : ℝ) ≤ 107 * Real.log 2 :=
    mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_gt_d9) (by norm_num)
  have hnum : (74 : ℝ) ≤ 107 * (0.6931471803 : ℝ) := by norm_num
  have hlb : (74 : ℝ) ≤ Real.log ((300000 : ℝ) * 10 ^ 27) := by linarith
  have hsq : (5476 : ℝ) ≤ Real.log ((300000 : ℝ) * 10 ^ 27) ^ 2 := by nlinarith [hlb]
  have hfin : (300000 : ℝ) * 5476 / 10 ^ 8
      ≤ 300000 * Real.log ((300000 : ℝ) * 10 ^ 27) ^ 2 / 10 ^ 8 := by gcongr
  have hnum2 : (16 : ℝ) ≤ 300000 * (5476 : ℝ) / 10 ^ 8 := by norm_num
  linarith

/-! ## THE ADVERSARIAL PASS, as theorems

Every link above is a statement about concretely defined objects (`Spine.majorIntegral`,
`arcSum`, `kernelIntegral`, `SingularSeries.localTerm`, `DirichletCharacter.LFunction`), so none
of them has a function, measure or witness to instantiate degenerately. What remains are the
*parameters*, and each is pinned by a theorem. -/

/-- **Attack 1: make the cutoffs degenerate.** `Spine.minorSet_one_one` shows that at `P = Q = 1`
the minor set is empty and the arc split buys nothing. At *these* cutoffs it is not: `1/600001` is
in the minor set for every `H ≥ 10^27`. The witness is the Farey point of the *smallest* modulus
above `2P`, and the computation is the standard one — for every `q ≤ P` and every `a : ℤ`,
`|1/600001 − a/q| = |q − 600001a|/(600001q) ≥ 1/(600001q)` because `600001 ∤ q`, while the window
has half-width `1/(q(Q+1))` and `Q + 1 > 600001`. -/
theorem minorSet_nonempty_at_cutoffs (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    (1 / 600001 : ℝ) ∈ minorSet (Pcut H) (Qcut H) := by
  have hQ : 600001 ≤ Qcut H := by
    have h1 : 600001 * 1200000 ≤ H := le_trans (by norm_num) hH
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr h1
  have hQR : (600001 : ℝ) ≤ (Qcut H : ℝ) := by exact_mod_cast hQ
  refine ⟨⟨by norm_num, by norm_num⟩, fun hmem => ?_⟩
  simp only [MajorArcs, Set.mem_iUnion, Set.mem_Icc, Metric.mem_closedBall, Real.dist_eq,
    exists_prop] at hmem
  obtain ⟨q, ⟨hq1, hqP⟩, a, hball⟩ := hmem
  have hq300 : q ≤ 300000 := by rw [← Pcut_apply H]; exact hqP
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hqRP : (q : ℝ) ≤ 300000 := by exact_mod_cast hq300
  have hnum : (q : ℤ) - 600001 * a ≠ 0 := by
    intro h
    have hdvd : (600001 : ℤ) ∣ (q : ℤ) := ⟨a, by linarith⟩
    have h2 : (600001 : ℤ) ≤ (q : ℤ) := Int.le_of_dvd (by exact_mod_cast hq1) hdvd
    have h3 : (q : ℤ) ≤ 300000 := by exact_mod_cast hq300
    omega
  have habs : (1 : ℝ) ≤ |((((q : ℤ) - 600001 * a : ℤ)) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hnum
  have heq : (1 / 600001 : ℝ) - (a : ℝ) / (q : ℝ)
      = ((((q : ℤ) - 600001 * a : ℤ)) : ℝ) / (600001 * (q : ℝ)) := by
    push_cast
    field_simp
  have hstrict : 1 / ((q : ℝ) * ((Qcut H : ℝ) + 1))
      < |(1 / 600001 : ℝ) - (a : ℝ) / (q : ℝ)| := by
    rw [heq, abs_div, abs_of_pos (show (0 : ℝ) < 600001 * (q : ℝ) by positivity),
      div_lt_div_iff₀ (by positivity) (by positivity)]
    have h1 : (1 : ℝ) * ((q : ℝ) * ((Qcut H : ℝ) + 1))
        ≤ |((((q : ℤ) - 600001 * a : ℤ)) : ℝ)| * ((q : ℝ) * ((Qcut H : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right habs (by positivity)
    have h2 : 600001 * (q : ℝ) < (q : ℝ) * ((Qcut H : ℝ) + 1) := by nlinarith [hQR, hqR]
    linarith
  linarith

/-- **Attack 2: spend the whole budget.** The reassembly may lose at most
`(cSing/2 − cMaj)·H² = 0.125·H²` at the instantiated constants. `WindowApproxUnder`'s charge
`1000·errScale H` is `1.22·10⁻⁷·H²` at the threshold and shrinks relative to `H²` thereafter — six
orders inside; a full `H²` of error is refused outright, and this is the inequality that refuses
it. So the error bound in `WindowApproxUnder` is not a free parameter, and the *scale* it sits on
is the thing `KernelTailBound`'s docstring records getting wrong. -/
theorem budget_refuses_quadratic_scale (H : ℕ) (hH : 10 ^ 27 ≤ H) :
    1000 * errScale H ≤ (H : ℝ) ^ 2 / 8 ∧ ¬ ((H : ℝ) ^ 2 ≤ (H : ℝ) ^ 2 / 8) := by
  have hHR : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH
  have h10 : (0 : ℝ) < (10 : ℝ) ^ 27 := by positivity
  have hHpos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le h10 hHR
  have hpos : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · have h1 := errScale_le_sq H hH
    nlinarith [h1, hpos]
  · intro hcon
    linarith [hpos, hcon]

/-- **Normalization probe for `localTerm`.** `T₃(1) = 1`, so the `q = 1` term of the singular
series is the bare main term and the whole of `𝔖₃ − 1` is the arithmetic correction. -/
theorem localTerm_one (H : ℕ) : localTerm 1 H = 1 := by
  simp [localTerm, cRam_one]

/-- **Normalization probe for `arcSum`.** At `q = 1` there is exactly one Farey window, the one
about `0`; by `kern_periodic` it is also the one about `1`. -/
theorem arcSum_one (H Q : ℕ) : arcSum H 1 Q = windowIntegral H 1 Q 0 := by
  simp [arcSum]

/-- `𝔖₃(H, 1) = 1`. -/
theorem singSeriesTrunc_one (H : ℕ) : singSeriesTrunc H 1 = 1 := by
  simp [singSeriesTrunc, localTerm_one]

/-- **Attack 4: make the modulus cutoff degenerate on the singular-series side too.** At `P = 1`
the truncated series is exactly `1`, so `SingularSeriesLower` at any constant above `1` is **false**
there. The margin `cSing − 1 = 1/4` is bought entirely by the moduli `2 ≤ q ≤ 3·10⁵`, which is the
third certificate (with `cutoff_separation` and `minorSet_nonempty_at_cutoffs`) that the cutoffs are
not decoration: the Euler factor at `2` alone contributes a factor `2` for odd `H`. -/
theorem singularSeriesLower_fails_at_trivial_cutoff :
    ¬ (∀ H : ℕ, Odd H → 10 ^ 27 ≤ H → (5 : ℝ) / 4 ≤ singSeriesTrunc H 1) := by
  intro h
  have h1 := h (10 ^ 27 + 1) ⟨5 * 10 ^ 26, by norm_num⟩ (by norm_num)
  rw [singSeriesTrunc_one] at h1
  norm_num at h1

/-- **Attack 3: satisfy the major-arc link with a non-positive constant.** `Spine`'s
`lowerWith_nonpos_free` already shows the *goal* is free at `c ≤ 0`; the same is true one level up,
and it locates all of this file's content in the positive margin `cSing/2 − cErr/10⁴`. The
`Re`-part of the major integral can be negative (it is an integral of a complex kernel), so this is
not immediate from non-negativity — it needs the reassembly, which is the point: **there is no
cheap way to satisfy `MajorArcLower` even at `cMaj = 0`**. Recorded as the budget instance at
`cMaj = 0`, where the requirement on the singular series drops to `cSing ≥ 2·cErr/10⁴`. -/
theorem majorArcLower_zero_of_reassembly {cErr : ℝ}
    (ss : SingularSeriesLower (2 * cErr)) (mr : MajorReassembly cErr) :
    MajorArcLower Pcut Qcut 0 :=
  majorArcLower_of_reassembly (by rw [zero_add]; exact le_of_eq (by ring)) ss mr

end Principia.Common.TernaryGoldbach.MajorPlatt
