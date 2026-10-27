# HRT at Λ₀ = {(0,0), (1,0), (0,1), (√2,√2)} — two routes, Lean 4

**What is machine-checked here, in one sentence:** two independent Lean developments of the
paper `paper/hrt-lambda0.tex`, each **conditional on one explicitly named hypothesis** —
neither claims the HRT subconjecture at `Λ₀` unconditionally in Lean.

## The problem

The Heil–Ramanathan–Topiwala (HRT) conjecture asserts that finitely many time–frequency
translates of a nonzero `g ∈ L²(ℝ)` are linearly independent. The four-point configuration

```
Λ₀ = {(0,0), (1,0), (0,1), (√2,√2)}
```

is a distinguished open special case: it is **Conjecture 2 (HRT Subconjecture)** of the
Heil–Speegle survey — *"If g ∈ S(ℝ)\{0}, then {g(x), g(x−1), e^{2πix}g(x), e^{2πi√2x}g(x−√2)}
is linearly independent"*, their equation (5) naming exactly Λ₀ — and Conjecture 9.2(a) of
Heil's 2006 survey. It is **unreachable** from the solved lattice (Linnell) and parallel-line
cases; `lambda0_symplectic_escape` proves that obstruction inside Lean.

## The paper

`paper/hrt-lambda0.tex` (built to `paper/hrt-lambda0.pdf`, 12pp) proves two theorems about the
resonant family `Λ_{a,j} = {(0,0),(1,0),(0,1),(a,a+j)}`, `a` irrational, `j ∈ ℤ\{−1,1}`:

| | window class | status |
|---|---|---|
| **Theorem 1** | `g` with continuous Zak transform (⊇ Schwartz, `W(C,ℓ¹)`) | **unconditional** |
| **Theorem 2** | **every** nonzero `g ∈ L²(ℝ)` | conditional on Iwanik–Lemańczyk–Rudolph |

Theorem 1 at `a=√2, j=0` settles Heil–Speegle Conjecture 2 **as stated** (their hypothesis is
`g ∈ S(ℝ)`). Theorem 2 removes every regularity hypothesis but quotes one published spectral
theorem rather than reproving it.

Both theorems pass through the same central identity — the root count `N(θ) = j+1` — reached
by two genuinely different arguments. Under continuity a degree is available and the identity
is *forced* by invariance of the degree of a circle map under precomposition with a rotation;
in `L²` no degree exists and the identity is instead *deduced* from a spectral obstruction.
Neither argument subsumes the other; see the paper's Remark 8.

## The two Lean developments

Both are in this directory, as two separate `lean_lib`s so their import closures stay
independent.

### Route I — `HRTLambda0` (the endgame; Comparator-certified)

```lean
theorem HRTLambda0.Statement.lambda0_independent_of_reduction {g : ℝ → ℂ}
    (h : HRTLambda0.ZakReduction g) : HRTLambda0.Lambda0Independent g
```

*If the paper's analytic reduction applies to `g`, then the four translates are linearly
independent.* `#print axioms`: exactly `[propext, Classical.choice, Quot.sound]`.

**The hypothesis is the honesty-critical part.** `ZakReduction g`
(`HRTLambda0/Statement.lean`) packages the paper's pre-endgame analysis — the Zak reduction,
the fibre dichotomy, the degree identity at `j = 0`, and Jensen's formula on the fibre — and
**none of that is proved in this library.**

| paper item | Lean |
|---|---|
| Remark 4 — `Λ₀` escapes the solved cases | `lambda0_symplectic_escape` |
| Lemma 6 (dichotomy), propagation step | `zero_propagates` |
| Lemma 6 (dichotomy), full | `fibre_dichotomy` |
| Prop. 7 (root count), arithmetic core (`\|j\| ≥ 2` dies) | `degree_identity_kills` |
| quadratic rigidity | `two_of_three_eq_of_quadratic` |
| two-circle rigidity (continuity-free strengthening) | `circle_pair_quadratic` |
| Lemma 13 (Vieta) — Jensen constancy vs Vieta ⇒ contradiction | `hrt_endgame` |
| Theorem 1, conditional form | `lambda0_independent_of_reduction` |

The formalized endgame is *stronger* than the paper's prose in one respect:
`circle_pair_quadratic` cuts the two-circle intersection out by a single fixed quadratic, so
three sample fibres suffice and no continuity is needed.

### Route II — `HRT` (the full `L²` development)

25 modules, ~19,300 lines, 1,065 declarations, **no `sorry`**, no declared axiom; every
footprint exactly `[propext, Classical.choice, Quot.sound]`. Unlike Route I this library
proves the *analysis*, not just the endgame:

- the Zak reduction, covariance, and modulus cocycle — arbitrary real shift, arbitrary `j`,
  no compact-support or decay hypothesis;
- the Birkhoff coboundary lemma and the mean condition (paper Lemma 10, eq. 20);
- **the argument principle in the form actually required** (`exists_lift_quadratic`): an
  explicit lift of the quadratic loop is constructed and its winding number computed, giving
  `deg ξ_θ = −(j+1) + N(θ)`. Mathlib has no winding number, no argument principle and no
  `π₁(S¹) ≅ ℤ` — none is needed, because only this one family of loops occurs;
- the fixed-radius counting lemma (paper Lemma 12) and Jensen's consequence;
- **the three-point input, discharged** (`hthree_lambdaZero`): every three-point subset of
  `Λ₀` is handled outright, so the final theorem carries no three-point hypothesis;
- `lambdaZero_dependence_forces_norm_eq` — an unconditional consequence of a hypothetical
  dependence, requiring no external input at all.

The conditional part is isolated as `ILRStatement` — a **`def … : Prop`, not an `axiom`** —
discharged by the caller in `heil_speegle_lambda_zero_L2_of_ILR` and
`lambda0Translates_linearIndependent_of_ILR`. Because it is a hypothesis rather than an axiom,
no `sorryAx` and no extra axiom enters any footprint. It is pinned to the loops that actually
arise (`quadLoop`) so it cannot be accidentally stronger than the cited theorem. One
nontrivial fragment of it **is** proved outright: the character case (`ILR_character`), via
Parseval and invariance of `|Ŵ|` along arithmetic progressions.

`lambda0Translates_eq` bridges the two vocabularies, proving that Route I's
`lambda0Translates` and Route II's `configTranslates √2 0` describe the same four functions.

## What is NOT claimed

- **Neither library proves the HRT subconjecture at `Λ₀` unconditionally.** Route I is
  conditional on `ZakReduction`, Route II on `ILRStatement`.
- **Theorem 1 of the paper (the unconditional one) is not formalized.** The winding
  infrastructure it needs exists (`windOf`, `IsLoopLift`, `windOf_add`, `exists_lift_char`),
  but invariance of the degree under precomposition with a rotation, and the continuous fibre
  dichotomy, are not. Formalizing Route I would remove the last quoted input from the formal
  development and is the natural next step.
- **`ZakReduction g` is an implication**, so it holds *vacuously* for any window whose
  translates are already independent. Route I's value is that it machine-checks the endgame
  *reasoning*, not that its hypothesis is hard to satisfy. Route II does not have this
  weakness — it proves the analysis.

## Relation to Guan–Okoudjou (arXiv:2607.26878)

S. Guan and K. A. Okoudjou, *The HRT conjecture for symmetric configurations and real-valued
functions*, proved HRT for the symmetric `(2n+1,2)` configurations
`Λₙ = {(0,k) : −n ≤ k ≤ n} ∪ {(a,b),(a,−b)}` with arbitrary `L²` windows and `ab ≠ 0`. Their
Corollary 1 covers **every** four-point configuration `{(0,0),(0,1),(s,0),(a,b)}` for
**real-valued** windows (conjugation sends `b ↦ −b`, producing the symmetric companion
point); their Corollary 2 extends this to `e^{2πiφ}g` with `g` real-valued and `φ` a real
polynomial of degree ≤ 2. `Λ₀` is an instance (`s=1`, `(a,b)=(√2,√2)`), so **for
quadratic-phase-times-real windows the `Λ₀` case is theirs**, unconditionally and by a far
shorter route than either route here. We claim no priority for it.

What their method cannot reach is a general phase, and they say so: writing
`g = |g|e^{2πiφ}` with `φ` merely measurable, their Remark 2 notes that Corollary 1 settles
`|g|` and Corollary 2 settles quadratic `φ`, so *"the essential remaining problem is to
understand the effect of more general phase functions."* Our theorems impose **no condition
on the phase at all** — a Schwartz window with a cubic phase is covered by Theorem 1 and by
neither of their corollaries. Since Heil–Speegle Conjecture 2 permits an arbitrary smooth
phase, it is **not** settled by their results, and Theorem 1 settles it.

Neither dominates. The paper's §9 also records the synthesis we think most promising: in the
Zak fibration the modulus and the phase separate into two independent cocycles — exactly the
`|g|` / `e^{2πiφ}` split their Remark 2 asks about — and their Demeter–Zaharescu product
estimates, which need no degree, are a candidate replacement for this paper's one quoted
input (ILR), which would make Theorem 2 unconditional.

## What to read

`Challenge.lean` + `HRTLambda0/Statement.lean` + Mathlib are the entire audit surface for
Route I; read `ZakReduction` before anything else. For Route II, read `ILRStatement` in
`HRT/HRTBridge.lean` and check it against the cited theorem. `comparator/all.json` lists the
five project-specific definitions Route I's statement rests on.

## Verification

See `VERIFICATION.md`: the kernel-check logs (recorded verbatim), the paper's sha256 pins,
what is and is not claimed, and the CI/Comparator posture
(`.github/workflows/hrt-lambda0-build.yml`, `hrt-lambda0-comparator.yml`).
