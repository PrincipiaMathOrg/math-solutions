# MathDB formalizations that are NOT fully verified

This directory holds Lean for 188 MathDB problems. **143 of them are fully
verified**; they are the ones listed in [README.md](README.md). The **45 listed
here are not**, and each one's Principia project links to its module, so this file
exists to say what that link does and does not mean before anyone reads the Lean.

## What a row here is

Each is a **spine**: the chain of inferences to the problem's conclusion, written in
Lean, with every step the campaign could prove proved outright and every step it
could not stated as a **named hypothesis** in the theorem's own signature. The
composition is therefore a typing fact -- the pieces provably fit -- while the
hypotheses are provably still owed. Three kinds of row appear:

- **conditional** -- the conclusion is derived from one or more named hypotheses that
  are not proved here (most often because Mathlib has no theory of the object at all).
- **refuted-but-not-counted** -- the write-up's claim is *disproved* outright and
  nothing is carried, but the row still is not counted, because some *other* part of
  the write-up is not formalized. A refutation is a result; it is not a verification
  of the write-up.
- **partial** -- a genuine fragment: the engine is proved, the assembly is not.

## What it is not

- **Not verified.** No row here may be cited as a machine-checked proof of its
  problem. `sorry` does not appear in any of these modules -- the gaps are
  hypotheses, not holes -- and that is exactly why the distinction has to be written
  down: a clean `#print axioms` footprint says nothing about what a binder assumes.
- **Not through the Comparator.** Not one of these has a Challenge/Solution contract.
  See [VERIFICATION.md](VERIFICATION.md).
- **Not CI-checked.** Every verdict below is a LOCAL gate run on the development
  machine. There is no CI run id for any of them.

## The 45

Decl counts are of top-level declarations in the module as committed here. The
verdict text is lifted from the campaign table's own cells, not rewritten.

| # | decls | Result claimed by the write-up | Where this Lean stands |
|---|---|---|---|
| [#322495](Principia/MathDB/Problem322495.lean) | 6 | Vanishing in Nuttall's normalized determinant expansion — *proof* | partial — SPINE: the write-up's entire engine is PROVED, and it turned out to be CAMPAIGN-AGNOSTIC commutative algebra, so it was promoted to `Common/`. |
| [#322992](Principia/MathDB/Problem322992.lean) | 18 | Amdeberhan–Moll–Vignat Conjecture 8.7 (an initial value making every term of the quadratic recurrence `a_n = Σ_k C_μ(n,k) a_k a_{n−k}` `p`-integral) — *proof* | PARTIAL — the floor lemma that is the whole engine is proved in full generality, in both its forms, and it is no longer a bound that nothing consumes: `factorization_bound` turns it into a statement about the `p`-adic valuation of the factorial ratio via. |
| [#323297](Principia/MathDB/Problem323297.lean) | 7 | Nonintegrality of Schmidt-type coefficients — *proof* | partial — SPINE: the write-up's number-theoretic ENGINE is proved outright. |
| [#325507](Principia/MathDB/Problem325507.lean) | 10 | Signed mean-value trace inequality, the joint conjecture — *counterexample / disproof* | partial — THE POLYNOMIAL CLAUSE IS REFUTED FOR SCALARS, UNCONDITIONALLY AND WITH NOTHING CARRIED. |
| [#328441](Principia/MathDB/Problem328441.lean) | 13 | Negative-parameter ACMS reciprocal-tail formulas — *proof* | partial — SPINE: the conjecture is FALSE AS PRINTED and all three exclusions are PROVED necessary, each for a different reason. |
| [#328940](Principia/MathDB/Problem328940.lean) | 16 | Consecutive attraction for augmented happy functions — *proof* | partial — SPINE: the write-up's own parity equation is PROVED, together with the invariance its pair lemma consumes and the *consequently* step. |
| [#330132](Principia/MathDB/Problem330132.lean) | 10 | A strict strip for Ehrhart roots in dimensions six and seven — *proof* | partial — SPINE: both bridges are PROVED and the conjecture is derived from the carried theorem, so the only obligation left is the determinant expansion. |
| [#330197](Principia/MathDB/Problem330197.lean) | 20 | The Beatty logarithm bound by pi^2/6 — *proof* | partial — SPINE: the whole `R`-side is PROVED, including the bound by the conjecture's own constant `pi^2/6`. |
| [#330198](Principia/MathDB/Problem330198.lean) | 11 | Beatty logarithm bound by one — *counterexample / disproof* | partial — SPINE: the certificate arithmetic and the logarithm bound are PROVED. |
| [#331410](Principia/MathDB/Problem331410.lean) | 9 | Prime periods of the chocolate numbers — *proof* | partial — SPINE: the write-up's *consequently* is PROVED rather than restated, and the dichotomy is reused by import. |
| [#331783](Principia/MathDB/Problem331783.lean) | 10 | Chaos criterion for a rational second-order recurrence — *counterexample / disproof* | partial — THE CONJECTURE IS REFUTED UNCONDITIONALLY AND NOTHING IS CARRIED. |
| [#332493](Principia/MathDB/Problem332493.lean) | 17 | A dimension-free proof of the four-projection trace inequality — *proof* | partial — (17 decls) gated, the write-up's entire NON-MATRIX content proved, row deliberately NOT counted. |
| [#332639](Principia/MathDB/Problem332639.lean) | 24 | The trace coefficient formula for web-colouring matrices — *proof* | partial — SPINE gated 2026-10-27, deliberately NOT counted (24 decls, `Principia/MathDB/Problem332639.lean`). |
| [#333489](Principia/MathDB/Problem333489.lean) | 13 | Equal-parameter period rule for a delay recurrence — *counterexample / disproof* | partial — THE CONJECTURE IS REFUTED, UNCONDITIONALLY AND WITH NOTHING CARRIED. |
| [#335304](Principia/MathDB/Problem335304.lean) | 67 | Holt Conjecture 17 (every canonical four-digit continued-fraction permutiple is symmetric: `ad = eh` and `bc = fg`) — *proof* | PARTIAL — the RATIO LEMMA and LEMMA `last` are now both proved in full, and with them every ingredient of the argument except the case analysis A–E. |
| [#338791](Principia/MathDB/Problem338791.lean) | 63 | Nenashev's central matrix-algebra conjecture (central zonotopal algebra determines the configuration up to z-equivalence) is FALSE — *refutation* | partial — THE REFUTING CLAUSE IS UNCONDITIONAL. |
| [#338918](Principia/MathDB/Problem338918.lean) | 37 | Alternating Turan inequalities for normalized Euler numbers — *proof* | partial — SPINE gated, CONDITIONAL, deliberately NOT counted as fully verified. |
| [#347913](Principia/MathDB/Problem347913.lean) | 15 | Convexity of hypergraph polynomials from exponential moments — *proof* | SPINE (15 decls here + 4 promoted to `Common/`) — NOT verified. |
| [#350746](Principia/MathDB/Problem350746.lean) | 12 | A denominator bound for a contiguous basic hypergeometric ratio — *proof* | partial — SPINE: the exponent structure of the clearing denominator is PROVED, including the monotonicity the write-up assumes silently. |
| [#351647](Principia/MathDB/Problem351647.lean) | 14 | Restricted reciprocal-permutation sums and hollow Cauchy matrices — *proof* | partial — SPINE: the LITERAL conjecture is REFUTED by a finite witness and the exceptional class is pinned exactly. |
| [#351688](Principia/MathDB/Problem351688.lean) | 29 | Complete monotonicity of squared derivative ratios of Mills ratio — *counterexample / disproof* | partial — SPINE gated 2026-09-25, deliberately NOT counted (29 decls, `Principia/MathDB/Problem351688.lean`). |
| [#352456](Principia/MathDB/Problem352456.lean) | 141 | Polar-parabola centroid-locus conjecture for arbitrary polygon size — *proof* | SPINE (141 decls) — the headline constant is PROVED for arbitrary `N`, nothing carried. |
| [#352496](Principia/MathDB/Problem352496.lean) | 10 | The Polynexus formula for nonzero interval-translation products — *proof* | partial — SPINE: the closed form is PROVED integer-valued and the total-count lemma is proved. |
| [#352917](Principia/MathDB/Problem352917.lean) | 14 | Coinciding symmetries determine a homogeneous mean — *proof* | partial — SPINE: the algebraic core is PROVED by the write-up's own argument, and the parameter-independence that makes the theorem hold on ALL of the reals is now a theorem rather than an unremarked computation. |
| [#357172](Principia/MathDB/Problem357172.lean) | 12 | Garcia Conjecture 6.5 (the density of the quadratic-residue jumps: `J_n/n → 3/8` for `p = 4n−1` prime) — *proof, unrestricted* | PARTIAL — the analytic core is the one named hypothesis, and everything around it is proved exactly: the residue reduction that makes the second residue linear, the jump restatement in one residue, the `ε ↓ 0` squeeze with no analysis in it, the transfer from. |
| [#357173](Principia/MathDB/Problem357173.lean) | 23 | Garcia Conjecture 6.6 (`A_n/D_n → 1/3` for the paired floor sum over `p = 4n−1`) — *proof with an explicit rate* | PARTIAL — a SPINE. The theorem's three claims are proved from ONE named analytic hypothesis, and everything that is not that hypothesis is discharged: the arithmetic core `⌊n²/(4n−1)⌋ = ⌊n/4⌋`, the exact `D_n` expansion and its two consequences, the root. |
| [#358005](Principia/MathDB/Problem358005.lean) | 19 | The Amdeberhan-Callan Gaussian-product inequality — *proof* | partial — SPINE: Mathlib has NO Gaussian binomials, so this row BUILDS the object, proves it lies in `N[q]`, and settles both easy cases of the Pascal-minor lemma. |
| [#364074](Principia/MathDB/Problem364074.lean) | 84 | `u(0,n) − u(1,n) ≥ N(0,n)/2` for `n ≥ 8` | in flight — THE STATEMENT IS COMPLETE and the REINDEXING IS NOW PROVED. |
| [#366795](Principia/MathDB/Problem366795.lean) | 24 | Rowland–Sistos Barrón Conjecture 5.3, *particular*-rank half (the power-rank sequence `M ↦ rank ((s n ^ M)_n)` of a constant-recursive integer sequence is eventually quasipolynomial) is FALSE — *refutation* | PARTIAL — the REFUTING MECHANISM is fully proved and carries nothing. |
| [#367323](Principia/MathDB/Problem367323.lean) | 48 | All Motzkin convolution boundary formulas for exponents divisible by three — *proof* | partial — (48 decls) gated, the checkable kernel proved, the PRINTED conjecture refuted and the coefficient chain now COMPOSED by a theorem. |
| [#367324](Principia/MathDB/Problem367324.lean) | 63 | Exact Motzkin boundary values for every exponent not divisible by three — *proof* | partial — THE SOURCE CONJECTURE IS REFUTED, UNCONDITIONALLY (63 decls). |
| [#370786](Principia/MathDB/Problem370786.lean) | 7 | Two-prime quadratic remainder sums — *proof* | partial — SPINE: the conjecture is STATED in Lean and two ingredient families are proved. |
| [#370788](Principia/MathDB/Problem370788.lean) | 14 | Chamberland–Dilcher Conjecture 7.4, and the equivalent #370787 / Conjecture 7.3 (a squarefree floor sum and its class-number inversion) — *proof* | PARTIAL — the write-up claims ONE campaign credit for TWO conjectures on the ground that "Möbius inversion makes them equivalent". |
| [#370789](Principia/MathDB/Problem370789.lean) | 7 | Chamberland–Dilcher Conjecture 7.5 (the four residue-class limits of the square-root floor sum) — *proof* | PARTIAL — the four-case theorem is the named hypothesis, and what is proved is the thing a reader of the source most needs: the write-up's TYPO DIAGNOSIS of Equation (7.14) is CORRECT, and it follows from the `r = 2` case alone (7 decls. |
| [#371345](Principia/MathDB/Problem371345.lean) | 40 | Vendi's conjecture that Vendi Score bounds LCR — *proof* | partial — (40 decls) gated, the write-up's ENTIRE new contribution proved, row deliberately NOT counted. |
| [#372858](Principia/MathDB/Problem372858.lean) | 24 | The conjectured extension of the Burnside–Stirling–Gautschi bound — *proof* | partial — (24 decls) gated as a SPINE, conditional on ONE named hypothesis. |
| [#373405](Principia/MathDB/Problem373405.lean) | 19 | The weight-to-Laplacian dictionary for the extremal ML-degree bound — *proof* | partial — SPINE: the coordinate dictionary the write-up asserts in one sentence is PROVED, and THREE of its clauses came out STRICTLY STRONGER than stated. |
| [#373701](Principia/MathDB/Problem373701.lean) | 20 | Hyman Conjecture 3.17 (the persistent integer bases `P_N` have natural density `1/12`) is FALSE — for every fixed sample depth `N ≥ 3` the density does not exist — *refutation* | PARTIAL — the PERSISTENCE CRITERION IS DECIDED ON BOTH CYLINDERS, which is the mathematical core of the refutation, and both verdicts are proved with the two analytic inputs isolated to one line each. |
| [#374957](Principia/MathDB/Problem374957.lean) | 68 | Transpose duality for preorder multichain matrices — *proof* | partial — (68 decls) gated as a SPINE, conditional on ONE named input. |
| [#374965](Principia/MathDB/Problem374965.lean) | 12 | Bivariate Ehrhart reciprocity for preorder polytopes — *proof* | partial — SPINE gated 2026-10-27, deliberately NOT counted (12 decls, `Principia/MathDB/Problem374965.lean`). |
| [#377007](Principia/MathDB/Problem377007.lean) | 11 | Half-integral continued fractions for Chebyshev products — *proof* | partial — SPINE: the whole instantiation bridge from the general theorem to Cohn's conjecture is PROVED. |
| [#378712](Principia/MathDB/Problem378712.lean) | 11 | A common majorant for both orders of multiplication in a Banach algebra — *proof* | partial — SPINE: the write-up's own stated analytic mechanism is PROVED IN FULL, and it turned out to be CAMPAIGN-AGNOSTIC, so it was promoted to `Common/`. |
| [#381792](Principia/MathDB/Problem381792.lean) | 12 | High-frequency characteristic roots and diffusive boundary feedback — *proof* | partial — SPINE: the write-up's logical reduction is PROVED, its Rouche inputs are proved, and ITS THRESHOLD IS MEASURED SLACK IN BOTH PLACES IT IS USED. |
| [#381794](Principia/MathDB/Problem381794.lean) | 29 | Brenti–Sentinelli Conjecture 6.3 (the convex hull of the Wachs permutations in `S_{2m}` is simple for every `m ≥ 1`) — *proof* | PARTIAL — the AFFINE ISOMORPHISM, which is the write-up's entire geometric content, is proved UNCONDITIONALLY and in full generality. |
| [#381795](Principia/MathDB/Problem381795.lean) | 34 | Brenti–Sentinelli Conjecture 6.4 (the convex hull of the SIGNED Wachs permutations in `B_{2m}` is simple for every `m ≥ 1`) — *proof* | PARTIAL — the CONE CERTIFICATE, which is this write-up's real content and the thing that distinguishes it from the unsigned Conjecture 6.3, is proved as a telescoping identity in full generality. |

**1167 declarations across the 45 modules.**

## Reproducing a row

```sh
cd mathdb
lake exe cache get
lake build Principia.MathDB.Problem<num>
```

A successful build establishes that the module elaborates and that its hypotheses
compose. To see what each theorem actually assumes, read its signature: the named
hypotheses are the content of this file.
