# VERIFICATION — HRT at Λ₀, two routes (BOTH CONDITIONAL)

The honest ledger. Every claim below is either a command that was run with its actual
output recorded, or an explicit note that it was **not** run and where it *is* run.

Two results are claimed, from two independent Lean libraries. **Route I** (`HRTLambda0`):

```lean
theorem HRTLambda0.Statement.lambda0_independent_of_reduction {g : ℝ → ℂ}
    (h : HRTLambda0.ZakReduction g) : HRTLambda0.Lambda0Independent g
```

**Route II** (`HRT`):

```lean
theorem HRTBridge.lambda0Translates_linearIndependent_of_ILR (g : ℝ → ℂ)
    (hgm : Measurable g) (hg2 : MemLp g 2 volume) (hgne : ¬ (g =ᵐ[volume] 0))
    (hILR : …) : LinearIndependent ℂ (HRTLambda0Mirror.lambda0Translates g)
```

both with `#print axioms` showing exactly `[propext, Classical.choice, Quot.sound]`.

## §1 Scope — read this first

- **BOTH theorems are CONDITIONAL, on different hypotheses.**
  - Route I's hypothesis `ZakReduction g` (`HRTLambda0/Statement.lean`) packages the
    paper's entire pre-endgame analysis — the Zak reduction, the fibre dichotomy, the
    root count at `j = 0`, and Jensen's formula on the fibre — and **none of that is
    proved in that library**.
  - Route II's hypothesis is the Iwanik–Lemańczyk–Rudolph spectral theorem, isolated as
    `ILRStatement` in `HRT/HRTBridge.lean`. Route II **does** prove the analysis Route I
    assumes; what it quotes instead is one published theorem whose conclusion (Lebesgue
    maximal spectral type) is not currently expressible in Mathlib — there is no maximal
    spectral type, no spectral measure for unitaries, and no Lebesgue spectrum.
- **Therefore the HRT subconjecture at `Λ₀` (Heil 2006 Conjecture 9.2(a) / Heil–Speegle
  Conjecture 2) is NOT claimed unconditionally in Lean by this directory**, by either
  route. The paper's *Theorem 1* is unconditional on paper; it is **not formalized** (see
  §7).
- **`ILRStatement` is a `def … : Prop`, not an `axiom`.** It is discharged by the caller,
  so no `sorryAx` and no additional axiom enters any footprint — the axiom assertions in
  §2/§3 remain meaningful. It is pinned to the loop family that actually arises
  (`quadLoop`) so that it cannot be accidentally *stronger* than the cited theorem; an
  earlier draft was both too weak (missing periodicity, making consumers vacuous) and
  later too strong (quantified over all unimodular loops with a continuous lift), and both
  defects were corrected. One nontrivial fragment, the character case, is proved outright
  (`ILR_character`).
- **Mathematical attribution**, as recorded in the paper's §11: the fibration of `𝕋²`, the
  zero-propagation dichotomy and the winding identity are due to Oussa (arXiv:2508.04613v2);
  the paper's own contributions are the reading of the winding value as a *root count*,
  the Jensen fixed-radius consequence, the two endgames, and the removal of the regularity
  hypothesis via ILR. **For real-valued windows the `Λ₀` case belongs to Guan–Okoudjou**
  (arXiv:2607.26878, Corollary 1) — see paper §9; no priority is claimed there.
- **An honest caveat about Route I's conditional theorem:** `ZakReduction g` is an
  implication (`¬ independent → ∃ …`), so it holds *vacuously* for any window whose
  translates are already independent. Route I's value is that it machine-checks the endgame
  *reasoning* — the step every window class must pass through — not that the hypothesis is
  hard to satisfy. A skeptic should read the definition of `ZakReduction` and decide
  whether it faithfully transcribes the paper's §2; that transcription is Route I's trust
  boundary. **Route II does not have this weakness**: it proves the analysis, and its
  trust boundary is the single statement `ILRStatement`, which a reader can compare
  directly against \[ILR].
- **No `sorry`** outside the single deliberate placeholder in `Challenge.lean` — neither
  in `HRTLambda0` nor anywhere in the 25-module `HRT` library; **no declared axiom**
  anywhere in this directory.

## §2 The build

**Environment.** Lean `leanprover/lean4:v4.31.0`; Mathlib `rev
fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (tag `v4.31.0`), pinned in
`lake-manifest.json` — identical pins to `sendov9-11/`.

**Where the authoritative build runs: CI.** `.github/workflows/hrt-lambda0-build.yml`
builds the `HRTLambda0` library, then `Solution`, then `Challenge`, and asserts: no
`declaration uses 'sorry'` in the development or Solution logs; no axiom outside the
permitted triple in any footprint (this also catches `sorryAx`); the headline result
carries the clean triple; no `native_decide` / `implemented_by` / `unsafe` / `axiom`
declaration; and `Challenge.lean` has exactly one `sorry`. **RUN and PASSED**, 2026-08-07,
commit `8959fd3` (see §3b for the two earlier failed attempts and their cause).

**Locally (Windows), RUN — the monolithic development file.** The development was
written and certified as a single file; before this folder was assembled it was
kernel-checked in the certification environment (same toolchain and Mathlib pins),
2026-08-05, `lake env lean HRTLambda0.lean` → **exit 0**, actual output in full:

```
'HRTLambda0.lambda0_symplectic_escape' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.zero_propagates' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.fibre_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.degree_identity_kills' depends on axioms: [propext, Quot.sound]
'HRTLambda0.two_of_three_eq_of_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.circle_pair_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.hrt_endgame' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.lambda0_independent_of_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(`degree_identity_kills` legitimately needs only `[propext, Quot.sound]` — it is pure
integer arithmetic by `omega`.)

**Locally (Windows), RUN — this folder's split layout.** For this repository the file
was split into `HRTLambda0/Statement.lean` (definitions, byte-identical) +
`HRTLambda0/Endgame.lean` (theorems, byte-identical bodies) + `Challenge.lean` +
`Solution.lean`. Each module was then kernel-checked in dependency order with
`lake env lean` under the same pins (see §3 for the recorded log). This is what
establishes that the split introduced no drift.

## §3 The split check — actual output

Sequential `lake env lean` on `Statement` → `Endgame` → build root → `Challenge` →
`Solution`, 2026-08-05:

```
== Statement ==
STATEMENT_EXIT=0
== Endgame ==
'HRTLambda0.lambda0_symplectic_escape' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.zero_propagates' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.fibre_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.degree_identity_kills' depends on axioms: [propext, Quot.sound]
'HRTLambda0.two_of_three_eq_of_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.circle_pair_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.hrt_endgame' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.lambda0_independent_of_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
ENDGAME_EXIT=0
== Root ==
ROOT_EXIT=0
== Challenge ==
hrtcheck\Challenge.lean:34:8: warning: declaration uses `sorry`
CHALLENGE_EXIT=0
== Solution ==
'HRTLambda0.Statement.lambda0_independent_of_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
SOLUTION_EXIT=0
```

Exits all 0; `Challenge` reports exactly its one deliberate `sorry`; `Solution` reprints
the clean footprint for `HRTLambda0.Statement.lambda0_independent_of_reduction`; the
`Endgame` footprints are **identical** to the monolithic file's (§2), so the split
introduced no drift.

## §3b Route II — the `HRT` library, verification status

**Where it was checked: the development environment, NOT this folder's layout.** The 25
modules under `HRT/` were written and kernel-checked in the private development repository
(`PrincipiaAI`, `LeanSandbox/problems/`) under the *same* toolchain and Mathlib pins as this
folder (`leanprover/lean4:v4.31.0`, Mathlib tag `v4.31.0`), most recently 2026-08-07, with
every `#print axioms` line reporting exactly `[propext, Classical.choice, Quot.sound]` and no
`declaration uses 'sorry'` warning anywhere.

**What has NOT been run:** `lake build HRT` **in this folder**. This directory has no `.lake`
and Mathlib is not built here, so the vendored library has not yet been compiled under this
`lakefile.toml` (`srcDir = "HRT"`, `roots = ["HRTBridge"]`). A layout/module-path defect would
therefore not yet have surfaced. This ledger says so rather than implying otherwise.

**Where it *is* run: CI, and it has now PASSED.** The job `build-hrt-l2-route` in
`.github/workflows/hrt-lambda0-build.yml` builds `HRT` on Linux over the cached Mathlib and
asserts the same three properties as the Route I job — no `declaration uses 'sorry'`, no axiom
outside the permitted triple in any footprint (this also catches `sorryAx`), and no `axiom`
declaration in the sources. It is a **separate job** from `build`, so the two routes are
verified independently and a failure in one cannot be mistaken for the other.

**Result, 2026-08-07, commit `8959fd3`: `hrt-lambda0-build` — success (both jobs), and
`hrt-lambda0-comparator` — success.** This closes the layout gap noted above: the vendored
library does compile under this folder's `lakefile.toml`, so the flat module names resolve
against `srcDir` correctly and no module-path defect was hiding in the vendoring.

Two earlier attempts on this branch (`b53970e`, `b1fd301`) failed **all three jobs** at the
Mathlib-cache step. That was not an infrastructure fault and not a Lean fault: the `HRT`
library had been registered with `globs = ["*"]`, which is not a valid module glob, and a
lakefile *configuration* error aborts `lake exe cache get` before it fetches anything. Fixed
in `8959fd3` by listing the 25 module names explicitly (the pattern
`sendov9-11/lakefile.toml` already uses) with no `roots` key. Recorded here because the
symptom impersonated a cache outage.

Static facts about the vendored sources, checked locally on Windows 2026-08-07: 25 modules,
19,275 lines, 1,065 declarations; `grep -c sorry` returns nonzero for exactly two files
(`BirkhoffErgodic.lean`, `HRTZakL2.lean`) and in **both** cases the match is inside a prose
comment, not a tactic — there is no `sorry` in any proof; `grep -rn "^axiom "` returns nothing.

**The import closure is not prunable.** `HRTBridge` reaches all 25 modules, including the
`Atiyah*` / `GroupVonNeumann` group-von-Neumann-algebra development, via
`HRTRectangular → AtiyahHRT`. Those modules are load-bearing, not stray campaign files.

## §4 Statement fidelity

The risk Lean's kernel cannot address is a sound proof of a subtly *different*
statement. Mitigations:

- The definitions in `HRTLambda0/Statement.lean` are copied **verbatim** from the
  certified development file; the theorem in `Challenge.lean` is stated at literally the
  type `ZakReduction g → Lambda0Independent g`, and `Solution.lean` proves it by a
  **direct term assignment** from the development — no transport lemma, no coercion.
- `comparator/all.json` therefore carries `definition_names` for all five
  project-specific definitions (`tfTranslate`, `configTranslates`, `lambda0Translates`,
  `Lambda0Independent`, `ZakReduction`): Comparator checks the definitions as well as
  the theorem.
- **Negative control: NOT run** for this folder. The statement's load-bearing pieces are
  the five definitions, which Comparator audits directly; a perturbation control in the
  style of `sendov9-11/`'s §5(b) has not been constructed here and this ledger says so
  rather than implying otherwise.

## §5 Comparator

**Linux-only** (landrun / Landlock sandbox); **NOT run on this platform (Windows)**.
`.github/workflows/hrt-lambda0-comparator.yml` runs `comparator/all.json` on push with
permitted axioms exactly `propext / Quot.sound / Classical.choice` and requires
`Your solution is okay!`.

**RUN and PASSED on CI**, 2026-08-07, commit `8959fd3`.

Note exactly what that pass does and does not mean. It certifies that `Solution.lean`
proves the statement in `Challenge.lean` and no other, that the five project-specific
definitions the statement rests on match, and that the axiom footprint stays within the
permitted triple. It **cannot** upgrade a conditional theorem to an unconditional one:
the certified statement is still `ZakReduction g → Lambda0Independent g`, and Comparator
has nothing to say about whether `ZakReduction` is true. It also covers **Route I only** —
Route II is gated by the `build-hrt-l2-route` job (§3b), not by Comparator.

## §6 The paper

The `.pdf` was built from the committed `.tex` with `pdflatex` (two passes, exit 0 both,
no undefined reference or citation warning) on the certification machine, 2026-08-07 —
unlike `sendov9-11/paper/`, the PDF here is a build product, not author-supplied bytes,
and this ledger says so.

**The paper is a merge, 2026-08-07.** It supersedes two earlier manuscripts that proved
the same central identity by different means: the continuous-Zak paper previously
committed at this path, and the `L²` manuscript archived alongside it at
`paper/hrt_lambda0_rigorous.tex`. The merged text carries **both** routes (paper §3,
Proposition 7(i) and (ii)), both endgames (§5), the `j = ±1` saturation analysis, a new §9
on Guan–Okoudjou, and a new §10 recording the formalization boundary. The archived
`L²` source is retained for provenance; the earlier continuous-Zak source is recoverable
from git history. Pins:

```
b5c5f4190821304d68394e192ed0f5a211561011eb4eae28afc1c150caddc028  paper/hrt-lambda0.tex
41fb3772d6493cccabbc21e575145603ac23095782946841498fcf55030ee042  paper/hrt-lambda0.pdf
b833084083d3a02aa732e4d6030bd3b329320a99b998fc3de72e7d24960e2134  paper/hrt_lambda0_rigorous.tex
```

**A second citation was checked rather than inherited, and two errors were found and fixed.**
The Guan–Okoudjou preprint was extracted from arXiv on 2026-08-07. Its authors are **Shuang**
Guan and Kasso A. Okoudjou (an earlier draft of this directory wrote "Xuanxuan"), and its
title is *The HRT conjecture for symmetric configurations and real-valued functions* (not
"…for symmetric (2n+1,2) configurations"). Their coverage of Λ₀ was also understated: their
Corollary **2** extends Corollary 1 from real-valued windows to `exp(2πiφ)·g` with `g` real
and `deg φ ≤ 2`, so the class of Λ₀ windows they settle is larger than "real-valued". All
three corrections are reflected in the paper's §9, the README, and `formalization.yaml`.

**One citation was checked rather than inherited.** Both source manuscripts asserted that
`Λ₀` is Heil–Speegle *Conjecture 2*. That attribution was verified against the published
chapter on 2026-08-07 by extracting the text of
`https://heil.math.gatech.edu/papers/hrtzero.pdf`: Conjecture 2 (HRT Subconjecture) reads
*"If g ∈ S(ℝ)\{0}, then {g(x), g(x−1), e^{2πix}g(x), e^{2πi√2x}g(x−√2)} is linearly
independent"*, and their equation (5) names `Λ₀` explicitly. The citation is correct, and
— load-bearing for the paper's §9 — their hypothesis is `g ∈ S(ℝ)`, which permits
**complex** Schwartz windows.

## §7 Deliberately excluded

- **Formerly excluded, now included (2026-08-07).** Two earlier entries here said that the
  wider Lean campaign attacking the reduction, and the stronger `L²` manuscript, were *not*
  part of this folder. Both statements are now **false and have been retracted**: the
  campaign is vendored as the `HRT` library (§3b) and the `L²` manuscript is merged into
  `paper/hrt-lambda0.tex` (§6). The calibration of this folder's claims changed accordingly
  — see §1, which now describes two conditional routes rather than one.
- **The paper's Theorem 1 (unconditional, continuous windows) is not formalized.** The
  winding-number infrastructure it needs is present in `HRT` (`windOf`, `IsLoopLift`,
  `windOf_add`, `exists_lift_char`, `exists_lift_quadratic`), but two ingredients are not:
  invariance of the degree of a circle map under precomposition with a rotation, and the
  continuous fibre dichotomy. Until those land, no library here certifies an unconditional
  statement.
- **Comparator covers Route I only.** `comparator/all.json` names
  `HRTLambda0.Statement.lambda0_independent_of_reduction` and Route I's five definitions.
  Route II is gated by CI (§3b) but not by Comparator.
- The website publication step of the project's solution SOP has **not** been performed.

## §8 Reproduction

```sh
cd hrt-lambda0
lake exe cache get
lake build             # the HRTLambda0 library (Statement + Endgame)
lake build Solution    # prints the #print axioms line for the headline theorem
lake build Challenge   # one intentional sorry

# Comparator (Linux only; see .github/workflows/hrt-lambda0-comparator.yml for pins):
lake env <comparator> comparator/all.json
```
