# VERIFICATION — erdos1054/ep1054

The honest ledger. Every claim below is either a command that was actually run, with its real
output, or an explicit note that it was **not** run.

Environment for everything marked *run here*: the development machine (Windows 10 Pro 19045,
Git Bash / PowerShell), Lean `leanprover/lean4:v4.31.0` via elan, Lake 5.0.0, 2026-10-02.

Source of the vendored development: the PrincipiaAI repository, Lean library at
`Principia Application/LeanSandbox`, **commit `c1c3bb5d0404e769c46d9a276c102f15d4353c8d`**
(`SOURCE.txt`).

---

## 1. Vendored files are the source commit's bytes — RUN, passes

Every file under `Principia/` was extracted with `git show c1c3bb5d…:<path>` (committed bytes, not
a working tree; the source working tree carried other sessions' uncommitted edits).

```
$ sha256sum -c --strict --quiet SHA256SUMS; echo "exit=$?"
exit=0
$ wc -l < SHA256SUMS; find Principia -name '*.lean' | wc -l
359
359
$ find Principia -name '*.lean' -print0 | xargs -0 cat | wc -l -c
 237980 12529436
```

An independent script (run from the PrincipiaAI repository root) recomputed the closure and
compared bytes against `git show`:

```
statements modules at HEAD: 9 all in roots: True
roots: 17
closure modules: 359 missing: []
vendored files: 359
in closure not vendored: []
vendored not in closure: []
byte mismatches vs git show: []
SHA256SUMS entries: 359 mismatches: [] set equal: True
statement closure: ['Principia.Erdos1054.Defs', 'Principia.Erdos1054.Statements.Inputs',
  'Principia.Erdos1054.Statements.S1_Main', ..., 'Principia.Erdos1054.Statements.S7_Limits']
ledger verified records: 33
Solution theorems: 33 name==stmt: True
Solution proof terms not named in ledger verified records: []
```

So: the vendored set is **exactly** the transitive `import Principia.*` closure of the 17 roots
listed in `SOURCE.txt` (the nine statement modules; `Proofs.Assembly`, `Alt.Round4`,
`Alt.Unconditional`, `Alt5.Round5`, `Alt6.Round6`, `Alt7.Round7`, which hold the 33 proofs;
`Spine`; `Alt7.FromAtomsZD`); the statement layer's own closure is `Defs` + the nine statement
modules + Mathlib; and every proof term used in `Solution.lean` is the declaration the PrincipiaAI
theorem ledger (`Campaigns/Erdos-1054/THEOREM-LEDGER.jsonl` at the same commit) records as that
result's verification.

## 2. Paper bytes — RUN, passes

`paper/EP1054.bib` is `git show c1c3bb5d…:Campaigns/Erdos-1054/collab-paper/EP1054.bib`, unedited
(`cmp`: identical). `paper/EP1054.tex` is the same file (sha256 `cdd5ddfbd201f2e76deeabf0636ca9fc69689cca826bbaedcffd7d3befa44112`) with its 36
whole-line `%` comments removed (internal notes between authors; no trailing comments existed),
by a script that treats `\%` as an escape; nothing else changed. `paper/EP1054.pdf` was
built from these in a scratch copy with `latexmk -pdf -interaction=nonstopmode EP1054.tex`
(MiKTeX): exit 0, `Output written on EP1054.pdf (41 pages, 625068 bytes)`, no undefined
references or citations in the log, bibtex 0 warnings.

```
$ cd paper && sha256sum -c SHA256SUMS
EP1054.tex: OK
EP1054.bib: OK
EP1054.pdf: OK
```

| file | sha256 |
| --- | --- |
| `EP1054.tex` | `f37c5ecfc208b7793c351c65ef9ff0eb6627a1a65f3cea4ada85a11bc1e79ee7` |
| `EP1054.bib` | `9f13c45520a5a14f40ed0b67056dd4f838e3863d8a3103a20c2316db2db3634b` |
| `EP1054.pdf` | `cbb2d47335ffa93d94ca67da807bdeb1efdf077dc3599356798362b6fb3bbece` |

A PDF is not byte-reproducible across TeX installations (it embeds timestamps); the `.tex` and
`.bib` are the reference, the PDF a convenience copy of those exact sources.

## 3. Build of the vendored modules in the source tree — RUN, passes

In the PrincipiaAI LeanSandbox (the library these files come from), with none of the 359 closure
files differing from commit `c1c3bb5d` at the time (`git diff --name-only HEAD` listed only files
outside the closure):

```
$ lake build Principia.Erdos1054.Statements.Inputs … Principia.Erdos1054.Statements.S7_Limits \
    Principia.Erdos1054.Proofs.Assembly Principia.Erdos1054.Alt.Round4 \
    Principia.Erdos1054.Alt.Unconditional Principia.Erdos1054.Alt5.Round5 \
    Principia.Erdos1054.Alt6.Round6 Principia.Erdos1054.Alt7.Round7 \
    Principia.Erdos1054.Spine Principia.Erdos1054.Alt7.FromAtomsZD
...
Build completed successfully (4155 jobs).
SLOTBUILD_EXIT=0 SECONDS=100
```

(All 17 roots; the modules were replayed from that tree's existing build, which Lake accepts only
when each source's hash matches its trace. Finished 15:13 local time; a file in the closure,
`Principia/Common/TernaryGoldbach/AgamonDecay.lean`, was edited in that working tree afterwards, at
15:21, by another session, which is why §5 repeats these checks in an isolated copy.)

## 4. `Challenge.lean`, `Solution.lean` — RUN, pass

Each file compiled with `lake env lean <file>` against the build of §3:

**4a. `Challenge.lean`** — exit 0, 0 errors, and exactly **33** warnings, all of the form

```
Challenge.lean:49:8: warning: declaration uses `sorry`
```

one per theorem, as intended. (Counted with `grep -c "declaration uses" …` = 33. The wrapper
script's own `SORRY_WARNINGS` counter printed `0` here: its pattern looks for `'sorry'` in
quotes, while Lean v4.31 prints `` `sorry` `` in backticks. A sorry check keyed on the quoted form
is therefore **vacuous** on this toolchain. The same defect was in the first draft of this
folder's CI workflow; `erdos1054-ep1054-build.yml` now matches both forms,
``"declaration uses ['\`]sorry['\`]"``.)

**4b. `Solution.lean`** — exit 0, 0 errors, no warnings, and 33 footprint lines, one per result,
every one exactly the three permitted axioms:

```
'EP1054.Lem_FmModulus' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Lem_FixedModulusNormality' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Lem_SigmaRangeZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Lem_SigmaRate' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Lem_Moment' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Lem_AnalyticOddRepresentability' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Prop_FraitureFinite' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Lem_KovacMoment' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Thm_SmallUpper' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Prop_SmallRatioThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Lem_SvA0' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Lem_SmoothPartInput' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Lem_SvRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Lem_SvClasses' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Prop_SvSecondMoment' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Thm_SmallValues' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Lem_KernelTails' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Prop_FmEnvelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Cor_FmEnvelopeTail' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Thm_AlmostLogTail' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Thm_SubexpGrowth' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Prop_ClassFirstMoment' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Cor_FmPrimeCeiling' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Cor_FixedCofactorDefect' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Prop_EtaALower' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Prop_ThetaTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Cor_EtaTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Prop_TightnessEquivalence' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Prop_DaddWitnessMeans' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Thm_DaddUniversalSingularity' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Cor_DaddHeavyTails' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Prop_DaddCollisionCriterion' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Prop_DaddCollisionLowerBound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Because each proof in `Solution.lean` is a bare term `theorem X : Principia.Erdos1054.X := <proof>`,
this also checks that each development theorem's type is the trusted statement constant itself.

## 5. Build of THIS Lake project from the vendored files — RUN, passes (in two stages)

To check the folder as shipped, independently of the PrincipiaAI tree, a scratch copy of
`erdos1054/ep1054/` (its `.lean` files, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`)
was built with `lake build`. The vendored `Principia/**` was compiled **from source**; only
the dependency packages were reused, through a directory junction `.lake/packages` → the
PrincipiaAI LeanSandbox's `.lake/packages`, which is at the same manifest revisions (so
`lake exe cache get` was **not run**; Mathlib's oleans came from that checkout and were replayed,
not rebuilt).

**5a. All 359 vendored modules — RUN, every module built with no error, but not in ONE
`lake build` invocation.**

- *Stage 1, `lake build` (default target).* Started 16:07; by 18:05, **298 of the 359 vendored
  modules had built with no error** (`✔`/`⚠` lines only; the warnings are linter style
  warnings). Lake then ran eight `lean` processes in parallel at ~4.4 GB committed each on a
  16 GB machine shared with other Lean jobs; they thrashed (≈10 CPU-seconds each in 20+ minutes)
  and the build was stopped by killing its own process tree at ~18:42. The five
  `✖ … error: Lean exited with code 1` lines at the end of that log are the killed processes;
  none printed a diagnostic.
- *Stage 2, one module at a time.* The remaining **61** modules were then built in topological
  order with one `lake build <Module>` per module (so at most one `lean` compiling at once), in
  the same scratch project: `[1/61] … [61/61] Principia.Erdos1054.Alt7.FromAtomsZD`, **every one
  `exit=0`**, 4528 s in total, no `error` line in the log.

After both stages the scratch project holds **359 `.olean` files under
`.lake/build/lib/lean/Principia`**, one per vendored module, and `sha256sum -c --strict SHA256SUMS`
still passes there. No `declaration uses sorry` warning occurs in either stage's log. What has
not been observed is one uninterrupted `lake build` from an empty `.lake/build` to "Build
completed successfully"; the build-time consequence (memory) is the reason, and is the open
question for the 4-vCPU / 16 GB CI runner too (§7).

**5b. `Solution.lean` against the stage-1 oleans of 5a — RUN, passes.** `lake env lean Solution.lean` in
the scratch project: exit 0, no errors, no warnings, and the same 33 lines as §4b, every one
`depends on axioms: [propext, Classical.choice, Quot.sound]` (counted: 33).

**5c. `Challenge.lean` against the stage-1 oleans of 5a — RUN, passes.** Exit 0; exactly 33
``declaration uses `sorry` `` warnings and no other output.

**5d. Statement-fidelity negative control — RUN, behaves as required.** A scratch file (not
shipped) assigning a proof of one statement to another:

```lean
theorem right : Principia.Erdos1054.Lem_FmModulus :=
  Principia.Erdos1054.Proofs.ep1054_Lem_FmModulus
theorem wrong : Principia.Erdos1054.Lem_FmModulus :=
  Principia.Erdos1054.Proofs.ep1054_Lem_Moment
```

```
NegCtl.lean:10:2: error: Type mismatch
  Principia.Erdos1054.Proofs.ep1054_Lem_Moment
has type
  Principia.Erdos1054.Lem_Moment
but is expected to have type
  Principia.Erdos1054.Lem_FmModulus
```

Only `wrong` is rejected, so the term-assignment check of `Solution.lean` does distinguish the
statements.

**5e. `Conditional.lean` against the oleans of 5a (both stages) — RUN, passes.**
`lake env lean Conditional.lean` in the scratch project: exit 0, no errors, no warnings, and
nine footprint lines, each exactly the three permitted axioms:

```
'EP1054.Conditional.Lem_FraitureBalancedGoldbach_of_helfgott' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Conditional.Prop_FraitureTail_of_helfgott' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Conditional.Thm_FraitureRepresentability_of_helfgott' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Conditional.Eq_ExactRepresentability_of_helfgott' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Conditional.derivedClaims_of_atoms' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Conditional.Lem_FraitureBalancedGoldbach_of_atoms' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Conditional.Prop_FraitureTail_of_atoms' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Conditional.Thm_FraitureRepresentability_of_atoms' depends on axioms: [propext, Classical.choice, Quot.sound]
'EP1054.Conditional.Eq_ExactRepresentability_of_atoms' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A clean footprint here means only that no axiom was *added*: every hypothesis of these theorems
is an explicit binder, and `#print axioms` does not list binders. These are **conditional**
results; see §8. (An earlier attempt at 15:23 to compile `Conditional.lean` against the
PrincipiaAI tree's build failed with `object file … AgamonDecay.olean … does not exist`, because
another session was rebuilding that module from an edited source; that is why this check was
moved into the isolated scratch project.)

## 6. Text audits of the vendored tree — RUN, clean

```
$ grep -rnwE 'sorry|admit' Principia      # only prose inside docstrings/comments, e.g.
Principia/Common/TernaryGoldbach/Spine.lean:130:... `sorry` appears nowhere, deliberately ...
$ grep -rnP '(?<!`)\bnative_decide\b|\bimplemented_by\b|^\s*unsafe\b|set_option\s+debug\.skipKernelTC' Principia
(no output)
$ grep -rhE '^\s*(@\[[^]]*\]\s*)?(private |protected |noncomputable )*axiom\s' Principia
(no output)
```

A text search is not the authority on `sorry` (a failed tactic can inject `sorryAx` without the
word appearing); the authority is the `#print axioms` output of §4–§5, which would print
`sorryAx`.

## 7. Comparator — NOT RUN locally; shipped as a CI workflow

Comparator needs Linux (the landrun / Landlock sandbox) and was **not run** on this Windows
machine. It is configured in `comparator/` (33 per-result configs + `all.json`; `permitted_axioms`
exactly `propext`, `Quot.sound`, `Classical.choice`; no `definition_names`, so every statement
constant is compared in full rather than as a definition hole) and runs in
`.github/workflows/erdos1054-ep1054-comparator.yml`, success string `Your solution is okay!`.
**As of this commit it has never run**, and whether a cold build of the 359-module closure fits
in GitHub's 360-minute job limit is unknown. Likewise `erdos1054-ep1054-build.yml` has not yet
run on CI.

## 8. What the 4 conditional results depend on

Not proved unconditionally: `lem:fraiture-balanced-goldbach`, `prop:fraiture-tail`,
`thm:fraiture-representability`, `eq:exact-representability`. `Conditional.lean` proves them
(a) from the single hypothesis `Principia.Erdos1054.Cite_Helfgott_weighted`, and (b) from 35 named
hypotheses with no Helfgott hypothesis: 7 cited machine computations, 17 cited published
theorems, and 11 steps of Helfgott's argument that are **not yet proved in Lean**. While those 11
remain hypotheses, the representability theorem `R = ℕ \ {2, 5}` is not formally verified here,
and nothing in this folder should be cited as an unconditional Lean proof of it.
