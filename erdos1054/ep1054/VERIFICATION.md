# VERIFICATION — erdos1054/ep1054

The honest ledger. Every claim below is either a command that was actually run, with its real
output, or an explicit note that it was **not** run.

**This is a CONDITIONAL verification, not a complete one.** Of the manuscript's 37 numbered
results, **33 are verified unconditionally** (§5); the other **4 are verified conditionally on 41
cited inputs** — 18 published machine computations and 23 published theorems — which are linked to
their sources **by owner decision and not re-proved in Lean** (§8).

Environment for everything marked *run here*: the development machine (Windows 10 Pro 19045,
16 GB RAM, Git Bash / PowerShell), Lean `leanprover/lean4:v4.31.0` via elan, Lake 5.0.0,
2026-10-03.

Source of the vendored development: the PrincipiaAI repository, Lean library at
`Principia Application/LeanSandbox`, **commit `6a12668add5e38043019b93837a1832d62cc573e`**
(`SOURCE.txt`). This refresh replaces the previous vendoring (commit `c1c3bb5d`, headline
`FromAtomsZD` with 35 hypotheses, 11 of them owed steps of Helfgott's argument).

---

## 1. Vendored files are the source commit's bytes — RUN here, passes

Every file under `Principia/` was extracted with `git show 6a12668a…:<path>` (committed bytes, not
a working tree; the source working tree carried other sessions' uncommitted edits).

```
$ sha256sum -c --strict --quiet SHA256SUMS; echo "exit=$?"
exit=0
$ wc -l < SHA256SUMS; find Principia -name '*.lean' | wc -l
461
461
$ find Principia -name '*.lean' -print0 | xargs -0 cat | wc -l -c
 274747 14330726
```

An independent script (reads the source repository with `git show` only) recomputed the closure
and compared bytes:

```
statement modules at commit: 9
roots (incl. audit-file imports): 18
closure modules: 461
vendored files: 461
in closure not vendored: []
vendored not in closure: []
byte mismatches vs git show: []
SHA256SUMS entries: 461 mismatches: [] set equal: True
```

So the vendored set is **exactly** the transitive `import Principia.*` closure of the 18 roots in
`SOURCE.txt` (the nine statement modules; `Proofs.Assembly`, `Alt.Round4`, `Alt.Unconditional`,
`Alt5.Round5`, `Alt6.Round6`, `Alt7.Round7`, which hold the 33 proofs; `Spine`;
`Alt7.FromAtoms896I` and its gate `Alt7.GateFromAtoms896I`), and every `import Principia.*` of
`Challenge.lean`, `Solution.lean` and `Conditional.lean` lies inside it. Against the previous
vendoring: 102 modules added, 0 removed, 2 changed
(`Principia/Common/TernaryGoldbach/AgamonDecay.lean`, `AgamonLimit.lean`).

The statement layer (`Principia/Erdos1054/Defs.lean`, `Principia/Erdos1054/Statements/*.lean`)
and `Principia/Erdos1054/Spine.lean` are byte-identical between `c1c3bb5d` and `6a12668a`
(`git diff --stat c1c3bb5d 6a12668a -- <those paths>` is empty), so `Challenge.lean` and
`Solution.lean` are unchanged by this refresh.

## 2. Paper bytes — RUN here, passes

Unchanged since the folder's first commit (`57570ce`):

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

`paper/EP1054.bib` is the source repository's `Campaigns/Erdos-1054/collab-paper/EP1054.bib`
unedited; `paper/EP1054.tex` is that `.tex` (sha256
`cdd5ddfbd201f2e76deeabf0636ca9fc69689cca826bbaedcffd7d3befa44112`) with its 36 whole-line `%`
comments removed; `paper/EP1054.pdf` was built from them with `latexmk -pdf` (MiKTeX, 41 pages).
A PDF is not byte-reproducible across TeX installations; the `.tex` and `.bib` are the reference.

## 3. Build of THIS Lake project from the vendored files — RUN here, passes

In an isolated scratch copy of this folder (its `.lean` files, `lakefile.toml`,
`lake-manifest.json`, `lean-toolchain`, `SHA256SUMS`), with the dependency packages reached through
a directory junction `.lake/packages` → the PrincipiaAI LeanSandbox's `.lake/packages` (same
manifest revisions; Mathlib's oleans replayed, `lake exe cache get` not run):

```
$ LEAN_NUM_THREADS=2 lake build
...
✔ [4276/4278] Built Principia.Erdos1054.Alt7.FromAtoms896I (12s)
Build completed successfully (4278 jobs).
LAKE_EXIT=0 SECONDS=1991
```

(Lake 5.0.0 has no `-j` flag; `LEAN_NUM_THREADS=2` held it to two concurrent `lean` processes,
observed with `Get-Process`.) The log has no `✖` line, no `error:` line and no
`declaration uses sorry` line; its 72 `⚠` lines are linter style warnings. Afterwards
`.lake/build/lib/lean/Principia` holds **461 `.olean` files**, one per vendored module, and
`sha256sum -c --strict SHA256SUMS` passes in that copy.

**What was compiled in this run, and what was replayed.** The copy started from the `.lake/build`
of the previous refresh's isolated build (which compiled all 359 modules of `c1c3bb5d` from source,
in two stages, on 2026-10-02). In this run Lake **compiled 108 modules from source** — the 102 new
ones, the 2 changed ones, and the 4 old modules downstream of them (`Alt7.FromAtomsZB`, `ZC`, `ZCS`,
`ZD`) — and **replayed the other 353** from their existing oleans, which Lake does only when each
source's hash and every dependency's trace match. Every one of the 461 modules has therefore been
compiled from these exact bytes in an isolated copy, but not in one uninterrupted build from an
empty `.lake/build`.

## 4. `Challenge.lean`, `Solution.lean`, `Conditional.lean`, the gate — RUN here, pass

Each compiled with `lake env lean <file>` against the build of §3.

**4a. `Solution.lean`** — exit 0, no errors, no warnings, and 33 footprint lines, every one exactly
the three permitted axioms (identical, line for line, to the previous refresh):

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

**4b. `Challenge.lean`** — exit 0, 0 errors, and exactly **33** warnings, all
``declaration uses `sorry` ``, one per theorem, as intended.

**4c. `Conditional.lean`** — exit 0, no errors, no warnings, and ten footprint lines, each exactly
the three permitted axioms:

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
'Principia.Erdos1054.Alt7.FromAtoms896I.ep1054_atoms896I' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**4d. The vendored gate `Principia/Erdos1054/Alt7/GateFromAtoms896I.lean`** — exit 0; it prints
the same footprint for `ep1054_atoms896I` and its type, which has exactly **41** hypotheses, in this
order, before `Principia.Erdos1054.Spine.DerivedClaims` (namespace prefix
`Principia.Common.TernaryGoldbach.` dropped):

```
PC.PlattThm71 → PC.PlattTrudgian → HC.EspagnCheckCited → HC.EspagnSmallCited → HC.CharpyCited →
HX.CharpasCited → HC.AusteriaGridCited → HC.MalMainCited → HC.AmanitaBisectCited → HC.AppBCited →
HC.CameloGridCited → HC.WollustCited → HC.KastCited → HC.NotungCited → HC.CortoSmallCited →
HC.YuttoSmallCited → HC.CortoC0Cited → HC.RamareCited → HM.ZeroCount → HX.RS75Theta →
CY.CERange → CY.Malito → CY.Cante → GS.RS62Thm15 → EB.RS62Thm12 → EB.RS62Thm13 → LQ.RS62_316 →
LQ.RS62_324 → LQ.RS62_330 → LQ.RS62_332 → EF.RosserL17 → EF.RamareSaouterL2 → MPc.Grara →
MPc.Ronsard → MPc.Meproz → KLR.RS75Cor2 → T2K.LargeSieve → T2M.MontgomeryIneq →
M2Y.RamareMarraki → T2G.MVWeighted → T2V.MV8Large → Principia.Erdos1054.Spine.DerivedClaims
```

A clean footprint on a conditional theorem means only that no axiom was *added*: every hypothesis
is an explicit binder, and `#print axioms` does not list binders. See §8 for what they are.

**4e. Statement-fidelity negative control — NOT re-run in this refresh.** It was run on the
previous vendoring (a scratch file assigning `ep1054_Lem_Moment` to `Lem_FmModulus` was rejected
with `Type mismatch`); `Solution.lean` and the statement layer are byte-identical since then.

## 5. The 33 unconditional results

`Solution.lean` (§4a) proves the 33 statements of `Challenge.lean` with footprint
`[propext, Classical.choice, Quot.sound]` and no hypotheses. The list, paper label → Lean name, is
the `alignment` block of `formalization.yaml`.

## 6. Text audits of the vendored tree — RUN here, clean

```
$ grep -rnwE 'sorry|admit' Principia      # 7 hits, all prose inside docstrings/comments, e.g.
Principia/Common/TernaryGoldbach/Spine.lean:130:... `sorry` appears nowhere, deliberately ...
$ grep -rnP '(?<!`)\bnative_decide\b|\bimplemented_by\b|^\s*unsafe\b|set_option\s+debug\.skipKernelTC' Principia
(no output)
$ grep -rhE '^\s*(@\[[^]]*\]\s*)?(private |protected |noncomputable )*axiom\s' Principia
(no output)
```

A text search is not the authority on `sorry`; the authority is the `#print axioms` output of §4,
which would print `sorryAx`.

## 7. Comparator — RUN on CI, PASSES (2026-10-04)

Comparator needs Linux (the landrun / Landlock sandbox), so it runs in CI, not on this Windows
machine. It is configured in `comparator/` (33 per-result configs + `all.json`; `permitted_axioms`
exactly `propext`, `Quot.sound`, `Classical.choice`; no `definition_names`) and runs in
`.github/workflows/erdos1054-ep1054-comparator.yml`.

**Result: `erdos1054-ep1054-comparator`, run 37185465168 (commit `cced91c`), on all 33 verified
results: `Your solution is okay!` — `Finished with result: success`.** The companion
`erdos1054-ep1054-build` run 37185465114 also passed (vendored build 4278 jobs; Solution and
Conditional built; no `sorry` outside `Challenge`; no axiom outside the three; each of the 33
Solution results has a clean footprint; no `native_decide` / `implemented_by` / `unsafe` /
`skipKernelTC` / `axiom` declarations; `Challenge` builds with exactly its 33 sorries). Logs:
artifacts `erdos1054-ep1054-comparator-log` and `erdos1054-ep1054-build-logs` of those runs.

How the earlier failures were fixed. Every earlier run died on memory before reaching a check
(runs 37110713167/37110713171, 37174571376/37174571408, 37177504797, 37178537454, 37184184807).
Per-module logging (`seqbuild.py`) pinned the kill on `Principia.Common.PrimeSumExact.CertsA`
(47 `decide +kernel` segment certificates of ~1.3 GB each), which the runner checked in parallel.
The fix is resource-only: `seqbuild.py` builds one module at a time, `lakefile.toml` passes
`moreLeanArgs = ["--threads=1"]` to the `Principia` library (no elaboration option changes), and
the runner gets 20 GB of swap. The sequential build takes about 4.5 hours; the workflows now also
cache the vendored build products between runs.

**Scope, unchanged:** Comparator certifies the 33 UNCONDITIONAL results (each `Solution` theorem
proves exactly its `Challenge` statement with only the three permitted axioms). It says nothing
about the 4 conditional results, which rest on the 41 cited inputs listed in §8 and in
`Conditional.lean`.

## 8. What the 4 conditional results depend on

Not proved unconditionally: `lem:fraiture-balanced-goldbach`, `prop:fraiture-tail`,
`thm:fraiture-representability`, `eq:exact-representability`. `Conditional.lean` proves them

- (a) from the single hypothesis `Principia.Erdos1054.Cite_Helfgott_weighted`, and
- (b) **without any Helfgott hypothesis**, through `ep1054_atoms896I`, from **41 cited inputs**:

**18 cited machine computations** — Platt, Thm 7.1 (GRH for conductor ≤ 400000 to his height);
Platt–Trudgian (RH to `3·10¹²`); and 16 of Helfgott's runs: `EspagnCheck`, `EspagnSmall`,
`Charpy`, `Charpas`, `AusteriaGrid`, `MalMain` (VNODE-LP integrals), `AmanitaBisect`, `AppB`,
`CameloGrid`, `Wollust`, `Kast`, `Notung`, `CortoSmall`, `YuttoSmall`, `CortoC0`, `Ramare`.

**23 cited published theorems** — Rosser–Schoenfeld 1962 Theorems 12, 13, 15, (2.11), (3.16),
(3.24), (3.30), (3.32); Rosser–Schoenfeld 1975 (5.1) and Corollary 2; Ramaré 1995 Lemma 3.4 (×2);
the explicit zero count as Helfgott cites it (Rosser 1941, McCurley 1984, Trudgian 2015); Rosser
1941 Lemma 17; Ramaré–Saouter 2003 Lemma 2; Granville–Ramaré 1996 Lemma 10.2; Ramaré 2015 (×2);
Ramaré 2013 Corollary 1.4; the sharp large sieve (Montgomery–Vaughan 1974); Montgomery's
inequality (1968); Montgomery–Vaughan 1973 Theorem 1 (1.6) and Lemma 8.

Each input is a hypothesis whose definition's docstring names its source; `Conditional.lean`
lists all 41 with a one-line source each. **By owner decision these inputs are linked to their
publications and not re-proved in Lean**, so the four results are formally verified only
*conditionally on them*. **No step of Helfgott's argument is owed**: every analytic step between
the inputs is kernel-checked (the previous vendoring still carried 11 owed steps as hypotheses).
Nothing in this folder should be cited as an unconditional Lean proof of `R = ℕ \ {2, 5}`.

**Caveats that travel with this result.**

1. **`T2V.MV8Large`** (Montgomery–Vaughan 1973, Lemma 8, for `R ≥ 100`). The vendored docstring
   (written before the check) says the lemma was not checked against the paper. It has since been
   checked by the PrincipiaAI coordinator against *The large sieve*, Mathematika 20 (1973),
   119–134 (U. Michigan Deep Blue PDF), p. 127: "Suppose that `z ≥ 100`. Then
   `Σ_{q≤z} (1 + qz⁻¹)⁻¹ μ(q)²/φ(q) > log z + 0.361`." The hypothesis uses Helfgott's `0.25068 <
   0.361`, so it is **weaker** than the published lemma. (The OCR text layer of that PDF, read for
   this refresh, shows "LEMMA 8. Suppose that z ^ 100." and the constant "0-361"; the formula
   itself is not legible in the text layer.)
2. **`T2G.MVWeighted`** (Montgomery–Vaughan 1973, Theorem 1, (1.6)). Checked by the coordinator
   against the same paper, pp. 119–120: with `δ_r = min_{s≠r} ‖x_r − x_s‖`,
   `Σ_r (N + (3/2)δ_r⁻¹)⁻¹ |S(x_r)|² ≤ Σ_{M+1}^{M+N} |a_n|²`. The hypothesis allows any `δ_r`
   below that minimum, which only shrinks the weights, so it is **weaker**. (Earlier it had been
   checked only against Montgomery's restatement, Bull. AMS 84 (1978), p. 557, eq. (16).)
3. **Several links are CORRECTED forms of Helfgott's statements**, not his verbatim ones: the
   Main Theorem constant `0.896` minor-arc route; corrected `lem:bogus` and `lem:yutto`; `10.25` in
   place of `lem:monro`'s `1.27` (which rests on an uncited computer check). Each corrected link is
   **implied by, or weaker than, what the source proves**, and each is a proved theorem here, not
   a hypothesis.
4. `SecIICalcC` applies `eq:garn1b` and `eq:procida3` without `prop:kraken`'s blanket hypothesis
   `Q ≥ 3.5W`; checked against the source, those bounds come from `lem:kastor2` (needs only
   `q ≤ Q`) and `lem:ogor` (no `Q` hypothesis); only `eq:garn1a` needs `Q ≥ 3.5W`.
5. The PrincipiaAI theorem ledger had not been updated for the newest links at the source commit.

**Errata in Helfgott's printed argument found along the way** (source-level; each corrected link
above is what the chain uses):

- `lem:crepe` is FALSE as printed (`eq:envy` omits a factor 4); the chain uses the corrected
  `CrepeC` (`0.8√x`).
- `eq:tvorog` (in `lem:bogus`) misses a factor 2 relative to its own proof (`eq:iulia`).
- `eq:etoile` (proof of `lem:bogus`) is false as printed (`q = 3`, `V = 9`); valid with a factor
  `3/2`.
- `lem:bogus` uses `c1b = 1 + η₁D/(2x)` where its odd-`n` sum needs `c1 = 1 + η₁D/x`.
- `eq:bocio` (proof of `lem:bostb1`) has a wrong step but a true conclusion (repaired in Lean).
- `lem:yutto`, `v = 2`, `[10⁶, 10¹⁰)`: the printed proof drops a factor `(x/2)^{2ε}`; and its last
  step for `x ≥ 10¹⁰` is false at `x = 10¹⁰`.
- `lem:ogor` applies Montgomery's inequality where `R ≤ W′` is not forced (needs a case split,
  done in Lean).
- `eq:pokor2` counts `W/2` integers in `(W′, W]` where there can be `(W + 1)/2`; repaired by
  choosing `R = (7X/23)^{1/2}`.
- `lem:monro`'s constant `1.27` depends on a computer check not among Helfgott's cited runs
  (bypassed).

The full record, with line numbers and commits, is `Campaigns/Erdos-1054/LEAN-PROGRESS.md` in the
source repository.
