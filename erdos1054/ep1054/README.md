# EP1054 — Lean formalization of the collaboration paper

This folder is a self-contained Lake project formalizing the manuscript

> H. Chae, J. Fraiture, E. Hou, V. Kovač, C. Kudeba, A. Shakov, D. Vidal,
> **On the first occurrence of an integer as a prefix sum of divisors**
> (unpublished manuscript, Overleaf export of 2026-09-25)

committed in [`paper/`](paper/) (the `.tex` with its internal `%` comment lines removed) (`EP1054.tex`, `EP1054.bib`, and `EP1054.pdf`
built from them; sha256 in [`paper/SHA256SUMS`](paper/SHA256SUMS)). The manuscript's
"Formalization" section is still an empty placeholder; its "Methodology and AI usage" paragraph
refers to an accompanying Lean formalization repository, and this folder is Principia Math's
formalization of the manuscript's results. It does **not** contain H. Chae's formalization of
"every integer besides 2 and 5 is representable"; here representability is one of the four
CONDITIONAL results (see below).

It sits beside the July masters in [`../`](../) (the limsup result of Erdős Problem 1054 and the
almost-all binary Goldbach theorem), which are unchanged and remain valid on their own.

## What is proved

For `N ≥ 1`, `f(N)` is the least `m` whose increasing list of divisors has an initial segment
summing to `N`. The manuscript has **37 numbered results**. Each is stated in Lean as a single
`def … : Prop` in `Principia/Erdos1054/Statements/*.lean` (a definitions-only layer importing
Mathlib and `Principia/Erdos1054/Defs.lean`, nothing else).

| | count | where |
| --- | --- | --- |
| **Verified** — proved with no hypotheses, axiom footprint `[propext, Classical.choice, Quot.sound]`, Comparator targets | **33** | `Challenge.lean` (statements), `Solution.lean` (proofs), `comparator/` |
| **Conditional** — rest on Helfgott's weighted ternary Goldbach theorem; proved here from 41 cited inputs (18 machine computations, 23 published theorems) | **4** | `Conditional.lean` |

The 33 include Theorems 1.1–1.4 (`thm:small-upper`, `thm:small-values`, `thm:almost-log-tail`,
`thm:subexp-growth`), `thm:dadd:universal-singularity`, and `prop:fraiture-finite` (the finite
part of representability). The full list, paper label → Lean name, is the `alignment` block of
[`formalization.yaml`](formalization.yaml).

## What is conditional

`lem:fraiture-balanced-goldbach`, `prop:fraiture-tail`, `thm:fraiture-representability`
(`R = ℕ \ {2, 5}`, i.e. `f(N)` exists for every `N ≠ 2, 5`) and `eq:exact-representability` (the
same statement). **These are not proved unconditionally here.** `Conditional.lean` proves each of
them in two ways, both with every assumption an explicit binder (no `axiom`, no `sorry`):

1. from the single hypothesis `Principia.Erdos1054.Cite_Helfgott_weighted` (Helfgott,
   arXiv:1312.7748, §7.4, (7.49)–(7.50), encoded with existential weights);
2. without that hypothesis, via `Principia.Erdos1054.Alt7.FromAtoms896I.ep1054_atoms896I`, from
   **41 hypotheses, every one of which is a cited input**:
   - **18 cited machine computations**: Platt's Theorem 7.1; Platt–Trudgian RH to `3·10¹²`; and
     16 of Helfgott's runs (`EspagnCheck`, `EspagnSmall`, `Charpy`, `Charpas`, `AusteriaGrid`,
     `MalMain` (VNODE-LP), `AmanitaBisect`, `AppB`, `CameloGrid`, `Wollust`, `Kast`, `Notung`,
     `CortoSmall`, `YuttoSmall`, `CortoC0`, `Ramare`);
   - **23 cited published theorems**: Rosser 1941; Rosser–Schoenfeld 1962 (×8), 1975 (θ bound and
     Cor. 2); Ramaré 1995 (×2), 2013 (Cor. 1.4), 2015 (×2); Ramaré–Saouter 2003; Granville–Ramaré
     1996; the explicit zero count as Helfgott cites it; the sharp large sieve (Montgomery–Vaughan
     1974); Montgomery's inequality (1968); and Montgomery–Vaughan 1973 Theorem 1 (1.6) and
     Lemma 8.

   **No step of Helfgott's argument is owed any more**: every analytic step between these inputs
   is kernel-checked. The 41 inputs are cited — stated as hypotheses referenced to their
   publications — and, **by owner decision, linked rather than re-proved in Lean**. The docstring
   of `Conditional.lean` lists all 41 by name, kind and source; each one's exact meaning is the
   docstring of its definition in the vendored `Principia/Common/TernaryGoldbach/` modules.

**So this is a CONDITIONAL verification, not a complete one**: 33 of the 37 results are verified
unconditionally; the other 4 are verified conditionally on the 41 cited inputs. The caveats that
travel with it (inputs checked against their sources, corrected forms of Helfgott's statements,
errata) are in [`VERIFICATION.md`](VERIFICATION.md) §8.

## Layout

```
lean-toolchain  lakefile.toml  lake-manifest.json   Lean v4.31.0, Mathlib fabf563a (pinned)
Principia/**        the vendored development: 461 modules, copied byte-for-byte from the
                    PrincipiaAI repository (source commit in SOURCE.txt, hashes in SHA256SUMS)
Challenge.lean      the 33 verified statements, `sorry` proofs (the audit fixture)
Solution.lean       the same 33, proved by direct term assignment; `#print axioms` per result
Conditional.lean    the 4 conditional results, every hypothesis named
comparator/         one Comparator config per verified result + all.json
paper/              EP1054.tex, EP1054.bib, EP1054.pdf, SHA256SUMS
formalization.yaml  mathlib-initiative v0.3 metadata, alignment of all 37 results
VERIFICATION.md     what was actually run, with its output, and what was not
```

The vendored set is exactly the transitive `import Principia.*` closure of the nine statement
modules, the modules holding the 33 verified proofs, `Principia.Erdos1054.Spine`,
`Principia.Erdos1054.Alt7.FromAtoms896I` and its axiom gate `GateFromAtoms896I` — nothing else.

**What must be trusted.** Unlike this repository's other folders, `Challenge.lean` imports its
statement modules rather than carrying a copy (the statement layer is ~6.5k lines of definitions).
The audit surface is therefore `Challenge.lean` plus `Principia/Erdos1054/Defs.lean` and the nine
`Principia/Erdos1054/Statements/*.lean` files; each statement's docstring quotes the paper's text
beside its encoding.

## How to verify

```bash
cd erdos1054/ep1054
sha256sum -c --strict SHA256SUMS        # vendored files are the source commit's bytes
(cd paper && sha256sum -c SHA256SUMS)   # the paper is the pinned bytes
lake exe cache get                      # Mathlib oleans
lake build                              # every vendored module
lake build Solution                     # 33 x  'EP1054.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
lake build Conditional                  # the conditional results and their footprints
```

Statement fidelity (that `Solution.lean` proves exactly `Challenge.lean`'s statements with only
the three permitted axioms) is checked by Comparator, which is Linux-only; it runs in CI as
[`.github/workflows/erdos1054-ep1054-comparator.yml`](../../.github/workflows/erdos1054-ep1054-comparator.yml).
The build and audit job is
[`erdos1054-ep1054-build.yml`](../../.github/workflows/erdos1054-ep1054-build.yml). What has and has
not been run so far is recorded in [`VERIFICATION.md`](VERIFICATION.md).
**Comparator passed on CI on 2026-10-04** (run 37185465168: `Your solution is okay!` on all 33
verified results); details in `VERIFICATION.md` §7.
