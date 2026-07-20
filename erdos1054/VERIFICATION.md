# VERIFICATION — erdos1054

The honest ledger. Every claim below is either a command that was actually run with its
real output recorded, or an explicit note that it was **not** run. Nothing here is
inferred from "it should work."

Environment for everything marked *run here*: Docker on WSL2 (kernel 6.6.87.2, aarch64),
Debian bookworm, Lean toolchains installed via elan.

---

## 1. Master integrity — RUN, passes

```
$ cd masters && sha256sum -c SHA256SUMS
Erdos1054_2ndMomentProof.gate.log: OK
Erdos1054_2ndMomentProof.lean: OK
Erdos1054_3rdMomentProof.gate.log: OK
Erdos1054_3rdMomentProof.lean: OK
GoldbachChainMaster.gate.log: OK
GoldbachChainMaster.lean: OK
lakefile.toml: OK
lake-manifest.json: OK
lean-toolchain: OK
README.md: OK
```

All 10 entries verify. Note: `SHA256SUMS` previously carried a stray CRLF on its final
line, which made this exact command fail on `README.md` with "No such file or directory"
even though the hash was correct. The file has been normalized to LF; the hashes
themselves are unchanged and still describe the same bytes.

## 2. `sorry` / `axiom` audit of the masters — RUN, clean

No `sorry`, no `admit`, and no `axiom` declaration occurs in any master. The only textual
matches for "sorry" are prose inside comments (e.g. `Erdos1054_3rdMomentProof.lean:35087`,
"compiles with zero sorry"). `Erdos1054Conditional.lean:452` likewise mentions `sorry`
only in a comment.

`comparator/Challenge.lean` does contain `sorry` — deliberately. It is the specification
half, and those `sorry`s are what Comparator is asked to discharge against a master.

## 3. Axiom footprint — NOT re-run here; recorded from the gate logs

Each master ships its full compiler log (`masters/*.gate.log`), whose final lines are the
`#print axioms` verdicts. Those logs report, for every headline theorem:

```
[propext, Classical.choice, Quot.sound]
```

covering `almost_all_binary_goldbach_proven`, `Erdos1054.almost_all_binary_goldbach`,
`erdos1054_third_moment_full_proof`, `erdos1054_second_moment_full_proof`, and
`Represented.main`.

**These logs were produced elsewhere and have not been reproduced in this repository.**
Recompiling a master requires a PrimeNumberTheoremAnd checkout at the pinned revision plus
~1-2 h for the dependency and ~50-75 min for the master itself. The logs are integrity-
pinned by §1, so they are the same bytes that were generated — but "the same bytes" is a
weaker claim than "re-derived independently," and it is the only claim made here.

## 4. Statement fidelity of `comparator/Challenge.lean` — RUN (by hand), passes

All 8 definitions in `Challenge.lean` (`F`, `IsRep`, `Represented`, `f`, `countUpTo`,
`PositiveLowerDensity`, `DensityZero`, `notSumOfTwoPrimes`) were compared
character-for-character against the `Erdos1054` namespace of
`masters/Erdos1054_3rdMomentProof.lean` (L35101-35113). All 8 match exactly. The same
check passes against each `comparator/Solution_*.lean`.

All 7 delegation targets referenced by the bridges exist as real theorems in their
corresponding masters.

## 5. Comparator on the real masters — **NOT RUN**

Comparator has **not** been run against any master in `masters/`. Doing so requires
building PrimeNumberTheoremAnd + Mathlib + a 36k-line master inside the sandbox, which is
the ~350-minute `.github/workflows/erdos1054-comparator.yml` job. That workflow is
`workflow_dispatch` only and had not been dispatched as of this commit.

**Do not read anything in this repository as a claim that Comparator has certified these
theorems.** It has not. §6 records what *was* established.

## 6. Comparator on a structural mirror — RUN, passes

To de-risk §5 without the multi-hour build, a miniature project was constructed that
mirrors this repository's Comparator arrangement exactly — same namespace layout
(`Erdos1054Challenge` vs `Erdos1054`), same verbatim-definition duplication, same
`Master` delegation pattern, same config shape including `definition_names` — but with
trivial arithmetic in place of the real mathematics, so no Mathlib is needed.

Real Comparator, at the SHAs pinned in `.github/workflows/erdos1054-comparator.yml`, run
against that mirror:

```
Exporting #[Erdos1054Challenge.erdos1054_main, propext, Quot.sound, Classical.choice, ...] from Challenge
Exporting #[...] from Solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
COMPARATOR_EXIT=0
```

This establishes three things about the *arrangement*, and nothing about the mathematics:

- The bridge structure is accepted by Comparator.
- Listing fully-defined (non-hole) definitions under `definition_names` is accepted.
  Comparator's documentation presents that field in terms of definition *holes*; this
  confirms non-hole entries do not cause a rejection.
- The pinned `LEAN4EXPORT_SHA` (see §7) is the one that works.

Sandboxing caveat: this run used Comparator's own `scripts/fake-landrun.sh`, because the
pinned `landrun` requires Landlock ABI v5 (Linux >= 6.10) and the WSL2 kernel used here
provides ABI v3, aborting with "missing kernel Landlock support". With fake-landrun the
adversarial-sandbox guarantee is void — statement comparison, the axiom whitelist, and
kernel replay all still ran, but a hostile `Solution.lean` would not have been contained.
That is acceptable for checking one's own arrangement and is **not** acceptable as a
trust claim. The CI workflow builds real landrun and probes that it actually denies an
out-of-policy write before trusting a pass.

## 7. Two bugs found and fixed — both would have failed CI

**(a) The Solution bridges could not compile.** Each `comparator/Solution_*.lean`
previously did `import Challenge` and then re-declared `erdos1054_main` etc. in the same
`Erdos1054Challenge` namespace. That is a duplicate declaration:

```
Solution.lean:4:8: error: `Erdos1054Challenge.erdos1054_main` has already been declared
```

Comparator's own test projects confirm the intended shape: no test `Solution` imports its
`Challenge`; each re-declares independently, because Comparator compares two separately
elaborated environments. The bridges now import only `Mathlib` and `Master` and reproduce
the definitions verbatim. Verified: `countUpTo` is built through a `classical` tactic
block, so "verbatim implies definitionally equal" was not automatic there — two
independent elaborations in separate namespaces were checked to be `rfl`-equal.

**(b) The pinned `lean4export` was the wrong Lean version.** The lean-eval pin
`3de59f1` has `lean-toolchain = v4.32.0-rc1`, while this project is on `v4.31.0`. Running
Comparator with it fails at the export step:

```
failed to read file '.../Challenge.olean', incompatible header
```

`lean4export` must be built against the *same* Lean version as the project it exports.
`8554815c2dc6b7abe99ec1f08849c9759ba77947` is the lean4export commit whose lean-toolchain
is `v4.31.0`; with it, the §6 run succeeds. Both `scripts/run-comparator.sh` and the CI
workflow now pin that commit.

The same mismatch was present in `.github/workflows/erdos123-comparator.yml` (pinned
`af5aa64`, toolchain v4.33.0-rc1, against a v4.31.0 project) and has been corrected there
too.

**(c) `systemd-run --pty` hangs on a CI runner.** Comparator's README gives `--pty`, which
allocates a terminal and waits on it; on a GitHub runner that never resolves. The first
erdos123 comparator dispatch sat for 2h19m with no output after printing "Press ^] three
times within 1s to disconnect TTY". `--pipe --wait --collect` is the non-interactive
counterpart. This workflow uses it from the start, and carries `timeout-minutes` so a
future hang is reported as a failure rather than running to the job cap. Credit for
diagnosing this goes to the erdos123 run; the fix is carried over here unchanged, and the
`RestrictAddressFamilies` guard is kept verbatim.

**(d) lean4export must be on `PATH`, not merely named by `COMPARATOR_LEAN4EXPORT`.**
Comparator invokes lean4export *by name* inside the landrun sandbox, and `systemd-run`
does not inherit the caller's environment — only what is passed with `-E`. The erdos123
run therefore failed with:

```
[landrun:error] Failed to find binary: exec: "lean4export": executable file not found in $PATH
```

Three configurations were tested directly:

| lean4export on `PATH` | `COMPARATOR_LEAN4EXPORT` set | result |
| --- | --- | --- |
| no  | no  | `Failed to find binary` |
| no  | yes | `Failed to find binary` — the env var is **not** sufficient |
| yes | no  | `Your solution is okay!` |

Both workflows now add `/tmp/lean4export/.lake/build/bin` to `$GITHUB_PATH`. This
repository's erdos1054 workflow originally passed only `-E COMPARATOR_LEAN4EXPORT`, which
the middle row shows would have failed identically; it was corrected before any dispatch.

Note the ordering of (b), (c) and (d): the hang in (c) occurs before the export step, so
the first erdos123 dispatch never reached (d), and (d) blocks the export step, so no run
has yet reached (b). Each fix uncovers the next. (b) is therefore still *unconfirmed on
CI* — it is confirmed only in the local mirror of §6, where the corrected pin produced a
passing run.

## 8. Correspondence between the Lean and the paper

- `masters/Erdos1054_3rdMomentProof.lean` formalizes the route written up in the paper
  (§6, *A third-moment estimate for large cofactors*).
- `masters/Erdos1054_2ndMomentProof.lean` proves the **same headline statement** by an
  independent second-moment route that is **not** written up in the current paper draft.
  The paper contains no second-moment argument. Earlier revisions of `README.md` and
  `formalization.yaml` described this file as formalizing "the paper's §6 pure
  second-moment route", which was incorrect; the description has been corrected rather
  than the file removed, since it is a genuine independent verification of the result.
- Quantifier: the paper's Theorem 1 quantifies over real `A >= 1`; the masters quantify
  over `A : Nat`. Equivalent in strength (apply the Nat form to the ceiling of a real
  `A`). `Erdos1054Conditional.lean` states the real form directly. This is noted in
  `comparator/Challenge.lean` so a reviewer reading only the audit surface sees it.

## 9. Line counts

`README.md` and `formalization.yaml` previously reported line counts that did not match
the files (3,904 vs 4,136 for `Erdos1054Conditional.lean`; 36,698 vs 36,697; 31,714 vs
31,716). Corrected to the actual `wc -l` values.
