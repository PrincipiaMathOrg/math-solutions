# Comparator certification

This directory arranges the Erdős 1054 verification for the
[`comparator`](https://github.com/leanprover/comparator) tool, following the
practice T. Tao recommended (email, 16 Jul 2026) and discussed on the Lean Zulip
`#AI-authored-projects` channel.

## What comparator certifies

`comparator` is a trusted judge for Lean proofs. Given a *challenge* module of
human-readable statements and a *solution* module that proves them, it exports
both to Lean's kernel export format and checks, in a sandbox, that:

1. the solution's theorems prove **exactly** the challenge's statements (no
   weakening, no altered definitions — this rules out "semantic hallucination"
   where a proof typechecks but proves something other than intended); and
2. the proofs use **no axioms** beyond the permitted set
   `[propext, Quot.sound, Classical.choice]` (Lean's three foundations).

## Files

- **`Challenge.lean`** — the specification. Self-contained, human-auditable. It
  reproduces the relevant definitions *verbatim* from the masters and states the
  headline theorems, split by logical dependency per Tao's suggestion:
  - **(A)** `erdos1054_main` / `erdos1054_ratio_unbounded` — the unconditional
    main result (positive lower density of `N` with `f(N) > A·N`).
  - **(B)** `almost_all_binary_goldbach` — the heavy circle-method input, stated
    separately so the light/heavy split is explicit.
- **`Solution_3rdMoment.lean`**, **`Solution_2ndMoment.lean`**,
  **`Solution_goldbach.lean`** — bridges that prove the challenge statements by
  delegating to the corresponding master theorem. The delegation is by
  definitional equality: each `Erdos1054Challenge` definition has a body
  identical to its master counterpart.

  These files deliberately do **not** `import Challenge`. Comparator builds and
  exports `Challenge` and `Solution` as two *independently elaborated*
  environments and then checks that the declarations used in the listed
  theorems' statements agree; a solution that imported the challenge would fail
  to compile outright (`'Erdos1054Challenge.erdos1054_main' has already been
  declared`) and would defeat the comparison. Each bridge therefore reproduces
  the definitions it needs verbatim from `Challenge.lean` — byte-identical
  bodies — and imports only `Mathlib` and `Master`. The `countUpTo` definition
  is elaborated through a `classical` tactic block in both files; the two
  independent elaborations are definitionally equal, so the delegation still
  goes through by `exact`.
- **`config/*.json`** — one comparator config per master, listing the
  `theorem_names`, `definition_names`, and `permitted_axioms` to check.

## Reproducing

Comparator requires Linux (it sandboxes with `landrun` / `systemd-run`), so runs
happen in CI, not on a typical dev laptop. See
[`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml) and
[`scripts/`](../scripts). Locally on Linux:

```bash
# 1. Build the workspace: clone PNT+ @ the pinned rev, copy a master in as
#    module `Master`, and wire in Challenge + the matching Solution bridge.
scripts/assemble-workspace.sh 3rdMoment

# 2. Install the pinned comparator toolchain and run the check.
scripts/run-comparator.sh 3rdMoment
```

`assemble-workspace.sh <target>` accepts `3rdMoment`, `2ndMoment`, or
`goldbach`; it copies `masters/Erdos1054_3rdMomentProof.lean` (etc.) into the
PNT+ checkout as `Master.lean`, registers `Master`, `Challenge`, and `Solution`
as `lean_lib`s, and copies the matching `Solution_<target>.lean` to `Solution.lean`.

> **Status note.** The bridges are written to hold by definitional equality, and
> the definitions have been checked byte-identical against `Challenge.lean` and
> against the `Erdos1054` namespace of each master. Comparator itself has **not**
> yet been run end-to-end: it requires Linux (`landrun`/Landlock under
> `systemd-run`) plus a full PrimeNumberTheoremAnd + Mathlib + master build, so
> the first `workflow_dispatch` run of `.github/workflows/comparator.yml` is the
> authoritative check. If comparator reports a mismatch, iterate on
> `Challenge.lean` / the bridge **only** — never on the masters, whose
> kernel-checked axiom verdicts are recorded in `masters/*.gate.log`.
>
> One open question for that first run: `config/*.json` lists the shared
> definitions under `definition_names`. In comparator's documented usage that
> field is for *definition holes* (definitions left `sorry` in the challenge for
> the solution to fill in), whereas these are fully defined on both sides. The
> listing should be harmless — comparator checks name/type/universe/safety match
> for them — but if the run rejects it, drop `definition_names` and rely on the
> statement-declaration comparison, which already covers these definitions.
