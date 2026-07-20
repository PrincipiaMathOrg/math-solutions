# Erdős Problem 1054 — full machine-verified solution

A complete, Lean 4 kernel-checked resolution of the limsup part of
[Erdős Problem 1054](https://www.erdosproblems.com/1054), together with the
unconditional formalization of the almost-all binary Goldbach theorem it rests
on, and the accompanying paper draft.

Let `f(N)` be the least `m` such that `N` is the sum of an initial segment of the
increasing divisors of `m`. This project proves that for every fixed `A ≥ 1`, a
**positive proportion** of integers `N` satisfy both `f(N) < ∞` and `f(N) > A·N`
— in particular `limsup f(N)/N = ∞` over represented `N`.

Every headline theorem compiles with **zero errors and no axioms beyond Lean's
three foundations**:

    [propext, Classical.choice, Quot.sound]

## The masters (the full ~36k-line verification)

Each file in [`masters/`](masters/) is a single self-contained Lean file, kernel-checked,
shipping with its full compiler log (`*.gate.log`) whose final lines are the
`#print axioms` verdicts.

| File | Headline theorem | Lines |
|---|---|---|
| `masters/GoldbachChainMaster.lean` | `GoldbachChain.GoldbachReduction.almost_all_binary_goldbach_proven : DensityZero notSumOfTwoPrimes` | 31,716 |
| `masters/Erdos1054_2ndMomentProof.lean` | `Erdos1054.erdos1054_second_moment_full_proof` (alternate second-moment route; **not** covered by the current paper draft) | 36,748 |
| `masters/Erdos1054_3rdMomentProof.lean` | `Erdos1054.erdos1054_third_moment_full_proof` (the route written up in paper §6) | 36,697 |

`GoldbachChainMaster.lean` is the standalone almost-all Goldbach proof (Siegel via
Goldfeld's route, uniform zero-free region, Siegel–Walfisz, Vinogradov's minor
arcs via Vaughan's identity, circle-method variance assembly). The two Erdős
masters each bundle the Goldbach master with the complete Erdős 1054 development
and differ only in §6.

## Logical dependency (the split T. Tao suggested)

- **(A) Main result — unconditional.** `erdos1054_third_moment_full_proof` /
  `_second_moment_full_proof`: positive lower density of `{ N : f(N) > A·N }`.
  Stated with `f(N) = sInf{…}` so it does not presuppose finiteness.
- **(B) Almost-all binary Goldbach — the one heavy input.**
  `almost_all_binary_goldbach_proven`. The Erdős masters discharge (B) against
  this proof, so (A) stands on Lean's foundations alone.
- **(C) Conditional route.** [`Erdos1054Conditional.lean`](Erdos1054Conditional.lean)
  (4,136 lines) proves the limsup result assuming a `DeepInputs` hypothesis that
  bundles (B); it is the lighter, conditional formalization referenced in the
  correspondence. `C + B ⇒ A`.

This split is spelled out machine-readably in
[`formalization.yaml`](formalization.yaml) and arranged for `comparator` in
[`comparator/`](comparator/).

## Paper

[`paper/erdos1054.tex`](paper/erdos1054.tex) / `paper/erdos1054.pdf` — *Unbounded
ratios in Erdős Problem 1054* (draft). Prior contributions to the full problem
(Tao; Kovač, Price, Bloom; user `jif`) are noted in `formalization.yaml`.

## Verifying

**Integrity of the masters:**

```bash
cd masters && sha256sum -c SHA256SUMS
```

**Recompiling a master** (inside the pinned PNT+ checkout; ~1–2 h for the
dependency, then ~50–75 min per master):

```bash
git clone https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
cd PrimeNumberTheoremAnd
git checkout d963a6e694a05cd82e5f9b9ae7f4d94123e85393
# copy the master .lean file(s) into this directory, then:
lake exe cache get
lake build PrimeNumberTheoremAnd.MediumPNT PrimeNumberTheoremAnd.PerronFormula
lake env lean Erdos1054_3rdMomentProof.lean   # prints the axiom verdict
```

Toolchain `leanprover/lean4:v4.31.0`; Mathlib pinned at
`db127794c79fdeb86f6b0cf6ff2c804026fbaff1` (see `masters/lake-manifest.json`).

**Comparator certification** (that the masters prove exactly the human-readable
statements, using only the three permitted axioms) has **not yet been run against the
masters** — see [`VERIFICATION.md`](VERIFICATION.md) §5 for exactly what has and has not
been checked. It runs in CI on Linux — see
[`comparator/README.md`](comparator/README.md) and
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml).

## Layout

```
README.md                  formalization.yaml
VERIFICATION.md            what was actually run, and what was not
paper/                     erdos1054.tex, erdos1054.pdf
masters/                   the three masters + gate logs + SHA256SUMS + lake files
Erdos1054Conditional.lean  light conditional (DeepInputs) formalization
comparator/                Challenge.lean, Solution_*.lean bridges, config/, README
scripts/                   assemble-workspace.sh, run-comparator.sh
.github/workflows/         comparator.yml (workflow_dispatch)
```
