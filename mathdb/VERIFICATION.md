# Verification record -- MathDB formalizations

## What was run

For every module in this directory:

1. `lake build Principia.MathDB.Problem<n>` against `lean-toolchain`
   (`leanprover/lean4:v4.31.0`) and the Mathlib revision pinned in `lake-manifest.json`.
2. A per-module gate: a scratch file importing the module with a `#print axioms` line for
   every declaration it introduces, run as
   `env LAKE_NO_CACHE=1 lake env lean <gate>.lean`.
3. The gate log parsed by the campaign's reporter, which requires the printed footprints and
   the gated declarations to agree **as sets** and every footprint to be inside
   `[propext, Classical.choice, Quot.sound]`.

A whole-directory gate was not used: it exhausts memory on the machine these were built on,
and a partial gate that dies is indistinguishable from a clean one in its log.

## What was NOT run, and must not be inferred

- **Comparator has run on exactly one problem, and a contract exists for only that one.**
  #343324 PASSED: workflow `mathdb-comparator`, run 40425676138 at commit `b541a22`, and the
  Principia project reports `comparator.verdict: passed` with `current_verified: true`. It has
  `Principia/MathDB/Statements/P343324.lean` (definitions and statement constants, no proof),
  `Challenge343324.lean` (which imports that module and nothing else) and
  `Solution343324.lean` (which imports the development and discharges the same constants by
  term assignment), each its own `lean_lib`, with `comparator/343324.json`,
  `formalization/343324/formalization.yaml` and the `mathdb-comparator` workflow. The other
  142 problems have no contract at all, so for each of them the formalization stage link on
  its Principia project is a pointer to source a reader can rebuild, not a verdict.
- **A Comparator pass here does not certify faithfulness to MathDB.** MathDB publishes no
  formal statement for any of these problems -- its repository carries two `.lean` files in
  total, both for Collatz -- so every statement constant was written by this project from the
  informal text. Comparator checks that the solution proves the challenge's statements, with a
  clean footprint, without having been compiled first. Whether the challenge says what MathDB
  meant is a separate question that no mechanical check here answers.
- **CI certifies exactly one of them.** #343324 was checked by the `mathdb-comparator`
  workflow in this repository. Every other verdict recorded here is a LOCAL gate run on the
  authors' machine with no CI run id: the project's own CI was unavailable (billing) for the
  whole period in which the formalization work was done, and the gates were never re-run
  under it.
- **A clean axiom footprint is not a faithfulness check.** It says the proof rests on nothing
  but Lean's standard axioms; it says nothing about whether the formal statement renders the
  informal problem. Each module's header states what it formalizes, where it departs from the
  source statement, and what it still owes. Several modules formalize a *refutation* of the
  source conjecture, or a corrected version of a statement that is false as written.

## Reproducing

```
cd mathdb
lake exe cache get
lake build Principia
```

Then, for one module, print the footprints yourself:

```lean
import Principia.MathDB.Problem<n>
#print axioms <declaration>
```
