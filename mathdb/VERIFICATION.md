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

- **Comparator has run on no problem yet, and a contract exists for only one.** #343324 has
  `Principia/MathDB/Statements/P343324.lean` (definitions and statement constants, no proof),
  `challenge/Challenge343324.lean` (which imports that module and nothing else) and
  `challenge/Solution343324.lean` (which imports the development and discharges the same
  constants by term assignment), with `comparator/343324.json` and the
  `mathdb-comparator` workflow. The other 142 problems have no contract. Until a run
  finishes, the formalization stage link on a Principia project is a pointer to the source,
  not a verdict.
- **A Comparator pass here would not certify faithfulness to MathDB.** MathDB publishes no
  formal statement for any of these problems -- its repository carries two `.lean` files in
  total, both for Collatz -- so every statement constant was written by this project from the
  informal text. Comparator checks that the solution proves the challenge's statements, with a
  clean footprint, without having been compiled first. Whether the challenge says what MathDB
  meant is a separate question that no mechanical check here answers.
- **No continuous-integration run certifies them.** They were gated locally. The project's own
  CI has been unavailable (billing) for the whole period in which this work was done, so every
  verdict recorded here is a local one.
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
