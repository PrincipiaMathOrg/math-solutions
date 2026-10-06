# Notes by Principia Math on this folder

## Attribution

- **Author: Hyunsik Chae** (hsc1403@snu.ac.kr). Everything in this folder except this file,
  `SOURCE.txt` and `SHA256SUMS` is his work, copied byte-for-byte from
  <https://github.com/hs-chae/erdos1054_hyunsik> at commit
  `c065f3788160ee5a7da0390538428af237a5f7f4`, and is distributed under **his Apache-2.0 license**
  ([`LICENSE`](LICENSE), as shipped upstream). His [`README.md`](README.md) and
  [`formalization.yaml`](formalization.yaml) are unchanged and are the authoritative description of
  his work, including the sources it adapts (Jimmy/JIF's verifier; Helfgott; Dusart / Rosser and
  Schoenfeld). He prepared this repository for inclusion in the unified Erdős 1054 repository
  (email to Anton Shakov, 2026-09-28). Principia Math claims no part of it.
- **What it proves.** `Solution.lean` proves

  ```lean
  theorem Pntpp.DivisorPrefix.erdos1054_conditional
      (dusart : DusartBounds) (helfgott : HelfgottTailHypothesis) : TargetClassification
  ```

  where `TargetClassification` says: for every `n > 0`, `n` is the sum of a nonempty initial
  segment of the increasing divisors of some positive integer **iff** `n ≠ 2` and `n ≠ 5`.
  `Challenge.lean` states the same theorem with a `sorry` proof (the intended audit fixture; it is
  the only `sorry` in the folder).
- **Its two explicit assumptions**, both theorem parameters (no `axiom`):
  1. `DusartBounds` — `x / log x ≤ π(x)` for `x ≥ 17` and `π(x) ≤ 1.2551 · x / log x` for `x > 1`
     (Dusart, *Explicit estimates of some functions over primes*, Cor. 5.2);
  2. `HelfgottTailHypothesis` — every odd `N ≥ 10^27` is `p + q + r` with `p, q, r` distinct odd
     primes, each `> N / (30000 log N)` (from §7 of Helfgott, *The ternary Goldbach conjecture is
     true*).
- **Relation to the unified package.** The unified package's [`../ep1054/`](../ep1054/) formalizes
  Helfgott's argument independently and derives, from 41 cited inputs (18 cited machine
  computations, 23 cited published theorems; see `../ep1054/VERIFICATION.md` §8), the paper's
  `lem:fraiture-balanced-goldbach` (`Lem_FraitureBalancedGoldbach`), which is the same statement as
  his `HelfgottTailHypothesis`. The connecting module is **`Principia.Erdos1054.Chae.Bridge`** in the
  PrincipiaAI Lean library; it transcribes his five statement definitions (statements only, none of
  his proofs) and proves `helfgottTail_iff : HelfgottTailHypothesis ↔ Lem_FraitureBalancedGoldbach`
  and **`Principia.Erdos1054.Chae.chae_atoms896I`** (the 41 cited inputs ⟹
  `HelfgottTailHypothesis ∧ TargetClassification`). Caveats, stated plainly: that bridge module is
  **not** part of the vendored `../ep1054/` closure at the time of writing, and it does not
  discharge `DusartBounds` — it obtains `TargetClassification` through the ep1054 route, not
  through this folder's proof. Nothing here changes his theorem or its assumptions.

## Build record (run by Principia Math, with this folder's own toolchain)

**Build of record: GitHub Actions run
[37405367153](https://github.com/antoshashakov/Principia-Math-Solutions/actions/runs/37405367153)**
(workflow `erdos1054-hyunsik-build`, commit `181c41b`, `ubuntu-latest`, 2026-10-06, conclusion
**success**, job 9m19s). elan resolved this folder's `lean-toolchain` (v4.35.0-rc2); nothing in the
folder was modified. Real output, quoted from the log:

```
$ sha256sum -c --quiet --strict SHA256SUMS
SHA256SUMS lines: 46, upstream files present: 46
$ lake exe cache get
Decompressed 8915 file(s)
$ lake build
warning: Challenge.lean:44:8: declaration uses `sorry`
✔ [8967/8969] Built Pntpp.DivisorPrefix.FullCoverage (3.1s)
⚠ [8968/8969] Built Solution (3.0s)
Build completed successfully (8969 jobs).
$ # sorry check over the build log
no sorry-using declaration outside Challenge.lean
$ lake env lean Axioms.lean    # import Solution / #print axioms Pntpp.DivisorPrefix.erdos1054_conditional
'Pntpp.DivisorPrefix.erdos1054_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
footprint within {propext, Classical.choice, Quot.sound}
```

The only `sorry` warning is `Challenge.lean`'s intended hole. The other 38 build warnings are
linter style notes (34 × `unnecessarySeqFocus` in `ExplicitBridge.lean`, one in `SmallBq.lean`,
two "ambiguous namespace `Computation`" notes, one "Try this" suggestion in `Solution.lean`); none
affects the result.

**Local build on the development machine (Windows 10, 16 GB RAM, HDD): not completed.**
`lake exe cache get` first failed (8905 decompressions: "The system cannot find the path specified" —
the build directory was too deep for Windows' 260-character path limit) and then succeeded from a
short path (`Completed successfully`). `lake build` was then terminated without an error message
after ~90 minutes (exit 127) with five Mathlib imports competing for a saturated disk alongside
another Lean build; a one-module-at-a-time retry was stopped by us after the first module had not
finished importing Mathlib in 48 minutes. These are environment limits of that machine, not
findings about this development; the CI run above is the independent build.

## Continuous integration

`.github/workflows/erdos1054-hyunsik-build.yml` (triggered by changes under `erdos1054/hyunsik/**`)
checks `SHA256SUMS`, installs elan, runs `lake exe cache get` and `lake build`, fails if any
declaration outside `Challenge.lean` uses `sorry`, and fails unless the printed axiom footprint of
`Pntpp.DivisorPrefix.erdos1054_conditional` lies within `{propext, Classical.choice, Quot.sound}`.
The footprint probe file is written to the runner's temp directory, never into this folder.
