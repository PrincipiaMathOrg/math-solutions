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

**Pending** — not yet recorded. A local build on the development machine (Windows 10, 16 GB RAM,
elan-installed `leanprover/lean4:v4.35.0-rc2`, Lake 5.0.0-src+11acb17) is in progress; this section
will be replaced by its real output. So far, measured and not run:

- `lake exe cache get`: first attempt **failed** (8905 decompressions failed with "The system cannot
  find the path specified" — the build directory was nested too deep for Windows' 260-character
  path limit); re-run from a short path: `Completed successfully`, exit 0.
- `lake build`: the first full attempt at the short path was **terminated without an error message
  after ~90 minutes** (exit 127) while five Mathlib imports ran concurrently on a disk-bound machine;
  it is being re-run one module at a time.
- `#print axioms Pntpp.DivisorPrefix.erdos1054_conditional`: **not yet run** here.

Until this section is filled in, the author's own record stands (his `formalization.yaml`:
`sorry_count: 0`, axioms `propext, Classical.choice, Quot.sound`, local build and Comparator
passed) and is **not** independently confirmed by Principia Math.

## Continuous integration

`.github/workflows/erdos1054-hyunsik-build.yml` (triggered by changes under `erdos1054/hyunsik/**`)
checks `SHA256SUMS`, installs elan, runs `lake exe cache get` and `lake build`, fails if any
declaration outside `Challenge.lean` uses `sorry`, and fails unless the printed axiom footprint of
`Pntpp.DivisorPrefix.erdos1054_conditional` lies within `{propext, Classical.choice, Quot.sound}`.
The footprint probe file is written to the runner's temp directory, never into this folder.
