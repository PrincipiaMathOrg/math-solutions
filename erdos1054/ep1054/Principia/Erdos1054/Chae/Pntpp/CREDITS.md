# Credits for `Principia/Erdos1054/Chae/Pntpp/`

These modules are a port of **Hyunsik Chae's** Lean development
[`hs-chae/erdos1054_hyunsik`](https://github.com/hs-chae/erdos1054_hyunsik) (commit `c065f37`,
Lean v4.35.0-rc2), Apache License 2.0 (full text: [`LICENSE`](LICENSE), copied unchanged from
upstream). The port changes only import paths and adds two file-level `set_option`s; every
statement and proof is his.

**What his development formalizes.** In his own words (`formalization.yaml`): "Formalization of the
divisor-prefix argument in Jimmy/JIF's Erdos 1054 verifier, conditional on two explicit
prime-counting estimates and the distinct-prime Helfgott tail. Finite checks use kernel-verified
subset-sum bitsets." The mathematical source is **Jimmy Fraiture (JIF)**, *Erdős Problem 1054
verifier*, [`jif-perso/erdos_1054`](https://github.com/jif-perso/erdos_1054/tree/e0e377e79538842721d9b515f53a6d821ad62cec)
(relationship: adapts). The prime-window, subset-sum extension, `Bq` and Goldbach-tail arguments are
Jimmy Fraiture's; the Lean formalization and its new finite certificate algorithms are Hyunsik
Chae's. His `formalization.yaml` also records that the conversion was carried out with a Codex agent
under his direction, and acknowledges Helfgott (§7 of *The ternary Goldbach conjecture is true*),
Rosser and Schoenfeld (1962), PNT+, Lean and Mathlib.

**His inputs.** `DusartBounds` (two prime-counting estimates; his README cites Dusart,
*Explicit estimates of some functions over primes*, Cor. 5.2, and his `formalization.yaml` cites
Rosser–Schoenfeld 1962 as their source) and `HelfgottTailHypothesis`. In `Chae/Route.lean`,
`HelfgottTailHypothesis` is supplied by Principia's formalization of Helfgott's argument
(`Chae/Bridge.lean`, `chae_atoms896I`, from 41 cited inputs) and `DusartBounds` from
Rosser–Schoenfeld 1962, Corollary 1, (3.5)–(3.6), as named literature hypotheses.

The connecting modules `Chae/Bridge.lean` (sections 2–3) and `Chae/Route.lean` (sections 2–4) are
Principia's; they prove nothing of his route.
