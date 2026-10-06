# Erdős 1054

Every positive integer except 2 and 5 is the sum of an initial segment of some
positive integer’s increasing divisors, assuming the prime-counting bounds in
Pierre Dusart’s [*Explicit estimates of some functions over primes*](https://doi.org/10.1007/s11139-016-9839-4)
(Corollary 5.2) and the quantitative distinct-prime tail hypothesis used in
[Jimmy/JIF’s argument](https://github.com/jif-perso/erdos_1054/tree/e0e377e79538842721d9b515f53a6d821ad62cec),
based on §7 of Harald Helfgott’s
[*The ternary Goldbach conjecture is true*](https://arxiv.org/abs/1312.7748v2).
These are the explicit Lean assumptions `DusartBounds` and `HelfgottTailHypothesis`, respectively.

Statement: [Challenge.lean](Challenge.lean). Proof: [Solution.lean](Solution.lean).

```sh
lake exe cache get
lake build
```
