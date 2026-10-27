# MathDB #351036 -- source and status audit

Audit date: 2026-08-18.

## Source reconstruction

The primary source is:

- Noah Bertram, Xiantao Deng, C. Douglas Haessig, and Yan Li, "Partial zeta
  functions, partial exponential sums, and p-adic estimates," arXiv:2106.09755.
- arXiv record: https://arxiv.org/abs/2106.09755
- Final article: *Finite Fields and Their Applications* 87 (2023), 102139,
  https://doi.org/10.1016/j.ffa.2022.102139

Version 1, Conjecture 2.1, says that the sum is an integer and asks for a
closed form.  Version 2 and the final article retain it as Conjecture 3.2,
using the phrase "rational integer" and adding a prime-`n` formula in Theorem
3.3.

The standalone conjecture does not repeat the restriction on `k`.  However,
Theorem 3.1 immediately before it factors the partial zeta function as a
product over `k | phi(n)`.  Its derivation begins with a primitive
`phi(n)`-th root `zeta`, chooses a residue `j` of additive order `k`, and sets
`zeta_k=zeta^j`.  The intended hypothesis is therefore exactly

\[
k\mid\varphi(n).
\]

Without it, the MathDB statement is false; `n=2,a=2,d=1,k=3` gives `zeta_3`.

## Current-status search

The arXiv record has no version after v2 (2022-10-25).  The final 2023 article
still presents the general integrality assertion as Conjecture 3.2.  Exact
formula, exact phrase, title/author, and forward-citation searches found no
later paper claiming a resolution.  The two forward-citing works located do
not discuss this conjecture; in particular, the 2026 preprint "p-adic Theory
for Partial Toric Exponential Sums" (arXiv:2604.07330) does not address the
gcd sum.

This is a current evidence report, not a claim that no unpublished or
unindexed proof exists.

## Disposition

The literal MathDB record is malformed and false because it omits
`k | phi(n)`.  The intended integrality conjecture is resolved by the proof in
`proof.md`: reduce the coprime case modulo `n` to a prime base via Dirichlet's
theorem and invoke the source's own zeta-factor exponent theorem; then remove
the prime-power factors of `n` that divide `a`.  The same file gives a finite
Ramanujan-divisor formula.
