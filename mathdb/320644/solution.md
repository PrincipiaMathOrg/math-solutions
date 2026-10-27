# The supercongruence modulo \(p^3\)

## Statement

Write

\[
S_n(m)=\sum_{j=1}^m j^n.
\]

Suppose that `n,k` are positive integers satisfying

\[
S_n(k)\equiv(k+1)^n\pmod {k^2}.                       \tag{1}
\]

We prove that, for every prime `p` dividing `k`,

\[
\boxed{S_n(k)\equiv\frac{k}{p}S_n(p)\pmod {p^3}}.     \tag{2}
\]

This proves Conjecture 2 of Sondow and MacMillan.

## Two elementary reductions

Fix `p|k` and put `a=k/p`.  Splitting `1,...,k` into the `a` blocks
`tp+1,...,tp+p` and reducing modulo `p` gives

\[
S_n(k)\equiv aS_n(p)\pmod p.
\]

On the other hand, (1) is congruent to `1` modulo `p`.  The standard
finite-field power-sum identity is

\[
S_n(p)\equiv
\begin{cases}
-1\pmod p,&p-1\mid n,\\
0\pmod p,&p-1\nmid n.
\end{cases}                                           \tag{3}
\]

It follows at once that

\[
p-1\mid n,\qquad a\equiv-1\pmod p.                   \tag{4}
\]

In particular `p` does not divide `a`.  Since this holds for every prime
dividing `k`, the integer `k` is squarefree.

For the main calculation, let

\[
A_1=\sum_{t=0}^{a-1}t=\frac{a(a-1)}2,
\qquad
A_2=\sum_{t=0}^{a-1}t^2=\frac{a(a-1)(2a-1)}6.
\]

For `n>=2`, expand `(tp+r)^n` through the quadratic term and sum over
`0<=t<a`, `1<=r<=p`.  This gives the exact congruence

\[
\begin{aligned}
S_n(ap)-aS_n(p)
&\equiv npA_1S_{n-1}(p)\\
&\quad+\binom n2p^2A_2S_{n-2}(p)
\pmod {p^3}.                                          \tag{5}
\end{aligned}
\]

The definitions of `A_1,A_2` as sums make clear that they are integers,
including when `p=2` or `3`.

## Primes \(p\ge5\)

By (4), `p-1|n`; hence `n>=4`.  The exponent `n-1` is odd, so pairing
`r` with `p-r` yields

\[
r^{n-1}+(p-r)^{n-1}
\equiv(n-1)p r^{n-2}\pmod {p^2}.
\]

The term `p^{n-1}` is also zero modulo `p^2`, and therefore

\[
S_{n-1}(p)
\equiv(n-1)p\sum_{r=1}^{(p-1)/2}r^{n-2}\pmod {p^2}.   \tag{6}
\]

Now `n-2` is even, while `p-1` cannot divide `n-2`: it divides `n`, and
`p-1>=4`.  By (3),

\[
\sum_{r=1}^{p-1}r^{n-2}\equiv0\pmod p.
\]

The full sum is twice the half-sum modulo `p`, so the half-sum in (6) is
zero modulo `p`.  Consequently

\[
p^2\mid S_{n-1}(p).
\]

The same power-sum identity also gives `p|S_{n-2}(p)`.  Both correction
terms in (5) vanish modulo `p^3`, proving (2) for every `p>=5`.

## The prime \(p=3\)

Assume first that `n>=4` is even.  Reducing the block expansion modulo
`9` gives

\[
S_n(3a)\equiv aS_n(3)\pmod9,                          \tag{7}
\]

because `3|S_{n-1}(3)`.  Since `3|k`, we also have `9|k^2`, so (1) gives

\[
S_n(3a)\equiv(3a+1)^n\equiv1+3an\pmod9.              \tag{8}
\]

The following table records all three possibilities for an even `n`.
Here `q=S_{n-1}(3)/3 modulo 3`; all remaining entries after `a` are also
read modulo `3`.

| `n mod 6` | `S_n(3) mod 9` | `a mod 9` from (7)--(8) | `q` | `A_1` | `A_2` | `binom(n,2)` |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 2 | 5 | 2 | 1 | 0 | 0 |
| 2 | 5 | 8 | 1 | 1 | 2 | 1 |
| 4 | 8 | 2 | 0 | 1 | 1 | 0 |

Also \(S_{n-2}(3)\equiv2\pmod3\).  Both terms on the right of
(5) are divisible by `9`; after division by `9`, their sum modulo `3` is

\[
nA_1q+\binom n2A_2S_{n-2}(3).                         \tag{9}
\]

In the three rows of the table, (9) is respectively

\[
0,\qquad 2+1,\qquad0\pmod3.
\]

It always vanishes.  Thus the right side of (5) is zero modulo `27`,
which proves (2) for `p=3`.  Notice that the information modulo `9`
coming from the original hypothesis is essential to the middle-row
cancellation.

## The prime \(p=2\)

Let `n>=4` be even.  Equation (4) says that `a=k/2` is odd.  Every odd
integer \(j\) satisfies \(j^n\equiv1\pmod8\), while every even integer
satisfies \(j^n\equiv0\pmod8\).  Exactly `a` integers
from `1` through `2a` are odd, so

\[
S_n(2a)\equiv a\pmod8.
\]

Since \(S_n(2)\equiv1\pmod8\), this is precisely (2).

## Small and odd exponents

It remains only to avoid silently applying the preceding expansions outside
their ranges.

If `n=1`, (4) permits no prime divisor other than `2`; squarefreeness gives
`k=1` or `2`.  The first case is vacuous and the second makes (2) an
identity.

If `n>=3` is odd, again only `2` could divide `k`, so `k=1` or `2`.
But for `k=2`, the two sides of (1) are `1` and `3` modulo `4`, a
contradiction.  Hence this case is vacuous.

Finally, if `n=2`, (4) restricts every prime divisor of `k` to `2` or
`3`; squarefreeness gives \(k\in\{1,2,3,6\}\).  Direct substitution into
(1) excludes `3` and `6`.  Thus only `k=1,2` remain, and the only
nonvacuous instance of (2) is again an identity.  This completes the proof.

## Verification scope

The proof is exact and does not depend on computation.  The companion
verifier checks the block identity over a bounded grid, validates every
row of the exceptional-prime table, and directly checks all premise cases
in a bounded range.
