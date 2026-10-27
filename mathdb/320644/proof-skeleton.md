# MathDB #320644 -- proof skeleton

## Claim

Let

\[
S_n(m)=\sum_{j=1}^m j^n.
\]

If \(S_n(k)\equiv(k+1)^n\pmod{k^2}\) and `p` is any prime dividing `k`,
then

\[
S_n(k)\equiv \frac{k}{p}S_n(p)\pmod {p^3}.
\]

Thus Conjecture 2 of Sondow--MacMillan is true.

## Gate G0 -- local consequences of the premise

Put `a=k/p`.  Reducing the premise modulo `p` and splitting the sum into
`a` blocks gives

\[
aS_n(p)\equiv1\pmod p.
\]

The standard finite-field power-sum identity says

\[
S_n(p)\equiv
\begin{cases}
-1\pmod p,&p-1\mid n,\\
0\pmod p,&p-1\nmid n.
\end{cases}
\]

Consequently \(p-1\mid n\) and \(a\equiv-1\pmod p\).  In particular,
no square of a prime divides `k`, so `k` is squarefree.

Status: closed directly from the premise; this is the necessary part of the
source's Theorems 1--2.

## Gate G1 -- exact block expansion

For `n>=2`, group the integers from `1` through `ap` as `tp+r`, where
`0<=t<a` and `1<=r<=p`.  With

\[
A_1=\sum_{t=0}^{a-1}t=\frac{a(a-1)}2,
\qquad
A_2=\sum_{t=0}^{a-1}t^2=\frac{a(a-1)(2a-1)}6,
\]

the binomial theorem gives

\[
S_n(ap)-aS_n(p)
\equiv npA_1S_{n-1}(p)
+\binom n2p^2A_2S_{n-2}(p)\pmod {p^3}. \tag{B}
\]

Status: closed; the quantities `A_1,A_2` are integral sums, so there is no
division issue at `p=2` or `p=3`.

## Gate G2 -- primes at least five

Here `p-1|n` forces `n>=4`.  Pairing `r` with `p-r` gives

\[
S_{n-1}(p)\equiv
(n-1)p\sum_{r=1}^{(p-1)/2}r^{n-2}\pmod {p^2}.
\]

The coefficient is `n-1`.  Since `n-2` is even and `p-1` does not divide
`n-2`, the half-sum is zero modulo `p`.  Thus

\[
p^2\mid S_{n-1}(p),\qquad p\mid S_{n-2}(p).
\]

Both correction terms in (B) therefore vanish modulo `p^3`.

Status: closed.

## Gate G3 -- the exceptional prime three

Assume `n>=4` is even.  Since `9|k^2`, applying the block expansion only
modulo `9` to the original premise gives

\[
aS_n(3)\equiv1+3an\pmod9,
\]

because `3|S_{n-1}(3)`.  According as `n` is `0,2,4 modulo 6`, this forces

\[
a\equiv5,8,2\pmod9.
\]

Let `q=S_{n-1}(3)/3 modulo 3`.  In the same three residue classes, the
tuples

\[
\left(q,\ A_1,\ A_2,\ \binom n2\right)\pmod3
\]

are respectively

\[
(2,1,0,0),\qquad(1,1,2,1),\qquad(0,1,1,0).
\]

Also \(S_{n-2}(3)\equiv2\pmod3\).  Dividing the right side of
(B) by `9` and reducing modulo `3` leaves

\[
nA_1q+\binom n2A_2S_{n-2}(3),
\]

which is `0`, `2+1`, and `0`, respectively.  Hence (B) vanishes modulo
`27`.

Status: closed.  The use of the original premise modulo `9` is essential;
the weaker fact \(a\equiv-1\pmod3\) would not suffice.

## Gate G4 -- the exceptional prime two

For even `n>=4`, Gate G0 says `a=k/2` is odd.  Among `1,...,2a` there are
exactly `a` odd integers.  Every odd \(j\) satisfies
\(j^n\equiv1\pmod8\), while every even \(j\) satisfies
\(j^n\equiv0\pmod8\).
Therefore

\[
S_n(2a)\equiv a\equiv aS_n(2)\pmod8.
\]

Status: closed without using (B).

## Gate G5 -- small and odd exponents

- If `n=1`, Gate G0 permits only the prime `2`; squarefreeness gives
  `k=1` or `2`.  The first case is vacuous and the second makes the target
  an identity.
- If `n>=3` is odd, Gate G0 again permits only `k=1` or `2`, but `k=2`
  fails the premise modulo `4`.  Thus the assertion is vacuous.
- If `n=2`, every prime divisor is `2` or `3`, and `k` is squarefree.
  Direct checking of \(k\in\{1,2,3,6\}\) leaves only `k=1,2`; again the only
  nonvacuous target is an identity.

Status: closed.

## Audit state

- Exact statement and the source's surrounding Theorem 2: checked against
  arXiv:1011.2154v1 and the journal version, *Integers* 11 (2011), A34.
- The proof is self-contained apart from the standard finite-field
  power-sum identity.
- Independent hostile audit: complete.  It checked the sign and coefficient
  in the paired expansion, the modulo-9 information in the `p=3` case, and
  every small-exponent case.
- Bounded exact arithmetic verification: passed (4,301 block identities,
  108 exceptional-prime table checks, and all bounded premise instances
  through `k<=500`, `n<=60`).  Verifier SHA-256:
  `895013caaea93e8ab0feff742da38f3759d586486abbbdaf7191430ef7b554d4`.
