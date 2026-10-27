# MathDB #351036 -- correction, proof, and divisor formula

## Corrected statement

For positive integers `n,a,d`, define the geometric sum

\[
M_i(a,d)=\sum_{r=0}^{d-1}a^{ri}.
\]

The source context requires `k` to divide `phi(n)`, a condition omitted from
the MathDB statement.  If `zeta_k` is a primitive `k`-th root of unity, put

\[
E_k(n,a,d)=\frac1{\varphi(n)}
 \sum_{i=1}^{\varphi(n)}\gcd(n,M_i(a,d))\zeta_k^i.
\]

Then

\[
\boxed{E_k(n,a,d)\in\mathbb Z\qquad(k\mid\varphi(n)).}
\tag{1}
\]

The geometric-sum definition also covers `a=1` without a `0/0` quotient.

## The literal MathDB statement is false

The record imposes no condition on `k`.  Take

\[
(n,a,d,k)=(2,2,1,3).
\]

Here `phi(n)=1` and `M_1=1`, so the displayed sum is `zeta_3`, not a rational
integer.  The intended restriction `k | phi(n)` is forced by the source's
preceding zeta-function factorization.

## Source lemma

Theorem 3.1 of the source gives the following special case.  Let `q` be a
prime power, let `D` be positive, and suppose `k | phi(n)`.  Then

\[
\frac1{\varphi(n)}\sum_{i=1}^{\varphi(n)}
 \gcd\!\left(n,\frac{q^{Di}-1}{q^i-1}\right)\zeta_k^i
 \in\mathbb Z.
\tag{2}
\]

Indeed, take the source's extension vector `(d_1,d_2)=(D,1)`, whose gcd is
`c=1`.  The quantity in (2) is the integer exponent of the corresponding
cyclotomic factor in the rational partial zeta function.

## Proof when `gcd(a,n)=1`

If `n=1`, (1) is immediate.  Otherwise Dirichlet's theorem supplies a prime

\[
q\equiv a\pmod n.
\]

For every `i`,

\[
M_i(q,d)\equiv M_i(a,d)\pmod n,
\]

and consequently

\[
\gcd(n,M_i(q,d))=\gcd(n,M_i(a,d)).
\tag{3}
\]

Substitute (3) into the source lemma with `D=d`.  This proves (1) whenever
`a` is a unit modulo `n`.

## Reduction of the general case

Factor `n=n_0n_1`, where

\[
n_0=\prod_{\substack{p^e\parallel n\\p\nmid a}}p^e,
\qquad
n_1=\prod_{\substack{p^e\parallel n\\p\mid a}}p^e.
\]

If `p | a`, then `M_i(a,d) = 1 (mod p)`.  Hence no prime factor of `n_1`
divides `M_i`, and

\[
\gcd(n,M_i)=\gcd(n_0,M_i).                       \tag{4}
\]

Set

\[
h_0=\varphi(n_0),\qquad L=\varphi(n_1),\qquad
h=\varphi(n)=Lh_0.
\]

Because `gcd(a,n_0)=1`, the sequence

\[
f(i)=\gcd(n_0,M_i(a,d))
\]

has period `h_0`: Euler's theorem makes every summand in `M_i` periodic
modulo `n_0`.  Split the sum into `i=r+t h_0`.  Since `k | h`,

\[
\begin{aligned}
E_k(n,a,d)
&=\frac1h\sum_{r=1}^{h_0} f(r)\zeta_k^r
       \sum_{t=0}^{L-1}\zeta_k^{t h_0}\\
&=
\begin{cases}
0,& k\nmid h_0,\\[2mm]
\displaystyle\frac1{h_0}\sum_{r=1}^{h_0}f(r)\zeta_k^r,
   & k\mid h_0.
\end{cases}                                      \tag{5}
\end{aligned}
\]

For the first line of (5), the finite geometric sum vanishes unless
`zeta_k^{h_0}=1`; this condition is exactly `k | h_0`.  In the second case,
the remaining expression is `E_k(n_0,a,d)`, which is integral by the coprime
case.  This completes the proof of (1).

## A finite Ramanujan-divisor formula

Formula (5) already says that `E_k=0` if `k` does not divide `h_0`.  Suppose
now that `k | h_0`, and for `g | h_0` define

\[
F(g)=\gcd\!\left(n_0,\sum_{r=0}^{d-1}a^{rg}\right).
\]

The preceding integrality proof shows that the value is fixed by every Galois
automorphism, so it is independent of the chosen primitive `k`-th root.  For
the Fourier calculation, take `zeta_k=exp(2 pi i/k)`.

Then

\[
\boxed{
E_k(n,a,d)=\frac1{h_0}
 \sum_{g\mid h_0}F(g)
 c_{h_0/g}\!\left(\frac{h_0}{k}\right),
}
\tag{6}
\]

where the Ramanujan sum is

\[
c_m(t)=\sum_{s\mid(m,t)}s\,\mu(m/s).
\]

To prove (6), first observe that `f(i)` depends only on `gcd(i,h_0)`.  It is
enough to show `f(ui)=f(i)` for every unit class `u` modulo `h_0`.  Choose a
positive representative `U` of this class that is also coprime to `n_0`.
Such a representative always exists: for a prime `p | n_0` that also divides
`h_0`, every representative is already nonzero modulo `p`; for each remaining
prime impose `U=1 (mod p)` alongside `U=u (mod h_0)` and use the Chinese
remainder theorem.  Periodicity gives `f(ui)=f(Ui)`.

Now fix `p^e || n_0` and put `x=a^i`.  The integer `U` is coprime to `p`, and
it is coprime to `p-1` because `p-1 | phi(p^e) | h_0`.

- If `x=1` as an integer, the geometric sum is simply `d`, so there is nothing
  to prove.
- For odd `p`, if `x` is not `1 (mod p)`, exponentiation by `U` preserves the
  order of `x` modulo `p`; when that order divides `d`, LTE applied to
  `(x^d)^U-1` preserves the valuation because `p` does not divide `U`.
  If `x=1 (mod p)`, LTE gives
  `v_p(1+x+...+x^(d-1))=v_p(d)`, again unchanged by `x -> x^U`.
- For `p=2`, `U` is odd.  If `d` is odd the geometric sum is odd.  If `d` is
  even, the 2-adic LTE formula gives valuation
  `v_2(x+1)+v_2(d)-1`, and `v_2(x^U+1)=v_2(x+1)`.

Thus every truncated `p`-adic valuation entering the gcd with `n_0` is
unchanged.  Units modulo `h_0` act transitively on residue classes having the
same gcd with `h_0`, so

\[
f(i)=F(\gcd(i,h_0)).                              \tag{7}
\]

Group the Fourier sum in (5) by `g=gcd(i,h_0)`.  The inner sum over the units
modulo `h_0/g` is precisely
`c_(h_0/g)(h_0/k)`, proving (6).

The exact checker `verify_integrality.py` verifies the literal counterexample,
the prime-transfer identity, the nonunit reduction, the even-function property,
and formula (6) without floating-point arithmetic.
