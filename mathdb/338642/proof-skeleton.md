# Proof skeleton for MathDB #338642

Let \(n=4k+7\), \(m=4k\), and \(r=2k\).  The source's layer
counts are

\[
F=7\binom mr+21\binom m{r+1}
  +7\binom m{r+2}+\binom m{r+3}
\]

at size \(r+3\), together with every odd layer of size at least
\(r+5\).

1. If
   \[
   T=\sum_{j\ge r+5,\ j\text{ odd}}\binom nj,
   \]
   then complement symmetry and
   \(
   \sum_{j=s}^{n}(-1)^j\binom nj=(-1)^s\binom{n-1}{s-1}
   \)
   give
   \[
   T=2^{n-2}-\frac12\binom{n-1}{r+3}.
   \]

2. Put \(B_j=\binom m{r+j}\).  Vandermonde and symmetry give
   \[
   \frac12\binom{m+6}{r+3}
   =10B_0+15B_1+6B_2+B_3.
   \]
   Hence
   \[
   |\mathcal D|-2^{n-2}
   =(7B_0+21B_1+7B_2+B_3)
    -(10B_0+15B_1+6B_2+B_3)
   =-3B_0+6B_1+B_2.
   \]

3. Use
   \[
   B_1=\frac{2k}{2k+1}B_0,
   \qquad
   B_2=\frac{2k(2k-1)}{(2k+1)(2k+2)}B_0
   \]
   to obtain the exact identity
   \[
   |\mathcal D|-2^{n-2}
   =\frac{2(4k+3)(2k-1)}{(2k+1)(2k+2)}
    \binom{4k}{2k}.
   \]

4. The prefactor tends to \(4\), while
   \(\binom{4k}{2k}/2^{4k}=O(k^{-1/2})\).  Since
   \(2^{n-2}=32\,2^{4k}\), the normalized excess tends to zero.

The exact formula also proves \(|\mathcal D|>2^{n-2}\) for every
\(k\ge2\), matching the source's finite computations.

Independent hostile proof audit: passed on 19 August 2026.
