# Proof skeleton for MathDB #338641

Put \(n=4k+7\), \(m=4k\), \(r=2k\), and
\(B_t=\binom m{r+t}\).  Then \(B_{-t}=B_t\).

1. The source's exceptional layers have sizes
   \[
   B_1,
   \quad 7B_0+21B_1+7B_2+B_3,
   \quad B_5+7B_4+21B_3+35B_2+35B_1+21B_0,
   \]
   at \(r+1,r+3,r+5\), respectively.  Every odd layer at least
   \(r+7\) is full.

2. Complement symmetry and the alternating-binomial tail identity give
   \[
   \sum_{\substack{j\ge r+7\\j\text{ odd}}}\binom nj
   =2^{n-2}-\frac12\binom{n-1}{r+3}-\binom n{r+5}.
   \]

3. Two Vandermonde expansions, collected with \(B_{-t}=B_t\), are
   \[
   \frac12\binom{n-1}{r+3}=10B_0+15B_1+6B_2+B_3
   \]
   and
   \[
   \binom n{r+5}
   =B_5+7B_4+21B_3+36B_2+42B_1+21B_0.
   \]

4. Substitution cancels every term except \(-3B_0\), proving
   \[
   |\operatorname{Cone}|=2^{n-2}-3\binom{4k}{2k}.
   \]

5. Divide by \(2^{n-2}=32\,2^{4k}\).  The product formula
   \[
   \frac{\binom{4k}{2k}}{2^{4k}}
   =\prod_{j=1}^{2k}\left(1-\frac1{2j}\right)
   \]
   tends to zero because its logarithm is at most
   \(-\tfrac12\sum_{j=1}^{2k}1/j\).  The desired ratio therefore tends
   to one.

Separate hostile dependency audit: passed on 19 August 2026.  The rerun
checked the layer endpoints and parities, both uncollected Vandermonde sums,
the symmetry indices \(B_{-1},B_{-2}\), the source's independent
\(|\mathcal D|-|\operatorname{Cone}|\) formula, and the \(k=2\) boundary.
