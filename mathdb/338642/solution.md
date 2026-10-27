# Exact excess and the asymptotic size of \(\mathcal D\)

## Statement

For \(k\ge 2\), put

\[
n=4k+7,\qquad m=4k,\qquad r=2k.
\]

Section 4 of Bovdi and Leung's construction gives a maximal commutative
algebraic system \(\mathcal D\subseteq\mathcal P_n(*)\) with

\[
\begin{aligned}
|\mathcal D_{r+3}|
 &=7\binom mr+21\binom m{r+1}
   +7\binom m{r+2}+\binom m{r+3},\\
|\mathcal D_j|&=\binom nj
 \qquad(j\ge r+5\text{ odd}),
\end{aligned}                                                   \tag{1}
\]

and no other layers.  They conjecture that

\[
\lim_{k\to\infty}\frac{|\mathcal D|}{2^{n-2}}=1.
\]

We prove the stronger exact identity

\[
\boxed{
|\mathcal D|-2^{n-2}
=\frac{2(4k+3)(2k-1)}{(2k+1)(2k+2)}
  \binom{4k}{2k}.}                                             \tag{2}
\]

In particular, the excess is positive for every \(k\ge2\), and its
ratio to \(2^{n-2}\) tends to zero.  This proves the conjecture.

## The odd upper tail

Let

\[
T=\sum_{\substack{j\ge r+5\\j\text{ odd}}}\binom nj.
\]

Because \(n=2r+7\) is odd, complement symmetry gives

\[
\sum_{j=r+4}^{n}\binom nj=2^{n-1}.                            \tag{3}
\]

We also use the elementary alternating-tail identity

\[
\sum_{j=s}^{n}(-1)^j\binom nj
=(-1)^s\binom{n-1}{s-1}.                                      \tag{4}
\]

Here \(s=r+4=2k+4\) is even.  Thus the difference
between the even and odd terms in the upper half is

\[
\sum_{j=r+4}^{n}(-1)^j\binom nj=\binom{n-1}{r+3}.
\]

The odd terms in that upper half begin at \(r+5=2k+5\), exactly
the terms defining \(T\).  Combining this observation with (3) gives

\[
T=2^{n-2}-\frac12\binom{n-1}{r+3}.                            \tag{5}
\]

## The exceptional layer

Write

\[
B_j=\binom m{r+j}.
\]

The exceptional layer in (1) is

\[
F=7B_0+21B_1+7B_2+B_3.                                       \tag{6}
\]

Since \(n-1=m+6\), Vandermonde's identity and
\(B_{-j}=B_j\) give

\[
\begin{aligned}
\frac12\binom{n-1}{r+3}
 &=\frac12\binom{m+6}{r+3}\\
 &=\frac12\sum_{i=0}^{6}\binom6i B_{3-i}\\
 &=10B_0+15B_1+6B_2+B_3.                                    \tag{7}
\end{aligned}
\]

Equations (5)--(7) therefore imply

\[
|\mathcal D|-2^{n-2}=F-\frac12\binom{n-1}{r+3}
=-3B_0+6B_1+B_2.                                             \tag{8}
\]

The adjacent-binomial ratios are

\[
\frac{B_1}{B_0}=\frac{2k}{2k+1},\qquad
\frac{B_2}{B_0}=\frac{2k(2k-1)}{(2k+1)(2k+2)}.
\]

Substitution into (8) yields

\[
\begin{aligned}
|\mathcal D|-2^{n-2}
 &=\left(
 -3+\frac{12k}{2k+1}
 +\frac{2k(2k-1)}{(2k+1)(2k+2)}
 \right)\binom{4k}{2k}\\
 &=\frac{2(4k+3)(2k-1)}{(2k+1)(2k+2)}
   \binom{4k}{2k},
\end{aligned}
\]

which is (2).

## Taking the limit

The rational prefactor in (2) tends to \(4\), while the standard
central-binomial estimate gives

\[
\frac{\binom{4k}{2k}}{2^{4k}}=O(k^{-1/2})\longrightarrow0.
\]

Since \(2^{n-2}=2^{4k+5}=32\,2^{4k}\), division of (2) by
\(2^{n-2}\) proves

\[
\frac{|\mathcal D|}{2^{n-2}}
=1+O(k^{-1/2})\longrightarrow1.
\]

This resolves the asymptotic-size conjecture.
