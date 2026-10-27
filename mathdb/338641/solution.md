# Exact deficit and the asymptotic size of the cone

## Statement

For \(k\ge 2\), put

\[
n=4k+7,\qquad m=4k,\qquad r=2k.
\]

Section 4 of Bovdi and Leung's construction gives a maximal commutative
algebraic system

\[
\operatorname{Cone}
=\operatorname{Cone}(\operatorname{Cone}_{2k+1}
  \cup\operatorname{Cone}_{2k+3})
\subseteq\mathcal P_n(*) .
\]

The authors conjecture that

\[
\lim_{k\to\infty}
\frac{|\operatorname{Cone}|}{2^{n-2}}=1.
\]

We prove the stronger exact identity

\[
\boxed{
|\operatorname{Cone}|=2^{n-2}-3\binom{4k}{2k}.}
\tag{1}
\]

Thus the source's observed strict inequality
\(|\operatorname{Cone}|<2^{n-2}\) holds for every \(k\ge2\), and the
normalized deficit tends to zero.

## The four source layers

For an integer \(t\), write

\[
B_t=\binom{m}{r+t}.
\]

Since \(m=2r\), binomial symmetry gives \(B_{-t}=B_t\).  The source's
layer description gives

\[
\begin{aligned}
L_{r+1}&=B_1,\\
L_{r+3}&=7B_0+21B_1+7B_2+B_3,\\
L_{r+5}&=B_5+7B_4+21B_3+35B_2+35B_1+21B_0,
\end{aligned}
\tag{2}
\]

and every odd layer of size at least \(r+7\).  Hence, if

\[
T_7=\sum_{\substack{j\ge r+7\\j\text{ odd}}}\binom nj,
\]

then

\[
|\operatorname{Cone}|=L_{r+1}+L_{r+3}+L_{r+5}+T_7.
\tag{3}
\]

## The odd upper tail

Let

\[
T_5=\sum_{\substack{j\ge r+5\\j\text{ odd}}}\binom nj.
\]

The integer \(n=2r+7\) is odd.  Complementation therefore shows that
the full upper half, starting at \(r+4\), has size \(2^{n-1}\).  The
alternating-tail identity

\[
\sum_{j=s}^{n}(-1)^j\binom nj
=(-1)^s\binom{n-1}{s-1}
\tag{4}
\]

with the even integer \(s=r+4\) says that, within this upper half, the
number of even sets minus the number of odd sets is
\(\binom{n-1}{r+3}\).  Consequently

\[
T_5=2^{n-2}-\frac12\binom{n-1}{r+3},
\qquad
T_7=T_5-\binom n{r+5}.
\tag{5}
\]

## Two Vandermonde collections

First, \(n-1=m+6\), so Vandermonde's identity and
\(B_{-t}=B_t\) give

\[
\frac12\binom{n-1}{r+3}
=10B_0+15B_1+6B_2+B_3.
\tag{6}
\]

Second, \(n=m+7\), and another Vandermonde expansion gives

\[
\begin{aligned}
\binom n{r+5}
&=\sum_{i=0}^{7}\binom7i B_{5-i}\\
&=B_5+7B_4+21B_3+36B_2+42B_1+21B_0.
\end{aligned}
\tag{7}
\]

Comparing (7) with the third line of (2),

\[
L_{r+5}-\binom n{r+5}=-B_2-7B_1.
\tag{8}
\]

Now substitute (2), (5), (6), and (8) into (3).  The difference from
\(2^{n-2}\) is

\[
\begin{aligned}
|\operatorname{Cone}|-2^{n-2}
={}&B_1+(7B_0+21B_1+7B_2+B_3)\\
&{}-B_2-7B_1-(10B_0+15B_1+6B_2+B_3)\\
=&-3B_0.
\end{aligned}
\]

This is exactly (1).

## Taking the limit

Because \(n-2=4k+5\), equation (1) gives

\[
\frac{|\operatorname{Cone}|}{2^{n-2}}
=1-\frac3{32}\frac{\binom{4k}{2k}}{2^{4k}}.
\tag{9}
\]

The remaining factor tends to zero elementarily.  Indeed,

\[
\frac{\binom{4k}{2k}}{2^{4k}}
=\prod_{j=1}^{2k}\left(1-\frac1{2j}\right)
\leq \exp\!\left(-\frac12\sum_{j=1}^{2k}\frac1j\right)
\longrightarrow0.
\]

Taking the limit in (9) proves the conjecture.
