# Balanced complete bipartite graphs uniquely minimize the spread

## Statement and scope

As in the source's global convention, all graphs below are finite, simple,
connected, and undirected.  Connectedness is necessary for the distance
matrix to be defined.  Let

\[
\mathcal Q(G)=\operatorname{Tr}(G)+\mathcal D(G)
\]

be the distance signless Laplacian, and write
\(q_1(G)\geq\cdots\geq q_n(G)\) for its eigenvalues.  Its spread is
\(S_{\mathcal Q}(G)=q_1(G)-q_n(G)\).

We prove that every connected bipartite graph \(G\) of order \(n\) satisfies

\[
S_{\mathcal Q}(G)\geq
S_{\mathcal Q}\!\left(
K_{\lfloor n/2\rfloor,\lceil n/2\rceil}
\right),
\]

with equality exactly for the balanced complete bipartite graph.

The cases \(n\leq3\) are immediate: up to isomorphism there is only one
connected bipartite graph at each such order.  Hence assume \(n\geq4\).

## Three distance sums

Let \(A\cup B\) be the bipartition, with

\[
a=|A|\geq b=|B|,\qquad n=a+b,\qquad d=a-b.
\]

Set

\[
\begin{aligned}
X&=\sum_{\{u,v\}\subseteq A}d_G(u,v),\\
Y&=\sum_{\{u,v\}\subseteq B}d_G(u,v),\\
Z&=\sum_{u\in A,\ v\in B}d_G(u,v).
\end{aligned}
\]

The Wiener index is \(W=X+Y+Z\).  Bipartite parity gives

\[
X\geq a(a-1),\qquad
Y\geq b(b-1),\qquad
Z\geq ab.
\tag{1}
\]

If \(G\) is not complete bipartite, some cross-part pair is a nonedge.
Its odd distance is at least \(3\), so in that case

\[
Z\geq ab+2.
\tag{2}
\]

## Rayleigh bounds from the two parts

The all-ones vector gives

\[
q_1(G)\geq\frac{\mathbf1^{T}\mathcal Q(G)\mathbf1}{n}
=\frac{4W}{n}.
\tag{3}
\]

Suppose first that \(a,b\geq2\).  Consider the \((a-1)\)-dimensional
space of vectors supported on \(A\) whose coordinates sum to zero.  If
\(P_A=I_A-J_A/a\) is its orthogonal projection, the average Rayleigh
quotient of \(\mathcal Q(G)\) on an orthonormal basis of this space is

\[
\frac{\operatorname{tr}(P_A\mathcal Q_{AA})}{a-1}.
\]

Now

\[
\operatorname{tr}\mathcal Q_{AA}=2X+Z,
\qquad
\mathbf1_A^T\mathcal Q_{AA}\mathbf1_A=4X+Z.
\]

Consequently

\[
q_n(G)\leq
r_A:=\frac{2(a-2)X+(a-1)Z}{a(a-1)}.
\tag{4}
\]

The same calculation on \(B\) gives

\[
q_n(G)\leq
r_B:=\frac{2(b-2)Y+(b-1)Z}{b(b-1)}.
\tag{5}
\]

For every \(0\leq\theta\leq1\), equations (3)--(5) imply

\[
S_{\mathcal Q}(G)
\geq \frac{4(X+Y+Z)}n-\theta r_A-(1-\theta)r_B
=c_XX+c_YY+c_ZZ,
\tag{6}
\]

where

\[
\begin{aligned}
c_X&=\frac4n-\theta\frac{2(a-2)}{a(a-1)},\\
c_Y&=\frac4n-(1-\theta)\frac{2(b-2)}{b(b-1)},\\
c_Z&=\frac4n-\frac{\theta}{a}-\frac{1-\theta}{b}.
\end{aligned}
\tag{7}
\]

## Choosing the convex weight

We choose \(\theta\) so that all three coefficients in (7) are
nonnegative.  Define

\[
\theta_Y=
\frac{a(b-2)-b^2}{n(b-2)},
\qquad
\theta_Z=
\frac{a(a-3b)}{nd}.
\]

Only the rows in which their numerators are positive use these
quantities.  Substitution in (6) at the lower endpoints in (1) gives
the following table.

| Part sizes | \(\theta\) | Base lower bound \(B_\theta\) |
|---|---:|---:|
| \(b\geq4,\ a(b-2)\leq b^2\) | \(0\) | \(\frac{3n}{2}+\frac d2+\frac{d^2}{n}\) |
| \(b\geq4,\ a(b-2)>b^2\) | \(\theta_Y\) | \(\frac{3n}{2}+\frac{d(bn-2d)}{2n(b-2)}\) |
| \(b=3,\ a\leq9\) | \(0\) | \(\frac{3n}{2}+\frac d2+\frac{d^2}{n}\) |
| \(b=3,\ a>9\) | \(\theta_Z\) | \(2n\) |
| \(b=2,\ a\leq6\) | \(0\) | \(\frac{3n}{2}+\frac d2+\frac{d^2}{n}\) |
| \(b=2,\ a>6\) | \(\theta_Z\) | \(2n\) |

Here are the coefficient checks.  First, for every listed weight,

\[
c_X\geq
\frac4n-\frac{2(a-2)}{a(a-1)}
=\frac{2\{a(a-b)+2b\}}{na(a-1)}>0.
\tag{8}
\]

For the zero-weight rows, their defining inequalities give
\(c_Y\geq0\) and imply \(c_Z\geq0\).  In the \(\theta_Y\) row, \(c_Y=0\).
If \(a\leq3b\), then already \(c_Z\geq0\) at \(\theta=0\); if
\(a>3b\), then

\[
\theta_Y-\theta_Z
=\frac{b\{ab-4a+b^2\}}{(a-b)(a+b)(b-2)}\geq0
\]

because \(b\geq4\).  Thus \(c_Z\geq0\) there as well.  In each
\(\theta_Z\) row, \(c_Z=0\).  When \(b=3\),
\(\theta_Z\geq(a-9)/(a+3)\), which is the threshold for \(c_Y\geq0\);
when \(b=2\), the term involving \(b-2\) vanishes.  Direct numerator
comparisons also give \(0\leq\theta_Y,\theta_Z\leq1\).

It follows from (1), (6), and (7) that

\[
S_{\mathcal Q}(G)\geq B_\theta.
\tag{9}
\]

## Comparison with the balanced target

A block calculation for \(K_{a,b}\) gives the eigenvalues

\[
\begin{gathered}
n+a-4\quad [a-1\text{ times}],\qquad
n+b-4\quad [b-1\text{ times}],\\
\frac{5n-8\pm\sqrt{9n^2-32ab}}2.
\end{gathered}
\tag{10}
\]

Therefore, for \(n\geq4\), the balanced target is

\[
T_n=
\begin{cases}
\dfrac{3n}{2},&n\ \text{even},\\[4pt]
\dfrac{2n+1+\sqrt{n^2+8}}2,&n\ \text{odd}.
\end{cases}
\tag{11}
\]

For odd \(n\geq5\),

\[
T_n-\frac{3n}{2}
=\frac12+\frac4{\sqrt{n^2+8}+n}
<\frac12+\frac2n.
\tag{12}
\]

Now suppose the parts are unbalanced.  In a zero-weight row, the
surplus over \(3n/2\) is \(d/2+d^2/n\).  This is positive for even
\(n\); for odd \(n\), unbalancedness gives \(d\geq3\), and (12) makes
the inequality strict.  In the \(\theta_Y\) row,

\[
B_{\theta_Y}-\frac{3n}{2}
=\frac{d(bn-2d)}{2n(b-2)}
\geq\frac d2,
\]

because \(d\leq n\).  This again beats (11)--(12), strictly.  Finally,
\(B_{\theta_Z}=2n>T_n\).

It remains to handle balanced parts.  If \(n\) is even, take
\(\theta=0\).  The base bound is exactly \(T_n\), while
\(c_Z=2/n>0\).  By (2), every noncomplete graph has spread strictly
larger than \(T_n\).

If \(n\geq5\) is odd and \(d=1\), again take \(\theta=0\).  Then

\[
B_0=\frac{3n}{2}+\frac12+\frac1n,
\qquad
c_Z=\frac{2(n-2)}{n(n-1)}.
\]

The shortfall of \(B_0\) from \(T_n\) is

\[
\frac4{\sqrt{n^2+8}+n}-\frac1n<\frac1n,
\]

whereas a missing cross edge adds at least

\[
2c_Z=\frac{4(n-2)}{n(n-1)}>\frac1n
\]

to the right side of (6).  Thus every noncomplete graph is again
strictly above \(T_n\).  Formula (10) shows that the complete balanced
graph attains \(T_n\).

Finally, if \(b=1\), connectedness forces \(G=K_{1,n-1}\).  For
\(n\geq4\), (10) gives

\[
S_{\mathcal Q}(K_{1,n-1})
=\sqrt{9n^2-32n+32}.
\]

For even \(n\), its square exceeds \((3n/2)^2\), since the difference
has numerator \(27n^2-128n+128>0\).  For odd \(n\geq5\),
\[
\sqrt{9n^2-32n+32}>2n-1>T_n;
\]
the two squared comparisons reduce respectively to
\(5n^2-28n+31>0\) and \(3n^2-12n+1>0\).

All unbalanced cases are therefore strict, and every balanced
noncomplete case is strict.  Equality occurs exactly for
\[
\boxed{G\cong
K_{\lfloor n/2\rfloor,\lceil n/2\rceil}}.
\]
