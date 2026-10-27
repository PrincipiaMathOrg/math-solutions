# A weighted-gauge counterexample to the residue-class decomposition

## Statement

Let \(m\) be normalized Lebesgue measure on the unit circle
\(\mathbb T\). For a continuous, normalized,
\(\lVert\cdot\rVert _1\)-dominating gauge norm \(\alpha\), let
\(H^\alpha\) be the \(\alpha\)-closure of \(H^\infty\), and let

\[
M_\alpha(z^n)=[H^\infty(z^n)]_\alpha.
\]

Conjecture 4.4 in the source asks whether

\[
H^\alpha=M_\alpha(z^n)\oplus zM_\alpha(z^n)\oplus\cdots
\oplus z^{n-1}M_\alpha(z^n)
\tag{1}
\]

for every such norm. We disprove (1) already for \(n=2\).

## The gauge norm

Put

\[
a=b=\frac23,
\qquad
c_b=\left(\int_{\mathbb T}|1-\zeta|^{-b}\,dm(\zeta)\right)^{-1},
\qquad
w(\zeta)=c_b|1-\zeta|^{-b}.
\]

The integral defining \(c_b\) is finite because \(b<1\), and
\(\int_{\mathbb T}w\,dm=1\). For \(h\in L^\infty(\mathbb T)\), define

\[
\alpha(h)=\max\left\{
   \int_{\mathbb T}|h|\,dm,
   \int_{\mathbb T}|h|w\,dm
\right\}.
\tag{2}
\]

This is the maximum of two norms. Moreover,

* \(\alpha(1)=1\);
* \(\alpha(h)=\alpha(|h|)\);
* \(\alpha(h)\geq\lVert h\rVert _1\); and
* if \(m(A)\to0\), then
  \(\alpha(\mathbf1_A)=\max\{m(A),\int_Aw\,dm\}\to0\), by absolute
  continuity of the integral of \(w\in L^1\).

Thus (2) is a continuous
\(\lVert\cdot\rVert _1\)-dominating normalized gauge norm. Its extension
to measurable functions is the same maximum of the two displayed
integrals. The norm is deliberately not rotationally symmetric: the
weight has its singularity at \(1\).

## A function in \(H^\alpha\)

On the disk, take the analytic branch

\[
f(z)=(1+z)^{-a}.
\tag{3}
\]

Its boundary modulus has an integrable singularity of order \(a<1\) at
\(-1\). The weight \(w\) is bounded near \(-1\), while \(f\) is bounded
near the only singularity \(1\) of \(w\). Consequently

\[
\int_{\mathbb T}|f|\,dm<\infty,
\qquad
\int_{\mathbb T}|f|w\,dm<\infty.
\tag{4}
\]

For completeness, membership in \(H^\alpha\) follows directly from
bounded analytic approximants. Let \(f_r(z)=(1+rz)^{-a}\), \(0<r<1\).
For \(r\geq1/2\) and \(\zeta=e^{i\theta}\),

\[
|1+r e^{i\theta}|^2
=(1-r)^2+4r\cos^2(\theta/2),
\]

so both the unweighted and weighted differences \(f_r-f\) are dominated
by integrable multiples of

\[
|\cos(\theta/2)|^{-a}
\quad\text{and}\quad
|\cos(\theta/2)|^{-a}|\sin(\theta/2)|^{-b},
\]

respectively. These are integrable because \(a,b<1\). Dominated
convergence therefore gives \(\alpha(f_r-f)\to0\). Since every
\(f_r\in H^\infty\), equation (3) indeed defines an element of
\(H^\alpha\).

## Its even part is not in \(H^\alpha\)

The even Fourier-residue component of \(f\) is

\[
E_0f(z)=\frac{f(z)+f(-z)}2
=\frac12\left((1+z)^{-a}+(1-z)^{-a}\right).
\tag{5}
\]

As \(\zeta\to1\), the first summand in (5) stays bounded and the second
has modulus \(|1-\zeta|^{-a}\to\infty\). Hence, on a sufficiently small
punctured arc about \(1\),

\[
|E_0f(\zeta)|\geq\frac14|1-\zeta|^{-a}.
\]

It follows that

\[
\int_{\mathbb T}|E_0f|w\,dm
\geq C\int_0^\delta \theta^{-(a+b)}\,d\theta
=\infty,
\tag{6}
\]

because \(a+b=4/3>1\). Thus \(E_0f\notin L^\alpha\), and in particular
\(E_0f\notin H^\alpha\).

## Contradiction to the proposed decomposition

Every \(g\in M_\alpha(z^2)\) is even. Indeed, choose
\(g_j\in H^\infty(z^2)\) with \(\alpha(g_j-g)\to0\). Since
\(\alpha\geq\lVert\cdot\rVert _1\), this convergence also holds in
\(L^1\). Every odd Fourier coefficient of every \(g_j\) is zero, and
Fourier coefficients are continuous on \(L^1\); hence every odd
coefficient of \(g\) is zero. Therefore \(g(-z)=g(z)\) in the disk.

If (1) held for \(n=2\), the function (3) would have a representation

\[
f=g_0+zg_1,
\qquad g_0,g_1\in M_\alpha(z^2).
\]

Both \(g_0\) and \(g_1\) are even, so replacing \(z\) by \(-z\) and
adding gives

\[
g_0(z)=\frac{f(z)+f(-z)}2=E_0f(z).
\]

But \(g_0\in M_\alpha(z^2)\subset H^\alpha\subset L^\alpha\), whereas
(6) shows that \(E_0f\notin L^\alpha\). This contradiction disproves
the conjecture.
