# MathDB #359102: the uniform-separation conjecture is false

## Result

There is a bounded, uniformly separated subset of a separable
infinite-dimensional complex Hilbert space that is not
\(\ell^1\)-bounded.  In fact, the example below is not even
\(\ell^1\)-**frame**-bounded, which is the formally stronger failure.

This refutes Conjecture 4.10 of Heil--Yu, and hence the assertion recorded as
MathDB #359102.

## 1. A coding lemma

For \(r\geq3\), put \(d_r=2^r\), index the coordinates of
\(\mathbb F_2^{d_r}\) by the points of \(\mathbb F_2^r\), and let

\[
C_r=\operatorname{RM}(2,r)
\]

be the binary Reed--Muller code obtained by evaluating all multilinear
polynomials of degree at most two on \(\mathbb F_2^r\).  We use two elementary
properties of these codes:

\[
d(C_r)=2^{r-2}=\frac{d_r}{4},
\qquad
C_r^\perp=\operatorname{RM}(r-3,r),
\qquad
d(C_r^\perp)=8.                                      \tag{1}
\]

Here is a quick self-contained reminder.  More generally,
\(\operatorname{RM}(s,r)\) has minimum distance \(2^{r-s}\).  Write a
nonzero Boolean polynomial as

\[
f(y,t)=g(y)+t h(y).
\]

If \(h=0\), its two evaluation halves agree and induction doubles the lower
bound for \(g\).  If \(h\ne0\), the two halves are \(g\) and \(g+h\); on
every point where \(h=1\), exactly one of them is nonzero.  Induction applied
to \(h\), whose degree is at most \(s-1\), again gives weight at least
\(2^{r-s}\).  The monomial \(x_1\cdots x_s\) attains the bound.

For duality, a monomial of degree at most \(s\) and one of degree at most
\(r-s-1\) have a product missing at least one variable.  The sum of that
product over \(\mathbb F_2^r\) is therefore even.  Thus the two Reed--Muller
codes are orthogonal.  Their dimensions,

\[
\sum_{j=0}^{s}\binom rj
\quad\hbox{and}\quad
\sum_{j=0}^{r-s-1}\binom rj,
\]

sum to \(2^r\), so they are exact duals.  Taking \(s=2\) proves (1).

Choose a uniformly random codeword \(c\in C_r\) and set
\(\varepsilon_z=(-1)^{c_z}\).  The signs \((\varepsilon_z)\) are four-wise
independent.  Indeed, failure of uniformity on some set of at most four
coordinates would give a nonzero linear constraint supported on those
coordinates, hence a nonzero word of \(C_r^\perp\) of weight at most four,
contrary to (1).

Consequently, for arbitrary complex numbers \((a_z)\), if

\[
S=\sum_z\varepsilon_z a_z,
\qquad
\sigma^2=\sum_z|a_z|^2,
\]

then the usual second and fourth Rademacher moments remain valid:

\[
\mathbb E|S|^2=\sigma^2,
\qquad
\mathbb E|S|^4\leq3\sigma^4.                          \tag{2}
\]

Applying Paley--Zygmund to \(|S|^2\) gives

\[
\Pr\left\{|S|\geq\frac{\sigma}{\sqrt2}\right\}
 \geq\frac1{12},
\qquad
\mathbb E|S|\geq\frac{\sigma}{12\sqrt2}.             \tag{3}
\]

## 2. The separated set

Let

\[
H=\bigoplus_{r=3}^{\infty}H_r,
\qquad H_r\cong\mathbb C^{d_r},
\]

and fix an orthonormal basis
\(\{u_{r,z}:z\in\mathbb F_2^r\}\) of each block.  For \(c\in C_r\), define

\[
x_{r,c}=\frac1{\sqrt{d_r}}
        \sum_{z\in\mathbb F_2^r}(-1)^{c_z}u_{r,z},
\qquad
M=\bigcup_{r\geq3}\{x_{r,c}:c\in C_r\}.              \tag{4}
\]

Every member of \(M\) has norm one, so \(M\) is bounded.  If \(c\ne c'\)
belong to the same code, then (1) gives

\[
\|x_{r,c}-x_{r,c'}\|^2
 =\frac{4\operatorname{wt}(c-c')}{d_r}\geq1.          \tag{5}
\]

Vectors from distinct blocks are orthogonal unit vectors and hence are at
distance \(\sqrt2\).  Thus

\[
\inf_{x\ne y\in M}\|x-y\|\geq1.                      \tag{6}
\]

The set is a countable union of finite sets, as required in a separable
Hilbert space.

## 3. No frame can give a uniform \(\ell^1\) bound

Let \(\mathcal F=\{e_n\}_{n\geq1}\) be an arbitrary frame for \(H\), with
frame bounds \(0<A\leq B<\infty\):

\[
A\|x\|^2\leq\sum_n|\langle x,e_n\rangle|^2
 \leq B\|x\|^2.                                      \tag{7}
\]

Fix a block \(H_r\), write \(d=d_r\), and put

\[
\sigma_n=
\left(\sum_{z\in\mathbb F_2^r}
 |\langle u_{r,z},e_n\rangle|^2\right)^{1/2}
=\|P_{H_r}e_n\|.                                      \tag{8}
\]

Summing (7) over the \(d\) orthonormal vectors in the block yields

\[
\sum_n\sigma_n^2\geq Ad.                              \tag{9}
\]

Also \(\|e_n\|\leq\sqrt B\) for every \(n\): apply the upper frame bound to
\(e_n\) and retain the \(n\)-th summand.  Hence

\[
\sup_n\sigma_n\leq\sqrt B,
\qquad
\sum_n\sigma_n
 \geq\frac{\sum_n\sigma_n^2}{\sqrt B}
 \geq\frac{Ad}{\sqrt B}.                              \tag{10}
\]

Choose \(c\) uniformly in \(C_r\).  For each \(n\), apply (3) with
\(a_z=\langle u_{r,z},e_n\rangle\).  Tonelli's theorem and (10) give

\[
\begin{aligned}
\mathbb E_c\sum_n|\langle x_{r,c},e_n\rangle|
&=\frac1{\sqrt d}\sum_n
  \mathbb E_c\left|\sum_z(-1)^{c_z}
             \langle u_{r,z},e_n\rangle\right|\\
&\geq\frac1{12\sqrt{2d}}\sum_n\sigma_n\\
&\geq\frac{A}{12\sqrt{2B}}\sqrt d.                  \tag{11}
\end{aligned}
\]

Because \(C_r\) is finite, at least one \(c\in C_r\) attains the lower bound
in (11).  Since \(d_r=2^r\to\infty\),

\[
\sup_{x\in M}\sum_n|\langle x,e_n\rangle|=\infty.    \tag{12}
\]

The frame \(\mathcal F\) was arbitrary.  Therefore \(M\) is not
\(\ell^1\)-frame-bounded.  Every Riesz basis is a frame, so \(M\) is not
\(\ell^1\)-bounded either, completing the refutation.

## Exact verification

`verify_reed_muller.py` independently constructs the relevant Reed--Muller
codes for \(r=3,4,5\), checks their dimensions, orthogonality, primal and
dual minimum distances, every coordinate projection of size at most four,
and exact complex second/fourth moments.  These finite checks stress the
coding lemma; the all-\(r\) statements used above are proved by the induction
and dimension argument in Section 1.
