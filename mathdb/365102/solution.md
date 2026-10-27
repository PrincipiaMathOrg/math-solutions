# MathDB #365102: the logarithmic-growth barycenter conjecture is false

## Result

The literal Conjecture 1 of arXiv:2410.02715v2 is false.  A smooth
counterexample is

\[
f(x)=2\log\bigl(1+(x-1)^2\bigr).
\tag{1}
\]

This potential satisfies the source's logarithmic confinement assumption.
Its free Gibbs measure exists and has barycenter \(1\), not zero.  Moreover,
for every nonzero linear tilt \(f+\lambda\operatorname{id}\), the
free-energy variational problem is unbounded above.  Consequently there is
no \(\lambda\) whose associated free Gibbs equilibrium has barycenter zero.

## 1. The source hypothesis holds

The one-dimensional existence assumption numbered (14) in the source is

\[
\lim_{|x|\to\infty}\bigl(u(x)-2\log|x|\bigr)=+\infty.
\tag{2}
\]

The function in (1) is real-valued, smooth, and

\[
f(x)-2\log|x|
=2\log\left(\frac{1+(x-1)^2}{|x|}\right)
\longrightarrow +\infty,
\tag{3}
\]

because the fraction in (3) is asymptotic to \(|x|\).  For an elementary
bound, if \(|x|\geq4\), then

\[
1+(x-1)^2\geq \frac{|x|^2}{4},
\]

so the expression in (3) is at least \(2\log(|x|/4)\).

The existence-and-uniqueness theorem quoted immediately before (2) in the
source therefore supplies a unique compactly supported maximizer
\(\nu_f\) of

\[
\chi_f(\mu)=\chi(\mu)-\int f\,d\mu.
\tag{4}
\]

Here the additive normalization in \(\chi\) will play no role.

## 2. The un-tilted equilibrium has barycenter one

Let \(r(x)=2-x\), reflection about \(1\).  Equation (1) gives

\[
f(r(x))=f(x).
\tag{5}
\]

For every probability measure \(\mu\), reflection preserves the logarithmic
interaction because

\[
|r(s)-r(t)|=|s-t|.
\]

Thus \(\chi(r_\#\mu)=\chi(\mu)\), and (5) also gives

\[
\int f\,d(r_\#\mu)=\int f\,d\mu.
\]

The functional (4) is invariant under \(r_\#\).  By uniqueness of its
maximizer,

\[
r_\#\nu_f=\nu_f.
\tag{6}
\]

The measure is compactly supported, so its barycenter \(m\) is finite.
Using (6),

\[
m=\int x\,d\nu_f(x)
 =\int r(x)\,d\nu_f(x)
 =2-m.
\]

Hence

\[
\int x\,d\nu_f(x)=1.
\tag{7}
\]

In particular, \(\lambda=0\) does not center the equilibrium measure.

## 3. Every nonzero tilt destroys finite-barycenter equilibrium

Fix \(\lambda\ne0\), put \(s=\operatorname{sgn}(\lambda)\), and let
\(\mu_0\) be normalized Lebesgue measure on \([-1,1]\).  Its logarithmic
energy is finite; in fact

\[
\iint\log|x-y|\,d\mu_0(x)d\mu_0(y)=\log2-\frac32.
\]

For \(t>0\), translate it by \(-st\):

\[
\mu_t=(x\mapsto x-st)_\#\mu_0.
\]

Free entropy is translation invariant, so
\(\chi(\mu_t)=\chi(\mu_0)\).  Also, for \(y\in[-1,1]\),

\[
|y-st-1|\leq t+2
\]

and therefore

\[
f(y-st)
\leq2\log\bigl(1+(t+2)^2\bigr)
\leq4\log(t+3).
\tag{8}
\]

Since \(\mu_0\) is centered, the tilted functional satisfies

\[
\begin{aligned}
\chi_{f+\lambda\operatorname{id}}(\mu_t)
&=\chi(\mu_0)-\int_{-1}^{1}f(y-st)\,d\mu_0(y)
  -\lambda(-st)\\
&\geq \chi(\mu_0)+|\lambda|t-4\log(t+3).
\end{aligned}
\tag{9}
\]

The right side tends to \(+\infty\).  Thus

\[
\sup_\mu\chi_{f+\lambda\operatorname{id}}(\mu)=+\infty
\qquad(\lambda\ne0).
\tag{10}
\]

Every probability measure with a barycenter has finite first absolute
moment.  For such a measure the positive part of the logarithmic interaction
is finite, since

\[
\log^+|x-y|\leq \log(1+|x|+|y|)\leq |x|+|y|,
\]

and the potential term is finite.  Its value in (10) is therefore finite or
\(-\infty\), never \(+\infty\), so it cannot maximize a functional whose
supremum is \(+\infty\).  In the standard equilibrium convention, this
unbounded variational problem has no free Gibbs measure at all.  Under any
extended-value convention, it has no free Gibbs maximizer with a finite
barycenter, and in particular none with barycenter zero.

Combining (7) and (10), no \(\lambda\in\mathbb R\) has the property asserted
in Conjecture 1.

## Scope of the refutation

This counterexample targets the source's literal quantifier over every
continuous \(f\) satisfying only (2).  It grows like \(4\log|x|\), so a
linear tilt is nonconfining in one direction.

The surrounding proposed application considers functions \(f,g\) satisfying
\(f(x)+g(y)\geq xy\) for every \(x,y\).  That stronger premise forces \(f\)
and \(g\) to grow faster than every linear function.  The example above
therefore does **not** refute a repaired conjecture restricted to
superlinear potentials, or more generally to potentials for which every
linear tilt remains confining.

## Exact verification

The file *verify_counterexample.py* checks the reflection and confinement
algebra on exact rational grids, the uniform escape bound for both tails, and
an exact diverging family behind (9).  The all-real-variable implications
and the variational argument are proved above; the program is a regression
check for their algebraic inequalities.
