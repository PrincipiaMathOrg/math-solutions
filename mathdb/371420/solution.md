# MathDB #371420: an aperiodic torus translation

## Result

The conjecture recorded by MathDB and stated literally as Conjecture 2 of
the cited source is false.  The missing hypothesis is positive topological
entropy.

Indeed, an irrational translation of the two-dimensional torus is a
smooth surface diffeomorphism with zero topological entropy and no periodic
points.  Consequently, every numerator in the proposed quotient is zero.

## Counterexample

Let

\[
M=\mathbb T^2=\mathbb R^2/\mathbb Z^2
\]

with its flat metric, and fix an irrational number \(\alpha\), for example
\(\alpha=\sqrt2\).  Define

\[
f([x,y])=[x+\alpha,y].
\tag{1}
\]

This is a \(C^\infty\) diffeomorphism of the compact surface \(\mathbb T^2\).
It is in fact an isometry and preserves area.

For every positive integer \(n\),

\[
f^n([x,y])=[x+n\alpha,y].
\]

If \([x,y]\) were fixed by \(f^n\), then \(n\alpha\in\mathbb Z\).  This is
impossible because \(\alpha\) is irrational.  Hence

\[
P_n(f)=\varnothing
\qquad(n\geq1).
\tag{2}
\]

## Entropy

For the flat quotient metric \(d\), translation invariance gives

\[
d(f^kz,f^kw)=d(z,w)
\qquad(k\geq0).
\]

Thus every Bowen metric

\[
d_n(z,w)=\max_{0\leq k<n}d(f^kz,f^kw)
\]

is just \(d\).  For each \(\varepsilon>0\), the maximum size of an
\((n,\varepsilon)\)-separated set is therefore independent of \(n\), and it
is finite by compactness of \(\mathbb T^2\).  The separated-set definition of
topological entropy now gives

\[
h_{\operatorname{top}}(f)=0.
\tag{3}
\]

Combining (2) and (3),

\[
\limsup_{n\to\infty}
\frac{\#P_n(f)}{e^{n h_{\operatorname{top}}(f)}}
=\limsup_{n\to\infty}\frac0{1}=0,
\]

contrary to the asserted strict positivity.

## Scope

The usual positive-entropy formulation is materially different.  Sarig's
affirmative \(C^\infty\) theorem explicitly assumes
\(h_{\operatorname{top}}(f)>0\), and the paragraph preceding Conjecture 2 in
the cited source discusses Katok's lower bound under the same hypothesis.
The counterexample above only refutes the unqualified statement that the
displayed inequality holds for *any* surface diffeomorphism.  It does not
address the remaining finite-smoothness problem for positive-entropy maps.
