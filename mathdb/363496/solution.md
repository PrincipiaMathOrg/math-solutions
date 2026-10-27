# MathDB #363496: a four-element counterexample

## Result

Conjecture 3.13 of arXiv:2406.07166v2 is false. The counterexample uses
three very simple pseudoultrametric-preserving maps.

For \(t\in\mathbb R^+=[0,\infty)\), define

\[
e(t)=t,
\qquad
u(t)=
\begin{cases}
0,&0\le t<2,\\
1,&t\ge2,
\end{cases}
\qquad
v(t)=
\begin{cases}
0,&t=0,\\
1,&t>0,
\end{cases}
\]

and let \(z(t)=0\) for every \(t\ge0\). Put

\[
\mathbf A=\{e,u,v\}.
\]

Every member of \(\mathbf A\) is increasing and vanishes at zero. By
Proposition 2.2 of the source,
\(\mathbf A\subseteq\mathbf P_{\mathbf{PU}}\). Also \(e\) is the identity
of this composition monoid, so the conjecture's hypothesis
\(1_{\mathbf P_{\mathbf{PU}}}\in\mathbf A\) holds.

We prove that the two sides of the conjectured equality are different.
The same example works under both possible readings of the source's
notation \(R_{\mathbf A}\).

## The generated semigroup

Composition gives

\[
u\circ u=u\circ v=z,
\qquad
v\circ u=u,
\qquad
v\circ v=v.
\tag{1}
\]

Together with the identity and zero rules, these identities show that

\[
[\mathbf A]_{\mathbf P_{\mathbf{PU}}}=\{e,u,v,z\}.
\tag{2}
\]

For reference, the complete composition table, with the left factor
indexing rows, is

\[
\begin{array}{c|cccc}
\circ&e&u&v&z\\ \hline
e&e&u&v&z\\
u&u&z&z&z\\
v&v&u&v&z\\
z&z&z&z&z
\end{array}.
\tag{3}
\]

## A function in \(\mathbf P_{\mathbf X}\)

Let

\[
\mathbf X=
\{(\mathbb R^+,g\circ d^+):g\in\mathbf A\}
\]

as in the conjecture. A function \(f\in\mathbf P_{\mathbf{PU}}\) belongs
to \(\mathbf P_{\mathbf X}\) precisely when applying \(f\) to the distance
of each member of \(\mathbf X\) produces another member of
\(\mathbf X\).

The row for \(v\) in (3) gives

\[
v\circ e=v,
\qquad
v\circ u=u,
\qquad
v\circ v=v.
\]

Thus \(v\) sends each of the three spaces in \(\mathbf X\) back into
\(\mathbf X\), and hence

\[
v\in\mathbf P_{\mathbf X}.
\tag{4}
\]

In fact, \(\mathbf P_{\mathbf X}=\{e,v\}\). The distance \(d^+\) realizes
every value in \(\mathbb R^+\): use a diagonal pair for zero and the pair
\((0,t)\) for \(t>0\). Since \(e\in\mathbf A\), any
\(f\in\mathbf P_{\mathbf X}\) must therefore satisfy
\(f\circ e=f\in\mathbf A\). The three relevant rows of (3) then leave
exactly \(e\) and \(v\). Only the membership (4) is needed for the
intended-reading contradiction below.

## Intended right-ideal reading

Lemma 3.10 of the source defines \(R_{\mathbf A}\) to consist of the right
ideals \(R\) of \([\mathbf A]\) satisfying \(R\subseteq\mathbf A\), and
then sets

\[
\overline R=\bigcup_{R\in R_{\mathbf A}}R.
\]

This containment condition is used again in the proof of Proposition
3.12, so it is the natural intended reading of the abbreviated notation in
Conjecture 3.13.

There is no nonempty right ideal of \([\mathbf A]\) contained in
\(\mathbf A\). Indeed, if such an ideal contains \(e\), \(u\), or \(v\),
respectively, right multiplication within \([\mathbf A]\) gives

\[
e\circ z=z,
\qquad
u\circ u=z,
\qquad
v\circ z=z.
\]

In every case the ideal must contain \(z\notin\mathbf A\), a
contradiction. Consequently

\[
\overline R=\varnothing,
\qquad
\overline R^{\,1_{\mathbf P_{\mathbf{PU}}}}=\{e\}.
\tag{5}
\]

Equations (4) and (5) disprove the conjectured equality.

## Literal all-right-ideals reading

Proposition 3.12 and Conjecture 3.13 abbreviate \(R_{\mathbf A}\) as the
set of "all right ideals" of \([\mathbf A]\), without restating
\(R\subseteq\mathbf A\). If that phrase is instead read literally, the
counterexample still works.

The whole semigroup \([\mathbf A]\) is a right ideal of itself, so the
union of all its right ideals is

\[
\overline R=[\mathbf A]=\{e,u,v,z\}.
\]

On the other hand, \(z\notin\mathbf P_{\mathbf X}\): applying \(z\) to
the member \((\mathbb R^+,e\circ d^+)\) gives the identically zero
pseudoultrametric, whereas none of \(e\circ d^+\), \(u\circ d^+\), or
\(v\circ d^+\) is identically zero. Hence again

\[
\overline R^{\,1_{\mathbf P_{\mathbf{PU}}}}
\ne\mathbf P_{\mathbf X}.
\]

Thus the conjecture is false under either reading of its right-ideal
notation.
