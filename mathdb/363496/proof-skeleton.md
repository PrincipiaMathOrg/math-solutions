# Proof skeleton for MathDB #363496

## Counterexample

In the monoid of pseudoultrametric-preserving maps on
\(\mathbb R^+\), set

\[
e(t)=t,
\quad
u(t)=\mathbf 1_{[2,\infty)}(t),
\quad
v(t)=\mathbf 1_{(0,\infty)}(t),
\quad
z(t)=0,
\]

and take \(\mathbf A=\{e,u,v\}\). The maps \(e,u,v\) are increasing and
zero at zero, hence belong to \(\mathbf P_{\mathbf{PU}}\), and \(e\) is
the monoid identity.

## Composition gate

The exact table is

\[
\begin{array}{c|cccc}
\circ&e&u&v&z\\\hline
e&e&u&v&z\\
u&u&z&z&z\\
v&v&u&v&z\\
z&z&z&z&z.
\end{array}
\]

Therefore \([\mathbf A]=\{e,u,v,z\}\).

## Preservation gate

For

\[
\mathbf X=\{(\mathbb R^+,g\circ d^+):g\in\mathbf A\},
\]

surjectivity of \(d^+\) and \(e\in\mathbf A\) imply

\[
f\in\mathbf P_{\mathbf X}
\iff f\circ g\in\mathbf A\text{ for every }g\in\mathbf A.
\]

The table gives exactly \(\mathbf P_{\mathbf X}=\{e,v\}\).

## Right-ideal gate

Under the intended Lemma 3.10 convention, \(R_{\mathbf A}\) consists of
right ideals of \([\mathbf A]\) contained in \(\mathbf A\). No such ideal
is nonempty: every nonempty right ideal contains \(z\), because
\(r\circ z=z\). Thus
\(\overline R^{\,1}=\{e\}\ne\{e,v\}=\mathbf P_{\mathbf X}\).

If "all right ideals" is read literally without the containment
condition, their union is \([\mathbf A]\), which contains \(z\). But
\(z\notin\mathbf P_{\mathbf X}\), since the zero pseudoultrametric is not
one of the three members of \(\mathbf X\). The equality fails on that
reading as well.
