# Proof skeleton for MathDB #361368

## Claim

The literal arbitrary-set cone-and-cylinder conjecture is false.  For every
\(d\ge1\), the compact choice

\[
A=\overline B(0,1)\subset\mathbb R^d
\]

satisfies

\[
\dim_F(A)=d,
\qquad
\dim_F(C_A)=\dim_F(D_A)=d+1.
\]

## Interior lemma

If \(E\subset\mathbb R^N\) is Borel with nonempty interior, choose a
nonnegative \(C_c^\infty\) function of integral one supported in an interior
ball.  The corresponding probability measure is supported on \(E\), and
its Fourier transform is Schwartz.  It therefore satisfies the Fourier
decay condition at the maximal admissible exponent \(N\).  Thus

\[
\dim_F(E)=N.
\]

Applying this to the closed unit ball gives \(\dim_F(A)=d\).

## Cylinder gate

\[
D_A=A\times\mathbb R,
\qquad
\operatorname{Int}(D_A)=B(0,1)\times\mathbb R\ne\varnothing.
\]

The interior lemma in \(\mathbb R^{d+1}\) gives
\(\dim_F(D_A)=d+1\).

## Cone gate

Writing ambient points as \((y,h)\),

\[
C_A=\{(hx,h):\lVert x\rVert\le1,\ h\in\mathbb R\}
=\{(y,h):\lVert y\rVert\le|h|\}.
\]

Hence

\[
\operatorname{Int}(C_A)=\{(y,h):\lVert y\rVert<|h|\}\ne\varnothing,
\]

and the same lemma yields \(\dim_F(C_A)=d+1\).

## Conclusion and limitation

Both generated sets have full ambient Fourier dimension \(d+1\), whereas
the generator has Fourier dimension \(d\).  This refutes the statement as
written, even for compact convex Borel \(A\).  It uses the allowed endpoint
\(s=d\) and makes no claim about a repaired hypothesis such as \(s<d\).
