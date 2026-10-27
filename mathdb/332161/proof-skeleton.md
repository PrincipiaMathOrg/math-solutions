# Proof skeleton for MathDB #332161

## Claim

The literal source conjecture is false.

## Data

1. Let \(R=M=\mathbb F_2\), with \(M\) the regular left \(R\)-module.
2. Let \(B_1=\{0\}\) and \(B_2=\{1\}\).
3. Let \(F=\{0,1\}\subseteq R\).

## Algebra gate

The operation tables are

\[
\begin{array}{c|cc}+&0&1\\\hline0&0&1\\1&1&0\end{array},
\qquad
\begin{array}{c|cc}\cdot&0&1\\\hline0&0&0\\1&0&1\end{array}.
\]

They make \(R\) a field and hence a semiring under the source definition.
Using the multiplication table as scalar action makes \(M\) a left
semimodule under every identity displayed in the source.

## Partition gate

The two nonempty singleton cells are disjoint and cover \(M\).  Thus they
form a finite partition allowed by the conjecture.

## Quantifier gate

The source assertion has the order

\[
\exists j\ \forall F\ \exists a\ \exists b\ne0.
\]

It is enough to exhibit, for every cell \(j\), one finite \(F\) for which
no \((a,b)\) works.  The same \(F=R\) works for both cells.

- In \(B_1\), there is no nonzero \(b\).
- In \(B_2\), necessarily \(b=1\), and for every \(a\in\mathbb F_2\),
  \(a+Fb=\{a,a+1\}=\mathbb F_2\not\subseteq B_2\).

Therefore neither cell has the source property.

## Boundary-hypothesis gate

- The conjecture says “any finite subset of \(R\),” so \(F=\{0,1\}\) is
  allowed and may contain zero.
- The conjecture says semiring, not \(*\)-semiring.  This wording is
  unchanged across arXiv v1--v4.
- No infinitude, cancellativity, characteristic-zero, or torsion-free
  hypothesis occurs.
- Even if discreteness from the surrounding paper were imported, finite
  \(\mathbb F_2\) is discrete.

## Machine gate

`verify_counterexample.py` reads the pinned JSON certificate and exhausts
all possibilities for \(a\) and permitted \(b\).  It also verifies the
operation-table identities rather than assuming that the labels encode
\(\mathbb F_2\).
