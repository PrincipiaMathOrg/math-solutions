# MathDB #332161: a two-element counterexample

## Result

The stated Schur--Brauer conjecture for semimodules is **false**.  A
counterexample is the regular one-dimensional module over the field
\(\mathbb F_2\), split into its two singleton color classes.

## The source statement

Conjecture 3.26 of Xiongping Dai, “Grünwald version of van der Waerden's
theorem for semi-modules,” [arXiv:1512.08695v4](https://arxiv.org/html/1512.08695v4),
says the following.  If

\[
M=B_1\cup\cdots\cup B_q
\]

is any finite partition of a semimodule \(M\) over a semiring \(R\), then
some fixed cell \(B_j\) has the property that, for every finite \(F\subseteq
R\), there are \(a\in M\) and \(b\in B_j\setminus\{\boldsymbol o\}\) such
that

\[
a+Fb\subseteq B_j.
\tag{1}
\]

Here \(Fb=\{fb:f\in F\}\).  The source does not require \(R\) or \(M\) to
be infinite, cancellative, torsion-free, or a \(*\)-semiring, and it places no
restriction on the finite subset \(F\) beyond \(F\subseteq R\).

## Counterexample

Take

\[
R=M=\mathbb F_2=\{0,1\}
\]

with the usual operations, and let \(M\) be the regular left \(R\)-module.
Partition it as

\[
B_1=\{0\},\qquad B_2=\{1\}.
\]

Choose the finite set

\[
F=R=\{0,1\}.
\]

The cell \(B_1\) cannot satisfy (1), because it contains no permitted
element \(b\ne\boldsymbol o=0\).

For \(B_2\), the only possible \(b\) is \(b=1\).  For either \(a\in M\),

\[
a+Fb=\{a+0\cdot1,a+1\cdot1\}=\{a,a+1\}=\mathbb F_2,
\]

which is not contained in the singleton \(B_2\).  Thus the same finite set
\(F\) defeats both color classes.  No cell has the asserted property, so the
conjecture is false.

## Hypothesis check

The source defines a semiring by requiring an abelian additive semigroup
with zero, an associative multiplicative semigroup with unit and absorbing
zero, and both distributive laws.  It defines a left semimodule as an
abelian additive semigroup with zero and an action satisfying

\[
(r+t)g=rg+tg,\qquad r(g+h)=rg+rh,\qquad 1g=g,\qquad 0g=\boldsymbol o.
\]

The field \(\mathbb F_2\) and its regular module satisfy every one of these
axioms (as well as the usual scalar-associativity axiom).  A finite algebra
also causes no issue with the paper's use of the discrete topology.

There is likewise no quantifier ambiguity.  The conjecture asserts

\[
\exists j\ \forall F\subseteq_{\rm fin}R\ \exists a\in M\
\exists b\in B_j\setminus\{\boldsymbol o\}:a+Fb\subseteq B_j.
\]

The construction proves its negation using one common choice
\(F=\{0,1\}\) for both cells.  Although the source only requires \(a\in M\),
the presence of \(0\in F\) would force \(a=a+0b\in B_j\) whenever (1)
held, so allowing \(a\) outside the cell cannot rescue the claim.

## Exact verification

The accompanying `certificate.json` records the two operation tables, the
regular scalar action, the partition, and \(F\).  The standard-library
script `verify_counterexample.py` independently checks all finite semiring
and semimodule identities, the partition axioms, and every possible pair
\((a,b)\) in the conjecture's conclusion.  Run

```text
python verify_counterexample.py
```

from this directory.  All checks use explicit exceptions and therefore
remain active under `python -O`.

## Scope

This refutes the conjecture exactly as stated in all arXiv versions and in
MathDB #332161.  It does not decide a repaired version restricted to an
infinite or otherwise nonperiodic class of semirings/semimodules.  Any such
repair needs new hypotheses that explicitly exclude this finite-field
obstruction.
