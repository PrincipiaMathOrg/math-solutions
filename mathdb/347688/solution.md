# MathDB #347688: a five-dimensional representation of \(X_{2,9}\)

## Result

The answer is **yes**:

\[
\operatorname{rep}(X_{2,9})\le 5.
\]

The representation is defined by integral affine inequalities and has integral
witnesses for all faces.

## Definition and convention

For a finite family \(\mathcal C=(C_v)_{v\in V}\) of compact convex subsets of
\(\mathbb R^d\), its nerve is

\[
N(\mathcal C)=\{S\subseteq V:\bigcap_{v\in S}C_v\ne\varnothing\}.
\]

The intersection indexed by the empty set is \(\mathbb R^d\), so the empty
face is present.  A simplicial complex is \(d\)-representable if it is the
nerve of such a family in \(\mathbb R^d\), and \(\operatorname{rep}(K)\) is
the least such \(d\).  This is the convention in Alan Lew,
“Representability and boxicity of simplicial complexes,” arXiv:2008.09997,
Conjecture 20 (published in *Discrete & Computational Geometry* 68 (2022),
592–607).  Our representing sets are compact polytopes.

Identify the nine vertices with \(\mathbb F_3^2\), in lexicographic order

\[
0=(0,0),1=(0,1),2=(0,2),3=(1,0),4=(1,1),5=(1,2),
6=(2,0),7=(2,1),8=(2,2).
\]

The twelve affine lines, in the order used by the certificate, are

\[
036,147,258;\quad012,345,678;\quad048,156,237;\quad057,138,246.
\]

Thus

\[
X_{2,9}=\{S\subseteq\{0,\ldots,8\}:S\text{ contains none of these lines}\}.
\]

## The explicit construction

For every incident pair \((L,v)\), where \(L\) is a line and \(v\in L\),
the accompanying file `certificate.json` gives an integer row

\[
a_{L,v}=(a_0,a_1,\ldots,a_5).
\]

It denotes the affine function

\[
\ell_{L,v}(x_1,\ldots,x_5)=a_0+\sum_{i=1}^5a_i x_i.
\]

Define nine compact convex polytopes by

\[
C_v=[-42,42]^5\cap
\bigcap_{\substack{L\text{ a line}\\v\in L}}
\{x\in\mathbb R^5:\ell_{L,v}(x)\ge1\}.
\tag{1}
\]

The `normals` entry is aligned with the displayed `lines` entry: its
\(i,j\) row is the affine row for the \(j\)-th point of the \(i\)-th line.
The `witnesses` entry maps each line-free four-set, written as a four-digit
string, to an integral point of \([-42,42]^5\).

Only the following exact checks about those integers are used.

1. For each line \(L=\{p,q,r\}\), the three affine rows have coordinatewise
   sum zero.  Consequently
   \(\ell_{L,p}+\ell_{L,q}+\ell_{L,r}=0\) identically.
2. The witness keys are exactly all line-free four-subsets of
   \(\{0,\ldots,8\}\) (there are 54 of them).
3. If \(F\) is one of these four-sets and \(y_F\) its witness, then
   \(y_F\in[-42,42]^5\) and
   \(\ell_{L,v}(y_F)\ge1\) for every \(v\in F\) and every line \(L\ni v\).

These are integer equalities and inequalities.  The verifier reconstructs
the affine-plane lines and the 54 four-caps independently, and checks all of
them.  In fact the smallest left side in item 3 is 50, so there is no issue
of numerical tolerance.

## Completeness of the four-cap witnesses

A line-free set in \(AG(2,3)\) has at most four points.  Indeed, suppose five
points contained no line.  In each of the four parallel classes, their
occupancies on the three lines would have to be \((2,2,1)\), and hence that
parallel class would account for two pairs of the five points.  Every pair
of points has exactly one direction, so the four classes would account for
only \(4\cdot2=8\) pairs, whereas five points have \(\binom52=10\) pairs.

Moreover, every line-free set is contained in a line-free four-set.  For a
line-free triple, the third points on its three pair-lines are distinct; any
of the other three points extends the triple to a four-set with no line.  A
line-free set of size at most two can first be extended to a noncollinear
triple.  (The verifier also checks this containment directly for every one
of the \(2^9\) subsets.)

## Proof that the nerve is exactly \(X_{2,9}\)

Let \(S\) contain an affine line \(L=\{p,q,r\}\).  If some point \(x\)
belonged to every \(C_v\), \(v\in S\), then (1) would give

\[
\ell_{L,p}(x),\ell_{L,q}(x),\ell_{L,r}(x)\ge1.
\]

Their sum is identically zero, a contradiction.  Hence every nonface of
\(X_{2,9}\) has empty intersection in the constructed family.

Conversely, let \(S\) contain no line.  By the preceding paragraph choose a
line-free four-set \(F\supseteq S\).  The certificate point \(y_F\) satisfies
all defining inequalities of \(C_v\) for every \(v\in F\), as well as the
box constraints.  Thus

\[
y_F\in\bigcap_{v\in F}C_v\subseteq\bigcap_{v\in S}C_v,
\]

so \(S\) is a face of the nerve.  Therefore

\[
N(C_0,\ldots,C_8)=X_{2,9},
\]

and the nine polytopes (1) prove \(\operatorname{rep}(X_{2,9})\le5\).

## Exact audit

Run

```text
python verify_representation.py
```

from this directory.  The verifier uses only the Python standard library,
integer arithmetic, and constant-size data.  It does not invoke an LP solver
or make floating-point feasibility decisions.  It checks the certificate
schema, the affine-plane incidence structure, all line row-sums, all 54 cap
witnesses and their incident inequalities, and a certificate of the correct
answer for each of all \(512\) vertex subsets.  The pinned SHA-256 hashes are

```text
certificate.json         db557b4c51e033d699eece7478bcc155dad7f36165163c9e8f0b218366e64981
verify_representation.py 32c3ec8576beb538ec29b06fa016b63431ce5c11a83c5fca65ac339746084cfe
```

The archived output is in `verification.out`.

## Scope

This construction proves the requested upper bound only.  It does not claim
that five is the minimum representation dimension of \(X_{2,9}\).
