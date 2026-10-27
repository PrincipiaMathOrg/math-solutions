# Proof skeleton for MathDB #361027

Let

\[
G_n=(K_n\mathbin\cup K_n)+e
\]

and give every edge an arbitrary sign.  The two endpoints of the joining edge
have degree \(n\), so every signed edge coloring uses at least \(n\) colors.
It remains to construct an \(n\)-edge-coloring.

## 1. Walecki path decompositions

On \(\{\infty\}\cup\mathbb Z_{2m}\), the Walecki cycles

\[
C_i=(\infty,i,i-1,i+1,i-2,i+2,\ldots,
      i-(m-1),i+(m-1),i-m,\infty),
\qquad 0\le i<m,
\]

partition the edges of \(K_{2m+1}\).

- Removing \(\infty\) from every \(C_i\) decomposes \(K_{2m}\) into
  \(m\) Hamilton paths.  Every vertex is an endpoint of exactly one path.
- In every \(C_i\), delete its central finite edge.  These \(m\) edges are
  the diameter edges of \(\mathbb Z_{2m}\), hence form a perfect matching.
  The remaining graphs are \(m\) Hamilton paths of \(K_{2m+1}\), and
  \(\infty\) is internal to every path.

Relabeling lets \(\infty\) be any prescribed vertex in the odd case.

## 2. Every signed path uses one color pair

For a path and a nonzero color \(j\), choose either incidence color at its
first endpoint.  Across a signed edge \(uv\), define

\[
f(v:uv)=-\sigma(uv)f(u:uv),
\]

and at each internal vertex use the opposite member of \(\{\pm j\}\) on
the next edge.  The two incidences at every internal vertex are distinct,
so this is a proper signed 2-edge-coloring of the path.

## 3. Even order

If \(n=2m\), decompose each clique into \(m\) Hamilton paths and color the
paths with the disjoint pairs \(\{\pm1\},\ldots,\{\pm m\}\).  At the joining
vertex of each clique, exactly one path ends, so exactly one nonzero signed
color is missing.  Relabel the path pairs and reverse the sign orientation
of one endpoint path so that the two missing colors \(x,y\) satisfy

\[
x=-\sigma(e)y.
\]

Use \(x\) and \(y\) on the two incidences of \(e\).

## 4. Odd order

If \(n=2m+1\), use the odd decomposition with the joining vertex as
\(\infty\).  Color the \(m\) Hamilton paths with the \(m\) nonzero pairs
and the leftover perfect matching with \(0\).  The joining vertex is
internal to every path and is not covered by the matching, so it sees every
nonzero color and misses exactly \(0\).  Color both incidences of \(e\) by
\(0\); the signed edge equation holds for either sign of \(e\).

## 5. Boundary case and conclusion

For \(n=1\), the graph is a single signed edge and color \(0\) works.
Thus \(\chi'(G_n)=n=\Delta(G_n)\) for every \(n\ge1\) and every signature.

Second-pass dependency audit: every parity case, the arbitrary-sign
quantifier, the bridge sign, and \(n=1\) are explicit.  The accompanying
verifier checks the Walecki partitions through order 80, deterministic
arbitrary-sign constructions through order 40, and every signature through
order 4.
