# Signed edge coloring of two cliques joined by one edge

## Theorem

Let \(G_n\) be the graph obtained from two vertex-disjoint copies of
\(K_n\) by adding one edge between them.  For every signature
\(\sigma:E(G_n)\to\{\pm1\}\),

\[
\boxed{\chi'(G_n,\sigma)=\Delta(G_n)=n.}
\]

This proves Conjecture 26 in Janczewski--Turowski--Wroblewski and resolves
MathDB #361027.

We use the authors' convention

\[
M_k=
\begin{cases}
\{0,\pm1,\ldots,\pm \ell\},&k=2\ell+1,\\
\{\pm1,\ldots,\pm \ell\},&k=2\ell,
\end{cases}
\]

under which a signed \(k\)-edge-coloring assigns a color to every incidence
and satisfies

\[
f(u:uv)=-\sigma(uv)f(v:uv)                         \tag{1}
\]

on each edge, with distinct colors on incidences sharing a vertex.

## A path-coloring observation

Every arbitrarily signed path can be colored with one nonzero pair
\(\{\pm j\}\).  Choose either color at the first incidence.  Having colored
the incidence at the near end of an edge, use (1) to color its far end; at
an internal vertex use the opposite color on the next edge.  Thus the two
incidences at every internal vertex are \(j\) and \(-j\), while (1) holds on
every edge.

Consequently, if a graph is decomposed into paths, we may color different
paths with disjoint color pairs and the edge signs impose no further
restriction.  A matching may similarly be colored with \(0\).

## The needed Walecki decompositions

We record the relevant form of Walecki's construction.  On
\(\{\infty\}\cup\mathbb Z_{2m}\), put

\[
C_i=(\infty,i,i-1,i+1,i-2,i+2,\ldots,
      i-(m-1),i+(m-1),i-m,\infty)                 \tag{2}
\]

for \(0\le i<m\), with finite labels read modulo \(2m\).

These \(m\) Hamilton cycles partition \(K_{2m+1}\).  Here is a short
verification.  The two edges at \(\infty\) in the cycles collectively join
\(\infty\) once to every finite vertex.  The finite edges in \(C_i\) are

\[
\{i+j-1,i-j\}\quad(1\le j\le m)                  \tag{3}
\]

and

\[
\{i-j,i+j\}\quad(1\le j<m).                     \tag{4}
\]

The edges in (3) have endpoint sum \(2i-1\), and those in (4) have endpoint
sum \(2i\), modulo \(2m\).  For each odd sum there are exactly \(m\)
unordered non-loop pairs, all listed by (3) for the unique \(i\); for each
even sum there are exactly \(m-1\), all listed by (4).  Hence every finite
edge occurs exactly once.

Two consequences will be used.

1. Deleting \(\infty\) from every cycle in (2) gives an edge decomposition
   of \(K_{2m}\) into \(m\) Hamilton paths.  Each finite vertex is an
   endpoint of exactly one of the paths, because its unique edge to
   \(\infty\) was deleted.

2. In each cycle in (2), the central edge of the displayed finite sequence
   has endpoints differing by \(m\).  The \(m\) central edges are distinct,
   so they are precisely the diameter perfect matching of
   \(\mathbb Z_{2m}\).  Deleting one central edge from each cycle therefore
   decomposes \(K_{2m+1}\) into \(m\) Hamilton paths and that perfect
   matching.  The vertex \(\infty\) is internal to every path and is
   uncovered by the matching.  By relabeling, \(\infty\) may be any
   prescribed vertex.

## Even \(n\)

Let \(n=2m\).  In each copy of \(K_n\), use consequence 1 and color its
\(m\) Hamilton paths with the disjoint pairs

\[
\{\pm1\},\ldots,\{\pm m\}.
\]

At every vertex exactly one of those Hamilton paths ends and all the others
pass through.  In particular, the vertex incident with the joining edge
sees both colors from \(m-1\) pairs and one color from the remaining pair.
It therefore misses exactly one member of \(M_n\).

Order the path pairs in the two cliques so that the path ending at each
joining vertex uses the same absolute color.  Reversing all incidence
colors on one path preserves (1) and lets us choose which sign is missing.
Thus, if the missing colors at the two joining vertices are \(x\) and \(y\),
we may arrange

\[
x=-\sigma(e)y.                                    \tag{5}
\]

Color the two incidences of the joining edge by \(x\) and \(y\).  Equation
(5) is exactly (1), and the colors are proper because they were missing at
their respective endpoints.  This is an \(n\)-edge-coloring of the whole
signed graph.

## Odd \(n\)

Let \(n=2m+1\).  In each clique apply consequence 2 with its joining vertex
as \(\infty\).  Color the \(m\) Hamilton paths with
\(\{\pm1\},\ldots,\{\pm m\}\), and color the remaining perfect matching
with \(0\).

The joining vertex lies internally on every Hamilton path and is uncovered
by the matching.  It consequently sees every nonzero member of \(M_n\) and
misses exactly \(0\).  Assign \(0\) to both incidences of the joining edge.
They are proper at their endpoints and satisfy

\[
0=-\sigma(e)0
\]

regardless of the sign of the joining edge.

## Conclusion

The case \(n=1\) is a single signed edge and is colored by \(0\).  For every
\(n\ge2\), the preceding constructions give an \(n\)-edge-coloring.  The
two joining vertices have degree \(n\), so no coloring with fewer than
\(n\) colors is possible.  Therefore

\[
\chi'(G_n,\sigma)=n=\Delta(G_n)
\]

for every signature, as claimed.
