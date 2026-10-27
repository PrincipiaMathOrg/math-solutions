# Proof skeleton for MathDB #333521

The source works throughout with finite simple connected undirected graphs.
Let \(A\cup B\) be the bipartition, with
\(a=|A|\geq b=|B|\), \(n=a+b\), and \(d=a-b\).

1. Define \(X,Y,Z\) as the sums of distances within \(A\), within \(B\),
   and across the two parts.  Bipartite parity gives

   \[
   X\geq a(a-1),\quad Y\geq b(b-1),\quad Z\geq ab.
   \]

   If the graph is not complete bipartite, one cross-part nonedge has
   odd distance at least \(3\), so \(Z\geq ab+2\).

2. The all-ones Rayleigh quotient gives
   \(q_1\geq4(X+Y+Z)/n\).  Averaging Rayleigh quotients over the
   zero-sum subspaces supported on the two parts gives

   \[
   q_n\leq
   r_A=\frac{2(a-2)X+(a-1)Z}{a(a-1)},\qquad
   q_n\leq
   r_B=\frac{2(b-2)Y+(b-1)Z}{b(b-1)}.
   \]

3. For \(0\leq\theta\leq1\),

   \[
   S_{\mathcal Q}\geq
   \frac{4(X+Y+Z)}n-\theta r_A-(1-\theta)r_B
   =c_XX+c_YY+c_ZZ.
   \]

   Choose \(\theta=0\) when both smaller-part coefficients are already
   nonnegative.  Otherwise use

   \[
   \theta_Y=\frac{a(b-2)-b^2}{n(b-2)}
   \quad(b\geq4),
   \qquad
   \theta_Z=\frac{a(a-3b)}{n(a-b)}
   \quad(b=2,3).
   \]

   Direct algebra gives \(c_X,c_Y,c_Z\geq0\) and the three possible
   base bounds

   \[
   B_0=\frac{3n}{2}+\frac d2+\frac{d^2}{n},\quad
   B_Y=\frac{3n}{2}+\frac{d(bn-2d)}{2n(b-2)},\quad
   B_Z=2n.
   \]

4. The balanced complete-bipartite target is \(3n/2\) for even
   \(n\geq4\), and

   \[
   \frac{2n+1+\sqrt{n^2+8}}2
   \]

   for odd \(n\geq5\).  Every unbalanced base bound is strictly larger.

5. For even balanced parts, \(B_0\) equals the target and \(c_Z>0\);
   the extra two units in \(Z\) make every noncomplete graph strict.
   For odd balanced parts, the base deficit is less than \(1/n\), while
   a missing cross edge contributes
   \(2c_Z=4(n-2)/(n(n-1))>1/n\).  Complete balanced graphs attain the
   target by their explicit block spectrum.

6. If \(b=1\), connectedness forces a star.  Its spread
   \(\sqrt{9n^2-32n+32}\) is strictly above the balanced target for
   \(n\geq4\).  Orders at most three are immediate.

Hostile dependency audit, 19 August 2026: checked the source's global
connectedness convention, both Rayleigh inequalities and projection traces,
all six coefficient regimes, weight endpoints, even/odd target spectra,
the exceptional odd balanced deficit, the missing-edge distance increment,
the star and small-order cases, and every equality implication.
