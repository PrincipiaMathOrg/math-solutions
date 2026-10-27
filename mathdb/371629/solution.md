# Mensural densities and Reiter sequences

## Corrected statement

Let \(G\) be an infinite commutative discrete group, and let
\(\mu_n\in\ell^1(G)\) be probability measures:

\[
\mu_n(x)\geq 0,\qquad \sum_{x\in G}\mu_n(x)=1.
\]

For \(A\subseteq G\), put

\[
\overline d(A)=\limsup_{n\to\infty}\mu_n(A).
\]

Then \(\overline d\) is an upper density in the sense of
Révész--Ruzsa if and only if, for every \(t\in G\),

\[
\sum_{x\in G}\left|\mu_n(x)-\mu_n(x+t)\right|\longrightarrow 0.
\tag{1}
\]

This proves the normalized, and evidently intended, version of
Conjecture 12.3 in Révész--Ruzsa.  The word “probability” is absent from
the literal statement in the paper; without it the conjecture is false.
A counterexample to the literal wording is given below.

The sufficiency of (1) is noted in the source.  The substance is necessity.

## Properties of upper densities used

We use only two consequences of the definition, both recorded in
Statement 9.3 of the source.

1. If \(A+t_1,\ldots,A+t_m\) are disjoint, then

   \[
   \overline d\left(\bigcup_{i=1}^m(A+t_i)\right)
      =m\overline d(A).
   \tag{2}
   \]

2. If \(A'\) is obtained from \(A\) by a bijection whose displacements
   belong to one finite subset of \(G\), then

   \[
   \overline d(A')=\overline d(A).
   \tag{3}
   \]

The second property is called perturbation invariance.

## The selector lemma

The following is the main point of the proof.

**Lemma.**  Let \(\overline d\) be an upper density on \(G\).  Suppose
\(q\) is a finitely additive probability measure on all subsets of
\(G\) such that

\[
q(A)\leq\overline d(A)\qquad(A\subseteq G).
\tag{4}
\]

Then \(q\) is translation invariant.

**Proof.**  Fix \(t\in G\).

First suppose that \(t\) has infinite order.  Fix an integer \(L\geq2\).
Choose a transversal \(R\) for the cosets of the cyclic subgroup
\(\langle t\rangle\).  Partition every \(t\)-orbit into the blocks

\[
\{r+(kL+i)t:0\leq i<L\},
\qquad r\in R,\quad k\in\mathbb Z.
\]

Let

\[
C_0=\{r+kLt:r\in R,\ k\in\mathbb Z\},
\qquad C_i=C_0+it\quad(0\leq i<L).
\]

The sets \(C_0,\ldots,C_{L-1}\) partition \(G\).  Equation (2) gives

\[
\overline d(C_i)=\frac1L\qquad(0\leq i<L).
\tag{5}
\]

Call a set a selector if it contains exactly one point from each of the
displayed \(L\)-point blocks.  Every selector is a perturbation of
\(C_0\): move its selected point in a block to that block's zeroth
point.  Every displacement is one of
\(0,-t,\ldots,-(L-1)t\).  Thus (3) gives

\[
\overline d(S)=\frac1L
\quad\hbox{for every selector }S.
\tag{6}
\]

By (4), \(q(C_i)\leq1/L\).  Since the \(C_i\) partition \(G\) and
\(q(G)=1\), in fact

\[
q(C_i)=\frac1L\qquad(0\leq i<L).
\tag{7}
\]

Let \(E\subseteq C_0\), and let \(i\ne j\) lie in
\(\{0,\ldots,L-1\}\).  The two sets

\[
\begin{aligned}
S&=(E+it)\cup((C_0\setminus E)+jt),\\
S'&=((C_0\setminus E)+it)\cup(E+jt)
\end{aligned}
\]

are selectors, they are disjoint, and their union is \(C_i\cup C_j\).
Equations (4), (6), and (7) imply

\[
q(S)\leq\frac1L,\qquad q(S')\leq\frac1L,\qquad
q(S)+q(S')=\frac2L.
\]

Consequently both inequalities are equalities.  Comparing
\(q(S)=1/L\) with

\[
q(C_j)=q(E+jt)+q((C_0\setminus E)+jt)=\frac1L
\]

gives

\[
q(E+it)=q(E+jt).
\tag{8}
\]

Now take an arbitrary \(B\subseteq G\) and write
\(B_i=B\cap C_i\).  For \(0\leq i<L-1\), equation (8), applied to
\(E=B_i-it\), gives

\[
q(B_i+t)=q(B_i).
\]

All terms therefore cancel in \(q(B+t)-q(B)\), except possibly the
piece crossing from \(C_{L-1}\) to \(C_0\).  By (7),

\[
\left|q(B+t)-q(B)\right|
 =\left|q(B_{L-1}+t)-q(B_{L-1})\right|
\leq\frac1L.
\tag{9}
\]

Since \(L\) is arbitrary, \(q(B+t)=q(B)\).

If \(t\) has finite order \(m\), choose a transversal \(C_0\) for the
cosets of \(\langle t\rangle\), and put \(C_i=C_0+it\) for
\(0\leq i<m\).  The same selector and swap argument gives (8) for all
residues.  There is now no boundary error because \(mt=0\).  Thus
\(q(B+t)=q(B)\) exactly.  The case \(t=0\) is immediate.  Since \(t\)
was arbitrary, \(q\) is translation invariant. \(\square\)

## Necessity

Assume that

\[
\overline d(A)=\limsup_n\mu_n(A)
\tag{10}
\]

is an upper density.  Let \(\mathcal U\) be any free ultrafilter on
\(\mathbb N\), and define

\[
q_{\mathcal U}(A)=\lim_{n\to\mathcal U}\mu_n(A).
\tag{11}
\]

Ultrafilter limits preserve finite sums and positivity.  Because every
\(\mu_n\) is a probability measure, \(q_{\mathcal U}\) is a finitely
additive probability measure.  Moreover,

\[
q_{\mathcal U}(A)
\leq\limsup_n\mu_n(A)
=\overline d(A).
\]

The selector lemma shows that every \(q_{\mathcal U}\) is translation
invariant.

It follows that, for every fixed \(A\subseteq G\) and \(t\in G\),

\[
\mu_n(A)-\mu_n(A+t)\longrightarrow0.
\tag{12}
\]

Indeed, if (12) failed, then after passing to a subsequence and choosing
one sign there would be an \(\varepsilon>0\) for which the difference
were always at least \(\varepsilon\), or always at most
\(-\varepsilon\).  A free ultrafilter concentrated on that subsequence
would give a non-translation-invariant \(q_{\mathcal U}\), a
contradiction.

Fix \(t\), and define the signed \(\ell^1\)-vectors

\[
\nu_n(x)=\mu_n(x)-\mu_n(x+t).
\]

Equation (12) says that \(\sum_{x\in A}\nu_n(x)\to0\) for every
indicator \({\bf1}_A\).  It follows for every finite-valued bounded
function by linearity.  Such functions uniformly approximate every
\(f\in\ell^\infty(G)\), while

\[
\|\nu_n\|_1\leq2.
\]

Hence

\[
\sum_x f(x)\nu_n(x)\longrightarrow0
\qquad(f\in\ell^\infty(G)).
\tag{13}
\]

Thus \(\nu_n\) is weakly null in \(\ell^1(G)\).  The Schur property of
\(\ell^1\) now gives

\[
\|\nu_n\|_1\longrightarrow0,
\]

which is (1).

This last step is valid even when \(G\) is uncountable.  Every
\(\ell^1(G)\) vector has countable support, so the union of the supports
of the sequence \((\nu_n)\) is a countable set \(S\).  The whole
sequence lies in \(\ell^1(S)\), and the usual countable Schur theorem
applies.  Every functional in \(\ell^\infty(S)\) extends to one in
\(\ell^\infty(G)\), so (13) is precisely the needed weak convergence
on that subspace.

## Sufficiency

Assume (1), and define for every bounded real function \(f\)

\[
\overline M(f)=\limsup_n\sum_x f(x)\mu_n(x).
\]

Probability normalization gives norming on constants.  Monotonicity,
nonnegative homogeneity, and subadditivity are immediate.  For every
\(t\),

\[
\left|\sum_x\bigl(f(x)-f(x+t)\bigr)\mu_n(x)\right|
\leq \|f\|_\infty
   \sum_x|\mu_n(x)-\mu_n(x-t)|
\longrightarrow0.
\]

Thus \(\overline M(f-\tau_t f)=0\).  By restricted subtractivity
(Statement 2.5 of the source), \(\overline M\) is an upper mean.
Its restriction to indicators is exactly \(\overline d\), so
\(\overline d\) is an upper density.

## Why normalization cannot be omitted

Take \(G=\mathbb Z\).  Let

\[
\lambda_n(x)=
\begin{cases}
1/(2n),&1\leq x\leq2n,\\
0,&\text{otherwise},
\end{cases}
\qquad
\eta_n(x)={\bf1}_{2\mathbb Z}(x)\lambda_n(x).
\]

Thus \(\lambda_n\) is a probability measure, whereas
\(\eta_n(\mathbb Z)=1/2\).  Interleave them:

\[
\mu_{2n}=\lambda_n,\qquad \mu_{2n-1}=\eta_n.
\]

For every \(A\subseteq\mathbb Z\), \(\eta_n(A)\leq\lambda_n(A)\).
Therefore

\[
\limsup_j\mu_j(A)
=\limsup_n\lambda_n(A)
=\limsup_{N\to\infty}\frac{|A\cap[1,N]|}{N},
\]

because restricting the endpoint to even integers changes the ratios by
`o(1)`.  This is the ordinary asymptotic upper density.  Hence this unnormalized
sequence really does define an upper density.

On the other hand, \(\eta_n\) and its translate by \(1\) have disjoint
supports and both have mass \(1/2\), so

\[
\sum_x|\eta_n(x)-\eta_n(x+1)|=1.
\]

The sequence \((\mu_j)\) therefore violates (1).  This refutes the
necessity direction of the conjecture if “measures” is read literally
as arbitrary finite positive measures.  The zero sequence also shows
that (1) alone is not sufficient for norming.

The probability-measure hypothesis, or at least the condition
\(\mu_n(G)\to1\), is used exactly where the ultrafilter limit is made a
probability and the selector inequalities are forced to be equalities.

## Dependencies

- Révész--Ruzsa, Definition 2.1 and Statement 2.5 (upper means and
  restricted subtractivity).
- Révész--Ruzsa, Definition 9.1 and Statement 9.3(c),(e) (upper
  densities, restricted additivity, and perturbation invariance).
- The standard ultrafilter compactness principle.
- The classical Schur property of \(\ell^1\).

No amenability theorem, Følner theorem, or computation is used.
