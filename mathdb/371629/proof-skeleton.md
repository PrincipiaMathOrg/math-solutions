# Proof skeleton

## Source correction

The primary source is Révész--Ruzsa,
[Densitometria I. Discrete groups](https://arxiv.org/abs/2511.18064),
arXiv:2511.18064v1.

- The ambient group in the paper is an infinite commutative discrete
  group, not an arbitrary discrete group.
- Definition 12.1 calls \(\overline d(A)=\limsup\mu_n(A)\) mensural.
- Problem 12.2 asks which measure sequences define upper densities.
- Conjecture 12.3 proposes the Reiter condition
  \(\|\mu_n-\tau_t\mu_n\|_1\to0\) for every \(t\).
- The source never says “probability measure.”  That normalization is
  necessary for the conjecture as stated; see the counterexample below.

## Normalized theorem

For probability masses \(\mu_n\in\ell^1(G)\),
\(\limsup\mu_n(A)\) is an upper density if and only if
\(\|\mu_n-\tau_t\mu_n\|_1\to0\) for every \(t\).

## Necessity in five steps

1. **Dominated ultralimits.**  For a free ultrafilter \(\mathcal U\),
   \(q(A)=\lim_{\mathcal U}\mu_n(A)\) is a finitely additive
   probability and
   \(q(A)\leq\limsup_n\mu_n(A)=\overline d(A)\).

2. **Cyclic block selectors.**  Fix \(t\) of infinite order and
   \(L\geq2\).  On each \(t\)-orbit, divide the orbit into consecutive
   \(L\)-blocks.  Let \(C_i\) be the set of \(i\)-th points of all
   blocks.  The \(C_i\) partition \(G\) and are translates, so
   restricted additivity gives \(\overline d(C_i)=1/L\).
   Every set selecting one point from every block is a bounded
   perturbation of \(C_0\), hence also has upper density \(1/L\).

3. **Swap argument.**  Domination and \(q(G)=1\) force
   \(q(C_i)=1/L\).  For \(E\subseteq C_0\), the two selectors

   \[
   (E+it)\cup((C_0\setminus E)+jt),\qquad
   ((C_0\setminus E)+it)\cup(E+jt)
   \]

   partition \(C_i\cup C_j\).  Each has \(q\)-mass at most \(1/L\);
   their masses sum to \(2/L\).  Equality follows, and hence
   \(q(E+it)=q(E+jt)\).

4. **Boundary tends to zero.**  Decompose arbitrary \(B\) over the
   \(C_i\).  Translation by \(t\) preserves the \(q\)-mass of every
   piece except the piece crossing from residue \(L-1\) to residue
   \(0\).  Both boundary pieces have mass at most \(1/L\), so
   \(|q(B+t)-q(B)|\leq1/L\).  Let \(L\to\infty\).
   If \(t\) has finite order, use its finite orbits; the same swap
   argument has no boundary error.

5. **Schur upgrade.**  Every ultralimit is invariant, so
   \(\mu_n(A)-\mu_n(A+t)\to0\) for every fixed \(A\).  Thus
   \(\nu_n=\mu_n-\tau_t\mu_n\) is weakly null in \(\ell^1(G)\):
   first test indicators, then finite simple functions, then uniformly
   approximate arbitrary \(\ell^\infty\) functions using
   \(\|\nu_n\|_1\leq2\).  Schur's property gives
   \(\|\nu_n\|_1\to0\).

For uncountable \(G\), the union of the supports of the sequence is
countable, reducing Schur's theorem to ordinary \(\ell^1(\mathbb N)\).

## Sufficiency

Set

\[
\overline M(f)=\limsup_n\int f\,d\mu_n.
\]

Probability normalization, positivity, and the elementary properties
of limsup give all upper-mean axioms except restricted additivity.
The Reiter condition gives
\(\overline M(f-\tau_t f)=0\), which is the equivalent restricted
subtractivity axiom from Statement 2.5.

## Literal-wording counterexample

On \(\mathbb Z\), let \(\lambda_n\) be uniform on
\(\{1,\ldots,2n\}\), and let \(\eta_n\) be its restriction to the even
points, without renormalizing.  Interleave
\(\mu_{2n}=\lambda_n\), \(\mu_{2n-1}=\eta_n\).

Since \(0\leq\eta_n(A)\leq\lambda_n(A)\),

\[
\limsup_j\mu_j(A)=\limsup_n\lambda_n(A),
\]

which is asymptotic upper density.  But \(\eta_n\) and its unit
translate are disjoint measures of mass \(1/2\), so their
\(\ell^1\)-distance is \(1\).  Thus arbitrary unnormalized measures
make Conjecture 12.3 false even in the necessity direction.

## Exact gates

- Probability normalization is essential.  Merely having
  \(\limsup_n\mu_n(G)=1\) is not enough; the counterexample already has
  that property.
- Measures must be positive \(\ell^1\) masses, as indicated by the
  pointwise sum in Conjecture 12.3.
- The proof uses perturbation invariance, not translation invariance
  alone.  Equality of two limsups by itself does not force their
  pointwise difference to tend to zero.
