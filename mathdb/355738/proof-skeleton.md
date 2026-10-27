# Proof skeleton for MathDB #355738

Take \(n=2\) and \(a=b=2/3\). With normalized Haar measure \(m\) on
\(\mathbb T\), normalize

\[
w(\zeta)=c_b|1-\zeta|^{-b}
\quad\text{so that}\quad
\int w\,dm=1,
\]

and set

\[
\alpha(h)=\max\{\lVert h\rVert _1,\int|h|w\,dm\}.
\]

1. Since \(b<1\), \(w\in L^1\). The displayed maximum is a gauge norm,
   is normalized, dominates \(L^1\), and is continuous because the
   integral of an \(L^1\) function is absolutely continuous.

2. The analytic function \(f(z)=(1+z)^{-a}\) has its boundary singularity
   at \(-1\), away from the weight singularity at \(1\). Thus both
   \(\int|f|\,dm\) and \(\int|f|w\,dm\) are finite. The bounded radial
   approximants \(f_r(z)=(1+rz)^{-a}\) converge in both integrals, so
   \(f\in H^\alpha\).

3. Every element of \(M_\alpha(z^2)\) has only even Fourier
   coefficients. This follows by approximating it in \(\alpha\), hence
   in \(L^1\), by functions in \(H^\infty(z^2)\).

4. If \(f=g_0+zg_1\) with \(g_0,g_1\in M_\alpha(z^2)\), parity forces

   \[
   g_0(z)=\frac{f(z)+f(-z)}2
   =\frac12\big((1+z)^{-a}+(1-z)^{-a}\big).
   \]

5. Near \(1\), the first term is bounded and the second has size
   \(|1-z|^{-a}\), so no cancellation can remove the singularity. After
   multiplication by \(w\), the local integrand has order
   \(|1-z|^{-(a+b)}=|1-z|^{-4/3}\), which is not integrable. Hence
   \(g_0\notin L^\alpha\), a contradiction.

Separate hostile dependency audit: passed on 19 August 2026. The audit
checked normalization and continuity of the weighted maximum norm, the two
distinct boundary singularities, direct \(H^\alpha\) approximation rather
than mere ambient-space membership, continuity of Fourier coefficients under
the available \(L^1\) convergence, uniqueness of the even residue component,
the possible complex-phase cancellation in that component, and the endpoint
conditions \(a<1\), \(b<1\), \(a+b>1\).
