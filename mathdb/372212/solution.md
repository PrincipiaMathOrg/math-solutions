# The sharp universal Gaussian EOT coupling bound

## Statement

Let `A,B` be positive-definite covariance matrices on `R^d`.  Let
`pi_epsilon` be their Gaussian entropic optimal-transport coupling and let
`pi_0` be the unregularized Gaussian optimal coupling.  We prove that the
limit in MathDB #372212 exists and satisfies

\[
\lim_{\varepsilon\downarrow0}
\frac{\mathcal W_2^2(\pi_\varepsilon,\pi_0)}{\varepsilon}
\leq \frac d2.                                           \tag{1}
\]

The constant is sharp.  In fact, equality holds exactly when `A=B`.
Consequently the optimal universal constant is

\[
\boxed{C_d=d/2}.
\]

Throughout, `epsilon` has the normalization used by the source and by the
MathDB statement: the entropic objective contains `2 epsilon KL`.  Rescaling
that objective rescales the parameter and therefore the displayed constant.

## Aligned square roots

Choose the canonical properly aligned Green operators `G_0,M_0` used by
Theorem 3.10 of the source, and abbreviate them to `G,M`, so

\[
GG^*=A,\qquad MM^*=B,\qquad C:=G^*M=M^*G\succ0.
\]

All three matrices are invertible because `A` and `B` are positive
definite.  Put

\[
X=G^*G,\qquad Y=M^*M,\qquad S=X+Y.
\]

From `G^*M=C` we have `M=G^{-*}C`, and therefore

\[
Y=CX^{-1}C.                                             \tag{2}
\]

In particular,

\[
XC^{-1}Y=C,\qquad YC^{-1}X=C.                          \tag{3}
\]

## Differentiate the exact distance formula

The source defines

\[
R_\varepsilon=f_\varepsilon(C),\qquad
f_\varepsilon(t)=
\frac{2t}{\sqrt{4t^2+\varepsilon^2}+\varepsilon}
=\frac{\sqrt{4t^2+\varepsilon^2}-\varepsilon}{2t}.
\]

Because the spectrum of `C` is bounded away from zero,

\[
R_\varepsilon
=I-\frac{\varepsilon}{2}C^{-1}+O(\varepsilon^2)        \tag{4}
\]

in operator norm.  Theorem 3.10 gives

\[
\mathcal W_2^2(\pi_\varepsilon,\pi_0)
=2\operatorname{tr}\!\left(S-\sqrt{Q_\varepsilon}\right), \tag{5}
\]

where

\[
Q_\varepsilon
=X^2+Y^2+XR_\varepsilon Y+YR_\varepsilon X.
\]

Equations (3)--(4) now collapse the first-order perturbation:

\[
Q_\varepsilon
=S^2-\varepsilon C+O(\varepsilon^2).                  \tag{6}
\]

For completeness, if `Q(t)=S^2+tH+O(t^2)` and
`sqrt(Q(t))=S+tZ+O(t^2)`, differentiating the square gives the Sylvester
equation

\[
SZ+ZS=H.
\]

Multiplication by `S^{-1}`, followed by cyclicity of trace, yields

\[
\operatorname{tr}Z
=\frac12\operatorname{tr}(S^{-1}H).                  \tag{7}
\]

Here `S^2` is positive definite, so `Q_epsilon` remains positive definite
near zero and its principal square root is Frechet differentiable there.

Applying (7) to (6), then differentiating (5), proves the exact formula

\[
\boxed{
\lim_{\varepsilon\downarrow0}
\frac{\mathcal W_2^2(\pi_\varepsilon,\pi_0)}{\varepsilon}
=\operatorname{tr}(S^{-1}C).
}                                                       \tag{8}
\]

Thus the conjectured limsup is actually a limit.

## The universal bound and equality case

Proper alignment supplies the decisive order relation:

\[
S-2C
=X+Y-G^*M-M^*G
=(G-M)^*(G-M)\succeq0.                                 \tag{9}
\]

Conjugating (9) by `S^{-1/2}` gives

\[
0\prec S^{-1/2}CS^{-1/2}\preceq\frac12I.
\]

Taking traces and using cyclicity in (8),

\[
\operatorname{tr}(S^{-1}C)
=\operatorname{tr}(S^{-1/2}CS^{-1/2})\leq\frac d2,
\]

which proves (1).

If equality holds, the positive-semidefinite matrix
`I/2-S^{-1/2}CS^{-1/2}` has trace zero, hence is zero.  Therefore `S=2C`,
and (9) forces `G=M`, so `A=B`.  Conversely, when `A=B` we may take
`G=M`; then (8) gives `tr((2X)^{-1}X)=d/2`.  This also proves sharpness.

## Verification scope

The proof above is finite-dimensional matrix analysis and does not depend on
computation.  The companion script reconstructs aligned roots for deterministic
positive-definite test matrices, checks identities (2)--(3) and (9), and
confirms that the exact finite-`epsilon` formula converges to (8), including
the equality case.
