# Proof skeleton for MathDB #365102

## Target

Refute the literal assertion that every continuous potential satisfying

\[
f(x)-2\log|x|\longrightarrow+\infty
\]

admits a linear tilt whose free Gibbs equilibrium measure has barycenter
zero.

## G0 -- source and scope

- Conjecture 1 of arXiv:2410.02715v2 quantifies over every continuous \(f\)
  satisfying condition (14).
- Condition (14) is exactly logarithmic confinement, not superlinear growth.
- Definition 1 makes a free Gibbs measure the maximizer of
  \(\chi_f(\mu)=\chi(\mu)-\int f\,d\mu\).
- The theorem quoted before condition (14) gives existence, uniqueness, and
  compact support under that condition in one dimension.

Status: closed against the current primary source.

## G1 -- counterexample satisfies the hypothesis

Take

\[
f(x)=2\log(1+(x-1)^2).
\]

For \(|x|\geq4\),

\[
1+(x-1)^2\geq |x|^2/4,
\]

and hence

\[
f(x)-2\log|x|\geq2\log(|x|/4)\to+\infty.
\]

Status: closed.

## G2 -- the only confining tilt is not centered

The potential is invariant under \(r(x)=2-x\).  Both free entropy and the
potential term are invariant under pushing a measure forward by \(r\).
Uniqueness therefore gives \(r_\#\nu_f=\nu_f\).  Compact support makes the
barycenter finite, and reflection invariance gives

\[
m=2-m,
\qquad m=1.
\]

Status: closed.

## G3 -- nonzero tilts have no centered equilibrium measure

Let \(\mu_0\) be uniform on \([-1,1]\), let
\(s=\operatorname{sgn}(\lambda)\), and translate \(\mu_0\) by \(-st\).
Translation leaves \(\chi\) fixed.  For \(y\in[-1,1]\),

\[
f(y-st)\leq4\log(t+3).
\]

Consequently

\[
\chi_{f+\lambda\operatorname{id}}(\mu_t)
\geq\chi(\mu_0)+|\lambda|t-4\log(t+3)\to+\infty.
\]

The variational supremum is infinite, so no maximizer exists when
\(\lambda\ne0\) in the standard equilibrium convention.  More
convention-independently, every measure with a finite barycenter has finite
positive logarithmic energy and cannot attain the infinite supremum.  Thus
no centered free Gibbs maximizer exists.

Status: closed.

## G4 -- quantifier and edge audit

- At \(\lambda=0\), the free Gibbs measure exists but has barycenter \(1\).
- At every \(\lambda\ne0\), no associated centered free Gibbs measure exists.
- The translating test measure has finite logarithmic energy.
- The argument is insensitive to the additive normalization of free entropy.
- The example is smooth and real-valued, stronger than the requested
  continuity.
- It does not address a repair imposing superlinear growth or confinement
  under all linear tilts.

Status: closed.

## Verdict

Every proof obligation for the literal conjecture is closed.  Conjecture 1
and the corresponding MathDB assertion are false as written.
