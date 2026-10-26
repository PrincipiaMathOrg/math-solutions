# Proof skeleton for MathDB #371420

## Claim

The literal MathDB/arXiv statement is false.  A smooth irrational
translation of \(\mathbb T^2\) has no periodic points and has zero
topological entropy, so the conjectured limsup is zero.

## G0 -- statement and scope gate

Conjecture 2 of arXiv:2511.08227v1 asks whether

\[
\limsup_{n\to\infty}
\frac{\#P_n(f)}{e^{n h_{\operatorname{top}}(f)}}>0
\]

for any \(C^r\), \(r>1\), or \(C^\infty\) diffeomorphism of a compact
surface.  Neither the displayed conjecture nor the MathDB transcription
assumes positive topological entropy.

Status: closed against the cited arXiv source and live MathDB record.

## G1 -- smooth surface-diffeomorphism gate

On \(\mathbb T^2=\mathbb R^2/\mathbb Z^2\), let

\[
f([x,y])=[x+\sqrt2,y].
\]

Translation descends to the quotient, its inverse is translation by
\(-\sqrt2\), and both maps are smooth.  The torus is a compact surface.

Status: closed; the example satisfies both smoothness alternatives in the
statement.

## G2 -- periodic-point gate

For \(n\geq1\), a fixed point of \(f^n\) would imply
\(n\sqrt2\in\mathbb Z\), contradicting irrationality of \(\sqrt2\).
Therefore \(P_n(f)=\varnothing\) for every positive \(n\).

Status: closed for all periods, not merely along a subsequence.

## G3 -- entropy gate

The map is an isometry of the flat torus.  Hence its \(n\)-step Bowen metric
equals the original metric.  At any fixed separation scale the largest
separated set consequently has a finite cardinality independent of \(n\).
Dividing its logarithm by \(n\) and passing to the entropy limits gives

\[
h_{\operatorname{top}}(f)=0.
\]

Status: closed directly from the separated-set definition.

## G4 -- contradiction and limitation gates

Every quotient in the conjecture is \(0/e^0=0\), so its limsup is zero.
The strict inequality fails.

Sarig's standard formulation explicitly assumes positive entropy, and the
cited 2025 source invokes that repaired formulation when describing the
known \(C^\infty\) result.  The example has zero entropy and therefore says
nothing about the repaired finite-smoothness problem.

Status: closed.

## Hostile audit

- A two-dimensional torus is a surface; no boundary convention is involved.
- The translation vector is well-defined modulo \(\mathbb Z^2\).
- Irrationality rules out fixed points of every positive iterate.
- The source defines \(P_n(f)\) using fixed points of \(f^n\), exactly the
  sets shown to be empty here.
- Translation invariance holds for the quotient metric, so the Bowen metric
  equality is exact rather than asymptotic.
- Compactness makes every fixed-scale separated set finite.
- Topological entropy is zero, not negative, and the denominator is exactly
  one; there is no undefined \(0/0\) expression.
- The map is \(C^\infty\), so it also belongs to every finite \(C^r\) class.
- The result is expressly limited to the missing-hypothesis formulation.  It
  does not claim to refute Katok's positive-entropy conjecture.
- No executable verifier is relevant: all dependencies are the explicit
  iterate formula and the defining separated-set entropy calculation.

## Verdict

Every dependency for the literal claim is closed.  MathDB #371420 is
refuted by an aperiodic smooth torus translation.
