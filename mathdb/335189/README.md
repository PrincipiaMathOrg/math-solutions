# MathDB 335189

Complete counterexample to the proposed Redheffer lower bound for
normalized Bessel-function ratios. The bound fails at (nu, x) = (30, 1),
certified using exact rational arithmetic. For every real nu >= 28,
it also fails at every sufficiently small nonzero real x.

**Campaign eligibility is pending; zero new problem credit.**
The complete current preprint was inspected, but the complete 2018
journal version remains inaccessible. The credited batch total is 19.

- [LaTeX: Task 1 and exactly four follow-up Tasks 2--5](solution.tex)
- [Compiled PDF](solution.pdf)
- [Exact verifier](verify_counterexample.py) and [certificate](exact-certificate.json)
- [Proof audit](proof-audit.md)
- [Literature and eligibility audit](literature-audit.md)
- [Dated source records](source-check.json)
- [Verification manifest](verification-manifest.json)

Run with Python and SymPy:

    python verify_counterexample.py
    tectonic solution.tex

The 19 exact checks pass. All four PDF pages were visually inspected.
The analytic proof includes the boundary terms in the variational
identity and a rigorous Taylor-sign argument. No numerical approximation
of a Bessel zero is needed. This is an authoring-agent audit, with no
independent peer review or global priority claim.
