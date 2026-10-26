# MathDB 326757: positive reduced numerators

**Task 1 — Full proof; zero new credit pending source and prior-implication review.** Multiplying the credited Chapoton–Zeng recurrence by the appropriate q-factorial gives a positive polynomial recurrence. Its leading coefficient is a power of q, proving that the displayed q-factorial denominator cannot cancel.

[LaTeX](solution.tex) · [PDF](solution.pdf) · [Proof audit](proof-audit.md) · [Literature audit](literature-audit.md) · [Verification](verification-results.json)

The proof covers every positive n, coefficientwise nonnegativity in both variables, nonzero coefficients at every x-degree, and exact reduced denominator. The recurrence and the q-Catalan inputs are prior work.

All 15 pages of the current primary and all 14 pages of Cigler's related author note were read. Cigler's positive basis expansion is a substantial earlier implication. The 14-page journal final could not be retrieved beyond indexed metadata. This package makes no new priority claim and receives 0 new credit.

Run Python on [verify.py](verify.py), requiring SymPy. Three exact groups passed, including checks against the original Hahn equations and boundary values, rather than only the cleared recurrence. The PDF was visually inspected. Review is by the authoring agent only.

## Proposed follow-up tasks

- **Task 2.** Give a direct combinatorial model for numerator coefficients.
- **Task 3.** Determine exact monomial support and Newton polygons.
- **Task 4.** Classify coefficient unimodality or log-concavity in q.
- **Task 5.** Extend the exact-denominator result to the general Gould parameter.
