# MathDB 365004: a stationary-orthocenter counterexample

**Task 1 — Full counterexample; zero new credit pending source review.** The ellipses x²/4+y²=1 and (x−31/20)²/(4/25)+y²/(63/1600)=1 support a full Poncelet triangle family whose orthocenter is always (31/16,0). The pair is neither focal-X4, MacBeath, nor Dual.

[LaTeX proof](solution.tex) · [PDF](solution.pdf) · [Proof audit](proof-audit.md) · [Literature audit](literature-audit.md) · [Verification](verification-results.json)

Both ellipses are nondegenerate and strictly nested. The fixed orthocenter lies inside the caustic, so every triangle is acute. Exact algebra proves all tangencies and all altitude equations throughout the full family.

The example is a specialization of the already published general orthocenter-locus formula in Garcia–Helman–Reznik, arXiv:2508.02368, Theorem 3. That formula is fully credited. The proof independently verifies the explicit counterexample to the later three-family classification; it makes no novelty claim for the formula.

The complete current 24-page original preprint, 7-page later classification preprint, and 18-page general-locus preprint were read. The identified 32-page journal final of the original source remains inaccessible beyond its subscription preview. Source and priority eligibility remain pending, so this package earns **0 new credit**. MathDB 372155 is a duplicate target and earns no separate credit.

Run Python on [verify.py](verify.py), with SymPy and mpmath. Three exact groups and 48 supplemental configurations at 90 decimal digits passed. The general proof supplies the infinite quantifiers. The PDF was visually inspected. Review is by the authoring agent only.

## Proposed follow-up tasks

- **Task 2.** Give a synthetic explanation of the stationary orthocenter.
- **Task 3.** Classify all nested ellipse pairs with this property up to similarities.
- **Task 4.** Determine the exact region of attainable fixed orthocenters for a given outer ellipse.
- **Task 5.** Determine polar-circle invariants throughout that classification.
