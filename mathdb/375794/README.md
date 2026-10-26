# MathDB 375794: initial partial quotients of a zeta tail

Complete mathematical proof for g(N) = sqrt((sum over j > N of j^(-3))/2). The first two regular continued-fraction coefficients are 2N + 1 and 4N + 2 for every N >= 1. The third is floor((12N + 6)/19) for every N >= 2. Every fixed coefficient is eventually quasi-polynomial.

**Campaign eligibility is pending; zero new problem credit.** Qian Hu's 2026 dissertation claims the general asymptotic quasi-polynomial theorem. Its complete public abstract was read, but the PDF returned HTTP 403, leaving its treatment of these particular uniform formulas unchecked. The credited campaign total remains 21.

[Proof PDF](solution.pdf) · [LaTeX](solution.tex) · [MathDB](https://mathdb.com/p/375794)

Rational telescoping bounds establish the initial coefficients uniformly, including every Pell index in Feldman's Conjecture 4.1 and the smallest index left open in the source. A self-contained Laurent-series argument establishes the eventual pattern. The general mechanism is credited to Hu's stated prior result; no claim of novelty for that mechanism is made.

The third formula has a genuine small-input exception at N = 1, where the coefficient is 1. The source calls its pattern formal, and all its Pell indices are at least 3. This exception is explained for scope and is not the basis of a new-solution claim.

Task 1 is the complete theorem. Tasks 2–5 propose effective thresholds, period and degree growth, normalized tails of other odd zeta values, and a proof-assistant formalization.

Validation: 36 exact checks pass, including global polynomial sign certificates and rational enclosures of all three coefficients for N = 1 through 18. All five PDF pages were visually inspected. Run:

    python problems/375794/verify_quotients.py

The [proof audit](proof-audit.md), [literature audit](literature-audit.md), [source record](source-check.json), and [manifest](verification-manifest.json) record the evidence and its limits. Verification was performed by the authoring agent; the package has no independent or Lean verification.
