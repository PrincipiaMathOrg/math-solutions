# MathDB 368345 — Hoggatt sums fail infinite log-convexity

**Complete disproof for every parameter m >= 4; eligibility pending,
zero new campaign credit.**

At parameters 4 and 5, the fourth log-convexity iterate has a negative
entry at index 2. For every integer parameter m >= 6, the third iterate
already has a negative entry there. An explicit polynomial factorization
and a monotonicity argument prove the entire infinite family.

- [LaTeX solution](solution.tex) and [PDF](solution.pdf).
- [Proof audit](proof-audit.md) and [literature audit](literature-audit.md).
- [Exact verifier](verify.py) and [results](verification-results.json).
- Task 1 contains the proof; Tasks 2–5 give four follow-up directions.

Run `python verify.py` with SymPy installed. Four exact verification
groups pass. Review is by the authoring agent only.

The definition and conjecture are taken from the complete current
14-page preprint. The identified journal final remains inaccessible
and unread, so the package is pushed for review but is not counted
toward the new 100. The Baxter case m = 3 remains unresolved here.
The initial parameter-4 values are established OEIS A005362 data;
their numerical discovery is not claimed.
