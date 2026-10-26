# MathDB 330839: negative real zeros from index seven onward

**Complete disproof of the intended original conjunction; zero new campaign credit pending a related-paper claim audit.**

An exact sign certificate at n=7 gives two real roots in (-1,0). A negative-minimum argument propagates this to every n>=7, and reciprocity gives two more roots below -1. This is compatible with the known Hurwitz stability of the sequence.

[LaTeX](solution.tex) · [two-page PDF](solution.pdf) · [proof audit](proof-audit.md) · [literature audit](literature-audit.md) · [verification](verification-results.json)

- **Task 1:** Refute the original nonreal-zero and separation conjunction.
- **Task 2:** Determine the exact real-root count at every index.
- **Task 3:** Determine a limiting proportion of real roots.
- **Task 4:** Classify coordinate interlacing of the nonreal pairs.
- **Task 5:** Find asymptotics for the roots nearest zero and their reciprocals.

Tasks 2-5 are proposals. Run `python verify.py` with SymPy. Three exact groups passed, including independent enumeration of 135135 dual Stirling permutations. No independent peer review or proof assistant is claimed.
