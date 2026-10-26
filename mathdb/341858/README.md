# MathDB 341858: the two-variable Bernoulli determinant

[MathDB problem](https://mathdb.com/p/341858) · [Full evaluation](solution.tex) · [PDF](solution.pdf)

The intended factorization holds for every order after changing the lower product index from 0 to 1. A self-contained proof uses discrete uniform moments, rank deficiencies at positive and negative integers, and the Hilbert determinant as leading coefficient. The literal printed formula is already false at order 1.

**Zero new-solution credit.** Dominici's published Hahn determinant theorem specializes to the corrected formula after translation and polynomial continuation. The manuscript gives this connection explicitly and credits the existing evaluation.

Task 1 contains the full evaluation. Exactly four proposed Tasks 2–5 concern shifted minors, nullspaces at integer degeneracies, more variables, and deformed weights. They receive no solved credit.

Run the exact checks with Python and SymPy:

    python problems/341858/verify.py

See the [proof audit](proof-audit.md), [literature audit](literature-audit.md), and dated evidence. The full published source and preprint were read; the relevant first seven pages of Dominici were inspected. Authoring-agent verification only, with no independent review.
