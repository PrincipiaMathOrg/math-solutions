# MathDB 360642: Hilbert coefficients of the square of the maximal ideal

**Full intended formula proved; zero new campaign credit because classical Gegenbauer identities already imply it.**

For I=(x1,...,xn)^2, the coefficient e_j is 2^(n-2j) binomial(n-j,j) for 0<=j<=floor(n/2), and zero afterwards. The package gives an elementary generating-function proof and a sign-reversing involution valid in every dimension. The displayed source identity has a separate upper-index typo, explicitly corrected.

[LaTeX](solution.tex) · [three-page PDF](solution.pdf) · [proof audit](proof-audit.md) · [literature audit](literature-audit.md) · [exact checks](verification-results.json)

Task 1 is the complete intended coefficient theorem. Tasks 2-5 propose higher maximal-ideal powers, a cancellation interpretation for their coefficients, Hilbert series of graph ideals with all squares, and the signs of their Hilbert coefficients. They are proposals only.

Run `python verify.py` for three supplementary exact groups. No independent peer review or proof assistant is claimed. The campaign remains at 94 new solutions.
