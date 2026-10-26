# MathDB 339077

**Complete counterexample to the intended three-shift divisibility claim.**

- [MathDB problem](https://mathdb.com/p/339077)
- [LaTeX proof and four followups](solution.tex) · [PDF](solution.pdf)
- [Exact verifier](verify.py) · [Results](verification-results.json)
- [Proof audit](proof-audit.md) · [Literature audit](literature-audit.md)

The size-five Hankel determinant has value **2 at q = −1**, but its
conjectured divisor is 1 + q³, which vanishes there. No monomial
normalization can remove this contradiction. The proof uses twelve
integers from the defining recurrence and elementary row operations.
It resolves the source's f/g notation as intended.

Four exact verification groups cover the recurrence, two integer
determinant calculations, the full polynomial determinant and remainder,
and a separate weighted-walk calculation. Run `python verify.py` with
python-flint installed.

**Pending source audit; zero new campaign credit.** The complete
68-page current preprint was read, but the journal final remains
unavailable for a corrections check. The separate shift-two package
[339076](../339076/README.md) does not contain this counterexample.
Review is by the authoring agent, without independent peer review.

Tasks 2–5 ask about corrected divisors, complete three-shift evaluations,
roots of unity, and higher shifts. They carry no additional credit.
