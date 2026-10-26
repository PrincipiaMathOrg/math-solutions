# MathDB 339076

Complete evaluation of the two-shifted q-Motzkin Hankel determinant for
every size. A short condensation proof derives the answer from Cigler's
credited zero- and one-shift evaluations. It determines the monomial
exponent and all coefficients, including the constant term omitted from
one branch of the printed conjecture.

**Eligibility pending; zero new campaign credit.** The complete final
journal article was unavailable, and the current preprint has only been
inspected selectively. The result is published for review with these
limitations explicit.

- [LaTeX: Task 1 and four proposed follow-up Tasks 2--5](solution.tex)
- [Compiled PDF](solution.pdf)
- [Exact verifier](verify_determinants.py) and [certificate](exact-certificate.json)
- [Proof audit](proof-audit.md)
- [Literature and eligibility audit](literature-audit.md)
- [Source records](source-check.json)
- [Verification manifest](verification-manifest.json)

Run with Python and python-flint:

    python verify_determinants.py
    tectonic solution.tex

The audit is by the authoring agent. Independent peer review and global
priority are not claimed. The separate all-even-shifts conjecture,
MathDB 339078, remains unsolved here.
