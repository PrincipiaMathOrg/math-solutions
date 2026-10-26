# MathDB 323219: integrality of the alpha-triangle

**Complete mathematical proof; final-source audit pending. Zero new campaign credit.**

For every m, the polynomial `2^m m! a_(m+r+1,r)` has integer coefficients. More strongly, its expansion in falling factorials has nonnegative integer coefficients. Each reduced diagram's coordinate symmetry group has order dividing `2^m m!`: its action on the m added nodes has a kernel contained in independent swaps of isolated quadratic edges. Orbit counting proves the conjecture for all m.

The full 36-page preprint was read. The [2013 published version](https://doi.org/10.1016/j.jcta.2012.11.005) could not be retrieved in full, so its final scope remains unchecked. This proof is pushed under the standing instruction to publish completed solves, with eligibility pending.

- [Full proof and Tasks 1–5](solution.tex), [compiled PDF](solution.pdf)
- [Proof audit](proof-audit.md), [literature audit](literature-audit.md)
- [Exact verifier](verify.py), [results](verification-results.json)
- [Source check](source-check.json), [verification manifest](verification-manifest.json)
- [MathDB entry](https://mathdb.com/p/323219)

Run `python verify.py` using the Python standard library. All four groups passed, including complete checks of 87 reduced orbits and 40 comparisons with independently enumerated counts. Finite checks supplement the general proof. Review was by the authoring agent only.

The four followups concern the alpha–beta decomposition, sharper denominators for restricted families, weighted refinements, and computation by reduced orbits. They remain proposed directions.
