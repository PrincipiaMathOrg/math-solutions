# MathDB 360955: unimodality for hedgehog trees

**Complete mathematical proof; final-source audit pending. Zero new campaign credit.**

For every star with leaf delays in `{1,2}`, the plucking polynomial is unimodal. More generally, `A(q)[m]_q!` is unimodal whenever A has nonnegative coefficients and degree at most m. The proof combines the source's initial factor and comparison with an elementary moving-sum lemma, proved in full.

The 2026 published chapter, [DOI 10.1090/conm/834/16686](https://doi.org/10.1090/conm/834/16686), could not be retrieved: the publisher endpoints returned HTTP 403. Its final scope remains unchecked. The complete thirteen-page current preprint was read, but this does not replace the required final-source comparison. The proof is published now under the standing instruction to push each completed solve, while campaign eligibility remains pending.

- [Full proof and Tasks 1–5](solution.tex), [compiled PDF](solution.pdf)
- [Proof audit](proof-audit.md), [literature audit](literature-audit.md)
- [Exact verification script](verify.py), [results](verification-results.json)
- [Source check](source-check.json), [verification manifest](verification-manifest.json)
- [Original MathDB entry](https://mathdb.com/p/360955)

Run `python verify.py`; it uses only the Python standard library. All four groups passed: 1,023 recursive factorization cases, 29,780 polynomial examples, 18,152 moving-sum checks, and two known examples outside the delay restriction. These finite checks supplement the all-size proof. Review was by the authoring agent only.

The four proposed followups concern delays `{1,2,3}`, strict unimodality and peak location, the largest degree uniformly smoothed by a q-factorial, and extensions to other rooted trees. They are not claimed as solved.
