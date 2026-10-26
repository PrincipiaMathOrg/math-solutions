# MathDB 325835: the tensor-tubal-norm conjecture

[MathDB problem](https://mathdb.com/p/325835) · [Full counterexample](solution.tex) · [PDF](solution.pdf)

**Complete counterexample; zero new campaign credit pending related-literature scope.** See [the literature audit](literature-audit.md) for the outstanding 2022/2026 singular-tube penalty checks.

Two explicit real `2 x 2 x 2` tensors have tensor-tubal functional value `sqrt(5/2)` each, while their sum has value `2 + sqrt(2) > sqrt(10)`. This disproves the triangle inequality and convexity, including on every norm ball about zero after scaling. Consequently the functional cannot be the conjectured convex relaxation of tubal rank.

The proof uses the standard sorted matrix SVD at each Fourier slice, as in the source algorithm, and gives explicit valid real t-SVD factors. It concerns the sum of Euclidean norms of singular tubes (TTN). The different tensor-nuclear-norm (TNN) in the source and later tensor-completion literature is unaffected.

The package includes the complete Task 1 result and exactly four proposed Tasks 2–5. Run `python verify.py` with SymPy installed. Three exact verification groups check the rational inputs, sorted singular spectra, real t-SVD factorizations, strict inequalities and scaling.

All nine pages of the current original preprint and all eight pages of the official CVF conference copy were read. The related arXiv conference version was compared in full. The later conference text omits the conjecture without giving a resolution. The separate IEEE-hosted PDF was inaccessible and is not claimed read; the official CVF copy and related arXiv version provide the conference text reviewed here. Dated initial/final MathDB and bounded claim-index checks accompany the proof. This is authoring-agent review, without independent peer review or proof-assistant certification.
