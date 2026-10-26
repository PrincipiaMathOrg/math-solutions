# MathDB 356321: positive Bernstein coefficients of Bernoulli densities

**Complete intended theorem; zero new credit pending the journal-source check.** Dated 21 September 2026.

Every coefficient of the degree-\(n\) Bernstein expansion of \(1-2^n B_n(x)/n!\) is strictly positive for \(n\ge2\). For \(n=1\), the coefficients are exactly \((2,0)\). Thus the all-degree nonnegative version holds, with the boundary exception stated precisely.

The proof bounds every coefficient's distance from one by \(4e^{2\pi}\pi^{-n}\), which is less than one for \(n\ge9\). A complete exact table certifies all smaller degrees.

- [Full proof and four follow-ups](solution.tex); [compiled PDF](solution.pdf).
- [Proof audit](proof-audit.md); [literature audit](literature-audit.md).
- [Standard-library verifier](verify.py); [exact results](verification-results.json).
- [Dated attempt](attempt-record.json); [file manifest](verification-manifest.json).

The current [primary preprint](https://arxiv.org/abs/2210.02027) has been read completely and refreshed byte-identically. The identified [journal final](https://doi.org/10.1017/S0963548323000421) remains unread, so the campaign count is unchanged. The simple \(n=1\) wording correction earns no credit.

Four exact verification groups passed: polynomial reconstruction through degree 30, all eight base cases, 5,106 additional positive coefficients through degree 100, and normalization/reflection through degree 80. These supplement the analytic all-degree proof. Review is by the authoring agent only.

Reproduce with Python's standard library and Tectonic:

    python verify.py
    tectonic --keep-logs solution.tex

Target: [MathDB 356321](https://mathdb.com/p/356321), source Conjecture 3.7.
