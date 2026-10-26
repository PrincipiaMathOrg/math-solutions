# MathDB 356220

**Complete counterexample and corrected inverse. Campaign credit: 0, pending the final journal-source check.**

The conjectured partition sum gives **613766** at (n,k)=(58,1); exact matrix inversion gives **613767**. The manuscript proves a corrected formula for every inverse entry using ordinary Möbius inversion on the odd divisors of 2n+1, and extends it to arbitrary formal prefactors with constant coefficient one.

- [Manuscript](solution.tex) and [compiled PDF](solution.pdf)
- [Proof audit](proof-audit.md) and [literature audit](literature-audit.md)
- [Exact verifier](verify.py), [certificate](exact-certificate.json), and [verification manifest](verification-manifest.json)
- [Source check](source-check.json), [search audit](search-audit.json), and [attempt record](attempt-record.json)
- Dated [initial](mathdb-initial-check.json) and [final](mathdb-final-check.json) MathDB checks

Run python verify.py in this directory. Twelve exact check groups pass, including all 1,711 lower-triangular entries through row 58 for each of three prefactors and a direct matrix-product check. These finite checks supplement the general proof.

Task 1 is the refutation and corrected all-entry theorem. Exactly four proposed follow-up Tasks 2–5 appear in the manuscript.

The complete 2022 thesis and available 24-page arXiv preprint were inspected. The related 29-page final journal article was inaccessible; the downloaded one-page file contains a browser error. No campaign credit is claimed until that scope is checked. Verification is by the authoring agent, without independent mathematical review or proof-assistant verification.
