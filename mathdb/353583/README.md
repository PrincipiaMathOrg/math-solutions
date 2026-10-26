# MathDB 353583

**Complete counterexample to the stated conjecture; campaign eligibility pending.**

- [MathDB problem](https://mathdb.com/p/353583)
- [Proof and four followups](solution.tex) · [PDF](solution.pdf)
- [Exact verifier](verify.py) · [Results](verification-results.json)
- [Proof audit](proof-audit.md) · [Literature audit](literature-audit.md)

For every integer $u\geq0$,

$$
S_{\{1,2,6\},2}(12u+30)
=-\frac{(u+3)(52u^2+147u+35)}3<0.
$$

These even arguments are unbounded. Thus the proposed eventual
nonnegativity fails for the factorial set $U_3$ and weight $k=2$.
The proof pairs multiplicities of 6 and evaluates alternating squares
over multiplicities of 2. It establishes the infinite progression
exactly; the first counterexample on it is $S_{U_3,2}(30)=-35$.

Four exact verification groups passed: partition enumeration versus
dynamic programming through 240, generating-function coefficients
through 240, both alternating-square identities, and the symbolic
infinite-progression formula with 101 additional enumeration checks.
Run `python verify.py` with SymPy installed.

The entire current preprint and the entire later composition paper
were read. **The final 2023 partition article remains inaccessible
in full.** The university repository contains only a bibliographic
record for it. Until its final conjecture and any corrections can be
checked, this result carries **zero new campaign credit**.

Current MathDB claim fields and the checked public claim indexes
contain no target full claim. These bounded checks do not settle the
missing final-source comparison. Review was by the authoring agent,
without independent peer review or proof-assistant certification.

Tasks 2–5 give four followups and carry no additional credit.
