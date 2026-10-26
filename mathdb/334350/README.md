# MathDB 334350: the generalized power-sum identity

[MathDB problem](https://mathdb.com/p/334350) · [Full proof](solution.tex) · [PDF](solution.pdf)

**Campaign status: full mathematical proof, zero new credit pending the source audit.** One relevant later paper is accessible only as an abstract and first-page preview. The campaign's access-ambiguity rule prevents clearing this entry until that gap is resolved.

Svinin's conjectured equality between the two generalized sums holds for every allowed n, j, and k. More generally, any odd function on the integers can replace the odd power. The proof also establishes strict positivity of every coefficient after cancellation of opposite arguments.

The argument counts the gaps of weakly increasing tuples, evaluates a finite geometric sum, and applies a truncated negative-binomial identity. It proves an identity of entire Laurent polynomials, so all odd functions follow at once.

Task 1 contains the complete proof. Exactly four proposed Tasks 2–5 concern a direct combinatorial cancellation, even functions, the positive coefficient distribution, and recurrences for normalized sums. They receive no additional solved credit.

Run the standard-library exact verifier:

    python problems/334350/verify.py

It compares direct tuple enumeration with order-statistic counts and independent polynomial convolutions, then checks odd functions and the coefficient lemma using exact rational arithmetic. The finite checks supplement the proof for all parameters.

The full current preprint and the full published article were read. The [proof audit](proof-audit.md), [literature audit](literature-audit.md), and dated evidence records identify the outstanding related-source check. Verification is by the authoring agent only.
