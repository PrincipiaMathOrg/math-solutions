# Literature and status audit for MathDB #355738

Checked 19 August 2026.

## Database statement and live identity check

MathDB #355738 is titled *Decomposition conjecture for normalized
gauge-norm Hardy spaces*. Its live API record still reported status open
and post type open_problem, with no edit, comment, model attempt, or human
solve. The normalized live-statement SHA-256 was

    314a3c5c54982600d98ba780e640d4e32af17231c58a2d0038a9cbb193129975

exactly matching the immutable campaign ledger entry.

## Primary source and version scope

The source is Apoorva Singh and Niteesh Sahni, *Multiplication by finite
Blaschke factors on a general class of Hardy spaces*,
[arXiv:2208.08385](https://arxiv.org/abs/2208.08385). ArXiv records v1 on
17 August 2022 and v2 on 18 August 2022. The source text was compared
directly: Conjecture 4.4 has the same wording in both versions; their only
textual difference is a one-word repair in the abstract.

The definitions immediately preceding the conjecture say that a normalized
gauge norm satisfies \(\alpha(1)=1\),
\(\alpha(|f|)=\alpha(f)\), and
\(\alpha(f)\geq\lVert f\rVert _1\), and define continuity through
\(\alpha(\mathbf1_E)\to0\) as \(m(E)\to0\). The paper defines
\(H^\alpha=[H^\infty]_\alpha\) and
\(M_\alpha(z^n)=[H^\infty(z^n)]_\alpha\). Lemma 4.2 proves the residue-class
decomposition under the stronger rotational-symmetry hypothesis. The next
paragraph explicitly says that the authors do not know whether it remains
valid for a general continuous \(\lVert\cdot\rVert _1\)-dominating normalized
gauge norm, and states that assertion as Conjecture 4.4.

The paper was published as article 57 in *Advances in Operator Theory* 7
(2022), DOI
[10.1007/s43036-022-00222-0](https://link.springer.com/article/10.1007/s43036-022-00222-0).
The publisher records acceptance on 7 September and publication on
27 September 2022. The openly available arXiv body is therefore the exact
public statement used for the audit; no claim is made that every line of the
subscription version of record is identical.

## Forward search and distinction from later work

Exact Conjecture-4.4, displayed-formula, title, author/title, DOI, and
weighted-gauge searches located no public proof or counterexample for the
general-gauge statement through 19 August 2026. Crossref and OpenAlex each
reported one resolved forward citation. That citation is the same authors'
[arXiv:2303.17994](https://arxiv.org/abs/2303.17994), which works throughout
with **rotationally symmetric** norms and does not settle the general-gauge
conjecture.

A 2026 paper on weighted Hardy spaces studies a Beurling theorem and
inner--outer factorization for a different weighted symmetric-gauge setup;
its public abstract does not state the residue-class conjecture or the
counterexample given here. Broader searches likewise returned the original
paper and classical rotationally symmetric decompositions, not an explicit
resolution of Conjecture 4.4.

## Status conclusion

No prior explicit public resolution was located. The dossier gives a direct
counterexample for \(n=2\): a continuous weighted maximum gauge norm and an
\(H^\alpha\) function whose even residue component is not in \(L^\alpha\).
Publication priority is not claimed.
