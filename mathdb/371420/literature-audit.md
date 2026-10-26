# Literature and status audit for MathDB #371420

Checked 20 August 2026.

## Database identity

MathDB #371420 is titled *Katok's exponential periodic-orbit growth
conjecture for surface diffeomorphisms*.  A fresh API query returned
`status=open` and `post_type=open_problem`, with no edit, moderator edit,
progress record, comment, reply, model attempt, human solve, or alternate
formulation.  Its UUID is
`f11f8bb8-5a9a-4374-bd7b-d7e7c521cb6b`.  The normalized live-statement
SHA-256 is

    9d48878140e003e6d321020eee90e00d4fb79dd0406e1d98cec73fad659a6c64

which exactly matches the immutable batch and deduplication-ledger entry.
The UUID and problem number each occur once in the 813-record ledger, and
the record has no origin links.

## Cited primary source

MathDB cites Gang Liao and Jing Wei,
[*Metric entropy and homoclinic growth
rate*](https://arxiv.org/abs/2511.08227), arXiv:2511.08227v1, submitted
11 November 2025.  The arXiv record still has only v1 on the audit date.

The paper defines

\[
P_n(f)=\{x\in M:x=f^n(x)\}
\]

and its Conjecture 2 asks whether

\[
\limsup_{n\to\infty}
\frac{\#P_n(f)}{e^{n h_{\operatorname{top}}(f)}}>0
\]

for any (i) \(C^r\), \(r>1\), or (ii) \(C^\infty\) diffeomorphism of a
compact surface.  The conjecture as displayed contains no assumption that
the topological entropy is positive.  MathDB reproduces that quantifier and
formula accurately.

Crossref registered the journal DOI
[10.1016/j.jmaa.2026.131004](https://doi.org/10.1016/j.jmaa.2026.131004)
on 12 August 2026 and assigns the article to *Journal of Mathematical
Analysis and Applications* **566** (2027), no. 1, article 131004.  The
version-of-record body was not publicly readable in this audit, so no claim
about whether its wording has been silently repaired is made.  The cited
and publicly inspectable arXiv version remains unchanged.

## Original problem and the intended positive-entropy scope

The displayed question traces to Problem 7.4 of Anatole Katok,
[*Fifty years of entropy in dynamics:
1958--2007*](https://doi.org/10.3934/jmd.2007.1.545), *Journal of Modern
Dynamics* **1** (2007), 545--596.  Its display likewise says "for any"
surface diffeomorphism without writing a positive-entropy hypothesis.

The surrounding mathematical record makes the natural repair clear.  The
paragraph immediately before Conjecture 2 in the 2025 source recalls
Katok's logarithmic lower bound for a surface diffeomorphism **with positive
topological entropy**.  More decisively, Omri Sarig,
[*Symbolic dynamics for surface diffeomorphisms with positive topological
entropy*](https://arxiv.org/abs/1105.1650), arXiv:1105.1650v3 and *Journal
of the AMS* **26** (2013), 341--426, states the conjecture with
\(h_{\operatorname{top}}(f)>0\) in its abstract and proves the
\(C^\infty\) case.  The 2025 source also cites Sarig as proving its
Conjecture 2 for \(C^\infty\) maps, or more generally when a measure of
maximal entropy exists.

Thus the unqualified display and the standard positive-entropy conjecture
must not be conflated.  An irrational torus translation refutes the former
but is outside the latter.

## Forward and correction search

Exact-title, arXiv-identifier, DOI, conjecture-number, formula,
positive-entropy, zero-entropy, aperiodic-translation, correction,
corrigendum, proof, and counterexample searches located no public correction
of the arXiv statement and no explicit discussion of its missing entropy
hypothesis.  Crossref and OpenAlex each reported zero indexed citations to
the newly registered journal article on the audit date.  The arXiv record
remains at v1.

This is a scope and discoverability audit, not a claim that the elementary
observation was unknown.  Publication priority is not claimed.

## Status conclusion

The live MathDB record and the cited public source state an unqualified
universal claim.  That literal claim is false: a smooth irrational
translation of \(\mathbb T^2\) has no periodic points and entropy zero, so
the proposed limsup is zero.  The result does not address the standard
positive-entropy version; its \(C^\infty\) branch is already Sarig's theorem,
while the general finite-smoothness branch remains outside this dossier.
