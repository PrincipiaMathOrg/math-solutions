# Literature and status audit for MathDB #320644

Checked through: 2026-08-18.

## Primary formulation

Jonathan Sondow and Kieren MacMillan, *Reducing the Erdos--Moser equation
`1^n+2^n+...+k^n=(k+1)^n` modulo `k` and `k^2`*, states the assertion as
Conjecture 2:

\[
S_n(k)\equiv(k+1)^n\pmod{k^2},\quad p\mid k
\quad\Longrightarrow\quad
S_n(k)\equiv\frac{k}{p}S_n(p)\pmod{p^3}.
\]

- Abstract and submission history: https://arxiv.org/abs/1011.2154
- Full text and Section 4: https://arxiv.org/html/1011.2154#S4
- Journal publication: *Integers* 11 (2011), Article A34
- DOI: https://doi.org/10.1515/integ.2011.058

The arXiv submission history contains only v1, submitted 9 November 2010.
The source illustrates the conjecture with `(n,k)=(12,42)` and
`p in {2,3,7}`.  Its subsequent observation concerning all
\(n\equiv0\pmod6\) for `k=42` is an example-specific remark, not
part of Conjecture 2.  MathDB's statement is faithful to the conjecture.

## Source ingredients

The source's Theorem 2 classifies the solutions of the premise modulo
`k^2` using Wilson quotients.  The proof in this dossier needs even less:
reducing the premise modulo each `p|k` directly shows that `p-1|n` and
\(k/p\equiv-1\pmod p\).  The only other imported fact is the
standard finite-field power-sum identity.

## Forward-citation and exact-formula search

The DOI record exposes five linked forward citations.  The accessible
primary texts were inspected, including:

- Pieter Moree (2013), https://doi.org/10.1216/RMJ-2013-43-5-1707
- Jonathan Sondow (2014), https://arxiv.org/abs/1110.3113
- Grau--Oller-Marcen--Sondow (2015), https://arxiv.org/abs/1309.7941
- Sondow--MacMillan, https://arxiv.org/abs/1812.06566
- the 2024 Erdos--Moser survey, https://arxiv.org/abs/2306.05168

The related congruence paper https://arxiv.org/abs/1211.4570 was also
checked.  None of these texts states a proof or counterexample to Conjecture
2; several cite the source only as general Erdos--Moser background.

Exact searches covered the paper title and arXiv identifier, `Conjecture 2`
with the author names and `supercongruence`, and formula variants containing
`S_n(k)`, `k/p`, `S_n(p)`, and `p^3`.  No later claimed resolution was
located.

## Status conclusion

No published or arXiv proof or counterexample was located after the version,
exact-phrase, exact-formula, and forward-citation audit.  The defensible
conclusion is therefore: **the conjecture was apparently open in the indexed
literature through 2026-08-18**.  This is a search conclusion, not a claim
that no unpublished or unindexed proof exists.

The proof in this dossier appears not to occur in the audited citation chain.
Any novelty or priority claim should nevertheless remain cautious.
