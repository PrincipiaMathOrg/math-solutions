# Literature and status audit for MathDB #338641

Checked 19 August 2026.

## Database statement and live identity check

MathDB #338641 is titled *Asymptotic size conjecture for the constructed
cone*.  On 19 August 2026 its API record still reported
`status=open` and `post_type=open_problem`.  The live normalized statement
hash was

`44b1299c66eaea15c8c39d73b44f6470220d7f3d22123aea4bd68bc577009af9`,

which exactly matched the immutable campaign ledger entry.

## Primary statement

The source is Victor A. Bovdi and Ho-Hon Leung, *Maximal commutative
subalgebras of a Grassmann algebra*,
[arXiv:1803.03457v1](https://arxiv.org/abs/1803.03457), submitted
9 March 2018.  ArXiv lists only that version.  The exact public body is
available as [arXiv HTML](https://arxiv.org/html/1803.03457v1).

Section 4 gives the complete layer description and counts for
\(\operatorname{Cone}\): the three exceptional layers appear immediately
before the full odd upper tail.  The paper reports numerical ratios
\(s_2=0.97437\) and \(s_{249}=0.99763\), says the tested ratios are below
one and increasing, and states as Conjecture 3 that

\[
\lim_{k\to\infty}
\frac{|\operatorname{Cone}|}{2^{4k+5}}=1.
\]

There is one harmless display typo in the source's total-size line: the
summand is printed as \(|\mathcal U_{2k+7}|\) while the index is \(j\).
The immediately preceding layer definition and count correctly give
\(|\mathcal U_j|=\binom{4k+7}{j}\) for every odd \(j\ge2k+7\), which is
the reading used here.

The paper was published in *Journal of Algebra and Its Applications*
18(7), article 1950139 (2019), DOI
[10.1142/S0219498819501391](https://doi.org/10.1142/S0219498819501391).
The version-of-record body was not openly accessible during this audit, so
no assertion is made that its wording is identical to the arXiv body.

## Distinction from the known follow-up

Ho-Hon Leung's follow-up,
[arXiv:1810.08781v1](https://arxiv.org/abs/1810.08781), says explicitly
that it proves Conjecture 5 of the Bovdi--Leung paper, an inequality for a
different construction when \(n=4k+1\).  It does not address Conjecture 3
or the cone ratio.  The neighboring Conjecture 4 for the system
\(\mathcal D\) is also a distinct statement.

## Resolution and prior-art search

Exact-title, author/title, `s_249=0.99763`, Conjecture-3, and closed-form
searches located no later public proof or counterexample for this exact
limit through 19 August 2026.  Search results returned the original paper
but no source containing the identity proved in this dossier.

The proof uses only the source's displayed layer counts, two elementary
Vandermonde expansions, and an alternating binomial tail.  It yields the
exact formula

\[
|\operatorname{Cone}|=2^{4k+5}-3\binom{4k}{2k},
\]

which directly proves the conjecture and all of the source's finite
strict inequalities.

**Status conclusion.** No explicit prior public resolution was located.
This dossier supplies an apparently first explicit proof found in the
search, but publication priority is not claimed: the argument is a short
consequence of exact formulas already present in the source.
