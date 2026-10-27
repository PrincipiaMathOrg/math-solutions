# Literature audit for MathDB #363496

Audit date: 2026-08-18.

## Primary source and exact statement

The primary source is Oleksiy Dovgoshey, *Ultrametric-preserving functions as monoid endomorphisms*:

- [arXiv record and version history](https://arxiv.org/abs/2406.07166)
- [current arXiv text, v2](https://arxiv.org/html/2406.07166)
- [arXiv v1](https://arxiv.org/html/2406.07166v1)

The paper was submitted as v1 on 2024-06-11 and revised to v2 on 2024-06-12.  As of the audit date, v2 is the latest arXiv version.  Conjecture 3.13 is present in both versions.  In the notation of the paper, for

\[
\mathbf X=\{(\mathbb R^+,g\circ d^+):g\in\mathbf A\},
\]

it asserts that, if the identity belongs to \(\mathbf A\subseteq\mathbf P_{\mathbf{PU}}\), then

\[
\overline R^{\,1_{\mathbf P_{\mathbf{PU}}}}=\mathbf P_{\mathbf X}.
\]

Here \(d^+(p,q)=0\) for \(p=q\) and \(d^+(p,q)=\max\{p,q\}\) otherwise; Proposition 2.2 identifies \(\mathbf P_{\mathbf{PU}}\) with the increasing functions \(f:\mathbb R^+\to\mathbb R^+\) satisfying \(f(0)=0\).

## Publication record

The article appeared in *Ukrains'kyi Matematychnyi Visnyk* 21(3) (2024), 331--348, DOI [10.37069/1810-3200-2024-21-3-3](https://doi.org/10.37069/1810-3200-2024-21-3-3).  Its English translation appeared in *Journal of Mathematical Sciences* 285(5) (2024), 666--680, DOI [10.1007/s10958-024-07464-8](https://doi.org/10.1007/s10958-024-07464-8).  The [University of Turku publication record](https://research.utu.fi/converis/portal/detail/Publication/477893763?lang=en_US) confirms the journal, volume, pages, DOI, and translation provenance.

## Notation caveat: two defensible readings

There is an internal omission in the source.  Lemma 3.10 defines \(R_{\mathbf A}\) to consist of right ideals \(R\) of \([\mathbf A]\) that also satisfy \(R\subseteq\mathbf A\).  Proposition 3.12 and Conjecture 3.13 instead say merely "all right ideals of \([\mathbf A]\)," although the proof of Proposition 3.12 explicitly invokes the omitted containment via equation (3.31).  Thus the intended reading almost certainly retains \(R\subseteq\mathbf A\), while the literal displayed wording does not.

The counterexample survives both readings.  Put

\[
I(x)=x,\qquad
u(x)=\begin{cases}0&x<2,\\1&x\ge2,\end{cases}\qquad
v(x)=\begin{cases}0&x=0,\\1&x>0,\end{cases}
\]

and \(\mathbf A=\{I,u,v\}\).  These functions are increasing and vanish at zero, so they lie in \(\mathbf P_{\mathbf{PU}}\), and \([\mathbf A]=\{I,u,v,z\}\), where \(z\) is the zero function.  Direct composition gives

\[
u^2=u\circ v=z,\qquad v\circ u=u,\qquad v^2=v.
\]

Surjectivity of \(d^+\) implies that membership in \(\mathbf P_{\mathbf X}\) is exactly the condition \(f\circ g\in\mathbf A\) for every \(g\in\mathbf A\).  Consequently

\[
\mathbf P_{\mathbf X}=\{I,v\}.
\]

Under the intended Lemma 3.10 reading, no nonempty right ideal of \([\mathbf A]\) is contained in \(\mathbf A\): right multiplication sends \(I\) to \(z\) using \(z\), sends \(u\) to \(z\) using \(u\), and sends \(v\) to \(z\) using \(z\).  Hence \(\overline R=\varnothing\) and \(\overline R^1=\{I\}\ne\mathbf P_{\mathbf X}\).  Under the literal reading, \([\mathbf A]\) itself is a right ideal, so \(\overline R=[\mathbf A]\ne\mathbf P_{\mathbf X}\).

## Current-status and novelty check

Targeted searches were made for the exact title together with `Conjecture 3.13`, `counterexample`, `right ideal`, `correction`, and `erratum`; for arXiv identifier `2406.07166`; and for both publication DOIs.  The arXiv record, journal/translation records, author publication record, and publicly indexed citing/related literature were checked.  No later arXiv version, erratum, correction, published proof, or published counterexample to Conjecture 3.13 was found through 2026-08-18.

Accordingly, the defensible wording is: **Conjecture 3.13 remained stated without a known public resolution in the latest source and publication records located in this audit; the finite-function counterexample above appears not to have been previously recorded in the searched public literature.**  This is a search-based novelty assessment, not a claim that no unindexed communication exists.
