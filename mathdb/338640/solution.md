# MathDB #338640: a smaller bicommutative system on \([15]\)

## Result and status

The conjecture is **false**. At the first allowed parameter \(k=2\), the
source family has size \(1870\), whereas certificate.json gives a
7-bicommutative system of size \(1173\) in \(\mathcal P_{15}(7)\).

This is a self-contained exact counterexample, but it is **not a new
resolution**. Ahmed Ibrahim Al-Herz's 2012 master's thesis already reported
a still smaller independent dominating set of size \(1097\) in the same odd
graph \(O_8=KG(15,7)\). This dossier is therefore recorded as a stale
correction and receives no campaign-solution credit.

## The finite instance

An \(s\)-bicommutative system \(T\subseteq\mathcal P_n(s)\) is, in the
terminology of Bovdi and Leung, a family satisfying

1. \(A\cap B\ne\varnothing\) for all \(A,B\in T\); and
2. for every \(s\)-set \(S\notin T\), some \(A\in T\) is disjoint from \(S\).

Thus \(T\) is exactly a maximal intersecting \(s\)-uniform family. Equivalently,
it is an independent dominating set in the Kneser graph \(KG(n,s)\).

Take \(k=2\), which is within the conjecture's range. Then

\[
n=4k+7=15,\qquad m=2k+3=7.
\]

The source computes

\[
\begin{aligned}
|\mathcal A_m|
&=7\binom{4k}{2k}
  +\binom72\binom{4k}{2k+1}
  +\binom71\binom{4k}{2k+2}
  +\binom{4k}{2k+3}\\
&=7\binom84+\binom72\binom85
  +7\binom86+\binom87\\
&=490+1176+196+8=1870.
\end{aligned}
\tag{1}
\]

The verifier independently reconstructs these four classes, including the
seven Fano triples on \(\{9,\ldots,15\}\), rather than trusting the total in
the certificate.

## Explicit counterexample

The file certificate.json contains \(1173\) distinct integers. A mask

\[
a=\sum_{i\in A}2^{i-1}
\]

encodes the subset \(A\subseteq[15]\). Consequently the certificate is a
literal, finite list of 1173 seven-subsets; the discovery algorithm is not
part of the proof.

Let \(\mathcal F\) be that listed family. The exact verifier establishes:

- every mask lies in \([1,2^{15}-1]\) and has exactly seven set bits;
- all 1173 masks are distinct;
- for every one of the \(\binom{1173}{2}=687378\) pairs \(A,B\in\mathcal F\),
  \(A\mathbin{\&}B\ne0\), so \(A\cap B\ne\varnothing\);
- for every one of the \(6435-1173=5262\) seven-sets \(S\notin\mathcal F\),
  at least one listed mask \(A\) satisfies \(A\mathbin{\&}S=0\).

The last check is exhaustive. A seven-set in \([15]\) has an eight-element
complement, and its disjoint seven-sets are exactly the eight masks obtained
by deleting one element from that complement. No search or numerical
tolerance is involved in the verification.

The first two bullets make \(\mathcal F\) 7-uniform, the third makes it
intersecting, and the fourth makes it inclusion-maximal among intersecting
7-uniform families. Hence \(\mathcal F\) is a 7-bicommutative system. Since

\[
|\mathcal F|=1173<1870=|\mathcal A_7|,
\]

\(\mathcal A_7\) is not minimum, refuting the universal conjecture.

## Discovery and exact audit

The certificate was found by a deterministic sampled-greedy search for a
maximal independent set in \(KG(15,7)\), using seed 338640, 42 trials, and
192 sampled undominated candidates per step. Trial 41 (zero-based) produced
the archived family. Again, this history is informational: the explicit
list plus exhaustive checks are the proof.

Run

~~~text
python verify_counterexample.py
python -OO verify_counterexample.py
~~~

from this directory. Both runs use only the Python standard library and
produce byte-identical output. Besides checking the counterexample, they
reconstruct the source's 1870-set family and verify its pairwise-intersection
and maximality conditions over the same complete universe. The pinned hashes
are

~~~text
certificate.json         a66d12048d963de70180540eff002c7f3a97d6dce080c7fcd4ee78b7ecd523b7
verify_counterexample.py 591585970ae5579c2b9b8371bc549c3af761861987b07b76c44d9e88be126985
~~~

The archived transcript is in verification.out.

## Scope

This refutes only the claim that the particular family \(\mathcal A_m\) is
minimum for every \(k\ge2\). It does not determine the independent domination
number of \(KG(15,7)\), and \(1173\) is not claimed to be best; the prior 2012
computation already gives the stronger upper bound \(1097\).
