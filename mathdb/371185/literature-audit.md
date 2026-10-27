# Literature and status audit for MathDB #371185

Checked 19 August 2026.

## Database identity

MathDB #371185 is titled *Bounded discrepancies between tie-breaking
conventions*.  A live API check still reported `status=open` and
`post_type=open_problem`, with no edit, comment, model attempt, or human
solve.  The normalized live-statement SHA-256 was

    fe688f55a0fbe594046b8e969daa2855a9e874daebafe88dd9118ad631ec7d40

which exactly matches the immutable ledger entry.

## Primary source and version scope

The source is Anjali Bhagat, Tanmay Kulkarni, Urban Larsson, and Divya
Murali, *Tie-breaking in self interest cumulative subtraction games*,
[arXiv:2510.24280](https://arxiv.org/abs/2510.24280).  ArXiv records v1 on
28 October 2025 and v2 on 20 January 2026.  Both source archives were
checked directly.  The conjecture appears in both versions, with only a
punctuation change:

> For any S and any two tie-breaking conventions, the discrepancies are
> bounded.

The paper defines the four friendly/antagonistic profiles by backward
induction.  At each position the mover first maximizes their own
cumulation and uses the declared convention only among indifferent
actions.  Version 2 reports finite experiments for heap sizes through 300
immediately before the conjecture.  It neither states nor proves a
uniform bound.  A cited manuscript by Kulkarni and Larsson,
*Discrepancies in various 2-player self-interest cumulative subtraction
games*, is marked “in preparation” and is represented only by links to
interactive figures.

## Forward and exact-result search

Exact-conjecture, exact-title, author/title, “discrepancies are bounded,”
subtraction-game, almost-constant-sum, and follow-up-manuscript searches
located no public proof of this conjecture through the audit date.  The
available scholarly records expose only the two arXiv versions and no
forward citation resolving the question.  Searches for the in-preparation
title returned its bibliography entry, not a manuscript.

The equilibrium lemma used in the solution is elementary and may be
viewed as a standard stability observation for nearly constant-sum games.
The audit makes no priority claim for that general observation.  What was
not located is its explicit application to this conjecture or the sharp
(\min(S)-1) bound.

## Scope conclusion

The solution proves the exact MathDB/source conjecture, and more: for
every heap size and every two deterministic conventions, each player's
absolute discrepancy is at most (\min(S)-1).  It does not claim the
paper's separate conjecture that FvF utilities always dominate AvA
utilities for arbitrary (S).  No prior explicit public resolution was
located; publication priority is not claimed.

