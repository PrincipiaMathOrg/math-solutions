# A sharp uniform bound for tie-breaking discrepancies

## Statement

Let (S\subseteq\mathbb N) be a nonempty subtraction set.  Starting
from a heap of size (h), two players alternate; a move (s\in S)
removes (s) stones and adds them to the mover's utility.  Play stops
when no move is possible.  A deterministic tie-breaking convention
selects among moves giving the current player the same maximum utility.

The source conjectures that, for fixed (S), the discrepancies between
the PSPE utilities produced by any two tie-breaking conventions are
bounded as (h) varies.  In fact, if

\[
m=\min S,
\]

then every player's discrepancy has absolute value at most (m-1).
This bound is independent of the heap size and of the conventions.

## An almost-constant-sum equilibrium lemma

We use the following elementary fact.

**Lemma.**  Consider a finite two-player game in which every terminal
outcome has utilities (u_1,u_2) satisfying

\[
C\leq u_1+u_2\leq C+R.
\tag{1}
\]

If (sigma=(\sigma_1,\sigma_2)) and
(	au=(\tau_1,\tau_2)) are two Nash equilibria, then

\[
|u_i(\sigma)-u_i(\tau)|\leq R
\qquad(i=1,2).
\tag{2}
\]

To prove the assertion for player 1, use the two best-response
inequalities

\[
u_1(\sigma_1,\sigma_2)
 \geq u_1(\tau_1,\sigma_2),
\qquad
u_2(\tau_1,\tau_2)
 \geq u_2(\tau_1,\sigma_2).
\]

Adding them and applying the lower bound in (1) to the crossed profile
((\tau_1,\sigma_2)) gives

\[
u_1(\sigma)+u_2(\tau)\geq C.
\tag{3}
\]

The upper bound in (1), now at (	au), gives
(u_2(\tau)\leq C+R-u_1(\tau)).  Substitution in (3) yields

\[
u_1(\tau)-u_1(\sigma)\leq R.
\]

Interchanging (sigma) and (	au) proves the reverse inequality.
The argument for player 2 is symmetric, proving the lemma.

## Application to cumulative subtraction

Fix a heap size (h).  This is a finite extensive-form game: every
move removes a positive number of stones.  A deterministic convention
resolves only indifference between moves that already maximize the
current player's own terminal utility.  Backward induction under any
such convention therefore produces a pure subgame-perfect equilibrium,
and hence a Nash equilibrium, of the same underlying self-interest
game.  Different conventions merely select potentially different
equilibria.

For every terminal play, let (r) be the number of stones left.  Play
can stop only when (r<m), while (r\geq0).  Every removed stone is
credited to exactly one player, so

\[
u_1+u_2=h-r,
\qquad
h-m+1\leq u_1+u_2\leq h.
\tag{4}
\]

Apply the lemma with (C=h-m+1) and (R=m-1).  If (X) and (Y)
are any two deterministic tie-breaking conventions, then

\[
\boxed{
  |u_i^X(h)-u_i^Y(h)|\leq m-1
}
\qquad(i=1,2).
\tag{5}
\]

The right-hand side depends only on (S), proving the conjecture.
The argument also covers an infinite subtraction set, because only the
finite set (S\cap\{1,\ldots,h\}) can occur in the game from (h).

## Sharpness

The universal constant in (5) cannot be reduced using only (m).
For (S=\{3,5,8\}) and (h=23), the source recurrence gives utilities
((13,10)) under friendly-versus-friendly play and ((13,8)) when the
starting player is antagonistic and the other player is friendly.  The
second-player discrepancy is (2=m-1).

