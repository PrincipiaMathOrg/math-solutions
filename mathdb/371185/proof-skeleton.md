# Proof skeleton for MathDB #371185

Let (m=\min S).

1. For a fixed heap (h), cumulative subtraction is a finite
   extensive-form game.  Every deterministic tie-breaking convention
   chooses only among actions that maximize the mover's primary utility.
   Its backward-induction profile is therefore a subgame-perfect, hence
   Nash, equilibrium of the common underlying game.

2. In every terminal history the residual heap (r) satisfies
   (0\leq r<m).  Since each removed stone is credited exactly once,
   every strategy profile has total payoff

   \[
   h-m+1\leq u_1+u_2=h-r\leq h.
   \]

3. General lemma: if all outcomes of a two-player game have total payoff
   in an interval of width (R), then either player's payoffs at any two
   Nash equilibria differ by at most (R).  Cross the first strategy of
   one equilibrium with the second strategy of the other, add the two
   best-response inequalities, and use the lower and upper total-payoff
   bounds.  Swap the equilibria for the opposite inequality.

4. Apply the lemma with (R=m-1).  Thus every signed discrepancy between
   any two conventions lies in ([-(m-1),m-1]), uniformly in (h).

5. Exact recurrence check: (S=\{3,5,8\}), (h=23), and the profiles
   FvF and AvF give ((13,10)) and ((13,8)), respectively.  Hence the
   bound (m-1) is sharp as a function of (m).

Hostile dependency audit, 19 August 2026: the pass checked forced
termination, the residual-heap endpoints (including (m=1) and
(h<m)), that tie-breaking profiles are equilibria of one primary-payoff
game rather than different games, validity of crossed off-path strategies,
both signs and both player coordinates in the equilibrium lemma, infinite
subtraction sets, and the distinction from the source's separate
friendly-versus-antagonistic monotonicity conjecture.  No dependency on
eventual periodicity or on the source's empirical search remains.

