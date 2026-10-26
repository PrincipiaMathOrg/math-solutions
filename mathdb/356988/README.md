# MathDB 356988 — Backtracking PageRank is not monotonic

**Complete exact counterexamples; eligibility pending, zero new credit.**

With uniform personalization, the five-vertex house graph has a vertex
whose score decreases and then increases as the backtracking weight
changes. Its damping parameter is 1/2. A six-vertex theta graph at
damping 9/10 has score spread strictly increasing up to backtracking
weight 1 and strictly decreasing thereafter. Thus the spread is not
monotonic in either direction.

Both graphs are simple, connected, undirected, and have minimum degree
two. The proofs supply explicit positive rational stationary masses.
They refute the intended monotonicity assertions independently of the
opposite directions found in the source's displayed inequality and prose.

- [LaTeX solution](solution.tex) and [PDF](solution.pdf).
- [Proof audit](proof-audit.md) and [literature audit](literature-audit.md).
- [Exact verifier](verify.py) and [results](verification-results.json).
- Task 1 gives both counterexamples; Tasks 2–5 give four follow-ups.

Run `python verify.py` with SymPy installed. All four exact groups pass,
including 52 independently solved rational systems and six certified
Neumann-series intervals. Authoring-agent review only.

The complete current 22-page preprint was read. The identified journal
final remains inaccessible and unread; its conjecture and any corrections
have not been checked. The solution is pushed for review under the
standing publication instruction and is not counted toward the new 100.
