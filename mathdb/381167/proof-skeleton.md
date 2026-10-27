# MathDB #381167: counterexample skeleton

## Campaign status

- Candidate: [MathDB #381167](https://mathdb.com/p/381167)
- Source problem: Popa--Ceaușu--Megan, *On exponential stability for
  linear discrete-time systems in Banach spaces*, arXiv:1305.2036,
  Section 7.
- Mathematical status here: **complete counterexample; source, literature,
  computation, and two independent proof audits passed**.
- Count toward the twelve-solution target: **result 1 of 12 (internally
  verified; not a claim of publication priority)**.

## Exact target

For a Banach space `X` and a sequence `A(n) ∈ B(X)`, the source defines

\[
A_m^k=A(m)A(m-1)\cdots A(k+1)\quad(k<m),\qquad A_m^m=I.
\]

It conjectures that the following pointwise backward-sum condition implies
uniform exponential stability:

\[
\tag{BS}
\sum_{k=0}^{m}\lVert A_m^k x\rVert\le B\lVert x\rVert
\quad(m\in\mathbb N,\ x\in X).
\]

Uniform exponential stability (UES) would supply `N ≥ 1` and `α > 0` such
that

\[
\tag{UES}
\lVert A_m^k x\rVert\le Ne^{-\alpha(m-k)}\lVert x\rVert
\quad(0\le k\le m,\ x\in X).
\]

We refute `(BS) ⇒ (UES)`.

## Construction

Let

\[
X=\ell^1(\mathbb N_0)
\]

with standard unit vectors `e_0,e_1,…`. Set `A(0)=0` (its value is irrelevant
to the source's evolution-product convention), and for `n ≥ 1` define the
rank-one operator

\[
A(n)x=x_{n-1}e_n.
\]

Every `A(n)` is bounded and has operator norm one.

## Dependency ledger

### G1. Evolution-product formula — CLOSED

For `0 ≤ k < m`,

\[
\tag{1}
A_m^k x=x_ke_m.
\]

Proof: the first factor applied, `A(k+1)`, sends `x` to `x_k e_{k+1}`.
Each successive factor sends `x_k e_j` to `x_k e_{j+1}`. After the last
factor `A(m)`, the result is `x_k e_m`.

The identity case is separately `A_m^m x=x` by definition.

### G2. Backward-sum condition — CLOSED

Using (1), for every `m` and `x∈ℓ¹`,

\[
\begin{aligned}
\sum_{k=0}^{m}\lVert A_m^k x\rVert_1
&=\lVert x\rVert_1+\sum_{k=0}^{m-1}|x_k|\\
&\le 2\lVert x\rVert_1.
\end{aligned}
\]

Thus `(BS)` holds with the uniform constant `B=2`, including `m=0`.

### G3. Failure of UES — CLOSED

For every `0≤k<m`, equation (1) with `x=e_k` gives

\[
\lVert A_m^k e_k\rVert_1=\lVert e_m\rVert_1=1.
\]

If UES held, this would imply

\[
1\le Ne^{-\alpha(m-k)}
\]

for arbitrarily large `m-k`, impossible when `α>0`. Equivalently,
`‖A_m^k‖=1` for every `k<m`.

### G4. Scope and indexing audit — CLOSED

- `ℓ¹(ℕ₀)` is a Banach space, exactly within the source's stated scope.
- The operators are linear, bounded, and defined for every time index.
- The product order matches the source's displayed definition, including its
  indexing convention `A(m)…A(k+1)`.
- No invertibility, finite-dimensionality, reflexivity, or uniform lower bound
  is assumed by the conjecture.
- Condition `(BS)` uses one common `B=2`, not a constant depending on `m` or
  `x`.

### G5. Strong invertible variant — CLOSED

The failure is not an artifact of zero or noninvertible rank-one generators.
Let `0<ρ<1`, let `X=ℓ¹(ℤ)`, and define the weighted bilateral shifts

\[
A(n)e_j=\begin{cases}
e_{j+1},&j=n-1,\\
\rho e_{j+1},&j\ne n-1.
\end{cases}
\]

Then `‖A(n)‖=1` and `‖A(n)^{-1}‖=ρ^{-1}`. For `k<m`, direct induction gives

\[
A_m^k e_j=\begin{cases}
e_m,&j=k,\\
\rho^{m-k}e_{j+m-k},&j\ne k.
\end{cases}
\]

The output coordinates in the two cases are distinct, hence

\[
\lVert A_m^k x\rVert_1
=|x_k|+\rho^{m-k}(\lVert x\rVert_1-|x_k|).
\]

Consequently,

\[
\sum_{k=0}^m\lVert A_m^k x\rVert_1
\le\left(2+\frac{\rho}{1-\rho}\right)\lVert x\rVert_1.
\]

Nevertheless `A_m^k e_k=e_m`, so no exponential decay is possible. Taking
`ρ=1/2` gives `B=3`, while the generators and their inverses are uniformly
bounded.

### G6. Current-open-status / priority audit — CLOSED

The exact primary-source conjecture and all identifiable forward citations were
checked through 2026-08-18. Searches covered the journal DOI, arXiv mirror,
errata/corrections, exact phrases, the displayed condition, and the `ℓ¹`
rank-one-shift mechanism. No published proof, counterexample, erratum, or
correction of this exact primal condition was located. Later works found in the
citation trail use different hypotheses (operator norms, adjoints, sequence
spaces, or cocycle/ergodic conditions).

This supports the careful claim: the conjecture had no located published
resolution before this counterexample. It does not claim an impossible
guarantee about unindexed private work.

### G7. Independent proof audit — CLOSED

Two independent source-level audits reproduced the product formula, sum bound,
and failure of UES. The second audit specifically attacked product order, the
source's three-index UES definition, the convention for `ℕ`, dependence of the
witness vector on `k`, and possible confusion with the valid adjoint theorem;
none produces a defect.

## Why the conjectured implication fails

The sum in `(BS)` is pointwise in a single vector. In this construction the
different backward products read different coordinates of `x`; the `ℓ¹` norm
therefore pays for all of them only once. Operator norms can choose a different
unit vector `e_k` for each product, so every product still has norm one. This is
precisely the gap between

\[
\sup_{\lVert x\rVert=1}\sum_k\lVert T_kx\rVert
\quad\text{and}\quad
\sum_k\lVert T_k\rVert.
\]

## Lean-style formalization sketch

```lean
-- Pseudocode: use the ℓ¹ space over ℕ and its coordinate functionals.
def A (n : ℕ) : (ℕ →₁ ℝ) →L[ℝ] (ℕ →₁ ℝ) :=
  if h : n = 0 then 0 else rankOne (coord (n-1)) (basisVec n)

lemma evolution_apply (k m : ℕ) (h : k < m) (x : ℕ →₁ ℝ) :
    evolution A m k x = x k • basisVec m := by
  induction m - k with
  | zero => omega
  | succ d ih => simp [evolution, A, ih]

lemma backward_sum_le_two (m : ℕ) (x : ℕ →₁ ℝ) :
    ∑ k in Finset.range (m+1), ‖evolution A m k x‖ ≤ 2 * ‖x‖ := by
  rw [sum_split_last]
  simp_rw [evolution_apply]
  exact add_le_add_left (partial_coord_sum_le_norm x m) _

theorem not_uniformly_exponentially_stable : ¬ UES A := by
  intro h
  obtain ⟨N, α, hα, hbound⟩ := h
  specialize hbound (basisVec 0) 0 m
  -- Left side is 1 for every m; right side tends to 0.
  exact one_not_le_exp_decay_for_all_m N hα hbound
```

## Candidate final theorem

> There is a linear discrete-time system on a Banach space satisfying the
> pointwise Barbashin sum condition with `B=2` that is not uniformly
> exponentially stable. Hence the equivalence conjectured in Section 7 of the
> source is false in general Banach spaces.
