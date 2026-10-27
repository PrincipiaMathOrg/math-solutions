# Proof skeleton for MathDB #359102

## Target

Refute Heil--Yu Conjecture 4.10: every bounded uniformly separated subset of
a separable infinite-dimensional complex Hilbert space is
\(\ell^1\)-bounded.

## G0 -- source and scope

- The author-hosted final paper defines
  \(\|x\|_{1,E}=\sum_n|\langle x,e_n\rangle|\).
- It works in a separable infinite-dimensional complex Hilbert space.
- Conjecture 4.10 has exactly the quantifiers recorded by MathDB.
- A counterexample in \(\ell^2\) is therefore in scope.

Status: closed.

## G1 -- explicit codes

For \(r\geq3\), take \(C_r=\operatorname{RM}(2,r)\), of length \(d_r=2^r\).
The elementary Reed--Muller distance induction and monomial-orthogonality
argument give

\[
d(C_r)=d_r/4,
\qquad C_r^\perp=\operatorname{RM}(r-3,r),
\qquad d(C_r^\perp)=8.
\]

The last inequality makes the signs of a uniformly random codeword
four-wise independent.

Status: closed, with a self-contained proof and finite exact checks.

## G2 -- bounded uniform separation

Place the normalized sign vectors of \(C_r\) in mutually orthogonal blocks
of dimensions \(d_r\).  Every vector has norm one.  Within a block, squared
distance is four times relative Hamming distance and is at least one; across
blocks it is two.

Status: closed; the separation constant is at least one.

## G3 -- fourth-moment lower bound

Four-wise independence gives, for \(S=\sum_i\varepsilon_i a_i\),

\[
\mathbb E|S|^2=\sigma^2,
\qquad \mathbb E|S|^4\leq3\sigma^4.
\]

Paley--Zygmund then gives
\(\mathbb E|S|\geq\sigma/(12\sqrt2)\).

Status: closed, including complex coefficients.

## G4 -- defeat an arbitrary frame

For a frame \(\{e_n\}\) with bounds \(A,B\) and a \(d\)-dimensional block,
set \(\sigma_n=\|P e_n\|\).  The frame bounds imply

\[
\sum_n\sigma_n^2\geq Ad,
\qquad \sup_n\sigma_n\leq\sqrt B,
\qquad \sum_n\sigma_n\geq Ad/\sqrt B.
\]

Averaging the frame \(\ell^1\)-norm over the block code therefore gives

\[
\mathbb E\|x\|_{1,\mathcal F}
 \geq \frac{A}{12\sqrt{2B}}\sqrt d.
\]

As \(d=2^r\to\infty\), no frame has a uniform bound on the constructed set.
In particular, no Riesz basis does.

Status: closed.

## G5 -- edge and quantifier audit

- The construction is countable: it is a countable union of finite codes.
- It lies in a complex Hilbert space even though its displayed coordinates
  are real.
- Tonelli applies to nonnegative summands; an infinite term only strengthens
  the conclusion.
- The constants \(A,B\) may depend on the candidate frame but are fixed while
  \(r\to\infty\).
- Proving failure for all frames is stronger than the required failure for
  all Riesz bases.

Status: closed.

## Verdict

All proof obligations are closed.  The conjecture is false.
