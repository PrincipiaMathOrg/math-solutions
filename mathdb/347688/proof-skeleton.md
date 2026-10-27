# Proof skeleton for MathDB #347688

## Claim

The affine-plane complex \(X_{2,9}\) is the nerve of nine compact convex
polytopes in \(\mathbb R^5\).  Hence \(\operatorname{rep}(X_{2,9})\le5\).

## Data and construction

- Label the points by \(\mathbb F_3^2\) as
  \(0=(0,0),\ldots,8=(2,2)\).
- Independently reconstruct the 12 affine lines.  They are the minimal
  nonfaces of \(X_{2,9}\).
- For every incidence \(v\in L\), read the integral affine form
  \(\ell_{L,v}\) from `certificate.json`.
- Put
  \[
  C_v=[-42,42]^5\cap\bigcap_{L\ni v}\{\ell_{L,v}\ge1\}.
  \]

## Nonface gate

For every line \(L=\{p,q,r\}\), verify coefficientwise that

\[
\ell_{L,p}+\ell_{L,q}+\ell_{L,r}=0.
\]

Thus \(C_p\cap C_q\cap C_r=\varnothing\), since membership would make the
left side at least 3.  Every set containing a line therefore has empty
intersection.

## Face gate

- A line-free subset of \(AG(2,3)\) has size at most four: in a hypothetical
  five-set, each parallel class has occupancy \((2,2,1)\), accounting for
  only two pairs; four directions account for 8 rather than 10 pairs.
- Every line-free triple extends to a four-cap by avoiding the three third
  points on its pair-lines; smaller sets first extend to a triple.
- Independently enumerate the 54 four-caps.  The witness map has exactly one
  key for each.
- For every four-cap \(F\), verify in integers that its witness \(y_F\) lies
  in the box and that \(\ell_{L,v}(y_F)\ge1\) for every \(v\in F\), \(L\ni v\).
  Therefore every line-free set has nonempty intersection.

## Conclusion

The two gates give

\[
S\in N(C_0,\ldots,C_8)\iff S\text{ contains no affine line}
\iff S\in X_{2,9}.
\]

The verifier checks this equivalence separately for all \(2^9=512\) subsets,
using a contained line as the exact infeasibility certificate or a containing
four-cap witness as the exact feasibility certificate.

## What is not claimed

No lower bound \(\operatorname{rep}(X_{2,9})\ge5\) is asserted.
