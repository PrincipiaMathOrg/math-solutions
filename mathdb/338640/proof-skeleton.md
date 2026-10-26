# Proof skeleton for MathDB #338640

## Claim

The finite-parameter minimality conjecture of Bovdi--Leung is false, already
at \(k=2\).

## Dependencies

### D1. Source definition

An \(s\)-bicommutative system is an inclusion-maximal pairwise-intersecting
subfamily of \(\mathcal P_n(s)\). Equivalently, every outside \(s\)-set must
be disjoint from a family member.

### D2. Allowed specialization

The conjecture quantifies over every \(k\ge2\), so \(k=2\) is admissible and
gives \(n=15,m=7\).

### D3. Source-family cardinality

Substitution into the source formula gives

\[
|\mathcal A_7|
=7\binom84+\binom72\binom85+7\binom86+\binom87
=490+1176+196+8=1870.
\]

The verifier also reconstructs all four source classes and checks their
disjoint union and total independently.

### D4. Explicit smaller family

certificate.json lists 1173 distinct 15-bit masks. Bit \(i-1\) denotes
element \(i\in[15]\).

### D5. Uniformity

Every certificate mask is nonzero, below \(2^{15}\), and has popcount seven.

### D6. Pairwise intersection

For all \(\binom{1173}{2}=687378\) certificate pairs \(a,b\), the verifier
checks \(a\mathbin{\&}b\ne0\).

### D7. Maximality

The verifier enumerates all \(\binom{15}{7}=6435\) seven-sets. For each of
the 5262 masks outside the certificate it enumerates the eight seven-subsets
of its eight-element complement and checks that at least one is in the
certificate. Thus every outside seven-set has a disjoint family member.

### D8. Strict improvement

\[
1173<1870,
\]

with gap \(697\).

## Conclusion

D4--D7 make the certificate a 7-bicommutative system, while D3 and D8 make it
strictly smaller than \(\mathcal A_7\). Therefore the universal minimality
conjecture is false.

## Hostile-audit checklist

- The endpoint \(k=2\) is included, not extrapolated.
- The bit convention is pinned and checked against the complete universe.
- Pairwise intersection and maximality are both checked; neither is inferred
  from the greedy discovery process.
- No floating-point arithmetic, solver, or assertion disabled by -OO is used.
- The conclusion is non-optimality, not the exact minimum.
- The result is not counted as novel: Al-Herz (2012), Table 1, already reports
  a valid 1097-vertex independent dominating set in the identical graph
  \(O_8=KG(15,7)\).
