# Proof audit

The target is Svinin's Conjecture 3.1 in the current arXiv version and the published article. The hypotheses are n,j positive integers and k a nonnegative integer. The weak tuples permit ties. Negative shifted arguments have their ordinary odd-power signs. The proof uses these exact conventions and includes n = 1, j = 1, and k = 0.

The strengthened result permits every complex-valued odd function on the integers. To prove it, F records each weak tuple together with a marked position, while R records the source's binomial combination of ordered tuples. Reversing and complementing a tuple proves F(z inverse) = z^(−n−1) F(z), with multiplicities preserved.

Nonnegative gaps sum to jn − 1. Their independent generating functions yield the marked-tuple formula. Its finite geometric sum, multiplied by 1 − z^(−n−1), becomes T(b) − T(zb), where b = (z^n − 1)/(z^(n+1) − 1). The coefficient lemma is proved by a weighted partition of finite binary words; it requires no analytic probability argument or convergence assumption. Its leading rational terms cancel because a = jn.

The remainder is P(B(z)) − P(B(z inverse)), with B = 1 + z + ... + z^n. A separate binomial transform shows that R differs from P(B) by a constant. That constant cancels. The conclusion is an identity in Laurent polynomials, even though intermediate calculations take place in Q(z). No specialization at a root of a denominator is required.

The linear map z^r to an odd function psi(r) sends reciprocal monomials to opposite values, so the Laurent identity gives twice the desired equality. Division by two is valid over C. The source's polynomial coefficients count ordered bounded compositions, exactly as on the right-hand side of the theorem.

The verifier implements both direct weak-tuple enumeration and an independent marked-order-statistic count allowing ties. It compares every signed coefficient with direct convolutions, checks nonpolynomial odd functions as well as powers, and checks the coefficient lemma at exact rational values inside and outside the unit interval. These checks supplement the proof for every parameter.

Four proposed follow-ups are distinguished from the solved target. Review was performed by the authoring agent only; no independent peer review or proof assistant is claimed.
