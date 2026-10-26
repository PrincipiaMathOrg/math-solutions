"""Exact certificate for the singular-tube counterexample (SymPy required)."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
import sympy as s

R = s.Rational
I = s.eye(2)
P = s.Matrix([[0, 1], [1, 0]])
A = (s.diag(R(3, 2), 0), s.diag(R(1, 2), 0))
B = (s.diag(R(1, 2), 1), s.diag(-R(1, 2), 1))
C = tuple(a+b for a, b in zip(A, B))

def fft(x):
    return (x[0]+x[1], x[0]-x[1])

def ifft(x):
    return ((x[0]+x[1])/2, (x[0]-x[1])/2)

def spectra(x):
    # Exact eigenvalues of M^T M, including multiplicity, computed from input.
    return [sorted([s.sqrt(e) for e, n in (m.T*m).eigenvals().items()
                    for _ in range(n)], reverse=True) for m in fft(x)]

def value(x):
    v = spectra(x)
    return s.simplify(sum(s.sqrt((v[0][i]**2+v[1][i]**2)/2)
                          for i in range(2)))

for x, expected in [(A, [[2, 0], [1, 0]]),
                    (B, [[2, 0], [1, 0]]),
                    (C, [[2, 2], [2, 0]])]:
    assert spectra(x) == expected
    assert ifft(fft(x)) == x

# Check explicit frequency factorizations and the corresponding real t-products.
def tprod(x, y):
    return (x[0]*y[0]+x[1]*y[1], x[0]*y[1]+x[1]*y[0])

for x, u, sig in [(A, (I, I), (s.diag(2, 0), s.diag(1, 0))),
                  (B, (P, I), (s.diag(2, 0), s.diag(1, 0))),
                  (C, (I, I), (2*I, s.diag(2, 0)))]:
    ut = ifft(u)
    st = ifft(sig)
    transpose_ut = tuple(m.T for m in ut)  # length-two t-transpose
    assert tprod(ut, transpose_ut) == (I, s.zeros(2))
    assert tprod(tprod(ut, st), transpose_ut) == x

fa, fb, fc = map(value, (A, B, C))
assert s.simplify(fa-s.sqrt(R(5, 2))) == 0 and fa == fb
assert s.simplify(fc-(2+s.sqrt(2))) == 0
assert s.simplify(fc**2-(fa+fb)**2) == 4*(s.sqrt(2)-1)
assert s.sqrt(2) > 1
assert s.simplify(value(tuple(m/2 for m in C))-fc/2) == 0
# Put the same witness strictly inside the Frobenius unit ball.
for x in (A, B, C):
    scaled = tuple(m/10 for m in x)
    assert sum(sum(e**2 for e in m) for m in scaled) < 1
    assert s.simplify(value(scaled)-value(x)/10) == 0
assert [sum(sum(v) for v in spectra(x)) for x in (A, B, C)] == [3, 3, 6]

out = dict(status='passed', checked_at_utc=datetime.now(timezone.utc).isoformat(),
           verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           arithmetic='Exact rational matrices and symbolic algebraic numbers; no floating point.',
           groups=[dict(name='Fourier slices and sorted spectra from rational inputs', cases=3),
                   dict(name='Real t-SVD reconstruction and t-orthogonality', cases=3),
                   dict(name='Exact strict triangle and midpoint failures; norm-ball scaling; distinct TNN',
                        values=list(map(str, (fa, fb, fc))), squared_gap='4*(sqrt(2)-1)>0')])
Path(__file__).with_name('verification-results.json').write_text(
    json.dumps(out, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(out, indent=2))
