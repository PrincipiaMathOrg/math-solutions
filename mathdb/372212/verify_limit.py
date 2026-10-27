"""Low-memory numerical checks for the proof of MathDB #372212.

Dependency:
    NumPy (tested with NumPy's LAPACK-backed ``eigh`` and ``solve``)

The proof is analytic and does not depend on this script.  The checks below
reconstruct properly aligned Green roots, verify the algebraic identities used
by the proof, and compare the exact finite-epsilon formula from source Theorem
3.10 with the derived limit ``tr((X+Y)^-1 C)``.
"""

import os

# Keep BLAS implementations single-threaded and the memory footprint small.
for variable in (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
):
    os.environ[variable] = "1"

import numpy as np


def sym(matrix):
    """Remove roundoff-level skew-symmetric noise."""
    return (matrix + matrix.T) / 2.0


def psd_sqrt(matrix):
    """Principal square root of a real symmetric positive-semidefinite matrix."""
    eigenvalues, eigenvectors = np.linalg.eigh(sym(matrix))
    scale = max(1.0, float(np.max(np.abs(eigenvalues))))
    assert float(np.min(eigenvalues)) >= -2.0e-12 * scale
    eigenvalues = np.maximum(eigenvalues, 0.0)
    return (eigenvectors * np.sqrt(eigenvalues)) @ eigenvectors.T


def aligned_data(A, B):
    """Return the aligned G,M and the matrices X,Y,C,S."""
    G = psd_sqrt(A)
    C = psd_sqrt(G @ B @ G)
    M = np.linalg.solve(G.T, C)

    X = sym(G.T @ G)
    Y = sym(M.T @ M)
    C = sym(G.T @ M)
    S = X + Y
    return G, M, X, Y, C, S


def shrinkage(C, epsilon):
    """Apply f_epsilon spectrally to C."""
    eigenvalues, eigenvectors = np.linalg.eigh(C)
    values = (
        np.sqrt(4.0 * eigenvalues**2 + epsilon**2) - epsilon
    ) / (2.0 * eigenvalues)
    return (eigenvectors * values) @ eigenvectors.T


def squared_coupling_distance(X, Y, C, epsilon):
    """The exact Theorem 3.10 expression."""
    R = shrinkage(C, epsilon)
    Q = sym(X @ X + Y @ Y + X @ R @ Y + Y @ R @ X)
    return 2.0 * (np.trace(X + Y) - np.trace(psd_sqrt(Q)))


def check_case(A, B, label):
    G, M, X, Y, C, S = aligned_data(A, B)
    dimension = A.shape[0]

    assert np.allclose(G @ G.T, A, rtol=2e-12, atol=2e-12)
    assert np.allclose(M @ M.T, B, rtol=2e-11, atol=2e-11)
    assert np.allclose(G.T @ M, M.T @ G, rtol=2e-11, atol=2e-11)

    predicted_Y = C @ np.linalg.solve(X, C)
    assert np.allclose(Y, predicted_Y, rtol=3e-11, atol=3e-11)
    assert np.allclose(
        X @ np.linalg.solve(C, Y), C, rtol=3e-11, atol=3e-11
    )
    assert np.allclose(
        Y @ np.linalg.solve(C, X), C, rtol=3e-11, atol=3e-11
    )
    assert np.allclose(
        S - 2.0 * C,
        (G - M).T @ (G - M),
        rtol=3e-11,
        atol=3e-11,
    )

    exact_limit = float(np.trace(np.linalg.solve(S, C)))
    assert exact_limit <= dimension / 2.0 + 3e-12

    epsilons = (1.0e-2, 3.0e-3, 1.0e-3, 3.0e-4, 1.0e-4)
    rates = tuple(
        squared_coupling_distance(X, Y, C, epsilon) / epsilon
        for epsilon in epsilons
    )

    # The final rate is first-order accurate and the last two refinements
    # move toward the predicted derivative for these well-conditioned cases.
    assert abs(rates[-1] - exact_limit) < 8.0e-4
    assert abs(rates[-1] - exact_limit) < abs(rates[-2] - exact_limit)

    print(
        f"{label}: d={dimension}; limit={exact_limit:.12f}; "
        f"d/2={dimension / 2:.12f}; rate(eps=1e-4)={rates[-1]:.12f}"
    )


def main():
    generator = np.random.default_rng(372212)

    for dimension in (1, 2, 4, 7):
        left = generator.normal(size=(dimension, dimension))
        right = generator.normal(size=(dimension, dimension))
        A = left @ left.T + (1.25 + dimension / 10.0) * np.eye(dimension)
        B = right @ right.T + (0.90 + dimension / 8.0) * np.eye(dimension)
        check_case(A, B, f"random-{dimension}")

    # Equality case: any common positive-definite covariance has rate d/2.
    dimension = 5
    root = generator.normal(size=(dimension, dimension))
    A = root @ root.T + 1.5 * np.eye(dimension)
    check_case(A, A, "identity-transport")

    print("all checks: PASS")


if __name__ == "__main__":
    main()
