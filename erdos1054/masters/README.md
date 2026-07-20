# Erdős 1054 & Almost-All Binary Goldbach — final machine-verified masters

Three single-workspace Lean 4 files, each compiled by the Lean kernel with **zero
errors and zero axiom declarations**. Every kernel audit ends at Lean's three built-in
foundations — nothing else:

    [propext, Classical.choice, Quot.sound]

## The three masters

| File | Headline theorem | Lines |
|---|---|---|
| `GoldbachChainMaster.lean` | `GoldbachChain.GoldbachReduction.almost_all_binary_goldbach_proven : DensityZero notSumOfTwoPrimes` | 31,714 |
| `Erdos1054_2ndMomentProof.lean` | `Erdos1054.erdos1054_second_moment_full_proof` (the paper's §6 **pure second-moment** route) | 36,748 |
| `Erdos1054_3rdMomentProof.lean` | `Erdos1054.erdos1054_third_moment_full_proof` (the original **third-moment** route) | 36,698 |

Each ships with its full compiler log (`*.gate.log`), whose final lines are the
`#print axioms` verdicts.

**`GoldbachChainMaster.lean`** is the standalone almost-all Goldbach proof: almost every
even number is a sum of two primes (the exceptional set has density zero), built from
Mathlib alone — Siegel's theorem (Goldfeld's route), the uniform zero-free region,
Siegel–Walfisz (also re-verified at the baseline inside the same gate as
`siegel_walfisz_proven`), Vinogradov's minor arcs via Vaughan's identity, and the
circle-method variance assembly.

**The two Erdős masters** each consist of the Goldbach master plus the complete
Erdős 1054 development (A1 Dirichlet-AP divergence, A2 Mertens' third theorem, the §5–§8
sieve development), with the former deep assumption `almost_all_binary_goldbach`
discharged against the proven theorem. They differ only in §6: the `FinalMaster` follows
`erdos_1054_corrected.tex`'s pure second-moment large-cofactor argument (`U(E)`,
`moment2_le`, `U_power_saving`, `large_e_bound_cubed` at the paper's `A³` strength); the
`ThirdMomentMaster` is the original formalization via the third moment `T3`.

## Reproducing the verification

The masters import `PrimeNumberTheoremAnd` (Kontorovich–Tao's PNT+ project supplies
`MediumPNT` and the Perron formula) and compile inside a checkout of that project:

    git clone https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
    cd PrimeNumberTheoremAnd
    git checkout d963a6e694a05cd82e5f9b9ae7f4d94123e85393
    # copy the master .lean file(s) into this directory, then:
    lake exe cache get && lake build PrimeNumberTheoremAnd.MediumPNT PrimeNumberTheoremAnd.PerronFormula
    lake env lean <Master>.lean

Toolchain: `leanprover/lean4:v4.31.0`; Mathlib locked by the project's
`lake-manifest.json` at `db127794c79fdeb86f6b0cf6ff2c804026fbaff1` (the checkout's
`lean-toolchain`/`lakefile.toml`/`lake-manifest.json` are included in this package for
reference). The PNT+ dependency compiles once (~1–2 h); each master then takes
~50–75 min and prints the axiom verdicts above.
