/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.Retarget

set_option autoImplicit false

/-!
# The two machine verifications the Helfgott chain cites, each as its source states it

`RT.PlattFull` bundles GRH for every primitive character of conductor `q ≤ 400000`, INCLUDING
`q = 1`, i.e. RH for `ζ` up to height `10⁸`. **Platt's Theorem 7.1 does not cover `q = 1`**: his
count of `29,565,923,837` `L`-functions is exactly the number of primitive characters with
`2 ≤ q ≤ 400000` (the count including `q = 1` is one more), and his algorithm (§4.1) assumes
`q ≥ 3`. Found by the retarget round's verifier; `Spine.PlattGRH` had inherited the same slice.
The slice is TRUE, but it is somebody else's theorem, and Helfgott consumes it (HelfMaj Prop 1.5
and Thm 1.4 at `q = 1` use zeros of `ζ`). So this file cites two sources separately:

* `PlattThm71` — D. J. Platt, *Numerical computations concerning the GRH*, Math. Comp. 85 (2016),
  arXiv:1305.3087, Theorem 7.1: GRH for Dirichlet `L`-functions of primitive characters of modulus
  `q ≤ 400000`, to height `max(10⁸/q, 7.5·10⁷/q + 200)` for even `q` and
  `max(10⁸/q, 3.75·10⁷/q + 200)` for odd `q`; here with `2 ≤ q`, the range his count covers.
* `PlattTrudgian` — D. J. Platt and T. S. Trudgian, *The Riemann hypothesis is true up to
  3·10¹²*, Bull. London Math. Soc. 53 (2021) 792–797, arXiv:2004.09765. Their statement is about
  zeros with `0 < Im ρ ≤ 3·10¹²`; zeros of `ζ` are closed under conjugation, so `|Im ρ| ≤ 3·10¹²`
  is the same claim.

Both are rigorous machine computations (interval arithmetic), cited rather than replicated per the
owner's direction of 2026-09-29. `plattFull_of_cited` derives `RT.PlattFull` from the two, using
Mathlib's `DirichletCharacter.LFunction_modOne_eq` (`L(s, χ) = ζ(s)` for `χ` mod `1`) and
`plattHeight 1 = 10⁸ ≤ 3·10¹²`. `thm71_of_full` and `zeta_of_full` show the pair asks for nothing
beyond what `PlattFull` said, so the citation is only split, never strengthened.
-/

namespace Principia.Common.TernaryGoldbach.PC

/-- **Platt, Theorem 7.1** (arXiv:1305.3087), on the range his count covers, `2 ≤ q ≤ 400000`:
every non-trivial zero (`0 < Re s < 1`) of `L(s, χ)`, `χ` primitive of conductor `q`, with
`|Im s| ≤ plattHeight q`, lies on `Re s = 1/2`. CITED (a machine verification). -/
def PlattThm71 : Prop :=
  ∀ (q : ℕ) [NeZero q], 2 ≤ q → q ≤ 400000 → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ RT.plattHeight q → s.re = 1 / 2

/-- RH for `ζ` up to height `T`: every non-trivial zero with `|Im s| ≤ T` has `Re s = 1/2`. -/
def ZetaRHTo (T : ℝ) : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → |s.im| ≤ T → s.re = 1 / 2

/-- **Platt–Trudgian 2021**: RH holds up to height `3·10¹²`. CITED (a machine verification). -/
def PlattTrudgian : Prop := ZetaRHTo (3 * 10 ^ 12)

/-- A verification to a greater height gives one to any smaller height. -/
theorem zetaRHTo_mono {T T' : ℝ} (h : T' ≤ T) (hz : ZetaRHTo T) : ZetaRHTo T' :=
  fun s hs h0 h1 hT => hz s hs h0 h1 (hT.trans h)

/-- At the modulus `1` Platt's height formula gives `10⁸` (`1` is odd, `10⁸ ≥ 3.75·10⁷ + 200`). -/
theorem plattHeight_one : RT.plattHeight 1 = 10 ^ 8 := by
  unfold RT.plattHeight
  norm_num

/-- **The two citations give `RT.PlattFull`.** Conductor `1` is `ζ` (Mathlib's
`LFunction_modOne_eq`), covered by Platt–Trudgian at `10⁸ ≤ 3·10¹²`; conductors `2 … 400000` are
Platt's Theorem 7.1. -/
theorem plattFull_of_cited (p : PlattThm71) (z : PlattTrudgian) : RT.PlattFull := by
  intro q hnz hq χ hχ s hs h0 h1 hT
  rcases Nat.lt_or_ge q 2 with h2 | h2
  · have hq1 : q = 1 := by
      have := hnz.out
      omega
    subst hq1
    rw [DirichletCharacter.LFunction_modOne_eq] at hs
    rw [plattHeight_one] at hT
    exact z s hs h0 h1 (hT.trans (by norm_num))
  · exact p q h2 hq χ hχ s hs h0 h1 hT

/-- The split asks for no more than `PlattFull` did: Theorem 7.1's range is part of it. -/
theorem thm71_of_full (pf : RT.PlattFull) : PlattThm71 :=
  fun q _ _ hq χ hχ s hs h0 h1 hT => pf q hq χ hχ s hs h0 h1 hT

/-- … and so is the `ζ` slice at height `10⁸`, which is all that `PlattFull` claimed of `ζ`. -/
theorem zeta_of_full (pf : RT.PlattFull) : ZetaRHTo (10 ^ 8) :=
  fun s hs h0 h1 hT => RT.zeta_of_plattFull pf s hs h0 h1 hT

end Principia.Common.TernaryGoldbach.PC
