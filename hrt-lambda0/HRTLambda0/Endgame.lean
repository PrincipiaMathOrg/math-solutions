/-
# HRT at the resonant non-lattice configuration Λ₀ — the endgame, Lean 4

Companion to the paper

  *Linear independence of four time–frequency translates at a resonant
   non-lattice configuration* (`paper/hrt-lambda0.tex`),

which concerns the case `Λ₀ = {(0,0), (1,0), (0,1), (√2,√2)}` of the
Heil–Ramanathan–Topiwala conjecture (Conjecture 9.2(a) of Heil's 2006 survey,
Conjecture 2 of the Heil–Speegle survey) for windows with continuous Zak transform.

## What this file proves

The paper's own contribution is the **endgame**: the fibration of `𝕋²`, the
zero-propagation dichotomy and the value of the fibre winding number are due to
Oussa (cited in the paper as arXiv:2508.04613v2); what is new is

  (iii) the evaluation of the fibre mean by Jensen's formula, producing a
        quantity *constant across fibres*, and
  (iv)  the Vieta rigidity that contradicts that constancy.

`hrt_endgame` below is a complete, axiom-free formalization of (iv) taking (iii)
as input, i.e. of the final contradiction. `degree_identity_kills` is the
arithmetic core of the paper's Lemma "degree identity" (`Theorem general` for
`|j| ≥ 2`).

The formalized endgame is in one respect *stronger* than the paper's: the paper
argues that `ζ_out` is continuous, hence constant because it takes values in a
two-point set, and then contradicts Vieta. `circle_pair_quadratic` shows the
two-circle intersection is cut out by a *fixed* quadratic satisfied by `ζ_out c`
for every `c`, so no continuity is needed and three sample fibres suffice.

## What this file does NOT prove

The analytic inputs are hypotheses, never axioms; nothing here is declared as an
`axiom` and nothing is `sorry`-ed:

* the Zak-transform reduction (paper eq. (FE)) and the fibration of `𝕋²`;
* the zero-propagation dichotomy (paper Lemma "dichotomy");
* the winding/degree identity `deg η_c = 0` and its reading as `N(c) = j + 1`;
* Jensen's formula on the fibre (paper Lemma "jensen").

These enter `hrt_endgame` as the hypotheses `hvieta_sum`, `hvieta_prod`,
`hjensen`, and are packaged for the capstone as `ZakReduction`
(`HRTLambda0/Statement.lean`). Discharging them would require a Lean development
of the Zak transform, degree theory for circle maps, and Jensen's formula for
`H^p` functions on the disc, none of which is in Mathlib.

## Axiom footprint

`#print axioms` at the bottom; the verified footprint is exactly
`[propext, Classical.choice, Quot.sound]` (one lemma needs only
`[propext, Quot.sound]`).
-/
import HRTLambda0.Statement
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

namespace HRTLambda0

open Complex

/-! ## Paper Remark: `Λ₀` is not reachable from the solved cases

Affine symplectic maps preserve HRT dependences, and the difference vectors of
`Λ₀` have symplectic invariants `1, √2, -√2`.  Membership in a lattice would force
these into a common `dℤ`, which is impossible because `√2` is irrational.  Hence
neither Linnell's theorem nor the two-parallel-line results apply after any change
of coordinates. -/

/-- **Paper Remark (the symplectic escape is closed).**  There is no `d > 0` with
both `1` and `√2` in `dℤ`; so the symplectic invariants `1, √2` of `Λ₀` never lie
in a common lattice. -/
theorem lambda0_symplectic_escape :
    ¬ ∃ (d : ℝ) (m n : ℤ), 0 < d ∧ (1 : ℝ) = m * d ∧ Real.sqrt 2 = n * d := by
  rintro ⟨d, m, n, _hd, h1, h2⟩
  have hm : (m : ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1
    exact one_ne_zero h1
  have key : Real.sqrt 2 * (m : ℝ) = (n : ℝ) := by
    rw [h2]
    linear_combination (-(n : ℝ)) * h1
  refine irrational_sqrt_two ⟨(n : ℚ) / (m : ℚ), ?_⟩
  push_cast
  rw [div_eq_iff hm]
  exact key.symm

/-! ## Paper Lemma "dichotomy": zeros propagate along the fibre

On a fibre the functional equation reads `G_c(t - α) = P_c(t) G_c(t)`, in which no
division occurs, so a single zero propagates along the whole backward orbit.  Since
`α` is irrational that orbit is dense modulo `1`, and `|G_c|` is `1`-periodic, so a
continuous `G_c` with one zero vanishes identically. -/

/-- **Paper Lemma "dichotomy", propagation step.**  A zero of `G` propagates along
the backward `α`-orbit.  No division occurs, so this needs no hypothesis on `P`. -/
theorem zero_propagates {α t₀ : ℝ} {G P : ℝ → ℂ}
    (hFE : ∀ t, G (t - α) = P t * G t) (hzero : G t₀ = 0) :
    ∀ n : ℕ, G (t₀ - n * α) = 0 := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ k ih =>
      have hstep : G (t₀ - k * α - α) = P (t₀ - k * α) * G (t₀ - k * α) := hFE _
      rw [ih, mul_zero] at hstep
      have hrw : t₀ - ((k : ℝ) + 1) * α = t₀ - k * α - α := by ring
      push_cast
      rw [hrw]
      exact hstep

/-- **Paper Lemma "dichotomy".**  A continuous fibre function whose modulus is
`1`-periodic and which vanishes somewhere vanishes identically, given that the
backward `α`-orbit is dense modulo `1` (which is where irrationality of `α`
enters). -/
theorem fibre_dichotomy {α t₀ : ℝ} {G P : ℝ → ℂ}
    (hG : Continuous G)
    (hper : Function.Periodic (fun t => ‖G t‖) 1)
    (hFE : ∀ t, G (t - α) = P t * G t)
    (hzero : G t₀ = 0)
    (hdense : Dense {t : ℝ | ∃ (n : ℕ) (m : ℤ), t = t₀ - n * α - m}) :
    G = 0 := by
  refine Continuous.ext_on hdense hG continuous_const ?_
  rintro t ⟨n, m, rfl⟩
  have hshift : ‖G (t₀ - n * α - m)‖ = ‖G (t₀ - n * α)‖ := by
    have := hper.sub_int_mul_eq (x := t₀ - (n : ℝ) * α) m
    simpa using this
  rw [zero_propagates hFE hzero n, norm_zero] at hshift
  simpa using norm_eq_zero.mp hshift

/-! ## Paper Lemma "degree identity": the root count kills `|j| ≥ 2`

The winding computation gives `N(c) = j + 1`, where `N(c)` is the number of roots
of the quadratic `Q_c` inside the unit disc.  Since `Q_c` is quadratic,
`N(c) ∈ {0,1,2}`, so no fibre can be alive unless `j ∈ {-1,0,1}`. -/

/-- **Paper Lemma "degree identity", arithmetic core.**  A root count of a
quadratic lies in `{0,1,2}`; the winding identity forces it to equal `j + 1`.
Hence `j ∈ {-1, 0, 1}`, and for every other `j` the live-fibre set `C₁` is empty
— which is the paper's `Theorem general` for `|j| ≥ 2`. -/
theorem degree_identity_kills {j : ℤ} {N : ℕ} (hdeg : (N : ℤ) = j + 1)
    (hquad : N ≤ 2) : j = -1 ∨ j = 0 ∨ j = 1 := by
  omega

/-! ## Quadratic rigidity -/

/-- A nonzero quadratic cannot have three pairwise distinct roots. -/
theorem two_of_three_eq_of_quadratic {A B C u₁ u₂ u₃ : ℂ} (hA : A ≠ 0)
    (h₁ : A * u₁ ^ 2 + B * u₁ + C = 0)
    (h₂ : A * u₂ ^ 2 + B * u₂ + C = 0)
    (h₃ : A * u₃ ^ 2 + B * u₃ + C = 0) :
    u₁ = u₂ ∨ u₁ = u₃ ∨ u₂ = u₃ := by
  by_contra hcon
  have h12 : u₁ ≠ u₂ := fun h => hcon (Or.inl h)
  have h13 : u₁ ≠ u₃ := fun h => hcon (Or.inr (Or.inl h))
  have h23 : u₂ ≠ u₃ := fun h => hcon (Or.inr (Or.inr h))
  have key : ∀ x y : ℂ, x ≠ y → A * x ^ 2 + B * x + C = 0 →
      A * y ^ 2 + B * y + C = 0 → A * (x + y) + B = 0 := by
    intro x y hxy hx hy
    have h : (x - y) * (A * (x + y) + B) = 0 := by linear_combination hx - hy
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd (sub_eq_zero.mp h') hxy
    · exact h'
  have k12 := key u₁ u₂ h12 h₁ h₂
  have k13 := key u₁ u₃ h13 h₁ h₃
  have hz : A * (u₂ - u₃) = 0 := by linear_combination k12 - k13
  rcases mul_eq_zero.mp hz with h' | h'
  · exact hA h'
  · exact h23 (sub_eq_zero.mp h')

/-! ## Two-circle rigidity

The paper's `ζ_out(c)` lies in `{|z| = r} ∩ {|z - S| = r'}`, an intersection of
two circles with distinct centres, hence a set of at most two points.  The lemma
below realizes that intersection as the zero set of one *fixed* quadratic with
leading coefficient `conj S`, which is what makes the endgame continuity-free. -/

/-- **Two-circle rigidity.**  If `‖u‖ = r` and `‖S - u‖ = r'`, then `u` is a root
of the fixed quadratic `conj S · z² − (‖S‖² + r² − r'²) · z + r² S`. -/
theorem circle_pair_quadratic {S u : ℂ} {r r' : ℝ} (hu : ‖u‖ = r)
    (hv : ‖S - u‖ = r') :
    (starRingEnd ℂ) S * u ^ 2
      + (-((‖S‖ ^ 2 + r ^ 2 - r' ^ 2 : ℝ) : ℂ)) * u
      + (r : ℂ) ^ 2 * S = 0 := by
  have h1 : u * (starRingEnd ℂ) u = (r : ℂ) ^ 2 := by rw [Complex.mul_conj', hu]
  have h2 : (S - u) * ((starRingEnd ℂ) S - (starRingEnd ℂ) u) = (r' : ℂ) ^ 2 := by
    rw [← map_sub, Complex.mul_conj', hv]
  have h3 : S * (starRingEnd ℂ) S = ((‖S‖ : ℝ) : ℂ) ^ 2 := by rw [Complex.mul_conj']
  have hcross : S * (starRingEnd ℂ) u + u * (starRingEnd ℂ) S
      = ((‖S‖ ^ 2 + r ^ 2 - r' ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination -h2 + h3 + h1
  linear_combination u * hcross - S * h1

/-! ## The endgame: Jensen constancy + Vieta rigidity ⇒ contradiction

Setting.  A nontrivial dependence with all coefficients `c₁, …, c₄` nonzero has
been assumed.  On the live fibres `c ∈ C₁` the quadratic

  `Q_c(z) = c₃ z² + c₁ z + c₂ e^{-2πic}`

has one root `ζ_in(c)` inside and one root `ζ_out(c)` outside the unit circle
(paper Lemma "degree identity" with `j = 0`).  Vieta gives

  `ζ_in + ζ_out = -c₁/c₃`,   `ζ_in · ζ_out = (c₂/c₃) e^{-2πic}`,

and Jensen's formula on the fibre gives the *cross-fibre constancy*

  `|ζ_out(c)| = |c₄|/|c₃|`.

The theorem shows these three facts are jointly contradictory on any interval of
positive length shorter than the period — the step that settles `Λ₀`. -/

/-- **Paper endgame (Lemma "jensen" + Vieta rigidity), fully formalized.**

On an interval `[α, β]` of positive length `< 1` there is no pair of functions
`ζ_in, ζ_out` obeying Vieta's relations for `Q_c(z) = c₃z² + c₁z + c₂e^{-2πic}`
together with the Jensen constancy `‖ζ_out c‖ = ‖c₄‖/‖c₃‖`.

Consequently no live fibre interval exists, and the assumed dependence cannot
occur: this is the contradiction that proves the paper's main theorem in the case
`j = 0`, in particular at `Λ₀` (where `α = √2`). -/
theorem hrt_endgame
    {c₁ c₂ c₃ c₄ : ℂ} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0) (hc₄ : c₄ ≠ 0)
    {α β : ℝ} (hlt : α < β) (hlen : β - α < 1)
    (zin zout : ℝ → ℂ)
    (hvieta_sum : ∀ c ∈ Set.Icc α β, zin c + zout c = -c₁ / c₃)
    (hvieta_prod : ∀ c ∈ Set.Icc α β,
      zin c * zout c = (c₂ / c₃) * Complex.exp (-(2 * Real.pi * Complex.I * c)))
    (hjensen : ∀ c ∈ Set.Icc α β, ‖zout c‖ = ‖c₄‖ / ‖c₃‖) :
    False := by
  have hSne : (-c₁ / c₃) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hc₁) hc₃
  have hc₃0 : (0 : ℝ) < ‖c₃‖ := norm_pos_iff.mpr hc₃
  have hr : (0 : ℝ) < ‖c₄‖ / ‖c₃‖ := div_pos (norm_pos_iff.mpr hc₄) hc₃0
  have hexp_norm : ∀ c : ℝ,
      ‖Complex.exp (-(2 * Real.pi * Complex.I * c))‖ = 1 := by
    intro c
    rw [Complex.norm_exp]
    simp
  -- The modulus of the inner root is constant across fibres as well.
  have hzin_norm : ∀ c ∈ Set.Icc α β,
      ‖(-c₁ / c₃) - zout c‖ = ‖c₂‖ / ‖c₃‖ / (‖c₄‖ / ‖c₃‖) := by
    intro c hc
    have hin : zin c = (-c₁ / c₃) - zout c := by
      linear_combination hvieta_sum c hc
    have hp : ‖zin c‖ * ‖zout c‖ = ‖c₂‖ / ‖c₃‖ := by
      have h := congrArg norm (hvieta_prod c hc)
      rwa [norm_mul, norm_mul, norm_div, hexp_norm c, mul_one] at h
    rw [hjensen c hc] at hp
    rw [← hin]
    exact (eq_div_iff hr.ne').mpr hp
  -- Every value of `zout` is a root of one and the same nonzero quadratic.
  have hquad : ∀ c ∈ Set.Icc α β,
      (starRingEnd ℂ) (-c₁ / c₃) * (zout c) ^ 2
        + (-((‖(-c₁ / c₃)‖ ^ 2 + (‖c₄‖ / ‖c₃‖) ^ 2
              - (‖c₂‖ / ‖c₃‖ / (‖c₄‖ / ‖c₃‖)) ^ 2 : ℝ) : ℂ)) * (zout c)
        + ((‖c₄‖ / ‖c₃‖ : ℝ) : ℂ) ^ 2 * (-c₁ / c₃) = 0 := by
    intro c hc
    exact circle_pair_quadratic (hjensen c hc) (hzin_norm c hc)
  have hAne : (starRingEnd ℂ) (-c₁ / c₃) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact hSne
  -- Two distinct fibres sharing a `zout` value force `e^{-2πic}` to repeat.
  have main : ∀ s ∈ Set.Icc α β, ∀ t ∈ Set.Icc α β, s ≠ t →
      zout s = zout t → False := by
    intro s hs t ht hst heq
    have hins : zin s = (-c₁ / c₃) - zout s := by
      linear_combination hvieta_sum s hs
    have hint : zin t = (-c₁ / c₃) - zout t := by
      linear_combination hvieta_sum t ht
    have hprod_eq : (c₂ / c₃) * Complex.exp (-(2 * Real.pi * Complex.I * s))
        = (c₂ / c₃) * Complex.exp (-(2 * Real.pi * Complex.I * t)) := by
      rw [← hvieta_prod s hs, ← hvieta_prod t ht, hins, hint, heq]
    have hexp_eq := mul_left_cancel₀ (div_ne_zero hc₂ hc₃) hprod_eq
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp_eq
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hfac : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
    have hkey : ((t - s : ℝ) : ℂ) = (n : ℂ) := by
      have hz : (2 * (Real.pi : ℂ) * Complex.I) * (((t - s : ℝ) : ℂ) - (n : ℂ)) = 0 := by
        push_cast
        linear_combination hn
      rcases mul_eq_zero.mp hz with h' | h'
      · exact absurd h' hfac
      · exact sub_eq_zero.mp h'
    have hts : (t - s : ℝ) = (n : ℝ) := by exact_mod_cast hkey
    have hne0 : n ≠ 0 := by
      intro h0
      apply hst
      rw [h0] at hts
      push_cast at hts
      linarith
    obtain ⟨hs1, hs2⟩ := hs
    obtain ⟨ht1, ht2⟩ := ht
    rcases (by omega : (1 : ℤ) ≤ n ∨ n ≤ -1) with h | h
    · have hh : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      rw [← hts] at hh
      linarith
    · have hh : ((n : ℝ)) ≤ -1 := by exact_mod_cast h
      rw [← hts] at hh
      linarith
  -- Three sample fibres.
  have hmemα : α ∈ Set.Icc α β := ⟨le_refl α, hlt.le⟩
  have hmemβ : β ∈ Set.Icc α β := ⟨hlt.le, le_refl β⟩
  have hmemm : (α + β) / 2 ∈ Set.Icc α β := ⟨by linarith, by linarith⟩
  rcases two_of_three_eq_of_quadratic hAne (hquad α hmemα)
      (hquad ((α + β) / 2) hmemm) (hquad β hmemβ) with h | h | h
  · exact main α hmemα ((α + β) / 2) hmemm (by intro hc; linarith) h
  · exact main α hmemα β hmemβ (ne_of_lt hlt) h
  · exact main ((α + β) / 2) hmemm β hmemβ (by intro hc; linarith) h

/-! ## Capstone: the endgame really does close the paper

`ZakReduction g` (see `HRTLambda0/Statement.lean`) packages, as a single named
hypothesis, everything the paper establishes *before* its endgame.  None of that
is proven here.  What `lambda0_independent_of_reduction` shows is that
`hrt_endgame` is *sufficient* to finish: given the reduction, the four translates
at `Λ₀` are linearly independent. -/

/-- **Paper Theorem "main", conditional on the analytic reduction.**  For a window
`g` for which the paper's Zak-transform reduction applies, the four time–frequency
translates at `Λ₀ = {(0,0), (1,0), (0,1), (√2,√2)}` are linearly independent —
i.e. the HRT conjecture holds at `Λ₀`. -/
theorem lambda0_independent_of_reduction {g : ℝ → ℂ} (h : ZakReduction g) :
    Lambda0Independent g := by
  by_contra hdep
  obtain ⟨c₁, c₂, c₃, c₄, a, b, zin, zout,
    h1, h2, h3, h4, hab, hlen, hsum, hprod, hjen⟩ := h hdep
  exact hrt_endgame h1 h2 h3 h4 hab hlen zin zout hsum hprod hjen

end HRTLambda0

#print axioms HRTLambda0.lambda0_symplectic_escape
#print axioms HRTLambda0.zero_propagates
#print axioms HRTLambda0.fibre_dichotomy
#print axioms HRTLambda0.degree_identity_kills
#print axioms HRTLambda0.two_of_three_eq_of_quadratic
#print axioms HRTLambda0.circle_pair_quadratic
#print axioms HRTLambda0.hrt_endgame
#print axioms HRTLambda0.lambda0_independent_of_reduction
