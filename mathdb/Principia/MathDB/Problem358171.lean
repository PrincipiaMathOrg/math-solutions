import Mathlib

set_option autoImplicit false

/-!
# MathDB #358171 — Cohen's two polynomial difference equations

Write-up `mathdb-open-problems/problems/358171/solution.tex`,
*Explicit polynomial solutions of Cohen's two difference equations*, 18 September 2026.

For `u : ℕ` put `N = u(u+3)`, `λ = 2u²+8u+7`, `μ = (2u+3)(N+1)`.  Cohen's Conjecture 4.2
asks for nonzero polynomial solutions of

  (1)  `(x+2u+4)(x+u+1) P(x+1) − (x−1)(x+u−1) P(x−1) = (λx+μ) P(x)`
  (2)  `(x+2u+4)(x+u+4) Q(x+1) − (x−1)(x+u+2) Q(x−1) = (λx+(2u+3)(u+2)(u+3)) Q(x)`

and predicts that each solution space in `ℚ[x]` is one-dimensional with every nonzero
solution of degree `N`.  Degree, uniqueness-given-existence and the equivalence of the two
equations are due to Mueller; the write-up supplies the missing EXISTENCE proof.

## What this module contains

This is a **SPINE** in the sense of the project's spine rule: the chain of inferences to the
conjecture is written out with every gap a named hypothesis, and the gaps are then filled one
at a time.  `cohen_spine` is the composition; it typechecks, so the decomposition is a fact
rather than a plan.

**The write-up's Lemma 1 is PROVED here**: `hrec` is its coefficient recurrence and
`odeH : OdeH u` is the polynomial differential equation itself, so `cohen_spine` carries
exactly ONE hypothesis.  Proved here, besides Lemma 1: the reflection (equation (2) follows
from equation (1) by `y = -x-2u-3`), Mueller's degree argument (every nonzero solution of
(1) has degree `N`), uniqueness up to a nonzero scalar, and `Pconstr u ≠ 0` (its degree-`N`
coefficient is `2^(N+1) h_(N+1) / N!`).  What remains assumed is ONLY
`OdeH u → SolvesFirst u (Pconstr u)` — the write-up's residue computation, which is the
whole of the missing existence proof.

`hrec` is worth isolating because it is where the parameters are pinned: the odd-index case
collapses to `u² + 3u − N = 0`, which is the *definition* of `N`, and the even-index case to
an identity in `k` and `K` alone.  Both are `ring` facts once the coefficients are unfolded,
and neither needs the residue calculus the rest of the write-up runs on.

## The residue is NOT needed

The write-up defines `P` by a residue, `P(x) = Res_{t=0} e^{(x+u)t} H(coth(t/2)) dt`, but
immediately gives an equivalent **completely finite** expression, its equation (finite).
`Pconstr` below is that finite form, so no germ, Laurent series or residue appears anywhere
in this module.  What remains genuinely open for this row is the passage from `OdeH` to
`SolvesFirst (Pconstr u)`; the write-up does it through the residue identities, and finding a
finite-algebra route is the next piece of work, not a transcription job.

## Checked in SymPy before formalizing

`Campaigns/MathDB-Formalization/verify_358171.py`: both coefficient identities symbolically;
the three-term recurrence and the differential equation for `H` at `u = 0..6`; and, for
`u = 0..4`, that `Pconstr` is nonzero, has degree exactly `N`, satisfies (1), and that
`Q(x) = P(−x−2u−3)` satisfies (2).
-/

namespace Principia.MathDB.P358171

open Polynomial

/-! ### Parameters -/

/-- `N = u(u+3)`; it is always even. -/
def Nn (u : ℕ) : ℕ := u * (u + 3)

noncomputable def Nq (u : ℕ) : ℚ := (u : ℚ) * ((u : ℚ) + 3)

noncomputable def Dq (u : ℕ) : ℚ := Nq u + 2 * (u : ℚ) + 5

noncomputable def Kq (u : ℕ) : ℚ := Nq u + (u : ℚ) + 3

noncomputable def lamq (u : ℕ) : ℚ := 2 * (u : ℚ) ^ 2 + 8 * (u : ℚ) + 7

noncomputable def muq (u : ℕ) : ℚ := (2 * (u : ℚ) + 3) * (Nq u + 1)

theorem Nn_even (u : ℕ) : Even (Nn u) := by
  rcases Nat.even_or_odd u with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (u + 3), by rw [Nn, hm]; ring⟩
  · exact ⟨u * (m + 2), by rw [Nn, hm]; ring⟩

/-- `D = N + 2u + 5` is ODD, so it is never twice a natural number.  Every denominator in
the construction is of this shape, which is why none of them vanishes. -/
theorem two_sub_D_ne (u k : ℕ) : 2 * (k : ℚ) - Dq u ≠ 0 := by
  intro hcon
  have hq : ((2 * k : ℕ) : ℚ) = ((Nn u + 2 * u + 5 : ℕ) : ℚ) := by
    have hN : ((Nn u : ℕ) : ℚ) = Nq u := by
      simp only [Nn, Nq]; push_cast; ring
    push_cast [hN]
    simp only [Dq] at hcon
    linarith
  have hn : 2 * k = Nn u + 2 * u + 5 := by exact_mod_cast hq
  obtain ⟨r, hr⟩ := Nn_even u
  omega

/-! ### The coefficients `e` and `h` of the write-up's `H` -/

/-- `e_{k+1}/e_k = (2k−N)(2k+1) / (2(k+1)(2k−D))`.  Because `2n = N`, this recursion makes
`e` vanish from `k = n+1` on by itself — no explicit cutoff is needed. -/
noncomputable def ec (u : ℕ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => ec u k * ((2 * (k : ℚ) - Nq u) * (2 * (k : ℚ) + 1))
      / (2 * ((k : ℚ) + 1) * (2 * (k : ℚ) - Dq u))

/-- `h_{2k} = e_k`, `h_{2k+1} = ((2k−K)/(2k−D)) e_k`. -/
noncomputable def hc (u : ℕ) (j : ℕ) : ℚ :=
  if j % 2 = 0 then ec u (j / 2)
  else ((2 * ((j / 2 : ℕ) : ℚ) - Kq u) / (2 * ((j / 2 : ℕ) : ℚ) - Dq u)) * ec u (j / 2)

theorem hc_even (u m : ℕ) : hc u (2 * m) = ec u m := by
  have h1 : (2 * m) % 2 = 0 := by omega
  have h2 : (2 * m) / 2 = m := by omega
  simp [hc, h1, h2]

theorem hc_odd (u m : ℕ) :
    hc u (2 * m + 1)
      = ((2 * (m : ℚ) - Kq u) / (2 * (m : ℚ) - Dq u)) * ec u m := by
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  simp [hc, h1, h2]

/-! ### The coefficient recurrence — the write-up's Lemma 1

The coefficient of `z^j` in `z(z²−1)H'' + (−Nz²+3z+D)H' − KH` is

  `(j−1)(j−2−N) h_{j−1} + (3j−K) h_j + (j+1)(D−j) h_{j+1}`.

`hrec u j` is that expression at index `j+1`, which avoids ℕ-subtraction entirely and lets
the `j = 0` case (where `h_{-1}` is absent) be stated separately as `hrec_zero`. -/

theorem hrec_zero (u : ℕ) : (0 - Kq u) * hc u 0 + (Dq u - 0) * hc u 1 = 0 := by
  have hD : (0 : ℚ) - Dq u ≠ 0 := by
    have := two_sub_D_ne u 0; simpa using this
  have h0 : hc u 0 = 1 := by
    have : hc u (2 * 0) = ec u 0 := hc_even u 0
    simpa [ec] using this
  have h1 : hc u 1 = ((0 - Kq u) / (0 - Dq u)) * 1 := by
    have : hc u (2 * 0 + 1)
        = ((2 * ((0 : ℕ) : ℚ) - Kq u) / (2 * ((0 : ℕ) : ℚ) - Dq u)) * ec u 0 :=
      hc_odd u 0
    simpa [ec] using this
  rw [h0, h1]
  field_simp
  ring

/-- **The write-up's Lemma 1, in coefficient form.**  Proved, and it is the only link of the
spine's differential equation rests on; `odeH` turns it into the equation itself. -/
theorem hrec (u j : ℕ) :
    (j : ℚ) * ((j : ℚ) - 1 - Nq u) * hc u j
      + (3 * ((j : ℚ) + 1) - Kq u) * hc u (j + 1)
      + ((j : ℚ) + 2) * (Dq u - ((j : ℚ) + 1)) * hc u (j + 2) = 0 := by
  rcases Nat.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- `j = 2m`: indices `2m`, `2m+1`, `2m+2`
    have hj : j = 2 * m := by omega
    subst hj
    have hD : 2 * (m : ℚ) - Dq u ≠ 0 := two_sub_D_ne u m
    have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
    have e1 : hc u (2 * m) = ec u m := hc_even u m
    have e2 : hc u (2 * m + 1)
        = ((2 * (m : ℚ) - Kq u) / (2 * (m : ℚ) - Dq u)) * ec u m := hc_odd u m
    have e3 : hc u (2 * m + 2) = ec u m * ((2 * (m : ℚ) - Nq u) * (2 * (m : ℚ) + 1))
        / (2 * ((m : ℚ) + 1) * (2 * (m : ℚ) - Dq u)) := by
      have : hc u (2 * (m + 1)) = ec u (m + 1) := hc_even u (m + 1)
      rw [show 2 * m + 2 = 2 * (m + 1) by ring, this, ec]
    rw [e1, e2, e3]
    push_cast
    field_simp
    simp only [Nq, Dq, Kq]
    ring
  · -- `j = 2m+1`: indices `2m+1`, `2m+2`, `2m+3`
    have hj : j = 2 * m + 1 := by omega
    subst hj
    have hD : 2 * (m : ℚ) - Dq u ≠ 0 := two_sub_D_ne u m
    have hD' : 2 * ((m : ℚ) + 1) - Dq u ≠ 0 := by
      have := two_sub_D_ne u (m + 1); push_cast at this; convert this using 2
    have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
    have e1 : hc u (2 * m + 1)
        = ((2 * (m : ℚ) - Kq u) / (2 * (m : ℚ) - Dq u)) * ec u m := hc_odd u m
    have ecs : ec u (m + 1) = ec u m * ((2 * (m : ℚ) - Nq u) * (2 * (m : ℚ) + 1))
        / (2 * ((m : ℚ) + 1) * (2 * (m : ℚ) - Dq u)) := by rw [ec]
    have e2 : hc u (2 * m + 2) = ec u (m + 1) := by
      rw [show 2 * m + 2 = 2 * (m + 1) by ring]; exact hc_even u (m + 1)
    have e3 : hc u (2 * m + 3)
        = ((2 * ((m : ℚ) + 1) - Kq u) / (2 * ((m : ℚ) + 1) - Dq u)) * ec u (m + 1) := by
      have : hc u (2 * (m + 1) + 1)
          = ((2 * (((m + 1 : ℕ)) : ℚ) - Kq u) / (2 * (((m + 1 : ℕ)) : ℚ) - Dq u))
            * ec u (m + 1) := hc_odd u (m + 1)
      rw [show 2 * m + 3 = 2 * (m + 1) + 1 by ring]
      push_cast at this
      exact this
    rw [e1, e2, e3, ecs]
    push_cast
    field_simp
    simp only [Nq, Dq, Kq]
    ring

/-! ### The objects the conjecture is about -/

/-- `H(z) = ∑_{j≤N+1} h_j z^j`. -/
noncomputable def Hpoly (u : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (Nn u + 2), C (hc u j) * X ^ j

/-- The write-up's equation (Heqn). -/
def OdeH (u : ℕ) : Prop :=
  X * (X ^ 2 - 1) * derivative (derivative (Hpoly u))
    + (C (-(Nq u)) * X ^ 2 + 3 * X + C (Dq u)) * derivative (Hpoly u)
    - C (Kq u) * Hpoly u = 0

/-! ### `OdeH` is a THEOREM

`hrec` says the write-up's three-term expression vanishes at every index.  What remains is
the bookkeeping that identifies that expression with the coefficient of `z^j` in the ODE's
left-hand side.  Two facts make it finite: `hc` vanishes past `N+1` (because the
`e`-recursion kills itself at `k = n+1`), so `Hpoly`'s coefficients ARE `hc` at every index;
and the `X^3` and `X^2` guards at `j = 0, 1` happen to agree with the `j(j-1-N)` factor,
which vanishes there anyway. -/

/-- Past `k = n` the recursion has already produced a zero factor, so `ec` stays zero. -/
theorem ec_vanish (u : ℕ) : ∀ k : ℕ, Nn u < 2 * k → ec u k = 0 := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _
    rcases Nat.lt_or_ge (Nn u) (2 * k) with h | h
    · rw [ec, ih h]; ring
    · have hev : Nn u = 2 * k := by
        obtain ⟨r, hr⟩ := Nn_even u
        omega
      have hz : 2 * (k : ℚ) - Nq u = 0 := by
        have : ((Nn u : ℕ) : ℚ) = Nq u := by simp only [Nn, Nq]; push_cast; ring
        rw [← this, hev]; push_cast; ring
      rw [ec, hz]
      ring

theorem hc_vanish (u j : ℕ) (hj : Nn u + 2 ≤ j) : hc u j = 0 := by
  have h2 : Nn u < 2 * (j / 2) := by
    obtain ⟨r, hr⟩ := Nn_even u
    omega
  have := ec_vanish u (j / 2) h2
  simp [hc, this]

theorem coeff_Hpoly (u j : ℕ) : (Hpoly u).coeff j = hc u j := by
  rw [Hpoly, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (Nn u + 2)) j (fun i => hc u i)]
  split_ifs with h
  · rfl
  · have hj : ¬ j < Nn u + 2 := fun hlt => h (Finset.mem_range.mpr hlt)
    exact (hc_vanish u j (by omega)).symm

theorem coeff_d1 (u n : ℕ) :
    (derivative (Hpoly u)).coeff n = hc u (n + 1) * ((n : ℚ) + 1) := by
  rw [coeff_derivative, coeff_Hpoly]

theorem coeff_d2 (u n : ℕ) :
    (derivative (derivative (Hpoly u))).coeff n
      = hc u (n + 2) * ((n : ℚ) + 2) * ((n : ℚ) + 1) := by
  rw [coeff_derivative, coeff_d1]; push_cast; ring

/-- The ODE's left-hand side, normalised so every factor of `X` sits on the right. -/
theorem ode_lhs_eq (u : ℕ) :
    X * (X ^ 2 - 1) * derivative (derivative (Hpoly u))
        + (C (-(Nq u)) * X ^ 2 + 3 * X + C (Dq u)) * derivative (Hpoly u)
        - C (Kq u) * Hpoly u
      = derivative (derivative (Hpoly u)) * X ^ 3
        - derivative (derivative (Hpoly u)) * X
        + derivative (Hpoly u) * X ^ 2 * C (-(Nq u))
        + derivative (Hpoly u) * X * 3
        + derivative (Hpoly u) * C (Dq u)
        - Hpoly u * C (Kq u) := by
  ring

/-- **The write-up's Lemma 1, as a polynomial identity.**  No longer a hypothesis. -/
theorem odeH (u : ℕ) : OdeH u := by
  rw [OdeH, ode_lhs_eq]
  ext i
  rw [coeff_zero]
  simp only [coeff_add, coeff_sub, coeff_mul_C, coeff_mul_X_pow', coeff_ofNat_mul]
  match i with
  | 0 =>
    norm_num [coeff_d1, coeff_d2, coeff_Hpoly]
    linear_combination hrec_zero u
  | 1 =>
    norm_num [coeff_d1, coeff_d2, coeff_Hpoly, coeff_mul_X]
    linear_combination hrec u 0
  | 2 =>
    norm_num [coeff_d1, coeff_d2, coeff_Hpoly, coeff_mul_X]
    linear_combination hrec u 1
  | (k + 3) =>
    have h3 : 3 ≤ k + 3 := by omega
    have h2 : 2 ≤ k + 3 := by omega
    simp only [if_pos h3, if_pos h2, coeff_mul_X,
      show k + 3 - 3 = k from by omega, show k + 3 - 2 = k + 1 from by omega]
    norm_num [coeff_d1, coeff_d2, coeff_Hpoly]
    linear_combination (norm := (push_cast; ring)) hrec u (k + 2)

/-- The generalized binomial `C(x+u−1, ℓ)` as a polynomial in `x`. -/
noncomputable def binomP (u l : ℕ) : ℚ[X] :=
  C (1 / (l.factorial : ℚ)) * ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 1 - (i : ℚ)))

/-- The write-up's equation (finite) — the residue written as a finite sum, so that no
Laurent series or residue is needed to DEFINE the candidate solution. -/
noncomputable def Pconstr (u : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (Nn u + 2), ∑ l ∈ Finset.range j,
    C (hc u j * 2 ^ (l + 1) * ((j.choose (l + 1) : ℕ) : ℚ)) * binomP u l

/-- Equation (1). -/
def SolvesFirst (u : ℕ) (P : ℚ[X]) : Prop :=
  (X + C (2 * (u : ℚ) + 4)) * (X + C ((u : ℚ) + 1)) * P.comp (X + 1)
      - (X - 1) * (X + C ((u : ℚ) - 1)) * P.comp (X - 1)
    = (C (lamq u) * X + C (muq u)) * P

/-- Equation (2). -/
def SolvesSecond (u : ℕ) (Q : ℚ[X]) : Prop :=
  (X + C (2 * (u : ℚ) + 4)) * (X + C ((u : ℚ) + 4)) * Q.comp (X + 1)
      - (X - 1) * (X + C ((u : ℚ) + 2)) * Q.comp (X - 1)
    = (C (lamq u) * X + C ((2 * (u : ℚ) + 3) * ((u : ℚ) + 2) * ((u : ℚ) + 3))) * Q

/-! ### The reflection `Q(x) = P(-x-2u-3)`

The write-up's last step: substitute `y = -x-2u-3` into (1) and multiply by `-1`.  The two
shifted coefficients interchange, and the constant term works out because

  `lambda*(2u+3) - mu = (2u+3)(u+2)(u+3)`,

which is exactly the constant of (2).  Over `ℚ` a polynomial identity can be checked
pointwise (`Polynomial.funext`), which turns the whole step into scalar algebra and avoids
composing the equation with `-X - C (2u+3)` term by term. -/

theorem lam_mul_sub_mu (u : ℕ) :
    lamq u * (2 * (u : ℚ) + 3) - muq u
      = (2 * (u : ℚ) + 3) * ((u : ℚ) + 2) * ((u : ℚ) + 3) := by
  simp only [lamq, muq, Nq]
  ring

/-- **Equation (2) from equation (1).** -/
theorem reflect (u : ℕ) (P : ℚ[X]) (h : SolvesFirst u P) :
    SolvesSecond u (P.comp (-X - C (2 * (u : ℚ) + 3))) := by
  rw [SolvesFirst] at h
  rw [SolvesSecond]
  refine Polynomial.funext (fun x => ?_)
  have hy := congrArg (Polynomial.eval (-x - (2 * (u : ℚ) + 3))) h
  have hlm := lam_mul_sub_mu u
  simp only [eval_add, eval_sub, eval_mul, eval_neg, eval_X, eval_C, eval_one,
    eval_comp] at hy ⊢
  ring_nf at hy ⊢
  linear_combination (norm := ring_nf) -hy + Polynomial.eval
    (-x - (2 * (u : ℚ) + 3)) P * hlm

/-! ### Mueller's degree argument

If a nonzero `P` of degree `d` and leading coefficient `a` satisfies (1), the coefficient of
`x^(d+1)` in the residual is `a(2d + 2u + 7 - lambda) = 2a(d - N)`, so `d = N`.  The only
delicate input is the SUBLEADING coefficient of `P(x+1)`, which Mathlib has no lemma for;
`Polynomial.taylor` supplies it, since `(P.comp (X + C r)).coeff n = (hasseDeriv n P).eval r`
and `hasseDeriv e P` has degree at most one when `P` has degree `e+1`. -/

section Degree

theorem comp_coeff_eval (P : ℚ[X]) (r : ℚ) (n : ℕ) :
    (P.comp (X + C r)).coeff n = (hasseDeriv n P).eval r := by
  rw [← taylor_apply, taylor_coeff]

theorem hasse_coeff' (P : ℚ[X]) (k n : ℕ) :
    (hasseDeriv k P).coeff n = ((n + k).choose k : ℚ) * P.coeff (n + k) := by
  rw [hasseDeriv_coeff]

theorem comp_above (P : ℚ[X]) (r : ℚ) (d : ℕ) (hd : P.natDegree = d) :
    (P.comp (X + C r)).coeff (d + 1) = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  simp [natDegree_comp, hd]

theorem comp_top (P : ℚ[X]) (r : ℚ) (d : ℕ) (hd : P.natDegree = d) :
    (P.comp (X + C r)).coeff d = P.coeff d := by
  rw [comp_coeff_eval]
  have hG : hasseDeriv d P = C (P.coeff d) := by
    ext n
    rw [hasse_coeff', coeff_C]
    cases n with
    | zero => simp
    | succ m =>
      rw [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < m + 1 + d)]
      simp
  rw [hG, eval_C]

/-- **The subleading coefficients of `P(x+1)` and `P(x-1)` differ by exactly `2 d a`.**
The `b` terms cancel, which is why the degree argument never needs them. -/
theorem comp_sub_coeff (P : ℚ[X]) (e : ℕ) (hd : P.natDegree = e + 1) :
    (P.comp (X + C (1 : ℚ))).coeff e - (P.comp (X + C (-1 : ℚ))).coeff e
      = 2 * ((e : ℚ) + 1) * P.coeff (e + 1) := by
  rw [comp_coeff_eval, comp_coeff_eval]
  have hdeg : (hasseDeriv e P).natDegree ≤ 1 := by
    refine natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => ?_)
    rw [hasse_coeff', coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < m + e)]
    ring
  have hev : ∀ r : ℚ, (hasseDeriv e P).eval r
      = (hasseDeriv e P).coeff 0 + (hasseDeriv e P).coeff 1 * r := by
    intro r
    rw [eval_eq_sum_range' (by omega : (hasseDeriv e P).natDegree < 2)]
    simp [Finset.sum_range_succ]
  rw [hev, hev]
  have h1 : (hasseDeriv e P).coeff 1 = ((e : ℚ) + 1) * P.coeff (e + 1) := by
    rw [hasse_coeff']
    have hch : (1 + e).choose e = e + 1 := by
      rw [Nat.add_comm]; exact Nat.choose_succ_self_right e
    rw [hch, Nat.add_comm 1 e]
    push_cast
    ring
  rw [h1]
  ring

/-- Coefficients of a monic quadratic times anything, with both guards explicit. -/
theorem quad_mul_coeff (Q : ℚ[X]) (c1 c0 : ℚ) (n : ℕ) :
    ((X ^ 2 + C c1 * X + C c0) * Q).coeff n
      = (if 2 ≤ n then Q.coeff (n - 2) else 0)
        + c1 * (if 1 ≤ n then Q.coeff (n - 1) else 0) + c0 * Q.coeff n := by
  have h : (X ^ 2 + C c1 * X + C c0) * Q
      = Q * X ^ 2 + Q * X ^ 1 * C c1 + Q * C c0 := by ring
  rw [h]
  simp only [coeff_add, coeff_mul_C, coeff_mul_X_pow']
  ring

theorem quadA (u : ℕ) :
    (X + C (2 * (u : ℚ) + 4)) * (X + C ((u : ℚ) + 1))
      = X ^ 2 + C (3 * (u : ℚ) + 5) * X + C ((2 * (u : ℚ) + 4) * ((u : ℚ) + 1)) := by
  simp only [map_add, map_mul, map_one, map_ofNat]
  ring

theorem quadB (u : ℕ) :
    (X - 1) * (X + C ((u : ℚ) - 1))
      = X ^ 2 + C ((u : ℚ) - 2) * X + C (-((u : ℚ) - 1)) := by
  simp only [map_sub, map_mul, map_neg, map_one, map_ofNat]
  ring

theorem lin_mul_coeff (Q : ℚ[X]) (c1 c0 : ℚ) (n : ℕ) :
    ((C c1 * X + C c0) * Q).coeff (n + 1) = c1 * Q.coeff n + c0 * Q.coeff (n + 1) := by
  have h : (C c1 * X + C c0) * Q = C c1 * (X * Q) + C c0 * Q := by ring
  rw [h, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_mul]

/-- **The write-up's degree identity.**  The coefficient of `x^(d+1)` in the residual of
equation (1) is `2 a (d - N)`, where `a` is the leading coefficient. -/
theorem residual_top (u : ℕ) (P : ℚ[X]) :
    ((X + C (2 * (u : ℚ) + 4)) * (X + C ((u : ℚ) + 1)) * P.comp (X + 1)
      - (X - 1) * (X + C ((u : ℚ) - 1)) * P.comp (X - 1)
      - (C (lamq u) * X + C (muq u)) * P).coeff (P.natDegree + 1)
    = 2 * P.coeff P.natDegree * ((P.natDegree : ℚ) - Nq u) := by
  have hX1 : (X + 1 : ℚ[X]) = X + C (1 : ℚ) := by simp
  have hXm1 : (X - 1 : ℚ[X]) = X + C (-1 : ℚ) := by simp [sub_eq_add_neg]
  rw [quadA u, quadB u, hX1, hXm1, coeff_sub, coeff_sub, quad_mul_coeff, quad_mul_coeff,
    lin_mul_coeff]
  simp only [Nat.add_sub_cancel]
  rw [comp_above P 1 _ rfl, comp_above P (-1) _ rfl, comp_top P 1 _ rfl,
    comp_top P (-1) _ rfl,
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self P.natDegree)]
  simp only [if_pos (Nat.le_add_left 1 P.natDegree)]
  split_ifs with hh
  · obtain ⟨e, he⟩ : ∃ e, P.natDegree = e + 1 := ⟨P.natDegree - 1, by omega⟩
    rw [show P.natDegree + 1 - 2 = e from by omega]
    have hcs := comp_sub_coeff P e he
    have hcast : ((P.natDegree : ℕ) : ℚ) = (e : ℚ) + 1 := by rw [he]; push_cast; ring
    rw [← he] at hcs
    simp only [lamq, Nq, muq]
    push_cast
    rw [hcast]
    linear_combination hcs
  · have h0 : P.natDegree = 0 := by omega
    rw [h0]
    simp only [lamq, Nq, muq, Nat.cast_zero]
    push_cast
    ring

/-- **Every nonzero solution of (1) has degree `N`.**  Mueller's argument. -/
theorem solves_natDegree (u : ℕ) (P : ℚ[X]) (h : SolvesFirst u P) (hP : P ≠ 0) :
    P.natDegree = Nn u := by
  rw [SolvesFirst] at h
  have hz : ((X + C (2 * (u : ℚ) + 4)) * (X + C ((u : ℚ) + 1)) * P.comp (X + 1)
      - (X - 1) * (X + C ((u : ℚ) - 1)) * P.comp (X - 1)
      - (C (lamq u) * X + C (muq u)) * P) = 0 := by
    rw [h]; ring
  have h0 := congrArg (fun q : ℚ[X] => q.coeff (P.natDegree + 1)) hz
  simp only [coeff_zero] at h0
  rw [residual_top u P] at h0
  have ha : P.coeff P.natDegree ≠ 0 := by
    rw [← leadingCoeff]
    exact leadingCoeff_ne_zero.mpr hP
  have hq : ((P.natDegree : ℚ) - Nq u) = 0 := by
    rcases mul_eq_zero.mp h0 with hc | hc
    · rcases mul_eq_zero.mp hc with hc' | hc'
      · norm_num at hc'
      · exact absurd hc' ha
    · exact hc
  have hN : ((Nn u : ℕ) : ℚ) = Nq u := by simp only [Nn, Nq]; push_cast; ring
  have : ((P.natDegree : ℕ) : ℚ) = ((Nn u : ℕ) : ℚ) := by rw [hN]; linarith
  exact_mod_cast this

/-- The solution set of (1) is closed under subtraction … -/
theorem solves_sub (u : ℕ) (P Q : ℚ[X]) (hP : SolvesFirst u P) (hQ : SolvesFirst u Q) :
    SolvesFirst u (P - Q) := by
  rw [SolvesFirst] at hP hQ ⊢
  rw [sub_comp, sub_comp]
  linear_combination hP - hQ

/-- … and under scaling by a constant. -/
theorem solves_smul (u : ℕ) (c : ℚ) (P : ℚ[X]) (hP : SolvesFirst u P) :
    SolvesFirst u (C c * P) := by
  rw [SolvesFirst] at hP ⊢
  rw [mul_comp, mul_comp, C_comp, C_comp]
  linear_combination C c * hP

/-- **Uniqueness up to a nonzero scalar.**  Two nonzero solutions both have degree `N`, so a
suitable combination has smaller degree and must therefore vanish. -/
theorem uniqueness (u : ℕ) (P Q : ℚ[X]) (hP : SolvesFirst u P) (hQ : SolvesFirst u Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) : ∃ c : ℚ, c ≠ 0 ∧ Q = C c * P := by
  have hlcP : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  have hlcQ : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ0
  refine ⟨Q.leadingCoeff / P.leadingCoeff, div_ne_zero hlcQ hlcP, ?_⟩
  set c : ℚ := Q.leadingCoeff / P.leadingCoeff with hcdef
  have hc : c ≠ 0 := div_ne_zero hlcQ hlcP
  by_contra hne
  have hR0 : Q - C c * P ≠ 0 := sub_ne_zero.mpr hne
  have hRs : SolvesFirst u (Q - C c * P) :=
    solves_sub u Q _ hQ (solves_smul u c P hP)
  have hdQ := solves_natDegree u Q hQ hQ0
  have hdR := solves_natDegree u _ hRs hR0
  have hCP0 : C c * P ≠ 0 := mul_ne_zero (by simpa using hc) hP0
  have hdeg : (C c * P).degree = Q.degree := by
    rw [degree_mul, degree_C hc, zero_add, degree_eq_natDegree hP0,
      degree_eq_natDegree hQ0, solves_natDegree u P hP hP0, hdQ]
  have hlead : Q.leadingCoeff = (C c * P).leadingCoeff := by
    rw [leadingCoeff_mul, leadingCoeff_C, hcdef]
    field_simp
  have hlt : (Q - C c * P).degree < Q.degree :=
    degree_sub_lt hdeg.symm hQ0 hlead
  have := natDegree_lt_natDegree hR0 hlt
  omega

end Degree


/-! ### `Pconstr` is nonzero

The write-up's leading coefficient is `[x^N] P = 2^(N+1) h_(N+1) / N!`, nonzero because
`h_(N+1) = e_n (u+3)/(2u+5)` and `e_n ≠ 0`.  In the finite expression only the pair
`(j, l) = (N+1, N)` reaches degree `N`, since `binomP u l` has degree exactly `l`. -/

section Nonvanishing

theorem ec_ne_zero (u : ℕ) : ∀ k : ℕ, 2 * k ≤ Nn u → ec u k ≠ 0 := by
  intro k
  induction k with
  | zero => intro _; simp [ec]
  | succ k ih =>
    intro hk
    have hih : ec u k ≠ 0 := ih (by omega)
    have hN : ((Nn u : ℕ) : ℚ) = Nq u := by simp only [Nn, Nq]; push_cast; ring
    have h1 : 2 * (k : ℚ) - Nq u ≠ 0 := by
      rw [← hN]
      intro hcon
      have : ((2 * k : ℕ) : ℚ) = ((Nn u : ℕ) : ℚ) := by push_cast; push_cast at hcon; linarith
      have : 2 * k = Nn u := by exact_mod_cast this
      omega
    have h2 : 2 * (k : ℚ) + 1 ≠ 0 := by positivity
    have h3 : 2 * ((k : ℚ) + 1) ≠ 0 := by positivity
    have h4 := two_sub_D_ne u k
    rw [ec]
    exact div_ne_zero (mul_ne_zero hih (mul_ne_zero h1 h2)) (mul_ne_zero h3 h4)

/-- `h_(N+1) ≠ 0`; it equals `e_n (u+3)/(2u+5)`. -/
theorem hc_top_ne_zero (u : ℕ) : hc u (Nn u + 1) ≠ 0 := by
  obtain ⟨n, hn⟩ := Nn_even u
  have hn2 : Nn u = 2 * n := by omega
  have he : ec u n ≠ 0 := ec_ne_zero u n (by omega)
  have hN : ((Nn u : ℕ) : ℚ) = Nq u := by simp only [Nn, Nq]; push_cast; ring
  have hnq : 2 * (n : ℚ) = Nq u := by
    rw [← hN, hn2]; push_cast; ring
  rw [hn2, hc_odd]
  refine mul_ne_zero (div_ne_zero ?_ (two_sub_D_ne u n)) he
  rw [hnq]
  simp only [Kq]
  intro hcon
  have : ((u : ℚ) + 3) = 0 := by linarith
  have hu : (0 : ℚ) ≤ (u : ℚ) := Nat.cast_nonneg u
  linarith

theorem binomP_prod_monic (u l : ℕ) :
    (∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 1 - (i : ℚ)))).Monic :=
  monic_prod_of_monic _ _ (fun i _ => monic_X_add_C _)

theorem binomP_prod_natDegree (u l : ℕ) :
    (∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 1 - (i : ℚ)))).natDegree = l := by
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C _)]
  simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul,
    mul_one]

theorem fact_ne (l : ℕ) : ((l.factorial : ℕ) : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero l)

theorem binomP_natDegree (u l : ℕ) : (binomP u l).natDegree = l := by
  rw [binomP, natDegree_C_mul (one_div_ne_zero (fact_ne l))]
  exact binomP_prod_natDegree u l

theorem binomP_coeff_self (u l : ℕ) :
    (binomP u l).coeff l = 1 / ((l.factorial : ℕ) : ℚ) := by
  rw [binomP, coeff_C_mul]
  have hm := binomP_prod_monic u l
  have hd := binomP_prod_natDegree u l
  have h1 := hm.coeff_natDegree
  rw [hd] at h1
  rw [h1, mul_one]

/-- **The leading coefficient of the explicit solution.** -/
theorem Pconstr_coeff_N (u : ℕ) :
    (Pconstr u).coeff (Nn u)
      = hc u (Nn u + 1) * 2 ^ (Nn u + 1) / (((Nn u).factorial : ℕ) : ℚ) := by
  rw [Pconstr, finsetSum_coeff, Finset.sum_eq_single (Nn u + 1)]
  · rw [finsetSum_coeff, Finset.sum_eq_single (Nn u)]
    · rw [coeff_C_mul, binomP_coeff_self, Nat.choose_self]
      push_cast
      ring
    · intro l hl hne
      rw [coeff_C_mul,
        coeff_eq_zero_of_natDegree_lt (by
          rw [binomP_natDegree]; simp only [Finset.mem_range] at hl; omega)]
      ring
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by omega)) hmem
  · intro j hj hne
    rw [finsetSum_coeff]
    refine Finset.sum_eq_zero (fun l hl => ?_)
    rw [coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt (by
        rw [binomP_natDegree]
        simp only [Finset.mem_range] at hj hl
        omega)]
    ring
  · intro hmem
    exact absurd (Finset.mem_range.mpr (by omega)) hmem

theorem Pconstr_coeff_N_ne_zero (u : ℕ) : (Pconstr u).coeff (Nn u) ≠ 0 := by
  rw [Pconstr_coeff_N]
  refine div_ne_zero (mul_ne_zero (hc_top_ne_zero u) ?_) (fact_ne _)
  positivity

theorem Pconstr_ne_zero (u : ℕ) : Pconstr u ≠ 0 := by
  intro hzero
  have h := Pconstr_coeff_N_ne_zero u
  rw [hzero, coeff_zero] at h
  exact h rfl

/-- Every summand of `Pconstr` is a scalar times `binomP u l` with `l < j ≤ N+1`, so the
whole sum has degree at most `N`. -/
theorem Pconstr_natDegree_le (u : ℕ) : (Pconstr u).natDegree ≤ Nn u := by
  rw [Pconstr]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j hj => ?_)
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun l hl => ?_)
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [Polynomial.natDegree_C, zero_add, binomP_natDegree]
  simp only [Finset.mem_range] at hj hl
  omega

/-- **The degree of the explicit solution, UNCONDITIONALLY.**

The spine previously read this off `solves_natDegree` applied to the CARRIED hypothesis
`solvesOfOde`, so "the candidate has the right degree" rested on "the candidate solves the
equation".  It does not need to: the upper bound is a property of the construction (every
summand is a scalar times `binomP u l` with `l ≤ N`), and the lower bound is
`Pconstr_coeff_N`, which was already proved unconditionally.  So one of the spine's four
conclusions no longer depends on the residue step at all. -/
theorem Pconstr_natDegree (u : ℕ) : (Pconstr u).natDegree = Nn u :=
  le_antisymm (Pconstr_natDegree_le u)
    (Polynomial.le_natDegree_of_ne_zero (Pconstr_coeff_N_ne_zero u))

end Nonvanishing

/-! ### Equation (1) is TRIDIAGONAL in the binomial basis

`binomP u l` is `C(x+u−1, l)`, and this basis is adapted to the shift `x ↦ x ± 1`.  Three
product identities carry the whole step:

* `(X + (u−1−l)) · b_l = (l+1) · b_{l+1}`                        (`binomP_succ`)
* `(X + (u−l)) · b_l(x+1) = (X + u) · b_l`                        (`binomP_comp_add_one`)
* `(X + (u−1)) · b_l(x−1) = (X + (u−1−l)) · b_l`                  (`binomP_comp_sub_one`)

Each trades a shifted binomial for an unshifted one at the cost of a single linear factor.
Multiplying the residual of equation (1) at `b_m` by `(X + (u−m))(X + (u−1))` therefore
turns every term into a polynomial multiple of `b_m` alone, and what is left after
cancelling `b_m` is a degree-3 scalar identity in `x`, polynomial in `u` and `m`, which
`ring` closes.  The consequence is that equation (1)'s operator is **tridiagonal** in this
basis, so the equation for a polynomial written in it is an ordinary three-term recurrence
on the coefficients — with no residue, Laurent series or contour integral anywhere. -/

section Tridiagonal

open Finset

/-- `(X + (u−1−l)) · b_l = (l+1) · b_{l+1}`: climbing the basis is one linear factor. -/
theorem binomP_succ (u l : ℕ) :
    (X + C ((u : ℚ) - 1 - (l : ℚ))) * binomP u l
      = C ((l : ℚ) + 1) * binomP u (l + 1) := by
  have hs : (1 : ℚ) / (l.factorial : ℚ)
      = ((l : ℚ) + 1) * (1 / ((l + 1).factorial : ℚ)) := by
    rw [Nat.factorial_succ]
    have h := fact_ne l
    push_cast
    field_simp
  rw [binomP, binomP, Finset.prod_range_succ, hs, C_mul]
  push_cast
  ring

/-- `(X + (u−l)) · ∏_{i<l}(X + (u−i)) = (X + u) · ∏_{i<l}(X + (u−1−i))`. -/
theorem prod_shift_up (u l : ℕ) :
    (X + C ((u : ℚ) - (l : ℚ))) * ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - (i : ℚ)))
      = (X + C (u : ℚ)) * ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 1 - (i : ℚ))) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have hcast : ((l : ℚ) + 1) = (((l + 1 : ℕ) : ℚ)) := by push_cast; ring
    have hstep : (u : ℚ) - (((l + 1 : ℕ) : ℚ)) = (u : ℚ) - 1 - (l : ℚ) := by
      push_cast; ring
    calc (X + C ((u : ℚ) - (((l + 1 : ℕ) : ℚ)))) *
          ((∏ i ∈ Finset.range l, (X + C ((u : ℚ) - (i : ℚ)))) *
            (X + C ((u : ℚ) - (l : ℚ))))
        = (X + C ((u : ℚ) - (((l + 1 : ℕ) : ℚ)))) *
            ((X + C ((u : ℚ) - (l : ℚ))) *
              ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - (i : ℚ)))) := by ring
      _ = (X + C ((u : ℚ) - (((l + 1 : ℕ) : ℚ)))) *
            ((X + C (u : ℚ)) *
              ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 1 - (i : ℚ)))) := by rw [ih]
      _ = (X + C (u : ℚ)) *
            ((∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 1 - (i : ℚ)))) *
              (X + C ((u : ℚ) - 1 - (l : ℚ)))) := by rw [hstep]; ring

/-- `(X + (u−1)) · ∏_{i<l}(X + (u−2−i)) = (X + (u−1−l)) · ∏_{i<l}(X + (u−1−i))`. -/
theorem prod_shift_down (u l : ℕ) :
    (X + C ((u : ℚ) - 1)) * ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 2 - (i : ℚ)))
      = (X + C ((u : ℚ) - 1 - (l : ℚ))) *
          ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 1 - (i : ℚ))) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have hstep : (u : ℚ) - 1 - (((l + 1 : ℕ) : ℚ)) = (u : ℚ) - 2 - (l : ℚ) := by
      push_cast; ring
    calc (X + C ((u : ℚ) - 1)) *
          ((∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 2 - (i : ℚ)))) *
            (X + C ((u : ℚ) - 2 - (l : ℚ))))
        = ((X + C ((u : ℚ) - 1)) *
            ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 2 - (i : ℚ)))) *
            (X + C ((u : ℚ) - 2 - (l : ℚ))) := by ring
      _ = ((X + C ((u : ℚ) - 1 - (l : ℚ))) *
            ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 1 - (i : ℚ)))) *
            (X + C ((u : ℚ) - 2 - (l : ℚ))) := by rw [ih]
      _ = (X + C ((u : ℚ) - 1 - (((l + 1 : ℕ) : ℚ)))) *
            ((∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 1 - (i : ℚ)))) *
              (X + C ((u : ℚ) - 1 - (l : ℚ)))) := by rw [hstep]; ring

/-- `b_l(x+1)` is the same product with `u` in place of `u−1`. -/
theorem binomP_comp_add_one_aux (u l : ℕ) :
    (binomP u l).comp (X + 1)
      = C (1 / (l.factorial : ℚ)) * ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - (i : ℚ))) := by
  rw [binomP, mul_comp, C_comp, Polynomial.prod_comp]
  refine congrArg _ (Finset.prod_congr rfl (fun i _ => ?_))
  rw [add_comp, X_comp, C_comp]
  rw [show ((u : ℚ) - (i : ℚ)) = 1 + ((u : ℚ) - 1 - (i : ℚ)) from by ring, C_add, C_1]
  ring

/-- `b_l(x−1)` is the same product with `u−1` in place of `u`. -/
theorem binomP_comp_sub_one_aux (u l : ℕ) :
    (binomP u l).comp (X - 1)
      = C (1 / (l.factorial : ℚ)) *
          ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 2 - (i : ℚ))) := by
  rw [binomP, mul_comp, C_comp, Polynomial.prod_comp]
  refine congrArg _ (Finset.prod_congr rfl (fun i _ => ?_))
  rw [add_comp, X_comp, C_comp]
  rw [show ((u : ℚ) - 2 - (i : ℚ)) = -1 + ((u : ℚ) - 1 - (i : ℚ)) from by ring, C_add]
  simp only [map_neg, C_1]
  ring

/-- **`(X + (u−l)) · b_l(x+1) = (X + u) · b_l`** — the forward shift, at one linear factor. -/
theorem binomP_comp_add_one (u l : ℕ) :
    (X + C ((u : ℚ) - (l : ℚ))) * (binomP u l).comp (X + 1)
      = (X + C (u : ℚ)) * binomP u l := by
  rw [binomP_comp_add_one_aux, binomP]
  calc (X + C ((u : ℚ) - (l : ℚ))) *
        (C (1 / (l.factorial : ℚ)) *
          ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - (i : ℚ))))
      = C (1 / (l.factorial : ℚ)) *
          ((X + C ((u : ℚ) - (l : ℚ))) *
            ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - (i : ℚ)))) := by ring
    _ = C (1 / (l.factorial : ℚ)) *
          ((X + C (u : ℚ)) *
            ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 1 - (i : ℚ)))) := by
          rw [prod_shift_up]
    _ = (X + C (u : ℚ)) *
          (C (1 / (l.factorial : ℚ)) *
            ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 1 - (i : ℚ)))) := by ring

/-- **`(X + (u−1)) · b_l(x−1) = (X + (u−1−l)) · b_l`** — the backward shift. -/
theorem binomP_comp_sub_one (u l : ℕ) :
    (X + C ((u : ℚ) - 1)) * (binomP u l).comp (X - 1)
      = (X + C ((u : ℚ) - 1 - (l : ℚ))) * binomP u l := by
  rw [binomP_comp_sub_one_aux, binomP]
  calc (X + C ((u : ℚ) - 1)) *
        (C (1 / (l.factorial : ℚ)) *
          ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 2 - (i : ℚ))))
      = C (1 / (l.factorial : ℚ)) *
          ((X + C ((u : ℚ) - 1)) *
            ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 2 - (i : ℚ)))) := by ring
    _ = C (1 / (l.factorial : ℚ)) *
          ((X + C ((u : ℚ) - 1 - (l : ℚ))) *
            ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 1 - (i : ℚ)))) := by
          rw [prod_shift_down]
    _ = (X + C ((u : ℚ) - 1 - (l : ℚ))) *
          (C (1 / (l.factorial : ℚ)) *
            ∏ i ∈ Finset.range l, (X + C ((u : ℚ) - 1 - (i : ℚ)))) := by ring

/-- A monic linear polynomial is nonzero. -/
theorem X_add_C_ne_zero' (a : ℚ) : (X + C a) ≠ (0 : ℚ[X]) := by
  intro h
  have hc := congrArg (fun p : ℚ[X] => p.coeff 1) h
  simp at hc

/-- The residual of equation (1): `SolvesFirst u P` says exactly that it vanishes. -/
noncomputable def Lres (u : ℕ) (P : ℚ[X]) : ℚ[X] :=
  (X + C (2 * (u : ℚ) + 4)) * (X + C ((u : ℚ) + 1)) * P.comp (X + 1)
    - (X - 1) * (X + C ((u : ℚ) - 1)) * P.comp (X - 1)
    - (C (lamq u) * X + C (muq u)) * P

theorem solvesFirst_iff (u : ℕ) (P : ℚ[X]) : SolvesFirst u P ↔ Lres u P = 0 := by
  rw [SolvesFirst, Lres]
  constructor
  · intro h; rw [h]; ring
  · intro h; linear_combination h

/-- The subdiagonal coefficient `α_m = (m+1)(m+u+4)`. -/
noncomputable def alphaC (u m : ℕ) : ℚ := ((m : ℚ) + 1) * ((m : ℚ) + (u : ℚ) + 4)

/-- The diagonal coefficient `β_m = 3m² + (6−2N)m − (3N+u)`. -/
noncomputable def betaC (u m : ℕ) : ℚ :=
  3 * (m : ℚ) ^ 2 + (6 - 2 * Nq u) * (m : ℚ) - (3 * Nq u + (u : ℚ))

/-- The superdiagonal coefficient `γ_m = 2(m+1)(m−N)`. -/
noncomputable def gammaC (u m : ℕ) : ℚ := 2 * ((m : ℚ) + 1) * ((m : ℚ) - Nq u)

set_option maxRecDepth 8000 in
/-- **Equation (1) is TRIDIAGONAL in the binomial basis.**

`L(b_{m+1}) = α_{m+1} b_m + β_{m+1} b_{m+1} + γ_{m+1} b_{m+2}`.  Multiplying through by
`(X + (u−m−1))(X + (u−1))` lets the three basis identities trade every shifted or
off-diagonal binomial for `b_{m+1}` itself; what is left is a degree-3 scalar identity in
`X`, polynomial in `u` and `m`, which `ring` closes.  Both linear factors are monic, hence
nonzero, so the multiplication is cancellable. -/
theorem Lres_binomP_succ (u m : ℕ) :
    Lres u (binomP u (m + 1))
      = C (alphaC u (m + 1)) * binomP u m
        + C (betaC u (m + 1)) * binomP u (m + 1)
        + C (gammaC u (m + 1)) * binomP u (m + 2) := by
  have h1 : (X + C ((u : ℚ) - ((m : ℚ) + 1))) * (binomP u (m + 1)).comp (X + 1)
      = (X + C (u : ℚ)) * binomP u (m + 1) := by
    have h := binomP_comp_add_one u (m + 1)
    rw [show (((m + 1 : ℕ) : ℚ)) = (m : ℚ) + 1 from by push_cast; ring] at h
    exact h
  have h2 : (X + C ((u : ℚ) - 1)) * (binomP u (m + 1)).comp (X - 1)
      = (X + C ((u : ℚ) - ((m : ℚ) + 2))) * binomP u (m + 1) := by
    have h := binomP_comp_sub_one u (m + 1)
    rw [show (((m + 1 : ℕ) : ℚ)) = (m : ℚ) + 1 from by push_cast; ring,
      show (u : ℚ) - 1 - ((m : ℚ) + 1) = (u : ℚ) - ((m : ℚ) + 2) from by ring] at h
    exact h
  have h3 : (X + C ((u : ℚ) - ((m : ℚ) + 1))) * binomP u m
      = C ((m : ℚ) + 1) * binomP u (m + 1) := by
    have h := binomP_succ u m
    rw [show (u : ℚ) - 1 - (m : ℚ) = (u : ℚ) - ((m : ℚ) + 1) from by ring] at h
    exact h
  have h4 : (X + C ((u : ℚ) - ((m : ℚ) + 2))) * binomP u (m + 1)
      = C ((m : ℚ) + 2) * binomP u (m + 2) := by
    have h := binomP_succ u (m + 1)
    rw [show (((m + 1 : ℕ) : ℚ)) = (m : ℚ) + 1 from by push_cast; ring,
      show (u : ℚ) - 1 - ((m : ℚ) + 1) = (u : ℚ) - ((m : ℚ) + 2) from by ring,
      show ((m : ℚ) + 1) + 1 = (m : ℚ) + 2 from by ring] at h
    exact h
  have hM : ((X + C ((u : ℚ) - ((m : ℚ) + 1))) * (X + C ((u : ℚ) - 1)) : ℚ[X]) ≠ 0 :=
    mul_ne_zero (X_add_C_ne_zero' _) (X_add_C_ne_zero' _)
  refine mul_left_cancel₀ hM ?_
  rw [Lres]
  simp only [alphaC, betaC, gammaC, Nq, lamq, muq]
  push_cast
  linear_combination (norm := simp only [C_add, C_sub, C_mul, C_1, C_pow, C_neg,
      Polynomial.C_ofNat] <;> ring)
    ((X + C ((u : ℚ) - 1)) * ((X + C (2 * (u : ℚ) + 4)) * (X + C ((u : ℚ) + 1)))) * h1
      - ((X + C ((u : ℚ) - ((m : ℚ) + 1))) * ((X - 1) * (X + C ((u : ℚ) - 1)))) * h2
      - ((X + C ((u : ℚ) - 1)) * C (((m : ℚ) + 2) * ((m : ℚ) + (u : ℚ) + 5))) * h3
      + ((X + C ((u : ℚ) - ((m : ℚ) + 1))) * (X + C ((u : ℚ) - 1)) *
          C (2 * (((m : ℚ) + 1) - (u : ℚ) * ((u : ℚ) + 3)))) * h4

/-- The `m = 0` end of the tridiagonal identity.  `b_0 = 1`, so there is no subdiagonal
term and the shift lemmas are not needed: the whole thing is scalar algebra. -/
theorem Lres_binomP_zero (u : ℕ) :
    Lres u (binomP u 0)
      = C (betaC u 0) * binomP u 0 + C (gammaC u 0) * binomP u 1 := by
  have hb0 : binomP u 0 = 1 := by simp [binomP]
  have hb1 : binomP u 1 = X + C ((u : ℚ) - 1) := by
    simp [binomP, Finset.prod_range_one]
  rw [Lres, hb0, hb1]
  simp only [betaC, gammaC, Nq, lamq, muq, one_comp, Nat.cast_zero]
  simp only [C_add, C_sub, C_mul, C_1, C_0, C_pow, C_neg, Polynomial.C_ofNat]
  ring

/-! ### The coefficients of `T j`, and the recurrence they satisfy

`T j = ∑_{l<j} c_{j,l} · b_l` with `c_{j,l} = 2^{l+1} C(j, l+1)`.  Because `Lres` is linear
and tridiagonal on the basis, the identity
`L(T j) = j(j−1−N) T(j+1) + (3j−K) T j + j(D−j+1) T(j−1)` — the adjoint of the write-up's
coefficient recurrence — is TERMWISE in `c`, so no linear independence is needed, only
`Finset.sum_congr`.  `cc_recurrence` is that termwise identity.  Its whole content is three
standard facts about `Nat.choose` (absorption twice, and Pascal) plus one scalar identity;
the `(l+2)` factor is there because the step from `c_{j,l+1}` to `c_{j,l}` divides by it. -/

/-- `Nat.choose_succ_right_eq` over `ℚ`, with honest (non-truncated) subtraction. -/
theorem choose_succ_right_rat (n k : ℕ) :
    ((n.choose (k + 1) : ℕ) : ℚ) * ((k : ℚ) + 1)
      = ((n.choose k : ℕ) : ℚ) * ((n : ℚ) - (k : ℚ)) := by
  by_cases h : k ≤ n
  · have hn := Nat.choose_succ_right_eq n k
    have hc : ((n - k : ℕ) : ℚ) = (n : ℚ) - (k : ℚ) := by
      rw [Nat.cast_sub h]
    calc ((n.choose (k + 1) : ℕ) : ℚ) * ((k : ℚ) + 1)
        = ((n.choose (k + 1) * (k + 1) : ℕ) : ℚ) := by push_cast; ring
      _ = ((n.choose k * (n - k) : ℕ) : ℚ) := by rw [hn]
      _ = ((n.choose k : ℕ) : ℚ) * ((n : ℚ) - (k : ℚ)) := by push_cast [hc]; ring
  · have h1 : n.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h1, h2]
    simp

/-- `Nat.succ_mul_choose_eq` over `ℚ`. -/
theorem succ_mul_choose_rat (n k : ℕ) :
    ((n : ℚ) + 1) * ((n.choose k : ℕ) : ℚ)
      = (((n + 1).choose (k + 1) : ℕ) : ℚ) * ((k : ℚ) + 1) := by
  have h := Nat.add_one_mul_choose_eq n k
  calc ((n : ℚ) + 1) * ((n.choose k : ℕ) : ℚ)
      = (((n + 1) * n.choose k : ℕ) : ℚ) := by push_cast; ring
    _ = (((n + 1).choose (k + 1) * (k + 1) : ℕ) : ℚ) := by rw [h]
    _ = (((n + 1).choose (k + 1) : ℕ) : ℚ) * ((k : ℚ) + 1) := by push_cast; ring

/-- The coefficient of `b_l` in `T j`. -/
noncomputable def cc (j l : ℕ) : ℚ := 2 ^ (l + 1) * ((j.choose (l + 1) : ℕ) : ℚ)

/-- **The termwise coefficient identity** — the adjoint of the write-up's recurrence, read
off one basis vector at a time. -/
theorem cc_recurrence (u j l : ℕ) :
    cc (j + 1) (l + 2) * alphaC u (l + 2) + cc (j + 1) (l + 1) * betaC u (l + 1)
        + cc (j + 1) l * gammaC u l
      = (((j : ℚ) + 1) * ((j : ℚ) - Nq u)) * cc (j + 2) (l + 1)
        + (3 * ((j : ℚ) + 1) - Kq u) * cc (j + 1) (l + 1)
        + (((j : ℚ) + 1) * (Dq u - (j : ℚ))) * cc j (l + 1) := by
  have hl2 : ((l : ℚ) + 2) ≠ 0 := by positivity
  refine mul_left_cancel₀ hl2 ?_
  have h1 := choose_succ_right_rat (j + 1) (l + 2)
  have h2 := choose_succ_right_rat (j + 1) (l + 1)
  have h3 : (((j + 2).choose (l + 2) : ℕ) : ℚ)
      = (((j + 1).choose (l + 1) : ℕ) : ℚ) + (((j + 1).choose (l + 2) : ℕ) : ℚ) := by
    rw [show j + 2 = (j + 1) + 1 from rfl, Nat.choose_succ_succ]
    push_cast
    ring
  have h4 := succ_mul_choose_rat j (l + 2)
  simp only [cc, alphaC, betaC, gammaC, Nq, Dq, Kq]
  push_cast at h1 h2 h3 h4 ⊢
  linear_combination
    (((l : ℚ) + 2) * (4 * 2 ^ (l + 1) * ((l : ℚ) + (u : ℚ) + 6)
        - 2 * 2 ^ (l + 1) * ((u : ℚ) * ((u : ℚ) + 3) + 2 * (u : ℚ) + 5 - (j : ℚ)))) * h1
    + (2 * 2 ^ (l + 1) * (3 * ((l : ℚ) + 1) ^ 2
          + (6 - 2 * ((u : ℚ) * ((u : ℚ) + 3))) * ((l : ℚ) + 1)
          - (3 * ((u : ℚ) * ((u : ℚ) + 3)) + (u : ℚ)))
        - 2 * 2 ^ (l + 1) * (3 * ((j : ℚ) + 1)
          - ((u : ℚ) * ((u : ℚ) + 3) + (u : ℚ) + 3))
        + (4 * 2 ^ (l + 1) * ((l : ℚ) + (u : ℚ) + 6)
          - 2 * 2 ^ (l + 1) * ((u : ℚ) * ((u : ℚ) + 3) + 2 * (u : ℚ) + 5 - (j : ℚ)))
            * ((j : ℚ) - (l : ℚ) - 1)
        - 2 * 2 ^ (l + 1) * ((j : ℚ) + 1) * ((j : ℚ) - (u : ℚ) * ((u : ℚ) + 3))) * h2
    + (-(2 * 2 ^ (l + 1) * ((l : ℚ) + 2) * ((j : ℚ) + 1)
        * ((j : ℚ) - (u : ℚ) * ((u : ℚ) + 3)))) * h3
    + (-(2 * 2 ^ (l + 1) * ((l : ℚ) + 2)
        * ((u : ℚ) * ((u : ℚ) + 3) + 2 * (u : ℚ) + 5 - (j : ℚ)))) * h4

/-- `T j = ∑_{l<j} c_{j,l} · b_l`, so that `Pconstr u = ∑_j h_j · T j`. -/
noncomputable def Tpoly (u j : ℕ) : ℚ[X] :=
  ∑ l ∈ Finset.range j, C (cc j l) * binomP u l

theorem cc_eq_zero {j l : ℕ} (h : j ≤ l) : cc j l = 0 := by
  simp [cc, Nat.choose_eq_zero_of_lt (show j < l + 1 by omega)]

/-- `T j` may be summed over any range containing `j`: the extra coefficients vanish. -/
theorem Tpoly_eq_range (u j n : ℕ) (h : j ≤ n) :
    Tpoly u j = ∑ l ∈ Finset.range n, C (cc j l) * binomP u l := by
  rw [Tpoly]
  refine Finset.sum_subset (fun x hx => ?_) (fun l _ hl => ?_)
  · simp only [Finset.mem_range] at hx ⊢
    omega
  · rw [cc_eq_zero (by simpa using hl)]
    simp

theorem Lres_zero (u : ℕ) : Lres u 0 = 0 := by simp [Lres]

theorem Lres_add (u : ℕ) (P Q : ℚ[X]) : Lres u (P + Q) = Lres u P + Lres u Q := by
  simp only [Lres, add_comp]
  ring

theorem Lres_C_mul (u : ℕ) (c : ℚ) (P : ℚ[X]) : Lres u (C c * P) = C c * Lres u P := by
  simp only [Lres, mul_comp, C_comp]
  ring

theorem Lres_sum (u : ℕ) (s : Finset ℕ) (f : ℕ → ℚ[X]) :
    Lres u (∑ l ∈ s, f l) = ∑ l ∈ s, Lres u (f l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Lres_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Lres_add, ih]

/-- The tridiagonal expansion in one statement, valid at every index: at `l = 0` the
subdiagonal term is absent, which is what the `if` records. -/
theorem Lres_binomP (u l : ℕ) :
    Lres u (binomP u l)
      = (if l = 0 then 0 else C (alphaC u l) * binomP u (l - 1))
        + C (betaC u l) * binomP u l + C (gammaC u l) * binomP u (l + 1) := by
  cases l with
  | zero => simpa using Lres_binomP_zero u
  | succ m =>
    rw [Lres_binomP_succ u m]
    simp only [Nat.succ_sub_one, if_neg (Nat.succ_ne_zero m)]

/-- The `l = 0` end of the termwise identity: there is no subdiagonal term, and everything
in sight is a `choose 1` except `(j+1).choose 2`, which `choose_succ_right_rat` supplies. -/
theorem cc_recurrence_zero (u j : ℕ) :
    cc (j + 1) 1 * alphaC u 1 + cc (j + 1) 0 * betaC u 0
      = (((j : ℚ) + 1) * ((j : ℚ) - Nq u)) * cc (j + 2) 0
        + (3 * ((j : ℚ) + 1) - Kq u) * cc (j + 1) 0
        + (((j : ℚ) + 1) * (Dq u - (j : ℚ))) * cc j 0 := by
  have h := choose_succ_right_rat (j + 1) 1
  have e1 : (((j + 1).choose 1 : ℕ) : ℚ) = (j : ℚ) + 1 := by
    rw [Nat.choose_one_right]; push_cast; ring
  have e2 : ((j.choose 1 : ℕ) : ℚ) = (j : ℚ) := by rw [Nat.choose_one_right]
  have e3 : (((j + 2).choose 1 : ℕ) : ℚ) = (j : ℚ) + 2 := by
    rw [Nat.choose_one_right]; push_cast; ring
  rw [e1] at h
  simp only [cc, alphaC, betaC, Nq, Dq, Kq, e1, e2, e3]
  push_cast at h ⊢
  linear_combination (4 * ((u : ℚ) + 5)) * h

/-- **The regrouping.**  Expanding `∑_{l<n} p_l · L(b_l)` with the tridiagonal identity and
collecting by the index of `b` shifts the subdiagonal sum down and the superdiagonal sum up.
Both boundary terms vanish because `p` is supported below `m`, which is why the hypothesis
`m + 1 ≤ n` is the only thing needed. -/
theorem Lres_binom_regroup (u m n : ℕ) (p : ℕ → ℚ) (hp : ∀ l, m ≤ l → p l = 0)
    (hn : m + 1 ≤ n) :
    ∑ l ∈ Finset.range n, C (p l) * Lres u (binomP u l)
      = ∑ l ∈ Finset.range n,
          (C (p (l + 1) * alphaC u (l + 1)) + C (p l * betaC u l)
            + (if l = 0 then 0 else C (p (l - 1) * gammaC u (l - 1)))) * binomP u l := by
  have hL : ∀ l : ℕ, C (p l) * Lres u (binomP u l)
      = (if l = 0 then 0 else C (p l * alphaC u l) * binomP u (l - 1))
        + C (p l * betaC u l) * binomP u l
        + C (p l * gammaC u l) * binomP u (l + 1) := by
    intro l
    rw [Lres_binomP]
    cases l with
    | zero => simp [C_mul]; ring
    | succ k =>
      simp only [if_neg (Nat.succ_ne_zero k), C_mul]
      ring
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
  simp only [hL]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hR : ∀ l : ℕ,
      (C (p (l + 1) * alphaC u (l + 1)) + C (p l * betaC u l)
        + (if l = 0 then 0 else C (p (l - 1) * gammaC u (l - 1)))) * binomP u l
      = C (p (l + 1) * alphaC u (l + 1)) * binomP u l
        + C (p l * betaC u l) * binomP u l
        + (if l = 0 then 0 else C (p (l - 1) * gammaC u (l - 1)) * binomP u l) := by
    intro l
    cases l with
    | zero => simp; ring
    | succ k => simp only [if_neg (Nat.succ_ne_zero k)]; ring
  rw [Finset.sum_congr rfl (fun l _ => hR l), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ rfl) ?_
  · -- the subdiagonal sum shifts DOWN
    rw [Finset.sum_range_succ' (fun l => if l = 0 then (0 : ℚ[X])
      else C (p l * alphaC u l) * binomP u (l - 1)) q]
    rw [Finset.sum_range_succ (fun l => C (p (l + 1) * alphaC u (l + 1)) * binomP u l) q]
    rw [hp (q + 1) (by omega)]
    simp
  · -- the superdiagonal sum shifts UP
    have hq : p q = 0 := hp q (by omega)
    rw [Finset.sum_range_succ (fun x => C (p x * gammaC u x) * binomP u (x + 1)) q,
      Finset.sum_range_succ' (fun l => if l = 0 then (0 : ℚ[X])
        else C (p (l - 1) * gammaC u (l - 1)) * binomP u l) q]
    rw [hq]
    simp

/-- **The `T`-recurrence**, the adjoint of the write-up's coefficient recurrence:
`L(T j) = j(j−1−N) T(j+1) + (3j−K) T j + j(D−j+1) T(j−1)`, stated at `j+1` so that no
truncated subtraction appears.  Linearity plus the regrouping reduce it to `cc_recurrence`
one basis vector at a time. -/
theorem Lres_Tpoly (u j : ℕ) :
    Lres u (Tpoly u (j + 1))
      = C (((j : ℚ) + 1) * ((j : ℚ) - Nq u)) * Tpoly u (j + 2)
        + C (3 * ((j : ℚ) + 1) - Kq u) * Tpoly u (j + 1)
        + C (((j : ℚ) + 1) * (Dq u - (j : ℚ))) * Tpoly u j := by
  rw [Tpoly_eq_range u (j + 1) (j + 3) (by omega),
    Tpoly_eq_range u (j + 2) (j + 3) (by omega),
    Tpoly_eq_range u j (j + 3) (by omega), Lres_sum]
  simp only [Lres_C_mul]
  rw [Lres_binom_regroup u (j + 1) (j + 3) (cc (j + 1))
    (fun l hl => cc_eq_zero hl) (by omega)]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  cases l with
  | zero =>
    have key := cc_recurrence_zero u j
    simp only [Nat.zero_add, eq_self_iff_true, if_true, add_zero, ← mul_assoc, ← C_mul,
      ← add_mul, ← C_add]
    exact congrArg (fun z : ℚ => C z * binomP u 0) (by simpa using key)
  | succ i =>
    have key := cc_recurrence u j i
    simp only [if_neg (Nat.succ_ne_zero i), Nat.succ_sub_one, ← mul_assoc, ← C_mul,
      ← add_mul, ← C_add]
    exact congrArg (fun z : ℚ => C z * binomP u (i + 1)) (by simpa using key)

/-! ### The residue step, without residues

`Lres` is linear, `T` satisfies the three-term recurrence above, and `Pconstr = ∑_j h_j T_j`.
Regrouping by the index of `T` makes the coefficient of `T_{i+1}` literally `hrec u i`,
which is zero — so `Lres (Pconstr u) = 0`, which is equation (1).  The coefficient of `T_0`
never has to be computed, because `T_0 = 0`. -/

/-- `a_j = j(j−1−N)`, the coefficient of `T_{j+1}`. -/
noncomputable def aC (u j : ℕ) : ℚ := (j : ℚ) * ((j : ℚ) - 1 - Nq u)

/-- `b_j = 3j−K`, the coefficient of `T_j`. -/
noncomputable def bC (u j : ℕ) : ℚ := 3 * (j : ℚ) - Kq u

/-- `d_j = j(D−j+1)`, the coefficient of `T_{j−1}`. -/
noncomputable def dC (u j : ℕ) : ℚ := (j : ℚ) * (Dq u - (j : ℚ) + 1)

theorem Tpoly_zero (u : ℕ) : Tpoly u 0 = 0 := by simp [Tpoly]

/-- The `T`-recurrence at every index.  At `j = 0` all three terms vanish on their own
(`a_0 = d_0 = 0` and `T_0 = 0`), so no truncated subtraction ever bites. -/
theorem Lres_Tpoly_all (u j : ℕ) :
    Lres u (Tpoly u j)
      = C (aC u j) * Tpoly u (j + 1) + C (bC u j) * Tpoly u j
        + C (dC u j) * Tpoly u (j - 1) := by
  cases j with
  | zero => simp [Tpoly_zero, aC, dC, Lres_zero]
  | succ i =>
    have h := Lres_Tpoly u i
    have e1 : aC u (i + 1) = ((i : ℚ) + 1) * ((i : ℚ) - Nq u) := by
      simp only [aC]; push_cast; ring
    have e2 : bC u (i + 1) = 3 * ((i : ℚ) + 1) - Kq u := by
      simp only [bC]; push_cast; ring
    have e3 : dC u (i + 1) = ((i : ℚ) + 1) * (Dq u - (i : ℚ)) := by
      simp only [dC]; push_cast; ring
    rw [e1, e2, e3, Nat.succ_sub_one, h]

/-- `Pconstr` is `∑_j h_j · T_j`, which is what makes linearity applicable. -/
theorem Pconstr_eq_sum (u : ℕ) :
    Pconstr u = ∑ j ∈ Finset.range (Nn u + 2), C (hc u j) * Tpoly u j := by
  rw [Pconstr]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Tpoly, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [cc, ← mul_assoc, ← C_mul, mul_assoc]

/-- **Equation (1) for the explicit solution** — the write-up's residue step, proved with no
residue, Laurent series or germ anywhere. -/
theorem Lres_Pconstr (u : ℕ) : Lres u (Pconstr u) = 0 := by
  have hvan : ∀ j, Nn u + 2 ≤ j → hc u j = 0 := hc_vanish u
  have hT0 : Tpoly u 0 = 0 := Tpoly_zero u
  have hP : Pconstr u = ∑ j ∈ Finset.range (Nn u + 3), C (hc u j) * Tpoly u j := by
    rw [show Nn u + 3 = (Nn u + 2) + 1 from rfl,
      Finset.sum_range_succ (fun j => C (hc u j) * Tpoly u j) (Nn u + 2),
      hvan (Nn u + 2) (le_refl _), map_zero, zero_mul, add_zero, Pconstr_eq_sum]
  rw [hP, Lres_sum]
  simp only [Lres_C_mul, Lres_Tpoly_all]
  have hdist : ∀ j : ℕ, C (hc u j) * (C (aC u j) * Tpoly u (j + 1)
        + C (bC u j) * Tpoly u j + C (dC u j) * Tpoly u (j - 1))
      = C (hc u j * aC u j) * Tpoly u (j + 1) + C (hc u j * bC u j) * Tpoly u j
        + C (hc u j * dC u j) * Tpoly u (j - 1) := by
    intro j
    simp only [C_mul]
    ring
  simp only [hdist]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hSa : ∑ j ∈ Finset.range (Nn u + 3), C (hc u j * aC u j) * Tpoly u (j + 1)
      = ∑ k ∈ Finset.range (Nn u + 3),
          (if k = 0 then 0 else C (hc u (k - 1) * aC u (k - 1)) * Tpoly u k) := by
    rw [show Nn u + 3 = (Nn u + 2) + 1 from rfl,
      Finset.sum_range_succ (fun j => C (hc u j * aC u j) * Tpoly u (j + 1)) (Nn u + 2),
      Finset.sum_range_succ' (fun k => if k = 0 then (0 : ℚ[X])
        else C (hc u (k - 1) * aC u (k - 1)) * Tpoly u k) (Nn u + 2),
      hvan (Nn u + 2) (le_refl _)]
    simp
  have hSd : ∑ j ∈ Finset.range (Nn u + 3), C (hc u j * dC u j) * Tpoly u (j - 1)
      = ∑ k ∈ Finset.range (Nn u + 3), C (hc u (k + 1) * dC u (k + 1)) * Tpoly u k := by
    rw [show Nn u + 3 = (Nn u + 2) + 1 from rfl,
      Finset.sum_range_succ' (fun j => C (hc u j * dC u j) * Tpoly u (j - 1)) (Nn u + 2),
      Finset.sum_range_succ
        (fun k => C (hc u (k + 1) * dC u (k + 1)) * Tpoly u k) (Nn u + 2),
      hvan (Nn u + 3) (by omega)]
    simp [hT0]
  rw [hSa, hSd, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  cases k with
  | zero => simp [hT0]
  | succ i =>
    have hz : hc u i * aC u i + hc u (i + 1) * bC u (i + 1)
        + hc u (i + 2) * dC u (i + 2) = 0 := by
      simp only [aC, bC, dC]
      push_cast
      linear_combination hrec u i
    simp only [if_neg (Nat.succ_ne_zero i), Nat.succ_sub_one]
    rw [← add_mul, ← add_mul, ← C_add, ← C_add, hz, map_zero, zero_mul]

/-- **The write-up's residue step, discharged.** -/
theorem solvesFirst_Pconstr (u : ℕ) : SolvesFirst u (Pconstr u) :=
  (solvesFirst_iff u (Pconstr u)).mpr (Lres_Pconstr u)

end Tridiagonal

/-! ### The spine

Each link feeds the next and the last delivers Cohen's Conjecture 4.2.  `hrec` is supplied,
so `odeOfRec` is applied to a PROVED antecedent rather than an assumed one; the remaining
four hypotheses are the write-up's residue argument, its degree computation, Mueller's
uniqueness argument, and the reflection `Q(x) = P(−x−2u−3)`. -/

theorem cohen_spine (u : ℕ)
    (solvesOfOde : OdeH u → SolvesFirst u (Pconstr u)) :
    (∃ P : ℚ[X], P ≠ 0 ∧ SolvesFirst u P ∧ P.natDegree = Nn u) ∧
      (∃ Q : ℚ[X], Q ≠ 0 ∧ SolvesSecond u Q) ∧
      (∀ P Q : ℚ[X], SolvesFirst u P → SolvesFirst u Q → P ≠ 0 → Q ≠ 0 →
        ∃ c : ℚ, c ≠ 0 ∧ Q = C c * P) ∧
      (∀ P : ℚ[X], SolvesFirst u P → P ≠ 0 → P.natDegree = Nn u) := by
  have hO : OdeH u := odeH u
  have Pne : Pconstr u ≠ 0 := Pconstr_ne_zero u
  have hP : SolvesFirst u (Pconstr u) := solvesOfOde hO
  -- unconditional now: the degree is a property of the construction, not of `hP`
  have hdN : (Pconstr u).natDegree = Nn u := Pconstr_natDegree u
  refine ⟨⟨Pconstr u, Pne, hP, hdN⟩, ?_, uniqueness u,
    fun P hPs hPne => solves_natDegree u P hPs hPne⟩
  refine ⟨(Pconstr u).comp (-X - C (2 * (u : ℚ) + 3)), ?_, reflect u _ hP⟩
  intro hzero
  -- `q = -X - c` is an involution under composition, so `P.comp q = 0` forces `P = 0`.
  have hinv : (-X - C (2 * (u : ℚ) + 3) : ℚ[X]).comp (-X - C (2 * (u : ℚ) + 3)) = X := by
    simp [sub_comp, neg_comp, X_comp, C_comp]
  apply Pne
  have hc2 := congrArg (fun p : ℚ[X] => p.comp (-X - C (2 * (u : ℚ) + 3))) hzero
  simpa [comp_assoc, hinv] using hc2


/-! ### Equation (2) inherits degree and uniqueness

The spine gives equation (2) only EXISTENCE, but the write-up's Theorem claims that the
solution space of **each** equation is one-dimensional with every nonzero solution of degree
`N`.  The reflection `σ(x) = −x−2u−3` is an involution carrying (1) to (2) and back, so it
is a linear bijection between the two solution spaces; degree is preserved because `σ` has
degree 1.  `reflect'` is the missing direction. -/

/-- **Equation (1) from equation (2)** — the reverse reflection. -/
theorem reflect' (u : ℕ) (Q : ℚ[X]) (h : SolvesSecond u Q) :
    SolvesFirst u (Q.comp (-X - C (2 * (u : ℚ) + 3))) := by
  rw [SolvesSecond] at h
  rw [SolvesFirst]
  refine Polynomial.funext (fun x => ?_)
  have hy := congrArg (Polynomial.eval (-x - (2 * (u : ℚ) + 3))) h
  have hlm := lam_mul_sub_mu u
  simp only [eval_add, eval_sub, eval_mul, eval_neg, eval_X, eval_C, eval_one,
    eval_comp] at hy ⊢
  ring_nf at hy ⊢
  linear_combination (norm := ring_nf) -hy + Polynomial.eval
    (-x - (2 * (u : ℚ) + 3)) Q * hlm

/-- The reflection is an involution. -/
theorem refl_involutive (u : ℕ) (P : ℚ[X]) :
    (P.comp (-X - C (2 * (u : ℚ) + 3))).comp (-X - C (2 * (u : ℚ) + 3)) = P := by
  have hinv : (-X - C (2 * (u : ℚ) + 3) : ℚ[X]).comp (-X - C (2 * (u : ℚ) + 3)) = X := by
    simp [sub_comp, neg_comp, X_comp, C_comp]
  rw [comp_assoc, hinv, comp_X]

theorem comp_refl_ne_zero (u : ℕ) (P : ℚ[X]) (hP : P ≠ 0) :
    P.comp (-X - C (2 * (u : ℚ) + 3)) ≠ 0 := by
  intro h
  exact hP (by rw [← refl_involutive u P, h, zero_comp])

theorem natDegree_comp_refl (u : ℕ) (P : ℚ[X]) :
    (P.comp (-X - C (2 * (u : ℚ) + 3))).natDegree = P.natDegree := by
  have hq : (-X - C (2 * (u : ℚ) + 3) : ℚ[X]) = -(X + C (2 * (u : ℚ) + 3)) := by ring
  rw [Polynomial.natDegree_comp, hq, natDegree_neg, natDegree_X_add_C, mul_one]

/-- Every nonzero solution of equation (2) also has degree `N`. -/
theorem solvesSecond_natDegree (u : ℕ) (Q : ℚ[X]) (h : SolvesSecond u Q) (hQ : Q ≠ 0) :
    Q.natDegree = Nn u := by
  have hd := solves_natDegree u _ (reflect' u Q h) (comp_refl_ne_zero u Q hQ)
  rwa [natDegree_comp_refl] at hd

/-- Equation (2)'s solution space is one-dimensional too. -/
theorem solvesSecond_unique (u : ℕ) (Q₁ Q₂ : ℚ[X]) (h₁ : SolvesSecond u Q₁)
    (h₂ : SolvesSecond u Q₂) (hn₁ : Q₁ ≠ 0) (hn₂ : Q₂ ≠ 0) :
    ∃ c : ℚ, c ≠ 0 ∧ Q₂ = C c * Q₁ := by
  obtain ⟨c, hc, he⟩ := uniqueness u _ _ (reflect' u Q₁ h₁) (reflect' u Q₂ h₂)
    (comp_refl_ne_zero u Q₁ hn₁) (comp_refl_ne_zero u Q₂ hn₂)
  refine ⟨c, hc, ?_⟩
  have hcong : (Q₂.comp (-X - C (2 * (u : ℚ) + 3))).comp (-X - C (2 * (u : ℚ) + 3))
      = (C c * Q₁.comp (-X - C (2 * (u : ℚ) + 3))).comp
          (-X - C (2 * (u : ℚ) + 3)) := by rw [he]
  rwa [refl_involutive, mul_comp, C_comp, refl_involutive] at hcong

/-- **Cohen's Conjecture 4.2, UNCONDITIONALLY.**

`cohen_spine`'s last hypothesis — the write-up's residue computation — is discharged by
`solvesFirst_Pconstr`, so nothing is carried: equation (1) has a nonzero solution, it has
degree `N`, equation (2) has one too, and every nonzero solution of (1) is a scalar multiple
of it and has degree `N`. -/
theorem cohen_conjecture (u : ℕ) :
    (∃ P : ℚ[X], P ≠ 0 ∧ SolvesFirst u P ∧ P.natDegree = Nn u) ∧
      (∃ Q : ℚ[X], Q ≠ 0 ∧ SolvesSecond u Q) ∧
      (∀ P Q : ℚ[X], SolvesFirst u P → SolvesFirst u Q → P ≠ 0 → Q ≠ 0 →
        ∃ c : ℚ, c ≠ 0 ∧ Q = C c * P) ∧
      (∀ P : ℚ[X], SolvesFirst u P → P ≠ 0 → P.natDegree = Nn u) :=
  cohen_spine u (fun _ => solvesFirst_Pconstr u)


/-- **THE WRITE-UP'S THEOREM, IN FULL.**

*For every nonnegative integer `u`, the solution space in `ℚ[x]` of each equation (1) and
(2) is one-dimensional, and every nonzero solution has degree `N = u(u+3)`.*

The spine gave equation (2) only existence; `solvesSecond_natDegree` and
`solvesSecond_unique`, via the reverse reflection `reflect'`, supply its degree and
uniqueness, so this is the source's statement and not a weaker one. -/
theorem cohen_theorem (u : ℕ) :
    ((∃ P : ℚ[X], P ≠ 0 ∧ SolvesFirst u P) ∧
      (∀ P : ℚ[X], SolvesFirst u P → P ≠ 0 → P.natDegree = Nn u) ∧
      (∀ P Q : ℚ[X], SolvesFirst u P → SolvesFirst u Q → P ≠ 0 → Q ≠ 0 →
        ∃ c : ℚ, c ≠ 0 ∧ Q = C c * P)) ∧
    ((∃ Q : ℚ[X], Q ≠ 0 ∧ SolvesSecond u Q) ∧
      (∀ Q : ℚ[X], SolvesSecond u Q → Q ≠ 0 → Q.natDegree = Nn u) ∧
      (∀ Q₁ Q₂ : ℚ[X], SolvesSecond u Q₁ → SolvesSecond u Q₂ → Q₁ ≠ 0 → Q₂ ≠ 0 →
        ∃ c : ℚ, c ≠ 0 ∧ Q₂ = C c * Q₁)) := by
  obtain ⟨⟨P, hPne, hPs, _⟩, ⟨Q, hQne, hQs⟩, huniq, hdeg⟩ := cohen_conjecture u
  exact ⟨⟨⟨P, hPne, hPs⟩, hdeg, huniq⟩,
    ⟨⟨Q, hQne, hQs⟩, solvesSecond_natDegree u, solvesSecond_unique u⟩⟩

end Principia.MathDB.P358171
