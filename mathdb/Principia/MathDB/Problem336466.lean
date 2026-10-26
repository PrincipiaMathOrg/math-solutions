import Mathlib
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Pochhammer
import Principia.Common.AltBinomial

/-!
# MathDB #336466 — the odd-degree mean relation (PROVED)

Write-up `mathdb-open-problems/problems/336466/solution.tex`,
*The odd-degree peculiar linear mean relationship*, 18 September 2026.

For `f ∈ ℂ[x]` of degree `D` and `0 ≤ ρ < D`, let
`M_ρ(f) = (1/(D−ρ)) ∑_{f^{(ρ)}(r)=0} f(r)`, the mean of `f` over the roots of its `ρ`-th
derivative counted with multiplicity.  Wojnar–Wojnar–Brin Conjecture 2 asserts

`∑_{ρ=1}^{D−1} (−1)^ρ C(D,ρ) M_ρ(f) = 0`  for odd `D`.

## What this module is

**The conjecture, proved.**  `conj2` states it for every nonzero `f ∈ ℂ[x]` of odd degree `D`
and carries no hypothesis beyond that.  The module began as a spine — the chain of inferences
with its gaps named — and the gaps are now closed, so what follows is the history of that
construction as well as its result.

**What made the difference was writing the spine first.**  `conj2_of_interpolation` carried two
hypotheses; `endpoint_iff` then proved that in its ABSTRACT form one of them is equivalent to the
conjecture, which is why that route had to be replaced by a NAMED `H` rather than refined.  Every
rung after that was chosen by looking at what `conj2_of_H`'s two remaining hypotheses literally
said.

**Proved here, unconditionally:**

* `Jsum_odd_eq_zero` — the source's endpoint quantity `J_D(c) = ∑_m (−1)^m c_m c_{D−m}/C(D,m)`
  vanishes for odd `D`, because the `m`-term cancels the `(D−m)`-term and no middle term exists.
* `Principia.Common.altBinom_eq_zero` — **the alternating binomial sum annihilates low degree**:
  `∑_{k≤D} (−1)^k C(D,k) P(k) = 0` whenever `deg P < D`.  Mathlib has the forward-difference
  machinery (`fwdDiff_iter_eq_sum_shift`) but not this consequence, so it is built here from
  `fwdDiff_iter_eq_zero`, itself an induction on `D` using `taylor 1 P − P` to drop the degree.

**Formerly assumed, now proved:** that `ρ ↦ M_ρ(f)` agrees on `1 ≤ ρ < D` with a polynomial
of degree below `D` (`means_of_Hpoly`, with `Hpoly_natDegree_lt` for the degree), and that that
polynomial's value at the far endpoint is `J_D(c)` (`endpoint_of_Hpoly`).  The write-up obtains
both from a formal logarithm; **neither needs one.**  The logarithm's only role is to produce the
Newton recurrence, and that recurrence is taken here as the DEFINITION of `P_m` (`Pcoef`), after
which `Pcoef_eval_eq_psum` identifies `P_m(n)` with the `m`-th power sum of the roots of `g_n` by
induction — Vieta on one side (`Acoef_eval_eq_esymm_all`), Mathlib's Newton identities on the
other (`newton_multiset`), and the two recurrences are the same one.

**RE-PRICED 2026-09-25, and the first rung is built.**  Every tool the construction needs is in
Mathlib: `descPochhammer` is the falling factorial (`descPochhammer_eval_eq_descFactorial`,
`Nat.descFactorial_eq_zero_iff_lt`, `descPochhammer_ne_zero_eval_zero`), and the formal logarithm
is `PowerSeries.logOf`, defined exactly for a series of constant coefficient `1` (`constantCoeff_logOf`)
-- which is what the write-up's `A_0 = 1` supplies, so the step that looked least available is
present.  The final finite difference is already `Principia.Common.altBinom_eq_zero`.  **The
residue is an ordinary formalisation job, not a gap.**  Landed so far: `Acoef` (`A_j`), its closed
form at a natural argument, the vanishing `A_j(n) = 0` for `j > n` and `A_j(0) = 0` for `j ≥ 1`, and
`Bser_at_zero` (`B(0, z) = c_0`).  **Two of those are now built, and WITHOUT the logarithm.**  Differentiating
`B = prod (1 - r_i z)` gives `z B'/B = - sum_m p_m z^m`, which clearing denominators turns into
the Newton recurrence `P_n = -n A_n - sum_{m<n} P_m A_{n-m}`; that is taken as the DEFINITION
(`Pcoef`), and both properties fall straight out of it -- `Pcoef_natDegree_le` because
`deg A_j <= j` and `m + (n-m) = n`, and `Pcoef_eval_zero` because every term on the right
carries an `A_j` with `j >= 1`.  `Hpoly` is then the write-up's `H`, with `divX` as the exact
quotient, and `Hpoly_natDegree_lt` is its *"polynomial of degree at most D-1"* -- one of the
two properties the whole reduction needs, now unconditional.

**The spine is now stated with the CONSTRUCTED `H` (`conj2_of_H`).**  The write-up indexes the
other way round -- `H(n) = M_{D-n}` -- so the interpolant the spine consumes is the REFLECTION
`H(D - u)` (`Hrefl`), whose degree bound transfers (`Hrefl_natDegree_lt`).  The endpoint falls
out of the reflection for free, since `H(D - D) = H(0)`.  **What that changes:** `endpoint_iff`
shows the ABSTRACT interpolation spine transports the problem, because its `P` is existentially
quantified; `conj2_of_H` carries instead two statements about a NAMED object whose degree is
proved, so the circularity does not survive the construction.

The write-up's `(derivative)` display is now here too, and it was a rewrite rather than a
computation: `coeff_gnorm` already gave `(g_n).coeff (n-j)` and `Acoef_eval_natCast` gave `A_j(n)`,
and with the write-up's own indexing `c_j = g.coeff (D-j)` they are the SAME NUMBER
(`Acoef_eval_eq_coeff_gnorm`) -- which is what `Acoef` was defined to make true.  `gnorm_monic`
is the display's second half, and it is the hypothesis the Vieta step runs on, since a monic
polynomial of degree `n` over the complexes splits into `n` linear factors and only then do the
elementary symmetric functions of its roots and its coefficients have anything to say to each
other.

**Vieta is now here too.**  `g_n` is monic of degree `n` over the complexes, so it splits and has
exactly `n` roots with multiplicity (`gnorm_card_roots`), and Mathlib's
`coeff_eq_esymm_roots_of_card` then gives `A_j(n) = (-1)^j e_j(roots of g_n)`
(`Acoef_eval_eq_esymm`) -- which IS the write-up's reading of `B(n,z)` as `prod (1 - r_i z)`.

**Newton's identities are now available in the shape this module needs.**  Mathlib proves them
SYMBOLICALLY, for `MvPolynomial` over a `Fintype` of variables; the roots of `g_n` arrive as a
`Multiset`.  `newton_multiset` is the transfer, and it mentions `g_n` nowhere -- it is Newton's
identity for an arbitrary finite multiset of complex numbers, obtained by indexing with
`Fin s.toList.length`, applying Mathlib's identity and evaluating with `aeval`.

**The last three rungs, 2026-09-25.**  `Pcoef_eval_eq_psum` is the induction: both sequences
satisfy the same recurrence once Vieta is substituted, so no new mathematics was required, only
the care to run it for EVERY `k >= 1` rather than `k <= n` -- `Hpoly` sums `m` up to `D`, and
above the degree both sides of Vieta vanish (`Acoef_eval_eq_esymm_all`).  `means_of_Hpoly` is
then a finite rearrangement: expanding `g` at each root of `g_n` and summing gives
`sum_r g(r) = c_D n + sum_m c_{D-m} P_m(n)`, and dividing by `n` is `H(n)`.  `endpoint_of_Hpoly`
is a coefficient computation: every product in the recurrence has a DOUBLE zero at the origin, so
only `-m A_m` reaches `[u^1]`, and `[u^1](u)_m = (-1)^{m-1}(m-1)!` turns it into
`(-1)^m c_m / C(D,m)` -- the `m`-th summand of `J_D(c)`.  `conj2_monic` composes them;
`Mrho_C_mul` removes monicity, since `M_rho` is homogeneous of degree one in `f`.

## A route that turned out to be CIRCULAR, and is certified as such

The obvious spine — assume `M_ρ` is interpolated by a polynomial of degree `< D`, assume that
polynomial's value at `D` is `a·J_D(c)`, conclude the conjecture — does not reduce anything.
Interpolation through `D` nodes is free (`interpP`, by Lagrange), and `endpoint_iff` proves the
remaining endpoint hypothesis EQUIVALENT to the conjecture itself.  So `conj2_of_interpolation`
and `conj2_of_endpoint`, while true and proved, transport the problem rather than reduce it.

That is recorded here as a theorem rather than a remark, because the failure is invisible in
prose: both directions elaborate, and only writing the converse exposes it.  The write-up's real
content is that its EXPLICITLY CONSTRUCTED `H` — assembled from the power sums of the normalized
derivative's roots — has degree `< D` *and* endpoint `J_D(c)` at the same time; neither property
alone says anything.  `coeff_gnorm` is the input that construction consumes.

Checked in Python before formalizing (`verify_336466.py`, symbolic, no numerics): the general
formula for `D = 2…5`; `J_D = 0` for `D = 1,3,5,7,9`; the conjecture itself for `D = 3, 5`.  That
check also **ruled out a shortcut**: at `D = 3` the sum vanishes merely because `M_1 = M_2` and
`C(3,1) = C(3,2)`, but at `D = 5` the means differ (`M_1` vs `M_4`, 128/6250 against 8/6250), so
the vanishing is a genuine linear identity and the interpolation cannot be avoided.
-/

namespace Principia.MathDB.P336466

open Finset Polynomial Principia.Common

/-- `J_D(c) = ∑_m (−1)^m c_m c_{D−m} / C(D,m)`, the source's endpoint quantity. -/
noncomputable def Jsum (D : ℕ) (c : ℕ → ℂ) : ℂ :=
  ∑ m ∈ range (D + 1), (-1 : ℂ) ^ m * c m * c (D - m) / (D.choose m : ℂ)

/-- **The elementary gem.**  For odd `D` the `m`-term cancels the `(D−m)`-term, and there is no
middle term, so `J_D` vanishes identically. -/
theorem Jsum_odd_eq_zero (D : ℕ) (hD : Odd D) (c : ℕ → ℂ) : Jsum D c = 0 := by
  unfold Jsum
  refine Finset.sum_involution (fun m _ => D - m) ?_ ?_ ?_ ?_
  · intro m hm
    rw [mem_range] at hm
    have hmD : m ≤ D := by omega
    have e1 : D - (D - m) = m := by omega
    have e2 : D.choose (D - m) = D.choose m := Nat.choose_symm hmD
    rw [e1, e2]
    have hsq : ((-1 : ℂ)) ^ m * (-1) ^ m = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have hprod : ((-1 : ℂ)) ^ (D - m) * (-1) ^ m = -1 := by
      rw [← pow_add, show D - m + m = D from by omega, hD.neg_one_pow]
    have hsign : ((-1 : ℂ)) ^ (D - m) = -((-1 : ℂ) ^ m) := by
      calc ((-1 : ℂ)) ^ (D - m)
          = ((-1 : ℂ) ^ (D - m) * (-1) ^ m) * (-1) ^ m := by rw [mul_assoc, hsq, mul_one]
        _ = (-1 : ℂ) * (-1) ^ m := by rw [hprod]
        _ = -((-1 : ℂ) ^ m) := by ring
    rw [hsign]
    ring
  · intro m hm _
    rw [mem_range] at hm
    obtain ⟨k, hk⟩ := hD
    omega
  · intro m hm
    rw [mem_range] at hm ⊢
    omega
  · intro m hm
    rw [mem_range] at hm
    omega

/-- `M_ρ(f)`, the mean of `f` over the roots of its `ρ`-th derivative, counted with
multiplicity — the source's `φ_{D,0,ρ}`. -/
noncomputable def Mrho (f : Polynomial ℂ) (D ρ : ℕ) : ℂ :=
  ((((Polynomial.derivative)^[ρ]) f).roots.map (fun r => f.eval r)).sum / ((D : ℂ) - ρ)

/-- `M_0(f) = 0`: the roots of `f^{(0)} = f` are roots of `f`, so every summand vanishes.
This is the write-up's `H(D) = M_0(g) = 0`, and it discharges one of the two endpoints. -/
theorem Mrho_zero (f : Polynomial ℂ) (D : ℕ) : Mrho f D 0 = 0 := by
  unfold Mrho
  simp only [Function.iterate_zero, id_eq]
  have hz : (f.roots.map (fun r => f.eval r)) = f.roots.map (fun _ => (0 : ℂ)) := by
    refine Multiset.map_congr rfl ?_
    intro r hr
    exact Polynomial.isRoot_of_mem_roots hr
  rw [hz]
  simp

/-- The write-up's normalized derivative `g_n = (n!/D!) · g^{(D−n)}`, monic of degree `n`. -/
noncomputable def gnorm (g : Polynomial ℂ) (D n : ℕ) : Polynomial ℂ :=
  ((n.factorial : ℂ) / (D.factorial : ℂ)) • (derivative^[D - n] g)

/-- Normalizing does not move the roots, so `M_ρ` may be read off `gnorm`. -/
theorem roots_gnorm (g : Polynomial ℂ) (D n : ℕ) :
    (gnorm g D n).roots = (derivative^[D - n] g).roots := by
  unfold gnorm
  refine roots_smul_nonzero _ ?_
  have h1 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have h2 : (D.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.factorial_ne_zero
  exact div_ne_zero h1 h2

/-- **The write-up's `A_j(n)`.**  The coefficients of the normalized derivative are
`c_j · (n)_j / (D)_j`, falling factorials — polynomial in `n` of degree at most `j`. -/
theorem coeff_gnorm (g : Polynomial ℂ) (D n j : ℕ) (hj : j ≤ n) (hn : n ≤ D) :
    (gnorm g D n).coeff (n - j)
      = g.coeff (D - j) * ((n.descFactorial j : ℂ) / (D.descFactorial j : ℂ)) := by
  unfold gnorm
  rw [Polynomial.coeff_smul, smul_eq_mul, coeff_iterate_derivative]
  have hidx : n - j + (D - n) = D - j := by omega
  rw [hidx, nsmul_eq_mul]
  -- the three factorial identities
  have e1 : (n - j).factorial * n.descFactorial j = n.factorial :=
    Nat.factorial_mul_descFactorial hj
  have e2 : (D - j).factorial * D.descFactorial j = D.factorial :=
    Nat.factorial_mul_descFactorial (hj.trans hn)
  have e3 : (n - j).factorial * (D - j).descFactorial (D - n) = (D - j).factorial := by
    have h := Nat.factorial_mul_descFactorial (show D - n ≤ D - j by omega)
    rwa [show D - j - (D - n) = n - j by omega] at h
  have c1 : ((n - j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - j).factorial_ne_zero
  have c2 : ((D.factorial : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr D.factorial_ne_zero
  have c3 : ((D.descFactorial j : ℂ)) ≠ 0 := by
    refine Nat.cast_ne_zero.mpr fun h => ?_
    rw [h, mul_zero] at e2
    exact D.factorial_ne_zero e2.symm
  have E1 : ((n - j).factorial : ℂ) * (n.descFactorial j : ℂ) = (n.factorial : ℂ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) e1
  have E2 : ((D - j).factorial : ℂ) * (D.descFactorial j : ℂ) = (D.factorial : ℂ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) e2
  have E3 : ((n - j).factorial : ℂ) * ((D - j).descFactorial (D - n) : ℂ)
      = ((D - j).factorial : ℂ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) e3
  -- the single cross-multiplied identity behind the three factorial facts
  have key : (n.factorial : ℂ) * ((D - j).descFactorial (D - n) : ℂ) * (D.descFactorial j : ℂ)
      = (n.descFactorial j : ℂ) * (D.factorial : ℂ) := by
    rw [← E1, ← E2, ← E3]
    ring
  -- `nlinarith`/`linarith` are unavailable over ℂ; finish by linear_combination.
  field_simp
  linear_combination (g.coeff (D - j)) * key

/-- `M_ρ` read off the normalized derivative: scaling does not move roots. -/
theorem Mrho_via_gnorm (f : Polynomial ℂ) (D ρ : ℕ) (hρ : ρ ≤ D) :
    Mrho f D ρ
      = (((gnorm f D (D - ρ)).roots.map (fun r => f.eval r)).sum) / ((D : ℂ) - ρ) := by
  unfold Mrho
  rw [roots_gnorm, show D - (D - ρ) = ρ from by omega]

/-- **THE SPINE.**  Given the write-up's interpolation step — that `ρ ↦ M_ρ(f)` agrees on
`ρ < D` with a polynomial of degree below `D` — together with its value at the far endpoint, the
odd-degree conjecture follows from three facts proved here: `Mrho_zero`, `Jsum_odd_eq_zero`, and
`altBinom_eq_zero`.

Only ONE hypothesis remains beyond the interpolation itself (`hendD`), because the near endpoint
`P(0) = M_0(f) = 0` is now proved rather than assumed. -/
theorem conj2_of_interpolation (f : Polynomial ℂ) (D : ℕ) (hD : Odd D) (hD1 : 0 < D)
    (a : ℂ) (c : ℕ → ℂ) (P : Polynomial ℂ) (hPdeg : P.natDegree < D)
    (hinterp : ∀ ρ, ρ < D → Mrho f D ρ = P.eval (ρ : ℂ))
    (hendD : P.eval (D : ℂ) = a * Jsum D c) :
    ∑ ρ ∈ Finset.Ico 1 D, (-1 : ℂ) ^ ρ * (D.choose ρ : ℂ) * Mrho f D ρ = 0 := by
  have hJ : Jsum D c = 0 := Jsum_odd_eq_zero D hD c
  have hP0 : P.eval ((0 : ℕ) : ℂ) = 0 := by
    have h := hinterp 0 hD1
    rw [Mrho_zero] at h
    exact h.symm
  have hPD : P.eval (D : ℂ) = 0 := by rw [hendD, hJ, mul_zero]
  have hall := altBinom_eq_zero P D hPdeg
  rw [Finset.sum_range_succ, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot hD1] at hall
  have hrw : ∑ k ∈ Finset.Ico 1 D, (-1 : ℂ) ^ k * (D.choose k : ℂ) * P.eval (k : ℂ)
      = ∑ ρ ∈ Finset.Ico 1 D, (-1 : ℂ) ^ ρ * (D.choose ρ : ℂ) * Mrho f D ρ := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    rw [hinterp k hk.2]
  rw [hrw] at hall
  have h0 : (-1 : ℂ) ^ 0 * (D.choose 0 : ℂ) * P.eval ((0 : ℕ) : ℂ) = 0 := by
    rw [hP0]; ring
  have hDterm : (-1 : ℂ) ^ D * (D.choose D : ℂ) * P.eval (D : ℂ) = 0 := by
    rw [hPD]; ring
  rw [h0, hDterm] at hall
  linear_combination hall

/-- The Lagrange interpolant of `ρ ↦ M_ρ(f)` through the `D` nodes `0, …, D−1`. -/
noncomputable def interpP (f : Polynomial ℂ) (D : ℕ) : Polynomial ℂ :=
  Lagrange.interpolate (Finset.range D) (fun i => (i : ℂ)) (fun i => Mrho f D i)

theorem nodes_inj (D : ℕ) : Set.InjOn (fun i : ℕ => (i : ℂ)) (Finset.range D) :=
  fun a _ b _ h => Nat.cast_injective h

theorem interpP_degree (f : Polynomial ℂ) (D : ℕ) (hD : 0 < D) :
    (interpP f D).natDegree < D := by
  unfold interpP
  by_cases hz : Lagrange.interpolate (Finset.range D) (fun i : ℕ => (i : ℂ))
      (fun i => Mrho f D i) = 0
  · rw [hz]; simpa using hD
  · have h := Lagrange.degree_interpolate_lt (v := fun i : ℕ => (i : ℂ))
      (s := Finset.range D) (r := fun i => Mrho f D i) (nodes_inj D)
    rw [Finset.card_range] at h
    exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr h

theorem interpP_eval (f : Polynomial ℂ) (D ρ : ℕ) (h : ρ < D) :
    (interpP f D).eval (ρ : ℂ) = Mrho f D ρ :=
  Lagrange.eval_interpolate_at_node (v := fun i : ℕ => (i : ℂ)) (s := Finset.range D)
    (r := fun i => Mrho f D i) (nodes_inj D) (Finset.mem_range.mpr h)

/-- **The spine with ONE hypothesis.**  Interpolation through `D` nodes is free (Lagrange); all
the mathematical content sits in the value of that interpolant at the extra point `D`. -/
theorem conj2_of_endpoint (f : Polynomial ℂ) (D : ℕ) (hD : Odd D) (hD1 : 0 < D)
    (a : ℂ) (c : ℕ → ℂ)
    (hend : (interpP f D).eval (D : ℂ) = a * Jsum D c) :
    ∑ ρ ∈ Finset.Ico 1 D, (-1 : ℂ) ^ ρ * (D.choose ρ : ℂ) * Mrho f D ρ = 0 :=
  conj2_of_interpolation f D hD hD1 a c (interpP f D) (interpP_degree f D hD1)
    (fun ρ h => (interpP_eval f D ρ h).symm) hend

/-- If the conjecture's sum vanishes then the endpoint hypothesis holds.  Together with
`conj2_of_endpoint` this makes the two EQUIVALENT — i.e. the spine transports the problem
rather than reducing it. -/
theorem endpoint_of_conj (f : Polynomial ℂ) (D : ℕ) (hD : Odd D) (hD1 : 0 < D)
    (a : ℂ) (c : ℕ → ℂ)
    (hsum : ∑ ρ ∈ Finset.Ico 1 D, (-1 : ℂ) ^ ρ * (D.choose ρ : ℂ) * Mrho f D ρ = 0) :
    (interpP f D).eval (D : ℂ) = a * Jsum D c := by
  have hJ : Jsum D c = 0 := Jsum_odd_eq_zero D hD c
  rw [hJ, mul_zero]
  have hall := altBinom_eq_zero (interpP f D) D (interpP_degree f D hD1)
  rw [Finset.sum_range_succ, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot hD1] at hall
  have hrw : ∑ k ∈ Finset.Ico 1 D,
        (-1 : ℂ) ^ k * (D.choose k : ℂ) * (interpP f D).eval (k : ℂ)
      = ∑ ρ ∈ Finset.Ico 1 D, (-1 : ℂ) ^ ρ * (D.choose ρ : ℂ) * Mrho f D ρ := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    rw [interpP_eval f D k hk.2]
  rw [hrw, hsum] at hall
  have h0 : (-1 : ℂ) ^ 0 * (D.choose 0 : ℂ) * (interpP f D).eval ((0 : ℕ) : ℂ) = 0 := by
    rw [interpP_eval f D 0 hD1, Mrho_zero]; ring
  rw [h0] at hall
  have hlast : (-1 : ℂ) ^ D * (D.choose D : ℂ) * (interpP f D).eval (D : ℂ)
      = -((interpP f D).eval (D : ℂ)) := by
    rw [Nat.choose_self, hD.neg_one_pow]; push_cast; ring
  rw [hlast] at hall
  linear_combination -hall

/-- **THE ROUTE IS CIRCULAR, AND THIS CERTIFIES IT.**  The endpoint hypothesis of
`conj2_of_endpoint` is EQUIVALENT to the conjecture it was meant to reduce, so that spine
transports the problem instead of reducing it.  The genuine content of the write-up is not that
`M_ρ` is interpolated by a low-degree polynomial — that is free — nor that the interpolant takes
a particular value at `D`, which is merely the conjecture restated; it is that the EXPLICITLY
CONSTRUCTED `H`, built from the power sums of the normalized derivative's roots, simultaneously
has degree `< D` and endpoint `J_D(c)`.  `coeff_gnorm` is the input to that construction. -/
theorem endpoint_iff (f : Polynomial ℂ) (D : ℕ) (hD : Odd D) (hD1 : 0 < D)
    (a : ℂ) (c : ℕ → ℂ) :
    (interpP f D).eval (D : ℂ) = a * Jsum D c ↔
      ∑ ρ ∈ Finset.Ico 1 D, (-1 : ℂ) ^ ρ * (D.choose ρ : ℂ) * Mrho f D ρ = 0 :=
  ⟨fun h => conj2_of_endpoint f D hD hD1 a c h, fun h => endpoint_of_conj f D hD hD1 a c h⟩

section Interpolant

/-! ### The write-up's `A_j`, the first rung of the interpolant `H`

The header records that the module's two spines TRANSPORT the problem rather than reduce it, and
that the write-up's real content is its **explicitly constructed** `H`, which has degree `< D`
and endpoint `J_D(c)` at the same time.  This section starts that construction and, with it,
re-prices the residue: **every tool the construction needs is present in Mathlib.**

The write-up builds, for `0 ≤ j ≤ D`,

  `A_j(u) = c_j · (u)_j / (D)_j`,  `(u)_j = u(u−1)⋯(u−j+1)`,

then `B(u, z) = ∑_{j ≤ D} A_j(u) z^j`, then `P_m(u) = −m·[z^m] log B(u, z)`, and finally
`H(u) = c_D + ∑_{m=1}^{D} c_{D−m} P_m(u)/u`.  The chain then needs three facts: `deg_u A_j ≤ j`
(so `deg P_m ≤ m`), `A_j(0) = 0` for `j ≥ 1` (so `B(0, z) = 1` and `P_m(0) = 0`, giving the
divisibility by `u`), and `A_j(n) = 0` for `j > n` (the truncation of the derivative formula).

**What is in Mathlib, checked 2026-09-25:** `descPochhammer` is the falling factorial, with
`descPochhammer_eval_eq_descFactorial` evaluating it at a natural, `Nat.descFactorial_eq_zero_iff_lt`
giving the vanishing above the argument, and `descPochhammer_ne_zero_eval_zero` the vanishing at
`0`.  The formal logarithm is `PowerSeries.logOf`, defined exactly for a series with constant
coefficient `1` (`constantCoeff_logOf`), which is what `A_0 = 1` supplies — so the step that
looked least available is present.  And the final finite-difference step is already in this
repo as `Principia.Common.altBinom_eq_zero`.  **The residue is an ordinary formalisation job with
every tool to hand, not a gap.**

Landed here: `A_j` itself, its closed form at a natural argument, the two vanishing facts, and
`B(0, z) = c_0` — which is where `A_j(0) = 0` is spent.
-/

/-- The write-up's `A_j(u) = c_j · (u)_j / (D)_j`. -/
noncomputable def Acoef (c : ℕ → ℂ) (D j : ℕ) : Polynomial ℂ :=
  Polynomial.C (c j / (D.descFactorial j : ℂ)) * descPochhammer ℂ j

/-- `A_j` at a natural argument, in closed form. -/
theorem Acoef_eval_natCast (c : ℕ → ℂ) (D j n : ℕ) :
    (Acoef c D j).eval (n : ℂ) = c j * (n.descFactorial j : ℂ) / (D.descFactorial j : ℂ) := by
  simp only [Acoef, Polynomial.eval_mul, Polynomial.eval_C,
    descPochhammer_eval_eq_descFactorial]
  ring

/-- **`A_j(n) = 0` for `j > n`** — the truncation in the write-up's derivative formula. -/
theorem Acoef_eval_eq_zero_of_lt (c : ℕ → ℂ) (D : ℕ) {j n : ℕ} (h : n < j) :
    (Acoef c D j).eval (n : ℂ) = 0 := by
  rw [Acoef_eval_natCast, Nat.descFactorial_eq_zero_iff_lt.mpr h]
  simp

/-- **`A_j(0) = 0` for `j ≥ 1`** — what makes `B(0, z)` constant. -/
theorem Acoef_eval_zero (c : ℕ → ℂ) (D : ℕ) {j : ℕ} (hj : j ≠ 0) :
    (Acoef c D j).eval 0 = 0 := by
  have h := Acoef_eval_eq_zero_of_lt c D (n := 0) (Nat.pos_of_ne_zero hj)
  simpa using h

/-- The write-up's `B(u, z) = ∑_{j ≤ D} A_j(u) z^j`, as a polynomial in `z`. -/
noncomputable def Bser (c : ℕ → ℂ) (D : ℕ) (u : ℂ) : Polynomial ℂ :=
  ∑ j ∈ range (D + 1), Polynomial.C ((Acoef c D j).eval u) * Polynomial.X ^ j

/-- **`B(0, z) = c_0`.**  With `g` monic — the write-up's `A_0 = 1` — the constant coefficient is
`1`, which is exactly the hypothesis `PowerSeries.logOf` needs, and it is what forces
`P_m(0) = 0` and hence the divisibility of `P_m` by `u`. -/
theorem Bser_at_zero (c : ℕ → ℂ) (D : ℕ) : Bser c D 0 = Polynomial.C (c 0) := by
  rw [Bser, Finset.sum_eq_single 0]
  · simp [Acoef, descPochhammer_zero]
  · intro j _ hj
    rw [Acoef_eval_zero c D hj]
    simp
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos D)) h

end Interpolant

section PowerSums

/-! ### `P_m` by its recurrence, and `H` has degree `< D`

The write-up defines `P_m(u) = −m·[z^m] log B(u,z)` and then proves two things about it: its
degree in `u` is at most `m`, and it is divisible by `u`.  **Neither needs the logarithm.**
Differentiating `B = ∏(1 − r_i z)` gives `z·B'/B = −∑_m p_m z^m`, and clearing the denominator
turns that into the Newton recurrence

  `P_n = −n·A_n − ∑_{m=1}^{n−1} P_m · A_{n−m}`,

which is taken as the DEFINITION here.  Both properties then fall out of the recurrence:
the degree because `deg A_j ≤ j` and `m + (n−m) = n`, and the vanishing at `0` because every
factor on the right carries an `A_j` with `j ≥ 1`, and those vanish at `0` (`Acoef_eval_zero`).

**What this defers rather than avoids:** the identification of `P_n(k)` with the power sum
`∑ r_i^n` of the roots, which IS the content of the write-up's Lemma and does need the formal
logarithm (or Newton's identities).  That is what `H(n) = M_{D−n}` will rest on.  The degree
bound proved here is the other of the two properties `H` must have, and it is now unconditional:
`Hpoly_natDegree_lt` is the write-up's *"`H` is a polynomial of degree at most `D−1`"*.
-/

/-- `deg_u A_j ≤ j`. -/
theorem Acoef_natDegree_le (c : ℕ → ℂ) (D j : ℕ) : (Acoef c D j).natDegree ≤ j := by
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [descPochhammer_natDegree]

/-- The write-up's `P_m`, defined by the Newton recurrence rather than by a logarithm. -/
noncomputable def Pcoef (c : ℕ → ℂ) (D : ℕ) : ℕ → Polynomial ℂ
  | 0 => 0
  | (n + 1) =>
      -((n + 1 : ℕ) : Polynomial ℂ) * Acoef c D (n + 1)
        - ∑ m ∈ (Finset.range n).attach, Pcoef c D (m.1 + 1) * Acoef c D (n - m.1)
decreasing_by
  all_goals
    first
      | omega
      | (have hm := Finset.mem_range.mp m.2
         omega)

/-- The recurrence with a plain sum. -/
theorem Pcoef_succ (c : ℕ → ℂ) (D n : ℕ) :
    Pcoef c D (n + 1)
      = -((n + 1 : ℕ) : Polynomial ℂ) * Acoef c D (n + 1)
        - ∑ m ∈ range n, Pcoef c D (m + 1) * Acoef c D (n - m) := by
  conv_lhs => rw [Pcoef]
  congr 1
  exact Finset.sum_attach (range n) (fun m => Pcoef c D (m + 1) * Acoef c D (n - m))

/-- **`deg_u P_n ≤ n`.** -/
theorem Pcoef_natDegree_le (c : ℕ → ℂ) (D : ℕ) : ∀ n, (Pcoef c D n).natDegree ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 =>
          rw [Pcoef]
          simp
      | (t + 1) =>
          rw [Pcoef_succ]
          refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
          refine max_le ?_ ?_
          · refine le_trans (Polynomial.natDegree_mul_le) ?_
            have h1 : (-((t + 1 : ℕ) : Polynomial ℂ)).natDegree = 0 := by
              rw [Polynomial.natDegree_neg]
              exact Polynomial.natDegree_natCast _
            rw [h1, zero_add]
            exact Acoef_natDegree_le c D (t + 1)
          · refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
            refine Finset.sup_le (fun m hm => ?_)
            have hmt := Finset.mem_range.mp hm
            refine le_trans (Polynomial.natDegree_mul_le) ?_
            have h2 := ih (m + 1) (by omega)
            have h3 := Acoef_natDegree_le c D (t - m)
            omega

/-- **`P_n(0) = 0`** — every term of the recurrence carries an `A_j` with `j ≥ 1`. -/
theorem Pcoef_eval_zero (c : ℕ → ℂ) (D : ℕ) : ∀ n, (Pcoef c D n).eval 0 = 0 := by
  intro n
  match n with
  | 0 =>
      rw [Pcoef]
      simp
  | (t + 1) =>
      rw [Pcoef_succ]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_neg,
        Polynomial.eval_natCast, Polynomial.eval_finsetSum]
      rw [Acoef_eval_zero c D (Nat.succ_ne_zero t)]
      have hsum : ∀ m ∈ range t,
          (Pcoef c D (m + 1)).eval 0 * (Acoef c D (t - m)).eval 0 = 0 := by
        intro m hm
        have hmt := Finset.mem_range.mp hm
        rw [Acoef_eval_zero c D (by omega : t - m ≠ 0)]
        ring
      rw [Finset.sum_congr rfl hsum]
      simp

/-- The write-up's `H(u) = c_D + ∑_{m=1}^{D} c_{D−m}·P_m(u)/u`.  The quotient is exact because
`P_m(0) = 0`, so `divX` is the polynomial quotient the write-up means. -/
noncomputable def Hpoly (c : ℕ → ℂ) (D : ℕ) : Polynomial ℂ :=
  Polynomial.C (c D) + ∑ m ∈ Finset.Icc 1 D, Polynomial.C (c (D - m)) * (Pcoef c D m).divX

/-- **`H` has degree at most `D − 1`** — one of the two properties the whole reduction needs,
and now unconditional. -/
theorem Hpoly_natDegree_lt (c : ℕ → ℂ) (D : ℕ) (hD : 0 < D) : (Hpoly c D).natDegree < D := by
  have hbound : (Hpoly c D).natDegree ≤ D - 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    refine max_le ?_ ?_
    · rw [Polynomial.natDegree_C]
      omega
    · refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
      refine Finset.sup_le (fun m hm => ?_)
      have hmD := Finset.mem_Icc.mp hm
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
      have h := Pcoef_natDegree_le c D m
      omega
  omega

end PowerSums

section Reflected

/-! ### The spine, restated with the CONSTRUCTED `H`

`conj2_of_interpolation` takes an abstract `P` with `P.eval ρ = M_ρ`, and `endpoint_iff` shows
that in that abstract form the remaining endpoint hypothesis is EQUIVALENT to the conjecture —
so the spine transports the problem rather than reducing it.  That is a statement about the
abstract `P`, not about the write-up's `H`.

Two things separate them.  The write-up indexes the other way round, `H(n) = M_{D−n}`, so the
interpolant the spine consumes is the REFLECTION `H(D − u)`; and `H` is a closed term whose
degree is already proved (`Hpoly_natDegree_lt`, built from the Newton recurrence), where `P` was
existentially quantified.

`conj2_of_H` is the spine with those two facts supplied.  What it still carries is exactly the
write-up's two displayed facts about a NAMED object —

* `(means)`  `H(D − ρ) = M_ρ(f)` for `ρ < D`, and
* `(endpoint)`  `H(0) = J_D(c)`  —

neither of which is a restatement of the goal, because `H` is constructed and its degree is not
assumed.  The circularity `endpoint_iff` exposes lives in the abstract version and does not
survive the construction.

`(endpoint)` falls out of the reflection for free: `H(D − D) = H(0)`, so the spine's `hendD` at
`a = 1` IS the write-up's endpoint claim.
-/

/-- The reflection `u ↦ H(D − u)`, which is the interpolant in the spine's indexing. -/
noncomputable def Hrefl (c : ℕ → ℂ) (D : ℕ) : Polynomial ℂ :=
  (Hpoly c D).comp (Polynomial.C (D : ℂ) - Polynomial.X)

theorem Hrefl_eval (c : ℕ → ℂ) (D : ℕ) (x : ℂ) :
    (Hrefl c D).eval x = (Hpoly c D).eval ((D : ℂ) - x) := by
  simp [Hrefl, Polynomial.eval_comp]

/-- Reflecting does not change the degree, so the write-up's `deg H ≤ D − 1` is the spine's
`natDegree < D`. -/
theorem Hrefl_natDegree_lt (c : ℕ → ℂ) (D : ℕ) (hD : 0 < D) : (Hrefl c D).natDegree < D := by
  have hlin : (Polynomial.C (D : ℂ) - Polynomial.X).natDegree = 1 := by
    have hneg : (Polynomial.C (D : ℂ) - Polynomial.X)
        = -(Polynomial.X - Polynomial.C (D : ℂ)) := by ring
    rw [hneg, Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
  have h := Hpoly_natDegree_lt c D hD
  rw [Hrefl, Polynomial.natDegree_comp, hlin, mul_one]
  exact h

/-- **The spine, with the constructed `H` in place of an abstract interpolant.**  The two
hypotheses left are the write-up's own `(means)` and `(endpoint)`, both statements about a named
object whose degree is proved rather than assumed. -/
theorem conj2_of_H (f : Polynomial ℂ) (D : ℕ) (hD : Odd D) (hD1 : 0 < D) (c : ℕ → ℂ)
    (hmeans : ∀ ρ, ρ < D → Mrho f D ρ = (Hpoly c D).eval ((D : ℂ) - (ρ : ℂ)))
    (hend : (Hpoly c D).eval 0 = Jsum D c) :
    ∑ ρ ∈ Finset.Ico 1 D, (-1 : ℂ) ^ ρ * (D.choose ρ : ℂ) * Mrho f D ρ = 0 := by
  refine conj2_of_interpolation f D hD hD1 1 c (Hrefl c D) (Hrefl_natDegree_lt c D hD1)
    (fun ρ hρ => ?_) ?_
  · rw [Hrefl_eval]
    exact hmeans ρ hρ
  · rw [Hrefl_eval, sub_self, one_mul]
    exact hend

end Reflected

section Derivative

/-! ### The write-up's derivative display, and `g_n` monic of degree `n`

The write-up's `(derivative)` display is

  `g_n(x) = (n!/D!)·g^{(D−n)}(x) = ∑_{j=0}^{n} A_j(n) x^{n−j}`,  monic of degree `n`.

Both halves are now here, and the first is one line: `coeff_gnorm` already computes
`(g_n).coeff (n−j) = g.coeff (D−j) · (n)_j/(D)_j`, and `Acoef_eval_natCast` computes
`A_j(n) = c_j · (n)_j/(D)_j`.  **With the write-up's own indexing `c_j = g.coeff (D−j)` these are
the same number**, so the display is a rewrite rather than a computation — which is what one
would hope, since `Acoef` was defined to make it so.

`gnorm_monic` is the second half, and it is what the Vieta step will need: a monic polynomial of
degree `n` splits into `n` linear factors over `ℂ`, and only then do `esymm` of its roots and its
coefficients have anything to say to each other.
-/

/-- **The write-up's `(derivative)` display, coefficientwise.**  With `c_j = g.coeff (D−j)` the
`(n−j)`-th coefficient of `g_n` is exactly `A_j(n)`. -/
theorem Acoef_eval_eq_coeff_gnorm (g : Polynomial ℂ) (D n j : ℕ) (hj : j ≤ n) (hn : n ≤ D) :
    (gnorm g D n).coeff (n - j)
      = (Acoef (fun i => g.coeff (D - i)) D j).eval (n : ℂ) := by
  rw [coeff_gnorm g D n j hj hn, Acoef_eval_natCast]
  ring

/-- The top coefficient of `g_n` is the top coefficient of `g`: the case `j = 0`. -/
theorem gnorm_coeff_self (g : Polynomial ℂ) (D n : ℕ) (hn : n ≤ D) :
    (gnorm g D n).coeff n = g.coeff D := by
  have h := Acoef_eval_eq_coeff_gnorm g D n 0 (Nat.zero_le n) hn
  rw [Nat.sub_zero] at h
  rw [h, Acoef_eval_natCast]
  simp

theorem gnorm_natDegree_le (g : Polynomial ℂ) (D n : ℕ) (hn : n ≤ D) (hdeg : g.natDegree = D) :
    (gnorm g D n).natDegree ≤ n := by
  refine le_trans (Polynomial.natDegree_smul_le _ _) ?_
  refine le_trans (Polynomial.natDegree_iterate_derivative g (D - n)) ?_
  rw [hdeg]
  omega

/-- **`g_n` is monic of degree `n`** when `g` is monic of degree `D` — the second half of the
write-up's `(derivative)` display, and the hypothesis the Vieta step runs on. -/
theorem gnorm_monic (g : Polynomial ℂ) (D n : ℕ) (hn : n ≤ D) (hdeg : g.natDegree = D)
    (hlead : g.coeff D = 1) : (gnorm g D n).Monic := by
  have hcoeff : (gnorm g D n).coeff n = 1 := by
    rw [gnorm_coeff_self g D n hn, hlead]
  have hle := gnorm_natDegree_le g D n hn hdeg
  have hne : (gnorm g D n) ≠ 0 := by
    intro h
    rw [h] at hcoeff
    simp at hcoeff
  have hge : n ≤ (gnorm g D n).natDegree := by
    refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [hcoeff]
    exact one_ne_zero
  have hdegn : (gnorm g D n).natDegree = n := le_antisymm hle hge
  rw [Polynomial.Monic, Polynomial.leadingCoeff, hdegn, hcoeff]

end Derivative

section Vieta

/-! ### Vieta: `A_j(n)` IS a symmetric function of the roots of `g_n`

The write-up's Lemma rests on reading `B(n, z) = ∑_j A_j(n) z^j` as `∏_i (1 − r_i z)`, where the
`r_i` are the roots of `g_n`.  That identification is Vieta, and this section is it:

  `A_j(n) = (−1)^j · e_j(roots of g_n)`.

`gnorm_monic` supplies the hypothesis — a monic polynomial of degree `n` over `ℂ` splits, so it
has exactly `n` roots with multiplicity — and Mathlib's `coeff_eq_esymm_roots_of_card` supplies
the formula.  `Acoef_eval_eq_coeff_gnorm` then turns the coefficient into `A_j(n)`.

With this, the remaining gap in the write-up's Lemma is only the passage from the elementary
symmetric functions to the POWER SUMS — Newton's identities, which Mathlib has as
`MvPolynomial.psum_eq_mul_esymm_sub_sum`, and which `Pcoef` already takes as its defining
recurrence.
-/

/-- `g_n` has degree exactly `n`. -/
theorem gnorm_natDegree (g : Polynomial ℂ) (D n : ℕ) (hn : n ≤ D) (hdeg : g.natDegree = D)
    (hlead : g.coeff D = 1) : (gnorm g D n).natDegree = n := by
  refine le_antisymm (gnorm_natDegree_le g D n hn hdeg) ?_
  refine Polynomial.le_natDegree_of_ne_zero ?_
  rw [gnorm_coeff_self g D n hn, hlead]
  exact one_ne_zero

/-- `g_n` splits, so it has exactly `n` roots with multiplicity. -/
theorem gnorm_card_roots (g : Polynomial ℂ) (D n : ℕ) (hn : n ≤ D) (hdeg : g.natDegree = D)
    (hlead : g.coeff D = 1) : Multiset.card (gnorm g D n).roots = n := by
  have hsplit : (gnorm g D n).Splits := IsAlgClosed.splits _
  rw [Polynomial.splits_iff_card_roots.mp hsplit, gnorm_natDegree g D n hn hdeg hlead]

/-- **Vieta for `g_n`.**  `A_j(n)` is `(−1)^j` times the `j`-th elementary symmetric function of
the roots — which is the identification `B(n, z) = ∏_i (1 − r_i z)` the write-up's Lemma reads
off. -/
theorem Acoef_eval_eq_esymm (g : Polynomial ℂ) (D n j : ℕ) (hj : j ≤ n) (hn : n ≤ D)
    (hdeg : g.natDegree = D) (hlead : g.coeff D = 1) :
    (Acoef (fun i => g.coeff (D - i)) D j).eval (n : ℂ)
      = (-1 : ℂ) ^ j * (gnorm g D n).roots.esymm j := by
  have hmonic := gnorm_monic g D n hn hdeg hlead
  have hdegn := gnorm_natDegree g D n hn hdeg hlead
  have hcard := gnorm_card_roots g D n hn hdeg hlead
  have hle : n - j ≤ (gnorm g D n).natDegree := by
    rw [hdegn]
    omega
  have hvieta := Polynomial.coeff_eq_esymm_roots_of_card (by rw [hcard, hdegn]) hle
  have hidx : (gnorm g D n).natDegree - (n - j) = j := by
    rw [hdegn]
    omega
  rw [← Acoef_eval_eq_coeff_gnorm g D n j hj hn, hvieta, hidx, hmonic.leadingCoeff]
  ring

end Vieta

section Newton

/-! ### Newton's identities for a multiset of complex numbers

Mathlib proves Newton's identities symbolically, for `MvPolynomial σ R` over a `Fintype` of
variables (`MvPolynomial.psum_eq_mul_esymm_sub_sum`).  What this module needs is the same
identity for the ROOTS of `g_n`, which arrive as a `Multiset ℂ`.

`newton_multiset` is the transfer, and it mentions `g_n` nowhere: it is Newton's identity for an
arbitrary finite multiset of complex numbers, obtained by indexing the multiset with
`Fin s.toList.length`, applying Mathlib's symbolic identity, and evaluating with `aeval`.  Since
`aeval` is an algebra hom the identity passes through, and the two bridges
`MvPolynomial.aeval_esymm_eq_multiset_esymm` and the definition `psum = ∑ i, X i ^ k` turn the
symbolic objects into `Multiset.esymm` and the power sum.

**This is campaign-agnostic** and belongs in `Common/` once a second consumer appears; it is left
here for now because only this row uses it.
-/

theorem univ_val_map_ofFn {m : ℕ} (f : Fin m → ℂ) :
    (Finset.univ : Finset (Fin m)).val.map f = ↑(List.ofFn f) := by
  rw [List.ofFn_eq_map]
  rfl

/-- **Newton's identities for a finite multiset of complex numbers.** -/
theorem newton_multiset (s : Multiset ℂ) (k : ℕ) (hk : 0 < k) :
    (s.map (fun r => r ^ k)).sum
      = (-1 : ℂ) ^ (k + 1) * k * s.esymm k
        - ∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 ∈ Set.Ioo 0 k),
            (-1 : ℂ) ^ a.1 * s.esymm a.1 * (s.map (fun r => r ^ a.2)).sum := by
  classical
  set l := s.toList with hldef
  set f : Fin l.length → ℂ := l.get with hfdef
  have hmap : (Finset.univ : Finset (Fin l.length)).val.map f = s := by
    rw [univ_val_map_ofFn, hfdef, List.ofFn_get, hldef, Multiset.coe_toList]
  have hps : ∀ m : ℕ, MvPolynomial.aeval f (MvPolynomial.psum (Fin l.length) ℂ m)
      = (s.map (fun r => r ^ m)).sum := by
    intro m
    rw [MvPolynomial.psum, map_sum]
    simp only [map_pow, MvPolynomial.aeval_X]
    rw [Finset.sum_eq_multiset_sum, ← hmap, Multiset.map_map]
    rfl
  have hes : ∀ m : ℕ, MvPolynomial.aeval f (MvPolynomial.esymm (Fin l.length) ℂ m)
      = s.esymm m := by
    intro m
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, hmap]
  have hnewton := MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin l.length) ℂ k hk
  have := congrArg (MvPolynomial.aeval f) hnewton
  rw [hps k, map_sub, map_mul, map_mul, hes k, map_sum] at this
  rw [this]
  congr 1
  · simp
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_mul, map_mul, hes a.1, hps a.2]
    simp

end Newton

section PowerSumId

/-! ### `P_m(n)` IS the `m`-th power sum of the roots of `g_n`

This is the content of the write-up's Lemma, and it is what `Hpoly` was waiting for.  Three
ingredients meet here: `Pcoef` is DEFINED by the Newton recurrence; `Acoef_eval_eq_esymm`
(Vieta) identifies `A_j(n)` with `(−1)^j e_j` of the roots of `g_n`; and Newton's identities
say the power sums satisfy that same recurrence.  So the two sequences agree by a strong
induction, with no analysis anywhere.

The one piece of care: the induction must run for EVERY `k ≥ 1`, not only `k ≤ n`, because
`Hpoly` sums `m` up to `D`.  That is why `Acoef_eval_eq_esymm_all` comes first — above the
degree both sides vanish, `A_j(n)` because `(n)_j = 0` and `e_j` because a multiset of `n`
elements has no `j`-subsets, so the Vieta identity holds unrestrictedly.
-/

/-- `e_j` of a multiset vanishes above its cardinality. -/
theorem esymm_eq_zero_of_card_lt (s : Multiset ℂ) {j : ℕ} (h : Multiset.card s < j) :
    s.esymm j = 0 := by
  rw [Multiset.esymm, Multiset.powersetCard_eq_empty j h]
  simp

/-- **Vieta for `g_n`, for every index.**  Above the degree both sides are `0`. -/
theorem Acoef_eval_eq_esymm_all (g : Polynomial ℂ) (D n j : ℕ) (hn : n ≤ D)
    (hdeg : g.natDegree = D) (hlead : g.coeff D = 1) :
    (Acoef (fun i => g.coeff (D - i)) D j).eval (n : ℂ)
      = (-1 : ℂ) ^ j * (gnorm g D n).roots.esymm j := by
  by_cases hj : j ≤ n
  · exact Acoef_eval_eq_esymm g D n j hj hn hdeg hlead
  · have hj' : n < j := by omega
    rw [Acoef_eval_eq_zero_of_lt _ D hj',
      esymm_eq_zero_of_card_lt _ (by rw [gnorm_card_roots g D n hn hdeg hlead]; exact hj')]
    ring

/-- Newton's identities with the inner sum over `Finset.Ico 1 k` rather than a filtered
antidiagonal — the shape `Pcoef`'s recurrence is written in. -/
theorem newton_multiset_Ico (s : Multiset ℂ) (k : ℕ) (hk : 0 < k) :
    (s.map (fun r => r ^ k)).sum
      = (-1 : ℂ) ^ (k + 1) * k * s.esymm k
        - ∑ i ∈ Finset.Ico 1 k, (-1 : ℂ) ^ i * s.esymm i * (s.map (fun r => r ^ (k - i))).sum := by
  classical
  rw [newton_multiset s k hk]
  congr 1
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun i _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Set.mem_Ioo]
  omega

/-- **`P_k(n)` is the `k`-th power sum of the roots of `g_n`** — the write-up's Lemma, with no
logarithm and no analysis: `Pcoef`'s defining recurrence and Newton's identities are the SAME
recurrence once Vieta is substituted, so the two sequences agree by induction. -/
theorem Pcoef_eval_eq_psum (g : Polynomial ℂ) (D n : ℕ) (hn : n ≤ D)
    (hdeg : g.natDegree = D) (hlead : g.coeff D = 1) :
    ∀ k : ℕ, 0 < k →
      (Pcoef (fun i => g.coeff (D - i)) D k).eval (n : ℂ)
        = ((gnorm g D n).roots.map (fun r => r ^ k)).sum := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
    set s := (gnorm g D n).roots with hs
    have hA : ∀ j : ℕ,
        (Acoef (fun i => g.coeff (D - i)) D j).eval (n : ℂ) = (-1 : ℂ) ^ j * s.esymm j :=
      fun j => Acoef_eval_eq_esymm_all g D n j hn hdeg hlead
    rw [Pcoef_succ, Polynomial.eval_sub, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_natCast]
    rw [newton_multiset_Ico s (t + 1) (Nat.succ_pos t), hA (t + 1)]
    have hsum : ∑ m ∈ range t,
          ((Pcoef (fun i => g.coeff (D - i)) D (m + 1)).eval (n : ℂ) *
            (Acoef (fun i => g.coeff (D - i)) D (t - m)).eval (n : ℂ))
        = ∑ i ∈ Finset.Ico 1 (t + 1),
            (-1 : ℂ) ^ i * s.esymm i * (s.map (fun r => r ^ (t + 1 - i))).sum := by
      refine Finset.sum_nbij' (fun m => t - m) (fun i => t - i) ?_ ?_ ?_ ?_ ?_
      · intro m hm
        simp only [Finset.mem_range] at hm
        simp only [Finset.mem_Ico]
        omega
      · intro i hi
        simp only [Finset.mem_Ico] at hi
        simp only [Finset.mem_range]
        omega
      · intro m hm
        simp only [Finset.mem_range] at hm
        omega
      · intro i hi
        simp only [Finset.mem_Ico] at hi
        omega
      · intro m hm
        simp only [Finset.mem_range] at hm
        have hidx : t + 1 - (t - m) = m + 1 := by omega
        rw [hidx, hA (t - m), ih (m + 1) (by omega) (by omega)]
        ring
    rw [hsum]
    push_cast
    ring

end PowerSumId

section Means

/-! ### `(means)`: `H(D − ρ) = M_ρ(g)`

With `P_m(n)` identified as the `m`-th power sum of the roots of `g_n`, the write-up's first
displayed fact is a finite rearrangement and nothing more.  Write `n = D − ρ`, which is at least
`1` because `ρ < D`.  Expanding `g` at each root of `g_n` and summing,

  `∑_{r} g(r) = ∑_{k ≤ D} g_k · p_k = c_D · n + ∑_{m=1}^{D} c_{D−m} · P_m(n)`,

since `p_0 = n` and `g_k = c_{D−k}`.  Dividing by `n` is exactly `H(n)`, because `H`'s `m`-th
term is `c_{D−m} · P_m/u` and `divX` is an exact quotient (`P_m(0) = 0`).
-/

/-- `p/X` evaluated away from `0`, when `p` vanishes at `0` so the quotient is exact. -/
theorem divX_eval_of_eval_zero (p : Polynomial ℂ) (h0 : p.eval 0 = 0) {x : ℂ} (hx : x ≠ 0) :
    p.divX.eval x = p.eval x / x := by
  have hc : p.coeff 0 = 0 := by rw [Polynomial.coeff_zero_eq_eval_zero]; exact h0
  have h := Polynomial.divX_mul_X_add p
  rw [hc, map_zero, add_zero] at h
  have hx' := congrArg (Polynomial.eval x) h
  simp only [Polynomial.eval_mul, Polynomial.eval_X] at hx'
  exact (eq_div_iff hx).mpr hx'

/-- A finite sum pulled out of a multiset sum. -/
theorem multiset_sum_map_finsetSum {ι : Type*} (s : Multiset ℂ) (t : Finset ι) (F : ι → ℂ → ℂ) :
    (s.map (fun r => ∑ k ∈ t, F k r)).sum = ∑ k ∈ t, (s.map (F k)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih, Finset.sum_add_distrib]

/-- **`H(n)` is the mean of `g` over the roots of `g_n`.** -/
theorem Hpoly_eval_natCast (g : Polynomial ℂ) (D n : ℕ) (hn : n ≤ D) (hn0 : 0 < n)
    (hdeg : g.natDegree = D) (hlead : g.coeff D = 1) :
    (Hpoly (fun i => g.coeff (D - i)) D).eval (n : ℂ)
      = (((gnorm g D n).roots.map (fun r => g.eval r)).sum) / (n : ℂ) := by
  classical
  have hnne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
  have hcard : Multiset.card (gnorm g D n).roots = n := gnorm_card_roots g D n hn hdeg hlead
  -- the root sum, expanded coefficientwise
  have hg : ∀ r : ℂ, g.eval r = ∑ k ∈ range (D + 1), g.coeff k * r ^ k := by
    intro r
    conv_lhs => rw [Polynomial.eval_eq_sum_range r]
    rw [hdeg]
  have hp0 : ((gnorm g D n).roots.map (fun r => r ^ 0)).sum = (n : ℂ) := by
    simp [hcard]
  have hroots : ((gnorm g D n).roots.map (fun r => g.eval r)).sum
      = (∑ k ∈ range D,
            g.coeff (k + 1) * ((gnorm g D n).roots.map (fun r => r ^ (k + 1))).sum)
          + g.coeff 0 * (n : ℂ) := by
    rw [Multiset.map_congr rfl (fun r _ => hg r), multiset_sum_map_finsetSum,
      Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Multiset.sum_map_mul_left]
    · rw [Multiset.sum_map_mul_left, hp0]
  -- the interpolant, term by term
  have hterm : ∀ m ∈ Finset.Icc 1 D,
      g.coeff (D - (D - m)) *
          (Pcoef (fun i => g.coeff (D - i)) D m).divX.eval (n : ℂ)
        = g.coeff (D - (D - m))
            * ((gnorm g D n).roots.map (fun r => r ^ m)).sum / (n : ℂ) := by
    intro m hm
    have hm1 := (Finset.mem_Icc.mp hm).1
    rw [divX_eval_of_eval_zero _ (Pcoef_eval_zero _ D m) hnne,
      Pcoef_eval_eq_psum g D n hn hdeg hlead m hm1]
    ring
  have hreindex : ∑ m ∈ Finset.Icc 1 D,
        g.coeff (D - (D - m)) * ((gnorm g D n).roots.map (fun r => r ^ m)).sum / (n : ℂ)
      = (∑ k ∈ range D,
          g.coeff (k + 1) * ((gnorm g D n).roots.map (fun r => r ^ (k + 1))).sum) / (n : ℂ) := by
    rw [Finset.sum_div]
    refine Finset.sum_nbij' (fun m => m - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      simp only [Finset.mem_range]
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Icc]
      omega
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      omega
    · intro k hk
      omega
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      have h1 : m - 1 + 1 = m := by omega
      have h2 : D - (D - m) = m := by omega
      rw [h1, h2]
  rw [Hpoly, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [Finset.sum_congr rfl hterm, hreindex, hroots]
  have hc0 : g.coeff (D - D) = g.coeff 0 := by rw [Nat.sub_self]
  rw [hc0]
  field_simp
  ring

/-- **The write-up's `(means)`.**  `H(D − ρ) = M_ρ(g)` for `ρ < D` — the first of the two
hypotheses `conj2_of_H` still carries. -/
theorem means_of_Hpoly (g : Polynomial ℂ) (D : ℕ) (hdeg : g.natDegree = D)
    (hlead : g.coeff D = 1) (ρ : ℕ) (hρ : ρ < D) :
    Mrho g D ρ = (Hpoly (fun i => g.coeff (D - i)) D).eval ((D : ℂ) - (ρ : ℂ)) := by
  have hρD : ρ ≤ D := hρ.le
  have hcast : ((D - ρ : ℕ) : ℂ) = (D : ℂ) - (ρ : ℂ) := by
    push_cast [Nat.cast_sub hρD]
    ring
  rw [Mrho_via_gnorm g D ρ hρD, ← hcast,
    Hpoly_eval_natCast g D (D - ρ) (by omega) (by omega) hdeg hlead]

end Means

section Endpoint

/-! ### `(endpoint)`: `H(0) = J_D(c)`

The second of the two facts `conj2_of_H` carries.  `H`'s `m`-th term at `0` is
`(P_m/u)(0) = [u^1] P_m`, and the recurrence computes that coefficient outright: every product
`P_j · A_{m−j}` in the sum has a DOUBLE zero at the origin (both factors vanish there), so it
contributes nothing to `[u^1]`, and only the leading term `−m·A_m` survives.  Then
`[u^1] A_m = c_m·[u^1](u)_m / (D)_m` and `[u^1](u)_m = (−1)^{m−1}(m−1)!`, so

  `[u^1] P_m = (−1)^m·m!·c_m / (D)_m = (−1)^m·c_m / C(D,m)`,

which is the `m`-th summand of `J_D(c)`.  The `m = 0` summand of `J_D` is `c_0·c_D`, and `c_0`
is `g`'s leading coefficient `1`, so it is `H`'s constant term `c_D`.  **No analysis, and no
hypothesis beyond `g` monic.**
-/

/-- `[x^1](p·q) = 0` when both factors vanish at the origin. -/
theorem coeff_one_mul_of_coeff_zero (p q : Polynomial ℂ) (hp : p.coeff 0 = 0)
    (hq : q.coeff 0 = 0) : (p * q).coeff 1 = 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp [hp, hq]

/-- `[x^1]p` as the derivative at the origin — the form the Pochhammer recurrence is easiest in. -/
theorem coeff_one_eq_derivative_eval_zero (p : Polynomial ℂ) :
    p.coeff 1 = (Polynomial.derivative p).eval 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  simp

theorem descPochhammer_coeff_zero_succ (n : ℕ) : (descPochhammer ℂ (n + 1)).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact descPochhammer_ne_zero_eval_zero (R := ℂ) (Nat.succ_ne_zero n)

/-- **`[u^1](u)_{n+1} = (−1)^n·n!`.** -/
theorem descPochhammer_coeff_one (n : ℕ) :
    (descPochhammer ℂ (n + 1)).coeff 1 = (-1 : ℂ) ^ n * (n.factorial : ℂ) := by
  induction n with
  | zero => simp [descPochhammer_one]
  | succ n ih =>
    rw [coeff_one_eq_derivative_eval_zero, descPochhammer_succ_right,
      Polynomial.derivative_mul]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_natCast,
      sub_zero, mul_one, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_natCast, zero_sub]
    rw [← coeff_one_eq_derivative_eval_zero, ih,
      descPochhammer_ne_zero_eval_zero (R := ℂ) (Nat.succ_ne_zero n)]
    push_cast [Nat.factorial_succ]
    ring

theorem Acoef_coeff_zero_succ (c : ℕ → ℂ) (D m : ℕ) : (Acoef c D (m + 1)).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact Acoef_eval_zero c D (Nat.succ_ne_zero m)

theorem Acoef_coeff_one (c : ℕ → ℂ) (D m : ℕ) :
    (Acoef c D (m + 1)).coeff 1
      = c (m + 1) / (D.descFactorial (m + 1) : ℂ) * ((-1 : ℂ) ^ m * (m.factorial : ℂ)) := by
  rw [Acoef, Polynomial.coeff_C_mul, descPochhammer_coeff_one]

theorem Pcoef_coeff_zero (c : ℕ → ℂ) (D m : ℕ) : (Pcoef c D m).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact Pcoef_eval_zero c D m

/-- **Only the leading term of the recurrence reaches `[u^1]`.** -/
theorem Pcoef_coeff_one (c : ℕ → ℂ) (D t : ℕ) :
    (Pcoef c D (t + 1)).coeff 1 = -((t + 1 : ℕ) : ℂ) * (Acoef c D (t + 1)).coeff 1 := by
  classical
  rw [Pcoef_succ, Polynomial.coeff_sub, Polynomial.finsetSum_coeff]
  have hz : ∀ m ∈ range t, (Pcoef c D (m + 1) * Acoef c D (t - m)).coeff 1 = 0 := by
    intro m hm
    have hm' := Finset.mem_range.mp hm
    obtain ⟨j, hj⟩ : ∃ j, t - m = j + 1 := ⟨t - m - 1, by omega⟩
    rw [hj]
    exact coeff_one_mul_of_coeff_zero _ _ (Pcoef_coeff_zero c D (m + 1))
      (Acoef_coeff_zero_succ c D j)
  rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, sub_zero]
  have hC : -((t + 1 : ℕ) : Polynomial ℂ) * Acoef c D (t + 1)
      = Polynomial.C (-((t + 1 : ℕ) : ℂ)) * Acoef c D (t + 1) := by
    rw [map_neg, Polynomial.C_eq_natCast]
  rw [hC, Polynomial.coeff_C_mul]

/-- **`(P_m/u)(0) = (−1)^m·c_m / C(D,m)`** — the `m`-th summand of `J_D(c)`. -/
theorem Pcoef_divX_eval_zero (c : ℕ → ℂ) (D m : ℕ) (hm : 0 < m) (hmD : m ≤ D) :
    (Pcoef c D m).divX.eval 0 = (-1 : ℂ) ^ m * c m / (D.choose m : ℂ) := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have hchoose : (0 : ℕ) < D.choose (t + 1) := Nat.choose_pos hmD
  have hcne : ((D.choose (t + 1) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hchoose.ne'
  have hfne : (((t + 1).factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have htf : ((t.factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hdf : ((D.descFactorial (t + 1) : ℕ) : ℂ)
      = (((t + 1).factorial : ℕ) : ℂ) * ((D.choose (t + 1) : ℕ) : ℂ) := by
    rw [← Nat.cast_mul, Nat.descFactorial_eq_factorial_mul_choose]
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_divX, Pcoef_coeff_one,
    Acoef_coeff_one, hdf]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- **The write-up's `(endpoint)`.**  `H(0) = J_D(c)` for monic `g` — the second of the two
hypotheses `conj2_of_H` still carries. -/
theorem endpoint_of_Hpoly (g : Polynomial ℂ) (D : ℕ) (hlead : g.coeff D = 1) :
    (Hpoly (fun i => g.coeff (D - i)) D).eval 0 = Jsum D (fun i => g.coeff (D - i)) := by
  classical
  rw [Hpoly, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  have hterm : ∀ m ∈ Finset.Icc 1 D,
      g.coeff (D - (D - m)) * (Pcoef (fun i => g.coeff (D - i)) D m).divX.eval 0
        = (-1 : ℂ) ^ m * g.coeff (D - m) * g.coeff (D - (D - m)) / (D.choose m : ℂ) := by
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    rw [Pcoef_divX_eval_zero _ D m hm'.1 hm'.2]
    ring
  rw [Finset.sum_congr rfl hterm]
  rw [Jsum, Finset.sum_range_succ']
  have hreindex : ∑ m ∈ Finset.Icc 1 D,
        (-1 : ℂ) ^ m * g.coeff (D - m) * g.coeff (D - (D - m)) / (D.choose m : ℂ)
      = ∑ k ∈ range D,
          (-1 : ℂ) ^ (k + 1) * g.coeff (D - (k + 1)) * g.coeff (D - (D - (k + 1)))
            / (D.choose (k + 1) : ℂ) := by
    refine Finset.sum_nbij' (fun m => m - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      simp only [Finset.mem_range]
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Icc]
      omega
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      omega
    · intro k _
      omega
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      have h1 : m - 1 + 1 = m := by omega
      rw [h1]
  rw [hreindex]
  have hzero : (-1 : ℂ) ^ (0 : ℕ) * g.coeff (D - 0) * g.coeff (D - (D - 0))
        / (D.choose 0 : ℂ)
      = g.coeff (D - D) := by
    rw [Nat.sub_zero, Nat.choose_zero_right, hlead]
    norm_num
  rw [hzero]
  exact add_comm _ _

end Endpoint

section Unconditional

/-! ### Conjecture 2, unconditionally

`conj2_of_H` carried exactly two hypotheses, `(means)` and `(endpoint)`, and both are now
theorems for monic `g`.  Composing them discharges the spine.

Monicity is no restriction: `M_ρ` is homogeneous of degree one in `f` — scaling `f` scales every
`f(r)` and moves no root of `f^{(ρ)}` — so the general statement follows from the monic one by a
single scalar.
-/

/-- `M_ρ` is homogeneous of degree one: scaling `f` moves no root of `f^{(ρ)}`. -/
theorem Mrho_C_mul (f : Polynomial ℂ) (D ρ : ℕ) {a : ℂ} (ha : a ≠ 0) :
    Mrho (Polynomial.C a * f) D ρ = a * Mrho f D ρ := by
  unfold Mrho
  rw [Polynomial.iterate_derivative_C_mul, Polynomial.roots_C_mul _ ha]
  have hmap : ((Polynomial.derivative^[ρ] f).roots.map
        (fun r => (Polynomial.C a * f).eval r))
      = (Polynomial.derivative^[ρ] f).roots.map (fun r => a * f.eval r) := by
    refine Multiset.map_congr rfl (fun r _ => ?_)
    simp
  rw [hmap, Multiset.sum_map_mul_left, mul_div_assoc]

/-- **Conjecture 2 for monic `g` of odd degree, unconditionally.** -/
theorem conj2_monic (g : Polynomial ℂ) (D : ℕ) (hD : Odd D) (hD1 : 0 < D)
    (hdeg : g.natDegree = D) (hlead : g.coeff D = 1) :
    ∑ ρ ∈ Finset.Ico 1 D, (-1 : ℂ) ^ ρ * (D.choose ρ : ℂ) * Mrho g D ρ = 0 :=
  conj2_of_H g D hD hD1 (fun i => g.coeff (D - i))
    (fun ρ hρ => means_of_Hpoly g D hdeg hlead ρ hρ)
    (endpoint_of_Hpoly g D hlead)

/-- **Wojnar–Wojnar–Brin Conjecture 2, unconditionally.**  For every nonzero `f ∈ ℂ[x]` of odd
degree `D`, the alternating binomial combination of the means of `f` over the roots of its
derivatives vanishes. -/
theorem conj2 (f : Polynomial ℂ) (D : ℕ) (hD : Odd D) (hD1 : 0 < D)
    (hdeg : f.natDegree = D) (hf : f ≠ 0) :
    ∑ ρ ∈ Finset.Ico 1 D, (-1 : ℂ) ^ ρ * (D.choose ρ : ℂ) * Mrho f D ρ = 0 := by
  set a := f.leadingCoeff with hadef
  have ha : a ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
  have hainv : a⁻¹ ≠ 0 := inv_ne_zero ha
  set g := Polynomial.C a⁻¹ * f with hgdef
  have hgdeg : g.natDegree = D := by
    rw [hgdef, Polynomial.natDegree_C_mul hainv, hdeg]
  have hglead : g.coeff D = 1 := by
    rw [hgdef, Polynomial.coeff_C_mul, ← hdeg, ← Polynomial.leadingCoeff, ← hadef,
      inv_mul_cancel₀ ha]
  have hfg : f = Polynomial.C a * g := by
    rw [hgdef, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ ha, Polynomial.C_1, one_mul]
  have hsum : ∀ ρ : ℕ, Mrho f D ρ = a * Mrho g D ρ := by
    intro ρ
    rw [hfg, Mrho_C_mul g D ρ ha]
  have := conj2_monic g D hD hD1 hgdeg hglead
  calc ∑ ρ ∈ Finset.Ico 1 D, (-1 : ℂ) ^ ρ * (D.choose ρ : ℂ) * Mrho f D ρ
      = a * ∑ ρ ∈ Finset.Ico 1 D, (-1 : ℂ) ^ ρ * (D.choose ρ : ℂ) * Mrho g D ρ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun ρ _ => ?_)
        rw [hsum ρ]
        ring
    _ = 0 := by rw [this, mul_zero]

end Unconditional

end Principia.MathDB.P336466
