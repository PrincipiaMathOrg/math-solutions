import Mathlib

/-!
# MathDB #351518 — a counterexample to positive shifted Laguerre–Pólya preservation

Write-up `mathdb-open-problems/problems/351518/solution.tex`,
*A counterexample to positive shifted Laguerre–Pólya preservation*, 13 September 2026.
Source: I. Wagner, *On a new class of Laguerre–Pólya type functions*, arXiv:2108.01827v2,
pp. 3–4 and **Conjecture 4.3** on p. 11 (Pacific J. Math. **320** (2022), 177–192).

Wagner's Conjecture 4.3 asserts `L_j(φ) ∈ SL-P⁺` for every `φ ∈ SL-P⁺` and every positive
integer `j`, where `|φ(x+iy)|² = ∑_j L_j(φ)(x) y^{2j}` and `L₁(φ) = (φ')² − φφ''`.

**`main` refutes it already at `j = 1`**, with the witness `φ(z) = 1 + e^z`.

## The two halves

*Membership.*  `SLP` is the source's own definition (p. 3), unbundled into its two conditions:

* `TypeI` — there are real polynomials `p_N` converging **locally uniformly on `ℂ`** to `φ`
  such that for each fixed `d`, `p_N^{(deg p_N − d)}` has all roots real and of one strict sign
  for all large `N`;
* `EvNonneg` — the coefficients `γ_n = φ^{(n)}(0)` are eventually nonnegative (in `ComplexOrder`,
  so this says they are real AND `≥ 0`).

`p_N(x) = (x/N + 1)^N + 1` works.  `iter_derivative_lin_pow` is the source's display (1) as an
exact polynomial identity — `p_N^{(N-d)} = C(N^{̲͟d͟} / N^{N-d}) · (x/N + 1)^d`, by induction using
`Nat.descFactorial_succ` — and `allRoots_C_mul_lin_pow` reads off its `d` roots, all equal to
`−N`.  `exp_bound` is the one piece of analysis: Mathlib's `norm_log_one_add_sub_self_le` gives
`‖log(1+w) − w‖ ≤ ‖w‖²/(2(1−‖w‖))`, so at `w = z/N` the exponent `N·log(1+z/N)` is within
`R²/N` of `z` uniformly on `‖z‖ ≤ R`, and `norm_exp_sub_one_le` converts that into
`‖(z/N+1)^N − e^z‖ ≤ 2e^R R²/N`.  Mathlib has only the POINTWISE limit
(`Complex.tendsto_one_add_div_pow_exp`), which is not enough for the source's condition.

*Failure.*  `L1_wit` computes `L₁(1 + e^z) = −e^z`, so every `γ_n` of the image equals `−1` and
`EvNonneg` fails — `not_evNonneg_L1_wit`.

## The 215 check

* The conjecture quantifies over `j`; refuting the single instance `j = 1` is STRONGER than
  refuting the `∀ j` conjunction, and that is what `main` states.
* The write-up's proof verifies the root condition `for fixed d ≥ 1`.  **`d = 0` is free** — the
  top derivative is a nonzero constant with no roots at all — so `TypeI` here carries NO lower
  bound on `d`, which makes the class strictly more demanding and the membership claim strictly
  stronger than the write-up's.
* `main_sharp` states the result without reference to how the class is bundled: the witness
  satisfies BOTH source conditions, and its image fails the coefficient condition, which is part
  of every reading of `SL-P⁺`.  So the refutation is not an artifact of the packaging.
* Roots are required to share a STRICT sign (`< 0` or `> 0`), not merely to be `≤ 0`; the
  witness's roots are `−N`, so the stricter reading is what is verified.

## Absent

The write-up also records the coefficient criterion of Wagner's Theorem 1.1 as a *separate*
check of membership (the shifted Jensen polynomials `J^{d,m}(X) = a^m(1+aX)^d`).  That is a
second, independent route to `φ ∈ SL-P⁺` resting on a cited theorem, and it is **not**
formalized here — the direct approximation definition is, which is the one the source states.
The general family `c + e^{ax}` and the odd `j > 1` cases are also not formalized; `j = 1` at
`a = c = 1` suffices to refute, and refuting one instance is the stronger statement.
Tasks 2–5 of the write-up are questions, not solved problems.

Checked in Python before formalizing (`verify_351518.py`, symbolic): `L₁(c+e^{ax}) =
−ca²e^{ax}` and its agreement with the source's display (3) at `j = 1,2,3`; the modulus
identity `|φ(x+iy)|² = c² + e^{2ax} + 2ce^{ax}cos(ay)` (symbolic difference exactly `0`, and
`0` mismatches over 2000 random `(x,y,a,c)`); the derivative identity (1) for `2 ≤ N ≤ 8` and
every `1 ≤ d < N`; `γ_0 = c+1`, `γ_n = a^n`; the Jensen identity for `d ≤ 5`, `m ≤ 4`; every
`γ_n` of `L₁(φ)` equal to `−ca^{n+2} < 0`; and the numeric slack in the `R²/N` estimate.
-/

namespace Principia.MathDB.P351518

open Polynomial Filter Topology ComplexOrder

/-! ### The class -/

/-- All roots of a real polynomial are real (it splits over `ℝ`) and share one strict sign. -/
def AllRootsRealOneSign (q : Polynomial ℝ) : Prop :=
  Multiset.card q.roots = q.natDegree ∧
    ((∀ r ∈ q.roots, r < 0) ∨ (∀ r ∈ q.roots, 0 < r))

/-- Wagner's type-I shifted class condition. -/
def TypeI (φ : ℂ → ℂ) : Prop :=
  ∃ p : ℕ → Polynomial ℝ,
    TendstoLocallyUniformly (fun N (z : ℂ) => aeval z (p N)) φ atTop ∧
    ∀ d : ℕ, ∀ᶠ N in atTop,
      AllRootsRealOneSign (derivative^[(p N).natDegree - d] (p N))

/-- The exponential Taylor coefficients `γ_n = φ^{(n)}(0)` are eventually nonnegative. -/
def EvNonneg (φ : ℂ → ℂ) : Prop := ∀ᶠ n in atTop, 0 ≤ iteratedDeriv n φ 0

/-- Membership in the positive shifted Laguerre–Pólya class. -/
def SLP (φ : ℂ → ℂ) : Prop := TypeI φ ∧ EvNonneg φ

/-- The source's operator `L₁(φ) = (φ')² − φ φ''`. -/
noncomputable def L1 (φ : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (deriv φ z) ^ 2 - φ z * deriv (deriv φ) z

/-- The witness `φ(z) = 1 + e^z`. -/
noncomputable def wit : ℂ → ℂ := fun z => 1 + Complex.exp z

/-! ### The operator at the witness -/

theorem deriv_wit : deriv wit = Complex.exp := by
  have h : wit = fun z : ℂ => 1 + Complex.exp z := rfl
  rw [h]
  funext z
  simp [Complex.deriv_exp]

theorem L1_wit : L1 wit = fun z => -Complex.exp z := by
  funext z
  simp only [L1, deriv_wit, wit, Complex.deriv_exp]
  ring

theorem iteratedDeriv_exp (n : ℕ) : iteratedDeriv n Complex.exp = Complex.exp := by
  induction n with
  | zero => simp
  | succ k ih => rw [iteratedDeriv_succ, ih, Complex.deriv_exp]

theorem iteratedDeriv_neg_exp (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => -Complex.exp z) = fun z => -Complex.exp z := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    simp

/-- `L₁` of the witness has EVERY Taylor coefficient equal to `−1`. -/
theorem not_evNonneg_L1_wit : ¬ EvNonneg (L1 wit) := by
  intro h
  rw [L1_wit] at h
  obtain ⟨n, hn⟩ := h.exists
  rw [iteratedDeriv_neg_exp n] at hn
  simp only [Complex.exp_zero] at hn
  rw [Complex.le_def] at hn
  norm_num at hn

/-! ### The witness is in the class: the coefficient half -/

theorem iteratedDeriv_wit_succ (n : ℕ) : iteratedDeriv (n + 1) wit = Complex.exp := by
  rw [iteratedDeriv_succ', deriv_wit, iteratedDeriv_exp]

theorem evNonneg_wit : EvNonneg wit := by
  rw [EvNonneg, eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [iteratedDeriv_wit_succ, Complex.exp_zero, Complex.le_def]
  norm_num

/-! ### The witness is in the class: the approximating polynomials -/

/-- The linear factor `b·X + 1`. -/
noncomputable def lin (b : ℝ) : Polynomial ℝ := C b * X + C 1

theorem derivative_lin (b : ℝ) : derivative (lin b) = C b := by
  simp [lin]

theorem natDegree_lin (b : ℝ) (hb : b ≠ 0) : (lin b).natDegree = 1 :=
  natDegree_linear hb

theorem iter_derivative_add (k : ℕ) (p q : Polynomial ℝ) :
    derivative^[k] (p + q) = derivative^[k] p + derivative^[k] q := by
  induction k generalizing p q with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply, derivative_add, ih]

theorem derivative_lin_pow (b : ℝ) (m : ℕ) :
    derivative ((lin b) ^ (m + 1)) = C (((m : ℝ) + 1) * b) * (lin b) ^ m := by
  rw [derivative_pow, derivative_lin]
  push_cast
  simp only [map_mul]
  ring

/-- **The source's display (1)**, as an exact polynomial identity. -/
theorem iter_derivative_lin_pow (b : ℝ) :
    ∀ (k N : ℕ), k ≤ N →
      derivative^[k] ((lin b) ^ N)
        = C ((N.descFactorial k : ℝ) * b ^ k) * (lin b) ^ (N - k) := by
  intro k
  induction k with
  | zero => intro N _; simp
  | succ j ih =>
    intro N hN
    have hj : j ≤ N := by omega
    rw [Function.iterate_succ_apply', ih N hj]
    have hNj : N - j = (N - j - 1) + 1 := by omega
    rw [hNj, derivative_C_mul, derivative_lin_pow, ← mul_assoc, ← C_mul]
    have hcard : N.descFactorial (j + 1) = (N - j) * N.descFactorial j :=
      Nat.descFactorial_succ N j
    have hsub : N - (j + 1) = N - j - 1 := by omega
    rw [hsub, hcard]
    congr 1
    congr 1
    have : ((N - j - 1 : ℕ) : ℝ) + 1 = ((N - j : ℕ) : ℝ) := by
      have : (N - j - 1) + 1 = N - j := by omega
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
    rw [this]
    push_cast
    ring

/-- The roots of `C α · (b·X + 1)^d` are `d` copies of `−1/b`, all real and negative. -/
theorem allRoots_C_mul_lin_pow (b α : ℝ) (hb : 0 < b) (hα : α ≠ 0) (d : ℕ) :
    AllRootsRealOneSign (C α * (lin b) ^ d) := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hroots : (C α * (lin b) ^ d).roots = d • ({-b⁻¹} : Multiset ℝ) := by
    rw [roots_C_mul _ hα, roots_pow, lin, roots_C_mul_X_add_C 1 hb0]
    simp
  have hdeg : (C α * (lin b) ^ d).natDegree = d := by
    rw [natDegree_C_mul hα, natDegree_pow, natDegree_lin b hb0, mul_one]
  refine ⟨?_, Or.inl ?_⟩
  · rw [hroots, hdeg]
    simp
  · intro r hr
    rw [hroots, Multiset.nsmul_singleton] at hr
    have : r = -b⁻¹ := Multiset.eq_of_mem_replicate hr
    rw [this]
    simpa using inv_pos.mpr hb

/-! ### The approximating polynomials and their limit -/

/-- `p_N(x) = (x/N + 1)^N + 1`, the source's choice at `a = c = 1`. -/
noncomputable def pN (N : ℕ) : Polynomial ℝ := (lin (1 / N)) ^ N + C 1

theorem aeval_pN (N : ℕ) (z : ℂ) : (aeval z (pN N) : ℂ) = (z / N + 1) ^ N + 1 := by
  simp only [pN, lin, map_add, map_pow, map_mul, map_one, aeval_X, aeval_C,
    Complex.coe_algebraMap]
  push_cast
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · norm_num
  · have hne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp

/-- **The uniform estimate.**  Mathlib's `norm_log_one_add_sub_self_le` gives
`|log(1+w) - w| <= |w|^2/(2(1-|w|))`; at `w = z/N` that is `O(R^2/N)` uniformly on `|z| <= R`. -/
theorem exp_bound (R : ℝ) (hR : 0 < R) (N : ℕ) (hN : 4 * R ^ 2 + 4 * R + 4 ≤ (N : ℝ))
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖(z / N + 1) ^ N - Complex.exp z‖ ≤ 2 * Real.exp R * R ^ 2 / N := by
  have hNpos : (0 : ℝ) < N := by nlinarith
  set w : ℂ := z / N with hwdef
  have hw : ‖w‖ ≤ R / N := by
    rw [hwdef, norm_div, Complex.norm_natCast]
    gcongr
  have hRN : R / N ≤ 1 / 4 := by
    rw [div_le_iff₀ hNpos]
    nlinarith
  have hw4 : ‖w‖ ≤ 1 / 4 := hw.trans hRN
  have hwlt : ‖w‖ < 1 := by linarith
  have h1w : (1 : ℂ) + w ≠ 0 := by
    intro h
    have hm : w = -1 := by linear_combination h
    rw [hm] at hw4
    simp at hw4
    linarith
  have hlog := Complex.norm_log_one_add_sub_self_le hwlt
  have hlog2 : ‖Complex.log (1 + w) - w‖ ≤ R ^ 2 / (N : ℝ) ^ 2 := by
    refine hlog.trans ?_
    have hnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
    have hpos : (0 : ℝ) < 1 - ‖w‖ := by linarith
    have hid : (1 - ‖w‖)⁻¹ * (1 - ‖w‖) = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
    have hvpos : (0 : ℝ) < (1 - ‖w‖)⁻¹ := inv_pos.mpr hpos
    have hv2 : (1 - ‖w‖)⁻¹ ≤ 2 := by nlinarith [hid, hvpos]
    have hdp : (R / (N : ℝ)) ^ 2 = R ^ 2 / (N : ℝ) ^ 2 := div_pow R (N : ℝ) 2
    have husq : ‖w‖ ^ 2 ≤ R ^ 2 / (N : ℝ) ^ 2 := by nlinarith [hw, hnn, hdp]
    nlinarith [husq, hv2, sq_nonneg ‖w‖, hvpos]
  have hzw : z = (N : ℂ) * w := by
    have hne : (N : ℂ) ≠ 0 := by
      simpa using ne_of_gt hNpos
    rw [hwdef]; field_simp
  have hAB : ‖(N : ℂ) * Complex.log (1 + w) - z‖ ≤ R ^ 2 / N := by
    rw [hzw, ← mul_sub, norm_mul, Complex.norm_natCast]
    have hstep : (N : ℝ) * ‖Complex.log (1 + w) - w‖ ≤ (N : ℝ) * (R ^ 2 / (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hlog2 (le_of_lt hNpos)
    have hfin : (N : ℝ) * (R ^ 2 / (N : ℝ) ^ 2) = R ^ 2 / N := by
      field_simp
    linarith [hstep, hfin.le, hfin.ge]
  have hpow : (z / N + 1) ^ N = Complex.exp ((N : ℂ) * Complex.log (1 + w)) := by
    have h1 : z / (N : ℂ) + 1 = 1 + w := by rw [hwdef]; ring
    rw [h1]
    conv_lhs => rw [← Complex.exp_log h1w]
    rw [← Complex.exp_nsmul, nsmul_eq_mul]
  set A : ℂ := (N : ℂ) * Complex.log (1 + w) with hA
  have hsplit : Complex.exp A - Complex.exp z = Complex.exp z * (Complex.exp (A - z) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    ring_nf
  have hexpz : ‖Complex.exp z‖ ≤ Real.exp R := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm z).trans hz)
  have hR2N : R ^ 2 / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNpos]; nlinarith
  have hsub1 : ‖Complex.exp (A - z) - 1‖ ≤ 2 * (R ^ 2 / N) := by
    have hle : ‖A - z‖ ≤ 1 := hAB.trans hR2N
    have := Complex.norm_exp_sub_one_le hle
    linarith [hAB]
  rw [hpow, hsplit, norm_mul]
  have hnn : (0 : ℝ) ≤ ‖Complex.exp (A - z) - 1‖ := norm_nonneg _
  have hfinal : ‖Complex.exp z‖ * ‖Complex.exp (A - z) - 1‖
      ≤ Real.exp R * (2 * (R ^ 2 / N)) :=
    mul_le_mul hexpz hsub1 hnn (le_of_lt (Real.exp_pos R))
  have heq : Real.exp R * (2 * (R ^ 2 / N)) = 2 * Real.exp R * R ^ 2 / N := by ring
  linarith [hfinal, heq.le, heq.ge]

theorem tendsto_pN :
    TendstoLocallyUniformly (fun N (z : ℂ) => (aeval z (pN N) : ℂ)) wit atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε z0
  refine ⟨Metric.ball z0 1, Metric.ball_mem_nhds z0 one_pos, ?_⟩
  set R : ℝ := ‖z0‖ + 1 with hRdef
  have hR : 0 < R := by positivity
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => 2 * Real.exp R * R ^ 2 / (N : ℝ)) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hcast
  have h1 : ∀ᶠ N : ℕ in atTop, 2 * Real.exp R * R ^ 2 / (N : ℝ) < ε :=
    hlim.eventually (gt_mem_nhds hε)
  have h2 : ∀ᶠ N : ℕ in atTop, 4 * R ^ 2 + 4 * R + 4 ≤ (N : ℝ) :=
    hcast.eventually_ge_atTop _
  filter_upwards [h1, h2] with N hN1 hN2
  intro z hz
  have hball := Metric.mem_ball.mp hz
  rw [Complex.dist_eq] at hball
  have hzR : ‖z‖ ≤ R := by
    have hsp : z = z0 + (z - z0) := by ring
    have := norm_add_le z0 (z - z0)
    rw [← hsp] at this
    rw [hRdef]
    linarith
  have hkey := exp_bound R hR N hN2 z hzR
  rw [Complex.dist_eq, aeval_pN, wit]
  have hrw : 1 + Complex.exp z - ((z / N + 1) ^ N + 1)
      = -((z / N + 1) ^ N - Complex.exp z) := by ring
  rw [hrw, norm_neg]
  linarith

/-! ### The witness satisfies the type-I condition -/

theorem natDegree_pN (N : ℕ) (hN : 2 ≤ N) : (pN N).natDegree = N := by
  have hne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hb : (1 / (N : ℝ)) ≠ 0 := by simpa using hne
  have hdeg : ((lin (1 / (N : ℝ))) ^ N).natDegree = N := by
    rw [natDegree_pow, natDegree_lin _ hb, mul_one]
  rw [pN, natDegree_add_C, hdeg]

theorem typeI_wit : TypeI wit := by
  refine ⟨pN, tendsto_pN, ?_⟩
  intro d
  filter_upwards [eventually_ge_atTop (d + 2)] with N hN
  have hN2 : 2 ≤ N := by omega
  have hne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hbne : (1 / (N : ℝ)) ≠ 0 := by simpa using hne
  have hbpos : 0 < 1 / (N : ℝ) := by positivity
  rw [natDegree_pN N hN2]
  have hzero : derivative^[N - d] (C (1 : ℝ)) = 0 :=
    Polynomial.iterate_derivative_C (by omega)
  have hsplit : derivative^[N - d] (pN N)
      = derivative^[N - d] ((lin (1 / (N : ℝ))) ^ N) := by
    rw [pN, iter_derivative_add, hzero, add_zero]
  rw [hsplit, iter_derivative_lin_pow _ (N - d) N (by omega)]
  have hd2 : N - (N - d) = d := by omega
  rw [hd2]
  refine allRoots_C_mul_lin_pow _ _ hbpos ?_ d
  have hdf : N.descFactorial (N - d) ≠ 0 := by
    rw [Ne, Nat.descFactorial_eq_zero_iff_lt]
    omega
  have h1 : ((N.descFactorial (N - d) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hdf
  exact mul_ne_zero h1 (pow_ne_zero _ hbne)

/-! ### The refutation -/

theorem slp_wit : SLP wit := ⟨typeI_wit, evNonneg_wit⟩

/-- **The refutation, stated without reference to how the class is bundled.**  `1 + e^z`
satisfies BOTH of the source's conditions, and `L₁` of it fails the coefficient condition —
which is part of every reading of the class, so the failure is not an artifact of packaging. -/
theorem main_sharp : TypeI wit ∧ EvNonneg wit ∧ ¬ EvNonneg (L1 wit) :=
  ⟨typeI_wit, evNonneg_wit, not_evNonneg_L1_wit⟩

/-- **Wagner's Conjecture 4.3 is false**, already at `j = 1`. -/
theorem main : ¬ ∀ φ : ℂ → ℂ, SLP φ → SLP (L1 φ) := by
  intro h
  exact not_evNonneg_L1_wit (h wit slp_wit).2

end Principia.MathDB.P351518
