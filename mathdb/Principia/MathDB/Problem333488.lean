/-
MathDB #333488 — Hassan's Conjecture 3.1 for the complex rational delay recurrence

    z_{n+1} = (α + β z_{n−k}) / (γ − z_n).

The conjecture asserts that arbitrarily high least periods occur in this family.  We prove
the stronger explicit statement: for EVERY integer `p ≥ 2` there is a choice of delay `k`,
parameters `α, β, γ` (all nonzero and nonreal) and an initial history whose solution is
everywhere defined and has least period exactly `p`.

The construction collapses the delay: with `k = p − 1` the ansatz `z_{n−k} = z_{n+1}` turns
the two-step recurrence into the one-step Möbius map `T t w = 1/(t − w)`, whose orbit is
periodic of order exactly `p` when `t = 2 cos(π/p)`.  The whole argument is ALGEBRAIC in an
abstract pair `u, v` with `u + v = t` and `u * v = 1`; the only transcendental input is that
`u / v = exp(2πi/p)` is a primitive `p`-th root of unity, which is Mathlib's
`Complex.isPrimitiveRoot_exp`.  Sections 1–4 below therefore mention neither `exp` nor `cos`.

Reference: Sk. Sarif Hassan, *Dynamics of the complex rational delay recursive sequence
`z_{n+1} = (α + β z_{n−k})/(γ − z_n)`*, arXiv:1606.08887v1 (2016), pp. 1–2 and Conjecture 3.1,
p. 14.  Sibling row: `Problem333489.lean` refutes Conjecture 3.2 of the same paper.
-/
-- Scoped imports rather than `import Mathlib`, for the reason `MathDB/Gate.lean`'s own header
-- gives: a file should depend on exactly what it uses.  Measured 2026-09-30 -- `import Mathlib`
-- made this module take 825 s to build on this machine, and these four take minutes, with the
-- identical content elaborating clean.  Nothing is lost at gate time, since sibling modules pull
-- Mathlib in anyway.
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

set_option autoImplicit false

namespace Principia.MathDB.P333488

open Complex

/-! ## 1. The collapsed step map and its orbit -/

/-- The one-step Möbius map the delay collapses to. -/
noncomputable def T (t w : ℂ) : ℂ := 1 / (t - w)

/-- The forward orbit of `w₀` under `T t`. -/
noncomputable def orb (t w0 : ℂ) : ℕ → ℂ
  | 0 => w0
  | j + 1 => T t (orb t w0 j)

@[simp] theorem orb_zero (t w0 : ℂ) : orb t w0 0 = w0 := rfl

@[simp] theorem orb_succ (t w0 : ℂ) (j : ℕ) : orb t w0 (j + 1) = T t (orb t w0 j) := rfl

/-- Shifting the starting point along the orbit. -/
theorem orb_add (t w0 : ℂ) (a b : ℕ) : orb t w0 (a + b) = orb t (orb t w0 b) a := by
  induction a with
  | zero => simp
  | succ a ih =>
      have h : a + 1 + b = a + b + 1 := by omega
      rw [h, orb_succ, ih, orb_succ]

/-! ## 2. The upper half-plane is invariant, so the orbit never meets a pole -/

/-- For real `t`, a point of the open upper half-plane is never equal to `t`. -/
theorem sub_ne_zero_of_im_pos (t : ℝ) (w : ℂ) (hw : 0 < w.im) : ((t : ℂ) - w) ≠ 0 := by
  intro h
  have h1 : ((t : ℂ) - w).im = 0 := by rw [h]; simp
  simp at h1
  linarith

/-- `T t` preserves the open upper half-plane when `t` is real. -/
theorem im_T_pos (t : ℝ) (w : ℂ) (hw : 0 < w.im) : 0 < (T (t : ℂ) w).im := by
  have hne : ((t : ℂ) - w) ≠ 0 := sub_ne_zero_of_im_pos t w hw
  rw [T, one_div, Complex.inv_im]
  have h1 : ((t : ℂ) - w).im = -w.im := by simp
  have h2 : 0 < Complex.normSq ((t : ℂ) - w) := by rw [Complex.normSq_pos]; exact hne
  rw [h1, neg_neg]
  exact div_pos hw h2

/-- Hence every iterate stays in the upper half-plane: the solution is everywhere defined. -/
theorem orb_im_pos (t : ℝ) (w0 : ℂ) (h0 : 0 < w0.im) (j : ℕ) :
    0 < (orb (t : ℂ) w0 j).im := by
  induction j with
  | zero => simpa using h0
  | succ j ih => rw [orb_succ]; exact im_T_pos t _ ih

/-- The defining equation of the orbit, cleared of its denominator. -/
theorem orb_step_mul (t : ℝ) (w0 : ℂ) (h0 : 0 < w0.im) (j : ℕ) :
    orb (t : ℂ) w0 (j + 1) * ((t : ℂ) - orb (t : ℂ) w0 j) = 1 := by
  have hne : ((t : ℂ) - orb (t : ℂ) w0 j) ≠ 0 :=
    sub_ne_zero_of_im_pos t _ (orb_im_pos t w0 h0 j)
  rw [orb_succ, T, one_div, inv_mul_cancel₀ hne]

/-- A point of the upper half-plane is not a point of the closed lower half-plane. -/
theorem orb_ne_of_im_nonpos (t : ℝ) (w0 v : ℂ) (h0 : 0 < w0.im) (hv : v.im ≤ 0) (j : ℕ) :
    orb (t : ℂ) w0 j ≠ v := by
  intro h
  have := orb_im_pos t w0 h0 j
  rw [h] at this
  linarith

/-! ## 3. Conjugating `T` to a rotation

With `u + v = t` and `u * v = 1`, the points `u, v` are the fixed points of `T t`, and the
Möbius map `R u v` carries `T t` to multiplication by `u / v`. -/

/-- The conjugating Möbius map. -/
noncomputable def R (u v w : ℂ) : ℂ := (w - u) / (w - v)

theorem R_injective (u v a b : ℂ) (huv : u ≠ v) (ha : a ≠ v) (hb : b ≠ v)
    (h : R u v a = R u v b) : a = b := by
  have ha' : a - v ≠ 0 := sub_ne_zero.mpr ha
  have hb' : b - v ≠ 0 := sub_ne_zero.mpr hb
  rw [R, R, div_eq_div_iff ha' hb'] at h
  have hz : (u - v) * (a - b) = 0 := by linear_combination h
  have huv' : u - v ≠ 0 := sub_ne_zero.mpr huv
  rcases mul_eq_zero.mp hz with h1 | h2
  · exact absurd h1 huv'
  · linear_combination h2

/-- `u` is a fixed point of `T t`, in the precise form needed below. -/
theorem T_sub_left (t u v w : ℂ) (hsum : u + v = t) (huv : u * v = 1) (htw : t - w ≠ 0) :
    T t w - u = u * (w - u) / (t - w) := by
  rw [T, eq_div_iff htw, sub_mul, one_div, inv_mul_cancel₀ htw]
  linear_combination (-1 : ℂ) * huv + u * hsum

/-- and so is `v`. -/
theorem T_sub_right (t u v w : ℂ) (hsum : u + v = t) (huv : u * v = 1) (htw : t - w ≠ 0) :
    T t w - v = v * (w - v) / (t - w) := by
  rw [T, eq_div_iff htw, sub_mul, one_div, inv_mul_cancel₀ htw]
  linear_combination (-1 : ℂ) * huv + v * hsum

/-- The conjugation identity: `R ∘ T = (u/v) • R`. -/
theorem R_T (t u v w : ℂ) (hsum : u + v = t) (huv : u * v = 1) (htw : t - w ≠ 0)
    (hwv : w ≠ v) (hTv : T t w ≠ v) : R u v (T t w) = u / v * R u v w := by
  have hv0 : v ≠ 0 := by
    intro h; rw [h, mul_zero] at huv; exact one_ne_zero huv.symm
  have hwv' : w - v ≠ 0 := sub_ne_zero.mpr hwv
  have hTv' : T t w - v ≠ 0 := sub_ne_zero.mpr hTv
  rw [R, R, T_sub_left t u v w hsum huv htw, T_sub_right t u v w hsum huv htw]
  rw [T_sub_right t u v w hsum huv htw] at hTv'
  have hnum : v * (w - v) ≠ 0 := by
    intro h
    rw [h, zero_div] at hTv'
    exact hTv' rfl
  -- `field_simp` closes this outright; a trailing `ring` would error "No goals".
  field_simp

/-- The orbit is carried to a geometric progression. -/
theorem R_orb (t : ℝ) (u v w0 : ℂ) (hsum : u + v = (t : ℂ)) (huv : u * v = 1)
    (hvim : v.im ≤ 0) (h0 : 0 < w0.im) (j : ℕ) :
    R u v (orb (t : ℂ) w0 j) = (u / v) ^ j * R u v w0 := by
  induction j with
  | zero => simp
  | succ j ih =>
      have htw : (t : ℂ) - orb (t : ℂ) w0 j ≠ 0 :=
        sub_ne_zero_of_im_pos t _ (orb_im_pos t w0 h0 j)
      have hwv : orb (t : ℂ) w0 j ≠ v := orb_ne_of_im_nonpos t w0 v h0 hvim j
      have hTv : T (t : ℂ) (orb (t : ℂ) w0 j) ≠ v := by
        have := orb_ne_of_im_nonpos t w0 v h0 hvim (j + 1)
        rwa [orb_succ] at this
      rw [orb_succ, R_T (t : ℂ) u v _ hsum huv htw hwv hTv, ih]
      ring

/-- **The return characterisation.**  The orbit comes back to its start exactly when the
multiplier `u / v` returns to `1`.  This is where minimality of the period comes from. -/
theorem orb_eq_iff (t : ℝ) (u v w0 : ℂ) (hsum : u + v = (t : ℂ)) (huv : u * v = 1)
    (hvim : v.im ≤ 0) (h0 : 0 < w0.im) (huvne : u ≠ v) (hw0u : w0 ≠ u) (j : ℕ) :
    orb (t : ℂ) w0 j = w0 ↔ (u / v) ^ j = 1 := by
  have hw0v : w0 ≠ v := by
    have : orb (t : ℂ) w0 0 ≠ v := orb_ne_of_im_nonpos t w0 v h0 hvim 0
    simpa using this
  have hR0 : R u v w0 ≠ 0 := by
    rw [R, div_ne_zero_iff]
    exact ⟨sub_ne_zero.mpr hw0u, sub_ne_zero.mpr hw0v⟩
  constructor
  · intro h
    have hj := R_orb t u v w0 hsum huv hvim h0 j
    rw [h] at hj
    have hz : ((u / v) ^ j - 1) * R u v w0 = 0 := by linear_combination -hj
    rcases mul_eq_zero.mp hz with h1 | h2
    · linear_combination h1
    · exact absurd h2 hR0
  · intro h
    have hj := R_orb t u v w0 hsum huv hvim h0 j
    rw [h, one_mul] at hj
    exact R_injective u v _ _ huvne (orb_ne_of_im_nonpos t w0 v h0 hvim j) hw0v hj

/-! ## 4. The explicit parameters

`u = exp(iθ)`, `v = exp(−iθ)` with `θ = π/p`, so `t = u + v = 2 cos θ` is real. -/

/-- `θ p = π / p`. -/
noncomputable def thet (p : ℕ) : ℝ := Real.pi / p

/-- `t = 2 cos(π/p)`, a real number. -/
noncomputable def tt (p : ℕ) : ℝ := 2 * Real.cos (thet p)

noncomputable def uu (p : ℕ) : ℂ := Complex.exp ((thet p : ℂ) * I)

noncomputable def vv (p : ℕ) : ℂ := Complex.exp (-((thet p : ℂ) * I))

theorem exp_neg_re (θ : ℝ) : (Complex.exp (-((θ : ℂ) * I))).re = Real.cos θ := by
  rw [show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]

theorem exp_neg_im (θ : ℝ) : (Complex.exp (-((θ : ℂ) * I))).im = -Real.sin θ := by
  rw [show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_im, Real.sin_neg]

theorem uu_mul_vv (p : ℕ) : uu p * vv p = 1 := by
  rw [uu, vv, ← Complex.exp_add]
  simp

theorem uu_add_vv (p : ℕ) : uu p + vv p = ((tt p : ℝ) : ℂ) := by
  have h1 : (uu p).re = Real.cos (thet p) := Complex.exp_ofReal_mul_I_re _
  have h2 : (vv p).re = Real.cos (thet p) := exp_neg_re _
  have h3 : (uu p).im = Real.sin (thet p) := Complex.exp_ofReal_mul_I_im _
  have h4 : (vv p).im = -Real.sin (thet p) := exp_neg_im _
  apply Complex.ext
  · rw [Complex.add_re, h1, h2, Complex.ofReal_re]
    change Real.cos (thet p) + Real.cos (thet p) = 2 * Real.cos (thet p)
    ring
  · rw [Complex.add_im, h3, h4, Complex.ofReal_im]
    ring

theorem vv_im (p : ℕ) : (vv p).im = -Real.sin (thet p) := exp_neg_im _

theorem thet_pos (p : ℕ) (hp : 2 ≤ p) : 0 < thet p := by
  have hp' : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  exact div_pos Real.pi_pos hp'

theorem thet_le (p : ℕ) (hp : 2 ≤ p) : thet p ≤ Real.pi / 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hp2

theorem sin_thet_pos (p : ℕ) (hp : 2 ≤ p) : 0 < Real.sin (thet p) := by
  refine Real.sin_pos_of_pos_of_lt_pi (thet_pos p hp) ?_
  have := thet_le p hp
  have := Real.pi_pos
  linarith

/-- `0 ≤ t`, which is all that the parameter `γ` needs.  (The source also records `t < 2`;
that bound is used there only to see `1 + t > 0`, so it is not needed here.) -/
theorem tt_nonneg (p : ℕ) (hp : 2 ≤ p) : 0 ≤ tt p := by
  have h : 0 ≤ Real.cos (thet p) := by
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, thet_le p hp⟩
    have := thet_pos p hp
    have := Real.pi_pos
    linarith
  rw [tt]; linarith

theorem uu_ne_vv (p : ℕ) (hp : 2 ≤ p) : uu p ≠ vv p := by
  intro h
  have h1 := congrArg Complex.im h
  rw [uu, Complex.exp_ofReal_mul_I_im] at h1
  rw [vv, exp_neg_im] at h1
  have := sin_thet_pos p hp
  linarith

/-- The multiplier is `exp(2πi/p)`. -/
theorem uu_div_vv (p : ℕ) : uu p / vv p = Complex.exp (2 * (Real.pi : ℂ) * I / p) := by
  rw [uu, vv, ← Complex.exp_sub]
  congr 1
  rw [thet]
  push_cast
  ring

/-- and it is therefore a primitive `p`-th root of unity. -/
theorem isPrimitiveRoot_uu_div_vv (p : ℕ) (hp : p ≠ 0) :
    IsPrimitiveRoot (uu p / vv p) p := by
  rw [uu_div_vv]
  exact Complex.isPrimitiveRoot_exp p hp

/-! ## 5. The orbit of `2i` has least period exactly `p` -/

/-- The initial point of the construction. -/
noncomputable def w0 : ℂ := 2 * I

@[simp] theorem w0_im : w0.im = 2 := by simp [w0]

theorem w0_ne_uu (p : ℕ) : w0 ≠ uu p := by
  intro h
  have h1 := congrArg Complex.im h
  rw [w0_im, uu, Complex.exp_ofReal_mul_I_im] at h1
  have := Real.sin_le_one (thet p)
  linarith

/-- **The period is exactly `p`.**  The orbit returns to its start precisely at the
multiples of `p` — an equivalence, so this pins the least period and not merely a bound. -/
theorem orb_eq_iff_dvd (p : ℕ) (hp : 2 ≤ p) (j : ℕ) :
    orb ((tt p : ℝ) : ℂ) w0 j = w0 ↔ p ∣ j := by
  have hvim : (vv p).im ≤ 0 := by
    rw [vv_im]
    have := sin_thet_pos p hp
    linarith
  rw [orb_eq_iff (tt p) (uu p) (vv p) w0 (uu_add_vv p) (uu_mul_vv p) hvim (by simp)
    (uu_ne_vv p hp) (w0_ne_uu p) j]
  exact (isPrimitiveRoot_uu_div_vv p (by omega)).pow_eq_one_iff_dvd j

theorem orb_periodic (p : ℕ) (hp : 2 ≤ p) (j : ℕ) :
    orb ((tt p : ℝ) : ℂ) w0 (j + p) = orb ((tt p : ℝ) : ℂ) w0 j := by
  rw [orb_add]
  rw [(orb_eq_iff_dvd p hp p).mpr dvd_rfl]

/-! ## 6. The solution of the delay recurrence -/

noncomputable def s : ℂ := 1 + I

noncomputable def al : ℂ := s ^ 2

noncomputable def be : ℂ := s

noncomputable def ga (p : ℕ) : ℂ := s * (1 + ((tt p : ℝ) : ℂ))

/-- The solution: `z_n = s · w_n`. -/
noncomputable def Z (p : ℕ) (n : ℕ) : ℂ := s * orb ((tt p : ℝ) : ℂ) w0 n

theorem s_ne_zero : s ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [s] at this

theorem al_eq : al = 2 * I := by
  rw [al, s]
  linear_combination Complex.I_sq

theorem al_im : al.im = 2 := by rw [al_eq]; simp

theorem be_im : be.im = 1 := by simp [be, s]

theorem ga_im (p : ℕ) : (ga p).im = 1 + tt p := by
  simp [ga, s]

/-- The denominator never vanishes: the solution is everywhere defined.  Note this needs no
lower bound on `p` at all — it follows from `Im w_n > 0` and `t` being real, whatever `t` is. -/
theorem ga_sub_Z_ne_zero (p : ℕ) (n : ℕ) : ga p - Z p n ≠ 0 := by
  have him : 0 < (orb ((tt p : ℝ) : ℂ) w0 n).im := orb_im_pos (tt p) w0 (by simp) n
  have hfac : ga p - Z p n = s * (1 + ((tt p : ℝ) : ℂ) - orb ((tt p : ℝ) : ℂ) w0 n) := by
    rw [ga, Z]; ring
  rw [hfac]
  refine mul_ne_zero s_ne_zero ?_
  intro h
  have h1 := congrArg Complex.im h
  simp at h1
  linarith

/-- **The recurrence holds**, with delay `k = p − 1`. -/
theorem Z_rec (p : ℕ) (hp : 2 ≤ p) (n : ℕ) (hn : p - 1 ≤ n) :
    Z p (n + 1) = (al + be * Z p (n - (p - 1))) / (ga p - Z p n) := by
  set t : ℂ := ((tt p : ℝ) : ℂ) with ht
  set wn := orb t w0 n with hwn
  set wn1 := orb t w0 (n + 1) with hwn1
  -- the delayed entry is the NEXT one, because `(n − k) + p = n + 1`
  have hidx : n - (p - 1) + p = n + 1 := by omega
  have hdelay : orb t w0 (n - (p - 1)) = wn1 := by
    rw [hwn1, ← hidx, ht]
    exact (orb_periodic p hp (n - (p - 1))).symm
  have hstep : wn1 * (t - wn) = 1 := by
    rw [hwn1, hwn, ht]; exact orb_step_mul (tt p) w0 (by simp) n
  have hden : 1 + t - wn ≠ 0 := by
    have him : 0 < wn.im := by rw [hwn, ht]; exact orb_im_pos (tt p) w0 (by simp) n
    intro h
    have h1 := congrArg Complex.im h
    simp [ht] at h1
    linarith
  rw [Z, Z, Z, hdelay, al, be]
  have hd : ga p - s * wn = s * (1 + t - wn) := by rw [ga, ht]; ring
  rw [hd, eq_div_iff (mul_ne_zero s_ne_zero hden)]
  linear_combination (s ^ 2) * hstep

/-! ## 7. Hassan's Conjecture 3.1 -/

/-- Conjecture 3.1 of the source: arbitrarily high least periods occur in the family.  We
state the stronger form actually proved — every `p ≥ 2` occurs as a least period, with the
parameters nonzero and nonreal and the solution everywhere defined. -/
def Conjecture31 : Prop :=
  ∀ p : ℕ, 2 ≤ p → ∃ (a b c : ℂ) (k : ℕ) (z : ℕ → ℂ),
    a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a.im ≠ 0 ∧ b.im ≠ 0 ∧ c.im ≠ 0 ∧
    (∀ n, c - z n ≠ 0) ∧
    (∀ n, k ≤ n → z (n + 1) = (a + b * z (n - k)) / (c - z n)) ∧
    (∀ j, z (j + p) = z j) ∧
    (∀ q, 0 < q → q < p → ¬ ∀ j, z (j + q) = z j)

theorem conjecture31 : Conjecture31 := by
  intro p hp
  refine ⟨al, be, ga p, p - 1, Z p, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 : al.im = 2 := al_im
    rw [h] at h1
    simp at h1
  · intro h
    have h1 : be.im = 1 := be_im
    rw [h] at h1
    simp at h1
  · intro h
    have h1 : (ga p).im = 1 + tt p := ga_im p
    rw [h] at h1
    simp at h1
    have h2 := tt_nonneg p hp
    linarith
  · rw [al_im]; norm_num
  · rw [be_im]; norm_num
  · rw [ga_im p]
    have := tt_nonneg p hp
    intro h
    linarith
  · exact fun n => ga_sub_Z_ne_zero p n
  · exact fun n hn => Z_rec p hp n hn
  · intro j
    rw [Z, Z, orb_periodic p hp j]
  · intro q hq0 hqp hper
    have h := hper 0
    rw [Z, Z, zero_add] at h
    have hw : orb ((tt p : ℝ) : ℂ) w0 q = w0 := by
      have := mul_left_cancel₀ s_ne_zero h
      simpa using this
    have := (orb_eq_iff_dvd p hp q).mp hw
    have := Nat.le_of_dvd hq0 this
    omega

end Principia.MathDB.P333488
