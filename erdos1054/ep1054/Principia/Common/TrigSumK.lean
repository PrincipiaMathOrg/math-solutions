/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TrigSumElem

set_option autoImplicit false

/-!
# The three sums over sample points `kh` behind `lem:gotog`, `lem:couscous`, `lem:thina`

With `h = π/(2q)` the trigonometric-sum lemmas reduce (`TrigSums.lean`) to sums over the sample
points `θ = kh`, `k = 1, 2, …`. This file bounds them, each by a telescoping potential:

* `sum_min_csc_sq_le`: `∑_{k ≤ N} min(A, C csc²(kh)) ≤ 2√(AC)/h` when `Nh ≤ π/2`. Potential
  `Φ θ = A·min(θ, θ*) + C(cot θ* - cot max(θ, θ*))`, `sin²θ* = C/A`; the last step is
  `θ* + sin θ* cos θ* ≤ 2 sin θ*`.
* `sum_csc_sq_le`: `∑_{k ≤ M} csc²(kh) ≤ 5/(3h²)` when `h ≤ π/4`, `(M + 1/2)h ≤ π/2`. The
  midpoint step telescopes `k ≥ 2` to `cot(3h/2)/h`; then `h²csc²h + h cot(3h/2) ≤ 5/3`.
* `sum_min_csc_le`: `∑_{k ≤ N} min(B csc(kh), C csc²(kh)) ≤ (B/h)·max(2, log(Ce³/(2Bh)))`.
  Potential `B·L(min(θ, θ*)) + C(cot θ* - cot max(θ, θ*))`, `sin θ* = min(1, C/B)`,
  `L = log tan(·/2)`.
-/

namespace Principia.Common.TrigSum

open Real Finset

/-! ## 1. `min(A, C csc²)` -/

/-- The potential for `min(A, C csc²θ)`. -/
noncomputable def phiA (A C θs θ : ℝ) : ℝ := A * min θ θs + C * (ct θs - ct (max θ θs))

/-- `cot ≥ 0` on `(0, π/2]`. -/
theorem ct_nonneg {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ π / 2) : 0 ≤ ct θ := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])
  have hc : 0 ≤ cos θ := cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [pi_pos]) h1
  exact div_nonneg hc hs.le

/-- **One step of `Φ`**: `h·min(A, C csc²θ) ≤ Φ θ - Φ(θ - h)` for `0 < h ≤ θ ≤ π/2`. -/
theorem phiA_step (A C θs θ h : ℝ) (hC : 0 ≤ C) (hθs0 : 0 < θs)
    (hA : A = C / sin θs ^ 2) (hh : 0 < h) (hθ : θ ≤ π / 2) :
    h * min A (C / sin θ ^ 2) ≤ phiA A C θs θ - phiA A C θs (θ - h) := by
  have hm := min_le_left A (C / sin θ ^ 2)
  have hm' := min_le_right A (C / sin θ ^ 2)
  rcases le_or_gt θ θs with h1 | h1
  · unfold phiA
    rw [min_eq_left h1, min_eq_left (by linarith : θ - h ≤ θs), max_eq_right h1,
      max_eq_right (by linarith : θ - h ≤ θs)]
    nlinarith
  · rcases le_or_gt θs (θ - h) with h2 | h2
    · unfold phiA
      rw [min_eq_right h1.le, min_eq_right h2, max_eq_left h1.le, max_eq_left h2]
      have hst := csc_sq_step hh (by linarith) hθ
      have := mul_le_mul_of_nonneg_left hst hC
      have e : C * (h / sin θ ^ 2) = h * (C / sin θ ^ 2) := by ring
      nlinarith
    · unfold phiA
      rw [min_eq_right h1.le, min_eq_left h2.le, max_eq_left h1.le,
        max_eq_right h2.le]
      have hst := csc_sq_step (θ := θ) (h := θ - θs) (by linarith) (by linarith) hθ
      rw [show θ - (θ - θs) = θs by ring] at hst
      have hsθs : 0 < sin θs := sin_pos_of_pos_of_lt_pi hθs0 (by linarith [pi_pos])
      have hle : sin θs ≤ sin θ :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hθ h1.le
      have hAge : C / sin θ ^ 2 ≤ A := by
        rw [hA]
        exact div_le_div_of_nonneg_left hC (by positivity)
          (pow_le_pow_left₀ hsθs.le hle 2)
      have e1 : C * ((θ - θs) / sin θ ^ 2) = (θ - θs) * (C / sin θ ^ 2) := by ring
      have k1 := mul_le_mul_of_nonneg_left hst hC
      have k2 := mul_le_mul_of_nonneg_left hAge (by linarith : (0 : ℝ) ≤ θs - (θ - h))
      nlinarith

/-- **`Φ` telescopes**: `∑_{k < N} h·min(A, C csc²((k+1)h)) ≤ Φ(Nh) - Φ(0)`. -/
theorem phiA_sum (A C θs h : ℝ) (hC : 0 ≤ C) (hθs0 : 0 < θs)
    (hA : A = C / sin θs ^ 2) (hh : 0 < h) (N : ℕ) (hN : N * h ≤ π / 2) :
    ∑ k ∈ range N, h * min A (C / sin ((k + 1) * h) ^ 2) ≤
      phiA A C θs (N * h) - phiA A C θs 0 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast at hN ⊢
    have hn : (n : ℝ) * h ≤ π / 2 := by nlinarith
    have step := phiA_step A C θs ((n + 1) * h) h hC hθs0 hA hh hN
    rw [show (n + 1 : ℝ) * h - h = n * h by ring] at step
    linarith [ih hn]

/-- **`∑_{k < N} min(A, C csc²((k+1)h)) ≤ 2√(AC)/h`** for `Nh ≤ π/2`. -/
theorem sum_min_csc_sq_le (A C h : ℝ) (N : ℕ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hh : 0 < h)
    (hN : N * h ≤ π / 2) :
    ∑ k ∈ range N, min A (C / sin ((k + 1) * h) ^ 2) ≤ 2 * √(A * C) / h := by
  have hR : 0 ≤ 2 * √(A * C) / h := by positivity
  rcases hC.lt_or_eq with hC0 | hC0
  · rcases le_or_gt A C with hAC | hAC
    · -- every term is at most `A`
      have hs : ∑ k ∈ range N, min A (C / sin ((k + 1) * h) ^ 2) ≤ N * A := by
        calc ∑ k ∈ range N, min A (C / sin ((k + 1) * h) ^ 2) ≤ ∑ _k ∈ range N, A :=
              sum_le_sum fun k _ => min_le_left _ _
          _ = N * A := by rw [sum_const, card_range, nsmul_eq_mul]
      refine hs.trans ?_
      rw [le_div_iff₀ hh]
      have hsq : A ≤ √(A * C) := Real.le_sqrt_of_sq_le (by nlinarith)
      have h4 := pi_le_four
      nlinarith
    · -- `0 < C < A`: the potential
      have hA0 : 0 < A := lt_trans hC0 hAC
      set x := √(C / A) with hx
      have hx0 : 0 < x := Real.sqrt_pos.mpr (div_pos hC0 hA0)
      have hx2 : x ^ 2 = C / A := Real.sq_sqrt (div_pos hC0 hA0).le
      have hx1 : x ≤ 1 := by
        rw [hx, Real.sqrt_le_one]
        exact (div_le_one hA0).mpr hAC.le
      set θs := arcsin x with hθs
      have hsin : sin θs = x := sin_arcsin (by linarith) hx1
      have hθs0 : 0 < θs := arcsin_pos.mpr hx0
      have hθs1 : θs ≤ π / 2 := arcsin_le_pi_div_two x
      have hcos : 0 ≤ cos θs := cos_arcsin_nonneg x
      have hAeq : A = C / sin θs ^ 2 := by
        rw [hsin, hx2]; field_simp
      have hsum := phiA_sum A C θs h hC hθs0 hAeq hh N hN
      have hphi0 : phiA A C θs 0 = 0 := by
        unfold phiA; rw [min_eq_left hθs0.le, max_eq_right hθs0.le]; ring
      have hphiN : phiA A C θs (N * h) ≤ A * θs + C * ct θs := by
        unfold phiA
        have h1 : min (N * h) θs ≤ θs := min_le_right _ _
        have h2 : 0 ≤ ct (max (N * h) θs) :=
          ct_nonneg (lt_of_lt_of_le hθs0 (le_max_right _ _)) (max_le hN hθs1)
        nlinarith
      have hfin : A * θs + C * ct θs ≤ 2 * √(A * C) := by
        have hC' : C = A * sin θs ^ 2 := by rw [hsin, hx2]; field_simp
        have hsne : sin θs ≠ 0 := by rw [hsin]; exact hx0.ne'
        have e : A * θs + C * ct θs = A * (θs + sin θs * cos θs) := by
          unfold ct; rw [hC']; field_simp
        rw [e]
        have hk := theta_add_sin_mul_cos_le hθs0.le hθs1
        have hAx : A * x = √(A * C) := by
          have e1 : A * C = A ^ 2 * (C / A) := by field_simp
          rw [hx, e1, Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA0.le]
        rw [← hAx, ← hsin]
        nlinarith
      rw [← mul_sum, hphi0, sub_zero] at hsum
      rw [le_div_iff₀ hh]
      nlinarith
  · -- `C = 0`
    subst hC0
    have : ∑ k ∈ range N, min A (0 / sin ((k + 1) * h) ^ 2) = 0 := by
      refine sum_eq_zero fun k _ => ?_
      rw [zero_div, min_eq_right hA]
    rw [this]
    exact hR

/-! ## 2. `csc²` -/

/-- **The midpoint steps telescope**: `∑_{k < P} h csc²((k+2)h) ≤ cot(3h/2) - cot((P+3/2)h)`. -/
theorem mid_tele (h : ℝ) (hh : 0 < h) (hh2 : h ≤ π / 2) (P : ℕ) (hP : (P + 3 / 2) * h < π) :
    ∑ k ∈ range P, h / sin ((k + 2) * h) ^ 2 ≤ ct (3 / 2 * h) - ct ((P + 3 / 2) * h) := by
  induction P with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ]
    push_cast at hP ⊢
    have hn : ((n : ℝ) + 3 / 2) * h < π := by nlinarith
    have hm := csc_sq_mid (m := (n + 2) * h) (h := h) hh hh2 (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith) (by nlinarith)
    rw [show ((n : ℝ) + 2) * h - h / 2 = (n + 3 / 2) * h by ring,
      show ((n : ℝ) + 2) * h + h / 2 = (n + 1 + 3 / 2) * h by ring] at hm
    linarith [ih hn]

/-- **`∑_{k < M} csc²((k+1)h) ≤ 5/(3h²)`** for `0 < h ≤ π/4`, `(M + 1/2)h ≤ π/2`. -/
theorem sum_csc_sq_le (h : ℝ) (M : ℕ) (hh : 0 < h) (hh4 : h ≤ π / 4)
    (hM : (M + 1 / 2) * h ≤ π / 2) :
    ∑ k ∈ range M, 1 / sin ((k + 1) * h) ^ 2 ≤ 5 / (3 * h ^ 2) := by
  rcases M with _ | P
  · simp only [range_zero, sum_empty]; positivity
  · rw [sum_range_succ']
    push_cast at hM ⊢
    have ht := mid_tele h hh (by linarith [pi_pos]) P (by nlinarith [pi_pos])
    have hct : 0 ≤ ct ((P + 3 / 2) * h) :=
      ct_nonneg (by positivity) (by nlinarith)
    have e : ∑ k ∈ range P, h / sin ((k + 2) * h) ^ 2 =
        h * ∑ k ∈ range P, 1 / sin ((k + 1 + 1) * h) ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [show (k : ℝ) + 1 + 1 = k + 2 by ring]
      ring
    rw [e] at ht
    have hS : ∑ k ∈ range P, 1 / sin ((k + 1 + 1) * h) ^ 2 ≤ ct (3 / 2 * h) / h := by
      rw [le_div_iff₀ hh]; linarith
    have hk := csc_sq_add_cot_le hh hh4
    rw [zero_add, one_mul]
    have e2 : 5 / (3 * h ^ 2) = (5 / 3) / h ^ 2 := by ring
    have e3 : 1 / sin h ^ 2 + ct (3 / 2 * h) / h =
        (h ^ 2 / sin h ^ 2 + h * ct (3 / 2 * h)) / h ^ 2 := by
      field_simp
    have hfin : 1 / sin h ^ 2 + ct (3 / 2 * h) / h ≤ 5 / (3 * h ^ 2) := by
      rw [e3, e2]
      exact div_le_div_of_nonneg_right hk (by positivity)
    linarith

/-! ## 3. `min(B csc, C csc²)` -/

/-- The potential for `min(B cscθ, C csc²θ)`. -/
noncomputable def phiB (B C θs θ : ℝ) : ℝ := B * lg (min θ θs) + C * (ct θs - ct (max θ θs))

/-- **One step of the `B`-potential** for `0 < h < θ ≤ π/2`. -/
theorem phiB_step (B C θs θ h : ℝ) (hB : 0 < B) (hC : 0 < C) (hθs0 : 0 < θs)
    (hθs1 : θs ≤ π / 2) (hsθs : sin θs = min 1 (C / B)) (hh : 0 < h) (hθh : h < θ)
    (hθ : θ ≤ π / 2) :
    h * min (B / sin θ) (C / sin θ ^ 2) ≤ phiB B C θs θ - phiB B C θs (θ - h) := by
  have hm := min_le_left (B / sin θ) (C / sin θ ^ 2)
  have hm' := min_le_right (B / sin θ) (C / sin θ ^ 2)
  rcases le_or_gt θ θs with h1 | h1
  · unfold phiB
    rw [min_eq_left h1, min_eq_left (by linarith : θ - h ≤ θs), max_eq_right h1,
      max_eq_right (by linarith : θ - h ≤ θs)]
    have hst := lg_step (a := θ - h) (b := θ) (by linarith) (by linarith) hθ
    rw [show θ - (θ - h) = h by ring] at hst
    have k := mul_le_mul_of_nonneg_left hst hB.le
    have e : B * (h / sin θ) = h * (B / sin θ) := by ring
    nlinarith
  · rcases le_or_gt θs (θ - h) with h2 | h2
    · unfold phiB
      rw [min_eq_right h1.le, min_eq_right h2, max_eq_left h1.le, max_eq_left h2]
      have hst := csc_sq_step hh hθh hθ
      have k := mul_le_mul_of_nonneg_left hst hC.le
      have e : C * (h / sin θ ^ 2) = h * (C / sin θ ^ 2) := by ring
      nlinarith
    · unfold phiB
      rw [min_eq_right h1.le, min_eq_left h2.le, max_eq_left h1.le,
        max_eq_right h2.le]
      have hsp : 0 < sin θs := sin_pos_of_pos_of_lt_pi hθs0 (by linarith [pi_pos])
      have hlt : sin θs < sin θ :=
        sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [pi_pos]) hθ h1
      have hsθ : 0 < sin θ := lt_trans hsp hlt
      have hs1 : sin θ ≤ 1 := sin_le_one θ
      have hlm : sin θs = C / B := by
        rw [hsθs]
        rcases le_total 1 (C / B) with h3 | h3
        · rw [min_eq_left h3] at hsθs; linarith
        · exact min_eq_right h3
      have hkey : C / sin θ ^ 2 ≤ B / sin θs := by
        rw [hlm, div_le_div_iff₀ (by positivity) (div_pos hC hB)]
        have : (C / B) ^ 2 ≤ sin θ ^ 2 := by
          rw [← hlm]; exact pow_le_pow_left₀ hsp.le hlt.le 2
        have e : C * (C / B) = B * (C / B) ^ 2 := by field_simp
        nlinarith
      have hst1 := lg_step (a := θ - h) (b := θs) (by linarith) h2 hθs1
      have hst2 := csc_sq_step (θ := θ) (h := θ - θs) (by linarith) (by linarith) hθ
      rw [show θ - (θ - θs) = θs by ring] at hst2
      have k1 := mul_le_mul_of_nonneg_left hst1 hB.le
      have k2 := mul_le_mul_of_nonneg_left hst2 hC.le
      have k3 := mul_le_mul_of_nonneg_left hkey (by linarith : (0 : ℝ) ≤ θs - (θ - h))
      have e1 : B * ((θs - (θ - h)) / sin θs) = (θs - (θ - h)) * (B / sin θs) := by ring
      have e2 : C * ((θ - θs) / sin θ ^ 2) = (θ - θs) * (C / sin θ ^ 2) := by ring
      nlinarith

/-- **The `B`-potential telescopes** from `h`: `∑_{k < P} h·H((k+2)h) ≤ Φ((P+1)h) - Φ(h)`. -/
theorem phiB_sum (B C θs h : ℝ) (hB : 0 < B) (hC : 0 < C) (hθs0 : 0 < θs)
    (hθs1 : θs ≤ π / 2) (hsθs : sin θs = min 1 (C / B)) (hh : 0 < h) (P : ℕ)
    (hP : (P + 1) * h ≤ π / 2) :
    ∑ k ∈ range P, h * min (B / sin ((k + 2) * h)) (C / sin ((k + 2) * h) ^ 2) ≤
      phiB B C θs ((P + 1) * h) - phiB B C θs h := by
  induction P with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ]
    push_cast at hP ⊢
    have hn : ((n : ℝ) + 1) * h ≤ π / 2 := by nlinarith
    have step := phiB_step B C θs ((n + 2) * h) h hB hC hθs0 hθs1 hsθs hh (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith) (by nlinarith)
    rw [show ((n : ℝ) + 2) * h - h = (n + 1) * h by ring] at step
    rw [show ((n : ℝ) + 1 + 1) * h = (n + 2) * h by ring]
    linarith [ih hn]

/-- **`∑_{k < N} min(B csc((k+1)h), C csc²((k+1)h)) ≤ (B/h)·max(2, log(Ce³/(2Bh)))`** for
`0 < h ≤ π/4`, `(N + 1/2)h ≤ π/2`. -/
theorem sum_min_csc_le (B C h : ℝ) (N : ℕ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hh : 0 < h)
    (hh4 : h ≤ π / 4) (hN : (N + 1 / 2) * h ≤ π / 2) :
    ∑ k ∈ range N, min (B / sin ((k + 1) * h)) (C / sin ((k + 1) * h) ^ 2) ≤
      B / h * max 2 (log (C * exp 3 / (2 * B * h))) := by
  have hmax : 2 ≤ max 2 (log (C * exp 3 / (2 * B * h))) := le_max_left _ _
  have hR : 0 ≤ B / h * max 2 (log (C * exp 3 / (2 * B * h))) :=
    mul_nonneg (div_nonneg hB hh.le) (by linarith)
  have hspos : ∀ k : ℕ, k < N → 0 < sin ((k + 1) * h) := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
    exact sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])
  rcases hB.lt_or_eq with hB0 | hB0
  · rcases hC.lt_or_eq with hC0 | hC0
    · rcases le_or_gt C (B * sin h) with hsm | hbig
      · -- `C ≤ B sin h`: every term is at most `C csc²`
        have hS := sum_csc_sq_le h N hh hh4 hN
        have h1 : ∑ k ∈ range N, min (B / sin ((k + 1) * h)) (C / sin ((k + 1) * h) ^ 2) ≤
            C * ∑ k ∈ range N, 1 / sin ((k + 1) * h) ^ 2 := by
          rw [mul_sum]
          exact sum_le_sum fun k _ => (min_le_right _ _).trans (le_of_eq (by ring))
        have hsh : sin h ≤ h := sin_le hh.le
        have h2 : C * ∑ k ∈ range N, 1 / sin ((k + 1) * h) ^ 2 ≤ C * (5 / (3 * h ^ 2)) :=
          mul_le_mul_of_nonneg_left hS hC
        have h3 : C * (5 / (3 * h ^ 2)) ≤ 2 * (B / h) := by
          have hCB : C ≤ B * h := hsm.trans (mul_le_mul_of_nonneg_left hsh hB)
          rw [show C * (5 / (3 * h ^ 2)) = 5 * C / (3 * h ^ 2) by ring,
            div_le_iff₀ (by positivity)]
          have e : 2 * (B / h) * (3 * h ^ 2) = 6 * B * h := by field_simp; norm_num
          rw [e]; nlinarith
        have h4 : 2 * (B / h) ≤ B / h * max 2 (log (C * exp 3 / (2 * B * h))) := by
          rw [mul_comm 2]; exact mul_le_mul_of_nonneg_left hmax (div_nonneg hB hh.le)
        linarith
      · -- `C > B sin h`: the potential
        set lam := C / B with hlam
        have hlam0 : 0 < lam := div_pos hC0 hB0
        have hsh1 : sin h < 1 := by
          have := sin_lt_sin_of_lt_of_le_pi_div_two (x := h) (y := π / 2)
            (by linarith [pi_pos]) le_rfl (by linarith [pi_pos])
          rwa [sin_pi_div_two] at this
        have hshl : sin h < lam := by rw [hlam, lt_div_iff₀ hB0]; linarith
        set θs := arcsin (min 1 lam) with hθs
        have hm0 : 0 < min 1 lam := lt_min one_pos hlam0
        have hsθs : sin θs = min 1 lam := sin_arcsin (by linarith) (min_le_left _ _)
        have hθs0 : 0 < θs := arcsin_pos.mpr hm0
        have hθs1 : θs ≤ π / 2 := arcsin_le_pi_div_two _
        have hhθs : h < θs := by
          by_contra hc'
          have hc : θs ≤ h := not_lt.mp hc'
          have := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos])
            (by linarith [pi_pos]) hc
          rw [hsθs] at this
          have : sin h < min 1 lam := lt_min hsh1 hshl
          linarith
        rcases N with _ | P
        · simp only [range_zero, sum_empty]; exact hR
        · rw [sum_range_succ']
          push_cast at hN ⊢
          have hP : ((P : ℝ) + 1) * h ≤ π / 2 := by nlinarith
          have hsum := phiB_sum B C θs h hB0 hC0 hθs0 hθs1 hsθs hh P hP
          rw [← mul_sum] at hsum
          have hphih : phiB B C θs h = B * lg h := by
            unfold phiB; rw [min_eq_left hhθs.le, max_eq_right hhθs.le]; ring
          have hphiP : phiB B C θs ((P + 1) * h) ≤ B * lg θs + C * ct θs := by
            unfold phiB
            have h1 : lg (min ((P + 1) * h) θs) ≤ lg θs :=
              lg_mono (lt_min (by positivity) hθs0) (min_le_right _ _) hθs1
            have h2 : 0 ≤ ct (max ((P + 1) * h) θs) :=
              ct_nonneg (lt_of_lt_of_le hθs0 (le_max_right _ _)) (max_le hP hθs1)
            nlinarith
          -- `L(θ*) + λ cot θ* ≤ log λ + 1 - log 2`
          have hcot : lg θs + lam * ct θs ≤ log lam + (1 - log 2) := by
            have hl2 : 0 < 1 - log 2 := by linarith [log_two_lt_d9]
            have hcs : 0 ≤ cos θs := cos_nonneg_of_neg_pi_div_two_le_of_le
              (by linarith [pi_pos]) hθs1
            have hpy := sin_sq_add_cos_sq θs
            rcases le_total 1 lam with h1 | h1
            · rw [min_eq_left h1] at hsθs
              have hc0 : cos θs = 0 := by
                rw [hsθs] at hpy; nlinarith
              have hl : lg θs = 0 := by unfold lg; rw [hsθs, hc0]; simp
              have hct : ct θs = 0 := by unfold ct; rw [hc0, zero_div]
              rw [hl, hct, mul_zero, add_zero]
              have := log_nonneg h1
              linarith
            · rw [min_eq_right h1] at hsθs
              have hc1 : cos θs ≤ 1 := cos_le_one θs
              have hl : lg θs = log lam - log (1 + cos θs) := by unfold lg; rw [hsθs]
              have hct : lam * ct θs = cos θs := by
                unfold ct; rw [hsθs]; field_simp
              rw [hl, hct]
              have := sub_log_one_add_le hcs hc1
              linarith
          have hnl := neg_lg_le hh (by linarith [pi_pos])
          have hds := div_sin_le hh hh4
          have hsp : 0 < sin h := sin_pos_of_pos_of_lt_pi hh (by linarith [pi_pos])
          -- the first term
          have hfirst : min (B / sin ((0 + 1) * h)) (C / sin ((0 + 1) * h) ^ 2) ≤
              B / h * 1.115 := by
            rw [zero_add, one_mul]
            refine (min_le_left _ _).trans ?_
            rw [div_le_iff₀ hsp]
            have : h ≤ 1.115 * sin h := by rw [div_le_iff₀ hsp] at hds; linarith
            have e : B / h * 1.115 * sin h = B / h * (1.115 * sin h) := by ring
            rw [e]
            calc B = B / h * h := by field_simp
              _ ≤ B / h * (1.115 * sin h) := mul_le_mul_of_nonneg_left this (by positivity)
          -- the rest
          have hrest : ∑ k ∈ range P, min (B / sin ((k + 1 + 1) * h))
              (C / sin ((k + 1 + 1) * h) ^ 2) ≤
              B / h * (log lam + (1 - log 2) + log (2 / h)) := by
            have e : ∑ k ∈ range P, min (B / sin ((k + 1 + 1) * h))
                (C / sin ((k + 1 + 1) * h) ^ 2) =
                ∑ k ∈ range P, min (B / sin ((k + 2) * h)) (C / sin ((k + 2) * h) ^ 2) := by
              refine sum_congr rfl fun k _ => ?_
              rw [show (k : ℝ) + 1 + 1 = k + 2 by ring]
            rw [e]
            have hC' : C = B * lam := by rw [hlam]; field_simp
            have hcl : B * lg θs + C * ct θs ≤ B * (log lam + (1 - log 2)) := by
              rw [hC', mul_assoc, ← mul_add]
              exact mul_le_mul_of_nonneg_left hcot hB0.le
            have hlh : -(B * lg h) ≤ B * log (2 / h) := by
              rw [← mul_neg]; exact mul_le_mul_of_nonneg_left hnl hB0.le
            have key : h * ∑ k ∈ range P, min (B / sin ((k + 2) * h))
                (C / sin ((k + 2) * h) ^ 2) ≤ B * (log lam + (1 - log 2) + log (2 / h)) := by
              rw [hphih] at hsum; linarith
            rw [show B / h * (log lam + (1 - log 2) + log (2 / h)) =
              (B * (log lam + (1 - log 2) + log (2 / h))) / h by ring, le_div_iff₀ hh]
            linarith
          -- the target
          have hlog : log (C * exp 3 / (2 * B * h)) = log lam + 3 + log (2 / h) - log 4 := by
            have e : C * exp 3 / (2 * B * h) = lam * exp 3 * (2 / h) / 4 := by
              rw [hlam]; field_simp; ring
            rw [e, log_div (by positivity) (by norm_num), log_mul (by positivity) (by positivity),
              log_mul (by positivity) (by positivity), log_exp]
          have h4 : log 4 = 2 * log 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
          have hcmp : 1.115 + (log lam + (1 - log 2) + log (2 / h)) ≤
              log (C * exp 3 / (2 * B * h)) := by
            rw [hlog, h4]; linarith [log_two_lt_d9]
          have hfin : B / h * 1.115 + B / h * (log lam + (1 - log 2) + log (2 / h)) ≤
              B / h * max 2 (log (C * exp 3 / (2 * B * h))) := by
            rw [← mul_add]
            exact mul_le_mul_of_nonneg_left (hcmp.trans (le_max_right _ _))
              (div_nonneg hB hh.le)
          linarith
    · -- `C = 0`
      subst hC0
      refine (sum_nonpos fun k hk => ?_).trans hR
      rw [zero_div]; exact min_le_right _ _
  · -- `B = 0`
    subst hB0
    refine (sum_nonpos fun k hk => ?_).trans hR
    rw [zero_div]; exact min_le_left _ _

end Principia.Common.TrigSum
