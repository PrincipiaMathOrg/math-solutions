/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EsthelEta2K
import Principia.Common.TernaryGoldbach.Bosta2Main

set_option autoImplicit false

/-!
# `MPB2.EsthelEta2`, the `eq:kallervo2` branch PROVED -- so `EsthelEta2` is PROVED

Book `typeI.tex` 820-900 (Case (a) of `lem:bosta1`) with the `lem:bosta2` changes (1119-1141:
`eq:jenuf` doubled, the second line of `eq:sauna` halved, `eq:semin1` replaced by `eq:sosot`).

```
 EsthelEta2 ← EsthelEta2K  PROVED (EsthelEta2K.lean)
            ← EsthelEta2E  PROVED here (esthelEta2E_holds)
 esthelEta2_holds : EsthelEta2   PROVED
 bosta2Eta2_of_cited : MPc.Bosta2Eta2 from HC.CameloGridCited, HC.WollustCited alone
```

* `second_approx` -- the second approximation `a'/q'` (Dirichlet, `Real.exists_rat_abs_sub_le_
  and_den_le`, at `N = ⌊(1 + ε)Q⌋`): `(a', q') = 1`, `εQ ≤ (1 + ε)q'`, `q' ≤ (1 + ε)Q`; the
  book's `q' ≥ Q - q/(1 + ε)` argument, with `a'/q' ≠ a/q` forced by `N + 1 > Q`.
* `piece2E` -- `eq:jenuf`: `∑_{m ≤ M, q ∤ m} T ≤ (2√c₀/π)M + (35c₀c₂/3π²)q`.
* `piece3E` -- `eq:tenda` + `eq:beatri`: the `lem:gotog` windows of length `q'` from `Y = Q/2`.
* `esthelEta2E_holds` -- with the REAL `Q = x/|δ|q` throughout (so `M = mR = min(Q/2, D)` exactly,
  and `Q ≤ min(⌊Q⌋ + 1, 2D)` when `D > Q/2`); the book's integer `Q` is never needed.

No falsification: every constant of `eq:kallervo2` is reproduced (`35c₀c₂/3π² = 2·35c₀c₂/6π²`
from `q² ≤ 2c₂x`; `(3/2)c₁(2 + ((1 + ε)/ε)log⁺(2D/(x/|δ|q)))(x/Q₀)` from `x/Q ≤ x/Q₀`).
-/

namespace Principia.Common.TernaryGoldbach.MPE2

open Real Finset Principia.Common.TrigSumN
open Principia.Common.TernaryGoldbach.MPc Principia.Common.TernaryGoldbach.MPB2

/-! ## The second approximation `a'/q'` (Dirichlet) -/

/-- **The second approximation of `lem:bosta1`'s proof**: if `|α - a/q| = 1/(qQ)` exactly, with
`(a, q) = 1`, `q ≤ Q`, then for `ε > 0` there is `a'/q'`, `(a', q') = 1`, with
`α = a'/q' + β'/(q'Q')`, `|β'| ≤ 1`, `q' ≤ Q'`, and `εQ/(1 + ε) ≤ q' ≤ (1 + ε)Q` (written
multiplicatively). (Dirichlet at `N = ⌊(1 + ε)Q⌋`; `a'/q' ≠ a/q` because `N + 1 > Q`.) -/
theorem second_approx (α Q ε : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hαq : |α - a / q| = 1 / (q * Q)) (hqQ : (q : ℝ) ≤ Q) (hε : 0 < ε) :
    ∃ (a' : ℤ) (q' : ℕ) (β' Q' : ℝ), 1 ≤ q' ∧ Int.gcd a' q' = 1 ∧
      α = a' / q' + β' / (q' * Q') ∧ |β'| ≤ 1 ∧ (q' : ℝ) ≤ Q' ∧
      ε * Q ≤ (1 + ε) * q' ∧ (q' : ℝ) ≤ (1 + ε) * Q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ0 : 0 < Q := lt_of_lt_of_le hq0 hqQ
  set N := ⌊(1 + ε) * Q⌋₊ with hN_def
  have hN1 : 1 ≤ N := by
    rw [hN_def, Nat.one_le_floor_iff]
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  have hNr : (N : ℝ) ≤ (1 + ε) * Q := Nat.floor_le (by positivity)
  have hNr2 : (1 + ε) * Q < N + 1 := Nat.lt_floor_add_one _
  obtain ⟨r, hr, hrd⟩ := Real.exists_rat_abs_sub_le_and_den_le α (by omega : 0 < N)
  have hd1 : 1 ≤ r.den := r.pos
  have hd0 : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hdN : (r.den : ℝ) ≤ N := by exact_mod_cast hrd
  have hcast : (r : ℝ) = r.num / r.den := Rat.cast_def r
  refine ⟨r.num, r.den, (α - r) * (r.den * (N + 1)), N + 1, hd1, ?_, ?_, ?_, by linarith, ?_,
    by linarith⟩
  · have := r.reduced
    rw [Int.gcd]
    simpa using this
  · rw [← hcast]
    field_simp
    ring
  · rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < r.den * (N + 1))]
    calc |α - r| * (r.den * (N + 1)) ≤ 1 / ((N + 1) * r.den) * (r.den * (N + 1)) :=
          mul_le_mul_of_nonneg_right hr (by positivity)
      _ = 1 := by field_simp
  · -- `a'/q' ≠ a/q`
    have hne : (a : ℤ) * r.den - r.num * q ≠ 0 := by
      intro h0
      have hdvd : (q : ℤ) ∣ a * r.den := ⟨r.num, by linarith⟩
      have hg : Int.gcd (q : ℤ) a = 1 := by rw [Int.gcd_comm]; exact hcop
      have hqd : (q : ℤ) ∣ (r.den : ℤ) := Int.dvd_of_dvd_mul_right_of_gcd_one hdvd hg
      have hqd' : q ≤ r.den := Nat.le_of_dvd r.pos (Int.natCast_dvd_natCast.mp hqd)
      have hqdr : (q : ℝ) ≤ r.den := by exact_mod_cast hqd'
      have heq : (a : ℝ) / q = r.num / r.den := by
        rw [div_eq_div_iff hq0.ne' hd0.ne']
        have : ((a * r.den : ℤ) : ℝ) = ((r.num * q : ℤ) : ℝ) := by
          exact_mod_cast (sub_eq_zero.mp h0)
        push_cast at this
        linarith
      rw [heq, ← hcast] at hαq
      have h1 : 1 / (q * Q) ≤ 1 / ((N + 1) * r.den) := hαq ▸ hr
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul] at h1
      have h2 : (N + 1) * (q : ℝ) ≤ (N + 1) * r.den :=
        mul_le_mul_of_nonneg_left hqdr (by positivity)
      have h3 : (N + 1) * (q : ℝ) ≤ q * Q := by linarith
      have h4 : (N : ℝ) + 1 ≤ Q := by
        rw [mul_comm] at h3
        exact le_of_mul_le_mul_left h3 hq0
      nlinarith
    have hge : (1 : ℝ) ≤ |(a : ℝ) * r.den - r.num * q| := by
      have : (1 : ℤ) ≤ |(a : ℤ) * r.den - r.num * q| := Int.one_le_abs hne
      exact_mod_cast this
    -- `1/(q q') ≤ |a/q - a'/q'| ≤ 1/(qQ) + 1/((N+1)q')`
    have htri : |(a : ℝ) / q - r.num / r.den| ≤ 1 / (q * Q) + 1 / ((N + 1) * r.den) := by
      have e : (a : ℝ) / q - r.num / r.den = -(α - a / q) + (α - r) := by rw [hcast]; ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, hαq]
      linarith
    have hlow : 1 / (q * r.den) ≤ |(a : ℝ) / q - r.num / r.den| := by
      have e : (a : ℝ) / q - r.num / r.den = ((a : ℝ) * r.den - r.num * q) / (q * r.den) := by
        field_simp
      rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * r.den)]
      exact div_le_div_of_nonneg_right hge (by positivity)
    have hk := hlow.trans htri
    -- multiply by `q q' Q (N+1)`
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity), one_mul] at hk
    -- `(q Q)((N+1)q') ≤ q q' ((N+1)q' + qQ)`, i.e. `Q(N+1) ≤ q'(N+1) + qQ`... divide by `q`
    have hk2 : Q * (N + 1) ≤ r.den * (N + 1) + q * Q := by
      have e1 : (q : ℝ) * Q * ((N + 1) * r.den) = q * r.den * (Q * (N + 1)) := by ring
      have e2 : ((1 : ℝ) * ((N + 1) * r.den) + q * Q * 1) * (q * r.den) =
          q * r.den * (r.den * (N + 1) + q * Q) := by ring
      rw [e1] at hk
      have hk' : q * r.den * (Q * (N + 1)) ≤ q * r.den * (r.den * (N + 1) + q * Q) := by
        linarith
      exact le_of_mul_le_mul_left hk' (by positivity)
    -- `εQ ≤ (1+ε)q'`: from `Q(N+1) ≤ q'(N+1) + qQ`, `q ≤ Q`, `(1+ε)Q < N+1`
    have hqQ2 : (q : ℝ) * Q ≤ Q * Q := mul_le_mul_of_nonneg_right hqQ hQ0.le
    nlinarith

/-! ## Piece 2E -- `eq:jenuf`, `m ≤ M`, `q ∤ m` (`lem:couscous`), doubled -/

/-- `∑_{j < J} (j + 1) = J(J + 1)/2`. -/
theorem sum_j1 (J : ℕ) : ∑ j ∈ range J, ((j : ℝ) + 1) = J * (J + 1) / 2 := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- **Piece 2E -- `eq:jenuf` for `lem:bosta2`**: for `0 ≤ M ≤ Q/2`, `qM ≤ c₂x`, `q² ≤ 2c₂x`,
`∑_{m ≤ M, q ∤ m} T(m) ≤ (2√c₀/π)M + (35c₀c₂/3π²)q`. -/
theorem piece2E (x α β Q M : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hx : 0 < x) (hM0 : 0 ≤ M)
    (hMQ : 2 * M ≤ Q) (hMc : q * M ≤ c2 * x) (hqq : (q : ℝ) ^ 2 ≤ 2 * c2 * x)
    (t : ℕ → ℝ) (ht : TB x α t) :
    ∑ d ∈ (Ioc 0 ⌊M⌋₊).filter (fun d => ¬ q ∣ d), t d ≤
      2 * √c0 / π * M + 35 * c0 * c2 / (3 * π ^ 2) * q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 := c0_pos
  have hc2 := c2_pos
  have hpi := Real.pi_pos
  set N := ⌊M⌋₊ with hN_def
  set J := (N - 0 + q - 1) / q with hJ_def
  obtain ⟨hJ1, hJ2⟩ := cdiv_spec (N - 0) q hq
  rw [← hJ_def] at hJ1 hJ2
  have hNJ : N ≤ 0 + J * q := by
    generalize J * q = P at hJ1 hJ2 ⊢
    omega
  have hNr : (N : ℝ) ≤ M := Nat.floor_le hM0
  rw [sum_filter_windows t _ 0 q J N hNJ]
  have hwin : ∀ j ∈ range J,
      ∑ d ∈ Ioc (0 + j * q) (0 + j * q + q), (if d ≤ N ∧ ¬ q ∣ d then t d else 0) ≤
        20 / (3 * π ^ 2) * (c0 * ((j : ℝ) + 1) * q / (2 * x)) * q ^ 2 := by
    intro j _
    rw [window_trunc]
    refine couscousN α β Q _ a q hq hcop hα hβ (by positivity) (0 + j * q)
      (min (0 + j * q + q) N) (by omega) ?_ t ?_
    · have : ((min (0 + j * q + q) N : ℕ) : ℝ) ≤ N := by exact_mod_cast min_le_right _ _
      linarith
    · intro d hd
      have hd' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1
      have hd1 : 1 ≤ d := by omega
      have hdle : d ≤ 0 + j * q + q := le_trans hd'.2 (min_le_left _ _)
      have hdr : (d : ℝ) ≤ ((j : ℝ) + 1) * q := by
        have : (d : ℝ) ≤ 0 + j * q + q := by exact_mod_cast hdle
        linarith
      refine (ht d hd1).2.2.2.trans ?_
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hx (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hdr) hc0.le) hx.le]
  refine (Finset.sum_le_sum hwin).trans ?_
  have e : ∑ j ∈ range J, 20 / (3 * π ^ 2) * (c0 * ((j : ℝ) + 1) * q / (2 * x)) * q ^ 2 =
      20 / (3 * π ^ 2) * (c0 * q ^ 3 / (2 * x)) * (J * (J + 1) / 2) := by
    rw [← sum_j1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [e]
  have hJq : (J : ℝ) * q ≤ M + q := by
    have h1 : J * q ≤ N - 0 + q - 1 := hJ2
    have h2 : J * q ≤ N + q := by
      generalize J * q = P at h1 ⊢
      omega
    have h3 : (J : ℝ) * q ≤ N + q := by exact_mod_cast h2
    linarith
  have hJr : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  -- `q³J(J+1) ≤ x(c₂M + 7c₂q)`
  have hkey : (q : ℝ) ^ 3 * (J * (J + 1)) ≤ x * (c2 * M + 7 * c2 * q) := by
    have hy0 : (0 : ℝ) ≤ J * q := by positivity
    have e1 : (q : ℝ) ^ 3 * (J * (J + 1)) = q * ((J * q) * (J * q + q)) := by ring
    have h1 : (q : ℝ) * ((J * q) * (J * q + q)) ≤ q * ((M + q) * (M + q + q)) := by
      refine mul_le_mul_of_nonneg_left ?_ hq0.le
      exact mul_le_mul hJq (by linarith) (by positivity) (by positivity)
    have h2 : M * (q * M) ≤ M * (c2 * x) := mul_le_mul_of_nonneg_left hMc hM0
    have h3 : 3 * q * (q * M) ≤ 3 * q * (c2 * x) :=
      mul_le_mul_of_nonneg_left hMc (by positivity)
    have h4 : 2 * q * (q : ℝ) ^ 2 ≤ 2 * q * (2 * c2 * x) :=
      mul_le_mul_of_nonneg_left hqq (by positivity)
    have e4 : (q : ℝ) * ((M + q) * (M + q + q)) =
        M * (q * M) + 3 * q * (q * M) + 2 * q * (q : ℝ) ^ 2 := by ring
    have e5 : x * (c2 * M + 7 * c2 * q) =
        M * (c2 * x) + 3 * q * (c2 * x) + 2 * q * (2 * c2 * x) := by ring
    rw [e1, e5]
    rw [e4] at h1
    linarith
  rw [← sosot]
  have e2 : 20 / (3 * π ^ 2) * (c0 * q ^ 3 / (2 * x)) * (J * (J + 1) / 2) =
      5 * c0 / (3 * π ^ 2) * ((q : ℝ) ^ 3 * (J * (J + 1)) / x) := by
    field_simp
    ring
  have e3 : 5 * c0 * c2 / (3 * π ^ 2) * M + 35 * c0 * c2 / (3 * π ^ 2) * q =
      5 * c0 / (3 * π ^ 2) * (c2 * M + 7 * c2 * q) := by
    field_simp
    ring
  rw [e2, e3]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [div_le_iff₀ hx]
  linarith

/-! ## Piece 3E -- `eq:tenda` + `eq:beatri`, `Y < m ≤ D` with the second approximation -/

/-- `√(AC)` at `j = 0` for windows of length `q'` from `Y`: `≤ (√(c₀c₁)/2)·√(3 + 2ε)` when
`q' ≤ 2(1 + ε)Y`. -/
theorem sqrt_w0e (x c1v Y ε : ℝ) (q : ℕ) (hx : 0 < x) (hc1 : 0 ≤ c1v) (hε0 : 0 ≤ ε)
    (hY : (q : ℝ) ≤ 2 * (1 + ε) * Y) (hY0 : 0 < Y) :
    √(c1v * x / (2 * ((0 : ℕ) * q + Y)) * (c0 * (((0 : ℕ) + 1) * q + Y) / (2 * x))) ≤
      √(c0 * c1v) / 2 * √(3 + 2 * ε) := by
  have hc0 := c0_pos
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hε : 0 ≤ 3 + 2 * ε := by linarith
  have hv : 0 ≤ √(c0 * c1v) / 2 * √(3 + 2 * ε) := by positivity
  rw [← Real.sqrt_sq hv]
  refine Real.sqrt_le_sqrt ?_
  have e : (√(c0 * c1v) / 2 * √(3 + 2 * ε)) ^ 2 = c0 * c1v / 4 * (3 + 2 * ε) := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hε]
    ring
  rw [e]
  push_cast
  rw [show c1v * x / (2 * (0 * q + Y)) * (c0 * ((0 + 1) * q + Y) / (2 * x)) =
    c0 * c1v / 4 * ((q + Y) / Y) by field_simp; ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [div_le_iff₀ hY0]
  linarith

/-- **Piece 3E -- `eq:tenda` + `eq:beatri` for `lem:bosta2`**: for windows of length `q'` from
`Y > 0` (`q'` the second approximation's denominator), with `2εY ≤ (1 + ε)q'` and
`q' ≤ 2(1 + ε)Y`, `∑_{Y < m ≤ D} T(m) ≤ (3c₁/2)(x/2Y)(2 + ((1 + ε)/ε)log⁺(D/Y))
+ (2√(c₀c₁)/π)((1 + ε)(2Y)√(3 + 2ε) + max(D - Y, 0) + ((1 + ε)(2Y)/2)log⁺(D/Y))`. -/
theorem piece3E (x α β Q D Y ε : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hqQ : (q : ℝ) ≤ Q) (hx : 0 < x)
    (hD : 1 ≤ D) (hY0 : 0 < Y) (hε : 0 < ε) (hqlo : ε * (2 * Y) ≤ (1 + ε) * q)
    (hqhi : (q : ℝ) ≤ 2 * (1 + ε) * Y) (t : ℕ → ℝ) (ht : TB x α t) :
    ∑ d ∈ Ioc ⌊Y⌋₊ ⌊D⌋₊, t d ≤
      3 / 2 * c1 x D * (x / (2 * Y)) * (2 + (1 + ε) / ε * logp (D / Y)) +
        2 * √(c0 * c1 x D) / π * ((1 + ε) * (2 * Y) * √(3 + 2 * ε) + max (D - Y) 0 +
          (1 + ε) * (2 * Y) / 2 * logp (D / Y)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 := c0_pos
  have hpi := Real.pi_pos
  have he := eta1_pos
  have hc1 : 1 ≤ c1 x D := by
    unfold c1
    have : 0 ≤ eta1 * D / x := by positivity
    linarith
  have hc1' : 0 ≤ c1 x D := by linarith
  have hlp : 0 ≤ logp (D / Y) := le_max_right _ _
  have hmx : 0 ≤ max (D - Y) 0 := le_max_right _ _
  have h3e : 0 ≤ √(3 + 2 * ε) := Real.sqrt_nonneg _
  have hRHS : 0 ≤ 3 / 2 * c1 x D * (x / (2 * Y)) * (2 + (1 + ε) / ε * logp (D / Y)) +
      2 * √(c0 * c1 x D) / π * ((1 + ε) * (2 * Y) * √(3 + 2 * ε) + max (D - Y) 0 +
        (1 + ε) * (2 * Y) / 2 * logp (D / Y)) := by
    positivity
  set r := ⌊Y⌋₊ with hr_def
  set N := ⌊D⌋₊ with hN_def
  set J := (N - r + q - 1) / q with hJ_def
  obtain ⟨hJ1, hJ2⟩ := cdiv_spec (N - r) q hq
  rw [← hJ_def] at hJ1 hJ2
  have hNJ : N ≤ r + J * q := by
    generalize J * q = P at hJ1 hJ2 ⊢
    omega
  have hfil : (Ioc r N).filter (fun _ => True) = Ioc r N :=
    Finset.filter_true_of_mem (fun _ _ => trivial)
  rw [← hfil, sum_filter_windows t (fun _ => True) r q J N hNJ]
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
  · rw [hJ0]
    simpa using hRHS
  obtain ⟨K, hK⟩ : ∃ K, J = K + 1 := ⟨J - 1, by omega⟩
  have hNr : r + 1 ≤ N := by
    by_contra hcon
    have : N - r = 0 := by omega
    rw [this] at hJ_def
    have : J = 0 := by
      rw [hJ_def, zero_add]
      exact Nat.div_eq_of_lt (by omega)
    omega
  have hKr : (K : ℝ) * q + Y ≤ D := by
    rw [hK] at hJ2
    have h1 : K * q + r + 1 ≤ N := by
      have e : (K + 1) * q = K * q + q := by ring
      rw [e] at hJ2
      generalize K * q = P at hJ2 ⊢
      omega
    have h2 : (K : ℝ) * q + r + 1 ≤ N := by exact_mod_cast h1
    have h3 : Y < r + 1 := Nat.lt_floor_add_one Y
    have h4 : (N : ℝ) ≤ D := Nat.floor_le (by linarith)
    linarith
  have hKr0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [hK, Finset.sum_range_succ']
  set s := √(c0 * c1 x D) with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hwin : ∀ j ∈ range K,
      ∑ d ∈ Ioc (r + (j + 1) * q) (r + (j + 1) * q + q), (if d ≤ N ∧ True then t d else 0) ≤
        (3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) * (1 / (((j : ℝ) + 1) * q + Y)) +
          2 * q / π * s := by
    intro j hj
    have hjK : j + 1 ≤ K := Finset.mem_range.mp hj
    have hjK' : ((j + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hjK
    have hjD : ((j + 1 : ℕ) : ℝ) * q + Y ≤ D := by
      have := mul_le_mul_of_nonneg_right hjK' hq0.le
      linarith
    have hg := gwin x α β Q D Y a q hq hcop hα hβ hqQ hx hY0 t ht (j + 1) hjD
    have hsq := sqrt_ws x (c1 x D) Y q j hx hc1' hq0 hY0
    have hjR : 0 < ((j : ℝ) + 1) * q + Y := by positivity
    refine hg.trans ?_
    have h4 : 4 * q / π * √(c1 x D * x / (2 * (((j + 1 : ℕ) : ℝ) * q + Y)) *
        (c0 * ((((j + 1 : ℕ) : ℝ) + 1) * q + Y) / (2 * x))) ≤
        4 * q / π * (s / 2 * (1 + q / (2 * ((j + 1) * q + Y)))) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have e : 3 * (c1 x D * x / (2 * (((j + 1 : ℕ) : ℝ) * q + Y))) +
        4 * q / π * (s / 2 * (1 + q / (2 * ((j + 1) * q + Y)))) =
        (3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) * (1 / (((j : ℝ) + 1) * q + Y)) +
          2 * q / π * s := by
      push_cast
      field_simp
      ring
    linarith
  have hw0 := gwin x α β Q D Y a q hq hcop hα hβ hqQ hx hY0 t ht 0
    (by have := mul_nonneg hKr0 hq0.le; push_cast; linarith)
  have hsq0 := sqrt_w0e x (c1 x D) Y ε q hx hc1' hε.le hqhi hY0
  have h40 := mul_le_mul_of_nonneg_left hsq0 (by positivity : (0 : ℝ) ≤ 4 * q / π)
  have hsum := Finset.sum_le_sum hwin
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  have hH := harm_le q Y hq0 hY0 K
  set H := ∑ j ∈ range K, 1 / (((j : ℝ) + 1) * q + Y) with hH_def
  set Lg := Real.log ((K * q + Y) / Y) with hLg_def
  have hLg0 : 0 ≤ Lg := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hY0]
    have := mul_nonneg hKr0 hq0.le
    linarith
  have hLg1 : Lg ≤ logp (D / Y) := by
    refine log_le_logp _ _ (by positivity) ?_
    exact div_le_div_of_nonneg_right hKr hY0.le
  have hcoef : 0 ≤ 3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2) := by positivity
  have hH2 := mul_le_mul_of_nonneg_left hH hcoef
  have hA0 : 3 * (c1 x D * x / (2 * (((0 : ℕ) : ℝ) * q + Y))) =
      3 / 2 * c1 x D * (x / (2 * Y)) * 2 := by
    push_cast
    rw [zero_mul, zero_add]
    field_simp
  have hKq : (K : ℝ) * q ≤ max (D - Y) 0 := le_trans (by linarith) (le_max_left _ _)
  -- `1/q ≤ (1+ε)/(ε·2Y)`
  have hinvq : 1 / (q : ℝ) ≤ (1 + ε) / ε * (1 / (2 * Y)) := by
    rw [div_mul_div_comm, mul_one, div_le_div_iff₀ hq0 (by positivity), one_mul]
    linarith
  have hfin : (3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) * (1 / q * Lg) + K * (2 * q / π * s)
      ≤ 3 / 2 * c1 x D * (x / (2 * Y)) * ((1 + ε) / ε * logp (D / Y)) +
        2 * s / π * (max (D - Y) 0 + (1 + ε) * (2 * Y) / 2 * logp (D / Y)) := by
    have e : (3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) * (1 / q * Lg) + K * (2 * q / π * s)
        = 3 / 2 * c1 x D * x * (1 / q) * Lg + 2 * s / π * (K * q + q / 2 * Lg) := by
      field_simp
      ring
    rw [e]
    have h1 : 3 / 2 * c1 x D * x * (1 / q) * Lg ≤
        3 / 2 * c1 x D * x * ((1 + ε) / ε * (1 / (2 * Y))) * logp (D / Y) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hinvq (by positivity)) hLg1 hLg0
        (by positivity)
    have e1 : 3 / 2 * c1 x D * x * ((1 + ε) / ε * (1 / (2 * Y))) * logp (D / Y) =
        3 / 2 * c1 x D * (x / (2 * Y)) * ((1 + ε) / ε * logp (D / Y)) := by
      field_simp
    have hq2 : (q : ℝ) / 2 ≤ (1 + ε) * (2 * Y) / 2 := by linarith
    have h2 : (K : ℝ) * q + q / 2 * Lg ≤ max (D - Y) 0 + (1 + ε) * (2 * Y) / 2 * logp (D / Y) :=
      add_le_add hKq (mul_le_mul hq2 hLg1 hLg0 (by positivity))
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * s / π)
    linarith
  have h3q : 4 * q / π * (s / 2 * √(3 + 2 * ε)) ≤
      2 * s / π * ((1 + ε) * (2 * Y) * √(3 + 2 * ε)) := by
    have e : 4 * q / π * (s / 2 * √(3 + 2 * ε)) = 2 * s / π * (q * √(3 + 2 * ε)) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) h3e)
      (by positivity)
  have e4 : 3 / 2 * c1 x D * (x / (2 * Y)) * (2 + (1 + ε) / ε * logp (D / Y)) +
      2 * s / π * ((1 + ε) * (2 * Y) * √(3 + 2 * ε) + max (D - Y) 0 +
        (1 + ε) * (2 * Y) / 2 * logp (D / Y)) =
      3 / 2 * c1 x D * (x / (2 * Y)) * 2 + 2 * s / π * ((1 + ε) * (2 * Y) * √(3 + 2 * ε)) +
      (3 / 2 * c1 x D * (x / (2 * Y)) * ((1 + ε) / ε * logp (D / Y)) +
        2 * s / π * (max (D - Y) 0 + (1 + ε) * (2 * Y) / 2 * logp (D / Y))) := by
    ring
  rw [e4]
  linarith

/-! ## The `eq:kallervo2` branch, PROVED -/

/-- **`EsthelEta2E`, PROVED** (book `typeI.tex` 820-900, Case (a), with the `lem:bosta2`
changes): `Q = x/|δ|q` (real), `M = mR = min(Q/2, D)`; `piece2E` on `m ≤ M`, `q ∤ m`; when
`D > Q/2`, `piece3E` on `Q/2 < m ≤ D` with the second approximation `a'/q'` of
`second_approx`; then `(2√c₀/π)(Q/2) + (2√(c₀c₁)/π)(D - Q/2) ≤ (2√(c₀c₁)/π)D` and
`Q ≤ min(⌊Q⌋ + 1, 2D)`. -/
theorem esthelEta2E_holds : EsthelEta2E := by
  intro x β δ Q0 D a q hq hg h2 hδ hqQ hQ hD1 hDx T hT hbig ε hε hε1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hx : 0 < x := by linarith
  have hc0 := c0_pos
  have hc2 := c2_pos
  have hpi := Real.pi_pos
  have he := eta1_pos
  have hd : 0 < |δ| := lt_of_lt_of_le (by positivity) hbig
  have h0 : δ ≠ 0 := abs_pos.mp hd
  obtain ⟨Qr, hQr_def⟩ : ∃ Qr : ℝ, Qr = x / (|δ| * q) := ⟨_, rfl⟩
  have hQr0 : 0 < Qr := by rw [hQr_def]; positivity
  -- `Q₀ ≤ Q`, `q ≤ Q`
  have hδ' : |δ| * q * Q0 ≤ x := by
    rw [abs_div, abs_of_pos hx, div_le_div_iff₀ hx (by positivity), one_mul] at hδ
    linarith
  have hQ0r : Q0 ≤ Qr := by
    rw [hQr_def, le_div_iff₀ (by positivity)]
    linarith
  have hqr : (q : ℝ) ≤ Qr := hqQ.trans hQ0r
  -- `q² ≤ 2c₂x` and `|δ| ≥ 1/2c₂` facts
  have hdc : 1 ≤ 2 * c2 * |δ| := by
    rw [div_le_iff₀ (by positivity)] at hbig
    linarith
  have hqq : (q : ℝ) ^ 2 ≤ 2 * c2 * x := by
    have h1 : (q : ℝ) * Q0 ≤ 2 * c2 * x := by
      have : (q : ℝ) * Q0 * 1 ≤ q * Q0 * (2 * c2 * |δ|) :=
        mul_le_mul_of_nonneg_left hdc (by positivity)
      nlinarith
    have h2 : (q : ℝ) ^ 2 ≤ q * Q0 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left hqQ hq0.le
    linarith
  -- the first approximation, exactly: `|2β - a/q| = 1/(qQ)`
  have hα1 : 2 * β = a / q + (δ / |δ|) / (q * Qr) := by
    rw [h2, hQr_def]
    congr 1
    field_simp
  have hθ : |(δ / |δ|)| ≤ 1 := by rw [abs_div, abs_abs, div_self hd.ne']
  have hαq : |2 * β - a / q| = 1 / (q * Qr) := by
    rw [h2, add_sub_cancel_left, hQr_def, abs_div, abs_of_pos hx]
    field_simp
  -- `mR = min(Q/2, D)`
  obtain ⟨Y, hY_def⟩ : ∃ Y : ℝ, Y = Qr / 2 := ⟨_, rfl⟩
  have hY0 : 0 < Y := by rw [hY_def]; exact half_pos hQr0
  have hmR : mR x δ q D = min Y D := by
    unfold mR
    rw [if_neg h0, hY_def, hQr_def]
    congr 1
    field_simp
  rw [hmR]
  set M := min Y D with hM_def
  have hM0 : 0 ≤ M := le_min hY0.le (by linarith)
  have hMY : M ≤ Y := min_le_left _ _
  have hMD : M ≤ D := min_le_right _ _
  have hMc : (q : ℝ) * M ≤ c2 * x := by
    have h1 : (q : ℝ) * M ≤ q * Y := mul_le_mul_of_nonneg_left hMY hq0.le
    have h2 : (q : ℝ) * Y = x / (2 * |δ|) := by
      rw [hY_def, hQr_def]
      field_simp
    have h3 : x / (2 * |δ|) ≤ c2 * x := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have htb := tb_of_tromB x β T hT
  have hp2 := piece2E x (2 * β) (δ / |δ|) Qr M a q hq hg hα1 hθ hx hM0 (by linarith) hMc hqq T
    htb
  have hT0 : ∀ d, 0 ≤ (if 1 ≤ d then T d else 0) := by
    intro d
    split_ifs with h
    · exact (htb d h).1
    · exact le_rfl
  have e0 : ∀ (S : Finset ℕ), (∀ d ∈ S, 1 ≤ d) →
      ∑ d ∈ S, (if 1 ≤ d then T d else 0) = ∑ d ∈ S, T d := by
    intro S hS
    exact Finset.sum_congr rfl fun d hd => if_pos (hS d hd)
  have hpos1 : ∀ d ∈ (Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ M)), 1 ≤ d := by
    intro d hd
    have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1
    omega
  set s := √(c0 * c1 x D) with hs_def
  have hc1 : 1 ≤ c1 x D := by
    unfold c1
    have : 0 ≤ eta1 * D / x := by positivity
    linarith
  have hs1 : √c0 ≤ s := Real.sqrt_le_sqrt (by nlinarith)
  have hs0 : 0 ≤ √c0 := Real.sqrt_nonneg _
  clear_value s
  have hs0' : 0 ≤ s := hs0.trans hs1
  have hlp : 0 ≤ logp (2 * D / (Qr)) := le_max_right _ _
  have h3e : 0 ≤ √(3 + 2 * ε) := Real.sqrt_nonneg _
  have hfl : 0 ≤ ((⌊Qr⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrest : 0 ≤ 2 * s / π * ((1 + ε) * min ((⌊Qr⌋₊ : ℝ) + 1) (2 * D) *
      (√(3 + 2 * ε) + logp (2 * D / (Qr)) / 2)) +
      3 / 2 * c1 x D * (2 + (1 + ε) / ε * logp (2 * D / (Qr))) * (x / Q0) := by
    have : 0 ≤ min ((⌊Qr⌋₊ : ℝ) + 1) (2 * D) := le_min (by positivity) (by linarith)
    have : 0 < Q0 := by linarith
    positivity
  have ekal : kallervo2 x δ q D Q0 ε = 2 * s / π * D +
      (2 * s / π * ((1 + ε) * min ((⌊Qr⌋₊ : ℝ) + 1) (2 * D) *
        (√(3 + 2 * ε) + logp (2 * D / (Qr)) / 2)) +
      3 / 2 * c1 x D * (2 + (1 + ε) / ε * logp (2 * D / (Qr))) * (x / Q0)) +
      35 * c0 * c2 / (3 * π ^ 2) * q := by
    unfold kallervo2
    rw [← hQr_def, ← hs_def]
    ring
  rw [ekal]
  rcases le_or_gt D Y with hDY | hDY
  · -- `D ≤ Q/2`: every term is `m ≤ M = D`, `q ∤ m`
    have hMeq : M = D := min_eq_right hDY
    have hsub : (Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ M)) ⊆
        (Ioc 0 ⌊M⌋₊).filter (fun d => ¬ q ∣ d) := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Ioc] at hd ⊢
      refine ⟨⟨hd.1.1, by rw [hMeq]; exact hd.1.2⟩, fun hqd => hd.2 ⟨hqd, ?_⟩⟩
      have : (d : ℝ) ≤ ⌊D⌋₊ := by exact_mod_cast hd.1.2
      rw [hMeq]
      linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ D)]
    have hS := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun d => if 1 ≤ d then T d else 0) (fun d _ _ => hT0 d)
    rw [e0 _ hpos1, e0 _ (fun d hd => by
      have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1
      omega)] at hS
    refine hS.trans (hp2.trans ?_)
    rw [hMeq]
    have : 2 * √c0 / π * D ≤ 2 * s / π * D := by
      refine mul_le_mul_of_nonneg_right ?_ (by linarith)
      exact div_le_div_of_nonneg_right (by linarith) hpi.le
    linarith
  · -- `D > Q/2`: `M = Q/2`, and the terms `Q/2 < m ≤ D` use `a'/q'`
    have hMeq : M = Y := min_eq_left hDY.le
    obtain ⟨a', q', β'', Q'', hq'1, hg', hα', hβ'', hq'Q, hlo, hhi⟩ :=
      second_approx (2 * β) Qr ε a q hq hg hαq hqr hε
    have hlo' : ε * (2 * Y) ≤ (1 + ε) * q' := by rw [hY_def]; linarith
    have hhi' : (q' : ℝ) ≤ 2 * (1 + ε) * Y := by rw [hY_def]; linarith
    have hp3 := piece3E x (2 * β) β'' Q'' D Y ε a' q' hq'1 hg' hα' hβ'' hq'Q hx hD1 hY0 hε
      hlo' hhi' T htb
    rw [← hs_def] at hp3
    have hcov : (Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ M)) ⊆
        (Ioc 0 ⌊M⌋₊).filter (fun d => ¬ q ∣ d) ∪ Ioc ⌊Y⌋₊ ⌊D⌋₊ := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Ioc] at hd
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioc]
      by_cases h1 : d ≤ ⌊M⌋₊
      · refine Or.inl ⟨⟨hd.1.1, h1⟩, fun hqd => hd.2 ⟨hqd, ?_⟩⟩
        have : (d : ℝ) ≤ ⌊M⌋₊ := by exact_mod_cast h1
        linarith [Nat.floor_le hM0]
      · refine Or.inr ⟨?_, hd.1.2⟩
        rw [← hMeq]
        omega
    have hS := Finset.sum_le_sum_of_subset_of_nonneg hcov
      (f := fun d => if 1 ≤ d then T d else 0) (fun d _ _ => hT0 d)
    rw [e0 _ hpos1] at hS
    refine hS.trans ((sum_union_le_nn _ _ _ hT0).trans ?_)
    rw [e0 _ (fun d hd => by
      have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1
      omega), e0 _ (fun d hd => by
      have := (Finset.mem_Ioc.mp hd).1
      omega)]
    refine (add_le_add hp2 hp3).trans ?_
    clear hS hcov hp2 hp3 e0 hpos1 hT0 htb hT hα' hα1 hαq h2
    rw [hMeq]
    -- the arithmetic
    have hDYm : max (D - Y) 0 = D - Y := max_eq_left (by linarith)
    rw [hDYm]
    have hlogeq : logp (D / Y) = logp (2 * D / (Qr)) := by
      congr 1
      rw [hY_def]
      field_simp
    rw [hlogeq]
    have hxY : x / (2 * Y) ≤ x / Q0 := by
      refine div_le_div_of_nonneg_left hx.le (by linarith) ?_
      rw [hY_def]
      linarith
    have hmin : 2 * Y ≤ min ((⌊Qr⌋₊ : ℝ) + 1) (2 * D) := by
      refine le_min ?_ (by linarith)
      rw [hY_def]
      have := Nat.lt_floor_add_one Qr
      linarith
    have hk1 : 0 ≤ 2 + (1 + ε) / ε * logp (2 * D / (Qr)) := by positivity
    have hA : 3 / 2 * c1 x D * (x / (2 * Y)) * (2 + (1 + ε) / ε * logp (2 * D / (Qr)))
        ≤ 3 / 2 * c1 x D * (2 + (1 + ε) / ε * logp (2 * D / (Qr))) * (x / Q0) := by
      have e : 3 / 2 * c1 x D * (x / (2 * Y)) *
          (2 + (1 + ε) / ε * logp (2 * D / (Qr))) =
          3 / 2 * c1 x D * (2 + (1 + ε) / ε * logp (2 * D / (Qr))) *
            (x / (2 * Y)) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hxY (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hk1)
    have hB : (1 + ε) * (2 * Y) * √(3 + 2 * ε) +
        (1 + ε) * (2 * Y) / 2 * logp (2 * D / (Qr)) ≤
        (1 + ε) * min ((⌊Qr⌋₊ : ℝ) + 1) (2 * D) *
          (√(3 + 2 * ε) + logp (2 * D / (Qr)) / 2) := by
      have e : (1 + ε) * (2 * Y) * √(3 + 2 * ε) +
          (1 + ε) * (2 * Y) / 2 * logp (2 * D / (Qr)) =
          (1 + ε) * (2 * Y) * (√(3 + 2 * ε) + logp (2 * D / (Qr)) / 2) := by ring
      rw [e]
      refine mul_le_mul_of_nonneg_right ?_ (add_nonneg h3e (div_nonneg hlp (by norm_num)))
      exact mul_le_mul_of_nonneg_left hmin (by linarith only [hε])
    have h2s : (0 : ℝ) ≤ 2 * s / π := div_nonneg (mul_nonneg (by norm_num) (hs0.trans hs1)) hpi.le
    have hB2 := mul_le_mul_of_nonneg_left hB h2s
    have hC : 2 * √c0 / π * Y ≤ 2 * s / π * Y := by
      refine mul_le_mul_of_nonneg_right ?_ hY0.le
      exact div_le_div_of_nonneg_right (by linarith) hpi.le
    refine le_trans (le_of_eq ?_) (le_trans (add_le_add (add_le_add (add_le_add hC
      (le_refl (2 * s / π * (D - Y)))) (add_le_add hB2 hA))
      (le_refl (35 * c0 * c2 / (3 * π ^ 2) * q))) (le_of_eq ?_))
    · ring
    · ring

/-- **`MPB2.EsthelEta2`, PROVED** (both branches). -/
theorem esthelEta2_holds : EsthelEta2 :=
  esthelEta2_of_KE esthelEta2K_holds esthelEta2E_holds

/-- **`MPc.Bosta2Eta2` (`lem:bosta2` for `η₂`) from the two cited computer checks alone,
PROVED** (`MPBM.bosta2Eta2_of_esthel` with `esthelEta2_holds`). -/
theorem bosta2Eta2_of_cited (hG : HC.CameloGridCited) (hW : HC.WollustCited) : Bosta2Eta2 :=
  MPBM.bosta2Eta2_of_esthel hG hW esthelEta2_holds

end Principia.Common.TernaryGoldbach.MPE2
