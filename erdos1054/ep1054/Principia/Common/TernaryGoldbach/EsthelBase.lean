/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TrigSumsNat
import Principia.Common.TernaryGoldbach.Bosta2Spine

set_option autoImplicit false

/-!
# The three pieces of `eq:esthel` (`lem:bosta2`, the `eq:keks` case), for any `T`

Book `typeI.tex` 903-993 (Case (b) of `lem:bosta1`) with the `lem:bosta2` modifications
(1119-1141: `C` doubled, `c₂ = 6π/5√c₀`, `eq:sosot`). For a `t ≥ 0` obeying `eq:trompais`
written at `α = 2β = a/q + β'/(qQ)` (`TB`):

* `piece1` -- `eq:prokof`: `∑_{m ≤ q/2} t ≤ (2|η₂'|₁/π) q max(1, log(c₀e³q²/(4π|η₂'|₁x)))`
  (`lem:thina`, `B = |η₂'|₁/2`, `C = c₀q/4x`; `max(2, log 2 + L) ≤ 2max(1, L)`);
* `piece2` -- `eq:martinu`: `∑_{q/2 < m ≤ D', q ∤ m} t ≤ (2√c₀/π)D' + (55c₀c₂/6π²)q` for
  `D' ≤ min(c₂x/q, Q/2)` (`lem:couscous` on the windows `(⌊q/2⌋ + jq, ⌊q/2⌋ + (j+1)q]`;
  `eq:sosot`; the window count is the ceiling `⌈(⌊D'⌋ - ⌊q/2⌋)/q⌉ ≤ D'/q + 1/2`, which is what
  makes the book's `11q/2` come out exactly);
* `piece3` -- `eq:caron` + `eq:kosto` + `eq:kostas`: for any `R ≥ max(c₂x/q, q/2)`,
  `∑_{R < m ≤ D} t ≤ (3c₁/2c₂)q + (3c₁/2)(x/q)log⁺(D/(c₂x/q))
  + (2√(c₀c₁)/π)(√3q + max(D - R, 0) + (q/2)log⁺(D/(q/2)))` (`lem:gotog` per window, then
  `TrigSumN.harm_le` in place of the book's integrals).

The windows `(⌊R⌋ + jq, ⌊R⌋ + (j+1)q]` start at the INTEGER `⌊R⌋`; every `m` in window `j`
satisfies `m > R + jq`, which is all the per-window `A` needs.
-/

namespace Principia.Common.TernaryGoldbach.MPE2

open Real Finset Principia.Common.TrigSumN
open Principia.Common.TernaryGoldbach.MPc Principia.Common.TernaryGoldbach.MPB2

theorem c0_pos : 0 < c0 := by unfold c0; norm_num

theorem c2_pos : 0 < c2 := by
  unfold c2
  have := Real.sqrt_pos.mpr c0_pos
  positivity

theorem eta1_pos : 0 < eta1 := by
  unfold eta1
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

/-- `eq:sosot`: `5c₀c₂/(3π²) = 2√c₀/π`. -/
theorem sosot : 5 * c0 * c2 / (3 * π ^ 2) = 2 * √c0 / π := by
  unfold c2
  have h0 : 0 < √c0 := Real.sqrt_pos.mpr c0_pos
  have hp : 0 < π := Real.pi_pos
  rw [show 5 * c0 * (6 * π / (5 * √c0)) / (3 * π ^ 2) = 2 * (c0 / √c0) / π by
    field_simp; ring, Real.div_sqrt]

/-- `T` obeys `eq:trompais` written with `α = 2β`. -/
def TB (x α : ℝ) (t : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → 0 ≤ t d ∧ t d ≤ x / (2 * d) + eta1 / 2 ∧
    t d * |sin (π * (α * d))| ≤ eta1 / 2 ∧ t d * sin (π * (α * d)) ^ 2 ≤ d / x * (c0 / 2)

theorem tb_of_tromB (x β : ℝ) (T : ℕ → ℝ) (h : TromB x β T) : TB x (2 * β) T := by
  intro d hd
  obtain ⟨h0, h1, h2, h3⟩ := h d hd
  have e : π * (2 * β * d) = 2 * π * d * β := by ring
  rw [e]
  exact ⟨h0, h1, h2, h3⟩

/-! ## Piece 1 -- `eq:prokof`, `m ≤ q/2` (`lem:thina`) -/

/-- `max(2, log 2 + L) ≤ 2 max(1, L)`. -/
theorem max_two_le (L : ℝ) : max 2 (Real.log 2 + L) ≤ 2 * max 1 L := by
  have h2 := Real.log_two_lt_d9
  rcases le_total L 1 with h | h
  · rw [max_eq_left h]
    exact max_le (by norm_num) (by linarith)
  · rw [max_eq_right h]
    exact max_le (by linarith) (by linarith)

theorem piece1 (x α β Q : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hqQ : (q : ℝ) ≤ Q) (hx : 0 < x)
    (t : ℕ → ℝ) (ht : TB x α t) :
    ∑ d ∈ Ioc 0 (q / 2), t d ≤
      2 * eta1 / π * q *
        max 1 (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * π * eta1 * x))) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hfil : (Ioc 0 (q / 2)).filter (fun n => ¬ q ∣ n) = Ioc 0 (q / 2) := by
    refine Finset.filter_true_of_mem fun n hn => ?_
    have h1 := Finset.mem_Ioc.mp hn
    exact Nat.not_dvd_of_pos_of_lt h1.1 (by omega)
  have hh : ((q / 2 : ℕ) : ℝ) ≤ q / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    have : q / 2 * 2 ≤ q := Nat.div_mul_le_self q 2
    exact_mod_cast this
  have hB : (0 : ℝ) ≤ eta1 / 2 := by have := eta1_pos; positivity
  have hC : (0 : ℝ) ≤ c0 * q / (4 * x) := by have := c0_pos; positivity
  have key := thinaN α β Q (eta1 / 2) (c0 * q / (4 * x)) a q hq hcop hα hβ hB hC 0 (q / 2)
    (by omega) (by linarith) t
    (fun n hn => (ht n (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1).2.2.1)
    (fun n hn => by
      have hn' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
      have h3 := (ht n hn'.1).2.2.2
      have hnr : (n : ℝ) ≤ q / 2 := le_trans (by exact_mod_cast hn'.2) hh
      refine h3.trans ?_
      have := c0_pos
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hx (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hnr) this.le) hx.le])
  rw [hfil] at key
  have hlog : Real.log (c0 * q / (4 * x) * Real.exp 3 * q / (eta1 / 2 * π)) =
      Real.log 2 + Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * π * eta1 * x)) := by
    rw [← Real.log_mul (by norm_num) (by have := c0_pos; have := eta1_pos; positivity)]
    congr 1
    have := eta1_pos
    field_simp
  rw [hlog] at key
  have hm := max_two_le (Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * π * eta1 * x)))
  have hk : 0 ≤ eta1 * q / π := by have := eta1_pos; positivity
  have hk2 := mul_le_mul_of_nonneg_left hm hk
  calc _ ≤ _ := key
    _ = eta1 * q / π *
          max 2 (Real.log 2 + Real.log (c0 * Real.exp 3 * (q : ℝ) ^ 2 / (4 * π * eta1 * x))) := by
          ring
    _ ≤ _ := hk2
    _ = _ := by ring

/-- Ceiling division: `J = ⌈n/q⌉ = (n + q - 1)/q` has `n ≤ Jq ≤ n + q - 1`. -/
theorem cdiv_spec (n q : ℕ) (hq : 1 ≤ q) :
    n ≤ (n + q - 1) / q * q ∧ (n + q - 1) / q * q ≤ n + q - 1 := by
  have h1 := Nat.div_add_mod (n + q - 1) q
  have h2 := Nat.mod_lt (n + q - 1) (by omega : q > 0)
  obtain ⟨m, hm⟩ : ∃ m, m = (n + q - 1) / q := ⟨_, rfl⟩
  rw [← hm] at h1 ⊢
  rw [mul_comm m q]
  generalize q * m = P at h1 ⊢
  omega

/-- `∑_{j < J} (j + 3/2) = J(J + 2)/2`. -/
theorem sum_j32 (J : ℕ) : ∑ j ∈ range J, ((j : ℝ) + 3 / 2) = J * (J + 2) / 2 := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-! ## Piece 2 -- `eq:martinu`, `q/2 < m ≤ D'`, `q ∤ m` (`lem:couscous`) -/

theorem piece2 (x α β Q D' : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hx : 0 < x) (hD0 : 0 ≤ D')
    (hDQ : 2 * D' ≤ Q) (hDc : D' ≤ c2 * x / q) (t : ℕ → ℝ) (ht : TB x α t) :
    ∑ d ∈ (Ioc (q / 2) ⌊D'⌋₊).filter (fun d => ¬ q ∣ d), t d ≤
      2 * √c0 / π * D' + 55 * c0 * c2 / (6 * π ^ 2) * q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 := c0_pos
  have hc2 := c2_pos
  have hpi := Real.pi_pos
  set h := q / 2 with hh_def
  set N := ⌊D'⌋₊ with hN_def
  set J := (N - h + q - 1) / q with hJ_def
  obtain ⟨hJ1, hJ2⟩ := cdiv_spec (N - h) q hq
  rw [← hJ_def] at hJ1 hJ2
  have hNJ : N ≤ h + J * q := by
    generalize J * q = P at hJ1 hJ2 ⊢
    omega
  have hhr : (h : ℝ) ≤ q / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    have : q / 2 * 2 ≤ q := Nat.div_mul_le_self q 2
    exact_mod_cast this
  have hhr2 : ((q : ℝ) - 1) / 2 ≤ h := by
    have : q ≤ 2 * h + 1 := by omega
    have : (q : ℝ) ≤ 2 * h + 1 := by exact_mod_cast this
    linarith
  have hNr : (N : ℝ) ≤ D' := Nat.floor_le hD0
  rw [sum_filter_windows t _ h q J N hNJ]
  have hwin : ∀ j ∈ range J,
      ∑ d ∈ Ioc (h + j * q) (h + j * q + q), (if d ≤ N ∧ ¬ q ∣ d then t d else 0) ≤
        20 / (3 * π ^ 2) * (c0 * ((j : ℝ) + 3 / 2) * q / (2 * x)) * q ^ 2 := by
    intro j _
    rw [window_trunc]
    refine couscousN α β Q _ a q hq hcop hα hβ (by positivity) (h + j * q)
      (min (h + j * q + q) N) (by omega) ?_ t ?_
    · have : ((min (h + j * q + q) N : ℕ) : ℝ) ≤ N := by exact_mod_cast min_le_right _ _
      linarith
    · intro d hd
      have hd' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1
      have hd1 : 1 ≤ d := by omega
      have hdle : d ≤ h + j * q + q := le_trans hd'.2 (min_le_left _ _)
      have hdr : (d : ℝ) ≤ ((j : ℝ) + 3 / 2) * q := by
        have : (d : ℝ) ≤ h + j * q + q := by exact_mod_cast hdle
        nlinarith
      refine (ht d hd1).2.2.2.trans ?_
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hx (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hdr) hc0.le) hx.le]
  refine (Finset.sum_le_sum hwin).trans ?_
  have e : ∑ j ∈ range J, 20 / (3 * π ^ 2) * (c0 * ((j : ℝ) + 3 / 2) * q / (2 * x)) * q ^ 2 =
      20 / (3 * π ^ 2) * (c0 * q ^ 3 / (2 * x)) * (J * (J + 2) / 2) := by
    rw [← sum_j32, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [e]
  have hR0 : 0 ≤ 2 * √c0 / π * D' + 55 * c0 * c2 / (6 * π ^ 2) * q := by positivity
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
  · rw [hJ0]
    simpa using hR0
  -- `J ≥ 1`: then `N > h`, so `q/2 < D' ≤ c₂x/q` and `q² < 2c₂x`
  have hNh : h + 1 ≤ N := by
    by_contra hcon
    have : N - h = 0 := by omega
    rw [this] at hJ_def
    have : J = 0 := by
      rw [hJ_def, zero_add]
      exact Nat.div_eq_of_lt (by omega)
    omega
  have hNh' : (h : ℝ) + 1 ≤ N := by exact_mod_cast hNh
  have hqD : (q : ℝ) / 2 < D' := by linarith
  have hqq : (q : ℝ) ^ 2 < 2 * c2 * x := by
    have h1 : (q : ℝ) / 2 < c2 * x / q := lt_of_lt_of_le hqD hDc
    rw [lt_div_iff₀ hq0] at h1
    nlinarith
  have hJq : (J : ℝ) * q ≤ D' + q / 2 := by
    have h1 : J * q ≤ N - h + q - 1 := hJ2
    have h2 : J * q + h + 1 ≤ N + q := by
      generalize J * q = P at h1 ⊢
      omega
    have h3 : (J : ℝ) * q + h + 1 ≤ N + q := by exact_mod_cast h2
    linarith
  have hJr : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hDq : D' * q ≤ c2 * x := by rwa [le_div_iff₀ hq0] at hDc
  -- `q³J(J+2) ≤ x(c₂D' + (11/2)c₂q)`
  have hkey : (q : ℝ) ^ 3 * (J * (J + 2)) ≤ x * (c2 * D' + 11 / 2 * c2 * q) := by
    have hy0 : (0 : ℝ) ≤ J * q := by positivity
    have e1 : (q : ℝ) ^ 3 * (J * (J + 2)) = q * ((J * q) * (J * q + 2 * q)) := by ring
    have h1 : (q : ℝ) * ((J * q) * (J * q + 2 * q)) ≤
        q * ((D' + q / 2) * (D' + q / 2 + 2 * q)) := by
      refine mul_le_mul_of_nonneg_left ?_ hq0.le
      exact mul_le_mul hJq (by linarith) (by positivity) (by positivity)
    have h2 : D' * (D' * q) ≤ D' * (c2 * x) := mul_le_mul_of_nonneg_left hDq hD0
    have h3 : 3 * q * (D' * q) ≤ 3 * q * (c2 * x) :=
      mul_le_mul_of_nonneg_left hDq (by positivity)
    have h4 : 5 / 4 * q * (q : ℝ) ^ 2 ≤ 5 / 4 * q * (2 * c2 * x) :=
      mul_le_mul_of_nonneg_left hqq.le (by positivity)
    have e4 : (q : ℝ) * ((D' + q / 2) * (D' + q / 2 + 2 * q)) =
        D' * (D' * q) + 3 * q * (D' * q) + 5 / 4 * q * (q : ℝ) ^ 2 := by ring
    have e5 : x * (c2 * D' + 11 / 2 * c2 * q) =
        D' * (c2 * x) + 3 * q * (c2 * x) + 5 / 4 * q * (2 * c2 * x) := by ring
    rw [e1, e5]
    rw [e4] at h1
    linarith
  rw [← sosot]
  have e2 : 20 / (3 * π ^ 2) * (c0 * q ^ 3 / (2 * x)) * (J * (J + 2) / 2) =
      5 * c0 / (3 * π ^ 2) * ((q : ℝ) ^ 3 * (J * (J + 2)) / x) := by
    field_simp
    ring
  have e3 : 5 * c0 * c2 / (3 * π ^ 2) * D' + 55 * c0 * c2 / (6 * π ^ 2) * q =
      5 * c0 / (3 * π ^ 2) * (c2 * D' + 11 / 2 * c2 * q) := by
    field_simp
    ring
  rw [e2, e3]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [div_le_iff₀ hx]
  linarith


/-! ## Piece 3 -- `eq:caron`, `R < m ≤ D` (`lem:gotog`) -/

/-- **One `lem:gotog` window of `eq:caron`**: for `j` with `jq + R ≤ D`, the window
`(⌊R⌋ + jq, ⌊R⌋ + jq + q]` (truncated at `⌊D⌋`) sums to at most `3A + (4q/π)√(AC)` with
`A = c₁x/(2(jq + R))`, `C = c₀((j + 1)q + R)/(2x)`. -/
theorem gwin (x α β Q D R : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hqQ : (q : ℝ) ≤ Q) (hx : 0 < x)
    (hR : 0 < R) (t : ℕ → ℝ) (ht : TB x α t) (j : ℕ) (hj : (j : ℝ) * q + R ≤ D) :
    ∑ d ∈ Ioc (⌊R⌋₊ + j * q) (⌊R⌋₊ + j * q + q),
        (if d ≤ ⌊D⌋₊ ∧ True then t d else 0) ≤
      3 * (c1 x D * x / (2 * (j * q + R))) +
        4 * q / π * √(c1 x D * x / (2 * (j * q + R)) * (c0 * ((j + 1) * q + R) / (2 * x))) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 := c0_pos
  have he := eta1_pos
  have hjr : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hjR : 0 < (j : ℝ) * q + R := by positivity
  have hD0 : 0 < D := lt_of_lt_of_le hjR hj
  have hc1 : 1 ≤ c1 x D := by
    unfold c1
    have : 0 ≤ eta1 * D / x := by positivity
    linarith
  have hrR : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR.le
  have hRr : R < ⌊R⌋₊ + 1 := Nat.lt_floor_add_one R
  refine gotogN α β Q _ _ a q hq hcop hα hβ hqQ (by positivity) (by positivity) _ _ ?_ ?_
  · intro d hd
    have hd' := Finset.mem_Ioc.mp hd
    split_ifs with hdN
    · have hd1 : 1 ≤ d := by omega
      have hdr : (j : ℝ) * q + R ≤ d := by
        have : (⌊R⌋₊ : ℝ) + j * q + 1 ≤ d := by exact_mod_cast hd'.1
        linarith
      refine (ht d hd1).2.1.trans ?_
      have h1 : x / (2 * d) ≤ x / (2 * (j * q + R)) :=
        div_le_div_of_nonneg_left hx.le (by positivity) (by linarith)
      have h2 : eta1 / 2 ≤ eta1 * D / x * (x / (2 * (j * q + R))) := by
        rw [show eta1 * D / x * (x / (2 * (j * q + R))) = eta1 * D / (2 * (j * q + R)) by
          field_simp]
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith
      have e : c1 x D * x / (2 * (j * q + R)) =
          x / (2 * (j * q + R)) + eta1 * D / x * (x / (2 * (j * q + R))) := by
        unfold c1
        ring
      rw [e]
      linarith
    · positivity
  · intro d hd
    have hd' := Finset.mem_Ioc.mp hd
    split_ifs with hdN
    · have hd1 : 1 ≤ d := by omega
      have hdr : (d : ℝ) ≤ ((j : ℝ) + 1) * q + R := by
        have : (d : ℝ) ≤ ⌊R⌋₊ + j * q + q := by exact_mod_cast hd'.2
        linarith
      refine (ht d hd1).2.2.2.trans ?_
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hx (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hdr) hc0.le) hx.le]
    · rw [zero_mul]
      positivity

/-- `√(AC)` at `j = 0`: `≤ (√(c₀c₁)/2)·√3` (as `q ≤ 2R`). -/
theorem sqrt_w0 (x c1v R : ℝ) (q : ℕ) (hx : 0 < x) (hc1 : 0 ≤ c1v) (hR : (q : ℝ) ≤ 2 * R)
    (hR0 : 0 < R) :
    √(c1v * x / (2 * ((0 : ℕ) * q + R)) * (c0 * (((0 : ℕ) + 1) * q + R) / (2 * x))) ≤
      √(c0 * c1v) / 2 * √3 := by
  have hc0 := c0_pos
  have hv : 0 ≤ √(c0 * c1v) / 2 * √3 := by positivity
  rw [← Real.sqrt_sq hv]
  refine Real.sqrt_le_sqrt ?_
  have e : (√(c0 * c1v) / 2 * √3) ^ 2 = c0 * c1v / 4 * 3 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
    ring
  rw [e]
  push_cast
  rw [show c1v * x / (2 * (0 * q + R)) * (c0 * ((0 + 1) * q + R) / (2 * x)) =
    c0 * c1v / 4 * ((q + R) / R) by field_simp; ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [div_le_iff₀ hR0]
  linarith

/-- `√(AC)` at `j + 1`: `≤ (√(c₀c₁)/2)·(1 + q/(2((j+1)q + R)))`. -/
theorem sqrt_ws (x c1v R : ℝ) (q j : ℕ) (hx : 0 < x) (hc1 : 0 ≤ c1v) (hq : 0 < (q : ℝ))
    (hR0 : 0 < R) :
    √(c1v * x / (2 * (((j + 1 : ℕ) : ℝ) * q + R)) *
        (c0 * ((((j + 1 : ℕ) : ℝ) + 1) * q + R) / (2 * x))) ≤
      √(c0 * c1v) / 2 * (1 + q / (2 * ((j + 1) * q + R))) := by
  have hc0 := c0_pos
  have hjr : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hjR : 0 < ((j : ℝ) + 1) * q + R := by positivity
  have hv : 0 ≤ √(c0 * c1v) / 2 * (1 + q / (2 * ((j + 1) * q + R))) := by positivity
  rw [← Real.sqrt_sq hv]
  refine Real.sqrt_le_sqrt ?_
  set u := (q : ℝ) / (((j : ℝ) + 1) * q + R) with hu
  have hu0 : 0 ≤ u := by positivity
  have e : (√(c0 * c1v) / 2 * (1 + q / (2 * ((j + 1) * q + R)))) ^ 2 =
      c0 * c1v / 4 * (1 + u / 2) ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by positivity), hu]
    field_simp
    ring
  rw [e]
  push_cast
  have e2 : c1v * x / (2 * (((j : ℝ) + 1) * q + R)) * (c0 * (((j : ℝ) + 1 + 1) * q + R) / (2 * x))
      = c0 * c1v / 4 * (1 + u) := by
    rw [hu]
    field_simp
    ring
  rw [e2]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  nlinarith [sq_nonneg u]

/-- `log t ≤ log⁺ s` for `0 < t ≤ s`. -/
theorem log_le_logp (t s : ℝ) (ht : 0 < t) (hts : t ≤ s) : Real.log t ≤ logp s :=
  (Real.log_le_log ht hts).trans (le_max_left _ _)

/-- **Piece 3 -- `eq:caron` + `eq:kosto` + `eq:kostas` for `lem:bosta2`**: for any
`R ≥ max(c₂x/q, q/2)`, `∑_{R < m ≤ D} T(m) ≤ (3c₁/2c₂)q + (3c₁/2)(x/q)log⁺(D/(c₂x/q))
+ (2√(c₀c₁)/π)(√3 q + max(D - R, 0) + (q/2)log⁺(D/(q/2)))`. -/
theorem piece3 (x α β Q D R : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hqQ : (q : ℝ) ≤ Q) (hx : 0 < x)
    (hD : 1 ≤ D) (hR1 : c2 * x / q ≤ R) (hR2 : (q : ℝ) / 2 ≤ R) (t : ℕ → ℝ) (ht : TB x α t) :
    ∑ d ∈ Ioc ⌊R⌋₊ ⌊D⌋₊, t d ≤
      3 * c1 x D / (2 * c2) * q + 3 * c1 x D / 2 * (x / q) * logp (D / (c2 * x / q)) +
        2 * √(c0 * c1 x D) / π * (√3 * q + max (D - R) 0 + q / 2 * logp (D / (q / 2))) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 := c0_pos
  have hc2 := c2_pos
  have hpi := Real.pi_pos
  have he := eta1_pos
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR2
  have hc1 : 1 ≤ c1 x D := by
    unfold c1
    have : 0 ≤ eta1 * D / x := by positivity
    linarith
  have hc1' : 0 ≤ c1 x D := by linarith
  have hlp1 : 0 ≤ logp (D / (c2 * x / q)) := le_max_right _ _
  have hlp2 : 0 ≤ logp (D / (q / 2)) := le_max_right _ _
  have hmx : 0 ≤ max (D - R) 0 := le_max_right _ _
  have hRHS : 0 ≤ 3 * c1 x D / (2 * c2) * q + 3 * c1 x D / 2 * (x / q) * logp (D / (c2 * x / q)) +
      2 * √(c0 * c1 x D) / π * (√3 * q + max (D - R) 0 + q / 2 * logp (D / (q / 2))) := by
    positivity
  set r := ⌊R⌋₊ with hr_def
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
  have hKr : (K : ℝ) * q + R ≤ D := by
    rw [hK] at hJ2
    have h1 : K * q + r + 1 ≤ N := by
      have e : (K + 1) * q = K * q + q := by ring
      rw [e] at hJ2
      generalize K * q = P at hJ2 ⊢
      omega
    have h2 : (K : ℝ) * q + r + 1 ≤ N := by exact_mod_cast h1
    have h3 : R < r + 1 := Nat.lt_floor_add_one R
    have h4 : (N : ℝ) ≤ D := Nat.floor_le (by linarith)
    linarith
  have hKr0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [hK, Finset.sum_range_succ']
  set s := √(c0 * c1 x D) with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  -- the `j + 1` windows
  have hwin : ∀ j ∈ range K,
      ∑ d ∈ Ioc (r + (j + 1) * q) (r + (j + 1) * q + q), (if d ≤ N ∧ True then t d else 0) ≤
        (3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) * (1 / (((j : ℝ) + 1) * q + R)) +
          2 * q / π * s := by
    intro j hj
    have hjK : j + 1 ≤ K := Finset.mem_range.mp hj
    have hjK' : ((j + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hjK
    have hjD : ((j + 1 : ℕ) : ℝ) * q + R ≤ D := by
      have := mul_le_mul_of_nonneg_right hjK' hq0.le
      linarith
    have hg := gwin x α β Q D R a q hq hcop hα hβ hqQ hx hR0 t ht (j + 1) hjD
    have hsq := sqrt_ws x (c1 x D) R q j hx hc1' hq0 hR0
    have hjR : 0 < ((j : ℝ) + 1) * q + R := by positivity
    refine hg.trans ?_
    have h4 : 4 * q / π * √(c1 x D * x / (2 * (((j + 1 : ℕ) : ℝ) * q + R)) *
        (c0 * ((((j + 1 : ℕ) : ℝ) + 1) * q + R) / (2 * x))) ≤
        4 * q / π * (s / 2 * (1 + q / (2 * ((j + 1) * q + R)))) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have e : 3 * (c1 x D * x / (2 * (((j + 1 : ℕ) : ℝ) * q + R))) +
        4 * q / π * (s / 2 * (1 + q / (2 * ((j + 1) * q + R)))) =
        (3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) * (1 / (((j : ℝ) + 1) * q + R)) +
          2 * q / π * s := by
      push_cast
      field_simp
      ring
    linarith
  -- the `j = 0` window
  have hw0 := gwin x α β Q D R a q hq hcop hα hβ hqQ hx hR0 t ht 0
    (by have := mul_nonneg hKr0 hq0.le; push_cast; linarith)
  have hsq0 := sqrt_w0 x (c1 x D) R q hx hc1' (by linarith) hR0
  have h40 := mul_le_mul_of_nonneg_left hsq0 (by positivity : (0 : ℝ) ≤ 4 * q / π)
  have hsum := Finset.sum_le_sum hwin
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  have hH := harm_le q R hq0 hR0 K
  set H := ∑ j ∈ range K, 1 / (((j : ℝ) + 1) * q + R) with hH_def
  set Lg := Real.log ((K * q + R) / R) with hLg_def
  have hLg1 : Lg ≤ logp (D / (c2 * x / q)) := by
    refine log_le_logp _ _ (by positivity) ?_
    rw [div_le_div_iff₀ hR0 (by positivity)]
    have h1 : (K * q + R) * (c2 * x / q) ≤ (K * q + R) * R :=
      mul_le_mul_of_nonneg_left hR1 (by positivity)
    have h2 : (K * q + R) * R ≤ D * R := mul_le_mul_of_nonneg_right hKr hR0.le
    linarith
  have hLg2 : Lg ≤ logp (D / (q / 2)) := by
    refine log_le_logp _ _ (by positivity) ?_
    rw [div_le_div_iff₀ hR0 (by positivity)]
    have h1 : (K * q + R) * (q / 2) ≤ (K * q + R) * R :=
      mul_le_mul_of_nonneg_left hR2 (by positivity)
    have h2 : (K * q + R) * R ≤ D * R := mul_le_mul_of_nonneg_right hKr hR0.le
    linarith
  have hcoef : 0 ≤ 3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2) := by positivity
  have hH2 := mul_le_mul_of_nonneg_left hH hcoef
  have hA0 : 3 * (c1 x D * x / (2 * (((0 : ℕ) : ℝ) * q + R))) ≤ 3 * c1 x D / (2 * c2) * q := by
    have h1 : c2 * x ≤ R * q := by rwa [div_le_iff₀ hq0] at hR1
    have e1 : 3 * (c1 x D * x / (2 * (((0 : ℕ) : ℝ) * q + R))) =
        3 * c1 x D / (2 * c2) * (c2 * x / R) := by
      push_cast
      rw [zero_mul, zero_add]
      field_simp
    have e2 : 3 * c1 x D / (2 * c2) * q = 3 * c1 x D / (2 * c2) * (R * q / R) := by
      field_simp
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact div_le_div_of_nonneg_right h1 hR0.le
  have hKq : (K : ℝ) * q ≤ max (D - R) 0 := le_trans (by linarith) (le_max_left _ _)
  -- assemble
  have hfin : (3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) * (1 / q * Lg) + K * (2 * q / π * s)
      ≤ 3 * c1 x D / 2 * (x / q) * logp (D / (c2 * x / q)) +
        2 * s / π * (max (D - R) 0 + q / 2 * logp (D / (q / 2))) := by
    have e : (3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2)) * (1 / q * Lg) + K * (2 * q / π * s)
        = 3 * c1 x D / 2 * (x / q) * Lg + 2 * s / π * (K * q + q / 2 * Lg) := by
      field_simp
      ring
    rw [e]
    have h1 : 3 * c1 x D / 2 * (x / q) * Lg ≤ 3 * c1 x D / 2 * (x / q) * logp (D / (c2 * x / q)) :=
      mul_le_mul_of_nonneg_left hLg1 (by positivity)
    have h2 : (K : ℝ) * q + q / 2 * Lg ≤ max (D - R) 0 + q / 2 * logp (D / (q / 2)) :=
      add_le_add hKq (mul_le_mul_of_nonneg_left hLg2 (by positivity))
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * s / π)
    linarith
  have e3 : 4 * q / π * (s / 2 * √3) = 2 * s / π * (√3 * q) := by ring
  rw [e3] at h40
  have e4 : 2 * s / π * (√3 * q + max (D - R) 0 + q / 2 * logp (D / (q / 2))) =
      2 * s / π * (√3 * q) + 2 * s / π * (max (D - R) 0 + q / 2 * logp (D / (q / 2))) := by
    ring
  rw [e4]
  linarith

end Principia.Common.TernaryGoldbach.MPE2
