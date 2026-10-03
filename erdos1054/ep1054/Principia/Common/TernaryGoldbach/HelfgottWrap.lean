/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.HelfgottCited
import Principia.Common.PSieveG
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false

/-!
# Helfgott's wrappers, round 1: `AusteriaLip` PROVED, `CharpyGap` closed by `eq:charpas`

`HelfgottCited` (namespace `HC`) left two small owed inputs of the cited headline
`FromTopCited.ep1054_topC_cited` besides the deep `HC.Crepe` and the large `HC.EspagnRed`
(whose spine is `EspagnWrap.lean`). This file removes both.

## (1) `HC.AusteriaLip`, the grid-to-continuum step of `cor:austeria` — PROVED

`ternvin.tex` 5543-5547: "computing only at grid points results in an inaccuracy of at most
`0.00801x`", from `|η₂'|_∞ = 16` and `∑_{x/4 ≤ n ≤ x} Λ(n) ≤ x`. The proof here takes the log
variable instead: `η₂(t) = 4 max(log 2 − |log 2t|, 0)` is `4`-Lipschitz in `log t` (`eta2_sub_le`),
so `η₂(n/x) − η₂(n/x_k) ≤ 4|log x − log x_k| ≤ 4·0.0005/0.9995` for every `n`, and the terms where
`η₂(n/x) = 0` only help. Summing over `n ≤ x` costs `ψ(x) ≤ 3.3863x` (`psi_le_33863`, from
Mathlib's `ψ(x) ≤ log 4·x + 2√x log x` and `log x ≤ √x`), so the inaccuracy is
`≤ 4·(0.0005/0.9995)·3.3863x = 0.00678x < 0.00801x`. No Chebyshev bound sharper than Mathlib's is
needed: the log variable gains the factor `4` that Helfgott spends on `|η₂'|_∞ = 16`.

## (2) `HC.CharpyGap` — closed by Helfgott's OWN `eq:charpas` run, route (b)

`eq:charpy`'s lower bound `G(R) ≥ log R + 1.312` on `(4·10⁷, 355³)` is covered by no printed
argument (`eq:malito` gives only `1.31128` at `4·10⁷`). Route (a) — weaken the constant to what
`eq:malito` supplies — FAILS: `1.312` is baked into Helfgott's cited check itself, through
`c_{ρ,2} = exp((1.4709 − c_E) + ω(c_E − 1.312) − c_Δ)` in the third term of `ϖ(q)` (`eq:armor`),
which is the ACTIVE term of `ϖ(q)` for small `q` (`ϖ(1) = 71733.6` is that term). A weaker constant
enlarges `c_{ρ,2}`, lowers the true threshold below the cited `ϖ(q)`, and leaves `R` in between
covered by nothing. Route (b) works, with no new computation: the identity
`G(R) ≥ G₂(R) + G₂(R/2)` (every squarefree `r` is odd, or `2m` with `m` odd, and
`μ²(2m)/φ(2m) = μ²(m)/φ(m)`; `gQ_two_add_le`) and Helfgott's `eq:charpas`, checked by him for
`200 ≤ R ≤ 1.6·10⁸` (`CharpasCited`), give on the whole range `400 ≤ R ≤ 1.6·10⁸`
`G(R) ≥ log R + 1.661 − (log 2)/2 = log R + 1.31443`, margin `0.0024` over `1.312`
(`charpyGap_of_charpas`). A computation nobody ran is replaced by one Helfgott did run, cited at
his statement. (Float64: `G(R) = G₂(R) + G₂(R/2)` to `10⁻⁶` at three points of the gap, and
`eq:charpas` holds on `[200, 4.5·10⁷)` with margin `2.4·10⁻⁵`, `scratchpad/hcite/wrap_num.py`.)
-/

namespace Principia.Common.TernaryGoldbach.HX

open scoped ArithmeticFunction
open Principia.Common.PSieve (gQ)

/-! ## (1) `AusteriaLip` -/

/-- **`η₂` is `4`-Lipschitz in `log t`**: `η₂(a) − η₂(b) ≤ 4|log a − log b|` for `a, b > 0`. -/
theorem eta2_sub_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HW.eta2 a - HW.eta2 b ≤ 4 * |Real.log a - Real.log b| := by
  unfold HW.eta2
  rw [if_pos ha, if_pos hb]
  have h1 : max (Real.log 2 - |Real.log (2 * a)|) 0 - max (Real.log 2 - |Real.log (2 * b)|) 0 ≤
      |(Real.log 2 - |Real.log (2 * a)|) - (Real.log 2 - |Real.log (2 * b)|)| :=
    le_trans (le_abs_self _) (abs_max_sub_max_le_abs _ _ _)
  have e : (Real.log 2 - |Real.log (2 * a)|) - (Real.log 2 - |Real.log (2 * b)|) =
      |Real.log (2 * b)| - |Real.log (2 * a)| := by ring
  have h2 := abs_abs_sub_abs_le_abs_sub (Real.log (2 * b)) (Real.log (2 * a))
  have e2 : Real.log (2 * b) - Real.log (2 * a) = -(Real.log a - Real.log b) := by
    rw [Real.log_mul two_ne_zero ha.ne', Real.log_mul two_ne_zero hb.ne']
    ring
  rw [e2, abs_neg] at h2
  rw [e] at h1
  linarith

/-- `|log x − log y| ≤ 0.0005/0.9995` when `x ≥ 1`, `y ≥ 0.9995`, `|x − y| ≤ 0.0005`. -/
theorem abs_log_sub_le {x y : ℝ} (hx : 1 ≤ x) (hy : 0.9995 ≤ y) (h : |x - y| ≤ 0.0005) :
    |Real.log x - Real.log y| ≤ 0.0005 / 0.9995 := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  obtain ⟨hl, hr⟩ := abs_le.mp h
  rw [abs_le]
  constructor
  · have h1 := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at h1
    have h2 : y / x - 1 ≤ 0.0005 / 0.9995 := by
      rw [div_sub_one hx0.ne', div_le_div_iff₀ hx0 (by norm_num)]
      linarith
    linarith
  · have h1 := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rw [Real.log_div hx0.ne' hy0.ne'] at h1
    have h2 : x / y - 1 ≤ 0.0005 / 0.9995 := by
      rw [div_sub_one hy0.ne', div_le_div_iff₀ hy0 (by norm_num)]
      nlinarith
    linarith

/-- **`ψ(x) ≤ 3.3863x` for `x ≥ 1`**: Mathlib's `ψ(x) ≤ log 4·x + 2√x log x`, `log 4 ≤ 1.3863`,
and `log x = 2 log √x ≤ 2(log 2 + √x/2 − 1) ≤ √x`. -/
theorem psi_le_33863 {x : ℝ} (hx : 1 ≤ x) : Chebyshev.psi x ≤ 3.3863 * x := by
  have h1 := Chebyshev.psi_le hx
  have hl2 := Real.log_two_lt_d9
  have hl4 : Real.log 4 ≤ 1.3863 := by
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    rw [e]
    linarith
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hlogx : Real.log x ≤ Real.sqrt x := by
    have e1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt (by linarith)]
      ring
    have e2 : Real.log (Real.sqrt x) = Real.log 2 + Real.log (Real.sqrt x / 2) := by
      rw [← Real.log_mul two_ne_zero (div_pos hsx two_pos).ne']
      congr 1
      ring
    have e3 := Real.log_le_sub_one_of_pos (div_pos hsx two_pos)
    linarith
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have h2 : Real.sqrt x * Real.log x ≤ Real.sqrt x * Real.sqrt x :=
    mul_le_mul_of_nonneg_left hlogx hs0
  have h3 : Real.log 4 * x ≤ 1.3863 * x := mul_le_mul_of_nonneg_right hl4 (by linarith)
  have h4 : 2 * Real.sqrt x * Real.log x = 2 * (Real.sqrt x * Real.log x) := by ring
  linarith

/-- **`S(Y) = ∑_{n < N} Λ(n)η₂(n/Y)`** when `0 < Y ≤ N`: `η₂` vanishes on `[1, ∞)`. -/
theorem sEta2_eq_sum {Y : ℝ} (hY : 0 < Y) (N : ℕ) (hN : Y ≤ N) :
    GS.sEta2 Y = ∑ n ∈ Finset.range N, Λ n * HW.eta2 ((n : ℝ) / Y) := by
  unfold GS.sEta2
  refine tsum_eq_sum fun n hn => ?_
  have hn' : (N : ℝ) ≤ n := by
    have : N ≤ n := not_lt.mp (Finset.mem_range.not.mp hn)
    exact_mod_cast this
  rw [HW.eta2_of_one_le ((one_le_div hY).mpr (le_trans hN hn')), mul_zero]

/-- **`HC.AusteriaLip`, PROVED**: for `x ≥ 1` and a grid point `x_k = k/1000` with
`|x − x_k| ≤ 0.0005`, `S(x) ≤ S(x_k) + 0.00801x`. Termwise `Λ(n)(η₂(n/x) − η₂(n/x_k))` is `≤ 0`
unless `n < x`, and then `≤ 4·(0.0005/0.9995)Λ(n)`; the sum over `n ≤ x` is `ψ(x) ≤ 3.3863x`. -/
theorem austeriaLip : HC.AusteriaLip := by
  intro x hx k hk
  have hab := abs_le.mp hk
  have hy1 : (0.9995 : ℝ) ≤ (k : ℝ) / 1000 := by linarith [hab.2]
  have hx0 : 0 < x := by linarith
  have hy0 : (0 : ℝ) < (k : ℝ) / 1000 := by linarith
  have hfl := Nat.lt_floor_add_one x
  have hxN : x ≤ ((⌊x⌋₊ + 2 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hyN : (k : ℝ) / 1000 ≤ ((⌊x⌋₊ + 2 : ℕ) : ℝ) := by
    push_cast
    linarith [hab.1]
  rw [sEta2_eq_sum hx0 _ hxN, sEta2_eq_sum hy0 _ hyN]
  have hδ := abs_log_sub_le hx hy1 hk
  have hterm : ∀ n ∈ Finset.range (⌊x⌋₊ + 2),
      Λ n * HW.eta2 ((n : ℝ) / x) - Λ n * HW.eta2 ((n : ℝ) / ((k : ℝ) / 1000)) ≤
        if n ∈ Finset.Icc 0 ⌊x⌋₊ then 4 * (0.0005 / 0.9995) * Λ n else 0 := by
    intro n _
    have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have hη := HW.eta2_nonneg ((n : ℝ) / ((k : ℝ) / 1000))
    have hprod : 0 ≤ Λ n * HW.eta2 ((n : ℝ) / ((k : ℝ) / 1000)) := mul_nonneg hΛ hη
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      simp
    have hn : (0 : ℝ) < n := by exact_mod_cast hnpos
    by_cases hnx : (n : ℝ) < x
    · have hmem : n ∈ Finset.Icc 0 ⌊x⌋₊ :=
        Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor hnx.le⟩
      rw [if_pos hmem]
      have hl := eta2_sub_le (div_pos hn hx0) (div_pos hn hy0)
      have hlog : Real.log ((n : ℝ) / x) - Real.log ((n : ℝ) / ((k : ℝ) / 1000)) =
          -(Real.log x - Real.log ((k : ℝ) / 1000)) := by
        rw [Real.log_div hn.ne' hx0.ne', Real.log_div hn.ne' hy0.ne']
        ring
      rw [hlog, abs_neg] at hl
      have hd : HW.eta2 ((n : ℝ) / x) - HW.eta2 ((n : ℝ) / ((k : ℝ) / 1000)) ≤
          4 * (0.0005 / 0.9995) := by linarith
      have hm := mul_le_mul_of_nonneg_left hd hΛ
      nlinarith
    · have hz : HW.eta2 ((n : ℝ) / x) = 0 :=
        HW.eta2_of_one_le ((one_le_div hx0).mpr (not_lt.mp hnx))
      rw [hz, mul_zero]
      split_ifs
      · have : 0 ≤ 4 * (0.0005 / 0.9995) * Λ n := by positivity
        linarith
      · linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, Finset.sum_ite_mem] at hsum
  have hsub : Finset.range (⌊x⌋₊ + 2) ∩ Finset.Icc 0 ⌊x⌋₊ = Finset.Icc 0 ⌊x⌋₊ := by
    apply Finset.inter_eq_right.mpr
    intro n hn
    rw [Finset.mem_range]
    have := (Finset.mem_Icc.mp hn).2
    omega
  rw [hsub, ← Finset.mul_sum, ← Chebyshev.psi_eq_sum_Icc] at hsum
  have hψ := psi_le_33863 hx
  have hψ' : 4 * (0.0005 / 0.9995) * Chebyshev.psi x ≤ 4 * (0.0005 / 0.9995) * (3.3863 * x) :=
    mul_le_mul_of_nonneg_left hψ (by norm_num)
  linarith

/-! ## (2) `CharpyGap` from `eq:charpas` -/

/-- **CITED computer check — `eq:charpas` on the computed range** (`ternvin.tex` 2682-2687; book
arXiv:1501.05438 `l2normls.tex` 382-387): "for `R ≥ 200`, `(log R + 1.661)/2 ≤ G₂(R) ≤
(log R + 1.698)/2` by `eq:malito` for `R ≥ 1.6·10⁸`, and by a numerical computation for
`200 ≤ R ≤ 1.6·10⁸`", with `G₂ = PSieve.gQ 2`. The computed range, stated for real `R` as printed.
Same method and footnote as `eq:charpy` (Platt's interval arithmetic). Float64 evidence that the
transcription is true and has content: lower margin `2.4·10⁻⁵` (at `R = 200`), upper `1.8·10⁻⁴`,
on `[200, 4.5·10⁷)` (`scratchpad/hcite/wrap_num.py`). Link: arXiv:1312.7748v2, eq. (charpas).
CITED computer check (owner directive 2026-09-30). -/
def CharpasCited : Prop :=
  ∀ R : ℝ, 200 ≤ R → R ≤ 160000000 →
    (Real.log R + 1.661) / 2 ≤ gQ 2 R ∧ gQ 2 R ≤ (Real.log R + 1.698) / 2

/-- `μ²(2)/φ(2) = 1`. -/
theorem gt_two : PSieve.gt 2 = 1 := by
  unfold PSieve.gt
  rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two, Nat.totient_two]
  norm_num

/-- **`G₂(R) + G₂(R/2) ≤ G(R)`**: the odd `r ≤ R` and the `2m`, `m ≤ R/2` odd, are disjoint parts
of `r ≤ R`, and `μ²(2m)/φ(2m) = μ²(m)/φ(m)` for odd `m`. (It is an equality; `≤` is what is
used.) -/
theorem gQ_two_add_le (R : ℝ) : gQ 2 R + gQ 2 (R / 2) ≤ gQ 1 R := by
  classical
  rw [PSieve.gQ_eq_gt, PSieve.gQ_eq_gt, PSieve.gQ_eq_gt]
  have hinj : Set.InjOn (fun m : ℕ => 2 * m) (PSieve.sq 2 (R / 2) : Set ℕ) := by
    intro a _ b _ h
    simp only at h
    omega
  have himg : ∑ m ∈ PSieve.sq 2 (R / 2), PSieve.gt m =
      ∑ r ∈ (PSieve.sq 2 (R / 2)).image (fun m => 2 * m), PSieve.gt r := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hc : Nat.Coprime 2 m := (PSieve.mem_sq hm).2.2.symm
    rw [PSieve.gt_mul hc, gt_two, one_mul]
  have hdisj : Disjoint (PSieve.sq 2 R) ((PSieve.sq 2 (R / 2)).image (fun m => 2 * m)) := by
    rw [Finset.disjoint_left]
    intro r hr hr'
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hr'
    have hcop := (PSieve.mem_sq hr).2.2
    have h2 : 2 ∣ Nat.gcd (2 * m) 2 := Nat.dvd_gcd (dvd_mul_right 2 m) dvd_rfl
    rw [hcop] at h2
    exact absurd (Nat.le_of_dvd one_pos h2) (by norm_num)
  rw [himg, ← Finset.sum_union hdisj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun r _ _ => PSieve.gt_nonneg r
  intro r hr
  rcases Finset.mem_union.mp hr with h | h
  · obtain ⟨h1, h2, -⟩ := PSieve.mem_sq h
    exact PSieve.sq_mem h1 h2 (Nat.coprime_one_right r)
  · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨h1, h2, -⟩ := PSieve.mem_sq hm
    refine PSieve.sq_mem (by omega) ?_ (Nat.coprime_one_right _)
    push_cast
    linarith

/-- **`HC.CharpyGap` from `eq:charpas`, PROVED**: on `(4·10⁷, 355³)` both `R` and `R/2` lie in
`[200, 1.6·10⁸]`, so `G(R) ≥ G₂(R) + G₂(R/2) ≥ log R + 1.661 − (log 2)/2 ≥ log R + 1.312`. -/
theorem charpyGap_of_charpas (h : CharpasCited) : HC.CharpyGap := by
  intro R h1 h2
  have hA := (h R (by linarith) (by linarith)).1
  have hB := (h (R / 2) (by linarith) (by linarith)).1
  have hS := gQ_two_add_le R
  have hlog : Real.log (R / 2) = Real.log R - Real.log 2 := Real.log_div (by linarith) two_ne_zero
  rw [hlog] at hB
  have := Real.log_two_lt_d9
  linarith

/-- **`HC.CharpyLo` with no uncited gap**: `HC.charpyLo_of` fed `charpyGap_of_charpas`. -/
theorem charpyLo_of_charpas (ch : HC.CharpyCited) (cp : CharpasCited) (hm : CY.Malito)
    (hce : 1.3325822 ≤ CY.cE) : HC.CharpyLo :=
  HC.charpyLo_of ch (charpyGap_of_charpas cp) hm hce

end Principia.Common.TernaryGoldbach.HX
