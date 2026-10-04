/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MainBogusSpine
import Principia.Common.TernaryGoldbach.EBoundRS
import Principia.Common.Mertens.Mertens

set_option autoImplicit false

/-!
# The two coefficient links of `lem:bogus` PROVED, and `eq:rala` (odd `n`) PROVED

`MainBogusSpine` (`MPMB`) reduced the main term of the corrected `lem:bogus` (book `typeI.tex`
1576-1660) to two statements about `c = μ_{≤U} ∗ Λ_{≤V}` (`MPBG.cUV`). Both are theorems here,
from literature already cited in the headline (`MPc.Grara` = Granville–Ramaré Lemma 10.2,
`EB.RS62Thm12` = Rosser–Schoenfeld 1962 Thm 12) and Mathlib, with no new hypothesis:

```
 RalaOdd       ← RS62Thm12          (ralaOdd_of: Stirling via Mathlib's `stirlingSeq`,
                                     ∑ Λ(d)⌊N/d⌋ = log N!, ψ(N) < 1.03883N, the n = 2,4,8
                                     terms; N ≤ 7 by a count, every odd term ≤ (log N)/3)
 CoefMainBound ← Grara, RS62Thm12   (coefMainBound_of)
 CoefErrBound  ← RS62Thm12          (coefErrBound_of)
 MainBogusEta2C, SecI2At ← HC.CameloGridCited, HC.WollustCited, Grara, RS62Thm12
                                    (mainBogusC_of_lit, secI2At_of_lit)
```

**`CoefMainBound`.** Regroup `d = uv` (`coef_regroup`, the hyperbola interchange
`sum_antidiag`); for fixed `v`, with `r = q/(q, v)`, `q ∣ uv ⟺ r ∣ u` (`dvd_mul_iff_div_gcd`) and
`∑_{u ≤ Y, r ∣ u} μ(u)f(u)/u = (μ(r)f(r)/r)·muS(2r, Y/r)` (`sum_dvd_moeb`), so the `u`-sum is
`≤ 1/r = (q, v)/q` by `eq:grara` (`inner_main_le`). Then `∑_{v ≤ V odd} Λ(v)(q, v)/v ≤ log q +
∑_{v ≤ V odd} Λ(v)/v` (`gcd_sum_le`: the `v ∣ q` terms give `∑_{v ∣ q} Λ(v) = log q`; every other
prime power maps injectively to `v/(q, v)`, a power of the same prime). The book's last display
writes this sum with `(v, q) = 1`; it is the `p ∣ q` prime powers, and the bound is unchanged.

**`CoefErrBound`.** `|c(d)| ≤ ∑_{uv = d} 1_{u ≤ U}Λ_{≤V}(v)` (`err_regroup_le`). For `(v, q) = 1`
the `u` are odd multiples of `q` up to `M/v`, summing to `≤ (M/v)²/4q + 3M/4v`
(`odd_mult_sum_le`); otherwise all odd `u ≤ U`, summing to `≤ (U + 1)²/4` (`inner_err_le`). The
first group gives `M² log V/4q + (3/4)·1.03883·MV` (`RalaOdd`, `RS62Thm12`, and
`1.03883 ≤ c₄`); the second gives `(3/8)(U + 1)²V log q` from
`∑_{p^α ≤ V} p^α ≤ (3/2)V` for odd `p` (`sum_powers_le`) and `∑_{p ∣ q} log p ≤ log q`
(`sum_nonCoprime_le`) -- the CORRECTED `eq:etoile` exactly as `MPMB.CoefErrBound` states it.

`BogusSpine.coef_abs_le` (`|c(m)| ≤ log m`) was already PROVED in `BogusSpine.lean`.
-/

namespace Principia.Common.TernaryGoldbach.MPCB

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius
open Principia.Common.TernaryGoldbach.MT Principia.Common.TernaryGoldbach.MPc
  Principia.Common.TernaryGoldbach.MPBG Principia.Common.TernaryGoldbach.MPMB

/-- `log N! ≤ N log N − N + 1 + (log N)/2` (Stirling: `stirlingSeq N ≤ stirlingSeq 1`). -/
theorem log_factorial_le (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N.factorial : ℝ) ≤
      N * Real.log N - N + 1 + Real.log N / 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hanti : Stirling.stirlingSeq N ≤ Real.exp 1 / √2 := by
    have := Stirling.stirlingSeq'_antitone (Nat.zero_le (N - 1))
    simp only [Function.comp_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hN, zero_add,
      Stirling.stirlingSeq_one] at this
    exact this
  unfold Stirling.stirlingSeq at hanti
  have hD : 0 < √(2 * (N : ℝ)) * ((N : ℝ) / Real.exp 1) ^ N := by positivity
  rw [div_le_iff₀ hD] at hanti
  have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have e1 : Real.exp 1 / √2 * (√(2 * (N : ℝ)) * ((N : ℝ) / Real.exp 1) ^ N) =
      Real.exp 1 * √(N : ℝ) * ((N : ℝ) / Real.exp 1) ^ N := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have : (0 : ℝ) < √2 := by positivity
    field_simp
  rw [e1] at hanti
  have hl := Real.log_le_log hfac hanti
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_sqrt hNr.le, Real.log_pow, Real.log_div hNr.ne' (by positivity),
    Real.log_exp] at hl
  linarith

/-- `N·∑_{n ≤ N} Λ(n)/n ≤ log N! + ψ(N)`. -/
theorem mul_sum_le (N : ℕ) :
    (N : ℝ) * ∑ n ∈ Ioc 0 N, Λ n / n ≤ Real.log (N.factorial : ℝ) + Chebyshev.psi N := by
  have h1 := Mertens.sum_log_eq_log_factorial (N : ℝ)
  have h2 := @Mertens.sum_log_eq_sum_mangoldt (N : ℝ)
  rw [Nat.floor_natCast] at h1 h2
  unfold Chebyshev.psi
  rw [Nat.floor_natCast, ← h1, h2, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  have hd0 : (0 : ℝ) < d := by
    have := (Finset.mem_Ioc.mp hd).1
    exact_mod_cast this
  have hfl : (N : ℝ) / d ≤ ⌊(N : ℝ) / d⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  have hL := @vonMangoldt_nonneg d
  calc (N : ℝ) * (Λ d / d) = Λ d * ((N : ℝ) / d) := by ring
    _ ≤ Λ d * (⌊(N : ℝ) / d⌋₊ + 1) := mul_le_mul_of_nonneg_left hfl hL
    _ = Λ d * ⌊(N : ℝ) / d⌋₊ + Λ d := by ring

/-- The even part `n ∈ {2, 4, 8}`: `7(log 2)/8`. -/
theorem even_part (N : ℕ) (hN : 8 ≤ N) :
    7 / 8 * Real.log 2 ≤ ∑ n ∈ (Icc 1 N).filter (fun n => ¬ Odd n), Λ n / n := by
  have hsub : ({2, 4, 8} : Finset ℕ) ⊆ (Icc 1 N).filter (fun n => ¬ Odd n) := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.not_odd_iff_even]
    rcases hn with rfl | rfl | rfl <;> refine ⟨⟨by omega, by omega⟩, by decide⟩
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
    div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
  have h2 : Λ 2 = Real.log 2 := by
    rw [vonMangoldt_apply_prime Nat.prime_two]; norm_num
  have h4 : Λ 4 = Real.log 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, vonMangoldt_apply_pow (by norm_num), h2]
  have h8 : Λ 8 = Real.log 2 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, vonMangoldt_apply_pow (by norm_num), h2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    h2, h4, h8]
  push_cast
  linarith

/-- **`eq:rala`, odd `n`, at an integer `N`**, from `EB.RS62Thm12`. -/
theorem ralaOdd_nat (h12 : EB.RS62Thm12) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ (Icc 1 N).filter Odd, Λ n / n ≤ Real.log N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  rcases lt_or_ge N 8 with h7 | h8
  · -- small `N`: every odd `n ≥ 3` contributes at most `log N / 3`, and there are at most 3
    have hterm : ∀ n ∈ (Icc 1 N).filter Odd,
        Λ n / n ≤ if 3 ≤ n then Real.log N / 3 else 0 := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨h1, hnN⟩, hodd⟩ := hn
      split_ifs with h3
      · have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast h3
        have hLn : Λ n ≤ Real.log N :=
          vonMangoldt_le_log.trans (Real.log_le_log (by linarith) (by exact_mod_cast hnN))
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        nlinarith [@vonMangoldt_nonneg n]
      · have : n = 1 := by obtain ⟨k, hk⟩ := hodd; omega
        subst this
        simp
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hc : (((Icc 1 N).filter Odd).filter (fun n => 3 ≤ n)).card ≤ 3 := by
      interval_cases N <;> decide
    have hc' : ((((Icc 1 N).filter Odd).filter (fun n => 3 ≤ n)).card : ℝ) ≤ 3 := by
      exact_mod_cast hc
    nlinarith
  · have hN8 : (8 : ℝ) ≤ N := by exact_mod_cast h8
    have hfull := mul_sum_le N
    have hfac := log_factorial_le N hN
    have hpsi : Chebyshev.psi N < 1.03883 * N := h12 N (by linarith)
    have hsplit := Finset.sum_filter_add_sum_filter_not (Icc 1 N) Odd (fun n => Λ n / n)
    have hev := even_part N h8
    have hl1 : Real.log N ≤ N - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
    have hIoc : Ioc 0 N = Icc 1 N := rfl
    rw [hIoc, ← hsplit] at hfull
    set A := ∑ n ∈ (Icc 1 N).filter Odd, Λ n / n
    set B := ∑ n ∈ (Icc 1 N).filter (fun n => ¬ Odd n), Λ n / n
    have hNB : (N : ℝ) * (7 / 8 * Real.log 2) ≤ N * B :=
      mul_le_mul_of_nonneg_left hev (by linarith)
    have key : (N : ℝ) * A ≤ N * Real.log N := by nlinarith
    exact le_of_mul_le_mul_left key (by linarith)

/-- **`MPMB.RalaOdd`, PROVED from `EB.RS62Thm12`.** -/
theorem ralaOdd_of (h12 : EB.RS62Thm12) : RalaOdd := by
  intro V hV
  have hN : 1 ≤ ⌊V⌋₊ := Nat.le_floor (by exact_mod_cast hV)
  refine (ralaOdd_nat h12 ⌊V⌋₊ hN).trans ?_
  exact Real.log_le_log (by exact_mod_cast hN) (Nat.floor_le (by linarith))

/-- `q ∣ uv ⟺ q/(q, v) ∣ u`. -/
theorem dvd_mul_iff_div_gcd (q u v : ℕ) (hq : 1 ≤ q) :
    q ∣ u * v ↔ q / Nat.gcd q v ∣ u := by
  have hg : 0 < Nat.gcd q v := Nat.gcd_pos_of_pos_left v (by omega)
  have hcop := Nat.coprime_div_gcd_div_gcd hg
  have eq : Nat.gcd q v * (q / Nat.gcd q v) = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left q v)
  have ev : Nat.gcd q v * (v / Nat.gcd q v) = v := Nat.mul_div_cancel' (Nat.gcd_dvd_right q v)
  generalize Nat.gcd q v = g at hg hcop eq ev ⊢
  have e2 : q ∣ u * v ↔ g * (q / g) ∣ g * (u * (v / g)) := by
    rw [eq, show g * (u * (v / g)) = u * (g * (v / g)) by ring, ev]
  rw [e2, Nat.mul_dvd_mul_iff_left hg]
  exact hcop.dvd_mul_right

/-- The hyperbola interchange `∑_{n ≤ N} ∑_{uv = n} F(u, v) = ∑_{v ≤ N} ∑_{u ≤ N, uv ≤ N}`. -/
theorem sum_antidiag (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ n ∈ Ioc 0 N, ∑ x ∈ n.divisorsAntidiagonal, F x.1 x.2 =
      ∑ v ∈ Ioc 0 N, ∑ u ∈ Ioc 0 N, if u * v ≤ N then F u v else 0 := by
  trans ∑ n ∈ Ioc 0 N, ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = n, F x.1 x.2
  · refine sum_congr rfl fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]
  · simp_rw [sum_filter]
    rw [sum_comm, sum_product_right]
    refine sum_congr rfl fun v hv => sum_congr rfl fun u hu => ?_
    rw [Finset.sum_ite_eq]
    simp only [mem_Ioc] at hu hv ⊢
    have h0 : 0 < u * v := Nat.mul_pos hu.1 hv.1
    by_cases h : u * v ≤ N
    · rw [if_pos ⟨h0, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]

/-- The `u = rw` term: `μ(rw)f(rw)/(rw) = (μ(r)f(r)/r)·1_{(w,2r)=1} μ(w)/w`. -/
theorem moeb_term (r w : ℕ) :
    ((μ (r * w) : ℤ) : ℝ) * fOdd (r * w) / ((r * w : ℕ) : ℝ) =
      ((μ r : ℤ) : ℝ) * fOdd r / r *
        (if Nat.Coprime w (2 * r) then ((μ w : ℤ) : ℝ) / w else 0) := by
  split_ifs with hc
  · obtain ⟨h2, hr⟩ := Nat.coprime_mul_iff_right.mp hc
    have hodd : fOdd w = 1 := by
      rw [fOdd_apply, if_pos (Nat.odd_iff.mp (Nat.coprime_two_right.mp h2))]
    rw [isMultiplicative_moebius.map_mul_of_coprime hr.symm, fOdd_mul, hodd]
    push_cast
    ring
  · by_cases hcr : Nat.Coprime r w
    · have h2 : ¬ Nat.Coprime w 2 := fun h2 => hc (Nat.coprime_mul_iff_right.mpr ⟨h2, hcr.symm⟩)
      have hev : fOdd w = 0 := by
        rw [fOdd_apply, if_neg]
        intro h1
        exact h2 (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr h1))
      rw [fOdd_mul, hev]
      simp
    · have : μ (r * w) = 0 :=
        moebius_eq_zero_of_not_squarefree fun hsq => hcr (Nat.squarefree_mul_iff.mp hsq).1
      rw [this]
      simp

/-- **`∑_{u ≤ Y, r ∣ u} μ(u)f(u)/u = (μ(r)f(r)/r)·muS(2r, Y/r)`.** -/
theorem sum_dvd_moeb (r Y : ℕ) (hr : 1 ≤ r) :
    ∑ u ∈ (Ioc 0 Y).filter (fun u => r ∣ u), ((μ u : ℤ) : ℝ) * fOdd u / u =
      ((μ r : ℤ) : ℝ) * fOdd r / r * muS (2 * r) ((Y / r : ℕ) : ℝ) := by
  have himg : (Ioc 0 Y).filter (fun u => r ∣ u) = (Ioc 0 (Y / r)).image (fun w => r * w) := by
    ext u
    simp only [mem_filter, mem_Ioc, mem_image]
    constructor
    · rintro ⟨⟨h0, hY⟩, ⟨w, rfl⟩⟩
      refine ⟨w, ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at h0), ?_⟩, rfl⟩
      rw [Nat.le_div_iff_mul_le (by omega)]
      linarith [mul_comm r w]
    · rintro ⟨w, ⟨h0, hw⟩, rfl⟩
      rw [Nat.le_div_iff_mul_le (by omega)] at hw
      exact ⟨⟨Nat.mul_pos (by omega) h0, by linarith [mul_comm r w]⟩, dvd_mul_right r w⟩
  rw [himg, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by omega) h)]
  unfold muS
  rw [Nat.floor_natCast, sum_filter, mul_sum]
  exact sum_congr rfl fun w _ => moeb_term r w

/-- **`|∑_{u ≤ Y, r ∣ u} μ(u)f(u)/u| ≤ 1/r`**, from `eq:grara` at `2r`. -/
theorem abs_sum_dvd_moeb_le (hG : Grara) (r Y : ℕ) (hr : 1 ≤ r) :
    |∑ u ∈ (Ioc 0 Y).filter (fun u => r ∣ u), ((μ u : ℤ) : ℝ) * fOdd u / u| ≤ 1 / r := by
  rw [sum_dvd_moeb r Y hr, abs_mul]
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hm : |((μ r : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
  have h1 : |((μ r : ℤ) : ℝ) * fOdd r / r| ≤ 1 / r := by
    rw [abs_div, abs_mul, abs_of_nonneg (fOdd_nonneg r), abs_of_pos hrR]
    apply div_le_div_of_nonneg_right _ hrR.le
    calc |((μ r : ℤ) : ℝ)| * fOdd r ≤ 1 * 1 :=
          mul_le_mul hm (fOdd_le_one r) (fOdd_nonneg r) zero_le_one
      _ = 1 := one_mul 1
  have h2 := hG (2 * r) ((Y / r : ℕ) : ℝ) (by omega)
  calc |((μ r : ℤ) : ℝ) * fOdd r / r| * |muS (2 * r) ((Y / r : ℕ) : ℝ)| ≤ 1 / r * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 1 / r := mul_one _

/-- `gcd(q, p^k) = p^{v_p(q)}` when `p^k ∤ q`. -/
theorem gcd_prime_pow (p k q : ℕ) (hp : p.Prime) (hq : q ≠ 0) (hnd : ¬ p ^ k ∣ q) :
    Nat.gcd q (p ^ k) = p ^ (q.factorization p) := by
  obtain ⟨i, hik, hi⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right q (p ^ k))
  have hk : q.factorization p < k := by
    by_contra h
    exact hnd ((hp.pow_dvd_iff_le_factorization hq).mpr (not_lt.mp h))
  have h1 : i ≤ q.factorization p := by
    rw [← hp.pow_dvd_iff_le_factorization hq, ← hi]
    exact Nat.gcd_dvd_left q (p ^ k)
  have h2 : p ^ (q.factorization p) ∣ Nat.gcd q (p ^ k) :=
    Nat.dvd_gcd (Nat.ordProj_dvd q p) (pow_dvd_pow p hk.le)
  rw [hi] at h2 ⊢
  have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h2
  rw [le_antisymm h1 this]

/-- For a prime power `v ∤ q`: `w = v/(q, v)` is a prime power of the same prime, `w ≠ 1`. -/
theorem div_gcd_facts (q v : ℕ) (hq : q ≠ 0) (hv : IsPrimePow v) (hnd : ¬ v ∣ q) :
    ∃ p k j : ℕ, p.Prime ∧ v = p ^ k ∧ v / Nat.gcd q v = p ^ j ∧ 0 < j ∧
      Nat.gcd q v = p ^ (q.factorization p) := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff v).mp hv
  have hg := gcd_prime_pow p k q hp hq hnd
  obtain ⟨j, hjk, hj⟩ :=
    (Nat.dvd_prime_pow hp).mp (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right q (p ^ k)))
  refine ⟨p, k, j, hp, rfl, hj, Nat.pos_of_ne_zero ?_, hg⟩
  rintro rfl
  apply hnd
  have hgpos : 0 < Nat.gcd q (p ^ k) := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hq)
  have := Nat.div_mul_cancel (Nat.gcd_dvd_right q (p ^ k))
  rw [hj, pow_zero, one_mul] at this
  rw [← this]
  exact Nat.gcd_dvd_left q (p ^ k)

/-- **The `gcd` sum** (book `typeI.tex` 1617-1630, with the book's misprinted `(v, q) = 1` in the
last sum read as `p ∣ q`): `∑_{v ≤ K odd} Λ(v)(q, v)/v ≤ log q + ∑_{v ≤ K odd} Λ(v)/v`. -/
theorem gcd_sum_le (q K : ℕ) (hq : 1 ≤ q) :
    ∑ v ∈ (Icc 1 K).filter Odd, Λ v * (Nat.gcd q v : ℝ) / v ≤
      Real.log q + ∑ v ∈ (Icc 1 K).filter Odd, Λ v / v := by
  have hq0 : q ≠ 0 := by omega
  set A := (Icc 1 K).filter Odd with hA
  rw [← Finset.sum_filter_add_sum_filter_not A (fun v => v ∣ q)]
  refine add_le_add ?_ ?_
  · -- `v ∣ q`: the term is `Λ(v)`, and `∑_{v ∣ q} Λ(v) = log q`
    rw [← vonMangoldt_sum]
    have hsub : A.filter (fun v => v ∣ q) ⊆ q.divisors := by
      intro v hv
      exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hv).2, hq0⟩
    refine le_trans (le_of_eq (sum_congr rfl fun v hv => ?_))
      (sum_le_sum_of_subset_of_nonneg hsub fun v _ _ => vonMangoldt_nonneg)
    have hvq := (mem_filter.mp hv).2
    have hv1 : 1 ≤ v := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hv).1).1).1
    rw [Nat.gcd_eq_right hvq]
    have : (0 : ℝ) < v := by exact_mod_cast hv1
    field_simp
  · -- `v ∤ q`: the term is `Λ(w)/w` for `w = v/(q, v)`, an injective map into `A`
    set B := A.filter (fun v => ¬ v ∣ q)
    rw [← Finset.sum_filter_of_ne (p := IsPrimePow) (fun v _ h => by
      by_contra hpp
      exact h (by rw [vonMangoldt_eq_zero_iff.mpr hpp, zero_mul, zero_div]))]
    set C := B.filter IsPrimePow
    have hmem : ∀ v ∈ C, IsPrimePow v ∧ ¬ v ∣ q ∧ v ∈ A := by
      intro v hv
      have h1 := mem_filter.mp hv
      have h2 := mem_filter.mp h1.1
      exact ⟨h1.2, h2.2, h2.1⟩
    have hterm : ∀ v ∈ C, Λ v * (Nat.gcd q v : ℝ) / v =
        Λ (v / Nat.gcd q v) / ((v / Nat.gcd q v : ℕ) : ℝ) := by
      intro v hv
      obtain ⟨hpp, hnd, -⟩ := hmem v hv
      obtain ⟨p, k, j, hp, hvk, hw, hj, -⟩ := div_gcd_facts q v hq0 hpp hnd
      have hk : k ≠ 0 := by
        rintro rfl
        exact hnd (by rw [hvk, pow_zero]; exact one_dvd q)
      have hL : Λ v = Λ (v / Nat.gcd q v) := by
        rw [hw, vonMangoldt_apply_pow hj.ne', hvk, vonMangoldt_apply_pow hk]
      have hg0 : 0 < Nat.gcd q v := Nat.gcd_pos_of_pos_left _ (by omega)
      have hdiv := Nat.div_mul_cancel (Nat.gcd_dvd_right q v)
      have hgR : (0 : ℝ) < Nat.gcd q v := by exact_mod_cast hg0
      have hwpos : 0 < v / Nat.gcd q v := by rw [hw]; exact pow_pos hp.pos j
      have hwR : (0 : ℝ) < (v / Nat.gcd q v : ℕ) := by exact_mod_cast hwpos
      have hvR : (v : ℝ) = ((v / Nat.gcd q v : ℕ) : ℝ) * Nat.gcd q v := by
        exact_mod_cast hdiv.symm
      rw [hL, hvR]
      field_simp
    rw [sum_congr rfl hterm]
    have hinj : Set.InjOn (fun v => v / Nat.gcd q v) C := by
      intro v1 hv1 v2 hv2 heq
      obtain ⟨hpp1, hnd1, -⟩ := hmem v1 hv1
      obtain ⟨hpp2, hnd2, -⟩ := hmem v2 hv2
      obtain ⟨p1, k1, j1, hp1, hv1k, hw1, hj1, hg1⟩ := div_gcd_facts q v1 hq0 hpp1 hnd1
      obtain ⟨p2, k2, j2, hp2, hv2k, hw2, hj2, hg2⟩ := div_gcd_facts q v2 hq0 hpp2 hnd2
      simp only at heq
      have hpe : p1 = p2 := by
        have h1 : p1 ∣ p2 ^ j2 := by
          rw [← hw2, ← heq, hw1]
          exact dvd_pow_self p1 hj1.ne'
        exact (Nat.prime_dvd_prime_iff_eq hp1 hp2).mp (hp1.dvd_of_dvd_pow h1)
      subst hpe
      have e1 := Nat.div_mul_cancel (Nat.gcd_dvd_right q v1)
      have e2 := Nat.div_mul_cancel (Nat.gcd_dvd_right q v2)
      rw [← e1, ← e2, heq, hg1, hg2]
    rw [← sum_image (f := fun w => Λ w / (w : ℝ)) hinj]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun w _ _ =>
      div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
    intro w hw
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
    obtain ⟨hpp, hnd, hvA⟩ := hmem v hv
    obtain ⟨p, k, j, hp, hvk, hwj, hj, -⟩ := div_gcd_facts q v hq0 hpp hnd
    have hvA' := mem_filter.mp hvA
    have hvI := mem_Icc.mp hvA'.1
    have hwpos : 0 < v / Nat.gcd q v := by rw [hwj]; exact pow_pos hp.pos j
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hwpos, (Nat.div_le_self _ _).trans hvI.2⟩, ?_⟩
    exact Odd.of_dvd_nat hvA'.2 (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right q v))

/-- `aU U u = 1_{u ≤ ⌊U⌋} μ(u)`. -/
theorem aU_apply (U : ℝ) (u : ℕ) :
    aU U u = if u ≤ ⌊U⌋₊ then ((μ u : ℤ) : ℝ) else 0 := by
  unfold aU
  rw [Principia.Common.Goldbach.MinSum.truncate_apply, intCoe_apply]

/-- `bV V v = 1_{v ≤ ⌊V⌋} Λ(v)`. -/
theorem bV_apply (V : ℝ) (v : ℕ) : bV V v = if v ≤ ⌊V⌋₊ then Λ v else 0 := by
  unfold bV
  rw [Principia.Common.Goldbach.MinSum.truncate_apply]

theorem bV_nonneg (V : ℝ) (v : ℕ) : 0 ≤ bV V v := by
  rw [bV_apply]
  split_ifs
  · exact vonMangoldt_nonneg
  · exact le_refl 0

/-- **The `v`-`u` regrouping**: the `d ≤ N`, `q ∣ d` sum of `c(d)·w(d)` as a double sum over
`uv ≤ N`. -/
theorem coef_regroup (U V : ℝ) (q N : ℕ) (w : ℕ → ℝ) :
    ∑ d ∈ (Icc 1 N).filter (fun d => q ∣ d), cUV U V d * w d =
      ∑ v ∈ Ioc 0 N, ∑ u ∈ Ioc 0 N, if u * v ≤ N then
        (if q ∣ u * v then aU U u * bV V v * w (u * v) else 0) else 0 := by
  rw [← sum_antidiag N (fun u v => if q ∣ u * v then aU U u * bV V v * w (u * v) else 0),
    sum_filter]
  refine sum_congr rfl fun d _ => ?_
  unfold cUV
  rw [mul_apply]
  split_ifs with hqd
  · rw [sum_mul]
    refine sum_congr rfl fun x hx => ?_
    have hx' := (Nat.mem_divisorsAntidiagonal.mp hx).1
    rw [hx', if_pos hqd]
  · symm
    refine sum_eq_zero fun x hx => ?_
    have hx' := (Nat.mem_divisorsAntidiagonal.mp hx).1
    rw [hx', if_neg hqd]

/-- The inner `u`-sum of the main term, for fixed `v`: `|·| ≤ (b(v)f(v)/v)·(q, v)/q`. -/
theorem inner_main_le (hG : Grara) (U V : ℝ) (q N v : ℕ) (hq : 1 ≤ q) (hv : 1 ≤ v) :
    |∑ u ∈ Ioc 0 N, (if u * v ≤ N then (if q ∣ u * v then aU U u * bV V v *
        (fOdd (u * v) / ((u * v : ℕ) : ℝ)) else 0) else 0)| ≤
      bV V v * fOdd v / v * ((Nat.gcd q v : ℝ) / q) := by
  have hg0 : 0 < Nat.gcd q v := Nat.gcd_pos_of_pos_left _ (by omega)
  have hr1 : 1 ≤ q / Nat.gcd q v := Nat.div_pos (Nat.gcd_le_left v (by omega)) hg0
  set Y := min ⌊U⌋₊ (N / v) with hY
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have heq : ∑ u ∈ Ioc 0 N, (if u * v ≤ N then (if q ∣ u * v then aU U u * bV V v *
        (fOdd (u * v) / ((u * v : ℕ) : ℝ)) else 0) else 0) =
      bV V v * fOdd v / v * ∑ u ∈ (Ioc 0 Y).filter (fun u => q / Nat.gcd q v ∣ u),
        ((μ u : ℤ) : ℝ) * fOdd u / u := by
    have hYN : Y ≤ N := (min_le_right _ _).trans (Nat.div_le_self _ _)
    have hset : (Ioc 0 Y).filter (fun u => q / Nat.gcd q v ∣ u) =
        (Ioc 0 N).filter (fun u => u ≤ Y ∧ q / Nat.gcd q v ∣ u) := by
      ext u
      simp only [mem_filter, mem_Ioc]
      constructor
      · rintro ⟨⟨h0, h1⟩, h2⟩
        exact ⟨⟨h0, h1.trans hYN⟩, h1, h2⟩
      · rintro ⟨⟨h0, -⟩, h1, h2⟩
        exact ⟨⟨h0, h1⟩, h2⟩
    rw [hset, sum_filter, mul_sum]
    refine sum_congr rfl fun u hu => ?_
    have hu1 : 1 ≤ u := (mem_Ioc.mp hu).1
    have huR : (0 : ℝ) < u := by exact_mod_cast hu1
    have hcond1 : u ≤ Y ↔ u ≤ ⌊U⌋₊ ∧ u * v ≤ N := by
      rw [hY, le_min_iff, Nat.le_div_iff_mul_le (by omega)]
    have hcond2 : q ∣ u * v ↔ q / Nat.gcd q v ∣ u := dvd_mul_iff_div_gcd q u v hq
    by_cases h1 : u * v ≤ N
    · rw [if_pos h1]
      by_cases h2 : q / Nat.gcd q v ∣ u
      · rw [if_pos (hcond2.mpr h2)]
        by_cases h3 : u ≤ ⌊U⌋₊
        · rw [if_pos ⟨hcond1.mpr ⟨h3, h1⟩, h2⟩, aU_apply, if_pos h3, fOdd_mul]
          push_cast
          field_simp
        · rw [if_neg (fun h => h3 (hcond1.mp h.1).1), aU_apply, if_neg h3]
          simp
      · rw [if_neg (fun h => h2 (hcond2.mp h)), if_neg (fun h => h2 h.2), mul_zero]
    · rw [if_neg h1, if_neg (fun h => h1 (hcond1.mp h.1).2), mul_zero]
  rw [heq, abs_mul]
  have hb : 0 ≤ bV V v * fOdd v / v :=
    div_nonneg (mul_nonneg (bV_nonneg V v) (fOdd_nonneg v)) hvR.le
  rw [abs_of_nonneg hb]
  refine mul_le_mul_of_nonneg_left ((abs_sum_dvd_moeb_le hG _ Y hr1).trans (le_of_eq ?_)) hb
  have hqe : (q : ℝ) = (Nat.gcd q v : ℝ) * ((q / Nat.gcd q v : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left q v)).symm
  have hgR : (0 : ℝ) < Nat.gcd q v := by exact_mod_cast hg0
  have hrR : (0 : ℝ) < ((q / Nat.gcd q v : ℕ) : ℝ) := by exact_mod_cast hr1
  rw [hqe]
  field_simp

/-- `∑_{v ≤ N} (b(v)f(v)/v)·φ(v) ≤ ∑_{v ≤ V odd} Λ(v)φ(v)/v` for `φ ≥ 0`. -/
theorem sum_bV_le (V : ℝ) (N : ℕ) (φ : ℕ → ℝ) (hφ : ∀ v, 0 ≤ φ v) :
    ∑ v ∈ Ioc 0 N, bV V v * fOdd v / v * φ v ≤
      ∑ v ∈ (Icc 1 ⌊V⌋₊).filter Odd, Λ v * φ v / v := by
  have hterm : ∀ v ∈ Ioc 0 N, bV V v * fOdd v / v * φ v =
      if v ∈ (Icc 1 ⌊V⌋₊).filter Odd then Λ v * φ v / v else 0 := by
    intro v hv
    have hv1 : 1 ≤ v := (mem_Ioc.mp hv).1
    rw [bV_apply, fOdd_apply]
    simp only [mem_filter, mem_Icc, Nat.odd_iff]
    by_cases h1 : v ≤ ⌊V⌋₊ <;> by_cases h2 : v % 2 = 1 <;> simp [h1, h2, hv1]
    ring
  rw [sum_congr rfl hterm, ← sum_filter]
  exact sum_le_sum_of_subset_of_nonneg (fun v hv => (mem_filter.mp hv).2)
    fun v _ _ => div_nonneg (mul_nonneg vonMangoldt_nonneg (hφ v)) (Nat.cast_nonneg _)

/-- **`MPMB.CoefMainBound`, PROVED** from `eq:grara` (`MPc.Grara`) and `EB.RS62Thm12`
(through `RalaOdd`). -/
theorem coefMainBound_of (hG : Grara) (h12 : EB.RS62Thm12) : CoefMainBound := by
  intro U V M q hq hU hV
  set N := ⌊M⌋₊
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsum : ∑ d ∈ (Icc 1 N).filter (fun d => q ∣ d), cUV U V d * fOdd d / d =
      ∑ d ∈ (Icc 1 N).filter (fun d => q ∣ d), cUV U V d * (fOdd d / d) :=
    sum_congr rfl fun d _ => by ring
  rw [hsum, coef_regroup U V q N (fun d => fOdd d / d)]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum fun v hv => inner_main_le hG U V q N v hq (mem_Ioc.mp hv).1).trans ?_
  refine (sum_bV_le V N (fun v => (Nat.gcd q v : ℝ) / q) fun v => by positivity).trans ?_
  have hgs := gcd_sum_le q ⌊V⌋₊ hq
  have hra := ralaOdd_of h12 V hV
  have e : ∑ v ∈ (Icc 1 ⌊V⌋₊).filter Odd, Λ v * ((Nat.gcd q v : ℝ) / q) / v =
      (∑ v ∈ (Icc 1 ⌊V⌋₊).filter Odd, Λ v * (Nat.gcd q v : ℝ) / v) / q := by
    rw [sum_div]
    exact sum_congr rfl fun v _ => by ring
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith) hqR.le

/-- `∑_{j < J} (2j + 1) = J²`. -/
theorem sum_odd_range (J : ℕ) : ∑ j ∈ range J, (2 * (j : ℝ) + 1) = (J : ℝ) ^ 2 := by
  induction J with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- **Odd multiples of `q` up to `L`** (book `typeI.tex` 1641, CORRECTED form): their sum is
`qJ²` with `2qJ ≤ L + q`, hence `≤ (L + q)²/4q`, and `≤ L²/4q + 3L/4`. -/
theorem odd_mult_sum_le (q L : ℕ) (hq : 1 ≤ q) :
    ∑ u ∈ (Ioc 0 L).filter (fun u => Odd u ∧ q ∣ u), (u : ℝ) ≤
        ((L : ℝ) + q) ^ 2 / (4 * q) ∧
      ∑ u ∈ (Ioc 0 L).filter (fun u => Odd u ∧ q ∣ u), (u : ℝ) ≤
        (L : ℝ) ^ 2 / (4 * q) + 3 / 4 * L := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hLR : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  rcases Nat.even_or_odd q with hev | hodd
  · -- `q` even: no odd multiples
    have hempty : (Ioc 0 L).filter (fun u => Odd u ∧ q ∣ u) = ∅ := by
      ext u
      simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _ hu hqu
      exact (Nat.not_even_iff_odd.mpr hu) (hev.trans_dvd hqu)
    rw [hempty, sum_empty]
    constructor <;> positivity
  · set J := (L / q + 1) / 2 with hJ
    have himg : (Ioc 0 L).filter (fun u => Odd u ∧ q ∣ u) =
        (range J).image (fun j => q * (2 * j + 1)) := by
      ext u
      simp only [mem_filter, mem_Ioc, mem_image, mem_range]
      constructor
      · rintro ⟨⟨h0, hL⟩, hu, ⟨m, rfl⟩⟩
        have hm : Odd m := (Nat.odd_mul.mp hu).2
        obtain ⟨j, rfl⟩ := hm
        refine ⟨j, ?_, rfl⟩
        have : 2 * j + 1 ≤ L / q := by
          rw [Nat.le_div_iff_mul_le (by omega)]
          linarith [mul_comm q (2 * j + 1)]
        omega
      · rintro ⟨j, hj, rfl⟩
        have : 2 * j + 1 ≤ L / q := by omega
        rw [Nat.le_div_iff_mul_le (by omega)] at this
        refine ⟨⟨Nat.mul_pos (by omega) (by omega), by linarith [mul_comm q (2 * j + 1)]⟩,
          Nat.odd_mul.mpr ⟨hodd, by exact ⟨j, by ring⟩⟩, dvd_mul_right _ _⟩
    have hinj : Set.InjOn (fun j => q * (2 * j + 1)) (range J : Set ℕ) := by
      intro a _ b _ h
      have := Nat.eq_of_mul_eq_mul_left (by omega) h
      omega
    rw [himg, sum_image hinj]
    have hval : ∑ j ∈ range J, ((q * (2 * j + 1) : ℕ) : ℝ) = q * (J : ℝ) ^ 2 := by
      rw [← sum_odd_range J, mul_sum]
      refine sum_congr rfl fun j _ => ?_
      push_cast
      ring
    rw [hval]
    have h2J : 2 * (J : ℝ) ≤ (L : ℝ) / q + 1 := by
      have h1 : 2 * J ≤ L / q + 1 := by omega
      have h2 : ((L / q : ℕ) : ℝ) ≤ (L : ℝ) / q := Nat.cast_div_le
      have h3 : (2 * (J : ℝ)) ≤ ((L / q : ℕ) : ℝ) + 1 := by exact_mod_cast h1
      linarith
    have h2qJ : 2 * q * (J : ℝ) ≤ L + q := by
      have := mul_le_mul_of_nonneg_left h2J hqR.le
      rw [mul_add, mul_div_cancel₀ _ hqR.ne'] at this
      linarith
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hA : q * (J : ℝ) ^ 2 ≤ ((L : ℝ) + q) ^ 2 / (4 * q) := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul h2qJ h2qJ (by positivity) (by positivity)
      nlinarith
    refine ⟨hA, ?_⟩
    rcases Nat.eq_zero_or_pos J with h0 | hpos
    · have hJz : (J : ℝ) = 0 := by exact_mod_cast h0
      calc (q : ℝ) * (J : ℝ) ^ 2 = 0 := by rw [hJz]; ring
        _ ≤ _ := by positivity
    · have hqL : (q : ℝ) ≤ L := by
        have : 1 ≤ L / q := by omega
        have : q ≤ L := by
          have := (Nat.le_div_iff_mul_le (by omega)).mp this
          linarith
        exact_mod_cast this
      refine hA.trans ?_
      rw [div_le_iff₀ (by positivity)]
      have : ((L : ℝ) ^ 2 / (4 * q) + 3 / 4 * L) * (4 * q) = L ^ 2 + 3 * q * L := by
        field_simp
      rw [this]
      nlinarith

/-- Distinct powers of `p ≥ 3`, all `≤ B`, sum to at most `(3/2)B`. -/
theorem sum_powers_le (p : ℕ) (hp : 3 ≤ p) (S : Finset ℕ) (hS : ∀ x ∈ S, ∃ k : ℕ, x = p ^ k)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x ∈ S, (x : ℝ) ≤ B) :
    ∑ x ∈ S, (x : ℝ) ≤ 3 / 2 * B := by
  induction S using Finset.induction_on_max generalizing B with
  | empty => simp only [sum_empty]; positivity
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [sum_insert has]
    have haB : (a : ℝ) ≤ B := hB a (mem_insert_self a s)
    obtain ⟨j, hj⟩ := hS a (mem_insert_self a s)
    have hsmall : ∀ x ∈ s, (x : ℝ) ≤ (a : ℝ) / 3 := by
      intro x hx
      obtain ⟨i, hi⟩ := hS x (mem_insert_of_mem hx)
      have hxa := hlt x hx
      rw [hi, hj] at hxa
      have hij : i < j := (Nat.pow_lt_pow_iff_right (by omega)).mp hxa
      have h1 : p ^ (i + 1) ≤ p ^ j := Nat.pow_le_pow_right (by omega) hij
      have h2 : 3 * x ≤ a := by
        rw [hi, hj]
        calc 3 * p ^ i ≤ p * p ^ i := Nat.mul_le_mul_right _ hp
          _ = p ^ (i + 1) := by ring
          _ ≤ p ^ j := h1
      have : (3 : ℝ) * x ≤ a := by exact_mod_cast h2
      linarith
    have := ih (fun x hx => hS x (mem_insert_of_mem hx)) ((a : ℝ) / 3) (by positivity) hsmall
    linarith

/-- **The `p ∣ q` part of `eq:etoile`, CORRECTED**: `∑_{v ≤ K odd, (v, q) > 1} Λ(v)v
≤ (3/2)K log q` (book: `∑_{p^α ≤ V} p^α ≤ (3/2)V` for odd `p`, and `∑_{p ∣ q} log p ≤ log q`). -/
theorem sum_nonCoprime_le (q K : ℕ) (hq : 1 ≤ q) :
    ∑ v ∈ ((Icc 1 K).filter Odd).filter (fun v => ¬ Nat.Coprime q v), Λ v * v ≤
      3 / 2 * K * Real.log q := by
  have hq0 : q ≠ 0 := by omega
  set A := ((Icc 1 K).filter Odd).filter (fun v => ¬ Nat.Coprime q v)
  rw [← Finset.sum_filter_of_ne (p := IsPrimePow) (fun v _ h => by
    by_contra hpp
    exact h (by rw [vonMangoldt_eq_zero_iff.mpr hpp, zero_mul]))]
  set C := A.filter IsPrimePow
  have hmem : ∀ v ∈ C, IsPrimePow v ∧ Odd v ∧ ¬ Nat.Coprime q v ∧ 1 ≤ v ∧ v ≤ K := by
    intro v hv
    have h1 := mem_filter.mp hv
    have h2 := mem_filter.mp h1.1
    have h3 := mem_filter.mp h2.1
    exact ⟨h1.2, h3.2, h2.2, (mem_Icc.mp h3.1).1, (mem_Icc.mp h3.1).2⟩
  have hmaps : ∀ v ∈ C, Nat.minFac v ∈ q.primeFactors := by
    intro v hv
    obtain ⟨hpp, -, hnc, -, -⟩ := hmem v hv
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff v).mp hpp
    rw [hp.pow_minFac hk.ne']
    refine Nat.mem_primeFactors.mpr ⟨hp, ?_, hq0⟩
    by_contra hpq
    exact hnc (Nat.Coprime.pow_right k ((Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq))))
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hfib : ∀ p ∈ q.primeFactors,
      ∑ v ∈ C.filter (fun v => Nat.minFac v = p), Λ v * v ≤ Real.log p * (3 / 2 * K) := by
    intro p hpq
    have hp := Nat.prime_of_mem_primeFactors hpq
    have hterm : ∀ v ∈ C.filter (fun v => Nat.minFac v = p), Λ v * v = Real.log p * v := by
      intro v hv
      have h1 := mem_filter.mp hv
      rw [vonMangoldt_apply, if_pos (hmem v h1.1).1, h1.2]
    rw [sum_congr rfl hterm, ← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
    rcases (C.filter (fun v => Nat.minFac v = p)).eq_empty_or_nonempty with he | ⟨v0, hv0⟩
    · rw [he, sum_empty]; positivity
    · -- `p` is odd: it divides the odd `v0`
      have h0 := mem_filter.mp hv0
      obtain ⟨-, hodd0, -, h10, -⟩ := hmem v0 h0.1
      have hp3 : 3 ≤ p := by
        have hpd : p ∣ v0 := h0.2 ▸ Nat.minFac_dvd v0
        have hpodd : Odd p := Odd.of_dvd_nat hodd0 hpd
        have h2 := hp.two_le
        rcases hpodd with ⟨t, ht⟩
        omega
      refine sum_powers_le p hp3 _ ?_ K hK0 ?_
      · intro x hx
        have h1 := mem_filter.mp hx
        obtain ⟨hpp, -, -, -, -⟩ := hmem x h1.1
        obtain ⟨p', k, hp', hk, hx'⟩ := (isPrimePow_nat_iff x).mp hpp
        have : p' = p := by rw [← h1.2, ← hx', hp'.pow_minFac hk.ne']
        exact ⟨k, by rw [← hx', this]⟩
      · intro x hx
        obtain ⟨-, -, -, -, hxK⟩ := hmem x (mem_filter.mp hx).1
        exact_mod_cast hxK
  refine (sum_le_sum hfib).trans ?_
  rw [← sum_mul]
  have hlog : ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
    rw [← Real.log_prod (fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).pos
      positivity)]
    have hdvd := Nat.prod_primeFactors_dvd q
    have hle : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd (by omega) hdvd
    have hpos : 0 < ∏ p ∈ q.primeFactors, p :=
      prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    have : (∏ p ∈ q.primeFactors, (p : ℝ)) = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
      push_cast; rfl
    rw [this]
    exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
  nlinarith

/-- `|aU U u| ≤ 1_{u ≤ ⌊U⌋}`. -/
theorem abs_aU_le (U : ℝ) (u : ℕ) : |aU U u| ≤ if u ≤ ⌊U⌋₊ then 1 else 0 := by
  rw [aU_apply]
  split_ifs
  · exact_mod_cast abs_moebius_le_one
  · simp

/-- The error-term `d`-sum is at most the regrouped `|μ_{≤U}| ∗ Λ_{≤V}` double sum. -/
theorem err_regroup_le (U V : ℝ) (q N : ℕ) :
    ∑ d ∈ (Icc 1 N).filter (fun d => q ∣ d), |cUV U V d| * fOdd d * d ≤
      ∑ v ∈ Ioc 0 N, ∑ u ∈ Ioc 0 N, if u * v ≤ N then (if q ∣ u * v then
        |aU U u| * bV V v * (fOdd (u * v) * ((u * v : ℕ) : ℝ)) else 0) else 0 := by
  rw [← sum_antidiag N (fun u v => if q ∣ u * v then
    |aU U u| * bV V v * (fOdd (u * v) * ((u * v : ℕ) : ℝ)) else 0), sum_filter]
  refine sum_le_sum fun d _ => ?_
  split_ifs with hqd
  · have e : ∑ x ∈ d.divisorsAntidiagonal, (if q ∣ x.1 * x.2 then
        |aU U x.1| * bV V x.2 * (fOdd (x.1 * x.2) * ((x.1 * x.2 : ℕ) : ℝ)) else 0) =
        (∑ x ∈ d.divisorsAntidiagonal, |aU U x.1| * bV V x.2) * (fOdd d * d) := by
      rw [sum_mul]
      refine sum_congr rfl fun x hx => ?_
      have hx' := (Nat.mem_divisorsAntidiagonal.mp hx).1
      rw [hx', if_pos hqd]
    rw [e, mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_
      (mul_nonneg (fOdd_nonneg d) (Nat.cast_nonneg d))
    unfold cUV
    rw [mul_apply]
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun x _ => ?_))
    rw [abs_mul, abs_of_nonneg (bV_nonneg V x.2)]
  · refine le_of_eq (sum_eq_zero fun x hx => ?_).symm
    have hx' := (Nat.mem_divisorsAntidiagonal.mp hx).1
    rw [hx', if_neg hqd]

/-- The inner `u`-sum of the error term, for fixed `v`: `(v, q) = 1` gives the odd multiples of
`q` up to `M/v`; otherwise all odd `u ≤ U`. -/
theorem inner_err_le (U V M : ℝ) (q v : ℕ) (hq : 1 ≤ q) (hv : 1 ≤ v) (hU : 0 ≤ U)
    (hM : 0 ≤ M) :
    ∑ u ∈ Ioc 0 ⌊M⌋₊, (if u * v ≤ ⌊M⌋₊ then (if q ∣ u * v then
        |aU U u| * bV V v * (fOdd (u * v) * ((u * v : ℕ) : ℝ)) else 0) else 0) ≤
      bV V v * fOdd v / v * ((v : ℝ) ^ 2 * (if Nat.Coprime q v then
        (M / v) ^ 2 / (4 * q) + 3 / 4 * (M / v) else (U + 1) ^ 2 / 4)) := by
  set N := ⌊M⌋₊
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hb : 0 ≤ bV V v * fOdd v * v :=
    mul_nonneg (mul_nonneg (bV_nonneg V v) (fOdd_nonneg v)) hvR.le
  have hite : ∀ (T : Finset ℕ) (u : ℕ), 0 ≤ bV V v * fOdd v * v * (if u ∈ T then (u : ℝ) else 0) :=
    fun T u => mul_nonneg hb (by split_ifs <;> positivity)
  -- the generic pointwise step: an odd `u` in `T` with `|aU U u| ≤ 1`
  have hstep : ∀ (T : Finset ℕ) (u : ℕ), (Odd u → u ∈ T) → |aU U u| ≤ 1 →
      |aU U u| * bV V v * (fOdd (u * v) * ((u * v : ℕ) : ℝ)) ≤
        bV V v * fOdd v * v * (if u ∈ T then (u : ℝ) else 0) := by
    intro T u hT ha
    rw [fOdd_mul]
    push_cast
    rcases Nat.even_or_odd u with he | ho
    · have : fOdd u = 0 := by
        rw [fOdd_apply, if_neg]
        rw [Nat.even_iff] at he
        omega
      rw [this, zero_mul, zero_mul, mul_zero]
      exact hite T u
    · have hf : fOdd u = 1 := by
        rw [fOdd_apply, if_pos (Nat.odd_iff.mp ho)]
      rw [if_pos (hT ho), hf]
      have hX : 0 ≤ bV V v * fOdd v * ((u : ℝ) * v) :=
        mul_nonneg (mul_nonneg (bV_nonneg V v) (fOdd_nonneg v)) (by positivity)
      have ha0 := abs_nonneg (aU U u)
      nlinarith
  have hfin : ∀ T : Finset ℕ, ∑ u ∈ Ioc 0 N, bV V v * fOdd v * v * (if u ∈ T then (u : ℝ) else 0)
      ≤ bV V v * fOdd v * v * ∑ u ∈ T, (u : ℝ) := by
    intro T
    rw [← mul_sum, ← sum_filter]
    exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg
      (fun u hu => (mem_filter.mp hu).2) fun u _ _ => Nat.cast_nonneg u) hb
  by_cases hc : Nat.Coprime q v
  · rw [if_pos hc]
    set T := (Ioc 0 (N / v)).filter (fun u => Odd u ∧ q ∣ u)
    have hpt : ∀ u ∈ Ioc 0 N, (if u * v ≤ N then (if q ∣ u * v then
        |aU U u| * bV V v * (fOdd (u * v) * ((u * v : ℕ) : ℝ)) else 0) else 0) ≤
        bV V v * fOdd v * v * (if u ∈ T then (u : ℝ) else 0) := by
      intro u hu
      by_cases h1 : u * v ≤ N
      · rw [if_pos h1]
        by_cases h2 : q ∣ u * v
        · rw [if_pos h2]
          have hqu : q ∣ u := hc.dvd_mul_right.mp h2
          have huN : u ≤ N / v := (Nat.le_div_iff_mul_le (by omega)).mpr h1
          refine hstep T u (fun ho => mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hu).1, huN⟩,
            ho, hqu⟩) ?_
          refine (abs_aU_le U u).trans ?_
          split_ifs <;> norm_num
        · rw [if_neg h2]; exact hite T u
      · rw [if_neg h1]; exact hite T u
    refine (sum_le_sum hpt).trans ((hfin T).trans ?_)
    have hodd := (odd_mult_sum_le q (N / v) hq).2
    have hL : ((N / v : ℕ) : ℝ) ≤ M / v :=
      Nat.cast_div_le.trans (div_le_div_of_nonneg_right (Nat.floor_le hM) hvR.le)
    have hL0 : (0 : ℝ) ≤ ((N / v : ℕ) : ℝ) := Nat.cast_nonneg _
    have mono : ((N / v : ℕ) : ℝ) ^ 2 / (4 * q) + 3 / 4 * ((N / v : ℕ) : ℝ) ≤
        (M / v) ^ 2 / (4 * q) + 3 / 4 * (M / v) := by
      have := pow_le_pow_left₀ hL0 hL 2
      have h4 : ((N / v : ℕ) : ℝ) ^ 2 / (4 * q) ≤ (M / v) ^ 2 / (4 * q) :=
        div_le_div_of_nonneg_right this (by positivity)
      linarith
    calc bV V v * fOdd v * v * ∑ u ∈ T, (u : ℝ)
        ≤ bV V v * fOdd v * v * ((M / v) ^ 2 / (4 * q) + 3 / 4 * (M / v)) :=
          mul_le_mul_of_nonneg_left (hodd.trans mono) hb
      _ = bV V v * fOdd v / v * ((v : ℝ) ^ 2 * ((M / v) ^ 2 / (4 * q) + 3 / 4 * (M / v))) := by
          field_simp
  · rw [if_neg hc]
    set T := (Ioc 0 ⌊U⌋₊).filter (fun u => Odd u ∧ 1 ∣ u)
    have hpt : ∀ u ∈ Ioc 0 N, (if u * v ≤ N then (if q ∣ u * v then
        |aU U u| * bV V v * (fOdd (u * v) * ((u * v : ℕ) : ℝ)) else 0) else 0) ≤
        bV V v * fOdd v * v * (if u ∈ T then (u : ℝ) else 0) := by
      intro u hu
      by_cases h1 : u * v ≤ N
      · rw [if_pos h1]
        by_cases h2 : q ∣ u * v
        · rw [if_pos h2]
          by_cases h3 : u ≤ ⌊U⌋₊
          · refine hstep T u (fun ho => mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hu).1, h3⟩,
              ho, one_dvd u⟩) ?_
            refine (abs_aU_le U u).trans ?_
            rw [if_pos h3]
          · have : aU U u = 0 := by rw [aU_apply, if_neg h3]
            rw [this, abs_zero, zero_mul, zero_mul]
            exact hite T u
        · rw [if_neg h2]; exact hite T u
      · rw [if_neg h1]; exact hite T u
    refine (sum_le_sum hpt).trans ((hfin T).trans ?_)
    have hodd := (odd_mult_sum_le 1 ⌊U⌋₊ (le_refl 1)).1
    have hfl : (⌊U⌋₊ : ℝ) ≤ U := Nat.floor_le hU
    have mono : ((⌊U⌋₊ : ℝ) + ((1 : ℕ) : ℝ)) ^ 2 / (4 * ((1 : ℕ) : ℝ)) ≤ (U + 1) ^ 2 / 4 := by
      push_cast
      have : ((⌊U⌋₊ : ℝ) + 1) ^ 2 ≤ (U + 1) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      linarith
    calc bV V v * fOdd v * v * ∑ u ∈ T, (u : ℝ)
        ≤ bV V v * fOdd v * v * ((U + 1) ^ 2 / 4) :=
          mul_le_mul_of_nonneg_left (hodd.trans mono) hb
      _ = bV V v * fOdd v / v * ((v : ℝ) ^ 2 * ((U + 1) ^ 2 / 4)) := by
          field_simp

/-- **`MPMB.CoefErrBound`, PROVED** from `EB.RS62Thm12` (`ψ(V) < 1.03883V` and, through
`RalaOdd`, `eq:rala`). -/
theorem coefErrBound_of (h12 : EB.RS62Thm12) : CoefErrBound := by
  intro U V M q hq hU hV hM
  set N := ⌊M⌋₊
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set B : ℕ → ℝ := fun v => if Nat.Coprime q v then
    (M / v) ^ 2 / (4 * q) + 3 / 4 * (M / v) else (U + 1) ^ 2 / 4 with hBdef
  have hB0 : ∀ v : ℕ, 0 ≤ (v : ℝ) ^ 2 * B v := fun v => by
    rw [hBdef]
    simp only
    split_ifs <;> positivity
  refine (err_regroup_le U V q N).trans ?_
  refine (sum_le_sum fun v hv => inner_err_le U V M q v hq (mem_Ioc.mp hv).1 (by linarith)
    hM).trans ?_
  refine (sum_bV_le V N (fun v => (v : ℝ) ^ 2 * B v) hB0).trans ?_
  set W := (Icc 1 ⌊V⌋₊).filter Odd with hW
  rw [← sum_filter_add_sum_filter_not W (fun v => Nat.Coprime q v)]
  have hvpos : ∀ v ∈ W, (0 : ℝ) < v := fun v hv => by
    have := (mem_Icc.mp (mem_filter.mp hv).1).1
    exact_mod_cast this
  have ecop : ∑ v ∈ W.filter (fun v => Nat.Coprime q v), Λ v * ((v : ℝ) ^ 2 * B v) / v =
      M ^ 2 / (4 * q) * ∑ v ∈ W.filter (fun v => Nat.Coprime q v), Λ v / v +
        3 * M / 4 * ∑ v ∈ W.filter (fun v => Nat.Coprime q v), Λ v := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun v hv => ?_
    have h1 := mem_filter.mp hv
    have hv0 := hvpos v h1.1
    rw [hBdef]
    simp only
    rw [if_pos h1.2]
    field_simp
  have encop : ∑ v ∈ W.filter (fun v => ¬ Nat.Coprime q v), Λ v * ((v : ℝ) ^ 2 * B v) / v =
      (U + 1) ^ 2 / 4 * ∑ v ∈ W.filter (fun v => ¬ Nat.Coprime q v), Λ v * v := by
    rw [mul_sum]
    refine sum_congr rfl fun v hv => ?_
    have h1 := mem_filter.mp hv
    have hv0 := hvpos v h1.1
    rw [hBdef]
    simp only
    rw [if_neg h1.2]
    field_simp
  rw [ecop, encop]
  -- the three inputs
  have hra := ralaOdd_of h12 V hV
  have hsub : W.filter (fun v => Nat.Coprime q v) ⊆ W := filter_subset _ _
  have hr1 : ∑ v ∈ W.filter (fun v => Nat.Coprime q v), Λ v / v ≤ Real.log V :=
    (sum_le_sum_of_subset_of_nonneg hsub fun v _ _ =>
      div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)).trans hra
  have hpsi : ∑ v ∈ W.filter (fun v => Nat.Coprime q v), Λ v ≤ 1.03883 * V := by
    have h := h12 V (by linarith)
    unfold Chebyshev.psi at h
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ fun v _ _ => vonMangoldt_nonneg) h.le
    intro v hv
    exact (mem_filter.mp (mem_filter.mp hv).1).1
  have hnc := sum_nonCoprime_le q ⌊V⌋₊ hq
  have hfl : (⌊V⌋₊ : ℝ) ≤ V := Nat.floor_le (by linarith)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hlV : 0 ≤ Real.log V := Real.log_nonneg hV
  have hU1 : 0 ≤ (U + 1) ^ 2 / 4 := by positivity
  have hM2 : 0 ≤ M ^ 2 / (4 * q) := by positivity
  have t1 : M ^ 2 / (4 * q) * ∑ v ∈ W.filter (fun v => Nat.Coprime q v), Λ v / v ≤
      M ^ 2 * Real.log V / (4 * q) := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left hr1 hM2 |>.trans (le_of_eq (by ring))
  have t2 : 3 * M / 4 * ∑ v ∈ W.filter (fun v => Nat.Coprime q v), Λ v ≤
      3 * MPG.c4 / 4 * M * V := by
    have := mul_le_mul_of_nonneg_left hpsi (by positivity : (0 : ℝ) ≤ 3 * M / 4)
    have hc4 : (1.03883 : ℝ) ≤ MPG.c4 := by unfold MPG.c4; norm_num
    have hMV : 0 ≤ M * V := mul_nonneg hM (by linarith)
    have : 3 * M / 4 * (1.03883 * V) ≤ 3 * MPG.c4 / 4 * M * V := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc4) hMV]
    linarith
  have t3 : (U + 1) ^ 2 / 4 * ∑ v ∈ W.filter (fun v => ¬ Nat.Coprime q v), Λ v * v ≤
      3 / 8 * (U + 1) ^ 2 * V * Real.log q := by
    have h1 := mul_le_mul_of_nonneg_left hnc hU1
    have h2 : 3 / 2 * (⌊V⌋₊ : ℝ) * Real.log q ≤ 3 / 2 * V * Real.log q := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 hU1
    nlinarith
  linarith

/-- **`MPBD.MainBogusEta2C` from cited inputs only**: the two cited computer checks, `eq:grara`
and `EB.RS62Thm12` (the coefficient links are now theorems). -/
theorem mainBogusC_of_lit (hG : HC.CameloGridCited) (hW : HC.WollustCited) (hgr : Grara)
    (h12 : EB.RS62Thm12) : MPBD.MainBogusEta2C :=
  mainBogusC_of_cited hG hW (coefMainBound_of hgr h12) (coefErrBound_of h12)

/-- **`MPc.SecI2At` from cited inputs only** (`MPMB.secI2At_of_coef` with both coefficient links
discharged). -/
theorem secI2At_of_lit (hG : HC.CameloGridCited) (hW : HC.WollustCited) (hgr : Grara)
    (h12 : EB.RS62Thm12) : SecI2At :=
  secI2At_of_coef hG hW (coefMainBound_of hgr h12) (coefErrBound_of h12)

end Principia.Common.TernaryGoldbach.MPCB
