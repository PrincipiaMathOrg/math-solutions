/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Chebyshev's dyadic lower bound `∑_{n < p ≤ 2n} log p ≥ (log 4 / 6)·n`

Erdős' proof of Bertrand's postulate (Mathlib's `Bertrand.lean`) bounds the central binomial
coefficient by splitting its prime factorisation; keeping the primes of `(n, 2n]` instead of
assuming there are none gives

  `C(2n, n) ≤ (2n)^{⌊√(2n)⌋} · 4^{⌊2n/3⌋} · ∏_{n < p ≤ 2n} p`   (`centralBinom_le_mul_prod_primes`),

and with `4ⁿ < n·C(2n, n)` this yields
`∑_{n < p ≤ 2n} log p ≥ n log 4 / 3 − log n − ⌊√(2n)⌋ log(2n)` (`sum_log_primes_dyadic_ge`), hence
`≥ (log 4 / 6)·n` for `n ≥ 12 005 000` and, for real `t`, `∑_{⌊t⌋ < p ≤ ⌊2t⌋} log p ≥ (log 4/12)·t`
(`sum_log_primes_dyadic_real`). This is the principal-character input of the dyadic
Siegel–Walfisz lower bound (`Principia.Common.SW.Dyadic`); no prime number theorem is used.
-/

set_option autoImplicit false

namespace Principia.Common.SW

/-- **Erdős' factorisation bound, keeping the large primes**: for `n > 2`,
`C(2n, n) ≤ (2n)^{⌊√(2n)⌋} · 4^{⌊2n/3⌋} · ∏_{n < p ≤ 2n, p prime} p`. -/
theorem centralBinom_le_mul_prod_primes (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
      ∏ p ∈ (Finset.Ico (n + 1) (2 * n + 1)).filter Nat.Prime, p := by
  let f : ℕ → ℕ := fun x => x ^ n.centralBinom.factorization x
  have hsplit : n.centralBinom = (∏ x ∈ Finset.range (2 * n / 3 + 1), f x) *
      ∏ x ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1), f x := by
    rw [Finset.prod_range_mul_prod_Ico f (by omega)]
    exact n.prod_pow_factorization_centralBinom.symm
  have n_pos : 0 < n := by omega
  have n2_pos : 1 ≤ 2 * n := by omega
  -- the primes `≤ 2n/3`: exactly the bound in Mathlib's `centralBinom_le_of_no_bertrand_prime`
  have h1 : ∏ x ∈ Finset.range (2 * n / 3 + 1), f x ≤
      (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by
    let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
    have hS : ∏ x ∈ S, f x = ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := by
      refine Finset.prod_filter_of_ne fun p _ h => ?_
      contrapose h; dsimp only [f]
      rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom h, _root_.pow_zero]
    rw [← hS, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
      · exact Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)
      have : (Finset.Icc 1 (Nat.sqrt (2 * n))).card = Nat.sqrt (2 * n) := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
      rw [Finset.prod_const]
      refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
    · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)
      refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
      exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  -- the range `(2n/3, 2n]`: nothing in `(2n/3, n]`, multiplicity `≤ 1` above `n`
  have h2 : ∏ x ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1), f x ≤
      ∏ x ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1), (if Nat.Prime x ∧ n < x then x else 1) := by
    apply Finset.prod_le_prod'
    intro x hx
    rw [Finset.mem_Ico] at hx
    by_cases hp : Nat.Prime x
    · by_cases hnx : n < x
      · rw [if_pos ⟨hp, hnx⟩]
        have hsq : 2 * n < x ^ 2 := by nlinarith
        exact (pow_right_mono₀ hp.one_lt.le (Nat.factorization_choose_le_one hsq)).trans
          (pow_one x).le
      · rw [if_neg (fun h => hnx h.2)]
        have h0 : n.centralBinom.factorization x = 0 :=
          Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn (by omega) (by omega)
        change x ^ n.centralBinom.factorization x ≤ 1
        rw [h0, pow_zero]
    · rw [if_neg (fun h => hp h.1)]
      change x ^ n.centralBinom.factorization x ≤ 1
      rw [Nat.factorization_eq_zero_of_not_prime _ hp, pow_zero]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one] at h2
  have hset : (Finset.Ico (2 * n / 3 + 1) (2 * n + 1)).filter (fun x => Nat.Prime x ∧ n < x) =
      (Finset.Ico (n + 1) (2 * n + 1)).filter Nat.Prime := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨_, hb⟩, hp, hnx⟩
      exact ⟨⟨by omega, hb⟩, hp⟩
    · rintro ⟨⟨ha, hb⟩, hp⟩
      exact ⟨⟨by omega, hb⟩, hp, by omega⟩
  rw [hset] at h2
  rw [hsplit]
  exact Nat.mul_le_mul h1 h2

/-- `∑_{n < p ≤ 2n} log p ≥ n log 4 / 3 − log n − ⌊√(2n)⌋·log(2n)` for `n ≥ 4`. -/
theorem sum_log_primes_dyadic_ge (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 / 3 - Real.log n - (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * n) ≤
      ∑ p ∈ (Finset.Ico (n + 1) (2 * n + 1)).filter Nat.Prime, Real.log p := by
  have h4 := Nat.four_pow_lt_mul_centralBinom n hn
  have hb := centralBinom_le_mul_prod_primes n (by omega)
  have hP0 : 0 < ∏ p ∈ (Finset.Ico (n + 1) (2 * n + 1)).filter Nat.Prime, p :=
    Finset.prod_pos (fun p hp => (Finset.mem_filter.1 hp).2.pos)
  have hlogP : Real.log ((∏ p ∈ (Finset.Ico (n + 1) (2 * n + 1)).filter Nat.Prime, p : ℕ) : ℝ) =
      ∑ p ∈ (Finset.Ico (n + 1) (2 * n + 1)).filter Nat.Prime, Real.log p := by
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (Finset.mem_filter.1 hp).2.pos.ne'
  have hnat : 4 ^ n < n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
      ∏ p ∈ (Finset.Ico (n + 1) (2 * n + 1)).filter Nat.Prime, p) :=
    lt_of_lt_of_le h4 (Nat.mul_le_mul_left n hb)
  set P : ℕ := ∏ p ∈ (Finset.Ico (n + 1) (2 * n + 1)).filter Nat.Prime, p with hPdef
  set s : ℕ := Nat.sqrt (2 * n) with hsdef
  set k : ℕ := 2 * n / 3 with hkdef
  have hreal : (4 : ℝ) ^ n < (n : ℝ) * ((2 * (n : ℝ)) ^ s * (4 : ℝ) ^ k * (P : ℝ)) := by
    exact_mod_cast hnat
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hP0' : (0 : ℝ) < P := by exact_mod_cast hP0
  have hlt := Real.log_lt_log (by positivity) hreal
  rw [Real.log_pow, Real.log_mul hn0.ne' (by positivity), Real.log_mul (by positivity) hP0'.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlt
  have hk : (k : ℝ) ≤ 2 * (n : ℝ) / 3 := by
    have := Nat.cast_div_le (m := 2 * n) (n := 3) (α := ℝ)
    push_cast at this
    exact this
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hkl : (k : ℝ) * Real.log 4 ≤ 2 * (n : ℝ) / 3 * Real.log 4 :=
    mul_le_mul_of_nonneg_right hk hlog4.le
  rw [← hlogP]
  linarith

/-- For `n ≥ 12 005 000`: `∑_{n < p ≤ 2n} log p ≥ (log 4 / 6)·n`. -/
theorem sum_log_primes_dyadic_ge' (n : ℕ) (hn : 12005000 ≤ n) :
    Real.log 4 / 6 * n ≤ ∑ p ∈ (Finset.Ico (n + 1) (2 * n + 1)).filter Nat.Prime, Real.log p := by
  have hmain := sum_log_primes_dyadic_ge n (by omega)
  have hn' : (12005000 : ℝ) ≤ n := by exact_mod_cast hn
  set x : ℝ := 2 * (n : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity
  set w : ℝ := x ^ ((1 : ℝ) / 4) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg hx0 _
  have hw4 : w ^ 4 = x := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  -- `w ≥ 70`
  have hx70 : (70 : ℝ) ^ 4 ≤ x := by rw [hx]; nlinarith
  have hw70 : 70 ≤ w := by
    by_contra hcon
    have hlt : w < 70 := lt_of_not_ge hcon
    have := pow_lt_pow_left₀ hlt hw0 (by norm_num : (4 : ℕ) ≠ 0)
    linarith
  -- `⌊√(2n)⌋ ≤ w²`
  have hs : ((Nat.sqrt (2 * n) : ℕ) : ℝ) ≤ w ^ 2 := by
    have hsq : ((Nat.sqrt (2 * n) : ℕ) : ℝ) ^ 2 ≤ (w ^ 2) ^ 2 := by
      rw [← pow_mul, hw4, hx]
      exact_mod_cast Nat.sqrt_le' (2 * n)
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  -- `log(2n) ≤ 4w` and `log n ≤ 4w`
  have hlog2n : Real.log x ≤ 4 * w := by
    have := Real.log_le_rpow_div hx0 (by norm_num : (0 : ℝ) < 1 / 4)
    rw [← hw] at this
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn : Real.log n ≤ 4 * w := by
    have := Real.log_le_log hn0 (show (n : ℝ) ≤ x by rw [hx]; linarith)
    linarith
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by rw [hx]; linarith)
  have hsl : ((Nat.sqrt (2 * n) : ℕ) : ℝ) * Real.log x ≤ w ^ 2 * (4 * w) :=
    mul_le_mul hs hlog2n hlogx0 (by positivity)
  have hlog4 : 1.38 < Real.log 4 := by
    have h2 := Real.log_two_gt_d9
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  -- `8w³ ≤ (log 4 / 12)·w⁴ = (log 4 / 6)·n`
  have hpoly : 4 * w ^ 3 + 4 * w ≤ Real.log 4 / 6 * n := by
    have hn2 : (n : ℝ) = w ^ 4 / 2 := by rw [hw4, hx]; ring
    rw [hn2]
    have hw3 : 4 * w ≤ 4 * w ^ 3 := by nlinarith
    have hw4' : 8 * w ^ 3 ≤ 1.38 / 12 * w ^ 4 := by nlinarith [pow_nonneg hw0 3]
    nlinarith [pow_nonneg hw0 4]
  linarith

/-- **Chebyshev's dyadic lower bound, real form**: for `t ≥ 12 005 001`,
`∑_{⌊t⌋ < p ≤ ⌊2t⌋, p prime} log p ≥ (log 4 / 12)·t`. -/
theorem sum_log_primes_dyadic_real (t : ℝ) (ht : 12005001 ≤ t) :
    Real.log 4 / 12 * t ≤
      ∑ p ∈ (Finset.Ico (⌊t⌋₊ + 1) (⌊2 * t⌋₊ + 1)).filter Nat.Prime, Real.log p := by
  have ht0 : 0 ≤ t := by linarith
  set n := ⌊t⌋₊ with hndef
  have hn : 12005000 ≤ n := Nat.le_floor (by push_cast; linarith)
  have hnt : t < n + 1 := Nat.lt_floor_add_one t
  have h2n : 2 * n ≤ ⌊2 * t⌋₊ := by
    apply Nat.le_floor
    push_cast
    have := Nat.floor_le ht0
    linarith
  have hsub : (Finset.Ico (n + 1) (2 * n + 1)).filter Nat.Prime ⊆
      (Finset.Ico (n + 1) (⌊2 * t⌋₊ + 1)).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp ⊢
    exact ⟨⟨hp.1.1, by omega⟩, hp.2⟩
  have hmono : ∑ p ∈ (Finset.Ico (n + 1) (2 * n + 1)).filter Nat.Prime, Real.log (p : ℝ) ≤
      ∑ p ∈ (Finset.Ico (n + 1) (⌊2 * t⌋₊ + 1)).filter Nat.Prime, Real.log (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => Real.log_nonneg
      (show (1 : ℝ) ≤ (p : ℝ) by exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt.le))
  have hbase := sum_log_primes_dyadic_ge' n hn
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hn2 : t / 2 ≤ (n : ℝ) := by
    have : (12005001 : ℝ) ≤ t := ht
    linarith
  have : Real.log 4 / 12 * t ≤ Real.log 4 / 6 * n := by nlinarith
  linarith

end Principia.Common.SW
