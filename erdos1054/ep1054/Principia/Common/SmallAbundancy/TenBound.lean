/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.SmallAbundancy.Criterion
import Principia.Common.SmallAbundancy.LargePrime

set_option autoImplicit false

/-!
# `σ(m)/m < 10` for every `1 ≤ m ≤ 10^119`

The colossally-abundant bound of `Principia.Common.SmallAbundancy.Criterion` at the single
parameter `ε = 1/N`, `N = 1480`. The comparison number is
`M₀ = 2^10 3^6 5^4 7^3 (11·13·17·19)^2 · ∏_{23 ≤ p ≤ 263} p ≈ 1.529·10^119`
(`caM`, the colossally abundant number of parameter `1/1480`), and
`σ(m)/m ≤ (σ(M₀)/M₀) (m/M₀)^{1/1480} ≤ 9.9095` for `m ≤ 10^119`
(`σ(M₀)/M₀ = 9.91229…`; the bound `(σ(M₀)^N 10^{119} / M₀^{N+1})^{1/N} = 9.909451…`).

Everything is exact natural-number arithmetic, checked by the kernel (`decide +kernel`):
* `caList_check` — for each of the 57 primes `p ≤ 269`, `W(p^k) ≤ W(p^{e_p})` for `k` below a
  tail start `A_p ≤ 12`, and the tail inequality at `A_p` (`W(q) = σ(q)^N / q^{N+1}`, cleared);
* `caList_cover` — every prime `< 271` is in the list; primes `≥ 271` are handled uniformly by
  `pow_le_pred_pow_mul` (`2·1480 ≤ 11·270`);
* `caList_final` — `σ(M₀)^{1480} · 10^{119} < 10^{1480} · M₀^{1481}` (numbers of `~175 000`
  digits; the kernel's GMP arithmetic takes under a second).

The single-parameter bound needs the exponent structure: the crude
`∏_{p ≤ 283} p/(p − 1) ≈ 10.23` does not give `< 10`. Numerics re-checked in exact integer
arithmetic (Python) before formalisation: every inequality above, and the bound `9.909451…`.

**Headline:** `sigma_lt_ten_mul : 1 ≤ m → m ≤ 10^119 → σ(m) < 10 m`, and its real form
`sigma_div_lt_ten`.
-/

namespace Principia.Common.SmallAbundancy

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The triples `(p, e_p, A_p)` for the 57 primes `p ≤ 269`: `e_p` maximises
`σ(p^k)^{1480} / p^{1481 k}` (so `M₀ = ∏ p^{e_p}`), and `A_p` is where the tail bound takes over. -/
def caList : List (ℕ × ℕ × ℕ) :=
  [(2, 10, 12), (3, 6, 7), (5, 4, 5), (7, 3, 4), (11, 2, 3), (13, 2, 3), (17, 2, 3), (19, 2, 3),
   (23, 1, 2), (29, 1, 2), (31, 1, 2), (37, 1, 2), (41, 1, 2), (43, 1, 2), (47, 1, 2), (53, 1, 2),
   (59, 1, 2), (61, 1, 2), (67, 1, 2), (71, 1, 2), (73, 1, 2), (79, 1, 2), (83, 1, 2), (89, 1, 2),
   (97, 1, 2), (101, 1, 2), (103, 1, 2), (107, 1, 2), (109, 1, 2), (113, 1, 2), (127, 1, 2),
   (131, 1, 2), (137, 1, 2), (139, 1, 2), (149, 1, 2), (151, 1, 2), (157, 1, 2), (163, 1, 2),
   (167, 1, 2), (173, 1, 2), (179, 1, 2), (181, 1, 2), (191, 1, 2), (193, 1, 2), (197, 1, 2),
   (199, 1, 2), (211, 1, 2), (223, 1, 2), (227, 1, 2), (229, 1, 2), (233, 1, 2), (239, 1, 2),
   (241, 1, 2), (251, 1, 2), (257, 1, 2), (263, 1, 2), (269, 0, 1)]

/-- `M₀ = ∏ p^{e_p} ≈ 1.529·10^{119}`, colossally abundant for the parameter `1/1480`. -/
def caM : ℕ := mulPow caList

theorem caList_prime : ∀ x ∈ caList, x.1.Prime := by
  decide +kernel

theorem caList_cop : copCheck caList = true := by
  decide +kernel

theorem caList_lt : ∀ x ∈ caList, x.1 < 271 := by
  decide +kernel

/-- Every prime below `271` is the prime of some entry. -/
theorem caList_cover : ∀ p < 271, p.Prime → p ∈ caList.map Prod.fst := by
  decide +kernel

/-- The finite checks at `N = 1480`, all 57 primes. -/
theorem caList_check : checkList 1480 caList = true := by
  decide +kernel

/-- `σ(M₀)^{1480} · 10^{119} < 10^{1480} · M₀^{1481}`. -/
theorem caList_final :
    sigPow caList ^ 1480 * 10 ^ 119 < 10 ^ 1480 * mulPow caList ^ (1480 + 1) := by
  decide +kernel

theorem caM_ne_zero : caM ≠ 0 := mulPow_ne_zero caList caList_prime

theorem sigma_caM : σ 1 caM = sigPow caList := sigma_mulPow caList caList_prime caList_cop

/-- **`M₀` maximises `W = σ^{1480}/(·)^{1481}` prime by prime**: for every prime `p` and every
`k`, `W(p^k) ≤ W(p^{v_p(M₀)})`. Primes `< 271` by `caList_check`; primes `≥ 271` (where
`v_p(M₀) = 0`) by `pow_le_pred_pow_mul`. -/
theorem caM_local (p : ℕ) (hp : p.Prime) (k : ℕ) :
    σ 1 (p ^ k) ^ 1480 * p ^ (caM.factorization p * (1480 + 1)) ≤
      σ 1 (p ^ caM.factorization p) ^ 1480 * p ^ (k * (1480 + 1)) := by
  rcases Nat.lt_or_ge p 271 with hsmall | hbig
  · have h := compare_of_checkList caList_check caList_prime (caList_cover p hsmall hp) k
    rwa [show mulPow caList = caM from rfl] at h
  · have h0 : caM.factorization p = 0 := by
      rw [caM, factorization_mulPow caList caList_prime]
      exact expOf_eq_zero caList p (fun x hx => by have := caList_lt x hx; omega)
    rw [h0]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk]
    · refine compare_of_tail (A := 1) hp ?_ (by omega)
      simp only [zero_mul, pow_zero, mul_one, pow_one, isMultiplicative_sigma.map_one, one_pow,
        one_mul]
      exact pow_le_pred_pow_mul (P0 := 270) (by norm_num) (by norm_num) hbig

/-- **The colossally-abundant inequality for `M₀`**: `σ(m)^{1480} M₀^{1481} ≤ σ(M₀)^{1480}
m^{1481}` for every `m ≥ 1`, i.e. `σ(m)/m ≤ (σ(M₀)/M₀)(m/M₀)^{1/1480}`. -/
theorem caM_compare {m : ℕ} (hm : m ≠ 0) :
    σ 1 m ^ 1480 * caM ^ (1480 + 1) ≤ σ 1 caM ^ 1480 * m ^ (1480 + 1) :=
  sigma_pow_mul_le_of_local caM_ne_zero caM_local hm

/-- **`σ(m) < 10 m` for every `1 ≤ m ≤ 10^{119}`.** -/
theorem sigma_lt_ten_mul {m : ℕ} (hm : 1 ≤ m) (hmX : m ≤ 10 ^ 119) : σ 1 m < 10 * m := by
  refine lt_ten_mul_of_ca (N := 1480) (M := caM) (S := σ 1 caM) hm hmX
    (caM_compare (by omega)) ?_
  have hfin := caList_final
  rw [show mulPow caList = caM from rfl, ← sigma_caM] at hfin
  exact hfin

/-- **`σ(m)/m < 10` for every `1 ≤ m ≤ 10^{119}`** (real form of `sigma_lt_ten_mul`). -/
theorem sigma_div_lt_ten {m : ℕ} (hm : 1 ≤ m) (hmX : m ≤ 10 ^ 119) :
    (σ 1 m : ℝ) / m < 10 := by
  have hpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_lt_iff₀ hpos]
  exact_mod_cast sigma_lt_ten_mul hm hmX

end Principia.Common.SmallAbundancy
