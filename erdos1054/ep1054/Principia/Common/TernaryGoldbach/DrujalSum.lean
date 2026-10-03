/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# The arithmetic of `lem:drujal`: `S(r) = ∑_{q ≤ r odd} μ²(q)/φ(q)` and the error sums, BOTH WAYS

`lem:drujal` (`ternvin.tex` 1412–1453; its proof is 1222–1410) consumes four finite arithmetic sums
at `r = 150000`, `δ₀ = 8`. Every one is bounded here ELEMENTARILY — no `75 000`-term certification:

| sum | where it enters | truth | proved here |
|---|---|---|---|
| `S = sR` (`eq:mardi`, `eq:chetvyorg`) | main term `2|η|₂²S` | `6.7987792` | `hOdd ≤ S ≤ hOdd²` |
| `hOdd = ∑_{n ≤ r odd} 1/n` | bounds on `S` | `6.5943767` | `6.5942 ≤ hOdd ≤ 1 + ½ log 149999` |
| `nagS` (`eq:nagasa`, 1399–1401) | the `ET` aggregate | `2.5914552` | `≤ 3.125` |
| `harmS` (1402–1408) | the `E`, `K` aggregates | `19.0899863` | `≤ 2(1 + log r)` |

* **`S ≥ hOdd`** (`hOdd_le_sR`): group the odd `n ≤ r` by their squarefree kernel `q = rad n ≤ r`;
  the fibre over `q` has `∑ 1/n ≤ (1/q)∏_{p|q}(1 − 1/p)⁻¹ = 1/φ(q)` (`fiber_le`, Mathlib's Euler
  product over `factoredNumbers`).
* **`S ≤ hOdd²`** (`sR_le_sq`): `q ≤ τ(q)φ(q)` for squarefree `q` (`le_tau_mul_totient`:
  `p ≤ 2(p − 1)`), so `μ²(q)/φ(q) ≤ τ(q)/q = ∑_{de = q} 1/(de)`, and the pairs `(d, e)` inject into
  `oddQ × oddQ` (`sum_tau_le`).
* **`hOdd`** by the trapezoid rule (`trap`: `log(a+2) − log a ≤ 1/a + 1/(a+2)`, which is
  `t ≤ sinh t` at `t = log((a+2)/a)`) after `20` exact terms, and `41¹³⁵·2¹⁵⁹⁸ ≤ 149999¹³⁵`
  (`log_ratio_ge`); the upper bound by `log y ≥ 1 − 1/y` (`hOdd_up`).
* **`nagS = 2∑_{q odd} μ²/(qφ)`** (`nagS_eq`, the even moduli reindexed by `q = 2q'`, `evenOdd`)
  `≤ 2(∑_{d odd} 1/d²)² ≤ 2(5/4)²`, by the same `τ` injection with weight `1/n²`.

**A SLIP IN THE SOURCE (1407), found here**: `ternvin.tex` bounds `∑_{q ≤ r odd} 1/q +
∑_{q ≤ 2r even} 2/q ≤ 2 log er − log(r/2) ≤ log 2e²r = 14.61`. The sum is `19.09` (it is
`2H_r − H_{r/2}/2`; `∑_{q ≤ r/2} 1/(2q)` was bounded below by `log(r/2)`, not `½ log(r/2)`).
It multiplies only `E² ≈ 5.7·10⁻¹⁶`, so nothing downstream moves; the spine uses the TRUE sum
`harmS` and the proved bound `2(1 + log r) = 25.84`.
-/

namespace Principia.Common.TernaryGoldbach.DS

open Finset

/-! ## The sums -/

/-- **`μ(q)²/φ(q)`**, the weight of the modulus `q` in `L_{r,δ₀}` (`eq:juto`). -/
noncomputable def cQ (q : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ)

/-- **The odd moduli of `𝔐_{8,r}`**: `1 ≤ q ≤ r = 150000`, `q` odd (`eq:majdef`). -/
def oddQ : Finset ℕ := (Icc 1 150000).filter Odd

/-- **The even moduli of `𝔐_{8,r}`**: `q ≤ 2r = 300000`, `q` even. -/
def evenQ : Finset ℕ := (Icc 1 300000).filter Even

/-- **`S(r) = ∑_{q ≤ r odd} μ²(q)/φ(q)`** (`eq:mardi`, `eq:chetvyorg`). Truth `6.7987792`. -/
noncomputable def sR : ℝ := ∑ q ∈ oddQ, cQ q

/-- **`∑_{n ≤ r odd} 1/n`**. Truth `6.5943767`. -/
noncomputable def hOdd : ℝ := ∑ n ∈ oddQ, (1 : ℝ) / n

/-- **The `ET`-aggregate's sum** (`eq:juto` 1291–1293, `eq:nagasa` 1399–1401):
`∑_q μ²(q)/φ(q)·gcd(q,2)/q` over the odd `q ≤ r` and the even `q ≤ 2r`. Truth `2.5914552`
(Helfgott: `≤ 2.59147`). -/
noncomputable def nagS : ℝ := ∑ q ∈ oddQ, cQ q / q + ∑ q ∈ evenQ, 2 * cQ q / q

/-- **The `E`/`K`-aggregates' sum** (`eq:juto` 1295–1303, 1402–1408):
`∑_{q ≤ r odd} 1/q + ∑_{q ≤ 2r even} 2/q`. Truth `19.0899863` — NOT `≤ log 2e²r = 14.61` as
printed at 1407 (see the module docstring). -/
noncomputable def harmS : ℝ := ∑ q ∈ oddQ, (1 : ℝ) / q + ∑ q ∈ evenQ, (2 : ℝ) / q

/-! ## `μ²/φ` -/

/-- `μ²/φ ≥ 0`. -/
theorem cQ_nonneg (q : ℕ) : 0 ≤ cQ q := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- `μ(q)²/φ(q) = 1/φ(q)` for squarefree `q`. -/
theorem cQ_sqfree {q : ℕ} (hq : Squarefree q) : cQ q = 1 / (Nat.totient q : ℝ) := by
  unfold cQ
  rw [ArithmeticFunction.moebius_apply_of_squarefree hq]
  push_cast
  rw [← pow_mul, pow_mul', neg_one_sq, one_pow]

/-- `μ(q)²/φ(q) = 0` off the squarefree numbers. -/
theorem cQ_not_sqfree {q : ℕ} (hq : ¬ Squarefree q) : cQ q = 0 := by
  unfold cQ
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]
  simp

/-- `cQ(2q) = cQ(q)` for odd `q` (`φ(2q) = φ(q)`, `2q` squarefree iff `q` is). -/
theorem cQ_two_mul {q : ℕ} (hq : Odd q) : cQ (2 * q) = cQ q := by
  by_cases hs : Squarefree q
  · have h2 : Squarefree (2 * q) :=
      Nat.squarefree_mul_iff.mpr ⟨Nat.coprime_two_left.mpr hq, Nat.prime_two.prime.squarefree, hs⟩
    rw [cQ_sqfree h2, cQ_sqfree hs, Nat.totient_two_mul_of_odd hq]
  · have h2 : ¬ Squarefree (2 * q) := fun h => hs (Nat.squarefree_mul_iff.mp h).2.2
    rw [cQ_not_sqfree h2, cQ_not_sqfree hs]

/-- `cQ(2m) = 0` for even `m` (`4 ∣ 2m`). -/
theorem cQ_two_mul_even {m : ℕ} (hm : ¬ Odd m) : cQ (2 * m) = 0 := by
  refine cQ_not_sqfree fun h => ?_
  obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hm
  have hd : 2 * 2 ∣ 2 * m := ⟨k, by omega⟩
  exact absurd (h 2 hd) (by simp)

/-! ## The even moduli (`ternvin.tex` 1359–1365) -/

/-- The even moduli are `2m`, `1 ≤ m ≤ r`. -/
theorem evenQ_eq : evenQ = (Icc 1 150000).image (fun m => 2 * m) := by
  ext n
  simp only [evenQ, mem_filter, mem_Icc, mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨r, hr⟩⟩
    exact ⟨r, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨by omega, by omega⟩, ⟨m, by omega⟩⟩

/-- **The even moduli collapse onto the odd ones** (1359–1365): `∑_{q ≤ 2r even} μ²(q)/φ(q)·g(q) =
∑_{q ≤ r odd} μ²(q)/φ(q)·g(2q)`, for ANY `g` (the squarefree even `q` are `2q'`, `q'` odd, with
`φ(2q') = φ(q')`). -/
theorem evenOdd (g : ℕ → ℝ) : ∑ q ∈ evenQ, cQ q * g q = ∑ q ∈ oddQ, cQ q * g (2 * q) := by
  rw [evenQ_eq, sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by norm_num) h,
    ← sum_filter_add_sum_filter_not (Icc 1 150000) Odd]
  have h0 : ∑ m ∈ (Icc 1 150000).filter (fun m => ¬ Odd m), cQ (2 * m) * g (2 * m) = 0 :=
    sum_eq_zero fun m hm => by rw [cQ_two_mul_even (mem_filter.mp hm).2, zero_mul]
  rw [h0, add_zero]
  exact sum_congr rfl fun m hm => by rw [cQ_two_mul (mem_filter.mp hm).2]

/-! ## `S ≥ ∑_{n ≤ r odd} 1/n`: grouping by the squarefree kernel -/

/-- **The squarefree kernel** `rad n = ∏_{p | n} p`. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- `rad n ∣ n`. -/
theorem rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

/-- `rad n ≥ 1`. -/
theorem rad_pos (n : ℕ) : 0 < rad n :=
  prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

/-- `rad n` has the prime factors of `n`. -/
theorem rad_primeFactors (n : ℕ) : (rad n).primeFactors = n.primeFactors :=
  Nat.primeFactors_prod fun _ hp => Nat.prime_of_mem_primeFactors hp

/-- `rad n` is squarefree. -/
theorem rad_sqfree (n : ℕ) : Squarefree (rad n) := by
  rw [Nat.squarefree_iff_factorization_le_one (rad_pos n).ne']
  intro p
  unfold rad
  rw [Nat.factorization_prod fun x hx => (Nat.prime_of_mem_primeFactors hx).ne_zero,
    Finsupp.finsetSum_apply]
  calc ∑ x ∈ n.primeFactors, x.factorization p
      = ∑ x ∈ n.primeFactors, if x = p then 1 else 0 := by
        refine sum_congr rfl fun x hx => ?_
        rw [(Nat.prime_of_mem_primeFactors hx).factorization, Finsupp.single_apply]
    _ ≤ 1 := by
        rw [sum_ite_eq']
        split_ifs <;> norm_num

/-- `rad` maps the odd moduli to the odd moduli. -/
theorem rad_mem {n : ℕ} (hn : n ∈ oddQ) : rad n ∈ oddQ := by
  simp only [oddQ, mem_filter, mem_Icc] at hn ⊢
  obtain ⟨⟨h1, h2⟩, ho⟩ := hn
  exact ⟨⟨rad_pos n, le_trans (Nat.le_of_dvd (by omega) (rad_dvd n)) h2⟩,
    Odd.of_dvd_nat ho (rad_dvd n)⟩

/-- `m ↦ 1/m` as a monoid hom `ℕ →* ℝ` (`0 ↦ 0`), for Mathlib's Euler product. -/
noncomputable def invNat : ℕ →* ℝ :=
  (invMonoidHom : ℝ →* ℝ).comp (Nat.castRingHom ℝ).toMonoidHom

/-- `invNat m = 1/m`. -/
theorem invNat_apply (m : ℕ) : invNat m = (m : ℝ)⁻¹ := rfl

/-- **Euler's product over a finite set of primes, as an inequality**: a finite set of positive
integers whose prime factors lie in `P` has `∑ 1/m ≤ ∏_{p ∈ P} (1 − 1/p)⁻¹`. -/
theorem sum_inv_le_prod (P G : Finset ℕ)
    (hG : ∀ m ∈ G, m ≠ 0 ∧ ∀ p, p.Prime → p ∣ m → p ∈ P) :
    ∑ m ∈ G, (m : ℝ)⁻¹ ≤ ∏ p ∈ P with p.Prime, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hnorm : ∀ {p : ℕ}, p.Prime → ‖invNat p‖ < 1 := by
    intro p hp
    rw [invNat_apply, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hE := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    hnorm P).2
  have hmem : ∀ m ∈ G, m ∈ Nat.factoredNumbers P :=
    fun m hm => Nat.mem_factoredNumbers'.mpr (hG m hm).2
  have h1 := sum_le_hasSum (G.subtype (· ∈ Nat.factoredNumbers P))
    (fun i _ => by rw [invNat_apply]; exact inv_nonneg.mpr (Nat.cast_nonneg _)) hE
  rw [sum_subtype_eq_sum_filter, filter_true_of_mem hmem] at h1
  simp only [invNat_apply] at h1
  exact h1

/-- `∏_{p | q}(1 − 1/p)⁻¹ = q/φ(q)`. -/
theorem prod_inv_eq {q : ℕ} (hq : 0 < q) :
    ∏ p ∈ q.primeFactors with p.Prime, (1 - (p : ℝ)⁻¹)⁻¹ = (q : ℝ) / Nat.totient q := by
  rw [filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp, prod_inv_distrib]
  have h := Nat.totient_eq_mul_prod_factors q
  have h' : (Nat.totient q : ℝ) = q * ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have := congrArg (fun r : ℚ => (r : ℝ)) h
    push_cast at this
    exact this
  have hP : ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h'
    exact (Nat.totient_pos.mpr hq).ne' (by exact_mod_cast h')
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [h']
  field_simp

/-- **One fibre**: the positive `n` with `rad n = q` (`q` squarefree) have `∑ 1/n ≤ 1/φ(q)`
(`n = q·m`, `m` factored over `q`'s primes, Euler's product). -/
theorem fiber_le {q : ℕ} (hq : Squarefree q) (F : Finset ℕ)
    (hF : ∀ n ∈ F, n ≠ 0 ∧ rad n = q) : ∑ n ∈ F, (1 : ℝ) / n ≤ 1 / (Nat.totient q : ℝ) := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero hq.ne_zero
  have hdvd : ∀ n ∈ F, q ∣ n := fun n hn => (hF n hn).2 ▸ rad_dvd n
  have hpf : ∀ n ∈ F, n.primeFactors = q.primeFactors := fun n hn => by
    rw [← (hF n hn).2, rad_primeFactors]
  have hsplit : ∀ n ∈ F, (1 : ℝ) / n = 1 / q * ((n / q : ℕ) : ℝ)⁻¹ := by
    intro n hn
    obtain ⟨m, rfl⟩ := hdvd n hn
    rw [Nat.mul_div_cancel_left m hq0]
    push_cast
    simp only [one_div, mul_inv]
  rw [sum_congr rfl hsplit, ← mul_sum]
  have hinj : Set.InjOn (fun n => n / q) F := by
    intro a ha b hb hab
    obtain ⟨m, rfl⟩ := hdvd a ha
    obtain ⟨k, rfl⟩ := hdvd b hb
    have hab' : q * m / q = q * k / q := hab
    rw [Nat.mul_div_cancel_left m hq0, Nat.mul_div_cancel_left k hq0] at hab'
    rw [hab']
  have e : ∑ n ∈ F, ((n / q : ℕ) : ℝ)⁻¹ =
      ∑ m ∈ F.image (fun n => n / q), ((m : ℕ) : ℝ)⁻¹ :=
    (sum_image (f := fun m : ℕ => ((m : ℕ) : ℝ)⁻¹) hinj).symm
  rw [e]
  have hG : ∀ m ∈ F.image (fun n => n / q),
      m ≠ 0 ∧ ∀ p, p.Prime → p ∣ m → p ∈ q.primeFactors := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
    obtain ⟨k, hk⟩ := hdvd n hn
    have hn0 := (hF n hn).1
    refine ⟨?_, fun p hp hpm => ?_⟩
    · rw [hk, Nat.mul_div_cancel_left k hq0]
      rintro rfl
      exact hn0 (by rw [hk, mul_zero])
    · rw [← hpf n hn]
      exact Nat.mem_primeFactors.mpr
        ⟨hp, Nat.dvd_trans hpm (Nat.div_dvd_of_dvd (hdvd n hn)), hn0⟩
  have h1 := sum_inv_le_prod q.primeFactors _ hG
  rw [prod_inv_eq hq0] at h1
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  calc 1 / (q : ℝ) * ∑ m ∈ F.image (fun n => n / q), ((m : ℕ) : ℝ)⁻¹
      ≤ 1 / q * (q / Nat.totient q) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 / Nat.totient q := by field_simp

/-- **`S(r) ≥ ∑_{n ≤ r odd} 1/n`**: the odd `n ≤ r` split into fibres of `rad`, each fibre over a
squarefree `q` costing at most `1/φ(q)`. -/
theorem hOdd_le_sR : hOdd ≤ sR := by
  unfold hOdd sR
  rw [← sum_fiberwise_of_maps_to (fun n hn => rad_mem hn) (fun n => (1 : ℝ) / n)]
  refine sum_le_sum fun q _ => ?_
  by_cases hsq : Squarefree q
  · rw [cQ_sqfree hsq]
    refine fiber_le hsq _ fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := mem_filter.mp hn
    refine ⟨?_, hn2⟩
    simp only [oddQ, mem_filter, mem_Icc] at hn1
    omega
  · have he : oddQ.filter (fun n => rad n = q) = ∅ :=
      filter_eq_empty_iff.mpr fun n _ h => hsq (h ▸ rad_sqfree n)
    rw [he, sum_empty]
    exact cQ_nonneg q

/-! ## `S ≤ (∑_{n ≤ r odd} 1/n)²`: `q ≤ τ(q)φ(q)` -/

/-- **`q ≤ τ(q)φ(q)` for squarefree `q`**: `q = ∏ p ≤ ∏ 2(p − 1) = 2^{ω(q)}·φ(q)`. -/
theorem le_tau_mul_totient {q : ℕ} (hq : Squarefree q) :
    q ≤ q.divisors.card * Nat.totient q := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have hτ : q.divisors.card = ∏ p ∈ q.primeFactors, 2 := by
    rw [Nat.card_divisors hq0]
    refine prod_congr rfl fun p hp => ?_
    have h1 := hq.natFactorization_le_one p
    have h2 : q.factorization p ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]
      exact hp
    omega
  have hφ : Nat.totient q = ∏ p ∈ q.primeFactors, (p - 1) := by
    have h := Nat.totient_mul_prod_primeFactors q
    rw [Nat.prod_primeFactors_of_squarefree hq, mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq0) h
  calc q = ∏ p ∈ q.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hq).symm
    _ ≤ ∏ p ∈ q.primeFactors, (2 * (p - 1)) := by
        refine prod_le_prod' fun p hp => ?_
        have := (Nat.prime_of_mem_primeFactors hp).two_le
        omega
    _ = q.divisors.card * Nat.totient q := by rw [prod_mul_distrib, hτ, hφ]

/-- **`μ²(q)/φ(q) ≤ τ(q)/q`** for `q ≥ 1`. -/
theorem cQ_le_tau {q : ℕ} (hq : 1 ≤ q) : cQ q ≤ (q.divisors.card : ℝ) * (1 / q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hsq : Squarefree q
  · rw [cQ_sqfree hsq]
    have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
    have h' : (q : ℝ) ≤ q.divisors.card * Nat.totient q := by
      exact_mod_cast le_tau_mul_totient hsq
    rw [div_le_iff₀ hφ]
    calc (1 : ℝ) = q * (1 / q) := by field_simp
      _ ≤ (q.divisors.card * Nat.totient q) * (1 / q) :=
          mul_le_mul_of_nonneg_right h' (by positivity)
      _ = q.divisors.card * (1 / q) * Nat.totient q := by ring
  · rw [cQ_not_sqfree hsq]
    positivity

/-- **The `τ` injection**, over any divisor-closed `s`: for a nonnegative completely multiplicative
weight `w`, `∑_{q ∈ s} τ(q)w(q) ≤ (∑_{d ∈ s} w(d))²` (`τ(q)w(q) = ∑_{de = q} w(d)w(e)`, and both
factors of a pair `(d, e)` with `de ∈ s` lie in `s`). -/
theorem sum_tau_le (s : Finset ℕ) (hs : ∀ q ∈ s, ∀ d, d ∣ q → d ∈ s) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (hm : ∀ a b, w (a * b) = w a * w b) :
    ∑ q ∈ s, (q.divisors.card : ℝ) * w q ≤ (∑ d ∈ s, w d) ^ 2 := by
  have h1 : ∀ q ∈ s,
      (q.divisors.card : ℝ) * w q = ∑ p ∈ q.divisorsAntidiagonal, w p.1 * w p.2 := by
    intro q _
    have hs : ∑ d ∈ q.divisors, w d * w (q / d) = ∑ d ∈ q.divisors, w q := by
      refine sum_congr rfl fun d hd => ?_
      rw [← hm, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    rw [Nat.sum_divisorsAntidiagonal (fun a b => w a * w b), hs, sum_const, nsmul_eq_mul]
  rw [sum_congr rfl h1, sq, sum_mul_sum, ← sum_product']
  have hdisj : Set.PairwiseDisjoint (↑s : Set ℕ) Nat.divisorsAntidiagonal := by
    intro a _ b _ hab
    refine disjoint_left.mpr fun p hpa hpb => hab ?_
    rw [Nat.mem_divisorsAntidiagonal] at hpa hpb
    rw [← hpa.1, hpb.1]
  rw [← sum_biUnion hdisj]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => mul_nonneg (hw _) (hw _)
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_biUnion.mp hp
  rw [Nat.mem_divisorsAntidiagonal] at hpq
  exact mem_product.mpr ⟨hs q hq p.1 ⟨p.2, hpq.1.symm⟩,
    hs q hq p.2 ⟨p.1, by rw [← hpq.1, mul_comm]⟩⟩

/-- The odd moduli are closed under divisors. -/
theorem oddQ_dvd : ∀ q ∈ oddQ, ∀ d, d ∣ q → d ∈ oddQ := by
  intro q hq d hd
  simp only [oddQ, mem_filter, mem_Icc] at hq ⊢
  obtain ⟨⟨hq1, hq2⟩, hqo⟩ := hq
  have hq0 : 0 < q := by omega
  exact ⟨⟨Nat.pos_of_dvd_of_pos hd hq0, le_trans (Nat.le_of_dvd hq0 hd) hq2⟩,
    Odd.of_dvd_nat hqo hd⟩

/-- **`S(r) ≤ (∑_{n ≤ r odd} 1/n)²`**. -/
theorem sR_le_sq : sR ≤ hOdd ^ 2 := by
  unfold sR hOdd
  calc ∑ q ∈ oddQ, cQ q ≤ ∑ q ∈ oddQ, (q.divisors.card : ℝ) * (1 / (q : ℝ)) :=
        sum_le_sum fun q hq => cQ_le_tau (by simp only [oddQ, mem_filter, mem_Icc] at hq; omega)
    _ ≤ (∑ d ∈ oddQ, (1 : ℝ) / d) ^ 2 :=
        sum_tau_le oddQ oddQ_dvd (fun n => 1 / (n : ℝ)) (fun n => by positivity)
          (fun a b => by push_cast; rw [one_div_mul_one_div])

/-! ## `∑_{n ≤ r odd} 1/n`, numerically -/

/-- The odd moduli are `2k + 1`, `k < 75000`. -/
theorem oddQ_eq : oddQ = (range 75000).image (fun k => 2 * k + 1) := by
  ext n
  simp only [oddQ, mem_filter, mem_Icc, mem_image, mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨k, hk⟩⟩
    exact ⟨k, by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨by omega, by omega⟩, ⟨k, by omega⟩⟩

/-- A sum over the odd moduli is a sum over `k < 75000` at `2k + 1`. -/
theorem sum_oddQ (f : ℕ → ℝ) : ∑ n ∈ oddQ, f n = ∑ k ∈ range 75000, f (2 * k + 1) := by
  rw [oddQ_eq, sum_image fun a _ b _ h => by
    have h' : 2 * a + 1 = 2 * b + 1 := h
    omega]

/-- `f(k) = 1/(2k + 1)`. -/
noncomputable def fo (k : ℕ) : ℝ := 1 / (2 * (k : ℝ) + 1)

/-- `hOdd = ∑_{k < 75000} 1/(2k + 1)`. -/
theorem hOdd_eq : hOdd = ∑ k ∈ range 75000, fo k := by
  unfold hOdd fo
  rw [sum_oddQ (fun n => (1 : ℝ) / n)]
  exact sum_congr rfl fun k _ => by push_cast; ring

/-- **The trapezoid step**: `log(a + 2) − log a ≤ 1/a + 1/(a + 2)` for `a > 0` (`t ≤ sinh t` at
`t = log((a+2)/a)`, and `sinh(log y) = (y − 1/y)/2`). -/
theorem log_trap {a : ℝ} (ha : 0 < a) :
    Real.log (a + 2) - Real.log a ≤ 1 / a + 1 / (a + 2) := by
  have hy : 0 < (a + 2) / a := by positivity
  rw [← Real.log_div (by positivity) ha.ne']
  have h1 : Real.log ((a + 2) / a) ≤ Real.sinh (Real.log ((a + 2) / a)) :=
    Real.self_le_sinh_iff.mpr (Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith))
  rw [Real.sinh_eq, Real.exp_log hy, Real.exp_neg, Real.exp_log hy] at h1
  have e : ((a + 2) / a - ((a + 2) / a)⁻¹) / 2 = 1 / a + 1 / (a + 2) := by
    field_simp
    ring
  linarith

/-- **The trapezoid rule from `M` on**:
`∑_{k ≤ M+J} f(k) ≥ ∑_{k < M} f(k) + (f(M) + f(M+J))/2 + ½(log(2(M+J)+1) − log(2M+1))`. -/
theorem trap (M : ℕ) : ∀ J : ℕ, ∑ k ∈ range M, fo k + (fo M + fo (M + J)) / 2 +
    (Real.log (2 * ((M + J : ℕ) : ℝ) + 1) - Real.log (2 * (M : ℝ) + 1)) / 2 ≤
      ∑ k ∈ range (M + J + 1), fo k := by
  intro J
  induction J with
  | zero =>
    rw [Nat.add_zero, sub_self, zero_div, add_zero, sum_range_succ]
    linarith
  | succ J ih =>
    have hstep := log_trap (a := 2 * ((M + J : ℕ) : ℝ) + 1) (by positivity)
    rw [show M + (J + 1) + 1 = M + J + 1 + 1 from rfl, sum_range_succ]
    have hA : fo (M + J) = 1 / (2 * ((M + J : ℕ) : ℝ) + 1) := rfl
    have hB : fo (M + J + 1) = 1 / (2 * ((M + J : ℕ) : ℝ) + 1 + 2) := by
      unfold fo
      push_cast
      ring
    have hC : fo (M + (J + 1)) = fo (M + J + 1) := rfl
    have hD : Real.log (2 * ((M + (J + 1) : ℕ) : ℝ) + 1) =
        Real.log (2 * ((M + J : ℕ) : ℝ) + 1 + 2) := by
      congr 1
      push_cast
      ring
    linarith [ih, hstep, hA, hB, hC, hD]

set_option exponentiation.threshold 2000 in
/-- `log 149999 − log 41 ≥ (1598/135)·0.6931471803`, from `41¹³⁵·2¹⁵⁹⁸ ≤ 149999¹³⁵`. -/
theorem log_ratio_ge : 1598 / 135 * 0.6931471803 ≤ Real.log 149999 - Real.log 41 := by
  have h1 : (41 : ℝ) ^ 135 * 2 ^ 1598 ≤ 149999 ^ 135 := by norm_num
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at h2
  have h3 := Real.log_two_gt_d9
  push_cast at h2
  linarith

/-- **`∑_{n ≤ r odd} 1/n ≥ 6.5942`** (truth `6.5943767`): `20` exact terms, then the trapezoid
rule to `n = 149999` (`6.5942776`). -/
theorem hOdd_ge : 6.5942 ≤ hOdd := by
  rw [hOdd_eq]
  have h : ∑ k ∈ range 20, fo k + (fo 20 + fo 74999) / 2 +
      (Real.log (2 * (74999 : ℝ) + 1) - Real.log (2 * (20 : ℝ) + 1)) / 2 ≤
        ∑ k ∈ range 75000, fo k := trap 20 74979
  have hhead : ∑ k ∈ range 20, fo k = 414022624965424 / 166966608033225 := by
    simp only [sum_range_succ, sum_range_zero, fo]
    norm_num
  have e20 : fo 20 = 1 / 41 := by
    unfold fo
    norm_num
  have e2 : fo 74999 = 1 / 149999 := by
    unfold fo
    norm_num
  have hl1 : Real.log (2 * (74999 : ℝ) + 1) = Real.log 149999 := by norm_num
  have hl2 : Real.log (2 * (20 : ℝ) + 1) = Real.log 41 := by norm_num
  rw [hhead, e20, e2, hl1, hl2] at h
  have hl := log_ratio_ge
  generalize ∑ k ∈ range 75000, fo k = X at h ⊢
  linarith

/-- **`∑_{k < n} 1/(2k+1) ≤ 1 + ½ log(2n − 1)`** (`1/(2k+1) ≤ ½ log((2k+1)/(2k−1))`). -/
theorem hOdd_up : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ range n, fo k ≤ 1 + Real.log (2 * (n : ℝ) - 1) / 2 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num [fo]
  | succ n hn ih =>
    rw [sum_range_succ]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : 0 < 2 * (n : ℝ) - 1 := by linarith
    have hpos2 : 0 < 2 * (n : ℝ) + 1 := by linarith
    have hk := Real.one_sub_inv_le_log_of_pos
      (x := (2 * (n : ℝ) + 1) / (2 * (n : ℝ) - 1)) (div_pos hpos2 hpos)
    rw [Real.log_div hpos2.ne' hpos.ne'] at hk
    have e : 1 - ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) - 1))⁻¹ = 2 * fo n := by
      unfold fo
      rw [inv_div]
      field_simp
      ring
    have e2 : 2 * ((n + 1 : ℕ) : ℝ) - 1 = 2 * (n : ℝ) + 1 := by
      push_cast
      ring
    rw [e2]
    linarith

/-- **`∑_{n ≤ r odd} 1/n ≤ 1 + ½ log 149999`**. -/
theorem hOdd_le : hOdd ≤ 1 + Real.log 149999 / 2 := by
  rw [hOdd_eq]
  have h := hOdd_up 75000 (by norm_num)
  have e : 2 * ((75000 : ℕ) : ℝ) - 1 = 149999 := by norm_num
  rw [e] at h
  exact h

/-- **`∑_{k < n} 1/(2k+1)² ≤ 5/4 − 1/(4n)`** (`1/(2k+1)² ≤ ¼(1/k − 1/(k+1))`). -/
theorem sq_up : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ range n, fo k ^ 2 ≤ 5 / 4 - 1 / (4 * (n : ℝ)) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num [fo]
  | succ n hn ih =>
    rw [sum_range_succ]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hd : 1 / (4 * (n : ℝ)) - 1 / (4 * ((n + 1 : ℕ) : ℝ)) - fo n ^ 2 =
        1 / (4 * (n : ℝ) * (n + 1) * (2 * n + 1) ^ 2) := by
      unfold fo
      push_cast
      field_simp
      ring
    have h0 : 0 ≤ 1 / (4 * (n : ℝ) * (n + 1) * (2 * n + 1) ^ 2) := by positivity
    linarith

/-- **`∑_{d ≤ r odd} 1/d² ≤ 5/4`**. -/
theorem sum_sq_le : ∑ d ∈ oddQ, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 5 / 4 := by
  have e : ∑ d ∈ oddQ, (1 : ℝ) / (d : ℝ) ^ 2 = ∑ k ∈ range 75000, fo k ^ 2 := by
    rw [sum_oddQ (fun n => (1 : ℝ) / (n : ℝ) ^ 2)]
    exact sum_congr rfl fun k _ => by unfold fo; push_cast; rw [div_pow, one_pow]
  rw [e]
  have h := sq_up 75000 (by norm_num)
  have h1 : (0 : ℝ) ≤ 1 / (4 * ((75000 : ℕ) : ℝ)) := by positivity
  generalize ∑ k ∈ range 75000, fo k ^ 2 = X at h ⊢
  generalize 1 / (4 * ((75000 : ℕ) : ℝ)) = Y at h h1
  linarith

/-! ## The aggregate sums -/

/-- **`nagS = 2∑_{q ≤ r odd} μ²(q)/(qφ(q))`** (the even moduli by `evenOdd`). -/
theorem nagS_eq : nagS = 2 * ∑ q ∈ oddQ, cQ q / q := by
  unfold nagS
  have e1 : ∑ q ∈ evenQ, 2 * cQ q / q = ∑ q ∈ evenQ, cQ q * (2 / (q : ℝ)) :=
    sum_congr rfl fun q _ => by ring
  have e2 : ∑ q ∈ oddQ, cQ q * (2 / ((2 * q : ℕ) : ℝ)) = ∑ q ∈ oddQ, cQ q / q :=
    sum_congr rfl fun q _ => by push_cast; ring
  rw [e1, evenOdd (fun q => 2 / (q : ℝ)), e2]
  ring

/-- **`nagS ≤ 3.125`** (truth `2.5914552`; Helfgott's `eq:nagasa` is `2.59147`):
`μ²(q)/(qφ(q)) ≤ τ(q)/q²`, the `τ` injection at `w = 1/n²`, and `∑_{d odd} 1/d² ≤ 5/4`. -/
theorem nagS_le : nagS ≤ 3.125 := by
  rw [nagS_eq]
  have h1 : ∑ q ∈ oddQ, cQ q / q ≤ ∑ q ∈ oddQ, (q.divisors.card : ℝ) * (1 / (q : ℝ) ^ 2) := by
    refine sum_le_sum fun q hq => ?_
    have hq1 : 1 ≤ q := by simp only [oddQ, mem_filter, mem_Icc] at hq; omega
    calc cQ q / q ≤ (q.divisors.card : ℝ) * (1 / q) / q :=
          div_le_div_of_nonneg_right (cQ_le_tau hq1) (by positivity)
      _ = (q.divisors.card : ℝ) * (1 / (q : ℝ) ^ 2) := by ring
  have h2 := sum_tau_le oddQ oddQ_dvd (fun n => 1 / (n : ℝ) ^ 2) (fun n => by positivity)
    (fun a b => by push_cast; ring)
  have h3 := sum_sq_le
  have h30 : 0 ≤ ∑ d ∈ oddQ, (1 : ℝ) / (d : ℝ) ^ 2 := sum_nonneg fun _ _ => by positivity
  have h4 : (∑ d ∈ oddQ, (1 : ℝ) / (d : ℝ) ^ 2) ^ 2 ≤ (5 / 4) ^ 2 := pow_le_pow_left₀ h30 h3 2
  generalize ∑ q ∈ oddQ, cQ q / q = A at h1 ⊢
  generalize ∑ q ∈ oddQ, (q.divisors.card : ℝ) * (1 / (q : ℝ) ^ 2) = B at h1 h2
  generalize ∑ d ∈ oddQ, (1 : ℝ) / (d : ℝ) ^ 2 = C at h2 h4
  linarith

/-- **`harmS ≤ 2(1 + log r)`** (truth `19.09`): the even part is `H_r` (`q = 2m`), the odd part is
at most `H_r`, and `H_r ≤ 1 + log r` (Mathlib). -/
theorem harmS_le : harmS ≤ 2 * (1 + Real.log 150000) := by
  unfold harmS
  have hH : ((harmonic 150000 : ℚ) : ℝ) = ∑ i ∈ Icc (1 : ℕ) 150000, (1 : ℝ) / (i : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp only [one_div]
  have hb := harmonic_le_one_add_log 150000
  have hsub : oddQ ⊆ Icc (1 : ℕ) 150000 := fun x hx => (mem_filter.mp hx).1
  have h1 : ∑ q ∈ oddQ, (1 : ℝ) / q ≤ ∑ i ∈ Icc (1 : ℕ) 150000, (1 : ℝ) / (i : ℝ) :=
    sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => one_div_nonneg.mpr (Nat.cast_nonneg i)
  have h2 : ∑ q ∈ evenQ, (2 : ℝ) / q = ∑ i ∈ Icc (1 : ℕ) 150000, (1 : ℝ) / (i : ℝ) := by
    rw [evenQ_eq, sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by norm_num) h]
    exact sum_congr rfl fun m _ => by push_cast; ring
  rw [hH] at hb
  push_cast at hb
  generalize ∑ q ∈ oddQ, (1 : ℝ) / q = A at h1 ⊢
  generalize ∑ q ∈ evenQ, (2 : ℝ) / q = B at h2 ⊢
  generalize ∑ i ∈ Icc (1 : ℕ) 150000, (1 : ℝ) / (i : ℝ) = C at h1 h2 hb
  linarith

end Principia.Common.TernaryGoldbach.DS
