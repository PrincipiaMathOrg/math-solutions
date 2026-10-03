import Principia.Common.Sieve.SelbergBounds
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

/-!
# The Brun–Titchmarsh inequality in arithmetic progressions

For every modulus `q ≥ 1`, every residue `a` and every real `x > q`,
`π(x; q, a) ≤ 2008 · x / (φ(q) · log (x / q))`
(`Principia.Common.BrunTitchmarshAP.brun_titchmarsh_ap`). The constant is not optimised
(Montgomery–Vaughan give `2`); no coprimality of `a` and `q` is needed for the upper bound.

## Route (Selberg's Λ² sieve, from the PNT+ port in this directory)

* `apSieve q a N z`: the progression `{n ≤ N : n ≡ a (mod q)}` sifted by the primes `p ≤ z`
  with `p ∤ q`, density `ν(d) = 1/d`, total mass `X = (N+1)/q`.
* Remainders: for `d ∣ P` we have `gcd(d, q) = 1`, so by the Chinese remainder theorem the
  multiples of `d` in the progression form one class mod `qd`, whose count in `[0, N]` is
  `⌊(N+1)/(qd)⌋ + (0 or 1)`; hence `|R_d| ≤ 1` (`abs_rem_le`).
* Main term: `Sieve.selbergBoundingSum_ge_sum_div_filter` (added to the port) bounds the Selberg
  sum below by `∑_{n ≤ √z, (n, q) = 1} 1/n`, and `harmAvoid_prod` gives
  `∑_{n ≤ T, (n,q)=1} 1/n ≥ (φ(q)/q) ∑_{n ≤ T} 1/n ≥ (φ(q)/q) log T` by removing the primes of
  `q` one at a time (`(1 - 1/p) H_Q ≤ H_{Q ∪ {p}}`).
* Choice `z = √(x/q)`: main term `≤ 8x/(φ(q) log(x/q))`, remainder and the unsifted primes
  `p ≤ z` together `≤ 2000 x/(φ(q) log(x/q))` (`log_poly_bound`).
-/

open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.omega
open BoundingSieve SelbergSieve

noncomputable section

namespace Principia.Common.BrunTitchmarshAP

/-! ## Harmonic sums avoiding a finite set of primes -/

/-- `∑_{1 ≤ n ≤ T, q ∤ n for all q ∈ Q} 1/n`. -/
def harmAvoid (Q : Finset ℕ) (T : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n), (1 / (n : ℝ))

theorem harmAvoid_empty (T : ℕ) : harmAvoid ∅ T = ∑ n ∈ Finset.Icc 1 T, (1 / (n : ℝ)) := by
  unfold harmAvoid
  congr 1
  apply Finset.filter_true_of_mem
  intro n _ q hq
  simp at hq

/-- Removing one more prime `p` costs at most the factor `1 - 1/p`. -/
theorem harmAvoid_insert (Q : Finset ℕ) (p T : ℕ) (hp : p.Prime) :
    (1 - 1 / (p : ℝ)) * harmAvoid Q T ≤ harmAvoid (insert p Q) T := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)) (fun n => p ∣ n)
    (fun n => 1 / (n : ℝ))
  have hnot : ∑ n ∈ ((Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).filter
      (fun n => ¬ p ∣ n), (1 / (n : ℝ)) = harmAvoid (insert p Q) T := by
    unfold harmAvoid
    rw [Finset.filter_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    apply Finset.filter_congr
    intro n _
    simp only [Finset.mem_insert, forall_eq_or_imp]
    tauto
  have hsub : ((Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).filter (fun n => p ∣ n) ⊆
      ((Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).image (fun k => p * k) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨h1, hT⟩, hQ⟩, k, rfl⟩ := hn
    rw [Finset.mem_image]
    refine ⟨k, ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · rw [hk, Nat.mul_zero] at h1
        exact absurd h1 (by norm_num)
      · exact hk
    refine ⟨⟨hk, le_trans (Nat.le_mul_of_pos_left k hp.pos) hT⟩, ?_⟩
    intro q hq hqk
    exact hQ q hq (Dvd.dvd.mul_left hqk p)
  have hdvd : ∑ n ∈ ((Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).filter
      (fun n => p ∣ n), (1 / (n : ℝ)) ≤ (1 / (p : ℝ)) * harmAvoid Q T := by
    calc ∑ n ∈ ((Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).filter
          (fun n => p ∣ n), (1 / (n : ℝ))
        ≤ ∑ n ∈ ((Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).image (fun k => p * k),
            (1 / (n : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∑ k ∈ (Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n),
            (1 / (((p * k : ℕ)) : ℝ)) :=
          Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hp.pos hab)
      _ = (1 / (p : ℝ)) * harmAvoid Q T := by
          unfold harmAvoid
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [Nat.cast_mul, one_div_mul_one_div]
  have hH : harmAvoid Q T = ∑ n ∈ ((Finset.Icc 1 T).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).filter
      (fun n => p ∣ n), (1 / (n : ℝ)) + ∑ n ∈ ((Finset.Icc 1 T).filter
        (fun n => ∀ q ∈ Q, ¬ q ∣ n)).filter (fun n => ¬ p ∣ n), (1 / (n : ℝ)) := by
    unfold harmAvoid
    exact hsplit.symm
  rw [sub_mul, one_mul]
  linarith

/-- Removing all the primes of `Q` costs at most `∏_{p ∈ Q} (1 - 1/p)`. -/
theorem harmAvoid_prod (T : ℕ) (Q : Finset ℕ) :
    (∀ p ∈ Q, p.Prime) → (∏ p ∈ Q, (1 - 1 / (p : ℝ))) * harmAvoid ∅ T ≤ harmAvoid Q T := by
  induction Q using Finset.induction_on with
  | empty => intro _; simp
  | insert p Q hpQ ih =>
    intro hQ
    have hp : p.Prime := hQ p (Finset.mem_insert_self p Q)
    have ih' := ih (fun q hq => hQ q (Finset.mem_insert_of_mem hq))
    have h1 : 0 ≤ 1 - 1 / (p : ℝ) := by
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
      have : 1 / (p : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact hp1
      linarith
    rw [Finset.prod_insert hpQ, mul_assoc]
    calc (1 - 1 / (p : ℝ)) * ((∏ q ∈ Q, (1 - 1 / (q : ℝ))) * harmAvoid ∅ T)
        ≤ (1 - 1 / (p : ℝ)) * harmAvoid Q T := mul_le_mul_of_nonneg_left ih' h1
      _ ≤ harmAvoid (insert p Q) T := harmAvoid_insert Q p T hp

/-- Euler's product for `φ(q)/q`, over `ℝ`. -/
theorem totient_div_eq_prod (q : ℕ) (hq : 0 < q) :
    (q.totient : ℝ) / q = ∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := Nat.totient_eq_mul_prod_factors q
  have h' : (q.totient : ℝ) = q * ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have := congrArg (fun r : ℚ => (r : ℝ)) h
    push_cast at this
    exact this
  rw [h', mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hq.ne')]
  simp only [one_div]

/-- The coprime harmonic sum: `(φ(q)/q) log T ≤ ∑_{n ≤ T, (n, q) = 1} 1/n` for real `T ≥ 1`
(coprimality to `q` written as avoiding every prime factor of `q`). -/
theorem totient_mul_log_le_harmAvoid (q : ℕ) (hq : 0 < q) (T : ℝ) (hT : 1 ≤ T) :
    (q.totient : ℝ) / q * Real.log T ≤ harmAvoid q.primeFactors ⌊T⌋₊ := by
  have hlog : Real.log T ≤ harmAvoid ∅ ⌊T⌋₊ := by
    rw [harmAvoid_empty]
    simp only [one_div]
    exact Aux.log_le_sum_inv T hT
  have hnn : 0 ≤ (q.totient : ℝ) / q := by positivity
  calc (q.totient : ℝ) / q * Real.log T ≤ (q.totient : ℝ) / q * harmAvoid ∅ ⌊T⌋₊ :=
        mul_le_mul_of_nonneg_left hlog hnn
    _ = (∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ))) * harmAvoid ∅ ⌊T⌋₊ := by
        rw [totient_div_eq_prod q hq]
    _ ≤ harmAvoid q.primeFactors ⌊T⌋₊ :=
        harmAvoid_prod ⌊T⌋₊ q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)

/-! ## The sieve on an arithmetic progression -/

/-- The sifting primes: `p ≤ z` prime with `p ∤ q`. -/
def siftPrimes (q : ℕ) (z : ℝ) : Finset ℕ :=
  (Finset.range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ q)

/-- Sifting the primes `p ≤ z`, `p ∤ q`, from the progression `{n ≤ N : n ≡ a (mod q)}`, with
density `ν(d) = 1/d` and total mass `(N+1)/q`. -/
def apSieve (q a N : ℕ) (z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := (Finset.range (N + 1)).filter (fun n => n % q = a % q)
  prodPrimes := ∏ p ∈ siftPrimes q z, p
  prodPrimes_squarefree := Sieve.prodDistinctPrimes_squarefree _
    (fun p hp => (Finset.mem_filter.mp hp).2.1)
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := ((N : ℝ) + 1) / q
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hp.ne_zero, ↓reduceIte, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  level := z
  one_le_level := hz

section APSieve

variable (q a N : ℕ) (z : ℝ) (hz : 1 ≤ z)

theorem prime_dvd_prodPrimes_iff {p : ℕ} (hp : p.Prime) :
    p ∣ (apSieve q a N z hz).prodPrimes ↔ p ≤ ⌊z⌋₊ ∧ ¬ p ∣ q := by
  show p ∣ ∏ p ∈ siftPrimes q z, p ↔ _
  constructor
  · intro h
    obtain ⟨i, hi, hpi⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd h
    rw [siftPrimes, Finset.mem_filter, Finset.mem_range] at hi
    have hpi' : p = i := (Nat.prime_dvd_prime_iff_eq hp hi.2.1).mp hpi
    rw [← hpi'] at hi
    exact ⟨Nat.lt_succ_iff.mp hi.1, hi.2.2⟩
  · rintro ⟨h1, h2⟩
    exact Finset.dvd_prod_of_mem (fun p => p)
      (by rw [siftPrimes, Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.lt_succ_of_le h1, hp, h2⟩)

theorem coprime_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ (apSieve q a N z hz).prodPrimes) :
    Nat.Coprime q d := by
  apply Nat.coprime_of_dvd
  intro k hk hkq hkd
  exact ((prime_dvd_prodPrimes_iff q a N z hz hk).mp (hkd.trans hd)).2 hkq

theorem multSum_eq (d : ℕ) :
    multSum (s := (apSieve q a N z hz).toBoundingSieve) d =
      ((((Finset.range (N + 1)).filter (fun n => n % q = a % q)).filter
        (fun n => d ∣ n)).card : ℝ) := by
  show (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = a % q),
      if d ∣ n then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole]

/-- The multiples of `d` in the progression (`gcd(d, q) = 1`) form one class mod `qd`. -/
theorem card_filter_modEq_dvd {d : ℕ} (hd0 : 0 < d) (hq0 : 0 < q) (hcop : Nat.Coprime q d) :
    ∃ e : ℕ, e ≤ 1 ∧
      (((Finset.range (N + 1)).filter (fun n => n % q = a % q)).filter (fun n => d ∣ n)).card
        = (N + 1) / (q * d) + e := by
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder hcop a 0
  have hset : ((Finset.range (N + 1)).filter (fun n => n % q = a % q)).filter (fun n => d ∣ n)
      = (Finset.range (N + 1)).filter (fun n => n ≡ c [MOD q * d]) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro n _
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : n ≡ a [MOD q] := h1
      exact ⟨h1'.trans hc1.symm, (Nat.modEq_zero_iff_dvd.mpr h2).trans hc2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(h1.trans hc1 : n ≡ a [MOD q]), Nat.modEq_zero_iff_dvd.mp (h2.trans hc2)⟩
  rw [hset, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ (Nat.mul_pos hq0 hd0)]
  refine ⟨if c % (q * d) < (N + 1) % (q * d) then 1 else 0, ?_, rfl⟩
  split_ifs <;> norm_num

/-- The sieve remainders are bounded by `1` at every divisor of `P`. -/
theorem abs_rem_le (hq0 : 0 < q) {d : ℕ} (hd : d ∣ (apSieve q a N z hz).prodPrimes) :
    |rem (s := (apSieve q a N z hz).toBoundingSieve) d| ≤ 1 := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hd)
  obtain ⟨e, he, hcard⟩ :=
    card_filter_modEq_dvd q a N hd0 hq0 (coprime_of_dvd_prodPrimes q a N z hz hd)
  have hnu : (apSieve q a N z hz).nu d = 1 / (d : ℝ) := by
    show ((ζ : ArithmeticFunction ℝ).pdiv .id) d = 1 / (d : ℝ)
    simp [ArithmeticFunction.pdiv_apply, hd0.ne']
  have hmain : (apSieve q a N z hz).nu d * (apSieve q a N z hz).totalMass
      = ((N + 1 : ℕ) : ℝ) / ((q * d : ℕ) : ℝ) := by
    rw [hnu]
    show 1 / (d : ℝ) * (((N : ℝ) + 1) / q) = _
    push_cast
    rw [div_mul_div_comm, one_mul, mul_comm (d : ℝ) (q : ℝ)]
  have hk1 : ((((N + 1) / (q * d) : ℕ)) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) / ((q * d : ℕ) : ℝ) :=
    Nat.cast_div_le
  have hk2 : ((N + 1 : ℕ) : ℝ) / ((q * d : ℕ) : ℝ) < ((((N + 1) / (q * d) : ℕ)) : ℝ) + 1 := by
    rw [← Nat.floor_div_eq_div (K := ℝ) (N + 1) (q * d)]
    exact Nat.lt_floor_add_one _
  have he' : (e : ℝ) ≤ 1 := by exact_mod_cast he
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  unfold rem
  rw [multSum_eq, hcard, hmain, Nat.cast_add ((N + 1) / (q * d)) e, abs_le]
  constructor <;> linarith

/-- The primes counted by `π(N; q, a)` are sifted, or at most `z`. -/
theorem card_primes_le :
    (((Finset.Iic N).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ) ≤
      siftedSum (s := (apSieve q a N z hz).toBoundingSieve) + (⌊z⌋₊ : ℝ) := by
  have hsift : siftedSum (s := (apSieve q a N z hz).toBoundingSieve) =
      ((((Finset.range (N + 1)).filter (fun n => n % q = a % q)).filter
        (fun n => Nat.Coprime (apSieve q a N z hz).prodPrimes n)).card : ℝ) := by
    show (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = a % q),
      if Nat.Coprime (apSieve q a N z hz).prodPrimes n then (1 : ℝ) else 0) = _
    rw [Finset.sum_boole]
  have hsub : (Finset.Iic N).filter (fun p => p.Prime ∧ p % q = a % q) ⊆
      ((Finset.range (N + 1)).filter (fun n => n % q = a % q)).filter
        (fun n => Nat.Coprime (apSieve q a N z hz).prodPrimes n) ∪ Finset.Icc 1 ⌊z⌋₊ := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Iic] at hp
    obtain ⟨hpN, hpp, hpa⟩ := hp
    rw [Finset.mem_union]
    by_cases hpz : p ≤ ⌊z⌋₊
    · right
      rw [Finset.mem_Icc]
      exact ⟨hpp.one_lt.le, hpz⟩
    · left
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨by omega, hpa⟩, ?_⟩
      apply Nat.Coprime.symm
      rw [Nat.Prime.coprime_iff_not_dvd hpp]
      intro hdvd
      exact hpz ((prime_dvd_prodPrimes_iff q a N z hz hpp).mp hdvd).1
  have hcard := Finset.card_union_le (((Finset.range (N + 1)).filter
      (fun n => n % q = a % q)).filter (fun n => Nat.Coprime (apSieve q a N z hz).prodPrimes n))
    (Finset.Icc 1 ⌊z⌋₊)
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
  rw [hsift]
  have h1 := Finset.card_le_card hsub
  have h2 : ((Finset.Iic N).filter (fun p => p.Prime ∧ p % q = a % q)).card ≤
      (((Finset.range (N + 1)).filter (fun n => n % q = a % q)).filter
        (fun n => Nat.Coprime (apSieve q a N z hz).prodPrimes n)).card + ⌊z⌋₊ :=
    h1.trans hcard
  exact_mod_cast h2

/-- The Selberg lower bound for the sieve's bounding sum: `S ≥ (φ(q)/q) log √z`. -/
theorem boundingSum_ge (hq0 : 0 < q) :
    (q.totient : ℝ) / q * Real.log (Real.sqrt z) ≤ (apSieve q a N z hz).selbergBoundingSum := by
  have hsqrt1 : 1 ≤ Real.sqrt z := Real.one_le_sqrt.mpr hz
  have hCM : Sieve.CompletelyMultiplicative (apSieve q a N z hz).nu :=
    Sieve.CompletelyMultiplicative.zeta.pdiv Sieve.CompletelyMultiplicative.id
  have hnn : ∀ n, 0 ≤ (apSieve q a N z hz).nu n := by
    intro n
    show 0 ≤ ((ζ : ArithmeticFunction ℝ).pdiv .id) n
    rw [ArithmeticFunction.pdiv_apply]
    apply div_nonneg
    · by_cases h : n = 0 <;> simp [h]
    · simp
  refine le_trans ?_ (Sieve.selbergBoundingSum_ge_sum_div_filter (apSieve q a N z hz) hCM hnn
    (apSieve q a N z hz).nu_lt_one_of_prime)
  refine le_trans (totient_mul_log_le_harmAvoid q hq0 (Real.sqrt z) hsqrt1) ?_
  unfold harmAvoid
  calc ∑ n ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter (fun n => ∀ r ∈ q.primeFactors, ¬ r ∣ n),
        (1 / (n : ℝ))
      = ∑ n ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter (fun n => ∀ r ∈ q.primeFactors, ¬ r ∣ n),
          (apSieve q a N z hz).nu n := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mem_filter, Finset.mem_Icc] at hn
        have hn0 : n ≠ 0 := by
          obtain ⟨⟨hn1, _⟩, _⟩ := hn
          omega
        show _ = ((ζ : ArithmeticFunction ℝ).pdiv .id) n
        simp [ArithmeticFunction.pdiv_apply, hn0]
    _ ≤ _ := by
        classical
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [Finset.mem_filter, Finset.mem_Icc] at hn
          obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn
          refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hn2⟩, ?_⟩
          intro p hp hpn
          rw [prime_dvd_prodPrimes_iff q a N z hz hp]
          constructor
          · have hpn' : p ≤ n := Nat.le_of_dvd (by omega) hpn
            have hT : ⌊Real.sqrt z⌋₊ ≤ ⌊z⌋₊ := Nat.floor_mono (Sieve.sqrt_le_self z hz)
            omega
          · intro hpq
            exact hn3 p (Nat.mem_primeFactors.mpr ⟨hp, hpq, hq0.ne'⟩) hpn
        · intro i _ _
          exact hnn i

/-- The Selberg upper bound for the sifted progression. -/
theorem siftedSum_le (hq0 : 0 < q) (hz1 : 1 < z) :
    siftedSum (s := (apSieve q a N z hz).toBoundingSieve) ≤
      (((N : ℝ) + 1) / q) / ((q.totient : ℝ) / q * Real.log (Real.sqrt z)) +
        z * (1 + Real.log z) ^ 3 := by
  have hS := boundingSum_ge q a N z hz hq0
  have hpos : 0 < (q.totient : ℝ) / q * Real.log (Real.sqrt z) := by
    apply mul_pos
    · apply div_pos
      · exact_mod_cast Nat.totient_pos.mpr hq0
      · exact_mod_cast hq0
    · apply Real.log_pos
      exact Real.lt_sqrt_of_sq_lt (by norm_num; linarith)
  have herr := Sieve.rem_sum_le_of_const_of_dvd (apSieve q a N z hz) 1
    (fun d hd => abs_rem_le q a N z hz hq0 hd)
  have hX : 0 ≤ (apSieve q a N z hz).totalMass := by
    show 0 ≤ ((N : ℝ) + 1) / q
    positivity
  refine le_trans (SelbergSieve.selberg_bound_simple (apSieve q a N z hz)) ?_
  refine add_le_add (div_le_div_of_nonneg_left hX hpos hS) ?_
  refine le_trans herr (le_of_eq ?_)
  show 1 * z * (1 + Real.log z) ^ 3 = z * (1 + Real.log z) ^ 3
  rw [one_mul]

end APSieve

/-! ## The final estimate -/

/-- `4 (1 + log z)^3 log z ≤ 2000 z` for `z ≥ 1` (via `log z ≤ 4 z^{1/4}`). -/
theorem log_poly_bound (z : ℝ) (hz : 1 ≤ z) :
    4 * (1 + Real.log z) ^ 3 * Real.log z ≤ 2000 * z := by
  have hz0 : 0 ≤ z := by linarith
  have hlog : Real.log z ≤ z ^ ((1 : ℝ) / 4) / ((1 : ℝ) / 4) :=
    Real.log_le_rpow_div hz0 (by norm_num)
  have hv1 : 1 ≤ z ^ ((1 : ℝ) / 4) := Real.one_le_rpow hz (by norm_num)
  have hv4 : (z ^ ((1 : ℝ) / 4)) ^ 4 = z := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz0]
    norm_num
  have hl0 : 0 ≤ Real.log z := Real.log_nonneg hz
  have hl : Real.log z ≤ 4 * z ^ ((1 : ℝ) / 4) := by
    have : z ^ ((1 : ℝ) / 4) / ((1 : ℝ) / 4) = 4 * z ^ ((1 : ℝ) / 4) := by ring
    linarith
  have h1 : 1 + Real.log z ≤ 5 * z ^ ((1 : ℝ) / 4) := by linarith
  have h1' : (1 + Real.log z) ^ 3 ≤ (5 * z ^ ((1 : ℝ) / 4)) ^ 3 :=
    pow_le_pow_left₀ (by linarith) h1 3
  have h2 : 4 * (1 + Real.log z) ^ 3 ≤ 4 * (5 * z ^ ((1 : ℝ) / 4)) ^ 3 :=
    mul_le_mul_of_nonneg_left h1' (by norm_num)
  have hc : 0 ≤ 4 * (5 * z ^ ((1 : ℝ) / 4)) ^ 3 :=
    mul_nonneg (by norm_num) (pow_nonneg (by linarith) 3)
  calc 4 * (1 + Real.log z) ^ 3 * Real.log z
      ≤ 4 * (5 * z ^ ((1 : ℝ) / 4)) ^ 3 * (4 * z ^ ((1 : ℝ) / 4)) :=
        mul_le_mul h2 hl hl0 hc
    _ = 2000 * (z ^ ((1 : ℝ) / 4)) ^ 4 := by ring
    _ = 2000 * z := by rw [hv4]

/-- **Brun–Titchmarsh in arithmetic progressions.** For every `q ≥ 1`, every `a` and every real
`x > q`, `π(x; q, a) ≤ 2008 x / (φ(q) log (x / q))`, where
`π(x; q, a) = #{p ≤ x prime : p ≡ a (mod q)}`. -/
theorem brun_titchmarsh_ap (q a : ℕ) (hq : 1 ≤ q) (x : ℝ) (hx : (q : ℝ) < x) :
    (((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ) ≤
      2008 * x / ((q.totient : ℝ) * Real.log (x / q)) := by
  have hq0 : 0 < q := hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hx1 : 1 < x := lt_of_le_of_lt hq1R hx
  have hy1 : 1 < x / q := by rw [one_lt_div hqR]; exact hx
  have hy0 : 0 ≤ x / q := by linarith
  have hz1 : 1 < Real.sqrt (x / q) := Real.lt_sqrt_of_sq_lt (by norm_num; linarith)
  have hz1' : 1 ≤ Real.sqrt (x / q) := hz1.le
  have hz0 : 0 ≤ Real.sqrt (x / q) := Real.sqrt_nonneg _
  have hmain := card_primes_le q a ⌊x⌋₊ (Real.sqrt (x / q)) hz1'
  have hsift := siftedSum_le q a ⌊x⌋₊ (Real.sqrt (x / q)) hz1' hq0 hz1
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hL : 0 < Real.log (x / q) := Real.log_pos hy1
  have hlogz : Real.log (Real.sqrt (x / q)) = Real.log (x / q) / 2 := Real.log_sqrt hy0
  have hlogsz : Real.log (Real.sqrt (Real.sqrt (x / q))) = Real.log (x / q) / 4 := by
    rw [Real.log_sqrt hz0, hlogz]
    ring
  have hzy : Real.sqrt (x / q) ^ 2 = x / q := Real.sq_sqrt hy0
  have hNx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
  -- the main term, multiplied out
  have ht1 : (((⌊x⌋₊ : ℝ) + 1) / q) / ((q.totient : ℝ) / q *
      Real.log (Real.sqrt (Real.sqrt (x / q)))) * ((q.totient : ℝ) * Real.log (x / q))
      = 4 * ((⌊x⌋₊ : ℝ) + 1) := by
    have hq' : (q : ℝ) ≠ 0 := hqR.ne'
    have hφ' : (q.totient : ℝ) ≠ 0 := hφ.ne'
    have hL' : Real.log (x / q) ≠ 0 := hL.ne'
    rw [hlogsz]
    field_simp
  -- the remainder and the unsifted small primes, multiplied out
  have hpoly := log_poly_bound (Real.sqrt (x / q)) hz1'
  have hfl : ((⌊Real.sqrt (x / q)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (x / q) := Nat.floor_le hz0
  have hlz0 : 0 ≤ Real.log (Real.sqrt (x / q)) := Real.log_nonneg hz1'
  have hone : 1 ≤ (1 + Real.log (Real.sqrt (x / q))) ^ 3 := one_le_pow₀ (by linarith)
  have hzle : Real.sqrt (x / q) ≤ Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 :=
    le_mul_of_one_le_right hz0 hone
  have ht2 : (Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 +
      ((⌊Real.sqrt (x / q)⌋₊ : ℕ) : ℝ)) * ((q.totient : ℝ) * Real.log (x / q)) ≤ 2000 * x := by
    have h2 : Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 +
        ((⌊Real.sqrt (x / q)⌋₊ : ℕ) : ℝ) ≤
          2 * Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 := by linarith
    have hA : 0 ≤ 2 * Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 := by
      positivity
    have hLz : Real.log (x / q) = 2 * Real.log (Real.sqrt (x / q)) := by linarith
    calc (Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 +
          ((⌊Real.sqrt (x / q)⌋₊ : ℕ) : ℝ)) * ((q.totient : ℝ) * Real.log (x / q))
        ≤ (2 * Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3) *
            ((q : ℝ) * Real.log (x / q)) :=
          mul_le_mul h2 (mul_le_mul_of_nonneg_right hφq hL.le) (by positivity) hA
      _ = Real.sqrt (x / q) * (4 * (1 + Real.log (Real.sqrt (x / q))) ^ 3 *
            Real.log (Real.sqrt (x / q))) * q := by
          rw [hLz]
          ring
      _ ≤ Real.sqrt (x / q) * (2000 * Real.sqrt (x / q)) * q :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hz0) hqR.le
      _ = 2000 * (Real.sqrt (x / q) ^ 2 * q) := by ring
      _ = 2000 * x := by
          rw [hzy, div_mul_cancel₀ x hqR.ne']
  have hπ : (((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ) ≤
      (((⌊x⌋₊ : ℝ) + 1) / q) / ((q.totient : ℝ) / q *
        Real.log (Real.sqrt (Real.sqrt (x / q)))) +
      (Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 +
        ((⌊Real.sqrt (x / q)⌋₊ : ℕ) : ℝ)) := by
    linarith
  rw [le_div_iff₀ (mul_pos hφ hL)]
  have hφL : 0 ≤ (q.totient : ℝ) * Real.log (x / q) := (mul_pos hφ hL).le
  calc (((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ) *
        ((q.totient : ℝ) * Real.log (x / q))
      ≤ ((((⌊x⌋₊ : ℝ) + 1) / q) / ((q.totient : ℝ) / q *
          Real.log (Real.sqrt (Real.sqrt (x / q)))) +
        (Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 +
          ((⌊Real.sqrt (x / q)⌋₊ : ℕ) : ℝ))) * ((q.totient : ℝ) * Real.log (x / q)) :=
        mul_le_mul_of_nonneg_right hπ hφL
    _ = (((⌊x⌋₊ : ℝ) + 1) / q) / ((q.totient : ℝ) / q *
          Real.log (Real.sqrt (Real.sqrt (x / q)))) * ((q.totient : ℝ) * Real.log (x / q)) +
        (Real.sqrt (x / q) * (1 + Real.log (Real.sqrt (x / q))) ^ 3 +
          ((⌊Real.sqrt (x / q)⌋₊ : ℕ) : ℝ)) * ((q.totient : ℝ) * Real.log (x / q)) := by ring
    _ ≤ 4 * ((⌊x⌋₊ : ℝ) + 1) + 2000 * x := by
        rw [ht1]
        linarith
    _ ≤ 2008 * x := by linarith

end Principia.Common.BrunTitchmarshAP

end
