/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

set_option autoImplicit false

/-!
# The colossally-abundant comparison for `σ(m)/m`, in integers

For `N ≥ 1` put `W(q) = σ(q)^N / q^{N+1}` (so `W(m) = (σ(m)/m)^N / m`). `W` is multiplicative, so
if a number `M` maximises `W` *prime by prime* — `W(p^k) ≤ W(p^{v_p(M)})` for every prime `p` and
every `k ≥ 0` — then `W(m) ≤ W(M)` for every `m ≥ 1`, i.e. `σ(m)/m ≤ (σ(M)/M) (m/M)^{1/N}`. This is
the colossally-abundant bound `σ(m)/m ≤ F(ε) m^ε` at `ε = 1/N`, with all denominators cleared so
that everything is a statement about natural numbers.

* `sigma_pow_mul_le_of_local` — the comparison
  `σ(m)^N M^{N+1} ≤ σ(M)^N m^{N+1}` from the prime-by-prime hypothesis.
* `lt_ten_mul_of_ca` — the arithmetic that turns the comparison and one numerical inequality
  `σ(M)^N X < 10^N M^{N+1}` into `σ(m) < 10 m` for `1 ≤ m ≤ X`.
* The prime-by-prime hypothesis is infinite in `k`; `compare_of_tail` reduces it to finitely many
  `k` using `(p − 1) σ(p^k) < p^{k+1}`, and `checkPrime` / `compare_of_checkPrime` package the
  finite part as a kernel-evaluable Boolean (`geo p k = (p^{k+1} − 1)/(p − 1) = σ(p^k)`).
* A number given as a list of prime powers: `mulPow`, `sigPow`, `expOf`, with
  `factorization_mulPow` (`v_q(∏ p^e) = expOf L q`) and `sigma_mulPow` (`σ(∏ p^e) = ∏ geo p e`
  under a coprimality check), and `compare_of_checkList` (one Boolean for the whole list).
-/

namespace Principia.Common.SmallAbundancy

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-! ## Geometric sums -/

/-- `(p^{k+1} − 1)/(p − 1)`, the value of `σ(p^k)` for a prime `p`, in a kernel-evaluable form. -/
def geo (p k : ℕ) : ℕ := (p ^ (k + 1) - 1) / (p - 1)

/-- `σ(p^k) = (p^{k+1} − 1)/(p − 1)`. -/
theorem sigma_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : σ 1 (p ^ k) = geo p k := by
  rw [sigma_one_apply_prime_pow hp, Nat.geomSum_eq hp.two_le]
  rfl

/-- `(p − 1) σ(p^k) < p^{k+1}` (indeed `(p − 1) σ(p^k) + 1 = p^{k+1}`). -/
theorem pred_mul_sigma_lt {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p - 1) * σ 1 (p ^ k) < p ^ (k + 1) := by
  rw [sigma_one_apply_prime_pow hp]
  have h := geom_sum_mul_add (p - 1) (k + 1)
  rw [Nat.sub_add_cancel hp.one_le] at h
  calc (p - 1) * ∑ i ∈ range (k + 1), p ^ i = (∑ i ∈ range (k + 1), p ^ i) * (p - 1) :=
        Nat.mul_comm _ _
    _ < (∑ i ∈ range (k + 1), p ^ i) * (p - 1) + 1 := Nat.lt_succ_self _
    _ = p ^ (k + 1) := h

/-! ## One prime: the tail and the finite check -/

/-- **The tail.** If `p^N p^{e(N+1)} ≤ σ(p^e)^N (p − 1)^N p^A`, then
`σ(p^k)^N p^{e(N+1)} ≤ σ(p^e)^N p^{k(N+1)}` for every `k ≥ A`. -/
theorem compare_of_tail {N p e A : ℕ} (hp : p.Prime)
    (htail : p ^ N * p ^ (e * (N + 1)) ≤ σ 1 (p ^ e) ^ N * (p - 1) ^ N * p ^ A)
    {k : ℕ} (hk : A ≤ k) :
    σ 1 (p ^ k) ^ N * p ^ (e * (N + 1)) ≤ σ 1 (p ^ e) ^ N * p ^ (k * (N + 1)) := by
  have hq : 0 < (p - 1) ^ N := Nat.pow_pos (Nat.sub_pos_of_lt hp.one_lt)
  refine Nat.le_of_mul_le_mul_left ?_ hq
  have h1 : ((p - 1) * σ 1 (p ^ k)) ^ N ≤ (p ^ (k + 1)) ^ N :=
    Nat.pow_le_pow_left (pred_mul_sigma_lt hp k).le N
  have h2 : p ^ A ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
  calc (p - 1) ^ N * (σ 1 (p ^ k) ^ N * p ^ (e * (N + 1)))
      = ((p - 1) * σ 1 (p ^ k)) ^ N * p ^ (e * (N + 1)) := by rw [mul_pow]; ring
    _ ≤ (p ^ (k + 1)) ^ N * p ^ (e * (N + 1)) := Nat.mul_le_mul_right _ h1
    _ = p ^ (k * N) * (p ^ N * p ^ (e * (N + 1))) := by ring
    _ ≤ p ^ (k * N) * (σ 1 (p ^ e) ^ N * (p - 1) ^ N * p ^ A) := Nat.mul_le_mul_left _ htail
    _ ≤ p ^ (k * N) * (σ 1 (p ^ e) ^ N * (p - 1) ^ N * p ^ k) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
    _ = (p - 1) ^ N * (σ 1 (p ^ e) ^ N * p ^ (k * (N + 1))) := by ring

/-- The finite check for one prime `p` with chosen exponent `e` and tail start `A`: the comparison
at every `k < A`, and the tail inequality at `A`. -/
def checkPrime (N p e A : ℕ) : Bool :=
  (List.range A).all (fun k =>
      decide (geo p k ^ N * p ^ (e * (N + 1)) ≤ geo p e ^ N * p ^ (k * (N + 1)))) &&
    decide (p ^ N * p ^ (e * (N + 1)) ≤ geo p e ^ N * (p - 1) ^ N * p ^ A)

/-- Soundness of `checkPrime`: the comparison `W(p^k) ≤ W(p^e)` for **every** `k`. -/
theorem compare_of_checkPrime {N p e A : ℕ} (hp : p.Prime) (h : checkPrime N p e A = true)
    (k : ℕ) :
    σ 1 (p ^ k) ^ N * p ^ (e * (N + 1)) ≤ σ 1 (p ^ e) ^ N * p ^ (k * (N + 1)) := by
  simp only [checkPrime, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  rcases Nat.lt_or_ge k A with hk | hk
  · rw [sigma_prime_pow hp, sigma_prime_pow hp]
    exact h.1 k hk
  · refine compare_of_tail hp ?_ hk
    rw [sigma_prime_pow hp]
    exact h.2

/-! ## Multiplicativity: from prime powers to all `m` -/

/-- **The colossally-abundant comparison.** If `W(p^k) ≤ W(p^{v_p(M)})` for every prime `p` and
every `k` (denominators cleared), then `σ(m)^N M^{N+1} ≤ σ(M)^N m^{N+1}` for every `m ≥ 1`. -/
theorem sigma_pow_mul_le_of_local {N M : ℕ} (hM : M ≠ 0)
    (hloc : ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      σ 1 (p ^ k) ^ N * p ^ (M.factorization p * (N + 1)) ≤
        σ 1 (p ^ M.factorization p) ^ N * p ^ (k * (N + 1)))
    {m : ℕ} (hm : m ≠ 0) :
    σ 1 m ^ N * M ^ (N + 1) ≤ σ 1 M ^ N * m ^ (N + 1) := by
  classical
  set S := m.primeFactors ∪ M.primeFactors with hSdef
  have hσ : ∀ n : ℕ, n ≠ 0 → n.primeFactors ⊆ S →
      σ 1 n = ∏ p ∈ S, σ 1 (p ^ n.factorization p) := by
    intro n hn hS
    rw [IsMultiplicative.multiplicative_factorization (σ 1) isMultiplicative_sigma hn]
    refine Finsupp.prod_of_support_subset _ hS (fun p k => σ 1 (p ^ k)) (fun p _ => ?_)
    rw [pow_zero]
    exact isMultiplicative_sigma.map_one
  have hn : ∀ n : ℕ, n ≠ 0 → n.primeFactors ⊆ S → n = ∏ p ∈ S, p ^ n.factorization p := by
    intro n hn hS
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    exact Finsupp.prod_of_support_subset _ hS (fun p k => p ^ k) (fun p _ => pow_zero p)
  have hmS : m.primeFactors ⊆ S := Finset.subset_union_left
  have hMS : M.primeFactors ⊆ S := Finset.subset_union_right
  have expand : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → a.primeFactors ⊆ S → b.primeFactors ⊆ S →
      σ 1 a ^ N * b ^ (N + 1) =
        ∏ p ∈ S, (σ 1 (p ^ a.factorization p) ^ N * p ^ (b.factorization p * (N + 1))) := by
    intro a b ha hb haS hbS
    rw [Finset.prod_mul_distrib, Finset.prod_pow]
    simp_rw [pow_mul]
    rw [Finset.prod_pow, ← hσ a ha haS, ← hn b hb hbS]
  rw [expand m M hm hM hmS hMS, expand M m hM hm hMS hmS]
  refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun p hp => ?_)
  have hpr : p.Prime := by
    rcases Finset.mem_union.1 hp with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · exact Nat.prime_of_mem_primeFactors h
  exact hloc p hpr (m.factorization p)

/-- **From the comparison to `σ(m) < 10 m`.** If `s^N M^{N+1} ≤ S^N m^{N+1}` (the comparison with
`s = σ(m)`, `S = σ(M)`) and `S^N X < 10^N M^{N+1}`, then `s < 10 m` for `1 ≤ m ≤ X`. -/
theorem lt_ten_mul_of_ca {N X M S m s : ℕ} (hm : 0 < m) (hmX : m ≤ X)
    (hca : s ^ N * M ^ (N + 1) ≤ S ^ N * m ^ (N + 1))
    (hfin : S ^ N * X < 10 ^ N * M ^ (N + 1)) : s < 10 * m := by
  by_contra hcon
  have hle : 10 * m ≤ s := Nat.le_of_not_lt hcon
  have hmN : 0 < m ^ N := Nat.pow_pos hm
  have h1 : m ^ N * (10 ^ N * M ^ (N + 1)) ≤ m ^ N * (S ^ N * X) :=
    calc m ^ N * (10 ^ N * M ^ (N + 1)) = (10 * m) ^ N * M ^ (N + 1) := by ring
      _ ≤ s ^ N * M ^ (N + 1) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hle N)
      _ ≤ S ^ N * m ^ (N + 1) := hca
      _ = m ^ N * (S ^ N * m) := by ring
      _ ≤ m ^ N * (S ^ N * X) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hmX)
  exact absurd (Nat.le_of_mul_le_mul_left h1 hmN) (Nat.not_le.2 hfin)

/-! ## Numbers given as a list of prime powers `(p, e, A)` -/

/-- `∏ p^e` over a list of triples `(p, e, A)` (`A` is the tail start used by `checkList`). -/
def mulPow : List (ℕ × ℕ × ℕ) → ℕ
  | [] => 1
  | (p, e, _) :: t => p ^ e * mulPow t

/-- `∏ geo p e` over a list of triples `(p, e, A)`. -/
def sigPow : List (ℕ × ℕ × ℕ) → ℕ
  | [] => 1
  | (p, e, _) :: t => geo p e * sigPow t

/-- The exponent of `q` in `mulPow L`, read off the list (summed over repeated entries). -/
def expOf : List (ℕ × ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (p, e, _) :: t, q => (if p = q then e else 0) + expOf t q

/-- Each head prime is coprime to the product of the later prime powers. -/
def copCheck : List (ℕ × ℕ × ℕ) → Bool
  | [] => true
  | (p, _, _) :: t => Nat.gcd p (mulPow t) == 1 && copCheck t

/-- `checkPrime` for every entry, at the exponent `expOf L p` the entry's prime has in
`mulPow L`. -/
def checkList (N : ℕ) (L : List (ℕ × ℕ × ℕ)) : Bool :=
  L.all (fun x => checkPrime N x.1 (expOf L x.1) x.2.2)

theorem mulPow_ne_zero : ∀ L : List (ℕ × ℕ × ℕ), (∀ x ∈ L, x.1.Prime) → mulPow L ≠ 0
  | [], _ => by simp [mulPow]
  | (p, e, A) :: t, h => by
    have hp : p.Prime := h (p, e, A) List.mem_cons_self
    have ht : ∀ x ∈ t, x.1.Prime := fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [mulPow]
    exact Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (mulPow_ne_zero t ht)

/-- `v_q(∏ p^e) = expOf L q`. -/
theorem factorization_mulPow : ∀ L : List (ℕ × ℕ × ℕ), (∀ x ∈ L, x.1.Prime) →
    ∀ q : ℕ, (mulPow L).factorization q = expOf L q
  | [], _, q => by simp [mulPow, expOf]
  | (p, e, A) :: t, h, q => by
    have hp : p.Prime := h (p, e, A) List.mem_cons_self
    have ht : ∀ x ∈ t, x.1.Prime := fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [mulPow, expOf, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (mulPow_ne_zero t ht),
      Finsupp.add_apply, hp.factorization_pow, Finsupp.single_apply, factorization_mulPow t ht q]

/-- `expOf L q = 0` when `q` is not the prime of any entry. -/
theorem expOf_eq_zero : ∀ (L : List (ℕ × ℕ × ℕ)) (q : ℕ), (∀ x ∈ L, x.1 ≠ q) → expOf L q = 0
  | [], _, _ => rfl
  | (p, e, A) :: t, q, h => by
    have hpq : p ≠ q := h (p, e, A) List.mem_cons_self
    rw [expOf, if_neg hpq, expOf_eq_zero t q (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- `σ(∏ p^e) = ∏ geo p e` for a list of primes, each coprime to the later prime powers. -/
theorem sigma_mulPow : ∀ L : List (ℕ × ℕ × ℕ), (∀ x ∈ L, x.1.Prime) → copCheck L = true →
    σ 1 (mulPow L) = sigPow L
  | [], _, _ => by
    rw [mulPow, sigPow]
    exact isMultiplicative_sigma.map_one
  | (p, e, A) :: t, h, hc => by
    simp only [copCheck, Bool.and_eq_true, beq_iff_eq] at hc
    have hp : p.Prime := h (p, e, A) List.mem_cons_self
    have ht : ∀ x ∈ t, x.1.Prime := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hcop : Nat.Coprime (p ^ e) (mulPow t) := Nat.Coprime.pow_left e hc.1
    rw [mulPow, sigPow, ← sigma_mulPow t ht hc.2,
      isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_prime_pow hp]

/-- Soundness of `checkList`: for the prime `p` of any entry, `W(p^k) ≤ W(p^{v_p(mulPow L)})`
for every `k`. -/
theorem compare_of_checkList {N : ℕ} {L : List (ℕ × ℕ × ℕ)} (hL : checkList N L = true)
    (hpr : ∀ x ∈ L, x.1.Prime) {p : ℕ} (hp : p ∈ L.map Prod.fst) (k : ℕ) :
    σ 1 (p ^ k) ^ N * p ^ ((mulPow L).factorization p * (N + 1)) ≤
      σ 1 (p ^ (mulPow L).factorization p) ^ N * p ^ (k * (N + 1)) := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
  rw [factorization_mulPow L hpr]
  have hc : checkPrime N x.1 (expOf L x.1) x.2.2 = true := List.all_eq_true.1 hL x hx
  exact compare_of_checkPrime (hpr x hx) hc k

end Principia.Common.SmallAbundancy
