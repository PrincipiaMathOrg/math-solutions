/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Aliquot.DP
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false

/-!
# The divisor sum over a modulus as an iterated sum over prime powers

For a modulus `Q` put `wQ Q g = φ(Q/g)/Q` (the density of `{N : gcd(N, Q) = g}`) and
`hRatio g = σ(g)/g`. For `Q = p^e Q'` with `p ∤ Q'` (`peel`):
```
∑_{g ∣ Q, p^lo ∣ g} wQ Q g · Φ(hRatio g)
  = ∑_{lo ≤ a ≤ e} wt p e a · ∑_{b ∣ Q'} wQ Q' b · Φ(rat p a · hRatio b),
```
because `g = p^a b`, `φ(Q/g) = φ(p^{e−a}) φ(Q'/b)`, `φ(p^{e−a})/p^e = wt p e a` and
`σ(p^a b)/(p^a b) = rat p a · σ(b)/b`. Iterating over a list of prime powers (`Ex_eq_divSum`,
`Ex_head_eq`) identifies the iterated sum `Ex` of `Aliquot/DP.lean` with the divisor sum.
-/

namespace Principia.Common.Aliquot

open Finset

/-- `wQ Q g = φ(Q/g)/Q`. -/
noncomputable def wQ (Q g : ℕ) : ℝ := (Nat.totient (Q / g) : ℝ) / Q

/-- `hRatio g = σ(g)/g`. -/
noncomputable def hRatio (g : ℕ) : ℝ := (ArithmeticFunction.sigma 1 g : ℝ) / g

/-- `Q(L) = ∏ p^e` over the list. -/
def QL (L : List (ℕ × ℕ × ℕ)) : ℕ := (L.map (fun q => q.1 ^ q.2.1)).prod

/-- A tail list: distinct primes (each coprime to the product of the later ones), `lo = 0`. -/
def ValidTail : List (ℕ × ℕ × ℕ) → Prop
  | [] => True
  | q :: L => q.1.Prime ∧ Nat.Coprime q.1 (QL L) ∧ q.2.2 = 0 ∧ ValidTail L

theorem QL_nil : QL [] = 1 := rfl

theorem QL_cons (q : ℕ × ℕ × ℕ) (L : List (ℕ × ℕ × ℕ)) : QL (q :: L) = q.1 ^ q.2.1 * QL L := by
  simp [QL]

theorem QL_pos : ∀ (L : List (ℕ × ℕ × ℕ)), ValidTail L → 0 < QL L
  | [], _ => by simp [QL_nil]
  | q :: L, h => by
      rw [QL_cons]
      exact Nat.mul_pos (pow_pos h.1.pos _) (QL_pos L h.2.2.2)

/-- `σ(p^a) = sigPP p a` for a prime `p`. -/
theorem sigma_prime_pow_eq {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ArithmeticFunction.sigma 1 (p ^ a) = sigPP p a := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, Nat.geomSum_eq hp.two_le]
  rfl

/-- `φ(p^{e−a})/p^e = wt p e a` for `a ≤ e`. -/
theorem totient_div_eq_wt {p : ℕ} (hp : p.Prime) {e a : ℕ} (hae : a ≤ e) :
    (Nat.totient (p ^ (e - a)) : ℝ) / ((p ^ e : ℕ) : ℝ) = wt p e a := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold wt wNum wDen
  rcases lt_or_eq_of_le hae with h | h
  · rw [if_pos h, if_pos h]
    have hk : e - a = (e - a - 1) + 1 := by omega
    rw [hk, Nat.totient_prime_pow_succ hp]
    have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_le]
      simp
    have hpow : (p : ℝ) ^ e = (p : ℝ) ^ (e - a - 1) * (p : ℝ) ^ (a + 1) := by
      rw [← pow_add]
      congr 1
      omega
    push_cast
    rw [hp1, hpow]
    have h1 : (p : ℝ) ^ (e - a - 1) ≠ 0 := by positivity
    have h2 : (p : ℝ) ^ (a + 1) ≠ 0 := by positivity
    field_simp
  · subst h
    rw [if_neg (lt_irrefl a), if_neg (lt_irrefl a), Nat.sub_self, pow_zero, Nat.totient_one]

/-- A divisor sum over `m n` with `gcd(m, n) = 1` is a double sum over the divisors of `m`, `n`. -/
theorem sum_divisors_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) (f : ℕ → ℝ) :
    ∑ d ∈ (m * n).divisors, f d = ∑ a ∈ m.divisors, ∑ b ∈ n.divisors, f (a * b) := by
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image h.mul_injOn_divisors,
    Finset.sum_product]

/-- **Peeling one prime power off the modulus.** -/
theorem peel (p e lo Q' : ℕ) (hp : p.Prime) (hQ' : 0 < Q') (hcop : Nat.Coprime p Q')
    (Φ : ℝ → ℝ) :
    ∑ g ∈ (p ^ e * Q').divisors.filter (p ^ lo ∣ ·), wQ (p ^ e * Q') g * Φ (hRatio g) =
      ∑ a ∈ Finset.Icc lo e, wt p e a *
        ∑ b ∈ Q'.divisors, wQ Q' b * Φ (rat p a * hRatio b) := by
  have hcop' : Nat.Coprime (p ^ e) Q' := Nat.Coprime.pow_left e hcop
  rw [Finset.sum_filter, sum_divisors_mul_of_coprime hcop', Nat.divisors_prime_pow hp,
    Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  -- rewrite the outer range sum as a sum over `Icc lo e`
  have hrange : ∀ f : ℕ → ℝ, ∑ i ∈ Finset.range (e + 1), (if lo ≤ i then f i else 0) =
      ∑ a ∈ Finset.Icc lo e, f a := by
    intro f
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [← hrange]
  apply Finset.sum_congr rfl
  intro i hi
  have hie : i ≤ e := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  split_ifs with hlo
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    have hbQ : b ∣ Q' := Nat.dvd_of_mem_divisors hb
    have hb0 : 0 < b := Nat.pos_of_mem_divisors hb
    have hcopb : Nat.Coprime p b := Nat.Coprime.coprime_dvd_right hbQ hcop
    have hdvd : p ^ lo ∣ p ^ i * b :=
      Dvd.dvd.mul_right (Nat.pow_dvd_pow p hlo) b
    rw [if_pos hdvd]
    -- the weight
    have hw : wQ (p ^ e * Q') (p ^ i * b) = wt p e i * wQ Q' b := by
      unfold wQ
      have hdiv : p ^ e * Q' / (p ^ i * b) = p ^ (e - i) * (Q' / b) := by
        rw [← Nat.div_mul_div_comm (Nat.pow_dvd_pow p hie) hbQ, Nat.pow_div hie hp.pos]
      have hcop2 : Nat.Coprime (p ^ (e - i)) (Q' / b) :=
        Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hbQ) hcop)
      rw [hdiv, Nat.totient_mul hcop2, ← totient_div_eq_wt hp hie]
      push_cast
      have hpe : (0 : ℝ) < (p : ℝ) ^ e := by
        have : (0 : ℝ) < p := by exact_mod_cast hp.pos
        positivity
      have hQr : (0 : ℝ) < Q' := by exact_mod_cast hQ'
      field_simp
    -- the abundancy
    have hh : hRatio (p ^ i * b) = rat p i * hRatio b := by
      unfold hRatio rat
      have hcopib : Nat.Coprime (p ^ i) b := Nat.Coprime.pow_left i hcopb
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopib,
        sigma_prime_pow_eq hp]
      have hpi : (0 : ℝ) < (p : ℝ) ^ i := by
        have : (0 : ℝ) < p := by exact_mod_cast hp.pos
        positivity
      have hbr : (0 : ℝ) < b := by exact_mod_cast hb0
      push_cast
      field_simp
    rw [hw, hh]
    ring
  · apply Finset.sum_eq_zero
    intro b hb
    have hbQ : b ∣ Q' := Nat.dvd_of_mem_divisors hb
    have hcopb : Nat.Coprime (p ^ lo) b :=
      Nat.Coprime.pow_left lo (Nat.Coprime.coprime_dvd_right hbQ hcop)
    have hndvd : ¬ p ^ lo ∣ p ^ i * b := by
      intro h
      have h1 : p ^ lo ∣ p ^ i := hcopb.dvd_of_dvd_mul_right h
      exact hlo ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h1)
    rw [if_neg hndvd]

/-- **`Ex` of a tail list is the divisor sum over `Q(L)`.** -/
theorem Ex_eq_divSum : ∀ (L : List (ℕ × ℕ × ℕ)), ValidTail L → ∀ Φ : ℝ → ℝ,
    Ex L Φ = ∑ g ∈ (QL L).divisors, wQ (QL L) g * Φ (hRatio g)
  | [], _, Φ => by
      simp [Ex, QL_nil, wQ, hRatio]
  | q :: L, h, Φ => by
      obtain ⟨hp, hcop, hlo, hL⟩ := h
      have hQ := QL_pos L hL
      have key := peel q.1 q.2.1 0 (QL L) hp hQ hcop Φ
      rw [pow_zero, Finset.filter_true_of_mem (fun g _ => one_dvd g)] at key
      rw [QL_cons, key]
      simp only [Ex]
      rw [hlo]
      apply Finset.sum_congr rfl
      intro a _
      rw [Ex_eq_divSum L hL]

/-- **`Ex` of a list with a constrained head** is the divisor sum over the divisors `g` of
`Q(L)` with `p^lo ∣ g`. -/
theorem Ex_head_eq (p e lo : ℕ) (L : List (ℕ × ℕ × ℕ)) (hp : p.Prime)
    (hcop : Nat.Coprime p (QL L)) (hL : ValidTail L) (Φ : ℝ → ℝ) :
    Ex ((p, e, lo) :: L) Φ =
      ∑ g ∈ (QL ((p, e, lo) :: L)).divisors.filter (p ^ lo ∣ ·),
        wQ (QL ((p, e, lo) :: L)) g * Φ (hRatio g) := by
  rw [QL_cons, peel p e lo (QL L) hp (QL_pos L hL) hcop Φ]
  simp only [Ex]
  apply Finset.sum_congr rfl
  intro a _
  rw [Ex_eq_divSum L hL]

end Principia.Common.Aliquot
