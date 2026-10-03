import Principia.Common.Sieve.BrunTitchmarshAP
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Squarefree

set_option autoImplicit false

/-!
# The two-dimensional upper-bound sieve (Halberstam–Richert, Theorem 2.2 for two forms)

For coprime `a₁, a₂ ≥ 1` and `D = a₁ b₂ − a₂ b₁ ≠ 0`, every `u ∈ ℤ` and every real `T ≥ 2`,
`#{t ∈ [u, u + ⌊T⌋] : a₁ t + b₁ and a₂ t + b₂ both prime}
  ≤ 2^28 · T/(log T)^2 · a₁/φ(a₁) · a₂/φ(a₂) · |D|/φ(|D|)`
(`Principia.Common.TwoDimSieve.two_dim_sieve`). The constant is not optimised.

## Route (Selberg's Λ² sieve, from the PNT+ port in this directory)

* **Degenerate forms.** If `gcd(aᵢ, bᵢ) > 1`, the form `aᵢ t + bᵢ` takes at most one prime value
  (`card_prime_values_le_one`). Otherwise every prime `p` has `ρ(p) ∈ {1, 2}` roots of
  `F(t) = (a₁ t + b₁)(a₂ t + b₂)` modulo `p`: `ρ(p) = 1` if `p ∣ E = a₁ a₂ |D|`, else `2`
  (`rc_prime`, computed in the field `ZMod p`; `gcd(a₁, a₂) = 1` rules out `ρ(p) = 0`).
* **The sieve** `twoSieve`: the values `|F(t)|`, `t ∈ [u, u + L]`, weighted by multiplicity, sifted
  by the odd primes `p ≤ z`, with the completely multiplicative density `ν(p) = ρ(p)/p < 1` and
  total mass `L + 1`.
* **Remainders.** For squarefree `d ∣ P` the root count `ρ(d)` is multiplicative (Chinese
  remainder theorem, `rc_mul`), the multiples of `d` among the `F(t)` are `ρ(d)` residue classes
  of `t`, each of size `(L+1)/d + O(1)`, so `|R_d| ≤ ρ(d) ≤ 2^{ω(d)}` (`abs_rem_le`) and the Selberg
  error is `≤ z (1 + log z)^6` (`errSum_le`).
* **Main term.** `Sieve.selbergBoundingSum_ge_sum_div_filter` bounds the Selberg sum below by
  `∑_{m ≤ √z odd} ν(m)`; every pair `a, b ≤ z^{1/4}` with `a` odd and `b` prime to `2E` has
  `ab` in that range, and a divisor count (`card_divisors_avoid_le`) gives
  `∑ ν(m) ≥ (∑ 1/a)(∑ 1/b) ≥ (½ log z^{1/4}) (φ(2E)/(2E)) log z^{1/4}` (`boundingSum_ge`). This is
  the singular series to the **first** power; excluding the primes of `E` from the sieve instead
  would square it.
* **Parameters.** `z = √T` (`count_le_nondeg`, `err_bound`, `two_disc_le`, `two_dim_sieve`).
-/

noncomputable section

open scoped ArithmeticFunction ArithmeticFunction.omega
open BoundingSieve SelbergSieve

namespace Principia.Common.TwoDimSieve

/-! ## Completely multiplicative functions from prime values -/

/-- The completely multiplicative function with value `c p` at each prime `p`:
`n ↦ ∏_{p^e ∥ n} c(p)^e`, and `0 ↦ 0`. -/
def cmOf (c : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod (fun p e => c p ^ e), by simp⟩

theorem cmOf_apply (c : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    cmOf c n = n.factorization.prod (fun p e => c p ^ e) := by
  change (if n = 0 then (0 : ℝ) else _) = _
  rw [if_neg hn]

theorem cmOf_zero (c : ℕ → ℝ) : cmOf c 0 = 0 :=
  ArithmeticFunction.map_zero

theorem cmOf_cm (c : ℕ → ℝ) : Sieve.CompletelyMultiplicative (cmOf c) := by
  constructor
  · rw [cmOf_apply c one_ne_zero, Nat.factorization_one, Finsupp.prod_zero_index]
  · intro a b
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      rw [zero_mul, cmOf_zero, zero_mul]
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      rw [mul_zero, cmOf_zero, mul_zero]
    rw [cmOf_apply c (Nat.mul_ne_zero ha.ne' hb.ne'), cmOf_apply c ha.ne', cmOf_apply c hb.ne',
      Nat.factorization_mul ha.ne' hb.ne']
    exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem cmOf_prime (c : ℕ → ℝ) {p : ℕ} (hp : p.Prime) : cmOf c p = c p := by
  rw [cmOf_apply c hp.ne_zero, hp.factorization,
    Finsupp.prod_single_index (h := fun p e => c p ^ e) (pow_zero (c p))]
  exact pow_one (c p)

theorem cmOf_squarefree (c : ℕ → ℝ) {d : ℕ} (hd : Squarefree d) :
    cmOf c d = ∏ p ∈ d.primeFactors, c p := by
  rw [← ArithmeticFunction.IsMultiplicative.prod_factors_of_mult (cmOf c)
    (cmOf_cm c).isMultiplicative hd]
  exact Finset.prod_congr rfl (fun p hp => cmOf_prime c (Nat.prime_of_mem_primeFactors hp))

theorem cmOf_nonneg (c : ℕ → ℝ) (hc : ∀ p, 0 ≤ c p) (n : ℕ) : 0 ≤ cmOf c n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn, cmOf_zero]
  · rw [cmOf_apply c hn.ne']
    unfold Finsupp.prod
    exact Finset.prod_nonneg (fun p _ => pow_nonneg (hc p) _)

/-! ## The two linear forms and their local root counts -/

section Forms

variable (a₁ a₂ : ℕ) (b₁ b₂ : ℤ)

/-- The determinant `a₁ b₂ − a₂ b₁` of the two forms `a₁ t + b₁`, `a₂ t + b₂`. -/
def det : ℤ := (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁

/-- `E = a₁ a₂ |D|`. -/
def disc : ℕ := a₁ * a₂ * (det a₁ a₂ b₁ b₂).natAbs

/-- The local root count of `(a₁ t + b₁)(a₂ t + b₂)`: `1` at primes dividing `E`, `2` elsewhere
(under the non-degeneracy hypotheses of `rc_prime`). -/
def rho (p : ℕ) : ℝ := if p ∣ disc a₁ a₂ b₁ b₂ then 1 else 2

/-- The product of the two forms. -/
def F (t : ℤ) : ℤ := ((a₁ : ℤ) * t + b₁) * ((a₂ : ℤ) * t + b₂)

/-- The product of the two forms over `ZMod d`. -/
def Fz (d : ℕ) (r : ZMod d) : ZMod d :=
  ((a₁ : ZMod d) * r + (b₁ : ZMod d)) * ((a₂ : ZMod d) * r + (b₂ : ZMod d))

/-- The number of roots of the product of the two forms modulo `d`. -/
def rc (d : ℕ) : ℕ := Nat.card {r : ZMod d // Fz a₁ a₂ b₁ b₂ d r = 0}

theorem one_le_rho (p : ℕ) : 1 ≤ rho a₁ a₂ b₁ b₂ p := by
  unfold rho
  split_ifs <;> norm_num

theorem rho_le_two (p : ℕ) : rho a₁ a₂ b₁ b₂ p ≤ 2 := by
  unfold rho
  split_ifs <;> norm_num

theorem rho_nonneg (p : ℕ) : 0 ≤ rho a₁ a₂ b₁ b₂ p :=
  le_trans zero_le_one (one_le_rho a₁ a₂ b₁ b₂ p)

theorem lin_root {K : Type*} [Field K] {α β r : K} (hα : α ≠ 0) :
    α * r + β = 0 ↔ r = -β / α := by
  rw [eq_div_iff hα, add_eq_zero_iff_eq_neg, mul_comm]

theorem not_dvd_of_coprime {p a b : ℕ} (hp : p.Prime) (hab : Nat.Coprime a b) (ha : p ∣ a) :
    ¬ p ∣ b := by
  intro hb
  have h := Nat.dvd_gcd ha hb
  rw [hab.gcd_eq_one] at h
  exact hp.not_dvd_one h

/-- The root count at a prime. -/
theorem rc_prime (hcop : Nat.Coprime a₁ a₂) (hg₁ : Nat.Coprime a₁ b₁.natAbs)
    (hg₂ : Nat.Coprime a₂ b₂.natAbs) {p : ℕ} (hp : p.Prime) :
    (rc a₁ a₂ b₁ b₂ p : ℝ) = rho a₁ a₂ b₁ b₂ p := by
  haveI := Fact.mk hp
  classical
  have hcard : rc a₁ a₂ b₁ b₂ p =
      (Finset.univ.filter (fun r : ZMod p => Fz a₁ a₂ b₁ b₂ p r = 0)).card := by
    unfold rc
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hA : ∀ a : ℕ, (a : ZMod p) = 0 ↔ p ∣ a := fun a => ZMod.natCast_eq_zero_iff a p
  have hB : ∀ b : ℤ, (b : ZMod p) = 0 ↔ p ∣ b.natAbs := fun b => by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd]
  have hdet : ((a₁ : ZMod p) * b₂ - (a₂ : ZMod p) * b₁) = ((det a₁ a₂ b₁ b₂ : ℤ) : ZMod p) := by
    unfold det
    push_cast
    ring
  have hE : p ∣ disc a₁ a₂ b₁ b₂ ↔ p ∣ a₁ ∨ p ∣ a₂ ∨ p ∣ (det a₁ a₂ b₁ b₂).natAbs := by
    unfold disc
    rw [hp.dvd_mul, hp.dvd_mul, or_assoc]
  rw [hcard]
  unfold rho
  by_cases h1 : p ∣ a₁
  · have h2 : ¬ p ∣ a₂ := not_dvd_of_coprime hp hcop h1
    have hb1 : ¬ p ∣ b₁.natAbs := not_dvd_of_coprime hp hg₁ h1
    have hα₂ : (a₂ : ZMod p) ≠ 0 := fun h => h2 ((hA a₂).mp h)
    have hβ₁ : (b₁ : ZMod p) ≠ 0 := fun h => hb1 ((hB b₁).mp h)
    have hset : Finset.univ.filter (fun r : ZMod p => Fz a₁ a₂ b₁ b₂ p r = 0) =
        {-(b₂ : ZMod p) / (a₂ : ZMod p)} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fz,
        mul_eq_zero]
      rw [(hA a₁).mpr h1, zero_mul, zero_add, lin_root hα₂]
      constructor
      · rintro (h | h)
        · exact absurd h hβ₁
        · exact h
      · intro h
        exact Or.inr h
    rw [hset, Finset.card_singleton, if_pos (hE.mpr (Or.inl h1))]
    norm_num
  · by_cases h2 : p ∣ a₂
    · have hb2 : ¬ p ∣ b₂.natAbs := not_dvd_of_coprime hp hg₂ h2
      have hα₁ : (a₁ : ZMod p) ≠ 0 := fun h => h1 ((hA a₁).mp h)
      have hβ₂ : (b₂ : ZMod p) ≠ 0 := fun h => hb2 ((hB b₂).mp h)
      have hset : Finset.univ.filter (fun r : ZMod p => Fz a₁ a₂ b₁ b₂ p r = 0) =
          {-(b₁ : ZMod p) / (a₁ : ZMod p)} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fz,
          mul_eq_zero]
        rw [(hA a₂).mpr h2, zero_mul, zero_add, lin_root hα₁]
        constructor
        · rintro (h | h)
          · exact h
          · exact absurd h hβ₂
        · intro h
          exact Or.inl h
      rw [hset, Finset.card_singleton, if_pos (hE.mpr (Or.inr (Or.inl h2)))]
      norm_num
    · have hα₁ : (a₁ : ZMod p) ≠ 0 := fun h => h1 ((hA a₁).mp h)
      have hα₂ : (a₂ : ZMod p) ≠ 0 := fun h => h2 ((hA a₂).mp h)
      have hset : Finset.univ.filter (fun r : ZMod p => Fz a₁ a₂ b₁ b₂ p r = 0) =
          {-(b₁ : ZMod p) / (a₁ : ZMod p), -(b₂ : ZMod p) / (a₂ : ZMod p)} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Fz, mul_eq_zero]
        rw [lin_root hα₁, lin_root hα₂]
      have hroots : -(b₁ : ZMod p) / (a₁ : ZMod p) = -(b₂ : ZMod p) / (a₂ : ZMod p) ↔
          p ∣ (det a₁ a₂ b₁ b₂).natAbs := by
        rw [← hB, ← hdet, div_eq_div_iff hα₁ hα₂]
        constructor
        · intro h
          linear_combination h
        · intro h
          linear_combination h
      rw [hset]
      by_cases h3 : p ∣ (det a₁ a₂ b₁ b₂).natAbs
      · rw [(hroots.mpr h3), Finset.insert_eq_of_mem (Finset.mem_singleton_self _),
          Finset.card_singleton, if_pos (hE.mpr (Or.inr (Or.inr h3)))]
        norm_num
      · have hne : -(b₁ : ZMod p) / (a₁ : ZMod p) ≠ -(b₂ : ZMod p) / (a₂ : ZMod p) :=
          fun h => h3 (hroots.mp h)
        have hnE : ¬ p ∣ disc a₁ a₂ b₁ b₂ := by
          rw [hE]
          rintro (h | h | h)
          · exact h1 h
          · exact h2 h
          · exact h3 h
        rw [Finset.card_pair hne, if_neg hnE]
        norm_num

/-- The root count is multiplicative (Chinese remainder theorem). -/
theorem rc_mul {m n : ℕ} (h : Nat.Coprime m n) :
    rc a₁ a₂ b₁ b₂ (m * n) = rc a₁ a₂ b₁ b₂ m * rc a₁ a₂ b₁ b₂ n := by
  unfold rc
  rw [← Nat.card_prod]
  apply Nat.card_congr
  let e := ZMod.chineseRemainder h
  have key : ∀ r : ZMod (m * n), e (Fz a₁ a₂ b₁ b₂ (m * n) r) =
      (Fz a₁ a₂ b₁ b₂ m (e r).1, Fz a₁ a₂ b₁ b₂ n (e r).2) := by
    intro r
    ext <;> simp [Fz]
  have hiff : ∀ r : ZMod (m * n), Fz a₁ a₂ b₁ b₂ (m * n) r = 0 ↔
      (Fz a₁ a₂ b₁ b₂ m (e.toEquiv r).1 = 0 ∧ Fz a₁ a₂ b₁ b₂ n (e.toEquiv r).2 = 0) := by
    intro r
    rw [← map_eq_zero_iff e e.injective, key, Prod.ext_iff]
    rfl
  exact (e.toEquiv.subtypeEquiv hiff).trans Equiv.subtypeProdEquivProd

/-- The root count on a product of distinct primes. -/
theorem rc_prod_primes (hcop : Nat.Coprime a₁ a₂) (hg₁ : Nat.Coprime a₁ b₁.natAbs)
    (hg₂ : Nat.Coprime a₂ b₂.natAbs) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (rc a₁ a₂ b₁ b₂ (∏ p ∈ S, p) : ℝ) = ∏ p ∈ S, rho a₁ a₂ b₁ b₂ p := by
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty]
    haveI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
    have h1 : rc a₁ a₂ b₁ b₂ 1 = 1 := by
      unfold rc
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩,
        ⟨⟨0, Subsingleton.elim _ _⟩⟩⟩
    rw [h1, Nat.cast_one]
  | insert q S hq ih =>
    have hqp : q.Prime := hS q (Finset.mem_insert_self q S)
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hcopq : Nat.Coprime q (∏ p ∈ S, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      exact (Nat.coprime_primes hqp (hS' p hp)).mpr (fun h => hq (h ▸ hp))
    rw [Finset.prod_insert hq, Finset.prod_insert hq, rc_mul a₁ a₂ b₁ b₂ hcopq, Nat.cast_mul,
      rc_prime a₁ a₂ b₁ b₂ hcop hg₁ hg₂ hqp, ih hS']

/-- The root count at a squarefree modulus is `κ(d) = ∏_{p ∣ d} ρ(p)`. -/
theorem rc_squarefree (hcop : Nat.Coprime a₁ a₂) (hg₁ : Nat.Coprime a₁ b₁.natAbs)
    (hg₂ : Nat.Coprime a₂ b₂.natAbs) {d : ℕ} (hd : Squarefree d) :
    (rc a₁ a₂ b₁ b₂ d : ℝ) = cmOf (rho a₁ a₂ b₁ b₂) d := by
  rw [cmOf_squarefree _ hd]
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
  exact rc_prod_primes a₁ a₂ b₁ b₂ hcop hg₁ hg₂ d.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)

end Forms

/-! ## Counting an interval in a residue class -/

theorem natCast_zmod_eq_iff {d : ℕ} [NeZero d] (k : ℕ) (s : ZMod d) :
    (k : ZMod d) = s ↔ k ≡ s.val [MOD d] := by
  conv_lhs => rw [← ZMod.natCast_zmod_val s]
  exact ZMod.natCast_eq_natCast_iff k s.val d

/-- The class `r (mod d)` has `⌊(L+1)/d⌋` or `⌊(L+1)/d⌋ + 1` elements in `[u, u + L]`. -/
theorem card_Icc_filter_zmod (u : ℤ) (L d : ℕ) [NeZero d] (r : ZMod d) :
    ∃ e : ℕ, e ≤ 1 ∧
      ((Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ => (t : ZMod d) = r)).card =
        (L + 1) / d + e := by
  have hbij : ((Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ => (t : ZMod d) = r)).card =
      ((Finset.range (L + 1)).filter (fun k => k ≡ (r - (u : ZMod d)).val [MOD d])).card := by
    apply Finset.card_nbij' (fun t : ℤ => (t - u).toNat) (fun k : ℕ => u + (k : ℤ))
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ht
      obtain ⟨⟨h1, h2⟩, h3⟩ := ht
      have hcast : (((t - u).toNat : ℕ) : ℤ) = t - u := Int.toNat_of_nonneg (by omega)
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      rw [← natCast_zmod_eq_iff]
      refine ⟨by omega, ?_⟩
      rw [← Int.cast_natCast, hcast, Int.cast_sub, h3]
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hk1, hk2⟩ := hk
      rw [← natCast_zmod_eq_iff] at hk2
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [Int.cast_add, Int.cast_natCast, hk2]
      ring
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ht
      obtain ⟨⟨h1, _⟩, _⟩ := ht
      have h0 : 0 ≤ t - u := by omega
      change u + (((t - u).toNat : ℕ) : ℤ) = t
      rw [Int.toNat_of_nonneg h0]
      ring
    · intro k _
      change ((u + (k : ℤ)) - u).toNat = k
      simp
  rw [hbij, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ (NeZero.pos d)]
  refine ⟨_, ?_, rfl⟩
  split_ifs <;> norm_num

/-- Counting a finset through the fibres of a map into `ℕ`. -/
theorem sum_image_ite_card (s : Finset ℤ) (f : ℤ → ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    ∑ n ∈ s.image f, (if Q n then (((s.filter (fun t => f t = n)).card : ℕ) : ℝ) else 0) =
      (((s.filter (fun t => Q (f t))).card : ℕ) : ℝ) := by
  have hfib := Finset.card_eq_sum_card_fiberwise (f := f) (s := s.filter (fun t => Q (f t)))
    (t := s.image f) (fun t ht => Finset.mem_coe.mpr
      (Finset.mem_image_of_mem f (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).1))
  rw [hfib]
  push_cast
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.filter_filter]
  split_ifs with hQ
  · have hset : s.filter (fun t => Q (f t) ∧ f t = n) = s.filter (fun t => f t = n) := by
      apply Finset.filter_congr
      intro t _
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rw [h]
        exact hQ
    rw [hset]
  · have hset : s.filter (fun t => Q (f t) ∧ f t = n) = ∅ := by
      apply Finset.filter_false_of_mem
      intro t _ h
      apply hQ
      rw [← h.2]
      exact h.1
    rw [hset, Finset.card_empty, Nat.cast_zero]

/-! ## The sieve -/

section TheSieve

variable (a₁ a₂ : ℕ) (b₁ b₂ : ℤ)

/-- The sifting density `ν(n) = κ(n)/n`, with `κ` completely multiplicative, `κ(p) = ρ(p)`. -/
def nu : ArithmeticFunction ℝ := (cmOf (rho a₁ a₂ b₁ b₂)).pdiv .id

theorem nu_cm : Sieve.CompletelyMultiplicative (nu a₁ a₂ b₁ b₂) :=
  Sieve.CompletelyMultiplicative.pdiv (cmOf_cm _) Sieve.CompletelyMultiplicative.id

theorem nu_apply (n : ℕ) : nu a₁ a₂ b₁ b₂ n = cmOf (rho a₁ a₂ b₁ b₂) n / n := by
  unfold nu
  simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.id_apply]

theorem nu_prime {p : ℕ} (hp : p.Prime) : nu a₁ a₂ b₁ b₂ p = rho a₁ a₂ b₁ b₂ p / p := by
  rw [nu_apply, cmOf_prime _ hp]

theorem nu_nonneg (n : ℕ) : 0 ≤ nu a₁ a₂ b₁ b₂ n := by
  rw [nu_apply]
  exact div_nonneg (cmOf_nonneg _ (rho_nonneg a₁ a₂ b₁ b₂) n) (Nat.cast_nonneg n)

theorem nu_pos_of_prime' {p : ℕ} (hp : p.Prime) : 0 < nu a₁ a₂ b₁ b₂ p := by
  rw [nu_prime a₁ a₂ b₁ b₂ hp]
  exact div_pos (lt_of_lt_of_le zero_lt_one (one_le_rho a₁ a₂ b₁ b₂ p))
    (by exact_mod_cast hp.pos)

theorem nu_lt_one_of_odd {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : nu a₁ a₂ b₁ b₂ p < 1 := by
  rw [nu_prime a₁ a₂ b₁ b₂ hp]
  have h3' : 3 ≤ p := lt_of_le_of_ne hp.two_le (Ne.symm h2)
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast h3'
  rw [div_lt_one (by linarith)]
  linarith [rho_le_two a₁ a₂ b₁ b₂ p]

/-- The sifting primes: the odd primes `p ≤ z`. -/
def oddPrimes (z : ℝ) : Finset ℕ :=
  (Finset.range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

theorem oddPrimes_squarefree (z : ℝ) : Squarefree (∏ p ∈ oddPrimes z, p) :=
  Sieve.prodDistinctPrimes_squarefree _ (fun _ hp => (Finset.mem_filter.mp hp).2.1)

theorem prime_dvd_prod_oddPrimes_iff (z : ℝ) {p : ℕ} (hp : p.Prime) :
    p ∣ ∏ q ∈ oddPrimes z, q ↔ p ≤ ⌊z⌋₊ ∧ p ≠ 2 := by
  constructor
  · intro h
    obtain ⟨i, hi, hpi⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd h
    rw [oddPrimes, Finset.mem_filter, Finset.mem_range] at hi
    have hpi' : p = i := (Nat.prime_dvd_prime_iff_eq hp hi.2.1).mp hpi
    rw [← hpi'] at hi
    exact ⟨Nat.lt_succ_iff.mp hi.1, hi.2.2⟩
  · rintro ⟨h1, h2⟩
    exact Finset.dvd_prod_of_mem (fun q => q)
      (by rw [oddPrimes, Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.lt_succ_of_le h1, hp, h2⟩)

/-- The two-dimensional sieve: the values `|F(t)|` for `t ∈ [u, u + L]` (weighted by
multiplicity), sifted by the odd primes `p ≤ z`, with density `ν` and total mass `L + 1`. -/
def twoSieve (u : ℤ) (L : ℕ) (z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := (Finset.Icc u (u + (L : ℤ))).image (fun t => (F a₁ a₂ b₁ b₂ t).natAbs)
  prodPrimes := ∏ p ∈ oddPrimes z, p
  prodPrimes_squarefree := oddPrimes_squarefree z
  weights := fun n =>
    (((Finset.Icc u (u + (L : ℤ))).filter (fun t => (F a₁ a₂ b₁ b₂ t).natAbs = n)).card : ℝ)
  weights_nonneg := fun _ => Nat.cast_nonneg _
  totalMass := (L : ℝ) + 1
  nu := nu a₁ a₂ b₁ b₂
  nu_mult := (nu_cm a₁ a₂ b₁ b₂).isMultiplicative
  nu_pos_of_prime := fun _ hp _ => nu_pos_of_prime' a₁ a₂ b₁ b₂ hp
  nu_lt_one_of_prime := fun _ hp hpP =>
    nu_lt_one_of_odd a₁ a₂ b₁ b₂ hp ((prime_dvd_prod_oddPrimes_iff z hp).mp hpP).2
  level := z
  one_le_level := hz

theorem multSum_eq (u : ℤ) (L : ℕ) (z : ℝ) (hz : 1 ≤ z) (d : ℕ) :
    multSum (s := (twoSieve a₁ a₂ b₁ b₂ u L z hz).toBoundingSieve) d =
      ((((Finset.Icc u (u + (L : ℤ))).filter
        (fun t => d ∣ (F a₁ a₂ b₁ b₂ t).natAbs)).card : ℕ) : ℝ) := by
  change (∑ n ∈ (Finset.Icc u (u + (L : ℤ))).image (fun t => (F a₁ a₂ b₁ b₂ t).natAbs),
      if d ∣ n then ((((Finset.Icc u (u + (L : ℤ))).filter
        (fun t => (F a₁ a₂ b₁ b₂ t).natAbs = n)).card : ℕ) : ℝ) else 0) = _
  exact sum_image_ite_card _ _ (fun n => d ∣ n)

theorem siftedSum_eq (u : ℤ) (L : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    siftedSum (s := (twoSieve a₁ a₂ b₁ b₂ u L z hz).toBoundingSieve) =
      ((((Finset.Icc u (u + (L : ℤ))).filter
        (fun t => Nat.Coprime (∏ p ∈ oddPrimes z, p) (F a₁ a₂ b₁ b₂ t).natAbs)).card : ℕ)
          : ℝ) := by
  change (∑ n ∈ (Finset.Icc u (u + (L : ℤ))).image (fun t => (F a₁ a₂ b₁ b₂ t).natAbs),
      if Nat.Coprime (∏ p ∈ oddPrimes z, p) n then ((((Finset.Icc u (u + (L : ℤ))).filter
        (fun t => (F a₁ a₂ b₁ b₂ t).natAbs = n)).card : ℕ) : ℝ) else 0) = _
  exact sum_image_ite_card _ _ (fun n => Nat.Coprime (∏ p ∈ oddPrimes z, p) n)

theorem kappa_le_two_pow {d : ℕ} (hd : Squarefree d) :
    cmOf (rho a₁ a₂ b₁ b₂) d ≤ (2 : ℝ) ^ ω d := by
  rw [cmOf_squarefree _ hd, ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    Nat.toFinset_factors, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun p _ => rho_nonneg a₁ a₂ b₁ b₂ p)
    (fun p _ => rho_le_two a₁ a₂ b₁ b₂ p)

/-- The sieve remainders: `|R_d| ≤ κ(d)`, the number of root classes modulo `d`. -/
theorem abs_rem_le (hcop : Nat.Coprime a₁ a₂) (hg₁ : Nat.Coprime a₁ b₁.natAbs)
    (hg₂ : Nat.Coprime a₂ b₂.natAbs) (u : ℤ) (L : ℕ) (z : ℝ) (hz : 1 ≤ z) {d : ℕ}
    (hd : d ∣ ∏ p ∈ oddPrimes z, p) :
    |rem (s := (twoSieve a₁ a₂ b₁ b₂ u L z hz).toBoundingSieve) d| ≤
      cmOf (rho a₁ a₂ b₁ b₂) d := by
  classical
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (oddPrimes_squarefree z).ne_zero hd
  haveI : NeZero d := ⟨hd0⟩
  have hsq : Squarefree d := (oddPrimes_squarefree z).squarefree_of_dvd hd
  have hRcard : (((Finset.univ.filter (fun r : ZMod d => Fz a₁ a₂ b₁ b₂ d r = 0)).card : ℕ)
      : ℝ) = cmOf (rho a₁ a₂ b₁ b₂) d := by
    rw [← rc_squarefree a₁ a₂ b₁ b₂ hcop hg₁ hg₂ hsq]
    unfold rc
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcastF : ∀ t : ℤ, ((F a₁ a₂ b₁ b₂ t : ℤ) : ZMod d) = Fz a₁ a₂ b₁ b₂ d (t : ZMod d) := by
    intro t
    simp only [F, Fz, Int.cast_mul, Int.cast_add, Int.cast_natCast]
  have hmem : ∀ t : ℤ, d ∣ (F a₁ a₂ b₁ b₂ t).natAbs ↔ Fz a₁ a₂ b₁ b₂ d (t : ZMod d) = 0 := by
    intro t
    rw [← Int.natCast_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hcastF]
  have hdecomp : ((Finset.Icc u (u + (L : ℤ))).filter
      (fun t => d ∣ (F a₁ a₂ b₁ b₂ t).natAbs)).card =
      ∑ r ∈ Finset.univ.filter (fun r : ZMod d => Fz a₁ a₂ b₁ b₂ d r = 0),
        ((Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ => (t : ZMod d) = r)).card := by
    have hmaps : ∀ t ∈ (Finset.Icc u (u + (L : ℤ))).filter
        (fun t => d ∣ (F a₁ a₂ b₁ b₂ t).natAbs),
        (t : ZMod d) ∈ Finset.univ.filter (fun r : ZMod d => Fz a₁ a₂ b₁ b₂ d r = 0) := by
      intro t ht
      rw [Finset.mem_filter] at ht
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (hmem t).mp ht.2⟩
    have hfib := Finset.card_eq_sum_card_fiberwise (f := fun t : ℤ => (t : ZMod d))
      (s := (Finset.Icc u (u + (L : ℤ))).filter (fun t => d ∣ (F a₁ a₂ b₁ b₂ t).natAbs))
      (t := Finset.univ.filter (fun r : ZMod d => Fz a₁ a₂ b₁ b₂ d r = 0))
      (fun t ht => Finset.mem_coe.mpr (hmaps t (Finset.mem_coe.mp ht)))
    rw [hfib]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro t _
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [hmem, h]
      exact (Finset.mem_filter.mp hr).2
  have hnu : (twoSieve a₁ a₂ b₁ b₂ u L z hz).nu d * (twoSieve a₁ a₂ b₁ b₂ u L z hz).totalMass =
      ∑ r ∈ Finset.univ.filter (fun r : ZMod d => Fz a₁ a₂ b₁ b₂ d r = 0),
        (((L : ℝ) + 1) / d) := by
    change nu a₁ a₂ b₁ b₂ d * ((L : ℝ) + 1) = _
    rw [Finset.sum_const, nsmul_eq_mul, hRcard, nu_apply]
    ring
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hbound : ∀ r : ZMod d,
      |((((Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ => (t : ZMod d) = r)).card : ℕ) : ℝ) -
        ((L : ℝ) + 1) / d| ≤ 1 := by
    intro r
    obtain ⟨e, he, hc⟩ := card_Icc_filter_zmod u L d r
    have hk1 : ((((L + 1) / d : ℕ)) : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / (d : ℝ) := Nat.cast_div_le
    have hk2 : ((L + 1 : ℕ) : ℝ) / (d : ℝ) < ((((L + 1) / d : ℕ)) : ℝ) + 1 := by
      rw [← Nat.floor_div_eq_div (K := ℝ) (L + 1) d]
      exact Nat.lt_floor_add_one _
    have he' : (e : ℝ) ≤ 1 := by exact_mod_cast he
    have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
    have hL1 : ((L + 1 : ℕ) : ℝ) = (L : ℝ) + 1 := by norm_num
    rw [hL1] at hk1 hk2
    rw [hc, Nat.cast_add, abs_le]
    constructor <;> linarith
  unfold rem
  rw [multSum_eq, hdecomp, hnu, Nat.cast_sum, ← Finset.sum_sub_distrib]
  calc |∑ r ∈ Finset.univ.filter (fun r : ZMod d => Fz a₁ a₂ b₁ b₂ d r = 0),
        (((((Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ => (t : ZMod d) = r)).card : ℕ)
          : ℝ) - ((L : ℝ) + 1) / d)|
      ≤ ∑ r ∈ Finset.univ.filter (fun r : ZMod d => Fz a₁ a₂ b₁ b₂ d r = 0), (1 : ℝ) :=
        le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun r _ => hbound r))
    _ = cmOf (rho a₁ a₂ b₁ b₂) d := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, hRcard]

/-- The Selberg error term: `∑_{d ∣ P, d ≤ z} 3^{ω(d)} |R_d| ≤ z (1 + log z)^6`. -/
theorem errSum_le (hcop : Nat.Coprime a₁ a₂) (hg₁ : Nat.Coprime a₁ b₁.natAbs)
    (hg₂ : Nat.Coprime a₂ b₂.natAbs) (u : ℤ) (L : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (∑ d ∈ (twoSieve a₁ a₂ b₁ b₂ u L z hz).prodPrimes.divisors,
      if (d : ℝ) ≤ (twoSieve a₁ a₂ b₁ b₂ u L z hz).level then
        (3 : ℝ) ^ ω d * |rem (s := (twoSieve a₁ a₂ b₁ b₂ u L z hz).toBoundingSieve) d|
      else 0) ≤ z * (1 + Real.log z) ^ 6 := by
  have h6 := Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow
    (P := ∏ p ∈ oddPrimes z, p) (h := 6) z hz (oddPrimes_squarefree z)
  change (∑ d ∈ (∏ p ∈ oddPrimes z, p).divisors,
      if (d : ℝ) ≤ z then
        (3 : ℝ) ^ ω d * |rem (s := (twoSieve a₁ a₂ b₁ b₂ u L z hz).toBoundingSieve) d|
      else 0) ≤ z * (1 + Real.log z) ^ 6
  refine le_trans (Finset.sum_le_sum ?_) h6
  intro d hd
  have hdP : d ∣ ∏ p ∈ oddPrimes z, p := Nat.dvd_of_mem_divisors hd
  split_ifs with hdz
  · have hsq : Squarefree d := (oddPrimes_squarefree z).squarefree_of_dvd hdP
    calc (3 : ℝ) ^ ω d * |rem (s := (twoSieve a₁ a₂ b₁ b₂ u L z hz).toBoundingSieve) d|
        ≤ (3 : ℝ) ^ ω d * (2 : ℝ) ^ ω d :=
          mul_le_mul_of_nonneg_left
            ((abs_rem_le a₁ a₂ b₁ b₂ hcop hg₁ hg₂ u L z hz hdP).trans
              (kappa_le_two_pow a₁ a₂ b₁ b₂ hsq)) (by positivity)
      _ = ((6 : ℕ) : ℝ) ^ ω d := by
          rw [← mul_pow]
          norm_num
  · exact le_refl 0

/-! ## Values of a linear form that are small primes -/

theorem card_small_prime_values (a : ℕ) (b : ℤ) (ha : 0 < a) (s : Finset ℤ) (N : ℕ) :
    (s.filter (fun t => ((a : ℤ) * t + b).toNat.Prime ∧ ((a : ℤ) * t + b).toNat ≤ N)).card ≤
      N + 1 := by
  rw [← Finset.card_range (N + 1)]
  apply Finset.card_le_card_of_injOn (fun t => ((a : ℤ) * t + b).toNat)
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter] at ht
    simp only [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le ht.2.2
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
    have hx0 : 0 ≤ (a : ℤ) * x + b := by
      by_contra h
      push Not at h
      rw [Int.toNat_of_nonpos h.le] at hx
      exact Nat.not_prime_zero hx.2.1
    have hy0 : 0 ≤ (a : ℤ) * y + b := by
      by_contra h
      push Not at h
      rw [Int.toNat_of_nonpos h.le] at hy
      exact Nat.not_prime_zero hy.2.1
    have h1 : ((a : ℤ) * x + b).toNat = ((a : ℤ) * y + b).toNat := hxy
    have h2 : (((a : ℤ) * x + b).toNat : ℤ) = (((a : ℤ) * y + b).toNat : ℤ) := by rw [h1]
    rw [Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0] at h2
    have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
    exact mul_left_cancel₀ ha' (by linarith)

/-- A form `a t + b` with `gcd(a, b) > 1` takes at most one prime value. -/
theorem card_prime_values_le_one (a : ℕ) (b : ℤ) (ha : 0 < a) (h : ¬ Nat.Coprime a b.natAbs)
    (s : Finset ℤ) : (s.filter (fun t => ((a : ℤ) * t + b).toNat.Prime)).card ≤ 1 := by
  have key : ∀ t : ℤ, ((a : ℤ) * t + b).toNat.Prime →
      (a : ℤ) * t + b = ((Nat.gcd a b.natAbs : ℕ) : ℤ) := by
    intro t ht
    have hpos : 0 ≤ (a : ℤ) * t + b := by
      by_contra hneg
      push Not at hneg
      rw [Int.toNat_of_nonpos hneg.le] at ht
      exact Nat.not_prime_zero ht
    have hq : (((a : ℤ) * t + b).toNat : ℤ) = (a : ℤ) * t + b := Int.toNat_of_nonneg hpos
    have hg : Nat.gcd a b.natAbs ∣ ((a : ℤ) * t + b).toNat := by
      rw [← Int.natCast_dvd_natCast, hq]
      exact Dvd.dvd.add
        (Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)) t)
        (Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _))
    rcases Nat.Prime.eq_one_or_self_of_dvd ht _ hg with h1 | h1
    · exact absurd h1 h
    · rw [h1, hq]
  rw [Finset.card_le_one]
  intro x hx y hy
  rw [Finset.mem_filter] at hx hy
  have h1 := key x hx.2
  have h2 := key y hy.2
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  exact mul_left_cancel₀ ha' (by linarith)

/-- The prime pairs are sifted, or one of the two primes is at most `z`. -/
theorem card_prime_pairs_le_sifted (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (u : ℤ) (L : ℕ) (z : ℝ)
    (hz : 1 ≤ z) :
    ((((Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ =>
        ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card : ℕ) : ℝ) ≤
      siftedSum (s := (twoSieve a₁ a₂ b₁ b₂ u L z hz).toBoundingSieve) +
        2 * ((⌊z⌋₊ : ℝ) + 1) := by
  classical
  rw [siftedSum_eq]
  have hcop1 : ∀ q : ℕ, q.Prime → ¬ q ≤ ⌊z⌋₊ → Nat.Coprime (∏ p ∈ oddPrimes z, p) q := by
    intro q hq hqz
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hq]
    intro hdvd
    exact hqz ((prime_dvd_prod_oddPrimes_iff z hq).mp hdvd).1
  have hnat : ∀ x : ℤ, x.toNat.Prime → x.natAbs = x.toNat := by
    intro x hx
    have hx0 : 0 ≤ x := by
      by_contra h
      push Not at h
      rw [Int.toNat_of_nonpos h.le] at hx
      exact Nat.not_prime_zero hx
    have e1 : (x.natAbs : ℤ) = x := Int.natAbs_of_nonneg hx0
    have e2 : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx0
    exact_mod_cast e1.trans e2.symm
  have hsub : (Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ =>
        ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime) ⊆
      ((Finset.Icc u (u + (L : ℤ))).filter
          (fun t => Nat.Coprime (∏ p ∈ oddPrimes z, p) (F a₁ a₂ b₁ b₂ t).natAbs) ∪
        (Finset.Icc u (u + (L : ℤ))).filter (fun t =>
          ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₁ : ℤ) * t + b₁).toNat ≤ ⌊z⌋₊)) ∪
        (Finset.Icc u (u + (L : ℤ))).filter (fun t =>
          ((a₂ : ℤ) * t + b₂).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat ≤ ⌊z⌋₊) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htI, hp1, hp2⟩ := ht
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_filter]
    by_cases h1 : ((a₁ : ℤ) * t + b₁).toNat ≤ ⌊z⌋₊
    · exact Or.inl (Or.inr ⟨htI, hp1, h1⟩)
    by_cases h2 : ((a₂ : ℤ) * t + b₂).toNat ≤ ⌊z⌋₊
    · exact Or.inr ⟨htI, hp2, h2⟩
    refine Or.inl (Or.inl ⟨htI, ?_⟩)
    unfold F
    rw [Int.natAbs_mul, hnat _ hp1, hnat _ hp2]
    exact Nat.Coprime.mul_right (hcop1 _ hp1 h1) (hcop1 _ hp2 h2)
  have hc1 := card_small_prime_values a₁ b₁ ha₁ (Finset.Icc u (u + (L : ℤ))) ⌊z⌋₊
  have hc2 := card_small_prime_values a₂ b₂ ha₂ (Finset.Icc u (u + (L : ℤ))) ⌊z⌋₊
  have hcard := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hnat' : ((Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ =>
        ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card ≤
      ((Finset.Icc u (u + (L : ℤ))).filter
          (fun t => Nat.Coprime (∏ p ∈ oddPrimes z, p) (F a₁ a₂ b₁ b₂ t).natAbs)).card +
        (⌊z⌋₊ + 1) + (⌊z⌋₊ + 1) := by omega
  have hreal := (Nat.cast_le (α := ℝ)).mpr hnat'
  push_cast at hreal
  linarith

/-! ## The main term: a lower bound for the Selberg bounding sum -/

/-- The divisors of `m` avoiding the primes of `Q` number at most `κ(m)`, when `κ ≥ 1` at every
prime and `κ ≥ 2` at primes outside `Q`. -/
theorem card_divisors_avoid_le (c : ℕ → ℝ) (Q : Finset ℕ) (hc0 : ∀ p, 0 ≤ c p)
    (hc1 : ∀ p, p.Prime → 1 ≤ c p) (hc2 : ∀ p, p.Prime → p ∉ Q → 2 ≤ c p) (m : ℕ) :
    (((m.divisors.filter (fun b => ∀ q ∈ Q, ¬ q ∣ b)).card : ℕ) : ℝ) ≤ cmOf c m := by
  induction m using Nat.recOnMul with
  | zero =>
    simp
  | one =>
    rw [(cmOf_cm c).1]
    have hsub : (Nat.divisors 1).filter (fun b => ∀ q ∈ Q, ¬ q ∣ b) ⊆ {1} := by
      rw [Nat.divisors_one]
      exact Finset.filter_subset _ _
    have h := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h
    exact_mod_cast h
  | prime p hp =>
    rw [cmOf_prime c hp]
    by_cases hpQ : p ∈ Q
    · have hsub : p.divisors.filter (fun b => ∀ q ∈ Q, ¬ q ∣ b) ⊆ {1} := by
        intro b hb
        rw [Finset.mem_filter, Nat.Prime.divisors hp, Finset.mem_insert,
          Finset.mem_singleton] at hb
        rcases hb.1 with h | h
        · rw [h]
          exact Finset.mem_singleton_self 1
        · exact (hb.2 p hpQ (dvd_of_eq h.symm)).elim
      have h := Finset.card_le_card hsub
      rw [Finset.card_singleton] at h
      calc ((((p.divisors.filter (fun b => ∀ q ∈ Q, ¬ q ∣ b)).card : ℕ) : ℝ)) ≤ 1 := by
            exact_mod_cast h
        _ ≤ c p := hc1 p hp
    · have h := Finset.card_filter_le p.divisors (fun b => ∀ q ∈ Q, ¬ q ∣ b)
      have h2 : p.divisors.card = 2 := by
        rw [Nat.Prime.divisors hp, Finset.card_pair hp.one_lt.ne]
      calc ((((p.divisors.filter (fun b => ∀ q ∈ Q, ¬ q ∣ b)).card : ℕ) : ℝ)) ≤ 2 := by
            exact_mod_cast h.trans h2.le
        _ ≤ c p := hc2 p hp hpQ
  | mul a b iha ihb =>
    rw [(cmOf_cm c).2]
    have hsub : ((a * b).divisors.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)) ⊆
        ((a.divisors.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)) ×ˢ
          (b.divisors.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n))).image (fun x => x.1 * x.2) := by
      intro n hn
      rw [Finset.mem_filter, Nat.divisors_mul, Finset.mem_mul] at hn
      obtain ⟨⟨x, hx, y, hy, rfl⟩, hQ⟩ := hn
      rw [Finset.mem_image]
      refine ⟨(x, y), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hx, ?_⟩,
        Finset.mem_filter.mpr ⟨hy, ?_⟩⟩, rfl⟩
      · intro q hq hqx
        exact hQ q hq (Dvd.dvd.mul_right hqx y)
      · intro q hq hqy
        exact hQ q hq (Dvd.dvd.mul_left hqy x)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := (a.divisors.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)) ×ˢ
          (b.divisors.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n))) (f := fun x => x.1 * x.2)
    rw [Finset.card_product] at h2
    calc ((((a * b).divisors.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).card : ℕ) : ℝ)
        ≤ ((((a.divisors.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).card : ℕ) : ℝ)) *
          ((((b.divisors.filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).card : ℕ) : ℝ)) := by
          exact_mod_cast h1.trans h2
      _ ≤ cmOf c a * cmOf c b := mul_le_mul iha ihb (Nat.cast_nonneg _) (cmOf_nonneg c hc0 a)

/-- A product of two harmonic sums is dominated by `∑_{m ∈ M} κ(m)/m`. -/
theorem harm_mul_le (c : ℕ → ℝ) (Q : Finset ℕ) (hc0 : ∀ p, 0 ≤ c p)
    (hc1 : ∀ p, p.Prime → 1 ≤ c p) (hc2 : ∀ p, p.Prime → p ∉ Q → 2 ≤ c p)
    (A B M : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hB : ∀ b ∈ B, 0 < b ∧ ∀ q ∈ Q, ¬ q ∣ b)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ M) :
    (∑ a ∈ A, 1 / (a : ℝ)) * (∑ b ∈ B, 1 / (b : ℝ)) ≤ ∑ m ∈ M, cmOf c m / m := by
  classical
  have hprod : (∑ a ∈ A, 1 / (a : ℝ)) * (∑ b ∈ B, 1 / (b : ℝ)) =
      ∑ x ∈ A ×ˢ B, 1 / (x.1 : ℝ) * (1 / (x.2 : ℝ)) := by
    simp only [Finset.sum_mul_sum, Finset.sum_product]
  have hmaps : ∀ x ∈ A ×ˢ B, (fun x : ℕ × ℕ => x.1 * x.2) x ∈ M :=
    fun x hx => hAB x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2
  have hfw := Finset.sum_fiberwise_of_maps_to (s := A ×ˢ B) (t := M)
    (g := fun x : ℕ × ℕ => x.1 * x.2) hmaps (fun x => 1 / (x.1 : ℝ) * (1 / (x.2 : ℝ)))
  rw [hprod, ← hfw]
  apply Finset.sum_le_sum
  intro m _
  have hfib : ∀ x ∈ (A ×ˢ B).filter (fun x : ℕ × ℕ => x.1 * x.2 = m),
      1 / (x.1 : ℝ) * (1 / (x.2 : ℝ)) = 1 / (m : ℝ) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [one_div_mul_one_div, ← Nat.cast_mul, hx.2]
  have hsum_eq : ∑ x ∈ (A ×ˢ B).filter (fun x : ℕ × ℕ => x.1 * x.2 = m),
      1 / (x.1 : ℝ) * (1 / (x.2 : ℝ)) =
      ((((A ×ˢ B).filter (fun x : ℕ × ℕ => x.1 * x.2 = m)).card : ℕ) : ℝ) * (1 / (m : ℝ)) := by
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  refine le_trans (le_of_eq hsum_eq) ?_
  have hcard : ((A ×ˢ B).filter (fun x : ℕ × ℕ => x.1 * x.2 = m)).card ≤
      (m.divisors.filter (fun b => ∀ q ∈ Q, ¬ q ∣ b)).card := by
    apply Finset.card_le_card_of_injOn (fun x => x.2)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx
      obtain ⟨⟨hxA, hxB⟩, hxm⟩ := hx
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors]
      have ha0 := hA x.1 hxA
      have hb0 := (hB x.2 hxB).1
      refine ⟨⟨Dvd.intro_left x.1 hxm, ?_⟩, (hB x.2 hxB).2⟩
      rw [← hxm]
      exact (Nat.mul_pos ha0 hb0).ne'
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx hy
      have hb0 := (hB x.2 hx.1.2).1
      have hxy' : x.2 = y.2 := hxy
      have h1 : x.1 * x.2 = y.1 * x.2 := by rw [hx.2, hxy', hy.2]
      exact Prod.ext (Nat.eq_of_mul_eq_mul_right hb0 h1) hxy'
  have hm0 : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  calc ((((A ×ˢ B).filter (fun x : ℕ × ℕ => x.1 * x.2 = m)).card : ℕ) : ℝ) * (1 / (m : ℝ))
      ≤ ((((m.divisors.filter (fun b => ∀ q ∈ Q, ¬ q ∣ b)).card : ℕ) : ℝ)) * (1 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hm0
    _ ≤ cmOf c m * (1 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_right (card_divisors_avoid_le c Q hc0 hc1 hc2 m) hm0
    _ = cmOf c m / m := by rw [mul_one_div]

theorem disc_pos (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hD : det a₁ a₂ b₁ b₂ ≠ 0) :
    0 < disc a₁ a₂ b₁ b₂ := by
  unfold disc
  exact Nat.mul_pos (Nat.mul_pos ha₁ ha₂) (Int.natAbs_pos.mpr hD)

/-- The lower bound `G` for the Selberg bounding sum, `V = z^{1/4}`:
`G = (½ log V) · (φ(2E)/(2E) · log V)`. -/
def glb (z : ℝ) : ℝ :=
  (1 / 2 * Real.log (Real.sqrt (Real.sqrt z))) *
    (((2 * disc a₁ a₂ b₁ b₂).totient : ℝ) / ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ) *
      Real.log (Real.sqrt (Real.sqrt z)))

/-- **Main term.** `S ≥ (½ log z^{1/4}) (φ(2E)/(2E)) log z^{1/4}`. -/
theorem boundingSum_ge (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hD : det a₁ a₂ b₁ b₂ ≠ 0) (u : ℤ)
    (L : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    glb a₁ a₂ b₁ b₂ z ≤ (twoSieve a₁ a₂ b₁ b₂ u L z hz).selbergBoundingSum := by
  classical
  have hz0 : (0 : ℝ) ≤ z := by linarith
  have hsz1 : 1 ≤ Real.sqrt z := Real.one_le_sqrt.mpr hz
  have hV1 : 1 ≤ Real.sqrt (Real.sqrt z) := Real.one_le_sqrt.mpr hsz1
  have hV0 : 0 ≤ Real.sqrt (Real.sqrt z) := Real.sqrt_nonneg _
  have hq0 : 0 < 2 * disc a₁ a₂ b₁ b₂ := Nat.mul_pos two_pos (disc_pos a₁ a₂ b₁ b₂ ha₁ ha₂ hD)
  have hA := BrunTitchmarshAP.totient_mul_log_le_harmAvoid 2 two_pos _ hV1
  have hB := BrunTitchmarshAP.totient_mul_log_le_harmAvoid (2 * disc a₁ a₂ b₁ b₂) hq0 _ hV1
  rw [Nat.totient_two, Nat.cast_one] at hA
  have hlogV : 0 ≤ Real.log (Real.sqrt (Real.sqrt z)) := Real.log_nonneg hV1
  have hH0 : 0 ≤ BrunTitchmarshAP.harmAvoid (Nat.primeFactors 2) ⌊Real.sqrt (Real.sqrt z)⌋₊ := by
    unfold BrunTitchmarshAP.harmAvoid
    exact Finset.sum_nonneg (fun n _ => by positivity)
  have hprod : glb a₁ a₂ b₁ b₂ z ≤
      BrunTitchmarshAP.harmAvoid (Nat.primeFactors 2) ⌊Real.sqrt (Real.sqrt z)⌋₊ *
        BrunTitchmarshAP.harmAvoid (2 * disc a₁ a₂ b₁ b₂).primeFactors
          ⌊Real.sqrt (Real.sqrt z)⌋₊ := by
    unfold glb
    have hA' : 1 / 2 * Real.log (Real.sqrt (Real.sqrt z)) ≤
        BrunTitchmarshAP.harmAvoid (Nat.primeFactors 2) ⌊Real.sqrt (Real.sqrt z)⌋₊ := by
      have : ((2 : ℕ) : ℝ) = 2 := by norm_num
      rw [this] at hA
      exact hA
    exact mul_le_mul hA' hB
      (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hlogV) hH0
  refine le_trans hprod ?_
  refine le_trans ?_ (Sieve.selbergBoundingSum_ge_sum_div_filter (twoSieve a₁ a₂ b₁ b₂ u L z hz)
    (nu_cm a₁ a₂ b₁ b₂) (nu_nonneg a₁ a₂ b₁ b₂)
    (fun p hp hpP => (twoSieve a₁ a₂ b₁ b₂ u L z hz).nu_lt_one_of_prime p hp hpP))
  change _ ≤ ∑ m ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
      (fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ∣ ∏ q ∈ oddPrimes z, q), nu a₁ a₂ b₁ b₂ m
  rw [Finset.sum_congr rfl (fun m _ => nu_apply a₁ a₂ b₁ b₂ m)]
  unfold BrunTitchmarshAP.harmAvoid
  -- the size of the product ab
  have hWW : ⌊Real.sqrt (Real.sqrt z)⌋₊ * ⌊Real.sqrt (Real.sqrt z)⌋₊ ≤ ⌊Real.sqrt z⌋₊ := by
    apply Nat.le_floor
    have hW : ((⌊Real.sqrt (Real.sqrt z)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (Real.sqrt z) :=
      Nat.floor_le hV0
    push_cast
    calc ((⌊Real.sqrt (Real.sqrt z)⌋₊ : ℕ) : ℝ) * ((⌊Real.sqrt (Real.sqrt z)⌋₊ : ℕ) : ℝ)
        ≤ Real.sqrt (Real.sqrt z) * Real.sqrt (Real.sqrt z) :=
          mul_le_mul hW hW (Nat.cast_nonneg _) hV0
      _ = Real.sqrt z := Real.mul_self_sqrt (Real.sqrt_nonneg z)
  have hsqz : ⌊Real.sqrt z⌋₊ ≤ ⌊z⌋₊ := Nat.floor_mono (Sieve.sqrt_le_self z hz)
  have h2E : 2 ∈ (2 * disc a₁ a₂ b₁ b₂).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_mul_right 2 _, hq0.ne'⟩
  have h22 : 2 ∈ Nat.primeFactors 2 :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_refl 2, two_ne_zero⟩
  apply harm_mul_le (rho a₁ a₂ b₁ b₂) (2 * disc a₁ a₂ b₁ b₂).primeFactors
    (rho_nonneg a₁ a₂ b₁ b₂) (fun p _ => one_le_rho a₁ a₂ b₁ b₂ p)
  · intro p hp hpQ
    have hndvd : ¬ p ∣ disc a₁ a₂ b₁ b₂ := by
      intro h
      exact hpQ (Nat.mem_primeFactors.mpr ⟨hp, Dvd.dvd.mul_left h 2, hq0.ne'⟩)
    simp only [rho, if_neg hndvd, le_refl]
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_Icc] at ha
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one ha.1.1
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    exact ⟨Nat.lt_of_lt_of_le Nat.zero_lt_one hb.1.1, hb.2⟩
  · intro a ha b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at ha hb
    obtain ⟨⟨ha1, haW⟩, ha2⟩ := ha
    obtain ⟨⟨hb1, hbW⟩, hb2⟩ := hb
    have hab : a * b ≤ ⌊Real.sqrt z⌋₊ :=
      le_trans (Nat.mul_le_mul haW hbW) hWW
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.mul_pos ha1 hb1, hab⟩, ?_⟩
    intro p hp hpab
    rw [prime_dvd_prod_oddPrimes_iff z hp]
    constructor
    · exact le_trans (Nat.le_of_dvd (Nat.mul_pos ha1 hb1) hpab) (le_trans hab hsqz)
    · rintro rfl
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hpab with h | h
      · exact ha2 2 h22 h
      · exact hb2 2 h2E h

/-- **The sieve bound** (non-degenerate case), for `z > 1`. -/
theorem count_le_nondeg (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hcop : Nat.Coprime a₁ a₂)
    (hD : det a₁ a₂ b₁ b₂ ≠ 0) (hg₁ : Nat.Coprime a₁ b₁.natAbs)
    (hg₂ : Nat.Coprime a₂ b₂.natAbs) (u : ℤ) (L : ℕ) (z : ℝ) (hz : 1 < z) :
    ((((Finset.Icc u (u + (L : ℤ))).filter (fun t : ℤ =>
        ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card : ℕ) : ℝ) ≤
      ((L : ℝ) + 1) / glb a₁ a₂ b₁ b₂ z +
        (z * (1 + Real.log z) ^ 6 + 2 * ((⌊z⌋₊ : ℝ) + 1)) := by
  have hz1 : 1 ≤ z := hz.le
  have h1 := card_prime_pairs_le_sifted a₁ a₂ b₁ b₂ ha₁ ha₂ u L z hz1
  have h2 := SelbergSieve.selberg_bound_simple (twoSieve a₁ a₂ b₁ b₂ u L z hz1)
  have h3 := errSum_le a₁ a₂ b₁ b₂ hcop hg₁ hg₂ u L z hz1
  have h4 := boundingSum_ge a₁ a₂ b₁ b₂ ha₁ ha₂ hD u L z hz1
  have hsz : 1 < Real.sqrt z := Real.lt_sqrt_of_sq_lt (by rw [one_pow]; exact hz)
  have hV : 1 < Real.sqrt (Real.sqrt z) := Real.lt_sqrt_of_sq_lt (by rw [one_pow]; exact hsz)
  have hlogV : 0 < Real.log (Real.sqrt (Real.sqrt z)) := Real.log_pos hV
  have hq0 : 0 < 2 * disc a₁ a₂ b₁ b₂ := Nat.mul_pos two_pos (disc_pos a₁ a₂ b₁ b₂ ha₁ ha₂ hD)
  have hφ : (0 : ℝ) < (2 * disc a₁ a₂ b₁ b₂).totient := by
    exact_mod_cast Nat.totient_pos.mpr hq0
  have hqR : (0 : ℝ) < ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ) := by exact_mod_cast hq0
  have hGpos : 0 < glb a₁ a₂ b₁ b₂ z := by
    unfold glb
    exact mul_pos (mul_pos (by norm_num) hlogV) (mul_pos (div_pos hφ hqR) hlogV)
  have hX : 0 ≤ (twoSieve a₁ a₂ b₁ b₂ u L z hz1).totalMass := by
    change (0 : ℝ) ≤ (L : ℝ) + 1
    positivity
  have h5 : (twoSieve a₁ a₂ b₁ b₂ u L z hz1).totalMass /
      (twoSieve a₁ a₂ b₁ b₂ u L z hz1).selbergBoundingSum ≤ ((L : ℝ) + 1) / glb a₁ a₂ b₁ b₂ z :=
    div_le_div_of_nonneg_left hX hGpos h4
  have h6 : siftedSum (s := (twoSieve a₁ a₂ b₁ b₂ u L z hz1).toBoundingSieve) ≤
      ((L : ℝ) + 1) / glb a₁ a₂ b₁ b₂ z + z * (1 + Real.log z) ^ 6 :=
    le_trans h2 (add_le_add h5 h3)
  linarith

/-! ## Parameter choice `z = √T` -/

/-- `(√T (1 + log √T)^6 + 2(⌊√T⌋ + 1)) (log T)^2 ≤ 136049920 T` for `T ≥ 1`
(via `y = T^{1/16}`, `log T ≤ 16 y`). -/
theorem err_bound (T : ℝ) (hT : 1 ≤ T) :
    (Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 + 2 * ((⌊Real.sqrt T⌋₊ : ℝ) + 1)) *
      Real.log T ^ 2 ≤ 136049920 * T := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = T ^ ((1 : ℝ) / 16) := ⟨_, rfl⟩
  have hy1 : 1 ≤ y := by
    rw [hy]
    exact Real.one_le_rpow hT (by norm_num)
  have hy0' : 0 ≤ y := by linarith
  have hy16 : y ^ 16 = T := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hT0]
    norm_num
  have hsq : Real.sqrt T = y ^ 8 := by
    rw [← hy16, show (16 : ℕ) = 8 * 2 from rfl, pow_mul, Real.sqrt_sq (pow_nonneg hy0' 8)]
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlog : Real.log T ≤ 16 * y := by
    have h := Real.log_le_rpow_div hT0 (by norm_num : (0 : ℝ) < 1 / 16)
    rw [← hy] at h
    have e : y / (1 / 16) = 16 * y := by ring
    linarith
  have hlogs : Real.log (Real.sqrt T) = Real.log T / 2 := Real.log_sqrt hT0
  have hsq0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hfl : ((⌊Real.sqrt T⌋₊ : ℕ) : ℝ) ≤ y ^ 8 := (Nat.floor_le hsq0).trans (le_of_eq hsq)
  have h1 : 1 + Real.log (Real.sqrt T) ≤ 9 * y := by
    rw [hlogs]
    linarith
  have h1' : 0 ≤ 1 + Real.log (Real.sqrt T) := by
    rw [hlogs]
    linarith
  have h6 : (1 + Real.log (Real.sqrt T)) ^ 6 ≤ (9 * y) ^ 6 := pow_le_pow_left₀ h1' h1 6
  have h2 : Real.log T ^ 2 ≤ (16 * y) ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
  have hA : Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 ≤ y ^ 8 * (9 * y) ^ 6 := by
    calc Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 ≤ Real.sqrt T * (9 * y) ^ 6 :=
          mul_le_mul_of_nonneg_left h6 hsq0
      _ = y ^ 8 * (9 * y) ^ 6 := by rw [hsq]
  have hB : 2 * (((⌊Real.sqrt T⌋₊ : ℕ) : ℝ) + 1) ≤ 2 * (y ^ 8 + 1) := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hsum0 : 0 ≤ y ^ 8 * (9 * y) ^ 6 + 2 * (y ^ 8 + 1) := by positivity
  have hp2 : y ^ 2 ≤ y ^ 16 := pow_le_pow_right₀ hy1 (by norm_num)
  have hp10 : y ^ 10 ≤ y ^ 16 := pow_le_pow_right₀ hy1 (by norm_num)
  calc (Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 + 2 * ((⌊Real.sqrt T⌋₊ : ℝ) + 1)) *
        Real.log T ^ 2
      ≤ (y ^ 8 * (9 * y) ^ 6 + 2 * (y ^ 8 + 1)) * (16 * y) ^ 2 :=
        mul_le_mul (add_le_add hA hB) h2 (sq_nonneg _) hsum0
    _ = 136048896 * y ^ 16 + 512 * y ^ 10 + 512 * y ^ 2 := by ring
    _ ≤ 136048896 * y ^ 16 + 512 * y ^ 16 + 512 * y ^ 16 := by linarith
    _ = 136049920 * T := by
        rw [← hy16]
        ring

/-- `2E ≤ 2 · (a₁/φ(a₁)) (a₂/φ(a₂)) (|D|/φ(|D|)) · φ(2E)`. -/
theorem two_disc_le (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hD : det a₁ a₂ b₁ b₂ ≠ 0) :
    ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ) ≤
      2 * (((a₁ : ℝ) / (a₁.totient : ℝ)) * ((a₂ : ℝ) / (a₂.totient : ℝ)) *
        (((det a₁ a₂ b₁ b₂).natAbs : ℝ) / (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ))) *
        ((2 * disc a₁ a₂ b₁ b₂).totient : ℝ) := by
  have hD0 : 0 < (det a₁ a₂ b₁ b₂).natAbs := Int.natAbs_pos.mpr hD
  have hφ1 : (0 : ℝ) < a₁.totient := by exact_mod_cast Nat.totient_pos.mpr ha₁
  have hφ2 : (0 : ℝ) < a₂.totient := by exact_mod_cast Nat.totient_pos.mpr ha₂
  have hφD : (0 : ℝ) < ((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) := by
    exact_mod_cast Nat.totient_pos.mpr hD0
  have hn : a₁.totient * a₂.totient * (det a₁ a₂ b₁ b₂).natAbs.totient ≤
      (2 * disc a₁ a₂ b₁ b₂).totient := by
    calc a₁.totient * a₂.totient * (det a₁ a₂ b₁ b₂).natAbs.totient
        ≤ (a₁ * a₂).totient * (det a₁ a₂ b₁ b₂).natAbs.totient :=
          Nat.mul_le_mul_right _ (Nat.totient_super_multiplicative a₁ a₂)
      _ ≤ (disc a₁ a₂ b₁ b₂).totient := Nat.totient_super_multiplicative _ _
      _ = (2 : ℕ).totient * (disc a₁ a₂ b₁ b₂).totient := by rw [Nat.totient_two, one_mul]
      _ ≤ (2 * disc a₁ a₂ b₁ b₂).totient := Nat.totient_super_multiplicative _ _
  have e1 : (a₁ : ℝ) / (a₁.totient : ℝ) * (a₁.totient : ℝ) = a₁ := div_mul_cancel₀ _ hφ1.ne'
  have e2 : (a₂ : ℝ) / (a₂.totient : ℝ) * (a₂.totient : ℝ) = a₂ := div_mul_cancel₀ _ hφ2.ne'
  have e3 : ((det a₁ a₂ b₁ b₂).natAbs : ℝ) /
      (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ) *
      (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ) = (det a₁ a₂ b₁ b₂).natAbs :=
    div_mul_cancel₀ _ hφD.ne'
  have key : ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ) =
      2 * (((a₁ : ℝ) / (a₁.totient : ℝ)) * ((a₂ : ℝ) / (a₂.totient : ℝ)) *
        (((det a₁ a₂ b₁ b₂).natAbs : ℝ) / (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ))) *
        (((a₁.totient * a₂.totient * (det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ)) := by
    calc ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ)
        = 2 * ((a₁ : ℝ) * (a₂ : ℝ) * ((det a₁ a₂ b₁ b₂).natAbs : ℝ)) := by
          simp only [disc, Nat.cast_mul, Nat.cast_ofNat]
      _ = 2 * (((a₁ : ℝ) / (a₁.totient : ℝ) * (a₁.totient : ℝ)) *
            ((a₂ : ℝ) / (a₂.totient : ℝ) * (a₂.totient : ℝ)) *
            (((det a₁ a₂ b₁ b₂).natAbs : ℝ) / (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ) *
              (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ))) := by
          rw [e1, e2, e3]
      _ = _ := by
          push_cast
          ring
  rw [key]
  have hR0 : 0 ≤ 2 * (((a₁ : ℝ) / (a₁.totient : ℝ)) * ((a₂ : ℝ) / (a₂.totient : ℝ)) *
        (((det a₁ a₂ b₁ b₂).natAbs : ℝ) / (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ))) := by
    positivity
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hR0

end TheSieve

/-- **Two-dimensional upper-bound sieve** (Halberstam–Richert, *Sieve Methods*, Thm 2.2, the case
of two linear forms). For coprime `a₁, a₂ ≥ 1` and `D = a₁ b₂ − a₂ b₁ ≠ 0`, every integer `u` and
every real `T ≥ 2`, the number of `t ∈ [u, u + ⌊T⌋]` with `a₁ t + b₁` and `a₂ t + b₂` both prime is
at most `2^28 · T/(log T)^2 · a₁/φ(a₁) · a₂/φ(a₂) · |D|/φ(|D|)`. -/
theorem two_dim_sieve (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hcop : Nat.Coprime a₁ a₂) (hD : (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0) (u : ℤ) (T : ℝ)
    (hT : 2 ≤ T) :
    ((((Finset.Icc u (u + ⌊T⌋)).filter
          (fun t : ℤ =>
            ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card : ℕ)
          : ℝ) ≤
        2 ^ 28 * T / (Real.log T) ^ 2 * ((a₁ : ℝ) / (a₁.totient : ℝ)) *
          ((a₂ : ℝ) / (a₂.totient : ℝ)) *
          ((((a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁).natAbs : ℝ) /
            ((((a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁).natAbs.totient : ℕ) : ℝ)) := by
  have hdet : det a₁ a₂ b₁ b₂ ≠ 0 := hD
  have hdet' : det a₁ a₂ b₁ b₂ = (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ := rfl
  rw [← hdet']
  have hD0 : 0 < (det a₁ a₂ b₁ b₂).natAbs := Int.natAbs_pos.mpr hdet
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hK : 0 < Real.log T ^ 2 := by positivity
  have hφ1 : (0 : ℝ) < a₁.totient := by exact_mod_cast Nat.totient_pos.mpr ha₁
  have hφ2 : (0 : ℝ) < a₂.totient := by exact_mod_cast Nat.totient_pos.mpr ha₂
  have hφD : (0 : ℝ) < ((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) := by
    exact_mod_cast Nat.totient_pos.mpr hD0
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ((a₁ : ℝ) / (a₁.totient : ℝ)) * ((a₂ : ℝ) / (a₂.totient : ℝ)) *
      (((det a₁ a₂ b₁ b₂).natAbs : ℝ) / (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ)) :=
    ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by
    have e1 : 1 ≤ (a₁ : ℝ) / (a₁.totient : ℝ) := by
      rw [one_le_div hφ1]
      exact_mod_cast Nat.totient_le a₁
    have e2 : 1 ≤ (a₂ : ℝ) / (a₂.totient : ℝ) := by
      rw [one_le_div hφ2]
      exact_mod_cast Nat.totient_le a₂
    have e3 : 1 ≤ ((det a₁ a₂ b₁ b₂).natAbs : ℝ) /
        (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ) := by
      rw [one_le_div hφD]
      exact_mod_cast Nat.totient_le _
    rw [hR]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le e1 e2) e3
  have hgoal : 2 ^ 28 * T / (Real.log T) ^ 2 * ((a₁ : ℝ) / (a₁.totient : ℝ)) *
      ((a₂ : ℝ) / (a₂.totient : ℝ)) *
      (((det a₁ a₂ b₁ b₂).natAbs : ℝ) / (((det a₁ a₂ b₁ b₂).natAbs.totient : ℕ) : ℝ)) =
      268435456 * T * R / Real.log T ^ 2 := by
    rw [hR]
    ring
  rw [hgoal, le_div_iff₀ hK]
  have hTR : T ≤ T * R := le_mul_of_one_le_right hT0 hR1
  have hTR0 : 0 ≤ T * R := mul_nonneg hT0 (by linarith)
  have herr := err_bound T hT1
  have hErr2 : 2 ≤ Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 +
      2 * ((⌊Real.sqrt T⌋₊ : ℝ) + 1) := by
    have hlogs : 0 ≤ Real.log (Real.sqrt T) :=
      Real.log_nonneg (Real.one_le_sqrt.mpr hT1)
    have : 0 ≤ Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 := by positivity
    have : (0 : ℝ) ≤ (⌊Real.sqrt T⌋₊ : ℝ) := Nat.cast_nonneg _
    linarith
  by_cases hnd : Nat.Coprime a₁ b₁.natAbs ∧ Nat.Coprime a₂ b₂.natAbs
  · obtain ⟨hg₁, hg₂⟩ := hnd
    have hfloor : ⌊T⌋ = ((⌊T⌋₊ : ℕ) : ℤ) := (Int.natCast_floor_eq_floor hT0).symm
    rw [hfloor]
    have hz : 1 < Real.sqrt T := Real.lt_sqrt_of_sq_lt (by rw [one_pow]; linarith)
    have hmain := count_le_nondeg a₁ a₂ b₁ b₂ ha₁ ha₂ hcop hdet hg₁ hg₂ u ⌊T⌋₊ (Real.sqrt T) hz
    have hV : Real.log (Real.sqrt (Real.sqrt (Real.sqrt T))) = Real.log T / 8 := by
      rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt (Real.sqrt_nonneg _),
        Real.log_sqrt hT0]
      ring
    have hq0 : 0 < 2 * disc a₁ a₂ b₁ b₂ := Nat.mul_pos two_pos (disc_pos a₁ a₂ b₁ b₂ ha₁ ha₂ hdet)
    have hφq : (0 : ℝ) < (2 * disc a₁ a₂ b₁ b₂).totient := by
      exact_mod_cast Nat.totient_pos.mpr hq0
    have hqR : (0 : ℝ) < ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ) := by exact_mod_cast hq0
    have hGlb : glb a₁ a₂ b₁ b₂ (Real.sqrt T) = Real.log T ^ 2 *
        (((2 * disc a₁ a₂ b₁ b₂).totient : ℝ) / ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ)) / 128 := by
      unfold glb
      rw [hV]
      ring
    have hRφ : 1 / 2 ≤ R * (((2 * disc a₁ a₂ b₁ b₂).totient : ℝ) /
        ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ)) := by
      have h := two_disc_le a₁ a₂ b₁ b₂ ha₁ ha₂ hdet
      rw [← hR] at h
      rw [← mul_div_assoc, le_div_iff₀ hqR]
      linarith
    have hL : ((⌊T⌋₊ : ℕ) : ℝ) + 1 ≤ 2 * T := by
      have := Nat.floor_le hT0
      linarith
    have hGpos : 0 < Real.log T ^ 2 *
        (((2 * disc a₁ a₂ b₁ b₂).totient : ℝ) / ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ)) / 128 :=
      div_pos (mul_pos hK (div_pos hφq hqR)) (by norm_num)
    have hMK : (((⌊T⌋₊ : ℕ) : ℝ) + 1) / glb a₁ a₂ b₁ b₂ (Real.sqrt T) * Real.log T ^ 2 ≤
        512 * T * R := by
      rw [hGlb, div_mul_eq_mul_div, div_le_iff₀ hGpos]
      calc (((⌊T⌋₊ : ℕ) : ℝ) + 1) * Real.log T ^ 2 ≤ 2 * T * Real.log T ^ 2 :=
            mul_le_mul_of_nonneg_right hL hK.le
        _ = 4 * T * Real.log T ^ 2 * (1 / 2) := by ring
        _ ≤ 4 * T * Real.log T ^ 2 * (R * (((2 * disc a₁ a₂ b₁ b₂).totient : ℝ) /
              ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hRφ (mul_nonneg (mul_nonneg (by norm_num) hT0) hK.le)
        _ = 512 * T * R * (Real.log T ^ 2 *
              (((2 * disc a₁ a₂ b₁ b₂).totient : ℝ) / ((2 * disc a₁ a₂ b₁ b₂ : ℕ) : ℝ)) / 128) := by
            ring
    calc ((((Finset.Icc u (u + ((⌊T⌋₊ : ℕ) : ℤ))).filter (fun t : ℤ =>
            ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card : ℕ) : ℝ) *
          Real.log T ^ 2
        ≤ ((((⌊T⌋₊ : ℕ) : ℝ) + 1) / glb a₁ a₂ b₁ b₂ (Real.sqrt T) +
            (Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 +
              2 * ((⌊Real.sqrt T⌋₊ : ℝ) + 1))) * Real.log T ^ 2 :=
          mul_le_mul_of_nonneg_right hmain hK.le
      _ = (((⌊T⌋₊ : ℕ) : ℝ) + 1) / glb a₁ a₂ b₁ b₂ (Real.sqrt T) * Real.log T ^ 2 +
            (Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 +
              2 * ((⌊Real.sqrt T⌋₊ : ℝ) + 1)) * Real.log T ^ 2 := by ring
      _ ≤ 512 * T * R + 136049920 * T := add_le_add hMK herr
      _ ≤ 268435456 * T * R := by linarith
  · -- a degenerate form takes at most one prime value
    have hc : ((Finset.Icc u (u + ⌊T⌋)).filter (fun t : ℤ =>
        ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card ≤ 1 := by
      rcases not_and_or.mp hnd with h | h
      · refine le_trans (Finset.card_le_card ?_)
          (card_prime_values_le_one a₁ b₁ ha₁ h (Finset.Icc u (u + ⌊T⌋)))
        intro t ht
        rw [Finset.mem_filter] at ht ⊢
        exact ⟨ht.1, ht.2.1⟩
      · refine le_trans (Finset.card_le_card ?_)
          (card_prime_values_le_one a₂ b₂ ha₂ h (Finset.Icc u (u + ⌊T⌋)))
        intro t ht
        rw [Finset.mem_filter] at ht ⊢
        exact ⟨ht.1, ht.2.2⟩
    have hc' : ((((Finset.Icc u (u + ⌊T⌋)).filter (fun t : ℤ =>
        ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast hc
    have hK2 : 2 * Real.log T ^ 2 ≤ 136049920 * T := by
      calc 2 * Real.log T ^ 2 ≤ (Real.sqrt T * (1 + Real.log (Real.sqrt T)) ^ 6 +
            2 * ((⌊Real.sqrt T⌋₊ : ℝ) + 1)) * Real.log T ^ 2 :=
            mul_le_mul_of_nonneg_right hErr2 hK.le
        _ ≤ 136049920 * T := herr
    calc ((((Finset.Icc u (u + ⌊T⌋)).filter (fun t : ℤ =>
            ((a₁ : ℤ) * t + b₁).toNat.Prime ∧ ((a₂ : ℤ) * t + b₂).toNat.Prime)).card : ℕ) : ℝ) *
          Real.log T ^ 2
        ≤ 1 * Real.log T ^ 2 := mul_le_mul_of_nonneg_right hc' hK.le
      _ ≤ 268435456 * T * R := by linarith

end Principia.Common.TwoDimSieve

end
