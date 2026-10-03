/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.LucaPomerance.Abundancy
import Principia.Common.LucaPomerance.AliquotPrimes

set_option autoImplicit false

/-!
# Pollack's Theorem 1.4, weak form: `s(s(n))/s(n) ≤ s(n)/n + 1` for almost all `n`

Pollack (*Some arithmetic applications of a theorem of Erdős…* — Illinois J. Math. 58 (2014),
Theorem 1.4) proves `|s(s(n))/s(n) − s(n)/n| ≤ (log₂ x)^{-1/4}` for all but
`O(x (log₃ x)²/(log₂ x)^{1/4})` integers `n ≤ x`. **Here:** the one-sided statement with slack `1`,
without a rate (`pollack_weak`), which is all the Erdős-1054 paper uses.

It is proved from one hypothesis, `FixedModulusNormal` (for every fixed `V ≥ 1`, `V ∣ σ(n)` for
almost all `n`), which the Erdős-1054 library proves unconditionally
(`ep1054_Lem_FixedModulusNormality`, from Dirichlet's divergence of `∑_{p ≡ −1 (q)} 1/p`).

**Proof.** Fix `ε`, then `K, δ = 1/(4K), u, w, k` and `V = (w!)^k`. Off
* `{h(n) > K}` (`≤ 2X/K`, `Common.Davenport.card_abund_gt_le`),
* `{p^k ∣ n for a prime p ≤ w}` (`≤ (w + 1) X/2^k`),
* `{V ∤ σ(n)}` (density zero by hypothesis),
* `{∑_{p ∣ s(n), p > w} 1/p > δ}` (`card_bigPrimeRecip_gt_le`),

`abund_aliq_le` gives `h(s(n)) ≤ h(n) e^{2δ} ≤ h(n)(1 + 1/K) ≤ h(n) + 1`, which is the claim
(`s(s(n))/s(n) = h(s(n)) − 1`, `s(n)/n = h(n) − 1`).
-/

namespace Principia.Common.LucaPomerance.Pollack14

open Principia.Common.LucaPomerance.Aliquot

open Finset
open Principia.Common.Davenport (abund abund_nonneg card_abund_gt_le)

/-- The exceptional set of Pollack's Theorem 1.4 in the weak form: `s(n)/n + 1 < s(s(n))/s(n)`. -/
def PollackBad (n : ℕ) : Prop :=
  (aliq n : ℝ) / n + 1 < (aliq (aliq n) : ℝ) / (aliq n : ℝ)

/-- Fixed-modulus normality of `σ`, in counting form: for every `V ≥ 1`, `V ∤ σ(n)` for at most
`εX` integers `n ≤ X`, for all large `X`. -/
def FixedModulusNormal : Prop :=
  ∀ V : ℕ, 1 ≤ V → ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    (((Icc 1 ⌊X⌋₊).filter (fun n => ¬ V ∣ ArithmeticFunction.sigma 1 n)).card : ℝ) ≤ ε * X

/-- `s(N)/N = h(N) − 1` for `N ≥ 1`. -/
theorem aliq_div_eq {N : ℕ} (hN : N ≠ 0) : (aliq N : ℝ) / N = abund N - 1 := by
  unfold aliq abund
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [Nat.cast_sub (le_sigma N)]
  field_simp

/-- `e^{1/(2K)} ≤ 1 + 1/K`. -/
theorem exp_half_inv_le (K : ℝ) (hK : 1 ≤ K) : Real.exp (1 / (2 * K)) ≤ 1 + 1 / K := by
  have hK0 : 0 < K := by linarith
  have hx0 : 0 ≤ 1 / (2 * K) := by positivity
  have hx1 : 1 / (2 * K) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  refine (Real.exp_bound_div_one_sub_of_interval hx0 hx1).trans ?_
  have h1 : 0 < 1 - 1 / (2 * K) := by linarith
  rw [div_le_iff₀ h1]
  have e : (1 + 1 / K) * (1 - 1 / (2 * K)) = 1 + (1 / (2 * K)) * (1 - 1 / K) := by
    field_simp
    ring
  rw [e]
  have h2 : 0 ≤ 1 - 1 / K := by
    rw [sub_nonneg, div_le_one hK0]
    exact hK
  nlinarith

/-- **The pointwise step.** If `h(n) ≤ K`, `(w!)^k ∣ σ(n)`, `p^k ∤ n` for the primes `p ≤ w`, and
`∑_{p ∣ s(n), p > w} 1/p ≤ 1/(4K)`, then `n` is not exceptional. -/
theorem not_pollackBad {n w k K : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ K) (habund : abund n ≤ K)
    (hσ : (w.factorial) ^ k ∣ ArithmeticFunction.sigma 1 n)
    (hnk : ∀ p, p.Prime → p ≤ w → ¬ p ^ k ∣ n)
    (hT : bigPrimeRecip w n ≤ 1 / (4 * K)) : ¬ PollackBad n := by
  unfold PollackBad
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have h1 : n = 1 := by omega
    subst h1
    have hs : aliq 1 = 0 := by
      unfold aliq
      simp
    rw [hs]
    norm_num
  have hs0 : aliq n ≠ 0 := by have := one_le_aliq hn2; omega
  have hσ' : ∀ p, p.Prime → p ≤ w → p ^ k ∣ ArithmeticFunction.sigma 1 n := fun p hp hpw =>
    (pow_dvd_pow_of_dvd (Nat.dvd_factorial hp.pos hpw) k).trans hσ
  have hmain := abund_aliq_le hn2 hσ' hnk
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hexp : Real.exp (2 * bigPrimeRecip w n) ≤ 1 + 1 / (K : ℝ) := by
    refine le_trans (Real.exp_le_exp.2 ?_) (exp_half_inv_le K hKR)
    have : 2 * (1 / (4 * (K : ℝ))) = 1 / (2 * K) := by field_simp; ring
    have hT' : bigPrimeRecip w n ≤ 1 / (4 * (K : ℝ)) := by exact_mod_cast hT
    linarith
  have hb0 := abund_nonneg n
  have hle : abund (aliq n) ≤ abund n + 1 := by
    have h1 : abund (aliq n) ≤ abund n * (1 + 1 / (K : ℝ)) :=
      hmain.trans (mul_le_mul_of_nonneg_left hexp hb0)
    have h2 : abund n * (1 / (K : ℝ)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]
      exact habund
    nlinarith
  rw [aliq_div_eq (by omega : n ≠ 0), aliq_div_eq hs0]
  push Not
  linarith

/-- `#{n ≤ N : p^k ∣ n for a prime p ≤ w} ≤ (w + 1) N / 2^k`. -/
theorem card_small_prime_pow_dvd_le (N w k : ℕ) :
    (((Icc 1 N).filter (fun n => ∃ p ∈ (Iic w).filter Nat.Prime, p ^ k ∣ n)).card : ℝ) ≤
      (w + 1) * N / 2 ^ k := by
  have hsub : (Icc 1 N).filter (fun n => ∃ p ∈ (Iic w).filter Nat.Prime, p ^ k ∣ n) ⊆
      ((Iic w).filter Nat.Prime).biUnion (fun p => (Icc 1 N).filter (fun n => p ^ k ∣ n)) := by
    intro n hn
    obtain ⟨hn1, p, hp, hd⟩ := Finset.mem_filter.1 hn
    exact Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_filter.2 ⟨hn1, hd⟩⟩
  have hIcc : (Icc 1 N) = Ioc 0 N := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hterm : ∀ p ∈ (Iic w).filter Nat.Prime,
      ((((Icc 1 N).filter (fun n => p ^ k ∣ n)).card : ℕ) : ℝ) ≤ N / 2 ^ k := by
    intro p hp
    have hp2 : 2 ≤ p := (Finset.mem_filter.1 hp).2.two_le
    rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div N (p ^ k)]
    have h2k : (2 : ℝ) ^ k ≤ ((p ^ k : ℕ) : ℝ) := by
      push_cast
      exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp2) k
    calc (((N / p ^ k : ℕ)) : ℝ) ≤ (N : ℝ) / ((p ^ k : ℕ) : ℝ) := Nat.cast_div_le
      _ ≤ N / 2 ^ k := div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity) h2k
  have hcardP : (((Iic w).filter Nat.Prime).card : ℝ) ≤ w + 1 := by
    have h := Finset.card_filter_le (Iic w) Nat.Prime
    rw [Nat.card_Iic] at h
    exact_mod_cast h
  calc (((Icc 1 N).filter (fun n => ∃ p ∈ (Iic w).filter Nat.Prime, p ^ k ∣ n)).card : ℝ)
      ≤ ∑ p ∈ (Iic w).filter Nat.Prime,
          ((((Icc 1 N).filter (fun n => p ^ k ∣ n)).card : ℕ) : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ (Iic w).filter Nat.Prime, (N : ℝ) / 2 ^ k := Finset.sum_le_sum hterm
    _ = (((Iic w).filter Nat.Prime).card : ℝ) * (N / 2 ^ k) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (w + 1) * (N / 2 ^ k) := mul_le_mul_of_nonneg_right hcardP (by positivity)
    _ = (w + 1) * N / 2 ^ k := by ring

open Classical in
/-- **Pollack's Theorem 1.4, weak form**, from fixed-modulus normality: for every `ε > 0`, for all
large `X`, at most `εX` integers `n ≤ X` have `s(n)/n + 1 < s(s(n))/s(n)`. -/
theorem pollack_weak (hnorm : FixedModulusNormal) :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      (((Icc 1 ⌊X⌋₊).filter PollackBad).card : ℝ) ≤ ε * X := by
  intro ε hε
  -- the parameters
  set K : ℕ := ⌈16 / ε⌉₊ + 1 with hKdef
  have hK1 : 1 ≤ K := by omega
  have hKR : 16 / ε ≤ (K : ℝ) := by
    have := Nat.le_ceil (16 / ε)
    rw [hKdef]
    push_cast
    linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  set δ : ℝ := 1 / (4 * K) with hδdef
  have hδ : 0 < δ := by positivity
  set u : ℕ := ⌈32 * mertensConst / ε⌉₊ + 1 with hudef
  have hu1 : 1 ≤ u := by omega
  have huR : 32 * mertensConst / ε ≤ (u : ℝ) := by
    have := Nat.le_ceil (32 * mertensConst / ε)
    rw [hudef]
    push_cast
    linarith
  have hupos : (0 : ℝ) < u := by exact_mod_cast hu1
  set w : ℕ := ⌈16 / (ε * δ) * (1 + 16064 * u)⌉₊ + 1 with hwdef
  have hw1 : 1 ≤ w := by omega
  have hwR : 16 / (ε * δ) * (1 + 16064 * u) ≤ (w : ℝ) := by
    have := Nat.le_ceil (16 / (ε * δ) * (1 + 16064 * (u : ℝ)))
    rw [hwdef]
    push_cast
    linarith
  have hwpos : (0 : ℝ) < w := by exact_mod_cast hw1
  set k : ℕ := ⌈8 * (w + 1) / ε⌉₊ with hkdef
  have hkR : 8 * ((w : ℝ) + 1) / ε ≤ (2 : ℝ) ^ k := by
    have h1 := Nat.le_ceil (8 * ((w : ℝ) + 1) / ε)
    have h2 : (k : ℝ) ≤ (2 : ℝ) ^ k := by
      have := Nat.lt_two_pow_self (n := k)
      exact_mod_cast this.le
    rw [← hkdef] at h1
    linarith
  set V : ℕ := (w.factorial) ^ k with hVdef
  have hV1 : 1 ≤ V := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (Nat.factorial_ne_zero w))
  -- the two asymptotic inputs
  obtain ⟨X₁, hX₁⟩ := hnorm V hV1 (ε / 8) (by positivity)
  obtain ⟨X₂, hX₂⟩ := card_bigPrimeRecip_gt_le u w hu1 hw1 hδ (η := ε / 8) (by positivity)
  refine ⟨max (max X₁ X₂) 1, fun X hX => ?_⟩
  have hXX₁ : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXX₂ : X₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := by linarith
  set N := ⌊X⌋₊ with hN
  have hNX : (N : ℝ) ≤ X := Nat.floor_le hX0.le
  -- the covering
  have hcover : (Icc 1 N).filter PollackBad ⊆
      (((Icc 1 N).filter (fun n => (K : ℝ) < abund n) ∪
        (Icc 1 N).filter (fun n => ∃ p ∈ (Iic w).filter Nat.Prime, p ^ k ∣ n)) ∪
        (Icc 1 N).filter (fun n => ¬ V ∣ ArithmeticFunction.sigma 1 n)) ∪
        (Icc 1 N).filter (fun n => δ < bigPrimeRecip w n) := by
    intro n hn
    obtain ⟨hnI, hbad⟩ := Finset.mem_filter.1 hn
    have hn1 := (Finset.mem_Icc.1 hnI).1
    simp only [Finset.mem_union, Finset.mem_filter]
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩ := hcon
    have hA' : abund n ≤ K := hA hnI
    have hC' : V ∣ ArithmeticFunction.sigma 1 n := hC hnI
    have hD' : bigPrimeRecip w n ≤ 1 / (4 * K) := hD hnI
    have hB' : ∀ p, p.Prime → p ≤ w → ¬ p ^ k ∣ n := by
      intro p hp hpw hpk
      exact hB hnI p ⟨Finset.mem_Iic.2 hpw, hp⟩ hpk
    exact not_pollackBad hn1 hK1 hA' hC' hB' (by exact_mod_cast hD') hbad
  -- the four counts
  have hA := card_abund_gt_le N hKpos
  have hB := card_small_prime_pow_dvd_le N w k
  have hC := hX₁ X hXX₁
  have hD := hX₂ X hXX₂
  have htot : (((Icc 1 N).filter PollackBad).card : ℝ) ≤
      (((Icc 1 N).filter (fun n => (K : ℝ) < abund n)).card : ℝ) +
      (((Icc 1 N).filter (fun n => ∃ p ∈ (Iic w).filter Nat.Prime, p ^ k ∣ n)).card : ℝ) +
      (((Icc 1 N).filter (fun n => ¬ V ∣ ArithmeticFunction.sigma 1 n)).card : ℝ) +
      (((Icc 1 N).filter (fun n => δ < bigPrimeRecip w n)).card : ℝ) := by
    have h := (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
    exact_mod_cast h
  -- the numerics
  have hA' : 2 * (N : ℝ) / K ≤ ε / 8 * X := by
    rw [div_le_iff₀ hKpos]
    have : 16 ≤ ε * K := by
      have := mul_le_mul_of_nonneg_left hKR hε.le
      rwa [mul_div_cancel₀ _ hε.ne'] at this
    nlinarith
  have hB' : ((w : ℝ) + 1) * N / 2 ^ k ≤ ε / 8 * X := by
    rw [div_le_iff₀ (by positivity)]
    have : 8 * ((w : ℝ) + 1) ≤ ε * 2 ^ k := by
      have := mul_le_mul_of_nonneg_left hkR hε.le
      rwa [mul_div_cancel₀ _ hε.ne'] at this
    have hw0 : (0 : ℝ) ≤ (w : ℝ) + 1 := by positivity
    nlinarith
  have hDu : 4 * mertensConst / u ≤ ε / 8 := by
    rw [div_le_iff₀ hupos]
    have := mul_le_mul_of_nonneg_left huR hε.le
    rw [mul_div_cancel₀ _ hε.ne'] at this
    linarith
  have hDw : 2 / δ * (1 + 16064 * u) / w ≤ ε / 8 := by
    rw [div_le_iff₀ hwpos]
    have h1 := mul_le_mul_of_nonneg_left hwR (by positivity : (0 : ℝ) ≤ ε * δ)
    have e : ε * δ * (16 / (ε * δ) * (1 + 16064 * (u : ℝ))) = 16 * (1 + 16064 * u) := by
      field_simp
    rw [e] at h1
    have e2 : 2 / δ * (1 + 16064 * (u : ℝ)) = (16 * (1 + 16064 * u)) / (8 * δ) := by
      field_simp
      ring
    rw [e2, div_le_iff₀ (by positivity)]
    nlinarith
  have hD' : (4 * mertensConst / u + 2 / δ * (1 + 16064 * u) / w + ε / 8) * X ≤
      (3 * ε / 8) * X := by
    apply mul_le_mul_of_nonneg_right _ hX0.le
    linarith
  have hsum : (((Icc 1 N).filter PollackBad).card : ℝ) ≤
      ε / 8 * X + ε / 8 * X + ε / 8 * X + 3 * ε / 8 * X := by
    linarith
  linarith

end Principia.Common.LucaPomerance.Pollack14
