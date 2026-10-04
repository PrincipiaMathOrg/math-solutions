/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIGarnSpine

set_option autoImplicit false

/-!
# `T2G.WeightLB` reduced to one real variable `X = W/q`

`T2G.WeightLB` asks for `R` with
`∑_{r ≤ R sq-free, (r,q)=1} (N + (3/2)(1/qrR − 1/Q)⁻¹)⁻¹/φ(r) ≥ (φ(q)/q)·log(W/2q)/W`,
`N = ⌊W⌋ − ⌊W'⌋`. Two exact steps remove `q`, `Q`, `W'` and `N`:

```
 tS / step     dropping the multiples of one prime p from a square-free range costs at most
               the factor p/(p−1), for any weight f antitone on [1, R]          PROVED
 copRed        (φ(q)/q)·∑_{r ≤ R sq-free} f(r)/φ(r) ≤ ∑_{r ≤ R sq-free, (r,q)=1} f(r)/φ(r)
                                                                                PROVED
 n_le          N = ⌊W⌋ − ⌊W'⌋ ≤ (W + 1)/2   (W' ≥ W/2)                          PROVED
 den_le        N + (3/2)(1/qrR − 1/Q)⁻¹ ≤ W·(aW + (3/2)·rR/(X − rR/3.5)),
               aW = (W + 1)/2W, X = W/q, Q ≥ 3.5W                               PROVED
 WeightX       ∃ R ∈ [1, X/2], R² < 3.5X:
               log(X/2) ≤ ∑_{r ≤ R sq-free} (aW + (3/2)·rR/(X − rR/3.5))⁻¹/φ(r)  LINK
 weightLB_of_X : WeightX → T2G.WeightLB                                         PROVED
 garn1a_of_X   : MontgomeryIneq → MVWeighted → WeightX → T2X.Garn1a             PROVED
```

`copRed` is the step the book takes silently (`minarcs.tex` 3520-3523, "`≥ (φ(q)/q)∑_{r ≤ R}`"),
here for an arbitrary antitone weight. `WeightX` keeps `W` only through `aW ≤ 59/117`.
-/

namespace Principia.Common.TernaryGoldbach.T2V

open Principia.Common.TernaryGoldbach.T2G

/-- Square-free `r ∈ [1, R]` divisible by no prime of `P`. -/
noncomputable def tS (P : Finset ℕ) (R : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r ∧ ∀ p ∈ P, ¬ p ∣ r)

/-- Square-free `r ∈ [1, R]`. -/
noncomputable def sqS (R : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊R⌋₊).filter Squarefree

theorem tS_empty (R : ℝ) : tS ∅ R = sqS R := by
  unfold tS sqS
  refine Finset.filter_congr fun r _ => ?_
  simp

theorem tS_primeFactors (q : ℕ) (hq : q ≠ 0) (R : ℝ) : tS q.primeFactors R = rS q R := by
  unfold tS rS
  refine Finset.filter_congr fun r _ => ?_
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    refine Nat.coprime_of_dvd fun k hk hkr hkq => ?_
    exact h k (Nat.mem_primeFactors.mpr ⟨hk, hkq, hq⟩) hkr
  · intro h p hp hpr
    have hpq := (Nat.mem_primeFactors.mp hp)
    have h1 : p ∣ Nat.gcd r q := Nat.dvd_gcd hpr hpq.2.1
    rw [h] at h1
    exact hpq.1.one_lt.ne' (Nat.dvd_one.mp h1)

/-- **One prime**: removing the multiples of `p` loses at most the factor `p/(p − 1)`. -/
theorem step (P : Finset ℕ) (p : ℕ) (hp : p.Prime) (R : ℝ) (f : ℕ → ℝ)
    (hf0 : ∀ r, 1 ≤ r → r ≤ ⌊R⌋₊ → 0 ≤ f r)
    (hanti : ∀ s r, 1 ≤ s → s ≤ r → r ≤ ⌊R⌋₊ → f r ≤ f s) :
    ∑ r ∈ tS P R, f r / Nat.totient r ≤
      (p : ℝ) / (p - 1) * ∑ r ∈ tS (insert p P) R, f r / Nat.totient r := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p - 1 := by linarith
  rw [← Finset.sum_filter_add_sum_filter_not (tS P R) (fun r => p ∣ r)]
  have hnot : (tS P R).filter (fun r => ¬ p ∣ r) = tS (insert p P) R := by
    ext r
    simp only [tS, Finset.mem_filter, Finset.mem_insert, forall_eq_or_imp]
    tauto
  rw [hnot]
  set S := ∑ r ∈ tS (insert p P) R, f r / Nat.totient r with hS
  have hnn : ∀ s ∈ tS (insert p P) R, 0 ≤ f s / Nat.totient s := by
    intro s hs
    have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1
    exact div_nonneg (hf0 s h1.1 h1.2) (Nat.cast_nonneg _)
  have hS0 : 0 ≤ S := Finset.sum_nonneg hnn
  -- the multiples of `p`: `r = p s`
  have hmul : ∀ r ∈ (tS P R).filter (fun r => p ∣ r),
      r / p ∈ tS (insert p P) R ∧ r = p * (r / p) ∧
        f r / Nat.totient r ≤ f (r / p) / Nat.totient (r / p) / (p - 1) := by
    intro r hr
    obtain ⟨hr1, hdvd⟩ := Finset.mem_filter.mp hr
    obtain ⟨hrI, hsq, hP⟩ := Finset.mem_filter.mp hr1
    rw [Finset.mem_Icc] at hrI
    obtain ⟨s, rfl⟩ := hdvd
    have hps : p * s / p = s := Nat.mul_div_cancel_left s hp.pos
    rw [hps]
    have hs1 : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with h | h
      · rw [h] at hrI
        omega
      · exact h
    have hnps : ¬ p ∣ s := by
      intro h
      have h2 : p * p ∣ p * s := Nat.mul_dvd_mul_left p h
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p h2))
    have hcop : Nat.Coprime p s := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnps
    have hsle : s ≤ p * s := Nat.le_mul_of_pos_left s hp.pos
    refine ⟨?_, rfl, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hs1, hsle.trans hrI.2⟩,
        hsq.of_mul_right, ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with h | h
      · rw [h]
        exact hnps
      · exact fun hqs => hP q h (dvd_mul_of_dvd_right hqs p)
    · have htot : (Nat.totient (p * s) : ℝ) = (p - 1) * Nat.totient s := by
        rw [Nat.totient_mul hcop, Nat.totient_prime hp, Nat.cast_mul,
          Nat.cast_sub hp.one_le, Nat.cast_one]
      have hfs := hanti s (p * s) hs1 hsle hrI.2
      have hf0' := hf0 (p * s) (hs1.trans hsle) hrI.2
      have hts : (0 : ℝ) < Nat.totient s := by exact_mod_cast Nat.totient_pos.mpr hs1
      rw [htot, div_div, mul_comm ((Nat.totient s : ℕ) : ℝ) (p - 1)]
      exact div_le_div_of_nonneg_right hfs (by positivity)
  have hinj : Set.InjOn (fun r => r / p) ((tS P R).filter (fun r => p ∣ r) : Set ℕ) := by
    intro r1 h1 r2 h2 h
    have e1 := (hmul r1 h1).2.1
    have e2 := (hmul r2 h2).2.1
    simp only at h
    rw [e1, e2, h]
  have hT : ∑ r ∈ (tS P R).filter (fun r => p ∣ r), f r / Nat.totient r ≤ S / (p - 1) := by
    calc ∑ r ∈ (tS P R).filter (fun r => p ∣ r), f r / Nat.totient r
        ≤ ∑ r ∈ (tS P R).filter (fun r => p ∣ r),
            f (r / p) / Nat.totient (r / p) / (p - 1) :=
          Finset.sum_le_sum fun r hr => (hmul r hr).2.2
      _ = ∑ s ∈ ((tS P R).filter (fun r => p ∣ r)).image (fun r => r / p),
            f s / Nat.totient s / (p - 1) := by rw [Finset.sum_image hinj]
      _ ≤ ∑ s ∈ tS (insert p P) R, f s / Nat.totient s / (p - 1) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun s hs _ =>
            div_nonneg (hnn s hs) hp0.le
          intro s hs
          obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
          exact (hmul r hr).1
      _ = S / (p - 1) := by rw [Finset.sum_div]
  have e : (p : ℝ) / (p - 1) * S = S / (p - 1) + S := by
    field_simp
    ring
  rw [e]
  linarith

/-- **The coprimality reduction, over a set of primes**. -/
theorem copRed_P (R : ℝ) (f : ℕ → ℝ) (hf0 : ∀ r, 1 ≤ r → r ≤ ⌊R⌋₊ → 0 ≤ f r)
    (hanti : ∀ s r, 1 ≤ s → s ≤ r → r ≤ ⌊R⌋₊ → f r ≤ f s) :
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∏ p ∈ P, (1 - 1 / (p : ℝ))) * ∑ r ∈ tS ∅ R, f r / Nat.totient r ≤
        ∑ r ∈ tS P R, f r / Nat.totient r := by
  intro P
  induction P using Finset.induction_on with
  | empty => intro _; simp
  | insert p P hpP ih =>
    intro hP
    have hp := hP p (Finset.mem_insert_self p P)
    have ih' := ih fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hst := step P p hp R f hf0 hanti
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hc : 0 ≤ 1 - 1 / (p : ℝ) := by
      rw [sub_nonneg, div_le_one (by linarith)]
      exact hp1.le
    have hone : (1 - 1 / (p : ℝ)) * ((p : ℝ) / (p - 1)) = 1 := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp
    rw [Finset.prod_insert hpP, mul_assoc]
    calc (1 - 1 / (p : ℝ)) * ((∏ x ∈ P, (1 - 1 / (x : ℝ))) *
          ∑ r ∈ tS ∅ R, f r / Nat.totient r)
        ≤ (1 - 1 / (p : ℝ)) * ∑ r ∈ tS P R, f r / Nat.totient r :=
          mul_le_mul_of_nonneg_left ih' hc
      _ ≤ (1 - 1 / (p : ℝ)) * ((p : ℝ) / (p - 1) *
            ∑ r ∈ tS (insert p P) R, f r / Nat.totient r) :=
          mul_le_mul_of_nonneg_left hst hc
      _ = ∑ r ∈ tS (insert p P) R, f r / Nat.totient r := by
          rw [← mul_assoc, hone, one_mul]

/-- **`copRed`, PROVED**: for `f ≥ 0` antitone on `[1, R]`,
`(φ(q)/q)·∑_{r ≤ R sq-free} f(r)/φ(r) ≤ ∑_{r ≤ R sq-free, (r,q)=1} f(r)/φ(r)`. -/
theorem copRed (q : ℕ) (hq : 1 ≤ q) (R : ℝ) (f : ℕ → ℝ)
    (hf0 : ∀ r, 1 ≤ r → r ≤ ⌊R⌋₊ → 0 ≤ f r)
    (hanti : ∀ s r, 1 ≤ s → s ≤ r → r ≤ ⌊R⌋₊ → f r ≤ f s) :
    (Nat.totient q : ℝ) / q * ∑ r ∈ sqS R, f r / Nat.totient r ≤
      ∑ r ∈ rS q R, f r / Nat.totient r := by
  have hq0 : q ≠ 0 := by omega
  rw [Principia.Common.BrunTitchmarshAP.totient_div_eq_prod q (by omega), ← tS_empty,
    ← tS_primeFactors q hq0]
  exact copRed_P R f hf0 hanti q.primeFactors fun p hp => (Nat.mem_primeFactors.mp hp).1

/-- **`N ≤ (W + 1)/2`, PROVED**: `N = ⌊W⌋ − ⌊W'⌋` with `W' ≥ W/2 ≥ 0`. -/
theorem n_le (W W' : ℝ) (hW : 0 ≤ W) (hW' : W / 2 ≤ W') :
    (((⌊W⌋₊ - ⌊W'⌋₊ : ℕ)) : ℝ) ≤ (W + 1) / 2 := by
  set n := ⌊W⌋₊ with hn
  have h1 : n / 2 ≤ ⌊W'⌋₊ := by
    refine Nat.le_floor ?_
    have h2 : ((n / 2 : ℕ) : ℝ) * 2 ≤ n := by exact_mod_cast Nat.div_mul_le_self n 2
    have h3 : (n : ℝ) ≤ W := Nat.floor_le hW
    linarith
  have h4 : 2 * (n - ⌊W'⌋₊) ≤ n + 1 := by omega
  have h5 : (2 : ℝ) * (((n - ⌊W'⌋₊ : ℕ)) : ℝ) ≤ n + 1 := by exact_mod_cast h4
  have h3 : (n : ℝ) ≤ W := Nat.floor_le hW
  linarith

/-- The `q`-free weight: `aW = (W + 1)/(2W)`, `X = W/q`. -/
noncomputable def gX (W X R : ℝ) (r : ℕ) : ℝ :=
  ((W + 1) / (2 * W) + 3 / 2 * ((r : ℝ) * R / (X - r * R / 3.5)))⁻¹

/-- **Link [WeightX] — the `q`-free weight sum**: for `117 ≤ W`, `2 < X ≤ W`, some
`R ∈ [1, X/2]` with `R² < 3.5X` has `log(X/2) ≤ ∑_{r ≤ R sq-free} gX(r)/φ(r)`. OPEN. -/
def WeightX : Prop :=
  ∀ W X : ℝ, 117 ≤ W → 2 < X → X ≤ W →
    ∃ R : ℝ, 1 ≤ R ∧ R ≤ X / 2 ∧ R ^ 2 < 3.5 * X ∧
      Real.log (X / 2) ≤ ∑ r ∈ sqS R, gX W X R r / Nat.totient r

/-- `gX` is positive and antitone on `[1, R]` when `R² < 3.5X`. -/
theorem gX_pos_anti (W X R : ℝ) (hW : 0 < W) (hR : 1 ≤ R) (hRX : R ^ 2 < 3.5 * X) :
    (∀ r : ℕ, 1 ≤ r → r ≤ ⌊R⌋₊ → 0 < gX W X R r) ∧
      ∀ s r : ℕ, 1 ≤ s → s ≤ r → r ≤ ⌊R⌋₊ → gX W X R r ≤ gX W X R s := by
  have hR0 : 0 < R := by linarith
  rw [show (3.5 : ℝ) = 7 / 2 by norm_num] at hRX
  have hX : 0 < X := by nlinarith
  have key : ∀ r : ℕ, r ≤ ⌊R⌋₊ → 0 < X - r * R / 3.5 := by
    intro r hr
    have h1 : (r : ℝ) ≤ R := le_trans (Nat.cast_le.mpr hr) (Nat.floor_le hR0.le)
    have h2 : (r : ℝ) * R ≤ R ^ 2 := by nlinarith
    rw [show (3.5 : ℝ) = 7 / 2 by norm_num]
    linarith
  have hA : 0 < (W + 1) / (2 * W) := by positivity
  constructor
  · intro r _ hr
    have := key r hr
    unfold gX
    positivity
  · intro s r hs hsr hr
    have hr' := key r hr
    have hs' := key s (hsr.trans hr)
    have hsr' : (s : ℝ) ≤ r := by exact_mod_cast hsr
    unfold gX
    apply inv_anti₀ (by positivity)
    have : (s : ℝ) * R / (X - s * R / 3.5) ≤ r * R / (X - r * R / 3.5) := by
      rw [div_le_div_iff₀ hs' hr']
      rw [show (3.5 : ℝ) = 7 / 2 by norm_num]
      have := mul_nonneg (mul_nonneg (sub_nonneg.mpr hsr') hR0.le) hX.le
      nlinarith
    linarith

/-- **`den_le`, PROVED**: `N + (3/2)(1/qrR − 1/Q)⁻¹ ≤ W·(aW + (3/2)·rR/(X − rR/3.5))`. -/
theorem den_le (W W' Q R : ℝ) (q r : ℕ) (hW : 117 ≤ W) (hW' : W / 2 ≤ W') (hq : 1 ≤ q)
    (hQW : 3.5 * W ≤ Q) (hr : 1 ≤ r) (hrR : (r : ℝ) ≤ R) (hqR : (q : ℝ) * R ^ 2 < 3.5 * W) :
    0 < 1 / ((q : ℝ) * r * R) - 1 / Q ∧
    (((⌊W⌋₊ - ⌊W'⌋₊ : ℕ)) : ℝ) + 3 / 2 * (1 / ((q : ℝ) * r * R) - 1 / Q)⁻¹ ≤
      W * ((W + 1) / (2 * W) + 3 / 2 * ((r : ℝ) * R / (W / q - r * R / 3.5))) := by
  have hW0 : 0 < W := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hR0 : 0 < R := by linarith
  rw [show (3.5 : ℝ) = 7 / 2 by norm_num] at hQW hqR ⊢
  set c := (q : ℝ) * r * R with hc
  have hc0 : 0 < c := by positivity
  have hcW : c < 7 / 2 * W := by
    have : c ≤ (q : ℝ) * R ^ 2 := by
      rw [hc]
      have : (r : ℝ) * R ≤ R * R := mul_le_mul_of_nonneg_right hrR hR0.le
      nlinarith
    linarith
  have hcQ : c < Q := by linarith
  have hpos : 0 < 1 / c - 1 / Q := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt hc0 hcQ
  refine ⟨hpos, ?_⟩
  have e1 : (1 / c - 1 / Q)⁻¹ = c * Q / (Q - c) := by
    have h1 : Q - c ≠ 0 := by linarith
    have h2 : Q ≠ 0 := by linarith
    have h3 : c ≠ 0 := hc0.ne'
    rw [div_sub_div _ _ h3 h2, inv_div, one_mul, mul_one]
  have e2 : W * ((r : ℝ) * R / (W / q - r * R / (7 / 2))) = c * (7 / 2 * W) / (7 / 2 * W - c) := by
    have h35 : 7 / 2 * W - c ≠ 0 := by linarith
    have h36 : W / q - r * R / (7 / 2) = (7 / 2 * W - c) / (7 / 2 * q) := by
      rw [hc]
      field_simp
    rw [h36, hc]
    field_simp
  have hle : c * Q / (Q - c) ≤ c * (7 / 2 * W) / (7 / 2 * W - c) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have := mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hQW)
    nlinarith
  have hN := n_le W W' hW0.le hW'
  have hNa : (W + 1) / 2 = W * ((W + 1) / (2 * W)) := by
    field_simp
  have e3 : W * (3 / 2 * ((r : ℝ) * R / (W / q - r * R / (7 / 2)))) =
      3 / 2 * (c * (7 / 2 * W) / (7 / 2 * W - c)) := by
    rw [← e2]
    ring
  rw [e1, mul_add, ← hNa, e3]
  linarith [mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 3 / 2)]

/-- **`T2G.WeightLB` from `WeightX`, PROVED** (`X = W/q`, `copRed`, `den_le`). -/
theorem weightLB_of_X (wx : WeightX) : WeightLB := by
  intro W W' Q q hW hW' hWW hq hqW hQW
  have hW0 : 0 < W := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hX : 2 < W / q := by rw [lt_div_iff₀ hq0]; linarith
  have hXW : W / q ≤ W := div_le_self hW0.le hq1
  obtain ⟨R, hR1, hRX, hR2, hlog⟩ := wx W (W / q) hW hX hXW
  have hR0 : 0 < R := by linarith
  have hqR : (q : ℝ) * R ^ 2 < 3.5 * W := by
    have := mul_lt_mul_of_pos_left hR2 hq0
    rwa [show (q : ℝ) * (3.5 * (W / q)) = 3.5 * W by field_simp] at this
  refine ⟨R, hR1, ?_, by linarith, ?_⟩
  · have : W / q / 2 ≤ W / 2 := by
      have := div_le_self hW0.le hq1
      linarith
    linarith
  · obtain ⟨hgpos, hganti⟩ := gX_pos_anti W (W / q) R hW0 hR1 hR2
    have hcop := copRed q hq R (gX W (W / q) R) (fun r h1 h2 => (hgpos r h1 h2).le) hganti
    have hlogeq : Real.log (W / q / 2) = Real.log (W / (2 * q)) := by
      congr 1
      field_simp
    rw [hlogeq] at hlog
    have hphi : (0 : ℝ) ≤ Nat.totient q / q := by positivity
    have h1 : (Nat.totient q : ℝ) / q * Real.log (W / (2 * q)) / W ≤
        (∑ r ∈ rS q R, gX W (W / q) R r / Nat.totient r) / W := by
      apply div_le_div_of_nonneg_right _ hW0.le
      exact (mul_le_mul_of_nonneg_left hlog hphi).trans hcop
    refine h1.trans ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun r hr => ?_
    have hrm := Finset.mem_filter.mp hr
    have hrI := Finset.mem_Icc.mp hrm.1
    have hrR : (r : ℝ) ≤ R := le_trans (Nat.cast_le.mpr hrI.2) (Nat.floor_le hR0.le)
    obtain ⟨hpos, hden⟩ := den_le W W' Q R q r hW hW' hq hQW hrI.1 hrR hqR
    have hphr : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hrI.1
    have hDpos : 0 < (((⌊W⌋₊ - ⌊W'⌋₊ : ℕ)) : ℝ) +
        3 / 2 * (1 / ((q : ℝ) * r * R) - 1 / Q)⁻¹ := by positivity
    have hg : gX W (W / q) R r / W = (W * ((W + 1) / (2 * W) +
        3 / 2 * ((r : ℝ) * R / (W / q - r * R / 3.5))))⁻¹ := by
      unfold gX
      rw [mul_inv, div_eq_mul_inv, mul_comm]
    calc gX W (W / q) R r / Nat.totient r / W = gX W (W / q) R r / W / Nat.totient r := by
          ring
      _ = (W * ((W + 1) / (2 * W) +
            3 / 2 * ((r : ℝ) * R / (W / q - r * R / 3.5))))⁻¹ / Nat.totient r := by rw [hg]
      _ ≤ _ := div_le_div_of_nonneg_right (inv_anti₀ hDpos hden) hphr.le

/-- **`T2X.Garn1a` from Montgomery's inequality, the weighted large sieve and `WeightX`**. -/
theorem garn1a_of_X (mi : T2M.MontgomeryIneq) (mv : MVWeighted) (wx : WeightX) :
    Principia.Common.TernaryGoldbach.T2X.Garn1a :=
  garn1a_of_links mi mv (weightLB_of_X wx)

end Principia.Common.TernaryGoldbach.T2V
