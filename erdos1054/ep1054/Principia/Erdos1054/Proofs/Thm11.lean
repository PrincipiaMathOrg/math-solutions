/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Density

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) — the proof of Theorem 1.1 (`thm:small-upper`), lines 1118–1148

Discharges the `Thm11` package of `Principia.Erdos1054.Spine`.

Leaves (from the definitions and Mathlib alone):
* `leaf_SmallUpper_emptyCase` (line 1124) — `δX < 1` makes `𝓔_δ(X)` empty, since `f(N) ≥ 1`.
* `leaf_SmallUpper_markov` (lines 1124–1131) — `N ↦ (f(N), j)` with `N = σ_j(f(N))` lands in
  `{(n, j) : n ≤ δX, j < τ(n), δ σ_j(n)/n ≥ 1}` and has the left inverse `(n, j) ↦ σ_j(n)`, so
  `#𝓔_δ(X)` is at most the number of such pairs, which Markov bounds by the `q`-th moment.
* `leaf_SmallUpper_paramChoice` (lines 1134–1145) — explicit constants: `c = 1/(2C)` and
  `δ₀ = exp(-(4 + 2/c))` (so `log(1/δ) ≥ 4` and `(1/δ)^c ≥ 3`, whence `q ≥ 3`); then
  `C log log q ≤ C c log(1/δ) = ½ log(1/δ)` and `(q/2 + 1) log(1/δ) ≥ 2(E + 1) ≥ E`, where
  `E = exp((1/δ)^c) ≥ exp((1/δ)^{c/2})` and `q > E − 1` (`paramChoice_aux`).
* `leaf_SmallUpper_doubleExpPower` (lines 1145–1147) — with `s = log(1/δ) ≥ 0`,
  `M s ≤ (sc)²/2 + (M/c)²/2 ≤ exp(sc) + (M/c)²/2 ≤ exp(exp(sc)) + (M/c)²/2`, i.e. the constant is
  `K = exp((M/c)²/2)`, valid on all of `δ ∈ (0, 1]`.

Links (from exactly the dependencies the spine names):
* `link_SmallUpper_momentStep` — `SmallUpper_markov`, then `Lem_KovacMoment` at `x = δX ≥ 1`;
  the constants `C, K` are the lemma's.
* `link_Thm_SmallUpper_doubleExp` — `SmallUpper_emptyCase` for `δX < 1`; otherwise
  `SmallUpper_momentStep` at `q = ⌊exp((1/δ)^c)⌋` and `SmallUpper_paramChoice` at the moment
  lemma's `C`. The theorem's exponent is `c/2` ("renaming `c/2` as `c`") and its constant is
  `max K 0` (nonnegative, so the empty case also satisfies the bound).
* `link_Thm_SmallUpper_fixedPower` — `δ₀' = min(δ₀, 1)` (the power bound is stated on `(0, 1]`),
  constant `max(C, 0) · K_M`.
* `link_Thm_SmallUpper_upperDens` — divide by `X` (`upperDens_le_of_forall_ge`, `Density.lean`).

`Thm_SmallUpper` itself is the conjunction `Thm_SmallUpper_doubleExp ∧ Thm_SmallUpper_fixedPower`,
assembled by `And.intro` in the spine; it gets no declaration here.
-/

namespace Principia.Erdos1054.Proofs

open Principia.Erdos1054

namespace Thm11

/-- For `N ∈ 𝓡`, the minimiser `f N` is `≥ 1` and represents `N`. -/
theorem f_spec {N : ℕ} (hN : N ∈ R) : 1 ≤ f N ∧ IsRep N (f N) := by
  have hne : {m | 1 ≤ m ∧ IsRep N m}.Nonempty := hN
  exact Nat.sInf_mem hne

/-- `δ^n = exp(-n log(1/δ))` for `δ > 0`. -/
theorem pow_eq_exp_neg (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    δ ^ n = Real.exp (-(n : ℝ) * Real.log (1 / δ)) := by
  rw [one_div, Real.log_inv, show -(n : ℝ) * -Real.log δ = n * Real.log δ by ring,
    Real.exp_nat_mul, Real.exp_log hδ]

/-- The parameter choice of the proof of Theorem 1.1, for an explicit `c` with `C c = 1/2` and
`δ ≤ exp(-(4 + 2/c))`. -/
theorem paramChoice_aux (C c : ℝ) (hC : 0 < C) (hc : 0 < c) (hCc : C * c = 1 / 2) (δ : ℝ)
    (hδ : 0 < δ) (hδ0 : δ ≤ Real.exp (-(4 + 2 / c))) :
    3 ≤ S4a.qChoice c δ ∧
      δ ^ (S4a.qChoice c δ + 1) *
          Real.exp (C * (S4a.qChoice c δ : ℝ) * Real.log (Real.log (S4a.qChoice c δ : ℝ))) ≤
        Real.exp (-Real.exp ((1 / δ) ^ (c / 2))) := by
  have ht : 0 < 1 / δ := one_div_pos.mpr hδ
  have hL : 4 + 2 / c ≤ Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log hδ hδ0
    rw [Real.log_exp] at this
    linarith
  have hc2 : 0 < 2 / c := div_pos two_pos hc
  have hL4 : 4 ≤ Real.log (1 / δ) := by linarith
  have ht1 : 1 ≤ 1 / δ := by
    have h := Real.add_one_le_exp (Real.log (1 / δ))
    rw [Real.exp_log ht] at h
    linarith
  have hLc : 2 ≤ Real.log (1 / δ) * c := by
    have h1 : (2 / c) * c = 2 := div_mul_cancel₀ 2 hc.ne'
    nlinarith
  have hu : (1 / δ) ^ c = Real.exp (Real.log (1 / δ) * c) := Real.rpow_def_of_pos ht c
  have hu3 : 3 ≤ (1 / δ) ^ c := by
    rw [hu]
    have := Real.add_one_le_exp (Real.log (1 / δ) * c)
    linarith
  have hE4 : 4 ≤ Real.exp ((1 / δ) ^ c) := by
    have := Real.add_one_le_exp ((1 / δ) ^ c)
    linarith
  have hq_def : S4a.qChoice c δ = ⌊Real.exp ((1 / δ) ^ c)⌋₊ := rfl
  have hq3 : 3 ≤ S4a.qChoice c δ := by
    rw [hq_def]
    apply Nat.le_floor
    push_cast
    linarith
  have hqE : (S4a.qChoice c δ : ℝ) ≤ Real.exp ((1 / δ) ^ c) := by
    rw [hq_def]
    exact Nat.floor_le (Real.exp_pos _).le
  have hEq : Real.exp ((1 / δ) ^ c) < (S4a.qChoice c δ : ℝ) + 1 := by
    rw [hq_def]
    exact Nat.lt_floor_add_one _
  refine ⟨hq3, ?_⟩
  have hhalf : (1 / δ) ^ (c / 2) ≤ (1 / δ) ^ c :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have hexpc2 : Real.exp ((1 / δ) ^ (c / 2)) ≤ Real.exp ((1 / δ) ^ c) :=
    Real.exp_le_exp.mpr hhalf
  have hlogrpow : Real.log ((1 / δ) ^ c) = c * Real.log (1 / δ) := Real.log_rpow ht c
  have hQ3 : (3 : ℝ) ≤ (S4a.qChoice c δ : ℝ) := by exact_mod_cast hq3
  have hlogQ_pos : 0 < Real.log (S4a.qChoice c δ : ℝ) := Real.log_pos (by linarith)
  have hlogQ_le : Real.log (S4a.qChoice c δ : ℝ) ≤ (1 / δ) ^ c := by
    have := Real.log_le_log (by linarith) hqE
    rwa [Real.log_exp] at this
  have hloglog : Real.log (Real.log (S4a.qChoice c δ : ℝ)) ≤ c * Real.log (1 / δ) := by
    have := Real.log_le_log hlogQ_pos hlogQ_le
    rwa [hlogrpow] at this
  rw [pow_eq_exp_neg δ hδ, ← Real.exp_add, Real.exp_le_exp]
  push_cast
  generalize S4a.qChoice c δ = q at hQ3 hqE hEq hloglog ⊢
  generalize Real.log (1 / δ) = L at hL4 hloglog ⊢
  generalize Real.exp ((1 / δ) ^ c) = E at hqE hEq hexpc2
  generalize Real.exp ((1 / δ) ^ (c / 2)) = e2 at hexpc2 ⊢
  have hCq : 0 ≤ C * (q : ℝ) := mul_nonneg hC.le (Nat.cast_nonneg _)
  have hCQ : C * q * Real.log (Real.log q) ≤ C * q * (c * L) :=
    mul_le_mul_of_nonneg_left hloglog hCq
  have hCQ' : C * q * (c * L) = q * L / 2 := by
    calc C * q * (c * L) = (C * c) * (q * L) := by ring
      _ = q * L / 2 := by rw [hCc]; ring
  have hkey : 2 * E ≤ ((q : ℝ) + 2) * L := by
    have h1 : ((q : ℝ) + 2) * 4 ≤ ((q : ℝ) + 2) * L :=
      mul_le_mul_of_nonneg_left hL4 (by positivity)
    linarith
  linarith

end Thm11

open Thm11

/-- `SmallUpper_emptyCase` (EP1054.tex line 1124): if `δX < 1` then `𝓔_δ(X) = ∅`, because
`f(N) ≥ 1` for `N ∈ 𝓡`. -/
theorem leaf_SmallUpper_emptyCase : Principia.Erdos1054.SmallUpper_emptyCase := by
  intro δ hδ X hδX
  unfold cnt
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro N hN
  rw [mem_cntFinset] at hN
  obtain ⟨⟨hN1, hNX⟩, hNS⟩ := hN
  obtain ⟨hR, hf⟩ : N ∈ R ∧ (f N : ℝ) ≤ δ * N := hNS
  have hf1 : 1 ≤ f N := (f_spec hR).1
  have hX1 : 1 ≤ X := Nat.floor_pos.mp (by omega)
  have hNX' : (N : ℝ) ≤ X := (Nat.le_floor_iff (by linarith)).mp hNX
  have hf1' : (1 : ℝ) ≤ f N := by exact_mod_cast hf1
  have : δ * N ≤ δ * X := mul_le_mul_of_nonneg_left hNX' hδ.le
  linarith

/-- `SmallUpper_markov` (EP1054.tex lines 1124–1131): each `N ∈ 𝓔_δ(X)` is `σ_j(n)` for
`n = f(N) ≤ δX` and some `j < τ(n)`, with `δ σ_j(n)/n ≥ 1`; the map `N ↦ (n, j)` is injective
(it has the left inverse `(n, j) ↦ σ_j(n)`), so Markov's inequality gives the bound. -/
theorem leaf_SmallUpper_markov : Principia.Erdos1054.SmallUpper_markov := by
  classical
  intro δ hδ X hδX q hq
  have hX0 : 0 < X := by
    by_contra h
    have h' : X ≤ 0 := not_lt.mp h
    nlinarith
  obtain ⟨T, hT⟩ : ∃ T : Finset (Σ _ : ℕ, ℕ),
      T = (Finset.Icc 1 ⌊δ * X⌋₊).sigma (fun n => Finset.range n.divisors.card) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : (Σ _ : ℕ, ℕ) → ℝ,
      w = fun p => δ ^ q * ((sigmaPrefix p.2 p.1 : ℝ) / p.1) ^ q := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T' : Finset (Σ _ : ℕ, ℕ), T' = T.filter (fun p => 1 ≤ w p) := ⟨_, rfl⟩
  have hw0 : ∀ p, 0 ≤ w p := fun p => by
    rw [hw]
    exact mul_nonneg (pow_nonneg hδ.le _)
      (pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)
  have hcard : cnt (smallRatioSet δ) X ≤ (T'.image (fun p => sigmaPrefix p.2 p.1)).card := by
    unfold cnt
    apply Finset.card_le_card
    intro N hN
    rw [mem_cntFinset] at hN
    obtain ⟨⟨hN1, hNX⟩, hNS⟩ := hN
    obtain ⟨hR, hf⟩ : N ∈ R ∧ (f N : ℝ) ≤ δ * N := hNS
    obtain ⟨hn1, k, hk1, hk2, hNk⟩ := f_spec hR
    have hNX' : (N : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).mp hNX
    have hnpos : (0 : ℝ) < f N := by exact_mod_cast hn1
    have hnle : f N ≤ ⌊δ * X⌋₊ := by
      apply Nat.le_floor
      have : δ * N ≤ δ * X := mul_le_mul_of_nonneg_left hNX' hδ.le
      linarith
    have hsig : sigmaPrefix ((f N).divisors.card - k) (f N) = N := by
      have hlt : (f N).divisors.card - k < (f N).divisors.card := by omega
      unfold sigmaPrefix
      rw [if_pos hlt, show (f N).divisors.card - ((f N).divisors.card - k) = k by omega]
      exact hNk.symm
    rw [Finset.mem_image]
    refine ⟨⟨f N, (f N).divisors.card - k⟩, ?_, hsig⟩
    rw [hT', Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simp only [hT, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range]
      refine ⟨⟨hn1, hnle⟩, ?_⟩
      omega
    · rw [hw]
      simp only
      rw [hsig, ← mul_pow]
      apply one_le_pow₀
      rw [← mul_div_assoc, le_div_iff₀ hnpos, one_mul]
      exact hf
  have h2 : ((T'.image (fun p => sigmaPrefix p.2 p.1)).card : ℝ) ≤ T'.card := by
    exact_mod_cast Finset.card_image_le
  have h3 : (T'.card : ℝ) ≤ ∑ p ∈ T', w p := by
    have := Finset.card_nsmul_le_sum T' w 1 (fun p hp => by
      rw [hT', Finset.mem_filter] at hp
      exact hp.2)
    simpa using this
  have h4 : ∑ p ∈ T', w p ≤ ∑ p ∈ T, w p := by
    rw [hT']
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p _ _ => hw0 p)
  have h5 : ∑ p ∈ T, w p = δ ^ q * ∑ n ∈ Finset.Icc 1 ⌊δ * X⌋₊, S4a.prefixMoment q n := by
    rw [hT, hw, Finset.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    unfold S4a.prefixMoment
    rw [Finset.mul_sum]
  calc (cnt (smallRatioSet δ) X : ℝ)
      ≤ ((T'.image (fun p => sigmaPrefix p.2 p.1)).card : ℝ) := by exact_mod_cast hcard
    _ ≤ T'.card := h2
    _ ≤ ∑ p ∈ T', w p := h3
    _ ≤ ∑ p ∈ T, w p := h4
    _ = δ ^ q * ∑ n ∈ Finset.Icc 1 ⌊δ * X⌋₊, S4a.prefixMoment q n := h5

/-- `SmallUpper_momentStep` (EP1054.tex lines 1129–1133): Markov's bound, then Kovač's moment
lemma at `x = δX ≥ 1`. -/
theorem link_SmallUpper_momentStep : Principia.Erdos1054.Spine.Link_SmallUpper_momentStep := by
  intro hmarkov hkovac
  obtain ⟨C, hC, K, hK⟩ := hkovac
  refine ⟨C, hC, K, fun δ hδ X hδX q hq => ?_⟩
  have h1 := hmarkov δ hδ X hδX q hq
  have h2 := hK q hq (δ * X) hδX
  have hδq : 0 ≤ δ ^ q := pow_nonneg hδ.le q
  calc (cnt (smallRatioSet δ) X : ℝ)
      ≤ δ ^ q * ∑ n ∈ Finset.Icc 1 ⌊δ * X⌋₊, S4a.prefixMoment q n := h1
    _ ≤ δ ^ q * (K * Real.exp (C * (q : ℝ) * Real.log (Real.log (q : ℝ))) * (δ * X)) :=
        mul_le_mul_of_nonneg_left h2 hδq
    _ = K * δ ^ (q + 1) * Real.exp (C * (q : ℝ) * Real.log (Real.log (q : ℝ))) * X := by ring

/-- `SmallUpper_paramChoice` (EP1054.tex lines 1134–1145): `c = 1/(2C)`, `δ₀ = exp(-(4 + 2/c))`. -/
theorem leaf_SmallUpper_paramChoice : Principia.Erdos1054.SmallUpper_paramChoice := by
  intro C hC
  have hc : 0 < 1 / (2 * C) := div_pos one_pos (mul_pos two_pos hC)
  have hC0 : C ≠ 0 := hC.ne'
  have hCc : C * (1 / (2 * C)) = 1 / 2 := by field_simp
  exact ⟨1 / (2 * C), hc, Real.exp (-(4 + 2 / (1 / (2 * C)))), Real.exp_pos _,
    fun δ hδ hδ0 => paramChoice_aux C (1 / (2 * C)) hC hc hCc δ hδ hδ0⟩

/-- `SmallUpper_doubleExpPower` (EP1054.tex lines 1145–1147): with `s = log(1/δ) ≥ 0`,
`M s ≤ (sc)²/2 + (M/c)²/2 ≤ exp(sc) + (M/c)²/2 ≤ exp(exp(sc)) + (M/c)²/2`. -/
theorem leaf_SmallUpper_doubleExpPower : Principia.Erdos1054.SmallUpper_doubleExpPower := by
  intro c hc M hM
  refine ⟨Real.exp ((M / c) ^ 2 / 2), fun δ hδ hδ1 => ?_⟩
  have ht : 0 < 1 / δ := one_div_pos.mpr hδ
  have hs : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hδM : δ ^ M = Real.exp (-(M * Real.log (1 / δ))) := by
    rw [Real.rpow_def_of_pos hδ, one_div, Real.log_inv]
    congr 1
    ring
  have htc : (1 / δ) ^ c = Real.exp (Real.log (1 / δ) * c) := Real.rpow_def_of_pos ht c
  rw [hδM, ← Real.exp_add, Real.exp_le_exp, htc]
  generalize Real.log (1 / δ) = s at hs ⊢
  have hsc : 0 ≤ s * c := mul_nonneg hs hc.le
  have h1 := Real.add_one_le_exp (Real.exp (s * c))
  have h2 := Real.quadratic_le_exp_of_nonneg hsc
  have hab : M * s = (M / c) * (s * c) := by
    calc M * s = M * s * (c / c) := by rw [div_self hc.ne', mul_one]
      _ = (M / c) * (s * c) := by ring
  have h3 : M * s ≤ (s * c) ^ 2 / 2 + (M / c) ^ 2 / 2 := by
    nlinarith [sq_nonneg (M / c - s * c)]
  linarith

/-- `Thm_SmallUpper_doubleExp` (Theorem 1.1, first assertion; proof EP1054.tex lines 1118–1145):
the case `δX < 1` is empty; otherwise the moment step at `q = ⌊exp((1/δ)^c)⌋` and the parameter
choice give the bound with exponent `c/2` ("renaming `c/2` as `c`"). -/
theorem link_Thm_SmallUpper_doubleExp :
    Principia.Erdos1054.Spine.Link_Thm_SmallUpper_doubleExp := by
  intro hempty hmoment hparam
  obtain ⟨C₁, hC₁, K, hK⟩ := hmoment
  obtain ⟨c, hc, δ₀, hδ₀, hchoice⟩ := hparam C₁ hC₁
  refine ⟨c / 2, half_pos hc, max K 0, δ₀, hδ₀, fun δ hδ hδδ₀ X hX => ?_⟩
  have hE0 : 0 ≤ Real.exp (-Real.exp ((1 / δ) ^ (c / 2))) := (Real.exp_pos _).le
  have hX0 : 0 ≤ X := by linarith
  have hmax0 : 0 ≤ max K 0 := le_max_right _ _
  by_cases hδX : δ * X < 1
  · rw [hempty δ hδ X hδX]
    push_cast
    exact mul_nonneg (mul_nonneg hmax0 hX0) hE0
  · have hδX' : 1 ≤ δ * X := not_lt.mp hδX
    obtain ⟨hq3, hineq⟩ := hchoice δ hδ hδδ₀
    have h1 := hK δ hδ X hδX' (S4a.qChoice c δ) hq3
    have hP0 : 0 ≤ δ ^ (S4a.qChoice c δ + 1) * Real.exp (C₁ * (S4a.qChoice c δ : ℝ) *
        Real.log (Real.log (S4a.qChoice c δ : ℝ))) :=
      mul_nonneg (pow_nonneg hδ.le _) (Real.exp_pos _).le
    calc (cnt (smallRatioSet δ) X : ℝ)
        ≤ K * δ ^ (S4a.qChoice c δ + 1) * Real.exp (C₁ * (S4a.qChoice c δ : ℝ) *
            Real.log (Real.log (S4a.qChoice c δ : ℝ))) * X := h1
      _ = K * (δ ^ (S4a.qChoice c δ + 1) * Real.exp (C₁ * (S4a.qChoice c δ : ℝ) *
            Real.log (Real.log (S4a.qChoice c δ : ℝ)))) * X := by ring
      _ ≤ max K 0 * (δ ^ (S4a.qChoice c δ + 1) * Real.exp (C₁ * (S4a.qChoice c δ : ℝ) *
            Real.log (Real.log (S4a.qChoice c δ : ℝ)))) * X :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left K 0) hP0) hX0
      _ ≤ max K 0 * Real.exp (-Real.exp ((1 / δ) ^ (c / 2))) * X :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hineq hmax0) hX0
      _ = max K 0 * X * Real.exp (-Real.exp ((1 / δ) ^ (c / 2))) := by ring

/-- `Thm_SmallUpper_fixedPower` (Theorem 1.1, second assertion; EP1054.tex lines 148–149,
1145–1147): the double-exponential bound on `δ ≤ min(δ₀, 1)`, then `exp(-exp((1/δ)^c)) ≤ K δ^M`. -/
theorem link_Thm_SmallUpper_fixedPower :
    Principia.Erdos1054.Spine.Link_Thm_SmallUpper_fixedPower := by
  intro hdbl hpow
  obtain ⟨c, hc, C, δ₀, hδ₀, hbound⟩ := hdbl
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun M hM => ?_⟩
  obtain ⟨K, hK⟩ := hpow c hc M hM
  refine ⟨max C 0 * K, fun δ hδ hδle X hX => ?_⟩
  have hδ₀' : δ ≤ δ₀ := hδle.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδle.trans (min_le_right _ _)
  have h1 := hbound δ hδ hδ₀' X hX
  have h2 := hK δ hδ hδ1
  have hX0 : 0 ≤ X := by linarith
  have hE0 : 0 ≤ Real.exp (-Real.exp ((1 / δ) ^ c)) := (Real.exp_pos _).le
  have hmax0 : 0 ≤ max C 0 := le_max_right _ _
  have h3 := mul_le_mul_of_nonneg_right (le_max_left C 0) (mul_nonneg hX0 hE0)
  have h4 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hmax0 hX0)
  calc (cnt (smallRatioSet δ) X : ℝ) ≤ C * X * Real.exp (-Real.exp ((1 / δ) ^ c)) := h1
    _ ≤ max C 0 * X * Real.exp (-Real.exp ((1 / δ) ^ c)) := by linarith
    _ ≤ max C 0 * X * (K * δ ^ M) := h4
    _ = max C 0 * K * δ ^ M * X := by ring

/-- `Thm_SmallUpper_upperDens` (EP1054.tex lines 152–154): divide the bound of Theorem 1.1 by
`X` and take the `limsup`. -/
theorem link_Thm_SmallUpper_upperDens :
    Principia.Erdos1054.Spine.Link_Thm_SmallUpper_upperDens := by
  intro h
  obtain ⟨c, hc, C, δ₀, hδ₀, hbound⟩ := h
  refine ⟨c, hc, C, δ₀, hδ₀, fun δ hδ hδδ₀ => ?_⟩
  apply upperDens_le_of_forall_ge (X₀ := 1)
  intro X hX
  calc (cnt (smallRatioSet δ) X : ℝ) ≤ C * X * Real.exp (-Real.exp ((1 / δ) ^ c)) :=
        hbound δ hδ hδδ₀ X hX
    _ = C * Real.exp (-Real.exp ((1 / δ) ^ c)) * X := by ring

end Principia.Erdos1054.Proofs
